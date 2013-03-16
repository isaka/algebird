/*
Copyright 2012 Twitter, Inc.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*/

package com.twitter.algebird


class SketchMapMonoid[K, V](eps: Double, delta: Double, seed: Int, heavyHittersCount: Int)
                           (implicit serialization: K => Array[Byte], valueOrdering: Ordering[V], monoid: Monoid[V])
extends Monoid[SketchMap[K, V]] {

  val hashes: Seq[SketchMapHash[K]] = {
    val r = new scala.util.Random(seed)
    val numHashes = SketchMap.depth(delta)
    val numCounters = SketchMap.width(eps)
    (0 to (numHashes - 1)).map { _ =>
      SketchMapHash[K](CMSHash(r.nextInt, 0, numCounters), seed)
    }
  }

  val params: SketchMapParams[K, V] = SketchMapParams[K, V](hashes, eps, delta, heavyHittersCount)
  val zero: SketchMap[K, V] = {
    new SketchMap[K, V](params, SketchMapValuesTable[V](params.depth, params.width), SketchMapHeavyHitters.empty[K, V])
  }

  /**
   * We assume the Sketch Map on the left and right use the same hash functions.
   */
  def plus(left: SketchMap[K, V], right: SketchMap[K, V]): SketchMap[K, V] = left ++ right


  /**
   * Create a Sketch Map sketch out of a single key or data stream.
   */
  def create(key: K, value: V): SketchMap[K, V] = zero + (key, value)
  def create(data: Seq[(K, V)]): SketchMap[K, V] = {
    data.foldLeft(zero) { case (acc, (key, value)) =>
      plus(acc, create(key, value))
    }
  }
}


object SketchMap {
  /**
   * Functions to translate between (eps, delta) and (depth, width). The translation is:
   * depth = ceil(ln 1/delta)
   * width = ceil(e / eps)
   */
  def eps(width : Int) = scala.math.exp(1.0) / width
  def delta(depth : Int) = 1.0 / scala.math.exp(depth)
  def depth(delta : Double) = scala.math.ceil(scala.math.log(1.0 / delta)).toInt
  def width(eps : Double) = scala.math.ceil(scala.math.exp(1) / eps).toInt
}

class SketchMap[K, V](
  val params: SketchMapParams[K, V],
  val valuesTable: SketchMapValuesTable[V],
  val heavyHitters: SketchMapHeavyHitters[K, V]
)(implicit ordering: Ordering[V], implicit monoid: Monoid[V]) extends java.io.Serializable {

  def eps: Double = params.eps
  def delta: Double = params.delta

  def frequency(key: K): V = {
    val estimates = valuesTable.values.zipWithIndex.map { case (row, i) =>
      row(params.hashes(i)(key))
    }

    estimates.min
  }

  def +(pair: (K, V)): SketchMap[K, V] = {
    val (key, value) = pair

    val newHeavyHitters = updateHeavyHitters(key, value)
    val newValuesTable = (0 to (params.depth - 1)).foldLeft(valuesTable) { case (table, row) =>
      val pos = (row, params.hashes(row)(key))
      table + (pos, value)
    }

    SketchMap[K, V](params, newValuesTable, newHeavyHitters, params)
  }

  def ++(other: SketchMap[K, V]): SketchMap[K, V] = {
    val newHhs = (hhs ++ other.hhs).dropCountsBelow(params.heavyHittersCount)
    new SketchMap(params, valuesTable ++ other.valuesTable, newHhs)
  }

  /**
   * Updates the data structure of heavy hitters when a new item (with associated value)
   * enters the stream.
   */
  private def updatedHeavyHitters(key: K, value: V): SketchMapHeavyHitters[K, V] = {
    val oldValue = frequency(key)
    val newCount = Monoid.plus(oldValue, value)

    // If the new item is a heavy hitter, add it, and remove any previous instances.
    val newHhs =
      if (newItemCount >= heavyHittersPct * newTotalCount) {
        hhs - HeavyHitter(item, oldItemCount) + HeavyHitter(item, newItemCount)
      } else {
        hhs
      }

    // Remove any items below the heavy hitter threshold.
    newHhs.dropCountsBelow(params.heavyHittersCount)
  }
}

/**
 * Convenience class for holding constant parameters of a Sketch Map.
 */
case class SketchMapParams[K, V](hashes: Seq[SketchMapHash[K]], eps: Double, delta: Double, heavyHittersCount: Int) {
  assert(0 < eps && eps < 1, "eps must lie in (0, 1)")
  assert(0 < delta && delta < 1, "delta must lie in (0, 1)")
  assert(0 <= heavyHittersCount , "heavyHittersCount must be greater than 0")

  val depth = SketchMap.depth(delta)
  val width = SketchMap.width(eps)
}


/**
 * The 2-dimensional table of counters used in the Count-Min sketch.
 * Each row corresponds to a particular hash function.
 * TODO: implement a dense matrix type, and use it here
 */
case class SketchMapValuesTable[V](values: Vector[Vector[V]])(implicit monoid: Monoid[V]) {
  assert(depth > 0, "Table must have at least 1 row.")
  assert(width > 0, "Table must have at least 1 column.")

  def depth: Int = values.size
  def width: Int = values(0).size

  def getValue(pos: (Int, Int)): V = {
    val (row, col) = pos

    assert(row < depth && col < width, "Position must be within the bounds of this table.")

    values(row)(col)
  }

  /**
   * Updates the value of a single cell in the table.
   */
  def +(pos: (Int, Int), value: V): SketchMapValuesTable[V] = {
    val (row, col) = pos
    val currValue: V = getValue(pos)
    val newValues = values.updated(row, values(row).updated(col, Monoid.plus(currValue, value)))

    SketchMapValuesTable[V](newValues)
  }

  /**
   * Adds another values table to this one, through elementwise addition.
   */
  def ++(other: SketchMapValuesTable[V]): SketchMapValuesTable[V] = {
    assert((depth, width) == (other.depth, other.width), "Tables must have the same dimensions.")
    val iil = Monoid.plus[IndexedSeq[IndexedSeq[V]]](values, other.values)

    def toVector[Q](is: IndexedSeq[Q]): Vector[Q] = {
      is match {
        case v: Vector[_] => v
        case _ => Vector(is: _*)
      }
    }

    SketchMapValuesTable[V](toVector(iil.map { toVector(_) }))
  }
}

object SketchMapValuesTable {
   // Creates a new SketchMapValuesTable with counts initialized to all zeroes.
  def apply[V](depth: Int, width: Int)(implicit monoid: Monoid[V]): SketchMapValuesTable[V] = {
    SketchMapValuesTable(Vector.fill[V](depth, width)(monoid.zero))
  }
}

object SketchMapHeavyHitters {
  def empty[K, V] = {
    new SketchMapHeavyHitters(Seq.empty[SketchMapHeavyHitter[K, V]])
  }
}

case class SketchMapHeavyHitters[K, V](heavyHitters: Seq[SketchMapHeavyHitter[K, V]]) {
  def keys: Seq[K] = heavyHitters map { _.key }
}

case class SketchMapHeavyHitter[K, V](key: K, value: V) {

}

case class SketchMapHash[T](hasher: CMSHash, seed: Int)(implicit serialization: T => Array[Byte]) extends Function1[T, Int] {
  def apply(obj: T): Int = {
    val hashKey: Long = MurmurHash128(seed)(serialization(obj)) match {
      case (first: Long, second: Long) => (first ^ second)
    }

    hasher(hashKey)
  }
}

