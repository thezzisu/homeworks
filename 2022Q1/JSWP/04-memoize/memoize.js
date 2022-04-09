// @ts-check
class LRUCache {
  /**
   * @param {number} size
   */
  constructor(size) {
    this.size = size
    this.mapper = new Map()
    this.cache = new Map()
    this.kNotFound = Symbol()
  }

  /**
   * @param {Array<any>} keys
   */
  get(keys) {
    const k = this.#getMapper(keys)
    if (k == undefined) return this.kNotFound
    const entry = this.cache.get(k)
    this.cache.delete(k)
    this.cache.set(k, entry)
    return entry.val
  }

  /**
   * @param {Array<any>} keys
   * @param {any} val
   * @returns {this}
   */
  set(keys, val) {
    this.delete(keys)
    if (this.cache.size >= this.size) {
      const { keys } = this.cache.values().next().value
      this.delete(keys)
    }
    const k = Symbol()
    this.#setMapper(keys, k)
    this.cache.set(k, { keys, val })
    return this
  }

  /**
   * @param {Array<any>} keys
   * @returns {boolean}
   */
  delete(keys) {
    const k = this.#getMapper(keys)
    if (k == undefined) return false
    this.cache.delete(k)
    this.#deleteMapper(keys)
    return true
  }

  /**
   * @param {Array<any>} keys
   * @returns {symbol}
   */
  #getMapper(keys) {
    return keys.reduce((acc, key) => acc && acc.get(key), this.mapper)
  }

  /**
   * @param {Array<any>} keys
   * @param {symbol} k
   */
  #setMapper(keys, k) {
    const last = keys.pop()
    const mapper = keys.reduce(
      (acc, key) =>
        acc.has(key) ? acc.get(key) : acc.set(key, new Map()).get(key),
      this.mapper
    )
    mapper.set(last, k)
  }

  /**
   * @param {Array<any>} keys
   */
  #deleteMapper(keys) {
    /**
     * @param {Map<any, any>} cache
     * @param {Array<any>} keys
     * @returns {boolean}
     */
    const remove = (cache, keys) => {
      if (!cache || !keys.length) return false
      const key = keys.shift()
      if (cache.has(key)) {
        if (keys.length) {
          const sub = cache.get(key)
          const ret = remove(sub, keys)
          if (sub.size === 0) cache.delete(key)
          return ret
        } else {
          return cache.delete(key)
        }
      }
      return false
    }
    return remove(this.mapper, keys)
  }
}

/**
 * @template {Array} P
 * @template R
 * @param {(...args: P) => R} fn
 * @param {number} cacheSize
 * @returns {(...args: P) => R}
 */
function memoize(fn, cacheSize) {
  const cache = new LRUCache(cacheSize)
  return (...args) => {
    const cached = cache.get(args)
    if (cached === cache.kNotFound) {
      const ret = fn(...args)
      cache.set(args, ret)
      return ret
    }
    return cached
  }
}
