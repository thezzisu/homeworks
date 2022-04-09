# Implementation of memoize

## LRUCache

```
Data flow: (args : any[]) -- mapper -> (k : symbol) -- cache -> cachedValue
Public methods: get(keys), set(keys, val), delete(keys)
Time complexity: O(1) for all methods
Edge cases:
  - symbol in keys: supported!
  - null in keys: supported!
  - undefined in keys: supported!
  - null / undefined in value: supported!
```

## memoize

```
Data flow: (args : any[])  -- in cache -> cachedValue
                           |- not in cache -> evaluate, store and return
Edge cases:
  - symbol in args: supported!
  - null in args: supported!
  - undefined in args: supported!
  - null / undefined in return value: supported!

Typing: supported!
```
