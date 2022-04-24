# `Object.hasOwn` 与 `Object.prototype.hasOwnProperty` 之区别

## 摘要

`Object.hasOwn`与`Object.prototype.hasOwnProperty`都用以判断某属性是否为某对象的自有属性。`Object.prototype.hasOwnProperty`的浏览器兼容性更好，但更推荐使用`Object.hasOwn`。

## 函数签名

函数签名摘自`TypeScript 4.6.3`。

```ts
interface ObjectConstructor {
  /**
   * Determines whether an object has a property with the specified name.
   * @param o An object.
   * @param v A property name.
   */
  hasOwn(o: object, v: PropertyKey): boolean
}

interface Object {
  /**
   * Determines whether an object has a property with the specified name.
   * @param v A property name.
   */
  hasOwnProperty(v: PropertyKey): boolean
}
```

## 使用

```js
Object.hasOwn(instance, prop)
instance.hasOwnProperty(prop)
```

参数：

- `instance`：要判断的对象。
- `prop`：要判断的属性名，类型为`string`或`symbol`。

返回值：

如果`prop`直接定义在`instance`中，则返回`true`，否则返回`false`。

## 描述

这两个方法都用于测试某个属性是否为某个对象的自有属性，而无论该属性的值为何。如果该属性是原型链上的属性，或没有定义，则返回`false`。与`in`运算符不同，`hasOwn`不会检查`instance`的原型链。

由于 Javascript 中大部分对象都是`Object`的派生，这两个方法可以用于绝大多数的 Javascript 对象。但在某些情况下，`Object.prototype.hasOwnProperty`的行为可能会与`Object.hasOwn`的行为不同：

- 对象重写了`hasOwnProperty`方法
- 对象的原型为`null`

因此，推荐使用`Object.hasOwn`。

另外，这两个属性并不尊重`enumerable`属性，即使该属性为`false`，也会被认为是自有属性。

在老版本浏览器中，可用`Object.prototype.hasOwnProperty.call`代替`Object.hasOwn`。

## 示例

示例摘自 MDN。

```js
let example = {}
example.hasOwnProperty('prop')
Object.hasOwn(example, 'prop') // false = 'prop' 未定义

example.prop = 'exists'
example.hasOwnProperty('prop')
Object.hasOwn(example, 'prop') // true - 'prop' 已经定义

example.prop = null
example.hasOwnProperty('prop')
Object.hasOwn(example, 'prop') // true - 'prop' 已经定义，值为null

example.prop = undefined
example.hasOwnProperty('prop')
Object.hasOwn(example, 'prop') // true - 'prop' 已经定义，值为undefined

example.hasOwnProperty('toString')
Object.hasOwn(example, 'toString') // false
example.hasOwnProperty('hasOwnProperty')
Object.hasOwn(example, 'hasOwnProperty') // false

let foo = {
  hasOwnProperty: function () {
    return false
  },
  bar: 'The dragons be out of office'
}

foo.hasOwnProperty('bar') // false
Object.hasOwn(foo, 'bar') // true

let bar = Object.create(null)
bar.prop = 'exists'
bar.hasOwnProperty('prop') // Uncaught TypeError: bar.hasOwnProperty is not a function
Object.hasOwn(bar, 'prop') // true
```
