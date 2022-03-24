// @ts-check
const out = document.createElement('div')
out.classList.add('z-result-wrapper')

/**
 * DFS the dom tree and generate output
 * @param {Element} node
 * @returns {Element[]}
 */
function dfs(node) {
  const children = [...node.children]
  if (children.length) {
    const li = document.createElement('li')
    li.classList.add('z-result-li')
    li.textContent = `${node.tagName}`
    const ol = document.createElement('ol')
    ol.classList.add('z-result-ol')
    children
      .map((child) => dfs(child))
      .flat()
      .forEach(ol.appendChild.bind(ol))
    return [li, ol]
  } else {
    const li = document.createElement('li')
    li.classList.add('z-result-li')
    li.textContent = `${node.tagName}`
    return [li]
  }
}

dfs(document.querySelector('html')).forEach(out.appendChild.bind(out))
document.body.appendChild(out)

// inject css
const style = document.createElement('style')
style.textContent = `
.z-result-wrapper {
  margin: 32px;
  padding: 32px;
  border: 1px solid #ccc;
}
.z-result-ol {
  padding-inline-start: 40px;
  list-style: decimal-leading-zero;
}
`
document.head.appendChild(style)
