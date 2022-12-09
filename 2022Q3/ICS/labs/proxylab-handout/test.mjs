import HttpsProxyAgent from 'https-proxy-agent'
import fetch from 'node-fetch'

const agent = new HttpsProxyAgent('http://127.0.0.1:6677')

const resp = await fetch('https://www.baidu.com', {
  agent
})

const text = await resp.text()
console.log(resp.status, text)
