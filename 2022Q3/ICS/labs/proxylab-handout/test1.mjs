import { connect } from 'net'

const s = connect(6677, '127.0.0.1')
s.write('GET http://www.baidu.com HTTP/1.1\r\n')
s.write('\r\n')
let str = ''
s.on('data', (data) => (str += data.toString()))
s.on('end', () => console.log(str))
