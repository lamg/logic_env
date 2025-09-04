#r "nuget: FsHttp"
open FsHttp

// {
//   "txns": [
//     ""
//   ],
//   "accounts": [],
//   "apps": [],
//   "latest-timestamp": 0,
//   "protocol-version": "string",
//   "round": 0,
//   "sources": [
//     {
//       "app-index": 0,
//       "field-name": "lsig",
//       "source": "dup\nint 1234\neq\nbz L0\nint 1\nb L1\nlabel L0\nint 0\nlabel L1",
//       "txn-index": 0
//     }
//   ]
// }

let authToken = String.replicate 64 "a"
printfn $"{authToken}"

http {
    POST "http://localhost:4001/v2/teal/compile"
    header "X-Algo-API-Token" authToken
    body

    jsonSerialize
        {| txns = [ "" ]
           accounts = []
           apps = []
           ``latest-timestamp`` = 0
           ``protocol-version`` = "future"
           round = 0
           sources =
            [ {| ``app-index`` = 0
                 ``field-name`` = "lsig"
                 source = "#pragma version 2\nint 1234\ndup\n==\nbz L0\nint 1\nb L1\nL0:\nint 0\nL1:"
                 ``txn-index`` = 0 |} ] |}
}
|> Request.send
|> Response.print

// curl -X POST "http://localhost:4001/v2/teal/dryrun" \
//   -H "Content-Type: application/json" \
//   -H "Accept: application/json" \
//   -H "X-Algo-API-Token: aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" \
//   -d '{
//     "accounts": [],
//     "apps": [],
//     "latest-timestamp": 0,
//     "protocol-version": "future",
//     "round": 0,
//     "sources": [
//       {
//         "field-name": "lsig",
//         "source": "#pragma version 2\narg_0\ndup\nbyte 0x04D2\n==\nbz L0\nint 1\nb L1\nL0:\nint 0\nL1:",
//         "txn-index": 0
//       }
//     ],
//     "txns": []
//   }'
