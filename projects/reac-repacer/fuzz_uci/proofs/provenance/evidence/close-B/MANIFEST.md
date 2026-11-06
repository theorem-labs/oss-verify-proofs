# provenance/evidence/close-B: fuzz_uci image-B composition lib/B/UciBClose.v

Written by scripts/mk_slice_manifest.py; not edited by hand. Start with RECORD.md.

| path | role | sha256 |
|---|---|---|
| `RECORD.md` | the record: the 18 rows with file:line and status, build, Print Assumptions, measurements | `81f74a3c49ab730df1aab590b0d5e920a6822e75fd3561281659d71f2f2b703e` |
| `env.example.sh` | every variable run.sh reads, without values | `143fbaee2df5366b77f5d8fd30049c94990ba58448f99d95e140e92f868670f3` |
| `images.sha256` | sha256 of every image read | `8dd945dbd391b4c3e419ac625a0fda5fbb35fe6e8df3f66ec9781c549b81d463` |
| `records/build.txt` | the build of record: mode, pins, targets, rc, About / Print Assumptions | `ee6b07c2d9e65b40eb0f08a3511bf2966d386b9302ce92625954d9a387a6f62f` |
| `run.sh` | reruns every measurement and rewrites tables/, records/, RECORD.md and MANIFEST.md | `b8240359c26e88a9e817331e776058a76d28577eced23f23169189bcbed603f1` |
| `scripts/cells.py` | runtime cells, GOT words and REAL values of one image | `226ff1db04a786e20217e349df74bb938544fb0143a808db5f998f757d9a8f6e` |
| `scripts/dis_rv64.py` | listings, UBSan trap branches and s0 writes of the six program functions | `9cf250fe305995e7823df72b203dc8f71b2fd28c810bdb33edde376208c54ceb` |
| `scripts/mk_record.py` | writes records/build.txt and RECORD.md | `68b2179e03676cb1f6484d79dc72a1c74086fa451497db24b0310a1954fbf564` |
| `scripts/mk_slice_manifest.py` | this writer | `21a85ce3f46fcd56d868f447719cbefbceb492242c670063b02bf1a0d155a39f` |
| `tables/cells-A.txt` | runtime cells of one image | `1b3f51866bcbbec3bef392b24a0180488c4d9ee095575cbcbd94228fb37481ec` |
| `tables/cells-B.txt` | runtime cells of one image | `c636cd78439246a3c252b80da2e2d4c1ac418030c3312f4e7fc1fc545b5cdfe0` |
| `tables/dis-A.txt` | listing of the six program functions of one image | `439330fc3887219371f0db99586834236cc6ab1b079c562fad82cae2d0fcdd58` |
| `tables/dis-B.txt` | listing of the six program functions of one image | `9cf15e8f3e12c534bd34d1f2764e83e4cc5f06c1420462a74e6602a7e7b85247` |
| `tables/s0-writes-A.txt` | s0 writes in the three call-context functions of one image | `19edf5edfa95751aad93612a4f5022e391231cbfbd0a3bd77c4af5856984e420` |
| `tables/s0-writes-B.txt` | s0 writes in the three call-context functions of one image | `009ab3f62f2e61e3399a77b03f87c333008dcc16011e077eee4b76df7d298e03` |
| `tables/ubsan-traps-A.txt` | branches to UBSan's unimp in the six program functions of one image | `13e2ee9ce694710e29ec3a62f457f0eea106ae66a327a21ad3191e6dd451115c` |
| `tables/ubsan-traps-B.txt` | branches to UBSan's unimp in the six program functions of one image | `771bb746a3e4ef97028719e8c0b6594edf48103095d56eb5f2de13dfd318d8fe` |
