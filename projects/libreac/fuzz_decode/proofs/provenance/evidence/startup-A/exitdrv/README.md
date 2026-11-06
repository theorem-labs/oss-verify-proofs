# exitdrv/: the exit-driver record of libreac/fuzz_decode (image A)

This directory holds the exit-driver record `EXITDRV.md`, the stdout of the run that wrote the four exit-driver files
(`exitdrv.run2.out`), and three run outputs beside them. `COPY.md` says how each file relates to its original (the
copies are equal to the source apart from named tokens for names and work-directory paths) and how `copycheck.py`
proves it.

## One record for both images

The same record covers both images: in its section 5 (and in `exitdrv.run2.out`), the decode.asan column is image A
(`lib/A/AE23.v`, `lib/A/AD1y.v`) and the decode.asan-ubsan column is image B (`lib/B/YE23.v`, `lib/B/YD1y.v`). Image B's
copy of the record is `../../startup-B/exitdrv/`.

## Erratum (image B)

Record row DEC 0x5f9920 -> 0x5f49e0 (buf, 8) for image B is WRONG; the shipped YE23 uses STDOUT_BUFA = 0x5f49e8
(lib/B/YE3m.v:34, since b5a5f994474f), and the B pin holds 0x5f49e8 at __stdout_FILE+0x58 (measured: the command
below). The row is line 81 of `exitdrv.run2.out` (`EXITDRV.md` section 5 has no DEC row). The same row's image-A value,
0x5f4468, is what the A pin holds at its __stdout_FILE+0x58.

Measured (`<pin>`: the pinned image; the second argument: __stdout_FILE + 0x58, with __stdout_FILE = 0x9d9a8 on B and
0x9d400 on A, the record's section 5 DATA row `0xa2668 0xa28d8`). The command prints the pin's sha256 prefix, the
address and the 8 bytes there as read through the pin's PT_LOAD segments:

    python3 -c 'import sys,struct,hashlib;b=open(sys.argv[1],"rb").read();o,e,n=struct.unpack_from("<Q",b,32)[0],struct.unpack_from("<H",b,54)[0],struct.unpack_from("<H",b,56)[0];a=int(sys.argv[2],0);print(hashlib.sha256(b).hexdigest()[:12],hex(a),[hex(int.from_bytes(b[f+a-v:f+a-v+8],"little")) for t,f,v,s in (struct.unpack_from("<I4xQQ8xQ",b,o+i*e) for i in range(n)) if t==1 and v<=a<v+s])' <pin> <address>

    B, <pin> = bin/fuzz_decode/fuzz_decode.asan-ubsan, <address> = 0x9da00:  5d05689fd5b1 0x9da00 ['0x5f49e8']
    A, <pin> = bin/fuzz_decode/fuzz_decode.asan,       <address> = 0x9d458:  5973b76807d8 0x9d458 ['0x5f4468']

The copies keep the wrong value: they stay equal to the source apart from the token spans.

## Where the headers point

Since commit `8529e243afd7` the 4 lib headers cite the record here: a header-only tool (`exitdrv_header.py`
`08ee0e66ac66`, `tools/exitdrv/c4a86fa61d82`) rewrote lines 1 and 5 only. Line 5 of `lib/A/AD1y.v` and `lib/A/AE23.v`
cites `provenance/evidence/startup-A/exitdrv/EXITDRV.md` (this directory), and line 5 of `lib/B/YD1y.v` and
`lib/B/YE23.v` cites `provenance/evidence/startup-B/exitdrv/EXITDRV.md`. Before, they cited the old record locations:
`provenance/startup-gen/A/exitdrv/EXITDRV.md` (prover-only, not shipped) for image A, and the record's path in the
start-up writer's work directory for image B.
