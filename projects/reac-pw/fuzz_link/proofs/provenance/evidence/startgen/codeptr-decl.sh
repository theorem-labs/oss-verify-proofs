# codeptr declarations of reac-pw/fuzz_link image A (each read from the generated file's own slot; see codeptr.*.out)
DECL=(
  --same '0x10800=__global_pointer$ (gp) of both images, 0x10800 in link.asan and libreac/fuzz_pcap.asan'
  --not-address '0x10101=the 4-byte VALUE of a flags cell the collector read (bytes 1,1,1,0), not an address'
  --not-address '0x1ffff=KRange bound 131071 = 2^17 - 1 on a symbolic index, not an address'
  --not-address '0x445c0=KRange bound 280000 on a symbolic count, not an address'
  --not-address '0x71c00=KDisj length 465920 bytes, not an address'
  --not-address '0x100000=KDisj length 1 MiB, not an address'
  --not-address '0x100018=KDisj length 1048600 bytes, not an address'
  --not-address '0x20112d=KRange bound 2101549 on a symbolic value, not an address'
  --not-address '0x38e000=KDisj length 3727360 bytes, not an address'
  --not-address '0x3b0000=a_eager byte count 3866624 of the allocator mapping, not an address'
  --not-address '0x3fffff=KRange bound 4194303 = 2^22 - 1 on a symbolic value, not an address'
  --not-address '0x20000=KDisj length 131072 bytes in a hand-off state, not an address'
  --not-address '0x161200=KDisj length 1446400 bytes in a hand-off state, not an address'
  --same '0x10310=AE3i chunk start right after the owned 8-byte cell (0x10308, 8) of the Tfib_owned_static of link.asan (.rodata); libreac/fuzz_pcap also owns a cell (0x10308, 8), hence the same number'
)
