(* The image end of this unit's ASan binary, fuzz_manifest.asan: the end of its last PT_LOAD (the RW segment,
   vaddr 0x9b000, memsz 0x55c000), page aligned. These files state the image end through this name: off_img in
   Reusable/YCbq.v and Reusable/YCe5.v, TFIB_IMG_END in A/ACeg.v and A/AF0x.v. Other relocated files still state the
   number 0x5f7000 (6254592) directly (A/AB12, AB13, AB1w, AD1e, AD1f, AD1g, AD1j, AD1o and others); a port to another
   binary must change those too. A parsing-only notation, so every proof sees the number itself. *)
From Stdlib Require Import ZArith.
Notation ASAN_IMG_END := 0x5f7000%Z (only parsing).
