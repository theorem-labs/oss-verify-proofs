(* The loaded image range of the fuzz_ctrl asan-ubsan build (build B), [IMG_LO, IMG_HI), libreac v1.9.0: the PT_LOAD
   segments of fuzz_ctrl.asan-ubsan run from 0x10000 to 0x5fdf30, page-rounded up to 0x5fe000 (= RT_GT in lib/B/AsanRT.v,
   the last region end of lib/B/ZImage.v). Relocated from fuzz_pcap's lib/B/Prog/ImgBounds.v
   (a working branch 0ce4d3317ea), whose image ends at 0x5f7000. *)
From Stdlib Require Import ZArith.
Local Open Scope Z_scope.

Definition IMG_LO : Z := 0x10000.
Definition IMG_HI : Z := 0x5fe000.
