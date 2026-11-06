(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/YImgTop.v at origin/ossv/recipes 6ebe35ba632 (fuzz_knock's released ASan tree); module paths changed to reac-pw/fuzz_rate. *)
From Stdlib Require Import ZArith.
Local Open Scope Z_scope.

(* The NOTATION form of libreac/fuzz_scene's and fuzz_identity's YImgTop.v, which the scene-route A layer is written in:
   its `unfold ... off_img` sites then call lia, and lia cannot see through a Definition. Both values are this unit's own
   image (measured below). *)
Notation IMG_LO := 0x10000%Z (only parsing).
(* IMG_TOP = page_up of the end of the last PT_LOAD (vaddr + memsz), the same in both ASan pins of reac-pw/fuzz_rate:
   fuzz_rate.asan (sha256 22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a) ends at 0x5f94b0 (last
   PT_LOAD vaddr 0x9db68 + memsz 0x55b948) and fuzz_rate.asan-ubsan (sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14) at 0x5f97b0 (0x9de68 + 0x55b948); both page_up to
   0x5fa000. fuzz_knock's (and fuzz_qdisc's) value was 0x5f3000, reac-pw/fuzz_role's 0x5f8000. *)
Notation IMG_TOP := 0x5fa000%Z (only parsing).
