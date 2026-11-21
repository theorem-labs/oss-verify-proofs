(* SPDX-License-Identifier: MIT *)
(* The fresh-variable renumbering of the A and B driver layers (lib/A/AD1*, AD2*, AWH8 and their B twins)
   at LPS 727298f3: the variables those files name in the hand-off states, old number -> new number.

   Read, not chosen: the computed hand-off states of A/AB01r.v and B/AB01r.v were compared with the recorded
   ones of A/AB01.v and B/AB01.v.  One run (probes A/ZZ_boxdrv.v, B/ZZ_boxdrvB.v, markers
   ZZD_R0, ZZDB_R0) printed the hand-off maps side by side: 4096 * EVar {518, 501, 500, 441, 424, 292, 275,
   274, 273, 255, 254, 109} became the same plus 4 below 293 and plus 6 above 356, EVar 357 became 363 and the
   ghost page 358 became 364.  A second run (probe B/ZZ_boxdrv2B.v, markers ZZEB_HOLE, ZZEB_IF,
   ZZEB_OTHER, ZZEB_ENTRY) ran the recorded drivers' computed checks (hole_chk, if_chk, avis_chk, kz_chk, the
   image-shadow check, finv_check, avis8_chk, and entry_check's TIDV range and register table) on the 20
   computed states with every variable mapped back by the inverse of [dsh]: all held.  Below 9 nothing moves;
   the launch's V_G took 9 and moved V_HW to 10 (YA01). *)
From Stdlib Require Import Arith List.
Import ListNotations.
Definition dsh (v : nat) : nat :=
if Nat.ltb v 9 then v else if Nat.eqb v 9 then 10
else if Nat.ltb v 357 then v + 4 else v + 6.
(* every variable number the driver files name, and its image *)
Lemma dsh_driver_literals :
map dsh [43; 60; 109; 254; 255; 256; 273; 274; 275; 292; 357; 358; 391; 424; 500; 501; 518]
= [47; 64; 113; 258; 259; 260; 277; 278; 279; 296; 363; 364; 397; 430; 506; 507; 524].
Proof. reflexivity. Qed.
