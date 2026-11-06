(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1cg X1df X1ck X1co.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X05l.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation mem := (word -> option byte).

Section C.
Variables (cq : Z) (m : mem).
Variables xra sp gp tp s0 s1 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word.
Hypothesis CQR : 0 <= cq /\ cq + 112 < 2 ^ 63.

Definition scanj_post (i rp re : Z) : machine_state -> Prop :=
fun ms' => exists (mi mj : Z) (t1 t2 : word) (G' : bvmap 5 word) (fc' : bv 32),
ms' = MS (mkR xra sp gp tp (Z_to_bv 64 mj) t1 t2 s0 s1 (Z_to_bv 64 i) (Z_to_bv 64 4) (Z_to_bv 64 mi) (Z_to_bv 64 rp)
(Z_to_bv 64 mj) (Z_to_bv 64 7) (Z_to_bv 64 re) (Z_to_bv 64 re)
s2 s3 s4 (Z_to_bv 64 cq) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
G' (Z_to_bv 64 0xa5c4c) fc' None m (seg_rom asegs)
/\ frm0 fc' /\ 0 <= mi <= 3 /\ 0 <= mj <= 6.

Lemma scanj : forall (k : nat) (crest : list word) (i rp ca re j mi mj : Z) (cw t1 t2 : word) (G : bvmap 5 word) (fc : bv 32),
length crest = k -> j + Z.of_nat k = 6 -> 0 <= j -> ca = rp + 4 * j -> re = rp + 28 -> rp = cq + 28 * i ->
0 <= i <= 3 -> 0 <= mi <= 3 -> 0 <= mj <= 6 ->
frm0 fc -> mem_inv asegs m -> rw_cells asegs m ca (f32 (cw :: crest)) ->
evt asegs (scanj_post i rp re)
(MS (mkR xra sp gp tp (Z_to_bv 64 mj) t1 t2 s0 s1 (Z_to_bv 64 i) (Z_to_bv 64 4) (Z_to_bv 64 mi) (Z_to_bv 64 rp)
(Z_to_bv 64 mj) (Z_to_bv 64 j) (Z_to_bv 64 re) (Z_to_bv 64 ca)
s2 s3 s4 (Z_to_bv 64 cq) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
G (Z_to_bv 64 0xa5c10) fc None m (seg_rom asegs)).
Proof.
induction k as [|k IH]; intros crest i rp ca re j mi mj cw t1 t2 G fc LC Hj Hj0 Hca Hre Hrp Hi Hmi Hmj FRM MI CW;
pose proof (rw_cells_bound _ _ _ _ CW) as BC; rewrite cells_size_f32 in BC; cbn [length] in BC.
- destruct crest; [|cbn in LC; lia]. cbn [Z.of_nat] in Hj. rewrite f32_cons, f32_nil in CW.
do 4 astep. if_cases B; bfact B.
+ do 2 astep. rewrite B. if_true. do 6 astep. rewrite Z.add_0_r, swrap32_small by lia. sh_if.
replace (ca + 4) with re by lia. replace (j + 1) with 7 by lia.
apply evt_done; unfold scanj_post. exists i, j. do 4 eexists. split; [reflexivity|]. repeat split; try assumption; lia.
+ do 4 astep. rewrite B. if_false. do 7 astep. rewrite Z.add_0_r, swrap32_small by lia. sh_if.
replace (ca + 4) with re by lia. replace (j + 1) with 7 by lia.
apply evt_done; unfold scanj_post. exists mi, mj. do 4 eexists. split; [reflexivity|]. repeat split; try assumption; lia.
- destruct crest as [|cw' crest]; [cbn in LC; lia|]. cbn [length] in LC, BC. rewrite !f32_cons in CW.
do 4 astep. if_cases B; bfact B.
+ do 2 astep. rewrite B. if_true. do 6 astep. rewrite Z.add_0_r, swrap32_small by lia. sh_if.
rewrite <- !f32_cons in CW. apply rw_cells_uncons in CW as [_ CW]. cbn [csize Z.of_nat Pos.of_succ_nat Pos.succ] in CW.
eapply (IH crest i rp (ca + 4) re (j + 1) i j cw'); [lia|lia|lia|lia|lia|lia|lia|lia|lia| assumption | exact MI | exact CW].
+ do 4 astep. rewrite B. if_false. do 7 astep. rewrite Z.add_0_r, swrap32_small by lia. sh_if.
rewrite <- !f32_cons in CW. apply rw_cells_uncons in CW as [_ CW]. cbn [csize Z.of_nat Pos.of_succ_nat Pos.succ] in CW.
eapply (IH crest i rp (ca + 4) re (j + 1) mi mj cw'); [lia|lia|lia|lia|lia|lia|lia|lia|lia| assumption | exact MI | exact CW].
Qed.

Definition amax_post : machine_state -> Prop :=
fun ms' => exists (mi mj : Z) (t0 t1 t2 a3 a5 a6 a7 : word) (G' : bvmap 5 word) (fc' : bv 32),
ms' = MS (mkR xra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 4) (Z_to_bv 64 4) (Z_to_bv 64 mi) a3
(Z_to_bv 64 mj) a5 a6 a7
s2 s3 s4 (Z_to_bv 64 cq) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
G' (Z_to_bv 64 0xa5c58) fc' None m (seg_rom asegs)
/\ frm0 fc' /\ 0 <= mi <= 3 /\ 0 <= mj <= 6.

Lemma scani : forall (k : nat) (rows : list word) (i rp mi mj : Z) (t0 t1 t2 a5 a6 a7 : word) (G : bvmap 5 word) (fc : bv 32),
length rows = (7 * k)%nat -> i + Z.of_nat k = 4 -> 0 <= i -> (1 <= k)%nat -> rp = cq + 28 * i ->
0 <= mi <= 3 -> 0 <= mj <= 6 ->
frm0 fc -> mem_inv asegs m -> rw_cells asegs m rp (f32 rows) ->
evt asegs amax_post
(MS (mkR xra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 i) (Z_to_bv 64 4) (Z_to_bv 64 mi) (Z_to_bv 64 rp)
(Z_to_bv 64 mj) a5 a6 a7
s2 s3 s4 (Z_to_bv 64 cq) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
G (Z_to_bv 64 0xa5bec) fc None m (seg_rom asegs)).
Proof.
induction k as [|k IH]; intros rows i rp mi mj t0 t1 t2 a5 a6 a7 G fc LR Hik Hi0 Hk Hrp Hmi Hmj FRM MI R; [lia|].
pose proof (rw_cells_bound _ _ _ _ R) as BR; rewrite cells_size_f32, LR in BR.
destruct rows as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 [|w6 rest]]]]]]]; try (cbn in LR; lia). cbn [length] in LR.
destruct (f32_split asegs m rp (w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: rest) 7%nat ltac:(cbn [length]; lia) R) as [RW RT]. cbn [firstn skipn] in RW, RT.
change (4 * Z.of_nat 7) with 28 in RT.
do 9 astep.
lazymatch goal with |- evt _ _ (MS _ ?G0 _ ?fc0 _ _ _) =>
eapply evt_cut; [eapply (scanj 6%nat [w1; w2; w3; w4; w5; w6] i rp rp _ 0 mi mj w0 _ _ G0 fc0);
[reflexivity | cbn; lia | lia | lia | rewrite !Z.shiftl_mul_pow2, ?Z.mod_small by lia; lia | lia | lia | lia | lia | exact FRM | exact MI | exact RW] | ]
end.
clear FRM. intros ms' (mi' & mj' & t1' & t2' & G' & fc' & -> & FRM & Hmi' & Hmj').
destruct k as [|k'].
- cbn [length Nat.mul Nat.add] in LR. destruct rest; [|cbn in LR; lia]. change (Z.of_nat 1) with 1 in Hik.
do 3 astep. sh_if. replace (i + 1) with 4 by lia.
apply evt_done; unfold amax_post. exists mi', mj'. do 9 eexists. split; [reflexivity|].
repeat split; try assumption; lia.
- do 3 astep. sh_if.
eapply (IH rest (i + 1) (rp + 28) mi' mj'); [lia|lia|lia|lia|lia|lia|lia| exact FRM | exact MI | exact RT].
Qed.

Lemma amax : forall (c : list word) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 : word) (G : bvmap 5 word) (fc : bv 32),
length c = 28%nat -> frm0 fc -> mem_inv asegs m -> rw_cells asegs m cq (f32 c) ->
evt asegs amax_post
(MS (mkR xra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 cq) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
G (Z_to_bv 64 0xa5bd4) fc None m (seg_rom asegs)).
Proof.
intros c t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 G fc LC FRM MI C.
pose proof (rw_cells_bound _ _ _ _ C) as BC; rewrite cells_size_f32, LC in BC.
destruct c as [|c0 c']; [cbn in LC; lia|]. rewrite f32_cons in C.
do 6 astep. rewrite <- f32_cons in C.
eapply (scani 4%nat (c0 :: c') 0 cq 0 0); [exact LC | reflexivity | lia | lia | lia | lia | lia | | exact MI | exact C]. assumption.
Qed.
End C.
