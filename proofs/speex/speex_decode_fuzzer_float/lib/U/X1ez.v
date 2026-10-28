(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho X1hm.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import UbDec.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.

Section C.
Context {RCEIL : RunCeiling}.
Variables (q : Z) (m : mem).
Variables xra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word.

Definition scanj_post (i rp : Z) : machine_state -> Prop :=
fun ms' => exists (mi mj : Z) (t0 t1 t2 a7 t3 t4 t5 : word) (G' : bvmap 5 word) (fc' : bv 32),
ms' = MS (mkR xra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 i) (Z_to_bv 64 q)
(Z_to_bv 64 mi) (Z_to_bv 64 28) (Z_to_bv 64 4) (Z_to_bv 64 rp) (Z_to_bv 64 mj) a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
G' (Z_to_bv 64 0x24d9c) fc' None m (seg_rom rsegs)
/\ frm0 fc' /\ 0 <= mi <= 3 /\ 0 <= mj <= 6.

#[using="Type"] Lemma scanj : forall (k : nat) (crest : list word) (i rp cq j mi mj : Z) (cw t5 : word) (G : bvmap 5 word) (fc : bv 32),
length crest = k -> j + Z.of_nat k = 6 -> 0 <= j -> cq = rp + 4 * j -> 0 <= rp ->
0 <= i <= 3 -> 0 <= mi <= 3 -> 0 <= mj <= 6 ->
frm0 fc -> mem_inv rsegs m -> rw_cells rsegs m cq (f32 (cw :: crest)) ->
evt rsegs (scanj_post i rp)
(MS (mkR xra (Z_to_bv 64 q) gp tp (Z_to_bv 64 (4 * j)) (Z_to_bv 64 (18446744073709551615 - rp)) (Z_to_bv 64 cq) s0 s1 (Z_to_bv 64 i) (Z_to_bv 64 q)
(Z_to_bv 64 mi) (Z_to_bv 64 28) (Z_to_bv 64 4) (Z_to_bv 64 rp) (Z_to_bv 64 mj) (Z_to_bv 64 j)
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 mj) (Z_to_bv 64 mi) t5 t6)
G (Z_to_bv 64 0x24d5c) fc None m (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros crest i rp cq j mi mj cw u5 G fc LC Hj Hj0 Hcq Hrp Hi Hmi Hmj FRM MI CW;
pose proof (rw_cells_bound _ _ _ _ CW) as BC; rewrite cells_size_f32 in BC; cbn [length] in BC.
- destruct crest; [|cbn in LC; lia]. cbn [Z.of_nat] in Hj. rewrite f32_cons, f32_nil in CW.
zstep. ub_dec. do 5 zstep. if_cases B; bfact B.
+ do 6 zstep. rewrite swrap32_small by lia. zstep. if_false_x.
apply evt_done; unfold scanj_post. exists i, j. sf_eexists 9%nat. split; [reflexivity|]. repeat split; try assumption; lia.
+ do 9 zstep. rewrite swrap32_small by lia. zstep. if_false_x.
apply evt_done; unfold scanj_post. exists mi, mj. sf_eexists 9%nat. split; [reflexivity|]. repeat split; try assumption; lia.
- destruct crest as [|cw' crest]; [cbn in LC; lia|]. cbn [length] in LC, BC. rewrite !f32_cons in CW.
zstep. ub_dec. do 5 zstep. if_cases B; bfact B.
+ do 6 zstep. rewrite swrap32_small by lia. zstep. if_true_x.
rewrite <- !f32_cons in CW. apply rw_cells_uncons in CW as [_ CW]. cbn [csize Z.of_nat Pos.of_succ_nat Pos.succ] in CW.
replace (4 * j + 4) with (4 * (j + 1)) by lia.
eapply (IH crest i rp (cq + 4) (j + 1) i j cw'); [lia|lia|lia|lia|lia|lia|lia|lia| assumption | exact MI | exact CW].
+ do 9 zstep. rewrite swrap32_small by lia. zstep. if_true_x.
rewrite <- !f32_cons in CW. apply rw_cells_uncons in CW as [_ CW]. cbn [csize Z.of_nat Pos.of_succ_nat Pos.succ] in CW.
replace (4 * j + 4) with (4 * (j + 1)) by lia.
eapply (IH crest i rp (cq + 4) (j + 1) mi mj cw'); [lia|lia|lia|lia|lia|lia|lia|lia| assumption | exact MI | exact CW].
Qed.

Definition amax_post : machine_state -> Prop :=
fun ms' => exists (mi mj : Z) (t0 t1 t2 a7 t3 t4 t5 : word) (G' : bvmap 5 word) (fc' : bv 32),
ms' = MS (mkR xra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 4) (Z_to_bv 64 q)
(Z_to_bv 64 mi) (Z_to_bv 64 28) (Z_to_bv 64 4) (Z_to_bv 64 (q + 112)) (Z_to_bv 64 mj) a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
G' (Z_to_bv 64 0x24da8) fc' None m (seg_rom rsegs)
/\ frm0 fc' /\ 0 <= mi <= 3 /\ 0 <= mj <= 6.

#[using="Type"] Lemma scani : forall (k : nat) (rows : list word) (i rp mi mj : Z) (t0 t1 t2 a7 t3 t4 t5 : word) (G : bvmap 5 word) (fc : bv 32),
length rows = (7 * k)%nat -> i + Z.of_nat k = 4 -> 0 <= i -> (1 <= k)%nat -> rp = q + 28 * i ->
0 <= mi <= 3 -> 0 <= mj <= 6 ->
frm0 fc -> mem_inv rsegs m -> rw_cells rsegs m rp (f32 rows) ->
evt rsegs amax_post
(MS (mkR xra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 i) (Z_to_bv 64 q)
(Z_to_bv 64 mi) (Z_to_bv 64 28) (Z_to_bv 64 4) (Z_to_bv 64 rp) (Z_to_bv 64 mj) a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
G (Z_to_bv 64 0x24d30) fc None m (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros rows i rp mi mj t0 t1 t2 a7 t3 u4 u5 G fc LR Hik Hi0 Hk Hrp Hmi Hmj FRM MI R; [lia|].
pose proof (rw_cells_bound _ _ _ _ R) as BR; rewrite cells_size_f32, LR in BR.
destruct rows as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 [|w6 rest]]]]]]]; try (cbn in LR; lia). cbn [length] in LR.
destruct (f32_split rsegs m rp (w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: rest) 7%nat ltac:(cbn [length]; lia) R) as [RW RT]. cbn [firstn skipn] in RW, RT.
change (4 * Z.of_nat 7) with 28 in RT.
do 11 zstep.
lazymatch goal with |- context [Z.lxor ?x 18446744073709551615] =>
replace (Z.lxor x 18446744073709551615) with (18446744073709551615 - rp);
[| rewrite zb_lxor_ones; rewrite ?Z.shiftl_mul_pow2 by lia; rewrite ?(Z.mod_small (i * 2 ^ 5)), ?(Z.mod_small (i * 2 ^ 2)) by lia; rewrite ?Z.mod_small by lia; lia]
end.
lazymatch goal with |- evt _ _ (MS _ ?G0 _ ?fc0 _ _ _) =>
eapply evt_cut; [eapply (scanj 6%nat [w1; w2; w3; w4; w5; w6] i rp rp 0 mi mj w0 _ G0 fc0);
[reflexivity | cbn; lia | lia | lia | lia | lia | lia | lia | exact FRM | exact MI | exact RW] | ]
end.
clear FRM. intros ms' PO; first [ sf_destruct 15%nat PO as mi' mj' t0' t1' t2' a7' t3' t4' t5' G' fc' -> FRM Hmi' Hmj' | sf_fb; destruct PO as (mi' & mj' & t0' & t1' & t2' & a7' & t3' & t4' & t5' & G' & fc' & -> & FRM & Hmi' & Hmj') ].
destruct k as [|k'].
- cbn [length Nat.mul Nat.add] in LR. destruct rest; [|cbn in LR; lia]. change (Z.of_nat 1) with 1 in Hik.
do 3 zstep. if_false_x. replace (i + 1) with 4 by lia. replace (rp + 28) with (q + 112) by lia.
apply evt_done; unfold amax_post. exists mi', mj'. sf_eexists 9%nat. split; [reflexivity|].
repeat split; try assumption; lia.
- do 3 zstep. if_true_x.
eapply (IH rest (i + 1) (rp + 28) mi' mj'); [lia|lia|lia|lia|lia|lia|lia| exact FRM | exact MI | exact RT].
Qed.

#[using="Type"] Lemma amax : forall (c : list word) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 : word) (G : bvmap 5 word) (fc : bv 32),
length c = 28%nat -> frm0 fc -> mem_inv rsegs m -> rw_cells rsegs m q (f32 c) ->
evt rsegs amax_post
(MS (mkR xra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
G (Z_to_bv 64 0x24d10) fc None m (seg_rom rsegs)).
Proof.
intros c t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 G fc LC FRM MI C.
pose proof (rw_cells_bound _ _ _ _ C) as BC; rewrite cells_size_f32, LC in BC.
destruct c as [|c0 c']; [cbn in LC; lia|]. rewrite f32_cons in C.
do 8 zstep. rewrite <- f32_cons in C.
eapply (scani 4%nat (c0 :: c') 0 q 0 0); [exact LC | reflexivity | lia | lia | lia | lia | lia | | exact MI | exact C]. assumption.
Qed.
End C.
