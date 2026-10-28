(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1bu.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho X1hm.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.

Definition EXP_DATA : Z := 0x159e8.

Definition exp_data_bytes : list byte :=
match image_bytes rsegs EXP_DATA 2176 return list byte with Some bs => bs | None => [] end.

Lemma exp_data_len : length exp_data_bytes = 2176%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma exp_data_ro : forall m, mem_inv rsegs m -> ro_cells rsegs m EXP_DATA [CB 2176 exp_data_bytes].
Proof.
intros m MI. apply (ro_cells_image rsegs m); [exact MI | vm_compute; reflexivity | unfold EXP_DATA; lia | rewrite exp_data_len; unfold EXP_DATA; lia].
Qed.

Lemma mod_neg_2p64 : forall z, -2^64 <= z < 0 -> z mod 2^64 = z + 2^64.
Proof. intros z Hz. symmetry. apply (Z.mod_unique_pos z (2^64) (-1)); lia. Qed.

Lemma exp_row : forall m e, mem_inv rsegs m -> 0 <= e < 2048 ->
exists junk w1 w2, ro_cells rsegs m (EXP_DATA + e) [CB 112 junk; C8 w1; C8 w2].
Proof.
intros m e MI He. pose proof (exp_data_ro m MI) as [WF BA].

assert (CBE_ : forall n (l : list byte), cells_bytes [CB n l] = l) by (intros; cbn [cells_bytes cbytes app]; apply app_nil_r). rewrite CBE_ in BA. clear CBE_.
pose proof exp_data_len as L. set (bs := exp_data_bytes) in *.
rewrite <- (firstn_skipn (Z.to_nat e) bs) in BA. apply bytes_at_app in BA as [_ BA].
rewrite firstn_length_le in BA by lia. rewrite Z2Nat.id in BA by lia.
set (rest := skipn (Z.to_nat e) bs) in *.
assert (LR : (length rest >= 128)%nat) by (subst rest; rewrite skipn_length; lia).
rewrite <- (firstn_skipn 112 rest) in BA. apply bytes_at_app in BA as [B1 BA].
rewrite firstn_length_le in BA by lia.
rewrite <- (firstn_skipn 16 (skipn 112 rest)) in BA. apply bytes_at_app in BA as [B2 _].
assert (L16 : length (firstn 16 (skipn 112 rest)) = (8 * 2)%nat) by (rewrite firstn_length_le; [reflexivity|]; rewrite skipn_length; lia).
destruct (bytes_are_C8s 2 _ L16) as (ws & Lws & Ews).
destruct ws as [|w1 [|w2 [|? ?]]]; try (cbn in Lws; lia).
first [ unshelve sf_eexists 3%nat; [ exact ((firstn 112 rest)) | exact (w1) | exact (w2) | ] | sf_fb; exists (firstn 112 rest), w1, w2 ]. split.
- cbn. split; [rewrite firstn_length_le; [reflexivity| lia]|]. exact (conj I (conj I I)).
- cbn [cells_bytes cbytes app]. rewrite app_nil_r. apply bytes_at_app. split; [exact B1|].
rewrite firstn_length_le by lia. cbn [map cells_bytes cbytes app] in Ews. rewrite app_nil_r in Ews. rewrite Ews. exact B2.
Qed.

Section S.
Context {RCEIL : RunCeiling}.
Variables (lo : Z) (m0 : mem).
Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Hypothesis LOW : lo + 16 <= bv_unsigned sp.
Local Notation usp := (bv_unsigned sp).
Local Notation POST := (exp_post lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0).

Ltac finish_exp MU WM MI ST :=
apply evt_done; unfold exp_post;
eexists _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _, _; split; [reflexivity|];
split; [exact MU|]; split; [exact WM|]; split; [exact MI|]; split; [assumption| exact ST].

#[using="LOW"] Lemma exp_sc : forall (t0 t1 t2 xa0 xa1 xa2 xa3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (G : bvmap 5 word) (fc : bv 32) (m : mem),
frm0 fc -> mem_inv rsegs m -> munch [(lo, usp)] m0 m -> wmono rsegs m0 m -> stk rsegs m lo usp ->
evt rsegs POST
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 xa0 xa1 xa2 xa3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
G (Z_to_bv 64 0x33ad4) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros FRM MI MU WM ST.
pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR.
zstep. zstep. if_cases SGN.
all: lazymatch goal with
| |- evt _ _ (MS _ _ (Z_to_bv 64 211712) _ _ _ _) =>

zstep; carve_frame 16%nat ST;
destruct (rw_cells_CB_C8s rsegs _ _ 2%nat _ FR) as (fw2 & Lfw & FR'); clear FR;
destruct fw2 as [|u0 [|u1 [|? ?]]]; cbn in Lfw; try lia; cbn [map] in FR'; rename FR' into FR;
do 10 zstep; if_cases LT1;
[ lazymatch goal with
| |- evt _ _ (MS _ _ (Z_to_bv 64 211832) _ _ _ _) => idtac
| _ => do 11 zstep; if_cases EQ0;
try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 211800) _ _ _ _) => zstep end);
zstep; zstep; lstep; zstep; zstep; zstep; zstep
end .. ];
zstep; zstep; zstep; zstep;
release_frame FR ST (bv_unsigned sp)
| _ =>   do 9 zstep
end.
all: finish_exp MU WM MI ST.
Qed.

#[using="LOW"] Lemma exp_main : forall (va2 : Z) (t0 t1 t2 xa0 xa1 xa3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
0 <= va2 < 2048 ->
frm0 fc -> mem_inv rsegs m -> munch [(lo, usp)] m0 m -> wmono rsegs m0 m -> stk rsegs m lo usp ->
evt rsegs POST
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 xa0 xa1 (Z_to_bv 64 va2) xa3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x339c8) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros Hva2 FRM MI MU WM ST.
pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR.
do 15 zstep.
zstep. zstep. zstep.
set (kdw := fadd_d RNE (fmul_d RNE (Z_to_bv 64 4640701337412797182) (reg_get F 10)) (Z_to_bv 64 4843621399236968448)) in *.
set (e := Z.shiftr (Z.shiftl (bv_unsigned kdw) 57 mod 18446744073709551616) 53) in *.
assert (He : 0 <= e < 2048).
{ subst e. rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.mod_pos_bound (Z.shiftl (bv_unsigned kdw) 57) 18446744073709551616 ltac:(lia)).
split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. change (2 ^ 53 * 2048) with 18446744073709551616. lia. }
first [ pose proof (exp_row m e MI He) as sfP_; sf_destruct 4%nat sfP_ as junk w1 w2 ROW | sf_fb; destruct (exp_row m e MI He) as (junk & w1 & w2 & ROW) ]. unfold EXP_DATA in ROW.
do 13 zstep. clear ROW.
destruct (Z.eq_dec va2 0) as [-> | NZ].
- if_true. zstep. apply exp_sc; assumption.
- replace (bv_eqb (Z_to_bv 64 va2) (Z_to_bv 64 0)) with false by (symmetry; unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
cbv iota. zstep. zstep. zstep. finish_exp MU WM MI ST.
Qed.

#[using="LOW"] Lemma exp_xflow : forall (t0 t1 t2 xa1 xa2 xa3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (G : bvmap 5 word) (fc : bv 32) (m : mem),
frm0 fc -> mem_inv rsegs m -> munch [(lo, usp)] m0 m -> wmono rsegs m0 m -> stk rsegs m lo usp ->
evt rsegs POST
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) xa1 xa2 xa3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
G (Z_to_bv 64 0x33b94) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros FRM MI MU WM ST.
pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR.
zstep. zstep. if_true. zstep. carve_frame 16%nat ST.
destruct (rw_cells_CB_C8s rsegs _ _ 2%nat _ FR) as (fw2 & Lfw & FR'); clear FR.
destruct fw2 as [|u0 [|u1 [|? ?]]]; cbn in Lfw; try lia. cbn [map] in FR'. rename FR' into FR.
zstep. zstep. zstep. zstep. zstep.
release_frame FR ST (bv_unsigned sp). finish_exp MU WM MI ST.
Qed.
End S.

Lemma exp_proof : exp_stmt.
Proof.
intros lo. intros until m. intros ST LOW MI FRM.
unfold EXP_DEPTH in LOW. unfold A_exp.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
zstep. zstep. zstep.
set (ab := Z.shiftr (Z.shiftl (bv_unsigned (reg_get F 10)) 1 mod 18446744073709551616) 53).
assert (AB : 0 <= ab < 2048).
{ subst ab. rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.mod_pos_bound (Z.shiftl (bv_unsigned (reg_get F 10)) 1) 18446744073709551616 ltac:(lia)).
split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. change (2 ^ 53 * 2048) with 18446744073709551616. lia. }
zstep. zstep. zstep. if_cases BA1.
-
zstep. zstep. if_cases BA2.
+   zstep. zstep. if_cases BA3.
*
zstep. zstep. zstep. zstep. zstep. if_cases BA4.
--   zstep. zstep. zstep. zstep. zstep. zstep. if_cases BA5.
++   zstep. zstep. zstep. zstep.
apply evt_done; unfold exp_post; eexists _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _, _; split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [assumption| exact ST].
++ zstep. if_cases BA6.
**   zstep. zstep. zstep. zstep. zstep.
eapply (exp_xflow lo m ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 LOW); try assumption.
**   zstep. zstep. zstep. zstep. zstep.
eapply (exp_xflow lo m ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 LOW); try assumption.
--   zstep. zstep.
apply evt_done; unfold exp_post; eexists _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _, _; split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [assumption| exact ST].
*
zstep. zstep. eapply (exp_main lo m ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 LOW 0); try assumption. lia.
+
zstep. zstep. zstep. zstep.
apply evt_done; unfold exp_post; eexists _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _, _; split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [assumption| exact ST].
-
eapply (exp_main lo m ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 LOW ab); try assumption.
Qed.
