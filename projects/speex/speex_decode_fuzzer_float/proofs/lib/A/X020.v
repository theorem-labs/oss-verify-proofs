(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cg X1cr X1cs X1cn X1df.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.PA Require Import X1e9.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X02c.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0tb.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0tb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := bsegs.
Local Notation mem := (word -> option byte).

Definition A_exp : Z := 0xe9580.
Definition EXP_DEPTH : Z := 16.

Definition fp_callee_saved (k : reg) : Prop := 8 <= bv_unsigned k <= 9 \/ 18 <= bv_unsigned k <= 27.

Definition exp_postA (lo : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F' (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ munch [(lo, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ frm0 fc' /\ stk rsegs m' lo (bv_unsigned sp)
/\ (forall k : reg, fp_callee_saved k -> reg_get F' k = reg_get F k).

Definition exp_stmtA : Prop :=
forall (lo : Z)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
stk rsegs m lo (bv_unsigned sp) -> lo + EXP_DEPTH <= bv_unsigned sp ->
mem_inv rsegs m -> frm0 fc ->
evt rsegs (exp_postA lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_exp) fc None m (seg_rom rsegs)).

Definition EXP_DATA : Z := 0x2c658.

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
exists (firstn 112 rest), w1, w2. split.
- cbn. split; [rewrite firstn_length_le; [reflexivity| lia]|]. exact (conj I (conj I I)).
- cbn [cells_bytes cbytes app]. rewrite app_nil_r. apply bytes_at_app. split; [exact B1|].
rewrite firstn_length_le by lia. cbn [map cells_bytes cbytes app] in Ews. rewrite app_nil_r in Ews. rewrite Ews. exact B2.
Qed.

Section S.
Variables (lo : Z) (m0 : mem) (F0 : bvmap 5 word).
Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Hypothesis LOW : lo + 16 <= bv_unsigned sp.
Local Notation usp := (bv_unsigned sp).
Local Notation POST := (exp_postA lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F0 m0).

Ltac fs_kept :=
let k := fresh "k" in let Hk := fresh "Hk" in
intros k Hk; unfold fp_callee_saved in Hk;
repeat (lazymatch goal with |- context [reg_get (bvmap_set ?r _ _) k] =>
rewrite (reg_get_set_other _ r k) by
(let E := fresh "E" in intros E; subst k; revert Hk;
let v := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with v; lia) end);
first [ reflexivity | lazymatch goal with FSK : forall k0 : reg, fp_callee_saved k0 -> _ |- _ => apply FSK; exact Hk end ].

Ltac finish_exp MU WM MI ST :=
apply evt_done; unfold exp_postA;
do 18 eexists; split; [reflexivity|];
split; [exact MU|]; split; [exact WM|]; split; [exact MI|]; split; [assumption|]; split; [exact ST|];
fs_kept.

#[using="LOW"] Lemma exp_sc : forall (t0 t1 t2 xa0 xa1 xa2 xa3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (G : bvmap 5 word) (fc : bv 32) (m : mem),
(forall k : reg, fp_callee_saved k -> reg_get G k = reg_get F0 k) ->
frm0 fc -> mem_inv rsegs m -> munch [(lo, usp)] m0 m -> wmono rsegs m0 m -> stk rsegs m lo usp ->
evt rsegs POST
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 xa0 xa1 xa2 xa3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
G (Z_to_bv 64 0xe96a4) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros FSK FRM MI MU WM ST.
pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR.
zstep. zstep. if_cases SGN.
all: lazymatch goal with
| |- evt _ _ (MS _ _ (Z_to_bv 64 956112) _ _ _ _) =>

zstep; carve_frame 16%nat ST;
destruct (rw_cells_CB_C8s rsegs _ _ 2%nat _ FR) as (fw2 & Lfw & FR'); clear FR;
destruct fw2 as [|u0 [|u1 [|? ?]]]; cbn in Lfw; try lia; cbn [map] in FR'; rename FR' into FR;
do 10 zstep; if_cases LT1;
[ lazymatch goal with
| |- evt _ _ (MS _ _ (Z_to_bv 64 956232) _ _ _ _) => idtac
| _ => do 11 zstep; if_cases EQ0;
try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 956200) _ _ _ _) => zstep end);
zstep; zstep; lstep; zstep; zstep; zstep; zstep
end .. ];
zstep; zstep; zstep; zstep;
release_frame FR ST (bv_unsigned sp)
| _ =>   do 9 zstep
end.
all: finish_exp MU WM MI ST.
Qed.

#[using="LOW"] Lemma exp_main : forall (va2 : Z) (t0 t1 t2 xa0 xa1 xa3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
0 <= va2 < 2048 -> (forall k : reg, fp_callee_saved k -> reg_get F k = reg_get F0 k) ->
frm0 fc -> mem_inv rsegs m -> munch [(lo, usp)] m0 m -> wmono rsegs m0 m -> stk rsegs m lo usp ->
evt rsegs POST
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 xa0 xa1 (Z_to_bv 64 va2) xa3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xe9598) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros Hva2 FSK FRM MI MU WM ST.
pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR.
do 15 zstep.
zstep. zstep. zstep.
set (kdw := fadd_d RNE (fmul_d RNE (Z_to_bv 64 4640701337412797182) (reg_get F 10)) (Z_to_bv 64 4843621399236968448)) in *.
set (e := Z.shiftr (Z.shiftl (bv_unsigned kdw) 57 mod 18446744073709551616) 53) in *.
assert (He : 0 <= e < 2048).
{ subst e. rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.mod_pos_bound (Z.shiftl (bv_unsigned kdw) 57) 18446744073709551616 ltac:(lia)).
split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. change (2 ^ 53 * 2048) with 18446744073709551616. lia. }
destruct (exp_row m e MI He) as (junk & w1 & w2 & ROW). unfold EXP_DATA in ROW.
do 13 zstep. clear ROW.
destruct (Z.eq_dec va2 0) as [-> | NZ].
- if_true. zstep. apply exp_sc; try assumption. fs_kept.
- replace (bv_eqb (Z_to_bv 64 va2) (Z_to_bv 64 0)) with false by (symmetry; unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
cbv iota. zstep. zstep. zstep. finish_exp MU WM MI ST.
Qed.

#[using="LOW"] Lemma exp_xflow : forall (t0 t1 t2 xa1 xa2 xa3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (G : bvmap 5 word) (fc : bv 32) (m : mem),
(forall k : reg, fp_callee_saved k -> reg_get G k = reg_get F0 k) ->
frm0 fc -> mem_inv rsegs m -> munch [(lo, usp)] m0 m -> wmono rsegs m0 m -> stk rsegs m lo usp ->
evt rsegs POST
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) xa1 xa2 xa3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
G (Z_to_bv 64 0xe9764) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros FSK FRM MI MU WM ST.
pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR.
zstep. zstep. if_true. zstep. carve_frame 16%nat ST.
destruct (rw_cells_CB_C8s rsegs _ _ 2%nat _ FR) as (fw2 & Lfw & FR'); clear FR.
destruct fw2 as [|u0 [|u1 [|? ?]]]; cbn in Lfw; try lia. cbn [map] in FR'. rename FR' into FR.
zstep. zstep. zstep. zstep. zstep.
release_frame FR ST (bv_unsigned sp). finish_exp MU WM MI ST.
Qed.
End S.

Ltac fs_keptT :=
let k := fresh "k" in let Hk := fresh "Hk" in
intros k Hk; unfold fp_callee_saved in Hk;
repeat (lazymatch goal with |- context [reg_get (bvmap_set ?r _ _) k] =>
rewrite (reg_get_set_other _ r k) by
(let E := fresh "E" in intros E; subst k; revert Hk;
let v := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with v; lia) end);
reflexivity.
Ltac finish_expT MU WM MI ST :=
apply evt_done; unfold exp_postA;
do 18 eexists; split; [reflexivity|];
split; [exact MU|]; split; [exact WM|]; split; [exact MI|]; split; [assumption|]; split; [exact ST|];
fs_keptT.

Theorem exp_proofA : exp_stmtA.
Proof.
intros lo. intros until m. intros ST LOW MI FRM.
unfold EXP_DEPTH in LOW. unfold A_exp.
assert (FSK : forall k : reg, fp_callee_saved k -> reg_get F k = reg_get F k) by (intros; reflexivity).
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
finish_expT MU WM MI ST.
++ zstep. if_cases BA6.
**   zstep. zstep. zstep. zstep. zstep.
eapply (exp_xflow lo m F ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 LOW); try assumption; try fs_keptT.
**   zstep. zstep. zstep. zstep. zstep.
eapply (exp_xflow lo m F ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 LOW); try assumption; try fs_keptT.
--   zstep. zstep.
finish_expT MU WM MI ST.
*
zstep. zstep. eapply (exp_main lo m F ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 LOW 0); try assumption; try lia; try fs_keptT.
+
zstep. zstep. zstep. zstep.
finish_expT MU WM MI ST.
-
eapply (exp_main lo m F ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 LOW ab); try assumption; try fs_keptT.
Qed.
End B_TWIN.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := asegs.
Local Notation mem := (word -> option byte).

Definition A_exp : Z := 0xe0e50.
Definition EXP_DEPTH : Z := 16.

Definition fp_callee_saved (k : reg) : Prop := 8 <= bv_unsigned k <= 9 \/ 18 <= bv_unsigned k <= 27.

Definition exp_postA (lo : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F' (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ munch [(lo, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ frm0 fc' /\ stk rsegs m' lo (bv_unsigned sp)
/\ (forall k : reg, fp_callee_saved k -> reg_get F' k = reg_get F k).

Definition exp_stmtA : Prop :=
forall (lo : Z)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
stk rsegs m lo (bv_unsigned sp) -> lo + EXP_DEPTH <= bv_unsigned sp ->
mem_inv rsegs m -> frm0 fc ->
evt rsegs (exp_postA lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_exp) fc None m (seg_rom rsegs)).

Definition EXP_DATA : Z := 0x2c658.

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
exists (firstn 112 rest), w1, w2. split.
- cbn. split; [rewrite firstn_length_le; [reflexivity| lia]|]. exact (conj I (conj I I)).
- cbn [cells_bytes cbytes app]. rewrite app_nil_r. apply bytes_at_app. split; [exact B1|].
rewrite firstn_length_le by lia. cbn [map cells_bytes cbytes app] in Ews. rewrite app_nil_r in Ews. rewrite Ews. exact B2.
Qed.

Section S.
Variables (lo : Z) (m0 : mem) (F0 : bvmap 5 word).
Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Hypothesis LOW : lo + 16 <= bv_unsigned sp.
Local Notation usp := (bv_unsigned sp).
Local Notation POST := (exp_postA lo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F0 m0).

Ltac fs_kept :=
let k := fresh "k" in let Hk := fresh "Hk" in
intros k Hk; unfold fp_callee_saved in Hk;
repeat (lazymatch goal with |- context [reg_get (bvmap_set ?r _ _) k] =>
rewrite (reg_get_set_other _ r k) by
(let E := fresh "E" in intros E; subst k; revert Hk;
let v := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with v; lia) end);
first [ reflexivity | lazymatch goal with FSK : forall k0 : reg, fp_callee_saved k0 -> _ |- _ => apply FSK; exact Hk end ].

Ltac finish_exp MU WM MI ST :=
apply evt_done; unfold exp_postA;
do 18 eexists; split; [reflexivity|];
split; [exact MU|]; split; [exact WM|]; split; [exact MI|]; split; [assumption|]; split; [exact ST|];
fs_kept.

#[using="LOW"] Lemma exp_sc : forall (t0 t1 t2 xa0 xa1 xa2 xa3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (G : bvmap 5 word) (fc : bv 32) (m : mem),
(forall k : reg, fp_callee_saved k -> reg_get G k = reg_get F0 k) ->
frm0 fc -> mem_inv rsegs m -> munch [(lo, usp)] m0 m -> wmono rsegs m0 m -> stk rsegs m lo usp ->
evt rsegs POST
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 xa0 xa1 xa2 xa3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
G (Z_to_bv 64 0xe0f74) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros FSK FRM MI MU WM ST.
pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR.
zstep. zstep. if_cases SGN.
all: lazymatch goal with
| |- evt _ _ (MS _ _ (Z_to_bv 64 921504) _ _ _ _) =>

zstep; carve_frame 16%nat ST;
destruct (rw_cells_CB_C8s rsegs _ _ 2%nat _ FR) as (fw2 & Lfw & FR'); clear FR;
destruct fw2 as [|u0 [|u1 [|? ?]]]; cbn in Lfw; try lia; cbn [map] in FR'; rename FR' into FR;
do 10 zstep; if_cases LT1;
[ lazymatch goal with
| |- evt _ _ (MS _ _ (Z_to_bv 64 921624) _ _ _ _) => idtac
| _ => do 11 zstep; if_cases EQ0;
try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 921592) _ _ _ _) => zstep end);
zstep; zstep; lstep; zstep; zstep; zstep; zstep
end .. ];
zstep; zstep; zstep; zstep;
release_frame FR ST (bv_unsigned sp)
| _ =>   do 9 zstep
end.
all: finish_exp MU WM MI ST.
Qed.

#[using="LOW"] Lemma exp_main : forall (va2 : Z) (t0 t1 t2 xa0 xa1 xa3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
0 <= va2 < 2048 -> (forall k : reg, fp_callee_saved k -> reg_get F k = reg_get F0 k) ->
frm0 fc -> mem_inv rsegs m -> munch [(lo, usp)] m0 m -> wmono rsegs m0 m -> stk rsegs m lo usp ->
evt rsegs POST
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 xa0 xa1 (Z_to_bv 64 va2) xa3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xe0e68) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros Hva2 FSK FRM MI MU WM ST.
pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR.
do 15 zstep.
zstep. zstep. zstep.
set (kdw := fadd_d RNE (fmul_d RNE (Z_to_bv 64 4640701337412797182) (reg_get F 10)) (Z_to_bv 64 4843621399236968448)) in *.
set (e := Z.shiftr (Z.shiftl (bv_unsigned kdw) 57 mod 18446744073709551616) 53) in *.
assert (He : 0 <= e < 2048).
{ subst e. rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.mod_pos_bound (Z.shiftl (bv_unsigned kdw) 57) 18446744073709551616 ltac:(lia)).
split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. change (2 ^ 53 * 2048) with 18446744073709551616. lia. }
destruct (exp_row m e MI He) as (junk & w1 & w2 & ROW). unfold EXP_DATA in ROW.
do 13 zstep. clear ROW.
destruct (Z.eq_dec va2 0) as [-> | NZ].
- if_true. zstep. apply exp_sc; try assumption. fs_kept.
- replace (bv_eqb (Z_to_bv 64 va2) (Z_to_bv 64 0)) with false by (symmetry; unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
cbv iota. zstep. zstep. zstep. finish_exp MU WM MI ST.
Qed.

#[using="LOW"] Lemma exp_xflow : forall (t0 t1 t2 xa1 xa2 xa3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (G : bvmap 5 word) (fc : bv 32) (m : mem),
(forall k : reg, fp_callee_saved k -> reg_get G k = reg_get F0 k) ->
frm0 fc -> mem_inv rsegs m -> munch [(lo, usp)] m0 m -> wmono rsegs m0 m -> stk rsegs m lo usp ->
evt rsegs POST
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) xa1 xa2 xa3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
G (Z_to_bv 64 0xe1034) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros FSK FRM MI MU WM ST.
pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR.
zstep. zstep. if_true. zstep. carve_frame 16%nat ST.
destruct (rw_cells_CB_C8s rsegs _ _ 2%nat _ FR) as (fw2 & Lfw & FR'); clear FR.
destruct fw2 as [|u0 [|u1 [|? ?]]]; cbn in Lfw; try lia. cbn [map] in FR'. rename FR' into FR.
zstep. zstep. zstep. zstep. zstep.
release_frame FR ST (bv_unsigned sp). finish_exp MU WM MI ST.
Qed.
End S.

Ltac fs_keptT :=
let k := fresh "k" in let Hk := fresh "Hk" in
intros k Hk; unfold fp_callee_saved in Hk;
repeat (lazymatch goal with |- context [reg_get (bvmap_set ?r _ _) k] =>
rewrite (reg_get_set_other _ r k) by
(let E := fresh "E" in intros E; subst k; revert Hk;
let v := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with v; lia) end);
reflexivity.
Ltac finish_expT MU WM MI ST :=
apply evt_done; unfold exp_postA;
do 18 eexists; split; [reflexivity|];
split; [exact MU|]; split; [exact WM|]; split; [exact MI|]; split; [assumption|]; split; [exact ST|];
fs_keptT.

Theorem exp_proofA : exp_stmtA.
Proof.
intros lo. intros until m. intros ST LOW MI FRM.
unfold EXP_DEPTH in LOW. unfold A_exp.
assert (FSK : forall k : reg, fp_callee_saved k -> reg_get F k = reg_get F k) by (intros; reflexivity).
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
finish_expT MU WM MI ST.
++ zstep. if_cases BA6.
**   zstep. zstep. zstep. zstep. zstep.
eapply (exp_xflow lo m F ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 LOW); try assumption; try fs_keptT.
**   zstep. zstep. zstep. zstep. zstep.
eapply (exp_xflow lo m F ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 LOW); try assumption; try fs_keptT.
--   zstep. zstep.
finish_expT MU WM MI ST.
*
zstep. zstep. eapply (exp_main lo m F ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 LOW 0); try assumption; try lia; try fs_keptT.
+
zstep. zstep. zstep. zstep.
finish_expT MU WM MI ST.
-
eapply (exp_main lo m F ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 LOW ab); try assumption; try fs_keptT.
Qed.
