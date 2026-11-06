(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumA.v; 256 of its 345 lines of code are new or changed and 689 lines of the source are left out. *)
(* fuzz_preset, slice S10 TX-REST: the IMAGE- AND FUNCTION-AGNOSTIC segment environment of the program walks over the
   listing engine (YC80x / YC1fPx over YCbqG's ajournal_x), split out of S10TxStrGlue.v (WalkS10's ask, 2026-10-29):
   the environment TE regs0 regsc more (atoms 0-31 a function's ENTRY registers, 32-63 the current ones, 64- a
   segment's extras, over the image env Eimg of `{L : ptable asym} {PA : PAImg L}`), building a segment's symbolic state
   from concrete machine facts (ts_st_ok, ts_rok, ts_chunk), reading a run's final regions back (ts_region_nth, ts_field),
   bytes a run kept (ts_keep, ts_vm_av, ts_garr_av), registers a run kept (ts_reg_kept, te_close), and the callee-saved
   register facts (ts_cs, ts_ap). Same names as before the split, so PRW_WalkEnv stays replaceable by this file.
   Numerals: 5 / 8 / 32 / 64 / 240 / 2 ^ 64 (LENGTH: register, byte and word widths, the env's atom bounds), 2 ^ 44 /
   2 ^ 47 (DERIVED: the shadow span and the user range), atom indices (DERIVED: the engine's numbering). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YGcallx YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================================================================================== *)
(* ---- registers and the segment environment ---- *)
Lemma s10s_nth_all_regs : forall k, (k < 32)%nat -> nth k all_regs 0%bv = Z_to_bv 5 (Z.of_nat k).
Proof. intros k Hk. do 32 (destruct k as [|k]; [apply bv_eq; reflexivity|]). lia. Qed.
(* the atoms 32-63 hold the current registers *)
Definition cur_atoms : list sv := SLit 0 :: map (fun i => SOff (32 + i) 0) (seq 1 31).
Definition xr (r : nat) : nat := (32 + r)%nat.

(* `andi sp, sp, -32` on a 64-bit value *)
Lemma ts_land_m32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 32) = x / 32 * 32.
Proof.
intros x Hx. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
replace (2 ^ 64 - 32) with (Z.shiftl (Z.ones 59) 5) by reflexivity.
replace (x / 32 * 32) with (Z.shiftl (Z.shiftr x 5) 5)
  by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; reflexivity).
rewrite !Z.shiftl_spec by lia.
destruct (Z_lt_le_dec i 5) as [Hl|Hl].
- rewrite (Z.testbit_neg_r (Z.ones 59) (i - 5)), (Z.testbit_neg_r (Z.shiftr x 5) (i - 5)) by lia. apply andb_false_r.
- rewrite Z.shiftr_spec by lia. replace (i - 5 + 5) with i by lia.
  destruct (Z_lt_le_dec i 64) as [H64|H64].
  + rewrite Z.ones_spec_low by lia. apply andb_true_r.
  + rewrite Z.ones_spec_high by lia. rewrite andb_false_r.
    symmetry. apply (Z.bits_above_log2 x i); [lia|]. destruct (Z.eq_dec x 0) as [->|Hnz]; [cbn; lia|].
    apply (Z.lt_le_trans _ 64); [apply Z.log2_lt_pow2; lia | lia].
Qed.
Lemma ts_low_byte_mod : forall u n k, 0 <= u -> (k < n)%nat ->
  Z_to_bv 8 (Z.shiftr (u mod 2 ^ (8 * Z.of_nat n)) (8 * Z.of_nat k)) = Z_to_bv 8 (Z.shiftr u (8 * Z.of_nat k)).
Proof.
intros u n k Hu Hk. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with (2 ^ 8).
apply Z.bits_inj'. intros i Hi.
destruct (Z_lt_le_dec i 8) as [Hl|Hge].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia. rewrite Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma ts_add0_word : forall w : word, alu64 ALU_ADD w (Z_to_bv 64 0) = w.
Proof. intros w. apply bv_eq. cbn [alu64 alu]. rewrite bv_add_unsigned. change (bv_unsigned (Z_to_bv 64 0)) with 0.
rewrite Z.add_0_r. unfold bv_wrap. apply Z.mod_small. exact (bv_unsigned_in_range 64 w). Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {L : ptable asym} {PA : PAImg L}.
#[local] Notation SEGS := (@pa_segs _ L PA).
#[local] Notation VAL := (@pa_val _ L PA).
#[local] Notation BASE := (@pa_val _ L PA A_TEXT).

(* the segment environment: entry registers, current registers, extras *)
Definition TE (regs0 regsc : bvmap 5 word) (more : list word) : env :=
  @Eimg _ L PA (Ereg regs0 (map (getr regsc) all_regs ++ more)).

Lemma te_env : forall regs0 regsc more, img_env VAL A_LIM (TE regs0 regsc more).
Proof. intros. unfold TE. apply Eimg_env. Qed.
Lemma te_entry : forall regs0 regsc more (r : bv 5) n, Z.of_nat n = bv_unsigned r -> ew (TE regs0 regsc more) n = getr regs0 r.
Proof.
intros regs0 regsc more r n Hn. pose proof (u5_range r). unfold TE. rewrite Eimg_low by (unfold A_TEXT; lia).
apply ew_Ereg_nat. exact Hn.
Qed.
Lemma te_cur : forall regs0 regsc more (r : bv 5) k, Z.of_nat k = bv_unsigned r -> ew (TE regs0 regsc more) (32 + k) = getr regsc r.
Proof.
intros regs0 regsc more r k Hk. pose proof (u5_range r). unfold TE. rewrite Eimg_low by (unfold A_TEXT; lia).
rewrite ew_Ereg_extra. rewrite app_nth1 by (rewrite length_map; cbn; lia).
rewrite (nth_indep _ _ (getr regsc 0%bv)) by (rewrite length_map; cbn; lia).
rewrite map_nth. rewrite s10s_nth_all_regs by lia. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 5) with 32. rewrite Hk. apply Z.mod_small. lia.
Qed.
Lemma te_more : forall regs0 regsc more j, ew (TE regs0 regsc more) (64 + j) = nth j more (Z_to_bv 64 0) \/ (240 <= 64 + j)%nat.
Proof.
intros regs0 regsc more j. destruct (Nat.lt_ge_cases (64 + j) 240) as [H|H]; [left|right; exact H].
unfold TE. rewrite Eimg_low by (unfold A_TEXT; lia). replace (64 + j)%nat with (32 + (32 + j))%nat by lia.
rewrite ew_Ereg_extra. rewrite app_nth2 by (rewrite length_map; cbn; lia). rewrite length_map. cbn [length all_regs].
f_equal. lia.
Qed.
Lemma te_more_lt : forall regs0 regsc more j, (64 + j < 240)%nat -> ew (TE regs0 regsc more) (64 + j) = nth j more (Z_to_bv 64 0).
Proof. intros regs0 regsc more j Hj. destruct (te_more regs0 regsc more j) as [H|H]; [exact H | lia]. Qed.
Lemma te_img : forall regs0 regsc more n, (A_TEXT <= n < A_LIM)%nat -> ew (TE regs0 regsc more) n = Z_to_bv 64 (VAL n).
Proof. intros regs0 regsc more n Hn. unfold TE. apply Eimg_img. exact Hn. Qed.
Lemma te_obj : forall regs0 regsc more n kk, (A_TEXT <= n < A_LIM)%nat ->
  sv_denot (TE regs0 regsc more) (SOff n kk) = Z_to_bv 64 (VAL n + kk).
Proof.
intros regs0 regsc more n kk Hn. cbn [sv_denot]. rewrite te_img by exact Hn.
pose proof (@pa_val_range _ _ PA n) as R. rewrite unsigned_lit_small by lia. reflexivity.
Qed.

Lemma cur_atoms_nth : forall k, (1 <= k < 32)%nat -> nth k cur_atoms (SLit 0) = SOff (32 + k) 0.
Proof.
intros k Hk. destruct k as [|k']; [lia|]. unfold cur_atoms. cbn [nth].
pose proof (map_nth (fun i : nat => SOff (32 + i) 0) (seq 1 31) 0%nat k') as M. cbv beta in M.
rewrite (nth_indep _ (SLit 0) (SOff (32 + 0) 0)) by (rewrite length_map, length_seq; lia).
rewrite M, seq_nth by lia. first [reflexivity | f_equal; lia].
Qed.
Lemma te_regs_ok : forall regs0 regsc more, regs_ok (TE regs0 regsc more) cur_atoms regsc.
Proof.
intros regs0 regsc more r. unfold sr_get. pose proof (u5_range r) as Hr.
destruct (bv_eqb r 0) eqn:Hz.
- apply bv_eqb_eq in Hz. subst r. rewrite getr_zero. reflexivity.
- assert (Hne : bv_unsigned r <> 0).
  { intros H0. assert (r = 0%bv) by (apply bv_eq; rewrite H0; reflexivity). subst r. rewrite bv_eqb_refl in Hz. discriminate. }
  unfold ridx. rewrite cur_atoms_nth by lia. cbn [sv_denot]. rewrite Z.add_0_r.
  rewrite (te_cur regs0 regsc more r (Z.to_nat (bv_unsigned r))) by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* ---- building a segment's symbolic state from concrete facts ---- *)
Lemma ts_st_ok : forall regs0 regsc more pc sr rs G (Wc : world SEGS) memc,
  regs_ok (TE regs0 regsc more) sr regsc -> regions_wf rs = true ->
  Forall (YP09.region_ok SEGS (TE regs0 regsc more) (mrestrict (w_H Wc) memc)) rs ->
  pairwise_disjoint (TE regs0 regsc more) rs -> facts_ok (TE regs0 regsc more) G ->
  st_ok_pi SEGS VAL (TE regs0 regsc more) (mkSS pc sr rs None G)
    (restrict (w_H Wc) (mkst regsc (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof. intros. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full; assumption. Qed.

Lemma ts_bv_some : forall E n, base_val E (Some n) = bv_unsigned (ew E n).
Proof. reflexivity. Qed.

Lemma ts_rok : forall E m n base lo hi wlo whi cs, bv_unsigned (ew E n) = base -> 0 <= base + lo -> base + hi <= 2 ^ 64 ->
  (forall o, wlo <= o < whi -> YP09.writable_at SEGS m (base + o)) -> Forall (YP09.chunk_ok SEGS E m base) cs ->
  YP09.region_ok SEGS E m (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E m n base lo hi wlo whi cs Hb H1 H2 H3 H4. unfold YP09.region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Hb. auto.
Qed.

Lemma ts_chunk : forall E m base off (n : N) e v, sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) ->
  (Z.of_N n <= 8) -> val_mem SEGS m (base + off) (N.to_nat n) v -> YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal n e)).
Proof. intros. eapply chunk_ok_val; eassumption. Qed.

Lemma ts_aview_range : forall H mem a v, aview SEGS H mem a = Some v -> 0 <= v < 256.
Proof.
intros H mem a v Hv. unfold aview in Hv. destruct (mbyte SEGS (mrestrict H mem) a) as [b|]; [|discriminate].
cbn in Hv. injection Hv as <-. pose proof (bv_unsigned_in_range 8 b) as X. unfold bv_modulus in X. cbn in X. lia.
Qed.
Lemma ts_rdword_range : forall H mem a v, rdword (aview SEGS H mem) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
intros H mem a v Hw. unfold rdword in Hw.
destruct (aview SEGS H mem a) as [b0|] eqn:E0; [|discriminate].
destruct (aview SEGS H mem (a + 1)) as [b1|] eqn:E1; [|discriminate].
destruct (aview SEGS H mem (a + 2)) as [b2|] eqn:E2; [|discriminate].
destruct (aview SEGS H mem (a + 3)) as [b3|] eqn:E3; [|discriminate].
destruct (aview SEGS H mem (a + 4)) as [b4|] eqn:E4; [|discriminate].
destruct (aview SEGS H mem (a + 5)) as [b5|] eqn:E5; [|discriminate].
destruct (aview SEGS H mem (a + 6)) as [b6|] eqn:E6; [|discriminate].
destruct (aview SEGS H mem (a + 7)) as [b7|] eqn:E7; [|discriminate].
injection Hw as <-.
apply ts_aview_range in E0, E1, E2, E3, E4, E5, E6, E7. lia.
Qed.

(* reading a region of a run's final state back as concrete bytes *)
Lemma ts_region_nth : forall E ss ms i r, st_ok_pi SEGS VAL E ss ms -> nth_error (ss_mem ss) i = Some r ->
  YP09.region_ok SEGS E (ms_mem ms) r.
Proof.
intros E ss ms i r HS Hi. destruct (st_ok_mem_ok SEGS E _ ms HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
Lemma ts_region_nth_c : forall E ss ms i r, st_ok SEGS E ss ms -> nth_error (ss_mem ss) i = Some r ->
  YP09.region_ok SEGS E (ms_mem ms) r.
Proof.
intros E ss ms i r HS Hi. destruct (st_ok_mem_ok SEGS E _ ms HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
Lemma ts_field : forall E m n b cs lo hi wlo whi od (w : N) e,
  YP09.region_ok SEGS E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> (Z.of_N w <= 8) ->
  val_mem SEGS m (b + od) (N.to_nat w) (U E e mod 2 ^ (8 * Z.of_N w)).
Proof.
intros E m n b cs lo hi wlo whi od w e (_ & _ & _ & Hcs) Hn Hc Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as H. cbn [YP09.r_base base_val] in H. rewrite Hn in H.
intros k Hk. unfold YP09.chunk_ok in H. cbn [YP09.c_off YP09.c_val c_len cv_len] in H.
pose proof (N_nat_Z w) as Hnn.
destruct (H (Z.of_nat k) ltac:(lia)) as (bb & Hb1 & Hb2). cbn [cbyte] in Hb1. unfold YP09.byte_of_word in Hb1.
injection Hb1 as <-. rewrite Hb2. f_equal. unfold U.
pose proof (bv_unsigned_in_range 64 (sv_denot E e)) as Hu. change (bv_modulus 64) with (2 ^ 64) in Hu.
set (u := bv_unsigned (sv_denot E e)) in *.
assert (Hm : 0 <= u mod 2 ^ (8 * Z.of_N w) < 2 ^ (8 * Z.of_nat (N.to_nat w))).
{ rewrite Hnn. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia. }
rewrite (le_byte_small _ _ _ Hm Hk). rewrite <- Hnn. symmetry. apply ts_low_byte_mod; [lia | exact Hk].
Qed.
Lemma ts_U0 : forall E n, U E (SOff n 0) = bv_unsigned (ew E n).
Proof.
intros E n. rewrite U_SOff, Z.add_0_r. apply YP0m.zcanon_small.
pose proof (bv_unsigned_in_range 64 (ew E n)) as H. change (bv_modulus 64) with (2 ^ 64) in H. exact H.
Qed.
Lemma ts_U_atom_mod : forall E n, U E (SOff n 0) mod 2 ^ 64 = bv_unsigned (ew E n).
Proof.
intros E n. rewrite U_SOff, Z.add_0_r. pose proof (bv_unsigned_in_range 64 (ew E n)) as H. change (bv_modulus 64) with (2 ^ 64) in H.
rewrite zcanon_id by (unfold M64; lia). apply Z.mod_small. lia.
Qed.

(* a byte a value is read from is present *)
Lemma ts_vm_present : forall (H : word -> bool) m a n v, val_mem SEGS (mrestrict H m) a n v ->
  forall j, (j < n)%nat -> aview SEGS H m (a + Z.of_nat j) <> None.
Proof. intros H m a n v HV j Hj. unfold aview. rewrite (HV j Hj). discriminate. Qed.
(* a word read through readers that agree on its 8 bytes *)
Lemma ts_rdword_keep : forall (rd rd' : reader) a, (forall j, 0 <= j < 8 -> rd' (a + j) = rd (a + j)) ->
  rdword rd' a = rdword rd a.
Proof.
intros rd rd' a H. pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. unfold rdword.
rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.

(* bytes a run did not write *)
Lemma ts_keep : forall (Wx : world SEGS) E rs mA mB (P : Z -> Prop),
  frame_of E rs (mrestrict (w_H Wx) mA) (mrestrict (w_H Wx) mB) ->
  (forall a, in_wrange E rs a -> P a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS (w_H Wx) mB a = aview SEGS (w_H Wx) mA a.
Proof.
intros Wx E rs mA mB P HF HP a Ha Hn. unfold aview. f_equal. unfold mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. intros H. exact (Hn (HP a H)).
Qed.
Lemma ts_val_mem_rd32 : forall (H : word -> bool) m a v, rd32 (aview SEGS H m) a v -> val_mem SEGS (mrestrict H m) a 4 v.
Proof.
intros H m a v Hr kk Hk. pose proof (Hr kk Hk) as Hb. unfold aview in Hb.
destruct (mbyte SEGS (mrestrict H m) (a + Z.of_nat kk)) as [b|] eqn:Em; [|discriminate].
cbn [option_map] in Hb. injection Hb as Hb. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. transitivity (bv_wrap 8 (bv_unsigned b)).
- unfold bv_wrap. rewrite Z.mod_small; [reflexivity | exact (bv_unsigned_in_range 8 b)].
- f_equal. exact Hb.
Qed.
(* bytes kept in the reader's view are kept in the value view *)
Lemma ts_vm_av : forall (H H' : word -> bool) m m' a n v,
  (forall j, (j < n)%nat -> aview SEGS H' m' (a + Z.of_nat j) = aview SEGS H m (a + Z.of_nat j)) ->
  val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v Hag HV j Hj. rewrite (mbyte_of_aview SEGS H H' m m' _ (Hag j Hj)). exact (HV j Hj).
Qed.
Lemma ts_garr_av : forall (H H' : word -> bool) m m' a l,
  (forall j, (j < length l)%nat -> aview SEGS H' m' (a + Z.of_nat j) = aview SEGS H m (a + Z.of_nat j)) ->
  garr8 SEGS (mrestrict H m) a l -> garr8 SEGS (mrestrict H' m') a l.
Proof.
intros H H' m m' a l Hag HG j Hj. destruct (HG j Hj) as [V R]. split; [|exact R].
apply (ts_vm_av H H' m m' _ 1 _); [|exact V].
intros i Hi. assert (i = 0%nat) by lia. subst i. cbn [Z.of_nat]. rewrite Z.add_0_r. exact (Hag j Hj).
Qed.
(* a register the segment did not write: its final value is the segment's start value *)
Lemma ts_reg_kept : forall regs0 regsc more ss (H : word -> bool) ms (r r' : bv 5),
  st_ok_pi SEGS VAL (TE regs0 regsc more) ss (restrict H ms) ->
  sr_get (ss_regs ss) r = SOff (32 + Z.to_nat (bv_unsigned r')) 0 -> getr (ms_regs ms) r = getr regsc r'.
Proof.
intros regs0 regsc more ss H ms r r' HS Hr. rewrite (st_ok_pi_restrict_reg H _ ss ms r HS), Hr. cbn [sv_denot].
rewrite Z.add_0_r, (te_cur regs0 regsc more r' (Z.to_nat (bv_unsigned r'))) by (pose proof (u5_range r'); lia).
apply Z_to_bv_bv_unsigned.
Qed.
Lemma ts_reg_kept_c : forall regs0 regsc more ss (H : word -> bool) ms (r r' : bv 5),
  st_ok SEGS (TE regs0 regsc more) ss (restrict H ms) ->
  sr_get (ss_regs ss) r = SOff (32 + Z.to_nat (bv_unsigned r')) 0 -> getr (ms_regs ms) r = getr regsc r'.
Proof.
intros regs0 regsc more ss H ms r r' HS Hr. rewrite (st_ok_restrict_reg SEGS H _ ss ms r HS), Hr. cbn [sv_denot].
rewrite Z.add_0_r, (te_cur regs0 regsc more r' (Z.to_nat (bv_unsigned r'))) by (pose proof (u5_range r'); lia).
apply Z_to_bv_bv_unsigned.
Qed.
(* the frame's shadow pointer `(F >> 3) + shadow base` (A 0x84f24 / 0x84f4c) as one atom *)
Lemma ts_alias_shadow : forall E nF nB nS F, bv_unsigned (ew E nF) = F -> bv_unsigned (ew E nB) = SHADOW_OFF ->
  bv_unsigned (ew E nS) = shadow_addr F -> 0 <= F < 2 ^ 47 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff nF 0) (SLit 3)) (SOff nB 0)) = sv_denot E (SOff nS 0).
Proof.
intros E nF nB nS F HF HB HS HFr. apply U_inj. rewrite !U_SAlu, !U_SOff, U_SLit, HF, HB, HS.
unfold zcanon, M64, zalu_raw, shadow_addr, SHADOW_OFF.
change (Z.land (3 mod 2 ^ 64) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (0 <= F / 8 < 2 ^ 44) by lia. rewrite !Z.add_0_r. rewrite !Z.mod_small; lia.
Qed.
(* one byte: its value in the view and in val_mem *)
Lemma ts_le_byte1 : forall v, 0 <= v < 256 -> le_byte v 1 0 = v.
Proof.
intros v Hv. unfold le_byte. cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.shiftr_0_r.
change (2 ^ (8 * Z.of_nat 1)) with 256. rewrite !Z.mod_small; lia.
Qed.
Lemma ts_aview_of_vm1 : forall (H : word -> bool) m a v, val_mem SEGS (mrestrict H m) a 1 v -> 0 <= v < 256 ->
  aview SEGS H m a = Some v.
Proof.
intros H m a v HV Hv. pose proof (HV 0%nat ltac:(lia)) as H0. cbn [Z.of_nat] in H0. rewrite Z.add_0_r in H0.
unfold aview. rewrite H0. cbn [option_map]. f_equal. rewrite ts_le_byte1 by exact Hv.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hv.
Qed.
Lemma ts_vm1_of_aview : forall (H : word -> bool) m a v, aview SEGS H m a = Some v -> val_mem SEGS (mrestrict H m) a 1 v.
Proof.
intros H m a v Ha k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r.
unfold aview in Ha. destruct (mbyte SEGS (mrestrict H m) a) as [bb|] eqn:Em; [|discriminate].
cbn [option_map] in Ha. injection Ha as <-.
pose proof (bv_unsigned_in_range 8 bb) as Hr. change (bv_modulus 8) with 256 in Hr.
rewrite ts_le_byte1 by exact Hr. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
(* a byte register differs from each listed value: the conditions a segment starts with *)
Lemma ts_conds_ne : forall E n cb nes, bv_unsigned (ew E n) = cb ->
  Forall (fun v => cb <> v /\ 0 <= v < 2 ^ 64) nes ->
  conds_ok E (map (fun v => mkAC BC_NE (SOff n 0) (SLit v)) nes).
Proof.
intros E n cb nes Hn H. induction H as [|v nes [Hv Hr] _ IH]; [exact I|].
cbn [map conds_ok]. split; [|exact IH].
unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_ne_U, ts_U0, U_SLit, Hn.
rewrite YP0m.zcanon_small by lia. apply negb_true_iff, Z.eqb_neq. exact Hv.
Qed.
Lemma ts_conds_eq : forall E n cb eqs, bv_unsigned (ew E n) = cb ->
  Forall (fun v => cb = v /\ 0 <= v < 2 ^ 64) eqs ->
  conds_ok E (map (fun v => mkAC BC_EQ (SOff n 0) (SLit v)) eqs).
Proof.
intros E n cb eqs Hn H. induction H as [|v eqs [Hv Hr] _ IH]; [exact I|].
cbn [map conds_ok]. split; [|exact IH].
unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_eq_U, ts_U0, U_SLit, Hn.
rewrite YP0m.zcanon_small by lia. apply Z.eqb_eq. exact Hv.
Qed.
Lemma ts_conds_app : forall E l1 l2, conds_ok E l1 -> conds_ok E l2 -> conds_ok E (l1 ++ l2).
Proof. intros E l1 l2 H1 H2. induction l1 as [|c l1 IH]; [exact H2|]. destruct H1 as [Hc H1]. split; [exact Hc | exact (IH H1)]. Qed.
(* the value of an ALU result over known operands, as a word (the forms prreg leaves after a run) *)
Lemma ts_alu_w64 : forall op (w1 w2 : word) a b, bv_unsigned w1 = a -> bv_unsigned w2 = b ->
  alu64 op w1 w2 = w64 (zalu64 op a b).
Proof.
intros op w1 w2 a b H1 H2. rewrite <- (Z_to_bv_bv_unsigned _ w1), <- (Z_to_bv_bv_unsigned _ w2), H1, H2.
apply zalu64_sound.
Qed.
Lemma ts_zalu_and255 : forall c, 0 <= c < 256 -> zalu64 ALU_AND c 255 = c.
Proof.
intros c Hc. unfold zalu64. rewrite (YP0m.zcanon_small c), (YP0m.zcanon_small 255) by lia. unfold zalu_raw.
change 255 with (Z.ones 8). rewrite Z.land_ones by lia. rewrite Z.mod_small by (change (2 ^ 8) with 256; lia).
apply YP0m.zcanon_small. lia.
Qed.
Lemma ts_zalu_and15 : forall c, 0 <= c < 256 -> zalu64 ALU_AND c 15 = c mod 16.
Proof.
intros c Hc. unfold zalu64. rewrite (YP0m.zcanon_small c), (YP0m.zcanon_small 15) by lia. unfold zalu_raw.
change 15 with (Z.ones 4). rewrite Z.land_ones by lia. change (2 ^ 4) with 16. apply YP0m.zcanon_small. lia.
Qed.
Lemma ts_zalu_srl4 : forall c, 0 <= c < 256 -> zalu64 ALU_SRL c 4 = c / 16.
Proof.
intros c Hc. unfold zalu64. rewrite (YP0m.zcanon_small c), (YP0m.zcanon_small 4) by lia. unfold zalu_raw.
change (Z.land 4 63) with 4. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16. apply YP0m.zcanon_small. lia.
Qed.
Lemma ts_zalu_add : forall a d, 0 <= a -> 0 <= d -> a + d < 2 ^ 64 -> zalu64 ALU_ADD a d = a + d.
Proof.
intros a d Ha Hd Hs. unfold zalu64. rewrite (YP0m.zcanon_small a), (YP0m.zcanon_small d) by lia. unfold zalu_raw.
apply YP0m.zcanon_small. lia.
Qed.
(* bytes a run did not write, at the mbyte level (for garr8's frame lemmas) *)
Lemma ts_keep_mb : forall (H : word -> bool) E rs mA mB (P : Z -> Prop),
  frame_of E rs (mrestrict H mA) (mrestrict H mB) ->
  (forall a, in_wrange E rs a -> P a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ P a -> mbyte SEGS (mrestrict H mB) a = mbyte SEGS (mrestrict H mA) a.
Proof.
intros H E rs mA mB P HF HP a Ha Hn. unfold mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. intros HW. exact (Hn (HP a HW)).
Qed.
End d.

(* closes `ew (TE r0 rc mo) n = X` for an entry register (n < 32), a current register (32 <= n < 64) or an extra *)
Ltac te_close :=
  lazymatch goal with |- ew (TE ?r0 ?rc ?mo) ?n = _ =>
    let nn := eval vm_compute in n in
    lazymatch eval vm_compute in (Nat.ltb nn 32) with
    | true => apply (te_entry r0 rc mo _ nn); reflexivity
    | false => lazymatch eval vm_compute in (Nat.ltb nn 64) with
      | true => let kk := eval vm_compute in (Nat.sub nn 32) in apply (te_cur r0 rc mo _ kk); reflexivity
      | false => let j := eval vm_compute in (Nat.sub nn 64) in rewrite (te_more_lt r0 rc mo j) by lia; reflexivity
      end
    end
  end.

(* a callee-saved register index, by computation *)
Ltac ts_cs := unfold acallee_saved;
  lazymatch goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end;
  lia.
Lemma ts_ap : forall rg rg' (r : bv 5), aregs_preserved rg rg' -> acallee_saved (bv_unsigned r) -> getr rg' r = getr rg r.
Proof. intros rg rg' r HP Hr. pose proof (HP _ Hr) as Hq. rewrite Z_to_bv_bv_unsigned in Hq. exact Hq. Qed.

