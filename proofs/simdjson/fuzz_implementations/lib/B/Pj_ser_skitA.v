(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep Frame.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim SjModel PjModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjTape SjTapeList SjTapeTile SjPjSer.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_libiface Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_hkit3A Atp_hkit4A Pj_rtkA Pj_defsA Pj_cpsA Pj_ser_defsA Pj_ser_kitA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition PJ_TABS_A : Z := 0x23a80.
Definition PJ_TABS_LEN : Z := 512.

Definition ne_val (b : Z) : Z := nth (Z.to_nat b) pj_ne_table 0.
Definition esc_byte (o : Z) : Z := nth (Z.to_nat o) pj_esc_table 0.

Lemma ne_imageA : ro_bytes_b bsegs PJ_NE_TAB_A (map (Z_to_bv 8) pj_ne_table) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma esc_imageA : ro_bytes_b bsegs PJ_ESC_TAB_A (map (Z_to_bv 8) pj_esc_table) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma table_Forall_range : forall (l : list Z) o, Forall (fun c => 0 <= c < 256) l -> 0 <= nth (Z.to_nat o) l 0 < 256.
Proof.
  intros l o H. destruct (Nat.lt_ge_cases (Z.to_nat o) (length l)) as [L|L].
  - rewrite Forall_forall in H. apply H. apply nth_In. exact L.
  - rewrite nth_overflow by exact L. lia.
Qed.
Lemma ne_val_range : forall b, 0 <= ne_val b < 256.
Proof. intros b. apply table_Forall_range. unfold pj_ne_table. repeat (constructor; [lia|]). constructor. Qed.
Lemma esc_byte_range : forall o, 0 <= esc_byte o < 256.
Proof. intros o. apply table_Forall_range. unfold pj_esc_table. repeat (constructor; [lia|]). constructor. Qed.
Lemma esc_len_byte : forall c, esc_byte (8 * c) = esc_len c.
Proof. reflexivity. Qed.

Lemma zbytes_read1A : forall (m : mem) A (l : list Z) (k : Z),
  bytes_at bsegs m A (map (Z_to_bv 8) l) -> 0 <= k < Z.of_nat (length l) ->
  ov_read_bytes bsegs m (wa (A + k)) 1 = Some [Z_to_bv 8 (nth (Z.to_nat k) l 0)].
Proof. intros m A l k HB Hk. exact (sbuf_read1 m A l k HB Hk). Qed.

Lemma ne_readA : forall (m : mem) b, mem_inv bsegs m -> 0 <= b < 256 ->
  ov_read_bytes bsegs m (wa (PJ_NE_TAB_A + b)) 1 = Some [Z_to_bv 8 (ne_val b)].
Proof.
  intros m b MI Hb. apply zbytes_read1A; [| rewrite pj_ne_table_length; lia].
  apply ro_bytes_at; [exact MI| unfold PJ_NE_TAB_A; lia| rewrite length_map, pj_ne_table_length; unfold PJ_NE_TAB_A; lia|].
  apply ro_bytes_b_sound. exact ne_imageA.
Qed.
Lemma esc_readA : forall (m : mem) o, mem_inv bsegs m -> 0 <= o < 256 ->
  ov_read_bytes bsegs m (wa (PJ_ESC_TAB_A + o)) 1 = Some [Z_to_bv 8 (esc_byte o)].
Proof.
  intros m o MI Ho. apply zbytes_read1A; [| rewrite pj_esc_table_length; lia].
  apply ro_bytes_at; [exact MI| unfold PJ_ESC_TAB_A; lia| rewrite length_map, pj_esc_table_length; unfold PJ_ESC_TAB_A; lia|].
  apply ro_bytes_b_sound. exact esc_imageA.
Qed.

Lemma shz_tabs : forall m, acc bsegs m PJ_TABS_A PJ_TABS_LEN -> shz m PJ_TABS_A PJ_TABS_LEN.
Proof.
  intros m AC. pose proof (shz_of_acc m PJ_TABS_A PJ_TABS_LEN AC eq_refl ltac:(unfold PJ_TABS_A; lia)) as H.
  exact H.
Qed.

Lemma shz_ne : forall m b, shz m PJ_TABS_A PJ_TABS_LEN -> 0 <= b < 256 ->
  ov_read_bytes bsegs m (wa (shad (PJ_NE_TAB_A + b))) 1 = Some [Z_to_bv 8 0].
Proof. intros m b SH Hb. apply SH. unfold PJ_TABS_A, PJ_TABS_LEN, PJ_NE_TAB_A. lia. Qed.
Lemma shz_esc : forall m o, shz m PJ_TABS_A PJ_TABS_LEN -> 0 <= o < 256 ->
  ov_read_bytes bsegs m (wa (shad (PJ_ESC_TAB_A + o))) 1 = Some [Z_to_bv 8 0].
Proof. intros m o SH Ho. apply SH. unfold PJ_TABS_A, PJ_TABS_LEN, PJ_ESC_TAB_A. lia. Qed.

Ltac str_envA OK CX :=
  lazymatch type of CX with sctxA ?E ?D ?I =>
  let H := fresh in
  pose proof (env_rangesA E OK) as H;
  let FS := fresh "FS" in let B1 := fresh "B1" in let B2 := fresh "B2" in let D1 := fresh "D1" in let D2 := fresh "D2" in let FL := fresh "FL" in
  destruct H as (T0 & TL & _ & S0 & SL & S16 & _ & _ & _ & FS & B1 & B2 & D1 & D2 & FL & LO & _);
  pose proof (c_dd E D I CX) as DD;
  let LOQ := fresh in pose proof (c_lo E D I CX) as LOQ; unfold ser_needA, PJ_TC_STACK_A, RT_STACK in LOQ;
  assert (LQ : pa_lo E + 656 + 65536 <= si_q I) by (clear - LOQ; lia); clear LOQ;
  pose proof (c_qtop E D I CX) as QT; unfold USTACK_TOP in QT;
  let Hf := fresh in pose proof (c_f E D I CX) as Hf; destruct Hf as (F0 & _ & FSG & FLO); unfold SEGTOP_A in FSG;
  let H8 := fresh in pose proof (env_div8 E D I OK CX) as H8;
  destruct H8 as (ED & _ & Ef & ESB & _);
  assert (SBR : 7208960 <= pa_SB E /\ pa_SB E + 96 <= pa_lo E) by (clear - FS B1 B2 FL; unfold SEGTOP_A in *; lia);
  assert (DOCR : 7208960 <= pa_DOC E /\ pa_DOC E + 24 <= pa_lo E) by (clear - FS D1 D2 FL; unfold SEGTOP_A in *; lia);
  clear FS B1 B2 D1 D2 FL
  end.

Lemma S_rangeA : forall E o, pjenvA_ok E -> 0 <= pa_S E o < 256.
Proof.
  intros E o OK. pose proof (ok_sbs E OK) as SB. unfold Tf. apply table_Forall_range. exact SB.
Qed.

Lemma read1_at : forall (m : mem) (a : Z) bs, ov_read_bytes bsegs m (wa a) 1 = Some bs -> forall x, x = a -> ov_read_bytes bsegs m (wa x) 1 = Some bs.
Proof. intros m a bs H x ->. exact H. Qed.

Lemma shz_at : forall (m : mem) (a n : Z), shz m a n -> forall y, a <= y < a + n -> forall x, x = y / 8 + 2147450880 ->
  ov_read_bytes bsegs m (wa x) 1 = Some [Z_to_bv 8 0].
Proof. intros m a n SH y Hy x ->. apply SH. exact Hy. Qed.

Lemma shz_rd : forall (m : mem) (a n : Z), shz m a n -> forall y, a <= y < a + n ->
  ov_read_bytes bsegs m (wa (shad y)) 1 = Some [Z_to_bv 8 0].
Proof. intros m a n SH y Hy. apply SH. exact Hy. Qed.
Ltac shfold :=
  repeat match goal with
  | |- context [Z_to_bv 64 (?y / 8 + 2147450880)] => change (Z_to_bv 64 (y / 8 + 2147450880)) with (Z_to_bv 64 (shad y))
  end.

Ltac astep := zstep; shz_norm; pjnorm; shfold; try (first [if_false | if_true]).

Lemma f3tmp_accA : forall (m : mem) (f : Z) (k : Z) (g : nat) (shp : list byte),
  u8arr bsegs m (f / 8 + 2147450880) shp -> nth_error shp g = Some z8 -> 8 * (f / 8) = f -> 0 <= f -> k = 8 * Z.of_nat g ->
  acc bsegs m (f + k) 8.
Proof.
  intros m f k g shp [HB _] HG Ef F0 -> i Hi. exists z8. split; [| left; reflexivity].
  pose proof (bytes_at_nth1 bsegs m _ shp g z8 HB HG) as H.
  replace (shad (f + 8 * Z.of_nat g + i)) with (f / 8 + 2147450880 + Z.of_nat g); [exact H|].
  unfold shad, SHB. Z.div_mod_to_equations. lia.
Qed.

Lemma apart_of_pointwise : forall a n s n', (forall y, a <= y < a + n -> ~ (s <= y < s + n')) -> 0 < n -> 0 < n' ->
  a + n <= s \/ s + n' <= a.
Proof.
  intros a n s n' H Hn Hn'.
  destruct (Z.le_gt_cases (a + n) s) as [L|L]; [left; exact L|].
  destruct (Z.le_gt_cases (s + n') a) as [L'|L']; [right; exact L'|].
  exfalso. apply (H (Z.max a s)); lia.
Qed.

Section SbufZ.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Lemma shz_sbufA : forall E D I Σc st mr m, pjenvA_ok E -> sctxA E D I -> SREFA RT E I Σc st mr -> munch (serWA E I st) mr m -> wmono bsegs mr m ->
    shz m (pa_SBUF E) (pa_sn E).
  Proof using AF.
    intros E D I Σc st mr m OK CX HR MU WM.
    pose proof (shz_sbuf_mu RT AF E D I OK CX Σc st mr m HR MU WM) as SH.
    pose proof (ok_ns8 E OK) as N8. pose proof (ok_sbuf E OK) as (_ & SN & _).
    eapply shz_sub; [exact SH| lia|]. Z.div_mod_to_equations. lia.
  Qed.
End SbufZ.

Ltac str_envA_sb OK :=
  lazymatch type of OK with pjenvA_ok ?E =>
  let H := fresh in
  pose proof (env_rangesA E OK) as H;
  destruct H as (T0 & TL & _ & S0 & SL & S16 & _)
  end.

Section TabsRT.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Lemma tabs_accA : forall Σ m, ART RT Σ m -> acc bsegs m PJ_TABS_A PJ_TABS_LEN.
  Proof using AF.
    intros Σ m HA. apply (acc_lit RT AF Σ m PJ_TABS_A PJ_TABS_LEN HA).
    unfold ACC_LITS, PJ_TABS_A, PJ_TABS_LEN. cbn [In]. repeat (first [left; reflexivity | right]).
  Qed.
End TabsRT.
