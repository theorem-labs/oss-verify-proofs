(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE23.v, with its module paths changed, names TfibSyms -> BoxregSyms and its addresses moved to libreac/fuzz_boxreg's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/AE23.v, with its module paths changed; 1735 of its 1799 lines of code are new or changed and 1611 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A (the asan build, pin 059dae63e07c): musl mwrite 0x96cc0 (69 instructions, frame 48) on
   link's memory FILE, against LinkRwDefs.v.
   link_amwrite_gen   : amwrite_mf_realizes (window 96 + ESTACK, up to 1024 pending bytes).
     k = 0: the k = 0 contract (Section hypothesis HK0) at the same sp; its window lies inside this one.
     k > 0: a symbolic walk. +0x34 beq not taken; +0x3c f->wpos = f->wbase; +0x4c jal 0x96cc0 is HK0 one frame
     lower on the k pending bytes; +0x50 bgeu: n1 < k returns 0 (+0x54), else the k = 0 path from +0x5c:
     +0x80 bgeu (ENOSPC arm: +0x84 ___errno_location 0x90a7c, run inline; +0x8c errno; F_ERR; window 0),
     +0xc0 jal 0x52d74 the memory-checking runtime's memcpy wrapper (Section hypothesis AMEMCPY),
     +0xc4..+0xec pos, len and the NUL at buf[pos] (the one store done by hand, mw_sb_zero).
   link_amwrite_flush : amwrite_mf_flush_realizes, link_amwrite_gen at x = 0 and no data. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AE20 AE2y.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AMemFileSink AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs LinkRwDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ==========================================================================
   0. The code table: mwrite (69 instructions) and ___errno_location (3), which the symbolic run executes inline
   ========================================================================== *)

Definition mw_ranges : list (Z * nat) := [(0x96cc0, 69%nat); (0x90a7c, 3%nat)].
Definition tbl_mw : ctable := Eval vm_compute in build_ranges mw_ranges TEmpty.
Lemma tbl_mw_eq : tbl_mw = build_ranges mw_ranges TEmpty.
Proof. vm_cast_no_check (eq_refl tbl_mw). Qed.
Lemma tbl_mw_ok : table_ok tfibsegs tbl_mw.
Proof. rewrite tbl_mw_eq. apply build_ranges_ok; [| apply table_ok_empty]. unfold mw_ranges. repeat constructor; cbn; discriminate. Qed.

(* ==========================================================================
   1. Byte-level helpers
   ========================================================================== *)

(* the bytes of a value fix it modulo 2^(8n) (donor: the 8-byte wms_le_bytes_mod of
   (internal path) (internal record, sha256 5332f18fa29b), generalised to n bytes) *)
Lemma mw_le_bytes_mod : forall (n : nat) x y,
  (forall k, (k < n)%nat -> YO0f.le_byte x n k = YO0f.le_byte y n k) ->
  x mod 2 ^ (8 * Z.of_nat n) = y mod 2 ^ (8 * Z.of_nat n).
Proof.
  intros n x y H. unfold YO0f.le_byte in H. set (M := 8 * Z.of_nat n) in *.
  assert (HM : 0 <= M) by (subst M; lia).
  apply Z.bits_inj'. intros i Hi.
  destruct (Z_lt_le_dec i M) as [Hlt|Hge].
  - assert (Hq : 0 <= i / 8) by (apply Z.div_pos; lia).
    assert (Hq2 : i / 8 < Z.of_nat n) by (apply Z.div_lt_upper_bound; lia).
    set (k := Z.to_nat (i / 8)).
    assert (Hk : (k < n)%nat) by (subst k; lia).
    assert (Ek : Z.of_nat k = i / 8) by (subst k; rewrite Z2Nat.id; lia).
    specialize (H k Hk). change 256 with (2 ^ 8) in H.
    assert (Hb : forall z, Z.testbit (Z.shiftr (z mod 2 ^ M) (8 * Z.of_nat k) mod 2 ^ 8) (i mod 8) =
                           Z.testbit (z mod 2 ^ M) i).
    { intros z. pose proof (Z.mod_pos_bound i 8 ltac:(lia)) as Hm.
      rewrite Z.mod_pow2_bits_low by lia. rewrite Z.shiftr_spec by lia. f_equal.
      pose proof (Z.div_mod i 8 ltac:(lia)). lia. }
    rewrite <- (Hb x), <- (Hb y), H. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

(* (donor: wms_val_mem8_det of WMseek.v, generalised to n bytes) *)
Lemma mw_val_mem_det : forall segs (m : word -> option byte) a (n : nat) x y,
  val_mem segs m a n x -> val_mem segs m a n y ->
  0 <= x < 2 ^ (8 * Z.of_nat n) -> 0 <= y < 2 ^ (8 * Z.of_nat n) -> x = y.
Proof.
  intros segs m a n x y Hx Hy Rx Ry.
  rewrite <- (Z.mod_small x (2 ^ (8 * Z.of_nat n))), <- (Z.mod_small y (2 ^ (8 * Z.of_nat n))) by lia.
  apply mw_le_bytes_mod. intros k Hk. specialize (Hx k Hk). specialize (Hy k Hk). rewrite Hx in Hy.
  assert (Hb : Z_to_bv 8 (YO0f.le_byte x n k) = Z_to_bv 8 (YO0f.le_byte y n k)) by congruence.
  apply (f_equal bv_unsigned) in Hb. rewrite !Z_to_bv_unsigned in Hb. unfold bv_wrap in Hb.
  change (bv_modulus 8) with 256 in Hb. unfold YO0f.le_byte in *. rewrite !Z.mod_mod in Hb by lia. exact Hb.
Qed.

Lemma mw_val_mem_xfer : forall segs (m m' : word -> option byte) a (n : nat) v,
  (forall i, 0 <= i < Z.of_nat n -> mbyte segs m' (a + i) = mbyte segs m (a + i)) ->
  val_mem segs m a n v -> val_mem segs m' a n v.
Proof. intros segs m m' a n v Hk Hv k Hkn. rewrite Hk by lia. exact (Hv k Hkn). Qed.

Lemma mw_grows_apresent : forall (H : word -> bool) (m m' : word -> option byte) a,
  mem_grows (mrestrict H m) (mrestrict H m') -> apresent H m a -> apresent H m' a.
Proof.
  intros H m m' a Hg [Hh [b Hb]]. split; [exact Hh|].
  assert (Hm : mrestrict H m (Z_to_bv 64 a) <> None) by (unfold mrestrict; rewrite Hh, Hb; discriminate).
  pose proof (Hg _ Hm) as Hm'. unfold mrestrict in Hm'. rewrite Hh in Hm'.
  destruct (m' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity | exfalso; apply Hm'; reflexivity].
Qed.

Lemma mw_grows_aview : forall (H : word -> bool) (m m' : word -> option byte) a,
  mem_grows (mrestrict H m) (mrestrict H m') -> aview tfibsegs H m a <> None -> aview tfibsegs H m' a <> None.
Proof.
  intros H m m' a Hg Hv. unfold aview, mbyte in *.
  destruct (mrestrict H m (Z_to_bv 64 a)) eqn:E1.
  - assert (H' : mrestrict H m' (Z_to_bv 64 a) <> None) by (apply Hg; rewrite E1; discriminate).
    destruct (mrestrict H m' (Z_to_bv 64 a)); [discriminate | exfalso; apply H'; reflexivity].
  - destruct (mrestrict H m' (Z_to_bv 64 a)); [discriminate | exact Hv].
Qed.

(* writability is carried by presence: either the byte is in memory, or the image's writable segment gives it *)
Lemma mw_writable_grows : forall (H : word -> bool) (m m' : word -> option byte) a,
  (forall x, mrestrict H m x <> None -> mrestrict H m' x <> None) ->
  writable_at tfibsegs (mrestrict H m) a -> writable_at tfibsegs (mrestrict H m') a.
Proof.
  intros H m m' a Hg Hw. unfold writable_at, wview in *.
  destruct (mrestrict H m (Z_to_bv 64 a)) eqn:E1.
  - assert (H' : mrestrict H m' (Z_to_bv 64 a) <> None) by (apply Hg; rewrite E1; discriminate).
    destruct (mrestrict H m' (Z_to_bv 64 a)); [discriminate | exfalso; apply H'; reflexivity].
  - destruct (mrestrict H m' (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.

Lemma mw_apresent_restrict : forall (H : word -> bool) (m m' : word -> option byte),
  (forall a, apresent H m a -> apresent H m' a) ->
  forall x, mrestrict H m x <> None -> mrestrict H m' x <> None.
Proof.
  intros H m m' Hp x Hx. unfold mrestrict in *.
  destruct (H x) eqn:Hh; [exfalso; apply Hx; reflexivity|].
  destruct (m x) as [b|] eqn:Hb; [|exfalso; apply Hx; reflexivity].
  assert (Ha : apresent H m (bv_unsigned x)) by (unfold apresent; rewrite Z_to_bv_bv_unsigned, Hh, Hb; split; [reflexivity | exists b; reflexivity]).
  destruct (Hp _ Ha) as [_ [b' Hb']]. rewrite Z_to_bv_bv_unsigned in Hb'. rewrite Hb'. discriminate.
Qed.

(* ==========================================================================
   2. One symbolic phase lifted to SRr, exposing that the memory only grows
   ========================================================================== *)

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma mw_phase : forall (W : world tfibsegs) E ss ss' st ms md,
  st_ok tfibsegs E ss (restrict (w_H W) ms) ->
  sym_runN tfibsegs tbl_mw FUEL ss = (ss', st) -> st <> RS_ecall ->
  SRr tfibsegs W (mkCfg ms md)
    (fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
       st_ok tfibsegs E ss' (restrict (w_H W) ms1) /\
       frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\
       frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1)) /\
       mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
  intros W E ss ss' st ms md HS Hrun Hne.
  destruct (msteps_run_gen tfibsegs tbl_mw tbl_mw_ok FUEL E ss ss' st _ HS Hrun) as (msr' & Hms & HS' & Hfr).
  apply (SRr_msteps tfibsegs AF0x.Hwx_tfa W ms msr' md _ Hms).
  intros model' Hsame Hcl.
  rewrite (same_but_materialized_wvb md model' Hsame).
  pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
  apply SRr_ret. split; [reflexivity|].
  exists (unrestrict (w_H W) (ms_mem ms) msr'), (m_vm_materialized model'). split; [reflexivity|].
  assert (Hm : mrestrict (w_H W) (ms_mem (unrestrict (w_H W) (ms_mem ms) msr')) = ms_mem msr')
    by (change (mrestrict (w_H W) (ms_mem (unrestrict (w_H W) (ms_mem ms) msr')))
          with (ms_mem (restrict (w_H W) (unrestrict (w_H W) (ms_mem ms) msr'))); rewrite Hrr; reflexivity).
  split; [rewrite Hrr; destruct st as [| |why]; [exact HS' | exfalso; apply Hne; reflexivity | exact HS'] |].
  split; [cbn [unrestrict ms_mem]; apply frame_of_unrestrict; exact Hfr |].
  rewrite Hm. split; [exact Hfr|].
  exact (msteps_mem_grows tfibsegs _ _ Hms).
Qed.

Lemma mw_phase_to : forall (W : world tfibsegs) E stop ss ss' st ms md,
  st_ok tfibsegs E ss (restrict (w_H W) ms) ->
  sym_run_toN tfibsegs tbl_mw FUEL stop ss = (ss', st) -> st <> RS_ecall ->
  SRr tfibsegs W (mkCfg ms md)
    (fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
       st_ok tfibsegs E ss' (restrict (w_H W) ms1) /\
       frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\
       frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1)) /\
       mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
  intros W E stop ss ss' st ms md HS Hrun Hne.
  destruct (msteps_run_to_gen tfibsegs tbl_mw tbl_mw_ok FUEL stop E ss ss' st _ HS Hrun) as (msr' & Hms & HS' & Hfr).
  apply (SRr_msteps tfibsegs AF0x.Hwx_tfa W ms msr' md _ Hms).
  intros model' Hsame Hcl.
  rewrite (same_but_materialized_wvb md model' Hsame).
  pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
  apply SRr_ret. split; [reflexivity|].
  exists (unrestrict (w_H W) (ms_mem ms) msr'), (m_vm_materialized model'). split; [reflexivity|].
  assert (Hm : mrestrict (w_H W) (ms_mem (unrestrict (w_H W) (ms_mem ms) msr')) = ms_mem msr')
    by (change (mrestrict (w_H W) (ms_mem (unrestrict (w_H W) (ms_mem ms) msr')))
          with (ms_mem (restrict (w_H W) (unrestrict (w_H W) (ms_mem ms) msr'))); rewrite Hrr; reflexivity).
  split; [rewrite Hrr; destruct st as [| |why]; [exact HS' | exfalso; apply Hne; reflexivity | exact HS'] |].
  split; [cbn [unrestrict ms_mem]; apply frame_of_unrestrict; exact Hfr |].
  rewrite Hm. split; [exact Hfr|].
  exact (msteps_mem_grows tfibsegs _ _ Hms).
Qed.

(* the facts of a state are only used to decide branches: dropping them keeps st_ok *)
Lemma mw_st_ok_nofacts : forall E ss ms,
  st_ok tfibsegs E ss ms -> st_ok tfibsegs E (mkSS (ss_pc ss) (ss_regs ss) (ss_mem ss) (ss_resv ss) (mkFacts [] [] [])) ms.
Proof.
  intros E ss ms (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & _).
  unfold st_ok. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts]. repeat (split; [assumption|]). split; [exact I | split; exact I].
Qed.

End g.

(* ==========================================================================
   3. What every step of the walk keeps: AR, the bytes outside the contract's written set, presence
   ========================================================================== *)

Section inv. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Variables (ly : alayout) (S : astate) (W : world tfibsegs) (sp0 f : Z) (mem0 : word -> option byte) (md0 : Model).

Definition mw_chg (a : Z) : Prop :=
  (sp0 - AMW_STK <= a < sp0) \/ (f <= a < f + AMF_ZEROED) \/
  (amf_buf link_amf <= a < amf_buf link_amf + amf_size link_amf) \/ (as_errno B <= a < as_errno B + 4).

Definition INV (mem : word -> option byte) (md : Model) : Prop :=
  AR tfibsegs B ly S W mem md /\ same_but_materialized md0 md /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ mw_chg a -> aview tfibsegs (w_H W) mem a = aview tfibsegs (w_H W) mem0 a) /\
  (forall a, apresent (w_H W) mem0 a -> apresent (w_H W) mem a) /\
  (forall a, sp0 - AMW_STK <= a < sp0 -> apresent (w_H W) mem a).

Lemma INV_init : AR tfibsegs B ly S W mem0 md0 -> (forall a, sp0 - AMW_STK <= a < sp0 -> apresent (w_H W) mem0 a) ->
  INV mem0 md0.
Proof.
  intros HAR Hp. split; [exact HAR|]. split; [apply same_but_materialized_refl|]. split; [intros; reflexivity|].
  split; [intros a Ha; exact Ha | exact Hp].
Qed.

(* a symbolic phase whose writable windows lie in the written set, off the runtime's bytes and off the shadow band *)
Lemma INV_run : forall (OKw : Z -> Prop) mem md mem' mat,
  INV mem md ->
  (forall x : word, ~ OKw (bv_unsigned x) -> mem' x = mem x) ->
  (forall x : word, ~ OKw (bv_unsigned x) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  (forall a, OKw a -> mw_chg a /\ ~ aowned B ly S a /\ ~ in_band_rw a) ->
  INV mem' (with_vm_backing (m_vm_lazy md) mat md).
Proof.
  intros OKw mem md mem' mat (HAR & Hsbm & Hfr & Hpr & Hwp) Hraw Hres Hgr Hok.
  assert (AV : forall a, 0 <= a < 2 ^ 64 -> ~ OKw a -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a).
  { intros a Ha Hn. apply aview_eq_of. apply Hres. rewrite unsigned_lit_small by lia. exact Hn. }
  pose proof (same_but_materialized_frame md _ (with_vm_backing_same md mat)) as MF.
  split; [|split; [|split; [|split]]].
  - apply (al_frame _ _ LAWS ly S W mem md mem' _ HAR).
    + intros a Ha Hown. apply AV; [exact Ha|]. intros Hk. exact (proj1 (proj2 (Hok a Hk)) Hown).
    + intros a Hv. exact (mw_grows_aview _ _ _ a Hgr Hv).
    + apply MF. + apply MF. + apply MF.
    + intros a Hb Hh. apply Hraw. unfold YG0d.w64. rewrite unsigned_lit_small by (apply in_band_rw_u64; exact Hb).
      intros Hk. exact (proj2 (proj2 (Hok a Hk)) Hb).
  - eapply same_but_materialized_trans; [exact Hsbm | apply with_vm_backing_same].
  - intros a Ha Hn. rewrite AV; [apply Hfr; assumption | exact Ha | intros Hk; exact (Hn (proj1 (Hok a Hk)))].
  - intros a Ha. apply (mw_grows_apresent _ _ _ _ Hgr). apply Hpr. exact Ha.
  - intros a Ha. apply (mw_grows_apresent _ _ _ _ Hgr). apply Hwp. exact Ha.
Qed.

(* a called contract whose written set lies in mwrite's *)
Lemma INV_call : forall (Kc : Z -> Prop) mem md mem' md',
  INV mem md -> AR tfibsegs B ly S W mem' md' -> same_but_materialized md md' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Kc a -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
  (forall a, Kc a -> mw_chg a) ->
  INV mem' md'.
Proof.
  intros Kc mem md mem' md' (HAR & Hsbm & Hfr & Hpr & Hwp) HAR' Hsbm' Hk Hp HK.
  split; [exact HAR'|]. split; [eapply same_but_materialized_trans; [exact Hsbm | exact Hsbm']|].
  split; [intros a Ha Hn; rewrite Hk; [apply Hfr; assumption | exact Ha | intros Hc; exact (Hn (HK a Hc))]|].
  split; [intros a Ha; apply Hp; apply Hpr; exact Ha | intros a Ha; apply Hp; apply Hwp; exact Ha].
Qed.

(* the return: the post of the contract, with its FILE part P *)
Lemma mw_finish : forall regs0 extra E ss ms md (P : bvmap 5 word -> (word -> option byte) -> Prop),
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> clookup tbl_mw (ss_pc ss) = Some RET_WORD_r ->
  sr_get (ss_regs ss) 1 = SOff 1 0 ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) CALLEE_SAVED = true ->
  env_agree 32 (Ereg regs0 extra) E -> YK0s.ret_ok (getr regs0 1) ->
  INV (ms_mem ms) md -> P (ms_regs ms) (ms_mem ms) ->
  SRr tfibsegs W (mkCfg ms md) (fun W' c' => W' = W /\ exists regs' mem' md',
     c' = cfg_at tfibsegs (raZ regs0) regs' mem' md' /\
     AR tfibsegs B ly S W mem' md' /\ aregs_preserved regs0 regs' /\ same_but_materialized md0 md' /\
     P regs' mem' /\
     (forall a, 0 <= a < 2 ^ 64 -> ~ mw_chg a -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem0 a) /\
     (forall a, apresent (w_H W) mem0 a -> apresent (w_H W) mem' a) /\
     (forall a, sp0 - AMW_STK <= a < sp0 -> apresent (w_H W) mem' a)).
Proof.
  intros regs0 extra E ss ms md P HS Hrv Hpc Hra Hcs HAE Hret (HAR & Hsbm & Hfr & Hpr & Hwp) HP.
  eapply (SRr_ret_at tfibsegs tbl_mw tbl_mw_ok AF0x.Hwx_tfa W E ss ms md _ HS Hrv Hpc).
  intros mat'. split; [reflexivity|].
  exists (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy md) mat' md).
  pose proof (same_but_materialized_frame md _ (with_vm_backing_same md mat')) as MF.
  split.
  { unfold cfg_at. do 2 f_equal.
    rewrite (st_ok_restrict_reg tfibsegs (w_H W) E ss ms 1 HS), Hra. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
    destruct HAE as [HA _]. rewrite (HA 1%nat ltac:(lia)). rewrite (ew_Ereg_nat regs0 extra 1 1%bv eq_refl).
    unfold raZ, YG0d.w64. rewrite Z_to_bv_bv_unsigned. exact Hret. }
  split; [apply (al_frame _ _ LAWS ly S W (ms_mem ms) md (ms_mem ms) _ HAR);
          [intros; reflexivity | intros a Hv; exact Hv | apply MF | apply MF | apply MF | intros; reflexivity]|].
  split; [exact (aregs_preserved_of_st_ok (w_H W) E ss ms regs0 extra HS HAE Hcs)|].
  split; [eapply same_but_materialized_trans; [exact Hsbm | apply with_vm_backing_same]|].
  split; [exact HP|]. split; [exact Hfr|]. split; [exact Hpr | exact Hwp].
Qed.

End inv.

(* ==========================================================================
   4. The symbolic states of the walk (k > 0) and their runs
   Atoms: 0..31 the entry registers; 32 the entry wpos (f + 280 + k); after the inner call 33..38 the cookie's
   pos / len, the flags, wend / wpos / wbase as the inner call left them, 39..54 the clobbered registers (43 = a0,
   the inner call's result n1); after the copy 55..70 the clobbered registers and 71 the copied count n2 (s0).
   ========================================================================== *)

(* the entry: the frame mwrite pushes, and the FILE words +0x24..+0x3c read and write *)
Definition R_stkA : YP09.region := YP09.mkRegion (Some 2%nat) (-48) 0 (-48) 0 [].
Definition R_fileA : YP09.region := YP09.mkRegion (Some 10%nat) 0 272 40 48
  [YP09.mkChunk 40 (CVal 8 (SOff 32 0)); YP09.mkChunk 56 (CVal 8 (SOff 10 280)); YP09.mkChunk 152 (CVal 8 (SOff 10 232))].
Definition ssA : sstate := mkSS LA_MWRITE sr_atoms [R_stkA; R_fileA] None (mkFacts [] [] []).
Definition ssA_st1 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tbl_mw FUEL ssA).
Lemma runA1 : sym_runN tfibsegs tbl_mw FUEL ssA = (ssA_st1, RS_stopped (SR_branch BC_EQ (SOff 32 0) (SOff 10 280))).
Proof. vm_compute. reflexivity. Qed.
Definition ssA1 : sstate := Eval vm_compute in YP06.add_cond ssA_st1 (mkAC BC_NE (SOff 32 0) (SOff 10 280)).
Lemma ssA1_eq : YP06.add_cond ssA_st1 (mkAC (neg_bc BC_EQ) (SOff 32 0) (SOff 10 280)) = ssA1.
Proof. vm_compute. reflexivity. Qed.
Definition ssA_end : sstate := Eval vm_compute in fst (sym_run_toN tfibsegs tbl_mw FUEL LA_MWRITE ssA1).
Lemma runA2 : sym_run_toN tfibsegs tbl_mw FUEL LA_MWRITE ssA1 = (ssA_end, RS_running).
Proof. vm_compute. reflexivity. Qed.

(* after the inner call (+0x50): the frame, the FILE words the rest reads or writes, and errno *)
Definition RF_fl : YP09.region := YP09.mkRegion (Some 10%nat) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SOff 35 0))].
Definition RF_win : YP09.region := YP09.mkRegion (Some 10%nat) 32 48 32 48
  [YP09.mkChunk 32 (CVal 8 (SOff 36 0)); YP09.mkChunk 40 (CVal 8 (SOff 37 0))].
Definition RF_wb : YP09.region := YP09.mkRegion (Some 10%nat) 56 64 56 64 [YP09.mkChunk 56 (CVal 8 (SOff 38 0))].
Definition RF_ck : YP09.region := YP09.mkRegion (Some 10%nat) 232 272 232 248
  [YP09.mkChunk 232 (CVal 8 (SOff 33 0)); YP09.mkChunk 240 (CVal 8 (SOff 34 0));
   YP09.mkChunk 248 (CVal 8 (SLit 4096)); YP09.mkChunk 256 (CVal 8 (SLit 0x62fee0)); YP09.mkChunk 264 (CVal 4 (SLit 119))].
Definition R_errno : YP09.region := YP09.mkRegion (Some 4%nat) (-164) (-160) (-164) (-160) [].
Definition R_stkC : YP09.region := Eval vm_compute in hd R_stkA (ss_mem ssA_end).
Definition rsC : smem := [R_stkC; RF_fl; RF_win; RF_wb; RF_ck; R_errno].
Definition ssC : sstate := Eval vm_compute in
  mkSS 0x96d10 (sr_sets (ss_regs ssA_end) ([] ++ junk_upd 39 CLOB)) rsC None (ss_facts ssA_end).
Lemma ssC_eq : mkSS 0x96d10 (sr_sets (ss_regs ssA_end) ([] ++ junk_upd 39 CLOB)) rsC None (ss_facts ssA_end) = ssC.
Proof. vm_compute. reflexivity. Qed.

(* s3 = wpos - wbase as the run writes it, and s3 = size - pos1 *)
Definition SK3 : sv := SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 10 0) (SLit (-1))) (SLit (-280))) (SOff 32 0).
Definition SKA2 : sv := SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 10 0) (SLit 18446744073709551615)) (SLit (-280))) (SOff 32 0).
Definition SROOM : sv := SAlu ALU_SUB (SLit 0) (SOff 33 (-4096)).

Definition ssC_st1 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tbl_mw FUEL ssC).
Lemma runC1 : sym_runN tfibsegs tbl_mw FUEL ssC = (ssC_st1, RS_stopped (SR_branch BC_GEU (SOff 43 0) SK3)).
Proof. vm_compute. reflexivity. Qed.
Definition ssC_lt : sstate := Eval vm_compute in YP06.add_cond ssC_st1 (mkAC BC_LTU (SOff 43 0) SK3).
Lemma ssC_lt_eq : YP06.add_cond ssC_st1 (mkAC (neg_bc BC_GEU) (SOff 43 0) SK3) = ssC_lt.
Proof. vm_compute. reflexivity. Qed.
Definition ssC_ret : sstate := Eval vm_compute in fst (sym_runN tfibsegs tbl_mw FUEL ssC_lt).
Lemma runC_lt : sym_runN tfibsegs tbl_mw FUEL ssC_lt = (ssC_ret, RS_stopped (SR_jalr (SOff 1 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ssC_ge : sstate := Eval vm_compute in YP06.add_cond ssC_st1 (mkAC BC_GEU (SOff 43 0) SK3).
Definition ssC_st2 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tbl_mw FUEL ssC_ge).
Lemma runC2 : sym_runN tfibsegs tbl_mw FUEL ssC_ge = (ssC_st2, RS_stopped (SR_branch BC_GEU SROOM (SOff 12 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ssC_n : sstate := Eval vm_compute in YP06.add_cond ssC_st2 (mkAC BC_GEU SROOM (SOff 12 0)).
Definition ssC_e : sstate := Eval vm_compute in YP06.add_cond ssC_st2 (mkAC BC_LTU SROOM (SOff 12 0)).
Lemma ssC_e_eq : YP06.add_cond ssC_st2 (mkAC (neg_bc BC_GEU) SROOM (SOff 12 0)) = ssC_e.
Proof. vm_compute. reflexivity. Qed.
Definition ssM1 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tbl_mw FUEL ssC_n).
Lemma runM1 : sym_runN tfibsegs tbl_mw FUEL ssC_n = (ssM1, RS_stopped SR_fetch).
Proof. vm_compute. reflexivity. Qed.
Definition ssM2 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tbl_mw FUEL ssC_e).
Lemma runM2 : sym_runN tfibsegs tbl_mw FUEL ssC_e = (ssM2, RS_stopped SR_fetch).
Proof. vm_compute. reflexivity. Qed.

(* after the copy (+0xc4): the frame and the cookie; s0 (the copied count) abstracted to atom 71, facts dropped *)
Definition rsD : smem := Eval vm_compute in [hd R_stkA (ss_mem ssM1); nth 4 (ss_mem ssM1) R_stkA].
Definition ssD : sstate := Eval vm_compute in
  mkSS 0x96d84 (sr_set (sr_sets (ss_regs ssM1) (junk_upd 55 CLOB)) 8 (SOff 71 0)) rsD None (mkFacts [] [] []).
Lemma ssD_1 : mkSS 0x96d84 (sr_set (sr_sets (ss_regs ssM1) (junk_upd 55 CLOB)) 8 (SOff 71 0)) rsD None (mkFacts [] [] []) = ssD.
Proof. vm_compute. reflexivity. Qed.
Lemma ssD_2 : mkSS 0x96d84 (sr_set (sr_sets (ss_regs ssM2) (junk_upd 55 CLOB)) 8 (SOff 71 0)) rsD None (mkFacts [] [] []) = ssD.
Proof. vm_compute. reflexivity. Qed.

Definition SNP : sv := SAlu ALU_ADD (SOff 33 0) (SOff 71 0).
Definition ssD_st1 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tbl_mw FUEL ssD).
Lemma runD1 : sym_runN tfibsegs tbl_mw FUEL ssD = (ssD_st1, RS_stopped (SR_branch BC_GEU (SOff 34 0) SNP)).
Proof. vm_compute. reflexivity. Qed.
Definition ssD_ge : sstate := Eval vm_compute in YP06.add_cond ssD_st1 (mkAC BC_GEU (SOff 34 0) SNP).
Definition ssD_ret1 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tbl_mw FUEL ssD_ge).
Lemma runD_ge : sym_runN tfibsegs tbl_mw FUEL ssD_ge = (ssD_ret1, RS_stopped (SR_jalr (SOff 1 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ssD_lt : sstate := Eval vm_compute in YP06.add_cond ssD_st1 (mkAC BC_LTU (SOff 34 0) SNP).
Lemma ssD_lt_eq : YP06.add_cond ssD_st1 (mkAC (neg_bc BC_GEU) (SOff 34 0) SNP) = ssD_lt.
Proof. vm_compute. reflexivity. Qed.
Definition ssD_st2 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tbl_mw FUEL ssD_lt).
Lemma runD2 : sym_runN tfibsegs tbl_mw FUEL ssD_lt = (ssD_st2, RS_stopped (SR_branch BC_GEU SNP (SLit 4096))).
Proof. vm_compute. reflexivity. Qed.
Definition ssD_ge2 : sstate := Eval vm_compute in YP06.add_cond ssD_st2 (mkAC BC_GEU SNP (SLit 4096)).
Definition ssD_ret2 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tbl_mw FUEL ssD_ge2).
Lemma runD_ge2 : sym_runN tfibsegs tbl_mw FUEL ssD_ge2 = (ssD_ret2, RS_stopped (SR_jalr (SOff 1 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ssD_lt2 : sstate := Eval vm_compute in YP06.add_cond ssD_st2 (mkAC BC_LTU SNP (SLit 4096)).
Lemma ssD_lt2_eq : YP06.add_cond ssD_st2 (mkAC (neg_bc BC_GEU) SNP (SLit 4096)) = ssD_lt2.
Proof. vm_compute. reflexivity. Qed.
Definition ssD_sb : sstate := Eval vm_compute in fst (sym_runN tfibsegs tbl_mw FUEL ssD_lt2).
Lemma runD_sb : sym_runN tfibsegs tbl_mw FUEL ssD_lt2 = (ssD_sb, RS_stopped (SR_addr (SAlu ALU_ADD (SOff 33 6487776) (SOff 71 0)))).
Proof. vm_compute. reflexivity. Qed.
(* +0xec sb zero,0(a0) is done by hand (its address is not a region of the state); then the epilogue *)
Definition ssD_af : sstate := Eval vm_compute in mkSS (ss_pc ssD_sb + 4) (sr_sets (ss_regs ssD_sb) (junk_upd 72 [])) (ss_mem ssD_sb) None (ss_facts ssD_sb).
Definition ssD_ret3 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tbl_mw FUEL ssD_af).
Lemma runD_af : sym_runN tfibsegs tbl_mw FUEL ssD_af = (ssD_ret3, RS_stopped (SR_jalr (SOff 1 0))).
Proof. vm_compute. reflexivity. Qed.

Lemma mw_ret_word : forall ss, ss = ssC_ret \/ ss = ssD_ret1 \/ ss = ssD_ret2 \/ ss = ssD_ret3 ->
  ss_resv ss = None /\ clookup tbl_mw (ss_pc ss) = Some RET_WORD_r /\ sr_get (ss_regs ss) 1 = SOff 1 0 /\
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) CALLEE_SAVED = true.
Proof. intros ss [-> | [-> | [-> | ->]]]; vm_compute; repeat split; reflexivity. Qed.

(* ==========================================================================
   5. Values the runs compute, link's image, regions, the FILE rebuilt, and the hand step at +0xec
   ========================================================================== *)

Lemma zc_eq : forall z q r, z = q * 2 ^ 64 + r -> 0 <= r < 2 ^ 64 -> zcanon z = r.
Proof. intros z q r -> Hr. unfold zcanon, M64. rewrite Z.add_comm, Z_mod_plus_full. apply Z.mod_small. exact Hr. Qed.

(* s3 (and a2) at +0x38..+0x48: wpos - wbase *)
Lemma vl_k : forall E fv kk, bv_unsigned (ew E 10) = fv -> ew E 32 = Z_to_bv 64 (fv + 280 + kk) ->
  0 < fv -> 0 <= kk -> fv + 280 + kk < 2 ^ 64 -> U E SK3 = kk /\ U E SKA2 = kk.
Proof.
  intros E fv kk H10 H32 Hf Hk Hr. unfold SK3, SKA2.
  rewrite !U_SAlu. cbn [zalu_raw]. rewrite !U_SMd. cbn [zmd_raw].
  rewrite !U_SLit, !U_SOff, H10, H32, unsigned_lit_small, !Z.add_0_r by lia.
  rewrite (zc_eq fv 0 fv), (zc_eq (fv + 280 + kk) 0 (fv + 280 + kk)), (zc_eq (-280) (-1) (2 ^ 64 - 280)) by lia.
  rewrite (zc_eq (-1) (-1) (2 ^ 64 - 1)), (zc_eq 18446744073709551615 0 (2 ^ 64 - 1)) by lia.
  rewrite (zc_eq (fv * (2 ^ 64 - 1)) (fv - 1) (2 ^ 64 - fv)) by lia.
  rewrite (zc_eq (2 ^ 64 - fv + (2 ^ 64 - 280)) 1 (2 ^ 64 - fv - 280)) by lia.
  split; apply (zc_eq _ 1 kk); lia.
Qed.

(* s3 at +0x7c: size - pos1 *)
Lemma vl_room : forall E p, ew E 33 = Z_to_bv 64 p -> 0 <= p <= 4096 -> U E SROOM = 4096 - p.
Proof.
  intros E p H33 Hp. unfold SROOM. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, U_SOff, H33, unsigned_lit_small by lia.
  rewrite (zc_eq 0 0 0) by lia.
  destruct (Z.eq_dec p 4096) as [-> | Hne].
  - rewrite (zc_eq (4096 + -4096) 0 0) by lia. apply (zc_eq _ 0 0); lia.
  - rewrite (zc_eq (p + -4096) (-1) (2 ^ 64 + p - 4096)) by lia. apply (zc_eq _ (-1) (4096 - p)); lia.
Qed.

(* the new pos (+0xcc) and the NUL's address (+0xe8) *)
Lemma vl_np : forall E p m c, ew E 33 = Z_to_bv 64 p -> ew E 71 = Z_to_bv 64 m -> 0 <= p -> 0 <= m -> 0 <= c ->
  c + p + m < 2 ^ 64 -> U E (SAlu ALU_ADD (SOff 33 c) (SOff 71 0)) = c + p + m.
Proof.
  intros E p m c H33 H71 Hp Hm Hc Hr. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, H33, H71, !unsigned_lit_small by lia.
  rewrite Z.add_0_r. rewrite (zc_eq (p + c) 0 (p + c)), (zc_eq m 0 m) by lia. apply (zc_eq _ 0 (c + p + m)); lia.
Qed.

(* the flags after +0x90..+0x98 on a FILE whose flags are F_NORD or F_NORD | F_ERR *)
Lemma vl_flags : forall E fv, ew E 35 = Z_to_bv 64 fv -> fv = AF_NORD \/ fv = AF_NORD + AF_ERR ->
  sv_denot E (SAlu ALU_OR (SExt true 32 (SOff 35 0)) (SLit 32)) = Z_to_bv 64 (AF_NORD + AF_ERR).
Proof.
  intros E fv H35 Hf. rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SExt, U_SLit, U_SOff, H35.
  unfold AF_NORD, AF_ERR in *. destruct Hf as [-> | ->]; rewrite unsigned_lit_small by lia; vm_compute; reflexivity.
Qed.

(* link's four load segments, by evaluation (the idiom of wms_seg_table / wms_img_full in
   (internal path) (internal record, sha256 5332f18fa29b); the numerals here are
   checked by vm_compute against tfibsegs, link's image) *)
Lemma mw_seg_table : map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs =
  [(65536, 135168); (200704, 458752); (659456, 8192); (667648, 5967872)].
Proof. vm_compute. reflexivity. Qed.

Lemma mw_img_full : forall a, 0x10000 <= a < 0x654000 -> YG0d.in_img tfibsegs a.
Proof.
  intros a Ha. pose proof mw_seg_table as Hm. unfold YG0d.in_img.
  destruct tfibsegs as [|s0 [|s1 [|s2 [|s3 [|s4 l]]]]]; cbn [map] in Hm; try discriminate Hm.
  injection Hm as E0 F0 E1 F1 E2 F2 E3 F3.
  destruct (Z_lt_le_dec a 200704). { exists s0. split; [left; reflexivity | lia]. }
  destruct (Z_lt_le_dec a 659456). { exists s1. split; [right; left; reflexivity | lia]. }
  destruct (Z_lt_le_dec a 667648). { exists s2. split; [right; right; left; reflexivity | lia]. }
  exists s3. split; [right; right; right; left; reflexivity | lia].
Qed.

Lemma mw_errno_owned_chk : forallb (fun r => (fst r + snd r <=? 0x631b6c) || (0x631b70 <=? fst r)) Tfib_owned_static = true.
Proof. vm_compute. reflexivity. Qed.

Lemma mw_wz_errno : wseg_ok tfibsegs (Z_to_bv 64 0x631b6c) (Z.to_nat 4) = true.
Proof. vm_compute. reflexivity. Qed.

(* errno is a byte of the image's writable segment (the store_ok_all / store_ok_wseg route of AE23.v wseg_writable) *)
Lemma mw_errno_writable : forall m a, 0x631b6c <= a < 0x631b70 -> writable_at tfibsegs m a.
Proof.
  intros m a Ha. unfold writable_at.
  apply (store_ok_all tfibsegs m (Z.to_nat 4) (Z_to_bv 64 0x631b6c));
  [rewrite unsigned_lit_small by lia; rewrite Z2Nat.id by lia; lia
  | apply store_ok_wseg; exact mw_wz_errno
  | rewrite !unsigned_lit_small by lia; rewrite Z2Nat.id by lia; lia].
Qed.

Section rg. Context {fx : YK11.FPState}.

Lemma mw_region_ok : forall E ss ms (H : word -> bool) i r,
  st_ok tfibsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
  region_ok tfibsegs E (mrestrict H (ms_mem ms)) r.
Proof.
  intros E ss ms H i r HS Hi. destruct (st_ok_mem_ok tfibsegs E ss _ HS) as (_ & Hok & _).
  rewrite Forall_forall in Hok. apply Hok. eapply nth_error_In. exact Hi.
Qed.

Lemma mw_reg_atom : forall E ss ms (H : word -> bool) r n,
  st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 -> getr (ms_regs ms) r = ew E n.
Proof.
  intros E ss ms H r n HS Hr. rewrite (st_ok_restrict_reg tfibsegs H E ss ms r HS), Hr. cbn [sv_denot].
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma mw_reg_sv : forall E ss ms (H : word -> bool) r e,
  st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = e -> getr (ms_regs ms) r = sv_denot E e.
Proof. intros E ss ms H r e HS Hr. rewrite (st_ok_restrict_reg tfibsegs H E ss ms r HS), Hr. reflexivity. Qed.

Lemma mw_cval : forall E ss ms (H : word -> bool) i r j off (n : N) e v,
  st_ok tfibsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
  nth_error (YP09.r_chunks r) j = Some (YP09.mkChunk off (CVal n e)) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
  val_mem tfibsegs (mrestrict H (ms_mem ms)) (base_val E (YP09.r_base r) + off) (N.to_nat n) v.
Proof.
  intros E ss ms H i r j off n e v HS Hi Hj He Hv Hn.
  destruct (mw_region_ok E ss ms H i r HS Hi) as (_ & _ & _ & Hcs).
  rewrite Forall_forall in Hcs. apply (val_of_chunk_ok tfibsegs E _ _ off n e v); [| exact He | exact Hv | exact Hn].
  apply Hcs. eapply nth_error_In. exact Hj.
Qed.

End rg.

Lemma mw_region_kept : forall E (H : word -> bool) (m m' : word -> option byte) r,
  (forall a, base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r ->
     aview tfibsegs H m' a = aview tfibsegs H m a) ->
  (forall x, mrestrict H m x <> None -> mrestrict H m' x <> None) ->
  region_kept tfibsegs E (mrestrict H m) (mrestrict H m') r.
Proof.
  intros E H m m' r Hv Hg. split.
  - intros a Ha. apply mbyte_of_aview. apply Hv. exact Ha.
  - intros a _ Hw. exact (mw_writable_grows H m m' a Hg Hw).
Qed.

(* the FILE words the walk writes after the inner call: flags, wend / wpos, wbase, the cookie's pos / len *)
Definition dynf (o : Z) : Prop := (0 <= o < 4) \/ (32 <= o < 48) \/ (56 <= o < 64) \/ (232 <= o < 248).

Lemma amf_at_rebuild : forall (m m' : word -> option byte) f fl' wend' wpos' wbase' pos' len',
  amemfile_at tfibsegs link_amf m f ->
  (forall a, f <= a < f + AMF_ZEROED -> ~ dynf (a - f) -> mbyte tfibsegs m' a = mbyte tfibsegs m a) ->
  (fl' = AF_NORD \/ fl' = AF_NORD + AF_ERR) -> val_mem tfibsegs m' (f + 0) 4 fl' ->
  ((wend' = 0 /\ wpos' = 0 /\ wbase' = 0) \/ (wend' = f + AMF_BUF + AMF_BUFSIZ /\ wpos' = f + AMF_BUF /\ wbase' = f + AMF_BUF)) ->
  val_mem tfibsegs m' (f + 32) 8 wend' -> val_mem tfibsegs m' (f + 40) 8 wpos' -> val_mem tfibsegs m' (f + 56) 8 wbase' ->
  0 <= pos' <= len' -> len' <= amf_size link_amf ->
  val_mem tfibsegs m' (f + AMF_COOKIE) 8 pos' -> val_mem tfibsegs m' (f + (AMF_COOKIE + 8)) 8 len' ->
  amf_k tfibsegs link_amf m' f 0.
Proof.
  intros m m' f fl' wend' wpos' wbase' pos' len' (Hf0 & Hf1 & Hf2 & Hs & Hfl & Hom & Hw & Hc) Hfr Hfl' V0 Hwv
    V32 V40 V56 Hpl Hls V232 V240.
  assert (HV : forall off n v, 0 <= off -> off + Z.of_nat n <= AMF_ZEROED ->
    (forall o, off <= o < off + Z.of_nat n -> ~ dynf o) ->
    val_mem tfibsegs m (f + off) n v -> val_mem tfibsegs m' (f + off) n v).
  { intros off n v H0 H1 Hd Hv. eapply amf_val_mem_frame; [|exact Hv]. intros x Hx. apply Hfr; [lia|]. apply Hd. lia. }
  unfold AMF_ZEROED, AMF_COOKIE, AMF_BUF, AMF_BUFSIZ, dynf in *.
  split.
  - split; [exact Hf0|]. split; [exact Hf1|]. split; [exact Hf2|]. split; [|split; [|split; [|split]]].
    + unfold amemfile_static in *. unfold AMF_COOKIE in *.
      repeat match goal with H : _ /\ _ |- _ => destruct H end.
      repeat match goal with |- _ /\ _ => split end; (apply HV; [lia | cbn; lia | cbn; intros; lia | assumption]).
    + unfold amemfile_flags. destruct Hfl' as [-> | ->]; [left | right]; exact V0.
    + destruct Hom as [H|H]; [left|right]; (apply HV; [lia | cbn; lia | cbn; intros; lia | exact H]).
    + destruct Hw as (H8 & H16 & _). split; [apply HV; [lia | cbn; lia | cbn; intros; lia | exact H8]|].
      split; [apply HV; [lia | cbn; lia | cbn; intros; lia | exact H16]|].
      destruct Hwv as [(-> & -> & ->) | (-> & -> & ->)]; [left | right].
      * split; [|split]; assumption.
      * exists 0. unfold AMF_BUF, AMF_BUFSIZ. split; [lia|]. rewrite Z.add_0_r. split; [|split]; assumption.
    + exists pos', len'. split; [exact Hpl|]. split; [exact Hls|]. split; assumption.
  - unfold amf_win. destruct Hwv as [(-> & -> & ->) | (-> & -> & ->)]; [left | right].
    + split; [reflexivity|]. split; [|split]; assumption.
    + unfold AMF_BUF, AMF_BUFSIZ. split; [lia|]. rewrite Z.add_0_r. split; [|split]; assumption.
Qed.

Lemma mrestrict_munrestrict : forall (H : word -> bool) (full m : word -> option byte),
  mrestrict H (munrestrict H full m) = mrestrict H m.
Proof.
  intros H full m. apply functional_extensionality. intros x. unfold mrestrict, munrestrict. destruct (H x); reflexivity.
Qed.

Section sb. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma mw_restrict_unrestrict : forall (H : word -> bool) full regs pc (m : word -> option byte) rom,
  restrict H (unrestrict H full (mkst regs pc m rom)) = mkst regs pc (mrestrict H m) rom.
Proof. intros H full regs pc m rom. unfold restrict, unrestrict, mkst. cbn. rewrite mrestrict_munrestrict. reflexivity. Qed.

(* +0xec sb zero,0(a0), at an address that is in no region of the state *)
Lemma mw_sb_zero : forall (W : world tfibsegs) E ss ms md Q a,
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = 0x96dac ->
  ss_atoms_lt 72 ss = true -> no_cdata (ss_mem ss) = true ->
  sv_denot E (sr_get (ss_regs ss) 10) = Z_to_bv 64 a -> 0 <= a < 2 ^ 64 - 1 ->
  writable_at tfibsegs (mrestrict (w_H W) (ms_mem ms)) a ->
  (forall r, In r (ss_mem ss) ->
     base_val E (YP09.r_base r) + YP09.r_hi r <= a \/ a < base_val E (YP09.r_base r) + YP09.r_lo r) ->
  (forall ms' mat', st_ok tfibsegs E (mkSS (ss_pc ss + 4) (ss_regs ss) (ss_mem ss) None (ss_facts ss)) (restrict (w_H W) ms') ->
     (forall x : word, bv_unsigned x <> a -> ms_mem ms' x = ms_mem ms x) ->
     (forall x : word, bv_unsigned x <> a -> mrestrict (w_H W) (ms_mem ms') x = mrestrict (w_H W) (ms_mem ms) x) ->
     mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
     SRr tfibsegs W (mkCfg ms' (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
  SRr tfibsegs W (mkCfg ms md) Q.
Proof.
  intros W E ss ms md Q a HS Hrv Hpc Hat Hnc Ha Har Hwr Hout Hk.
  pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E ss ms HS Hrv) as Hshape. rewrite Hpc in Hshape.
  set (regs1 := ms_regs ms) in *. set (m1 := ms_mem ms) in *.
  assert (R10 : getr regs1 10 = Z_to_bv 64 a) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E ss ms 10 HS); exact Ha).
  assert (Hfetch : fetch_word tfibsegs (Z_to_bv 64 0x96dac) = Some (0x00050023%bv : bv 32)).
  { replace (0x00050023%bv : bv 32) with (Z_to_bv 32 0x00050023) by (apply bv_eq; reflexivity).
    apply (tbl_mw_ok 0x96dac 0x00050023). vm_compute. reflexivity. }
  assert (Hdec : decode_any (0x00050023%bv : bv 32) = Some (Store SZ1 10 0 0, 4%Z)) by vm_refl_bv.
  assert (Haddr : v_addi (getr regs1 10) (bv_signed (0%bv : bv 12)) = Z_to_bv 64 a).
  { rewrite R10. apply bv_eq. unfold v_addi. rewrite !Z_to_bv_unsigned. change (bv_signed (0%bv : bv 12)) with 0.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.add_0_r, Z.mod_mod by lia. reflexivity. }
  assert (Hok : store_ok tfibsegs (mrestrict (w_H W) m1) (v_addi (getr regs1 10) (bv_signed (0%bv : bv 12))) 1 = true).
  { rewrite Haddr. apply (store_ok_of_all tfibsegs 1 (mrestrict (w_H W) m1) (Z_to_bv 64 a)).
    - rewrite unsigned_lit_small by lia. cbn. lia.
    - intros y Hy. rewrite unsigned_lit_small in Hy by lia. cbn in Hy.
      assert (Ey : y = Z_to_bv 64 a) by (rewrite <- (Z_to_bv_bv_unsigned 64 y); f_equal; lia).
      rewrite Ey. exact Hwr. }
  rewrite Hshape. eapply (SRr_step tfibsegs AF0x.Hwx_tfa W); [reflexivity | |].
  - rewrite restrict_mkst_fx. exact (step_sb tfibsegs regs1 _ _ _ _ 10 0 0 Hfetch eq_refl Hdec Hok).
  - intros model' Hsbm. rewrite (same_but_materialized_wvb md model' Hsbm).
    rewrite Haddr.
    set (bs := word_to_le_bytes 1 (getr regs1 0)).
    assert (Lbs : Z.of_nat (length bs) = 1) by (unfold bs; rewrite length_N_to_le_bytes; reflexivity).
    set (mw := wbytes (mrestrict (w_H W) m1) (Z_to_bv 64 a) bs).
    assert (Mout : forall x : word, bv_unsigned x <> a -> mw x = mrestrict (w_H W) m1 x).
    { intros x Hx. subst mw. destruct (Z_lt_le_dec (bv_unsigned x) a) as [L|L].
      - apply wbytes_below; rewrite ?Lbs, unsigned_lit_small by lia; lia.
      - apply wbytes_above. rewrite Lbs, unsigned_lit_small by lia. lia. }
    assert (Mgr : mem_grows (mrestrict (w_H W) m1) mw) by (subst mw; apply wbytes_grows).
    assert (Mgr' : forall y, mrestrict (w_H W) m1 y <> None -> mrestrict (w_H W) mw y <> None).
    { intros y Hy. assert (Hh : w_H W y = false)
        by (unfold mrestrict in Hy; destruct (w_H W y); [exfalso; apply Hy; reflexivity | reflexivity]).
      unfold mrestrict at 1. rewrite Hh. exact (Mgr y Hy). }
    apply Hk.
    + rewrite mw_restrict_unrestrict.
      replace (v_addi (Z_to_bv 64 0x96dac) 4) with (Z_to_bv 64 (ss_pc ss + 4) : word)
        by (rewrite Hpc; apply bv_eq; unfold v_addi; rewrite !Z_to_bv_unsigned; unfold bv_wrap;
            change (bv_modulus 64) with (2 ^ 64); rewrite Zplus_mod_idemp_l; reflexivity).
      rewrite Hshape in HS. rewrite restrict_mkst_fx in HS.
      pose proof (st_ok_set_regs_mem tfibsegs 72 E E ss regs1 regs1 (Z_to_bv 64 0x96dac) (ss_pc ss + 4)
        (mrestrict (w_H W) m1) (mrestrict (w_H W) mw) (ss_mem ss) [] HS (env_agree_refl 72 E) Hat) as HS2.
      cbn [sr_sets map] in HS2. apply HS2.
      * reflexivity.
      * intros r _. reflexivity.
      * constructor.
      * apply (mem_ok_kept tfibsegs E (mrestrict (w_H W) m1)); [exact (st_ok_mem_ok tfibsegs E ss _ HS) | exact Hnc |].
        apply Forall_forall. intros r Hr. split.
        -- intros b Hb. unfold mbyte.
           assert (Hb0 : 0 <= b < 2 ^ 64) by (destruct (st_ok_mem_ok tfibsegs E ss _ HS) as (_ & Hok2 & _);
               rewrite Forall_forall in Hok2; destruct (Hok2 r Hr) as (Hl & Hh & _); lia).
           assert (Hm : mrestrict (w_H W) mw (Z_to_bv 64 b) = mrestrict (w_H W) m1 (Z_to_bv 64 b)).
           { unfold mrestrict at 1. rewrite Mout by (rewrite unsigned_lit_small by lia; destruct (Hout r Hr); lia).
             unfold mrestrict. destruct (w_H W (Z_to_bv 64 b)); reflexivity. }
           rewrite Hm. reflexivity.
        -- intros b _ Hw. exact (mw_writable_grows (w_H W) m1 mw b Mgr' Hw).
    + intros x Hx. cbn [unrestrict ms_mem mkst]. unfold munrestrict. destruct (w_H W x) eqn:Ex; [reflexivity|].
      rewrite Mout by exact Hx. unfold mrestrict. rewrite Ex. reflexivity.
    + intros x Hx. cbn [unrestrict ms_mem mkst]. rewrite mrestrict_munrestrict. unfold mrestrict at 1.
      destruct (w_H W x) eqn:Ex; [unfold mrestrict; rewrite Ex; reflexivity|].
      rewrite Mout by exact Hx. reflexivity.
    + cbn [unrestrict ms_mem mkst]. rewrite mrestrict_munrestrict. intros y Hy. exact (Mgr' y Hy).
Qed.

End sb.

(* the writable windows of the three state shapes *)
Lemma mw_winA : forall E rs a, windows rs = [(Some 2%nat, -48, 0); (Some 10%nat, 40, 48)] -> in_wrange E rs a ->
  (bv_unsigned (ew E 2) - 48 <= a < bv_unsigned (ew E 2)) \/ (bv_unsigned (ew E 10) + 40 <= a < bv_unsigned (ew E 10) + 48).
Proof.
  intros E rs a Hw Hin. destruct (in_wrange_windows E rs a Hin) as (b & lo & hi & Ht & Hr). rewrite Hw in Ht.
  cbn [In] in Ht. destruct Ht as [Hq|[Hq|[]]]; injection Hq as <- <- <-; cbn [base_val] in Hr; lia.
Qed.

Lemma mw_winC : forall E rs a,
  windows rs = [(Some 2%nat, -48, 0); (Some 10%nat, 0, 4); (Some 10%nat, 32, 48); (Some 10%nat, 56, 64);
                (Some 10%nat, 232, 248); (Some 4%nat, -164, -160)] -> in_wrange E rs a ->
  (bv_unsigned (ew E 2) - 48 <= a < bv_unsigned (ew E 2)) \/
  (bv_unsigned (ew E 10) <= a < bv_unsigned (ew E 10) + 4) \/
  (bv_unsigned (ew E 10) + 32 <= a < bv_unsigned (ew E 10) + 48) \/
  (bv_unsigned (ew E 10) + 56 <= a < bv_unsigned (ew E 10) + 64) \/
  (bv_unsigned (ew E 10) + 232 <= a < bv_unsigned (ew E 10) + 248) \/
  (bv_unsigned (ew E 4) - 164 <= a < bv_unsigned (ew E 4) - 160).
Proof.
  intros E rs a Hw Hin. destruct (in_wrange_windows E rs a Hin) as (b & lo & hi & Ht & Hr). rewrite Hw in Ht.
  cbn [In] in Ht. destruct Ht as [Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[]]]]]]]; injection Hq as <- <- <-; cbn [base_val] in Hr; lia.
Qed.

Lemma mw_winD : forall E rs a, windows rs = [(Some 2%nat, -48, 0); (Some 10%nat, 232, 248)] -> in_wrange E rs a ->
  (bv_unsigned (ew E 2) - 48 <= a < bv_unsigned (ew E 2)) \/ (bv_unsigned (ew E 10) + 232 <= a < bv_unsigned (ew E 10) + 248).
Proof.
  intros E rs a Hw Hin. destruct (in_wrange_windows E rs a Hin) as (b & lo & hi & Ht & Hr). rewrite Hw in Ht.
  cbn [In] in Ht. destruct Ht as [Hq|[Hq|[]]]; injection Hq as <- <- <-; cbn [base_val] in Hr; lia.
Qed.

Lemma mw_nth_firstn : forall (l : list Z) n i, (i < n)%nat -> nth i (firstn n l) 0 = nth i l 0.
Proof.
  induction l as [|a l IH]; intros n i Hi; [destruct n, i; reflexivity|].
  destruct n as [|n]; [lia|]. destruct i as [|i]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.

Lemma mw_azbytes_app : forall (m : word -> option byte) a l1 l2,
  azbytes tfibsegs m a l1 -> azbytes tfibsegs m (a + Z.of_nat (length l1)) l2 -> azbytes tfibsegs m a (l1 ++ l2).
Proof.
  intros m a l1 l2 H1 H2 i Hi. rewrite length_app in Hi.
  destruct (Nat.lt_ge_cases i (length l1)) as [L|L].
  - rewrite app_nth1 by exact L. apply H1. exact L.
  - rewrite app_nth2 by exact L. specialize (H2 (i - length l1)%nat ltac:(lia)).
    replace (a + Z.of_nat i) with (a + Z.of_nat (length l1) + Z.of_nat (i - length l1)) by lia. exact H2.
Qed.

Lemma mw_azbytes_xfer : forall (H : word -> bool) (m m' : word -> option byte) a l,
  (forall i, (i < length l)%nat -> aview tfibsegs H m' (a + Z.of_nat i) = aview tfibsegs H m (a + Z.of_nat i)) ->
  azbytes tfibsegs (mrestrict H m) a l -> azbytes tfibsegs (mrestrict H m') a l.
Proof.
  intros H m m' a l Hk Hz i Hi. change (aview tfibsegs H m' (a + Z.of_nat i) = Some (nth i l 0)).
  rewrite Hk by exact Hi. exact (Hz i Hi).
Qed.

Lemma mw_val_mem_xfer_av : forall (H : word -> bool) (m m' : word -> option byte) a (n : nat) v,
  (forall i, 0 <= i < Z.of_nat n -> aview tfibsegs H m' (a + i) = aview tfibsegs H m (a + i)) ->
  val_mem tfibsegs (mrestrict H m) a n v -> val_mem tfibsegs (mrestrict H m') a n v.
Proof.
  intros H m m' a n v Hk Hv. apply (mw_val_mem_xfer tfibsegs (mrestrict H m)); [|exact Hv].
  intros i Hi. apply mbyte_of_aview. apply Hk. exact Hi.
Qed.

(* ==========================================================================
   6. The case k > 0
   ========================================================================== *)

(* a sub-range of a block whose shadow map marks it addressable (n a multiple of 8: every granule 0) *)
Lemma mw_block_ra : forall (rd : Z -> option Z) Bs p n a len,
  block_shadow rd Bs p n -> n mod 8 = 0 -> p <= a -> a + len <= p + n -> range_addressable rd Bs a len.
Proof.
  intros rd Bs p n a len (Hp & Hn & Hc) Hn8 H1 H2 x Hx. exists 0. split; [|left; reflexivity].
  assert (Hi : shadow_of_addr Bs x = shadow_of_addr Bs p + (x - p) / 8).
  { rewrite <- (shadow_of_addr_aligned_off Bs p (x - p) Hp). f_equal. lia. }
  pose proof (Z.div_mod n 8 ltac:(lia)) as Hd.
  assert (L : (x - p) / 8 < n / 8) by (apply Z.div_lt_upper_bound; lia).
  assert (L0 : 0 <= (x - p) / 8) by (apply Z.div_pos; lia).
  assert (L2 : n / 8 <= (n + 7) / 8) by (apply Z.div_le_mono; lia).
  rewrite Hi, Hc by lia. rewrite (proj2 (Z.ltb_lt _ _) L). reflexivity.
Qed.

(* the shadow hull of a sub-range lies in the hull of the range *)
Lemma mw_hull_sub : forall (rd : Z -> option Z) a n a' n',
  shadow_hull_vis rd a n -> a <= a' -> 0 < n' -> a' + n' <= a + n -> 0 <= a -> shadow_hull_vis rd a' n'.
Proof.
  intros rd a n a' n' H H1 H2 H3 H0 s Hs. apply H.
  assert (M : forall x y, 0 <= x <= y -> shadow_addr x / 8 * 8 <= shadow_addr y / 8 * 8).
  { intros x y Hxy. apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|].
    unfold shadow_addr. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
  pose proof (M a a' ltac:(lia)). pose proof (M (a' + n' - 1) (a + n - 1) ltac:(lia)). lia.
Qed.

(* linear arithmetic over the walk's constants (the FILE block, the windows, the high memory) *)
Ltac mwlia := unfold AMF_BUF, AMF_BLOCK, AMF_BUFSIZ, AMF_ZEROED, AMF_COOKIE, AMW_STK, ESTACK, kHighMemEnd, kHighMemBeg,
  kLowMemEnd, kLowShadowBeg in *; cbn [amf_buf amf_size amf_mode link_amf] in *; lia.

Section K. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis TB : PcapSyms B.
Hypothesis AMEMCPY : aintrin_realizes tfibsegs B OCpy (pc_wrap_memcpy (as_code B)).
Hypothesis HK0 : amwrite_mf_k0_realizes tfibsegs B link_amf LA_MWRITE.
Let LAWS : AR_laws tfibsegs B := YG0q.AR_laws_ok tfibsegs B.

Variables (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (f k fl om wend wpos wbase pos len x : Z) (pb ds : list Z).
Hypothesis HPRE : ecall_pre tfibsegs B ly S W regs mem md.
Hypothesis Hstk : ly_stk_lo ly + 4192 <= spZ regs.   (* AMW_STK = 96 + ESTACK = 4192 *)
Hypothesis Hpres : forall a, spZ regs - AMW_STK <= a < spZ regs -> apresent (w_H W) mem a.
Hypothesis H10 : getr regs 10 = w64 f.
Hypothesis H11 : getr regs 11 = w64 x.
Hypothesis H12 : getr regs 12 = w64 (Z.of_nat (length ds)).
Hypothesis Hblk : In (f, AMF_BLOCK) (ablocks B ly S).
Hypothesis Hamk : amf_k tfibsegs link_amf (mrestrict (w_H W) mem) f k.
Hypothesis Hkmax : k <= AMF_BUFSIZ.
Hypothesis Hdyn : amf_dyn tfibsegs link_amf (mrestrict (w_H W) mem) f fl om wend wpos wbase pos len.
Hypothesis Hpend : amf_pend tfibsegs (mrestrict (w_H W) mem) f pb.
Hypothesis Hpbk : Z.of_nat (length pb) = k.
Hypothesis Hbuf : amf_buf_ok tfibsegs B link_amf AMW_STK ly S W regs mem.
Hypothesis Hds : azbytes tfibsegs (mrestrict (w_H W) mem) x ds.
Hypothesis Hx0 : 0 <= x.
Hypothesis Hxn : x + Z.of_nat (length ds) <= 2 ^ 63.
Hypothesis Hxam : amem_range x (Z.of_nat (length ds)).
Hypothesis Hxra : range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x (Z.of_nat (length ds)).
Hypothesis Hxhull : 0 < Z.of_nat (length ds) -> shadow_hull_vis (aview tfibsegs (w_H W) mem) x (Z.of_nat (length ds)).
Hypothesis Hxdisj : forall a, x <= a < x + Z.of_nat (length ds) ->
  ~ (amf_buf link_amf <= a < amf_buf link_amf + amf_size link_amf) /\ ~ (f <= a < f + AMF_ZEROED) /\
  ~ (as_errno B <= a < as_errno B + 4) /\ ~ (spZ regs - AMW_STK <= a < spZ regs).
Hypothesis Hkpos : 0 < k.

Definition E0 : env := Ereg regs [Z_to_bv 64 (f + 280 + k)].

(* the FILE part of the contract's post *)
Definition PF (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  let n := Z.of_nat (length ds) in
  let n1 := amf_n1 link_amf k pos in
  let pos1 := amw_pos1 link_amf k pos in
  let n2 := amw_n2 link_amf k pos n in
  amf_k tfibsegs link_amf (mrestrict (w_H W) mem') f 0 /\ amf_pend tfibsegs (mrestrict (w_H W) mem') f pb /\
  (n1 < k ->
     getr regs' 10 = w64 0 /\
     amf_dyn tfibsegs link_amf (mrestrict (w_H W) mem') f (Z.lor fl AF_ERR) om 0 0 0 pos1 (Z.max len pos1) /\
     azbytes tfibsegs (mrestrict (w_H W) mem') (amf_buf link_amf + pos) (firstn (Z.to_nat n1) pb)) /\
  (n1 = k ->
     getr regs' 10 = w64 n2 /\
     (exists fl' wend' wpos' wbase',
        amf_dyn tfibsegs link_amf (mrestrict (w_H W) mem') f fl' om wend' wpos' wbase' (pos1 + n2) (Z.max len (pos1 + n2)) /\
        (n2 < n -> fl' = Z.lor fl AF_ERR /\ wend' = 0 /\ wpos' = 0 /\ wbase' = 0) /\
        (n2 = n -> fl' = fl /\ wend' = wend /\ wpos' = wbase /\ wbase' = wbase)) /\
     azbytes tfibsegs (mrestrict (w_H W) mem') (amf_buf link_amf + pos) (pb ++ firstn (Z.to_nat n2) ds)).

Definition FP : world tfibsegs -> config -> Prop := fun W' c' => W' = W /\ exists regs' mem' md',
  c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
  AR tfibsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
  PF regs' mem' /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ mw_chg B (spZ regs) f a -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
  (forall a, spZ regs - AMW_STK <= a < spZ regs -> apresent (w_H W) mem' a).

Local Notation INVk := (INV B ly S W (spZ regs) f mem md).

(* ---- the entry's facts ---- *)

Lemma kf_pre : AR tfibsegs B ly S W mem md /\ YK0s.ret_ok (getr regs 1) /\ spZ regs mod 16 = 0 /\
  ly_stk_lo ly + ESTACK <= spZ regs /\ spZ regs <= ly_stk_hi ly /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B).
Proof. destruct HPRE as (A & R & M & L & T & _ & G & P). exact (conj A (conj R (conj M (conj L (conj T (conj G P)))))). Qed.

Lemma kf_lay : kHighMemBeg <= ly_stk_lo ly /\ ASAN_CEIL <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd /\
  kHighMemBeg + AMW_STK <= spZ regs <= kHighMemEnd.
Proof.
  pose proof kf_pre as (HAR & _ & _ & _ & Htop & _).
  pose proof (am_layout B ly S _ (proj1 HAR)) as HL.
  pose proof (lo_top ly HL) as (_ & _ & _ & L4 & _ & _ & L7). pose proof (lo_stk_ceil ly HL) as Hc.
  split; [exact L7|]. split; [exact Hc|]. split; [exact L4|]. unfold AMW_STK, ESTACK. lia.
Qed.

Lemma kf_blk : f mod 16 = 0 /\ 4096 <= f /\ f + AMF_BLOCK <= ly_stk_lo ly /\
  (f + AMF_BLOCK <= kLowShadowBeg \/ kHighMemBeg <= f) /\
  (forall a, f <= a < f + AMF_BLOCK -> apresent (w_H W) mem a /\ ~ aowned B ly S a /\ ~ YG0d.in_img tfibsegs a) /\
  block_shadow (aview tfibsegs (w_H W) mem) SHADOW_OFF f AMF_BLOCK /\
  shadow_hull_vis (aview tfibsegs (w_H W) mem) f AMF_BLOCK.
Proof.
  pose proof kf_pre as (HAR & _). pose proof kf_lay as (L1 & L2 & _).
  destruct (amf_block_facts tfibsegs B LAWS ly S W mem md f HAR Hblk) as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
  split; [exact A1|]. split; [exact A2|]. split.
  { destruct A4 as [_ [H|[_ H]]]; unfold kLowShadowBeg, kHighMemBeg in *; lia. }
  split; [destruct A4 as [_ [H|[H _]]]; [left | right]; lia|].
  split; [exact A5|]. split; [exact A6 | exact A7].
Qed.

Lemma kf_fimg : f + AMF_BLOCK <= 0x10000 \/ 0x654000 <= f.
Proof.
  pose proof kf_blk as (_ & _ & _ & _ & Bp & _).
  destruct (Z_le_gt_dec (f + AMF_BLOCK) 0x10000) as [L|L]; [left; exact L|].
  destruct (Z_le_gt_dec 0x654000 f) as [L2|L2]; [right; exact L2|]. exfalso.
  apply (proj2 (proj2 (Bp (Z.max f 0x10000) ltac:(unfold AMF_BLOCK in *; lia)))). apply mw_img_full. lia.
Qed.

Lemma kf_win : wend = f + 1304 /\ wpos = f + 280 + k /\ wbase = f + 280.
Proof.
  pose proof kf_blk as (_ & B4 & Bs & _). pose proof kf_lay as (_ & _ & _ & _).
  destruct Hamk as (_ & [(Hk' & _) | (_ & W32 & W40 & W56)]); [lia|].
  destruct Hdyn as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & D0 & D136 & D32 & D40 & D56 & D232 & D240).
  pose proof kf_lay as (L1 & L2 & L3 & L4). pose proof Hstk as Hst.
  unfold AMF_BUF, AMF_BUFSIZ, AMF_BLOCK, kHighMemEnd, AMW_STK, ESTACK in *.
  split; [|split].
  - assert (E : wend = f + 280 + 1024) by (eapply mw_val_mem_det; [exact D32 | exact W32 | cbn; lia | cbn; lia]). lia.
  - eapply mw_val_mem_det; [exact D40 | exact W40 | cbn; lia | cbn; lia].
  - eapply mw_val_mem_det; [exact D56 | exact W56 | cbn; lia | cbn; lia].
Qed.

Lemma kf_fl : fl = AF_NORD \/ fl = AF_NORD + AF_ERR.
Proof.
  destruct Hamk as ((_ & _ & _ & _ & Hfl & _) & _).
  destruct Hdyn as (R1 & _ & _ & _ & _ & _ & _ & D0 & _).
  unfold amemfile_flags in Hfl.
  destruct Hfl as [H|H]; [left | right]; (eapply mw_val_mem_det; [exact D0 | exact H | cbn; lia | cbn; unfold AF_NORD, AF_ERR; lia]).
Qed.

Lemma kf_lor : Z.lor fl AF_ERR = AF_NORD + AF_ERR.
Proof. destruct kf_fl as [-> | ->]; reflexivity. Qed.

Lemma kf_cookie : 0 <= pos <= len /\ len <= 4096 /\ 0 <= om < 2 ^ 32.
Proof. destruct Hdyn as (_ & R2 & _ & _ & _ & R6 & R7 & _). cbn [amf_size link_amf] in R7. lia. Qed.

Lemma kf_errno : as_errno B = 0x631b6c /\ as_tp B = 0x631c10.
Proof. rewrite (ts_errno B TB), (ts_tp B TB). split; reflexivity. Qed.

Lemma k_E : forall E, env_agree 33 E0 E ->
  bv_unsigned (ew E 2) = spZ regs /\ bv_unsigned (ew E 10) = f /\ ew E 32 = Z_to_bv 64 (f + 280 + k) /\
  ew E 1 = getr regs 1 /\ ew E 3 = getr regs 3 /\ ew E 4 = getr regs 4 /\ ew E 11 = getr regs 11 /\ ew E 12 = getr regs 12 /\
  bv_unsigned (ew E 4) = 0x631c10.
Proof.
  intros E [HA _]. pose proof kf_blk as (_ & B4 & Bs & _). pose proof kf_lay as (_ & _ & _ & L4).
  pose proof kf_pre as (_ & _ & _ & _ & _ & _ & Htp). pose proof kf_errno as (_ & Etp).
  assert (G : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
  { intros n r Hn Hr. rewrite (HA n ltac:(lia)). unfold E0. exact (ew_Ereg_nat regs _ n r Hr). }
  split; [rewrite (G 2%nat 2%bv ltac:(lia) eq_refl); reflexivity|].
  split; [rewrite (G 10%nat 10%bv ltac:(lia) eq_refl), H10; unfold w64; apply unsigned_lit_small; pose proof Hstk;
          unfold AMF_BLOCK, kHighMemEnd, AMW_STK, ESTACK in *; lia|].
  split; [rewrite (HA 32%nat ltac:(lia)); unfold E0; exact (ew_Ereg_extra regs _ 0)|].
  split; [exact (G 1%nat 1%bv ltac:(lia) eq_refl)|]. split; [exact (G 3%nat 3%bv ltac:(lia) eq_refl)|].
  split; [exact (G 4%nat 4%bv ltac:(lia) eq_refl)|]. split; [exact (G 11%nat 11%bv ltac:(lia) eq_refl)|].
  split; [exact (G 12%nat 12%bv ltac:(lia) eq_refl)|].
  rewrite (G 4%nat 4%bv ltac:(lia) eq_refl), Htp, Etp. reflexivity.
Qed.

(* every byte mwrite may write is in the contract's written set, is not the runtime's and is not a shadow byte *)
Lemma kf_safe : forall a,
  (spZ regs - AMW_STK <= a < spZ regs) \/ (f <= a < f + AMF_ZEROED) \/ (as_errno B <= a < as_errno B + 4) \/
  (amf_buf link_amf <= a < amf_buf link_amf + amf_size link_amf) ->
  mw_chg B (spZ regs) f a /\ ~ aowned B ly S a /\ ~ in_band_rw a.
Proof.
  intros a Ha. pose proof kf_pre as (HAR & _ & _ & _ & Htop & _). pose proof kf_lay as (L1 & L2 & L3 & L4).
  pose proof kf_blk as (_ & B4 & Bs & Bap & Bp & _). pose proof kf_errno as (Ee & _).
  destruct Hbuf as (_ & _ & _ & Hbw & _).
  assert (CS : 0x7fff7000 = kLowShadowBeg) by reflexivity.
  unfold mw_chg. destruct Ha as [Ha|[Ha|[Ha|Ha]]].
  - split; [left; exact Ha|]. split; [apply (al_stack _ _ LAWS ly S W mem md a HAR); unfold AMW_STK, ESTACK in Ha; lia|].
    unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, AMW_STK, ESTACK in *. lia.
  - split; [right; left; exact Ha|]. split; [apply (Bp a); unfold AMF_ZEROED, AMF_BLOCK in *; lia|].
    unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, AMF_ZEROED, AMF_BLOCK in *. lia.
  - split; [right; right; right; exact Ha|]. split.
    + intros O. rewrite Ee in Ha.
      apply (proj1 (al_owned_image _ _ LAWS ly S W mem md a HAR (mw_img_full a ltac:(lia)))) in O.
      rewrite (ts_owned B TB) in O. apply Exists_exists in O as (r & Hr & Hz).
      pose proof (proj1 (forallb_forall _ _) mw_errno_owned_chk r Hr) as Hc. cbv beta in Hc.
      unfold in_zr in Hz. apply orb_prop in Hc as [Hc|Hc]; apply Z.leb_le in Hc; lia.
    + rewrite Ee in Ha. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *. lia.
  - split; [right; right; left; exact Ha|]. split; [exact (proj1 (proj2 (Hbw a Ha)))|].
    cbn [amf_buf amf_size link_amf] in Ha. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *. lia.
Qed.

(* the shadow band and the gap below the high memory hold no byte mwrite writes *)
Lemma kf_shadow : forall m md', INVk m md' -> forall s, kLowShadowBeg <= s < kHighMemBeg ->
  aview tfibsegs (w_H W) m s = aview tfibsegs (w_H W) mem s.
Proof.
  intros m md' (_ & _ & Hfr & _) s Hs. pose proof kf_lay as (L1 & L2 & L3 & L4). pose proof kf_blk as (_ & B4 & Bs & Bap & _).
  pose proof kf_errno as (Ee & _). apply Hfr; [unfold kLowShadowBeg, kHighMemBeg in *; lia|].
  unfold mw_chg. rewrite Ee. cbn [amf_buf amf_size link_amf].
  unfold kLowShadowBeg, kHighMemBeg, AMW_STK, ESTACK, AMF_ZEROED, AMF_BLOCK in *. lia.
Qed.

Lemma kf_ra_xfer : forall m md' a n, INVk m md' -> 0 <= a -> a + n <= kHighMemEnd ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF a n -> range_addressable (aview tfibsegs (w_H W) m) SHADOW_OFF a n.
Proof.
  intros m md' a n HI Ha0 Han Hra z Hz. destruct (Hra z Hz) as (s & Hs & Hok). exists s. split; [|exact Hok].
  rewrite (kf_shadow m md' HI); [exact Hs|]. unfold shadow_of_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, kHighMemEnd in *.
  pose proof (Z.div_pos z 8 ltac:(lia) ltac:(lia)). assert (z / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

Lemma kf_hull_xfer : forall m md' a n, INVk m md' -> 0 <= a -> 0 < n -> a + n <= kHighMemEnd ->
  shadow_hull_vis (aview tfibsegs (w_H W) mem) a n -> shadow_hull_vis (aview tfibsegs (w_H W) m) a n.
Proof.
  intros m md' a n HI Ha0 Hn Han Hh s Hs. rewrite (kf_shadow m md' HI); [exact (Hh s Hs)|].
  unfold shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, kHighMemEnd in *.
  pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)).
  assert ((a + n - 1) / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
  pose proof (Z.mod_pos_bound (2147450880 + a / 8) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (2147450880 + (a + n - 1) / 8) 8 ltac:(lia)).
  pose proof (Z.div_mod (2147450880 + a / 8) 8 ltac:(lia)).
  pose proof (Z.div_mod (2147450880 + (a + n - 1) / 8) 8 ltac:(lia)). lia.
Qed.

(* the copy's source: unchanged since the entry *)
Lemma kf_src : forall m md', INVk m md' -> forall i, (i < length ds)%nat ->
  aview tfibsegs (w_H W) m (x + Z.of_nat i) = Some (nth i ds 0).
Proof.
  intros m md' (_ & _ & Hfr & _) i Hi. rewrite Hfr; [exact (Hds i Hi) | lia |].
  destruct (Hxdisj (x + Z.of_nat i) ltac:(lia)) as (N1 & N2 & N3 & N4). unfold mw_chg. tauto.
Qed.

(* the pending bytes: unchanged since the entry *)
Lemma kf_pend : forall m md', INVk m md' -> amf_pend tfibsegs (mrestrict (w_H W) m) f pb.
Proof.
  intros m md' (_ & _ & Hfr & _). pose proof kf_blk as (_ & B4 & Bs & _). pose proof kf_lay as (L1 & L2 & L3 & L4).
  pose proof kf_fimg as Fi. pose proof kf_errno as (Ee & _).
  apply (mw_azbytes_xfer (w_H W) mem m); [|exact Hpend].
  intros i Hi. apply Hfr; [mwlia|].
  unfold mw_chg. rewrite Ee. mwlia.
Qed.

(* ---- one phase, with the windows of the shape after the copy (stack frame, the cookie's pos / len) ---- *)
Lemma kD_step : forall E ss ss' st ms md' Q,
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> windows (ss_mem ss) = [(Some 2%nat, -48, 0); (Some 10%nat, 232, 248)] ->
  env_agree 33 E0 E -> sym_runN tfibsegs tbl_mw FUEL ss = (ss', st) -> st <> RS_ecall ->
  INVk (ms_mem ms) md' ->
  (forall ms1 mat1, st_ok tfibsegs E ss' (restrict (w_H W) ms1) ->
     INVk (ms_mem ms1) (with_vm_backing (m_vm_lazy md') mat1 md') ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 48 <= a < spZ regs) -> ~ (f + 232 <= a < f + 248) ->
        aview tfibsegs (w_H W) (ms_mem ms1) a = aview tfibsegs (w_H W) (ms_mem ms) a) ->
     SRr tfibsegs W (mkCfg ms1 (with_vm_backing (m_vm_lazy md') mat1 md')) Q) ->
  SRr tfibsegs W (mkCfg ms md') Q.
Proof.
  intros E ss ss' st ms md' Q HS Hw HAE Hrun Hne HI Hk.
  destruct (k_E E HAE) as (E2 & E10 & _).
  eapply SRr_bind; [exact (mw_phase W E ss ss' st ms md' HS Hrun Hne)|].
  intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1 & HG1).
  assert (WIN : forall z, in_wrange E (ss_mem ss) z -> (spZ regs - 48 <= z < spZ regs) \/ (f + 232 <= z < f + 248)).
  { intros z Hz. destruct (mw_winD E (ss_mem ss) z Hw Hz) as [Hz'|Hz']; rewrite ?E2, ?E10 in Hz'; [left|right]; lia. }
  apply Hk; [exact HS1 | |].
  - apply (INV_run B LAWS ly S W (spZ regs) f mem md (fun z => (spZ regs - 48 <= z < spZ regs) \/ (f + 232 <= z < f + 248))
      (ms_mem ms) md' (ms_mem ms1) mat1 HI).
    + intros y Hy. apply HF1. intros Hin. apply Hy. exact (WIN _ Hin).
    + intros y Hy. apply HFr1. intros Hin. apply Hy. exact (WIN _ Hin).
    + exact HG1.
    + intros z [Hz|Hz]; apply kf_safe; [left; unfold AMW_STK, ESTACK; lia | right; left; unfold AMF_ZEROED; lia].
  - intros z Hz H1 H2. apply aview_eq_of. apply HFr1. rewrite unsigned_lit_small by lia. intros Hin. destruct (WIN _ Hin); lia.
Qed.

(* ---- one phase, with the windows of the shape after the inner call ---- *)
Lemma kC_step : forall E ss ss' st ms md' Q,
  st_ok tfibsegs E ss (restrict (w_H W) ms) ->
  windows (ss_mem ss) = [(Some 2%nat, -48, 0); (Some 10%nat, 0, 4); (Some 10%nat, 32, 48); (Some 10%nat, 56, 64);
                         (Some 10%nat, 232, 248); (Some 4%nat, -164, -160)] ->
  env_agree 33 E0 E -> sym_runN tfibsegs tbl_mw FUEL ss = (ss', st) -> st <> RS_ecall ->
  INVk (ms_mem ms) md' ->
  (forall ms1 mat1, st_ok tfibsegs E ss' (restrict (w_H W) ms1) ->
     INVk (ms_mem ms1) (with_vm_backing (m_vm_lazy md') mat1 md') ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 48 <= a < spZ regs) -> ~ (f <= a < f + 4) -> ~ (f + 32 <= a < f + 48) ->
        ~ (f + 56 <= a < f + 64) -> ~ (f + 232 <= a < f + 248) -> ~ (as_errno B <= a < as_errno B + 4) ->
        aview tfibsegs (w_H W) (ms_mem ms1) a = aview tfibsegs (w_H W) (ms_mem ms) a) ->
     SRr tfibsegs W (mkCfg ms1 (with_vm_backing (m_vm_lazy md') mat1 md')) Q) ->
  SRr tfibsegs W (mkCfg ms md') Q.
Proof.
  intros E ss ss' st ms md' Q HS Hw HAE Hrun Hne HI Hk.
  destruct (k_E E HAE) as (E2 & E10 & _ & _ & _ & _ & _ & _ & E4).
  pose proof kf_errno as (Ee & _).
  eapply SRr_bind; [exact (mw_phase W E ss ss' st ms md' HS Hrun Hne)|].
  intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1 & HG1).
  set (OKw := fun z => (spZ regs - 48 <= z < spZ regs) \/ (f <= z < f + 4) \/ (f + 32 <= z < f + 48) \/
                       (f + 56 <= z < f + 64) \/ (f + 232 <= z < f + 248) \/ (as_errno B <= z < as_errno B + 4)).
  assert (WIN : forall z, in_wrange E (ss_mem ss) z -> OKw z).
  { intros z Hz. unfold OKw. rewrite Ee. destruct (mw_winC E (ss_mem ss) z Hw Hz) as [H|[H|[H|[H|[H|H]]]]];
      rewrite ?E2, ?E10, ?E4 in H; lia. }
  apply Hk; [exact HS1 | |].
  - apply (INV_run B LAWS ly S W (spZ regs) f mem md OKw (ms_mem ms) md' (ms_mem ms1) mat1 HI).
    + intros y Hy. apply HF1. intros Hin. apply Hy. exact (WIN _ Hin).
    + intros y Hy. apply HFr1. intros Hin. apply Hy. exact (WIN _ Hin).
    + exact HG1.
    + intros z Hz. apply kf_safe. unfold OKw in Hz. unfold AMW_STK, ESTACK, AMF_ZEROED. lia.
  - intros z Hz H1 H2 H3 H4 H5 H6. apply aview_eq_of. apply HFr1. rewrite unsigned_lit_small by lia.
    intros Hin. pose proof (WIN _ Hin) as Hq. unfold OKw in Hq. lia.
Qed.

(* ---- the post at the three returns after the copy (the arm n1 = k) ---- *)
Lemma kD_post : forall (regs' : bvmap 5 word) (m m' : word -> option byte) md'' n2 flF wendF wposF wbaseF lenF,
  amf_n1 link_amf k pos = k -> n2 = Z.min (Z.of_nat (length ds)) (4096 - (pos + k)) ->
  (n2 < Z.of_nat (length ds) -> flF = Z.lor fl AF_ERR /\ wendF = 0 /\ wposF = 0 /\ wbaseF = 0) ->
  (n2 = Z.of_nat (length ds) -> flF = fl /\ wendF = f + 1304 /\ wposF = f + 280 /\ wbaseF = f + 280) ->
  lenF = Z.max len (pos + k + n2) ->
  getr regs' 10 = Z_to_bv 64 n2 ->
  INVk m' md'' ->
  amemfile_at tfibsegs link_amf (mrestrict (w_H W) m) f ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 48 <= a < spZ regs) -> ~ (f + 232 <= a < f + 248) ->
     a <> amf_buf link_amf + (pos + k + n2) -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) ->
  val_mem tfibsegs (mrestrict (w_H W) m) (f + 0) 4 flF -> val_mem tfibsegs (mrestrict (w_H W) m) (f + 32) 8 wendF ->
  val_mem tfibsegs (mrestrict (w_H W) m) (f + 40) 8 wposF -> val_mem tfibsegs (mrestrict (w_H W) m) (f + 56) 8 wbaseF ->
  val_mem tfibsegs (mrestrict (w_H W) m) (f + 136) 4 om ->
  azbytes tfibsegs (mrestrict (w_H W) m) (amf_buf link_amf + pos) (pb ++ firstn (Z.to_nat n2) ds) ->
  val_mem tfibsegs (mrestrict (w_H W) m') (f + 232) 8 (pos + k + n2) ->
  val_mem tfibsegs (mrestrict (w_H W) m') (f + 240) 8 lenF ->
  PF regs' m'.
Proof.
  intros regs' m m' md'' n2 flF wendF wposF wbaseF lenF Hn1 Hn2 Hlt Heq HlenF Ha0 HI Hat Hfr V0 V32 V40 V56 V136 Hbz V232 V240.
  pose proof kf_blk as (_ & B4 & Bs & _). pose proof kf_lay as (L1 & L2 & L3 & L4). pose proof kf_fimg as Fi.
  pose proof kf_cookie as (Hpl & Hls & Hom). pose proof kf_win as (Wend & Wpos & Wbase). pose proof kf_fl as Hfl.
  assert (Hpk : pos + k <= 4096) by (unfold amf_n1 in Hn1; cbn [amf_size link_amf] in Hn1; lia).
  assert (P1 : amw_pos1 link_amf k pos = pos + k) by (unfold amw_pos1; rewrite Hn1; reflexivity).
  assert (P2 : amw_n2 link_amf k pos (Z.of_nat (length ds)) = n2) by (unfold amw_n2; rewrite P1; cbn [amf_size link_amf]; lia).
  assert (TF : forall off (nb : nat) v, 0 <= off -> off + Z.of_nat nb <= 272 -> (off + Z.of_nat nb <= 232 \/ 248 <= off) ->
    val_mem tfibsegs (mrestrict (w_H W) m) (f + off) nb v -> val_mem tfibsegs (mrestrict (w_H W) m') (f + off) nb v).
  { intros off nb v H0 H1 H2 Hv. apply (mw_val_mem_xfer_av (w_H W) m m'); [|exact Hv].
    intros i Hi. apply Hfr; mwlia. }
  assert (Fl' : flF = AF_NORD \/ flF = AF_NORD + AF_ERR).
  { destruct (Z_lt_ge_dec n2 (Z.of_nat (length ds))) as [Hc|Hc].
    - right. rewrite (proj1 (Hlt Hc)). exact kf_lor.
    - assert (Hq : n2 = Z.of_nat (length ds)) by lia. rewrite (proj1 (Heq Hq)). exact Hfl. }
  assert (Wv : (wendF = 0 /\ wposF = 0 /\ wbaseF = 0) \/ (wendF = f + 1304 /\ wposF = f + 280 /\ wbaseF = f + 280)).
  { destruct (Z_lt_ge_dec n2 (Z.of_nat (length ds))) as [Hc|Hc].
    - left. destruct (Hlt Hc) as (_ & A2 & A3 & A4). auto.
    - right. assert (Hq : n2 = Z.of_nat (length ds)) by lia. destruct (Heq Hq) as (_ & A2 & A3 & A4). auto. }
  unfold PF. cbv zeta. rewrite P1, P2.
  split.
  { apply (amf_at_rebuild (mrestrict (w_H W) m) (mrestrict (w_H W) m') f flF wendF wposF wbaseF (pos + k + n2) lenF Hat).
    - intros a Ha Hd. apply mbyte_of_aview. apply Hfr; unfold dynf in *; mwlia.
    - exact Fl'.
    - apply TF; [lia | cbn; lia | cbn; lia | exact V0].
    - destruct Wv as [W'|W']; [left; exact W' | right; unfold AMF_BUF, AMF_BUFSIZ; lia].
    - apply TF; [lia | cbn; lia | cbn; lia | exact V32].
    - apply TF; [lia | cbn; lia | cbn; lia | exact V40].
    - apply TF; [lia | cbn; lia | cbn; lia | exact V56].
    - lia.
    - cbn [amf_size link_amf]. lia.
    - exact V232.
    - exact V240. }
  split; [exact (kf_pend m' md'' HI)|].
  split; [intros Hc; lia|].
  intros _. split; [exact Ha0|]. split.
  - exists flF, wendF, wposF, wbaseF. split; [|split].
    + unfold amf_dyn. subst lenF.
      split; [destruct Fl' as [-> | ->]; unfold AF_NORD, AF_ERR; lia|].
      split; [exact Hom|].
      split; [destruct Wv as [(-> & -> & ->)|(-> & -> & ->)]; mwlia|].
      split; [destruct Wv as [(-> & -> & ->)|(-> & -> & ->)]; mwlia|].
      split; [destruct Wv as [(-> & -> & ->)|(-> & -> & ->)]; mwlia|].
      split; [lia|]. split; [cbn [amf_size link_amf]; lia|].
      split; [apply TF; [lia | cbn; lia | cbn; lia | exact V0]|].
      split; [apply TF; [lia | cbn; lia | cbn; lia | exact V136]|].
      split; [apply TF; [lia | cbn; lia | cbn; lia | exact V32]|].
      split; [apply TF; [lia | cbn; lia | cbn; lia | exact V40]|].
      split; [apply TF; [lia | cbn; lia | cbn; lia | exact V56]|].
      split; [exact V232 | exact V240].
    + intros Hc. destruct (Hlt Hc) as (A1 & A2 & A3 & A4). auto.
    + intros Hc. destruct (Heq Hc) as (A1 & A2 & A3 & A4). rewrite Wend, Wbase. auto.
  - apply (mw_azbytes_xfer (w_H W) m m'); [|exact Hbz].
    intros i Hi. rewrite length_app, firstn_length_le in Hi by lia.
    apply Hfr; mwlia.
Qed.

(* ---- after the copy: +0xc4 to the return ---- *)
Lemma kD : forall E ms md' n2 flF wendF wposF wbaseF,
  st_ok tfibsegs E ssD (restrict (w_H W) ms) ->
  env_agree 33 E0 E -> ew E 33 = Z_to_bv 64 (pos + k) -> ew E 34 = Z_to_bv 64 (Z.max len (pos + k)) ->
  ew E 71 = Z_to_bv 64 n2 ->
  amf_n1 link_amf k pos = k -> n2 = Z.min (Z.of_nat (length ds)) (4096 - (pos + k)) ->
  (n2 < Z.of_nat (length ds) -> flF = Z.lor fl AF_ERR /\ wendF = 0 /\ wposF = 0 /\ wbaseF = 0) ->
  (n2 = Z.of_nat (length ds) -> flF = fl /\ wendF = f + 1304 /\ wposF = f + 280 /\ wbaseF = f + 280) ->
  INVk (ms_mem ms) md' ->
  amemfile_at tfibsegs link_amf (mrestrict (w_H W) (ms_mem ms)) f ->
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (f + 0) 4 flF ->
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (f + 32) 8 wendF ->
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (f + 40) 8 wposF ->
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (f + 56) 8 wbaseF ->
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (f + 136) 4 om ->
  azbytes tfibsegs (mrestrict (w_H W) (ms_mem ms)) (amf_buf link_amf + pos) (pb ++ firstn (Z.to_nat n2) ds) ->
  SRr tfibsegs W (mkCfg ms md') FP.
Proof.
  intros E ms md' n2 flF wendF wposF wbaseF HS HAE E33 E34 E71 Hn1 Hn2 Hlt Heq HI Hat V0 V32 V40 V56 V136 Hbz.
  pose proof kf_blk as (_ & B4 & Bs & _). pose proof kf_lay as (L1 & L2 & L3 & L4). pose proof kf_fimg as Fi.
  pose proof kf_cookie as (Hpl & Hls & Hom). pose proof kf_pre as (_ & Hra & _).
  destruct (k_E E HAE) as (E2 & E10 & _).
  assert (Hpk : pos + k <= 4096) by (unfold amf_n1 in Hn1; cbn [amf_size link_amf] in Hn1; lia).
  assert (Hn2r : 0 <= n2 <= Z.of_nat (length ds) /\ n2 <= 4096 - (pos + k)) by lia.
  assert (HAE32 : env_agree 32 (Ereg regs [Z_to_bv 64 (f + 280 + k)]) E) by exact (env_agree_le 33 32 _ _ ltac:(lia) HAE).
  assert (UL : U E (SOff 34 0) = Z.max len (pos + k)) by (apply (U_atom E 34); [exact E34 | lia]).
  assert (UN : U E SNP = pos + k + n2) by (unfold SNP; rewrite (vl_np E (pos + k) n2 0 E33 E71) by lia; lia).
  assert (DN : sv_denot E SNP = Z_to_bv 64 (pos + k + n2)) by (rewrite denot_lit_U, UN; reflexivity).
  assert (DL : sv_denot E (SOff 34 0) = Z_to_bv 64 (Z.max len (pos + k)))
    by (cbn [sv_denot]; rewrite E34, unsigned_lit_small, Z.add_0_r by lia; reflexivity).
  assert (A10 : forall ss ms2, st_ok tfibsegs E ss (restrict (w_H W) ms2) -> sr_get (ss_regs ss) 10 = SOff 71 0 ->
     getr (ms_regs ms2) 10 = Z_to_bv 64 n2)
    by (intros ss ms2 HS2 Hr; rewrite (mw_reg_atom E ss ms2 (w_H W) 10 71 HS2 Hr); exact E71).
  apply (kD_step E ssD ssD_st1 _ ms md' FP HS ltac:(vm_compute; reflexivity) HAE runD1 ltac:(discriminate) HI).
  intros ms1 mat1 HS1 HI1 HV1.
  destruct (Z_le_gt_dec (pos + k + n2) (Z.max len (pos + k))) as [Hge | Hlt1].
  - (* +0xd4 bgeu taken: len stays *)
    pose proof (st_ok_add_cond tfibsegs E ssD_st1 _ BC_GEU (SOff 34 0) SNP HS1
      ltac:(rewrite branch_geu_U, UL, UN; apply negb_true_iff, Z.ltb_ge; lia)) as HS2.
    change (YP06.add_cond ssD_st1 (mkAC BC_GEU (SOff 34 0) SNP)) with ssD_ge in HS2.
    apply (kD_step E ssD_ge ssD_ret1 _ ms1 _ FP HS2 ltac:(vm_compute; reflexivity) HAE runD_ge ltac:(discriminate) HI1).
    intros ms2 mat2 HS3 HI2 HV2.
    pose proof (mw_ret_word ssD_ret1 (or_intror (or_introl eq_refl))) as (Rv & Rp & Rr & Rc).
    apply (mw_finish B LAWS ly S W (spZ regs) f mem md regs _ E ssD_ret1 ms2 _ PF HS3 Rv Rp Rr Rc HAE32 Hra HI2).
    pose proof (mw_cval E ssD_ret1 ms2 (w_H W) 1 _ 0 232 8 SNP (pos + k + n2) HS3 eq_refl eq_refl DN
      ltac:(cbn; lia) ltac:(cbn; lia)) as VP.
    pose proof (mw_cval E ssD_ret1 ms2 (w_H W) 1 _ 1 240 8 (SOff 34 0) (Z.max len (pos + k)) HS3 eq_refl eq_refl DL
      ltac:(cbn; lia) ltac:(cbn; lia)) as VL.
    cbn [base_val YP09.r_base] in VP, VL. rewrite E10 in VP, VL.
    apply (kD_post (ms_regs ms2) (ms_mem ms) (ms_mem ms2) _ n2 flF wendF wposF wbaseF (Z.max len (pos + k))
      Hn1 Hn2 Hlt Heq ltac:(lia) (A10 _ _ HS3 eq_refl) HI2 Hat); try assumption.
    intros a Ha H1 H2 H3. rewrite HV2 by assumption. apply HV1; assumption.
  - (* +0xd4 not taken: len = pos *)
    pose proof (st_ok_add_cond_neg tfibsegs E ssD_st1 _ BC_GEU (SOff 34 0) SNP HS1
      ltac:(rewrite branch_geu_U, UL, UN; apply negb_false_iff, Z.ltb_lt; lia)) as HS2.
    rewrite ssD_lt_eq in HS2.
    apply (kD_step E ssD_lt ssD_st2 _ ms1 _ FP HS2 ltac:(vm_compute; reflexivity) HAE runD2 ltac:(discriminate) HI1).
    intros ms2 mat2 HS3 HI2 HV2.
    assert (U4 : U E (SLit 4096) = 4096) by (apply U_lit; lia).
    destruct (Z_le_gt_dec 4096 (pos + k + n2)) as [Hge2 | Hlt2].
    + (* +0xe0 bgeu taken: pos = size, no NUL *)
      pose proof (st_ok_add_cond tfibsegs E ssD_st2 _ BC_GEU SNP (SLit 4096) HS3
        ltac:(rewrite branch_geu_U, UN, U4; apply negb_true_iff, Z.ltb_ge; lia)) as HS4.
      change (YP06.add_cond ssD_st2 (mkAC BC_GEU SNP (SLit 4096))) with ssD_ge2 in HS4.
      apply (kD_step E ssD_ge2 ssD_ret2 _ ms2 _ FP HS4 ltac:(vm_compute; reflexivity) HAE runD_ge2 ltac:(discriminate) HI2).
      intros ms3 mat3 HS5 HI3 HV3.
      pose proof (mw_ret_word ssD_ret2 (or_intror (or_intror (or_introl eq_refl)))) as (Rv & Rp & Rr & Rc).
      apply (mw_finish B LAWS ly S W (spZ regs) f mem md regs _ E ssD_ret2 ms3 _ PF HS5 Rv Rp Rr Rc HAE32 Hra HI3).
      pose proof (mw_cval E ssD_ret2 ms3 (w_H W) 1 _ 1 232 8 SNP (pos + k + n2) HS5 eq_refl eq_refl DN
        ltac:(cbn; lia) ltac:(cbn; lia)) as VP.
      pose proof (mw_cval E ssD_ret2 ms3 (w_H W) 1 _ 0 240 8 SNP (pos + k + n2) HS5 eq_refl eq_refl DN
        ltac:(cbn; lia) ltac:(cbn; lia)) as VL.
      cbn [base_val YP09.r_base] in VP, VL. rewrite E10 in VP, VL.
      apply (kD_post (ms_regs ms3) (ms_mem ms) (ms_mem ms3) _ n2 flF wendF wposF wbaseF (pos + k + n2)
        Hn1 Hn2 Hlt Heq ltac:(lia) (A10 _ _ HS5 eq_refl) HI3 Hat); try assumption.
      intros a Ha H1 H2 H3. rewrite HV3 by assumption. rewrite HV2 by assumption. apply HV1; assumption.
    + (* +0xe0 not taken: +0xec buf[pos] = 0 *)
      pose proof (st_ok_add_cond_neg tfibsegs E ssD_st2 _ BC_GEU SNP (SLit 4096) HS3
        ltac:(rewrite branch_geu_U, UN, U4; apply negb_false_iff, Z.ltb_lt; lia)) as HS4.
      rewrite ssD_lt2_eq in HS4.
      apply (kD_step E ssD_lt2 ssD_sb _ ms2 _ FP HS4 ltac:(vm_compute; reflexivity) HAE runD_sb ltac:(discriminate) HI2).
      intros ms3 mat3 HS5 HI3 HV3.
      set (aN := amf_buf link_amf + (pos + k + n2)).
      assert (HaN : aN = 0x62fee0 + (pos + k + n2)) by reflexivity.
      destruct Hbuf as (_ & _ & _ & Hbw & _).
      apply (mw_sb_zero W E ssD_sb ms3 _ FP aN HS5 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
      * replace (sr_get (ss_regs ssD_sb) 10) with (SAlu ALU_ADD (SOff 33 6487776) (SOff 71 0)) by (vm_compute; reflexivity).
        rewrite denot_lit_U, (vl_np E (pos + k) n2 6487776 E33 E71) by lia. rewrite HaN. f_equal. lia.
      * rewrite HaN. lia.
      * destruct HI3 as (_ & _ & _ & Hpr3 & _).
        apply (mw_writable_grows (w_H W) mem (ms_mem ms3) aN (mw_apresent_restrict (w_H W) mem (ms_mem ms3) Hpr3)).
        apply (Hbw aN). rewrite HaN. cbn [amf_buf amf_size link_amf]. lia.
      * intros r Hr. vm_compute in Hr. destruct Hr as [<- | [<- | []]]; cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi];
          rewrite ?E2, ?E10, HaN; mwlia.
      * intros ms4 mat4 HS6 HR1 HR2 HG4.
        assert (HI4 : INVk (ms_mem ms4) (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy (with_vm_backing
                        (m_vm_lazy (with_vm_backing (m_vm_lazy md') mat1 md')) mat2 (with_vm_backing (m_vm_lazy md') mat1 md')))
                        mat3 (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md') mat1 md')) mat2
                        (with_vm_backing (m_vm_lazy md') mat1 md')))) mat4 (with_vm_backing (m_vm_lazy (with_vm_backing
                        (m_vm_lazy (with_vm_backing (m_vm_lazy md') mat1 md')) mat2 (with_vm_backing (m_vm_lazy md') mat1 md')))
                        mat3 (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md') mat1 md')) mat2
                        (with_vm_backing (m_vm_lazy md') mat1 md'))))).
        { apply (INV_run B LAWS ly S W (spZ regs) f mem md (fun z => z = aN) (ms_mem ms3) _ (ms_mem ms4) mat4 HI3).
          - intros y Hy. exact (HR1 y Hy).
          - intros y Hy. exact (HR2 y Hy).
          - exact HG4.
          - intros z ->. apply kf_safe. right; right; right. rewrite HaN. cbn [amf_buf amf_size link_amf]. lia. }
        change (mkSS (ss_pc ssD_sb + 4) (ss_regs ssD_sb) (ss_mem ssD_sb) None (ss_facts ssD_sb)) with ssD_af in HS6.
        apply (kD_step E ssD_af ssD_ret3 _ ms4 _ FP HS6 ltac:(vm_compute; reflexivity) HAE runD_af ltac:(discriminate) HI4).
        intros ms5 mat5 HS7 HI5 HV5.
        pose proof (mw_ret_word ssD_ret3 (or_intror (or_intror (or_intror eq_refl)))) as (Rv & Rp & Rr & Rc).
        apply (mw_finish B LAWS ly S W (spZ regs) f mem md regs _ E ssD_ret3 ms5 _ PF HS7 Rv Rp Rr Rc HAE32 Hra HI5).
        pose proof (mw_cval E ssD_ret3 ms5 (w_H W) 1 _ 1 232 8 SNP (pos + k + n2) HS7 eq_refl eq_refl DN
          ltac:(cbn; lia) ltac:(cbn; lia)) as VP.
        pose proof (mw_cval E ssD_ret3 ms5 (w_H W) 1 _ 0 240 8 SNP (pos + k + n2) HS7 eq_refl eq_refl DN
          ltac:(cbn; lia) ltac:(cbn; lia)) as VL.
        cbn [base_val YP09.r_base] in VP, VL. rewrite E10 in VP, VL.
        apply (kD_post (ms_regs ms5) (ms_mem ms) (ms_mem ms5) _ n2 flF wendF wposF wbaseF (pos + k + n2)
          Hn1 Hn2 Hlt Heq ltac:(lia) (A10 _ _ HS7 eq_refl) HI5 Hat); try assumption.
        intros a Ha H1 H2 H3. rewrite HV5 by assumption.
        rewrite (aview_eq_of (w_H W) (ms_mem ms3) (ms_mem ms4) a)
          by (apply HR2; rewrite unsigned_lit_small by lia; exact H3).
        rewrite HV3 by assumption. rewrite HV2 by assumption. apply HV1; assumption.
Qed.

(* ---- +0xc0 jal 0x52d74: the copy (the memory-checking runtime's memcpy wrapper), in both arms; then kD ---- *)
Lemma kM : forall E ss ms md' e2 n2 flF wendF wposF wbaseF,
  st_ok tfibsegs E ss (restrict (w_H W) ms) ->
  ss_pc ss = 0x52d74 -> ss_resv ss = None -> ss_atoms_lt 55 ss = true ->
  sr_get (ss_regs ss) 1 = SLit 0x96d84 -> sr_get (ss_regs ss) 2 = SOff 2 (-48) ->
  sr_get (ss_regs ss) 3 = SOff 3 0 -> sr_get (ss_regs ss) 4 = SOff 4 0 ->
  sr_get (ss_regs ss) 10 = SOff 33 6487776 -> sr_get (ss_regs ss) 11 = SOff 11 0 ->
  sr_get (ss_regs ss) 12 = e2 -> sr_get (ss_regs ss) 8 = e2 ->
  submem rsD (ss_mem ss) -> ss_atoms_lt 71 (ss_after_call ss rsD 55 0x96d84) = true ->
  mkSS 0x96d84 (sr_set (sr_sets (ss_regs ss) (junk_upd 55 CLOB)) 8 (SOff 71 0)) rsD None (mkFacts [] [] []) = ssD ->
  env_agree 33 E0 E -> ew E 33 = Z_to_bv 64 (pos + k) -> ew E 34 = Z_to_bv 64 (Z.max len (pos + k)) ->
  sv_denot E e2 = Z_to_bv 64 n2 ->
  amf_n1 link_amf k pos = k -> n2 = Z.min (Z.of_nat (length ds)) (4096 - (pos + k)) ->
  (n2 < Z.of_nat (length ds) -> flF = Z.lor fl AF_ERR /\ wendF = 0 /\ wposF = 0 /\ wbaseF = 0) ->
  (n2 = Z.of_nat (length ds) -> flF = fl /\ wendF = f + 1304 /\ wposF = f + 280 /\ wbaseF = f + 280) ->
  INVk (ms_mem ms) md' ->
  amemfile_at tfibsegs link_amf (mrestrict (w_H W) (ms_mem ms)) f ->
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (f + 0) 4 flF ->
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (f + 32) 8 wendF ->
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (f + 40) 8 wposF ->
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (f + 56) 8 wbaseF ->
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (f + 136) 4 om ->
  azbytes tfibsegs (mrestrict (w_H W) (ms_mem ms)) (amf_buf link_amf + pos) pb ->
  SRr tfibsegs W (mkCfg ms md') FP.
Proof.
  intros E ss ms md' e2 n2 flF wendF wposF wbaseF HS Hpc Hrv Hat R1 R2 R3 R4 R10 R11 R12 R8 Hsub HatD HD
    HAE E33 E34 Hn2v Hn1 Hn2 Hlt Heq HI Hfa V0 V32 V40 V56 V136 Hbz.
  pose proof kf_blk as (_ & B4 & Bs & _). pose proof kf_lay as (L1 & L2 & L3 & L4). pose proof kf_fimg as Fi.
  pose proof kf_cookie as (Hpl & Hls & Hom). pose proof kf_pre as (_ & _ & Hal & Hslo & Htop & Hgp & Htp).
  destruct (k_E E HAE) as (E2 & E10 & _ & _ & E3 & E4 & E11 & _).
  assert (Hpk : pos + k <= 4096) by (unfold amf_n1 in Hn1; cbn [amf_size link_amf] in Hn1; lia).
  assert (Hn2r : 0 <= n2 <= Z.of_nat (length ds) /\ n2 <= 4096 - (pos + k)) by lia.
  pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E ss ms HS Hrv) as Hshape. rewrite Hpc in Hshape.
  pose proof HI as (HAR & Hsbm & Hfr & Hpr & Hwp).
  destruct Hbuf as (Hb0 & Hb1 & Hb2 & Hbw & Hbam & Hbra & Hbhull).
  set (d := amf_buf link_amf + (pos + k)).
  assert (Hd : d = 0x62fee0 + (pos + k)) by reflexivity.
  assert (G1 : getr (ms_regs ms) 1 = Z_to_bv 64 0x96d84) by (rewrite (mw_reg_sv E ss ms (w_H W) 1 _ HS R1); reflexivity).
  assert (G2 : getr (ms_regs ms) 2 = Z_to_bv 64 (spZ regs - 48))
    by (rewrite (mw_reg_sv E ss ms (w_H W) 2 _ HS R2); cbn [sv_denot]; rewrite E2; f_equal; lia).
  assert (G3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite (mw_reg_atom E ss ms (w_H W) 3 3 HS R3), E3; exact Hgp).
  assert (G4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite (mw_reg_atom E ss ms (w_H W) 4 4 HS R4), E4; exact Htp).
  assert (G10 : getr (ms_regs ms) 10 = w64 d).
  { rewrite (mw_reg_sv E ss ms (w_H W) 10 _ HS R10). cbn [sv_denot]. rewrite E33, unsigned_lit_small by lia.
    unfold w64. rewrite Hd. f_equal. lia. }
  assert (G11 : getr (ms_regs ms) 11 = w64 x) by (rewrite (mw_reg_atom E ss ms (w_H W) 11 11 HS R11), E11; exact H11).
  assert (G12 : getr (ms_regs ms) 12 = w64 n2) by (rewrite (mw_reg_sv E ss ms (w_H W) 12 _ HS R12); exact Hn2v).
  assert (G8 : getr (ms_regs ms) 8 = Z_to_bv 64 n2) by (rewrite (mw_reg_sv E ss ms (w_H W) 8 _ HS R8); exact Hn2v).
  assert (Hsp1 : spZ (ms_regs ms) = spZ regs - 48)
    by (unfold spZ at 1; rewrite G2; apply unsigned_lit_small; mwlia).
  assert (BUFI : forall a, d <= a < d + n2 -> amf_buf link_amf <= a < amf_buf link_amf + amf_size link_amf)
    by (intros a Ha; rewrite Hd in Ha; cbn [amf_buf amf_size link_amf]; lia).
  set (regs1 := ms_regs ms) in *. set (m1 := ms_mem ms) in *.
  pose proof AMEMCPY as AM. unfold aintrin_realizes, cfg_at in AM. rewrite (ts_code B TB) in AM. cbn [pc_wrap_memcpy Tfib_code] in AM.
  rewrite Hshape. eapply SRr_bind.
  { apply (AM ly S W regs1 m1 md' d x n2).
    - split; [exact HAR|]. split; [rewrite G1; apply YK0s.ret_ok_even; rewrite unsigned_lit_small by lia; reflexivity|].
      rewrite Hsp1. split; [rewrite Zminus_mod, Hal; reflexivity|]. split; [mwlia|]. split; [lia|].
      split; [intros a Ha; apply Hwp; mwlia|]. split; [exact G3 | exact G4].
    - exact G10. - exact G11. - exact G12.
    - lia. - rewrite Hd. lia. - rewrite Hd. lia.
    - intros a Ha. rewrite Hsp1. pose proof (Hbw a (BUFI a Ha)) as (Hw & Ho & Hs).
      split; [exact (mw_writable_grows (w_H W) mem m1 a (mw_apresent_restrict _ _ _ Hpr) Hw)|].
      split; [exact Ho|]. mwlia.
    - left. rewrite Hd. mwlia.
    - apply (kf_ra_xfer m1 md' d n2 HI); [rewrite Hd; lia | rewrite Hd; mwlia |].
      intros z Hz. apply Hbra. pose proof (BUFI z Hz). lia.
    - intros Hn. apply (kf_hull_xfer m1 md' d n2 HI); [rewrite Hd; lia | exact Hn | rewrite Hd; unfold kHighMemEnd; lia |].
      intros s Hs. apply Hbhull. cbn [amf_buf amf_size link_amf] in *. unfold shadow_addr, SHADOW_OFF in *. rewrite Hd in Hs.
      assert (Q1 : (2147450880 + 6487776 / 8) / 8 * 8 <= (2147450880 + (6487776 + (pos + k)) / 8) / 8 * 8).
      { apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|]. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
      assert (Q2 : (2147450880 + (0x62fee0 + (pos + k) + n2 - 1) / 8) / 8 * 8 <= (2147450880 + (6487776 + 4096 - 1) / 8) / 8 * 8).
      { apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|]. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
      lia.
    - split; [lia|]. split; [lia|]. split.
      + intros a Ha. rewrite Hsp1. split.
        * pose proof (kf_src m1 md' HI (Z.to_nat (a - x)) ltac:(lia)) as Hv. rewrite Z2Nat.id in Hv by lia.
          replace (x + (a - x)) with a in Hv by lia. rewrite Hv. discriminate.
        * destruct (Hxdisj a ltac:(lia)) as (_ & _ & _ & N4). mwlia.
      + split.
        { destruct (Z_le_gt_dec (d + n2) x) as [Q|Q]; [left; exact Q|].
          destruct (Z_le_gt_dec (x + n2) d) as [Q'|Q']; [right; exact Q'|]. exfalso.
          destruct (Hxdisj (Z.max x d) ltac:(lia)) as (N1 & _). apply N1. apply BUFI. lia. }
        split; [destruct Hxam as [Q|[Q1 Q2]]; [left; lia | right; lia]|].
        split.
        * apply (kf_ra_xfer m1 md' x n2 HI); [lia | destruct Hxam as [Q|[Q1 Q2]]; mwlia |].
          intros z Hz. apply Hxra. lia.
        * intros Hn. apply (kf_hull_xfer m1 md' x n2 HI); [lia | exact Hn | destruct Hxam as [Q|[Q1 Q2]]; mwlia |].
          intros s Hs. apply (Hxhull ltac:(lia)). unfold shadow_addr, SHADOW_OFF in *.
          assert (Q2 : (2147450880 + (x + n2 - 1) / 8) / 8 * 8 <= (2147450880 + (x + Z.of_nat (length ds) - 1) / 8) / 8 * 8).
          { apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|]. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
          lia. }
  intros W2 c2 _ (-> & regs2 & m2 & md2 & -> & HAR2 & HP2 & Hsbm2 & Ha02 & Heff & Hfr2 & Hpr2).
  cbv beta iota in Heff.
  assert (Hra1 : raZ regs1 = 0x96d84) by (unfold raZ; rewrite G1; apply unsigned_lit_small; lia).
  unfold cfg_at. rewrite Hra1. change (w64 0x96d84) with (Z_to_bv 64 0x96d84).
  assert (FR : forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n2) -> ~ (spZ regs - 48 - ESTACK <= a < spZ regs - 48) ->
     aview tfibsegs (w_H W) m2 a = aview tfibsegs (w_H W) m1 a).
  { intros a Ha H1 H2. apply Hfr2; [exact Ha | exact H1 | rewrite Hsp1; exact H2]. }
  assert (PG : forall y, mrestrict (w_H W) m1 y <> None -> mrestrict (w_H W) m2 y <> None)
    by exact (mw_apresent_restrict _ _ _ Hpr2).
  assert (KEPT : Forall (region_kept tfibsegs E (mrestrict (w_H W) m1) (mrestrict (w_H W) m2)) rsD).
  { unfold rsD. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; apply (mw_region_kept E (w_H W) m1 m2); try exact PG;
      intros a Ha; cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi] in Ha; rewrite ?E2, ?E10 in Ha; apply FR;
      rewrite ?Hd; mwlia. }
  rewrite Hshape in HS. rewrite restrict_mkst_fx in HS.
  pose proof (st_ok_after_call tfibsegs 55 E ss _ regs2 (mrestrict (w_H W) m2) rsD 0x96d84 HS Hrv Hat
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Hsub R1 HP2 KEPT) as HSa.
  pose proof (st_ok_abstract_reg tfibsegs 71 _ _ _ 8 HSa HatD eq_refl) as HSb.
  pose proof (mw_st_ok_nofacts _ _ _ HSb) as HSc.
  cbn [ms_regs mkst] in HSc.
  set (E1 := havoc E 55 (map (getr regs2) CLOB)) in HSc.
  set (E2' := ewset E1 71 (getr regs2 8)) in HSc.
  assert (HSD : st_ok tfibsegs E2' ssD (restrict (w_H W) (mkst regs2 (Z_to_bv 64 0x96d84) m2 (seg_rom tfibsegs)))).
  { rewrite restrict_mkst_fx. rewrite <- HD. exact HSc. }
  assert (AG55 : env_agree 55 E E2').
  { apply (env_agree_trans 55 E E1 E2'); [exact (env_agree_havoc E 55 _)|].
    exact (env_agree_le 71 55 _ _ ltac:(lia) (env_agree_ewset E1 71 _)). }
  assert (HAE2 : env_agree 33 E0 E2') by (apply (env_agree_trans 33 E0 E E2'); [exact HAE | exact (env_agree_le 55 33 _ _ ltac:(lia) AG55)]).
  assert (P8 : getr regs2 8 = getr regs1 8) by exact (regs_preserved_frame regs1 regs2 HP2 8 eq_refl).
  assert (E71 : ew E2' 71 = Z_to_bv 64 n2).
  { unfold E2'. cbn [ew ewset]. try rewrite Nat.eqb_refl. rewrite P8. exact G8. }
  assert (HI2 : INVk m2 md2).
  { apply (INV_call B ly S W (spZ regs) f mem md (fun a => (d <= a < d + n2) \/ (spZ regs - 48 - ESTACK <= a < spZ regs - 48))
      m1 md' m2 md2 HI HAR2 Hsbm2).
    - intros a Ha Hn. apply FR; [exact Ha | intros Q; apply Hn; left; exact Q | intros Q; apply Hn; right; exact Q].
    - exact Hpr2.
    - intros a [Ha|Ha]; [apply (kf_safe a); right; right; right; exact (BUFI a Ha) | apply (kf_safe a); left; mwlia]. }
  assert (TF : forall off (nb : nat) v, 0 <= off -> off + Z.of_nat nb <= 272 ->
    val_mem tfibsegs (mrestrict (w_H W) m1) (f + off) nb v -> val_mem tfibsegs (mrestrict (w_H W) m2) (f + off) nb v).
  { intros off nb v H0 H1 Hv. apply (mw_val_mem_xfer_av (w_H W) m1 m2); [|exact Hv].
    intros i Hi. apply FR; rewrite ?Hd; mwlia. }
  apply (kD E2' _ md2 n2 flF wendF wposF wbaseF HSD HAE2).
  - destruct AG55 as [A _]. rewrite (A 33%nat ltac:(lia)). exact E33.
  - destruct AG55 as [A _]. rewrite (A 34%nat ltac:(lia)). exact E34.
  - exact E71.
  - exact Hn1. - exact Hn2. - exact Hlt. - exact Heq.
  - exact HI2.
  - apply (amemfile_at_frame tfibsegs link_amf (mrestrict (w_H W) m1)); [|exact Hfa].
    intros z Hz. apply mbyte_of_aview. apply FR; rewrite ?Hd; mwlia.
  - apply TF; [lia | cbn; lia | exact V0].
  - apply TF; [lia | cbn; lia | exact V32].
  - apply TF; [lia | cbn; lia | exact V40].
  - apply TF; [lia | cbn; lia | exact V56].
  - apply TF; [lia | cbn; lia | exact V136].
  - apply mw_azbytes_app.
    + apply (mw_azbytes_xfer (w_H W) m1 m2); [|exact Hbz].
      intros i Hi. apply FR; rewrite ?Hd; mwlia.
    + intros i Hi. rewrite firstn_length_le in Hi by lia.
      change (aview tfibsegs (w_H W) m2 (amf_buf link_amf + pos + Z.of_nat (length pb) + Z.of_nat i) =
              Some (nth i (firstn (Z.to_nat n2) ds) 0)).
      rewrite mw_nth_firstn by exact Hi.
      replace (amf_buf link_amf + pos + Z.of_nat (length pb) + Z.of_nat i) with (d + Z.of_nat i) by (rewrite Hd; cbn [amf_buf link_amf]; lia).
      rewrite Heff by lia. exact (kf_src m1 md' HI i ltac:(lia)).
Qed.

(* ---- after the inner call: +0x50 to the copy, or to the return when the inner call stopped at g_said's end ---- *)
Lemma kC : forall E ms md' fl1 wend1 wpos1 wbase1,
  st_ok tfibsegs E ssC (restrict (w_H W) ms) ->
  env_agree 33 E0 E ->
  ew E 33 = Z_to_bv 64 (pos + amf_n1 link_amf k pos) ->
  ew E 34 = Z_to_bv 64 (Z.max len (pos + amf_n1 link_amf k pos)) ->
  ew E 35 = Z_to_bv 64 fl1 -> ew E 36 = Z_to_bv 64 wend1 -> ew E 37 = Z_to_bv 64 wpos1 -> ew E 38 = Z_to_bv 64 wbase1 ->
  ew E 43 = Z_to_bv 64 (amf_n1 link_amf k pos) ->
  (amf_n1 link_amf k pos < k -> fl1 = Z.lor fl AF_ERR /\ wend1 = 0 /\ wpos1 = 0 /\ wbase1 = 0) ->
  (amf_n1 link_amf k pos = k -> fl1 = fl /\ wend1 = f + 1304 /\ wpos1 = f + 280 /\ wbase1 = f + 280) ->
  INVk (ms_mem ms) md' ->
  amemfile_at tfibsegs link_amf (mrestrict (w_H W) (ms_mem ms)) f ->
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (f + 136) 4 om ->
  azbytes tfibsegs (mrestrict (w_H W) (ms_mem ms)) (amf_buf link_amf + pos) (firstn (Z.to_nat (amf_n1 link_amf k pos)) pb) ->
  SRr tfibsegs W (mkCfg ms md') FP.
Proof.
  intros E ms md' fl1 wend1 wpos1 wbase1 HS HAE E33 E34 E35 E36 E37 E38 E43 Hlt Heq HI Hfa V136 Hbz.
  pose proof kf_blk as (_ & B4 & Bs & _). pose proof kf_lay as (L1 & L2 & L3 & L4). pose proof kf_fimg as Fi.
  pose proof kf_cookie as (Hpl & Hls & Hom). pose proof kf_pre as (_ & Hra & _). pose proof kf_fl as Hfl.
  destruct (k_E E HAE) as (E2 & E10 & E32 & _ & _ & _ & _ & E12 & E4).
  set (n1 := amf_n1 link_amf k pos) in *.
  assert (Hn1r : 0 <= n1 <= k /\ (n1 < k -> n1 = 4096 - pos)) by (unfold n1, amf_n1; cbn [amf_size link_amf]; lia).
  assert (HAE32 : env_agree 32 (Ereg regs [Z_to_bv 64 (f + 280 + k)]) E) by exact (env_agree_le 33 32 _ _ ltac:(lia) HAE).
  assert (U43 : U E (SOff 43 0) = n1) by (apply (U_atom E 43); [exact E43 | mwlia]).
  assert (UK : U E SK3 = k) by (exact (proj1 (vl_k E f k E10 E32 ltac:(lia) ltac:(lia) ltac:(mwlia)))).
  assert (DA : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v)
    by (intros n v Hn Hv; cbn [sv_denot]; rewrite Hn, unsigned_lit_small, Z.add_0_r by lia; reflexivity).
  (* the FILE bytes outside the words written after the inner call, through one phase of this shape *)
  set (CW := fun a => (spZ regs - 48 <= a < spZ regs) \/ (f <= a < f + 4) \/ (f + 32 <= a < f + 48) \/
                      (f + 56 <= a < f + 64) \/ (f + 232 <= a < f + 248) \/ (as_errno B <= a < as_errno B + 4)).
  assert (FW : forall a, f <= a < f + AMF_ZEROED -> ~ dynf (a - f) -> ~ CW a).
  { intros a Ha Hd Hc. pose proof kf_errno as (Ee & _). unfold CW in Hc. rewrite Ee in Hc. unfold dynf in *. mwlia. }
  apply (kC_step E ssC ssC_st1 _ ms md' FP HS ltac:(vm_compute; reflexivity) HAE runC1 ltac:(discriminate) HI).
  intros ms1 mat1 HS1 HI1 HV1.
  destruct (Z_lt_ge_dec n1 k) as [Hlt1 | Hge1].
  - (* +0x50 bgeu not taken: s0 = 0, return 0 *)
    destruct (Hlt Hlt1) as (F1 & F2 & F3 & F4).
    pose proof (st_ok_add_cond_neg tfibsegs E ssC_st1 _ BC_GEU (SOff 43 0) SK3 HS1
      ltac:(rewrite branch_geu_U, U43, UK; apply negb_false_iff, Z.ltb_lt; lia)) as HS2.
    rewrite ssC_lt_eq in HS2.
    apply (kC_step E ssC_lt ssC_ret _ ms1 _ FP HS2 ltac:(vm_compute; reflexivity) HAE runC_lt ltac:(discriminate) HI1).
    intros ms2 mat2 HS3 HI2 HV2.
    pose proof (mw_ret_word ssC_ret (or_introl eq_refl)) as (Rv & Rp & Rr & Rc).
    apply (mw_finish B LAWS ly S W (spZ regs) f mem md regs _ E ssC_ret ms2 _ PF HS3 Rv Rp Rr Rc HAE32 Hra HI2).
    assert (Hfl1 : fl1 = AF_NORD + AF_ERR) by (rewrite F1; exact kf_lor).
    pose proof (mw_cval E ssC_ret ms2 (w_H W) 1 _ 0 0 4 (SOff 35 0) fl1 HS3 eq_refl eq_refl (DA 35%nat fl1 E35 ltac:(rewrite Hfl1; unfold AF_NORD, AF_ERR; lia))
      ltac:(cbn; rewrite Hfl1; unfold AF_NORD, AF_ERR; lia) ltac:(cbn; lia)) as VF.
    pose proof (mw_cval E ssC_ret ms2 (w_H W) 2 _ 0 32 8 (SOff 36 0) wend1 HS3 eq_refl eq_refl (DA 36%nat wend1 E36 ltac:(lia))
      ltac:(cbn; lia) ltac:(cbn; lia)) as VW1.
    pose proof (mw_cval E ssC_ret ms2 (w_H W) 2 _ 1 40 8 (SOff 37 0) wpos1 HS3 eq_refl eq_refl (DA 37%nat wpos1 E37 ltac:(lia))
      ltac:(cbn; lia) ltac:(cbn; lia)) as VW2.
    pose proof (mw_cval E ssC_ret ms2 (w_H W) 3 _ 0 56 8 (SOff 38 0) wbase1 HS3 eq_refl eq_refl (DA 38%nat wbase1 E38 ltac:(lia))
      ltac:(cbn; lia) ltac:(cbn; lia)) as VW3.
    pose proof (mw_cval E ssC_ret ms2 (w_H W) 4 _ 0 232 8 (SOff 33 0) (pos + n1) HS3 eq_refl eq_refl (DA 33%nat _ E33 ltac:(lia))
      ltac:(cbn; lia) ltac:(cbn; lia)) as VP.
    pose proof (mw_cval E ssC_ret ms2 (w_H W) 4 _ 1 240 8 (SOff 34 0) (Z.max len (pos + n1)) HS3 eq_refl eq_refl (DA 34%nat _ E34 ltac:(lia))
      ltac:(cbn; lia) ltac:(cbn; lia)) as VL.
    cbn [base_val YP09.r_base] in VF, VW1, VW2, VW3, VP, VL. rewrite E10 in VF, VW1, VW2, VW3, VP, VL.
    rewrite F2 in VW1. rewrite F3 in VW2. rewrite F4 in VW3.
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ CW a -> aview tfibsegs (w_H W) (ms_mem ms2) a = aview tfibsegs (w_H W) (ms_mem ms) a).
    { intros a Ha Hc. unfold CW in Hc. rewrite HV2 by (try exact Ha; intros Q; apply Hc; tauto). apply HV1; try exact Ha; intros Q; apply Hc; tauto. }
    unfold PF. cbv zeta. change (amw_pos1 link_amf k pos) with (pos + n1).
    split.
    { apply (amf_at_rebuild (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms2)) f fl1 0 0 0 (pos + n1) (Z.max len (pos + n1)) Hfa).
      - intros a Ha Hd. apply mbyte_of_aview. apply KEEP; [mwlia | exact (FW a Ha Hd)].
      - right. exact Hfl1.
      - exact VF.
      - left. auto.
      - exact VW1. - exact VW2. - exact VW3.
      - lia.
      - cbn [amf_size link_amf]. lia.
      - exact VP. - exact VL. }
    split; [exact (kf_pend _ _ HI2)|].
    split.
    + intros _. split; [rewrite (mw_reg_sv E ssC_ret ms2 (w_H W) 10 (SLit 0) HS3 eq_refl); reflexivity|].
      split.
      * rewrite <- F1. unfold amf_dyn. split; [rewrite Hfl1; unfold AF_NORD, AF_ERR; lia|]. split; [exact Hom|].
        split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [cbn [amf_size link_amf]; lia|].
        split; [exact VF|]. split.
        { apply (mw_val_mem_xfer_av (w_H W) (ms_mem ms) (ms_mem ms2)); [|exact V136].
          intros i Hi. apply KEEP; [mwlia|]. apply (FW (f + 136 + i)); [unfold AMF_ZEROED; cbn in Hi; lia | unfold dynf; cbn in Hi; lia]. }
        split; [exact VW1|]. split; [exact VW2|]. split; [exact VW3|]. split; [exact VP | exact VL].
      * apply (mw_azbytes_xfer (w_H W) (ms_mem ms) (ms_mem ms2)); [|exact Hbz].
        intros i Hi. rewrite firstn_length_le in Hi by lia. apply KEEP; [mwlia|].
        pose proof kf_errno as (Ee & _). unfold CW. rewrite Ee. mwlia.
    + intros Hc. lia.
  - (* +0x50 bgeu taken: n1 = k, the rest of the k = 0 path from +0x5c *)
    assert (Hn1k : n1 = k) by lia. destruct (Heq Hn1k) as (F1 & F2 & F3 & F4).
    pose proof (st_ok_add_cond tfibsegs E ssC_st1 _ BC_GEU (SOff 43 0) SK3 HS1
      ltac:(rewrite branch_geu_U, U43, UK; apply negb_true_iff, Z.ltb_ge; lia)) as HS2.
    change (YP06.add_cond ssC_st1 (mkAC BC_GEU (SOff 43 0) SK3)) with ssC_ge in HS2.
    apply (kC_step E ssC_ge ssC_st2 _ ms1 _ FP HS2 ltac:(vm_compute; reflexivity) HAE runC2 ltac:(discriminate) HI1).
    intros ms2 mat2 HS3 HI2 HV2.
    assert (E33' : ew E 33 = Z_to_bv 64 (pos + k)) by (rewrite E33, Hn1k; reflexivity).
    assert (E34' : ew E 34 = Z_to_bv 64 (Z.max len (pos + k))) by (rewrite E34, Hn1k; reflexivity).
    assert (Hpk : pos + k <= 4096) by (unfold n1, amf_n1 in Hn1k; cbn [amf_size link_amf] in Hn1k; lia).
    assert (UR : U E SROOM = 4096 - (pos + k)) by (apply vl_room; [exact E33' | lia]).
    assert (U12 : U E (SOff 12 0) = Z.of_nat (length ds)) by (apply (U_atom E 12); [rewrite E12, H12; reflexivity | lia]).
    assert (KEEP2 : forall ms3, (forall a, 0 <= a < 2 ^ 64 -> ~ CW a ->
        aview tfibsegs (w_H W) (ms_mem ms3) a = aview tfibsegs (w_H W) (ms_mem ms2) a) ->
        forall a, 0 <= a < 2 ^ 64 -> ~ CW a -> aview tfibsegs (w_H W) (ms_mem ms3) a = aview tfibsegs (w_H W) (ms_mem ms) a).
    { intros ms3 H3 a Ha Hc. rewrite H3 by assumption. unfold CW in Hc.
      rewrite HV2 by (try exact Ha; intros Q; apply Hc; tauto). apply HV1; try exact Ha; intros Q; apply Hc; tauto. }
    assert (Hpb : firstn (Z.to_nat n1) pb = pb) by (apply firstn_all2; lia).
    rewrite Hpb in Hbz.
    destruct (Z_le_gt_dec (Z.of_nat (length ds)) (4096 - (pos + k))) as [Hfit | Hover].
    + (* +0x80 bgeu taken: the data fits *)
      pose proof (st_ok_add_cond tfibsegs E ssC_st2 _ BC_GEU SROOM (SOff 12 0) HS3
        ltac:(rewrite branch_geu_U, UR, U12; apply negb_true_iff, Z.ltb_ge; lia)) as HS4.
      change (YP06.add_cond ssC_st2 (mkAC BC_GEU SROOM (SOff 12 0))) with ssC_n in HS4.
      apply (kC_step E ssC_n ssM1 _ ms2 _ FP HS4 ltac:(vm_compute; reflexivity) HAE runM1 ltac:(discriminate) HI2).
      intros ms3 mat3 HS5 HI3 HV3.
      pose proof (KEEP2 ms3 ltac:(intros a Ha Hc; unfold CW in Hc; apply HV3; try exact Ha; intros Q; apply Hc; tauto)) as KP.
      pose proof (mw_cval E ssM1 ms3 (w_H W) 1 _ 0 0 4 (SOff 35 0) fl1 HS5 eq_refl eq_refl (DA 35%nat fl1 E35 ltac:(rewrite F1; destruct Hfl as [-> | ->]; unfold AF_NORD, AF_ERR; lia))
        ltac:(cbn; rewrite F1; destruct Hfl as [-> | ->]; unfold AF_NORD, AF_ERR; lia) ltac:(cbn; lia)) as VF.
      pose proof (mw_cval E ssM1 ms3 (w_H W) 2 _ 0 32 8 (SOff 36 0) wend1 HS5 eq_refl eq_refl (DA 36%nat wend1 E36 ltac:(rewrite F2; mwlia))
        ltac:(cbn; rewrite F2; mwlia) ltac:(cbn; lia)) as VW1.
      pose proof (mw_cval E ssM1 ms3 (w_H W) 2 _ 1 40 8 (SOff 37 0) wpos1 HS5 eq_refl eq_refl (DA 37%nat wpos1 E37 ltac:(rewrite F3; mwlia))
        ltac:(cbn; rewrite F3; mwlia) ltac:(cbn; lia)) as VW2.
      pose proof (mw_cval E ssM1 ms3 (w_H W) 3 _ 0 56 8 (SOff 38 0) wbase1 HS5 eq_refl eq_refl (DA 38%nat wbase1 E38 ltac:(rewrite F4; mwlia))
        ltac:(cbn; rewrite F4; mwlia) ltac:(cbn; lia)) as VW3.
      pose proof (mw_cval E ssM1 ms3 (w_H W) 4 _ 0 232 8 (SOff 33 0) (pos + k) HS5 eq_refl eq_refl (DA 33%nat _ E33' ltac:(lia))
        ltac:(cbn; lia) ltac:(cbn; lia)) as VP.
      pose proof (mw_cval E ssM1 ms3 (w_H W) 4 _ 1 240 8 (SOff 34 0) (Z.max len (pos + k)) HS5 eq_refl eq_refl (DA 34%nat _ E34' ltac:(lia))
        ltac:(cbn; lia) ltac:(cbn; lia)) as VL.
      cbn [base_val YP09.r_base] in VF, VW1, VW2, VW3, VP, VL. rewrite E10 in VF, VW1, VW2, VW3, VP, VL.
      rewrite F1 in VF. rewrite F2 in VW1. rewrite F3 in VW2. rewrite F4 in VW3.
      assert (Hat3 : amf_k tfibsegs link_amf (mrestrict (w_H W) (ms_mem ms3)) f 0).
      { apply (amf_at_rebuild (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms3)) f fl (f + 1304) (f + 280) (f + 280)
          (pos + k) (Z.max len (pos + k)) Hfa).
        - intros a Ha Hd. apply mbyte_of_aview. apply KP; [mwlia | exact (FW a Ha Hd)].
        - exact Hfl. - exact VF.
        - right. unfold AMF_BUF, AMF_BUFSIZ. lia.
        - exact VW1. - exact VW2. - exact VW3.
        - lia. - cbn [amf_size link_amf]. lia. - exact VP. - exact VL. }
      apply (kM E ssM1 ms3 _ (SOff 12 0) (Z.of_nat (length ds)) fl (f + 1304) (f + 280) (f + 280) HS5 eq_refl eq_refl
        ltac:(vm_compute; reflexivity) eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
        ltac:(vm_compute; submem_tac) ltac:(vm_compute; reflexivity) ssD_1 HAE E33' E34').
      * cbn [sv_denot]. rewrite E12, H12, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity.
      * unfold n1 in Hn1k. exact Hn1k.
      * lia.
      * intros Hc. lia.
      * intros _. auto.
      * exact HI3.
      * exact (proj1 Hat3).
      * exact VF. * exact VW1. * exact VW2. * exact VW3.
      * apply (mw_val_mem_xfer_av (w_H W) (ms_mem ms) (ms_mem ms3)); [|exact V136].
        intros i Hi. apply KP; [mwlia|]. apply (FW (f + 136 + i)); [unfold AMF_ZEROED; cbn in Hi; lia | unfold dynf; cbn in Hi; lia].
      * apply (mw_azbytes_xfer (w_H W) (ms_mem ms) (ms_mem ms3)); [|exact Hbz].
        intros i Hi. apply KP; [mwlia|]. pose proof kf_errno as (Ee & _). unfold CW. rewrite Ee. mwlia.
    + (* +0x80 bgeu not taken: ENOSPC, errno, F_ERR, the window emptied, n2 = size - pos1 *)
      pose proof (st_ok_add_cond_neg tfibsegs E ssC_st2 _ BC_GEU SROOM (SOff 12 0) HS3
        ltac:(rewrite branch_geu_U, UR, U12; apply negb_false_iff, Z.ltb_lt; lia)) as HS4.
      rewrite ssC_e_eq in HS4.
      apply (kC_step E ssC_e ssM2 _ ms2 _ FP HS4 ltac:(vm_compute; reflexivity) HAE runM2 ltac:(discriminate) HI2).
      intros ms3 mat3 HS5 HI3 HV3.
      pose proof (KEEP2 ms3 ltac:(intros a Ha Hc; unfold CW in Hc; apply HV3; try exact Ha; intros Q; apply Hc; tauto)) as KP.
      assert (D0 : sv_denot E (SLit 0) = Z_to_bv 64 0) by reflexivity.
      pose proof (mw_cval E ssM2 ms3 (w_H W) 1 _ 0 0 4 (SAlu ALU_OR (SExt true 32 (SOff 35 0)) (SLit 32)) (AF_NORD + AF_ERR) HS5 eq_refl eq_refl
        (vl_flags E fl1 E35 ltac:(rewrite F1; exact Hfl)) ltac:(cbn; unfold AF_NORD, AF_ERR; lia) ltac:(cbn; lia)) as VF.
      pose proof (mw_cval E ssM2 ms3 (w_H W) 2 _ 1 32 8 (SLit 0) 0 HS5 eq_refl eq_refl D0 ltac:(cbn; lia) ltac:(cbn; lia)) as VW1.
      pose proof (mw_cval E ssM2 ms3 (w_H W) 2 _ 0 40 8 (SLit 0) 0 HS5 eq_refl eq_refl D0 ltac:(cbn; lia) ltac:(cbn; lia)) as VW2.
      pose proof (mw_cval E ssM2 ms3 (w_H W) 3 _ 0 56 8 (SLit 0) 0 HS5 eq_refl eq_refl D0 ltac:(cbn; lia) ltac:(cbn; lia)) as VW3.
      pose proof (mw_cval E ssM2 ms3 (w_H W) 4 _ 0 232 8 (SOff 33 0) (pos + k) HS5 eq_refl eq_refl (DA 33%nat _ E33' ltac:(lia))
        ltac:(cbn; lia) ltac:(cbn; lia)) as VP.
      pose proof (mw_cval E ssM2 ms3 (w_H W) 4 _ 1 240 8 (SOff 34 0) (Z.max len (pos + k)) HS5 eq_refl eq_refl (DA 34%nat _ E34' ltac:(lia))
        ltac:(cbn; lia) ltac:(cbn; lia)) as VL.
      cbn [base_val YP09.r_base] in VF, VW1, VW2, VW3, VP, VL. rewrite E10 in VF, VW1, VW2, VW3, VP, VL.
      assert (Hat3 : amf_k tfibsegs link_amf (mrestrict (w_H W) (ms_mem ms3)) f 0).
      { apply (amf_at_rebuild (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms3)) f (AF_NORD + AF_ERR) 0 0 0
          (pos + k) (Z.max len (pos + k)) Hfa).
        - intros a Ha Hd. apply mbyte_of_aview. apply KP; [mwlia | exact (FW a Ha Hd)].
        - right. reflexivity. - exact VF.
        - left. auto.
        - exact VW1. - exact VW2. - exact VW3.
        - lia. - cbn [amf_size link_amf]. lia. - exact VP. - exact VL. }
      apply (kM E ssM2 ms3 _ SROOM (4096 - (pos + k)) (Z.lor fl AF_ERR) 0 0 0 HS5 eq_refl eq_refl
        ltac:(vm_compute; reflexivity) eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
        ltac:(vm_compute; submem_tac) ltac:(vm_compute; reflexivity) ssD_2 HAE E33' E34').
      * rewrite denot_lit_U, UR. reflexivity.
      * unfold n1 in Hn1k. exact Hn1k.
      * lia.
      * intros _. auto.
      * intros Hc. lia.
      * exact HI3.
      * exact (proj1 Hat3).
      * rewrite kf_lor. exact VF. * exact VW1. * exact VW2. * exact VW3.
      * apply (mw_val_mem_xfer_av (w_H W) (ms_mem ms) (ms_mem ms3)); [|exact V136].
        intros i Hi. apply KP; [mwlia|]. apply (FW (f + 136 + i)); [unfold AMF_ZEROED; cbn in Hi; lia | unfold dynf; cbn in Hi; lia].
      * apply (mw_azbytes_xfer (w_H W) (ms_mem ms) (ms_mem ms3)); [|exact Hbz].
        intros i Hi. apply KP; [mwlia|]. pose proof kf_errno as (Ee & _). unfold CW. rewrite Ee. mwlia.
Qed.

(* ---- the values the inner call leaves: atoms 33..38 of the walk, fixed in the entry environment ---- *)
Definition kn1 : Z := amf_n1 link_amf k pos.
Definition kfl1 : Z := if kn1 <? k then Z.lor fl AF_ERR else fl.
Definition kwe1 : Z := if kn1 <? k then 0 else f + 1304.
Definition kwb1 : Z := if kn1 <? k then 0 else f + 280.
Definition EK : env := Ereg regs [Z_to_bv 64 (f + 280 + k); Z_to_bv 64 (pos + kn1); Z_to_bv 64 (Z.max len (pos + kn1));
  Z_to_bv 64 kfl1; Z_to_bv 64 kwe1; Z_to_bv 64 kwb1; Z_to_bv 64 kwb1].

Lemma EK_agree : env_agree 33 E0 EK.
Proof.
  split; [|reflexivity]. intros n Hn. unfold E0, EK, Ereg. cbn [ew].
  destruct (n <? 32)%nat eqn:Hc; [reflexivity|]. apply Nat.ltb_ge in Hc. replace n with 32%nat by lia. reflexivity.
Qed.

Lemma kn1_facts : 0 <= kn1 <= k /\ (kn1 < k -> kn1 = 4096 - pos) /\ (kn1 = k -> pos + k <= 4096).
Proof. pose proof kf_cookie as (Hpl & Hls & _). unfold kn1, amf_n1. cbn [amf_size link_amf]. lia. Qed.

(* ---- one phase, with the windows of the entry shape (stack frame, f->wpos) ---- *)
Lemma kA_gen : forall E ss ss' ms md' Q,
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> windows (ss_mem ss) = [(Some 2%nat, -48, 0); (Some 10%nat, 40, 48)] ->
  env_agree 33 E0 E -> INVk (ms_mem ms) md' ->
  SRr tfibsegs W (mkCfg ms md')
    (fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md') mat1 md') /\
       st_ok tfibsegs E ss' (restrict (w_H W) ms1) /\
       frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\
       frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1)) /\
       mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))) ->
  (forall ms1 mat1, st_ok tfibsegs E ss' (restrict (w_H W) ms1) ->
     INVk (ms_mem ms1) (with_vm_backing (m_vm_lazy md') mat1 md') ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 48 <= a < spZ regs) -> ~ (f + 40 <= a < f + 48) ->
        aview tfibsegs (w_H W) (ms_mem ms1) a = aview tfibsegs (w_H W) (ms_mem ms) a) ->
     SRr tfibsegs W (mkCfg ms1 (with_vm_backing (m_vm_lazy md') mat1 md')) Q) ->
  SRr tfibsegs W (mkCfg ms md') Q.
Proof.
  intros E ss ss' ms md' Q HS Hw HAE HI Hph Hk.
  destruct (k_E E HAE) as (E2 & E10 & _).
  eapply SRr_bind; [exact Hph|].
  intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1 & HG1).
  assert (WIN : forall z, in_wrange E (ss_mem ss) z -> (spZ regs - 48 <= z < spZ regs) \/ (f + 40 <= z < f + 48)).
  { intros z Hz. destruct (mw_winA E (ss_mem ss) z Hw Hz) as [Hz'|Hz']; rewrite ?E2, ?E10 in Hz'; [left|right]; lia. }
  apply Hk; [exact HS1 | |].
  - apply (INV_run B LAWS ly S W (spZ regs) f mem md (fun z => (spZ regs - 48 <= z < spZ regs) \/ (f + 40 <= z < f + 48))
      (ms_mem ms) md' (ms_mem ms1) mat1 HI).
    + intros y Hy. apply HF1. intros Hin. apply Hy. exact (WIN _ Hin).
    + intros y Hy. apply HFr1. intros Hin. apply Hy. exact (WIN _ Hin).
    + exact HG1.
    + intros z [Hz|Hz]; apply kf_safe; [left; mwlia | right; left; mwlia].
  - intros z Hz H1 H2. apply aview_eq_of. apply HFr1. rewrite unsigned_lit_small by lia. intros Hin. destruct (WIN _ Hin); lia.
Qed.

(* ---- the entry state: the frame mwrite pushes, f->wpos, f->wbase, f->cookie ---- *)
Lemma kA_entry : st_ok tfibsegs EK ssA (restrict (w_H W) (mkst regs (Z_to_bv 64 LA_MWRITE) mem (seg_rom tfibsegs))).
Proof.
  pose proof kf_blk as (_ & B4 & Bs & _ & Bp & _). pose proof kf_lay as (L1 & L2 & L3 & L4). pose proof kf_win as (Wend & Wpos & Wbase).
  pose proof Hamk as ((_ & _ & _ & Hst & _) & _).
  destruct Hst as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S152 & _).
  pose proof Hdyn as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D40 & D56 & _).
  assert (EK2 : bv_unsigned (ew EK 2) = spZ regs) by (unfold EK; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
  assert (EK10 : bv_unsigned (ew EK 10) = f) by (destruct (k_E EK EK_agree) as (_ & E10 & _); exact E10).
  assert (EK32 : ew EK 32 = Z_to_bv 64 (f + 280 + k)) by exact (ew_Ereg_extra regs _ 0).
  rewrite restrict_mkst_fx. unfold ssA. apply (entry_st_ok_full tfibsegs); fold EK.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (region_ok_stack tfibsegs EK _ 2 (spZ regs) (-48)); [exact EK2 | mwlia | mwlia |].
      intros a Ha. apply apresent_writable. apply Hpres. mwlia.
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val R_fileA]. rewrite EK10.
      split; [lia|]. split; [mwlia|].
      split; [intros o Ho; apply apresent_writable; exact (proj1 (Bp (f + o) ltac:(mwlia)))|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
      * apply (chunk_ok_val tfibsegs EK _ f 40 8 (SOff 32 0) (f + 280 + k));
          [cbn [sv_denot]; rewrite EK32, unsigned_lit_small, Z.add_0_r by mwlia; reflexivity | cbn; mwlia | cbn; lia |].
        rewrite <- Wpos. exact D40.
      * apply (chunk_ok_val tfibsegs EK _ f 56 8 (SOff 10 280) (f + 280)); [cbn [sv_denot]; rewrite EK10; reflexivity | cbn; mwlia | cbn; lia |].
        rewrite <- Wbase. exact D56.
      * apply (chunk_ok_val tfibsegs EK _ f 152 8 (SOff 10 232) (f + 232)); [cbn [sv_denot]; rewrite EK10; reflexivity | cbn; mwlia | cbn; lia |].
        exact S152.
  - apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val R_stkA R_fileA]. rewrite EK2, EK10.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; mwlia.
  - split; [cbn; exact I | split; exact I].
Qed.

(* ---- +0x4c jal 0x96cc0: the inner call (the k = 0 contract HK0, one frame lower), then the state after it ---- *)
Lemma kB : forall ms md',
  st_ok tfibsegs EK ssA_end (restrict (w_H W) ms) ->
  INVk (ms_mem ms) md' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 48 <= a < spZ regs) -> ~ (f + 40 <= a < f + 48) ->
     aview tfibsegs (w_H W) (ms_mem ms) a = aview tfibsegs (w_H W) mem a) ->
  SRr tfibsegs W (mkCfg ms md') FP.
Proof.
  intros ms md' HS HI HV.
  pose proof kf_blk as (_ & B4 & Bs & Bap & Bp & Bsh & Bhull). pose proof kf_lay as (L1 & L2 & L3 & L4). pose proof kf_fimg as Fi.
  pose proof kf_cookie as (Hpl & Hls & Hom). pose proof kf_pre as (_ & _ & Hal & Hslo & Htop & Hgp & Htp).
  pose proof kf_win as (Wend & Wpos & Wbase). pose proof kf_errno as (Ee & Etp). pose proof kn1_facts as (N1a & N1b & N1c).
  pose proof kf_fl as Hfl.
  destruct (k_E EK EK_agree) as (E2 & E10 & E32 & _ & E3 & E4 & _ & _ & E4v).
  pose proof HI as (HAR & Hsbm & Hfr & Hpr & Hwp).
  pose proof Hdyn as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & D0 & D136 & D32 & D40 & D56 & D232 & D240).
  pose proof Hbuf as (Hb0 & Hb1 & Hb2 & Hbw & Hbam & Hbra & Hbhull).
  pose proof HS as HS0.
  pose proof (st_ok_restrict_mkst tfibsegs (w_H W) EK ssA_end ms HS eq_refl) as Hshape.
  change (ss_pc ssA_end) with LA_MWRITE in Hshape.
  assert (DA : forall n v, ew EK n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot EK (SOff n 0) = Z_to_bv 64 v)
    by (intros n v Hn Hv; cbn [sv_denot]; rewrite Hn, unsigned_lit_small, Z.add_0_r by lia; reflexivity).
  assert (G1 : getr (ms_regs ms) 1 = Z_to_bv 64 0x96d10)
    by (rewrite (mw_reg_sv EK ssA_end ms (w_H W) 1 (SLit 617744) HS ltac:(vm_compute; reflexivity)); reflexivity).
  assert (G2 : getr (ms_regs ms) 2 = Z_to_bv 64 (spZ regs - 48))
    by (rewrite (mw_reg_sv EK ssA_end ms (w_H W) 2 (SOff 2 (-48)) HS ltac:(vm_compute; reflexivity)); cbn [sv_denot];
        rewrite E2; f_equal; lia).
  assert (G3 : getr (ms_regs ms) 3 = w64 (as_gp B))
    by (rewrite (mw_reg_atom EK ssA_end ms (w_H W) 3 3 HS ltac:(vm_compute; reflexivity)), E3; exact Hgp).
  assert (G4 : getr (ms_regs ms) 4 = w64 (as_tp B))
    by (rewrite (mw_reg_atom EK ssA_end ms (w_H W) 4 4 HS ltac:(vm_compute; reflexivity)), E4; exact Htp).
  assert (G10 : getr (ms_regs ms) 10 = w64 f)
    by (rewrite (mw_reg_atom EK ssA_end ms (w_H W) 10 10 HS ltac:(vm_compute; reflexivity));
        unfold EK; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
  assert (G11 : getr (ms_regs ms) 11 = w64 (f + 280))
    by (rewrite (mw_reg_sv EK ssA_end ms (w_H W) 11 (SOff 10 280) HS ltac:(vm_compute; reflexivity)); cbn [sv_denot];
        rewrite E10; reflexivity).
  assert (G12 : getr (ms_regs ms) 12 = w64 (Z.of_nat (length pb))).
  { rewrite (mw_reg_sv EK ssA_end ms (w_H W) 12 SKA2 HS ltac:(vm_compute; reflexivity)), denot_lit_U.
    rewrite (proj2 (vl_k EK f k E10 E32 ltac:(lia) ltac:(lia) ltac:(mwlia))), Hpbk. reflexivity. }
  assert (Hsp : spZ (ms_regs ms) = spZ regs - 48) by (unfold spZ at 1; rewrite G2; apply unsigned_lit_small; mwlia).
  assert (Hra1 : raZ (ms_regs ms) = 0x96d10) by (unfold raZ; rewrite G1; apply unsigned_lit_small; lia).
  assert (TF1 : forall off (nb : nat) v, 0 <= off -> off + Z.of_nat nb <= 272 -> (off + Z.of_nat nb <= 40 \/ 48 <= off) ->
    val_mem tfibsegs (mrestrict (w_H W) mem) (f + off) nb v -> val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (f + off) nb v).
  { intros off nb v H0 H1 H2 Hv. apply (mw_val_mem_xfer_av (w_H W) mem (ms_mem ms)); [|exact Hv].
    intros i Hi. apply HV; mwlia. }
  pose proof (mw_cval EK ssA_end ms (w_H W) 1 _ 0 40 8 (SOff 10 280) (f + 280) HS eq_refl eq_refl
    ltac:(cbn [sv_denot]; rewrite E10; reflexivity) ltac:(cbn; mwlia) ltac:(cbn; lia)) as V40.
  cbn [base_val YP09.r_base] in V40. rewrite E10 in V40.
  set (regs1 := ms_regs ms) in *. set (m1 := ms_mem ms) in *.
  rewrite Hshape. pose proof HK0 as K0. unfold amwrite_mf_k0_realizes, amwrite_mf_at, cfg_at in K0.
  eapply SRr_bind.
  { apply (K0 ly S W regs1 m1 md' f 0 fl om (f + 1304) (f + 280) (f + 280) pos len (f + 280) [] pb).
    - split; [exact HAR|]. split; [rewrite G1; apply YK0s.ret_ok_even; rewrite unsigned_lit_small by lia; reflexivity|].
      rewrite Hsp. split; [rewrite Zminus_mod, Hal; reflexivity|]. split; [mwlia|]. split; [lia|].
      split; [intros a Ha; apply Hwp; mwlia|]. split; [exact G3 | exact G4].
    - rewrite Hsp. unfold AMW0_STK. mwlia.
    - intros a Ha. rewrite Hsp in Ha. apply Hwp. unfold AMW0_STK in Ha. mwlia.
    - exact G10.
    - exact G11.
    - exact G12.
    - exact Hblk.
    - apply (amf_at_rebuild (mrestrict (w_H W) mem) (mrestrict (w_H W) m1) f fl (f + 1304) (f + 280) (f + 280) pos len (proj1 Hamk)).
      + intros a Ha Hd. apply mbyte_of_aview. unfold dynf in Hd. apply HV; mwlia.
      + exact Hfl.
      + apply TF1; [lia | cbn; lia | cbn; lia | exact D0].
      + right. unfold AMF_BUF, AMF_BUFSIZ. lia.
      + rewrite <- Wend. apply TF1; [lia | cbn; lia | cbn; lia | exact D32].
      + exact V40.
      + rewrite <- Wbase. apply TF1; [lia | cbn; lia | cbn; lia | exact D56].
      + lia.
      + cbn [amf_size link_amf]. lia.
      + apply TF1; [mwlia | cbn; mwlia | cbn; mwlia | exact D232].
      + apply TF1; [mwlia | cbn; mwlia | cbn; mwlia | exact D240].
    - lia.
    - unfold amf_dyn. split; [exact R1|]. split; [exact R2|]. split; [mwlia|]. split; [mwlia|]. split; [mwlia|].
      split; [exact R6|]. split; [exact R7|].
      split; [apply TF1; [lia | cbn; lia | cbn; lia | exact D0]|].
      split; [apply TF1; [lia | cbn; lia | cbn; lia | exact D136]|].
      split; [rewrite <- Wend; apply TF1; [lia | cbn; lia | cbn; lia | exact D32]|].
      split; [exact V40|].
      split; [rewrite <- Wbase; apply TF1; [lia | cbn; lia | cbn; lia | exact D56]|].
      split; [apply TF1; [mwlia | cbn; mwlia | cbn; mwlia | exact D232] | apply TF1; [mwlia | cbn; mwlia | cbn; mwlia | exact D240]].
    - intros i Hi. cbn in Hi. lia.
    - reflexivity.
    - split; [exact Hb0|]. split; [exact Hb1|]. split; [exact Hb2|].
      split; [intros a Ha; destruct (Hbw a Ha) as (Hw & Ho & Hs);
              split; [exact (mw_writable_grows (w_H W) mem m1 a (mw_apresent_restrict _ _ _ Hpr) Hw)|];
              split; [exact Ho|]; rewrite Hsp; unfold AMW0_STK; mwlia|].
      split; [exact Hbam|].
      split; [apply (kf_ra_xfer m1 md' _ _ HI); [mwlia | mwlia | exact Hbra]|].
      apply (kf_hull_xfer m1 md' _ _ HI); [mwlia | mwlia | mwlia | exact Hbhull].
    - exact (kf_pend m1 md' HI).
    - lia.
    - mwlia.
    - unfold amem_range. destruct Bap as [Q|Q]; [left | right]; mwlia.
    - apply (kf_ra_xfer m1 md' _ _ HI); [lia | mwlia |].
      apply (mw_block_ra _ _ f AMF_BLOCK); [exact Bsh | reflexivity | lia | mwlia].
    - intros Hn. apply (kf_hull_xfer m1 md' _ _ HI); [lia | exact Hn | mwlia |].
      apply (mw_hull_sub _ f AMF_BLOCK); [exact Bhull | lia | exact Hn | mwlia | lia].
    - intros a Ha. split; [mwlia|]. split; [mwlia|]. split; [rewrite Ee; mwlia|]. rewrite Hsp. unfold AMW0_STK. mwlia. }
  intros W2 c2 _ (-> & regs2 & m2 & md2 & HP). cbv zeta in HP.
  destruct HP as (-> & HAR2 & HP2 & Hsbm2 & Hk2 & Hpend2 & _ & Heq2 & Hfr2 & Hpr2 & Hwp2).
  assert (Hi0 : amf_n1 link_amf 0 pos = 0) by (unfold amf_n1; cbn [amf_size link_amf]; lia).
  assert (Hp0 : amw_pos1 link_amf 0 pos = pos) by (unfold amw_pos1; rewrite Hi0; lia).
  assert (Hn2i : amw_n2 link_amf 0 pos (Z.of_nat (length pb)) = kn1)
    by (unfold amw_n2, kn1, amf_n1; rewrite Hp0; cbn [amf_size link_amf]; lia).
  destruct (Heq2 Hi0) as (Ha2 & (fl' & we' & wp' & wb' & Hdyn2 & Hlt2 & Heq2') & Hbz2).
  rewrite Hp0, Hn2i in Hdyn2. rewrite Hn2i in Ha2, Hlt2, Heq2', Hbz2.
  assert (FV : fl' = kfl1 /\ we' = kwe1 /\ wp' = kwb1 /\ wb' = kwb1).
  { unfold kfl1, kwe1, kwb1. destruct (Z.ltb_spec kn1 k) as [Hl|Hg].
    - destruct (Hlt2 ltac:(lia)) as (A1 & A2 & A3 & A4). auto.
    - destruct (Heq2' ltac:(lia)) as (A1 & A2 & A3 & A4). auto. }
  destruct FV as (-> & -> & -> & ->).
  pose proof Hdyn2 as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & P0 & P136 & P32 & P40 & P56 & P232 & P240).
  destruct Hk2 as (Hat2 & _). pose proof Hat2 as (_ & _ & _ & Hst2 & _).
  destruct Hst2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ssz & Sbuf & Smode).
  assert (PG2 : forall y, mrestrict (w_H W) m1 y <> None -> mrestrict (w_H W) m2 y <> None) by exact (mw_apresent_restrict _ _ _ Hpr2).
  assert (PR2 : forall a, f <= a < f + AMF_BLOCK -> apresent (w_H W) m2 a) by (intros a Ha; apply Hpr2, Hpr, (proj1 (Bp a Ha))).
  (* the stack frame mwrite pushed: outside the inner call's window *)
  assert (HR0 : region_ok tfibsegs EK (mrestrict (w_H W) m1) R_stkC) by exact (mw_region_ok EK ssA_end ms (w_H W) 0 R_stkC HS0 eq_refl).
  assert (KEPT0 : region_kept tfibsegs EK (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) R_stkC).
  { apply (mw_region_kept EK (w_H W) m1 m2 R_stkC); [|exact PG2].
    intros a Ha. cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi R_stkC] in Ha. rewrite E2 in Ha.
    apply Hfr2; [mwlia | rewrite Hsp; unfold AMW0_STK; mwlia | mwlia | mwlia | rewrite Ee; mwlia]. }
  assert (HM0 : mem_ok tfibsegs EK (mrestrict (w_H W) m1) [R_stkC]).
  { split; [vm_compute; reflexivity|]. split; [apply Forall_cons; [exact HR0 | apply Forall_nil] | split; exact I]. }
  pose proof (mem_ok_kept tfibsegs EK (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) [R_stkC] HM0
    ltac:(vm_compute; reflexivity) ltac:(apply Forall_cons; [exact KEPT0 | apply Forall_nil])) as (_ & HR0' & _).
  assert (HM : mem_ok tfibsegs EK (mrestrict (w_H W) m2) rsC).
  { split; [vm_compute; reflexivity|]. split.
    - unfold rsC. apply Forall_cons; [exact (Forall_inv HR0')|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]].
      + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val RF_fl]. rewrite E10.
        split; [lia|]. split; [mwlia|]. split; [intros o Ho; apply apresent_writable; apply PR2; mwlia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val tfibsegs EK _ f 0 4 (SOff 35 0) kfl1); [apply DA; [exact (ew_Ereg_extra regs _ 3) | lia] | cbn; lia | cbn; lia | exact P0].
      + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val RF_win]. rewrite E10.
        split; [lia|]. split; [mwlia|]. split; [intros o Ho; apply apresent_writable; apply PR2; mwlia|].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
        * apply (chunk_ok_val tfibsegs EK _ f 32 8 (SOff 36 0) kwe1); [apply DA; [exact (ew_Ereg_extra regs _ 4) | lia] | cbn; lia | cbn; lia | exact P32].
        * apply (chunk_ok_val tfibsegs EK _ f 40 8 (SOff 37 0) kwb1); [apply DA; [exact (ew_Ereg_extra regs _ 5) | lia] | cbn; lia | cbn; lia | exact P40].
      + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val RF_wb]. rewrite E10.
        split; [lia|]. split; [mwlia|]. split; [intros o Ho; apply apresent_writable; apply PR2; mwlia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val tfibsegs EK _ f 56 8 (SOff 38 0) kwb1); [apply DA; [exact (ew_Ereg_extra regs _ 6) | lia] | cbn; lia | cbn; lia | exact P56].
      + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val RF_ck]. rewrite E10.
        split; [lia|]. split; [mwlia|]. split; [intros o Ho; apply apresent_writable; apply PR2; mwlia|].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]].
        * apply (chunk_ok_val tfibsegs EK _ f 232 8 (SOff 33 0) (pos + kn1));
            [apply DA; [exact (ew_Ereg_extra regs _ 1) | lia] | cbn; lia | cbn; lia | exact P232].
        * apply (chunk_ok_val tfibsegs EK _ f 240 8 (SOff 34 0) (Z.max len (pos + kn1)));
            [apply DA; [exact (ew_Ereg_extra regs _ 2) | lia] | cbn; lia | cbn; lia | exact P240].
        * apply (chunk_ok_val tfibsegs EK _ f 248 8 (SLit 4096) 4096); [reflexivity | cbn; lia | cbn; lia | exact Ssz].
        * apply (chunk_ok_val tfibsegs EK _ f 256 8 (SLit 0x62fee0) 0x62fee0); [reflexivity | cbn; lia | cbn; lia | exact Sbuf].
        * apply (chunk_ok_val tfibsegs EK _ f 264 4 (SLit 119) 119); [reflexivity | cbn; lia | cbn; lia | exact Smode].
      + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val R_errno]. rewrite E4v.
        split; [lia|]. split; [lia|]. split; [intros o Ho; apply mw_errno_writable; lia | apply Forall_nil].
    - apply pairwise_disjoint_of_extents. unfold rsC, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val R_stkC RF_fl RF_win RF_wb RF_ck R_errno]. rewrite E2, E10, E4v.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; mwlia. }
  rewrite Hshape in HS. rewrite restrict_mkst_fx in HS.
  pose proof (st_ok_splice_havoc tfibsegs 39 EK ssA_end regs1 regs2 (Z_to_bv 64 LA_MWRITE) 0x96d10
    (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) rsC [] CLOB HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
    (fun r Hr => regs_preserved_frame regs1 regs2 HP2 r Hr) (Forall_nil _) HM) as HSC.
  rewrite ssC_eq in HSC.
  unfold cfg_at. rewrite Hra1. change (w64 0x96d10) with (Z_to_bv 64 0x96d10).
  apply (kC (havoc EK 39 (map (getr regs2) CLOB)) (mkst regs2 (Z_to_bv 64 0x96d10) m2 (seg_rom tfibsegs)) md2 kfl1 kwe1 kwb1 kwb1).
  - rewrite restrict_mkst_fx. exact HSC.
  - exact (env_agree_trans 33 E0 EK _ EK_agree (env_agree_le 39 33 _ _ ltac:(lia) (env_agree_havoc EK 39 _))).
  - rewrite ew_havoc_old by lia. exact (ew_Ereg_extra regs _ 1).
  - rewrite ew_havoc_old by lia. exact (ew_Ereg_extra regs _ 2).
  - rewrite ew_havoc_old by lia. exact (ew_Ereg_extra regs _ 3).
  - rewrite ew_havoc_old by lia. exact (ew_Ereg_extra regs _ 4).
  - rewrite ew_havoc_old by lia. exact (ew_Ereg_extra regs _ 5).
  - rewrite ew_havoc_old by lia. exact (ew_Ereg_extra regs _ 6).
  - change 43%nat with (39 + 4)%nat.
    rewrite (ew_havoc_new EK 39 (map (getr regs2) CLOB) 4 (Z_to_bv 64 0)) by (rewrite length_map; unfold CLOB; cbn; lia).
    exact Ha2.
  - intros Hl. unfold kfl1, kwe1, kwb1. replace (kn1 <? k) with true by (symmetry; apply Z.ltb_lt; exact Hl). auto.
  - intros He. unfold kfl1, kwe1, kwb1. replace (kn1 <? k) with false by (symmetry; apply Z.ltb_ge; unfold kn1; lia). auto.
  - apply (INV_call B ly S W (spZ regs) f mem md
      (fun a => (spZ regs - 48 - AMW0_STK <= a < spZ regs - 48) \/ (f <= a < f + AMF_ZEROED) \/
                (amf_buf link_amf <= a < amf_buf link_amf + amf_size link_amf) \/ (as_errno B <= a < as_errno B + 4))
      m1 md' m2 md2 HI HAR2 Hsbm2).
    + intros a Ha Hn. apply Hfr2; [exact Ha | rewrite Hsp; intros Q; apply Hn; left; exact Q
        | intros Q; apply Hn; right; left; exact Q | intros Q; apply Hn; right; right; left; exact Q
        | intros Q; apply Hn; right; right; right; exact Q].
    + exact Hpr2.
    + intros a Hk. unfold mw_chg. unfold AMW0_STK in Hk. unfold AMW_STK. lia.
  - exact Hat2.
  - exact P136.
  - exact Hbz2.
Qed.

(* ---- the walk at k > 0: +0x00 to the inner call, then kB ---- *)
Lemma kA : SRr tfibsegs W (cfg_at tfibsegs LA_MWRITE regs mem md) FP.
Proof.
  pose proof kf_pre as (HAR & _). pose proof kf_lay as (L1 & L2 & L3 & L4). pose proof kf_blk as (_ & B4 & Bs & _).
  destruct (k_E EK EK_agree) as (E2 & E10 & E32 & _).
  unfold cfg_at. change (w64 LA_MWRITE) with (Z_to_bv 64 LA_MWRITE).
  assert (HI0 : INVk mem md) by (apply INV_init; [exact HAR | exact Hpres]).
  apply (kA_gen EK ssA ssA_st1 _ md FP kA_entry ltac:(vm_compute; reflexivity) EK_agree HI0
           (mw_phase W EK ssA ssA_st1 _ _ md kA_entry runA1 ltac:(discriminate))).
  intros ms1 mat1 HS1 HI1 HV1.
  assert (U32 : U EK (SOff 32 0) = f + 280 + k) by (apply (U_atom EK 32); [exact E32 | mwlia]).
  assert (U10 : U EK (SOff 10 280) = f + 280) by (rewrite U_SOff, E10; apply (zc_eq _ 0); mwlia).
  pose proof (st_ok_add_cond_neg tfibsegs EK ssA_st1 _ BC_EQ (SOff 32 0) (SOff 10 280) HS1
    ltac:(rewrite branch_eq_U, U32, U10; apply Z.eqb_neq; lia)) as HS2.
  rewrite ssA1_eq in HS2.
  apply (kA_gen EK ssA1 ssA_end _ _ FP HS2 ltac:(vm_compute; reflexivity) EK_agree HI1
           (mw_phase_to W EK LA_MWRITE ssA1 ssA_end _ _ _ HS2 runA2 ltac:(discriminate))).
  intros ms2 mat2 HS3 HI2 HV2.
  apply (kB ms2 _ HS3 HI2). intros a Ha H1 H2. rewrite HV2 by assumption. exact (HV1 a Ha H1 H2).
Qed.

End K.

(* ==========================================================================
   7. The theorems
   ========================================================================== *)

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis TB : PcapSyms B.
Hypothesis AMEMCPY : aintrin_realizes tfibsegs B OCpy (pc_wrap_memcpy (as_code B)).
Hypothesis HK0 : amwrite_mf_k0_realizes tfibsegs B link_amf LA_MWRITE.

Theorem link_amwrite_gen : amwrite_mf_realizes tfibsegs B link_amf LA_MWRITE.
Proof.
  intros ly S W regs mem md f k fl om wend wpos wbase pos len x pb ds HPRE Hstk Hpres H10 H11 H12 Hblk Hamk Hkmax Hdyn
    Hpend Hpbk Hbuf Hds Hx0 Hxn Hxam Hxra Hxhull Hxdisj.
  destruct (Z.eq_dec k 0) as [-> | Hk0].
  - (* k = 0: the k = 0 contract at the same sp; its window lies inside this one *)
    pose proof HK0 as K0. unfold amwrite_mf_k0_realizes, amwrite_mf_at in K0.
    eapply SRr_bind.
    { apply (K0 ly S W regs mem md f 0 fl om wend wpos wbase pos len x pb ds HPRE
               ltac:(unfold AMW0_STK, AMW_STK in *; lia)
               (fun a Ha => Hpres a ltac:(unfold AMW0_STK, AMW_STK in *; lia))
               H10 H11 H12 Hblk Hamk ltac:(lia) Hdyn Hpend Hpbk
               (amf_buf_ok_sub tfibsegs B link_amf AMW_STK AMW0_STK ly S W regs regs mem
                  ltac:(unfold AMW0_STK, AMW_STK; lia) ltac:(lia) Hbuf)
               Hds Hx0 Hxn Hxam Hxra Hxhull).
      intros a Ha. destruct (Hxdisj a Ha) as (N1 & N2 & N3 & N4).
      split; [exact N1|]. split; [exact N2|]. split; [exact N3|]. unfold AMW0_STK, AMW_STK in *. lia. }
    intros W' c' _ (-> & regs' & mem' & md' & HP). apply SRr_ret. split; [reflexivity|]. exists regs', mem', md'.
    cbv zeta in HP |- *. destruct HP as (Hc & HAR' & HP' & Hsbm & Hk' & Hpend' & Hlt & Heq & Hfr & Hpr & Hwp).
    split; [exact Hc|]. split; [exact HAR'|]. split; [exact HP'|]. split; [exact Hsbm|]. split; [exact Hk'|].
    split; [exact Hpend'|]. split; [exact Hlt|]. split; [exact Heq|]. split; [|split; [exact Hpr|]].
    + intros a Ha H1 H2 H3 H4. apply Hfr; [exact Ha | unfold AMW0_STK, AMW_STK in *; lia | exact H2 | exact H3 | exact H4].
    + intros a Ha. apply Hpr. apply Hpres. exact Ha.
  - (* k > 0: the walk *)
    assert (Hkpos : 0 < k) by lia.
    eapply SRr_bind; [eapply kA; eassumption|].
    intros W' c' _ (-> & regs' & mem' & md' & Hc & HAR' & HP' & Hsbm & HPF & Hfr & Hpr & Hwp).
    unfold PF in HPF. cbv zeta in HPF. destruct HPF as (Hk' & Hpend' & Hlt & Heq).
    apply SRr_ret. split; [reflexivity|]. exists regs', mem', md'. cbv zeta.
    split; [exact Hc|]. split; [exact HAR'|]. split; [exact HP'|]. split; [exact Hsbm|]. split; [exact Hk'|].
    split; [exact Hpend'|]. split; [exact Hlt|]. split; [exact Heq|]. split; [|split; [exact Hpr | exact Hwp]].
    intros a Ha H1 H2 H3 H4. apply Hfr; [exact Ha|]. unfold mw_chg. tauto.
Qed.

(* the flush f->write(f, 0, 0): theorem 1 at x = 0, no data *)
Theorem link_amwrite_flush : amwrite_mf_flush_realizes tfibsegs B link_amf LA_MWRITE.
Proof.
  intros ly S W regs mem md f k fl om wend wpos wbase pos len pb HPRE Hstk Hpres H10 H11 H12 Hblk Hamk Hdyn Hpend Hpbk Hbuf.
  assert (Hkmax : k <= AMF_BUFSIZ) by (destruct Hamk as (_ & [(-> & _) | (Hk & _)]); unfold AMF_BUFSIZ in *; lia).
  assert (Hpl : 0 <= pos <= len /\ len <= 4096)
    by (destruct Hdyn as (_ & _ & _ & _ & _ & H6 & H7 & _); cbn [amf_size link_amf] in H7; lia).
  eapply SRr_bind.
  { apply (link_amwrite_gen ly S W regs mem md f k fl om wend wpos wbase pos len 0 pb [] HPRE Hstk Hpres H10 H11 H12 Hblk Hamk
             Hkmax Hdyn Hpend Hpbk Hbuf).
    - intros i Hi. cbn in Hi. lia.
    - lia.
    - cbn. lia.
    - unfold amem_range. left. cbn. unfold kLowMemEnd. lia.
    - apply range_addressable_nil. cbn. lia.
    - intros Hc. cbn in Hc. lia.
    - intros a Ha. cbn in Ha. lia. }
  intros W' c' _ (-> & regs' & mem' & md' & HP). apply SRr_ret. split; [reflexivity|]. exists regs', mem', md'.
  cbv zeta in HP |- *. destruct HP as (Hc & HAR' & HP' & Hsbm & Hk' & Hpend' & Hlt & Heq & Hfr & Hpr & Hwp).
  change (Z.of_nat (length (@nil Z))) with 0 in Hlt, Heq.
  split; [exact Hc|]. split; [exact HAR'|]. split; [exact HP'|]. split; [exact Hsbm|].
  destruct (Z_lt_ge_dec (amf_n1 link_amf k pos) k) as [Hl | Hg].
  - destruct (Hlt Hl) as (R0 & D & Z0).
    split; [exact R0|]. split; [exact Hk'|]. split; [exact Hpend'|]. split; [exact Z0|].
    split; [intros _; exact D|]. split; [intros He; lia|]. split; [exact Hfr|]. split; [exact Hpr | exact Hwp].
  - assert (He : amf_n1 link_amf k pos = k) by (unfold amf_n1 in *; lia).
    assert (N2 : amw_n2 link_amf k pos 0 = 0)
      by (unfold amw_n2, amw_pos1; rewrite He; unfold amf_n1 in He; cbn [amf_size link_amf] in *; lia).
    assert (P1 : amw_pos1 link_amf k pos = pos + k) by (unfold amw_pos1; rewrite He; reflexivity).
    destruct (Heq He) as (R0 & (fl' & we' & wp' & wb' & D & _ & Hn) & Z0).
    rewrite N2 in R0, D, Hn, Z0. rewrite P1, Z.add_0_r in D.
    destruct (Hn eq_refl) as (-> & -> & -> & ->).
    cbn [firstn app] in Z0. rewrite app_nil_r in Z0.
    split; [exact R0|]. split; [exact Hk'|]. split; [exact Hpend'|].
    split; [rewrite He, firstn_all2 by lia; exact Z0|].
    split; [intros Hlk; lia|]. split; [intros _; exact D|]. split; [exact Hfr|]. split; [exact Hpr | exact Hwp].
Qed.

End W.

About link_amwrite_gen.
Print Assumptions link_amwrite_gen.
About link_amwrite_flush.
Print Assumptions link_amwrite_flush.
