(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec FxLin FxCore FxSubst FxSound FxMem FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv FxEnt FxRgs FxFacts FxPlan FxFrame FxWork FxWorkX.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWork OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWorkX.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Mem Cells Exec Frame Arr Step Image RegsEquiv MState.
From OSSVerify.Proofs.fast_float.from_chars.lib.KX Require Import KxBridge KxRun.
From OSSVerify.Proofs.fast_float.from_chars.lib.HX Require Import HxGen.
From OSSVerify.Proofs.fast_float.from_chars.lib.HXH Require Import HxBaseH.
From OSSVerify.Proofs.fast_float.from_chars.lib.HXHB Require Import HxPay HxFmtW.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Notation ASEGS := AsanUbsan.M.loaded_segments.
Definition FMT_KEYS : list Z := [22].
(* [comment removed for export] *)
Definition fmt_idx (L : sst) : option lin := ldivz (lsub (rgl L 10) (lconst 0x259a0)) 8.
Definition ro_cover (R : region) : bool :=
  match rg_kind R, is_const (rg_base R), is_const (rg_size R) with
  | RO, Some b, Some z => (Z.leb b 0x259a0 && Z.leb 0x259b8 (b + z))%bool
  | _, _, _ => false
  end.
Definition fmt_chk (L : sst) : bool :=
  match s_resv L, fmt_idx L with
  | RNone, Some x => (lin_eqb (rgl L 10) (laddc (lscale 8 x) 0x259a0) &&
                      (let '(lo, hi) := irange (s_facts L) x in Z.leb 0 lo && Z.leb hi 2) && existsb ro_cover (s_rgs L))%bool
  | _, _ => false
  end.
Definition fmt_newf (L : sst) : list fact :=
  [FRange (lvar (fv (s_next L) 0)) 1 5; FBits (lvar (fv (s_next L) 0)) 18446744073709551610 0].
Definition H_FMT : sst -> option sst := hpost 0x9021c 0x90220 FMT_KEYS fmt_chk fmt_newf.

Lemma af_table_facts : forall k, 0 <= k <= 2 -> 1 <= af_table k <= 5 /\ Z.land (af_table k) 18446744073709551610 = 0.
Proof. intros k Hk. assert (H4 : k = 0 \/ k = 1 \/ k = 2) by lia. destruct H4 as [ -> | [ -> | -> ] ]; cbn; split; (lia || reflexivity). Qed.

Theorem fmt_kit : hx_kit ASEGS xok0 0x9021c 0x90220 FMT_KEYS fmt_chk fmt_newf (fun _ => []).
Proof.
  intros L XL E ms m0 Hpc Hchk Hw Hd HxF Hm0.
  unfold fmt_chk in Hchk. destruct (s_resv L) eqn:Hrv; try discriminate. destruct (fmt_idx L) as [x|] eqn:Hx; [|discriminate].
  destruct (irange (s_facts L) x) as [lo hi] eqn:Hir.
  apply andb_prop in Hchk as [Hchk Hro]. apply andb_prop in Hchk as [Hlin Hrg]. apply lin_eqb_eq in Hlin.
  apply andb_prop in Hrg as [Hlo Hhi]. apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
  destruct (sden_0 _ _ _ _ Hd) as (Hpc0 & Hsvc0 & Hresv0 & HR & HG & HD & HF & Hfrm).
  rewrite Hrv in Hresv0. cbn [rsv_ok] in Hresv0.
  pose proof (irange_sound E (s_facts L) x HF) as Ix. rewrite Hir in Ix. cbn [fst snd] in Ix.
  set (k := bv_unsigned (lden E x)) in *.
  assert (RG : forall r, getr (ms_regs ms) (Z_to_bv 5 r) = lden E (rgl L r)) by (intros r; rewrite (HR _); reflexivity).
  assert (R10 : getr (ms_regs ms) 10%bv = Z_to_bv 64 (0x259a0 + 8 * k)).
  { transitivity (lden E (rgl L 10)); [exact (RG 10)|]. rewrite Hlin, lden_laddc, lden_lscale.
    apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616.
    rewrite (Z.mod_small (8 * k)) by lia. f_equal. lia. }
  assert (PR : pristine (ms_mem ms) 0x259a0 0x259b8).
  { apply existsb_exists in Hro as (Rr & HRin & Hcov). unfold ro_cover in Hcov.
    destruct (rg_kind Rr) eqn:Hk; try discriminate.
    destruct (is_const (rg_base Rr)) as [b|] eqn:Hb; [|discriminate]. destruct (is_const (rg_size Rr)) as [z|] eqn:Hz; [|discriminate].
    apply andb_prop in Hcov as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2.
    rewrite Forall_forall in HG. pose proof (HG Rr HRin) as (_ & Hflat & Hall & _).
    assert (Eb : bv_unsigned (lden E (rg_base Rr)) = b) by exact (is_const_u E _ b Hb).
    assert (Ez : rsz E Rr = z) by (unfold rsz; exact (is_const_u E _ z Hz)).
    rewrite Eb in Hflat, Hall. rewrite Ez in Hflat, Hall.
    split; [lia|]. split; [lia|]. intros j Hj. specialize (Hall (j - b) ltac:(lia)). rewrite Hk in Hall.
    destruct Hall as [Hm _]. replace (b + (j - b)) with j in Hm by lia. exact Hm. }
  set (R := ms_regs ms) in *.
  assert (HK : evt ASEGS (fmt_post (getr R 1) (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 6) (getr R 7) (getr R 8) (getr R 9)
                 (getr R 11) (getr R 12) (getr R 13) (getr R 14) (getr R 15) (getr R 16) (getr R 17) (getr R 18) (getr R 19) (getr R 20)
                 (getr R 21) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) (getr R 28) (getr R 29) (getr R 30)
                 (getr R 31) (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) k)
             (kms ASEGS ms)).
  { unfold kms, mkR_of. fold R. rewrite Hpc0, Hresv0, R10, Hpc.
    exact (blockFMT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ms) k ltac:(lia) PR _). }
  destruct (kit_run ASEGS _ ms Hsvc0 HK) as (ms1 & ms2 & Hst & Heq & Hpost). clear HK.
  unfold fmt_post in Hpost. subst ms2.
  destruct Heq as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
  cbn [with_rom MS ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in E1, E2, E3, E4, E5, E6, E7, E8.
  exists ms1, [Z_to_bv 64 (af_table k)].
  split; [exact Hst|]. split; [reflexivity|]. split; [exact E7|]. split; [exact E6|]. split; [rewrite E5, Hresv0; reflexivity|].
  split; [exact E4|]. split; [exact E3|].
  split; [|split; [|split]].
  - intros r Hr. rewrite (E1 r). destruct (reg_of_nat r) as (n & -> & Hn). rewrite getr_mkR. rewrite u5 by lia. rewrite Nat2Z.id.
    unfold FMT_KEYS in Hr. cbn [In] in Hr. rewrite u5 in Hr by lia.
    do 32 (destruct n as [|n]; [cbn; first [reflexivity | (symmetry; exact R10) | (exfalso; apply Hr; repeat (first [left; reflexivity | right]))]|]).
    lia.
  - intros i0 kk v Hi Hv. rewrite (E1 _).
    destruct i0 as [|i0]; cbn in Hi, Hv; [injection Hi as <-; injection Hv as <-; reflexivity | destruct i0; discriminate].
  - unfold fmt_newf. pose proof (af_table_facts k ltac:(lia)) as (AF1 & AF2).
    assert (Hv0 : E_of FMT_KEYS [Z_to_bv 64 (af_table k)] (s_next L) E (fv (s_next L) 0) = Z_to_bv 64 (af_table k))
      by exact (E_of_nth FMT_KEYS [Z_to_bv 64 (af_table k)] (s_next L) E 0 _ eq_refl eq_refl).
    constructor; [|constructor; [|constructor]]; cbn [fact_ok]; rewrite lden_lvar, Hv0; rewrite unsigned_lit by lia.
    + lia.
    + exact AF2.
  - constructor.
Qed.

Theorem H_FMT_ok : forall S K, H_FMT S = Some K ->
  hcall_rule ASEGS S K /\ (s_next S <= s_next K)%positive /\ shape (s_rgs K) = shape (s_rgs S).
Proof. exact (hpost_ok ASEGS _ _ _ _ _ fmt_kit). Qed.
