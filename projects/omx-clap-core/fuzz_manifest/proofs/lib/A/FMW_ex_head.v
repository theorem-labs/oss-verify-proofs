(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACer.v, with its module paths and module names changed; 1338 of its 1373 lines of code are new or changed and 261 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_K.v, with its module names changed; 259 of its 330 lines of code are new or changed and 1302 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_strkit.v, with its module paths and module names changed; 240 of its 267 lines of code are new or changed and 303 lines of the source are left out. *)
(* G4.ExHead: ex_seg_head (FMW_ex_base.v:183), the scan head of expected 0x81260 (fuzz_manifest.c:134-142) on fm.asan.
   From EX_L at index i: s4 = text + i, the instrumented load of text[i]; '@' -> strncmp (text + i + 1, "prefix", 6)
   (FMH_Rt.v astrncmp_realizes) -> 0: EX_P with a1 = 7; text[i] = NUL -> EX_R (i = |t|, the scan's answer 0);
   otherwise the inlined ex_prefix_word loop from EX_W (FMW_ex_head_w.v hd_W), which ends at EX_CONT -> EX_L (i + 1)
   or EX_TL (FMW_ex_head_t.v hd_T). The cut states are FMW_ex_head_d.v's; entries FMW_ex_head_e.v, exits
   FMW_ex_head_x.v, model facts FMW_ex_head_m.v. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YFen YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC20 YI16 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v ACeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMPstat FMH_Base FMH_Rt FMH_Fn FMW_lib FMW_ex_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_ex_head_d.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_ex_head_m FMW_ex_head_e FMW_ex_head_x FMW_ex_head_w.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ---- a suffix of a C string (copied from G5's lib/A/FMW_kitS.v cstr_ok_suffix, shadow_hull_vis_sub) ---- *)
Lemma hd_hull_sub : forall rd x n x' n',
  shadow_hull_vis rd x n -> x <= x' -> x' + n' <= x + n -> 0 < n' -> shadow_hull_vis rd x' n'.
Proof.
intros rd x n x' n' H H1 H2 H3 s Hs. apply H. unfold shadow_addr, SHADOW_OFF in *.
assert (M1 : (2147450880 + x / 8) / 8 <= (2147450880 + x' / 8) / 8)
  by (apply Z.div_le_mono; [lia|]; pose proof (Z.div_le_mono x x' 8 ltac:(lia) H1); lia).
assert (M2 : (2147450880 + (x' + n' - 1) / 8) / 8 <= (2147450880 + (x + n - 1) / 8) / 8)
  by (apply Z.div_le_mono; [lia|]; pose proof (Z.div_le_mono (x' + n' - 1) (x + n - 1) 8 ltac:(lia) ltac:(lia)); lia).
lia.
Qed.
Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma hd_cstr_ok_suffix : forall (W : world tfibsegs) mem p0 l0 k, (k <= length l0)%nat ->
  cstr_ok tfibsegs W mem p0 l0 -> cstr_ok tfibsegs W mem (p0 + Z.of_nat k) (skipn k l0).
Proof.
intros W mem p0 l0 k Hk ((Hg & Hnz) & H4096 & Hcl & H32 & Ham & Hra & Hhv & Htl).
assert (Hlen : Z.of_nat (length (skipn k l0)) = Z.of_nat (length l0) - Z.of_nat k) by (rewrite length_skipn; lia).
assert (Eend : p0 + Z.of_nat k + Z.of_nat (length (skipn k l0)) = p0 + Z.of_nat (length l0)) by lia.
split; [split|].
- rewrite <- (firstn_skipn k l0) in Hg. rewrite <- app_assoc in Hg. apply (garr8_app tfibsegs) in Hg as [_ Hg].
  rewrite length_firstn in Hg. replace (Nat.min k (length l0)) with k in Hg by lia. exact Hg.
- rewrite <- (firstn_skipn k l0) in Hnz. apply Forall_app in Hnz as [_ Hnz]. exact Hnz.
- split; [lia|]. split; [lia|]. split; [lia|]. split; [unfold amem_range in *; lia|].
  split; [intros x Hx; apply Hra; lia|].
  split; [apply (hd_hull_sub _ p0 (Z.of_nat (length l0) + 1)); [exact Hhv | lia | lia | lia]|].
  intros a Ha. rewrite Eend in Ha. exact (Htl a Ha).
Qed.
End k.

(* ---- walk tactics (after FMW_plain.v pl_av / pl_mk / pl_g, fw_reg) ---- *)
Ltac hd_reg HS r :=
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    rewrite (st_ok_restrict_reg segs H E ss ms r HS); change (sr_get (ss_regs ss) r) with e end.
Ltac hd_av W mem1 :=
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) |- _ =>
    let AVn := fresh "AVn" in
    pose proof (fw_nowin tfibsegs _ _ _ _ _ HFr ltac:(vm_compute; reflexivity)) as AVn;
    lazymatch goal with AV : forall a, _ -> aview _ _ m0 a = aview _ _ mem1 a |- _ =>
      let AV2 := fresh "AV" in
      assert (AV2 : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W) m1 a = aview tfibsegs (w_H W) mem1 a)
        by (intros a Ha; rewrite (AVn a Ha); exact (AV a Ha));
      clear AV AVn; rename AV2 into AV end end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
  repeat match goal with H : context [with_vm_backing (m_vm_lazy (with_vm_backing _ _ _)) _ _] |- _ =>
    rewrite wvb_collapse in H end.
Ltac hd_mk HS := rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl);
  lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?x)] =>
    let v := eval vm_compute in (ss_pc x) in change (ss_pc x) with v end.
Ltac hd_g HS :=
  lazymatch goal with |- getr _ ?r = _ => hd_reg HS r end;
  cbn [sv_denot ew ewset Nat.eqb]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned.

Section H. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis IMG : fm_img_facts tfibsegs B.
Hypothesis STRNCMP : astrncmp_realizes tfibsegs B PC_strncmp.
Hypothesis SEG_R : ex_seg_R B.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

Theorem ex_seg_head_holds : ex_seg_head B.
Proof.
  intros cx i d f ly3 S3 W3 regs3 mem3 md3 LF SP HA.
  pose proof LAWS as HL. pose proof fmw_segs_low as Hsegs. pose proof fmw_wx as Hwx.
  destruct (hd_L_entry B cx i d f ly3 S3 W3 regs3 mem3 md3 HA) as [HS SHOK].
  pose proof HA as (HB & HC & HSL & HSR & HSC & R19 & R9 & R15 & R16).
  pose proof HB as ((HPRE & HRO0) & _).
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HSTK : STK_expected = 208 + 8224) by reflexivity.
  pose proof HC as (HJ & Hbl & HGL & Rsp & Rgp & Rtp & R25 & HSV & HRO & HCt & HCu & HKt & HKu).
  pose proof HSC as (Hi & Hd & Hf & Hu0 & Hres).
  pose proof HSR as (R23 & R22 & R18 & R8).
  pose proof HCt as ((HGa & HNZ) & H4096 & Hcl & H32 & Ham & HRA & HHV & HT).
  destruct (HGa i ltac:(rewrite length_app; cbn [length]; lia)) as [Vc Rc].
  remember (Ereg regs3 (hd_extraL (cx_t cx) (Z.of_nat i) (nth i (cx_tb cx ++ [0]) 0))) as E eqn:HE.
  assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr regs3 q)
    by (intros n q Hn; rewrite HE; apply ew_Ereg_nat; exact Hn).
  assert (E32 : ew E 32 = Z_to_bv 64 (cx_t cx + Z.of_nat i)) by (rewrite HE; exact (ew_Ereg_extra regs3 _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 (nth i (cx_tb cx ++ [0]) 0)) by (rewrite HE; exact (ew_Ereg_extra regs3 _ 1)).
  clear HE.
  set (t := cx_t cx) in *. set (tb := cx_tb cx) in *. set (c := nth i (tb ++ [0]) 0) in *.
  assert (Hsp0 : cx_F cx = cx_sp cx - 208) by reflexivity.
  assert (AV : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W3) mem3 a)
    by reflexivity.
  change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 EX_L) mem3 (seg_rom tfibsegs))) in HJ, SHOK.
  unfold cfg_at. change (w64 EX_L) with (Z_to_bv 64 EX_L).
  aj_run_tok EX_tbl_ok HS HJ SHOK HD_Bspan.
  { awr_ok_tac. }
  hd_av W3 mem3.
  srr_branch_tok EX_tbl_ok HS SHOK HD_Bspan.
  - (* text[i] = '@' *)
    rewrite branch_eq_U, (U_atom _ 33 c), U_SLit, zcanon_id in Hc
      by (first [cbn [ew ewset Nat.eqb]; exact E33 | lia | unfold M64; lia]).
    apply Z.eqb_eq in Hc.
    aj_run_tok EX_tbl_ok HS HJ SHOK HD_Bspan; [awr_ok_tac|]. hd_av W3 mem3.
    rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2. rreg HS (1%bv : bv 5) Rra.
    rreg HS (2%bv : bv 5) Rsp'. rreg HS (3%bv : bv 5) Rgp'. rreg HS (4%bv : bv 5) Rtp'.
    assert (Hit : (i < length tb)%nat).
    { destruct (Nat.eq_dec i (length tb)) as [->|]; [|lia]. unfold c in Hc. rewrite app_nth2, Nat.sub_diag in Hc by lia.
      cbn in Hc. lia. }
    assert (KL : fw_low tfibsegs (w_H W3) mem3 (ms_mem ms0)) by (intros a Ha; apply AV; lia).
    pose proof (fw_rodata_low tfibsegs B _ mem3 _ Hsegs KL HRO) as HRO1.
    pose proof (fw_cstr_low tfibsegs W3 mem3 _ t tb KL HCt) as HCt1.
    pose proof (hd_cstr_ok_suffix W3 (ms_mem ms0) t tb (S i) ltac:(lia) HCt1) as HCsuf.
    destruct (IMG ly3 S3 W3 (ms_mem ms0) _ (proj1 HJ) HRO1) as (HROM & HROMO & _ & HSTRS & _).
    pose proof (proj1 (proj1 (Forall_forall _ _) HSTRS (0x20d00, ManifestModel.prefix_lc)
      ltac:(unfold FM_RO_STRS; cbn [In]; right; left; reflexivity))) as HCpre.
    cbn [fst snd] in HCpre.
    assert (UF : bv_unsigned (ew E 2) = cx_F cx).
    { rewrite (EE 2%nat 2%bv eq_refl), Rsp. unfold w64. apply unsigned_lit_small. unfold cx_F, cx_sp in *. lia. }
    rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
    eapply SRr_bind.
    { eapply (aj_ro_at tfibsegs B HL Hsegs PC_strncmp STK_RT_STR
        (fun v => v = 0 <-> strn_eq (Z.to_nat 6) (skipn (S i) tb) ManifestModel.prefix_lc)
        W3 (ms_regs ms0) (ms_mem ms0) STK_expected (cx_sp cx) [] (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx)
        [] ly3 S3 _ 0 (-208) (Z_to_bv 64 0x81294) HJ).
      - unfold spZ. rewrite Rsp', UF. unfold cx_F. lia.
      - reflexivity.
      - lia.
      - unfold STK_RT_STR, ESTACK. lia.
      - unfold STK_RT_STR, ESTACK. rewrite HSTK. lia.
      - rewrite Rgp', (EE 3%nat 3%bv eq_refl), Rgp. exact Hgp.
      - rewrite Rtp', (EE 4%nat 4%bv eq_refl), Rtp. exact Htp.
      - exact Rra.
      - vm_compute. reflexivity.
      - intros HPK. apply (STRNCMP ly3 S3 W3 (ms_regs ms0) (ms_mem ms0) _ (t + Z.of_nat (S i)) EX_PREFIX 6
          (skipn (S i) tb) ManifestModel.prefix_lc HPK).
        + exact HROM.
        + exact HROMO.
        + rewrite Ra0, E32. unfold w64. f_equal. rewrite unsigned_lit_small by lia. lia.
        + rewrite Ra1. reflexivity.
        + rewrite Ra2. reflexivity.
        + lia.
        + exact HCsuf.
        + exact HCpre. }
    cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hvr & Hvl & Hfr2 & Hpres2).
    lazymatch type of HS with st_ok _ _ ?ss _ =>
      let K := eval vm_compute in (run_K 0 HD_Bx SH_L ss) in
      jafter_call_keep HS K regs2 (mrestrict (w_H W3) mem2) HP2 [0; 1]%nat HS2 end.
    match type of HS2 with ?tt -> _ => assert (HK : tt) end.
    { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
      - eapply (fw_region_kept tfibsegs _ (w_H W3) (ms_mem ms0) mem2 2 (cx_F cx));
          [cbn [ew ewset Nat.eqb]; exact UF | | exact Hpres2].
        intros a Ha. apply Hfr2; [unfold cx_F, cx_sp in *; lia | unfold STK_RT_STR, ESTACK, cx_F; lia].
      - eapply (fw_region_kept tfibsegs _ (w_H W3) (ms_mem ms0) mem2 32 (t + Z.of_nat i));
          [cbn [ew ewset Nat.eqb]; rewrite E32; apply unsigned_lit_small; lia | | exact Hpres2].
        intros a Ha. apply Hfr2; [lia | unfold STK_RT_STR, ESTACK, cx_F, cx_sp in *; lia]. }
    specialize (HS2 HK). clear HK HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
    rename AV into AV0.
    assert (KP : hd_keep cx W3 mem3 mem2).
    { intros a Ha Hn. rewrite (Hfr2 a Ha) by (intros X; apply Hn; unfold cx_F; exact X). apply AV0. exact Ha. }
    clear Hfr2 KL.
    lazymatch type of HS with st_ok _ (havoc ?E0 ?K ?l) _ _ =>
      set (E1 := havoc E0 K l) in *;
      assert (E1o : forall k, (k < K)%nat -> ew E1 k = ew E0 k) by (intros k Hk; apply ew_havoc_old; exact Hk);
      assert (E38 : ew E1 38 = Z_to_bv 64 v)
        by (change 38%nat with (K + 4)%nat; unfold E1; rewrite (ew_havoc_new E0 K _ 4 (Z_to_bv 64 0)) by (cbn; lia);
            exact Hv)
    end.
    clear SHOK.
    assert (SHOK : sh_ok tfibsegs HD_Bx [] E1
      (mrestrict (w_H W3) (ms_mem (mkst regs2 (Z_to_bv 64 529044) mem2 (seg_rom tfibsegs))))) by constructor.
    change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 529044) mem2 (seg_rom tfibsegs))) in HJ2.
    clear HJ. rename HJ2 into HJ.
    assert (AV : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) mem2 a = aview tfibsegs (w_H W3) mem2 a)
      by reflexivity.
    aj_run_tok EX_tbl_ok HS HJ SHOK HD_Bspan; [awr_ok_tac|]. hd_av W3 mem2.
    assert (B64 : ManifestModel.byte_at tb i = 64).
    { rewrite <- (proj2 (hd_m_byte tb i Hi HNZ) Hit). exact Hc. }
    srr_branch_tok EX_tbl_ok HS SHOK HD_Bspan.
    + rewrite branch_eq_U, (U_atom _ 38 v), U_SLit in Hc0 by (first [cbn [ew ewset Nat.eqb]; exact E38 | lia]).
      change (zcanon 0) with 0 in Hc0. apply Z.eqb_eq in Hc0.
      assert (HA1 : hd_arm1 tb i = true).
      { unfold hd_arm1. rewrite B64, Z.eqb_refl. cbn [andb]. apply hd_m_strn. apply Hvl. exact Hc0. }
      aj_run_to_tok EX_tbl_ok HS HJ SHOK HD_Bspan EX_P; [awr_ok_tac|]. hd_av W3 mem2.
      hd_mk HS.
      eapply (hd_exit_P B cx i d f 7 ly3 S3 W3 regs3 mem3 md3 _ _ _ LF SP HA Hit (hd_m_head7 tb i HA1)
        ltac:(right; reflexivity) HJ).
      * intros a Ha Hn. rewrite (AV a Ha). exact (KP a Ha Hn).
      * repeat split; hd_g HS; first [rewrite E1o by lia; cbn [ew ewset Nat.eqb]; apply EE; reflexivity
          | rewrite R22; reflexivity | rewrite R18; reflexivity | rewrite R8; reflexivity].
      * hd_g HS. rewrite E1o by lia. cbn [ew ewset Nat.eqb]. apply EE. reflexivity.
      * repeat split; hd_g HS; reflexivity.
      * hd_g HS. rewrite E1o by lia. cbn [ew ewset Nat.eqb]. exact E32.
      * hd_g HS. reflexivity.
    + rewrite branch_eq_U, (U_atom _ 38 v), U_SLit in Hc0 by (first [cbn [ew ewset Nat.eqb]; exact E38 | lia]).
      change (zcanon 0) with 0 in Hc0. apply Z.eqb_neq in Hc0.
      assert (HA1 : hd_arm1 tb i = false).
      { unfold hd_arm1. apply andb_false_intro2. destruct (ManifestModel.zl_eqb _ _) eqn:Ez; [|reflexivity].
        exfalso. apply Hc0. apply Hvl. apply hd_m_strn. exact Ez. }
      aj_run_to_tok EX_tbl_ok HS HJ SHOK HD_Bspan EX_W; [awr_ok_tac|]. hd_av W3 mem2.
      hd_mk HS.
      eapply (hd_W B IMG 0 cx i d f ly3 S3 W3 _ _ _ LF SP).
      * eapply (hd_at_step B cx i d f ly3 S3 W3 regs3 mem3 md3 _ _ _ HA HJ).
        -- intros a Ha Hn. rewrite (AV a Ha). exact (KP a Ha Hn).
        -- repeat split; hd_g HS; first [rewrite E1o by lia; cbn [ew ewset Nat.eqb]; apply EE; reflexivity
             | rewrite R22; reflexivity | rewrite R18; reflexivity | rewrite R8; reflexivity].
        -- hd_g HS. rewrite E1o by lia. cbn [ew ewset Nat.eqb]. apply EE. reflexivity.
        -- repeat split; hd_g HS; reflexivity.
      * hd_g HS. rewrite E1o by lia. cbn [ew ewset Nat.eqb]. exact E32.
      * hd_g HS. reflexivity.
      * lia.
      * exact Hit.
      * revert Hit. unfold tb. lia.
      * exact HA1.
      * reflexivity.
  - (* text[i] <> '@' *)
    rewrite branch_eq_U, (U_atom _ 33 c), U_SLit, zcanon_id in Hc
      by (first [cbn [ew ewset Nat.eqb]; exact E33 | lia | unfold M64; lia]).
    apply Z.eqb_neq in Hc.
    aj_run_tok EX_tbl_ok HS HJ SHOK HD_Bspan; [awr_ok_tac|]. hd_av W3 mem3.
    srr_branch_tok EX_tbl_ok HS SHOK HD_Bspan.
    + rewrite branch_eq_U, (U_atom _ 33 c), U_SLit in Hc0 by (first [cbn [ew ewset Nat.eqb]; exact E33 | lia]).
      change (zcanon 0) with 0 in Hc0. apply Z.eqb_eq in Hc0.
      assert (Hie : i = length tb) by (apply (proj1 (hd_m_byte tb i Hi HNZ)); exact Hc0).
      aj_run_to_tok EX_tbl_ok HS HJ SHOK HD_Bspan EX_R; [awr_ok_tac|]. hd_av W3 mem3.
      hd_mk HS.
      eapply (hd_exit_R B cx i d f ly3 S3 W3 regs3 mem3 md3 _ _ _ SEG_R HA HJ).
      * intros a Ha Hn. exact (AV a Ha).
      * repeat split; hd_g HS; first [cbn [ew ewset Nat.eqb]; apply EE; reflexivity
          | rewrite R22; reflexivity | rewrite R18; reflexivity | rewrite R8; reflexivity].
      * hd_g HS. cbn [ew ewset Nat.eqb]. rewrite E33, Hc0, (hd_m_res_end cx i d f HSC Hie). reflexivity.
    + rewrite branch_eq_U, (U_atom _ 33 c), U_SLit in Hc0 by (first [cbn [ew ewset Nat.eqb]; exact E33 | lia]).
      change (zcanon 0) with 0 in Hc0. apply Z.eqb_neq in Hc0.
      assert (Hit : (i < length tb)%nat).
      { destruct (Nat.eq_dec i (length tb)) as [He|]; [|lia]. exfalso. apply Hc0.
        apply (proj2 (proj1 (hd_m_byte tb i Hi HNZ))). exact He. }
      assert (HA1 : hd_arm1 tb i = false).
      { unfold hd_arm1. rewrite <- (proj2 (hd_m_byte tb i Hi HNZ) Hit). fold c.
        apply Z.eqb_neq in Hc. rewrite Hc. reflexivity. }
      aj_run_to_tok EX_tbl_ok HS HJ SHOK HD_Bspan EX_W; [awr_ok_tac|]. hd_av W3 mem3.
      hd_mk HS.
      eapply (hd_W B IMG 0 cx i d f ly3 S3 W3 _ _ _ LF SP).
      * eapply (hd_at_step B cx i d f ly3 S3 W3 regs3 mem3 md3 _ _ _ HA HJ).
        -- intros a Ha Hn. exact (AV a Ha).
        -- repeat split; hd_g HS; first [cbn [ew ewset Nat.eqb]; apply EE; reflexivity
             | rewrite R22; reflexivity | rewrite R18; reflexivity | rewrite R8; reflexivity].
        -- hd_g HS. cbn [ew ewset Nat.eqb]. apply EE. reflexivity.
        -- repeat split; hd_g HS; reflexivity.
      * hd_g HS. cbn [ew ewset Nat.eqb]. exact E32.
      * hd_g HS. reflexivity.
      * lia.
      * exact Hit.
      * revert Hit. unfold tb. lia.
      * exact HA1.
      * reflexivity.
Qed.
End H.

Print Assumptions ex_seg_head_holds.
