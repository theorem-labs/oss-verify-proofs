(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 848 of its 931 lines of code are new or changed and 1841 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/A/FMW_hp_kit.v, with its module paths and module names changed; 213 of its 250 lines of code are new or changed and 894 lines of the source are left out. *)
(* G4.ExHead, IMAGE B: ex_seg_head (lib/B/FMW_ex_base.v:197), the scan head of expected 0x813c0 (fuzz_manifest.c:134-142)
   on fm.asan-ubsan (pin ca61e5c9eabc0050).
   From EX_L at index i (s7 = i, s5 = text + i): the instrumented load of text[i] at s5; '@' (0x813d8) -> the UBSan guard
   0x813e4 `beq s5, s0` (s5 + 1 wraps), strncmp (s5 + 1, "prefix", 6) (FMH_Rt.v astrncmp_realizes; 0x813f4), the caller-
   saved constants re-made (0x813f8..0x81404) -> 0: the guard 0x814c4 `bltu -8, s5`, EX_P with a0 = 7;
   text[i] = NUL (0x813dc) -> 0x81900 s7 = 0, a0 = s7, EX_R (i = |t|, the scan's answer 0); otherwise the inlined
   ex_prefix_word loop from EX_W (FMW_ex_head_w.v hd_W), which ends at EX_NEXT -> EX_L (i + 1) or EX_TL
   (FMW_ex_head_t.v hd_T). The cut states are FMW_ex_head_d.v's; entries FMW_ex_head_e.v, exits FMW_ex_head_x.v,
   model facts FMW_ex_head_m.v.
   UBSan guards (a Theorem Labs lane's FM-B-TRAPS.md rows 30-34, 40; trap 0x8194c) on the head's paths, each decided not taken
   (0x816a0: taken, its fall-through is the trap) by the cut states' interval facts: 0x813e4, 0x81414, 0x8148c, 0x814b4,
   0x814c4, 0x816a0.
   Shape after image A's lib/A/FMW_ex_head.v (06d82004dc3). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v YCeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMPstat FMH_Base FMH_Rt FMH_Fn FMW_lib FMTrapB.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_ex_base FMW_ex_head_d.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_ex_head_m FMW_ex_head_e FMW_ex_head_x FMW_ex_head_w.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
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

(* the strncmp result's branch 0x81408 `beqz a0` on the returned atom (Ev : ew _ n = v) *)
Ltac hd_Uv Hc Ev :=
  lazymatch type of Ev with ew _ ?n = Z_to_bv 64 ?v =>
    rewrite branch_eq_U, (U_atom _ n v), U_SLit in Hc by (first [cbn [ew ewset Nat.eqb]; exact Ev | lia]) end.

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
  pose proof HA as (HB & HC & HSL & HSR & HCR & HSC & R23 & R21).
  pose proof HB as ((HPRE & HRO0) & _).
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HSTK : STK_expected = 240 + 8224) by reflexivity.
  pose proof HC as (HJ & Hbl & HGL & Rsp & Rgp & Rtp & R25 & HSV & HRO & HCt & HCu & HKt & HKu).
  pose proof HSC as (Hi & Hd & Hf & Hu0 & Hres).
  pose proof HCR as (R16 & R17 & R5 & R6).
  pose proof HCt as ((HGa & HNZ) & H4096 & Hcl & H32 & Ham & HRA & HHV & HT).
  destruct (HGa i ltac:(rewrite length_app; cbn [length]; lia)) as [Vc Rc].
  remember (Ereg regs3 (hd_extraL (nth i (cx_tb cx ++ [0]) 0))) as E eqn:HE.
  assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr regs3 q)
    by (intros n q Hn; rewrite HE; apply ew_Ereg_nat; exact Hn).
  assert (E32 : ew E 32 = Z_to_bv 64 (nth i (cx_tb cx ++ [0]) 0)) by (rewrite HE; exact (ew_Ereg_extra regs3 _ 0)).
  clear HE.
  assert (E21 : ew E 21 = Z_to_bv 64 (cx_t cx + Z.of_nat i)) by (rewrite (EE 21%nat 21%bv eq_refl); exact R21).
  set (t := cx_t cx) in *. set (tb := cx_tb cx) in *. set (c := nth i (tb ++ [0]) 0) in *.
  assert (Hsp0 : cx_F cx = cx_sp cx - 240) by reflexivity.
  assert (AV : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W3) mem3 a)
    by reflexivity.
  change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 EX_L) mem3 (seg_rom tfibsegs))) in HJ, SHOK.
  unfold cfg_at. change (w64 EX_L) with (Z_to_bv 64 EX_L).
  aj_run_tok EX_tbl_ok HS HJ SHOK HD_Bspan.
  { awr_ok_tac. }
  hd_av W3 mem3.
  (* 0x813d8 beq a0, '@' *)
  srr_branch_tok EX_tbl_ok HS SHOK HD_Bspan.
  - (* text[i] = '@' *)
    rewrite branch_eq_U, (U_atom _ 32 c), U_SLit, zcanon_id in Hc
      by (first [cbn [ew ewset Nat.eqb]; exact E32 | lia | unfold M64; lia]).
    apply Z.eqb_eq in Hc.
    (* the guard 0x813e4 (decided), the call strncmp at 0x813f4 *)
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
        [] ly3 S3 _ 0 (-240) (Z_to_bv 64 0x813f8) HJ).
      - unfold spZ. rewrite Rsp'. cbn [ew ewset Nat.eqb]. rewrite UF. unfold cx_F. lia.
      - reflexivity.
      - lia.
      - unfold STK_RT_STR, ESTACK. lia.
      - unfold STK_RT_STR, ESTACK. rewrite HSTK. lia.
      - rewrite Rgp'. cbn [ew ewset Nat.eqb]. rewrite (EE 3%nat 3%bv eq_refl), Rgp. exact Hgp.
      - rewrite Rtp'. cbn [ew ewset Nat.eqb]. rewrite (EE 4%nat 4%bv eq_refl), Rtp. exact Htp.
      - exact Rra.
      - vm_compute. reflexivity.
      - intros HPK. apply (STRNCMP ly3 S3 W3 (ms_regs ms0) (ms_mem ms0) _ (t + Z.of_nat (S i)) EX_PREFIX 6
          (skipn (S i) tb) ManifestModel.prefix_lc HPK).
        + exact HROM.
        + exact HROMO.
        + rewrite Ra0. cbn [ew ewset Nat.eqb]. rewrite E21. unfold w64. f_equal.
          rewrite unsigned_lit_small by lia. lia.
        + rewrite Ra1. reflexivity.
        + rewrite Ra2. reflexivity.
        + lia.
        + exact HCsuf.
        + exact HCpre. }
    cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hvr & Hvl & Hfr2 & Hpres2).
    lazymatch type of HS with st_ok _ _ ?ss _ =>
      let K := eval vm_compute in (run_K 0 HD_Bx SH_L ss) in
      jafter_call_keep HS K regs2 (mrestrict (w_H W3) mem2) HP2 [0]%nat HS2 end.
    match type of HS2 with ?tt -> _ => assert (HK : tt) end.
    { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
      eapply (fw_region_kept tfibsegs _ (w_H W3) (ms_mem ms0) mem2 2 (cx_F cx));
        [cbn [ew ewset Nat.eqb]; exact UF | | exact Hpres2].
      intros a Ha. apply Hfr2; [unfold cx_F, cx_sp in *; lia | unfold STK_RT_STR, ESTACK, cx_F; lia]. }
    specialize (HS2 HK). clear HK HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
    rename AV into AV0.
    assert (KP : hd_keep cx W3 mem3 mem2).
    { intros a Ha Hn. rewrite (Hfr2 a Ha) by (intros X; apply Hn; unfold cx_F; exact X). apply AV0. exact Ha. }
    clear Hfr2 KL.
    lazymatch type of HS with st_ok _ (havoc ?E0 ?K ?l) _ _ =>
      set (E1 := havoc E0 K l) in *;
      assert (E1o : forall k, (k < K)%nat -> ew E1 k = ew E0 k) by (intros k Hk; apply ew_havoc_old; exact Hk);
      let n := eval vm_compute in (K + 4)%nat in
      assert (Ev : ew E1 n = Z_to_bv 64 v)
        by (change n with (K + 4)%nat; unfold E1; rewrite (ew_havoc_new E0 K _ 4 (Z_to_bv 64 0)) by (cbn; lia);
            exact Hv)
    end.
    clear SHOK.
    assert (SHOK : sh_ok tfibsegs HD_Bx [] E1
      (mrestrict (w_H W3) (ms_mem (mkst regs2 (Z_to_bv 64 529400) mem2 (seg_rom tfibsegs))))) by constructor.
    change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 529400) mem2 (seg_rom tfibsegs))) in HJ2.
    clear HJ. rename HJ2 into HJ.
    assert (AV : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) mem2 a = aview tfibsegs (w_H W3) mem2 a)
      by reflexivity.
    (* 0x813f8..0x81404 re-make t1, t0, a7, a6; 0x81408 beqz a0 *)
    aj_run_tok EX_tbl_ok HS HJ SHOK HD_Bspan; [awr_ok_tac|]. hd_av W3 mem2.
    assert (B64 : ManifestModel.byte_at tb i = 64).
    { rewrite <- (proj2 (hd_m_byte tb i Hi HNZ) Hit). exact Hc. }
    srr_branch_tok EX_tbl_ok HS SHOK HD_Bspan.
    + (* strncmp = 0: '@prefix', the guard 0x814c4 (decided), EX_P with a0 = 7 *)
      hd_Uv Hc0 Ev. change (zcanon 0) with 0 in Hc0. apply Z.eqb_eq in Hc0.
      assert (HA1 : hd_arm1 tb i = true).
      { unfold hd_arm1. rewrite B64, Z.eqb_refl. cbn [andb]. apply hd_m_strn. apply Hvl. exact Hc0. }
      aj_run_to_tok EX_tbl_ok HS HJ SHOK HD_Bspan EX_P; [awr_ok_tac|]. hd_av W3 mem2.
      hd_mk HS.
      eapply (hd_exit_P B cx i d f 7 ly3 S3 W3 regs3 mem3 md3 _ _ _ LF SP HA Hit (hd_m_head7 tb i HA1)
        ltac:(right; reflexivity) HJ).
      * intros a Ha Hn. rewrite (AV a Ha). exact (KP a Ha Hn).
      * repeat split; hd_g HS; rewrite E1o by lia; cbn [ew ewset Nat.eqb]; apply EE; reflexivity.
      * repeat split; hd_g HS; reflexivity.
      * hd_g HS. reflexivity.
    + (* strncmp <> 0: the word loop from EX_W with k = 0 *)
      hd_Uv Hc0 Ev. change (zcanon 0) with 0 in Hc0. apply Z.eqb_neq in Hc0.
      assert (HA1 : hd_arm1 tb i = false).
      { unfold hd_arm1. apply andb_false_intro2. destruct (ManifestModel.zl_eqb _ _) eqn:Ez; [|reflexivity].
        exfalso. apply Hc0. apply Hvl. apply hd_m_strn. exact Ez. }
      aj_run_to_tok EX_tbl_ok HS HJ SHOK HD_Bspan EX_W; [awr_ok_tac|]. hd_av W3 mem2.
      hd_mk HS.
      eapply (hd_W B IMG 0 cx i d f ly3 S3 W3 _ _ _ LF SP).
      * eapply (hd_at_step B cx i d f ly3 S3 W3 regs3 mem3 md3 _ _ _ HA HJ).
        -- intros a Ha Hn. rewrite (AV a Ha). exact (KP a Ha Hn).
        -- repeat split; hd_g HS; rewrite E1o by lia; cbn [ew ewset Nat.eqb]; apply EE; reflexivity.
        -- repeat split; hd_g HS; reflexivity.
      * hd_g HS. reflexivity.
      * lazymatch goal with |- getr _ ?r = _ => hd_reg HS r end. unfold w64. apply fw_sv_U.
        rewrite U_not, (U_atom _ 21 (t + Z.of_nat i))
          by (first [rewrite E1o by lia; cbn [ew ewset Nat.eqb]; exact E21 | cbn [ew ewset Nat.eqb]; exact E21 | lia]).
        lia.
      * lia.
      * exact Hit.
      * revert Hit. unfold tb. lia.
      * exact HA1.
      * reflexivity.
  - (* text[i] <> '@' *)
    rewrite branch_eq_U, (U_atom _ 32 c), U_SLit, zcanon_id in Hc
      by (first [cbn [ew ewset Nat.eqb]; exact E32 | lia | unfold M64; lia]).
    apply Z.eqb_neq in Hc.
    aj_run_tok EX_tbl_ok HS HJ SHOK HD_Bspan; [awr_ok_tac|]. hd_av W3 mem3.
    (* 0x813dc beqz a0 *)
    srr_branch_tok EX_tbl_ok HS SHOK HD_Bspan.
    + (* NUL: 0x81900 s7 = 0, a0 = s7, EX_R *)
      rewrite branch_eq_U, (U_atom _ 32 c), U_SLit in Hc0 by (first [cbn [ew ewset Nat.eqb]; exact E32 | lia]).
      change (zcanon 0) with 0 in Hc0. apply Z.eqb_eq in Hc0.
      assert (Hie : i = length tb) by (apply (proj1 (hd_m_byte tb i Hi HNZ)); exact Hc0).
      aj_run_to_tok EX_tbl_ok HS HJ SHOK HD_Bspan EX_R; [awr_ok_tac|]. hd_av W3 mem3.
      hd_mk HS.
      eapply (hd_exit_R B cx i d f ly3 S3 W3 regs3 mem3 md3 _ _ _ SEG_R HA HJ).
      * intros a Ha Hn. exact (AV a Ha).
      * hd_g HS. apply EE. reflexivity.
      * hd_g HS. apply EE. reflexivity.
      * hd_g HS. apply EE. reflexivity.
      * hd_g HS. apply EE. reflexivity.
      * hd_g HS. rewrite (hd_m_res_end cx i d f HSC Hie). reflexivity.
    + (* the word loop from EX_W with k = 0 *)
      rewrite branch_eq_U, (U_atom _ 32 c), U_SLit in Hc0 by (first [cbn [ew ewset Nat.eqb]; exact E32 | lia]).
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
        -- repeat split; hd_g HS; apply EE; reflexivity.
        -- repeat split; hd_g HS; reflexivity.
      * hd_g HS. reflexivity.
      * lazymatch goal with |- getr _ ?r = _ => hd_reg HS r end. unfold w64. apply fw_sv_U.
        rewrite U_not, (U_atom _ 21 (t + Z.of_nat i)) by (first [cbn [ew ewset Nat.eqb]; exact E21 | lia]).
        lia.
      * lia.
      * exact Hit.
      * revert Hit. unfold tb. lia.
      * exact HA1.
      * reflexivity.
Qed.
End H.

Print Assumptions ex_seg_head_holds.
