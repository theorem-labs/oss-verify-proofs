(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACer.v, with its module paths and module names changed; 1338 of its 1373 lines of code are new or changed and 261 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_K.v, with its module names changed; 259 of its 330 lines of code are new or changed and 1302 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_strkit.v, with its module paths and module names changed; 240 of its 267 lines of code are new or changed and 303 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/A/FMW_ex_head.v; 154 of its 201 lines of code are new or changed and 220 lines of the source are left out. *)
(* G4.ExHead.HeadTail: the head walk from EX_TL 0x81310 (ex_prefix_word matched all six letters, a1 = 6) to EX_P
   (i = 0, or text[i - 1] is a space) or through EX_CONT to EX_L at i + 1 (fuzz_manifest.c:141-142). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YFen.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC20 YI16 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v ACeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMPstat FMH_Base FMH_Rt FMH_Fn FMW_lib FMW_ex_base FMW_ex_head_d.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_ex_head_m FMW_ex_head_e FMW_ex_head_x.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* the walk tactics of FMW_plain.v (fw_reg, pl_av, pl_mk, pl_g), copied under the ht_ prefix *)
Ltac ht_reg HS r :=
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    rewrite (st_ok_restrict_reg segs H E ss ms r HS); change (sr_get (ss_regs ss) r) with e end.
Ltac ht_av W mem1 :=
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
Ltac ht_mk HS := rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl);
  lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?x)] =>
    let v := eval vm_compute in (ss_pc x) in change (ss_pc x) with v end.
Ltac ht_g HS :=
  lazymatch goal with |- getr _ ?r = _ => ht_reg HS r end;
  cbn [sv_denot ew ewset Nat.eqb]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned.
(* the head's exit register goals: the registers kept from the entry state regs1 (atoms or pinned literals) and the
   literal registers s1, a5, a6 *)
Ltac ht_kept HS EE regs1 :=
  unfold hd_kept_regs; repeat match goal with |- _ /\ _ => split end; ht_g HS;
  first [ apply EE; reflexivity
        | symmetry; lazymatch goal with H : getr regs1 ?r = _ |- getr regs1 ?r = _ => exact H end ].
Ltac ht_lits HS := unfold hd_lits; repeat match goal with |- _ /\ _ => split end; ht_g HS; reflexivity.
(* hd_T_byte (FMW_ex_head_e.v) on the state HS: add text[i - 1]'s byte region *)
Ltac ht_byte HS W p c E20 E32 VC :=
  lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msx) =>
    let HS2 := fresh "HS" in
    assert (HS2 : st_ok tfibsegs Ex (mkSS (ss_pc ssx) (ss_regs ssx) [hd_byteT] (ss_resv ssx) (ss_facts ssx))
      (restrict (w_H W) msx))
      by (refine (hd_T_byte Ex ssx _ p c HS _ _ _ _ _ _ _);
          [ vm_compute; reflexivity | vm_compute; reflexivity | cbn [ew ewset Nat.eqb]; exact E20
          | cbn [ew ewset Nat.eqb]; exact E32 | lia | lia | exact VC ]);
    clear HS; rename HS2 into HS end.

(* the ex_space branches of 0x81334 (bltu a0 - 9, s2 = 5) and 0x81338 (beq a0, s0 = ' ') on c = text[i - 1] (atom 32) *)
Section b. Context {fx : YK11.FPState}.
Lemma ht_ltu : forall E c, ew E 32 = Z_to_bv 64 c -> 0 <= c < 256 ->
  branch_taken BC_LTU (sv_denot E (SOff 32 (-9))) (sv_denot E (SLit 5)) = ((c - 9) mod 2 ^ 64 <? 5).
Proof.
  intros E c H Hc. rewrite branch_ltu_U, U_SOff, U_SLit, H, unsigned_lit_small by lia.
  unfold zcanon, M64. reflexivity.
Qed.
Lemma ht_eq32 : forall E c, ew E 32 = Z_to_bv 64 c -> 0 <= c < 256 ->
  branch_taken BC_EQ (sv_denot E (SOff 32 0)) (sv_denot E (SLit 32)) = (c =? 32).
Proof. intros E c H Hc. rewrite branch_eq_U, (U_atom E 32 c H), U_SLit by lia. reflexivity. Qed.
End b.
Ltac ht_dec HS Hc lem c E32 Rc :=
  lazymatch type of HS with st_ok _ ?Ex _ _ =>
    rewrite (lem Ex c ltac:(cbn [ew ewset Nat.eqb]; exact E32) Rc) in Hc end.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Lemma hd_T : forall cx i d f ly3 S3 W3 regs1 mem1 md1,
  ex_seg_L_from B cx i -> ex_seg_P B ->
  ex_at_L B cx i d f ly3 S3 W3 regs1 mem1 md1 ->
  getr regs1 20 = w64 (cx_t cx + Z.of_nat i) ->
  hd_arm1 (cx_tb cx) i = false ->
  ManifestModel.ci_eqb (firstn 6 (skipn i (cx_tb cx))) ManifestModel.prefix_lc = true ->
  SRr tfibsegs W3 (cfg_at tfibsegs EX_TL regs1 mem1 md1) (ex_post B cx).
Proof.
  intros cx i d f ly3 S3 W3 regs1 mem1 md1 HLF HP HAT R20 HA1 HCI.
  pose proof (AR_laws_ok tfibsegs B) as HL. pose proof fmw_segs_low as Hsegs. pose proof fmw_wx as Hwx.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (hd_m_ci6_len _ _ HCI) as H6.
  pose proof (hd_T_entry B cx i d f ly3 S3 W3 regs1 mem1 md1 HAT R20 H6) as HS.
  pose proof HAT as (HB & HC & HSL & HSR & HSC & R19 & R9 & R15 & R16).
  destruct HC as (HJ & Hbl & HGL & Rsp & Rgp & Rtp & R25 & HSV & HRO & HCt & HCu & HKt & HKu).
  destruct HSR as (R23 & R22 & R18 & R8).
  pose proof HCt as ((HGa & HNZ) & H4096 & Hcl & H32 & Ham & HRA & HHV & HT).
  remember (Ereg regs1 [Z_to_bv 64 (nth (pred i) (cx_tb cx) 0)]) as E eqn:HE.
  assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr regs1 q)
    by (intros n q Hn; rewrite HE; apply ew_Ereg_nat; exact Hn).
  assert (E32 : ew E 32 = Z_to_bv 64 (nth (pred i) (cx_tb cx) 0)) by (rewrite HE; exact (ew_Ereg_extra regs1 _ 0)).
  clear HE.
  assert (E19 : ew E 19 = Z_to_bv 64 (Z.of_nat i)) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
  assert (E20 : ew E 20 = Z_to_bv 64 (cx_t cx + Z.of_nat i)) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
  assert (E25 : ew E 25 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 25%nat 25%bv eq_refl); exact R25).
  assert (SHOK : sh_ok tfibsegs HD_Bx [] E
    (mrestrict (w_H W3) (ms_mem (mkst regs1 (Z_to_bv 64 EX_TL) mem1 (seg_rom tfibsegs))))) by constructor.
  assert (AV : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) mem1 a = aview tfibsegs (w_H W3) mem1 a)
    by reflexivity.
  change mem1 with (ms_mem (mkst regs1 (Z_to_bv 64 EX_TL) mem1 (seg_rom tfibsegs))) in HJ.
  unfold cfg_at. change (w64 EX_TL) with (Z_to_bv 64 EX_TL).
  aj_run_tok EX_tbl_ok HS HJ SHOK HD_Bspan.
  { awr_ok_tac. }
  ht_av W3 mem1.
  srr_branch_tok EX_tbl_ok HS SHOK HD_Bspan.
  - rewrite branch_eq_U, (U_atom _ 19 (Z.of_nat i)), U_SLit in Hc by (first [cbn [ew ewset Nat.eqb]; exact E19 | lia]).
    change (zcanon 0) with 0 in Hc. apply Z.eqb_eq in Hc.
    assert (Hi0 : i = 0%nat) by lia. clear Hc.
    aj_run_to_tok EX_tbl_ok HS HJ SHOK HD_Bspan EX_P; [awr_ok_tac|]. ht_av W3 mem1.
    ht_mk HS.
    refine (hd_exit_P B cx i d f 6 ly3 S3 W3 regs1 mem1 md1 _ _ _ HLF HP HAT ltac:(lia)
      (hd_m_some6 _ _ HA1 HCI (or_introl Hi0)) ltac:(lia) HJ _ _ _ _ _ _).
    + intros a Ha _. exact (AV a Ha).
    + ht_kept HS EE regs1.
    + ht_g HS. apply EE. reflexivity.
    + ht_lits HS.
    + ht_g HS. exact E20.
    + ht_g HS. reflexivity.
  - rewrite branch_eq_U, (U_atom _ 19 (Z.of_nat i)), U_SLit in Hc by (first [cbn [ew ewset Nat.eqb]; exact E19 | lia]).
    change (zcanon 0) with 0 in Hc. apply Z.eqb_neq in Hc.
    assert (Hi0 : i <> 0%nat) by lia. clear Hc.
    (* the shadow check of text[i - 1] (0x81318..0x81328): addressable by cstr_ok *)
    aj_run_tok EX_tbl_ok HS HJ SHOK HD_Bspan.
    { unfold HD_Bx.
      rewrite (U_atom_off _ 20 (cx_t cx + Z.of_nat i) (-1)) by (first [cbn [ew ewset Nat.eqb]; exact E20 | lia]).
      apply (obl_of_range tfibsegs (w_H W3) (ms_mem ms) _ (SOff 25 0) _ 1 (cx_t cx)
        (Z.of_nat (length (cx_tb cx)) + 1)).
      - pose proof (fw_cstr_low tfibsegs W3 mem1 (ms_mem ms) (cx_t cx) (cx_tb cx)
          ltac:(intros a Ha; apply AV; lia) HCt) as (_ & _ & _ & _ & _ & HRA1 & _).
        exact HRA1.
      - apply U_atom; [cbn [ew ewset Nat.eqb]; exact E25 | unfold SHADOW_OFF; lia].
      - lia.
      - lia. }
    { awr_ok_tac. }
    ht_av W3 mem1.
    (* the load of text[i - 1] at 0x8132c *)
    lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
      assert (VC : val_mem tfibsegs (mrestrict (w_H W3) (ms_mem msx)) (cx_t cx + Z.of_nat i - 1) 1
        (nth (pred i) (cx_tb cx) 0) /\ 0 <= nth (pred i) (cx_tb cx) 0 < 256) end.
    { destruct (HGa (pred i) ltac:(rewrite length_app; cbn [length]; lia)) as [Vc Rc].
      rewrite app_nth1 in Vc, Rc by lia.
      split; [|exact Rc].
      replace (cx_t cx + Z.of_nat i - 1) with (cx_t cx + Z.of_nat (pred i)) by lia.
      eapply fw_val_eqv; [exact AV | lia | cbn; lia | exact Vc]. }
    destruct VC as [VC Rc].
    ht_byte HS W3 (cx_t cx + Z.of_nat i) (nth (pred i) (cx_tb cx) 0) E20 E32 VC.
    aj_run_tok EX_tbl_ok HS HJ SHOK HD_Bspan.
    { awr_ok_tac. }
    ht_av W3 mem1.
    srr_branch_tok EX_tbl_ok HS SHOK HD_Bspan.
    + (* (c - 9) mod 2^64 <u 5: c is \t..\r, a space: EX_P *)
      ht_dec HS Hc ht_ltu (nth (pred i) (cx_tb cx) 0) E32 Rc.
      assert (SP : ManifestModel.is_space (ManifestModel.byte_at (cx_tb cx) (pred i)) = true)
        by (unfold ManifestModel.byte_at; rewrite (hd_m_space _ Rc), Hc; reflexivity).
      clear Hc.
      aj_run_to_tok EX_tbl_ok HS HJ SHOK HD_Bspan EX_P; [awr_ok_tac|]. ht_av W3 mem1.
      ht_mk HS.
      refine (hd_exit_P B cx i d f 6 ly3 S3 W3 regs1 mem1 md1 _ _ _ HLF HP HAT ltac:(lia)
        (hd_m_some6 _ _ HA1 HCI (or_intror SP)) ltac:(lia) HJ _ _ _ _ _ _).
      * intros a Ha _. exact (AV a Ha).
      * ht_kept HS EE regs1.
      * ht_g HS. apply EE. reflexivity.
      * ht_lits HS.
      * ht_g HS. exact E20.
      * ht_g HS. reflexivity.
    + ht_dec HS Hc ht_ltu (nth (pred i) (cx_tb cx) 0) E32 Rc. rename Hc into D1.
      aj_run_tok EX_tbl_ok HS HJ SHOK HD_Bspan.
      { awr_ok_tac. }
      ht_av W3 mem1.
      srr_branch_tok EX_tbl_ok HS SHOK HD_Bspan.
      * (* c = ' ': EX_P *)
        ht_dec HS Hc ht_eq32 (nth (pred i) (cx_tb cx) 0) E32 Rc.
        assert (SP : ManifestModel.is_space (ManifestModel.byte_at (cx_tb cx) (pred i)) = true)
          by (unfold ManifestModel.byte_at; rewrite (hd_m_space _ Rc), D1, Hc; reflexivity).
        clear Hc.
        aj_run_to_tok EX_tbl_ok HS HJ SHOK HD_Bspan EX_P; [awr_ok_tac|]. ht_av W3 mem1.
        ht_mk HS.
        refine (hd_exit_P B cx i d f 6 ly3 S3 W3 regs1 mem1 md1 _ _ _ HLF HP HAT ltac:(lia)
          (hd_m_some6 _ _ HA1 HCI (or_intror SP)) ltac:(lia) HJ _ _ _ _ _ _).
        -- intros a Ha _. exact (AV a Ha).
        -- ht_kept HS EE regs1.
        -- ht_g HS. apply EE. reflexivity.
        -- ht_lits HS.
        -- ht_g HS. exact E20.
        -- ht_g HS. reflexivity.
      * (* not a space: EX_CONT (0x814dc, s3 = i + 1), EX_L at i + 1 *)
        ht_dec HS Hc ht_eq32 (nth (pred i) (cx_tb cx) 0) E32 Rc.
        assert (SPF : ManifestModel.is_space (ManifestModel.byte_at (cx_tb cx) (pred i)) = false)
          by (unfold ManifestModel.byte_at; rewrite (hd_m_space _ Rc), D1, Hc; reflexivity).
        clear Hc.
        aj_run_to_tok EX_tbl_ok HS HJ SHOK HD_Bspan EX_L; [awr_ok_tac|]. ht_av W3 mem1.
        ht_mk HS.
        refine (hd_exit_L B cx i d f (pred f) ly3 S3 W3 regs1 mem1 md1 _ _ _ HLF HAT
          (hd_m_scan_step cx i d f HSC ltac:(lia) (hd_m_none_sp _ _ HA1 Hi0 SPF)) HJ _ _ _ _).
        -- intros a Ha _. exact (AV a Ha).
        -- ht_kept HS EE regs1.
        -- ht_g HS. rewrite E19, unsigned_lit_small by lia. unfold w64; f_equal; lia.
        -- ht_lits HS.
Qed.
End s.

Print Assumptions hd_T.
