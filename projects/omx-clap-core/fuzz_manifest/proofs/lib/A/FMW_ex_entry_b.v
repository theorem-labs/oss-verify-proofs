(* G4.ExEntry.PieceB2: ex_B_seg (FMW_ex_entry_kit.v:323). expected 0x811c4..0x811d8 on fm.asan (fuzz_manifest.c:119):
   a0 = q = text + j + 1 + n after strncmp (text + j + 1, uri, n) = 0; the instrumented load of text[j + 1 + n]
   (s9 = the shadow base, the token runner resolves the check); '>' goes to 0x81700 (a0 = 1) and EX_R (SEG_R, the
   answer names = 1), any other byte falls through to EX_S (SG, strchr (text + j + 1, '<') next).
   Cut state over raw register atoms with one byte region on a0, after G3's FMW_rd_lp.v lp_L_entry. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v ACeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMPstat FMH_Base FMH_Rt FMH_Fn FMW_lib FMW_ex_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_ex_entry_kit.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* run-to-run memory bookkeeping (FMW_ex_entry.v ee_fr): the frame of a run whose regions have no write window *)
Ltac eb_fr W lo hi :=
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) |- _ =>
    let K := fresh "KR" in
    pose proof (ee_kept_nowin _ _ W lo hi m0 m1 HFr ltac:(vm_compute; reflexivity)) as K end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
  repeat match goal with H : context [with_vm_backing (m_vm_lazy (with_vm_backing _ _ _)) _ _] |- _ =>
    rewrite wvb_collapse in H end.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis SEG_R : ex_seg_R B.
Hypothesis SG : ex_S_seg B.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* EX_B (0x811c4): raw register atoms; a0 = register 10's atom = q; extra atom 32 = the byte at q *)
Definition eb_byte : YP09.region := YP09.mkRegion (Some 10%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition eb_facts : facts :=
  mkFacts [(10%nat, mkAF 4096 (2 ^ 47 - 16) 0); (25%nat, EE_SB); (32%nat, mkAF 0 255 0)] [] [].
Definition ss_B : sstate := mkSS EX_B sr_atoms [eb_byte] None eb_facts.
Definition EB_SH : list shent := [mkSHE 10 0 1].

Lemma eb_cfg : forall (W : world tfibsegs) pc regs mem md Q,
  SRr tfibsegs W (cfg_at tfibsegs pc regs mem md) Q ->
  SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom tfibsegs)) md) Q.
Proof. intros W pc regs mem md Q H. exact H. Qed.

Lemma eb_entry : forall (W : world tfibsegs) mem regs3 q c,
  getr regs3 25 = w64 SHADOW_OFF -> getr regs3 10 = w64 q ->
  4096 <= q <= 2 ^ 47 - 16 -> 0 <= c < 256 ->
  val_mem tfibsegs (mrestrict (w_H W) mem) q 1 c ->
  st_ok tfibsegs (Ereg regs3 [Z_to_bv 64 c]) ss_B
    (restrict (w_H W) (mkst regs3 (Z_to_bv 64 EX_B) mem (seg_rom tfibsegs))).
Proof.
  intros W mem regs3 q c R25 R10 Hq Hc Vc.
  rewrite restrict_mkst_fx.
  set (E := Ereg regs3 [Z_to_bv 64 c]).
  assert (U25 : bv_unsigned (ew E 25) = SHADOW_OFF)
    by (subst E; rewrite (ew_Ereg_nat regs3 _ 25 25%bv eq_refl), R25; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U10 : bv_unsigned (ew E 10) = q)
    by (subst E; rewrite (ew_Ereg_nat regs3 _ 10 10%bv eq_refl), R10; apply unsigned_lit_small; lia).
  assert (U32 : bv_unsigned (ew E 32) = c)
    by (subst E; rewrite (ew_Ereg_extra regs3 _ 0); apply unsigned_lit_small; lia).
  unfold ss_B. apply (entry_st_ok_full tfibsegs); change (Ereg regs3 [Z_to_bv 64 c]) with E.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold eb_byte. apply Forall_cons; [|apply Forall_nil]; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U10. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val tfibsegs E _ q 0 1 (SOff 32 0) c);
      [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; lia
      | cbn; lia |].
    rewrite Z.add_0_r. exact Vc.
  - apply pairwise_disjoint_of_extents. unfold eb_byte, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. cbn [zpairwise_disjoint zall_disjoint]. tauto.
  - split; [|split; [exact I | exact I]].
    unfold eb_facts, EE_SB. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U10, U25, U32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SHADOW_OFF. repeat split; lia.
Qed.

Theorem ex_B_holds : ex_B_seg B.
Proof.
  intros cx j ly3 S3 W3 regs3 mem3 md3 HK HWF HA.
  pose proof LAWS as HL. pose proof fmw_segs_low as Hsegs. pose proof fmw_wx as Hwx.
  pose proof HA as (HCT & Hjl & H60 & Hfst & Hbef & R10 & R19 & R8).
  pose proof HCT as (HB & HC & Hn0 & R9 & R18 & R23).
  pose proof HC as (HJ & Hbl & HGL & Rsp & Rgp & Rtp & R25 & HSV & HRO & Ct & Cu & Kt & Ku).
  pose proof Ct as (_ & Ht4 & Htc & _ & Ham & HRA & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (ee_cstr_byte W3 mem3 (cx_t cx) (cx_tb cx) (S j + length (cx_ub cx)) Hjl Ct) as [Vc Hcr].
  set (c := nth (S j + length (cx_ub cx)) (cx_tb cx) 0) in *.
  assert (Eq : cx_t cx + Z.of_nat (S j + length (cx_ub cx)) = cx_t cx + Z.of_nat j + 1 + cx_n cx)
    by (unfold cx_n; lia).
  rewrite Eq in Vc. clear Eq.
  pose proof (eb_entry W3 mem3 regs3 (cx_t cx + Z.of_nat j + 1 + cx_n cx) c R25 R10
    ltac:(unfold cx_n; lia) Hcr Vc) as HS.
  remember (Ereg regs3 [Z_to_bv 64 c]) as E eqn:HE.
  assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr regs3 q)
    by (intros n q Hn; rewrite HE; apply ew_Ereg_nat; exact Hn).
  assert (E32 : ew E 32 = Z_to_bv 64 c) by (rewrite HE; exact (ew_Ereg_extra regs3 _ 0)).
  clear HE.
  assert (SHOK : sh_ok tfibsegs EE_Bx EB_SH E
    (mrestrict (w_H W3) (ms_mem (mkst regs3 (Z_to_bv 64 EX_B) mem3 (seg_rom tfibsegs))))).
  { unfold sh_ok, EB_SH. constructor; [|constructor]. cbn [ms_mem].
    apply (shent_ok_of_range tfibsegs (w_H W3) mem3 E EE_Bx 10 (cx_t cx) (Z.of_nat (length (cx_tb cx)) + 1)
      (cx_t cx + Z.of_nat j + 1 + cx_n cx) 0 1).
    - exact HRA.
    - unfold EE_Bx. apply U_atom; [rewrite (EE 25%nat 25%bv eq_refl); exact R25 | unfold SHADOW_OFF; lia].
    - apply U_atom; [rewrite (EE 10%nat 10%bv eq_refl); exact R10 | unfold cx_n; lia].
    - unfold cx_n; lia.
    - unfold cx_n; lia.
    - intros x Hx. cbn [Z.min Z.max] in Hx. unfold amem_range in Ham. unfold cx_n in Hx. unfold SHADOW_OFF. lia. }
  change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 EX_B) mem3 (seg_rom tfibsegs))) in HJ.
  unfold cfg_at. change (w64 EX_B) with (Z_to_bv 64 EX_B).
  aj_run_tok EX_tbl_ok HS HJ SHOK EX_Bspan.
  { awr_ok_tac. }
  eb_fr W3 (cx_sp cx - STK_expected) (cx_F cx + 104).
  srr_branch_tok EX_tbl_ok HS SHOK EX_Bspan.
  { (* text[j + 1 + n] = '>': "<uri>" at j, a0 = 1, return *)
    rewrite branch_eq_U, (U_atom _ 32 c), (U_atom _ 8 62) in Hc
      by (first [cbn [ew ewset Nat.eqb]; exact E32
                | cbn [ew ewset Nat.eqb]; rewrite (EE 8%nat 8%bv eq_refl); exact R8 | lia]).
    apply Z.eqb_eq in Hc.
    aj_run_to_tok EX_tbl_ok HS HJ SHOK EX_Bspan EX_R; [awr_ok_tac|].
    eb_fr W3 (cx_sp cx - STK_expected) (cx_F cx + 104).
    ee_mk HS. apply eb_cfg.
    apply (SEG_R cx ly3 S3 W3 _ _ _ HB).
    - apply (ee_com_keep B cx ly3 S3 W3 regs3 mem3 md3 _ _ _ HB HC HJ).
      + apply (ee_kept_trans _ _ _ _ _ _ _ _ _ _ KR KR0); lia.
      + ee_g HS. apply EE. reflexivity.
      + ee_g HS. apply EE. reflexivity.
      + ee_g HS. apply EE. reflexivity.
      + ee_g HS. apply EE. reflexivity.
    - ee_g HS. unfold cx_res.
      rewrite (ee_names_1 (cx_tb cx) (cx_ub cx) j Hn0 ltac:(lia) H60 Hfst Hc).
      first [reflexivity | apply bv_eq; vm_compute; reflexivity]. }
  { (* any other byte: no "<uri>" at j, strchr (text + j + 1, '<') next *)
    rewrite branch_eq_U, (U_atom _ 32 c), (U_atom _ 8 62) in Hc
      by (first [cbn [ew ewset Nat.eqb]; exact E32
                | cbn [ew ewset Nat.eqb]; rewrite (EE 8%nat 8%bv eq_refl); exact R8 | lia]).
    apply Z.eqb_neq in Hc.
    aj_run_to_tok EX_tbl_ok HS HJ SHOK EX_Bspan EX_S; [awr_ok_tac|].
    eb_fr W3 (cx_sp cx - STK_expected) (cx_F cx + 104).
    ee_mk HS. apply eb_cfg.
    apply (SG cx j ly3 S3 W3 _ _ _ HK HWF).
    split.
    { apply (ee_cut_keep B cx ly3 S3 W3 regs3 mem3 md3 _ _ _ HCT HJ).
      all: first [ apply (ee_kept_trans _ _ _ _ _ _ _ _ _ _ KR KR0); lia | ee_g HS; apply EE; reflexivity ]. }
    split; [lia|].
    split.
    { intros k Hk. destruct (Nat.lt_ge_cases k j) as [Hl|Hl]; [exact (Hbef k Hl)|].
      replace k with j by lia. apply ee_whole_at_close. exact Hc. }
    split.
    - ee_g HS. rewrite (EE 19%nat 19%bv eq_refl). exact R19.
    - ee_g HS. rewrite (EE 8%nat 8%bv eq_refl). exact R8. }
Qed.
End W.

Print Assumptions ex_B_holds.
