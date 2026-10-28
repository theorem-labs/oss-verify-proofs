(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module ETL2.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).

Lemma hpres_comp : forall (L : heap_layout) LB sp scr1 scr2 W (M M' M'' : mem),
  0 <= scr2 <= scr1 -> hl_ceil L <= sp - scr1 -> 0 <= hl_ceil L -> hl_errno L + 4 <= hl_ceil L -> sp <= 2 ^ 64 ->
  L5C.hpres L LB sp scr1 W M M' -> L5C.hpres L LB sp scr2 W M' M'' -> L5C.hpres L LB sp scr1 W M M''.
Proof.
  intros L LB sp scr1 scr2 W M M' M'' Hs Hc Hc0 He Hsp H1 H2.
  assert (CL : forall a, client_addr L LB sp scr1 a -> client_addr L LB sp scr2 a).
  { intros a [B|[[C1 C2]|C]]; [left; exact B | right; left; split; [exact C1 | lia] | right; right; exact C]. }
  apply L5C.hpres_intro.
  - intros a (K1 & K2 & K3 & K4). rewrite (L5C.hpres_kept _ _ _ _ _ _ _ a H2); [apply (L5C.hpres_kept _ _ _ _ _ _ _ a H1); exact (conj K1 (conj K2 (conj K3 K4)))|].
    split; [exact K1|]. split; [apply CL; exact K2|]. split; assumption.
  - intros j Hj. destruct (Z_lt_dec j (scr1 - scr2)) as [Hlo|Hhi].
    + apply (L5C.hpres_cdef _ _ _ _ _ _ _ (sp - scr1 + j) H2); [lia | right; left; split; lia | unfold in_errno; lia|].
      apply (L5C.hpres_defined _ _ _ _ _ _ _ H1). lia.
    + replace (sp - scr1 + j) with (sp - scr2 + (j - (scr1 - scr2))) by lia. apply (L5C.hpres_defined _ _ _ _ _ _ _ H2). lia.
  - intros a Ha HC HE Hd. apply (L5C.hpres_cdef _ _ _ _ _ _ _ a H2 Ha (CL a HC) HE). exact (L5C.hpres_cdef _ _ _ _ _ _ _ a H1 Ha HC HE Hd).
Qed.

Section Inst.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Variable NF : nat.
Variable E0 : env.
Variable M0 : mem.
Variable model0 : Model.
Variable LBrest : list (Z * Z).
Variable sp0 : Z.
Variable d : CH.hdecl.
Variable W : list L5.range.
Variable BLS : list CA.blocks.
Variable Cred : nat -> env -> credit -> Prop.
Hypothesis STK : sp0 mod 16 = 0 /\ hl_ceil L + CH.hd_scr d <= sp0 /\ sp0 <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47.
Hypothesis SCR_pos : 0 <= CH.hd_scr d.
Hypothesis NF32 : (32 <= NF)%nat.
Hypothesis SP0 : bv_unsigned (ev E0 2) = sp0.
Hypothesis W_ok : forall r a, In r W -> L5.in_rng r a -> CH2.wclient L sp0 a.
Hypothesis WRS_ok : forall r, In r (CH.hd_wrs d) -> SGP.region_vars_lt NF r = true /\ forall a, CH2.in_reg E0 r a -> exists w, In w W /\ L5.in_rng w a.
Variable CPS : list CC.cutpoint.
Variable TAGS : list (list CC.tag).
Variable K : ShapeAlg.TSet.
Hypothesis DEF0 : L5.defined M0 (sp0 - CH.hd_scr d) (CH.hd_scr d).
Variable SCRC : Z.
Hypothesis SCRC_ge : CH.hd_scr d <= SCRC.
Hypothesis STKC : hl_ceil L + SCRC <= sp0.
Hypothesis DEFC : L5.defined M0 (sp0 - SCRC) SCRC.
Variable R0 : bvmap 5 word.
Hypothesis EV0 : forall x : reg, ev E0 (ridx x) = getr R0 x.
Hypothesis HEAPCHK : CH2.heap_chk3 NF d BLS CPS TAGS = true.

Let LYI := PB.LYI_ L LAY.
Let LYE := PB.LYE_ L LAY.
Let LYR := PmLayout.ly_ro L LAY.
Abbreviation HAMB := (CH2.heap_amb L HI NF E0 M0 model0 LBrest sp0 d W BLS Cred).

Definition seg_base_chk (c : CC.cutpoint) : bool := Nat.leb NF (CC.cp_nx c).

(* [comment removed for export] *)
Lemma seg_leaf : forall i c k ps pc, CH2.is_leaf CPS TAGS i c k ps (CC.TOther pc) -> seg_base_chk c = true ->
  forall E R (M : mem) model E' R' (M' : mem),
    CC.At (hl_segs L) c E R M -> HAMB i E M model -> env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' ->
    L5C.hpres L LBrest sp0 SCRC W M0 M' /\ HAMB i E M' model /\ env_agree NF E0 E'.
Proof.
  intros i c k ps pc IL Hchk E R M model E' R' M' HAt HA Hag HLF.
  unfold seg_base_chk in Hchk. apply Nat.leb_le in Hchk.
  pose proof (CH2.leaf_amb3 L HI HIok LYI LYE LYR NF E0 M0 model0 LBrest sp0 d W BLS Cred STK SCR_pos NF32 SP0 W_ok WRS_ok CPS TAGS HEAPCHK i c k ps pc IL
                E E' R R' M M' model HAt HA Hag HLF) as HA'.
  pose proof HA' as (Hmo1 & Hbv1 & HagE1 & _ & Hfr1 & Hdf1).
  assert (HagE' : env_agree NF E0 E') by (eapply CC.env_agree_trans; [exact HagE1 | eapply CC.env_agree_le; [exact Hag | exact Hchk]]).
  pose proof (CH2.amb_hpres L HI LYI LYE NF E0 M0 model0 LBrest sp0 d W BLS Cred STK NF32 i E M' model HA' DEF0) as HP0.
  pose proof (CH2.ceil_lo L NF sp0 d STK NF32) as CLO. pose proof STK as (S1 & S2 & S3 & S4 & S5). pose proof LYI as [LI1 LI2]. pose proof LYE as [LE1 LE2].
  split; [|split; [exact HA' | exact HagE']].
  apply L5C.hpres_intro.
  - intros a (K1 & K2 & K3 & K4). apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP0). split; [exact K1|]. split; [|split; assumption].
    destruct K2 as [B|[[C1' C2']|C]]; [left; exact B | right; left; split; [exact C1' | lia] | right; right; exact C].
  - intros j Hj. apply (Hdf1 (sp0 - SCRC + j)); [lia | | apply DEFC; lia].
    split; [right; left; split; lia | unfold in_errno; lia].
  - intros a Ha HC HE Hd. apply (L5C.hpres_cdef _ _ _ _ _ _ _ a HP0 Ha); [|exact HE | exact Hd].
    destruct HC as [B|[[C1' C2']|C]]; [left; exact B | right; left; split; [exact C1' | lia] | right; right; exact C].
Qed.
(* [comment removed for export] *)
Lemma exit_ret2 : forall retpc i c k ps pc (rv : Z), CL.is_ret_at RSEGS retpc -> CH2.is_leaf CPS TAGS i c k ps (CC.TOther pc) -> seg_base_chk c = true ->
  SR.ps_pc ps = retpc -> L5.ra_ok rv ->
  forall (fx' : FPState) E R (M : mem) model E' R' (M' : mem),
    CC.At (hl_segs L) c E R M -> HAMB i E M model -> env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' ->
    getr R' 1%bv = Z_to_bv 64 rv ->
    (L5C.hpres L LBrest sp0 SCRC W M0 M' -> HAMB i E M' model -> env_agree NF E0 E' -> srealizes RSEGS SCFG (@PML.cfg fx' R' rv M' model) K) ->
    srealizes (hl_segs L) SCFG (mkCfg (@mkst fx' R' (Z_to_bv 64 (SR.ps_pc ps)) M' (seg_rom (hl_segs L))) model) K.
Proof.
  intros retpc i c k ps pc rv Hret IL Hchk Hpc Hraok fx' E R M model E' R' M' HAt HA Hag HLF Hra' Hcont.
  destruct (seg_leaf i c k ps pc IL Hchk E R M model E' R' M' HAt HA Hag HLF) as (HP & HA' & HagE').
  pose proof HA' as (Hmo1 & _).
  pose proof (PmLayout.ly_segs L LAY) as LS.
  rewrite Hpc, LS. eapply CL.ret_cps; [exact Hret | exact (proj1 Hmo1) | exact (proj1 (proj2 Hmo1)) | |].
  { rewrite Hra'. apply Hoare.ret_ok_even. destruct Hraok as [R1' R2']. rewrite u64_of_Z by lia. exact R2'. }
  rewrite Hra'. exact (Hcont HP HA' HagE').
Qed.
End Inst.
End ETL2.
