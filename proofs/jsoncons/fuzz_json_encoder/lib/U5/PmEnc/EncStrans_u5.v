(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX CutHeap2V.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncSums_u5 EncKit_u5 EncBridges_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module EST.
Import PMES.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Definition uv := PB.uv.

Section Inst.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis LAY : PmLayout.pm0_layout L.
Variable NF : nat.
Variable E0 : env.
Variable M00 : mem.
Variable model0 : Model.
Variable LBo : list (Z * Z).
Variable sp0 : Z.
Variable d : CH.hdecl.
Variable W : list L5.range.
Variable BLS : list CA.blocks.
(* [comment removed for export] *)
Variable GR : list (Z * Z).
Variable kx b0 : Z.
Variable XIv : eghost -> nat -> env -> mem -> Prop.
Abbreviation gB := (EB.gB GR).

Hypothesis STK : sp0 mod 16 = 0 /\ hl_ceil L + CH.hd_scr d <= sp0 /\ sp0 <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47.
Hypothesis SCR_pos : 0 <= CH.hd_scr d.
Hypothesis NF32 : (32 <= NF)%nat.
Hypothesis SP0 : bv_unsigned (ev E0 2) = sp0.
Hypothesis TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L).
Hypothesis W_ok : forall r a, In r W -> L5.in_rng r a -> CH2.wclient L sp0 a.
Hypothesis CRS_ok : forall r, In r (CH.hd_crs d) -> SGP.region_vars_lt NF r = true /\ forall a, CH2.in_reg E0 r a -> CH2.sclient L LBo sp0 a.
Hypothesis WRS_ok : forall r, In r (CH.hd_wrs d) -> SGP.region_vars_lt NF r = true /\ forall a, CH2.in_reg E0 r a -> exists w, In w W /\ L5.in_rng w a.
Hypothesis IMG_ok : forall r a, In r (CH.hd_img d) -> fst r <= a < snd r -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_alloc_static L a /\ ~ in_errno L a.
Variable CPS : list CC.cutpoint.
Variable TAGS : list (list CC.tag).
Variable RETS : list (nat * nat * nat * Z).
Variable K : ShapeAlg.TSet.
Hypothesis K_nil : K [].
Hypothesis DEF0 : L5.defined M00 (sp0 - CH.hd_scr d) (CH.hd_scr d).
(* [comment removed for export] *)
Variables V S2 : Z.
Hypothesis OBJS : objs_enc L sp0 V S2.
Hypothesis W_S2 : In (S2, 24) W.
(* [comment removed for export] *)
Variable OB : expr.
Variable OK : Z.
Hypothesis OB_frozen : APC.expr_vars_lt NF OB = true.
Hypothesis OADDR : estart E0 (SA OB OK) = S2.

Let LS : hl_segs L = RSEGS := PmLayout.ly_segs L LAY.
Let LYI := PB.LYI_ L LAY.
Let LYE := PB.LYE_ L LAY.
Let LYR := PmLayout.ly_ro L LAY.

Abbreviation OKV := (CH2V.okV L M00 LBo sp0 d W).
Abbreviation is_leaf := (CH2.is_leaf CPS TAGS).

(* [comment removed for export] *)
Definition kxs (g : eghost) : Z := kx + kv_st (g_scap g) * hl_k_per_malloc L.
Definition PAYMAX : Z := 2 ^ 50.

(* [comment removed for export] *)
Definition strans_chk (scr : Z) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : option CH2.cinfo :=
  let nx := (CC.cp_nx cj - APC.NCS - 1)%nat in
  if CH2.blocks_eqb BLj BLi
  then CH2.custom_chk NF d scr 1 BLi [(OB, OK, ELit 24)] [KRange (EVar nx) 0 PAYMAX] (Some (EVar nx)) c ps cj BLi
  else None.

Lemma objs_facts : sp0 <= V /\ V + 408 <= hl_sptop L /\ sp0 <= S2 /\ S2 + 24 <= hl_sptop L /\ S2 mod 8 = 0 /\ PML.apart V 408 S2 24.
Proof. destruct OBJS as ((A1 & A2 & A3) & (B1 & B2 & B3) & C). unfold ENC_SIZE in *. repeat split; assumption. Qed.

(* [comment removed for export] *)
Lemma enc_inv_kept : forall (M' M2 : mem) g rep' n LBk spc scr,
  enc_inv M' V S2 g -> L5C.hpres L LBk spc scr [(S2, 24)] M' M2 -> L5C.stk (hl_sptop L) M2 spc scr -> 0 <= scr -> spc <= sp0 ->
  incl (stack_blocks (g_sb g) (g_scap g)) LBk -> (forall b, In b LBk -> block_range L (fst b) (snd b)) ->
  sink_at M2 S2 rep' -> len (PML.srep_chars rep') = g_len g + n ->
  enc_inv M2 V S2 (EB.g_upd g rep' n).
Proof.
  intros M' M2 g rep' n LBk spc scr (I1 & I2 & I3 & I4 & I5) HP HSTK Hscr Hsp Hst Hbr Hsink Hlen.
  destruct objs_facts as (O1 & O2 & O3 & O4 & O5 & O6). pose proof STK as (S1 & S2' & S3 & S4 & S5).
  pose proof (PmLayout.ly_errno L LAY) as LE.
  assert (KV : forall a, V <= a < V + 408 -> L5C.kept L LBk spc scr [(S2, 24)] a).
  { intros a Ha. apply (L5C.kept_stack_stk L LBk M2 spc scr); [exact HSTK | exact Hscr | lia | rewrite LE; lia |].
    intros w [<-|[]]. unfold L5.in_rng. cbn [fst snd]. unfold PML.apart in O6. lia. }
  assert (AV : forall a n0, V <= a -> a + n0 <= V + 408 -> L5C.agree_on M' M2 a n0).
  { intros a n0 H1 H2 i Hi. apply (L5C.hpres_kept _ _ _ _ _ _ _ i HP). apply KV. lia. }
  unfold EB.g_upd. split; [|split; [|split; [|split]]]; cbn [g_es g_len g_rep g_sb g_scap].
  - apply (EK.enc_obj_agree M' M2 V S2 _ ltac:(lia) ltac:(unfold ENC_SIZE; lia)); [apply AV; unfold O_COLUMN; lia | apply AV; unfold O_COLON, ENC_SIZE; lia | | exact I1].
    apply (L5C.defined_agree M' M2 (V + O_COLUMN) 8); [apply AV; unfold O_COLUMN; lia|].
    destruct I1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _). exact X.
  - apply (EK.stack_at_agree M' M2 V _ _ _ ltac:(lia) ltac:(unfold ENC_SIZE; lia)); [apply AV; unfold O_STACK; lia | | exact I2].
    intros Hne. assert (Hin : In (g_sb g, g_scap g) LBk).
    { apply Hst. unfold stack_blocks. destruct (Z.eqb_spec (g_scap g) 0) as [E|E]; [contradiction | left; reflexivity]. }
    destruct (Hbr _ Hin) as (B0 & B1 & B2 & B3 & B4). cbn [fst snd] in *.
    split; [lia|]. split; [lia|]. intros i Hi. apply (L5C.hpres_kept _ _ _ _ _ _ _ i HP).
    pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI.
    apply (L5C.kept_block L LBk spc scr [(S2, 24)] (g_sb g) (g_scap g) i Hin); [lia | lia | lia | rewrite LE; lia|].
    intros w [<-|[]]. unfold L5.in_rng. cbn [fst snd]. lia.
  - exact Hsink.
  - exact Hlen.
  - exact I5.
Qed.


(* [comment removed for export] *)
End Inst.
End EST.
