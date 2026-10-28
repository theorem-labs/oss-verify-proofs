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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmEnc Require Import EncSums_u5 EncKit_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module ESB.
Import PMES.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Definition uv := PB.uv.
Record sghost : Type := SG { s_rep : PML.srep; s_len : Z }.
(* [comment removed for export] *)
Definition sink_inv (M : mem) (S2 : Z) (g : sghost) : Prop := sink_at M S2 (s_rep g) /\ len (PML.srep_chars (s_rep g)) = s_len g.

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
Definition gB (g : sghost) : list (Z * Z) := PML.srep_blocks (s_rep g) ++ GR.
Variable kx b0 : Z.
Variable XIv : sghost -> nat -> env -> mem -> Prop.

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
Variable S2 : Z.
Hypothesis S2OBJ : PML.obj_on_stack L sp0 S2 24.
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
Definition STR_SCR : Z := 8496.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition g_upd (g : sghost) (rep' : PML.srep) (n : Z) : sghost := SG rep' (s_len g + n).

(* [comment removed for export] *)
Definition sink_chk (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : option CH2.cinfo :=
  let regs := CA.ps_reglist ps in
  match split_lit (nth 10 regs (ELit 0)) with
  | (ob, ok) =>
      if (expr_eqb ob OB && Z.eqb ok OK && CH2.blocks_eqb BLj BLi)%bool
      then CH2.custom_chk NF d STR_SCR 0 BLi [(ob, ok, ELit 24)] [] None c ps cj BLi
      else None
  end.

Lemma objs_facts : sp0 <= S2 /\ S2 + 24 <= hl_sptop L /\ S2 mod 8 = 0.
Proof. exact S2OBJ. Qed.

Lemma den_app_nodup : forall (own : list (Z * Z)) rep cr (M : mem) VM, hi_heap HI (own ++ LBo ++ PML.srep_blocks rep ++ GR) cr M VM ->
  lb_drop rep (own ++ LBo ++ PML.srep_blocks rep ++ GR) = own ++ LBo ++ GR.
Proof.
  intros own rep cr M VM HH. destruct (hio_wf L SCFG HI HIok _ _ _ _ HH) as (_ & Hnd & _).
  destruct rep as [s|cap p s]; cbn [lb_drop PML.srep_blocks app] in *; [reflexivity|].
  rewrite app_assoc. rewrite EK.lb_remove_app.
  - cbn [lb_remove fst]. rewrite Z.eqb_refl. rewrite <- app_assoc. reflexivity.
  - rewrite app_assoc, map_app in Hnd. apply (EK.nodup_app_l' _ _ p Hnd). cbn [map fst In]. left. reflexivity.
Qed.

(* [comment removed for export] *)

Lemma strx_scr : STRX_SCR = STR_SCR.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Hypothesis PUSHB : str_push_back_x_spec L HI.
Definition pushb_chk (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : option CH2.cinfo :=
  if APC.fact_ok (SR.ps_cells ps) (KRange (nth 11 (CA.ps_reglist ps) (ELit 0)) 0 255) then sink_chk c ps cj BLi BLj else None.


(* [comment removed for export] *)
Hypothesis APPEND : str_append_x_spec L HI.

(* [comment removed for export] *)
Definition PAYMAX : Z := 2 ^ 50.
(* [comment removed for export] *)
Definition strans_chk (scr : Z) (c : CC.cutpoint) (ps : SR.post_spec) (cj : CC.cutpoint) (BLi BLj : CA.blocks) : option CH2.cinfo :=
  let nx := (CC.cp_nx cj - APC.NCS - 1)%nat in
  if CH2.blocks_eqb BLj BLi
  then CH2.custom_chk NF d scr 1 BLi [(OB, OK, ELit 24)] [KRange (EVar nx) 0 PAYMAX] (Some (EVar nx)) c ps cj BLi
  else None.

(* [comment removed for export] *)
End Inst.
End ESB.
