(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5 PmLibSpecsX_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX CutHeap2V.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import VisitSumsX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmSmall Require Import VisitBridgeX_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module VBXU.
Import PMES.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).

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
Variable CredV : eghost -> nat -> env -> credit -> Prop.
Variable XIv : eghost -> nat -> env -> mem -> Prop.

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
Variables V S2 : Z.
Hypothesis W_ENC : forall w, In w (W_enc V S2) -> In w W.
Variable VB : expr.
Hypothesis VB_frozen : APC.expr_vars_lt NF VB = true.
Hypothesis VADDR : VBX.uv E0 VB = V.
Hypothesis S2_frozen : (52 < NF)%nat.
Hypothesis S2ADDR : VBX.uv E0 VBX.S2V = S2.
Hypothesis LITLEN : PML.LIT_HI - PML.LIT_LO = VSX.LIT_LEN.

Let LS : hl_segs L = RSEGS := PmLayout.ly_segs L LAY.
Let LYI := PB.LYI_ L LAY.
Let LYE := PB.LYE_ L LAY.
Let LYR := PmLayout.ly_ro L LAY.

Abbreviation OKV := (CH2V.okV L M00 LBo sp0 d W).
Abbreviation HAMBV := (CH2V.heap_ambV L HI NF E0 model0 LBo sp0 d W BLS eghost VBX.gB CredV).
Abbreviation AMB3V := (CH2V.amb3V L HI NF E0 M00 model0 LBo sp0 d W BLS eghost VBX.gB CredV XIv).
Abbreviation LEAFOKV := (CH2V.leaf_okV L HI NF E0 M00 model0 LBo sp0 d W BLS eghost VBX.gB CredV XIv CPS K PML.fp_ok).
Abbreviation is_leaf := (CH2.is_leaf CPS TAGS).

(* Post of a visitor call (the post of PMES.vtrans_genU / vtrans_svU with return value 1). *)
Definition vpost (LBc : list (Z * Z)) (g : eghost) (ev : eev) (kx bx : Z)
  : bvmap 5 word -> mem -> bvmap 5 word -> mem -> list (Z * Z) -> credit -> list (Z * Z) -> list L5.range -> Prop :=
  fun _ _ R' M' LB' cr' LBk Wc => exists (g' : eghost) (pay : Z),
    PML.a0 R' 1 /\ enc_inv M' V S2 g' /\ g_es g' = estep (g_es g) ev /\ pay_ok ev pay /\ g_len g' = g_len g + ev_ind (g_es g) ev + pay /\
    PML.lits_ok M' /\ LB' = LBc ++ g_lbv g' /\ LBk = LBc /\ Wc = W_enc V S2 /\ ecreditU L cr' g' kx bx.

(* Return condition of a visitor call: the encoder ghost advanced by ev, encoder credit at the reserves kx bx. *)
Definition vret (g : eghost) (ev : eev) (E : env) (g' : eghost) (M2 : mem) : Prop :=
  enc_inv M2 V S2 g' /\ PML.lits_ok M2 /\ g_es g' = estep (g_es g) ev /\
  exists pay, pay_ok ev pay /\ g_len g' = g_len g + ev_ind (g_es g) ev + pay.

Lemma VIS_SCR_eq : PMES.VIS_SCR PMES.WD_SCR_X = VBX.VIS_SCR.
Proof. vm_compute. reflexivity. Qed.

(* Visitor-call leaf, generic in the callee: at the call the walk supplies a cps_heap triple for the callee whose
   post is vpost at the reserves (KXE E) (BXE E); the return premise receives the encoder credit at the same reserves. *)
Lemma vis_leaf_ok_core : forall (pc : Z) (ev : eev) (KXE BXE : env -> Z) i c k ps j cj ci g M0c,
  OKV M0c ->
  is_leaf i c k ps (CC.TOther pc) -> CH2.ret_of RETS i k = Some j -> nth_error CPS j = Some cj -> SR.ps_pc ps = pc ->
  VBX.vis_chk NF d VB c ps cj (nth i BLS []) (nth j BLS []) = Some ci ->
  (forall E R (M : mem) model E' R' (M' : mem) cr, CC.At (hl_segs L) c E R M -> HAMBV g M0c i E M model -> XIv g i E M -> env_agree (CC.cp_nx c) E E' ->
     CC.leaf_facts (hl_segs L) c ps E' R' M M' ->
     CH2.common_facts_x L HI NF E0 M0c model0 (CH2V.LBr LBo eghost VBX.gB g) sp0 d W BLS (CredV g) VBX.VIS_SCR 0 c ps cj ci i E E' R' M' model ->
     getr R' 10%bv = Z_to_bv 64 V ->
     hi_heap HI ((CH2.den E' (nth i BLS []) ++ LBo) ++ g_lbv g) cr M' (m_vmmaps model) -> CredV g i E cr ->
     exists Pre : bvmap 5 word -> mem -> Prop, Pre R' M' /\
       PML.cps_heap L HI pc (CC.cp_pc cj) (sp0 + CH2.ci_csp ci) VBX.VIS_SCR ((CH2.den E' (nth i BLS []) ++ LBo) ++ g_lbv g) cr Pre
         (vpost (CH2.den E' (nth i BLS []) ++ LBo) g ev (KXE E) (BXE E))) ->
  (forall E E' R' (M M' : mem) E2 (M2 : mem) g' cr', XIv g i E M -> env_agree NF E0 E' -> env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' ->
     env_agree (CH2.ci_nx ci) E' E2 -> (CC.cp_nx c <= CH2.ci_nx ci)%nat ->
     L5C.hpres L (CH2.den E' (nth i BLS []) ++ LBo) (sp0 + CH2.ci_csp ci) VBX.VIS_SCR (W_enc V S2) M' M2 ->
     hl_sptop L - 2 ^ 23 + VBX.VIS_SCR <= sp0 + CH2.ci_csp ci -> sp0 + CH2.ci_csp ci <= sp0 ->
     vret g ev E g' M2 -> ecreditU L cr' g' (KXE E) (BXE E) -> XIv g' j E2 M2 /\ CredV g' j E2 cr') ->
  LEAFOKV g M0c i c ps.
Proof.
  intros pc ev KXE BXE i c k ps j cj ci g M0c HOKV IL Hret Hcj Hpc Hchk CALLC XIRET.
  apply (VBX.vis_leaf_ok L HI HIok LAY NF E0 M00 model0 LBo sp0 d W BLS CredV XIv STK SCR_pos NF32 SP0 TP0 W_ok CRS_ok WRS_ok IMG_ok
           CPS TAGS RETS K DEF0 V S2 W_ENC VB VB_frozen VADDR S2_frozen S2ADDR LITLEN
           pc (vret g ev) (fun E g' cr' => ecreditU L cr' g' (KXE E) (BXE E)) i c k ps j cj ci g M0c HOKV IL Hret Hcj Hpc Hchk).
  - intros E R M model E' R' M' cr fx' HAt HAmb HXI Hag HLF CF Ga0 HH HC HFP HK.
    destruct (CALLC E R M model E' R' M' cr HAt HAmb HXI Hag HLF CF Ga0 HH HC) as (Pre & HPre & HCPS).
    pose proof CF as [HA' _ _ _ _ _ _ _ _ _ _ _].
    destruct HA' as (Hmo & _).
    assert (Hmo' : PML.model_ok model) by (first [exact Hmo | destruct Hmo as (A1 & A2 & A3); exact (conj A1 (conj A2 A3))]).
    apply (HCPS fx' R' M' model K HH Hmo' K_nil HFP HPre).
    intros fx2 R2 M2 model2 LB' cr' LBk Wc HFP2 HPost HRP HPRES HBV HH2.
    destruct HPost as (g' & pay & HA0 & HINV & HES & HPAY & HLEN & HLITS & HLB & HLBk & HWc & HCR).
    apply (HK fx2 R2 M2 model2 LB' cr' LBk Wc HFP2); [| exact HRP | exact HPRES | exact HBV | exact HH2].
    exists g'. split; [exact HA0|]. split; [split; [exact HINV|]; split; [exact HLITS|]; split; [exact HES|]; exists pay; split; [exact HPAY | exact HLEN]|].
    split; [exact HLB|]. split; [exact HLBk|]. split; [exact HWc|]. exact HCR.
  - exact XIRET.
Qed.

(* Site facts every visitor call derives in the walk: the callee's precondition apart from the stack/return-address
   part (taken from the certificate) and the encoder objects (taken from objs_enc at the walk's frame). *)
Lemma entry_at_call : forall g M0c c ps cj ci i E E' R' (M' : mem) model,
  CH2.common_facts_x L HI NF E0 M0c model0 (CH2V.LBr LBo eghost VBX.gB g) sp0 d W BLS (CredV g) VBX.VIS_SCR 0 c ps cj ci i E E' R' M' model ->
  PML.entry L R' M' (sp0 + CH2.ci_csp ci) (CC.cp_pc cj) VBX.VIS_SCR /\ CH2.ci_csp ci <= 0.
Proof.
  intros g M0c c ps cj ci i E E' R' M' model CF.
  pose proof CF as [_ _ _ _ _ [Hra Hraok] (Hsp & Hc1 & _) Hstk Htp _ _ _].
  split; [|exact Hc1].
  unfold PML.entry. split; [exact Hra|]. split; [exact Hraok|]. split; [exact Hsp|]. split; [|exact Hstk].
  rewrite Htp. rewrite (PmLayout.ly_tp L LAY). reflexivity.
Qed.

Lemma objs_enc_lower : forall sp sp', objs_enc L sp V S2 -> sp' <= sp -> objs_enc L sp' V S2.
Proof.
  unfold objs_enc, PML.obj_on_stack. intros sp sp' ((A1 & A2 & A3) & (B1 & B2 & B3) & C) H.
  repeat split; try assumption; lia.
Qed.

(* Visitor call to a callee with a PMES.vtransU spec (visit_null, visit_bool, visit_begin_*, visit_end_*, visit_*64,
   visit_double). *)
Lemma vis_leaf_okU : forall (pc : Z) (ev : eev) (Args : list (Z * Z) -> bvmap 5 word -> mem -> Prop) (KXE BXE : env -> Z) i c k ps j cj ci g M0c,
  vtransU L HI WD_SCR_X pc ev Args -> objs_enc L sp0 V S2 ->
  OKV M0c ->
  is_leaf i c k ps (CC.TOther pc) -> CH2.ret_of RETS i k = Some j -> nth_error CPS j = Some cj -> SR.ps_pc ps = pc ->
  VBX.vis_chk NF d VB c ps cj (nth i BLS []) (nth j BLS []) = Some ci ->
  (forall E R (M : mem) model E' R' (M' : mem) cr, CC.At (hl_segs L) c E R M -> HAMBV g M0c i E M model -> XIv g i E M -> env_agree (CC.cp_nx c) E E' ->
     CC.leaf_facts (hl_segs L) c ps E' R' M M' ->
     CH2.common_facts_x L HI NF E0 M0c model0 (CH2V.LBr LBo eghost VBX.gB g) sp0 d W BLS (CredV g) VBX.VIS_SCR 0 c ps cj ci i E E' R' M' model ->
     hi_heap HI ((CH2.den E' (nth i BLS []) ++ LBo) ++ g_lbv g) cr M' (m_vmmaps model) -> CredV g i E cr ->
     Args (CH2.den E' (nth i BLS []) ++ LBo) R' M' /\ enc_inv M' V S2 g /\ ev_guard (g_es g) ev /\ eroomU g ev /\ PML.img_ro M' /\ PML.lits_ok M' /\
     ecreditU L cr g (KXE E) (BXE E)) ->
  (forall E E' R' (M M' : mem) E2 (M2 : mem) g' cr', XIv g i E M -> env_agree NF E0 E' -> env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' ->
     env_agree (CH2.ci_nx ci) E' E2 -> (CC.cp_nx c <= CH2.ci_nx ci)%nat ->
     L5C.hpres L (CH2.den E' (nth i BLS []) ++ LBo) (sp0 + CH2.ci_csp ci) VBX.VIS_SCR (W_enc V S2) M' M2 ->
     hl_sptop L - 2 ^ 23 + VBX.VIS_SCR <= sp0 + CH2.ci_csp ci -> sp0 + CH2.ci_csp ci <= sp0 ->
     vret g ev E g' M2 -> ecreditU L cr' g' (KXE E) (BXE E) -> XIv g' j E2 M2 /\ CredV g' j E2 cr') ->
  LEAFOKV g M0c i c ps.
Proof.
  intros pc ev Args KXE BXE i c k ps j cj ci g M0c VS OBJS0 HOKV IL Hret Hcj Hpc Hchk SITE XIRET.
  apply (vis_leaf_ok_core pc ev KXE BXE i c k ps j cj ci g M0c HOKV IL Hret Hcj Hpc Hchk); [|exact XIRET].
  intros E R M model E' R' M' cr HAt HAmb HXI Hag HLF CF Ga0 HH HC.
  destruct (entry_at_call g M0c c ps cj ci i E E' R' M' model CF) as [HEN Hc1].
  destruct (SITE E R M model E' R' M' cr HAt HAmb HXI Hag HLF CF HH HC) as (HArgs & HINV & HGD & HRM & HIMG & HLIT & HCR).
  pose proof (VS (CH2.den E' (nth i BLS []) ++ LBo) cr (sp0 + CH2.ci_csp ci) (CC.cp_pc cj) V S2 (KXE E) (BXE E) g) as HCPS.
  try rewrite VIS_SCR_eq in HCPS.
  eexists. split; [|exact HCPS].
  cbv beta. split; [exact HEN|]. split; [exact Ga0|]. split; [exact HArgs|]. split; [exact HINV|]. split; [exact HGD|]. split; [exact HRM|].
  split; [exact HIMG|]. split; [exact HLIT|]. split; [exact HCR|]. apply (objs_enc_lower sp0); [exact OBJS0 | lia].
Qed.

(* Visitor call to a callee with a PMES.vtrans_svU spec (visit_key, visit_string): the site also supplies the
   string-view argument. *)
Lemma vis_leaf_ok_svU : forall (pc : Z) (ev : eev) (bs : list Z) (Extra : bvmap 5 word -> Prop) (KXE BXE : env -> Z) i c k ps j cj ci g M0c,
  vtrans_svU L HI WD_SCR_X pc ev bs Extra -> objs_enc L sp0 V S2 ->
  OKV M0c ->
  is_leaf i c k ps (CC.TOther pc) -> CH2.ret_of RETS i k = Some j -> nth_error CPS j = Some cj -> SR.ps_pc ps = pc ->
  VBX.vis_chk NF d VB c ps cj (nth i BLS []) (nth j BLS []) = Some ci ->
  (forall E R (M : mem) model E' R' (M' : mem) cr, CC.At (hl_segs L) c E R M -> HAMBV g M0c i E M model -> XIv g i E M -> env_agree (CC.cp_nx c) E E' ->
     CC.leaf_facts (hl_segs L) c ps E' R' M M' ->
     CH2.common_facts_x L HI NF E0 M0c model0 (CH2V.LBr LBo eghost VBX.gB g) sp0 d W BLS (CredV g) VBX.VIS_SCR 0 c ps cj ci i E E' R' M' model ->
     hi_heap HI ((CH2.den E' (nth i BLS []) ++ LBo) ++ g_lbv g) cr M' (m_vmmaps model) -> CredV g i E cr ->
     (exists sv, PML.a1 R' sv /\ Extra R' /\ sv_argU L (CH2.den E' (nth i BLS []) ++ LBo) M' (sp0 + CH2.ci_csp ci) V S2 sv bs) /\
     enc_inv M' V S2 g /\ ev_guard (g_es g) ev /\ eroomU g ev /\ PML.img_ro M' /\ PML.lits_ok M' /\
     ecreditU L cr g (KXE E) (BXE E)) ->
  (forall E E' R' (M M' : mem) E2 (M2 : mem) g' cr', XIv g i E M -> env_agree NF E0 E' -> env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' ->
     env_agree (CH2.ci_nx ci) E' E2 -> (CC.cp_nx c <= CH2.ci_nx ci)%nat ->
     L5C.hpres L (CH2.den E' (nth i BLS []) ++ LBo) (sp0 + CH2.ci_csp ci) VBX.VIS_SCR (W_enc V S2) M' M2 ->
     hl_sptop L - 2 ^ 23 + VBX.VIS_SCR <= sp0 + CH2.ci_csp ci -> sp0 + CH2.ci_csp ci <= sp0 ->
     vret g ev E g' M2 -> ecreditU L cr' g' (KXE E) (BXE E) -> XIv g' j E2 M2 /\ CredV g' j E2 cr') ->
  LEAFOKV g M0c i c ps.
Proof.
  intros pc ev bs Extra KXE BXE i c k ps j cj ci g M0c VS OBJS0 HOKV IL Hret Hcj Hpc Hchk SITE XIRET.
  apply (vis_leaf_ok_core pc ev KXE BXE i c k ps j cj ci g M0c HOKV IL Hret Hcj Hpc Hchk); [|exact XIRET].
  intros E R M model E' R' M' cr HAt HAmb HXI Hag HLF CF Ga0 HH HC.
  destruct (entry_at_call g M0c c ps cj ci i E E' R' M' model CF) as [HEN Hc1].
  destruct (SITE E R M model E' R' M' cr HAt HAmb HXI Hag HLF CF HH HC) as ((sv & HA1 & HEX & HSV) & HINV & HGD & HRM & HIMG & HLIT & HCR).
  pose proof (VS (CH2.den E' (nth i BLS []) ++ LBo) cr (sp0 + CH2.ci_csp ci) (CC.cp_pc cj) V S2 (KXE E) (BXE E) sv g) as HCPS.
  try rewrite VIS_SCR_eq in HCPS.
  eexists. split; [|exact HCPS].
  cbv beta. split; [exact HEN|]. split; [exact Ga0|]. split; [exact HA1|]. split; [exact HEX|]. split; [exact HSV|]. split; [exact HINV|].
  split; [exact HGD|]. split; [exact HRM|]. split; [exact HIMG|]. split; [exact HLIT|]. split; [exact HCR|].
  apply (objs_enc_lower sp0); [exact OBJS0 | lia].
Qed.
End Inst.
End VBXU.
