(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm9PlanKit Pm9L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm9CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtCpsA CutRtA CutRtC CutRtD.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA PmLibStaticsA PmCurDefs.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit Require Import PtKitA PtKitB.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Cut_psome_cboth_T Cut_psome_cboth_D Cut_psome_cboth.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import PsKitA PsoInstCB PsoSemA PsoSemCA PsoKnCB ParseSomeChkCB PsoBaseCB PsoAuxCB PsoXiCB PsoLinkCB PsoFrmCB PsoExitCB PsoStCB PsoCkCB PsoCallCB PsoKnOkCB.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module G := PSO.G.
Module GT := PSO.GT.
Import PSOC.
Abbreviation RSEGS := Pm9PlanKit.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation IC := PMLA.C_cboth.

Module PSOCALLP.
Import PSOCALL.

Definition a1_ok (nx : nat) (cells : list kentry) (e : expr) : bool :=
  match e with ELit z => ((0 <=? z) && (z <? 256))%bool | EVar _ => PSOCK.kr_ok nx cells (KRange e 0 255) | _ => false end.
Definition st_ok (c : CC.cutpoint) (cells : list kentry) : bool :=
  match PSO.pview (CC.cp_know c) with
  | Some t => match PSO.tst c cells t with Some z => ((1 <=? z) && (z <=? 28) && negb (z =? 17))%bool | None => false end
  | None => false end.
Definition pb_leaf (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) : bool :=
  let cells := SR.ps_cells ps in
  (kinb (PSO.kind_of i) [PSO.KCsl] && expr_eqb (PSO.reg_of ps 10) (EAlu Instr.ALU_ADD (EVar 10) (ELit 224))
   && a1_ok (CC.cp_nx c) cells (PSO.reg_of ps 11) && expr_eqb (nth 11 (CA.ps_reglist ps) (ELit 0)) (PSO.reg_of ps 11)
   && bshz_ok i && expr_eqb (snd (PSO.blk0 i)) (APC.escale 2 (EVar 54)) && stk_ok i && more1 c cells && st_ok c cells
   && match CAX.cell_at cells (EVar 10) 232 8 with Some (ELit 0) => true | _ => false end && PSO.lo_ge (CC.cp_know c) (EVar JV) 1
   && negb (PSO.u0 i) && match PSO.pview cells with Some l => expr_eqb (PSO.v_wptr l) PSO.CURH | None => false end)%bool.
Definition pb_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (tg : CC.tag) : bool :=
  match tg with CC.TOther pc => if Z.eqb pc PUSHB then (PSO.dead_chk i ps pc || pb_leaf i c ps)%bool else true | CC.TGoto _ _ => true end.
Lemma PB_all : CH2.leaves_all G.CPS G.TAGS pb_chk = true. Proof. vmc_refl. Qed.
Lemma PB : forall i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther PUSHB) -> PSO.dead_chk i ps0 PUSHB = false -> pb_leaf i c ps0 = true.
Proof.
  intros i c k ps0 IL Hd. pose proof (CH2.leaves_all_sound _ _ _ PB_all _ _ _ _ _ IL) as X. cbn [pb_chk] in X. rewrite Z.eqb_refl, Hd in X. exact X.
Qed.

Lemma LOGEb : forall segs E (Mv : mem) kn e v, know_ok segs E Mv kn -> PSO.lo_ge kn e v = true -> v <= CL5A.uv E e.
Proof.
  intros segs E Mv kn e v HK H. unfold PSO.lo_ge in H. destruct (CX.range3 kn e) as [[a b]|] eqn:HR; [|discriminate H].
  apply Z.leb_le in H. pose proof (CX.range3_sound _ _ _ _ _ _ _ HK HR) as X. unfold CL5A.uv. lia.
Qed.

Definition PBNEWS (regs : list expr) (cells : list kentry) (g : nat) : list kentry :=
  [KWord (SA (EVar g) (0)) 1 (nth 11 regs (ELit 0)); KWord (SA (EVar 10) (224)) 8 (APC.eaddz (APC.escale (2) (EVar (g + 1))) (1)); KWord (SA (EVar 10) (232)) 8 (APC.eaddz (match CAX.cell_at cells (EVar 10) 232 8 with Some e => e | None => ELit 0 end) (1)); KWord (SA (EVar 10) (240)) 8 (EVar g); KRange (EVar (g + 1)) (132) (67108864); KRange (APC.esub (APC.eaddz (APC.escale (2) (EVar (g + 1))) (-1)) (APC.eaddz (match CAX.cell_at cells (EVar 10) 232 8 with Some e => e | None => ELit 0 end) (1))) (0) (140737488355328); KAlign (APC.escale (2) (EVar (g + 1))) (8); KWord (SA (APC.eadd (APC.eaddz (match CAX.cell_at cells (EVar 10) 232 8 with Some e => e | None => ELit 0 end) (1)) (EVar g)) (0)) 1 (ELit (0)); KWr (SA (EVar g) (0)) (APC.escale (2) (EVar (g + 1))); KRange (EVar g) (4096) (140737479966720); KAlign (EVar g) (16); KZero (SA (EAlu Instr.ALU_SRL (EVar g) (ELit 3)) 2147450880) (ELit 33); KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar g) (0)) (APC.escale (2) (EVar (g + 1))); KDisj (SA (EVar g) (0)) (APC.escale (2) (EVar (g + 1))) (SA (ELit 0) 65536) (ELit 6963200); KDisj (SA (EVar g) (0)) (APC.escale (2) (EVar (g + 1))) (SA (EVar 57) (0)) (EVar 59); KDisj (SA (EVar 2) (-10496)) (ELit (10496)) (SA (EVar g) (0)) (APC.escale (2) (EVar (g + 1))); KDisj (SA (EVar 10) (0)) (ELit (272)) (SA (EVar g) (0)) (APC.escale (2) (EVar (g + 1))); KDisj (SA (EVar 12) (0)) (ELit (16)) (SA (EVar g) (0)) (APC.escale (2) (EVar (g + 1))); KDisj (SA (EVar 11) (0)) (ELit (8)) (SA (EVar g) (0)) (APC.escale (2) (EVar (g + 1))); KDisj (SA (EVar 11) (8)) (ELit (40)) (SA (EVar g) (0)) (APC.escale (2) (EVar (g + 1))); KDisj (SA (EVar 65) (0)) (ELit (1024)) (SA (EVar g) (0)) (APC.escale (2) (EVar (g + 1))); KDisj (SA (EVar 60) (0)) (ELit (1)) (SA (EVar g) (0)) (APC.escale (2) (EVar (g + 1))); KDisj (SA (EVar 36) (0)) (EVar 32) (SA (EVar g) (0)) (APC.escale (2) (EVar (g + 1))); KDisj (SA (EVar g) (0)) (APC.escale (2) (EVar (g + 1))) (SA (ELit 0) 6882184) (ELit 2); KDisj (SA (EVar g) (0)) (APC.escale (2) (EVar (g + 1))) (SA (ELit 0) 7020000) (ELit 544); KDisj (SA (EVar g) (0)) (APC.escale (2) (EVar (g + 1))) (SA (ELit 0) 6888684) (ELit 4); KDisj (SA (EAlu Instr.ALU_SRL (EVar g) (ELit 3)) 2147450880) (ELit 33) (SA (EVar 12) (0)) (ELit (16)); KDisj (SA (EAlu Instr.ALU_SRL (EVar g) (ELit 3)) 2147450880) (ELit 33) (SA (ELit (0)) (6882184)) (ELit (2)); KDisj (SA (EAlu Instr.ALU_SRL (EVar g) (ELit 3)) 2147450880) (ELit 33) (SA (ELit (0)) (7020000)) (ELit (544)); KDisj (SA (EAlu Instr.ALU_SRL (EVar g) (ELit 3)) 2147450880) (ELit 33) (SA (ELit (0)) (6888684)) (ELit (4)); KDisj (SA (EAlu Instr.ALU_SRL (EVar 65) (ELit 3)) 2147450880) (ELit 128) (SA (EAlu Instr.ALU_SRL (EVar g) (ELit 3)) 2147450880) (ELit 33); KDisj (SA (EAlu Instr.ALU_SRL (EVar g) (ELit 3)) 2147450880) (ELit 33) (SA (EAlu Instr.ALU_SRL (EVar 57) (ELit 3)) 2147450880) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 59) (7)) (ELit 3))].
Lemma PBNEWS_in : forall regs cells g xl xwe xwp xst xsst xnst xmore xdone xslen X,
  In X (PBNEWS regs cells g) ->
  X = KWord (SA (EVar g) (0)) 1 (nth 11 regs (ELit 0)) \/
  In X (PSOK.PSTATE xl xwe xwp xst xsst xnst xmore xdone (EVar (g + 1)) (APC.eaddz (match CAX.cell_at cells (EVar 10) 232 8 with Some e => e | None => ELit 0 end) (1))
          (EVar g) (EVar 57) xslen (EVar 59)
        ++ PSOK.BLOCKS_KN (EVar (g + 1)) (APC.eaddz (match CAX.cell_at cells (EVar 10) 232 8 with Some e => e | None => ELit 0 end) (1)) (EVar g) (EVar 57) xslen (EVar 59) xl
        ++ PSOK.BLOCKS_KDISJ_F (EVar g) (EVar (g + 1)) (EVar 57) (EVar 59)).
Proof.
  intros regs cells g xl xwe xwp xst xsst xnst xmore xdone xslen X H. unfold PBNEWS in H. cbn [In] in H.
  destruct H as [<-|H]; [left; reflexivity|]. right. unfold PSOK.PSTATE, PSOK.BLOCKS_KN, PSOK.BLOCKS_KDISJ_F. cbn [app].
  repeat (destruct H as [<-|H]; [cbn [In]; repeat (first [left; reflexivity | right]) |]).
  destruct H.
Qed.

Section C.
Context {SCFG_P : ScfgP}.
Variable I : PSOI.inst.
Local Abbreviation L := (PSOI.iL I).     Local Abbreviation ar := (PSOI.iar I).    Local Abbreviation C := (PSOI.iC I).     Local Abbreviation HI := (PSOI.iHI I).
Local Abbreviation LBo := (PSOI.iLBo I). Local Abbreviation FF := (PSOI.iFF I).    Local Abbreviation LK := (PSOI.iLK I).   Local Abbreviation A := (PSOI.iA I).
Local Abbreviation sp := (PSOI.isp I).   Local Abbreviation P := (PSOI.iP I).      Local Abbreviation V := (PSOI.iV I).     Local Abbreviation E := (PSOI.iE I).
Local Abbreviation B := (PSOI.iB I).     Local Abbreviation M := (PSOI.iM I).      Local Abbreviation model := (PSOI.imodel I). Local Abbreviation K := (PSOI.iK I).
Local Abbreviation HIok := (PSOI.iHIok I).
Local Abbreviation E0 := (PSOI.E0 I).      Local Abbreviation WW := (WW I).            Local Abbreviation Wo := (Wo I).         Local Abbreviation Cred := (PSOX.Cred I). Local Abbreviation XI := (PSOX.XI I).
Local Abbreviation bptrI := (PSOX.bptrI).  Local Abbreviation bcapI := (PSOX.bcapI). Local Abbreviation sbI := (PSOX.sbI). Local Abbreviation scapI := (PSOX.scapI).

Lemma ACL_RM1 : forall x l FFx spx scr a, aclient L ar (x :: l) FFx spx scr a -> ~ (fst x <= a < fst x + snd x) -> ~ in_shadow_of (fst x) (snd x) a ->
  aclient L ar l FFx spx scr a.
Proof.
  intros x l FFx spx scr a Hc N1 N2. unfold aclient, aclient_g, in_block in *.
  destruct Hc as [(b & Hb & Xb)|[Hc|[Hc|[Hc|[Hc|[Hc|(b & Hb & Xb)]]]]]].
  - left. exists b. split; [|exact Xb]. destruct Hb as [<-|Hb]; [contradiction (N1 Xb) | exact Hb].
  - right; left; exact Hc.
  - right; right; left; exact Hc.
  - do 3 right; left; exact Hc.
  - do 4 right; left; exact Hc.
  - do 5 right; left; exact Hc.
  - do 6 right. exists b. split; [|exact Xb]. destruct Hb as [<-|Hb]; [contradiction (N2 Xb) | exact Hb].
Qed.

Lemma GEO_B : forall i E1 A1 M1 m1 a, (2 <= i < PSO.NCUT)%nat -> AAMB I i E1 A1 M1 m1 ->
  ((P <= a < P + 272) \/ (E <= a < E + 16) \/ STATIC a \/ (sbI i E1 <= a < sbI i E1 + scapI i E1) \/ in_shadow_of (sbI i E1) (scapI i E1) a
   \/ (exists u n, In (u, n) LBo /\ (u <= a < u + n \/ in_shadow_of u n a))) ->
  ~ (bptrI i E1 <= a < bptrI i E1 + bcapI i E1) /\ ~ in_shadow_of (bptrI i E1) (bcapI i E1) a.
Proof.
  intros i E1 A1 M1 m1 a Hi HA Ha. pose_facts I.
  pose proof (PSOI.iAP2 I) as AP2. unfold PMLA.apart in AP2. unfold hid in O5, O7, Q5.
  destruct (FRM I i E1 A1 M1 m1 Hi HA) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (crX & LKX & HHX & _)).
  set (bp := bptrI i E1) in *. set (bc := bcapI i E1) in *. set (sb := sbI i E1) in *. set (sc := scapI i E1) in *.
  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HHX) as WFX.
  destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WFX (bp, bc) ltac:(left; reflexivity)) as ((T0 & T1 & T16 & T3 & T4 & (T5 & T6 & T7)) & _ & _ & Tbap & Tfap).
  cbn [fst snd lb_remove app] in *. rewrite Z.eqb_refl in Tbap. unfold BIGSHADOW_LO, BIGSHADOW_HI in T6.
  destruct Pfr as (fP & HfP & FP1 & FP2). destruct Efr as (fE & HfE & FE1 & FE2).
  pose proof (Tfap fP ltac:(right; apply in_or_app; left; exact HfP)) as TPF. pose proof (Tfap fE ltac:(right; apply in_or_app; left; exact HfE)) as TEF.
  assert (BK : forall u n, In (u, n) ([(bp, bc); (sb, sc)] ++ LBo) -> 0 <= u /\ 0 < n /\ u + n <= 2 ^ 47 /\ u mod 8 = 0 /\ (u + n <= 2147446784 \/ 17594333495296 <= u)).
  { intros u n Hun. destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WFX (u, n) Hun) as ((D0 & D1 & D16 & D3 & D4 & (D5 & D6 & D7)) & _).
    cbn [fst snd] in *. unfold BIGSHADOW_LO, BIGSHADOW_HI in D6.
    split; [exact D5|]. split; [exact D3|]. split; [exact D7|]. split; [exact (CHA.mod8_of_16 _ D16) | exact D6]. }
  assert (NSH : forall x, in_shadow_of bp bc x -> 2147450880 <= x < 17594333495296) by (intros x Hx; exact (SHR bp bc x T5 T3 T7 Hx)).
  destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|(u & n & Hun & Ha)]]]]].
  - split; [clear - Ha TPF FP1 FP2; lia|]. intros Hs. pose proof (NSH a Hs). clear - H Ha O5. lia.
  - split; [clear - Ha TEF FE1 FE2; lia|]. intros Hs. pose proof (NSH a Hs). clear - H Ha Q5. lia.
  - pose proof (proj1 (IMGCL I a Ha)) as RG. rewrite ILO, IHI in O7, T1.
    split; [clear - RG T1; lia|]. intros Hs; pose proof (NSH a Hs); clear - H RG; lia.
  - destruct (BK sb sc ltac:(right; left; reflexivity)) as (B0 & B1 & B2 & B3 & B4). pose proof (Tbap (sb, sc) ltac:(left; reflexivity)) as AB. cbn [fst snd] in AB.
    split; [clear - Ha AB; lia|]. intros Hs; pose proof (NSH a Hs); clear - H Ha B4; lia.
  - destruct (BK sb sc ltac:(right; left; reflexivity)) as (B0 & B1 & B2 & B3 & B4). pose proof (SHR sb sc a B0 B1 B2 Ha) as RG.
    pose proof (Tbap (sb, sc) ltac:(left; reflexivity)) as AB. cbn [fst snd] in AB.
    split; [clear - RG T6; lia|]. intros Hs.
    exact (CL5A.sh_apart2 bp bc sb sc a T5 B0 T3 B1 (CHA.mod8_of_16 _ T16) B3 AB Hs Ha).
  - destruct (BK u n ltac:(right; right; exact Hun)) as (B0 & B1 & B2 & B3 & B4). pose proof (Tbap (u, n) ltac:(right; exact Hun)) as AB. cbn [fst snd] in AB.
    destruct Ha as [Ha|Ha].
    + split; [clear - Ha AB; lia|]. intros Hs; pose proof (NSH a Hs); clear - H Ha B4; lia.
    + pose proof (SHR u n a B0 B1 B2 Ha) as RG. split; [clear - RG T6; lia|]. intros Hs.
      exact (CL5A.sh_apart2 bp bc u n a T5 B0 T3 B1 (CHA.mod8_of_16 _ T16) B3 AB Hs Ha).
Qed.

Lemma AG_B : forall i E1 A1 M1 m1 (Mx M2 : mem) scr Wc, (2 <= i < PSO.NCUT)%nat -> AAMB I i E1 A1 M1 m1 ->
  CHA.ahpres L ar ((sbI i E1, scapI i E1) :: LBo) (CHA.curF FF sp PSO.FFS i E1) (sp + PSO.CSP) scr Wc Mx M2 -> 672 + scr <= 10496 ->
  forall a, SUPP I (bptrI i E1) (bcapI i E1) (sbI i E1) (scapI i E1) a -> ~ (bptrI i E1 <= a < bptrI i E1 + bcapI i E1) -> ~ in_shadow_of (bptrI i E1) (bcapI i E1) a ->
  (L5.outside Wc a -> M2 (Z_to_bv 64 a) = Mx (Z_to_bv 64 a)) /\ (Mx (Z_to_bv 64 a) <> None -> M2 (Z_to_bv 64 a) <> None).
Proof.
  intros i E1 A1 M1 m1 Mx M2 scr Wc Hi HA HP Hs1 a Ha N1 N2. destruct (SUPP_geom I i E1 A1 M1 m1 a Hi HA Ha) as (RG & X1 & _ & _ & X4 & _).
  destruct (FRM I i E1 A1 M1 m1 Hi HA) as (HcB & _). rewrite HcB in X4. cbn [app] in X4.
  pose proof (ACL_RM1 (bptrI i E1, bcapI i E1) ((sbI i E1, scapI i E1) :: LBo) _ _ _ a X4 N1 N2) as X5.
  assert (X6 : aclient L ar ((sbI i E1, scapI i E1) :: LBo) (CHA.curF FF sp PSO.FFS i E1) (sp + PSO.CSP) scr a).
  { apply (CHA.aclient_scr_pt _ _ _ _ _ _ (sp + PSO.CSP) 256); [exact X5 | unfold PSO.CSP, SCR in *; clear - X1 Hs1; lia]. }
  split.
  - intros HW. apply (proj1 HP a). split; [exact RG|]. split; [exact X6 | exact HW].
  - intros Hd. exact (proj2 (proj2 HP) a RG X6 Hd).
Qed.
Lemma W_S_out : forall a, ~ (P + 224 <= a < P + 248) -> L5.outside [(P + 224, 24)] a.
Proof. intros a N r Hr Hin. cbn [In] in Hr. destruct Hr as [<-|[]]. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. apply N. lia. Qed.

Lemma PA_STR : forall (M1 M2 : mem) (Sg : Z -> Prop), (forall a, Sg a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  forall psx mw buf',
  PTA.out Sg P 224 -> PTA.out Sg (P + 248) 24 -> PTA.out Sg (PML.ps_sb psx) (Z.of_nat (length (PML.ps_stack psx))) -> PMLA.parser_at (hl_segs L) IC M1 P (PML.ps_set_win psx mw) ->
  PMLA.str_at (hl_segs L) M2 (P + 224) (PML.SLong (PML.ps_bcap psx) (PML.ps_bptr psx) buf') -> (forall k, 0 <= k < 272 -> M2 (Z_to_bv 64 (P + k)) <> None) ->
  PMLA.parser_at (hl_segs L) IC M2 P (PML.ps_set_win (PML.PS (PML.ps_st psx) (PML.ps_sst psx) (PML.ps_nst psx) (PML.ps_more psx) (PML.ps_done psx) (PML.ps_level psx)
                                                     (PML.ps_stack psx) (PML.ps_sb psx) (PML.ps_scap psx) (PML.ps_bcap psx) (PML.ps_bptr psx) buf' (PML.ps_win psx)) mw).
Proof.
  intros M1 M2 Sg AG psx mw buf' O0 O1 OS H HSTR HDEF.
  unfold PMLA.parser_at, PMLA.u64, PMLA.u32, PMLA.u8 in *. destruct psx; cbn in H, OS, HSTR |- *.
  destruct H as (A0 & A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27 & A28 & A29 & A30).
  pose proof (PTA.u64_ag (hl_segs L) M1 M2 Sg AG) as U64. pose proof (PTA.u32_ag (hl_segs L) M1 M2 Sg AG) as U32. pose proof (PTA.u8_ag (hl_segs L) M1 M2 Sg AG) as U8.
  split; [apply U64; [apply (PTA.out_sub _ _ _ _ _ O0); lia | exact A0]|].
  split; [apply U32; [apply (PTA.out_sub _ _ _ _ _ O0); lia | exact A1]|].
  split; [apply U8; [apply (PTA.out_sub _ _ _ _ _ O0); lia | exact A2]|]. split; [apply U8; [apply (PTA.out_sub _ _ _ _ _ O0); lia | exact A3]|].
  split; [apply U8; [apply (PTA.out_sub _ _ _ _ _ O0); lia | exact A4]|]. split; [apply U8; [apply (PTA.out_sub _ _ _ _ _ O0); lia | exact A5]|].
  split; [apply U8; [apply (PTA.out_sub _ _ _ _ _ O0); lia | exact A6]|]. split; [apply U8; [apply (PTA.out_sub _ _ _ _ _ O0); lia | exact A7]|].
  split; [apply U8; [apply (PTA.out_sub _ _ _ _ _ O0); lia | exact A8]|].
  split; [apply (PTA.lstr_short_nil_ag (hl_segs L) M1 M2 Sg AG); [apply (PTA.out_sub _ _ _ _ _ O0); lia | exact A9]|].
  split; [apply (PTA.lstr_short_nil_ag (hl_segs L) M1 M2 Sg AG); [apply (PTA.out_sub _ _ _ _ _ O0); lia | exact A10]|].
  split; [apply (PTA.lstr_short_nil_ag (hl_segs L) M1 M2 Sg AG); [apply (PTA.out_sub _ _ _ _ _ O0); lia | exact A11]|].
  split; [apply U64; [apply (PTA.out_sub _ _ _ _ _ O0); lia | exact A12]|]. split; [apply U64; [apply (PTA.out_sub _ _ _ _ _ O0); lia | exact A13]|].
  split; [apply U32; [apply (PTA.out_sub _ _ _ _ _ O0); lia | exact A14]|].
  split.
  { destruct mw as [[p e]|]; [destruct A15 as (Y1 & Y2 & Y3) | destruct A15 as (Y1 & Y2)];
      [split; [apply U64; [apply (PTA.out_sub _ _ _ _ _ O0); lia | exact Y1] | split; [apply U64; [apply (PTA.out_sub _ _ _ _ _ O0); lia | exact Y2] | exact Y3]]
      | split; [apply U64; [apply (PTA.out_sub _ _ _ _ _ O0); lia | exact Y1] | apply U64; [apply (PTA.out_sub _ _ _ _ _ O0); lia | exact Y2]]]. }
  split; [apply U8; [apply (PTA.out_sub _ _ _ _ _ O0); lia | exact A16]|]. split; [apply U8; [apply (PTA.out_sub _ _ _ _ _ O0); lia | exact A17]|].
  split; [apply U8; [apply (PTA.out_sub _ _ _ _ _ O0); lia | exact A18]|]. split; [apply U8; [apply (PTA.out_sub _ _ _ _ _ O0); lia | exact A19]|].
  split; [apply U8; [apply (PTA.out_sub _ _ _ _ _ O0); lia | exact A20]|]. split; [apply U8; [apply (PTA.out_sub _ _ _ _ _ O0); lia | exact A21]|].
  split; [apply U32; [apply (PTA.out_sub _ _ _ _ _ O0); lia | exact A22]|].
  split; [exact HSTR|].
  split; [exact A24|].
  split; [apply U64; [apply (PTA.out_sub _ _ _ _ _ O1); lia | exact A25]|]. split; [apply U64; [apply (PTA.out_sub _ _ _ _ _ O1); lia | exact A26]|].
  split; [apply U64; [apply (PTA.out_sub _ _ _ _ _ O1); lia | exact A27]|].
  split; [apply (PTA.bytes_ag (hl_segs L) M1 M2 Sg AG); [exact OS | exact A28]|]. split; [exact A29|].
  exact HDEF.
Qed.

Lemma A1V : forall c ps0 E' R' A1 M1 m1 M' m' e, CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' -> a1_ok (CC.cp_nx c) (SR.ps_cells ps0) e = true ->
  0 <= CL5A.uv E' e < 256 /\ e <> ELit (-1).
Proof.
  intros c ps0 E' R' A1 M1 m1 M' m' e HLF H. unfold a1_ok in H. destruct e as [z | v | op1 x1 y1 | op1 x1 y1 | op1 x1 y1 | op1 x1 y1 | s1 l1 n1 e1 | s1 k1 i1 n1]; try discriminate H.
  - apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    split; [unfold CL5A.uv; cbn [edenot]; rewrite L5.unsigned_lit by lia; lia | intros X; injection X as X; lia].
  - unfold PSOCK.kr_ok in H. apply andb_prop in H as [H1 _].
    pose proof (PROVE I prove_std c ps0 E' R' A1 M1 m1 M' m' (EVar v) 0 255 prove_std_ok HLF H1) as X. split; [lia | discriminate].
Qed.
Lemma A1AG : forall nx cells e (Ex Ey : env), a1_ok nx cells e = true -> env_agree nx Ex Ey -> CL5A.uv Ey e = CL5A.uv Ex e.
Proof.
  intros nx cells e Ex Ey H Hag. unfold a1_ok in H. destruct e as [z | v | op1 x1 y1 | op1 x1 y1 | op1 x1 y1 | op1 x1 y1 | s1 l1 n1 e1 | s1 k1 i1 n1]; try discriminate H.
  - reflexivity.
  - unfold PSOCK.kr_ok in H. apply andb_prop in H as [_ H]. cbn [APC.expr_vars_lt] in H. apply Nat.ltb_lt in H.
    unfold CL5A.uv. cbn [edenot]. rewrite <- (proj1 Hag v H). reflexivity.
Qed.
Lemma W224_of : forall (Ex : env), bv_unsigned (ev Ex 10) = P -> bv_unsigned (edenot Ex (EAlu Instr.ALU_ADD (EVar 10) (ELit 224))) = P + 224.
Proof.
  intros Ex H. pose_facts I. cbn [edenot]. fold (CL5A.uv Ex (EAlu Instr.ALU_ADD (EVar 10) (ELit 224))).
  unfold CL5A.uv. cbn [edenot]. rewrite u_add64, H, u_lit64. rewrite Zplus_mod_idemp_r. apply Z.mod_small. clear - O3 O6. lia.
Qed.

Lemma PB_WIN : forall i c ps0 E1 R1 A1 M1 m1 E' R' M' m' l ps2 g1,
  nth_error G.CPS i = Some c -> (2 <= i < PSO.NCUT)%nat -> PSO.u0 i = false -> PSOX.wlk (PSO.kind_of i) = true ->
  CCA.AtV (hl_segs L) c E1 R1 A1 M1 m1 -> AAMB I i E1 A1 M1 m1 -> env_agree (CC.cp_nx c) E1 E' -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' ->
  PSO.pview (SR.ps_cells ps0) = Some l -> PSO.v_wptr l = PSO.CURH -> PSO.lo_ge (CC.cp_know c) (EVar JV) 1 = true ->
  PSOX.CORE I i E1 M' (PML.ps_win ps2) ps2 0 g1 ->
  exists p, PML.ps_win ps2 = Some (p, PSOI.we0 I) /\ PSOI.wp0 I <= p /\ p + 1 <= PSOI.we0 I.
Proof.
  intros i c ps0 E1 R1 A1 M1 m1 E' R' M' m' l ps2 g1 Hci Hi HU HW HAt HA Hag HLF Hl HCU HJ CO2.
  pose_U I. pose proof (PSOST.nx66 i c Hi Hci) as NX.
  pose proof (PSOX.c_wl _ _ _ _ _ _ _ _ CO2 HU HW) as WL.
  pose proof (WINF I) as (WI0 & WI1 & WI2 & _ & _ & _ & WI6 & _).
  pose proof (PSOX.c_win _ _ _ _ _ _ _ _ CO2) as WN2. unfold PSOX.WIN in WN2.
  destruct (PML.ps_win (PSOI.ips I)) as [[p0 e0]|] eqn:Hw0; [|exfalso; pose proof (PSOI.WNONE I Hw0) as (_ & _ & W0 & _); clear - W0 WL; lia].
  pose proof (PSOI.WSOME I p0 e0 Hw0) as (WS1 & WS2 & _). destruct WN2 as (p & Hp & Rp). exists p.

  assert (CUR : p = CL5A.uv E' (PSO.v_wptr l)).
  { pose proof (CBA.amb_off L ar C HI HIok (LYB I) GT.NF E0 M model A LBo FF LK sp G.HDECL WW G.BLS PSO.FFS Cred 6 i E1 A1 M1 m1 HA) as Hoff.
    rewrite <- (L5LZ.sbm_ahid A1 m1 m' (CCA.lfa_sbm _ _ _ _ _ _ _ _ _ _ HLF)) in Hoff.
    destruct (PSOST.cut_env I i E1 A1 M1 m1 Hi HA) as (U10E1 & _).
    assert (W10 : bv_unsigned (ev E' 10) = P) by (rewrite <- (proj1 Hag 10%nat) by (clear - NX; lia); exact U10E1).
    assert (KL : forall X, In X (SR.ps_cells ps0) -> kentry_ok (hl_segs L) E' (CCA.vis A1 m' M') X)
      by (intros X HX; exact (CC.lf_cells _ _ _ _ _ _ _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) _ HX)).
    pose proof (PSOLK.VIEW_RD I E' A1 m' M' _ l Hoff W10 KL Hl) as VR.
    destruct (PSOLK.PA_cells I M' ps2 (PML.ps_win ps2) (PSOX.c_pa _ _ _ _ _ _ _ _ CO2)) as (_ & _ & _ & _ & _ & Awlo & _). rewrite Hp in Awlo. cbn [PSOI.wlo] in Awlo.
    apply (U64INJ I M' (P + 200)); [exact Awlo | exact (PSOLK.vr_wptr _ _ _ _ VR) | | apply CL5A.uv_range].
    clear - Rp WS1 WS2 WI0 WI1 WI6. unfold PSOI.wlen in *. lia. }

  destruct (FRM I i E1 A1 M1 m1 Hi HA) as (_ & _ & HagE1 & _).
  assert (U32' : CL5A.uv E' WLEN = PSOI.wlen I).
  { unfold CL5A.uv, WLEN, WLENV. cbn [edenot]. rewrite <- (proj1 Hag 32%nat) by (clear - NX; lia). rewrite <- (proj1 HagE1 32%nat) by (unfold GT.NF, Cut_psome_cboth_T.NF; clear; lia). exact U32. }
  assert (U36' : CL5A.uv E' WP0 = PSOI.wp0 I).
  { unfold CL5A.uv, WP0, WP0V. cbn [edenot]. rewrite <- (proj1 Hag 36%nat) by (clear - NX; lia). rewrite <- (proj1 HagE1 36%nat) by (unfold GT.NF, Cut_psome_cboth_T.NF; clear; lia). exact U36. }
  assert (KT : know_ok (hl_segs L) E1 (CCA.vis A1 m1 M1) (CC.cp_know c)) by (destruct HAt as [_ HK]; exact HK).
  pose proof (LOGEb _ _ _ _ _ _ KT HJ) as J1.
  assert (U46' : CL5A.uv E' (EVar JV) = CL5A.uv E1 (EVar JV)) by (unfold CL5A.uv, JV; cbn [edenot]; rewrite <- (proj1 Hag 46%nat) by (clear - NX; lia); reflexivity).
  pose proof (CL5A.uv_range E1 (EVar JV)) as RJ.
  rewrite HCU, PSOCK.uv_CURH, U32', U36', U46' in CUR.
  replace (PSOI.wlen I + PSOI.wp0 I) with (PSOI.we0 I) in CUR by (unfold PSOI.wlen; clear; lia).
  split; [rewrite Hp, WS2; reflexivity|].
  destruct (Z_le_gt_dec (CL5A.uv E1 (EVar JV)) (PSOI.we0 I)) as [G|G].
  - rewrite Z.mod_small in CUR by (clear - G RJ WS2 WI0 WI1 WI6; unfold PSOI.wlen in *; lia). clear - CUR Rp J1 G WS1 WS2. split; lia.
  - exfalso. rewrite <- (Z.mod_add _ 1 (2 ^ 64)) in CUR by lia. rewrite Z.mod_small in CUR by (clear - G RJ WS2 WI0 WI1 WI2 WI6; unfold PSOI.wlen in *; lia).
    clear - CUR Rp G RJ WS1 WS2 WI0 WI1 WI2 WI6. unfold PSOI.wlen in *. lia.
Qed.

Lemma SG_PB : forall i E1 A1 M1 m1 a, (2 <= i < PSO.NCUT)%nat -> AAMB I i E1 A1 M1 m1 ->
  ((P <= a < P + 224) \/ (P + 248 <= a < P + 272) \/ (E <= a < E + 16) \/ STATIC a \/ (sbI i E1 <= a < sbI i E1 + scapI i E1) \/ in_shadow_of (sbI i E1) (scapI i E1) a) ->
  SUPP I (bptrI i E1) (bcapI i E1) (sbI i E1) (scapI i E1) a /\ ~ (P + 224 <= a < P + 248) /\ ~ (bptrI i E1 <= a < bptrI i E1 + bcapI i E1) /\ ~ in_shadow_of (bptrI i E1) (bcapI i E1) a.
Proof.
  intros i E1 A1 M1 m1 a Hi HA Ha.
  assert (GB : ~ (bptrI i E1 <= a < bptrI i E1 + bcapI i E1) /\ ~ in_shadow_of (bptrI i E1) (bcapI i E1) a).
  { apply (GEO_B i E1 A1 M1 m1 a Hi HA). destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]]; [left; lia | left; lia | right; left; exact Ha | do 2 right; left; exact Ha | do 3 right; left; exact Ha | do 4 right; left; exact Ha]. }
  pose_facts I. pose proof (PSOI.iAP2 I) as AP2. unfold PMLA.apart in AP2. unfold hid in O5, O7.
  destruct (FRM I i E1 A1 M1 m1 Hi HA) as (HcB & _ & _ & _ & _ & _ & _ & _ & _ & _ & (crX & LKX & HHX & _)).
  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HHX) as WFX.
  destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WFX (sbI i E1, scapI i E1) ltac:(right; left; reflexivity)) as ((T0 & T1 & T16 & T3 & T4 & (T5 & T6 & T7)) & _ & _ & _ & Tfap).
  cbn [fst snd] in *. unfold BIGSHADOW_LO, BIGSHADOW_HI in T6.
  destruct Pfr as (fP & HfP & FP1 & FP2). pose proof (Tfap fP ltac:(right; apply in_or_app; left; exact HfP)) as TPF.
  split; [|split; [|exact GB]].
  - destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]]; [left; lia | left; lia | right; left; exact Ha | do 6 right; left; exact Ha | do 4 right; left; exact Ha | do 5 right; left; exact Ha].
  - destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]].
    + clear - Ha. lia.
    + clear - Ha. lia.
    + clear - Ha AP2. lia.
    + pose proof (proj1 (IMGCL I a Ha)) as RG. rewrite ILO, IHI in O7. clear - RG O7. lia.
    + clear - Ha TPF FP1 FP2. lia.
    + pose proof (SHR _ _ a T5 T3 T7 Ha) as RG. clear - RG O5. lia.
Qed.

Lemma WF_PB : forall psx buf' w', PML.wf_ps psx -> PML.ps_st psx <> PML.ST_NUMBER ->
  PML.wf_ps (PML.PS (PML.ps_st psx) (PML.ps_sst psx) (PML.ps_nst psx) (PML.ps_more psx) (PML.ps_done psx) (PML.ps_level psx) (PML.ps_stack psx) (PML.ps_sb psx)
                    (PML.ps_scap psx) (PML.ps_bcap psx) (PML.ps_bptr psx) buf' w').
Proof.
  intros psx buf' w' H HS. destruct psx. unfold PML.wf_ps in *. cbn in *.
  destruct H as (W1 & W2 & W3 & W4 & C0 & T & HS0 & HC & HM). split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|].
  exists C0, T. split; [exact HS0|]. split; [exact HC|]. intros Hm. destruct (HM Hm) as (M1 & M2 & M3 & M4 & M5 & _).
  split; [exact M1|]. split; [exact M2|]. split; [exact M3|]. split; [exact M4|]. split; [exact M5|]. intros X. contradiction.
Qed.

Lemma XI_PB : forall j E2 (M2 : mem) ps3 p e g1 cx, PSO.kind_of j = PSO.KPushb -> PSOX.FLF I E2 ->
  PSOX.CORE I j E2 M2 (Some (p, e)) ps3 0 g1 -> PML.ps_win ps3 = Some (p + 1, e) -> PMCUR.wf_c ps3 -> PML.ps_more ps3 = true -> PML.ps_st ps3 <> PML.ST_NUMBER ->
  PML.ps_buf ps3 = [cx] -> PSOX.XI_R I j E2 M2.
Proof.
  intros j E2 M2 ps3 p e g1 cx HK HFL CO HW WF Hm HS HB.
  constructor; try (intros _; exact HFL); try (intros Hk; exfalso; rewrite HK in Hk; first [discriminate Hk | destruct Hk as [Hk|Hk]; discriminate Hk]);
    try (intros pc0 Hk; exfalso; rewrite HK in Hk; discriminate Hk).
  intros _. exists ps3, p, e, g1, cx. split; [exact CO|]. split; [exact HW|]. split; [exact WF|]. split; [exact Hm|]. split; [exact HS | exact HB].
Qed.

Lemma L_PUSHB : forall i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther PUSHB) -> PSO.call_chk i c k ps0 PUSHB = true -> PSO.dead_chk i ps0 PUSHB = false ->
  CCA.leaf_ok (hl_segs L) G.CPS (AMBX I) K PMSA.fp_ok i c ps0.
Proof.
  intros i c k ps0 IL CHK HD. pose_facts I. pose_U I. pose proof (PSOI.VV I) as (_ & V4 & _).
  destruct (PSOCK.CALL_UNPACK PUSHB PSOK.XS_PUSHB i c k ps0 IL CHK HD eq_refl) as (j & cj & ci & Hret & CU).
  destruct CU as [Hci Hcj Hpc HKj HND Hchk Hcsp Hblk HFj HPC].
  change (CAX.xs_scr (PSOK.x_of PSOK.XS_PUSHB)) with 4368 in Hchk. change (CAX.xs_ng (PSOK.x_of PSOK.XS_PUSHB)) with 2%nat in Hchk.
  change (CAX.xs_keep (PSOK.x_of PSOK.XS_PUSHB) (CA.ps_reglist ps0) (nth i G.BLS [])) with (skipn 1 (nth i G.BLS [])) in Hchk, Hblk.
  change (CAX.xs_wregs (PSOK.x_of PSOK.XS_PUSHB) (CA.ps_reglist ps0)) with [((EVar 10), 224, ELit 24)] in Hchk.
  change (CAX.xs_a0 (PSOK.x_of PSOK.XS_PUSHB) (CA.ps_reglist ps0) (CH2.ci_nx ci)) with (@None expr) in Hchk.
  change (PSOK.blk_of PSOK.XS_PUSHB (CA.ps_reglist ps0) (SR.ps_cells ps0) (CH2.ci_nx ci) (skipn 1 (nth i G.BLS [])))
    with (((EVar (CH2.ci_nx ci)), (APC.escale (2) (EVar (CH2.ci_nx ci + 1)))) :: skipn 1 (nth i G.BLS [])) in Hblk.
  pose proof (PB i c k ps0 IL HD) as SIDE. unfold pb_leaf in SIDE.
  apply andb_prop in SIDE as [SIDE Scur]. apply andb_prop in SIDE as [SIDE Su0]. apply negb_true_iff in Su0.
  apply andb_prop in SIDE as [SIDE SJ1]. apply andb_prop in SIDE as [SIDE Ssz]. apply andb_prop in SIDE as [SIDE Sst]. apply andb_prop in SIDE as [SIDE Smore]. apply andb_prop in SIDE as [SIDE Sstk].
  apply andb_prop in SIDE as [SIDE Sb0]. apply andb_prop in SIDE as [SIDE Sbshz]. apply andb_prop in SIDE as [SIDE Sr11]. apply andb_prop in SIDE as [SIDE Sa1].
  apply andb_prop in SIDE as [Skind Sreg10].
  apply kinb_in in Skind. cbn [In] in Skind. destruct Skind as [Skind|[]]. apply expr_eqb_eq in Sreg10, Sr11, Sb0. unfold bshz_ok in Sbshz. apply expr_eqb_eq in Sbshz.
  unfold stk_ok in Sstk. apply andb_prop in Sstk as [Ssb Ssc]. apply expr_eqb_eq in Ssb, Ssc.
  destruct (CAX.cell_at (SR.ps_cells ps0) (EVar 10) 232 8) as [esz|] eqn:Hsz; [|discriminate Ssz].
  destruct esz as [[|zz|zz]| | | | | | | ]; try discriminate Ssz. clear Ssz.
  assert (HKj' : PSO.kind_of j = PSO.KPushb) by (rewrite HKj; reflexivity).
  assert (Hck : PSO.curk (PSO.kind_of i) = false) by (rewrite <- Skind; reflexivity).
  pose proof (ge2_of_kind i c _ Hci eq_refl ltac:(rewrite <- Skind; discriminate)) as Hi.
  pose proof (ge2_of_kind j cj _ Hcj HKj' ltac:(discriminate)) as Hj.
  assert (Hfeq : CHA.frames_eqb (nth j PSO.FFS []) (nth i PSO.FFS []) = true) by (rewrite (ffs_i i Hi), (ffs_i j Hj); reflexivity).
  destruct (PSOCK.CK_NEWS PUSHB i c k ps0 IL ltac:(cbn; tauto) HD) as (SMEAS & SFLAG).
  destruct (PSO.pview (CC.cp_know c)) as [t|] eqn:Ht; [|unfold PSO.pre_chk in HPC; rewrite Ht in HPC; discriminate HPC].
  destruct (PSO.pview (SR.ps_cells ps0)) as [l|] eqn:Hl; [|unfold PSO.pre_chk in HPC; rewrite Ht, Hl in HPC; discriminate HPC].
  pose proof (pclass_psame i c ps0 PUSHB t l HPC ltac:(discriminate) ltac:(discriminate) Ht Hl) as HCL.
  cbv beta iota in Scur. apply expr_eqb_eq in Scur.
  intros fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH. pose proof HAX as [HA HXI].
  pose proof (PSOX.xi_flf _ _ _ _ HXI (proj1 Hi)) as HFL.
  destruct (SRC I i E1 A1 M1 m1 HXI ltac:(rewrite <- Skind; cbn [In]; tauto)) as (ps1 & g1 & CO & WF).
  destruct (PSOCK.PSAME I PUSHB i c k ps0 E1 R1 A1 M1 m1 E' R' M' m' (PML.ps_win ps1) ps1 0 g1 t l IL ltac:(cbn; tauto) HD HPC Ht Hl HCL Hi Hck HAt HA Hag HLF HFL CO eq_refl WF)
    as (ps2 & CL2 & WFL & PSF).
  assert (HM2 : PML.ps_more ps2 = true).
  { rewrite (PSOCK.pf_eq _ _ _ _ _ PSF). cbn [PSOST.ps_upd PML.ps_more]. unfold more1 in Smore. rewrite Ht in Smore.
    destruct (PSOCK.more_pin c (SR.ps_cells ps0) t) as [z|] eqn:Hz; [|discriminate Smore]. destruct z as [|[| |]|]; try discriminate Smore.
    pose proof (PSOCK.pf_more _ _ _ _ _ PSF 1 Hz) as X. destruct (PML.ps_more ps1); [reflexivity | discriminate X]. }
  assert (HST2 : PML.ps_st ps2 <> PML.ST_NUMBER).
  { unfold st_ok in Sst. rewrite Ht in Sst. destruct (PSO.tst c (SR.ps_cells ps0) t) as [z|] eqn:Hz; [|discriminate Sst].
    apply andb_prop in Sst as [Sst S17]. apply andb_prop in Sst as [S1z Sz28]. apply Z.leb_le in S1z, Sz28. apply negb_true_iff, Z.eqb_neq in S17.
    assert (HM1 : PML.ps_more ps1 = true) by (rewrite (PSOCK.pf_eq _ _ _ _ _ PSF) in HM2; exact HM2).
    pose proof (PSOCK.pf_st _ _ _ _ _ PSF z Hz HM1 ltac:(clear - S1z Sz28; lia)) as Hst1.
    rewrite (PSOCK.pf_eq _ _ _ _ _ PSF). cbn [PSOST.ps_upd PML.ps_st]. rewrite Hst1. unfold PML.ST_NUMBER. exact S17. }
  destruct (LEAFK I i c ps0 E1 A1 M1 m1 E' R' M' m' Hi Hci (PSOST.cpf_of i c Hci) HA Hag HLF) as (FZ & W65 & W60 & CELLS & REGS & _).
  assert (W10 : bv_unsigned (ev E' 10) = P) by (rewrite (FZ 10%nat ltac:(clear; lia)); exact U10).
  pose proof (PSOST.nx66 i c Hi Hci) as NX.
  assert (W57 : CL5A.uv E' (EVar 57) = sbI i E1) by (unfold PSOX.sbI; rewrite Ssb; unfold CL5A.uv; cbn [edenot]; rewrite <- (proj1 Hag 57%nat) by (clear - NX; lia); reflexivity).
  assert (W59 : CL5A.uv E' (EVar 59) = scapI i E1) by (unfold PSOX.scapI; rewrite Ssc; unfold CL5A.uv; cbn [edenot]; rewrite <- (proj1 Hag 59%nat) by (clear - NX; lia); reflexivity).
  assert (W56 : CL5A.uv E' (EVar 56) = bptrI i E1) by (unfold PSOX.bptrI; rewrite Sbshz; unfold CL5A.uv; cbn [edenot]; rewrite <- (proj1 Hag 56%nat) by (clear - NX; lia); reflexivity).
  refine (CBA.callee_leaf L ar C HI HIok (LYI I) (LYR I) GT.NF E0 M model A LBo FF LK sp G.HDECL WW Wo G.BLS PSO.FFS Cred 6 (STKF I) SCRP NF32 U2 V4 (WINC I) (WOKo I) (PSOI.iHffrs I) (CRS_OKo I) (WRS_OK I) (IMG_OK I)
            G.CPS K PMSA.fp_ok (DEF0 I) S6 GT.SCELLS GT.GLO GT.GHI (SCOK I) (GOTOK I) XI (PSOI.iHKnil I)
            PUSHB 4368 2 (skipn 1 (nth i G.BLS [])) _ _ None 0 i c ps0 j cj ci Hcj Hchk Hpc Hfeq ltac:(rewrite (ffs_i i Hi); cbn; clear; lia)
            fx' E1 R1 A1 M1 m1 E' R' M' m' HAt HAX HFP Hag HLF HIH _).
  intros cr1 LK1 CF HH1 HLK1 HC1.
  destruct CF as [HAm HR Hreq HV HK' [HRA HRAok] (HSP & Hc1 & Hs0 & Hc2) HSTK HTP HagE' (HdenB & HdenF) HFFRS HMEAS].
  rewrite Hcsp in *.
  pose proof (PSOCK.akag_of I i E1 A1 M' m' HAm) as AK.
  destruct (FRM I i E1 A1 M1 m1 Hi HA) as (HcB & HcF & _).
  pose proof (PSOX.c_pa _ _ _ _ _ _ _ _ CL2) as PA2. rewrite PSOX.set_win_self in PA2.
  pose proof (PSOX.c_sh _ _ _ _ _ _ _ _ CL2) as SH2.
  pose proof (PSOX.c_blk _ _ _ _ _ _ _ _ CL2) as BK2. unfold PML.ps_blocks in BK2. injection BK2 as Ebp Ebc Esb Esc.

  assert (HB0 : PML.ps_buf ps2 = []).
  { pose proof (CBA.amb_off L ar C HI HIok (LYB I) GT.NF E0 M model A LBo FF LK sp G.HDECL WW G.BLS PSO.FFS Cred 6 i E1 A1 M1 m1 HA) as Hoff1.
    assert (Hoff : H_off_segments (hl_segs L) (ahid A1 m')) by (rewrite (L5LZ.sbm_ahid A1 m1 m' (CCA.lfa_sbm _ _ _ _ _ _ _ _ _ _ HLF)); exact Hoff1).
    pose proof (CELLS _ (cell_at_has _ _ _ _ _ Hsz)) as K232.
    pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ (P + 232) K232 ltac:(unfold estart; cbn [a_base a_off edenot]; rewrite W10; reflexivity)) as G0.
    apply (CL5A.u64_full (hl_segs L) _ Hoff) in G0. unfold CL5A.uv in G0. cbn [edenot] in G0. rewrite L5.unsigned_lit in G0 by (clear; lia).
    pose proof (PTB.pa_buf L IC M' P ps2 PA2) as ((_ & _ & U8s & _) & _ & LT). replace (P + 224 + 8) with (P + 232) in U8s by (clear; lia).
    rewrite Ebc in LT. pose proof (CL5A.uv_range E1 (snd (PSO.blk0 i))) as RB. unfold PSOX.bcapI in LT.
    pose proof (U64INJ I M' (P + 232) _ _ U8s G0 ltac:(clear - LT RB; lia) ltac:(clear; lia)) as LZ.
    destruct (PML.ps_buf ps2); [reflexivity | cbn [length] in LZ; clear - LZ; lia]. }
  set (bp := bptrI i E1) in *. set (bc := bcapI i E1) in *. set (sb := sbI i E1) in *. set (sc := scapI i E1) in *.
  pose proof (PTB.pa_bcap L IC M' P ps2 PA2) as BC264. rewrite Ebc in BC264.
  destruct (A1V c ps0 E' R' A1 M1 m1 M' m' (PSO.reg_of ps0 11) HLF Sa1) as (CV & NE11).
  set (cv := CL5A.uv E' (PSO.reg_of ps0 11)) in *.
  eexists. eexists. split; [exact (PSOI.iPUSHB I (CHA.curB LBo G.BLS i E1) (CHA.curF FF sp PSO.FFS i E1) LK1 cr1 A1 (P + 224) bc bp cv (sp + PSO.CSP) (CC.cp_pc cj) [])|].
  split.
  {
    split; [exact (REGS 10%nat _ (P + 224) (reg_of_is ps0 10 _ Sreg10 ltac:(discriminate)) (W224_of E' W10))|].
    split; [exact (REGS 11%nat _ cv (reg_of_is ps0 11 _ eq_refl NE11) eq_refl)|].
    split; [exact CV|].
    split; [pose proof (PTB.pa_buf L IC M' P ps2 PA2) as STR; rewrite Ebc, Ebp, HB0 in STR; exact STR|].
    split; [clear - BC264; lia|].
    split; [rewrite HcB; left; reflexivity|].
    split; [destruct SH2 as [SHB _]; rewrite Ebp, Ebc in SHB; exact SHB|].
    split.
    { pose proof (PSOCK.FOBJ I M' (CHA.curF FF sp PSO.FFS i E1) P 272 AK (PSOI.iOP I) ltac:(rewrite HcF; intros f Hf; right; exact Hf) ltac:(clear; lia) ltac:(clear - O6; lia))
        as (_ & _ & SZ).
      split; [destruct Pfr as (f & Hf & F1 & F2); exists f; split; [rewrite HcF; right; exact Hf | clear - F1 F2; lia]|].
      split; [clear - P8; replace (P + 224) with (P + 28 * 8) by lia; rewrite Z_mod_plus_full; exact P8|].
      intros jj Hjj. replace (HeapIfaceA.S (P + 224) + jj) with (HeapIfaceA.S P + (28 + jj)).
      - apply SZ. change (272 / 8) with 34. change (24 / 8) with 3 in Hjj. clear - Hjj; lia.
      - unfold HeapIfaceA.S. replace (P + 224) with (P + 28 * 8) by (clear; lia). rewrite Z.div_add by (clear; lia). clear; lia. }
    split; [exact (PSOCK.STKSH I M' 4368 AK ltac:(clear; lia) eq_refl ltac:(clear; lia))|].
    split; [cbn [length]; clear; lia|].
    intros X. exfalso. cbn [length] in X. clear - X BC264. lia. }

  intros R2 M2 m2 LB' cr' LBk Wc LK2 A2 (GROWN & ->) HRP HP Hrt2 HA2 Hmo2 HLK2 HH2.
  destruct GROWN as [(STR2 & SHB2 & -> & -> & ->)|(p' & GC & _)]; [|exfalso; cbn [app length] in GC; clear - GC BC264; lia].
  cbn [app] in STR2.
  assert (LBK : lb_remove bp (CHA.curB LBo G.BLS i E1) = (sb, sc) :: LBo) by (rewrite HcB; cbn [lb_remove app fst]; rewrite Z.eqb_refl; reflexivity).
  rewrite LBK in HP |- *.
  pose proof STR2 as ((_ & _ & _ & _ & BY2 & TM2) & SC8 & LT2). cbn [length] in LT2, TM2.
  exists [Z_to_bv 64 bp; Z_to_bv 64 (bc / 2)]. split; [reflexivity|]. cbv zeta.
  set (gx := CH2.ci_nx ci) in *. set (E2 := CH2.retEx E' gx [Z_to_bv 64 bp; Z_to_bv 64 (bc / 2)] R2).
  pose proof (CH2.retEx_agree E' gx [Z_to_bv 64 bp; Z_to_bv 64 (bc / 2)] R2 : env_agree gx E' E2) as Hag2. fold E2 in Hag2.
  destruct HV as (_ & _ & HV3 & _ & HV5).
  assert (Hag12 : env_agree (CC.cp_nx c) E1 E2) by (eapply CC.env_agree_trans; [exact Hag | eapply CC.env_agree_le; [exact Hag2 | exact HV3]]).

  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH1) as WFq. rewrite HcB in WFq.
  destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WFq (bp, bc) ltac:(left; reflexivity)) as ((J0 & _ & J16 & J3 & _ & (J5 & _ & J7)) & _). cbn [fst snd] in *.
  destruct (CHA.wf_blk _ _ _ _ _ _ _ _ WFq (sb, sc) ltac:(right; left; reflexivity)) as ((K0 & _ & K16 & K3 & _ & (K5 & _ & K7)) & _). cbn [fst snd] in *.
  assert (BC2 : 2 * (bc / 2) = bc) by (clear - SC8; Z.div_mod_to_equations; lia).
  assert (Tg0 : ev E2 gx = Z_to_bv 64 bp) by (pose proof (CH2.retEx_ghost E' gx [Z_to_bv 64 bp; Z_to_bv 64 (bc / 2)] R2 0 ltac:(cbn; clear; lia)) as G0; rewrite Nat.add_0_r in G0; exact G0).
  assert (Tg1 : ev E2 (gx + 1) = Z_to_bv 64 (bc / 2)) by (exact (CH2.retEx_ghost E' gx [Z_to_bv 64 bp; Z_to_bv 64 (bc / 2)] R2 1 ltac:(cbn; clear; lia))).
  assert (UB : CL5A.uv E2 (EVar gx) = bp) by (unfold CL5A.uv; cbn [edenot]; rewrite Tg0; apply u64_of_Z; clear - J5 J7 J3; lia).
  assert (UK : CL5A.uv E2 (EVar (gx + 1)) = bc / 2) by (unfold CL5A.uv; cbn [edenot]; rewrite Tg1; apply u64_of_Z; clear - J5 J7 J3; Z.div_mod_to_equations; lia).
  assert (T57 : CL5A.uv E2 (EVar 57) = sb) by (rewrite <- W57; unfold CL5A.uv; cbn [edenot]; rewrite <- (proj1 Hag2 57%nat) by (clear - NX HV3; lia); reflexivity).
  assert (T59 : CL5A.uv E2 (EVar 59) = sc) by (rewrite <- W59; unfold CL5A.uv; cbn [edenot]; rewrite <- (proj1 Hag2 59%nat) by (clear - NX HV3; lia); reflexivity).
  assert (T10 : bv_unsigned (ev E2 10) = P) by (rewrite <- (proj1 Hag2 10%nat) by (clear - NX HV3; lia); exact W10).
  assert (BJ : bptrI j E2 = bp /\ bcapI j E2 = bc /\ sbI j E2 = sb /\ scapI j E2 = sc).
  { unfold PSOX.bptrI, PSOX.bcapI, PSOX.sbI, PSOX.scapI, PSO.blk0, PSO.blk1. rewrite Hblk, (bls_i i ltac:(clear - Hi; lia)). cbn [skipn hd tl fst snd].
    rewrite Ssb, Ssc. split; [exact UB|]. split; [rewrite uv_escale, UK, BC2; apply Z.mod_small; clear - J5 J7 J3; lia|]. split; [exact T57 | exact T59]. }
  destruct BJ as (QJ1 & QJ2 & QJ3 & QJ4).
  assert (CBj : CHA.curB LBo G.BLS j E2 = CHA.curB LBo G.BLS i E1).
  { rewrite HcB. unfold CHA.curB. rewrite (bls_i j ltac:(clear - Hj; lia)). unfold CH2.den. cbn [map app].
    unfold PSOX.bptrI, PSOX.bcapI, PSOX.sbI, PSOX.scapI, CL5A.uv in QJ1, QJ2, QJ3, QJ4. rewrite QJ1, QJ2, QJ3, QJ4. reflexivity. }
    destruct (PB_WIN i c ps0 E1 R1 A1 M1 m1 E' R' M' m' l ps2 g1 Hci Hi Su0 ltac:(rewrite <- Skind; reflexivity) HAt HA Hag HLF Hl Scur SJ1 CL2) as (p & HW2 & Rp0 & Rp1).
    set (Sg := fun a => SUPP I bp bc sb sc a /\ ~ (P + 224 <= a < P + 248) /\ ~ (bp <= a < bp + bc) /\ ~ in_shadow_of bp bc a).
    assert (AGS : forall a, Sg a -> M2 (Z_to_bv 64 a) = M' (Z_to_bv 64 a)).
    { intros a (Ha & N1 & N2 & N3). exact (proj1 (AG_B i E1 A1 M1 m1 M' M2 4368 _ Hi HA HP ltac:(clear; lia) a Ha N2 N3) (W_S_out a N1)). }
    assert (GS : forall a, ((P <= a < P + 224) \/ (P + 248 <= a < P + 272) \/ (E <= a < E + 16) \/ STATIC a \/ (sb <= a < sb + sc) \/ in_shadow_of sb sc a) -> Sg a)
      by (intros a Ha; exact (SG_PB i E1 A1 M1 m1 a Hi HA Ha)).
    pose proof (PSOX.c_pa _ _ _ _ _ _ _ _ CL2) as PA2'. rewrite HW2 in PA2'.
    pose proof (PTB.pa_slen L IC M' P _ PA2) as SLn.
    assert (HDEF : forall kk, 0 <= kk < 272 -> M2 (Z_to_bv 64 (P + kk)) <> None).
    { intros kk Hkk. pose proof (PTB.pa_def L IC M' P ps2 PA2 kk Hkk) as D'.
      destruct (GEO_B i E1 A1 M1 m1 (P + kk) Hi HA ltac:(left; clear - Hkk; lia)) as (N2 & N3).
      exact (proj2 (AG_B i E1 A1 M1 m1 M' M2 4368 _ Hi HA HP ltac:(clear; lia) (P + kk) ltac:(left; clear - Hkk; lia) N2 N3) D'). }
    assert (PA3 := PA_STR M' M2 Sg AGS ps2 (Some (p, PSOI.we0 I)) [cv]
                     ltac:(split; [clear - O3; lia|]; split; [clear - O6; lia|]; intros x Hx; apply GS; left; exact Hx)
                     ltac:(split; [clear - O3; lia|]; split; [clear - O6; lia|]; intros x Hx; apply GS; right; left; clear - Hx; lia)
                     ltac:(rewrite Esb; split; [clear - K5; lia|]; split; [rewrite Esc in SLn; clear - SLn K5 K7; lia|]; intros x Hx; apply GS; do 4 right; left;
                           rewrite Esc in SLn; clear - Hx SLn; lia)
                     PA2' ltac:(rewrite Ebc, Ebp; exact STR2) HDEF).
    set (ps3 := PML.PS (PML.ps_st ps2) (PML.ps_sst ps2) (PML.ps_nst ps2) (PML.ps_more ps2) (PML.ps_done ps2) (PML.ps_level ps2) (PML.ps_stack ps2) (PML.ps_sb ps2)
                       (PML.ps_scap ps2) (PML.ps_bcap ps2) (PML.ps_bptr ps2) [cv] (Some (p + 1, PSOI.we0 I))).
    assert (T60 : CL5A.uv E2 FLE = CL5A.uv E1 FLE) by (unfold CL5A.uv, FLE, FLV; cbn [edenot]; rewrite <- (proj1 Hag12 60%nat) by (clear - NX; lia); reflexivity).
    assert (CO3 : PSOX.CORE I j E2 M2 (Some (p, PSOI.we0 I)) ps3 0 g1).
    { constructor.
      - exact PA3.
      - right; right. split; [exact HKj'|]. exists p, (PSOI.we0 I). split; reflexivity.
      - split; [cbn [ps3 PML.ps_bptr PML.ps_bcap]; rewrite Ebp, Ebc; exact SHB2|].
        destruct SH2 as [_ SC2]. cbn [ps3 PML.ps_sb PML.ps_scap PML.ps_stack].
        apply (PTA.shadow_cont_ag M' M2 Sg AGS); [clear - SLn; lia | rewrite Esb; exact (CHA.mod8_of_16 _ K16) | intros a Ha; apply GS; do 5 right; rewrite <- Esb, <- Esc; exact Ha | exact SC2].
      - unfold PSOX.WIN. pose proof (WINF I) as (WI0' & WI1' & WI2' & _ & _ & _ & WI6' & _).
        destruct (PML.ps_win (PSOI.ips I)) as [[p0 e0]|] eqn:Hw0.
        + pose proof (PSOI.WSOME I p0 e0 Hw0) as (WS1 & WS2 & _). exists (p + 1). cbn [ps3 PML.ps_win]. rewrite WS2. split; [reflexivity | clear - WS1 WS2 Rp0 Rp1; lia].
        + exfalso. pose proof (PSOI.WNONE I Hw0) as (W0 & W1 & _). clear - W0 W1 Rp0 Rp1. lia.
      - pose proof (PSOX.c_bb _ _ _ _ _ _ _ _ CL2) as (BB1' & BB2'). unfold PML.winlen in BB1'. rewrite HW2, HB0 in BB1'. cbn [length] in BB1'.
        split; [|exact BB2']. unfold PML.winlen. cbn [ps3 PML.ps_win PML.ps_buf length].
        replace (PML.buf_need ps3) with (PML.buf_need ps2) by (unfold PML.buf_need; reflexivity). clear - BB1'. lia.
      - exact (PTA.ec_at_ag (hl_segs L) IC M' M2 Sg AGS E 0 ltac:(split; [clear - Q3; lia|]; split; [clear - Q6; lia|]; intros x Hx; apply GS; right; right; left; exact Hx)
                 (PSOX.c_ec _ _ _ _ _ _ _ _ CL2)).
      - apply (LS_mv I g1 M' M2 (fun a Ha => AGS a (GS a ltac:(do 3 right; left; exact Ha)))); [|exact (PSOX.c_ls _ _ _ _ _ _ _ _ CL2)].
        destruct (PSOX.c_g _ _ _ _ _ _ _ _ CL2) as [->|(-> & X)]; [exact (PSOI.iHG I) | exfalso; exact (X eq_refl)].
      - exact (PSOX.c_g _ _ _ _ _ _ _ _ CL2).
      - cbn [ps3 PML.ps_more PML.ps_level]. exact (PSOX.c_lv _ _ _ _ _ _ _ _ CL2).
      - unfold PML.ps_blocks. cbn [ps3 PML.ps_bptr PML.ps_bcap PML.ps_sb PML.ps_scap]. rewrite QJ1, QJ2, QJ3, QJ4, Ebp, Ebc, Esb, Esc. reflexivity.
      - intros Hu Hr. rewrite (PSOCK.U0RET i k j Hret) in Hu. exact (PSOX.c_na _ _ _ _ _ _ _ _ CL2 Hu ltac:(rewrite <- Skind; reflexivity)).
      - intros Hu Hw. rewrite (PSOCK.U0RET i k j Hret) in Hu. exact (PSOX.c_wl _ _ _ _ _ _ _ _ CL2 Hu ltac:(rewrite <- Skind; reflexivity)).
      - intros Hu. rewrite (PSOCK.U0RET i k j Hret), Su0 in Hu. discriminate Hu. }
  split; [exact Logic.I|].
  split.
  { rewrite (bls_i i ltac:(clear - Hi; lia)). unfold CH2.den. cbn [skipn map app]. rewrite Ssb, Ssc.
    change (bv_unsigned (edenot E' (EVar 57))) with (CL5A.uv E' (EVar 57)). change (bv_unsigned (edenot E' (EVar 59))) with (CL5A.uv E' (EVar 59)). rewrite W57, W59. apply incl_refl. }
  split.
  { intros w a Hw Ha. cbn [In] in Hw. unfold L5.in_rng in Ha. destruct Hw as [<-|[]]; cbn [fst snd] in Ha.
    exists (EVar 10, 224, ELit 24). split; [left; reflexivity|]. unfold CHA.in_reg, estart, elenZ. cbn [a_base a_off edenot]. rewrite W10, u64_of_Z by (clear; lia). clear - Ha. lia. }
  split.
  { intros w a Hw Ha (_ & HAC & HO). cbn [In] in Hw. unfold L5.in_rng in Ha. destruct Hw as [<-|[]]; cbn [fst snd] in Ha.
    apply (HO (P, 272)); [unfold WW, PMSA.W_parEc, PMSA.W_parE; left; reflexivity | unfold L5.in_rng; cbn [fst snd]; clear - Ha; lia]. }
  split; [rewrite CBj; exact HH2|].
  split; [unfold Cred, PSOX.Cred; rewrite QJ2, QJ4; exact HC1|].
  split.
  {
    apply (XI_PB j E2 M2 ps3 p (PSOI.we0 I) g1 cv HKj' ltac:(unfold PSOX.FLF; rewrite T60; exact HFL) CO3 eq_refl (conj (WF_PB ps2 [cv] _ (proj1 WFL) HST2) (proj2 WFL)) HM2 HST2 eq_refl). }

  intros X HX _.
  change (PSOK.news_of PSOK.XS_PUSHB (CA.ps_reglist ps0) (SR.ps_cells ps0) gx (skipn 1 (nth i G.BLS [])))
    with (PSOK.STATICS_ISH ++ PSOK.MEASNEWS (SR.ps_cells ps0) ++ PBNEWS (CA.ps_reglist ps0) (SR.ps_cells ps0) gx ++ PSOK.FLAGC (SR.ps_cells ps0)) in HX.
  apply in_app_or in HX as [HX|HX]; [exact (proj1 (Forall_forall _ _) (PSOCK.NEWS_SI I E2 A2 m2 M2 _ _ _ _ HH2) X HX)|].
  apply in_app_or in HX as [HX|HX]; [exact (proj1 (Forall_forall _ _) (PSOCK.NEWS_KR I c ps0 E' R' A1 M1 m1 M' m' E2 _ _ HLF (CC.env_agree_le _ _ _ _ Hag2 HV3) SMEAS) X HX)|].
  assert (T65 : CL5A.uv E2 FE = CL5A.uv E1 FE) by (unfold CL5A.uv, FE, FEV; cbn [edenot]; rewrite <- (proj1 Hag12 65%nat) by (clear - NX; lia); reflexivity).
  apply in_app_or in HX as [HX|HX].
  { assert (TFX : forall kk z, (kk < 40)%nat -> bv_unsigned (ev E0 kk) = z -> CL5A.uv E2 (EVar kk) = z).
    { intros kk z Hk Hz. unfold CL5A.uv. cbn [edenot]. rewrite <- (proj1 Hag2 kk) by (clear - Hk NX HV3; lia). rewrite (FZ kk Hk). exact Hz. }
    pose proof (PSSA.wf_shape _ (proj1 WFL)) as (WS1 & WS2 & WS3 & WS4).
    assert (ULIT : forall z, 0 <= z < 2 ^ 64 -> CL5A.uv E2 (ELit z) = z) by (intros z Hz; unfold CL5A.uv; cbn [edenot]; apply L5.unsigned_lit; exact Hz).
    assert (B27 : bc <= 2 ^ 27) by (unfold Cred, PSOX.Cred in HC1; destruct HC1 as (X27 & _); exact X27).
    assert (HH2' := HH2). rewrite HcB in HH2'.
    assert (KH : PSOKK.knh I E2 M2 A2 m2 (CHA.curF FF sp PSO.FFS i E1) LK2 cr1 ps3 (Some (p, PSOI.we0 I)) bp bc sb sc
                   (ELit (PML.ps_level ps3 mod 2 ^ 32)) (ELit (PSOI.we0 I)) (ELit p) (ELit (PML.ps_st ps3 mod 256)) (ELit (PML.ps_sst ps3)) (ELit (PML.ps_nst ps3))
                   (ELit (PML.b2z (PML.ps_more ps3))) (ELit (PML.b2z (PML.ps_done ps3))) (EVar (gx + 1))
                   (APC.eaddz (match CAX.cell_at (SR.ps_cells ps0) (EVar 10) 232 8 with Some e => e | None => ELit 0 end) 1) (EVar gx) (EVar 57)
                   (ELit (Z.of_nat (length (PML.ps_stack ps3)))) (EVar 59)).
    { pose proof (WINF I) as (WI0' & WI1' & WI2' & _ & _ & _ & WI6' & _).
      constructor.
      - exact Ebp.
      - exact Ebc.
      - exact Esb.
      - exact Esc.
      - exact HH2'.
      - intros f Hf. unfold CHA.curF. apply in_or_app. right. exact Hf.
      - exact (PSOX.c_pa _ _ _ _ _ _ _ _ CO3).
      - exact (PSOX.c_sh _ _ _ _ _ _ _ _ CO3).
      - exact (WF_PB ps2 [cv] _ (proj1 WFL) HST2).
      - exact B27.
      - cbn [ps3 PML.ps_buf length]. clear; lia.
      - unfold CL5A.uv. cbn [edenot]. exact T10.
      - apply TFX; [clear; lia | exact U11].
      - apply TFX; [clear; lia | exact U12].
      - apply TFX; [clear; lia | exact U2].
      - apply TFX; [clear; lia | exact U32].
      - apply TFX; [clear; lia | exact U34].
      - apply TFX; [clear; lia | exact U35].
      - apply TFX; [clear; lia | exact U36].
      - apply ULIT. pose proof (Z.mod_pos_bound (PML.ps_level ps3) (2 ^ 32) ltac:(clear; lia)). clear - H. lia.
      - cbn [PSOI.whi]. apply ULIT. clear - WI0' WI2' WI1' WI6'. unfold PSOI.wlen in *. lia.
      - cbn [PSOI.wlo]. apply ULIT. clear - Rp0 Rp1 WI0' WI2' WI1' WI6'. unfold PSOI.wlen in *. lia.
      - apply ULIT. pose proof (Z.mod_pos_bound (PML.ps_st ps3) 256 ltac:(clear; lia)). clear - H. lia.
      - apply ULIT. cbn [ps3 PML.ps_sst]. clear - WS1. lia.
      - apply ULIT. cbn [ps3 PML.ps_nst]. clear - WS2. lia.
      - apply ULIT. destruct (PML.ps_more ps3); cbn; clear; lia.
      - apply ULIT. destruct (PML.ps_done ps3); cbn; clear; lia.
      - exact UK.
      - rewrite Hsz. rewrite uv_eaddz, ULIT by (clear; lia). cbn [ps3 PML.ps_buf length]. reflexivity.
      - exact UB.
      - exact T57.
      - apply ULIT. cbn [ps3 PML.ps_stack]. clear - WS3. lia.
      - exact T59. }
    assert (KF : PSOKK.knf I E2).
    { destruct (FRM I i E1 A1 M1 m1 Hi HA) as (_ & _ & _ & _ & _ & F64 & _ & F3 & F4 & _).
      constructor.
      - change (CL5A.uv E2 (EVar 65)) with (CL5A.uv E2 FE). rewrite T65. unfold FE, FEV in *. split; [exact F3|]. split; [exact F4 | exact F64].
      - change (CL5A.uv E2 (EVar 60)) with (CL5A.uv E2 FLE). rewrite T60. destruct HFL as (FL1 & _). unfold FLE, FLV in FL1. exact FL1. }
    destruct (PBNEWS_in (CA.ps_reglist ps0) (SR.ps_cells ps0) gx (ELit (PML.ps_level ps3 mod 2 ^ 32)) (ELit (PSOI.we0 I)) (ELit p) (ELit (PML.ps_st ps3 mod 256))
                (ELit (PML.ps_sst ps3)) (ELit (PML.ps_nst ps3)) (ELit (PML.b2z (PML.ps_more ps3))) (ELit (PML.b2z (PML.ps_done ps3))) (ELit (Z.of_nat (length (PML.ps_stack ps3))))
                X HX) as [->|HX'].
    -
      assert (VB : CL5A.visr (ahid A2 m2) bp bc) by (eapply PSOKK.VISB; [exact KH | left; reflexivity]).
      assert (UCV : CL5A.uv E2 (nth 11 (CA.ps_reglist ps0) (ELit 0)) = cv).
      { rewrite Sr11. exact (A1AG (CC.cp_nx c) (SR.ps_cells ps0) (PSO.reg_of ps0 11) E' E2 Sa1 (CC.env_agree_le _ _ _ _ Hag2 HV3)). }
      change (CCA.vis A2 m2 M2) with (mrestrict (ahid A2 m2) M2). apply (PSOKK.KW8 (hl_segs L) E2 (ahid A2 m2) M2 (EVar gx) 0 _ bp cv UB UCV); [clear - J5; lia | clear - J5 J7 J3; lia | | rewrite Z.add_0_r; pose proof (BY2 0%nat ltac:(cbn; lia)) as U0; cbn [nth Z.of_nat] in U0; rewrite Z.add_0_r in U0; exact U0].
      intros y Hy. rewrite Z.add_0_r. apply VB. clear - Hy J3. lia.
    - apply in_app_or in HX' as [HX'|HX']; [exact (proj1 (Forall_forall _ _) (PSOKK.PSTATE_ok KH) X HX')|].
      apply in_app_or in HX' as [HX'|HX']; [exact (proj1 (Forall_forall _ _) (PSOKK.BLOCKS_KN_ok KH KF) X HX') | exact (proj1 (Forall_forall _ _) (PSOKK.BLOCKS_KDISJ_F_ok KH KF) X HX')]. }

  unfold PSOK.FLAGC in HX. rewrite SFLAG in HX.
  pose proof (CBA.amb_off L ar C HI HIok (LYB I) GT.NF E0 M model A LBo FF LK sp G.HDECL WW G.BLS PSO.FFS Cred 6 i E1 A1 M1 m1 HA) as Hoff1.
  assert (Hoff : H_off_segments (hl_segs L) (ahid A1 m')) by (rewrite (L5LZ.sbm_ahid A1 m1 m' (CCA.lfa_sbm _ _ _ _ _ _ _ _ _ _ HLF)); exact Hoff1).
  assert (FLC : L5.u64_at (hl_segs L) M' (CL5A.uv E1 FE + 1016) (CL5A.uv E1 FLE)).
  { pose proof (cell_at_has _ _ _ _ _ SFLAG) as Hin. pose proof (CELLS _ Hin) as KFc.
    pose proof (CL5A.kword64_elim (hl_segs L) E' _ _ _ (CL5A.uv E1 FE + 1016) KFc ltac:(unfold estart; cbn [a_base a_off]; change (bv_unsigned (edenot E' (EVar 65))) with (CL5A.uv E' FE); rewrite W65; reflexivity)) as G0.
    apply (CL5A.u64_full (hl_segs L) _ Hoff) in G0. change (CL5A.uv E' (EVar 60)) with (CL5A.uv E' FLE) in G0. rewrite W60 in G0. exact G0. }
  exact (proj1 (Forall_forall _ _) (PSOCK.NEWS_FLAGC I i E1 A1 M1 m1 E2 A2 m2 M' M2 m' _ _ _ _ _ _ Hi HA HFL HH1 HH2 FLC T65 T60) X HX).
Qed.

End C.

End PSOCALLP.
