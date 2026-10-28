(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5 PmLibSpecsX_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX CutHeap2V.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseSums_u5 ParseSums2_u5 ParseSums2X_u5 ParseSpecs_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmParse Require Import ParseProve. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5 ParseBridges2_u5 ParseBridges6_u5 ParseBridgesX_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import VisitSumsX.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges6_u5 ParseBridges6X_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibSpecsW_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParseW Require Import ParseBridges6W_u5.

Module PB6WU.
Import PB6W.
Import PMES.

Section GBXEU.
Context {SCFG_P : ScfgP}.
Variables (L : heap_layout) (HI : heap_iface).
Definition ptrans_gbxEU (WFin : PML.pstate -> Prop) (BBin : PML.pstate -> Z -> Prop) (PAin : mem -> Z -> PML.pstate -> Prop) (PAout : PML.pstate -> mem -> Z -> PML.pstate -> Prop)
           (pc scr : Z) (Args : list (Z * Z) -> bvmap 5 word -> mem -> Z -> Z -> Z -> PML.pstate -> Prop)
           (Rel : PML.pstate -> PML.pstate -> Z -> bvmap 5 word -> Prop) (EXpost : eghost -> PML.pstate -> mem -> Z -> PML.pstate -> Z -> eghost -> Prop)
           (Room : eghost -> PML.pstate -> Prop) : Prop :=
  forall (LBo : list (Z * Z)) (cr : credit) (sp r P V E S2 B kx bx : Z) (g : PML.ls_state) (ps : PML.pstate) (eg : eghost),
    PML.cps_heap L HI pc r sp scr (PML.ps_blocks ps ++ LBo ++ g_lbv eg) cr
      (fun R M => PML.entry L R M sp r scr /\ Args LBo R M P V E ps /\ PAin M P ps /\ WFin ps /\ PML.win_ok M LBo ps /\ BBin ps B /\ PML.vis_at M V /\ PML.ec_at M E 0 /\
                  PML.ls_ok g M /\ g <> PML.LS0 /\ enc_inv M V S2 eg /\ PML.lits_ok M /\ PMX.enc_sync ps eg /\
                  0 <= kx /\ 0 <= bx /\ PML.pcredit_x L cr ps (kx + PMES.kenc L eg) (bx + PMES.benc L eg) /\ PMX.objs_x L sp P V E S2 /\ Room eg ps)
      (fun R M R' M' LB' cr' LBk W => exists (ps' : PML.pstate) (code : Z) (g' : PML.ls_state) (eg' : eghost),
          PAout ps M' P ps' /\ PML.wf_ps ps' /\ PML.win_ok M' LBo ps' /\ PML.buf_bound ps' B /\ PML.ec_at M' E code /\ (code <> 0 -> PML.ps_more ps' = false) /\
          PML.ls_ok g' M' /\ (g' = g \/ (g' = PML.LS2 /\ code <> 0)) /\ enc_inv M' V S2 eg' /\ PML.lits_ok M' /\ (code = 0 -> PMX.enc_sync ps' eg') /\
          LB' = PML.ps_blocks ps' ++ LBo ++ g_lbv eg' /\ LBk = LBo /\ W = PMX.W_parx P V E S2 /\
          PML.pcredit_x L cr' ps' (kx + PMES.kenc L eg') (bx + PMES.benc L eg') /\ Rel ps ps' code R' /\ EXpost eg ps M' P ps' code eg').
End GBXEU.

Section InstXWU.
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
(* [comment removed for export] *)
Variable EB : expr.
Variable EK : Z.
Hypothesis EB_frozen : APC.expr_vars_lt NF EB = true.
Variable eaddr : Z.
Hypothesis EADDR : estart E0 (SA EB EK) = eaddr.
Variable g0 : PML.ls_state.
Hypothesis G0 : g0 <> PML.LS0.
Variable PBx : expr.
Variable PKx : Z.
Hypothesis PB_frozen : APC.expr_vars_lt NF PBx = true.
Variable paddr : Z.
Hypothesis PADDR : estart E0 (SA PBx PKx) = paddr.
Variables vaddr s2addr : Z.
Hypothesis OBJS : PMX.objs_x L sp0 paddr vaddr eaddr s2addr.
Hypothesis WPAR_in : forall w a, In w (PML.W_par paddr eaddr) -> L5.in_rng w a -> exists w', In w' W /\ L5.in_rng w' a.
Hypothesis W_ENC : forall w, In w (W_enc vaddr s2addr) -> In w W.
Variable VB : expr.
Hypothesis VB_frozen : APC.expr_vars_lt NF VB = true.
Hypothesis VADDR : uv E0 VB = vaddr.
Hypothesis S2_frozen : (52 < NF)%nat.
Hypothesis S2ADDR : uv E0 S2V = s2addr.
Hypothesis LITLEN : PML.LIT_HI - PML.LIT_LO = VSX.LIT_LEN.
(* [comment removed for export] *)
Variables CPC CSCR : Z.
Variable WFin : PML.pstate -> Prop.
Variable BBin : PML.pstate -> Z -> Prop.
Variable TH : Type.
Variable PAin : TH -> mem -> Z -> PML.pstate -> Prop.
Variable PAout : TH -> PML.pstate -> mem -> Z -> PML.pstate -> Prop.
Variable Args : TH -> list (Z * Z) -> bvmap 5 word -> mem -> Z -> Z -> Z -> PML.pstate -> Prop.
Variable Rel : TH -> PML.pstate -> PML.pstate -> Z -> bvmap 5 word -> Prop.
Variable EXpost : TH -> eghost -> PML.pstate -> mem -> Z -> PML.pstate -> Z -> eghost -> Prop.
Variable Room : TH -> eghost -> PML.pstate -> Prop.
Hypothesis CALLEE : forall th : TH, ptrans_gbxEU L HI WFin BBin (PAin th) (PAout th) CPC CSCR (Args th) (Rel th) (EXpost th) (Room th).
Hypothesis PAOUT_CAP : forall th pst (M : mem) P ps2, PAout th pst M P ps2 -> PML.ps_bcap ps2 mod 2 = 0.
Variable Bv : Z.
Variables KXv BXv : Z.
Hypothesis KX0 : 0 <= KXv.
Hypothesis BX0 : 0 <= BXv.
Let LS : hl_segs L = RSEGS := PmLayout.ly_segs L LAY.
Let LYI := PB.LYI_ L LAY.
Let LYE := PB.LYE_ L LAY.
Let LYR := PmLayout.ly_ro L LAY.
Abbreviation OKV := (CH2V.okV L M00 LBo sp0 d W).
Abbreviation HAMBV := (CH2V.heap_ambV L HI NF E0 model0 LBo sp0 d W BLS eghost gB CredV).
Abbreviation LEAFOKV := (CH2V.leaf_okV L HI NF E0 M00 model0 LBo sp0 d W BLS eghost gB CredV XIv CPS K PML.fp_ok).
Abbreviation is_leaf := (CH2.is_leaf CPS TAGS).

Definition ptrans_prexU (th : TH) (g : eghost) (R : bvmap 5 word) (M : mem) (cr : credit) (pst : PML.pstate) : Prop :=
  Args th LBo R M paddr vaddr eaddr pst /\ PAin th M paddr pst /\ WFin pst /\ PML.win_ok M LBo pst /\ BBin pst Bv /\ PML.vis_at M vaddr /\ PML.ec_at M eaddr 0 /\
  PML.ls_ok g0 M /\ enc_inv M vaddr s2addr g /\ PML.lits_ok M /\ PMX.enc_sync pst g /\ PML.pcredit_x L cr pst (KXv + PMES.kenc L g) (BXv + PMES.benc L g) /\ Room th g pst.
Definition ptrans_postxU (th : TH) (g : eghost) (pst : PML.pstate) (R2 : bvmap 5 word) (M2 : mem) (cr2 : credit) (ps2 : PML.pstate) (code : Z) (g' : PML.ls_state) (eg' : eghost) : Prop :=
  PAout th pst M2 paddr ps2 /\ PML.wf_ps ps2 /\ PML.win_ok M2 LBo ps2 /\ PML.buf_bound ps2 Bv /\ PML.ec_at M2 eaddr code /\ (code <> 0 -> PML.ps_more ps2 = false) /\
  PML.ls_ok g' M2 /\ (g' = g0 \/ (g' = PML.LS2 /\ code <> 0)) /\
  enc_inv M2 vaddr s2addr eg' /\ PML.lits_ok M2 /\ (code = 0 -> PMX.enc_sync ps2 eg') /\
  PML.pcredit_x L cr2 ps2 (KXv + PMES.kenc L eg') (BXv + PMES.benc L eg') /\ Rel th pst ps2 code R2 /\ EXpost th g pst M2 paddr ps2 code eg'.

Lemma ptrans_leaf_okxwU : forall (lit_lo : Z) ereg i c k ps j cj ci g M0c,
  lit_lo = PML.LIT_LO ->
  OKV M0c ->
  is_leaf i c k ps (CC.TOther CPC) -> CH2.ret_of RETS i k = Some j -> nth_error CPS j = Some cj -> SR.ps_pc ps = CPC ->
  PBX.ptrans_chkx NF d EB EK PBx PKx CSCR VB lit_lo ereg c ps cj (nth i BLS []) (nth j BLS []) = Some ci ->
  (forall E E' R' (M M' : mem) model cr,
      env_agree NF E0 E' -> APC.sr_vars_lt (CH2.ci_nx ci) (CA.ps_reglist ps) = true -> CH2.ci_nx ci = (CC.cp_nx cj - APC.NCS - 5)%nat ->
      env_agree (CC.cp_nx c) E E' -> CC.leaf_facts (hl_segs L) c ps E' R' M M' -> regs_ok E' (CA.ps_reglist ps) R' -> HAMBV g M0c i E M' model -> XIv g i E M ->
      hi_heap HI (CH2.cur (CH2V.LBr LBo eghost gB g) BLS i E) cr M' (m_vmmaps model) -> CredV g i E cr ->
      exists (th : TH) pst, CH2.den E' (nth i BLS []) = PML.ps_blocks pst /\ ptrans_prexU th g R' M' cr pst /\
        forall R2 (M2 : mem) cr2 ps2 code g' eg' E2,
          ptrans_postxU th g pst R2 M2 cr2 ps2 code g' eg' -> env_agree (CH2.ci_nx ci) E' E2 -> bv_unsigned (ev E2 (CH2.ci_nx ci)) = code -> ev E2 (CH2.ci_nx ci + 9) = getr R2 10%bv ->
          CH2.den E2 (nth j BLS []) = PML.ps_blocks ps2 ->
          L5C.hpres L LBo (sp0 + CH2.ci_csp ci) CSCR (PMX.W_parx paddr vaddr eaddr s2addr) M' M2 ->
          XIv eg' j E2 M2 /\ CredV eg' j E2 cr2) ->
  LEAFOKV g M0c i c ps.
Proof.
  intros lit_lo ereg i c k ps j cj ci g M0c Hlit HOKV IL Hret Hcj Hpc Hchk USER fx' E R M model E' R' M' HAt HAmb HFP Hag HLF HIH.
  subst lit_lo.
  destruct HAmb as [HAmbH HXI0].
  unfold PBX.ptrans_chkx in Hchk.
  destruct (split_lit (nth 10 (CA.ps_reglist ps) (ELit 0))) as [pb pk] eqn:Hsplit.
  destruct (split_lit (nth ereg (CA.ps_reglist ps) (ELit 0))) as [eb ek] eqn:Hsplit2.
  lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end.
  apply andb_prop in Hb as [Hb B6]. apply andb_prop in Hb as [Hb B5]. apply andb_prop in Hb as [Hb B4]. apply andb_prop in Hb as [Hb B3]. apply andb_prop in Hb as [B1 B2].
  apply expr_eqb_eq in B1, B3. apply Z.eqb_eq in B2, B4. apply Z.leb_le in B5. apply CH2.blocks_eqb_eq in B6. subst pb pk eb ek.
  set (BLi := nth i BLS []) in *.
  destruct (CH2V.custom_retV L HI HIok LYI LYE LYR NF E0 M00 model0 LBo sp0 d W BLS eghost gB CredV XIv STK SCR_pos NF32 SP0 TP0 W_ok CRS_ok WRS_ok IMG_ok CPS K PML.fp_ok
              g M0c CSCR 5%nat [] _ _ None i c ps j cj ci HOKV Hcj Hchk E R M model E' R' M' HAt HAmbH Hag HLF HIH) as [CF RET].
  pose proof CF as [HA' HR Hreq (V1 & V2 & V3 & V4 & V5) HK [Hra Hraok] (Hsp & Hc1 & Hs0 & Hc2) Hstk Htp HagE' Hden Hmeas].
  assert (Hnx : CH2.ci_nx ci = (CC.cp_nx cj - APC.NCS - 5)%nat) by lia.
  rewrite <- Hnx in B6. set (nx := CH2.ci_nx ci) in *.
  pose proof HA' as (Hmo & Hbv & HagE & (cr & HH & HC) & Hfr & Hdf).
  assert (Hoe : estart E' (SA EB EK) = eaddr) by (rewrite (PB.estart_agree NF E0 E' EB EK HagE' EB_frozen); exact EADDR).
  assert (Hop : estart E' (SA PBx PKx) = paddr) by (rewrite (PB.estart_agree NF E0 E' PBx PKx HagE' PB_frozen); exact PADDR).
  assert (HV : PB.uv E' VB = vaddr) by (rewrite (PB.uv_agree NF E0 E' VB HagE' VB_frozen); exact VADDR).
  assert (HS2 : bv_unsigned (ev E' 52) = s2addr).
  { pose proof HagE' as [X _]. rewrite <- (X 52%nat S2_frozen). exact S2ADDR. }
  pose proof STK as (S1 & S2 & S3 & S4 & S5). pose proof (CH2.ceil_lo L NF sp0 d STK NF32) as CLO.
  assert (HRL : regs_ok E' (CA.ps_reglist ps) R') by (rewrite <- Hreq; exact HR).
  unfold CH2.cur in HH. fold BLi in HH, Hden. rewrite <- Hden in HH.
  destruct (USER E E' R' M M' model cr HagE' ltac:(rewrite <- Hreq; exact V1) Hnx Hag HLF HRL HA' HXI0 ltac:(unfold CH2.cur; fold BLi; rewrite <- Hden; exact HH) HC)
    as (th & pst & Hblk & (PA & PIN & PWF & PWIN & PBB & PVIS & PEC & PLS & PINV & PLIT & PSYNC & PCR & PROOM) & UPOST).
  pose proof OBJS as (OP & OV & OS & OE & AP1 & AP2 & AP3 & AP4 & AP5 & AP6).
  assert (OBM : forall o n, PML.obj_on_stack L sp0 o n -> PML.obj_on_stack L (sp0 + CH2.ci_csp ci) o n) by (intros o n (X & Y & Z); repeat split; try assumption; lia).
  rewrite Hblk in HH. unfold CH2V.LBr, gB in HH.
  rewrite Hpc, LS.
  apply (CALLEE th LBo cr (sp0 + CH2.ci_csp ci) (CC.cp_pc cj) paddr vaddr eaddr s2addr Bv KXv BXv g0 pst g fx' R' M' model K HH Hmo K_nil HFP).
  { split; [split; [exact Hra | split; [exact Hraok | split; [exact Hsp | split; [rewrite Htp, (PmLayout.ly_tp L LAY); reflexivity | exact Hstk]]]]|].
    split; [exact PA|]. split; [exact PIN|]. split; [exact PWF|]. split; [exact PWIN|]. split; [exact PBB|]. split; [exact PVIS|]. split; [exact PEC|].
    split; [exact PLS|]. split; [exact G0|]. split; [exact PINV|]. split; [exact PLIT|]. split; [exact PSYNC|]. split; [exact KX0|]. split; [exact BX0|]. split; [exact PCR|]. split; [|exact PROOM].
    split; [apply OBM; exact OP|]. split; [apply OBM; exact OV|]. split; [apply OBM; exact OS|]. split; [apply OBM; exact OE|].
    repeat split; assumption. }
  intros fx2 R2 M2 model2 LB' cr' LBk Wc HFP2 (ps2 & code & g' & eg' & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q8a & Q8b & Q8c & -> & -> & -> & Q9 & Q10 & Q11) HRP HPRES Hbv2 HH2.
  pose proof (PAOUT_CAP _ _ _ _ _ Q1) as Hcap2.
  set (bp := PML.ps_bptr ps2) in *. set (bc := PML.ps_bcap ps2) in *. set (sb := PML.ps_sb ps2) in *. set (sc := PML.ps_scap ps2) in *.
  assert (Hblk2 : PML.ps_blocks ps2 = [(bp, bc); (sb, sc)]) by reflexivity. rewrite Hblk2 in HH2. cbn [app] in HH2.
  destruct (hio_wf L SCFG HI HIok _ _ _ _ HH2) as (Hwf2 & _).
  destruct (Hwf2 (bp, bc) ltac:(left; reflexivity)) as ((X0 & X1 & X2 & X3 & X4) & _). destruct (Hwf2 (sb, sc) ltac:(right; left; reflexivity)) as ((Y0 & Y1 & Y2 & Y3 & Y4) & _).
  cbn [fst snd] in *.
  assert (Hcode : 0 <= code <= 31) by (destruct Q5 as (_ & _ & [Z0|[Z1 _]]); lia).
  set (ghosts := [Z_to_bv 64 code; Z_to_bv 64 bp; Z_to_bv 64 (bc / 2); Z_to_bv 64 sb; Z_to_bv 64 sc]).
  set (E2 := CH2.retEx E' nx ghosts R2).
  assert (Hag2 : env_agree nx E' E2) by apply CH2.retEx_agree.
  assert (Hh : 0 <= bc / 2 < 2 ^ 64) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  unfold hl_ceil in *.
  assert (G0' : bv_unsigned (ev E2 nx) = code) by (pose proof (PB6.ghost_val E' nx ghosts R2 0 code eq_refl ltac:(cbn; lia) ltac:(lia)) as G; rewrite Nat.add_0_r in G; exact G).
  assert (G1 : bv_unsigned (ev E2 (nx + 1)) = bp) by (apply (PB6.ghost_val E' nx ghosts R2 1 bp eq_refl); [cbn; lia | lia]).
  assert (G2 : bv_unsigned (ev E2 (nx + 2)) = bc / 2) by (apply (PB6.ghost_val E' nx ghosts R2 2 (bc / 2) eq_refl); [cbn; lia | exact Hh]).
  assert (G3 : bv_unsigned (ev E2 (nx + 3)) = sb) by (apply (PB6.ghost_val E' nx ghosts R2 3 sb eq_refl); [cbn; lia | lia]).
  assert (G4 : bv_unsigned (ev E2 (nx + 4)) = sc) by (apply (PB6.ghost_val E' nx ghosts R2 4 sc eq_refl); [cbn; lia | lia]).
  assert (Hbcd : bc = 2 * (bc / 2)) by (pose proof (Z.div_mod bc 2 ltac:(lia)) as D; rewrite Hcap2 in D; lia).
  assert (Hden2 : CH2.den E2 (nth j BLS []) = PML.ps_blocks ps2).
  { rewrite B6, Hblk2. unfold CH2.den. cbn [map fst snd]. unfold PSU.emul2. fold (PB.uv E2 (APC.escale 2 (EVar (nx + 2)))). rewrite PB.uv_escale. unfold PB.uv. cbn [edenot].
    rewrite G1, G2, G3, G4, <- Hbcd, Z.mod_small by lia. reflexivity. }
  assert (GA0 : ev E2 (nx + 9) = getr R2 10%bv).
  { unfold E2, CH2.retEx, CH2.retE. change (length ghosts) with 5%nat. replace (nx + 9)%nat with (nx + 5 + 4)%nat by lia. rewrite APS.ext_list_at by (cbn; lia). reflexivity. }
  destruct (UPOST R2 M2 cr' ps2 code g' eg' E2 (conj Q1 (conj Q2 (conj Q3 (conj Q4 (conj Q5 (conj Q6 (conj Q7 (conj Q8 (conj Q8a (conj Q8b (conj Q8c (conj Q9 (conj Q10 Q11))))))))))))) Hag2 G0' GA0 Hden2 HPRES)
    as [HXI2 HC2].
  unfold PML.cfg. rewrite <- LS.
  eapply (RET fx2 R2 M2 model2 ghosts LBo (PMX.W_parx paddr vaddr eaddr s2addr) eq_refl HFP2 (CH2.regs_preserved_kept R' R2 HRP) I HPRES).
  - intros b Hb. exact Hb.
  - (* [comment removed for export] *)
    intros w a Hw Hin. unfold PMX.W_parx, PML.W_par, W_enc in Hw. unfold PSU2X.wregsx, PSU.statics_wregs, VSX.wregs.
    apply in_app_or in Hw. destruct Hw as [[<-|[<-|[<-|[<-|[]]]]]|[<-|[<-|[<-|[<-|[]]]]]]; unfold L5.in_rng in Hin; cbn [fst snd] in Hin.
    + exists (PBx, PKx, ELit 272). split; [left; reflexivity|]. unfold CH2.in_reg. rewrite Hop. unfold elenZ. cbn [edenot]. rewrite u64_of_Z by lia. lia.
    + exists (EB, EK, ELit 16). split; [right; left; reflexivity|]. unfold CH2.in_reg. rewrite Hoe. unfold elenZ. cbn [edenot]. rewrite u64_of_Z by lia. lia.
    + exists (ELit 0, 0xdb5c0, ELit 2). split; [right; right; left; reflexivity|]. unfold CH2.in_reg, estart, elenZ. cbn [a_base a_off edenot]. rewrite (u64_of_Z 0), (u64_of_Z 2) by lia. lia.
    + exists (ELit 0, 0xfd058, ELit 544). split; [right; right; right; left; reflexivity|]. unfold CH2.in_reg, estart, elenZ. cbn [a_base a_off edenot]. rewrite (u64_of_Z 0), (u64_of_Z 544) by lia. lia.
    + exists (VB, 0 + 264, ELit 40). split; [do 4 right; left; reflexivity|].
      unfold CH2.in_reg, estart, elenZ. cbn [a_base a_off edenot]. unfold PB.uv in HV. rewrite HV. rewrite u64_of_Z by lia. unfold O_STACK in Hin. lia.
    + exists (VB, 0 + 400, ELit 4). split; [do 5 right; left; reflexivity|].
      unfold CH2.in_reg, estart, elenZ. cbn [a_base a_off edenot]. unfold PB.uv in HV. rewrite HV. rewrite u64_of_Z by lia. unfold O_DEPTH in Hin. lia.
    + exists (VSX.S2V, 0, ELit 24). split; [do 6 right; left; reflexivity|].
      unfold CH2.in_reg, estart, elenZ, VSX.S2V. cbn [a_base a_off edenot]. rewrite HS2. rewrite u64_of_Z by lia. lia.
    + exists (ELit 0, PML.LIT_LO, ELit VSX.LIT_LEN). split; [do 7 right; left; reflexivity|].
      unfold CH2.in_reg, estart, elenZ. cbn [a_base a_off edenot]. rewrite !u64_of_Z by (unfold VSX.LIT_LEN, PML.LIT_LO; lia). rewrite <- LITLEN. lia.
  - (* [comment removed for export] *)
    intros X HX _. fold E2. rewrite <- Hnx in HX. fold nx in HX.
    assert (HagE2 : env_agree NF E0 E2) by (eapply CC.env_agree_trans; [exact HagE' | eapply CC.env_agree_le; [exact Hag2 | lia]]).
    assert (Hest : estart E2 (SA EB EK) = eaddr) by (rewrite (PB.estart_agree NF E0 E2 EB EK HagE2 EB_frozen); exact EADDR).
    destruct OE as (O1 & O2 & O3). destruct Q5 as (Hu32 & _ & _). rewrite LS.
    destruct HX as [<-|[<-|[]]].
    + eapply PB.kword32_intro with (A := eaddr) (z := code); [exact Hest | lia | lia | | exact Hu32].
      cbn [edenot]. rewrite <- G0'. symmetry. apply Z_to_bv_bv_unsigned.
    + cbn [kentry_ok edenot]. rewrite G0'. lia.
  - (* [comment removed for export] *)
    fold E2.
    assert (Hcur : CH2.cur (CH2V.LBr LBo eghost gB eg') BLS j E2 = PML.ps_blocks ps2 ++ LBo ++ g_lbv eg').
    { unfold CH2.cur, CH2V.LBr, gB. rewrite Hden2. reflexivity. }
    destruct (CH2V.amb_callee_xV L HI LYI LYE NF E0 M00 model0 LBo sp0 d W BLS eghost gB CredV STK SCR_pos NF32 DEF0 g eg' M0c CSCR 5%nat c ps cj ci i j E E' R' M' model
                E2 M2 model2 LBo (PMX.W_parx paddr vaddr eaddr s2addr) cr' HOKV CF HPRES) as [OK2 HA2].
    + intros b Hb. exact Hb.
    + intros w a Hw Hin (_ & _ & _ & Hout).
      unfold PMX.W_parx in Hw. apply in_app_or in Hw as [Hw|Hw].
      * destruct (WPAR_in w a Hw Hin) as (w' & Hw' & Hin'). exact (Hout w' Hw' Hin').
      * exact (Hout w (W_ENC w Hw) Hin).
    + exact Hbv2.
    + rewrite Hcur. rewrite Hblk2. cbn [app]. exact HH2.
    + exact Hag2.
    + exact HC2.
    + apply (CH2V.amb3V_intro L HI NF E0 M00 model0 LBo sp0 d W BLS eghost gB CredV XIv eg' M2 j E2 M2 model2 OK2).
      split; [exact HA2 | exact HXI2].
Qed.
End InstXWU.

Section WADAPTU.
Context {SCFG_P : ScfgP}.
Variables (L : heap_layout) (HI : heap_iface) (RM : PMW.refmodel).
Definition roomW (f : PMW.fname) (inp : PML.pstate -> list Z -> list Z -> list Z) (th : THW RM) : eghost -> PML.pstate -> Prop :=
  fun eg ps => let '(w, x, c) := th in PMW.wroomrU RM eg (PMW.rm_step RM f c (inp ps w x)).
Lemma gbxw_EU : forall f MIn inp WFin BBin PAin PAout pc scr Args Rel,
  PMW.ptrans_gbxwU L HI RM f MIn inp WFin BBin PAin PAout pc scr Args Rel ->
  forall th : THW RM, ptrans_gbxEU L HI WFin BBin PAin PAout pc scr (argsXW RM Args MIn th) Rel (expostW RM f inp th) (roomW f inp th).
Proof.
  intros f MIn inp WFin BBin PAin PAout pc scr Args Rel HW [[w x] c] LBo cr sp r P V E S2 B kx bx g ps eg fx R M model K HH Hmo HK HFP PRE POST.
  apply (HW LBo cr sp r P V E S2 B kx bx g ps eg w x c fx R M model K HH Hmo HK HFP).
  - destruct PRE as (H1 & (HA & HWB & HMI) & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18).
    exact (conj H1 (conj HA (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10 (conj H11 (conj H12 (conj H13 (conj H14 (conj H15 (conj H16 (conj H17 (conj HWB (conj HMI H18))))))))))))))))))).
  - intros fx' R' M' model' LB' cr' LBk W0 HFP' PO. apply (POST fx' R' M' model' LB' cr' LBk W0 HFP').
    destruct PO as (ps' & code & g' & eg' & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q16 & Q17).
    exists ps', code, g', eg'.
    exact (conj Q1 (conj Q2 (conj Q3 (conj Q4 (conj Q5 (conj Q6 (conj Q7 (conj Q8 (conj Q9 (conj Q10 (conj Q11 (conj Q12 (conj Q13 (conj Q14 (conj Q15 (conj Q16 Q17)))))))))))))))).
Qed.
End WADAPTU.

End PB6WU.
