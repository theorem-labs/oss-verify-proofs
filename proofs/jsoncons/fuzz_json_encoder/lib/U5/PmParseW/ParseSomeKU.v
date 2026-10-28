(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5 PmLibSpecsX_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX CutHeap2V.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseSums_u5 ParseSums2_u5 ParseSums2X_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmParse Require Import ParseSomeKn. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseSpecs_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmParse Require Import ParseProve. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5 ParseBridges2_u5 ParseBridges3_u5 ParseBridges4_u5 ParseBridgesX_u5 ParseBridges5_u5 ParseBridges6_u5 ParseSomeAt_u5 ParseSomeSem_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParseW Require Import ParseSomeYWU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParseW Require Import ParseSomeChk_u5 ParseSomeChk2_u5 ParseSomeChk3_u5 ParseSomeChk4_u5 ParseSomeChk5_u5 ParseSomeChk6_u5 ParseSomeAU ParseSomeBU ParseSomeBXU ParseSomeCU ParseSomeD_u5 ParseSomeD2U ParseSomeEU ParseSomeFU.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import SmallKnX. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmSmall Require Import SmallPtX_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmSmall Require Import VisitSumsX. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmSmall Require Import VisitBridgeX_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Import PSMC. Import PSM2.
Module PSM7U.
Definition is_none {A} (o : option A) : bool := match o with None => true | Some _ => false end.
Definition tail_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TOther pc =>
      if Z.eqb pc SETEC then
        match CH2.ret_of G.RETS i k with
        | Some _ => true
        | None =>
            match kind_of i, ldelta i c ps, nth 11 (CA.ps_reglist ps) (ELit 0) with
            | KInv, Some (pv, lv, pe, ce, d), ELit code =>
                (Nat.eqb i 0 && Z.eqb (SR.ps_pc ps) SETEC && CH2.all_regs_chk ps && CL.ps_keeps ps CL5.CSAVED && Nat.leb GT.NF (CC.cp_nx c) && expr_eqb (nth 10 (CA.ps_reglist ps) (ELit 0)) Eb && (1 <=? code) && (code <=? 31)
                 && is_none (d_st d) && is_none (d_sst d) && is_none (d_nst d) && (match d_more d with Some 0 => true | _ => false end) && is_none (d_done d) && negb (d_clr d)
                 && ne_chk (SR.ps_cells ps) (EVar 42) 2)%bool
            | _, _, _ => false
            end
        end
      else true
  | _ => true
  end.
End PSM7U.
Lemma tail_ok : CH2.leaves_all PSMC.G.CPS PSMC.G.TAGS PSM7U.tail_chk = true.
Proof. vm_compute. reflexivity. Qed.

Module PSTU.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation uv := PB.uv.
Lemma areg : forall E' regs R' (n : nat) (x : reg) e z, regs_ok E' regs R' -> ridx x = n -> bv_eqb x 0 = false -> nth n regs (ELit 0) = e -> uv E' e = z -> getr R' x = Z_to_bv 64 z.
Proof. intros E' regs R' n x e z HR Hn Hx He Hz. rewrite (PSEU.reg_at E' regs R' n x HR Hn Hx), He, <- Hz. unfold uv, PB.uv. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Section K.
Context {SCFG_P : ScfgP}.
Variable I : PSIU.inst.
(* [comment removed for export] *)
Variables (eg : PMES.eghost) (M0c : mem).
Local Abbreviation L := (PSIU.iL I).      Local Abbreviation HI := (PSIU.iHI I).    Local Abbreviation LBo := (PSIU.iLBo I).  Local Abbreviation cr := (PSIU.icr I).
Local Abbreviation sp := (PSIU.isp I).    Local Abbreviation r := (PSIU.ir I).      Local Abbreviation P := (PSIU.iP I).      Local Abbreviation V := (PSIU.iV I).      Local Abbreviation E := (PSIU.iE I).
Local Abbreviation B := (PSIU.iB I).      Local Abbreviation kx := (PSIU.kxe I eg).    Local Abbreviation bx := (PSIU.ibx I).    Local Abbreviation g := (PSIU.ig I).      Local Abbreviation ps := (PSIU.ips I).
Local Abbreviation fx := (PSIU.ifx I).    Local Abbreviation R := (PSIU.iR I).      Local Abbreviation M := (PSIU.iM I).      Local Abbreviation model := (PSIU.imodel I).  Local Abbreviation K := (PSIU.iK I).
Local Abbreviation HIok := (PSIU.iHIok I).  Local Abbreviation LAY := (PSIU.iLAY I).
Local Abbreviation E0 := (PSIU.E0 I).     Local Abbreviation W := (PSIU.W I).       Local Abbreviation Cred := (PSIU.Cred I eg). Local Abbreviation XI := (PSIU.XI I eg).
Local Abbreviation XIv := (PSIU.XIv I eg).  Local Abbreviation LBr := (PSIU.LBr I eg).  Local Abbreviation S2 := (PSIU.iS2 I).
Local Abbreviation seg := (PSIU.seg I).   Local Abbreviation wend := (PSIU.wend I). Local Abbreviation wlen := (PSIU.wlen I). Local Abbreviation st0 := (PSIU.st0 I).
Local Abbreviation HAMB := (CH2.heap_amb L HI GT.NF E0 M0c model LBr sp G.HDECL W G.BLS Cred).
Local Abbreviation AMB3 := (CH2.amb3 L HI GT.NF E0 M0c model LBr sp G.HDECL W G.BLS Cred XIv).
Local Abbreviation is_leaf := (CH2.is_leaf G.CPS G.TAGS).
Let LS : hl_segs L = RSEGS := PmLayout.ly_segs L LAY.
Hypothesis OKV : CH2V.okV L M LBo sp G.HDECL W M0c.

(* [comment removed for export] *)
Hypothesis SETEC_OK : PMS.set_ec_spec L.

Lemma leaf_tail : forall i c k ps1, is_leaf i c k ps1 (CC.TOther SETEC) -> CH2.ret_of G.RETS i k = None -> CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok i c ps1.
Proof.
  intros i c k ps1 IL Hret fx' E1 R1 M1 model1 E' R' M' HAt [HAmb (HX & HXV & HSM)] HFP Hag HLF _. pose proof HX as HXW.
  pose proof (CH2.leaves_all_sound _ _ _ tail_ok _ _ _ _ _ IL) as X. unfold PSM7U.tail_chk in X. rewrite Z.eqb_refl, Hret in X.
  destruct (kind_of i) eqn:K1; try discriminate X. destruct (PSM2.ldelta i c ps1) as [[[[[pv lv] pe] ce] d]|] eqn:HLD; [|discriminate X].
  destruct (nth 11 (CA.ps_reglist ps1) (ELit 0)) as [code| | | | | | |] eqn:Hcode; try discriminate X.
  apply andb_prop in X as [X Xne]. apply andb_prop in X as [X Dc]. apply andb_prop in X as [X Ddone]. apply andb_prop in X as [X Dmore]. apply andb_prop in X as [X Dnst]. apply andb_prop in X as [X Dsst].
  apply andb_prop in X as [X Dst]. apply andb_prop in X as [X C31]. apply andb_prop in X as [X C1]. apply andb_prop in X as [X Ha0]. apply andb_prop in X as [X Hnf]. apply andb_prop in X as [X Hkeep].
  apply andb_prop in X as [X Hall]. apply andb_prop in X as [Hi0 Hpc]. apply Nat.eqb_eq in Hi0. apply Z.eqb_eq in Hpc. apply Nat.leb_le in Hnf. apply expr_eqb_eq in Ha0. apply Z.leb_le in C1, C31.
  (* [comment removed for export] *)
  pose proof (CH2.leaf_amb3 L HI HIok (PB.LYI_ L LAY) (PB.LYE_ L LAY) (PmLayout.ly_ro L LAY) GT.NF E0 M0c model LBr sp G.HDECL W G.BLS Cred (PSIU.STKF I) PSIU.SCRP PSIU.NF32 (PSIU.U2 I) (PSIU.W_OK I) (PSIU.WRS_OK I)
                G.CPS G.TAGS heap_ok3 i c k ps1 SETEC IL E1 E' R1 R' M1 M' model1 HAt HAmb Hag HLF) as HA'.
  pose proof HA' as (Hmo1 & Hbv1 & HagE1 & (cr1 & HH1 & HC1) & Hfr1 & Hdf1).
  assert (HagE' : env_agree GT.NF E0 E') by (eapply CC.env_agree_trans; [exact HagE1 | eapply CC.env_agree_le; [exact Hag | exact Hnf]]).
  assert (KEEP : forall x : reg, In (ridx x) CL5.CSAVED -> getr R' x = getr R x).
  { intros x Hx. assert (Hx32 : (ridx x < GT.NF)%nat) by (unfold CL5.CSAVED in Hx; cbn [In] in Hx; pose proof PSIU.NF32; intuition lia).
    rewrite (CL.ps_keeps_sound (hl_segs L) c ps1 E0 E' R' M1 M' CL5.CSAVED GT.NF x HLF Hkeep HagE' Hx Hx32). exact (PSIU.EV0 I x). }
  assert (HRP : regs_preserved R R') by (intros x Hx; apply KEEP; exact (CL5.csaved_in x Hx)).
  pose proof (PSIU.iHentry I) as (Hra & Hraok & Hsp & Htp & Hstk).
  assert (HRL : regs_ok E' (CA.ps_reglist ps1) R') by exact (CH2.leaf_regs_ok L GT.NF sp G.HDECL (PSIU.STKF I) PSIU.SCRP PSIU.NF32 c ps1 E' R' M1 M' Hall HLF).
  destruct (PSBU.FRZ I E' HagE') as (F1 & F2 & F3 & _ & _ & _ & _ & F8 & _).
  assert (Ga0 : getr R' 10%bv = Z_to_bv 64 E) by exact (areg E' _ R' 10 10%bv _ E HRL eq_refl eq_refl Ha0 F3).
  assert (Ga1 : getr R' 11%bv = Z_to_bv 64 code) by (rewrite (PSEU.reg_at E' _ R' 11 11%bv HRL eq_refl eq_refl), Hcode; reflexivity).
  (* [comment removed for export] *)
  pose proof (PSBU.leaf_know I c ps1 E' R' M1 M' HLF) as HKc.
  unfold PSIU.XI in HX. destruct HX as (X1 & _ & _ & XD & HX). rewrite K1, (PSBU.lview_vw _ _ _ _ _ _ _ (PSXU.ldelta_lview _ _ _ _ _ _ _ _ HLD)) in HX. destruct HX as (bm & bd & stack & buf & HC & HS & HW & HB & HWS & HR & HE).
  destruct (PSBU.leaf_state I eg M0c OKV i c k ps1 _ pv lv pe ce d E1 R1 E' R' M1 M' model1 bm bd stack buf IL HLD HAt HAmb Hag HLF HC)
    as (_ & HK & _ & L1 & L2 & L3 & L4 & L5 & L6 & L7 & (AG1 & AG2 & AG3) & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15 & L16 & HSB & FR2 & FRI & HPAX & Hden & HEQ).
  pose proof HC as (HC1' & HC2 & HC3 & HC4 & HC5 & HC6 & HC6b & HC7 & HC8 & HC9 & HCK).
  destruct (PSM2.d_st d) eqn:Est; [discriminate Dst|]. destruct (PSM2.d_sst d) eqn:Es; [discriminate Dsst|]. destruct (PSM2.d_nst d) eqn:En; [discriminate Dnst|]. destruct (PSM2.d_done d) eqn:Ed; [discriminate Ddone|].
  destruct (PSM2.d_clr d) eqn:Ec; [discriminate Dc|]. destruct (PSM2.d_more d) as [[| |]|] eqn:Em; try discriminate Dmore. cbn [PSBU.newv] in *.
  destruct (HPAX false bd L11 ltac:(rewrite L12; exact HC9)) as (bufm & HPA & Hlen & _). rewrite (HEQ false bd bufm) in HPA. rewrite L8, L9, L10 in HPA. rewrite L13 in Hlen.
  set (psc := PSIU.ps_of pv pe ce E1 bm bd stack buf) in *. set (w' := PB4.win_of (uv E' (PB4.pv_wptr lv)) wend) in *.
  set (ps' := PSS.upd psc (PML.ps_st psc) (PML.ps_sst psc) (PML.ps_nst psc) false bd (uv E1 ce) (uv E1 pe) bufm w') in *.
  assert (HLSg : PML.ls_ok g M') by exact (PSBU.ls_frame M1 M' g FRI (PSIU.iHG I) HS).
  pose proof (PSIU.iHEC I) as (_ & HEd & _). pose proof (PSIU.OBJR I) as (O1 & O2 & O3 & O4 & O5 & O6 & O7). pose proof (PSIU.SPF I) as (S1 & S2 & S3 & S4 & S5 & S6).
  assert (HdE' : L5.defined M' E 16) by (apply (PSBU.amb_def I eg M0c OKV i E1 M' model1 E 16 HA' HEd); clear - O6 O7; lia).
  assert (Hstk' : L5C.stk (hl_sptop L) M' sp PMS.SETEC_SCR).
  { apply (L5C.stk_weaken _ _ _ (PMX.PSOMEX_SCR PSIU.SSCR PSIU.WDX)); [|unfold PMS.SETEC_SCR; change (PMX.PSOMEX_SCR PSIU.SSCR PSIU.WDX) with 12800; clear; lia].
    destruct Hstk as (T1 & T2 & T3 & T4 & T5). split; [exact T1|]. split; [exact T2|]. split; [exact T3|]. split; [exact T4|].
    change (PMX.PSOMEX_SCR PSIU.SSCR PSIU.WDX) with 12800. rewrite PSIU.SCRV in X1. apply (PSBU.grows_def M1 M'); [exact (CC.lf_grows _ _ _ _ _ _ _ HLF) | exact X1]. }
  pose proof Hmo1 as (Hm1 & Hm2 & Hm3).
  rewrite Hpc, LS.
  apply (SETEC_OK E code sp r g fx' R' M' model1 K Hm1 Hm2 (PSIU.iHKnil I) HFP).
  { split; [split; [rewrite (KEEP 1%bv ltac:(left; reflexivity)); exact Hra|]; split; [exact Hraok|]; split; [rewrite (KEEP 2%bv ltac:(right; left; reflexivity)); exact Hsp|];
            split; [rewrite (KEEP 4%bv ltac:(right; right; right; left; reflexivity)); exact Htp | exact Hstk']|].
    split; [exact Ga0|]. split; [exact Ga1|]. split; [clear - C1 C31; lia|]. split; [exact HdE'|]. split; [exact (PSIU.iOE I)|]. split; [exact HLSg | exact (PSIU.iHG I)]. }
  intros fx2 R2 M2 HFP2 (Hec & Hls2 & _) HRP2 HFB HGR.
  (* [comment removed for export] *)
  assert (HA2 : HAMB i E1 M2 model1).
  { apply (CH2.amb_pure_step L HI HIok (PB.LYI_ L LAY) (PB.LYE_ L LAY) (PmLayout.ly_ro L LAY) GT.NF E0 M0c model LBr sp G.HDECL W G.BLS Cred (PSIU.STKF I) PSIU.SCRP PSIU.NF32 (PSIU.W_OK I) i i E1 E1 M' M2 model1 HA');
      [| exact HGR | apply CC.env_agree_refl | reflexivity | intros cr0 Hc0; exact Hc0].
    intros a Hnfoot. apply HFB. intros r0 [<-|Hr0] Hin.
    - apply Hnfoot. left. rewrite PSIU.SCRV. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. unfold PMS.SETEC_SCR in Hin. clear - Hin. lia.
    - apply Hnfoot. right. left. exists r0. split; [|exact Hin]. unfold PSIU.W, PMX.W_parx, PML.W_par, PMES.W_enc. cbn [In app] in Hr0 |- *. clear - Hr0. tauto. }
  (* [comment removed for export] *)
  assert (HXI2 : PSIU.xinv I M2 eg).
  { pose proof (PSIU.OBJR I) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7). pose proof (PSIU.OBJRX I) as (XR1 & XR2 & XR3 & XR4 & XR5 & XA1 & XA2 & XA3 & XA4 & XA5). unfold PML.apart in XA1, XA2, XA3, XA4, XA5.
    pose proof (PSBU.CEIL I) as CLx.
    apply (PSBXU.xinv_frame_but I eg M0c i E1 M' M' M2 model1 sp PMS.SETEC_SCR [(E, 16); (0xdb5c0, 2); (0xfd058, 544)] HA' HFB); [clear; lia | unfold PMS.SETEC_SCR; clear -CLx; lia | | exact (PSBU.xinv_leaf I eg M0c i c k ps1 _ E1 E' R' M1 M' M1 model1 IL HAmb HagE' Hag HLF HXV)].
    intros w Hw. destruct Hw as [<-|[<-|[<-|[]]]]; cbn [fst snd]; unfold PMES.ENC_SIZE, PML.LIT_LO, PML.LIT_HI; rewrite ?(PmLayout.ly_img_lo L LAY), ?(PmLayout.ly_img_hi L LAY); (split; [lia | split; [lia | lia]]). }
  pose proof (CH2.amb_hpres L HI (PB.LYI_ L LAY) (PB.LYE_ L LAY) GT.NF E0 M0c model LBr sp G.HDECL W G.BLS Cred (PSIU.STKF I) PSIU.NF32 i E1 M2 model1 HA2 (CH2V.okV_def0 L M LBo sp G.HDECL W M0c OKV)) as HP2.
  pose proof HA2 as (_ & _ & _ & (cr2 & HH2 & HC2') & _ & _).
  unfold CH2.cur in HH2. rewrite Hden in HH2.
  (* [comment removed for export] *)
  destruct (PSBU.bls2' _ _ _ _ _ IL) as (pe2 & ce2 & sbe & sce & HBL). destruct (PSBU.own_blocks I eg M0c i E1 M' model1 pe2 ce2 sbe sce HA' HBL) as ((C0 & C1' & C2 & C3 & C4) & (D0 & D1 & D2 & D3 & D4) & _).
  pose proof Hden as Hden'. rewrite HBL, !PB.den_cons in Hden'. change (CH2.den E1 []) with (@nil (Z * Z)) in Hden'. injection Hden' as Eb1 Eb2 Eb3 Eb4.
  rewrite Eb1 in C0, C1', C4. rewrite Eb2 in C1', C4. rewrite Eb3 in D0, D1, D4. rewrite Eb4 in D1, D4.
  pose proof (PSBU.CEIL I) as CL. rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY) in C1', D1. unfold hl_ceil in *.
  pose proof (PSIU.iAP2 I) as AP2. unfold PML.apart in AP2.
  set (F := (sp - PMS.SETEC_SCR, PMS.SETEC_SCR) :: [(E, 16); (0xdb5c0, 2); (0xfd058, 544)]) in *.
  assert (OUT : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= sp - 256 \/ sp <= a) -> (a + n <= E \/ E + 16 <= a) -> (a + n <= 0xdb5c0 \/ 0xfd058 + 544 <= a) -> PB2.out F a n).
  { intros a n A0 A1 A2 A3 A4. split; [exact A0|]. split; [exact A1|]. intros q Hq r0 Hr0. unfold F in Hr0. cbn [In] in Hr0. unfold L5.in_rng.
    destruct Hr0 as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; unfold PMS.SETEC_SCR; clear - Hq A2 A3 A4; lia. }
  assert (HPA2 : PML.parser_at M2 P ps').
  { apply (PB2.parser_at_fr F M' M2 HFB HGR P ps'); [| | | exact HPA].
    - apply OUT; clear - O1 O2 O3 AP2 S2; lia.
    - unfold ps', PSS.upd. cbn [PML.ps_bptr PML.ps_bcap]. apply OUT; clear - C0 C1' C4 CL O1 O6 S2 S3 S4; lia.
    - unfold ps', PSS.upd, psc, PSIU.ps_of. cbn [PML.ps_sb PML.ps_scap]. apply OUT; clear - D0 D1 D4 CL O1 O6 S2 S3 S4; lia. }
  pose proof (PSIU.WIN I) as (W0 & W1 & _).
  assert (Hwl1 : PML.winlen psc = wend - uv E1 (PB4.pv_wptr pv)) by (unfold psc, PSIU.ps_of; rewrite HC4; apply PSBU.winlen_of; clear - W0 HC5; lia).
  pose proof (PSBU.ne_chk_sound E' M' _ _ 2 HKc Xne ltac:(clear; lia)) as Hne2. rewrite F8 in Hne2.
  apply (PSIU.iHcont I fx2 R2 M2 model1 (PML.ps_blocks ps' ++ LBr) cr2 LBo W HFP2); [| exact (L5.regs_preserved_trans _ _ _ HRP HRP2) | exact (CH2V.hpres_rebase L GT.NF M LBo sp G.HDECL W PMES.eghost PMES.g_lbv PSIU.NF32 eg M0c M2 OKV HP2) | exact Hbv1 | exact HH2].
  exists ps', code, PML.LS2, eg.
  split; [exact HPA2|]. split; [apply PSS.wf_stop; [exact HW | exact (proj1 HW) | exact (proj1 (proj2 HW))]|].
  split; [unfold ps', PSS.upd, w'; apply PSXU.win_ok_of; [exact (PSXU.win_def I eg M0c OKV i E1 M2 model1 HA2) | clear - HC5 L14 L15 L16; lia]|].
  split; [split; [|exact (proj2 HB)]; unfold ps', PSS.upd, w'; cbn [PML.ps_buf]; rewrite PSBU.winlen_of by (clear - W0 HC5 L14 L15 L16; lia); unfold PML.buf_need; cbn [PML.ps_more andb];
          pose proof (PSBU.buf_need_range psc HW) as Hbn; destruct HB as [HB1 _]; unfold psc at 1, PSIU.ps_of in HB1; cbn [PML.ps_buf] in HB1; clear - HB1 Hwl1 Hlen HC6 L14 L15 Hbn; lia|].
  split; [exact Hec|]. split; [intros _; reflexivity|]. split; [exact Hls2|]. split; [right; split; [reflexivity | clear - C1; lia]|].
  split; [exact (proj1 HXI2)|]. split; [exact (proj2 HXI2)|]. split; [intros Q; exfalso; clear - Q C1; lia|].      (* [comment removed for export] *)
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [apply (PSIU.cred_of_blocks I eg i E1 cr2 ps'); [rewrite Hden; reflexivity | exact (proj1 (proj2 (proj2 (proj2 HW)))) | exact HC2']|].
  assert (HWE : PSIU.WERR I eg code).      (* [comment removed for export] *)
  { subst i. destruct (PSYWU.setec_entry_w I eg M0c c k ps1 E1 E' R' M1 M' M1 model1 IL HAmb Hag HLF HSM) as [HW1 Ha1]. rewrite Hcode in Ha1. injection Ha1 as ->. exact HW1. }
  split; [|exact (PSXU.obl_exit_err I eg ps' code M2 HWE ltac:(clear - C1; lia))].      (* [comment removed for export] *)
  split; [left; clear - C1; lia|]. split; [intros Q; exfalso; exact (Hne2 Q)|]. split; [intros _ Q; exfalso; clear - Q C1; lia | intros Q; exfalso; clear - Q C1; lia].
Qed.
End K.
End PSTU.
