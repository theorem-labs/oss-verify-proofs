(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u PmLibDefs_u PmLibSpecs_u PmLayout_u PmCurDefs_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSums_u ParseSums2_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmParse Require Import ParseSomeKn. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSpecs_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmParse Require Import ParseProve. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseBridges_u ParseBridges2_u ParseBridges3_u ParseBridges4_u ParseBridges5_u ParseBridges6_u ParseSomeAt_u ParseSomeSem_u ParseSomeSemC_u ParseSomeCurC_u ParseSomeChk_u ParseSomeChk2_u ParseSomeChk3_u ParseSomeChk4_u ParseSomeChk5_u ParseSomeChk6_u ParseSomeA_u ParseSomeB_u ParseSomeC_u ParseSomeD_u ParseSomeD2_u ParseSomeE_u ParseSomeF_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Import PSMC. Import PSM2.
Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module PSM7.
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
End PSM7.
Lemma tail_ok : CH2.leaves_all PSMC.G.CPS PSMC.G.TAGS PSM7.tail_chk = true.
Proof. vmc_refl. Qed.

Module PST.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation uv := PB.uv.
Lemma areg : forall E' regs R' (n : nat) (x : reg) e z, regs_ok E' regs R' -> ridx x = n -> bv_eqb x 0 = false -> nth n regs (ELit 0) = e -> uv E' e = z -> getr R' x = Z_to_bv 64 z.
Proof. intros E' regs R' n x e z HR Hn Hx He Hz. rewrite (PSE.reg_at E' regs R' n x HR Hn Hx), He, <- Hz. unfold uv, PB.uv. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Section K.
Context {SCFG_P : ScfgP}.
Variable I : PSI.inst.
Local Abbreviation L := (PSI.iL I).      Local Abbreviation HI := (PSI.iHI I).    Local Abbreviation LBo := (PSI.iLBo I).  Local Abbreviation cr := (PSI.icr I).
Local Abbreviation sp := (PSI.isp I).    Local Abbreviation r := (PSI.ir I).      Local Abbreviation P := (PSI.iP I).      Local Abbreviation V := (PSI.iV I).      Local Abbreviation E := (PSI.iE I).
Local Abbreviation B := (PSI.iB I).      Local Abbreviation kx := (PSI.ikx I).    Local Abbreviation bx := (PSI.ibx I).    Local Abbreviation g := (PSI.ig I).      Local Abbreviation ps := (PSI.ips I).
Local Abbreviation fx := (PSI.ifx I).    Local Abbreviation R := (PSI.iR I).      Local Abbreviation M := (PSI.iM I).      Local Abbreviation model := (PSI.imodel I).  Local Abbreviation K := (PSI.iK I).
Local Abbreviation HIok := (PSI.iHIok I).  Local Abbreviation LAY := (PSI.iLAY I).
Local Abbreviation E0 := (PSI.E0 I).     Local Abbreviation W := (PSI.W I).       Local Abbreviation Cred := (PSI.Cred I). Local Abbreviation XI := (PSI.XI I).
Local Abbreviation seg := (PSI.seg I).   Local Abbreviation wend := (PSI.wend I). Local Abbreviation wlen := (PSI.wlen I). Local Abbreviation st0 := (PSI.st0 I).
Local Abbreviation HAMB := (CH2.heap_amb L HI GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred).
Local Abbreviation AMB3 := (CH2.amb3 L HI GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred XI).
Local Abbreviation is_leaf := (CH2.is_leaf G.CPS G.TAGS).
Let LS : hl_segs L = RSEGS := PmLayout.ly_segs L LAY.
Hypothesis SETEC_OK : PMS.set_ec_spec L.

Lemma leaf_tail : forall i c k ps1, is_leaf i c k ps1 (CC.TOther SETEC) -> CH2.ret_of G.RETS i k = None -> CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok i c ps1.
Proof.
  intros i c k ps1 IL Hret fx' E1 R1 M1 model1 E' R' M' HAt [HAmb HX] HFP Hag HLF _.
  pose proof (CH2.leaves_all_sound _ _ _ tail_ok _ _ _ _ _ IL) as X. unfold PSM7.tail_chk in X. rewrite Z.eqb_refl, Hret in X.
  destruct (kind_of i) eqn:K1; try discriminate X. destruct (PSM2.ldelta i c ps1) as [[[[[pv lv] pe] ce] d]|] eqn:HLD; [|discriminate X].
  destruct (nth 11 (CA.ps_reglist ps1) (ELit 0)) as [code| | | | | | |] eqn:Hcode; try discriminate X.
  apply andb_prop in X as [X Xne]. apply andb_prop in X as [X Dc]. apply andb_prop in X as [X Ddone]. apply andb_prop in X as [X Dmore]. apply andb_prop in X as [X Dnst]. apply andb_prop in X as [X Dsst].
  apply andb_prop in X as [X Dst]. apply andb_prop in X as [X C31]. apply andb_prop in X as [X C1]. apply andb_prop in X as [X Ha0]. apply andb_prop in X as [X Hnf]. apply andb_prop in X as [X Hkeep].
  apply andb_prop in X as [X Hall]. apply andb_prop in X as [Hi0 Hpc]. apply Nat.eqb_eq in Hi0. apply Z.eqb_eq in Hpc. apply Nat.leb_le in Hnf. apply expr_eqb_eq in Ha0. apply Z.leb_le in C1, C31.

  pose proof (CH2.leaf_amb3 L HI HIok (PB.LYI_ L LAY) (PB.LYE_ L LAY) (PmLayout.ly_ro L LAY) GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred (PSI.STKF I) PSI.SCRP PSI.NF32 (PSI.U2 I) (PSI.W_OK I) (PSI.WRS_OK I)
                G.CPS G.TAGS heap_ok3 i c k ps1 SETEC IL E1 E' R1 R' M1 M' model1 HAt HAmb Hag HLF) as HA'.
  pose proof HA' as (Hmo1 & Hbv1 & HagE1 & (cr1 & HH1 & HC1) & Hfr1 & Hdf1).
  assert (HagE' : env_agree GT.NF E0 E') by (eapply CC.env_agree_trans; [exact HagE1 | eapply CC.env_agree_le; [exact Hag | exact Hnf]]).
  assert (KEEP : forall x : reg, In (ridx x) CL5.CSAVED -> getr R' x = getr R x).
  { intros x Hx. assert (Hx32 : (ridx x < GT.NF)%nat) by (unfold CL5.CSAVED in Hx; cbn [In] in Hx; pose proof PSI.NF32; intuition lia).
    rewrite (CL.ps_keeps_sound (hl_segs L) c ps1 E0 E' R' M1 M' CL5.CSAVED GT.NF x HLF Hkeep HagE' Hx Hx32). exact (PSI.EV0 I x). }
  assert (HRP : regs_preserved R R') by (intros x Hx; apply KEEP; exact (CL5.csaved_in x Hx)).
  pose proof (PSI.iHentry I) as (Hra & Hraok & Hsp & Htp & Hstk).
  assert (HRL : regs_ok E' (CA.ps_reglist ps1) R') by exact (CH2.leaf_regs_ok L GT.NF sp G.HDECL (PSI.STKF I) PSI.SCRP PSI.NF32 c ps1 E' R' M1 M' Hall HLF).
  destruct (PSB.FRZ I E' HagE') as (F1 & F2 & F3 & _ & _ & _ & _ & F8 & _).
  assert (Ga0 : getr R' 10%bv = Z_to_bv 64 E) by exact (areg E' _ R' 10 10%bv _ E HRL eq_refl eq_refl Ha0 F3).
  assert (Ga1 : getr R' 11%bv = Z_to_bv 64 code) by (rewrite (PSE.reg_at E' _ R' 11 11%bv HRL eq_refl eq_refl), Hcode; reflexivity).

  pose proof (PSB.leaf_know I c ps1 E' R' M1 M' HLF) as HKc.
  unfold PSI.XI in HX. destruct HX as (X1 & _ & _ & HX). rewrite K1, (PSB.lview_vw _ _ _ _ _ _ _ (PSX.ldelta_lview _ _ _ _ _ _ _ _ HLD)) in HX. destruct HX as (bm & bd & stack & buf & HC & HS & HW & HB & HWS & HR & HE).
  destruct (PSB.leaf_state I i c k ps1 _ pv lv pe ce d E1 R1 E' R' M1 M' model1 bm bd stack buf IL HLD HAt HAmb Hag HLF HC)
    as (_ & HK & _ & L1 & L2 & L3 & L4 & L5 & L6 & L7 & (AG1 & AG2 & AG3) & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15 & L16 & HSB & FR2 & FRI & HPAX & Hden & HEQ).
  pose proof HC as (HC1' & HC2 & HC3 & HC4 & HC5 & HC6 & HC6b & HC7 & HC8 & HC9).
  destruct (PSM2.d_st d) eqn:Est; [discriminate Dst|]. destruct (PSM2.d_sst d) eqn:Es; [discriminate Dsst|]. destruct (PSM2.d_nst d) eqn:En; [discriminate Dnst|]. destruct (PSM2.d_done d) eqn:Ed; [discriminate Ddone|].
  destruct (PSM2.d_clr d) eqn:Ec; [discriminate Dc|]. destruct (PSM2.d_more d) as [[| |]|] eqn:Em; try discriminate Dmore. cbn [PSB.newv] in *.
  destruct (HPAX false bd L11 ltac:(rewrite L12; exact HC9)) as (bufm & HPA & Hlen & _). rewrite (HEQ false bd bufm) in HPA. rewrite L8, L9, L10 in HPA. rewrite L13 in Hlen.
  set (psc := PSI.ps_of pv pe ce E1 bm bd stack buf) in *. set (w' := PB4.win_of (uv E' (PB4.pv_wptr lv)) wend) in *.
  set (ps' := PSS.upd psc (PML.ps_st psc) (PML.ps_sst psc) (PML.ps_nst psc) false bd (uv E1 ce) (uv E1 pe) bufm w') in *.
  assert (HLSg : PML.ls_ok g M') by exact (PSB.ls_frame M1 M' g FRI (PSI.iHG I) HS).
  pose proof (PSI.iHEC I) as (_ & HEd & _). pose proof (PSI.OBJR I) as (O1 & O2 & O3 & O4 & O5 & O6 & O7). pose proof (PSI.SPF I) as (S1 & S2 & S3 & S4 & S5 & S6).
  assert (HdE' : L5.defined M' E 16) by (apply (PSB.amb_def I i E1 M' model1 E 16 HA' HEd); clear - O6 O7; lia).
  assert (Hstk' : L5C.stk (hl_sptop L) M' sp PMS.SETEC_SCR).
  { apply (L5C.stk_weaken _ _ _ (PMS.PSOME_SCR PML.STRTOD_SCR_V)); [|unfold PMS.SETEC_SCR; change (PMS.PSOME_SCR PML.STRTOD_SCR_V) with 10096; clear; lia].
    destruct Hstk as (T1 & T2 & T3 & T4 & T5). split; [exact T1|]. split; [exact T2|]. split; [exact T3|]. split; [exact T4|].
    change (PMS.PSOME_SCR PML.STRTOD_SCR_V) with 10096. rewrite PSI.SCRV in X1. apply (PSB.grows_def M1 M'); [exact (CC.lf_grows _ _ _ _ _ _ _ HLF) | exact X1]. }
  pose proof Hmo1 as (Hm1 & Hm2 & Hm3).
  rewrite Hpc, LS.
  apply (SETEC_OK E code sp r g fx' R' M' model1 K Hm1 Hm2 (PSI.iHKnil I) HFP).
  { split; [split; [rewrite (KEEP 1%bv ltac:(left; reflexivity)); exact Hra|]; split; [exact Hraok|]; split; [rewrite (KEEP 2%bv ltac:(right; left; reflexivity)); exact Hsp|];
            split; [rewrite (KEEP 4%bv ltac:(right; right; right; left; reflexivity)); exact Htp | exact Hstk']|].
    split; [exact Ga0|]. split; [exact Ga1|]. split; [clear - C1 C31; lia|]. split; [exact HdE'|]. split; [exact (PSI.iOE I)|]. split; [exact HLSg | exact (PSI.iHG I)]. }
  intros fx2 R2 M2 HFP2 (Hec & Hls2 & _) HRP2 HFB HGR.

  assert (HA2 : HAMB i E1 M2 model1).
  { apply (CH2.amb_pure_step L HI HIok (PB.LYI_ L LAY) (PB.LYE_ L LAY) (PmLayout.ly_ro L LAY) GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred (PSI.STKF I) PSI.SCRP PSI.NF32 (PSI.W_OK I) i i E1 E1 M' M2 model1 HA');
      [| exact HGR | apply CC.env_agree_refl | reflexivity | intros cr0 Hc0; exact Hc0].
    intros a Hnfoot. apply HFB. intros r0 [<-|Hr0] Hin.
    - apply Hnfoot. left. rewrite PSI.SCRV. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. unfold PMS.SETEC_SCR in Hin. clear - Hin. lia.
    - apply Hnfoot. right. left. exists r0. split; [|exact Hin]. unfold PSI.W, PMS.W_parc, PML.W_par. cbn [In app] in Hr0 |- *. clear - Hr0. tauto. }
  pose proof (CH2.amb_hpres L HI (PB.LYI_ L LAY) (PB.LYE_ L LAY) GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred (PSI.STKF I) PSI.NF32 i E1 M2 model1 HA2 (PSI.DEF0 I)) as HP2.
  pose proof HA2 as (_ & _ & _ & (cr2 & HH2 & HC2') & _ & _).
  unfold CH2.cur in HH2. rewrite Hden in HH2.

  destruct (PSB.bls2' _ _ _ _ _ IL) as (pe2 & ce2 & sbe & sce & HBL). destruct (PSB.own_blocks I i E1 M' model1 pe2 ce2 sbe sce HA' HBL) as ((C0 & C1' & C2 & C3 & C4) & (D0 & D1 & D2 & D3 & D4) & _).
  pose proof Hden as Hden'. rewrite HBL, !PB.den_cons in Hden'. change (CH2.den E1 []) with (@nil (Z * Z)) in Hden'. injection Hden' as Eb1 Eb2 Eb3 Eb4.
  rewrite Eb1 in C0, C1', C4. rewrite Eb2 in C1', C4. rewrite Eb3 in D0, D1, D4. rewrite Eb4 in D1, D4.
  pose proof (PSB.CEIL I) as CL. rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY) in C1', D1. unfold hl_ceil in *.
  pose proof (PSI.iAP2 I) as AP2. unfold PML.apart in AP2.
  set (F := (sp - PMS.SETEC_SCR, PMS.SETEC_SCR) :: [(E, 16); (0xd4df8, 2); (0xf6848, 544)]) in *.
  assert (OUT : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= sp - 256 \/ sp <= a) -> (a + n <= E \/ E + 16 <= a) -> (a + n <= 0xd4df8 \/ 0xf6848 + 544 <= a) -> PB2.out F a n).
  { intros a n A0 A1 A2 A3 A4. split; [exact A0|]. split; [exact A1|]. intros q Hq r0 Hr0. unfold F in Hr0. cbn [In] in Hr0. unfold L5.in_rng.
    destruct Hr0 as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; unfold PMS.SETEC_SCR; clear - Hq A2 A3 A4; lia. }
  assert (HPA2 : PML.parser_at M2 P ps').
  { apply (PB2.parser_at_fr F M' M2 HFB HGR P ps'); [| | | exact HPA].
    - apply OUT; clear - O1 O2 O3 AP2 S2; lia.
    - unfold ps', PSS.upd. cbn [PML.ps_bptr PML.ps_bcap]. apply OUT; clear - C0 C1' C4 CL O1 O6 S2 S3 S4; lia.
    - unfold ps', PSS.upd, psc, PSI.ps_of. cbn [PML.ps_sb PML.ps_scap]. apply OUT; clear - D0 D1 D4 CL O1 O6 S2 S3 S4; lia. }
  pose proof (PSI.WIN I) as (W0 & W1 & _).
  assert (Hwl1 : PML.winlen psc = wend - uv E1 (PB4.pv_wptr pv)) by (unfold psc, PSI.ps_of; rewrite HC4; apply PSB.winlen_of; clear - W0 HC5; lia).
  pose proof (PSB.ne_chk_sound E' M' _ _ 2 HKc Xne ltac:(clear; lia)) as Hne2. rewrite F8 in Hne2.
  apply (PSI.iHcont I fx2 R2 M2 model1 (PML.ps_blocks ps' ++ LBo) cr2 LBo W HFP2); [| exact (L5.regs_preserved_trans _ _ _ HRP HRP2) | exact HP2 | exact Hbv1 | exact HH2].
  exists ps', code, (PML.regJ g).
  split; [exact HPA2|]. split; [split; [apply PSS.wf_stop; [exact HW | exact (proj1 HW) | exact (proj1 (proj2 HW))] | intros Q; unfold ps', PSS.upd in Q; cbn in Q; discriminate Q]|].
  split; [unfold ps', PSS.upd, w'; apply PSX.win_ok_of; [exact (PSX.win_def I i E1 M2 model1 HA2) | clear - HC5 L14 L15 L16; lia]|].
  split; [split; [|exact (proj2 HB)]; unfold ps', PSS.upd, w'; cbn [PML.ps_buf]; rewrite PSB.winlen_of by (clear - W0 HC5 L14 L15 L16; lia); unfold PML.buf_need; cbn [PML.ps_more andb];
          pose proof (PSB.buf_need_range psc HW) as Hbn; destruct HB as [HB1 _]; unfold psc at 1, PSI.ps_of in HB1; cbn [PML.ps_buf] in HB1; clear - HB1 Hwl1 Hlen HC6 L14 L15 Hbn; lia|].
  split; [exact Hec|]. split; [intros _; reflexivity|]. split; [exact Hls2|]. split; [right; split; [reflexivity | clear - C1; lia]|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [apply (PSI.cred_of_blocks I i E1 cr2 ps'); [rewrite Hden; reflexivity | exact (proj1 (proj2 (proj2 (proj2 HW)))) | exact HC2']|].
  split; [split; [left; clear - C1; lia|]; split; [intros Q; exfalso; exact (Hne2 Q) | intros _ Q; exfalso; clear - Q C1; lia]|].
  split; [intros Q; exfalso; clear - Q C1; lia | intros Q; exfalso; clear - Q C1; lia].
Qed.
End K.
End PST.
