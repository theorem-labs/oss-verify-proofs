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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSums_u ParseSums2_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmParse Require Import ParseSomeKn. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSpecs_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmParse Require Import ParseProve. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseBridges_u ParseBridges2_u ParseBridges3_u ParseBridges4_u ParseSomeAt_u ParseSomeChk_u ParseSomeChk2_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Import PSMC.
Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module PSI.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation uv := PB.uv.
Abbreviation SSCR := PML.STRTOD_SCR_V.

Definition box (X : Prop) : Prop := X.
Definition boxed {X : Prop} (x : X) : box X := x.

Definition seg_of (ps : PML.pstate) : Z := fst (PSA.wincells (PML.ps_win ps)).
Definition wend_of (ps : PML.pstate) : Z := snd (PSA.wincells (PML.ps_win ps)).

Record inst {SCFG_P : ScfgP} : Type := Inst {
  iL : heap_layout; iHI : heap_iface;
  iHIok : heap_iface_ok iL SCFG iHI;
  iLAY : PmLayout.pm0_layout iL;
  iLBo : list (Z * Z); icr : credit; isp : Z; ir : Z; iP : Z; iV : Z; iE : Z; iB : Z; ikx : Z; ibx : Z; ig : PML.ls_state; ips : PML.pstate;
  ifx : FPState; iR : bvmap 5 word; iM : mem; imodel : Model; iK : ShapeAlg.TSet;
  iHH : hi_heap iHI (PML.ps_blocks ips ++ iLBo) icr iM (m_vmmaps imodel);
  iHmo : PML.model_ok imodel;
  iHKnil : iK [];
  iHfp : PML.fp_ok ifx;
  iHentry : PML.entry iL iR iM isp ir (PMS.PSOME_SCR SSCR);
  iHa0 : PML.a0 iR iP; iHa1 : PML.a1 iR iV; iHa2 : PML.a2 iR iE;
  iHmore : PML.ps_more ips = true;
  iHPA : PML.parser_at iM iP ips;
  iHWF : PML.wf_ps ips;
  iHLV : PMCUR.lvl_ok ips;
  iHWIN : PML.win_ok iM iLBo ips;
  iHBB : PML.buf_bound ips iB;
  iHVIS : PML.vis_at iM iV;
  iHEC : PML.ec_at iM iE 0;
  iHLS : PML.ls_ok ig iM;
  iHG : ig <> PML.LS0;
  iHPC : PML.pcredit_x iL icr ips ikx ibx;
  iOP : PML.obj_on_stack iL isp iP 272; iOV : PML.obj_on_stack iL isp iV 48; iOE : PML.obj_on_stack iL isp iE 16;
  iAP1 : PML.apart iP 272 iV 48; iAP2 : PML.apart iP 272 iE 16; iAP3 : PML.apart iV 48 iE 16;

  iline0 : Z; ipos0 : Z; iwinb : list Z;
  iHline0 : PML.u64 iM (iP + 160) iline0; iHlr : 0 <= iline0 < 2 ^ 64;
  iHpos0 : PML.u64 iM (iP + 168) ipos0; iHpr : 0 <= ipos0 < 2 ^ 64;
  iHwinb : L5.bytes_at RSEGS iM (seg_of ips) iwinb /\ Z.of_nat (length iwinb) = wend_of ips - seg_of ips;

  iHcont : forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (LB' : list (Z * Z)) (cr' : credit) (LBk : list (Z * Z)) (W : list L5.range),
   PML.fp_ok fx' ->
   (exists (ps' : PML.pstate) (code : Z) (g' : PML.ls_state),
      PML.parser_at M' iP ps' /\ PMCUR.wf_c ps' /\ PML.win_ok M' iLBo ps' /\ PML.buf_bound ps' iB /\ PML.ec_at M' iE code /\
      (code <> 0 -> PML.ps_more ps' = false) /\ PML.ls_ok g' M' /\ (g' = ig \/ (g' = PML.regJ ig /\ code <> 0)) /\
      LB' = PML.ps_blocks ps' ++ iLBo /\ LBk = iLBo /\ W = PMS.W_parc iP iV iE /\ PML.pcredit_x iL cr' ps' ikx ibx /\
      ((code <> 0 \/ PML.ps_more ps' = false \/ PMS.win_exhausted ps') /\
       (PML.ps_st ips = PML.ST_ACCEPT -> code = 0 /\ PML.ps_more ps' = false /\ PML.ps_done ps' = true) /\
       (PMS.win_exhausted ips -> code = 0 -> PML.ps_more ps' = true -> In (PML.ps_st ips) [PML.ST_NUMBER; PML.ST_CR] /\ ~ In (PML.ps_st ps') [PML.ST_NUMBER; PML.ST_CR])) /\
      PMCUR.cur_post RSEGS ips ps' code M' iV) ->
   regs_preserved iR R' -> L5C.hpres iL LBk isp (PMS.PSOME_SCR SSCR) W iM M' -> model_but_vm imodel model' -> hi_heap iHI LB' cr' M' (m_vmmaps model') ->
   srealizes RSEGS SCFG (@PML.cfg fx' R' ir M' model') iK
}.

Definition RANK (ps : PML.pstate) : Z :=
  if PML.ps_more ps then (if Z.eqb (PML.ps_st ps) PML.ST_CR then 3 else if (Z.eqb (PML.ps_st ps) PML.ST_SLASH_SLASH || Z.eqb (PML.ps_st ps) PML.ST_NUMBER)%bool then 2 else 1) else 0.
Lemma RANK_range : forall ps, 0 <= RANK ps <= 3.
Proof. intros ps. unfold RANK. destruct (PML.ps_more ps); [|lia]. destruct (_ =? _); [lia|]. destruct (_ || _)%bool; lia. Qed.

Section A.
Context {SCFG_P : ScfgP}.
Variable I : inst.
Local Abbreviation L := (iL I).      Local Abbreviation HI := (iHI I).    Local Abbreviation LBo := (iLBo I).  Local Abbreviation cr := (icr I).
Local Abbreviation sp := (isp I).    Local Abbreviation r := (ir I).      Local Abbreviation P := (iP I).      Local Abbreviation V := (iV I).      Local Abbreviation E := (iE I).
Local Abbreviation B := (iB I).      Local Abbreviation kx := (ikx I).    Local Abbreviation bx := (ibx I).    Local Abbreviation g := (ig I).      Local Abbreviation ps := (ips I).
Local Abbreviation fx := (ifx I).    Local Abbreviation R := (iR I).      Local Abbreviation M := (iM I).      Local Abbreviation model := (imodel I).  Local Abbreviation K := (iK I).
Local Abbreviation HIok := (iHIok I).  Local Abbreviation LAY := (iLAY I).

Definition seg : Z := seg_of ps.
Definition wend : Z := wend_of ps.
Definition wlen : Z := wend - seg.
Definition bcap : Z := PML.ps_bcap ps.
Definition k0 : Z := bcap / 2.
Definition bptr : Z := PML.ps_bptr ps.
Definition size0 : Z := Z.of_nat (length (PML.ps_buf ps)).
Definition sb : Z := PML.ps_sb ps.
Definition scap : Z := PML.ps_scap ps.
Definition slen : Z := Z.of_nat (length (PML.ps_stack ps)).
Definition level : Z := PML.ps_level ps.
Definition st0 : Z := PML.ps_st ps.
Definition sst0 : Z := PML.ps_sst ps.
Definition nst0 : Z := PML.ps_nst ps.
Definition more0 : Z := PML.b2z (PML.ps_more ps).
Definition done0 : Z := PML.b2z (PML.ps_done ps).

Definition E0 : env :=
  Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) [seg; wlen; B; k0; size0; bptr; sb; slen; scap; level; st0; sst0; nst0; more0; done0; iline0 I; ipos0 I] 0)))
      (fun id => match id with 1%nat => map (Z_to_bv 8) (iwinb I) | _ => [] end).

Lemma SPF : sp mod 16 = 0 /\ 0x7fff7f800000 + 10096 <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47 /\ L5.defined M (sp - 10096) 10096
            /\ hl_sptop L - 2 ^ 23 + 10096 <= sp.
Proof.
  pose proof (iHentry I) as Hentry. destruct Hentry as (_ & _ & _ & _ & Hstk). pose proof (L5C.stk_floor _ _ _ _ Hstk) as F. pose proof (L5C.stk_window _ _ _ _ Hstk) as (W1 & W2 & W3).
  destruct Hstk as (S1 & S2 & S3 & S4 & S5). change (PMS.PSOME_SCR SSCR) with 10096 in *.
  repeat split; try lia; try assumption.
Qed.

Lemma WIN : 0 <= seg /\ seg <= wend <= 2 ^ 47 /\ 0 <= wlen <= 16384 /\ L5.defined M seg wlen /\
  ((seg = 0 /\ wend = 0) \/ exists ch, In (ch, 16384) LBo /\ ch <= seg /\ wend <= ch + 16384 /\ block_range L ch 16384).
Proof.
  pose proof (iHWIN I) as HW. pose proof (iHPA I) as HPA. unfold PML.win_ok in HW. unfold PML.parser_at in HPA.
  destruct HPA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CW & _).
  unfold wlen, wend, seg, wend_of, seg_of. destruct (PML.ps_win ps) as [[p e]|]; cbn [PSA.wincells fst snd].
  - destruct CW as (_ & _ & Hpe). destruct HW as (ch & Hch & Hc1 & Hc2 & Hwd).
    destruct (hio_wf (iL I) SCFG (iHI I) (iHIok I) _ _ _ _ (iHH I)) as (Hwf & _).
    destruct (Hwf (ch, 16384) ltac:(right; right; exact Hch)) as (BR & _). pose proof BR as (B0 & _ & _ & _ & B4). cbn [fst snd] in *.
    pose proof SPF as (_ & _ & _ & S4 & _). unfold hl_ceil in B4.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hwd|]. right. exists ch. split; [exact Hch|]. split; [exact Hc1|]. split; [exact Hc2 | exact BR].
  - split; [lia|]. split; [lia|]. split; [lia|]. split; [intros i Hi; lia | left; split; reflexivity].
Qed.

Lemma NUM :
  block_range L bptr bcap /\ block_range L sb scap /\ L5.defined M bptr bcap /\ L5.defined M sb scap /\
  (bptr + bcap <= sb \/ sb + scap <= bptr) /\ (bptr + bcap <= seg \/ seg + wlen <= bptr) /\ (sb + scap <= seg \/ seg + wlen <= sb) /\
  bcap = 2 * k0 /\ bcap mod 8 = 0 /\ 264 <= bcap <= 2 ^ 27 /\ size0 < bcap /\ 0 <= size0 /\ 1 <= slen <= 1027 /\ slen <= scap /\ 66 <= scap <= 1056 /\
  0 <= sst0 <= 11 /\ 0 <= nst0 <= 7 /\ more0 = 1 /\ 0 <= done0 <= 1 /\ size0 + wlen <= B /\ 0 <= B < 2 ^ 26 /\ 0 <= level <= 1024 /\ 1 <= st0 <= 28.
Proof.
  pose proof (iHPA I) as HPA. unfold PML.parser_at in HPA.
  destruct HPA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CW & _ & _ & _ & _ & _ & _ & _ & Hstr & Hb264 & _ & _ & _ & _ & Hsl & _).
  destruct (hio_wf (iL I) SCFG (iHI I) (iHIok I) _ _ _ _ (iHH I)) as (Hwf & Hnd & _).
  assert (I1 : In (bptr, bcap) (PML.ps_blocks ps ++ LBo)) by (left; reflexivity).
  assert (I2 : In (sb, scap) (PML.ps_blocks ps ++ LBo)) by (right; left; reflexivity).
  destruct (Hwf _ I1) as (BR1 & BD1 & BA1). destruct (Hwf _ I2) as (BR2 & BD2 & BA2). cbn [fst snd] in *.
  unfold PML.ps_blocks in Hnd. fold bptr bcap sb scap in Hnd. cbn [map fst app] in Hnd. inversion Hnd as [|x l N1 N2]; subst. inversion N2 as [|x l N3 N4]; subst.
  assert (Nsb : sb <> bptr) by (intros X; apply N1; apply list_elem_of_In; left; exact X).
  pose proof (L5C.blocks_apart_in _ _ _ sb scap BA1 (L5C.in_lb_remove_neq bptr sb scap _ I2 Nsb)) as A1.
  assert (A23 : (bptr + bcap <= seg \/ seg + wlen <= bptr) /\ (sb + scap <= seg \/ seg + wlen <= sb)).
  { pose proof WIN as (W0 & W1 & W2 & _ & [[W4 W5]|(ch & Hch & Hc1 & Hc2 & BRc)]).
    - destruct BR1 as (? & _), BR2 as (? & _). unfold wlen. split; right; lia.
    - assert (I3 : In (ch, 16384) (PML.ps_blocks ps ++ LBo)) by (right; right; exact Hch).
      assert (Nch1 : ch <> bptr) by (intros X; apply N1; apply list_elem_of_In; right; apply in_map_iff; exists (ch, 16384); split; [exact X | exact Hch]).
      assert (Nch2 : ch <> sb) by (intros X; apply N3; apply list_elem_of_In; apply in_map_iff; exists (ch, 16384); split; [exact X | exact Hch]).
      pose proof (L5C.blocks_apart_in _ _ _ ch 16384 BA1 (L5C.in_lb_remove_neq bptr ch 16384 _ I3 Nch1)) as A2.
      pose proof (L5C.blocks_apart_in _ _ _ ch 16384 BA2 (L5C.in_lb_remove_neq sb ch 16384 _ I3 Nch2)) as A3.
      unfold wlen, wend in *. split; lia. }
  destruct A23 as [A2 A3].
  destruct Hstr as (_ & Hc8 & Hlt). fold bcap size0 in Hc8, Hlt.
  assert (Hk : bcap = 2 * k0).
  { unfold k0. pose proof (Z.div_mod bcap 8 ltac:(lia)) as D. rewrite Hc8 in D. rewrite D at 2. replace (8 * (bcap / 8) + 0) with ((4 * (bcap / 8)) * 2) by lia. rewrite Z.div_mul by lia. lia. }
  pose proof (iHWF I) as HWF. destruct HWF as (W1 & W2 & W3 & W4 & (C & T & W5 & W6 & W7)).
  pose proof (iHPC I) as HPC. destruct HPC as (_ & _ & (HP27 & _)). pose proof (iHBB I) as HBB. destruct HBB as (HB1 & HB2).
  assert (Hwl : PML.winlen ps = wlen).
  { unfold PML.winlen, wlen, wend, seg, wend_of, seg_of. destruct (PML.ps_win ps) as [[p e]|]; cbn [PSA.wincells fst snd]; lia. }
  assert (Hbn : 0 <= PML.buf_need ps).
  { unfold PML.buf_need. destruct (_ && _)%bool; [|lia]. unfold PML.esc_need. fold sst0 in W1 |- *. assert (Hs : exists n, sst0 = Z.of_nat n /\ (n <= 11)%nat) by (exists (Z.to_nat sst0); lia).
    destruct Hs as (n & -> & Hn). rewrite Nat2Z.id. do 12 (destruct n as [|n]; [cbn; lia|]). lia. }
  rewrite Hwl in HB1. fold size0 in HB1.
  assert (Hs1 : 1 <= slen) by (unfold slen; rewrite W5; cbn [length]; lia).
  assert (Hs2 : slen <= 1027) by (unfold slen; lia).
  assert (Hsc : 66 <= scap <= 1056) by (fold scap in W4; cbn [In] in W4; lia).
  pose proof WIN as (_ & _ & WL & _).
  destruct (W7 (iHmore I)) as (W8 & W9 & W10 & _). unfold PML.handled in W10. fold st0 in W10. fold level in W9.
  assert (HM : more0 = 1) by (unfold more0; rewrite (iHmore I); reflexivity).
  fold bcap in HP27. fold sst0 in W1. fold nst0 in W2.
  destruct BR1 as (? & ? & ? & ? & ?), BR2 as (? & ? & ? & ? & ?).
  assert (Hs0 : 0 <= size0) by (unfold size0; lia).
  repeat split; try assumption; try lia; try (unfold done0; destruct (PML.ps_done ps); cbn; lia); try (unfold size0; lia).
Qed.

Lemma EV0 : forall x : reg, ev E0 (ridx x) = getr R x.
Proof. intros x. apply CL5.ev_reg. Qed.
Lemma VV : ev E0 2 = Z_to_bv 64 sp /\ ev E0 4 = Z_to_bv 64 PML.TP /\ ev E0 10 = Z_to_bv 64 P /\ ev E0 11 = Z_to_bv 64 V /\ ev E0 12 = Z_to_bv 64 E.
Proof.
  pose proof (iHentry I) as Hentry. destruct Hentry as (_ & _ & Hsp & Htp & _).
  repeat split; [rewrite <- Hsp; exact (EV0 2%bv) | rewrite <- Htp; exact (EV0 4%bv) | rewrite <- (iHa0 I); exact (EV0 10%bv) | rewrite <- (iHa1 I); exact (EV0 11%bv)
                 | rewrite <- (iHa2 I); exact (EV0 12%bv)].
Qed.
Lemma OBJR : 2 ^ 40 <= sp - 10096 /\ sp <= P /\ P + 272 <= 2 ^ 47 /\ sp <= V /\ V + 48 <= 2 ^ 47 /\ sp <= E /\ E + 16 <= 2 ^ 47.
Proof.
  pose proof SPF as (S1 & S2 & S3 & S4 & _). pose proof (iOP I) as (OP1 & OP2 & _). pose proof (iOV I) as (OV1 & OV2 & _). pose proof (iOE I) as (OE1 & OE2 & _). lia.
Qed.
Lemma UU : bv_unsigned (ev E0 2) = sp /\ bv_unsigned (ev E0 10) = P /\ bv_unsigned (ev E0 11) = V /\ bv_unsigned (ev E0 12) = E /\
  bv_unsigned (ev E0 32) = seg /\ bv_unsigned (ev E0 33) = wlen /\ bv_unsigned (ev E0 34) = B /\ bv_unsigned (ev E0 35) = k0 /\ bv_unsigned (ev E0 36) = size0 /\ bv_unsigned (ev E0 37) = bptr /\
  bv_unsigned (ev E0 38) = sb /\ bv_unsigned (ev E0 39) = slen /\ bv_unsigned (ev E0 40) = scap /\ bv_unsigned (ev E0 41) = level /\ bv_unsigned (ev E0 42) = st0 /\ bv_unsigned (ev E0 43) = sst0 /\
  bv_unsigned (ev E0 44) = nst0 /\ bv_unsigned (ev E0 45) = more0 /\ bv_unsigned (ev E0 46) = done0 /\ bv_unsigned (ev E0 47) = iline0 I /\ bv_unsigned (ev E0 48) = ipos0 I.
Proof.
  pose proof VV as (V2 & _ & V10 & V11 & V12). pose proof OBJR as (O1 & O2 & O3 & O4 & O5 & O6 & O7).
  pose proof NUM as ((C0 & C1 & C2 & C3 & C4) & (D0 & D1 & D2 & D3 & D4) & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & N14 & N15 & N16 & N17 & N18 & N19 & N20 & N21 & N22).
  pose proof WIN as (W0 & W1 & W2 & _). pose proof (iHlr I) as Q1. pose proof (iHpr I) as Q2. pose proof SPF as (_ & _ & _ & S4 & _). unfold hl_ceil in *.
  rewrite V2, V10, V11, V12.
  repeat split; try (apply u64_of_Z; lia).
Qed.

Definition X0 : PSK.pexprs := PSK.PX (EVar 41) (EVar 32) (EVar 42) (EVar 43) (EVar 44) (EVar 45) (EVar 46) (EVar 35) (EVar 36) (EVar 37) (EVar 38) (EVar 39) (EVar 40) (EVar 47) (EVar 48) (ELit 0).
Lemma cp0_know : CC.cp_know G.cp0 = PSK.pkn CONSTS false (EVar 10) (EVar 11) (EVar 12) (EVar 2) (EVar 32) (EVar 33) X0 ++ [KRange (APC.esub (APC.escale 4 (EVar 32)) (EVar 33)) 0 1125899906842624].
Proof. vmc_refl. Qed.

Ltac edl := rewrite <- (Z_to_bv_bv_unsigned _ (edenot E0 _)); f_equal; apply CL5.u_lin; [lin_eval; rw_atoms; lia | lia].
Lemma WINC : PSA.wincells (PML.ps_win ps) = (seg, wend).
Proof. unfold seg, wend, seg_of, wend_of. destruct (PSA.wincells (PML.ps_win ps)); reflexivity. Qed.

Lemma At0 : CC.At RSEGS G.cp0 E0 R M.
Proof.
  pose proof UU as (U2 & U10 & U11 & U12 & U32 & U33 & U34 & U35 & U36 & U37 & U38 & U39 & U40 & U41 & U42 & U43 & U44 & U45 & U46 & U47 & U48).
  pose proof NUM as (BRb & BRs & Hdb & Hdsb & A1 & A2 & A3 & N8 & N9 & N10 & N11 & N12 & N13 & N14 & N15 & N16 & N17 & N18 & N19 & N20 & N21 & N22 & N23).
  pose proof WIN as (W0 & W1 & W2 & Hwd & W4). pose proof OBJR as (O1 & O2 & O3 & O4 & O5 & O6 & O7). pose proof SPF as (Hsp16 & S2 & S3 & S4 & S5 & S6).
  pose proof (PmLayout.ly_img_lo L LAY) as ILO. pose proof (PmLayout.ly_img_hi L LAY) as IHI.
  split; [exact (regs_ok_id R _ _)|]. rewrite cp0_know. unfold know_ok. apply Forall_app. split; [unfold PSK.pkn; apply Forall_app; split |].
  -
    apply (PSA.pkn_sem_ok CONSTS eq_refl eq_refl (conj eq_refl eq_refl) ltac:(cbn; lia) (EVar 10) (EVar 11) (EVar 12) (EVar 2) (EVar 32) (EVar 33) X0 E0 M P E V sp seg wlen ps (iline0 I) (ipos0 I) 0) with (L := iL I);
      unfold PB.uv; cbn [edenot PSK.x_level PSK.x_wptr PSK.x_st PSK.x_sst PSK.x_nst PSK.x_more PSK.x_done PSK.x_k PSK.x_size PSK.x_p PSK.x_sb PSK.x_slen PSK.x_scap PSK.x_line PSK.x_pos PSK.x_ec X0];
      try assumption; try (rewrite ?WINC; cbn [fst snd]; first [assumption | unfold wlen; lia | cbn [PSK.c_scr CONSTS]; lia]).
    + unfold wlen in *. lia.
    + exact (iHPA I).
    + rewrite U35. unfold bcap in N8. lia.
    + exact (iHline0 I).
    + exact (iHpos0 I).
    + apply u64_of_Z. lia.
    + destruct (iHEC I) as (X & _). exact X.
    + fold level. lia.
    + fold st0 sst0 nst0. lia.
    + fold size0 bcap. lia.
    + fold slen scap. lia.
    + exact (iLAY I).
    + fold bptr bcap. split; assumption.
    + fold sb scap. split; assumption.
    + fold bptr bcap sb scap. split; assumption.
  -
    destruct (iHEC I) as (HE32 & HEdef & _). destruct (iHwinb I) as (Hwb & Hwbl). fold seg wend in Hwb, Hwbl. fold wlen in Hwbl. destruct (iHLS I) as (IMGRO & _).
    pose proof (iOP I) as (_ & _ & HP8). pose proof (iHPA I) as HPA. unfold PML.parser_at in HPA.
    assert (HdefP : L5.defined M P 272) by (repeat (destruct HPA as [_ HPA]); exact HPA).
    assert (DJW : box ((seg = 0 /\ wlen = 0) \/ seg + wlen <= sp - 10096 /\ (seg + wlen <= 0x10000 \/ 0xf8000 <= seg))).
    { unfold box. destruct W4 as [[W4 W5]|(ch & Hch & Hc1 & Hc2 & (B0 & B1 & B2 & B3 & B4))]; [left; unfold wlen; lia | right].
      pose proof (L5C.stk_floor _ _ _ _ (proj2 (proj2 (proj2 (proj2 (iHentry I)))))) as F. change (PMS.PSOME_SCR SSCR) with 10096 in F. unfold hl_ceil in B4. rewrite ILO, IHI in B1. unfold wlen in *. lia. }
    pose proof (iAP1 I) as AP1'. pose proof (iAP2 I) as AP2'. pose proof (iAP3 I) as AP3'. unfold PML.apart in AP1', AP2', AP3'.
    assert (DJ : box ((P + 272 <= V \/ V + 48 <= P) /\ (P + 272 <= E \/ E + 16 <= P) /\ (V + 48 <= E \/ E + 16 <= V))) by (unfold box; repeat split; assumption).
    clear A1 A2 A3 AP1' AP2' AP3' W4 HPA.
    unfold PSK.pkn_frz, PSK.objs_f, PSK.frame, PSK.disj_f, PSK.hull, PSK.kdisj, PSK.kw. cbn [app PSK.c_scr PSK.c_vt_visitor PSK.c_img_lo PSK.c_img_hi PSK.c_hull_lo PSK.c_hull_hi CONSTS].
    repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_wr.
    + e_range.
    + e_align HP8.
    + eapply CL5.kwr_intro; [ev_start | ev_len | lia | lia | lia | eapply (L5.defined_sub _ _ _ _ _ HEdef); lia].
    + e_range.
    + eapply CL5.kword64_intro with (A := V) (z := PML.VT_VISITOR); [ev_start | lia | lia | reflexivity | exact (proj1 (iHVIS I))].
    + e_range.
    + eapply CL5.kblob_intro with (bs := iwinb I) (A := seg); [ev_start | unfold elenZ; cbn [edenot]; rewrite U33; lia | lia | lia | lia | reflexivity | exact Hwb | rewrite Hwbl; exact Hwd].
    + eapply CL5.kunk_intro; [ev_start | ev_len | lia | lia | lia | eapply (L5.defined_sub _ _ _ _ _ Hwd); lia].
    + e_range.
    + e_range.
    + eapply CL5.kunk_intro; [ev_start | ev_len | lia | lia | lia | eapply (L5.defined_sub _ _ _ _ _ S5); lia].
    + eapply CL5.kwr_intro; [ev_start | ev_len | lia | lia | lia | eapply (L5.defined_sub _ _ _ _ _ S5); lia].
    + e_range.
    + e_align Hsp16.
    + cbn [kentry_ok]. split; [lia | split; [lia | exact IMGRO]].
    + e_disj.
    + e_disj.
    + e_disj.
    + unfold box in DJW. eapply CL5.kdisj_intro; [ev_start | ev_len | ev_start | ev_len | lia].
    + unfold box in DJ; destruct DJ as (_ & DJ2 & _). e_disj.
    + unfold box in DJ; destruct DJ as (DJ1 & _ & _). e_disj.
    + unfold box in DJW. eapply CL5.kdisj_intro; [ev_start | ev_len | ev_start | ev_len | lia].
    + unfold box in DJ; destruct DJ as (_ & _ & DJ3). e_disj.
    + unfold box in DJW. eapply CL5.kdisj_intro; [ev_start | ev_len | ev_start | ev_len | lia].
    + unfold box in DJW. eapply CL5.kdisj_intro; [ev_start | ev_len | ev_start | ev_len | lia].
    + unfold box in DJW. eapply CL5.kdisj_intro; [ev_start | ev_len | unfold estart; cbn [a_base a_off edenot]; rewrite (u64_of_Z 0) by lia; reflexivity | unfold elenZ; cbn [edenot]; apply u64_of_Z; lia | lia].
  -
    assert (F4R : 0 <= 4 * seg - wlen <= 1125899906842624).
    { destruct W4 as [[W4 W5]|(ch & Hch & Hc1 & Hc2 & (B0 & _))]; unfold wlen in *; lia. }
    apply Forall_cons; [|apply Forall_nil]. apply PSA.krange_uv.
    rewrite PB.uv_esub, PB.uv_escale. unfold PB.uv. cbn [edenot]. rewrite U32, U33.
    rewrite (Z.mod_small (4 * seg)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Definition W : list L5.range := PMS.W_parc P V E.
Lemma SCRV : CH.hd_scr G.HDECL = 10096.
Proof. reflexivity. Qed.
Lemma STKF : sp mod 16 = 0 /\ hl_ceil L + CH.hd_scr G.HDECL <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47.
Proof. pose proof SPF as (S1 & S2 & S3 & S4 & S5 & S6). rewrite SCRV. unfold hl_ceil. repeat split; lia. Qed.
Lemma SCRP : 0 <= CH.hd_scr G.HDECL.
Proof. rewrite SCRV. lia. Qed.
Lemma NF32 : (32 <= GT.NF)%nat.
Proof. unfold GT.NF. lia. Qed.
Lemma U2 : bv_unsigned (ev E0 2) = sp.
Proof. exact (proj1 UU). Qed.
Lemma TP0 : ev E0 4 = Z_to_bv 64 (hl_tp L).
Proof. pose proof VV as (_ & V4 & _). rewrite V4, (PmLayout.ly_tp L LAY). reflexivity. Qed.
Definition statw (a : Z) : Prop := 0xd4df8 <= a < 0xd4dfa \/ 0xf6848 <= a < 0xf6848 + 544.
Lemma STATW : forall a, statw a -> CH2.wclient L sp a.
Proof.
  intros a Ha. unfold statw in Ha. split; [lia|]. right. rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY). split; [lia|].
  split; [intros X; pose proof (PmLayout.ly_static L LAY a X); lia|].
  split; [intros X; destruct (PmLayout.ly_ro_img L LAY a X ltac:(rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY); lia)) as [Q|[Q|Q]]; lia|].
  unfold in_errno. rewrite (PmLayout.ly_errno L LAY). lia.
Qed.
Lemma W_OK : forall (w : L5.range) (a : Z), In w W -> L5.in_rng w a -> CH2.wclient L sp a.
Proof.
  pose proof OBJR as (O1 & O2 & O3 & O4 & O5 & O6 & O7). pose proof SPF as (_ & _ & S3 & S4 & _). pose proof (iOP I) as (_ & OP2 & _). pose proof (iOE I) as (_ & OE2 & _).
  pose proof (iOV I) as (_ & OV2 & _).
  intros w a Hw Hin. unfold W, PMS.W_parc, PML.W_par in Hw. cbn [app] in Hw. destruct Hw as [<-|[<-|[<-|[<-|[<-|[]]]]]]; unfold L5.in_rng in Hin; cbn [fst snd] in Hin.
  - split; [lia | left; lia].
  - split; [lia | left; lia].
  - apply STATW. unfold statw. lia.
  - apply STATW. unfold statw. lia.
  - split; [lia | left; lia].
Qed.
Lemma CRS_OK : forall rg : SGP.region, In rg (CH.hd_crs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> CH2.sclient L LBo sp a).
Proof.
  pose proof UU as (_ & _ & U11 & _ & U32 & U33 & _). pose proof WIN as (W0 & W1 & W2 & _ & W4).
  pose proof OBJR as (O1 & O2 & O3 & O4 & O5 & O6 & O7). pose proof SPF as (_ & _ & S3 & S4 & _). pose proof (iOV I) as (_ & OV2 & _).
  intros rg [<-|[<-|[]]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CH2.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha.
  - rewrite U32, U33 in Ha. destruct W4 as [[W4 W5]|(ch & Hch & Hc1 & Hc2 & (B0 & _))]; [unfold wlen in Ha; lia|]. split; [lia|]. right. right. exists (ch, 16384). split; [exact Hch | cbn [fst snd]; unfold wlen in Ha; lia].
  - rewrite U11 in Ha. rewrite u64_of_Z in Ha by lia. split; [lia | left; lia].
Qed.
Lemma WRS_OK : forall rg : SGP.region, In rg (CH.hd_wrs G.HDECL) -> SGP.region_vars_lt GT.NF rg = true /\ (forall a : Z, CH2.in_reg E0 rg a -> exists w : L5.range, In w W /\ L5.in_rng w a).
Proof.
  pose proof UU as (_ & U10 & _ & U12 & _).
  intros rg [<-|[<-|[]]]; (split; [vm_compute; reflexivity|]); intros a Ha; unfold CH2.in_reg, estart, elenZ in Ha; cbn [a_base a_off edenot] in Ha.
  - rewrite U10 in Ha. rewrite u64_of_Z in Ha by lia. exists (P, 272). split; [left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia].
  - rewrite U12 in Ha. rewrite u64_of_Z in Ha by lia. exists (E, 16). split; [right; left; reflexivity | unfold L5.in_rng; cbn [fst snd]; lia].
Qed.
Lemma IMG_OK : forall (rg : Z * Z) (a : Z), In rg (CH.hd_img G.HDECL) -> fst rg <= a < snd rg -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_alloc_static L a /\ ~ in_errno L a.
Proof.
  intros rg a [<-|[]] Ha. cbn [fst snd] in Ha. rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY). split; [lia|].
  split; [intros X; pose proof (PmLayout.ly_static L LAY a X); lia | unfold in_errno; rewrite (PmLayout.ly_errno L LAY); lia].
Qed.
Lemma DEF0 : L5.defined M (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL).
Proof. pose proof SPF as (S1 & S2 & S3 & S4 & S5 & S6). rewrite SCRV. exact S5. Qed.

Definition KXf (tlb : list (Z * Z)) : Z := PPS.stk_kx L (snd (hd (0, 0) tlb)) + kx.
Definition BXf (tlb : list (Z * Z)) : Z := PPS.stk_bx L (snd (hd (0, 0) tlb)) + bx.
Definition Cred (i : nat) (E1 : env) (cr1 : credit) : Prop := PPS.bufcred L cr1 (PB.cap_of G.BLS i E1) (KXf (PB.tl_of G.BLS i E1)) (BXf (PB.tl_of G.BLS i E1)).
Lemma CRED_EQ : forall i E1 cr1, Cred i E1 cr1 <-> PPS.bufcred L cr1 (PB.cap_of G.BLS i E1) (KXf (PB.tl_of G.BLS i E1)) (BXf (PB.tl_of G.BLS i E1)).
Proof. intros. reflexivity. Qed.
Lemma CRED_BLK : forall i j E1 E2 cr1, CH2.den E2 (nth j G.BLS []) = CH2.den E1 (nth i G.BLS []) -> Cred i E1 cr1 -> Cred j E2 cr1.
Proof. intros i j E1 E2 cr1 Hd H. unfold Cred, PB.cap_of, PB.tl_of in *. rewrite Hd. exact H. Qed.
Lemma KXBX : 0 <= kx /\ 0 <= bx.
Proof. destruct (iHPC I) as (K0 & B0 & _). split; assumption. Qed.
Lemma cred_of_blocks : forall i E1 cr1 ps1, CH2.den E1 (nth i G.BLS []) = PML.ps_blocks ps1 -> In (PML.ps_scap ps1) [66; 132; 264; 528; 1056] ->
  (Cred i E1 cr1 <-> PML.pcredit_x L cr1 ps1 kx bx).
Proof.
  intros i E1 cr1 ps1 Hd Hs. unfold Cred, PB.cap_of, PB.tl_of, KXf, BXf. rewrite Hd. cbn [PML.ps_blocks hd tl snd].
  destruct KXBX as (K0 & B0). symmetry. exact (PPS.pcredit_x_bufcred L cr1 ps1 kx bx (PmLayout.ly_kpm L LAY) (PmLayout.ly_bov L LAY) Hs K0 B0).
Qed.

Definition ps_of (pv : PB4.pvals2) (pe ce : expr) (E1 : env) (bm bd : bool) (stack buf : list Z) : PML.pstate :=
  PML.PS (uv E1 (PB4.pv_st pv)) (uv E1 (PB4.pv_sst pv)) (uv E1 (PB4.pv_nst pv)) bm bd (uv E1 (PB4.pv_level pv)) stack
         (uv E1 (PB4.pv_sb pv)) (uv E1 (PB4.pv_scend pv) - uv E1 (PB4.pv_sb pv)) (uv E1 ce) (uv E1 pe) buf
         (PB4.win_of (uv E1 (PB4.pv_wptr pv)) (uv E1 (PB4.pv_wend pv))).
Local Abbreviation cutn := PSM2.cutn.
Local Abbreviation vw := PSM2.vw.
Local Abbreviation in_loop := PSM2.in_loop.  Local Abbreviation under0 := PSM2.under0.  Local Abbreviation reent_pc := PSM2.reent_pc.  Local Abbreviation pushed_of := PSM2.pushed_of.

Definition contents (pv : PB4.pvals2) (pe ce : expr) (E1 : env) (M1 : mem) (bm bd : bool) (stack buf : list Z) : Prop :=
  L5.bytes_at RSEGS M1 (uv E1 (PB4.pv_sb pv)) stack /\ uv E1 (PB4.pv_send pv) = uv E1 (PB4.pv_sb pv) + Z.of_nat (length stack) /\
  Z.of_nat (length stack) <= uv E1 (PB4.pv_scend pv) - uv E1 (PB4.pv_sb pv) /\ uv E1 (PB4.pv_wend pv) = wend /\ seg <= uv E1 (PB4.pv_wptr pv) <= wend /\
  Z.of_nat (length buf) = uv E1 (PB4.pv_size pv) /\ Z.of_nat (length buf) < uv E1 ce /\ (uv E1 (PB4.pv_st pv) = PML.ST_NUMBER -> L5.bytes_at RSEGS M1 (uv E1 pe) buf) /\
  uv E1 (PB4.pv_more pv) = PML.b2z bm /\ uv E1 (PB4.pv_done pv) = PML.b2z bd.

Definition STOPOK (ps1 : PML.pstate) (M1 : mem) : Prop := PML.ps_more ps1 = false ->
  (PML.ws_ok ps1 /\ PML.ps_done ps1 = true /\ PML.ps_st ps1 = PML.ST_DONE) \/
  (PMCUR.wf_c (PMCUR.ps_set_more ps1 true) /\ PMCUR.evp RSEGS M1 V level (PML.ps_win ps) ps1).

Definition CL (ps1 : PML.pstate) : Prop := PMCUR.lvl_ok ps1 /\ (PML.ps_more ps1 = true -> PML.ps_level ps1 = level).

Definition CX (ps1 : PML.pstate) (M1 : mem) : Prop := CL ps1 /\ STOPOK ps1 M1.

Definition skip_cut (i : nat) : bool := match ret_src i with Some (_, _, pc) => Z.eqb pc PML.PC_SKIP_SPACE | None => false end.

Definition pt_post (i : nat) (E1 : env) (M1 : mem) : Prop :=
  let nxg := (CC.cp_nx (cutn i) - APC.NCS - 5)%nat in let a0v := (CC.cp_nx (cutn i) - APC.NCS + 4)%nat in
  let jv := bv_unsigned (ev E1 49) in let rkv := bv_unsigned (ev E1 50) in
  exists (ps2 : PML.pstate) (code : Z) (g' : PML.ls_state) (cw : option (Z * Z)),
    PML.parser_at M1 P (PML.ps_set_win ps2 cw) /\ PML.wf_ps ps2 /\ PML.win_ok M1 LBo ps2 /\ PML.buf_bound ps2 B /\ PML.ec_at M1 E code /\ (code <> 0 -> PML.ps_more ps2 = false) /\
    PML.ls_ok g' M1 /\ (g' = g \/ (g' = PML.regJ g /\ code <> 0)) /\ bv_unsigned (ev E1 nxg) = code /\
    CH2.den E1 (nth i G.BLS []) = PML.ps_blocks ps2 /\ (skip_cut i = true -> code = 0) /\

    (if PSM2.cur_cut i then exists p e, cw = Some (p, e) /\ PML.ps_win ps2 = Some (bv_unsigned (ev E1 a0v), e) /\ p <= bv_unsigned (ev E1 a0v) <= e else cw = PML.ps_win ps2) /\
    (code = 0 ->
       CX ps2 M1 /\ snd (PSA.wincells (PML.ps_win ps2)) = wend /\ seg <= fst (PSA.wincells (PML.ps_win ps2)) <= wend /\
       (under0 i = true -> In (PML.ps_st ps2) [PML.ST_ACCEPT; PML.ST_EXPECT_COMMA_OR_END]) /\
       (in_loop i = true ->
          if Z.eqb (reent_pc i) L2PC then PML.winlen ps2 = jv
          else PML.winlen ps2 + 1 <= jv \/ (PML.winlen ps2 = jv /\ RANK ps2 + 1 <= rkv))).

Definition eofc (ps1 : PML.pstate) : Prop := wlen = 0 -> PML.ps_more ps1 = true -> In st0 [PML.ST_NUMBER; PML.ST_CR] /\ ~ In (PML.ps_st ps1) [PML.ST_NUMBER; PML.ST_CR].

Definition XI (i : nat) (E1 : env) (M1 : mem) : Prop :=

  L5.defined M1 (sp - CH.hd_scr G.HDECL) (CH.hd_scr G.HDECL) /\

  (i <> 0%nat -> st0 <> PML.ST_ACCEPT) /\ (in_loop i = true -> 1 <= wlen) /\
  match kind_of i with
  | KPt => pt_post i E1 M1
  | k =>
      match vw i with
      | Some (pv, pe, ce) =>
          exists (bm bd : bool) (stack buf : list Z),
            contents pv pe ce E1 M1 bm bd stack buf /\
            match k with
            | KInv =>
                let ps1 := ps_of pv pe ce E1 bm bd stack buf in
                PML.ls_ok g M1 /\
                PML.wf_ps ps1 /\ PML.buf_bound ps1 B /\ CX ps1 M1 /\ ((i = I_HLO \/ i = I_HHI \/ i = I_HN \/ i = I_L) -> RANK ps1 <= bv_unsigned (ev E1 50)) /\ (i = I_L0 -> eofc ps1)
            | KParent =>
                let ps1 := ps_of pv pe ce E1 bm bd stack buf in
                PML.ls_ok g M1 /\ PML.wf_ps ps1 /\ PML.buf_bound ps1 B
            | KVec =>
                PML.ls_ok g M1 /\
                match CAX.cell_at (CC.cp_know (cutn i)) (EVar 2) (-120) 1 with
                | Some (ELit x) => exists old, stack = old ++ [x] /\ let ps1 := ps_of pv pe ce E1 bm bd old buf in PML.wf_ps ps1 /\ PML.buf_bound ps1 B /\ CL ps1
                | _ => False
                end
            | KPop =>
                PML.ls_ok g M1 /\
                exists x, bv_unsigned (ev E1 (CC.cp_nx (cutn i) - APC.NCS - 1)) = x /\
                  let ps1 := ps_of pv pe ce E1 bm bd (stack ++ [x]) buf in PML.wf_ps ps1 /\ PML.buf_bound ps1 B /\ CL ps1 /\ (in_loop i = true -> RANK ps1 <= bv_unsigned (ev E1 50))
            | KPushB =>
                PML.ls_ok g M1 /\
                buf = [uv E1 (pushed_of i)] /\ L5.bytes_at RSEGS M1 (uv E1 pe) buf /\
                  let ps1 := ps_of pv pe ce E1 bm bd stack [] in PML.wf_ps ps1 /\ PML.buf_bound ps1 B /\ CL ps1
            | KSetEc | KErr =>
                let ps1 := ps_of pv pe ce E1 false bd stack buf in
                PML.ls_ok (PML.regJ g) M1 /\ PML.wf_ps ps1 /\ Z.of_nat (length buf) + PML.winlen ps1 <= B /\ B < 2 ^ 26 /\ (exists code, PML.ec_at M1 E code /\ 1 <= code <= 31) /\ (k = KErr -> bm = false)
            | KVis =>
                let ps1 := ps_of pv pe ce E1 bm bd stack buf in
                PML.ls_ok g M1 /\ PML.wf_ps ps1 /\ PML.buf_bound ps1 B /\ CL ps1 /\ bm = true /\ 18 <= PML.ps_st ps1 <= 27 /\
                (exists e, PMCUR.ev_at RSEGS M1 V e /\ PMCUR.scalar_ev e)
            | KPt => False
            end
      | None => False
      end
  end.

Lemma vw_total : forallb (fun i => match kind_of i with KPt => true | _ => match vw i with Some _ => true | None => false end end) (seq 0 (length G.CPS)) = true.
Proof. vmc_refl. Qed.
End A.
End PSI.
