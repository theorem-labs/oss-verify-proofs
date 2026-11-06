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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm9CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA PmLibStaticsA PmCurDefs.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import PmLibSpecsBLocal.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation RSEGS := Pm9PlanKit.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation IC := PMLA.C_cboth.

Module PSOC.

Definition NDECL : nat := 39.
Definition I_entryS : nat := 0.
Definition I_entryN : nat := 1.
Definition I_H : nat := 2.
Definition I_HQ : nat := 3.
Definition I_L : nat := 4.
Definition I_LQ : nat := 5.
Definition I_LZ : nat := 6.
Definition I_L2 : nat := 7.
Definition I_L3 : nat := 8.
Definition I_RETX : nat := 9.
Definition I_SE : nat := 10.
Definition CSL_LO : nat := 11.  Definition CSL_HI : nat := 38.
Definition PC : Z := 751580.
Definition RET : Z := 774768.
Definition RETIRE : Z := 774652.
Definition RETXPC : Z := 774660.
Definition SETECJ : Z := 774644.
Definition HEAD : Z := 753436.
Definition LATCH : Z := 758568.
Definition CONSUME : Z := 758516.
Definition CONSUME2 : Z := 758556.
Definition DEAD : Z := 774864.
Definition SM4 : Z := 414896.
Definition SETSH : Z := 536236.
Definition SETEC : Z := 749196.
Definition ERRH : Z := 824952.
Definition PUSHB : Z := 990424.
Definition VPUSH : Z := 807908.
Definition POPST : Z := 780820.
Definition PARENT : Z := 801208.
Definition SKIPSP : Z := 781716.
Definition BOBJ : Z := 782464.
Definition BARR : Z := 783312.
Definition PSTRING : Z := 784204.
Definition PNUMBER : Z := 790556.
Definition PNULL : Z := 794316.
Definition PTRUE : Z := 795580.
Definition PFALSE : Z := 796780.
Definition EOBJ : Z := 798060.
Definition EARR : Z := 799336.
Definition BMEMBER : Z := 800616.
Definition ENDINT : Z := 779000.
Definition ENDFRAC : Z := 779184.
Definition SBz : Z := 2147450880.
Definition GD : Z := 6882184.
Definition AXT : Z := 7020000.
Definition ERRNO : Z := 6888684.
Definition FS_LO : Z := 7028736.
Definition VT_VISITOR : Z := 1370856.
Definition VT_FUNC : Z := 1370488.
Definition VT_PARSER : Z := 1369536.
Definition SCR : Z := 10496.

Definition WLENV : nat := 32.
Definition BXV : nat := 33.
Definition CHV : nat := 34.
Definition CHGV : nat := 35.
Definition WP0V : nat := 36.
Definition JV : nat := 46.
Definition ECV : nat := 47.
Definition STV : nat := 48.
Definition SSTV : nat := 49.
Definition NSTV : nat := 50.
Definition MOREV : nat := 51.
Definition DONEV : nat := 52.
Definition LEVELV : nat := 53.
Definition KKV : nat := 54.
Definition SIZEV : nat := 55.
Definition PPV : nat := 56.
Definition SBV : nat := 57.
Definition SLENV : nat := 58.
Definition SCAPV : nat := 59.
Definition FLV : nat := 60.
Definition FEV : nat := 65.
Definition IDXV : nat := 70.
Definition NXL : nat := 81.
Definition QSTATES : list Z := [1; 2; 5; 7; 9; 10; 11; 12; 13].

Definition VNULL : Z := 0xcb418.
Definition VBOOL : Z := 0xcb4c0.
Definition TP : Z := 6888848.
Definition IMGHI : Z := 7028736.

Definition ISLOTS : list Z := [VT_FUNC + 48; VT_VISITOR + 56; VT_VISITOR + 104; VT_VISITOR + 112].

Definition PE := EVar 10. Definition VE := EVar 11. Definition EE := EVar 12.
Definition WLEN := EVar WLENV. Definition BX := EVar BXV. Definition CH := EVar CHV. Definition CHG := EVar CHGV. Definition WP0 := EVar WP0V.
Definition WE : expr := EAlu Instr.ALU_ADD WP0 WLEN.
Definition FLE := EVar FLV. Definition FE := EVar FEV.
End PSOC.
Import PSOC.

Module PSOI.

Definition wlo (w : option (Z * Z)) : Z := match w with Some (p, _) => p | None => 0 end.
Definition whi (w : option (Z * Z)) : Z := match w with Some (_, e) => e | None => 0 end.
Definition wchg (w : option (Z * Z)) : Z := match w with Some _ => 2048 | None => 0 end.

Record inst {SCFG_P : ScfgP} : Type := Inst {
  iL : asan_layout; iar : asan_run; iC : asan_statics_cells; iHI : asan_iface; iIL : icpt_layout;
  iHIok : PmHeapIfaceA.asan_iface_ok iL iar iC SCFG iHI;
  iLAY : L5A.as0_layout iL iC;
  iISH : rt_img_shadow iL iIL iHI;
  iPOI : Forall (fun r : Z * Z => Forall (fun a => a + 8 <= fst r \/ snd r <= a) ISLOTS) (icl_poison iIL);
  iFOOTC : forall a, PMLA.in_foot IC a -> ~ hl_rt_static iL a;
  iSM4 : hl_stack_malloc iL 4 = SM4;
  iFPM : forall (fx fx' : FPState) R pc M R' pc' M',
      msteps (hl_segs iL) (@mkst fx R (Z_to_bv 64 pc) M (seg_rom (hl_segs iL))) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom (hl_segs iL))) -> PMSA.fp_ok fx -> PMSA.fp_ok fx';
  iTPV : hl_tp iL = TP;
  iERRNO : forall a, ERRNO <= a < ERRNO + 4 -> ~ hl_rt_static iL a;
  iSETSH : aset_shadow_spec iL iar SCFG iHI SETSH 245 256;

  iERRH : PMSA.errh_specA iL iar iHI ERRH;
  iSETEC : PMSA.set_ec_specA iL iar iHI IC SETEC;
  iPUSHB : PMSA.str_push_back_specA iL iar iHI PUSHB;
  iVPUSH : PMSA.vec_push_specA iL iar iHI VPUSH;
  iPOPST : PMSB.pop_state_specA iL iar iHI POPST;
  iPARENT : PMSA.parent_specA iL iar iHI PARENT;
  iSKIPSP : PMSA.skip_space_specA iL iar iHI IC SKIPSP;
  iBOBJ : PMSA.begin_object_specA iL iar iHI IC BOBJ;
  iBARR : PMSA.begin_array_specA iL iar iHI IC BARR;
  iEOBJ : PMSA.end_object_specA iL iar iHI IC EOBJ;
  iEARR : PMSA.end_array_specA iL iar iHI IC EARR;
  iBMEMBER : PMSA.begin_member_specA iL iar iHI IC BMEMBER;
  iPTRUE : PMSA.parse_true_specA iL iar iHI IC PTRUE;
  iPFALSE : PMSA.parse_false_specA iL iar iHI IC PFALSE;
  iPNULL : PMSA.parse_null_specA iL iar iHI IC PNULL;
  iPSTRING : PMSA.parse_string_specA iL iar iHI IC PSTRING;
  iPNUMBER : PMSA.parse_number_specA iL iar iHI IC PNUMBER;
  iENDINT : PMSA.end_integer_value_specA iL iar iHI IC ENDINT;
  iENDFRAC : PMSA.end_fraction_value_specA iL iar iHI IC ENDFRAC;
  iVNULL : PMSA.visit_null_specA iL iar iHI IC VNULL;
  iVBOOL : PMSA.visit_bool_specA iL iar iHI IC VBOOL;

  iLBo : list (Z * Z); iFF : list fframe; iLK : list fframe; icr : credit; iA : list (Z * Z);
  isp : Z; ir : Z; iP : Z; iV : Z; iE : Z; iB : Z; ikx : Z; ibx : Z; ig : PML.ls_state; ips : PML.pstate;
  ifx : FPState; iR : bvmap 5 word; iM : mem; imodel : Model; iK : TSet;

  iHH : ri_inv iHI (PML.ps_blocks ips ++ iLBo) iFF iLK icr iA iM (vml_of imodel);
  iHmo : CHA.amodel_ok iA imodel;
  iHKnil : iK [];
  iHfp : PMSA.fp_ok ifx;
  iHra : getr iR 1%bv = Z_to_bv 64 ir;
  iHraok : L5.ra_ok ir;
  iHsp : getr iR 2%bv = Z_to_bv 64 isp;
  iHtp : getr iR 4%bv = Z_to_bv 64 (hl_tp iL);
  iHstk : CHA.astk iar iM isp SCR;
  iHroom : CHA.ffroom iFF iLK 6;
  iHffrs : CHA.ffrs iFF isp;

  iHa0 : getr iR 10%bv = Z_to_bv 64 iP;
  iHa1 : getr iR 11%bv = Z_to_bv 64 iV;
  iHa2 : getr iR 12%bv = Z_to_bv 64 iE;
  iHMORE : PML.ps_more ips = true;
  iHsp32 : isp mod 32 = 0;
  iHstksh : PMLA.stksh iar iM isp SCR;
  iHPA : PMLA.parser_at (hl_segs iL) IC iM iP ips;
  iHPSH : PMLA.parser_sh iM ips;
  iHWF : PMCUR.wf_c ips;
  iHWIN : PMLA.win_okA iM iLBo ips;
  iHBB : PML.buf_bound ips iB;
  iHVIS : PMLA.vis_at (hl_segs iL) IC iM iV;
  iHEC : PMLA.ec_at (hl_segs iL) IC iM iE 0;
  iHLS : PMLA.ls_ok (hl_segs iL) IC ig iM;
  iHG : ig <> PML.LS0;
  iHPC : PMLA.pcredit_xA iL icr ips ikx ibx;
  iOP : PMLA.fobj iM iFF iP 272;
  iOV : PMLA.fobj iM iFF iV 48;
  iOE : PMLA.fobj iM iFF iE 16;
  iAP1 : PMLA.apart iP 272 iV 48;
  iAP2 : PMLA.apart iP 272 iE 16;
  iAP3 : PMLA.apart iV 48 iE 16;

  ich : Z; iwinb : list Z;
  iHCH : match PML.ps_win ips with
         | Some (p, e) => In (ich, 16384) iLBo /\ ich <= p /\ e <= ich + 16384 /\ L5.defined iM p (e - p) /\ shadow_blk iM ich 16384
         | None => ich = 0 end;
  iHwinb : L5.bytes_at (hl_segs iL) iM (wlo (PML.ps_win ips)) iwinb /\ Z.of_nat (length iwinb) = whi (PML.ps_win ips) - wlo (PML.ps_win ips);

  iHcont : forall (fx' : FPState) (R' : bvmap 5 word) (M' : mem) (model' : Model) (LB' : list (Z * Z)) (cr' : credit) (LBk : list (Z * Z)) (W : list L5.range)
      (LK' : list fframe) (A' : list (Z * Z)),
      PMSA.fp_ok fx' ->
      (exists (ps' : PML.pstate) (code : Z) (g' : PML.ls_state),
         PMLA.parser_at (hl_segs iL) IC M' iP ps' /\ PMLA.parser_sh M' ps' /\ PMCUR.wf_c ps' /\ PMLA.win_okA M' iLBo ps' /\ PML.buf_bound ps' iB /\
         PMLA.ec_at (hl_segs iL) IC M' iE code /\ (code <> 0 -> PML.ps_more ps' = false) /\
         PMLA.ls_ok (hl_segs iL) IC g' M' /\ (g' = ig \/ (g' = PML.regJ ig /\ code <> 0)) /\
         LB' = PML.ps_blocks ps' ++ iLBo /\ LBk = iLBo /\ W = PMSA.W_parEc iL IC iP iV iE /\ PMLA.pcredit_xA iL cr' ps' ikx ibx /\
         ((code <> 0 \/ PML.ps_more ps' = false \/ PMSA.win_exhausted ps') /\
          (PML.ps_st ips = PML.ST_ACCEPT -> code = 0 /\ PML.ps_more ps' = false /\ PML.ps_done ps' = true) /\
          (PMSA.win_exhausted ips -> code = 0 -> PML.ps_more ps' = true -> In (PML.ps_st ips) [PML.ST_NUMBER; PML.ST_CR] /\ ~ In (PML.ps_st ps') [PML.ST_NUMBER; PML.ST_CR])) /\
         PMCUR.cur_post (hl_segs iL) ips ps' code M' iV) ->
      regs_preserved iR R' -> CHA.ahpres iL iar LBk iFF isp SCR W iM M' -> model_rt imodel model' -> incl iA A' -> CHA.amodel_ok A' model' -> incl LK' iLK ->
      ri_inv iHI LB' iFF LK' cr' A' M' (vml_of model') ->
      srealizes (hl_segs iL) SCFG (@PMSA.cfg iL fx' R' ir M' model') iK
}.

Section A.
Context {SCFG_P : ScfgP}.
Variable I : inst.
Local Abbreviation L := (iL I).     Local Abbreviation ar := (iar I).    Local Abbreviation C := (iC I).     Local Abbreviation HI := (iHI I).
Local Abbreviation LBo := (iLBo I). Local Abbreviation FF := (iFF I).    Local Abbreviation LK := (iLK I).   Local Abbreviation cr := (icr I).   Local Abbreviation A := (iA I).
Local Abbreviation sp := (isp I).   Local Abbreviation P := (iP I).      Local Abbreviation V := (iV I).     Local Abbreviation E := (iE I).     Local Abbreviation B := (iB I).
Local Abbreviation kx := (ikx I).   Local Abbreviation bx := (ibx I).    Local Abbreviation g := (ig I).     Local Abbreviation ps := (ips I).
Local Abbreviation R := (iR I).     Local Abbreviation M := (iM I).      Local Abbreviation ch := (ich I).   Local Abbreviation winb := (iwinb I).
Definition LB : list (Z * Z) := PML.ps_blocks ps ++ LBo.

Definition win : option (Z * Z) := PML.ps_win ps.
Definition wp0 : Z := wlo win.
Definition we0 : Z := whi win.
Definition wlen : Z := we0 - wp0.
Definition chg : Z := wchg win.
Definition bcap : Z := PML.ps_bcap ps.
Definition k0 : Z := bcap / 2.
Definition bptr : Z := PML.ps_bptr ps.
Definition buf : list Z := PML.ps_buf ps.
Definition size0 : Z := Z.of_nat (length buf).
Definition sb : Z := PML.ps_sb ps.
Definition scap : Z := PML.ps_scap ps.
Definition stack : list Z := PML.ps_stack ps.
Definition slen : Z := Z.of_nat (length stack).
Definition level : Z := PML.ps_level ps.
Definition st0 : Z := PML.ps_st ps.
Definition sst0 : Z := PML.ps_sst ps.
Definition nst0 : Z := PML.ps_nst ps.
Definition done0 : Z := PML.b2z (PML.ps_done ps).

Definition gvals : list Z := [wlen; B; ch; chg; wp0; 0; 0; 0; 0; 0; 0; 0; 0; 0; wlen; 0; st0; sst0; nst0; 1; done0; level; k0; size0; bptr; sb; slen; scap].
Definition E0 : env :=
  Env (reg_ev R (fun v => Z_to_bv 64 (nth (v - 32) gvals 0)))
      (fun id => match id with 1%nat => map (Z_to_bv 8) winb | _ => [] end).

Lemma PAR : L5.u64_at (hl_segs L) M P (PMLA.VT_PARSER IC) /\ L5.u32_at (hl_segs L) M (P + 8) 1024 /\
  L5.u8_at (hl_segs L) M (P + 12) 0 /\ L5.u8_at (hl_segs L) M (P + 13) 1 /\ L5.u8_at (hl_segs L) M (P + 14) 0 /\ L5.u8_at (hl_segs L) M (P + 15) 1 /\
  L5.u8_at (hl_segs L) M (P + 16) 0 /\ L5.u8_at (hl_segs L) M (P + 17) 0 /\ L5.u8_at (hl_segs L) M (P + 18) 0 /\
  L5.lstr_short (hl_segs L) M (P + 24) [] /\ L5.lstr_short (hl_segs L) M (P + 48) [] /\ L5.lstr_short (hl_segs L) M (P + 72) [] /\
  L5.u64_at (hl_segs L) M (P + 96) (PMLA.VT_FUNC IC) /\ L5.u64_at (hl_segs L) M (P + 128) (P + 96) /\ L5.u32_at (hl_segs L) M (P + 144) level /\
  match win with None => L5.u64_at (hl_segs L) M (P + 192) 0 /\ L5.u64_at (hl_segs L) M (P + 200) 0 | Some (p, e) => L5.u64_at (hl_segs L) M (P + 200) p /\ L5.u64_at (hl_segs L) M (P + 192) e /\ p <= e end /\
  L5.u8_at (hl_segs L) M (P + 208) st0 /\ L5.u8_at (hl_segs L) M (P + 209) sst0 /\ L5.u8_at (hl_segs L) M (P + 210) nst0 /\ L5.u8_at (hl_segs L) M (P + 211) 1 /\
  L5.u8_at (hl_segs L) M (P + 212) done0 /\ L5.u8_at (hl_segs L) M (P + 213) 1 /\ L5.u32_at (hl_segs L) M (P + 216) 0 /\
  PMLA.str_at (hl_segs L) M (P + 224) (PML.SLong bcap bptr buf) /\ 264 <= bcap /\
  L5.u64_at (hl_segs L) M (P + 248) sb /\ L5.u64_at (hl_segs L) M (P + 256) (sb + slen) /\ L5.u64_at (hl_segs L) M (P + 264) (sb + scap) /\
  L5.bytes_at (hl_segs L) M sb stack /\ slen <= scap /\ L5.defined M P 272.
Proof. pose proof (iHPA I) as H. unfold PMLA.parser_at, PMLA.u64, PMLA.u32, PMLA.u8 in H. rewrite (iHMORE I) in H. exact H. Qed.
Lemma PDEFM : L5.defined M P 272.
Proof. pose proof PAR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PDEF). exact PDEF. Qed.
Lemma WINR : wp0 <= we0 /\ 0 <= wlen.
Proof.
  pose proof PAR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hw & _). unfold wlen, wp0, we0, win in *.
  destruct (PML.ps_win ps) as [[p e]|]; cbn [wlo whi]; [destruct Hw as (_ & _ & PE'); clear - PE'; lia | clear; lia].
Qed.

Lemma WFX : 0 <= sst0 <= 11 /\ 0 <= nst0 <= 7 /\ 1 <= slen <= 1027 /\ In scap [66; 132; 264; 528; 1056] /\ 66 <= scap <= 1056 /\ slen <= scap /\ 0 <= level <= 1024 /\ 0 <= done0 <= 1
  /\ 0 <= st0 <= 28.
Proof.
  pose proof (proj1 (iHWF I)) as (W1 & W2 & W3 & W4 & (Cc & T & W5 & _ & W7)). specialize (W7 (iHMORE I)). destruct W7 as (_ & W8 & W9 & _).
  pose proof PAR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SL & _).
  assert (SL1 : 1 <= slen) by (unfold slen, stack; rewrite W5; cbn [length]; clear; lia).
  unfold sst0, nst0, slen, stack, scap, level, done0, st0 in *. cbn [In] in W4. unfold PML.handled in W9.
  repeat split; try (clear - W1; lia); try (clear - W2; lia); try (clear - W3 SL1; lia); try (clear - W4; lia); try (clear - SL; lia); try (clear - W8; lia); try (clear - W9; lia).
  - cbn [In]. exact W4.
  - destruct (PML.ps_done ps); cbn; clear; lia.
  - destruct (PML.ps_done ps); cbn; clear; lia.
Qed.
Lemma buf_need_nonneg : forall psx, 0 <= PML.buf_need psx.
Proof.
  intros psx. unfold PML.buf_need, PML.esc_need. destruct (_ && _)%bool; [|lia]. generalize (Z.to_nat (PML.ps_sst psx)) as n. intros n.
  do 12 (destruct n as [|n]; [cbn; lia|]). destruct n; cbn; lia.
Qed.
Lemma BBX : size0 + wlen <= B /\ B < 2 ^ 26 /\ 0 <= wlen.
Proof.
  pose proof (iHBB I) as (H1 & H2). unfold PML.winlen in H1. pose proof WINR as [_ W0]. pose proof (buf_need_nonneg ps) as NN.
  unfold size0, buf, wlen, we0, wp0, win in *. destruct (PML.ps_win ps) as [[p e]|]; cbn [wlo whi] in *; clear - H1 H2 W0 NN; lia.
Qed.
Lemma BCX : bcap mod 8 = 0 /\ 264 <= bcap <= 2 ^ 27 /\ size0 < bcap /\ bcap = 2 * k0 /\ 132 <= k0 <= 2 ^ 26.
Proof.
  pose proof PAR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ((_ & BC8 & BLT) & A24 & _)).
  pose proof (iHPC I) as (_ & _ & (PC1 & _)). cbn [PML.ps_bcap fst] in PC1. fold bcap in PC1.
  assert (D : bcap = 2 * k0) by (unfold k0; pose proof (Z_div_mod_eq_full bcap 8) as D8; rewrite BC8 in D8; pose proof (Z_div_mod_eq_full bcap 2) as D2;
    assert (M2 : bcap mod 2 = 0) by (rewrite D8; replace (8 * (bcap / 8) + 0) with ((4 * (bcap / 8)) * 2) by lia; apply Z_mod_mult); clear - D2 M2; lia).
  unfold size0, buf in *. clear - BC8 BLT A24 PC1 D. lia.
Qed.

Lemma WSOME : forall p e, win = Some (p, e) ->
  wp0 = p /\ we0 = e /\ chg = 2048 /\ In (ch, 16384) LBo /\ ch <= p /\ e <= ch + 16384 /\ L5.defined M p (e - p) /\ shadow_blk M ch 16384 /\ p <= e.
Proof.
  intros p e Hw. pose proof (iHCH I) as HC. pose proof WINR as [PE' _]. unfold wp0, we0, chg, win in *. rewrite Hw in HC, PE' |- *. cbn [wlo whi wchg] in *.
  destruct HC as (C1 & C2 & C3 & C4 & C5). exact (conj eq_refl (conj eq_refl (conj eq_refl (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 PE')))))))).
Qed.
Lemma WNONE : win = None -> wp0 = 0 /\ we0 = 0 /\ wlen = 0 /\ chg = 0 /\ ch = 0.
Proof. intros Hw. pose proof (iHCH I) as HC. unfold wlen, wp0, we0, chg, win in *. rewrite Hw in HC |- *. cbn [wlo whi wchg]. exact (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl HC)))). Qed.

Lemma EV0 : forall y : reg, ev E0 (ridx y) = getr R y.
Proof. intros y; apply CL5.ev_reg. Qed.
Lemma VV : ev E0 2 = Z_to_bv 64 sp /\ ev E0 4 = Z_to_bv 64 (hl_tp L) /\ ev E0 10 = Z_to_bv 64 P /\ ev E0 11 = Z_to_bv 64 V /\ ev E0 12 = Z_to_bv 64 E
  /\ ev E0 32 = Z_to_bv 64 wlen /\ ev E0 33 = Z_to_bv 64 B /\ ev E0 34 = Z_to_bv 64 ch /\ ev E0 35 = Z_to_bv 64 chg /\ ev E0 36 = Z_to_bv 64 wp0
  /\ ev E0 46 = Z_to_bv 64 wlen /\ ev E0 47 = Z_to_bv 64 0 /\ ev E0 48 = Z_to_bv 64 st0 /\ ev E0 49 = Z_to_bv 64 sst0 /\ ev E0 50 = Z_to_bv 64 nst0 /\ ev E0 51 = Z_to_bv 64 1
  /\ ev E0 52 = Z_to_bv 64 done0 /\ ev E0 53 = Z_to_bv 64 level /\ ev E0 54 = Z_to_bv 64 k0 /\ ev E0 55 = Z_to_bv 64 size0 /\ ev E0 56 = Z_to_bv 64 bptr /\ ev E0 57 = Z_to_bv 64 sb
  /\ ev E0 58 = Z_to_bv 64 slen /\ ev E0 59 = Z_to_bv 64 scap.
Proof.
  rewrite <- (iHsp I), <- (iHtp I), <- (iHa0 I), <- (iHa1 I), <- (iHa2 I). repeat split; try reflexivity; try (exact (EV0 2%bv)); try (exact (EV0 4%bv)); try (exact (EV0 10%bv));
  try (exact (EV0 11%bv)); try (exact (EV0 12%bv)).
Qed.
End A.
End PSOI.
