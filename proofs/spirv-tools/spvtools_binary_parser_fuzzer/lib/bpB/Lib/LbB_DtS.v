(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BArr BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 BsWalk RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BakeStackRep FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_Own.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_DiagStmt LbB_DStat LbB_DRep LbB_DKit LbB_DKitN.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PcStmt LbB_PqK LbB_DtK LbB_DtR LbB_Dt.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_DCtorK LbB_DCtor LbB_DPdK LbB_PcOvf LbB_PcOvfS LbB_PcXsp LbB_PcLem LbB_Pq LbB_PqS LbB_HKit.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma dt_ret_ok : forall (Q : machine_state -> Prop) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
    x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (ret_pc x1) fc None m (seg_rom asegs)) ->
  evt asegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 ADT_RET) fc None m (seg_rom asegs)).
Proof.
  intros Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m HQ.
  unfold ADT_RET. step. apply evt_done. exact HQ.
Qed.

Section DTS.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
            (s : as_St H) (LB LBk : list block) (LF : list fframe) (CH : list (Z * Z)) (lo B shi : Z) (errv : word)
            (ds err len : Z) (DB : list block) (ms : sbuf) (pp hm fl fill : Z).
  Hypothesis PRE : ds_pre H LINV_P5 ADS_DTOR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                          F fc msF m mo s LB DB LF CH 0 lo B shi errv.
  Hypothesis PF : pf_ok (as_TR H) DS_DTOR_PF (bv_unsigned ra) CH.
  Hypothesis Ha0 : a0 = Z_to_bv 64 ds.
  Hypothesis REPW : ds_rep_w LB m ds err len DB ms pp hm fl fill.
  Hypothesis PERM : Permutation LB (DB ++ LBk).
  Hypothesis DSOB : ds_obj H LF m (bv_unsigned sp) ds DS_SIZE.
  Hypothesis DSIN : obj_inframe LF ds DS_SIZE.

  Notation spz := (bv_unsigned sp) (only parsing).
  Let HH : asan_rt_hyps H := rt_bp_base H HHbp.

  Lemma dt_ctx_ok : dt_ctx H sp tp a0 m ds len err lo LF LB DB ms pp hm fl fill s.
  Proof.
    destruct PRE as (VIS & FZ & RH & KR & OWN & LBS & LBC & LBL & RAUX & SPB & BB & SP16 & STK & CEIL & LO & ERRN & MI & TP & RA2 & LV
                     & AC & RFS & LFn & S0 & SPS & CHN & PF' & CHsp & TRok & COST).
    destruct DSOB as (DSA & DS8 & DSfs & DS0 & DS47 & DSsp & DSO).
    destruct (LbB_DCtor.inframe_facts H HH LF m ds DS_SIZE RFS DSIN ltac:(unfold DS_SIZE; clear; lia) (proj1 DSO)) as (DSH & DSV & _ & _).
    pose proof (stack0_bounds m lo shi S0) as SB.
    constructor; try assumption.
    - clear - SB SPS. lia.
    - clear - LFn. unfold DS_FRAMES in LFn. eapply Nat.le_trans; [| exact LFn]. apply (proj1 (Nat.add_le_mono_l _ _ _)). repeat constructor.
  Qed.

  Notation CTX := dt_ctx_ok (only parsing).
  Notation hw := (LbB_Dt.hw ms) (only parsing).
  Notation dptr := (LbB_Dt.dptr ms) (only parsing).
  Notation hsel := (LbB_Dt.hsel ms) (only parsing).
  Notation WW ff fp spa := (LbB_DtK.WD ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds err ff fp spa hw dptr) (only parsing).
  Notation DTARGS := (fun X => X H HHbp ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ds len err lo LF LB DB ms pp hm fl fill s CTX) (only parsing).

  Definition XSd (ff fp : Z) : list (Z * Z) :=
    [(as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + fsz 2); (sh ff, sh ff + fshn 2)].

  Lemma xsd_scratch : forall ff fp, fresh_frame H LF 2 ff fp -> Forall (fs_scratch H LF) (XSd ff fp).
  Proof. intros ff fp FR. exact (fs_scratch_of_fresh H LF 2 ff fp FR). Qed.

  Ltac evWW := cbn [edenot]; unfold wenv, HLib.Eseed, reg_ev, LbB_DtK.WD;
    lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op
          Init.Nat.add Nat.sub nth app length N.of_nat Pos.of_succ_nat Pos.succ N.add Pos.add].

  Ltac rgq HRT r e E := assert (E := rtbl_In _ _ _ r e HRT ltac:(apply LbB_DCtorK.inb_In'; vm_compute; reflexivity)); cbv beta in E; revert E; evWW; intros E.

  Lemma stk_pteq : forall mx mx' lo' hi', stk asegs mx lo' hi' ->
    (forall a, lo' <= a < hi' -> mx' (wa a) = mx (wa a) /\ (wview asegs mx (wa a) <> None -> wview asegs mx' (wa a) <> None)) ->
    stk asegs mx' lo' hi'.
  Proof.
    intros mx mx' lo' hi' (H0 & H1 & HW) HE. split; [exact H0|]. split; [exact H1|].
    intros i Hi. destruct (HE i Hi) as [E W]. destruct (HW i Hi) as [W0 [b Hb]].
    split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
  Qed.

  Record dz (ff fp spa : Z) (AT D0 D1 : list fent) (sx : as_St H) (LBc : list block) (mx : mem) : Prop := DZ {
    z_g : dg H sp ds err lo ff fp spa hw dptr;
    z_fr : fresh_frame H LF 2 ff fp;
    z_rh : as_RHEAP H sx LBc mx;
    z_sub : forall b, In b LBk -> In b LBc;
    z_raux : as_rauxv_ok H mx B;
    z_err : rw_cells asegs mx (errno_addr tp) [C4 errv];
    z_mi : mem_inv asegs mx;
    z_s0 : stack0 mx lo shi;
    z_al : as_AL H sx >= as_AL H s;
    z_rfs : as_RFS H ((2, ff, fp) :: LF) mx;
    z_q : df sp ds err lo ff fp hw dptr 0 mx;
    z_ts : ftbl (WW ff fp spa) spz mx TSD;
    z_ta : ftbl (WW ff fp spa) spa mx AT;
    z_td0 : ftbl (WW ff fp spa) ds mx D0;
    z_td1 : ftbl (WW ff fp spa) ds mx D1;
    z_tf : ftbl (WW ff fp spa) ff mx FTD2;
    z_th : ftbl (WW ff fp spa) (ff / 8) mx HTD2;
    z_xp : xpres H LBk spz ([(ds, ds + DS_SIZE)] ++ XSd ff fp) m mx;
    z_ch : as_chain H mx (bv_unsigned s0) CH
  }.

  Lemma chsp : forall fp' ra', In (fp', ra') CH -> spz + 16 <= fp'.
  Proof.
    destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CHsp & _).
    exact CHsp.
  Qed.

  Lemma dz_apres : forall ff fp spa AT D0 D1 sx sx' LBc LBc' mx mx' SP,
    dz ff fp spa AT D0 D1 sx LBc mx -> (forall b, In b LBk -> In b LBc') ->
    fin 0 16 (fkeys D0) = true -> fin 112 120 (fkeys D1) = true ->
    (SP <= spa - 48 /\ AT = ATD3 \/ SP <= spa /\ AT = [] \/ SP <= spa /\ AT = ATD2) -> apres H LBc' SP mx mx' ->
    as_RHEAP H sx' LBc' mx' -> as_rauxv_ok H mx' B -> rw_cells asegs mx' (errno_addr tp) [C4 errv] -> mem_inv asegs mx' ->
    ACONST mx' -> stk asegs mx' lo SP -> aceil <= SP -> lo <= SP -> as_AL H sx' >= as_AL H s ->
    dz ff fp spa AT D0 D1 sx' LBc' mx'.
  Proof.
    intros ff fp spa AT D0 D1 sx sx' LBc LBc' mx mx' SP Z SUB' FD0 FD1 HSP AP RH' RAUX' ERR' MI' AC' STK' CSP LSP AL'.
    destruct Z as [G FR RH PM RAUX ERR MI S0 AL RFS Q TS TA TD0 TD1 TF TH XP CHN].
    pose proof (LbB_DtK.d_nums H sp ds err lo ff fp spa hw dptr G) as NU. pose proof aceil_facts as ((A1 & A2) & _).
    assert (HSP' : SP <= spz) by (clear - HSP NU; lia).
    assert (XPa : xpres H LBk SP ([(ds, ds + DS_SIZE)] ++ XSd ff fp) mx mx').
    { eapply xpres_weaken; [exact (xpres_of_apres H _ _ _ _ _ AP) | apply Z.le_refl | exact SUB' | intros a Ha; exact Ha]. }

    assert (CF : forall A k, as_FSB H <= A -> A + k <= as_FSB H + AFS_SIZE -> aclient_range H LBc' SP A k).
    { intros A k H1 H2. do 4 right. left. split; [exact H1 | exact H2]. }
    assert (CS : forall A k, sh (as_FSB H) <= A -> A + k <= sh (as_FSB H + AFS_SIZE) -> aclient_range H LBc' SP A k).
    { intros A k H1 H2. do 5 right. left. split; [exact H1 | exact H2]. }
    assert (CU : forall A k, SP <= A -> aclient_range H LBc' SP A k) by (intros A k H1; left; exact H1).
    assert (EQU : forall a, SP <= a < spz -> mx' (wa a) = mx (wa a) /\ (wview asegs mx (wa a) <> None -> wview asegs mx' (wa a) <> None)).
    { intros a Ha. apply AP; [clear - Ha NU CSP A1; lia | left; clear - Ha; lia]. }
    assert (EQS : forall a, sh (as_FSB H) <= a < sh (as_FSB H + AFS_SIZE) -> mx' (wa a) = mx (wa a) /\ (wview asegs mx (wa a) <> None -> wview asegs mx' (wa a) <> None)).
    { intros a Ha. apply AP; [clear - Ha NU; unfold AFS_SIZE in *; lia | do 5 right; left; exact Ha]. }
    pose proof Q as [_ LV ST DSA DSW DSV DF _ FW HW LW].
    assert (RFS' : as_RFS H ((2, ff, fp) :: LF) mx') by (eapply (RFS_via_apres H HH); [exact RFS | exact AP]).
    destruct (LbB_DCtor.inframe_facts H HH _ mx' ds DS_SIZE RFS' (LbB_Dt.dsin2 H sp tp a0 m ds len err lo LF LB DB ms pp hm fl fill s CTX ff fp)
                ltac:(unfold DS_SIZE; clear; lia) ltac:(clear - NU; unfold AIMG_TOP; lia)) as (_ & DSV' & _ & _).
    unfold AFS_SIZE in *.
    constructor; try assumption.
    - eapply (stack0_xpres H); [exact (xpres_of_apres H _ _ [] _ _ AP) | exact S0 | apply Forall_nil].
    - constructor.
      + exact AC'.
      + eapply LINV_P5_cl; [exact LV|]. intros a Ha Hc. apply AP; [exact Ha | right; left; exact Hc].
      + apply (LbB_PqS.stk_join mx' lo SP spz STK'). apply (stk_pteq mx mx' SP spz); [| exact EQU].
        exact (proj2 (stk_split asegs mx lo SP spz ST ltac:(clear - LSP HSP'; lia))).
      + eapply addressable_pteq; [exact DSA|]. intros x Hx. apply EQS. change (nsh DS_SIZE) with 49 in Hx. clear - Hx NU. lia.
      + eapply (apres_wr_at H); [exact AP | exact DSW | apply CF; clear - NU; unfold DS_SIZE; lia].
      + exact DSV'.
      + destruct DF. constructor; (eapply (apres_rw_cells H); [exact AP | eassumption | apply CF; cbn; clear - NU; lia]).
      + exact I.
      + eapply (apres_wr_at H); [exact AP | exact FW | apply CF; clear - NU; lia].
      + eapply (apres_wr_at H); [exact AP | exact HW | apply CS; clear - NU; lia].
      + eapply (apres_wr_at H); [exact AP | exact LW | apply CF; clear - NU; lia].
    - eapply (ftbl_apres H LBc' SP _ spz mx mx' TSD (-104) 0); [exact TS | exact AP | vm_compute; reflexivity | apply CU; clear - HSP NU; lia].
    - destruct HSP as [[HSP1 ->]|[[_ ->]|[HSP1 ->]]]; [| constructor |].
      + eapply (ftbl_apres H LBc' SP _ spa mx mx' ATD3 (-48) 88); [exact TA | exact AP | vm_compute; reflexivity | apply CU; clear - HSP1; lia].
      + eapply (ftbl_apres H LBc' SP _ spa mx mx' ATD2 40 88); [exact TA | exact AP | vm_compute; reflexivity | apply CU; clear - HSP1; lia].
    - eapply (ftbl_apres H LBc' SP _ ds mx mx' D0 0 16); [exact TD0 | exact AP | exact FD0 | apply CF; clear - NU; lia].
    - eapply (ftbl_apres H LBc' SP _ ds mx mx' D1 112 120); [exact TD1 | exact AP | exact FD1 | apply CF; clear - NU; lia].
    - eapply (ftbl_apres H LBc' SP _ ff mx mx' FTD2 0 256); [exact TF | exact AP | vm_compute; reflexivity | apply CF; clear - NU; lia].
    - eapply (ftbl_apres H LBc' SP _ (ff / 8) mx mx' HTD2 SHBASE (SHBASE + 32)); [exact TH | exact AP | vm_compute; reflexivity |].
      rewrite (LbB_DtK.shbd_eq ff). replace (SHBASE + 32 - SHBASE) with 32 by (clear; lia). apply CS; clear - NU; lia.
    - eapply xpres_trans; [exact XP|]. eapply xpres_weaken; [exact XPa | exact HSP' | intros b Hb; exact Hb | intros a Ha; exact Ha].
    - eapply (ah_chain_ext H HH); [exact CHN|]. intros fp' ra' a Hin Ha. pose proof (chsp fp' ra' Hin) as K.
      pose proof (ah_chain_range H HH _ _ _ _ _ CHN Hin) as (K1 & _).
      apply AP; [clear - Ha K K1 NU; lia | left; clear - Ha K HSP'; lia].
  Qed.

  Lemma Cf0 : forall n, as_Cf H n = 0.
  Proof. exact (proj1 (rt_bp_cost H HHbp)). Qed.

  Lemma free_call : forall ff fp spa AT sx LBc mx R msFx mox raV SPv CHx RT (POST : config -> Prop),
    dz ff fp spa AT D0T3 D1T3 sx LBc mx ->
    as_VIS H sx msFx = MS R F (Z_to_bv 64 AFREE_STUB) fc None mx (seg_rom asegs) -> rfull R ->
    rtbl (WW ff fp spa) R ((1%bv, ELit raV) :: (10%bv, ELit 0) :: RT) -> rsub KEPT RT = true ->
    PropExec.getr R 4 = tp -> bv_unsigned (PropExec.getr R 2) = SPv -> SPv mod 16 = 0 -> lo <= SPv - AFREE_STACK ->
    (SPv <= spa - 48 /\ AT = ATD3 \/ SPv <= spa /\ AT = []) ->
    as_chain H mx (bv_unsigned (PropExec.getr R 8)) CHx ->
    as_AKREL H sx (mkCfg msFx mox) -> 0 <= raV < 2 ^ 48 -> raV mod 2 = 0 ->
    (forall sx' mx' R' msF' mo', dz ff fp spa AT D0T3 D1T3 sx' LBc mx' ->
        as_VIS H sx' msF' = MS R' F (Z_to_bv 64 raV) fc None mx' (seg_rom asegs) -> rfull R' ->
        rtbl (WW ff fp spa) R' ((1%bv, ELit raV) :: RT) -> as_AKREL H sx' (mkCfg msF' mo') -> as_MPRES H mox mo' ->
        as_SR H POST (mkCfg msF' mo')) ->
    as_SR H POST (mkCfg msFx mox).
  Proof.
    intros ff fp spa AT sx LBc mx R msFx mox raV SPv CHx RT POST Z VIS RF HRT RS K4 U2 SP16 LOS HSP CHN KR RAV RAE K.
    pose proof Z as [G FR RH PM RAUX ERR MI S0 AL RFS Q TS TA TD0 TD1 TF TH XP CH0].
    pose proof (LbB_DtK.d_nums H sp ds err lo ff fp spa hw dptr G) as NU. pose proof aceil_facts as ((A1 & A2) & _).
    destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SPB & BB & _ & _ & CEIL & _ & _ & _ & TP & _ & _
                     & _ & _ & _ & _ & _ & _ & _ & _ & _ & COST).
    pose proof Q as [AC _ ST _ _ _ _ _ _ _ _].
    assert (HSPz : SPv <= spz) by (clear - HSP NU; lia).
    pose proof (rtbl_In _ _ _ (1%bv : reg) (ELit raV) HRT (or_introl eq_refl)) as K1. cbn [edenot] in K1.
    pose proof (rtbl_In _ _ _ (10%bv : reg) (ELit 0) HRT (or_intror (or_introl eq_refl))) as K10. cbn [edenot] in K10.
    rewrite (MS_full_eq R F _ fc mx _ RF) in VIS. rewrite K10 in VIS.
    eapply (ah_seq H HH).
    { eapply ((ah_free_null H HH)
                (PropExec.getr R 1) (PropExec.getr R 2) (PropExec.getr R 3) (PropExec.getr R 4) (PropExec.getr R 5)
                (PropExec.getr R 6) (PropExec.getr R 7) (PropExec.getr R 8) (PropExec.getr R 9)
                (PropExec.getr R 11) (PropExec.getr R 12) (PropExec.getr R 13) (PropExec.getr R 14) (PropExec.getr R 15)
                (PropExec.getr R 16) (PropExec.getr R 17) (PropExec.getr R 18) (PropExec.getr R 19) (PropExec.getr R 20)
                (PropExec.getr R 21) (PropExec.getr R 22) (PropExec.getr R 23) (PropExec.getr R 24) (PropExec.getr R 25)
                (PropExec.getr R 26) (PropExec.getr R 27) (PropExec.getr R 28) (PropExec.getr R 29) (PropExec.getr R 30)
                (PropExec.getr R 31) F fc msFx mx sx LBc lo B errv mox CHx).
      - exact VIS.
      - exact RH.
      - exact KR.
      - rewrite Cf0. clear - AL COST. lia.
      - exact RAUX.
      - rewrite U2. clear - HSPz SPB. lia.
      - rewrite U2. exact (proj1 (stk_split asegs mx lo SPv spz ST ltac:(clear - LOS HSPz; unfold AFREE_STACK in *; lia))).
      - exact CEIL.
      - rewrite U2. exact LOS.
      - rewrite K4. exact ERR.
      - exact MI.
      - rewrite K4. exact TP.
      - rewrite U2. exact SP16.
      - exact AC.
      - exact CHN. }
    intros [msF2 mo2] POST2.
    destruct POST2 as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & s2x
                      & VIS2 & KR2 & MP2 & MI2 & STK2 & ERR2 & RAUX2 & AP2 & RH2 & AC2 & AL2).
    cbn [cfg_ms cfg_model] in VIS2, KR2, MP2. rewrite U2 in STK2, AP2. rewrite K4 in ERR2. rewrite Cf0 in AL2.
    rewrite K1, (ret_pc_even raV ltac:(clear - RAV; lia) RAE) in VIS2.
    assert (Z2 : dz ff fp spa AT D0T3 D1T3 s2x LBc m2).
    { eapply (dz_apres ff fp spa AT D0T3 D1T3 sx s2x LBc LBc mx m2 SPv Z (z_sub _ _ _ _ _ _ _ _ _ Z) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(clear - HSP; tauto) AP2 RH2 RAUX2 ERR2 MI2 AC2 STK2);
        [clear - LOS CEIL; unfold AFREE_STACK in *; lia | clear - LOS; unfold AFREE_STACK in *; lia | clear - AL AL2; lia]. }
    lazymatch type of VIS2 with _ = MS ?RR _ _ _ _ _ _ => set (R2 := RR) in VIS2 end.
    assert (KP : forall r, In r KEPT -> PropExec.getr R2 r = PropExec.getr R r).
    { intros r Hr. subst R2. apply (getr_mkR_keptR R); [exact (eq_sym K1) | exact Hr]. }
    apply (K s2x m2 R2 msF2 mo2 Z2 VIS2); [subst R2; apply rfull_mkR | | exact KR2 | exact MP2].
    assert (HRT' : rtbl (WW ff fp spa) R ((1%bv, ELit raV) :: RT)).
    { unfold rtbl in HRT |- *. apply Forall_cons_iff in HRT as [H1 HRT]. apply Forall_cons_iff in HRT as [_ HRT]. apply Forall_cons; [exact H1 | exact HRT]. }
    apply (rtbl_keep _ R R2 _ KEPT HRT'); [| exact KP].
    unfold rsub. cbn [forallb fst]. unfold rsub in RS. rewrite RS. reflexivity.
  Qed.

  Lemma qwd_laws : forall LBc ff fp spa, dg H sp ds err lo ff fp spa hw dptr -> fresh_frame H LF 2 ff fp ->
    let W := LbB_DtK.QWD sp ds ff fp spa in
    Forall (aclient_write_ok H LBc) W /\ Forall stack0_ok W /\ disjoint_from W (errno_addr tp) 4
    /\ Forall (fun iv : Z * Z => (aceil <= fst iv /\ snd iv <= spz) \/ (forall a, fst iv <= a < snd iv -> rin_ivs ([(ds, ds + DS_SIZE)] ++ XSd ff fp) a)) W
    /\ (forall fp' ra' a, In (fp', ra') CH -> fp' - 16 <= a < fp' -> outside W a).
  Proof.
    intros LBc ff fp spa G FR.
    pose proof (LbB_DtK.d_nums H sp ds err lo ff fp spa hw dptr G) as NU.
    pose proof (LbB_Dt.fr_place2 H sp tp a0 m ds len err lo LF LB DB ms pp hm fl fill s CTX LF ff fp FR) as (K2 & K3 & K4 & K6 & K6' & B1 & B2 & R2 & R3 & B4 & AP & S1 & S2 & S3 & S4 & S5 & S6 & S7 & A1).
    pose proof (LbB_Dt.ds_facts H HHbp sp tp a0 m ds len err lo LF LB DB ms pp hm fl fill s CTX) as (_ & _ & DSO & _ & _ & DSH & F3 & F4 & DSM & _).
    unfold AFS_HDR, AFS_SIZE, DS_SIZE in F3, F4, DSM.
    assert (TP : tp = Z_to_bv 64 ATP) by (destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TP & _); exact TP).
    assert (ERR : errno_addr tp + 4 <= 0x6e8000) by (rewrite TP, unsigned_lit by (clear; unfold ATP; lia); clear; unfold ATP; cbn; lia).
    set (e := errno_addr tp) in *. clearbody e.
    assert (SA : ALOWSH_LO <= sh aceil) by (clear - A1; unfold sh, ASHADOW_BASE, ALOWSH_LO in *; Z.div_mod_to_equations; lia).
    cbv zeta. unfold LbB_DtK.QWD. rewrite !Z.add_assoc, (LbB_DtK.shbd_eq ff), Z.add_0_r.
    split; [| split; [| split; [| split]]].
    - repeat apply Forall_cons; try apply Forall_nil; unfold aclient_write_ok; cbn [fst snd].
      + left. clear - R2 NU. lia.
      + left. clear - R2 NU. lia.
      + right; right; right; right; left. clear - F3 F4. unfold AFS_SIZE. lia.
      + right; right; right; right; left. clear - F3 F4. unfold AFS_SIZE. lia.
      + right; right; right; right; left. clear - K2 K3. unfold AFS_SIZE in *. lia.
      + right; right; right; right; right; left. clear - S2 S3 S1. unfold AFS_SIZE. unfold sh in *. lia.
      + right; right; right; right; left. clear - K6 K6'. unfold AFS_SIZE in *. lia.
    - repeat apply Forall_cons; try apply Forall_nil; unfold stack0_ok; cbn [fst snd].
      + left. clear - R2 NU A1. unfold AHI_LO in *. lia.
      + left. clear - R2 NU A1. unfold AHI_LO in *. lia.
      + clear - B4 SA F3 F4. unfold ALOWSH_LO, AHI_LO in *. destruct B4; [right | left]; lia.
      + clear - B4 SA F3 F4. unfold ALOWSH_LO, AHI_LO in *. destruct B4; [right | left]; lia.
      + clear - B4 SA K2 K3. unfold ALOWSH_LO, AHI_LO in *. destruct B4; [right | left]; lia.
      + right. clear - S3 S7. lia.
      + clear - B4 SA K6 K6'. unfold ALOWSH_LO, AHI_LO in *. destruct B4; [right | left]; lia.
    - cbn [disjoint_from]. clear - ERR R2 NU A1 B1 F3 K2 K6 S1 S2. lia.
    - repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      + left. clear - R2 NU. lia.
      + left. clear - R2 NU. lia.
      + right. intros a Ha. apply rin_ivs_app. left. cbn [rin_ivs fst snd]. left. unfold DS_SIZE. clear - Ha. lia.
      + right. intros a Ha. apply rin_ivs_app. left. cbn [rin_ivs fst snd]. left. unfold DS_SIZE. clear - Ha. lia.
      + right. intros a Ha. apply rin_ivs_app. right. unfold XSd. cbn [rin_ivs fst snd]. right; right; left. replace (fsz 2) with 256 by reflexivity. clear - Ha. lia.
      + right. intros a Ha. apply rin_ivs_app. right. unfold XSd. cbn [rin_ivs fst snd]. right; right; right; left. replace (fshn 2) with 32 by reflexivity. clear - Ha. lia.
      + right. intros a Ha. apply rin_ivs_app. right. unfold XSd. cbn [rin_ivs fst snd]. right; left. clear - Ha. lia.
    - intros fp' ra' a Hin Ha. pose proof (chsp fp' ra' Hin) as K. cbn [outside fst snd].
      clear - Ha K NU K2 K6 S3 S4 S6 B2 A1. lia.
  Qed.

  Lemma dz_run : forall ff fp spa AT D0 D1 AT' D0' D1' sx LBc mx m1,
    dz ff fp spa AT D0 D1 sx LBc mx -> munch (removelast (LbB_DtK.QWD sp ds ff fp spa)) mx m1 -> wmono asegs mx m1 -> mem_inv asegs m1 ->
    df sp ds err lo ff fp hw dptr 0 m1 ->
    ftbl (WW ff fp spa) spz m1 TSD -> ftbl (WW ff fp spa) spa m1 AT' -> ftbl (WW ff fp spa) ds m1 D0' -> ftbl (WW ff fp spa) ds m1 D1' ->
    ftbl (WW ff fp spa) ff m1 FTD2 -> ftbl (WW ff fp spa) (ff / 8) m1 HTD2 ->
    dz ff fp spa AT' D0' D1' sx LBc m1.
  Proof.
    intros ff fp spa AT D0 D1 AT' D0' D1' sx LBc mx m1 Z MU WM MI1 Q1 T1 T2 T3 T4 T5 T6.
    destruct Z as [G FR RH PM RAUX ERR MI S0 AL RFS Q TS TA TD0 TD1 TF TH XP CHN].
    destruct (qwd_laws LBc ff fp spa G FR) as (L1 & L2 & L3 & L4 & L5).
    assert (SUB : forall P : Z * Z -> Prop, Forall P (LbB_DtK.QWD sp ds ff fp spa) -> Forall P (removelast (LbB_DtK.QWD sp ds ff fp spa))).
    { intros P HP. unfold LbB_DtK.QWD in *. cbn [removelast].
      repeat match type of HP with Forall _ (_ :: _) => apply Forall_cons_iff in HP as [? HP] end.
      repeat apply Forall_cons; try assumption; try apply Forall_nil. }
    pose proof (LbB_DtK.munch6_QWD sp ds ff fp spa mx m1 MU) as MU7.
    constructor; try assumption.
    - eapply (ah_RHEAP_frame H HH); [exact RH | exact MU | exact WM | apply SUB; exact L1].
    - eapply (ah_rauxv_frame H HH); [exact RAUX | exact MU | exact WM | apply SUB; exact L1].
    - eapply rw_cells_transport; [exact ERR | exact MU7 | exact WM | exact L3].
    - eapply stack0_transport; [exact S0 | exact MU | exact WM | apply SUB; exact L2].
    - eapply (LbB_DtK.RFS_stepd H HHbp sp ds err lo ff fp spa hw dptr G); [exact RFS | left; reflexivity | | exact MU | exact WM].
      apply (LbB_Dt.dsin2 H sp tp a0 m ds len err lo LF LB DB ms pp hm fl fill s CTX).
    - eapply xpres_trans; [exact XP|].
      eapply xpres_weaken; [| apply Z.le_refl | exact PM | intros a Ha; exact Ha].
      eapply (xpres_of_munch H sx LBc); [exact HH | exact RH | exact MU | exact WM |].
      eapply Forall_impl; [| apply SUB; exact L4]. intros iv Hiv. exact Hiv.
    - eapply (ah_chain_ext H HH); [exact CHN|]. intros fp' ra' a Hin Ha. apply MU7.
      pose proof (ah_chain_range H HH _ _ _ _ _ CHN Hin) as (R1 & _). pose proof aceil_facts as ((A1 & _) & _).
      rewrite unsigned_lit by (clear - Ha R1 A1; lia). exact (L5 fp' ra' a Hin Ha).
  Qed.

  Lemma flag0_of_tbl : forall W fp mx, ftbl W fp mx LTZ -> mrd asegs mx (wa fp) = Some (b8 0).
  Proof.
    intros W fp mx HL. pose proof (ftbl_In W fp mx LTZ 0 1 (ELit 0) HL ltac:(left; reflexivity)) as C.
    rewrite Z.add_0_r in C. destruct C as [[_ (_ & _ & B0)] _]. specialize (B0 0%nat ltac:(cbn; lia)).
    rewrite Z.add_0_r in B0. exact B0.
  Qed.

  Lemma dz_at_nil : forall ff fp spa AT D0 D1 sx LBc mx, dz ff fp spa AT D0 D1 sx LBc mx -> dz ff fp spa [] D0 D1 sx LBc mx.
  Proof. intros ff fp spa AT D0 D1 sx LBc mx Z. destruct Z. constructor; try assumption. constructor. Qed.

  Lemma chain_sp0g : forall ff fp spa mx, dg H sp ds err lo ff fp spa hw dptr -> ftbl (WW ff fp spa) spz mx TSD ->
    as_chain H mx (bv_unsigned s0) CH -> as_chain H mx spz ((spz, bv_unsigned ra) :: CH).
  Proof.
    intros ff fp spa mx G TS CHN.
    pose proof (LbB_DtK.d_nums H sp ds err lo ff fp spa hw dptr G) as NU. pose proof aceil_facts as ((A1 & A2) & _).
    pose proof (bv_unsigned_in_range 64 s0) as R0. pose proof (bv_unsigned_in_range 64 ra) as R1. change (bv_modulus 64) with (2 ^ 64) in R0, R1.
    destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SP16 & _ & CEIL & _).
    pose proof (C8_of_ftbl _ spz mx TSD (-16) (EVar 35) TS ltac:(cbn; tauto)) as C16.
    pose proof (C8_of_ftbl _ spz mx TSD (-8) (EVar 34) TS ltac:(cbn; tauto)) as Cm8.
    revert C16 Cm8. evWW. intros C16 Cm8.
    apply (ah_chain_cons H HH mx (bv_unsigned s0) CH spz (bv_unsigned ra) CHN); [clear - R0; lia | clear - R1; lia | exact SP16 | clear - NU CEIL; lia | clear - NU; lia |].
    rewrite !Z_to_bv_bv_unsigned. apply (proj2 (rw_cells_app asegs mx (spz - 16) [C8 s0] [C8 ra])).
    replace (spz - 16) with (spz + -16) by (clear; lia). split; [exact C16|]. cbn [cells_size csize Nat.add].
    replace (spz + -16 + Z.of_nat 8) with (spz + -8) by (clear; lia). exact Cm8.
  Qed.
  Lemma chain_sp0 : forall ff fp spa AT D0 D1 sx LBc mx, dz ff fp spa AT D0 D1 sx LBc mx ->
    as_chain H mx spz ((spz, bv_unsigned ra) :: CH).
  Proof.
    intros ff fp spa AT D0 D1 sx LBc mx Z. pose proof Z as [G _ _ _ _ _ _ _ _ _ _ TS _ _ _ _ _ _ CHN]. exact (chain_sp0g ff fp spa mx G TS CHN).
  Qed.

  Definition POST : config -> Prop :=
    ds_post H LINV_P5 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LBk LF [(ds, ds + DS_SIZE)] 0 lo B shi m mo None
            (fun LB' m' => Permutation LB' LBk /\ addressable m' ds DS_SIZE /\ wr_at asegs m' ds DS_SIZE).

  Lemma fin_post : forall ff fp spa sx LBc m8 R' m9 msF' mo',
    dz ff fp spa [] D0T3 D1T3 sx LBc m8 -> Permutation LBc LBk ->
    munch (LbB_DtK.QWD sp ds ff fp spa) m8 m9 -> wmono asegs m8 m9 -> mem_inv asegs m9 -> df sp ds err lo ff fp hw dptr 0 m9 ->
    rfull R' -> rtbl (WW ff fp spa) R' RTDF -> ftbl (WW ff fp spa) fp m9 LTZ ->
    as_VIS H sx msF' = MS R' F (ret_pc (PropExec.getr R' 1)) fc None m9 (seg_rom asegs) ->
    as_AKREL H sx (mkCfg msF' mo') -> as_MPRES H mo mo' ->
    POST (mkCfg msF' mo').
  Proof.
    intros ff fp spa sx LBc m8 R' m9 msF' mo' Z PMc MU WM MI9 Q9 RF' HRT' HL9 VIS' KR' MP'.
    destruct Z as [G FR RH PM RAUX ERR MI S0 AL RFS Q TS TA TD0 TD1 TF TH XP CHN].
    destruct (qwd_laws LBc ff fp spa G FR) as (L1 & L2 & L3 & L4 & L5).
    pose proof (LbB_DtK.d_nums H sp ds err lo ff fp spa hw dptr G) as NU. pose proof aceil_facts as ((A1 & A2) & _).
    destruct PRE as (_ & FZ & _).
    pose proof Q9 as [AC9 LV9 ST9 DSA9 DSW9 _ _ _ _ _ _].

    rgq HRT' (1%bv : reg) (EVar 34) G1r. rgq HRT' (2%bv : reg) (EVar 33) G2r. rgq HRT' (3%bv : reg) (EVar 47) G3r. rgq HRT' (4%bv : reg) (EVar 48) G4r.
    rgq HRT' (8%bv : reg) (EVar 35) G8r. rgq HRT' (9%bv : reg) (EVar 36) G9r.
    rgq HRT' (18%bv : reg) (EVar 37) G18r. rgq HRT' (19%bv : reg) (EVar 38) G19r. rgq HRT' (20%bv : reg) (EVar 39) G20r.
    rgq HRT' (21%bv : reg) (EVar 40) G21r. rgq HRT' (22%bv : reg) (EVar 41) G22r. rgq HRT' (23%bv : reg) (EVar 42) G23r.
    rgq HRT' (24%bv : reg) (EVar 43) G24r. rgq HRT' (25%bv : reg) (EVar 44) G25r. rgq HRT' (26%bv : reg) (EVar 45) G26r.
    rgq HRT' (27%bv : reg) (EVar 46) G27r.
    rewrite (MS_full_eq R' F _ fc m9 _ RF') in VIS'.
    rewrite G1r, G2r, G3r, G4r, G8r, G9r, G18r, G19r, G20r, G21r, G22r, G23r, G24r, G25r, G26r, G27r in VIS'.

    assert (RFS9 : as_RFS H LF m9).
    { pose proof (ah_release H HH _ m8 m9 _ 2 ff fp RFS (or_introl eq_refl) MU WM) as KR. rewrite lf_remove_head in KR. apply KR.
      - pose proof (LbB_Dt.fr_place2 H sp tp a0 m ds len err lo LF LB DB ms pp hm fl fill s CTX LF ff fp FR) as (K2 & K3 & K4 & K6 & K6' & B1 & B2 & R2 & R3 & B4 & AP & S1 & S2 & S3 & S4 & S5 & S6 & S7 & A1').
        unfold LbB_DtK.QWD. rewrite !Z.add_assoc, (LbB_DtK.shbd_eq ff), Z.add_0_r.
        repeat apply Forall_cons; try apply Forall_nil.
        + left. left. cbn [fst snd]. clear - NU R2. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE. lia.
        + left. left. cbn [fst snd]. clear - NU R2. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE. lia.
        + left. apply (LbB_DtK.afsd_ok_ds H ds _ _ _ (LbB_Dt.dsin2 H sp tp a0 m ds len err lo LF LB DB ms pp hm fl fill s CTX ff fp)); unfold DS_SIZE; clear; lia.
        + left. apply (LbB_DtK.afsd_ok_ds H ds _ _ _ (LbB_Dt.dsin2 H sp tp a0 m ds len err lo LF LB DB ms pp hm fl fill s CTX ff fp)); unfold DS_SIZE; clear; lia.
        + left. right. exists (2, ff, fp). split; [left; reflexivity|]. cbn [ff_addr ff_class fst snd]. replace (fsz 2) with 256 by reflexivity. clear. lia.
        + left. apply (LbB_DtK.afsd_ok_shadow H sp ds err lo ff fp spa hw dptr G).
        + right. cbn [fst snd]. clear. split; lia.
      - exact (flag0_of_tbl _ fp m9 HL9). }

    unfold POST, ds_post. cbn [cfg_ms cfg_model].
    exists (PropExec.getr R' 5), (PropExec.getr R' 6), (PropExec.getr R' 7), (PropExec.getr R' 10), (PropExec.getr R' 11), (PropExec.getr R' 12),
           (PropExec.getr R' 13), (PropExec.getr R' 14), (PropExec.getr R' 15), (PropExec.getr R' 16), (PropExec.getr R' 17),
           (PropExec.getr R' 28), (PropExec.getr R' 29), (PropExec.getr R' 30), (PropExec.getr R' 31), m9, errv, sx, LBc, (XSd ff fp), F, fc.
    split; [exact VIS'|]. split; [exact FZ|]. split; [intros d Hd; discriminate Hd|].
    split; [exact KR'|]. split; [exact MP'|]. split; [exact MI9|]. split; [exact ST9|].
    split; [eapply rw_cells_transport; [exact ERR | exact MU | exact WM | exact L3]|].
    split; [eapply (ah_rauxv_frame H HH); [exact RAUX | exact MU | exact WM | exact L1]|].
    split; [eapply (ah_RHEAP_frame H HH); [exact RH | exact MU | exact WM | exact L1]|].
    split; [split; [exact PMc | split; [exact DSA9 | exact DSW9]]|].
    split; [exact (xsd_scratch ff fp FR)|].
    split.
    { eapply xpres_trans; [exact XP|].
      eapply xpres_weaken; [| apply Z.le_refl | exact PM | intros a Ha; exact Ha].
      eapply (xpres_of_munch H sx LBc); [exact HH | exact RH | exact MU | exact WM | exact L4]. }
    split; [exact RFS9|]. split; [exact AC9|].
    split; [eapply stack0_transport; [exact S0 | exact MU | exact WM | exact L2]|].
    split; [exact LV9 | clear - AL; lia].
  Qed.

  Lemma dt_tail : forall ff fp spa sx LBc mx R msFx mox,
    dz ff fp spa ATD2 D0T2 D1T2 sx LBc mx -> Permutation LBc LBk ->
    as_VIS H sx msFx = MS R F (Z_to_bv 64 ADT_D3) fc None mx (seg_rom asegs) -> rfull R -> rtbl (WW ff fp spa) R RTD3 ->
    as_AKREL H sx (mkCfg msFx mox) -> as_MPRES H mo mox ->
    as_SR H POST (mkCfg msFx mox).
  Proof.
    intros ff fp spa sx LBc mx R msFx mox Z PMc VIS RF HRT KR MP.
    pose proof Z as [G FR RH PM RAUX ERR MI S0 AL RFS Q TS TA TD0 TD1 TF TH XP CHN].
    pose proof (LbB_DtK.d_nums H sp ds err lo ff fp spa hw dptr G) as NU. pose proof aceil_facts as ((A1 & A2) & _).
    destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SP16 & _ & CEIL & LO & _ & _ & TP & _).
    assert (SPA16 : (spa - 48) mod 16 = 0 /\ spa mod 16 = 0) by (clear - NU; Z.div_mod_to_equations; lia).
    destruct SPA16 as [SPA16 SPA16'].
    assert (LOS : lo <= spa - 48 - AFREE_STACK /\ lo <= spa - AFREE_STACK) by (clear - NU; unfold AFREE_STACK; lia).
    destruct LOS as [LOS LOS'].
    pose proof (LbB_DtK.d_ranges H sp ds err lo ff fp spa hw dptr G) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rds4 & _).
    assert (DSC : ds + 112 <= aceil) by (clear - Rds4; unfold DS_SIZE in Rds4; lia). clear Rds4.

    eapply (ahh_evt_then H HH _ _ sx msFx _ mox KR VIS).
    { eapply (q_d3 H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ds err lo ff fp spa hw dptr G mx R mx RF HRT TS TA TD0 TD1 TF TH (conj Q (LbB_DtK.Dx_refl sp ds ff fp spa mx)) MI). }
    intros msF1 mo1 KR1 MP1 (R1 & m1 & E1 & RF1 & HRT1 & HX1 & HA1 & HD01 & HD11 & HF1 & HH1 & HQP1 & MI1 & MU1 & WM1).
    pose proof (dz_run ff fp spa _ _ _ _ _ _ sx LBc mx m1 Z MU1 WM1 MI1 (LbB_DtK.Dx_ok H sp ds err lo ff fp spa hw dptr G 0%nat mx m1 HQP1 MI1)
                  HX1 HA1 HD01 HD11 HF1 HH1) as Z1.

    rgq HRT1 (4%bv : reg) (EVar 48) K4. rgq HRT1 (2%bv : reg) (EAlu ALU_ADD (EVar 51) (ELit (-48))) K2.
    rgq HRT1 (8%bv : reg) (EAlu ALU_ADD (EVar 32) (ELit 112)) K8.
    rewrite w_addm in K2 by (clear - NU; lia). rewrite w_add in K8 by (clear - NU; lia).
    eapply (free_call ff fp spa ATD3 sx LBc m1 R1 msF1 mo1 0x1236c4 (spa - 48) [] RTD4 POST Z1 E1 RF1 HRT1 eq_refl K4);
      [rewrite K2; apply unsigned_lit; clear - NU; lia | exact SPA16 | exact LOS | left; split; [apply Z.le_refl | reflexivity]
      | rewrite K8, unsigned_lit by (clear - NU; lia); apply (ah_chain_nil H HH); left; exact DSC
      | exact KR1 | clear; lia | reflexivity |].
    clear R1 msF1 E1 RF1 HRT1 HX1 HA1 HD01 HD11 HF1 HH1 HQP1 MI1 MU1 WM1 Z1 K4 K2 K8 KR1.
    intros sx2 m2 R2 msF2 mo2 Z2 E2 RF2 HRT2 KR2 MP2.

    pose proof Z2 as [_ _ _ _ _ _ MI2 _ _ _ Q2 TS2 TA2 TD02 TD12 TF2 TH2 _ _].
    assert (HRT2' : rtbl (WW ff fp spa) R2 RTD4) by (apply (rtbl_sub _ _ _ _ HRT2); vm_compute; reflexivity).
    eapply (ahh_evt_then H HH _ _ sx2 msF2 _ mo2 KR2 E2).
    { eapply (q_d4 H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ds err lo ff fp spa hw dptr G m2 R2 m2 RF2 HRT2' TS2 TA2 TD02 TD12 TF2 TH2 (conj Q2 (LbB_DtK.Dx_refl sp ds ff fp spa m2)) MI2). }
    intros msF3 mo3 KR3 MP3 (R3 & m3 & E3 & RF3 & HRT3 & HX3 & HA3 & HD03 & HD13 & HF3 & HH3 & HQP3 & MI3 & MU3 & WM3).
    pose proof (dz_run ff fp spa _ _ _ _ _ _ sx2 LBc m2 m3 Z2 MU3 WM3 MI3 (LbB_DtK.Dx_ok H sp ds err lo ff fp spa hw dptr G 0%nat m2 m3 HQP3 MI3)
                  HX3 HA3 HD03 HD13 HF3 HH3) as Z3.

    rgq HRT3 (4%bv : reg) (EVar 48) K4. rgq HRT3 (2%bv : reg) (EAlu ALU_ADD (EVar 51) (ELit (-48))) K2.
    rgq HRT3 (8%bv : reg) (EAlu ALU_ADD (EVar 32) (ELit 112)) K8.
    rewrite w_addm in K2 by (clear - NU; lia). rewrite w_add in K8 by (clear - NU; lia).
    eapply (free_call ff fp spa ATD3 sx2 LBc m3 R3 msF3 mo3 0x1236cc (spa - 48) [] RTD4 POST Z3 E3 RF3 HRT3 eq_refl K4);
      [rewrite K2; apply unsigned_lit; clear - NU; lia | exact SPA16 | exact LOS | left; split; [apply Z.le_refl | reflexivity]
      | rewrite K8, unsigned_lit by (clear - NU; lia); apply (ah_chain_nil H HH); left; exact DSC
      | exact KR3 | clear; lia | reflexivity |].
    clear sx2 m2 R2 msF2 Z2 E2 RF2 HRT2 KR2 MI2 Q2 TS2 TA2 TD02 TD12 TF2 TH2 HRT2' R3 msF3 E3 RF3 HRT3 HX3 HA3 HD03 HD13 HF3 HH3 HQP3 MI3 MU3 WM3 Z3 K4 K2 K8 KR3.
    intros sx4 m4 R4 msF4 mo4 Z4 E4 RF4 HRT4 KR4 MP4.

    pose proof Z4 as [_ _ _ _ _ _ MI4 _ _ _ Q4 TS4 TA4 TD04 TD14 TF4 TH4 _ _].
    assert (HRT4' : rtbl (WW ff fp spa) R4 RTD4) by (apply (rtbl_sub _ _ _ _ HRT4); vm_compute; reflexivity).
    eapply (ahh_evt_then H HH _ _ sx4 msF4 _ mo4 KR4 E4).
    { eapply (q_d5 H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ds err lo ff fp spa hw dptr G m4 R4 m4 RF4 HRT4' TS4 TA4 TD04 TD14 TF4 TH4 (conj Q4 (LbB_DtK.Dx_refl sp ds ff fp spa m4)) MI4). }
    intros msF5 mo5 KR5 MP5 (R5 & m5 & E5 & RF5 & HRT5 & HX5 & HA5 & HD05 & HD15 & HF5 & HH5 & HQP5 & MI5 & MU5 & WM5).
    pose proof (dz_run ff fp spa _ _ _ _ _ _ sx4 LBc m4 m5 Z4 MU5 WM5 MI5 (LbB_DtK.Dx_ok H sp ds err lo ff fp spa hw dptr G 0%nat m4 m5 HQP5 MI5)
                  HX5 HA5 HD05 HD15 HF5 HH5) as Z5.

    rgq HRT5 (4%bv : reg) (EVar 48) K4. rgq HRT5 (2%bv : reg) (EAlu ALU_ADD (EVar 51) (ELit (-48))) K2.
    rgq HRT5 (8%bv : reg) (EAlu ALU_ADD (EVar 32) (ELit 112)) K8.
    rewrite w_addm in K2 by (clear - NU; lia). rewrite w_add in K8 by (clear - NU; lia).
    eapply (free_call ff fp spa ATD3 sx4 LBc m5 R5 msF5 mo5 0x1236d4 (spa - 48) [] RTD4 POST Z5 E5 RF5 HRT5 eq_refl K4);
      [rewrite K2; apply unsigned_lit; clear - NU; lia | exact SPA16 | exact LOS | left; split; [apply Z.le_refl | reflexivity]
      | rewrite K8, unsigned_lit by (clear - NU; lia); apply (ah_chain_nil H HH); left; exact DSC
      | exact KR5 | clear; lia | reflexivity |].
    clear sx4 m4 R4 msF4 Z4 E4 RF4 HRT4 KR4 MI4 Q4 TS4 TA4 TD04 TD14 TF4 TH4 HRT4' R5 msF5 E5 RF5 HRT5 HX5 HA5 HD05 HD15 HF5 HH5 HQP5 MI5 MU5 WM5 Z5 K4 K2 K8 KR5.
    intros sx6 m6 R6 msF6 mo6 Z6 E6 RF6 HRT6 KR6 MP6.

    pose proof Z6 as [_ _ _ _ _ _ MI6 _ _ _ Q6 TS6 TA6 TD06 TD16 TF6 TH6 _ _].
    assert (HRT6' : rtbl (WW ff fp spa) R6 RTD4) by (apply (rtbl_sub _ _ _ _ HRT6); vm_compute; reflexivity).
    eapply (ahh_evt_then H HH _ _ sx6 msF6 _ mo6 KR6 E6).
    { eapply (q_d6 H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ds err lo ff fp spa hw dptr G m6 R6 m6 RF6 HRT6' TS6 TA6 TD06 TD16 TF6 TH6 (conj Q6 (LbB_DtK.Dx_refl sp ds ff fp spa m6)) MI6). }
    intros msF7 mo7 KR7 MP7 (R7 & m7 & E7 & RF7 & HRT7 & HX7 & HA7 & HD07 & HD17 & HF7 & HH7 & HQP7 & MI7 & MU7 & WM7).
    pose proof (dz_run ff fp spa _ _ _ _ _ _ sx6 LBc m6 m7 Z6 MU7 WM7 MI7 (LbB_DtK.Dx_ok H sp ds err lo ff fp spa hw dptr G 0%nat m6 m7 HQP7 MI7)
                  HX7 HA7 HD07 HD17 HF7 HH7) as Z7.

    rgq HRT7 (4%bv : reg) (EVar 48) K4. rgq HRT7 (2%bv : reg) (EVar 51) K2. rgq HRT7 (8%bv : reg) (EVar 33) K8.
    eapply (free_call ff fp spa [] sx6 LBc m7 R7 msF7 mo7 0xfd17c spa ((spz, bv_unsigned ra) :: CH) RTD3 POST (dz_at_nil _ _ _ _ _ _ _ _ _ Z7) E7 RF7 HRT7 eq_refl K4);
      [rewrite K2; apply unsigned_lit; clear - NU; lia | exact SPA16' | exact LOS' | right; split; [apply Z.le_refl | reflexivity]
      | rewrite K8; exact (chain_sp0 _ _ _ _ _ _ _ _ _ Z7)
      | exact KR7 | clear; lia | reflexivity |].
    clear sx6 m6 R6 msF6 Z6 E6 RF6 HRT6 KR6 MI6 Q6 TS6 TA6 TD06 TD16 TF6 TH6 HRT6' R7 msF7 E7 RF7 HRT7 HX7 HA7 HD07 HD17 HF7 HH7 HQP7 MI7 MU7 WM7 Z7 K4 K2 K8 KR7.
    intros sx8 m8 R8 msF8 mo8 Z8 E8 RF8 HRT8 KR8 MP8.

    pose proof Z8 as [_ _ _ _ _ _ MI8 _ _ _ Q8 TS8 TA8 TD08 TD18 TF8 TH8 _ _].
    assert (HRT8' : rtbl (WW ff fp spa) R8 RTD3) by (apply (rtbl_sub _ _ _ _ HRT8); vm_compute; reflexivity).
    assert (HL8 : ftbl (WW ff fp spa) fp m8 []) by constructor.
    eapply (ahh_evt_then H HH _ _ sx8 msF8 _ mo8 KR8 E8).
    { eapply evt_cut; [eapply (q_d7 H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ds err lo ff fp spa hw dptr G m8 R8 m8 RF8 HRT8' TS8 TA8 TD08 TD18 TF8 TH8 HL8 (conj Q8 (LbB_DtK.Dx_refl sp ds ff fp spa m8)) MI8)|].
      intros ms9 (R9 & m9 & -> & RF9 & HRT9 & HL9 & HQP9 & MI9 & MU9 & WM9).
      rewrite (MS_full_eq R9 F _ fc m9 _ RF9). apply dt_ret_ok.
      instantiate (1 := fun msx => exists R' m', msx = MS R' F (ret_pc (PropExec.getr R' 1)) fc None m' (seg_rom asegs)
         /\ rfull R' /\ rtbl (WW ff fp spa) R' RTDF /\ ftbl (WW ff fp spa) fp m' LTZ
         /\ (df sp ds err lo ff fp hw dptr 0 m8 /\ LbB_DtK.Dx sp ds ff fp spa m8 m') /\ mem_inv asegs m' /\ munch (LbB_DtK.QWD sp ds ff fp spa) m8 m' /\ wmono asegs m8 m').
      cbv beta. exists R9, m9. rewrite <- (MS_full_eq R9 F _ fc m9 _ RF9).
      split; [reflexivity|]. split; [exact RF9|]. split; [exact HRT9|]. split; [exact HL9|]. split; [exact HQP9|]. split; [exact MI9|]. split; [exact MU9 | exact WM9]. }
    intros msF9 mo9 KR9 MP9 (R' & m' & E9 & RF' & HRT' & HL' & HQP' & MI' & MU' & WM').
    apply (ah_done H HH).
    eapply (fin_post ff fp spa sx8 LBc m8 R' m' msF9 mo9 Z8 PMc MU' WM' MI' (LbB_DtK.Dx_ok H sp ds err lo ff fp spa hw dptr G 0%nat m8 m' HQP' MI') RF' HRT' HL' E9 KR9).
    eapply (ah_mpres_trans H HH); [exact MP|]. eapply (ah_mpres_trans H HH); [exact MP1|]. eapply (ah_mpres_trans H HH); [exact MP2|].
    eapply (ah_mpres_trans H HH); [exact MP3|]. eapply (ah_mpres_trans H HH); [exact MP4|]. eapply (ah_mpres_trans H HH); [exact MP5|].
    eapply (ah_mpres_trans H HH); [exact MP6|]. eapply (ah_mpres_trans H HH); [exact MP7|]. eapply (ah_mpres_trans H HH); [exact MP8 | exact MP9].
  Qed.

  Lemma dt_main : as_SR H POST (mkCfg msF mo).
  Proof.
    pose proof PRE as PRE'.
    destruct PRE' as (VIS & FZ & RH & KR & OWN & LBS & LBC & LBL & RAUX & SPB & BB & SP16 & STK & CEIL & LO & ERRN & MI & TP & RA2 & LV
                      & AC & RFS & LFn & S0 & SPS & CHN & PF' & CHsp & TRok & COST).
    pose proof REPW as (DI0 & BLK0 & DSA0 & DSW0 & DSO0 & SBA0).
    assert (SUBk : forall b, In b LBk -> In b LB).
    { intros b Hb. apply (Permutation_in _ (Permutation_sym PERM)). apply in_or_app. right. exact Hb. }
    eapply (ahh_evt_then H HH _ _ s msF _ mo KR VIS).
    { eapply evt_cut; [apply (dt_s1 H HHbp ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ds len err lo LF LB DB ms pp hm fl fill s CTX)|].
      intros ms1 (ff & fp & spa & R1 & m1 & -> & ST1).
      eapply evt_cut; [apply (dt_s2 H HHbp ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m ds len err lo LF LB DB ms pp hm fl fill s CTX ff fp spa R1 m1 ST1)|].
      intros ms2 (R2 & m2 & -> & ST2).
      apply evt_done.
      instantiate (1 := fun msx => exists ff fp spa R' m', msx = MS R' F (Z_to_bv 64 (LbB_Dt.PC2x ms)) fc None m' (seg_rom asegs)
         /\ dt_st2 H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m ds err lo LF ms ff fp spa R' m').
      cbv beta. exists ff, fp, spa, R2, m2. split; [reflexivity | exact ST2]. }
    intros msF2 mo2 KR2 MP2 (ff & fp & spa & R2 & m2 & E2 & ST2).
    destruct ST2 as [G FR RF2 HRT2 TS2 TA2 TD02 TD12 TF2 TH2 Q2 MI2 RFS2 MU2 WM2].
    pose proof (LbB_DtK.d_nums H sp ds err lo ff fp spa hw dptr G) as NU. pose proof aceil_facts as ((A1 & A2) & _).
    destruct (LbB_Dt.wa2_laws H HHbp sp tp a0 m ds len err lo LF LB DB ms pp hm fl fill s CTX LB ((2, ff, fp) :: LF) ff fp FR (or_introl eq_refl)
                (LbB_Dt.dsin2 H sp tp a0 m ds len err lo LF LB DB ms pp hm fl fill s CTX ff fp)) as (L1 & L2 & L3 & L4 & L5).
    pose proof (LbB_Dt.fr_place2 H sp tp a0 m ds len err lo LF LB DB ms pp hm fl fill s CTX LF ff fp FR) as (K2 & K3 & K4 & K6 & K6' & B1 & B2 & R2' & R3' & B4 & AP & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & A1').

    assert (ERRW : disjoint_from (LbB_Dt.WA2 H sp ds ff fp) (errno_addr tp) 4).
    { assert (ERR : errno_addr tp + 4 <= 0x6e8000) by (rewrite TP, unsigned_lit by (clear; unfold ATP; lia); clear; unfold ATP; cbn; lia).
      set (e := errno_addr tp) in *. clearbody e. unfold LbB_Dt.WA2, AFS_FLAGS. cbn [disjoint_from]. clear - ERR NU B1 K2 K6 Y1 Y2. lia. }
    assert (RH2 : as_RHEAP H s LB m2) by (eapply (ah_RHEAP_frame H HH); [exact RH | exact MU2 | exact WM2 | exact L1]).
    assert (RAUX2 : as_rauxv_ok H m2 B) by (eapply (ah_rauxv_frame H HH); [exact RAUX | exact MU2 | exact WM2 | exact L1]).
    assert (ERR2 : rw_cells asegs m2 (errno_addr tp) [C4 errv]) by (eapply rw_cells_transport; [exact ERRN | exact MU2 | exact WM2 | exact ERRW]).
    assert (S02 : stack0 m2 lo shi) by (eapply stack0_transport; [exact S0 | exact MU2 | exact WM2 | exact L2]).
    assert (XP2 : xpres H LBk spz ([(ds, ds + DS_SIZE)] ++ XSd ff fp) m m2).
    { eapply xpres_weaken; [| apply Z.le_refl | exact SUBk | intros a Ha; exact Ha].
      eapply (xpres_of_munch H s LB); [exact HH | exact RH | exact MU2 | exact WM2 |].
      unfold LbB_Dt.WA2. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      - left. clear - CEIL LO. unfold ADS_STACK in *. lia.
      - right. intros a Ha. apply rin_ivs_app. right. unfold XSd. cbn [rin_ivs fst snd]. left. exact Ha.
      - right. intros a Ha. apply rin_ivs_app. right. unfold XSd. cbn [rin_ivs fst snd]. right; left. exact Ha.
      - right. intros a Ha. apply rin_ivs_app. right. unfold XSd. cbn [rin_ivs fst snd]. right; right; left. replace (fsz 2) with 256 by reflexivity. exact Ha.
      - right. intros a Ha. apply rin_ivs_app. right. unfold XSd. cbn [rin_ivs fst snd]. right; right; right; left. replace (fshn 2) with 32 by reflexivity. exact Ha.
      - right. intros a Ha. apply rin_ivs_app. left. cbn [rin_ivs fst snd]. left. unfold DS_SIZE. clear - Ha. lia.
      - right. intros a Ha. apply rin_ivs_app. left. cbn [rin_ivs fst snd]. left. unfold DS_SIZE. clear - Ha. lia. }
    assert (CH2 : as_chain H m2 (bv_unsigned s0) CH).
    { eapply (ah_chain_ext H HH); [exact CHN|]. intros fp' ra' a Hin Ha. pose proof (CHsp fp' ra' Hin) as K.
      pose proof (ah_chain_range H HH _ _ _ _ _ CHN Hin) as (K1 & _).
      apply MU2. rewrite unsigned_lit by (clear - Ha K K1 A1; lia). unfold LbB_Dt.WA2, AFS_FLAGS. cbn [outside fst snd].
      clear - Ha K NU K2 K6 Y3 Y4 Y6 B2 A1. lia. }
    assert (Z2 : dz ff fp spa ATD2 D0T2 D1T2 s LB m2).
    { constructor; try assumption.
      - clear. lia.
      - exact (LbB_DtK.df_0 sp ds err lo ff fp hw dptr hsel m2 Q2). }
    assert (CASES : ms = SShort \/ exists d asz, ms = SLong d asz) by (clear; destruct ms; [left; reflexivity | right; eexists; eexists; reflexivity]).
    destruct CASES as [Ems | (d & asz & Ems)].
    -
      assert (EP : LbB_Dt.PC2x ms = ADT_D3) by (unfold LbB_Dt.PC2x; rewrite Ems; reflexivity).
      assert (ER : LbB_Dt.RT2x ms = RTD3) by (unfold LbB_Dt.RT2x; rewrite Ems; reflexivity).
      rewrite EP in E2. rewrite ER in HRT2. rewrite Ems in BLK0.
      cbn [ds_blk] in BLK0. pose proof PERM as PERM0. rewrite BLK0 in PERM0. cbn [app] in PERM0.
      exact (dt_tail ff fp spa s LB m2 R2 msF2 mo2 Z2 PERM0 E2 RF2 HRT2 KR2 MP2).
    -
      assert (EP : LbB_Dt.PC2x ms = AOPDEL2) by (unfold LbB_Dt.PC2x; rewrite Ems; reflexivity).
      assert (ER : LbB_Dt.RT2x ms = RTD2L) by (unfold LbB_Dt.RT2x; rewrite Ems; reflexivity).
      assert (ED : LbB_Dt.dptr ms = d) by (unfold LbB_Dt.dptr; rewrite Ems; reflexivity).
      rewrite EP in E2. rewrite ER in HRT2. rewrite Ems in BLK0, SBA0.
      cbn [ds_blk] in BLK0. destruct BLK0 as (pid & EDB & INb). cbn [sb_addr] in SBA0. destruct SBA0 as [SAD SAO].
      pose proof (ah_blocks H HH _ _ _ (pid, d, asz) RH INb) as (Q0 & Q16 & Qn & QI & QC & QF & QAPP). cbn [blk_addr blk_size fst snd] in Q0, Q16, Qn, QI, QC, QF, QAPP.
      pose proof (di_dj _ _ _ _ _ _ _ _ _ _ _ DI0 d asz Ems) as QDJ.
      assert (QAPP' : d + asz <= 0x7fff7000 \/ 0x10007fff8000 <= d).
      { clear - QAPP. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP, AAPP_HI in QAPP. lia. }
      assert (DJB : disjoint_from (LbB_Dt.WA2 H sp ds ff fp) d asz).
      { unfold LbB_Dt.WA2, AFS_FLAGS. cbn [disjoint_from]. unfold DS_SIZE in QDJ. unfold AFS_SIZE in QF. unfold AIMG_TOP in QI.
        split; [clear - QC R2'; lia|].
        split; [clear - QF Qn; lia|].
        split; [clear - QF Qn K6 K6'; lia|].
        split; [clear - QF Qn K2 K3; lia|].
        split; [clear - QAPP' Qn Y1 Y2 Y3 Y4 Y5; lia|].
        split; [clear - QDJ Qn; lia|].
        split; [clear - QDJ Qn; lia| exact I]. }
      assert (DJS : disjoint_from (LbB_Dt.WA2 H sp ds ff fp) (sh d) (nsh asz)).
      { unfold AFS_SIZE in QF. unfold AIMG_TOP in QI.
        pose proof aceil_facts as (_ & A3 & _).
        assert (Sa : 0x800d5000 <= sh d) by (clear - QI; unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia).
        assert (Sb : sh d + nsh asz <= sh aceil) by (clear - QC Qn Q16 A3; unfold sh, nsh, ASHADOW_BASE; Z.div_mod_to_equations; lia).
        assert (Sc : sh aceil + 2048 <= spz - 16384 /\ sh aceil <= 0x10007fff8000) by (clear - R2' A1 R3'; unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia).
        assert (Se : sh ff + 32 <= sh d \/ sh d + nsh asz <= sh ff) by (clear - QF K2 K3 K4 Q16 Qn; unfold sh, nsh, ASHADOW_BASE in *; Z.div_mod_to_equations; lia).
        set (sd := sh d) in *. set (na := nsh asz) in *. set (sa := sh aceil) in *. clearbody sd na sa.
        unfold LbB_Dt.WA2, AFS_FLAGS. cbn [disjoint_from].
        split; [clear - Sb Sc; lia|].
        split; [clear - Sa Sb Sc B4; lia|].
        split; [clear - Sa Sb Sc B4 K6 K6'; lia|].
        split; [clear - Sa Sb Sc B4 K2 K3; lia|].
        split; [clear - Se; lia|].
        split; [clear - Sa Sb Sc B4 NU; lia|].
        split; [clear - Sa Sb Sc B4 NU; lia| exact I]. }
      destruct (rw_cells_of_wr_hi m d asz (lb_own_In _ _ _ OWN ltac:(rewrite EDB; left; reflexivity)) QI Qn) as [bs CB0].
      assert (CB2 : rw_cells asegs m2 d [CB (Z.to_nat asz) bs]).
      { eapply rw_cells_transport; [exact CB0 | exact MU2 | exact WM2 |]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by (clear - Qn; lia). exact DJB. }
      assert (SH2 : SHAD m2 d (shadow_of asz)).
      { destruct SAD as [_ (D0 & D8 & U)]. split; [exact D0|]. split; [exact D8|].
        eapply u8arr_transport; [exact U | exact MU2 | exact WM2 |]. rewrite shadow_of_length by (clear - Qn; lia). exact DJS. }
      pose proof Q2 as [AC2 _ ST2 _ _ _ _ _ _ _ _].
      rgq HRT2 (1%bv : reg) (ELit 0xfd148) K1. rgq HRT2 (2%bv : reg) (EVar 51) Kr2. rgq HRT2 (4%bv : reg) (EVar 48) K4r.
      rgq HRT2 (8%bv : reg) (EVar 33) K8. rgq HRT2 (10%bv : reg) (EVar 54) K10.
      rewrite ED in K10.
      rewrite (MS_full_eq R2 F _ fc m2 _ RF2) in E2.
      eapply (ah_seq H HH).
      { eapply ((ah_opdel2 H HH)
                  (PropExec.getr R2 1) (PropExec.getr R2 2) (PropExec.getr R2 3) (PropExec.getr R2 4) (PropExec.getr R2 5)
                  (PropExec.getr R2 6) (PropExec.getr R2 7) (PropExec.getr R2 8) (PropExec.getr R2 9) (PropExec.getr R2 10)
                  (PropExec.getr R2 11) (PropExec.getr R2 12) (PropExec.getr R2 13) (PropExec.getr R2 14) (PropExec.getr R2 15)
                  (PropExec.getr R2 16) (PropExec.getr R2 17) (PropExec.getr R2 18) (PropExec.getr R2 19) (PropExec.getr R2 20)
                  (PropExec.getr R2 21) (PropExec.getr R2 22) (PropExec.getr R2 23) (PropExec.getr R2 24) (PropExec.getr R2 25)
                  (PropExec.getr R2 26) (PropExec.getr R2 27) (PropExec.getr R2 28) (PropExec.getr R2 29) (PropExec.getr R2 30)
                  (PropExec.getr R2 31) F fc msF2 m2 s LB pid d asz lo B errv mo2 ((spz, bv_unsigned ra) :: CH) bs (shadow_of asz)).
        - exact E2.
        - exact RH2.
        - exact KR2.
        - exact INb.
        - rewrite Cf0. exact COST.
        - exact CB2.
        - exact SH2.
        - rewrite shadow_of_length by (clear - Qn; lia). reflexivity.
        - exact RAUX2.
        - rewrite Kr2, unsigned_lit by (clear - NU; lia). clear - NU SPB. lia.
        - rewrite Kr2, unsigned_lit by (clear - NU; lia). exact (proj1 (stk_split asegs m2 lo spa spz ST2 ltac:(clear - NU; lia))).
        - exact CEIL.
        - rewrite Kr2, unsigned_lit by (clear - NU; lia). clear - NU. unfold AFREE_STACK. lia.
        - rewrite K4r. exact ERR2.
        - exact MI2.
        - rewrite K4r. exact TP.
        - rewrite Kr2, unsigned_lit by (clear - NU; lia). clear - NU. Z.div_mod_to_equations. lia.
        - exact AC2.
        - rewrite K8. exact (chain_sp0g ff fp spa m2 G TS2 CH2).
        - rewrite K1, unsigned_lit by (clear; lia). cbn [map snd]. exact (pf_ok_site _ _ _ _ APC0_FREE [0xfd148] PF (or_introl eq_refl)).
        - exact K10. }
      intros [msF3 mo3] POST3.
      destruct POST3 as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m3 & s3x
                        & VIS3 & KR3 & MP3 & MI3 & STK3 & ERR3 & RAUX3 & AP3 & RH3 & AC3 & AL3).
      cbn [cfg_ms cfg_model] in VIS3, KR3, MP3. rewrite Kr2, unsigned_lit in STK3, AP3 by (clear - NU; lia). rewrite K4r in ERR3. rewrite Cf0 in AL3.
      rewrite K1, (ret_pc_even 0xfd148 ltac:(clear; lia) eq_refl) in VIS3.
      pose proof (ah_nodup H HH _ _ _ RH) as ND.
      assert (PERM3 : Permutation (as_lb_remove H pid LB) LBk).
      { rewrite EDB in PERM. exact (LbB_HKit.lb_remove_perm_app H HH LB [] LBk pid d asz ND PERM). }
      assert (SUB3 : forall b, In b LBk -> In b (as_lb_remove H pid LB)).
      { intros b Hb. exact (Permutation_in _ (Permutation_sym PERM3) Hb). }
      assert (Z3 : dz ff fp spa ATD2 D0T2 D1T2 s3x (as_lb_remove H pid LB) m3).
      { eapply (dz_apres ff fp spa ATD2 D0T2 D1T2 s s3x LB _ m2 m3 spa Z2 SUB3 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(right; right; split; [apply Z.le_refl | reflexivity]) AP3 RH3 RAUX3 ERR3 MI3 AC3 STK3);
          [clear - NU CEIL; lia | clear - NU; lia | clear - COST AL3; lia]. }
      lazymatch type of VIS3 with _ = MS ?RR _ _ _ _ _ _ => set (R3 := RR) in VIS3 end.
      assert (KP : forall r, In r KEPT -> PropExec.getr R3 r = PropExec.getr R2 r).
      { intros r Hr. subst R3. apply (getr_mkR_keptR R2); [exact (eq_sym K1) | exact Hr]. }
      assert (HRT3 : rtbl (WW ff fp spa) R3 RTD3).
      { assert (HRT2' : rtbl (WW ff fp spa) R2 RTD3).
        { unfold RTD2L in HRT2. unfold rtbl in HRT2 |- *. apply Forall_cons_iff in HRT2 as [_ HRT2]. apply Forall_cons_iff in HRT2 as [_ HRT2]. exact HRT2. }
        apply (rtbl_keep _ R2 R3 _ KEPT HRT2'); [vm_compute; reflexivity | exact KP]. }
      apply (dt_tail ff fp spa s3x (as_lb_remove H pid LB) m3 R3 msF3 mo3 Z3 PERM3 VIS3); [subst R3; apply rfull_mkR | exact HRT3 | exact KR3 |].
      eapply (ah_mpres_trans H HH); [exact MP2 | exact MP3].
  Qed.

End DTS.

Theorem dtor_okA {HCEIL : HeapCeil} : forall H, asan_rt_hyps_bp H -> ds_dtor_stmtA H LINV_P5 ds_repA0.
Proof.
  intros H HHbp ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc msF m mo s LB LBk LF CH lo B shi errv ds err len DB PRE PF Ha0 REP PERM DSOB DSIN.
  apply ds_repA0_w in REP as (ms & pp & hm & fl & fill & REPW).
  exact (dt_main H HHbp ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc msF m mo s LB LBk LF CH lo B shi errv ds err len DB ms pp hm fl fill PRE PF Ha0 REPW PERM DSOB DSIN).
Qed.
