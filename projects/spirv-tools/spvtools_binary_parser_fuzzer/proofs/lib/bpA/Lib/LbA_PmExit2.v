(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HTac HArr HSysStep HExec CellsX TacX HMem HMState HLFrame.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HPrelim.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsCXXHeap CXXRep AsStack0 RtA_Iface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_Kit LbA_Bridge LbA_Call LbA_Conv LbA_SR LbA_FKit LbA_MILB LbA_PrsStmt LbA_Own LbA_PmBase LbA_FSlots LbA_PmOwn LbA_PmCut LbA_PmTac LbA_PmHdr LbA_PmCall LbA_PmXp LbA_PmExit LbA_PmInit LbA_PmFin.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition TBL_EXIT : list (Z * expr) := [(968, EVar WV_FF); (1040, EVar WV_FF)].

Definition RT_EDFB0 : list (reg * expr) := [(2%bv, EVar WV_S1); (8%bv, EVar WV_SP0); (9%bv, EVar WV_S1); (20%bv, SH_FF)].
Definition RT_EDFC4 : list (reg * expr) :=
  [(2%bv, EVar WV_S1); (8%bv, EVar WV_SP0); (9%bv, EVar WV_S1); (18%bv, EVar WV_FF); (20%bv, SH_FF); (27%bv, EVar WV_FF)].

Definition RT_ED894 : list (reg * expr) := RT_EDFC4.

Lemma pm_ret_ok : forall (Q : machine_state -> Prop) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
        x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (ret_pc x1) fc None m (seg_rom asegs)) ->
  evt asegs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0xeda84) fc None m (seg_rom asegs)).
Proof.
  intros Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m HQ.
  step. apply evt_done. exact HQ.
Qed.

Section Restrict.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.

  Lemma pmxa_restrict : forall w s LB LBs m mo c ins tbl ftbl TB spal tbl' ftbl',
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    incl tbl' tbl -> incl ftbl' ftbl -> PMXAT H LINV w s LB LBs m mo c ins tbl' ftbl' TB spal.
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal tbl' ftbl' OK X It If.
    eapply (pmxa_munch H HH LINV LINV_frame w s LB LBs m mo c ins tbl ftbl TB spal m [] tbl' ftbl' OK X (munch_refl [] m)
              (wmono_refl asegs m) (fun x Hx => Hx) (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) (xa_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)
              (Forall_nil _) (Forall_nil _) I I It); [| exact If |].
    - apply Forall_forall. intros ke _. exact I.
    - apply Forall_forall. intros ke _. exact I.
  Qed.
End Restrict.

Section Epi.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.
  Lemma HHe : asan_rt_hyps H. Proof. exact (proj1 HHbp). Qed.

  Lemma pm_epi_a : forall (w : pmwA H) s LB LBs m mo c spal msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c [OB_BINARY] TBL_EXIT [] [] spal ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xee140) fc None m (seg_rom asegs) -> rfull R ->
    regs_tbl w R RT_EDFB0 ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) ->
       as_VIS H s msF1 = MS R1 F (Z_to_bv 64 0xee154) fc None m1 (seg_rom asegs) -> rfull R1 ->
       PMXAT H LINV w s LB LBs m1 mo1 c [] TBL_EXIT [] [] spal -> regs_tbl w R1 RT_EDFC4 ->
       (forall r, In r [1%bv; 3%bv; 4%bv; 25%bv] -> PropExec.getr R1 r = PropExec.getr R r) ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c spal msF R F fc Q OK X KR VIS RF HT K.
    pm_go HHe LINV_frame OK X KR VIS RF HT (@nil word) (@nil kentry) 40%nat [0xee154] (@nil bool) 41%N
          (@nil nat) (@nil Z) (@nil Z) TBL_EXIT (@nil (Z * expr)) RT_EDFC4.
    - split_scs.
    - intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HT1 HR1 _. eapply K; [exact KR1 | exact VIS1 | exact RF1 | exact X1 | exact HT1 |].
      intros r Hr. rewrite (HR1 r).
      repeat (destruct Hr as [<-|Hr]; [vm_compute; reflexivity |]); destruct Hr.
  Qed.

  Lemma pm_epi_call : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (p : Z) (c0 : parserC) (ff fp : Z)
      (LB0 : list block) (LF : list fframe) (CH : list (Z * Z)) (m0 : mem) (mo0 : Model) (st0 : as_St H) (lo B shi : Z)
      s LB LBs m mo c ins tbl ftbl spal msF2 mo2 R2 F fc M2,
    let w := pm_world H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p c0 ff fp LB0 LF CH m0 mo0 st0 lo B shi in
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl [] spal -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    munch [(wa_ff w, wa_ff w + 8)] m M2 -> wmono asegs m M2 -> mem_inv asegs M2 -> as_MPRES H mo mo2 ->
    as_AKREL H s (mkCfg msF2 mo2) -> as_VIS H s msF2 = MS R2 F (Z_to_bv 64 0x9ea14) fc None M2 (seg_rom asegs) -> rfull R2 ->
    frm_zero fc ->
    PropExec.getr R2 1%bv = Z_to_bv 64 0xeda44 -> PropExec.getr R2 2%bv = Z_to_bv 64 (wa_s1 w) ->
    PropExec.getr R2 3%bv = gp -> PropExec.getr R2 4%bv = tp -> PropExec.getr R2 8%bv = Z_to_bv 64 (wa_sp0 w) ->
    PropExec.getr R2 10%bv = Z_to_bv 64 (wa_ff w) -> PropExec.getr R2 11%bv = Z_to_bv 64 15616 ->
    as_SR H (pm_post H LINV ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st0 LB0 LF p c0 lo B shi m0 mo0) (mkCfg msF2 mo2).
  Proof.
    intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p c0 ff fp LB0 LF CH m0 mo0 st0 lo B shi s LB LBs m mo c ins tbl ftbl spal
           msF2 mo2 R2 F fc M2 w OK X Htr Hbsz MU3 WM3 MI3 MP2 KR2 VIS2 RF2 FZ Y1 Y2 Y3 Y4 Y8 Y10 Y11.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    rewrite (rfull_eq R2 RF2) in VIS2.

    pose proof (pmw_frame_facts H w OK) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10). change (fsz PM_FCLASS) with 16384 in *.
    pose proof (wk_stack H w OK) as (SK1 & SK2 & SK3 & SK4 & SK5 & SK6).
    pose proof (wk_s1 H w OK) as (WS1 & WS2).
    assert (STK2 : stk asegs M2 (wa_lo w) (wa_s1 w)).
    { destruct (stk_split asegs m (wa_lo w) (wa_s1 w) (wa_sp0 w) (xa_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) ltac:(lia)) as [ST1 _].
      eapply (stk_transport_disjoint asegs _ m M2 _ _ ST1 MU3 WM3). cbn [disjoint_from]. split; [right; lia | exact I]. }
    assert (RFS2 : as_RFS H (PMLF H w) M2).
    { eapply (ah_RFS_frame H HHe); [exact (xa_rfs _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | exact MU3 | exact WM3 |].
      apply Forall_cons; [| apply Forall_nil]. unfold afs_write_ok. right. exists (PM_FCLASS, wa_ff w, wa_fp w).
      split; [left; reflexivity|]. cbn [ff_addr ff_class fst snd]. change (fsz PM_FCLASS) with 16384. lia. }
    assert (FFL2 : rw_cells asegs M2 (wa_ff w + fsz 8 - 8) [C8 (Z_to_bv 64 (wa_fp w))]).
    { eapply rw_cells_transport; [exact (xa_fflag _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | exact MU3 | exact WM3 |].
      cbn [disjoint_from cells_size csize Nat.add]. change (fsz 8) with 16384. split; [right; lia | exact I]. }
    assert (ACM2 : ACONST M2).
    { eapply ACONST_frame; [exact (xa_aconst _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | exact MU3 | exact WM3 |].
      apply Forall_cons; [| apply Forall_nil]. apply aconst_ok_of.
      destruct F8 as [(L1 & L2)|(L1 & L2)].
      - right. unfold AIMG_TOP, AFS_HDR, AFS_SIZE, ALOWSH_LO in *. lia.
      - left. replace (sh AIMG_TOP) with 0x800d4c00 by reflexivity. unfold AHI_LO, AFS_HDR in *. lia. }
    pose proof (rt_bp_ext H HHbp) as EXT. destruct EXT as (_ & _ & _ & _ & _ & _ & _ & _ & SF8 & _).
    eapply (ahh_evt_then H HHe _ _ s msF2 _ mo2 KR2 VIS2).
    { eapply (SF8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc M2 (PMLF H w) (wa_ff w) (wa_fp w) (wa_lo w) 15616);
        [exact RFS2 | left; reflexivity | exact Y10 | exact FFL2 | exact Y11 | change (fsz 8) with 16384; lia | reflexivity
        | rewrite Y2, u64_of_Z by (unfold AAPP_HI in *; lia); exact STK2 | exact SK1 | rewrite Y2, u64_of_Z by (unfold AAPP_HI in *; lia); unfold AFS_STACK, APM_STACK in *; lia
        | exact MI3 | exact ACM2]. }
    intros msF3 mo3 KR3 MP3 POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & M3 & VIS3 & MU4 & WM4 & MI4 & STK4 & RFS4 & SH4 & ACM4).
    rewrite Y1, (ret_pc_even 0xeda44 ltac:(lia) eq_refl) in VIS3. rewrite Y2, u64_of_Z in MU4, STK4 by (unfold AAPP_HI in *; lia).
    change (15616 / 8) with 1952 in MU4.

    assert (SAV3 : rw_cells asegs M3 (wa_sp0 w - 104) (map C8 (wa_saved w))).
    { pose proof (xa_saved _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as SV.
      assert (Q5' : sh (wa_ff w) + 2048 <= aceil) by lia.
      eapply rw_cells_transport; [eapply rw_cells_transport; [exact SV | exact MU3 | exact WM3 |] | exact MU4 | exact WM4 |].
      - rewrite cells_size_mapC8, (wk_saved H w OK). cbn [disjoint_from]. split; [right; lia | exact I].
      - rewrite cells_size_mapC8, (wk_saved H w OK). cbn [disjoint_from]. unfold AFS_STACK.
        split; [right; lia|]. split; [right; unfold AFS_HDR, AFS_SIZE in *; lia|]. split; [right; lia | exact I]. }

    lazymatch type of VIS3 with _ = MS ?RR _ _ _ _ _ _ => set (R5 := RR) in VIS3 end.
    pose (E5 := Eseed R5 (wenv_vals w ++ wa_saved w)).
    assert (HR5 : regs_ok E5 (srs sr_id [(8%bv, EVar WV_SP0)]) R5).
    { apply regs_ok_srs; [apply regs_ok_seed|]. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
      split; [intros Hx; discriminate Hx|]. subst R5. transitivity (PropExec.getr R2 8%bv); [reflexivity | rewrite Y8; reflexivity]. }
    assert (U34 : bv_unsigned (edenot E5 (EVar WV_SP0)) = wa_sp0 w) by (change (edenot E5 (EVar WV_SP0)) with (Z_to_bv 64 (wa_sp0 w)); apply u64_of_Z; unfold AAPP_HI in *; lia).
    assert (HK5 : know_ok asegs E5 M3 [KRange (EVar WV_SP0) 0x7fff7f800000 (2 ^ 47);
                                  KWord (SA (EVar WV_SP0) (-104)) 8 (EVar 41);
                                  KWord (SA (EVar WV_SP0) (-96)) 8 (EVar 42);
                                  KWord (SA (EVar WV_SP0) (-88)) 8 (EVar 43);
                                  KWord (SA (EVar WV_SP0) (-80)) 8 (EVar 44);
                                  KWord (SA (EVar WV_SP0) (-72)) 8 (EVar 45);
                                  KWord (SA (EVar WV_SP0) (-64)) 8 (EVar 46);
                                  KWord (SA (EVar WV_SP0) (-56)) 8 (EVar 47);
                                  KWord (SA (EVar WV_SP0) (-48)) 8 (EVar 48);
                                  KWord (SA (EVar WV_SP0) (-40)) 8 (EVar 49);
                                  KWord (SA (EVar WV_SP0) (-32)) 8 (EVar 50);
                                  KWord (SA (EVar WV_SP0) (-24)) 8 (EVar 51);
                                  KWord (SA (EVar WV_SP0) (-16)) 8 (EVar 52);
                                  KWord (SA (EVar WV_SP0) (-8)) 8 (EVar 53)]).
    { apply Forall_cons; [cbn [kentry_ok]; rewrite U34; unfold AAPP_HI in *; lia|].
      repeat (apply Forall_cons;
        [ lazymatch goal with |- kentry_ok _ _ _ (KWord (SA _ ?off) _ _) =>
            let k := eval compute in (Z.to_nat (off + 104)) in
            eapply (kword_of_rw_cells asegs E5 M3 (wa_sp0 w - 104) (map C8 (wa_saved w)) k (C8 _) _ _ 8%nat SAV3);
            [ reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; rewrite U34; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
            | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold AAPP_HI in *; lia | reflexivity ]
          end |]).
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R5 0xeda44 M3 (seg_rom asegs) HR5 HK5 30%nat [0xeda84] (SCR [] [] []) 54%N.
    { split_scs. }

    rename R' into R6. rename HR' into HR6. rename Hms into Hms6. rename Hlf into Hlf6.
    lazymatch type of Hms6 with CatSim.msteps _ (@PropExec.mkst _ _ _ ?m0 _) (@PropExec.mkst _ _ _ ?mm _) => change mm with m0 in Hms6 end.
    assert (HF5 : rfull R5) by (unfold R5; apply rfull_mkR).
    assert (HF6 : rfull R6) by exact (msteps_full asegs _ _ Hms6 HF5).
    assert (K1 : PropExec.getr R6 1%bv = ra) by (rewrite (HR6 1%bv); reflexivity).
    assert (K2 : PropExec.getr R6 2%bv = sp).
    { rewrite (HR6 2%bv). transitivity (Z_to_bv 64 (bv_unsigned sp)); [reflexivity | apply Z_to_bv_bv_unsigned]. }
    assert (K3 : PropExec.getr R6 3%bv = gp).
    { rewrite (HR6 3%bv). transitivity (PropExec.getr R2 3%bv); [reflexivity | exact Y3]. }
    assert (K4 : PropExec.getr R6 4%bv = tp).
    { rewrite (HR6 4%bv). transitivity (PropExec.getr R2 4%bv); [reflexivity | exact Y4]. }
    assert (K8 : PropExec.getr R6 8%bv = s0) by (rewrite (HR6 8%bv); reflexivity).
    assert (K9 : PropExec.getr R6 9%bv = s1) by (rewrite (HR6 9%bv); reflexivity).
    assert (K18 : PropExec.getr R6 18%bv = s2) by (rewrite (HR6 18%bv); reflexivity).
    assert (K19 : PropExec.getr R6 19%bv = s3) by (rewrite (HR6 19%bv); reflexivity).
    assert (K20 : PropExec.getr R6 20%bv = s4) by (rewrite (HR6 20%bv); reflexivity).
    assert (K21 : PropExec.getr R6 21%bv = s5) by (rewrite (HR6 21%bv); reflexivity).
    assert (K22 : PropExec.getr R6 22%bv = s6) by (rewrite (HR6 22%bv); reflexivity).
    assert (K23 : PropExec.getr R6 23%bv = s7) by (rewrite (HR6 23%bv); reflexivity).
    assert (K24 : PropExec.getr R6 24%bv = s8) by (rewrite (HR6 24%bv); reflexivity).
    assert (K25 : PropExec.getr R6 25%bv = s9) by (rewrite (HR6 25%bv); reflexivity).
    assert (K26 : PropExec.getr R6 26%bv = s10) by (rewrite (HR6 26%bv); reflexivity).
    assert (K27 : PropExec.getr R6 27%bv = s11) by (rewrite (HR6 27%bv); reflexivity).

    assert (MUa : munch ([(wa_ff w, wa_ff w + 8)] ++ [(wa_s1 w - AFS_STACK, wa_s1 w); (wa_fp w, wa_fp w + 1); (sh (wa_ff w), sh (wa_ff w) + 1952)]) m M3)
      by exact (LbA_Conv.munch_app _ _ _ _ _ MU3 MU4).
    assert (WMa : wmono asegs m M3) by exact (wmono_trans asegs _ _ _ WM3 WM4).
    assert (FWa : Forall (fin_ivl H w) ([(wa_ff w, wa_ff w + 8)] ++ [(wa_s1 w - AFS_STACK, wa_s1 w); (wa_fp w, wa_fp w + 1); (sh (wa_ff w), sh (wa_ff w) + 1952)])).
    { unfold AFS_STACK, APM_STACK in *. cbn [app].
      repeat apply Forall_cons; try apply Forall_nil; unfold fin_ivl; cbn [fst snd]; change (fsz PM_FCLASS) with 16384.
      - right; left. lia.
      - left. lia.
      - right; right; right. lia.
      - right; right; left. unfold PM_NSH. lia. }
    destruct (pm_fin H HHbp LINV LINV_frame w s LB LBs m mo c ins tbl ftbl spal M3 _ OK X Htr MUa WMa FWa)
      as (errv' & XSf & Ferr & Faux & Frh & Fso & Flo & Fpr & Fps & Fm1 & Fm2 & Fm3 & Fvs & Fxs & Fxp & Fs0 & Fli & Fal).
    assert (STKf : stk asegs M3 (wa_lo w) (wa_sp0 w)).
    { eapply stk_wmono_fin; [exact (xa_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | exact WMa | lia]. }
    assert (RFSf : as_RFS H (wa_LF0 w) M3).
    { unfold PMLF in RFS4. cbn [lf_remove ff_addr fst snd] in RFS4. rewrite Z.eqb_refl in RFS4. exact RFS4. }
    pose proof (xa_mpres _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as MP0.
    eapply (sr_evt H HHe) with
      (P := fun ms => ms = MS (mkR ra sp gp tp (PropExec.getr R6 5) (PropExec.getr R6 6) (PropExec.getr R6 7) s0 s1
                                   (Z_to_bv 64 (bv_unsigned (PropExec.getr R6 10)))
                                   (PropExec.getr R6 11) (PropExec.getr R6 12) (PropExec.getr R6 13) (PropExec.getr R6 14)
                                   (PropExec.getr R6 15) (PropExec.getr R6 16) (PropExec.getr R6 17)
                                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                   (PropExec.getr R6 28) (PropExec.getr R6 29) (PropExec.getr R6 30) (PropExec.getr R6 31))
                              F (ret_pc ra) fc None M3 (seg_rom asegs));
      [exact KR3 | exact VIS3 | |].
    { eapply evt_of_msteps; [exact Hms6|]. rewrite (rfull_eq R6 HF6). apply pm_ret_ok.
      rewrite K1, K2, K3, K4, K8, K9, K18, K19, K20, K21, K22, K23, K24, K25, K26, K27, Z_to_bv_bv_unsigned. reflexivity. }
    intros msF4 mo4 KR4 MP4 HP. cbv beta in HP.
    exists (PropExec.getr R6 5), (PropExec.getr R6 6), (PropExec.getr R6 7), (bv_unsigned (PropExec.getr R6 10)),
      (PropExec.getr R6 11), (PropExec.getr R6 12), (PropExec.getr R6 13), (PropExec.getr R6 14), (PropExec.getr R6 15),
      (PropExec.getr R6 16), (PropExec.getr R6 17), (PropExec.getr R6 28), (PropExec.getr R6 29), (PropExec.getr R6 30),
      (PropExec.getr R6 31), M3, errv', s, LB, LBs, (prc_ofA w c), XSf, F, fc.
    cbn [cfg_ms cfg_model].
    split; [exact HP|]. split; [exact FZ|]. split; [exact KR4|].
    split; [eapply (ah_mpres_trans H HHe); [exact MP0 | eapply (ah_mpres_trans H HHe); [exact MP2 | eapply (ah_mpres_trans H HHe); [exact MP3 | exact MP4]]]|].
    split; [exact MI4|]. split; [exact STKf|]. split; [exact Ferr|]. split; [exact Faux|].
    split; [exact Frh|]. split; [exact Fso|]. split; [exact Flo|]. split; [exact Fpr|]. split; [exact Fps|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [exact Fm1|]. split; [exact Fm2|]. split; [exact Fm3|]. split; [exact Fvs|].
    split; [intros q k Hq; apply (Hbsz q k); rewrite (state_blocks_of w c), Htr, app_nil_r; exact Hq|].
    split; [exact Fxs|]. split; [exact Fxp|].
    split; [exact RFSf|]. split; [exact ACM4|]. split; [exact Fs0|]. split; [exact Fli|]. exact Fal.
  Qed.

  Lemma pm_epi_b : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (p : Z) (c0 : parserC) (ff fp : Z)
      (LB0 : list block) (LF : list fframe) (CH : list (Z * Z)) (m0 : mem) (mo0 : Model) (st0 : as_St H) (lo B shi : Z)
      s LB LBs m mo c spal msF R F fc,
    let w := pm_world H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p c0 ff fp LB0 LF CH m0 mo0 st0 lo B shi in
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c [] TBL_EXIT [] [] spal -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xee154) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_EDFC4 -> PropExec.getr R 3%bv = gp -> PropExec.getr R 4%bv = tp ->
    as_SR H (pm_post H LINV ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st0 LB0 LF p c0 lo B shi m0 mo0) (mkCfg msF mo).
  Proof.
    intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p c0 ff fp LB0 LF CH m0 mo0 st0 lo B shi s LB LBs m mo c spal msF R F fc
           w OK X Htr Hbsz KR VIS RF FZ HT G3 G4.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).

    pose (E := Eseed R (wenv_vals w ++ [])).
    pose proof (regs_ok_of_tbl w R RT_EDFC4 [] 41%N HT ltac:(vm_compute; reflexivity)) as HR.
    assert (HK : know_ok asegs E m [KRange (EVar WV_FF) (AIMG_TOP + AFS_HDR) (2 ^ 47); KWr (SA (EVar WV_FF) 0) (ELit 8)]).
    { pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as FW. change (fsz PM_FCLASS) with 16384 in FW.
      assert (EF : edenot E (EVar WV_FF) = Z_to_bv 64 (wa_ff w)) by reflexivity.
      assert (UF : bv_unsigned (edenot E (EVar WV_FF)) = wa_ff w) by (rewrite EF; apply u64_of_Z; lia).
      apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
      - cbn [kentry_ok]. rewrite UF. unfold AIMG_TOP, AFS_HDR in *. lia.
      - eapply (kwr_of_wr_at asegs E m (wa_ff w) 16384); [exact FW | | |].
        + unfold estart. cbn [a_base a_off]. rewrite UF. lia.
        + unfold estart, elenZ. cbn [a_base a_off]. rewrite UF. change (edenot E (ELit 8)) with (Z_to_bv 64 8). rewrite u64_of_Z by lia. lia.
        + unfold elenZ. change (edenot E (ELit 8)) with (Z_to_bv 64 8). rewrite u64_of_Z by lia. lia. }
    xrun_at (PropExec.mkFP F fc) asegs R 0xee154 m (seg_rom asegs) HR HK 20%nat [0x9ea14] (SCR [] [] []) 41%N.
    { split_scs. }
    lazymatch type of Hlf with log_flat _ ?lg => set (LOG3 := lg) in * end.
    lazymatch type of Hms with CatSim.msteps _ _ (PropExec.mkst _ _ ?mm _) => change mm with (mem_denot E m LOG3) in Hms end.
    set (M2 := mem_denot E m LOG3) in Hms.
    assert (UF : bv_unsigned (edenot E (EVar WV_FF)) = wa_ff w) by (change (edenot E (EVar WV_FF)) with (Z_to_bv 64 (wa_ff w)); apply u64_of_Z; lia).
    assert (MU3 : munch [(wa_ff w, wa_ff w + 8)] m M2).
    { pose proof (munch_sym E m LOG3 [(EVar WV_FF, 0, 8)] Hlf ltac:(vm_compute; reflexivity)) as MS3.
      cbn [num_wins map] in MS3. rewrite UF in MS3. replace (wa_ff w + 0) with (wa_ff w) in MS3 by lia. exact MS3. }
    assert (WM3 : wmono asegs m M2) by (subst M2; apply LbA_Conv.wmono_mem_denot).
    assert (MI3 : mem_inv asegs M2) by exact (msteps_mem_inv asegs _ _ Hms (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)).
    assert (Y1 : PropExec.getr R' 1%bv = Z_to_bv 64 0xeda44) by (rewrite (HR' 1%bv); reflexivity).
    assert (Y2 : PropExec.getr R' 2%bv = Z_to_bv 64 (wa_s1 w)) by (rewrite (HR' 2%bv); reflexivity).
    assert (Y8 : PropExec.getr R' 8%bv = Z_to_bv 64 (wa_sp0 w)) by (rewrite (HR' 8%bv); reflexivity).
    assert (Y10 : PropExec.getr R' 10%bv = Z_to_bv 64 (wa_ff w)) by (rewrite (HR' 10%bv); reflexivity).
    assert (Y11 : PropExec.getr R' 11%bv = Z_to_bv 64 15616) by (rewrite (HR' 11%bv); reflexivity).
    assert (Y3 : PropExec.getr R' 3%bv = gp) by (rewrite (HR' 3%bv); exact G3).
    assert (Y4 : PropExec.getr R' 4%bv = tp) by (rewrite (HR' 4%bv); exact G4).
    assert (RF' : rfull R') by exact (msteps_full asegs _ _ Hms RF).
    eapply (sr_blk H HHe _ s msF mo R F (Z_to_bv 64 0xee154) fc m (seg_rom asegs) R' (Z_to_bv 64 0x9ea14) M2 KR VIS RF Hms).
    intros msF2 mo2 KR2 MP2 VIS2. rewrite <- (rfull_eq R' RF') in VIS2.
    exact (pm_epi_call ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p c0 ff fp LB0 LF CH m0 mo0 st0 lo B shi s LB LBs m mo c
             [] TBL_EXIT [] spal msF2 mo2 R' F fc M2 OK X Htr Hbsz MU3 WM3 MI3 MP2 KR2 VIS2 RF' FZ Y1 Y2 Y3 Y4 Y8 Y10 Y11).
  Qed.

  Lemma pm_epi_c : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (p : Z) (c0 : parserC) (ff fp : Z)
      (LB0 : list block) (LF : list fframe) (CH : list (Z * Z)) (m0 : mem) (mo0 : Model) (st0 : as_St H) (lo B shi : Z)
      s LB LBs m mo c tbl spal msF R F fc,
    let w := pm_world H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p c0 ff fp LB0 LF CH m0 mo0 st0 lo B shi in
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c [] tbl [] [] spal -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xeda24) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_ED894 -> PropExec.getr R 3%bv = gp -> PropExec.getr R 4%bv = tp ->
    as_SR H (pm_post H LINV ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st0 LB0 LF p c0 lo B shi m0 mo0) (mkCfg msF mo).
  Proof.
    intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p c0 ff fp LB0 LF CH m0 mo0 st0 lo B shi s LB LBs m mo c tbl spal msF R F fc
           w OK X Htr Hbsz KR VIS RF FZ HT G3 G4.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).

    pose (E := Eseed R (wenv_vals w ++ [])).
    pose proof (regs_ok_of_tbl w R RT_ED894 [] 41%N HT ltac:(vm_compute; reflexivity)) as HR.
    assert (HK : know_ok asegs E m [KRange (EVar WV_FF) (AIMG_TOP + AFS_HDR) (2 ^ 47); KWr (SA (EVar WV_FF) 0) (ELit 8)]).
    { pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as FW. change (fsz PM_FCLASS) with 16384 in FW.
      assert (EF : edenot E (EVar WV_FF) = Z_to_bv 64 (wa_ff w)) by reflexivity.
      assert (UF : bv_unsigned (edenot E (EVar WV_FF)) = wa_ff w) by (rewrite EF; apply u64_of_Z; lia).
      apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
      - cbn [kentry_ok]. rewrite UF. unfold AIMG_TOP, AFS_HDR in *. lia.
      - eapply (kwr_of_wr_at asegs E m (wa_ff w) 16384); [exact FW | | |].
        + unfold estart. cbn [a_base a_off]. rewrite UF. lia.
        + unfold estart, elenZ. cbn [a_base a_off]. rewrite UF. change (edenot E (ELit 8)) with (Z_to_bv 64 8). rewrite u64_of_Z by lia. lia.
        + unfold elenZ. change (edenot E (ELit 8)) with (Z_to_bv 64 8). rewrite u64_of_Z by lia. lia. }
    xrun_at (PropExec.mkFP F fc) asegs R 0xeda24 m (seg_rom asegs) HR HK 20%nat [0x9ea14] (SCR [] [] []) 41%N.
    { split_scs. }
    lazymatch type of Hlf with log_flat _ ?lg => set (LOG3 := lg) in * end.
    lazymatch type of Hms with CatSim.msteps _ _ (PropExec.mkst _ _ ?mm _) => change mm with (mem_denot E m LOG3) in Hms end.
    set (M2 := mem_denot E m LOG3) in Hms.
    assert (UF : bv_unsigned (edenot E (EVar WV_FF)) = wa_ff w) by (change (edenot E (EVar WV_FF)) with (Z_to_bv 64 (wa_ff w)); apply u64_of_Z; lia).
    assert (MU3 : munch [(wa_ff w, wa_ff w + 8)] m M2).
    { pose proof (munch_sym E m LOG3 [(EVar WV_FF, 0, 8)] Hlf ltac:(vm_compute; reflexivity)) as MS3.
      cbn [num_wins map] in MS3. rewrite UF in MS3. replace (wa_ff w + 0) with (wa_ff w) in MS3 by lia. exact MS3. }
    assert (WM3 : wmono asegs m M2) by (subst M2; apply LbA_Conv.wmono_mem_denot).
    assert (MI3 : mem_inv asegs M2) by exact (msteps_mem_inv asegs _ _ Hms (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)).
    assert (Y1 : PropExec.getr R' 1%bv = Z_to_bv 64 0xeda44) by (rewrite (HR' 1%bv); reflexivity).
    assert (Y2 : PropExec.getr R' 2%bv = Z_to_bv 64 (wa_s1 w)) by (rewrite (HR' 2%bv); reflexivity).
    assert (Y8 : PropExec.getr R' 8%bv = Z_to_bv 64 (wa_sp0 w)) by (rewrite (HR' 8%bv); reflexivity).
    assert (Y10 : PropExec.getr R' 10%bv = Z_to_bv 64 (wa_ff w)) by (rewrite (HR' 10%bv); reflexivity).
    assert (Y11 : PropExec.getr R' 11%bv = Z_to_bv 64 15616) by (rewrite (HR' 11%bv); reflexivity).
    assert (Y3 : PropExec.getr R' 3%bv = gp) by (rewrite (HR' 3%bv); exact G3).
    assert (Y4 : PropExec.getr R' 4%bv = tp) by (rewrite (HR' 4%bv); exact G4).
    assert (RF' : rfull R') by exact (msteps_full asegs _ _ Hms RF).
    eapply (sr_blk H HHe _ s msF mo R F (Z_to_bv 64 0xeda24) fc m (seg_rom asegs) R' (Z_to_bv 64 0x9ea14) M2 KR VIS RF Hms).
    intros msF2 mo2 KR2 MP2 VIS2. rewrite <- (rfull_eq R' RF') in VIS2.
    exact (pm_epi_call ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p c0 ff fp LB0 LF CH m0 mo0 st0 lo B shi s LB LBs m mo c
             [] tbl [] spal msF2 mo2 R' F fc M2 OK X Htr Hbsz MU3 WM3 MI3 MP2 KR2 VIS2 RF' FZ Y1 Y2 Y3 Y4 Y8 Y10 Y11).
  Qed.

  Lemma pm_epi_d : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (p : Z) (c0 : parserC) (ff fp : Z)
      (LB0 : list block) (LF : list fframe) (CH : list (Z * Z)) (m0 : mem) (mo0 : Model) (st0 : as_St H) (lo B shi : Z)
      s LB LBs m mo c tbl spal msF R F fc,
    let w := pm_world H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p c0 ff fp LB0 LF CH m0 mo0 st0 lo B shi in
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c [] tbl [] [] spal -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xed758) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_ED894 -> PropExec.getr R 3%bv = gp -> PropExec.getr R 4%bv = tp ->
    as_SR H (pm_post H LINV ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st0 LB0 LF p c0 lo B shi m0 mo0) (mkCfg msF mo).
  Proof.
    intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p c0 ff fp LB0 LF CH m0 mo0 st0 lo B shi s LB LBs m mo c tbl spal msF R F fc
           w OK X Htr Hbsz KR VIS RF FZ HT G3 G4.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).

    pose (E := Eseed R (wenv_vals w ++ [])).
    pose proof (regs_ok_of_tbl w R RT_ED894 [] 41%N HT ltac:(vm_compute; reflexivity)) as HR.
    assert (HK : know_ok asegs E m [KRange (EVar WV_FF) (AIMG_TOP + AFS_HDR) (2 ^ 47); KWr (SA (EVar WV_FF) 0) (ELit 8)]).
    { pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as FW. change (fsz PM_FCLASS) with 16384 in FW.
      assert (EF : edenot E (EVar WV_FF) = Z_to_bv 64 (wa_ff w)) by reflexivity.
      assert (UF : bv_unsigned (edenot E (EVar WV_FF)) = wa_ff w) by (rewrite EF; apply u64_of_Z; lia).
      apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
      - cbn [kentry_ok]. rewrite UF. unfold AIMG_TOP, AFS_HDR in *. lia.
      - eapply (kwr_of_wr_at asegs E m (wa_ff w) 16384); [exact FW | | |].
        + unfold estart. cbn [a_base a_off]. rewrite UF. lia.
        + unfold estart, elenZ. cbn [a_base a_off]. rewrite UF. change (edenot E (ELit 8)) with (Z_to_bv 64 8). rewrite u64_of_Z by lia. lia.
        + unfold elenZ. change (edenot E (ELit 8)) with (Z_to_bv 64 8). rewrite u64_of_Z by lia. lia. }
    xrun_at (PropExec.mkFP F fc) asegs R 0xed758 m (seg_rom asegs) HR HK 20%nat [0x9ea14] (SCR [] [] []) 41%N.
    { split_scs. }
    lazymatch type of Hlf with log_flat _ ?lg => set (LOG3 := lg) in * end.
    lazymatch type of Hms with CatSim.msteps _ _ (PropExec.mkst _ _ ?mm _) => change mm with (mem_denot E m LOG3) in Hms end.
    set (M2 := mem_denot E m LOG3) in Hms.
    assert (UF : bv_unsigned (edenot E (EVar WV_FF)) = wa_ff w) by (change (edenot E (EVar WV_FF)) with (Z_to_bv 64 (wa_ff w)); apply u64_of_Z; lia).
    assert (MU3 : munch [(wa_ff w, wa_ff w + 8)] m M2).
    { pose proof (munch_sym E m LOG3 [(EVar WV_FF, 0, 8)] Hlf ltac:(vm_compute; reflexivity)) as MS3.
      cbn [num_wins map] in MS3. rewrite UF in MS3. replace (wa_ff w + 0) with (wa_ff w) in MS3 by lia. exact MS3. }
    assert (WM3 : wmono asegs m M2) by (subst M2; apply LbA_Conv.wmono_mem_denot).
    assert (MI3 : mem_inv asegs M2) by exact (msteps_mem_inv asegs _ _ Hms (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)).
    assert (Y1 : PropExec.getr R' 1%bv = Z_to_bv 64 0xeda44) by (rewrite (HR' 1%bv); reflexivity).
    assert (Y2 : PropExec.getr R' 2%bv = Z_to_bv 64 (wa_s1 w)) by (rewrite (HR' 2%bv); reflexivity).
    assert (Y8 : PropExec.getr R' 8%bv = Z_to_bv 64 (wa_sp0 w)) by (rewrite (HR' 8%bv); reflexivity).
    assert (Y10 : PropExec.getr R' 10%bv = Z_to_bv 64 (wa_ff w)) by (rewrite (HR' 10%bv); reflexivity).
    assert (Y11 : PropExec.getr R' 11%bv = Z_to_bv 64 15616) by (rewrite (HR' 11%bv); reflexivity).
    assert (Y3 : PropExec.getr R' 3%bv = gp) by (rewrite (HR' 3%bv); exact G3).
    assert (Y4 : PropExec.getr R' 4%bv = tp) by (rewrite (HR' 4%bv); exact G4).
    assert (RF' : rfull R') by exact (msteps_full asegs _ _ Hms RF).
    eapply (sr_blk H HHe _ s msF mo R F (Z_to_bv 64 0xed758) fc m (seg_rom asegs) R' (Z_to_bv 64 0x9ea14) M2 KR VIS RF Hms).
    intros msF2 mo2 KR2 MP2 VIS2. rewrite <- (rfull_eq R' RF') in VIS2.
    exact (pm_epi_call ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p c0 ff fp LB0 LF CH m0 mo0 st0 lo B shi s LB LBs m mo c
             [] tbl [] spal msF2 mo2 R' F fc M2 OK X Htr Hbsz MU3 WM3 MI3 MP2 KR2 VIS2 RF' FZ Y1 Y2 Y3 Y4 Y8 Y10 Y11).
  Qed.

  Lemma pm_epi_e : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (p : Z) (c0 : parserC) (ff fp : Z)
      (LB0 : list block) (LF : list fframe) (CH : list (Z * Z)) (m0 : mem) (mo0 : Model) (st0 : as_St H) (lo B shi : Z)
      s LB LBs m mo c tbl spal msF R F fc,
    let w := pm_world H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p c0 ff fp LB0 LF CH m0 mo0 st0 lo B shi in
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c [OB_BINARY] tbl [] [] spal -> incl TBL_EXIT tbl -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xee140) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_EDFB0 -> PropExec.getr R 3%bv = gp -> PropExec.getr R 4%bv = tp ->
    as_SR H (pm_post H LINV ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st0 LB0 LF p c0 lo B shi m0 mo0) (mkCfg msF mo).
  Proof.
    intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p c0 ff fp LB0 LF CH m0 mo0 st0 lo B shi s LB LBs m mo c tbl spal msF R F fc
           w OK X Hi Htr Hbsz KR VIS RF FZ HT G3 G4.
    pose proof (pmxa_restrict H HHe LINV LINV_frame w s LB LBs m mo c [OB_BINARY] tbl [] [] spal TBL_EXIT [] OK X Hi (incl_refl _)) as X'.
    eapply (pm_epi_a w s LB LBs m mo c spal msF R F fc _ OK X' KR VIS RF HT).
    intros msF1 mo1 m1 R1 KR1 VIS1 RF1 X1 HT1 HK1.
    eapply (pm_epi_b ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p c0 ff fp LB0 LF CH m0 mo0 st0 lo B shi s LB LBs m1 mo1 c spal msF1 R1 F fc
              OK X1 Htr Hbsz KR1 VIS1 RF1 FZ HT1); [rewrite (HK1 3%bv ltac:(inb)); exact G3 | rewrite (HK1 4%bv ltac:(inb)); exact G4].
  Qed.
End Epi.
