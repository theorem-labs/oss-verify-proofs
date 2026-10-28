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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_Own LbB_ContStmt LbB_ContVot.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_TablStmt LbB_TablOS LbB_TablPT1 LbB_TablPT2 LbB_TablPT4 LbB_TablPT5.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma dj_of_Forall : forall W a n, Forall (fun iv : Z * Z => a + n <= fst iv \/ snd iv <= a) W -> disjoint_from W a n.
Proof.
  induction W as [|[l h] W IH]; intros a n F; [exact I|]. inversion F as [|? ? F1 F2]; subst. cbn in F1 |- *.
  split; [lia | exact (IH a n F2)].
Qed.

Section PT6.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HB : asan_rt_hyps H.

  Definition pgeo (e : ptent H) : Prop :=
       pSP e mod 16 = 0 /\ 2 ^ 45 <= pS1 e /\ pS1 e mod 32 = 0 /\ pS1 e + 192 <= pSP e /\ pSP e - 223 <= pS1 e /\ pSP e <= 2 ^ 47
    /\ aceil <= p_lo e /\ p_lo e + PT_STACK - 223 <= pS1 e
    /\ p_ff e mod 64 = 0 /\ 0x6e8000 + 0x9000 <= p_ff e /\ p_ff e + 64 <= aceil
    /\ as_FSB H + 0x1000 <= p_fp e /\ p_fp e < as_FSB H + 0x9000 /\ as_FSB H + 0x9000 <= p_ff e
    /\ p_ff e + 64 <= as_FSB H + AFS_SIZE
    /\ 0x6e8000 <= as_FSB H /\ as_FSB H + AFS_SIZE <= aceil
    /\ sh (p_ff e) + 8 = sh (p_ff e + 64) /\ 0x7fff8000 <= sh (p_ff e) /\ sh (p_ff e) + 8 <= 0x10007fff8000
    /\ (sh (p_ff e) + 8 <= as_FSB H \/ as_FSB H + AFS_SIZE <= sh (p_ff e))
    /\ (p_ff e + 64 <= 0x7fff7000 \/ 0x10007fff8000 <= p_ff e) /\ (p_fp e + 1 <= 0x7fff7000 \/ 0x10007fff8000 <= p_fp e)
    /\ p_v e mod 8 = 0 /\ ((0x6e8000 <= p_v e /\ p_v e + 24 <= 0x7fff7000) \/ (0x10007fff8000 <= p_v e /\ p_v e + 24 <= 2 ^ 47))
    /\ (p_v e + 24 <= p_lo e \/ pSP e <= p_v e) /\ (p_v e + 24 <= p_ff e \/ p_ff e + 64 <= p_v e)
    /\ (p_v e + 24 <= as_FSB H \/ as_FSB H + 0x9000 <= p_v e) /\ (p_v e + 24 <= p_fp e \/ p_fp e + 1 <= p_v e)
    /\ 0x7fff8000 <= sh (p_v e) /\ sh (p_v e) + 3 <= 0x10007fff8000
    /\ 0 <= pn e <= 48 /\ p_tp e = Z_to_bv 64 ATP.

  Lemma pgeo_of : forall e, ppre H e -> pgeo e.
  Proof.
    intros e P. destruct P as (FF & LFL & LFR & SP16 & SPH & SPB & SPS & CE & LO & TP & RA & SK & PS8 & PSD & SPN & N48 & LR
                              & V8 & VB & OBJ & OLD & BUD).
    clear SK OLD BUD LR SPN.
    pose proof (osframe_facts H _ _ _ FF) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18).
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    destruct OBJ as (_ & _ & _ & FW & _ & SD).
    assert (VFF : (p_v e + 24 <= p_ff e \/ p_ff e + 64 <= p_v e)
                  /\ (p_v e + 24 <= as_FSB H \/ as_FSB H + 0x9000 <= p_v e) /\ (p_v e + 24 <= p_fp e \/ p_fp e + 1 <= p_v e)).
    { clear - FW FF LFR G4 G5 G6 G7. unfold afs_write_ok in FW. cbn [fst snd] in FW.
      destruct FF as (_ & _ & FD).
      destruct FW as [(F1 & F2)|(f & Hf & F1 & F2)].
      - unfold AFS_SIZE, AFS_FLAGS in *. lia.
      - destruct (FD f Hf) as [D1 D2]. change (fsz 0) with 64 in D1.
        destruct (LFR f Hf) as (_ & R1 & R2 & _).
        clear - D1 R1 R2 F1 F2 G4 G5 G6 G7. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE in *. lia. }
    clear FW LFR.
    assert (SHV : 0x7fff8000 <= sh (p_v e) /\ sh (p_v e) + 3 <= 0x10007fff8000).
    { clear - VB. unfold sh. rewrite ASHADOW_BASE_val. destruct VB; Z.div_mod_to_equations; lia. }
    assert (SPR : 2 ^ 45 <= pSP e - 223)
      by (clear - LO CE ACF1; unfold PT_STACK, AFS_STACK, AINTRIN_STACK, V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO; lia).
    assert (S1R : pSP e - 223 <= pS1 e /\ pS1 e + 192 <= pSP e /\ pS1 e mod 32 = 0)
      by (unfold pS1; clear - SP16; Z.div_mod_to_equations; lia).
    destruct VFF as (VF1 & VF2 & VF3).
    unfold pgeo. unfold AFS_SIZE in *.
    vhide VB. vhide G16. vhide G17. vhide G18. vhide SD. vhide VF1. vhide VF2. vhide VF3. vhide PSD. vhide G10.
    split; [exact SP16|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact SPH|].
    split; [exact CE|]. split; [clear - S1R LO; unfold PT_STACK, AFS_STACK, AINTRIN_STACK, V4_STACK, AOPNEW_STACK, AMALLOC_STACK in *; lia|].
    split; [exact G3|]. split; [lia|]. split; [lia|].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [exact G11|]. split; [lia|]. split; [lia|]. split; [destruct G16 as [X]; exact X|].
    split; [destruct G17 as [X]; exact X|]. split; [destruct G18 as [X]; exact X|].
    split; [exact V8|]. split; [destruct VB as [X]; exact X|]. split; [destruct SD as [X]; exact X|].
    split; [destruct VF1 as [X]; exact X|]. split; [destruct VF2 as [X]; exact X|]. split; [destruct VF3 as [X]; exact X|].
    split; [lia|]. split; [lia|]. split; [unfold pn, Zlen in *; lia|]. exact TP.
  Qed.

  Definition pt_ok0 (e : ptent H) (LBi : list block) (iv : Z * Z) : Prop :=
    aclient_write_ok H LBi iv /\ afs_write_ok H (pLF e) iv /\ aconst_ok iv /\ stack0_ok iv
    /\ (snd iv <= ATP - 164 \/ ATP - 160 <= fst iv)
    /\ (snd iv <= pSP e - 104 \/ pSP e <= fst iv)
    /\ (snd iv <= pS1 e \/ pS1 e + 64 <= fst iv)
    /\ (snd iv <= p_ff e + 56 \/ p_ff e + 64 <= fst iv).

  Lemma pframe_munch : forall e k mL M sL LBi eL W,
    ppre H e -> pframe H e k mL sL LBi eL -> munch W mL M -> wmono asegs mL M -> mem_inv asegs M ->
    stk asegs M (p_lo e) (pSP e) -> Forall (pt_ok0 e LBi) W ->
    Forall (fun iv : Z * Z => snd iv <= sh (p_ff e) + 4 \/ sh (p_ff e) + 5 <= fst iv) W ->
    pframe H e k M sL LBi eL.
  Proof.
    intros e k mL M sL LBi eL W P PF MU WM MI SK FW FK.
    destruct PF as (MI0 & AC0 & ST0 & S00 & ER0 & RA0 & SV0 & SL0 & FP0 & WF0 & WS0 & WP0 & WL0 & KC0 & RF0 & RH0 & OW0).
    pose proof (pgeo_of e P) as G. destruct G as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                                                 & _ & _ & _ & _ & _ & _ & _ & _ & _ & TP).
    destruct (client_frame H HB sL LBi (pLF e) (p_B e) W mL M RH0 RF0 AC0 RA0 MU WM
                (Forall_impl _ (fun iv (X : pt_ok0 e LBi iv) => proj1 X) FW)
                (Forall_impl _ (fun iv (X : pt_ok0 e LBi iv) => proj1 (proj2 X)) FW)
                (Forall_impl _ (fun iv (X : pt_ok0 e LBi iv) => proj1 (proj2 (proj2 X))) FW)) as (RH1 & RF1 & AC1 & RA1).
    assert (ERA : errno_addr (p_tp e) = ATP - 164) by (rewrite TP, HLib.u64_of_Z by (unfold ATP; lia); lia).
    unfold pframe.
    split; [exact MI|]. split; [exact AC1|]. split; [exact SK|].
    split; [eapply stack0_transport; [exact S00 | exact MU | exact WM | exact (Forall_impl _ (fun iv (X : pt_ok0 e LBi iv) => proj1 (proj2 (proj2 (proj2 X)))) FW)]|].
    split.
    { eapply rw_cells_transport; [exact ER0 | exact MU | exact WM |]. rewrite ERA. apply dj_of_Forall.
      eapply Forall_impl; [|exact FW]. intros iv X. destruct X as (_ & _ & _ & _ & X & _). cbn. lia. }
    split; [exact RA1|].
    split.
    { eapply rw_cells_transport; [exact SV0 | exact MU | exact WM |]. apply dj_of_Forall.
      eapply Forall_impl; [|exact FW]. intros iv X. destruct X as (_ & _ & _ & _ & _ & X & _). cbn. lia. }
    split.
    { destruct SL0 as [SLa SLb]. split.
      - eapply rw_cells_transport; [exact SLa | exact MU | exact WM |]. apply dj_of_Forall.
        eapply Forall_impl; [|exact FW]. intros iv X. destruct X as (_ & _ & _ & _ & _ & _ & X & _). cbn. lia.
      - intros NZ. eapply rw_cells_transport; [exact (SLb NZ) | exact MU | exact WM |]. apply dj_of_Forall.
        eapply Forall_impl; [|exact FW]. intros iv X. destruct X as (_ & _ & _ & _ & _ & _ & X & _). cbn. lia. }
    split.
    { eapply rw_cells_transport; [exact FP0 | exact MU | exact WM |]. apply dj_of_Forall.
      eapply Forall_impl; [|exact FW]. intros iv X. destruct X as (_ & _ & _ & _ & _ & _ & _ & X). cbn. lia. }
    split; [exact (LbB_Own.wr_at_wmono _ _ _ _ WF0 WM)|]. split; [exact (LbB_Own.wr_at_wmono _ _ _ _ WS0 WM)|].
    split; [exact (LbB_Own.wr_at_wmono _ _ _ _ WP0 WM)|]. split; [exact (LbB_Own.wr_at_wmono _ _ _ _ WL0 WM)|].
    split.
    { eapply rw_cells_transport; [exact KC0 | exact MU | exact WM |]. apply dj_of_Forall.
      eapply Forall_impl; [|exact FK]. intros iv X. cbv beta in X. change (Z.of_nat (cells_size [C1 (b8 k)])) with 1. lia. }
    split; [exact RF1|]. split; [exact RH1|]. exact (lb_own_wmono _ _ _ OW0 WM).
  Qed.

  Lemma pvec_munch : forall e ys mL M LBi bi capi pidi W,
    pvec H e ys mL LBi bi capi pidi -> munch W mL M -> wmono asegs mL M ->
    disjoint_from W (p_v e) 24 -> disjoint_from W bi (4 * Zlen ys) ->
    (0 < capi -> disjoint_from W (sh bi) (nsh (4 * capi))) -> disjoint_from W (sh (p_v e)) (nsh 24) ->
    pvec H e ys M LBi bi capi pidi.
  Proof.
    intros e ys mL M LBi bi capi pidi W PV MU WM D1 D2 D3 D4.
    destruct PV as (VEC & SH & AD & WV & OB & GR).
    pose proof VEC as (_ & _ & _ & Hlen & _).
    split; [exact (vec32A_munch LBi mL M (p_v e) bi ys capi W VEC MU D1 D2)|].
    split; [intros Hc; eapply SHAD_transport; [exact (SH Hc) | exact MU | exact WM |]; rewrite cc_gen_length by lia; exact (D3 Hc)|].
    split; [eapply addressable_transport; [exact AD | exact MU | exact WM | exact D4]|].
    split; [exact (LbB_Own.wr_at_wmono _ _ _ _ WV WM)|].
    split; [exact OB | exact GR].
  Qed.

  Lemma pgrown_blocks : forall e LBi bi capi pidi, ppre H e -> pgrown H e LBi bi capi pidi ->
    forall bb, In bb (p_LB e) -> In bb LBi \/ (bb = (p_pid e, p_b e, 4 * p_cap e) /\ 0 < p_cap e /\ p_b e <> 0).
  Proof.
    intros e LBi bi capi pidi P GR bb Hb.
    destruct P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OLD & ND & _).
    destruct GR as [(_ & _ & -> & _)|(_ & -> & _)]; [left; exact Hb|].
    unfold v4_newLB. destruct (Z.eqb_spec (p_b e) 0) as [B0|B0]; [left; right; exact Hb|].
    destruct OLD as [(E0 & _)|(C0 & HIn)]; [contradiction|].
    destruct (Z.eq_dec (blk_id bb) (p_pid e)) as [E|NE].
    - right. destruct bb as [[pb Ab] nb]. cbn [blk_id fst] in E. subst pb.
      pose proof (LbB_ContV4.nodup_id_same _ _ _ _ _ _ ND HIn Hb) as EQ. rewrite <- EQ. split; [reflexivity|]. split; [exact C0 | exact B0].
    - left. right. exact (LbB_ContV4.lb_remove_keep H HB _ _ _ ND Hb NE).
  Qed.

  Lemma pvec_blk : forall e ys mL sL LBi bi capi pidi, as_RHEAP H sL LBi mL -> pvec H e ys mL LBi bi capi pidi ->
    0 <= Zlen ys <= capi /\ ((capi = 0 /\ bi = 0) \/ (0 < capi /\ In (pidi, bi, 4 * capi) LBi /\ ablock_range H bi (4 * capi)))
    /\ (bi <> 0 -> p_v e + 24 <= bi \/ bi + 4 * capi <= p_v e).
  Proof.
    intros e ys mL sL LBi bi capi pidi RH PV. destruct PV as (VEC & _ & _ & _ & OB & _).
    pose proof VEC as (_ & _ & _ & Hlen & Hb & _).
    split; [exact Hlen|]. split.
    - destruct OB as [(E0 & E1)|(C0 & HIn)]; [left; split; assumption|].
      right. split; [exact C0|]. split; [exact HIn|]. exact (ah_blocks H HB _ _ _ _ RH HIn).
    - intros NZ. destruct Hb as [(E0 & _)|(_ & _ & _ & _ & _ & D)]; [contradiction | exact D].
  Qed.

  Lemma pt_ok0_local : forall e LBi, ppre H e ->
    pt_ok0 e LBi (p_ff e + 32, p_ff e + 36) /\ (p_ff e + 36 <= sh (p_ff e) + 4 \/ sh (p_ff e) + 5 <= p_ff e + 32).
  Proof.
    intros e LBi P. pose proof (pgeo_of e P) as G.
    pose proof P as (FF & _).
    pose proof (osframe_facts H _ _ _ FF) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G10 & _).
    destruct G as (_ & _ & _ & S1S & _ & _ & CE & LO & F64 & FL & FH & P1 & P2 & P3 & P4 & FS1 & FS2 & SH1 & SH2 & SH3 & SH4 & FB & PB & _).
    unfold pt_ok0. cbn [fst snd]. unfold PT_STACK, AFS_STACK, AINTRIN_STACK, V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO.
    pose proof aceil_facts as ((ACF1 & ACF2) & _).
    split; [|unfold ASHADOW_BASE in *; lia].
    split; [right; right; right; right; left; cbn [fst snd]; unfold AFS_SIZE in *; lia|].
    split; [right; exists (0, p_ff e, p_fp e); split; [left; reflexivity | cbn; change (fsz 0) with 64; lia]|].
    split; [eapply (LbB_SR.aconst_ok_app (as_FSB H) AFS_SIZE); [exact G10 | lia | unfold AFS_SIZE in *; lia]|].
    split; [eapply (stack0_ok_aapp (as_FSB H) AFS_SIZE); [exact G10 | lia | unfold AFS_SIZE in *; lia]|].
    unfold ATP. lia.
  Qed.
End PT6.
