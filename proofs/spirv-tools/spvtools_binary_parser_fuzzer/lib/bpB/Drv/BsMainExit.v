(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Bs0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BCatExec BCatSim BSeqExec BStoreOk BShapeAlg BNodes BHoare BFrame BShapeLaws BpecConsts BAgentLib BFileSim BSymExec2 BSymExec2Sound BSymRun BSymDrive BSymDriveX BMemSplit BSpec BLibTail BRefPrintfLib BRefMemcpyLib BReach BegsEquivM BainEqv BeapCeil BazyRestrict BazySR BazyFdNodes BainWalk_defs BainSegs BainMem.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMem BCells BArr BStep BLFrame BMState BSysStep BExec BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsDriverLaws BsStack0 BXXRep DvB_CXXAs RtB_Iface DvB_FuzzStmt BRefExitBase BsPrintfFirst BsExitDefs BsTailExit BsRefused BsDrvTails BsDrvHeap BsDrvRun BsDrvMem BsDrvDefs BsTRSegs BsMainWalk_defs BsMainSegs BsMainPre BsMainLoop BsDrvCells.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import DvB_ExitPre DvB_ExitIface DvB_ExitCells.
Import ListNotations.
Import BSymExec2.SX2. Import BSymExec2Sound.SX2S.
Import BPropExec.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma zero_lines_length : forall k, length (zero_lines k) = (2 * k)%nat.
Proof. induction k as [|k IH]; [reflexivity|]. cbn [zero_lines length]. rewrite IH. lia. Qed.
Lemma zero_lines_S : forall k, zero_lines (S k) = [Z_to_bv 8 48; Z_to_bv 8 10] ++ zero_lines k.
Proof. reflexivity. Qed.

Definition cells_in_b (lo hi : Z) (cs : list (Z * nat * Z)) : bool :=
  forallb (fun c => match c with (a, w, _) => ((lo <=? a) && (a + Z.of_nat w <=? hi))%Z end) cs.

Lemma cells_ok_T : forall (m m' : word -> option byte) (cs : list (Z * nat * Z)) lo hi,
  cells_in_b lo hi cs = true ->
  (forall (a : Z) n bs, lo <= a -> a + Z.of_nat n <= hi -> rdn RSEGS m (Z_to_bv 64 a) n = Some bs -> rdn RSEGS m' (Z_to_bv 64 a) n = Some bs) ->
  cells_ok m cs -> cells_ok m' cs.
Proof.
  intros m m' cs lo hi B T C. unfold cells_ok in *. induction cs as [|[[a w] v] cs IH]; [constructor|].
  cbn [cells_in_b forallb] in B. apply andb_true_iff in B as [B1 B]. apply andb_true_iff in B1 as [B1 B2].
  apply Z.leb_le in B1. apply Z.leb_le in B2.
  inversion C as [|c cs' Hok Hc']; subst. constructor; [| apply IH; assumption]. unfold cell_ok in *. apply T; assumption.
Qed.

Lemma xdrv2_wf : forallb cell_wf_b xdrv2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma xdrv2_client :
  Forall (fun c : Z * nat * Z => match c with (a, w, _) => forall x, a <= x < a + Z.of_nat w -> aimg_client x end) xdrv2.
Proof. unfold xdrv2, aimg_client. repeat (apply Forall_cons; [cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; intros; lia|]). apply Forall_nil. Qed.
Lemma xdrv2_range : Forall (fun c : Z * nat * Z => match c with (a, w, _) =>
  0 <= a /\ a + Z.of_nat w <= 0x6e8000 /\ (a + Z.of_nat w <= 0x189920 \/ 0x189a08 <= a) end) xdrv2.
Proof. unfold xdrv2. repeat (apply Forall_cons; [cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]). apply Forall_nil. Qed.

Section Exit.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Variable FZP : fuzz_params.
  Hypothesis HH : asan_rt_hyps H.
  Hypothesis AHM : RHEAP_ahm H.
  Hypothesis DL : asan_driver_laws H.
  Variables (sp0 : word) (tid can : Z).
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis HCE : hceil + 8388608 <= bv_unsigned sp0.
  Hypothesis Htid : 0 < tid < 2 ^ 22.
  Hypothesis TRC : adrv_traces H FZP.

  Let SPlo : 0x7fff80000000 <= bv_unsigned sp0 := proj1 Hvsp.
  Let SPhi : bv_unsigned sp0 <= 0x800000000000 := proj1 (proj2 Hvsp).
  Let SP16 : bv_unsigned sp0 mod 16 = 0 := proj2 (proj2 Hvsp).
  Let rom := seg_rom asegs.
  Let lo : Z := bv_unsigned sp0 - 128 - ATR_STACK.
  Let Elo : lo = bv_unsigned sp0 - 128 - 69632. Proof. reflexivity. Qed.

  Lemma aceil_loX : aceil + 4096 <= lo.
  Proof. pose proof Elo. acb. lia. Qed.

  Lemma ahm_of : forall s LB m, as_RHEAP H s LB m -> exists TB, ahm_ok m TB.
  Proof. intros s LB m RH. exact (AHM s LB m RH). Qed.

  Record xstat (m : word -> option byte) : Prop := XS {
    xs_inv   : mem_inv asegs m;
    xs_stk   : stk asegs m lo (bv_unsigned sp0);
    xs_ac    : ACONST m;
    xs_relro : arelro_none m;
    xs_glb   : aglb_none m;
    xs_cells : cells_ok m xdrv2;
    xs_tid   : exists t, atid_cell m t;
    xs_can   : exists c, acanary m c;
    xs_frame : amframe sp0 m;
    xs_aux   : exists B, as_rauxv_ok H m B /\ bv_unsigned sp0 <= B < 2 ^ 64;
    xs_sh0   : exists shi, stack0 m lo shi /\ 0x800000000000 <= shi }.

  Definition ostate (pending : list byte) (m : word -> option byte) : Prop :=
    (pending = [] /\ cells_ok m xk_stderr2 /\ cells_ok m astdout0 /\ cells_ok m xk_atxU)
    \/ (exists k, (k <= 3)%nat /\ astdout_after m k /\ cells_ok m xk_err0 /\ cells_ok m xk_atxT /\ pending = zero_lines k).

  Lemma xstat_of_mstatics : forall mem0 m, mstatics H sp0 tid can mem0 m -> xstat m.
  Proof.
    intros mem0 m [INV STK AC RELRO GLB CELLS OUT TID CAN RFS LATCH SH0 ABOVE FR AUX]. split; try assumption.
    - apply xdrv2_of. exact CELLS.
    - exists tid. exact TID.
    - exists can. exact CAN.
  Qed.

  Lemma img_rdn_frameL : forall m m' (a : Z) n bs,
    frame_mod m m' (regL_w sp0) -> rdn RSEGS m (Z_to_bv 64 a) n = Some bs -> 0 <= a -> a + Z.of_nat n <= AIMG_TOP ->
    rdn RSEGS m' (Z_to_bv 64 a) n = Some bs.
  Proof.
    intros m m' a n bs FM RD Ha Hn. pose proof SPlo. pose proof SPhi. unfold AIMG_TOP in Hn.
    eapply ardn_frame; [exact FM | exact RD | lia | lia |].
    intros r Hr. unfold regL_w, MSTK in Hr. cbn [In] in Hr. destruct Hr as [<-|[]]. cbn [fst snd]. rewrite u_small by lia. lia.
  Qed.
  Lemma img_rdn_apres : forall LB m m' (a : Z) n bs,
    apres H LB (bv_unsigned sp0 - 128) m m' -> rdn RSEGS m (Z_to_bv 64 a) n = Some bs -> 0 <= a ->
    (forall x, a <= x < a + Z.of_nat n -> aimg_client x) -> a + Z.of_nat n <= AIMG_TOP ->
    rdn RSEGS m' (Z_to_bv 64 a) n = Some bs.
  Proof.
    intros LB m m' a n bs HP RD Ha HC Hn. unfold AIMG_TOP in Hn. eapply rdn_apresW; [exact HP | exact RD | lia | lia |].
    intros x Hx. right; left. apply HC. exact Hx.
  Qed.

  Lemma ostate_pres : forall pending m m',
    (forall (a : Z) n bs, 0x189920 <= a -> a + Z.of_nat n <= 0x6e6880 -> (a + Z.of_nat n <= 0x189b94 \/ 0x6c3694 <= a) ->
       rdn RSEGS m (Z_to_bv 64 a) n = Some bs -> rdn RSEGS m' (Z_to_bv 64 a) n = Some bs) ->
    ostate pending m -> ostate pending m'.
  Proof.
    intros pending m m' T [(E & SE & SO & SA)|(k & Hk & ST & SE & SA & E)].
    - left. split; [exact E|]. split; [|split].
      + eapply (cells_ok_T m m' xk_stderr2 0x189920 0x189b94); [vm_compute; reflexivity | | exact SE].
        intros a n bs H1 H2 RD. apply T; [lia | lia | lia | exact RD].
      + eapply (cells_ok_T m m' astdout0 0x189920 0x189b94); [vm_compute; reflexivity | | exact SO].
        intros a n bs H1 H2 RD. apply T; [lia | lia | lia | exact RD].
      + eapply (cells_ok_T m m' xk_atxU 0x6c3694 0x6e59e8); [vm_compute; reflexivity | | exact SA].
        intros a n bs H1 H2 RD. apply T; [lia | lia | lia | exact RD].
    - right. exists k. split; [exact Hk|]. split; [| split; [| split; [| exact E]]].
      + destruct ST as [F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14]. pose proof (zero_lines_length k) as ZL.
        split; (apply T; [cbn; lia | cbn; try rewrite ZL; lia | cbn; try rewrite ZL; lia | assumption]).
      + eapply (cells_ok_T m m' xk_err0 0x189920 0x189b94); [vm_compute; reflexivity | | exact SE].
        intros a n bs H1 H2 RD. apply T; [lia | lia | lia | exact RD].
      + eapply (cells_ok_T m m' xk_atxT 0x6c3694 0x6e59e8); [vm_compute; reflexivity | | exact SA].
        intros a n bs H1 H2 RD. apply T; [lia | lia | lia | exact RD].
  Qed.

  Lemma ostate_frameL : forall pending m m', ostate pending m -> frame_mod m m' (regL_w sp0) -> ostate pending m'.
  Proof.
    intros pending m m' OS FM. eapply ostate_pres; [|exact OS]. intros a n bs H1 H2 H3 RD.
    eapply img_rdn_frameL; [exact FM | exact RD | lia | unfold AIMG_TOP; lia].
  Qed.
  Lemma ostate_apres : forall pending LB m m', ostate pending m -> apres H LB (bv_unsigned sp0 - 128) m m' -> ostate pending m'.
  Proof.
    intros pending LB m m' OS HP. eapply ostate_pres; [|exact OS]. intros a n bs H1 H2 H3 RD.
    eapply img_rdn_apres; [exact HP | exact RD | lia | | unfold AIMG_TOP; lia]. intros x Hx. unfold aimg_client. lia.
  Qed.

  Lemma xstat_frameL : forall m m', xstat m -> frame_mod m m' (regL_w sp0) -> xstat m'.
  Proof.
    intros m m' [INV STK AC RELRO GLB CELLS [t [TID Ht]] [c [CAN Hc]] [FRa FRs] [B' [AUX HB']] [shi [SH0 Hshi]]] FM.
    pose proof SPlo. pose proof SPhi. pose proof Elo. pose proof aceil_loX as HCL. acb.
    pose proof (frame_mod_munch _ _ _ FM) as MU. pose proof (aframe_mod_wmono _ _ _ FM) as WM.
    unfold regL_w, ivls, MSTK in MU. cbn [map fst snd] in MU. rewrite u_small in MU by lia.
    assert (T : forall (a : Z) n bs, rdn RSEGS m (Z_to_bv 64 a) n = Some bs -> 0 <= a -> a + Z.of_nat n <= AIMG_TOP -> rdn RSEGS m' (Z_to_bv 64 a) n = Some bs).
    { intros a n bs RD Ha Hn. eapply img_rdn_frameL; eassumption. }
    split.
    - eapply amem_inv_frame; [exact INV | exact FM |]. constructor; [|constructor]. cbn [fst snd]. unfold MSTK. rewrite u_small by lia. lia.
    - destruct STK as (S1 & S2 & S3).
      assert (STK1 : stk asegs m lo (bv_unsigned sp0 - 128)) by (split; [exact S1|]; split; [lia|]; intros x Hx; apply S3; lia).
      pose proof (astk_grows m m' lo (bv_unsigned sp0 - 128) STK1 ltac:(lia) ltac:(lia) (proj2 FM)) as (_ & _ & S3').
      split; [exact S1|]. split; [exact S2|].
      intros a Ha. destruct (Z_lt_le_dec a (bv_unsigned sp0 - 128)) as [L|L].
      + apply S3'. lia.
      + assert (E : m' (wa a) = m (wa a)) by (apply MU; rewrite wa_eq, u_small by lia; cbn; lia).
        unfold wview, mrd. rewrite E. apply S3. lia.
    - eapply ACONST_frame; [exact AC | exact MU | exact WM |]. constructor; [|constructor]. apply aconst_ok_hi. cbn [fst]. unfold AHI_LO. lia.
    - intros i Hi. rewrite <- (RELRO i Hi), <- wa_eq. apply MU. rewrite wa_eq, u_small by lia. cbn. lia.
    - destruct GLB as [G1 G2]. split; intros i Hi; [rewrite <- (G1 i Hi) | rewrite <- (G2 i Hi)]; rewrite <- wa_eq; apply MU;
        rewrite wa_eq, u_small by lia; cbn; lia.
    - eapply cells_ok_munchW; [apply xdrv2_wf | exact CELLS | exact MU |].
      eapply Forall_impl; [| apply xdrv2_range]. intros [[a w] v] Ra. cbn. lia.
    - exists t. split; [|exact Ht]. apply T; [exact TID | lia | unfold AIMG_TOP; cbn; lia].
    - exists c. split; [|exact Hc]. apply T; [exact CAN | lia | unfold AIMG_TOP; cbn; lia].
    - split.
      + eapply rdn_munchW; [exact MU | exact FRa | lia | cbn; lia |]. intros x Hx. cbn in Hx |- *. lia.
      + intros i Hi. destruct (FRs i Hi) as [w Hw]. exists w. eapply rdn_munchW; [exact MU | exact Hw | lia | cbn; lia |]. intros x Hx. cbn in Hx |- *. lia.
    - exists B'. split; [|exact HB']. eapply (ah_rauxv_frame H HH []); [exact AUX | exact MU | exact WM |].
      constructor; [|constructor]. left. cbn [fst]. lia.
    - exists shi. split; [|exact Hshi]. eapply stack0_transport; [exact SH0 | exact MU | exact WM |].
      constructor; [|constructor]. apply stack0_ok_app; cbn [fst]; unfold AHI_LO; lia.
  Qed.

  Lemma xstat_apres : forall m m' LB1 B2,
    xstat m -> apres H LB1 (bv_unsigned sp0 - 128) m m' ->
    mem_inv asegs m' -> stk asegs m' lo (bv_unsigned sp0 - 128) -> ACONST m' ->
    as_rauxv_ok H m' B2 -> bv_unsigned sp0 <= B2 < 2 ^ 64 ->
    xstat m'.
  Proof.
    intros m m' LB1 B2 [INV STK AC RELRO GLB CELLS [t [TID Ht]] [c [CAN Hc]] [FRa FRs] AUX [shi [SH0 Hshi]]] HP INV' STK' AC' AUX' HB2.
    pose proof SPlo. pose proof SPhi. pose proof Elo.
    assert (AG : forall x : word, bv_unsigned sp0 - 128 <= bv_unsigned x -> m' x = m x).
    { intros x Hx. rewrite <- (Z_to_bv_bv_unsigned x), <- wa_eq. exact (proj1 (HP _ (u64_range x) ltac:(left; lia))). }
    assert (IMG : forall x, aimg_client x -> 0 <= x < 2 ^ 64 -> m' (wa x) = m (wa x)).
    { intros x Hx Hx64. exact (proj1 (HP x Hx64 ltac:(right; left; exact Hx))). }
    assert (T : forall (a : Z) n bs, rdn RSEGS m (Z_to_bv 64 a) n = Some bs -> 0 <= a -> (forall x, a <= x < a + Z.of_nat n -> aimg_client x) ->
               a + Z.of_nat n <= AIMG_TOP -> rdn RSEGS m' (Z_to_bv 64 a) n = Some bs).
    { intros a n bs RD Ha HC Hn. eapply img_rdn_apres; eassumption. }
    split; try assumption.
    - destruct STK as (S1 & S2 & S3). destruct STK' as (_ & _ & S3'). split; [exact S1|]. split; [exact S2|].
      intros a Ha. destruct (Z_lt_le_dec a (bv_unsigned sp0 - 128)) as [L|L]; [apply S3'; lia|].
      assert (E : m' (wa a) = m (wa a)) by (apply AG; rewrite wa_eq, u_small by lia; lia).
      unfold wview, mrd. rewrite E. apply S3. lia.
    - intros i Hi. rewrite <- (RELRO i Hi), <- wa_eq. apply IMG; [unfold aimg_client; lia | lia].
    - destruct GLB as [G1 G2]. split; intros i Hi; [rewrite <- (G1 i Hi) | rewrite <- (G2 i Hi)]; rewrite <- wa_eq;
        apply IMG; first [lia | unfold aimg_client; lia].
    - eapply cells_ok_apresW; [apply xdrv2_wf | exact CELLS | exact HP | apply xdrv2_client].
    - exists t. split; [|exact Ht]. apply T; [exact TID | lia | intros x Hx; unfold aimg_client; cbn in Hx; lia | unfold AIMG_TOP; cbn; lia].
    - exists c. split; [|exact Hc]. apply T; [exact CAN | lia | intros x Hx; unfold aimg_client; cbn in Hx; lia | unfold AIMG_TOP; cbn; lia].
    - split.
      + eapply rdn_apresW; [exact HP | exact FRa | lia | cbn; lia |]. intros x Hx. left. cbn in Hx. lia.
      + intros i Hi. destruct (FRs i Hi) as [w Hw]. exists w. eapply rdn_apresW; [exact HP | exact Hw | lia | cbn; lia |]. intros x Hx. left. cbn in Hx. lia.
    - exists B2. split; assumption.
    - exists shi. split; [|exact Hshi]. eapply (stack0_xpres H); [apply xpres_of_apres; exact HP | exact SH0 | constructor].
  Qed.

  Lemma xs_shadow : forall m (spz : Z), xstat m -> lo + 4104 <= spz -> spz <= bv_unsigned sp0 ->
    forall a, 2147450880 + (spz - 4096) / 8 <= a < 2147450880 + spz / 8 -> m (Z_to_bv 64 a) = Some (Z_to_bv 8 0).
  Proof.
    intros m spz XS H1 H2 a Ha. destruct (xs_sh0 m XS) as [shi [SH0 Hshi]].
    apply (stack0_qsh0 m lo shi spz SH0 H1 ltac:(lia)). rewrite ASHADOW_BASE_val. exact Ha.
  Qed.

  Lemma axA_of : forall m TB pending, xstat m -> ahm_ok m TB -> ostate pending m ->
    exists t c, axA m (Z_to_bv 64 (bv_unsigned sp0 - 48)) t c TB.
  Proof.
    intros m TB pending XS AH OS. pose proof SPlo. pose proof SPhi. pose proof SP16. pose proof Elo. acb.
    destruct XS as [INV STK AC RELRO GLB CELLS [t TID] [c CAN] FR AUX SH0] eqn:EXS.
    pose proof AH as (_ & _ & _ & TBCE & _).
    assert (CFG : cells_ok m xk_err6 /\ cells_ok m xk_out4).
    { destruct OS as [(_ & SE & SO & SA)|(k & _ & ST & SE & SA & _)].
      - destruct (cfg_U2_cells m SE SO SA) as (C1 & C2 & _). split; assumption.
      - destruct (cfg_T_cells m k ST SE SA) as (C1 & C2 & _). split; assumption. }
    exists t, c. apply axA_intro; try assumption; try (rewrite u_small by lia; unfold ASP_LO, ASP_HI; lia); try tauto.
    - rewrite u_small by lia. rewrite <- Zminus_mod_idemp_l, SP16. reflexivity.
    - eapply astk_stk_ok; [exact STK | rewrite u_small by lia; lia | rewrite u_small by lia; lia | lia | lia].
    - rewrite u_small by lia. apply (xs_shadow m _ XS); lia.
  Qed.

  Lemma exitA_of : forall m TB t c, xstat m -> ahm_ok m TB -> cells_ok m astdout0 -> cells_ok m xk_atxU -> atid_cell m t -> acanary m c ->
    exitA m (Z_to_bv 64 (bv_unsigned sp0 - 128)) t c TB.
  Proof.
    intros m TB t c XS AH SO SA TID CAN. pose proof SPlo. pose proof SPhi. pose proof Elo. acb.
    destruct XS as [INV STK AC RELRO GLB CELLS TID' CAN' FR AUX SH0] eqn:EXS.
    pose proof AH as (_ & _ & _ & TBCE & _).
    apply exitA_intro; try assumption.
    - rewrite u_small by lia. lia.
    - rewrite u_small by lia. apply (xs_shadow m _ XS); lia.
  Qed.

  Section FX.
  Context {fx : DFP}.
  Theorem free_exit : forall s msF mo regs mem p (A cap : Z) (status : word) (pending : list byte) junk,
    as_VIS H s msF = mkst regs (Z_to_bv 64 0xe85e8) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) -> getr regs 4 = Z_to_bv 64 ATP -> getr regs 8 = status -> getr regs 9 = Z_to_bv 64 A ->
    bv_unsigned status < 256 ->
    as_RHEAP H s [(p, A, cap)] mem -> rw_cells asegs mem A [CB (Z.to_nat cap) junk] -> addressable mem A cap ->
    as_Cf H cap <= as_AL H s ->
    xstat mem -> ostate pending mem ->
    fd_lookup (m_fds mo) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    realizes asegs (mkCfg msF mo) (t_emit (W 1 pending) (t_exit (bv_and status (Z_to_bv 64 255)) (m_fs mo))).
  Proof.
    intros s msF mo regs mem p A cap status pending junk HV HA R2 R4 R8 R9 Hst RH HCB AD HCF XS OS Hfd1. pose proof (u64_range status) as HstR.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof Elo. pose proof aceil_loX as HCL. acb.
    pose proof (ah_blocks H HH _ _ _ (p, A, cap) RH ltac:(left; reflexivity)) as BR. pose proof BR as (B1 & B2 & B3 & B4 & B5 & B6 & B7). cbn [blk_addr blk_size fst snd] in *.

    assert (STK0 : stk_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK).
    { eapply astk_stk_ok; [exact (xs_stk _ XS) | unfold MSTK; rewrite u_small by lia; lia | rewrite u_small by lia; lia | unfold MSTK; lia | lia]. }
    eapply (aseg_I H DL sp0 Hvsp s msF mo regs mem (getr regs 18) A status _ R2 R4 R8 R9 STK0 (amem_inv_ro_none _ (xs_inv _ XS)) (xs_relro _ XS));
      [| exact HV | exact HA].
    intros regs1 mem1 msF1 mo1 HV1 HA1 SB1 Q2 Q4 Q8 Q1 Q9 Q10 KP FM1 STK1.
    pose proof (xstat_frameL _ _ XS FM1) as XS1. pose proof (ostate_frameL _ _ _ OS FM1) as OS1.
    pose proof (rheap_frameL H HH sp0 Hvsp HCE _ _ _ _ RH FM1) as RH1.
    destruct (blkR_frameL H sp0 Hvsp HCE A cap mem mem1 junk 0%nat [] BR FM1 HCB AD ltac:(reflexivity) ltac:(lia)) as (CB1 & AD1 & _).

    destruct (aerrno_rw_any mem1) as [errv ERR]. destruct (xs_aux _ XS1) as [B' [AUX1 HB']].
    assert (STKlo : stk asegs mem1 lo (bv_unsigned sp0 - 128)).
    { destruct (xs_stk _ XS1) as (S1 & S2 & S3). split; [exact S1|]. split; [lia|]. intros a Ha. apply S3. lia. }
    change (Z_to_bv 64 0xba104) with (Z_to_bv 64 AFREE_STUB) in HV1.
    eapply (afree_call H HH DL regs1 mem1 msF1 mo1 s [(p, A, cap)] p A cap lo B' errv 0xe85f0 [] junk (shadow_of cap) _ HV1 HA1 Q1);
      [ lia | reflexivity | exact Q4 | exact Q10 | exact RH1 | left; reflexivity | exact HCF
      | exact CB1 | exact (proj2 AD1) | apply shadow_of_length; lia
      | exact AUX1 | rewrite Q2, u_small by lia; lia
      | rewrite Q2, u_small by lia; exact STKlo | lia | rewrite Q2, u_small by lia; unfold AFREE_STACK; lia
      | rewrite Q2, u_small by lia; rewrite <- Zminus_mod_idemp_l, SP16; reflexivity
      | rewrite Q4; unfold ATP; rewrite u_small by lia; exact ERR | exact (xs_inv _ XS1) | exact (xs_ac _ XS1)
      | apply (ah_chain_nil H HH); rewrite Q8; lia
      | cbn [map]; destruct TRC as (_ & _ & _ & T4 & _); exact T4 |].
    rewrite Q2, !u_small by lia.
    intros regs2 mem2 msF2 mo2 s2 HV2 HA2 MP2 KEPT2 INV2 STK2 ERR2 AUX2 HP2 RH2 AC2 HAL2.
    pose proof (xstat_apres _ _ _ _ XS1 HP2 INV2 STK2 AC2 AUX2 HB') as XS2. pose proof (ostate_apres _ _ _ _ OS1 HP2) as OS2.
    assert (S2 : getr regs2 2 = Z_to_bv 64 (bv_unsigned sp0 - 128)) by (rewrite (KEPT2 2%bv ltac:(in_solve)); exact Q2).
    assert (S4 : getr regs2 4 = Z_to_bv 64 0x6c5858) by (rewrite (KEPT2 4%bv ltac:(in_solve)); exact Q4).
    assert (S8 : getr regs2 8 = status) by (rewrite (KEPT2 8%bv ltac:(in_solve)); exact Q8).

    assert (STK2' : stk_ok RSEGS mem2 (Z_to_bv 64 (bv_unsigned sp0 - 128)) MSTK).
    { eapply astk_stk_ok; [exact (xs_stk _ XS2) | unfold MSTK; rewrite u_small by lia; lia | rewrite u_small by lia; lia | unfold MSTK; lia | lia]. }
    eapply (aseg_X H DL sp0 Hvsp s2 msF2 mo2 regs2 mem2 status _ S2 S4 S8 STK2' (amem_inv_ro_none _ (xs_inv _ XS2)) (xs_relro _ XS2) (xs_frame _ XS2));
      [| exact HV2 | exact HA2].
    intros regs3 msF3 mo3 HV3 HA3 SB3 T2 T4 T10 T1.

    assert (EQ3 : m_fs mo3 = m_fs mo /\ m_fds mo3 = m_fds mo).
    { pose proof (mo_tr _ _ _ (mo_sb _ _ SB1) (mo_tr _ _ _ (mo_mp H DL _ _ MP2) (mo_sb _ _ SB3))) as [E1 E2]. split; assumption. }
    destruct EQ3 as [EFS EFDS]. rewrite <- EFS.

    destruct (ahm_of _ _ _ RH2) as [TB AH2].
    destruct (axA_of mem2 TB pending XS2 AH2 OS2) as (t & c & XA).
    apply (drv_lazy H DL s2 msF3 mo3 regs3 _ mem2 _ HV3 HA3). intros Lz Sz Zr OK RS _.
    change (Z_to_bv 64 0x165478) with (Z_to_bv 64 AEXIT) in RS.
    destruct OS2 as [(-> & SE & SO & SA) | (k & Hk & STA & SE & SA & ->)].
    -
      destruct (cfg_U2_cells mem2 SE SO SA) as (_ & _ & CU).
      eapply rz_conseq; [| apply t_eq_sym; apply t_emit_W_nil; apply t_exit_has_nil].
      exact (as_exit_U2 regs3 mem2 msF3 mo3 Lz Sz Zr _ status t c TB XA CU T2 T4 T10 OK RS).
    - destruct (cfg_T_cells mem2 k STA SE SA) as (_ & _ & C0 & CT).
      destruct k as [|k'].
      +
        cbn [zero_lines]. eapply rz_conseq; [| apply t_eq_sym; apply t_emit_W_nil; apply t_exit_has_nil].
        exact (as_exit_T0 regs3 mem2 msF3 mo3 Lz Sz Zr _ status t c TB XA (C0 eq_refl) T2 T4 T10 OK RS).
      +
        unfold W.
        apply (as_exit_T (Z.of_nat (S k')) regs3 mem2 msF3 mo3 Lz Sz Zr (Z_to_bv 64 (bv_unsigned sp0 - 48)) status t c TB (zero_lines (S k')));
          [ lia | exact XA | exact CT | rewrite zero_lines_length; lia
          | rewrite zero_lines_length; exact (so_bytes _ _ STA)
          | rewrite EFDS; exact Hfd1 | exact T2 | exact T4 | exact T10 | exact OK | exact RS ].
  Qed.

  End FX.

  Theorem refuse_exit : forall mem0 pp fs0 s msF mo regs mem p (A : Z),
    as_VIS H s msF = mkst regs (Z_to_bv 64 0xe863c) mem rom -> as_AKREL H s (mkCfg msF mo) ->
    ARfInv H sp0 pp tid can fs0 mem0 A s p regs mem mo ->
    realizes asegs (mkCfg msF mo) (t_die msg_refused fs0).
  Proof.
    intros mem0 pp fs0 s msF mo regs mem p A HV HA [(R2 & R4 & R8 & R18 & R20) R9 [cap RH] ST EFS Hfd1 Hfd2]. rewrite <- EFS.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof SP16. pose proof Elo. pose proof aceil_loX as HCL. acb.
    pose proof (xstat_of_mstatics _ _ ST) as XS.
    destruct (ahm_of _ _ _ RH) as [TB AH].
    pose proof (exitA_of mem TB tid can XS AH (mst_out _ _ _ _ _ _ ST) (xk_atxU_of _ (mst_cells _ _ _ _ _ _ ST)) (mst_tid _ _ _ _ _ _ ST) (mst_can _ _ _ _ _ _ ST)) as XA.
    destruct ST as [INV STK AC RELRO [G1 G2] CELLS OUT [TID Ht] [CAN Hc] RFS LATCH [shi [SH0 Hshi]] ABOVE FR AUX].
    apply (drv_lazy H DL s msF mo regs _ mem _ HV HA). intros Lz Sz Zr OK RS _.
    apply (as_refused Lz Sz Zr regs mem msF mo (Z_to_bv 64 (bv_unsigned sp0 - 128)) can tid TB);
      [| | exact R4 | exact OK | exact RS | exact Hfd2].
    -   split.
      + exact R2.
      + rewrite u_small by lia. rewrite <- Zminus_mod_idemp_l, SP16. reflexivity.
      + unfold ASP_LO. rewrite u_small by lia. lia.
      + unfold ASP_HI. rewrite u_small by lia. lia.
      + eapply astk_stk_ok; [exact STK | unfold RF_FR; rewrite u_small by lia; lia | rewrite u_small by lia; lia | unfold RF_FR; lia | lia].
      + exact (amem_inv_ro_none _ INV).
      + exact RELRO.
      + apply rf_cells_of; assumption.
      + exact CAN.
      + exact Hc.
      + intros a Ha. rewrite u_small in Ha by lia.
        apply (stack0_qsh0 mem lo shi (bv_unsigned sp0 - 128) SH0 ltac:(lia) ltac:(lia)). rewrite ASHADOW_BASE_val. lia.
    - exact XA.
  Qed.
End Exit.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
