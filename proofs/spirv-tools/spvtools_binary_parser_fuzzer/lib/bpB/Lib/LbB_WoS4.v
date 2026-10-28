(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame BCells BStep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 BsWalk RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_SR LbB_Conv.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_PrsStmt LbB_StateStmt LbB_Own LbB_HKit LbB_HStKit LbB_ContStmt LbB_ResvB.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_WoGen LbB_WoDefs LbB_WoKit LbB_WoKit3 LbB_WoSt LbB_WoCut LbB_WoE0 LbB_WoVec LbB_WoT2 LbB_WoR6 LbB_WoG LbB_WoRv.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section WoS4.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHb : asan_rt_hyps_bp H.
  Let HB := rt_bp_base H HHb.
  Hypothesis TRO : trace_ok (as_TR H) APC0_FREE [RESV_OPND_DEL_RA].
  Hypothesis TRW : trace_ok (as_TR H) APC0_FREE [rv_del_ra RESV_W32].
  Hypothesis TRT : trace_ok (as_TR H) APC0_FREE [rv_del_ra RESV_TYP].

  Ltac mpres_chain :=
    repeat match goal with
    | |- as_MPRES H ?a ?a => apply (ah_mpres_refl H HB)
    | K : as_MPRES H ?a ?b |- as_MPRES H ?a ?c => apply (ah_mpres_trans H HB a b c K)
    end.

  Definition wtc (e : went H) (ff : Z) (m : mem) : Prop :=
       rw_cells asegs m (wS1 e) [C8 (Z_to_bv 64 (ff + 3360)); C8 (Z_to_bv 64 ff)]
    /\ rw_cells asegs m (wS1 e + 40) [C8 (Z_to_bv 64 0x7fff8000)]
    /\ rw_cells asegs m (wS1 e + 56) [C8 (Z_to_bv 64 (ff + 3376))]
    /\ rw_cells asegs m (ff + 3408) [C8 (Z_to_bv 64 0)]
    /\ wr_at asegs m (sh ff) 476.

  Definition wtl (e : went H) (ff fp : Z) (XS : list (Z * Z)) (s : as_St H) (LB LBs LBt : list block) (m : mem) (cP : stateC)
      : Prop :=
       winv H e ff fp XS s LB m /\ wtc e ff m
    /\ state_repA LB m (ff + 3504) cP /\ state_sh m cP
    /\ Permutation (lbl LBs) (state_blocks cP) /\ (forall p n, In (p, n) (state_blocks cP) -> n <= 2 ^ 40)
    /\ Permutation LB (w_LB e ++ LBs ++ LBt)
    /\ lb_own (LBt ++ LBs) m /\ List.NoDup (map blk_id (LBt ++ LBs))
    /\ addressable m (ff + 3056) 240 /\ addressable m (ff + 3456) 288.

  Lemma wtl_incl : forall (e : went H) ff fp XS s LB LBs LBt m cP, wtl e ff fp XS s LB LBs LBt m cP ->
    (forall b, In b (LBt ++ LBs) -> In b LB) /\ (forall b, In b (w_LB e) -> In b LB)
    /\ (forall p n, In (p, n) (state_blocks cP) -> In (p, n) (lbl LB)).
  Proof.
    intros e ff fp XS s LB LBs LBt m cP (_ & _ & _ & _ & PB & _ & PL & _).
    split; [|split].
    - intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PL|]. apply in_or_app. right.
      apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [right | left]; exact Hb.
    - intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PL|]. apply in_or_app. left. exact Hb.
    - intros p n Hin. assert (L : In (p, n) (lbl LBs)) by (eapply Permutation_in; [apply Permutation_sym; exact PB | exact Hin]).
      destruct (lbl_in_inv _ _ _ L) as (q & Hq). apply (lbl_in _ q).
      eapply Permutation_in; [apply Permutation_sym; exact PL|]. apply in_or_app. right. apply in_or_app. left. exact Hq.
  Qed.

  Lemma wtc_rv : forall (e : went H) ff fp XS s LB m m' v,
    wpre H e -> winv H e ff fp XS s LB m -> xpres H LB (wS1 e) [(v, v + 24)] m m' -> ff + 3224 <= v -> v + 24 <= ff + 3296 ->
    wtc e ff m -> wtc e ff m'.
  Proof.
    intros e ff fp XS s LB m m' v HP HI XP V1 V2 (C1 & C2 & C3 & C4 & W).
    pose proof (wframe_bounds H e ff fp XS s LB m HP HI) as (F0 & F64 & FLO & FH & FL & FS & SH1 & SH2 & S1L & S1SP & SPH & LOS1).
    unfold WO_FLAGP, AINTRIN_STACK in *.
    assert (FX : Forall (fun iv : Z * Z => ff <= fst iv /\ snd iv <= ff + 4096) [(v, v + 24)])
      by (apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]).
    split; [|split; [|split; [|split]]].
    - eapply (wrv_xs1 H e ff fp XS s LB LB m m' [(v, v + 24)]); [exact HP | exact HI | exact XP | exact C1 | lia
        | apply Forall_cons; [cbn; lia | apply Forall_nil]].
    - eapply (wrv_xs1 H e ff fp XS s LB LB m m' [(v, v + 24)]); [exact HP | exact HI | exact XP | exact C2 | lia
        | apply Forall_cons; [cbn; lia | apply Forall_nil]].
    - eapply (wrv_xs1 H e ff fp XS s LB LB m m' [(v, v + 24)]); [exact HP | exact HI | exact XP | exact C3 | lia
        | apply Forall_cons; [cbn; lia | apply Forall_nil]].
    - eapply (wrv_xcells H e ff fp XS s LB LB m m' [(v, v + 24)]); [exact HP | exact HI | exact XP | exact C4 | lia | cbn; lia
        | apply Forall_cons; [cbn; lia | apply Forall_nil]].
    - replace (sh ff) with (sh ff + 0) by lia. replace (sh ff) with (sh ff + 0) in W by lia.
      exact (wrv_xshwr H e ff fp XS s LB LB m m' [(v, v + 24)] 0 476 HP HI XP W ltac:(lia) ltac:(lia) ltac:(lia) FX).
  Qed.

  Lemma wtl_rv : forall (e : went H) ff fp XS s s' LB LBs LBt m m' cP v (pid : bptr) b' n,
    wpre H e -> wtl e ff fp XS s LB LBs LBt m cP -> winv H e ff fp XS s' ((pid, b', n) :: LB) m' ->
    xpres H LB (wS1 e) [(v, v + 24)] m m' -> ff + 3224 <= v -> v + 24 <= ff + 3296 ->
    lb_own ((pid, b', n) :: LBt ++ LBs) m' -> List.NoDup (map blk_id ((pid, b', n) :: LBt ++ LBs)) ->
    wtl e ff fp XS s' ((pid, b', n) :: LB) LBs ((pid, b', n) :: LBt) m' cP.
  Proof.
    intros e ff fp XS s s' LB LBs LBt m m' cP v pid b' n HP W HI' XP V1 V2 OWN' ND'.
    destruct (wtl_incl e ff fp XS s LB LBs LBt m cP W) as (OINC & INC & BLP).
    destruct W as (HI & WTC & RP & SP & PB & BN & PL & OWN & ND & ADT & ADP).
    assert (FX : Forall (fun iv : Z * Z => ff <= fst iv /\ snd iv <= ff + 4096) [(v, v + 24)])
      by (apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]).
    destruct (wrv_xstate H HHb e ff fp XS s LB s LB ((pid, b', n) :: LB) m m' [(v, v + 24)] (ff + 3504) cP HP HI
                (winv_rh H _ _ _ _ _ _ _ HI) XP FX
                ltac:(apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]) ltac:(lia) ltac:(lia)
                ltac:(intros p n0 Hin; split; [exact (BLP p n0 Hin) | cbn [lbl map]; right; exact (BLP p n0 Hin)])
                RP SP) as [RP' SP'].
    split; [exact HI'|]. split; [exact (wtc_rv e ff fp XS s LB m m' v HP HI XP V1 V2 WTC)|].
    split; [exact RP'|]. split; [exact SP'|]. split; [exact PB|]. split; [exact BN|].
    split; [rewrite PL; rewrite !app_assoc; apply Permutation_middle|].
    split; [exact OWN'|]. split; [exact ND'|].
    split; [exact (wrv_xaddr H e ff fp XS s LB LB m m' [(v, v + 24)] (ff + 3056) 240 HP HI XP ADT ltac:(lia)
             ltac:(unfold WO_FLAGP; lia) FX)|].
    exact (wrv_xaddr H e ff fp XS s LB LB m m' [(v, v + 24)] (ff + 3456) 288 HP HI XP ADP ltac:(lia)
             ltac:(unfold WO_FLAGP; lia) FX).
  Qed.

  Lemma wtst0_rv : forall (e : went H) ff fp XS s LB m m' v v1 v2 v3,
    wpre H e -> winv H e ff fp XS s LB m -> xpres H LB (wS1 e) [(v, v + 24)] m m' ->
    ff + 3224 <= v -> v + 24 <= ff + 3296 -> wtst0 ff m v1 v2 v3 ->
    rw_cells asegs m' (ff + 3056) [CB 46 (poison_bytes 46 0)] /\ st_maps_cells m' (ff + 3056).
  Proof.
    intros e ff fp XS s LB m m' v v1 v2 v3 HP HI XP V1 V2 TS.
    destruct TS as (C0 & TM & _). unfold st_maps_cells in TM. destruct TM as (M1 & M2 & M3 & M4 & M5 & M6).
    assert (FD : forall A k, A + k <= ff + 3224 -> Forall (fun iv : Z * Z => A + k <= fst iv \/ snd iv <= A) [(v, v + 24)])
      by (intros A k K; apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]).
    split; [|unfold st_maps_cells; refine (conj _ (conj _ (conj _ (conj _ (conj _ _)))))];
      (eapply (wrv_xcells H e ff fp XS s LB LB m m' [(v, v + 24)]); [exact HP | exact HI | exact XP | first [exact C0 | exact M1 | exact M2 | exact M3 | exact M4 | exact M5 | exact M6]
        | lia | cbn [cells_size csize Z.of_nat Pos.of_succ_nat Pos.succ]; lia
        | apply FD; cbn [cells_size csize Z.of_nat Pos.of_succ_nat Pos.succ]; lia]).
  Qed.

  Lemma seg_on7 : forall (Q : config -> Prop) (e : went H) ff fp XS s LB LBs LBt m msF mo cP
      (x5 x6 x7 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s8 s10 s11 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32),
    wpre H e -> wtl e ff fp XS s LB LBs LBt m cP ->
    wtst0 ff m Z24 Z24 Z24 ->
    lb_small LB + 700 <= RT_SMALL_MAX -> Z.of_nat (length LB) + 3 <= RT_CNT_MAX -> nlarge LB <= RT_LARGE_MAX ->
    as_AKREL H s (mkCfg msF mo) -> 0 <= as_AL H s ->
    as_VIS H s msF = MS (mkR (Z_to_bv 64 WO_AN7_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) x5 x6 x7
                           (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e)) (Z_to_bv 64 (ff + 3224)) (Z_to_bv 64 25)
                           x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 (Z_to_bv 64 (ff + 3248)) s8 (Z_to_bv 64 (ff + 3272)) s10 s11
                           x28 x29 x30 x31)
                        F (Z_to_bv 64 RESV_OPND_ENTRY) fc None m (seg_rom asegs) ->
    (forall msF' mo' s' (p7 : bptr) b7 m' (y5 y6 y7 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
       as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' -> as_AL H s' >= as_AL H s ->
       wtl e ff fp XS s' ((p7, b7, 500) :: LB) LBs ((p7, b7, 500) :: LBt) m' cP ->
       wtst0 ff m' (vtrip b7 500) Z24 Z24 -> wblk m' b7 500 -> ~ In p7 (map blk_id LB) ->
       as_VIS H s' msF' = MS (mkR (Z_to_bv 64 WO_AN8_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) y5 y6 y7
                                (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e)) (Z_to_bv 64 (ff + 3248)) (Z_to_bv 64 25)
                                y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 (Z_to_bv 64 (ff + 3248)) s8 (Z_to_bv 64 (ff + 3272)) s10 s11
                                y28 y29 y30 y31)
                             F (Z_to_bv 64 (rv_entry RESV_W32)) fc None m' (seg_rom asegs) ->
       as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros Q e ff fp XS s LB LBs LBt m msF mo cP x5 x6 x7 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s8 s10 s11 x28 x29 x30 x31 F fc
      HP W TS LS LC LL KR AL0 VIS K.
    destruct (wtl_incl e ff fp XS s LB LBs LBt m cP W) as (OINC & INC & BLP).
    pose proof W as (HI & WTC & RP & SP & PB & BN & PL & OWN & ND & ADT & ADP).
    destruct (wrv_fsb H e ff fp XS s LB m HP HI) as (G1 & G2 & F64 & FC & FAPP).
    pose proof TS as (TC & TM & TV1 & TV2 & TV3).
    assert (ADv : addressable m (ff + 3224) 24).
    { replace (ff + 3224) with (ff + 3056 + 168) by lia.
      apply (addressable_sub8 m (ff + 3056) 240 168 24 ADT); [reflexivity | reflexivity | reflexivity | lia | lia | lia]. }
    eapply (wrv_opnd H HHb e ff fp XS s LB (LBt ++ LBs) m msF mo Q (Z_to_bv 64 WO_AN7_RA) x5 x6 x7
              (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e)) x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 (Z_to_bv 64 (ff + 3248)) s8
              (Z_to_bv 64 (ff + 3272)) s10 s11 x28 x29 x30 x31 (ff + 3224) F fc HP HI INC VIS KR
              ltac:(rewrite HLib.u64_of_Z by (unfold WO_AN7_RA; lia); unfold WO_AN7_RA; reflexivity) AL0 TV1 ADv
              ltac:(lia) ltac:(unfold WO_FLAGP; lia) ltac:(clear - F64; Z.div_mod_to_equations; lia) OWN OINC ND
              ltac:(lia) ltac:(lia) LL TRO).
    intros msF' mo' s' pid b' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
      VIS' KR' MP' HI' XP NI VEC ABR SHB AD' WR' OWN' ND' AL'.
    rewrite (ret_pc_even WO_AN7_RA ltac:(unfold WO_AN7_RA; lia) eq_refl) in VIS'.
    pose proof (wtl_rv e ff fp XS s s' LB LBs LBt m m' cP (ff + 3224) pid b' 500 HP W HI' XP ltac:(lia) ltac:(lia) OWN' ND') as W'.
    assert (FX : Forall (fun iv : Z * Z => ff <= fst iv /\ snd iv <= ff + 4096) [(ff + 3224, ff + 3224 + 24)])
      by (apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]).
    destruct (wtst0_rv e ff fp XS s LB m m' (ff + 3224) _ _ _ HP HI XP ltac:(lia) ltac:(lia) TS) as (TC' & TM').
    assert (TS' : wtst0 ff m' (vtrip b' 500) Z24 Z24).
    { split; [exact TC'|]. split; [exact TM'|]. split; [|split].
      - exact (wrv_vtrip_opnd _ m' (ff + 3224) b' VEC WR').
      - eapply (wrv_xcells H e ff fp XS s LB LB m m' [(ff + 3224, ff + 3224 + 24)]); [exact HP | exact HI | exact XP | exact TV2
          | lia | cbn; lia | apply Forall_cons; [cbn; lia | apply Forall_nil]].
      - eapply (wrv_xcells H e ff fp XS s LB LB m m' [(ff + 3224, ff + 3224 + 24)]); [exact HP | exact HI | exact XP | exact TV3
          | lia | cbn; lia | apply Forall_cons; [cbn; lia | apply Forall_nil]]. }
    pose proof (wrv_wblk (LBt ++ LBs) m' pid b' 500 OWN' SHB) as B7.
    eapply (ahh_evt_then H HB (wv1_post H e ff m' s2 s3 s4 s5 s6 s8 (Z_to_bv 64 (ff + 3272)) s10 s11 F fc) Q s' msF' _ mo');
      [exact KR' | exact VIS' | exact (wv1 H e ff fp XS s' ((pid, b', 500) :: LB) m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7'
                                   s2 s3 s4 s5 s6 s8 (Z_to_bv 64 (ff + 3272)) s10 s11 t3' t4' t5' t6' F fc HP HI') |].
    intros msF2 mo2 KR2 MP2 (y5 & y6 & y7 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & EQ).
    eapply (K msF2 mo2 s' pid b' m' y5 y6 y7 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31);
      [exact KR2 | mpres_chain | exact AL' | exact W' | exact TS' | exact B7 | exact NI | exact EQ].
  Qed.

  Lemma seg_on8 : forall (Q : config -> Prop) (e : went H) ff fp XS s LB LBs LBt m msF mo cP (p7 : bptr) b7
      (x5 x6 x7 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s8 s10 s11 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32),
    wpre H e -> wtl e ff fp XS s LB LBs LBt m cP ->
    wtst0 ff m (vtrip b7 500) Z24 Z24 -> In (p7, b7, 500) LB -> wblk m b7 500 ->
    lb_small LB + 200 <= RT_SMALL_MAX -> Z.of_nat (length LB) + 2 <= RT_CNT_MAX -> nlarge LB <= RT_LARGE_MAX ->
    as_AKREL H s (mkCfg msF mo) -> 0 <= as_AL H s ->
    as_VIS H s msF = MS (mkR (Z_to_bv 64 WO_AN8_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) x5 x6 x7
                           (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e)) (Z_to_bv 64 (ff + 3248)) (Z_to_bv 64 25)
                           x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 (Z_to_bv 64 (ff + 3248)) s8 (Z_to_bv 64 (ff + 3272)) s10 s11
                           x28 x29 x30 x31)
                        F (Z_to_bv 64 (rv_entry RESV_W32)) fc None m (seg_rom asegs) ->
    (forall msF' mo' s' (p8 : bptr) b8 m' (y5 y6 y7 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
       as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' -> as_AL H s' >= as_AL H s ->
       wtl e ff fp XS s' ((p8, b8, 100) :: LB) LBs ((p8, b8, 100) :: LBt) m' cP ->
       wtst0 ff m' (vtrip b7 500) (vtrip b8 100) Z24 -> wblk m' b7 500 -> wblk m' b8 100 -> ~ In p8 (map blk_id LB) ->
       as_VIS H s' msF' = MS (mkR (Z_to_bv 64 WO_AN9_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) y5 y6 y7
                                (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e)) (Z_to_bv 64 (ff + 3272)) (Z_to_bv 64 25)
                                y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 (Z_to_bv 64 (ff + 3248)) s8 (Z_to_bv 64 (ff + 3272)) s10 s11
                                y28 y29 y30 y31)
                             F (Z_to_bv 64 (rv_entry RESV_TYP)) fc None m' (seg_rom asegs) ->
       as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros Q e ff fp XS s LB LBs LBt m msF mo cP p7 b7 x5 x6 x7 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s8 s10 s11 x28 x29 x30 x31 F fc
      HP W TS B7IN B7 LS LC LL KR AL0 VIS K.
    destruct (wtl_incl e ff fp XS s LB LBs LBt m cP W) as (OINC & INC & BLP).
    pose proof W as (HI & WTC & RP & SP & PB & BN & PL & OWN & ND & ADT & ADP).
    destruct (wrv_fsb H e ff fp XS s LB m HP HI) as (G1 & G2 & F64 & FC & FAPP).
    pose proof TS as (TC & TM & TV1 & TV2 & TV3).
    assert (ADv : addressable m (ff + 3248) 24).
    { replace (ff + 3248) with (ff + 3056 + 192) by lia.
      apply (addressable_sub8 m (ff + 3056) 240 192 24 ADT); [reflexivity | reflexivity | reflexivity | lia | lia | lia]. }
    eapply (wrv_w32 H HHb e ff fp XS s LB (LBt ++ LBs) m msF mo Q (Z_to_bv 64 WO_AN8_RA) x5 x6 x7
              (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e)) x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 (Z_to_bv 64 (ff + 3248)) s8
              (Z_to_bv 64 (ff + 3272)) s10 s11 x28 x29 x30 x31 (ff + 3248) F fc HP HI INC VIS KR
              ltac:(rewrite HLib.u64_of_Z by (unfold WO_AN8_RA; lia); unfold WO_AN8_RA; reflexivity) AL0 TV2 ADv
              ltac:(lia) ltac:(unfold WO_FLAGP; lia) ltac:(clear - F64; Z.div_mod_to_equations; lia) OWN OINC ND
              ltac:(lia) ltac:(lia) LL TRW).
    intros msF' mo' s' pid b' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
      VIS' KR' MP' HI' XP NI VEC ABR SHB AD' WR' OWN' ND' AL'.
    rewrite (ret_pc_even WO_AN8_RA ltac:(unfold WO_AN8_RA; lia) eq_refl) in VIS'.
    pose proof (wtl_rv e ff fp XS s s' LB LBs LBt m m' cP (ff + 3248) pid b' 100 HP W HI' XP ltac:(lia) ltac:(lia) OWN' ND') as W'.
    assert (FX : Forall (fun iv : Z * Z => ff <= fst iv /\ snd iv <= ff + 4096) [(ff + 3248, ff + 3248 + 24)])
      by (apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]).
    destruct (wtst0_rv e ff fp XS s LB m m' (ff + 3248) _ _ _ HP HI XP ltac:(lia) ltac:(lia) TS) as (TC' & TM').
    assert (TS' : wtst0 ff m' (vtrip b7 500) (vtrip b' 100) Z24).
    { split; [exact TC'|]. split; [exact TM'|]. split; [|split].
      - eapply (wrv_xcells H e ff fp XS s LB LB m m' [(ff + 3248, ff + 3248 + 24)]); [exact HP | exact HI | exact XP | exact TV1
          | lia | cbn; lia | apply Forall_cons; [cbn; lia | apply Forall_nil]].
      - exact (wrv_vtrip32 _ m' (ff + 3248) b' VEC WR').
      - eapply (wrv_xcells H e ff fp XS s LB LB m m' [(ff + 3248, ff + 3248 + 24)]); [exact HP | exact HI | exact XP | exact TV3
          | lia | cbn; lia | apply Forall_cons; [cbn; lia | apply Forall_nil]]. }
    pose proof (wrv_xblk H HHb e ff fp XS s LB s LB m m' [(ff + 3248, ff + 3248 + 24)] p7 b7 500 HP HI (winv_rh H _ _ _ _ _ _ _ HI)
                  XP FX B7IN B7) as B7'.
    pose proof (wrv_wblk (LBt ++ LBs) m' pid b' 100 OWN' SHB) as B8.
    eapply (ahh_evt_then H HB (wv2_post H e ff m' s2 s3 s4 s5 s6 (Z_to_bv 64 (ff + 3248)) s8 s10 s11 F fc) Q s' msF' _ mo');
      [exact KR' | exact VIS' | exact (wv2 H e ff fp XS s' ((pid, b', 100) :: LB) m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7'
                                   s2 s3 s4 s5 s6 (Z_to_bv 64 (ff + 3248)) s8 s10 s11 t3' t4' t5' t6' F fc HP HI') |].
    intros msF2 mo2 KR2 MP2 (y5 & y6 & y7 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & EQ).
    eapply (K msF2 mo2 s' pid b' m' y5 y6 y7 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31);
      [exact KR2 | mpres_chain | exact AL' | exact W' | exact TS' | exact B7' | exact B8 | exact NI | exact EQ].
  Qed.

  Lemma seg_on9 : forall (Q : config -> Prop) (e : went H) ff fp XS s LB LBs LBt m msF mo cP (p7 p8 : bptr) b7 b8
      (x5 x6 x7 x12 x13 x14 x15 x16 x17 s3 s4 s5 s8 s10 s11 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32),
    wpre H e -> wtl e ff fp XS s LB LBs LBt m cP ->
    wtst0 ff m (vtrip b7 500) (vtrip b8 100) Z24 -> In (p7, b7, 500) LB -> wblk m b7 500 -> In (p8, b8, 100) LB -> wblk m b8 100 ->
    lb_small LB + 100 <= RT_SMALL_MAX -> Z.of_nat (length LB) + 1 <= RT_CNT_MAX -> nlarge LB <= RT_LARGE_MAX ->
    as_AKREL H s (mkCfg msF mo) -> 0 <= as_AL H s ->
    as_VIS H s msF = MS (mkR (Z_to_bv 64 WO_AN9_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) x5 x6 x7
                           (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e)) (Z_to_bv 64 (ff + 3272)) (Z_to_bv 64 25)
                           x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (ff + 3056)) s3 s4 s5 (Z_to_bv 64 (ff + 3504))
                           (Z_to_bv 64 (ff + 3248)) s8 (Z_to_bv 64 (ff + 3272)) s10 s11 x28 x29 x30 x31)
                        F (Z_to_bv 64 (rv_entry RESV_TYP)) fc None m (seg_rom asegs) ->
    (forall msF' mo' s' (p9 : bptr) b9 m' (y5 y6 y7 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
       as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' -> as_AL H s' >= as_AL H s ->
       wtl e ff fp XS s' ((p9, b9, 100) :: LB) LBs ((p9, b9, 100) :: LBt) m' cP ->
       wtst0 ff m' (vtrip b7 500) (vtrip b8 100) (vtrip b9 100) -> wblk m' b7 500 -> wblk m' b8 100 -> wblk m' b9 100 ->
       ~ In p9 (map blk_id LB) ->
       as_VIS H s' msF' = MS (mkR (Z_to_bv 64 WO_MVA2_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) y5 y6 y7
                                (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e)) (Z_to_bv 64 (ff + 3504)) (Z_to_bv 64 (ff + 3056))
                                y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (ff + 3056)) s3 s4 s5 (Z_to_bv 64 (ff + 3504))
                                (Z_to_bv 64 (ff + 3248)) s8 (Z_to_bv 64 (ff + 3272)) s10 s11 y28 y29 y30 y31)
                             F (Z_to_bv 64 AST_MVA) fc None m' (seg_rom asegs) ->
       as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros Q e ff fp XS s LB LBs LBt m msF mo cP p7 p8 b7 b8 x5 x6 x7 x12 x13 x14 x15 x16 x17 s3 s4 s5 s8 s10 s11 x28 x29 x30 x31 F fc
      HP W TS B7IN B7 B8IN B8 LS LC LL KR AL0 VIS K.
    destruct (wtl_incl e ff fp XS s LB LBs LBt m cP W) as (OINC & INC & BLP).
    pose proof W as (HI & WTC & RP & SP & PB & BN & PL & OWN & ND & ADT & ADP).
    destruct (wrv_fsb H e ff fp XS s LB m HP HI) as (G1 & G2 & F64 & FC & FAPP).
    pose proof TS as (TC & TM & TV1 & TV2 & TV3).
    assert (ADv : addressable m (ff + 3272) 24).
    { replace (ff + 3272) with (ff + 3056 + 216) by lia.
      apply (addressable_sub8 m (ff + 3056) 240 216 24 ADT); [reflexivity | reflexivity | reflexivity | lia | lia | lia]. }
    eapply (wrv_typ H HHb e ff fp XS s LB (LBt ++ LBs) m msF mo Q (Z_to_bv 64 WO_AN9_RA) x5 x6 x7
              (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (ff + 3056)) s3 s4 s5
              (Z_to_bv 64 (ff + 3504)) (Z_to_bv 64 (ff + 3248)) s8
              (Z_to_bv 64 (ff + 3272)) s10 s11 x28 x29 x30 x31 (ff + 3272) F fc HP HI INC VIS KR
              ltac:(rewrite HLib.u64_of_Z by (unfold WO_AN9_RA; lia); unfold WO_AN9_RA; reflexivity) AL0 TV3 ADv
              ltac:(lia) ltac:(unfold WO_FLAGP; lia) ltac:(clear - F64; Z.div_mod_to_equations; lia) OWN OINC ND
              ltac:(lia) ltac:(lia) LL TRT).
    intros msF' mo' s' pid b' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
      VIS' KR' MP' HI' XP NI VEC ABR SHB AD' WR' OWN' ND' AL'.
    rewrite (ret_pc_even WO_AN9_RA ltac:(unfold WO_AN9_RA; lia) eq_refl) in VIS'.
    pose proof (wtl_rv e ff fp XS s s' LB LBs LBt m m' cP (ff + 3272) pid b' 100 HP W HI' XP ltac:(lia) ltac:(lia) OWN' ND') as W'.
    assert (FX : Forall (fun iv : Z * Z => ff <= fst iv /\ snd iv <= ff + 4096) [(ff + 3272, ff + 3272 + 24)])
      by (apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]).
    destruct (wtst0_rv e ff fp XS s LB m m' (ff + 3272) _ _ _ HP HI XP ltac:(lia) ltac:(lia) TS) as (TC' & TM').
    assert (TS' : wtst0 ff m' (vtrip b7 500) (vtrip b8 100) (vtrip b' 100)).
    { split; [exact TC'|]. split; [exact TM'|]. split; [|split].
      - eapply (wrv_xcells H e ff fp XS s LB LB m m' [(ff + 3272, ff + 3272 + 24)]); [exact HP | exact HI | exact XP | exact TV1
          | lia | cbn; lia | apply Forall_cons; [cbn; lia | apply Forall_nil]].
      - eapply (wrv_xcells H e ff fp XS s LB LB m m' [(ff + 3272, ff + 3272 + 24)]); [exact HP | exact HI | exact XP | exact TV2
          | lia | cbn; lia | apply Forall_cons; [cbn; lia | apply Forall_nil]].
      - exact (wrv_vtrip32 _ m' (ff + 3272) b' VEC WR'). }
    pose proof (wrv_xblk H HHb e ff fp XS s LB s LB m m' [(ff + 3272, ff + 3272 + 24)] p7 b7 500 HP HI (winv_rh H _ _ _ _ _ _ _ HI)
                  XP FX B7IN B7) as B7'.
    pose proof (wrv_xblk H HHb e ff fp XS s LB s LB m m' [(ff + 3272, ff + 3272 + 24)] p8 b8 100 HP HI (winv_rh H _ _ _ _ _ _ _ HI)
                  XP FX B8IN B8) as B8'.
    pose proof (wrv_wblk (LBt ++ LBs) m' pid b' 100 OWN' SHB) as B9.
    eapply (ahh_evt_then H HB (wv3_post H e ff m' s3 s4 s5 (Z_to_bv 64 (ff + 3248)) s8 (Z_to_bv 64 (ff + 3272)) s10 s11 F fc)
              Q s' msF' _ mo');
      [exact KR' | exact VIS' | exact (wv3 H e ff fp XS s' ((pid, b', 100) :: LB) m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7'
                                   s3 s4 s5 (Z_to_bv 64 (ff + 3248)) s8 (Z_to_bv 64 (ff + 3272)) s10 s11 t3' t4' t5' t6' F fc HP HI') |].
    intros msF2 mo2 KR2 MP2 (y5 & y6 & y7 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & EQ).
    eapply (K msF2 mo2 s' pid b' m' y5 y6 y7 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31);
      [exact KR2 | mpres_chain | exact AL' | exact W' | exact TS' | exact B7' | exact B8' | exact B9 | exact NI | exact EQ].
  Qed.

End WoS4.
