(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCLemmas1 CmpMem BzSepTac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpCutSM CmpCutSmA CmpCutSD CmpSdKit CmpSdTac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpArith.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCNumZ BzCLemmasSd BzCLemmasSd2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpArith2 BzWalkArith2 BzWalkArith4.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From Stdlib Require Lia. Unset Lia Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut6.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.
Local Ltac U.Bz.BzTac.mlia ::= CmpFast.mlia_fast.
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac U.Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
Local Ltac lia ::= CmpLiaC.lia_c.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpStEq.
Local Ltac U.Bz.BzTac.st_eq ::= CmpStEq.st_eq_fast.
Local Ltac simpl_arr_sizes ::= CmpFast.sas10_all.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpArith2.CmpSdArith OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCLemmasSd2.BzCLemmasSd3.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCHuff BzCHuffF1.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1.BzCFactsHm.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import UKit CmpCut0 BzCFactsSmB CmpSmKit2 CmpSmKit20 S0_cmp_hmZ.

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section SDK.
  Variables (cx : cctx) (e : est) (Q : machine_state -> Prop).
  Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (sv : word).
  Variable SP : Z.
  Hypothesis CX : cctx_ok cx. Hypothesis IMG : cctx_img S0C cx.
  Hypothesis CEP : (CEIL <= SP)%Z. Hypothesis PHI : (SP + 1200 <= 18446744073709551616)%Z.
  Notation E := (c_E cx). Notation J := (c_J cx).
  Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e).
  Hypothesis HA : (3 <= A <= 258)%Z. Hypothesis HNG : (2 <= nG <= 6)%Z. Hypothesis HM : (1 <= nMTF <= (NBLOCKMAX + 20))%Z.
  Notation cSP := (Z_to_bv 64 SP).
  Notation NOT z := (Z_to_bv 64 (18446744073709551615 - z)).
  Notation RIT ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6 :=
    (mkR ra cSP gp tp t0 t1 t2 (Z_to_bv 64 E) (Z_to_bv 64 257) a0 a1 a2 a3 a4 a5 a6 a7
         s2 (Z_to_bv 64 1548) (Z_to_bv 64 (258 * nG)) s5 (Z_to_bv 64 (4 * A)) s7 s8 (NOT (E + 37708)) s10 s11 t3 t4 t5 t6).
  Notation Wk := [(E + 37708, E + 39256); (SP - HM_FRAME, SP)]%Z.
  Ltac openCX :=
    let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb).

  Lemma U0_sm_mkl : forall (n t : nat) (s : sits) (rfe : zarr) (lo : Z) (m mf : word -> option byte)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s10 s11 t3 t4 t5 t6 : word),
    (Z.of_nat t + Z.of_nat n = nG)%Z -> (1 <= n)%nat ->
    (forall t', (Z.of_nat t' < nG)%Z ->
       hm_facts (ml_len e s t') rfe (258 * Z.of_nat t') (258 * Z.of_nat t') A /\
       ml_len e s (S t') = hs_len (hbMakeCodeLengths (ml_len e s t') rfe znew znew znew (258 * Z.of_nat t') (258 * Z.of_nat t') A 17)) ->
    (forall tt v, (0 <= tt < nG)%Z -> (0 <= v < A)%Z -> zdef rfe (258 * tt + v) = true /\ (0 <= zget rfe (258 * tt + v) <= nMTF)%Z) ->
    u8arr s0segs m (E + 37708) (ovb (ml_len e s t) (jseg J 37708 1548) 1548) ->
    u32arr s0segs m (E + 45448) (ovw rfe (jseg J 45448 6192) 1548) ->
    cimg_mem S0C m sv -> mem_inv s0segs m ->
    stk s0segs m lo SP -> (lo + HM_FRAME <= SP)%Z -> (CEIL <= lo)%Z -> (SP mod 16 = 0)%Z ->
    munch Wk mf m -> wmono s0segs mf m ->
    frdW s0segs Wk mf (SP + 888) [C8 (Z_to_bv 64 (1032 * nG))] ->
    frdW s0segs Wk mf (SP + 944) [C8 (NOT (E + 45448))] ->
    frdW s0segs Wk mf (SP + 952) [C8 (Z_to_bv 64 (E + 45448))] ->
    frdW s0segs Wk mf (SP + 960) [C8 (Z_to_bv 64 (E + 37708))] ->
    frdW s0segs Wk mf (SP + 968) [C8 (Z_to_bv 64 A)] ->
    (forall m' (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      u8arr s0segs m' (E + 37708) (ovb (ml_len e s (t + n)) (jseg J 37708 1548) 1548) ->
      u32arr s0segs m' (E + 45448) (ovw rfe (jseg J 45448 6192) 1548) ->
      cimg_mem S0C m' sv -> mem_inv s0segs m' -> stk s0segs m' lo SP ->
      munch Wk mf m' -> wmono s0segs mf m' ->
      evt s0segs Q (MS (RIT ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (1032 * nG)) (Z_to_bv 64 (258 * nG - 1548)) s7 s8 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x1b3bc) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RIT ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (1032 * Z.of_nat t)) (Z_to_bv 64 (258 * Z.of_nat t - 1548)) s7 s8 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x1b36c) fc None m (seg_rom s0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros t s rfe lo m mf ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s10 s11 t3 t4 t5 t6 Ht Hn MLF RFF LEN RFQ CM MI ST STK CLO AL MU WM
           V888 V944 V952 V960 V968 K.
    openCX. unfold HM_FRAME in *. bz_ceil; bz_params; unfold CEIL in CLO, CEP.
    pose proof IMG as IMG'. unfold cctx_img, img_apart, IMG_LO3 in IMG'. cbn [ci_hi S0C] in IMG'. destruct IMG' as (IE & _). unfold ESTATE_SIZE in IE.
    pose proof (jseg_length J 37708 1548 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ6. pose proof (jseg_length J 45448 6192 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ8.
    destruct (MLF t ltac:(lia)) as [HMF EML].
    pose proof (V888 m MU) as R888. pose proof (V944 m MU) as R944. pose proof (V952 m MU) as R952.
    pose proof (V960 m MU) as R960. pose proof (V968 m MU) as R968.
    urun_to 0x23ba8%Z.
    clear R888 R944 R952 R960 R968.
    pose proof S0_hbMakeCodeLengths as HBS. unfold hbMakeCodeLengths_spec in HBS. cbn [ci_segs ci_hbMakeCodeLengths ci_hi S0C] in HBS. unfold HM_FRAME in HBS.
    eapply evt_cut.
    { eapply (HBS _ cSP gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m (E + 37708)%Z (E + 45448)%Z (258 * Z.of_nat t)%Z (258 * Z.of_nat t)%Z A 1548%Z 1548%Z lo (ml_len e s t) rfe (jseg J 37708 1548) (jseg J 45448 6192) sv);
        [ f_equal; lia | f_equal; lia | reflexivity | reflexivity
        | exact LEN | exact RFQ | exact CM | exact MI | rewrite unsigned_lit by lia; exact ST | rewrite unsigned_lit by lia; lia | bz_ceil; bz_params; unfold CEIL; lia | rewrite unsigned_lit by lia; exact AL
        | lia | lia | lia | lia | lia | lia | bz_ceil; bz_params; unfold CEIL; lia | lia | bz_ceil; bz_params; unfold CEIL; lia
        | clear -ME; Z.div_mod_to_equations; lia
        | unfold apart; lia | unfold img_apart, IMG_LO3; cbn [ci_hi S0C]; lia | unfold img_apart, IMG_LO3; cbn [ci_hi S0C]; lia
        | intros v Hv; destruct (RFF (Z.of_nat t) v ltac:(lia) Hv) as [D R]; split; [exact D| lia]
        | exact HMF ]. }
    clear LEN MI ST. unfold hbMakeCodeLengths_post.
    intros ms' PO; destruct_exs PO. destruct PO as [EQ [MUc [WMc [MI2 [ST LEN]]]]]; subst ms'.
    rewrite (unsigned_lit SP) in MUc, ST by lia.
    lazymatch type of MUc with munch _ m ?m' =>
      pose proof (cimg_transportK0 S0C _ m m' sv eq_refl CM MUc WMc
                    ltac:(constructor; [cbn [fst snd ci_hi S0C]; unfold IMG_LO3; lia| constructor; [cbn [fst snd ci_hi S0C]; unfold IMG_LO3; lia| constructor]])) as CM';
      clear CM; transport_after_call s0segs m m' MUc WMc; clear MUc WMc; try clear m end.
    lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    rewrite <- EML in LEN.
    lazymatch goal with MU' : munch _ mf ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (V888 mm MU') as R888 end.
    urun_to 0x1b3b8%Z.
    wstep; if_cases Ke; zify_cond_z Ke.
    - enter_with (IH (S t) s rfe lo _ mf);
        [st_eq| lia| lia| exact MLF| exact RFF| exact LEN| assumption| exact CM'| exact MI2| exact ST| exact STK| exact CLO| exact AL| assumption| assumption
        | exact V888| exact V944| exact V952| exact V960| exact V968|].
      intros mm; intros *. replace (S t + n)%nat with (t + S n)%nat by lia. apply K.
    - assert (n = 0)%nat by lia. subst n. replace (t + 1)%nat with (S t) in K by lia.
      enter_with (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [st_eq| exact LEN| assumption| exact CM'| exact MI2| exact ST| assumption| assumption].
  Qed.
End SDK.
End ACeilS1.
