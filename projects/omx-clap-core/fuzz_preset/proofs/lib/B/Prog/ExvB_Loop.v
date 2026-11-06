(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Does not rest on tex_word_specX or memnorm: EXV_HYP has neither field since b29a52d6b76b / 379ec9e4a7d5. *)
(* Theorem Labs, 2026-10: fuzz_preset, image B, ex_value, segment CL (the items loop, B 0x83a60 = exv_pc 0x534):
   the COMPOSITION of the loop's pieces (ExvB_Loop_Stmt.v's cuts) into ExvB_Top.v's seg_loop, by induction on
   m >= exv_len E - ip (each pass moves the cursor past the nested value and the ','); at n = 0 the cut is vacuous
   (EXV_PRE: 32 <= dep + 0, CUT_CL: dep + 1 <= 32).
   Pieces: A1 (CL -> LK, kid fetch; ExvB_Loop_A1.v), A2 (LK -> LR / CX, key path; ExvB_Loop_A2.v), B1 (LR -> LS / CX,
   the nested ex_value; ExvB_Loop_B1.v), B2 (LS -> CL at i + 1 / CC / CX, separator and closer; ExvB_Loop_B2.v), over the
   loop's facts (ExvB_Loop_kitL.v, ExvB_Loop_pure.v), the shared call kit (ExvB_Loop_kitP.v / _kitQ.v) and ExvOpen's
   ExvB_Open_kt.v (exv_kt). The closed lemma exvB_loop (end of file) is seg_loop with EXV_HYP added.
   Numerals: 1 (DERIVED: the bound step). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Stmt ExvB_Loop_kit ExvB_Loop_Stmt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Open_kt ExvB_Loop_kitP ExvB_Loop_kitQ.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Loop_kitL ExvB_Loop_pure.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Loop_A1 ExvB_Loop_A2 ExvB_Loop_B1 ExvB_Loop_B2.
Import ListNotations.
Local Open Scope Z_scope.

#[local] Existing Instance prh_img_B.

(* ---- the composition over the four pieces' statements ---- *)
Section c. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.

Local Notation TEXT n fx := (tex_value_specX (fx := fx) (PA := PI_prog_B) B ARx SK n).
Local Notation REC n := (match n with O => True | S n' => forall fx : YK11.FPState, TEXT n' fx end).

Hypothesis PA1 : forall n m, (forall fx : YK11.FPState, CUT_LK (fx := fx) B ARx SK n m) ->
  forall fx : YK11.FPState, CUT_CLm (fx := fx) B ARx SK n m.
Hypothesis PA2 : forall n m, (forall fx : YK11.FPState, CUT_CX (fx := fx) B ARx SK n) ->
  (forall fx : YK11.FPState, CUT_LR (fx := fx) B ARx SK n m) -> forall fx : YK11.FPState, CUT_LK (fx := fx) B ARx SK n m.
Hypothesis PB1 : forall n' m, (forall fx : YK11.FPState, TEXT n' fx) ->
  (forall fx : YK11.FPState, CUT_CX (fx := fx) B ARx SK (S n')) ->
  (forall fx : YK11.FPState, CUT_LS (fx := fx) B ARx SK (S n') m) -> forall fx : YK11.FPState, CUT_LR (fx := fx) B ARx SK (S n') m.
Hypothesis PB2 : forall n m, (forall fx : YK11.FPState, CUT_CX (fx := fx) B ARx SK n) ->
  (forall fx : YK11.FPState, CUT_CC (fx := fx) B ARx SK n) ->
  (forall fx : YK11.FPState, CUT_CLm (fx := fx) B ARx SK n (m - 1)) -> forall fx : YK11.FPState, CUT_LS (fx := fx) B ARx SK n m.

(* below 0 no cursor fits *)
Lemma exvl_CLm_neg : forall n m (fx : YK11.FPState), m < 0 -> CUT_CLm (fx := fx) B ARx SK n m.
Proof.
intros n m fx Hm. unfold CUT_CLm. intros E lyc Sc Hpc Wc regs memc mdc k pos c i cap acc ip vv dlc. cbv zeta.
intros _ _ _ _ _ _ _ _ _ Hip _ _ Hb. clear - Hm Hip Hb. lia.
Qed.

(* one more pass: the bound m from m - 1 *)
Lemma exvl_CLm_all : forall n', (forall fx : YK11.FPState, TEXT n' fx) ->
  (forall fx : YK11.FPState, CUT_CX (fx := fx) B ARx SK (S n')) ->
  (forall fx : YK11.FPState, CUT_CC (fx := fx) B ARx SK (S n')) ->
  forall (k : nat) (fx : YK11.FPState), CUT_CLm (fx := fx) B ARx SK (S n') (Z.of_nat k - 1).
Proof.
intros n' HR HX HC k. induction k as [|k IH].
- intros fx. apply exvl_CLm_neg. lia.
- apply PA1. apply PA2; [exact HX|]. apply PB1; [exact HR | exact HX |]. apply PB2; [exact HX | exact HC |].
  replace (Z.of_nat (S k) - 1 - 1) with (Z.of_nat k - 1) by lia. exact IH.
Qed.

(* the cut itself *)
Lemma exvl_loop : forall n, REC n ->
  (forall fx : YK11.FPState, CUT_CX (fx := fx) B ARx SK n) -> (forall fx : YK11.FPState, CUT_CC (fx := fx) B ARx SK n) ->
  forall fx : YK11.FPState, CUT_CL (fx := fx) B ARx SK n.
Proof.
intros [|n'] HR HX HC fx; unfold CUT_CL;
  intros E lyc Sc Hpc Wc regs memc mdc k pos c i cap acc ip vv dlc; cbv zeta;
  intros Hn HPRE HB Hi1 Hc Hc2 Hdep Hacc Hcur Hip Hdl Hii HV Hdif H27 H22 H23
    S152 S88 S56 S48 S40 S80 S24 S16 S72 S8 S32 S136 S112 S128 S64 S104 S96 S120 S144.
- exfalso. pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H32 & _).
  rewrite Hn in H32. cbn [Z.of_nat] in H32. clear - H32 Hdep. lia.
- pose proof (exvl_CLm_all n' HR HX HC (Z.to_nat (exv_len E - ip + 1)) fx) as HL.
  replace (Z.of_nat (Z.to_nat (exv_len E - ip + 1)) - 1) with (exv_len E - ip) in HL
    by (clear - Hip; lia).
  exact (HL E lyc Sc Hpc Wc regs memc mdc k pos c i cap acc ip vv dlc Hn HPRE HB Hi1 Hc Hc2 Hdep Hacc Hcur Hip Hdl
    Hii (Z.le_refl _) HV Hdif H27 H22 H23
    S152 S88 S56 S48 S40 S80 S24 S16 S72 S8 S32 S136 S112 S128 S64 S104 S96 S120 S144).
Qed.
End c.

(* ---- the pieces and the kit closed: seg_loop under EXV_HYP ---- *)
Section f. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis HYP : EXV_HYP B ARx SK.

Local Ltac kfact t := first [exact (t B ARx SK HYP) | exact (t B ARx SK)].

Lemma exvl_loop_closed : forall n,
  (match n with O => True | S n' => forall fx : YK11.FPState, tex_value_specX (fx := fx) (PA := PI_prog_B) B ARx SK n' end) ->
  (forall fx : YK11.FPState, CUT_CX (fx := fx) B ARx SK n) -> (forall fx : YK11.FPState, CUT_CC (fx := fx) B ARx SK n) ->
  forall fx : YK11.FPState, CUT_CL (fx := fx) B ARx SK n.
Proof.
assert (KRUN : forall fx : YK11.FPState, KIT_RUNs (fx := fx) B ARx SK)
  by exact (exvl_kit_runs B ARx SK HYP (fun fx => exv_kt (fx := fx) B ARx SK HYP)).
assert (KEC : forall fx : YK11.FPState, KIT_EXB_CALL (fx := fx) B ARx SK) by kfact exv_kit_call.
assert (KCALL : forall fx : YK11.FPState, KIT_CALLs (fx := fx) B ARx SK)
  by (first [exact (exvl_kit_calls B ARx SK HYP KEC) | exact (exvl_kit_calls B ARx SK KEC)]).
assert (KOFS : forall fx : YK11.FPState, KIT_EXB_OF_S (fx := fx) B ARx SK) by kfact exvl_kit_exb_of_s.
assert (KNODE : forall fx : YK11.FPState, KIT_NODE (fx := fx) B ARx SK) by kfact exvl_kit_node.
assert (KKEY : forall fx : YK11.FPState, KIT_KEY (fx := fx) B ARx SK) by kfact exvl_kit_key.
assert (KCHILD : forall fx : YK11.FPState, KIT_CHILD (fx := fx) B ARx SK) by kfact exvl_kit_child.
assert (KCHAIN : forall fx : YK11.FPState, KIT_CALL_CHAIN (fx := fx) B ARx SK) by kfact exv_kit_chain.
assert (KROD : forall fx : YK11.FPState, KIT_RODATA (fx := fx) B ARx SK) by kfact exv_kit_rodata.
assert (KWD : forall fx : YK11.FPState, KIT_WDEST (fx := fx) B ARx SK) by kfact exv_kit_wdest.
pose proof exvl_L_step as PLS. pose proof exvl_V_rest as PVR. pose proof exvl_name_rest as PNR.
pose proof exvl_suffix as PSUF. pose proof exvl_pref_cons as PPC. pose proof exvl_pref_long as PPL.
apply (exvl_loop B ARx SK).
- eapply (exvl_A1 B ARx SK); eassumption.
- eapply (exvl_A2 B ARx SK); eassumption.
- eapply (exvl_B1 B ARx SK); eassumption.
- eapply (exvl_B2 B ARx SK); eassumption.
Qed.
End f.

(* THE SEGMENT LEMMA: ExvB_Top.v's seg_loop, with EXV_HYP *)
Lemma exvB_loop : forall {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive} (B : asyms)
  (ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop) (SK : YI16.sink_head),
  EXV_HYP B ARx SK ->
  forall n,
  (match n with O => True | S n' => forall fx : YK11.FPState, tex_value_specX (fx := fx) (PA := PI_prog_B) B ARx SK n' end) ->
  (forall fx : YK11.FPState, CUT_CX (fx := fx) B ARx SK n) -> (forall fx : YK11.FPState, CUT_CC (fx := fx) B ARx SK n) ->
  forall fx : YK11.FPState, CUT_CL (fx := fx) B ARx SK n.
Proof. intros rc ci cp RL B ARx SK HYP. exact (exvl_loop_closed B ARx SK HYP). Qed.
Print Assumptions exvB_loop.
