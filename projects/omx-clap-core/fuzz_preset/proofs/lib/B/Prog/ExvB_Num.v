(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Does not rest on tex_word_specX; memnorm only through EXB's exv_rm keep and EXV_PRE's entry memnorm (kit 4f18c75d4900). *)
(* Theorem Labs, 2026-10: fuzz_preset, image B (asan-ubsan, rebuilt pin f8f98a95bc52, unstripped twin 3b5e1a099b53),
   ex_value's NUMBER SEGMENT: ExvB_Top.v's Section hypothesis `seg_num` PROVED, with EXV_HYP as its premise -
   CUT_CX at every float state gives CUT_CN (B 0x837a4 = exv_pc 0x278) at every float state.
   Composed from the seven sub-piece lemmas of lib/B/Prog/ExvB_Num{M,FT,A,B,C,D,E}.v over the internal cuts of
   lib/B/Prog/ExvB_NumCut.v:  T (CT -> CX), F (CD -> CT), Ec (CC -> CD), D (CR -> CT | CC), C (CS -> CR),
   Bl (CL -> CS), A (CN -> CT | CL); M carries EXB across the segment's own writes.
   Numerals: 14 (DERIVED: the position of `0 <= i0 <= len` in EXV_PRE's conjunction, a destruct pattern width).
   No ADDRESS, no image constant. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YStrtodRowX YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Stmt ExvB_NumPure ExvB_NumCut.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require
  ExvB_NumM ExvB_NumFT ExvB_NumA ExvB_NumB ExvB_NumC ExvB_NumD ExvB_NumE.
Import ListNotations.
Local Open Scope Z_scope.

#[local] Existing Instance prh_img_B.

(* CUT_CN's dispatch facts give EXN_disp: the byte at i1 heads skip (skipn i0 x), so it is not whitespace *)
Lemma exn_disp_of : forall (E : exv_e) (c : Z), 0 <= e_i0 E <= exv_len E -> exv_i1 E < exv_len E ->
  nth (Z.to_nat (exv_i1 E)) (e_x E) 0 = c -> exv_disp c = false -> EXN_disp E c.
Proof.
intros E c Hi0 Hlt Hnth Hdisp.
pose proof (exn_i1_eq E Hi0) as Hsk.
destruct (skipn (EXN_i1 E) (e_x E)) as [|b y] eqn:Esk.
{ exfalso. unfold exv_i1 in Hlt. rewrite <- Hsk in Hlt. cbn [length Z.of_nat] in Hlt. lia. }
assert (Hb : b = c).
{ rewrite <- Hnth. symmetry. exact (exn_nth_skipn (e_x E) (EXN_i1 E) b y Esk). }
split; [exact Hlt|]. split; [exact Hnth|]. split; [exact Hdisp|].
rewrite <- Hb. exact (exn_skip_head _ b y (eq_sym Hsk)).
Qed.

(* ExvB_Top.v's `seg_num`: CUT_CX at every float state gives CUT_CN at every float state. The strtod site's
   whole-overlay memory facts come from EXV_PRE's entry memnorm and EXB's exv_rm keep (kit 4f18c75d4900); the
   segment's own steps keep it through the engine's _inv runners and the runtime rows' m-form keeps. *)
Lemma exvB_num : forall {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}
  (B : asyms) (ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop)
  (SK : YI16.sink_head),
  EXV_HYP B ARx SK ->
  forall n, (forall fx : YK11.FPState, CUT_CX (fx := fx) B ARx SK n) ->
  forall fx : YK11.FPState, CUT_CN (fx := fx) B ARx SK n.
Proof.
intros rc ci cp RL B ARx SK HYP n HX fx.
unfold CUT_CN.
intros E lyc Sc Hpc Wc regs memc mdc k pos c Hn HPRE HB Hcur Hlt Hnth Hdisp H11 H12 H27 H20 Hs144 Hs152.
subst n.
assert (MK : EXN_keepM B ARx SK E pos) by (eapply ExvB_NumM.exn_keepM; eassumption).
assert (MC : EXN_keepM_cur B ARx SK E pos) by (eapply ExvB_NumM.exn_keepM_cur; eassumption).
assert (KS : EXN_keep_spill E) by (eapply ExvB_NumM.exn_keep_spill; eassumption).
assert (HT : EXN_T B ARx SK E pos) by (eapply ExvB_NumFT.exn_T; eassumption).
assert (HF : EXN_F B ARx SK E pos) by (eapply ExvB_NumFT.exn_F; eassumption).
assert (HE : EXN_Ec B ARx SK E pos) by (eapply ExvB_NumE.exn_Ec; eassumption).
assert (HD : EXN_D B ARx SK E pos) by (eapply ExvB_NumD.exn_D; eassumption).
assert (HC : EXN_C B ARx SK E pos) by (eapply ExvB_NumC.exn_C; eassumption).
assert (HL : EXN_Bl B ARx SK E pos) by (eapply ExvB_NumB.exn_Bl; eassumption).
assert (HA : EXN_A B ARx SK E pos) by (eapply ExvB_NumA.exn_A; eassumption).
assert (Hi0 : 0 <= e_i0 E <= exv_len E)
  by (destruct HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hi0 & _); exact Hi0).
exact (HA fx lyc Sc Hpc Wc regs memc mdc k c HPRE (conj HB (conj Hs144 Hs152))
  (exn_disp_of E c Hi0 Hlt Hnth Hdisp) Hcur H11 H12 H27 H20).
Qed.

Print Assumptions exvB_num.
