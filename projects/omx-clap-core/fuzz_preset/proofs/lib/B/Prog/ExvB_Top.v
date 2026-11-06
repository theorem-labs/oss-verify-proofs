(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, image B, ex_value: the COMPOSITION of the seven segment lemmas into the
   tex_value_specX at every nesting n, by induction on n (the recursive call at the loop takes the text at n - 1,
   at any float state), as preset's released plain ex_value proof closes its recursion by depth (lib/Prog/
   ex_value.v; read for the shape only, not cited). The segment lemmas are this file's Section hypotheses until
   their files land (lib/B/Prog/ExvB_<segment>.v); each takes EXV_HYP and the downstream cuts, as ExvB_Stmt.v
   states them. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YStrtodRowX YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Stmt.
Import ListNotations.
Local Open Scope Z_scope.

#[local] Existing Instance prh_img_B.

(* fpostWF is monotone in its post (PRH_Base.v gives none) *)
Lemma exv_fpostWF_mono : forall {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams}
  (B : asyms) (ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop)
  (SK : YI16.sink_head) STK d FP regs ly S Hp (W : world rsegs) mem md
  (Q Q' : alayout -> astate -> list Z -> world rsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) W' c',
  (forall ly' S' Hp' W'' regs' mem' md', Q ly' S' Hp' W'' regs' mem' md' -> Q' ly' S' Hp' W'' regs' mem' md') ->
  fpostWF (PA := PI_prog_B) B ARx SK STK d FP regs ly S Hp W mem md Q W' c' ->
  fpostWF (PA := PI_prog_B) B ARx SK STK d FP regs ly S Hp W mem md Q' W' c'.
Proof.
intros fx rc cp B ARx SK STK d FP regs ly S Hp W mem md Q Q' W' c' HQ
  (fx' & ly' & S' & Hp' & regs' & mem' & md' & k & Hc & Hz & Hk & HJ & HW & Hpr & HQ0).
exists fx', ly', S', Hp', regs', mem', md', k. repeat (split; [eassumption|]). exact (HQ _ _ _ _ _ _ _ HQ0).
Qed.

Section t. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis HYP : EXV_HYP B ARx SK.

Local Notation TEXT n fx := (tex_value_specX (fx := fx) (PA := PI_prog_B) B ARx SK n).
Local Notation REC n := (match n with O => True | S n' => forall fx : YK11.FPState, TEXT n' fx end).

(* the segment lemmas (ExvB_<segment>.v), each at every float state *)
Hypothesis seg_exit : forall n (fx : YK11.FPState), CUT_CX (fx := fx) B ARx SK n.
Hypothesis seg_close : forall n, (forall fx : YK11.FPState, CUT_CX (fx := fx) B ARx SK n) ->
  forall fx : YK11.FPState, CUT_CC (fx := fx) B ARx SK n.
Hypothesis seg_loop : forall n, REC n ->
  (forall fx : YK11.FPState, CUT_CX (fx := fx) B ARx SK n) -> (forall fx : YK11.FPState, CUT_CC (fx := fx) B ARx SK n) ->
  forall fx : YK11.FPState, CUT_CL (fx := fx) B ARx SK n.
Hypothesis seg_open : forall n,
  (forall fx : YK11.FPState, CUT_CX (fx := fx) B ARx SK n) -> (forall fx : YK11.FPState, CUT_CC (fx := fx) B ARx SK n) ->
  (forall fx : YK11.FPState, CUT_CL (fx := fx) B ARx SK n) ->
  forall fx : YK11.FPState, CUT_CI (fx := fx) B ARx SK n.
Hypothesis seg_num : forall n, (forall fx : YK11.FPState, CUT_CX (fx := fx) B ARx SK n) ->
  forall fx : YK11.FPState, CUT_CN (fx := fx) B ARx SK n.
Hypothesis seg_disp : forall n,
  (forall fx : YK11.FPState, CUT_CX (fx := fx) B ARx SK n) -> (forall fx : YK11.FPState, CUT_CN (fx := fx) B ARx SK n) ->
  (forall fx : YK11.FPState, CUT_CI (fx := fx) B ARx SK n) ->
  forall fx : YK11.FPState, CUT_C1 (fx := fx) B ARx SK n.
Hypothesis seg_entry : forall n, (forall fx : YK11.FPState, CUT_C1 (fx := fx) B ARx SK n) ->
  forall fx : YK11.FPState, CUT_C0 (fx := fx) B ARx SK n.

(* one nesting level from the segments *)
Lemma exv_level : forall n, REC n -> forall fx : YK11.FPState, CUT_C0 (fx := fx) B ARx SK n.
Proof.
intros n HR.
assert (HX : forall fx : YK11.FPState, CUT_CX (fx := fx) B ARx SK n) by (intros fx; apply seg_exit).
assert (HC : forall fx : YK11.FPState, CUT_CC (fx := fx) B ARx SK n) by exact (seg_close n HX).
assert (HL : forall fx : YK11.FPState, CUT_CL (fx := fx) B ARx SK n) by exact (seg_loop n HR HX HC).
assert (HI : forall fx : YK11.FPState, CUT_CI (fx := fx) B ARx SK n) by exact (seg_open n HX HC HL).
assert (HN : forall fx : YK11.FPState, CUT_CN (fx := fx) B ARx SK n) by exact (seg_num n HX).
assert (H1 : forall fx : YK11.FPState, CUT_C1 (fx := fx) B ARx SK n) by exact (seg_disp n HX HN HI).
exact (seg_entry n H1).
Qed.

(* the entry cut is the text *)
Lemma exv_text_of_C0 : forall n (fx : YK11.FPState), CUT_C0 (fx := fx) B ARx SK n -> TEXT n fx.
Proof.
intros n fx H0. unfold tex_value_specX.
intros ly S Hp W regs mem md ch q v x0 i0 dep dl scr d x t D Lam peak cnt fail ran most own
  Hpre Hmn Hfrm Hcnt Ha0 Ha1 Hcur Hq8 Hca Hq1 Hq2 Hwin Hsrc Hblk Hlen Hi0 Hdep Hdepn Hdl Hwd Hsblk Hsx Hsq Hv Hled.
set (E := MkExv fx n ly S Hp W regs mem md ch q v x0 i0 dep dl scr d x t D Lam peak cnt fail ran most own).
assert (HP : EXV_PRE B ARx E).
{ unfold EXV_PRE, exv_len, exv_STK; cbn [e_fx e_n e_ly e_S e_Hp e_W e_regs e_mem e_md e_ch e_q e_v e_x0 e_i0 e_dep
    e_dl e_scr e_d e_x e_t e_D e_Lam e_peak e_cnt e_fail e_ran e_most e_own].
  repeat (split; [assumption|]). assumption. }
pose proof (H0 E eq_refl eq_refl HP) as HS.
unfold E in HS. unfold EXV_POST, fpostWFm in HS. unfold fpostWFm. cbn [e_fx e_n e_ly e_S e_Hp e_W e_regs e_mem e_md e_scr e_q e_d] in HS.
refine (SRr_mono rsegs _ _ _ _ HS _). cbv beta. intros W' c' _ HF.
eapply (exv_fpostWF_mono (fx := fx) (rc := rc) (cp := cp)). 2: { exact HF. } cbv beta.
intros ly' S' Hp' W'' regs' mem' md' (((Hrk & Hrp & Hhu) & r & Hr & (p' & dep' & dl' & Hc & Hdl' & Hm) & HHp & Hab & Hl) & Hkeep).
split; [|exact Hkeep].
split; [exact Hrk|]. split; [exact Hhu|]. split; [exact Hrp|]. exists r, p', dep', dl'. split; [exact Hr|]. split; [exact Hc|]. split; [exact Hdl'|].
split; [exact HHp|]. split; [exact Hab|]. split; [exact Hl|]. exact Hm.
Qed.

Theorem ex_value_holds_B : forall n (fx : YK11.FPState), TEXT n fx.
Proof.
induction n as [|n IH]; intros fx.
- apply exv_text_of_C0. apply exv_level. exact I.
- apply exv_text_of_C0. apply exv_level. exact IH.
Qed.
End t.
