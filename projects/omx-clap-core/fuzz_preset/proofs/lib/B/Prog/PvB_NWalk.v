(* fuzz_preset image B, parse_value SEGMENT N (the number arm): the composition of the sub-pieces of PvB_NCut.v
   into SEG_N's statement (PvB_Top.v:74-76). Chain: TX -> F -> E (with TX) -> D (with TX) -> C -> B -> A (with TX).
   rule 24: no function proved
   rule 24: proves no function (kind: composition of already-stated segment lemmas). No numeral. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader PRH_FnParse PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PvB_Defs PvB_NCut.
Import ListNotations.
Local Open Scope Z_scope.

Section c. Context {fx0 : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
Context {PA : PAImg B_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.

Lemma pvN_of_pieces :
  pnA_stmt (SK := SK) B ARx -> pnB_stmt (SK := SK) B ARx -> pnC_stmt (SK := SK) B ARx ->
  pnD_stmt (SK := SK) B ARx -> pnE_stmt (SK := SK) B ARx -> pnF_stmt (SK := SK) B ARx ->
  pnTX_stmt (SK := SK) B ARx ->
  forall en W' ms mdc, pv_pre B ARx en -> pv_at_N B ARx en W' ms mdc ->
  (forall W2 ms2 md2, pv_at_exit B ARx en W2 ms2 md2 -> SRr SEGS W2 (mkCfg ms2 md2) (pv_FINK (SK := SK) B ARx en)) ->
  SRr SEGS W' (mkCfg ms mdc) (pv_FINK (SK := SK) B ARx en).
Proof.
intros PA_ PB PC PD PE PF PT en W' ms mdc Hpre HN KX.
pose proof (PT en Hpre KX) as KT.
pose proof (PF en Hpre KT) as KC.
pose proof (PE en Hpre KT KC) as KR.
pose proof (PD en Hpre KT KR) as KM.
pose proof (PC en Hpre KM) as KS.
pose proof (PB en Hpre KS) as KL.
exact (PA_ en Hpre KT KL W' ms mdc HN).
Qed.
End c.
