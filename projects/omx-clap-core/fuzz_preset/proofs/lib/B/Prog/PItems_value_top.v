(* Theorem Labs, 2026-10: segment VALUE of parse_items' image-B walk, COMPOSED:
   PItems_top.v's STEP_VAL from the four walk files of the segment.
     pi_val_holds   PItems_value.v       PI_O_VAL .. PI_O_PVAL: the kid slot's checks, the checked memset
     pv_call_holds  PItems_value_call.v  PI_O_PVAL: the parse_value call (window e + 144)
     pv_aftv_holds  PItems_value_aftv.v  PI_O_AFTV .. PV_O_SEP: v->n++, the refusal exit, skip_ws
     pv_sep_holds   PItems_value_sep.v   PV_O_SEP .. PI_O_GROW2 and PI_O_CLS1 .. PI_O_CLOSE2: the ',' / closer test,
                                         in->p++, grow, and the exits to PI_O_BODY / PI_O_CLOSE2 / PI_O_EPI
   pv_step_val has EXACTLY STEP_VAL's statement (PItems_top.v); the Section hypotheses below are the segment's own
   callee texts and laws, each with its owner, and the top takes them as its own.
   The batch kit (240b06ed4fd4): every spec takes the cursor set CW after CTX0 (a Section variable here, as in
   PItems_top.v), and the parse_value text at S d (pi_PV) is the batch kit's tparse_value_specX at that CW.
   (pi_PV) is the kit's tparse_value_specX at that CW. Rule 24: proves no function in this file (kind: segment wiring);
   the walk index for parse_items is the rule-24 lookup the internal file idx-parse_items.txt (rule-24 check: CONFIRM).
   Numerals: none. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YG0s YP07 YI00 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YC80x YPsym YC4aP YImgTop YC1fP YC1fPx YCbqG YCbqGcall YCbqGcallW YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YK06 YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
PRH_Base PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import
PItems_defs PItems_pres PItems_kept PItems_top PItems_value_pres
PItems_value PItems_value_call PItems_value_aftv PItems_value_sep.
Import ListNotations.
Open Scope Z_scope.

Section vt. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Existing Instance prh_img_B.
#[local] Notation PA := (PI_prog_B).
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
Variable SK : YI16.sink_head.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable CTX0 : list (list Z).
(* the cursor set (the batch kit 240b06ed4fd4): parse_items' own, handed to every block spec and to parse_value at S d *)
Variable CW : list (list Z).
(* the engine's laws at the instance's head length *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* the harness-block shadow law (PItems_defs.v; YGcfHeadSh.v ARx_hshadow_law_cf at ARcf) *)
Hypothesis HSH : pi_hshadow_law (L := B_prog_listing) (PA := PA) B ARx cf_head.
(* The kit's PRH_Base.v:182, 8 <= cf_head (a Theorem Labs lane's preset_head_wide) *)
Hypothesis HW : prh_head_wide.
(* __asan_memset's realizes text WITH the memnorm keep (YGcallMxmn.v) *)
Hypothesis AMEMSET : forall fy : YK11.FPState,
  YGcallMxmn.aintrin_realizes_xm (fx := fy) SEGS B ARx OSet (@pa_sigma _ B_prog_listing PA AS___asan_memset).
(* skip_ws's record text *)
Hypothesis SKW : forall (fy : YK11.FPState), tskip_ws_specX (fx := fy) (L := B_prog_listing) (PA := PA) B ARx SK.
(* PItems_kept.v's two call-keep statements over a world relation R (pi_cur_kept_callR /
   pi_curmem_kept_callR): the walks call at wle' segs RZ_cf, so the callee's journal is at that relation *)
Hypothesis HCURK : pi_cur_kept_callR_stmt (L := B_prog_listing) (PA := PA) (SKq := SK) B ARx.
Hypothesis CURM : pi_curmem_kept_callR_stmt (L := B_prog_listing) (PA := PA) (SKq := SK) B ARx.
(* grow's record text (the kit's tgrow_specX, same shape on the batch kit 240b06ed4fd4; the grow lane), at the segment's CTX0 *)
Hypothesis GROW : forall (fy : YK11.FPState),
  tgrow_specX (fx := fy) (PI := prh_img_B) (L := B_prog_listing) (PA := PA) B ARx SK CTX0.
(* the instance's head length is the model's (PItems_body_loop.v PIL_HEAD, same text): grow's event lists prhPg_evs
   are rd_hevs of its trace (PRH_FnReader.v prhPg_evs_model). OWNER: the instance (reflexivity at the preset's
   CfParams) *)
Hypothesis PIL_HEAD : cf_head = PresetReqAt.HEAD.

Theorem pv_step_val : forall d, ((d < PjGrammar.MAXD)%nat ->
    pi_PV (L := B_prog_listing) (PA := PA) B ARx SK CTX0 CW (Nat.succ d)) ->
  forall N, (forall N', (N' < N)%nat ->
    pi_body_spec (L := B_prog_listing) (PA := PA) (PL := PL_prog_B) B ARx SK d CTX0 CW N') ->
  pi_close2_spec (L := B_prog_listing) (PA := PA) (PL := PL_prog_B) B ARx SK d CTX0 CW ->
  pi_epi_spec (L := B_prog_listing) (PA := PA) (PL := PL_prog_B) B ARx SK d ->
  pi_val_spec (L := B_prog_listing) (PA := PA) (PL := PL_prog_B) B ARx SK d CTX0 CW N.
Proof.
intros d HPV N IHB HCL HEP.
exact (pi_val_holds SK B ARx LAWS d HSH AMEMSET HW CTX0 CW N
  (pv_call_holds SK B ARx LAWS d CTX0 CW HPV HSH CURM N
     (pv_aftv_holds SK B ARx d LAWS SKW HCURK CTX0 CW N
        (pv_sep_holds B ARx SK d CTX0 CW LAWS PIL_HEAD GROW HCURK N IHB HCL HEP) HEP))).
Qed.

End vt.
