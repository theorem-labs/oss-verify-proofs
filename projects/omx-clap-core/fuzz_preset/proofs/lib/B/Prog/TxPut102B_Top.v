(* fuzz_preset lib/B, the #102 re-walk of tx_put on image B' (asan-ubsan pin d663f82d7f488d30): the COMPOSITION of
   the four segments into the twin text, and the kit's text with tp_live discharged (the image-B tx_put walk's lane, a Theorem Labs lane). No
   instruction is walked here. PORT of the A' walk's lib/A/Prog/TxPut102A_Top.v: the same composition over
   lib/B/Prog/TxPut102B_Base.v (the cut graph S0 -> END / FIT / GROW, GROW -> FIT, FIT -> END - the batch kit's text has no
   refused path; P := tp_mn D; the END row's fpostWb turned into the text's fpostWbm).
   rule 24: proves function tx_put (reuse search: the internal file REWALK-102-PLAN.md section T3)
   THE IMAGE: parametric over {PA : PAImg B_prog_listing} - lib/B/PAImg_prog.v (blob 4392ab2c09ba) fails at :160
   (B_prog_range) until the per-instance image bounds land, so its PI_prog_B does not build; tp_img (the image
   facts, each a vm_compute at PI_prog_B) is this file's one image hypothesis.
   tx_put_holds_B is the kit's ttx_put_specX (lib/A/PRH_FnTx.v blob 88468bf162d8, the batch kit c23331281d07), the
   GROW row taken with ARX_DEPOT (AR_laws_x's field 25 at ARcfx, TxPut102B_Base.v); the twin's tp_live is closed from
   the text's own iface_room_pos premise by PresetRoomCounts.counts_of_room_pos_ok / _rl
   (lib/Spec/PresetRoomCounts.v 8a4dfa84e8be).
   Numerals: none. No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRealloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnTx CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomCounts.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import TxPutCall102.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PLB102 TxPut102B_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
Import ListNotations.
Local Open Scope Z_scope.

Section top. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {PA : PAImg B_prog_listing}.
(* the same bindings TxPut102A_Base.v makes, so the twin text's PI / RL are the walk's *)
#[local] Instance TPT_PrhImg : PrhImg := prh_img_B.
#[local] Instance TPT_RL : PrhRoomLive := prh_room_live_a8.
#[local] Notation segs := (@pa_segs _ B_prog_listing PA).
Variable B : asyms.
Variable SK : YI16.sink_head.
Variable CTX0 : list (list Z).

(* the four rows, each in the form its file proves: `forall P, srr_inv_laws segs P -> [srr_inv_call segs P ->]
   tp_seg_* B SK CTX0 P`. A row that crosses no call (S0, END) plugs in as `fun P HL _ => H P HL`. The batch kit's text has
   no refused path (the GROW row refutes the realloc's NULL), so there is no NULL row. *)
Variable SEG_S0 : forall P, srr_inv_laws segs P -> srr_inv_call segs P -> tp_seg_S0 B SK CTX0 P.
(* the realloc wrapper's two callee texts (tp_AREAL is the cf layer's primed row with room and the memnorm keep,
   tp_AREALN the null row with the keep, TxPut102B_Base.v:538 / :540) and the GROW row in its ruled form
   tp_seg_GROW_stmt *)
Variable AREAL : tp_AREAL B.
Variable AREALN : tp_AREALN B.
(* ARX_DEPOT: AR_laws_x's field 25 at ARcfx (TxPut102B_Base.v's tp_ARX_DEPOT comment); the instance,
   TxPut102B_Inst.v, projects it from the cf laws *)
Variable ARX_DEPOT : tp_ARX_DEPOT B.
Variable SEG_GROW : tp_seg_GROW_stmt B SK CTX0.
Variable SEG_FIT : forall P, srr_inv_laws segs P -> srr_inv_call segs P -> tp_seg_FIT B SK CTX0 P.
Variable SEG_END : forall P, srr_inv_laws segs P -> srr_inv_call segs P -> tp_seg_END B SK CTX0 P.
(* the image facts, each a vm_compute at PAImg_prog.v's PI_prog_B once it builds (owner: the image-B instance) *)
Variable IMG : tp_img B.

(* ---- the END row's plain window post gives the text's m-form at P := tp_mn D ---- *)
Lemma tp_postm_of_postW : forall (D : tp_in) W' c',
  tp_QP (tp_mn D) (tp_text_postW B SK D) W' c' -> tp_text_post B SK D W' c'.
Proof.
intros D W' c' [(ly' & S' & Hp' & regs' & mem' & md' & k & WS & Hc & HPW & HJ & HW & HP & HQ) HPm].
exists ly', S', Hp', regs', mem', md', k, WS.
split; [exact Hc|]. split; [exact HPW|]. split; [exact HJ|]. split; [exact HW|]. split; [exact HP|].
split; [exact HQ|]. subst c'. exact HPm.
Qed.

(* ---- the walk of one record: the continuations bottom-up, at P := tp_mn D. The GROW row's realloc frees the old
   buffer, so the walk concludes SRr' segs RZ_cf; S0 takes the GROW continuation at wle' segs RZ_cf ---- *)
Lemma tp_walk_one : forall D, tp_pre B CTX0 D -> tp_k1pre B D ->
  SRr' segs YGcfRehidePost.RZ_cf (tp_W D) (tp_cfg0 D) (tp_QP (tp_mn D) (tp_text_postW B SK D)).
Proof.
intros D HPRE HK1.
pose proof (tp_mn_laws D) as HL. pose proof (tp_mn_call D) as HC.
set (P := tp_mn D) in *.
set (Q := tp_text_postW B SK D).
assert (KEND : tp_k_END B SK CTX0 P Q D).
{ intros ly3 S3 Hp3 W3 regs3 mem3 md3 k HAT HP.
  exact (SEG_END P HL HC D ly3 S3 Hp3 W3 regs3 mem3 md3 k HAT IMG HP). }
assert (KFIT : tp_k_FIT B SK CTX0 P Q D).
{ intros ly3 S3 Hp3 W3 regs3 mem3 md3 k b1 cap1 HAT HP.
  exact (SEG_FIT P HL HC Q D ly3 S3 Hp3 W3 regs3 mem3 md3 k b1 cap1 HAT IMG KEND HP). }
assert (KGROW : tp_k_GROWR B SK CTX0 P (wle' segs YGcfRehidePost.RZ_cf) Q D).
{ intros ly3 S3 Hp3 W3 regs3 mem3 md3 k HAT HP.
  exact (SEG_GROW AREAL AREALN ARX_DEPOT P HL HC Q D ly3 S3 Hp3 W3 regs3 mem3 md3 k HAT IMG KFIT HP). }
exact (SEG_S0 P HL HC Q D HPRE HK1 IMG KEND KFIT KGROW (tp_mn_refl D)).
Qed.

(* ---- the twin text ---- *)
Theorem tx_put_holds_ev : TxPutCall102.ttx_put_specX_ev B (ARcfx B) SK CTX0.
Proof.
apply (tp_text_of_walk B SK CTX0).
intros D HPRE HK1. eapply (SRr'_mono segs YGcfRehidePost.RZ_cf); [exact (tp_walk_one D HPRE HK1)|].
intros W' c' _ H. exact (tp_postm_of_postW D W' c' H).
Qed.

End top.

Section inst. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
#[local] Existing Instance CfParams_preset.
Context {PA : PAImg B_prog_listing}.
#[local] Instance TPU_PrhImg : PrhImg := prh_img_B.
#[local] Instance TPU_RL : PrhRoomLive := prh_room_live_a8.
#[local] Notation segs := (@pa_segs _ B_prog_listing PA).
Variable B : asyms.
Variable SK : YI16.sink_head.
Variable CTX0 : list (list Z).
Variable SEG_S0 : forall P, srr_inv_laws segs P -> srr_inv_call segs P -> tp_seg_S0 B SK CTX0 P.
(* the realloc wrapper's two callee texts (tp_AREAL is the cf layer's primed row with room and the memnorm keep,
   tp_AREALN the null row with the keep, TxPut102B_Base.v:538 / :540) and the GROW row in its ruled form
   tp_seg_GROW_stmt *)
Variable AREAL : tp_AREAL B.
Variable AREALN : tp_AREALN B.
(* ARX_DEPOT: AR_laws_x's field 25 at ARcfx (TxPut102B_Base.v's tp_ARX_DEPOT comment); the instance,
   TxPut102B_Inst.v, projects it from the cf laws *)
Variable ARX_DEPOT : tp_ARX_DEPOT B.
Variable SEG_GROW : tp_seg_GROW_stmt B SK CTX0.
Variable SEG_FIT : forall P, srr_inv_laws segs P -> srr_inv_call segs P -> tp_seg_FIT B SK CTX0 P.
Variable SEG_END : forall P, srr_inv_laws segs P -> srr_inv_call segs P -> tp_seg_END B SK CTX0 P.
Variable IMG : tp_img B.

(* ---- the twin's named premise, from the text's own run-position premise (counts_of_room_pos, image-free:
   iface_room_pos and the live counts only; the image-free leaf lib/Spec/PresetRoomCounts.v blob 8a4dfa84e8be,
   owner 19:19Z, where the counts lemmas moved verbatim from PresetCfnA)
   ---- *)
Lemma tp_live_of_pos : forall rp_sm rp_x rp_os rp_i rp_H0 rp_hist S,
  PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S -> TxPutCall102.tp_live S.
Proof.
intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist S HP.
destruct (PresetRoomCounts.counts_of_room_pos_ok rp_sm rp_x rp_os rp_i rp_H0 rp_hist S HP) as [Hs Hb].
destruct (PresetRoomCounts.counts_of_room_pos_rl rp_sm rp_x rp_os rp_i rp_H0 rp_hist S HP) as [_ Hc].
split; [exact Hs|]. split; [exact Hb | lia].
Qed.

(* ---- THE FUNCTION'S THEOREM: the kit's text (SRr' segs RZ_cf, the post's journal at wle' segs RZ_cf, the run-length
   premise length rp_os <= 4, which the twin threads to tp_pre), PAImg-parametric ---- *)
Theorem tx_put_holds_B : ttx_put_specX B (ARcfx B) SK CTX0.
Proof.
apply (TxPutCall102.ttx_put_specX_of_pos B (ARcfx B) SK CTX0 tp_live_of_pos).
exact (tx_put_holds_ev B SK CTX0 SEG_S0 AREAL AREALN ARX_DEPOT SEG_GROW SEG_FIT SEG_END IMG).
Qed.

End inst.
Print Assumptions tx_put_holds_B.