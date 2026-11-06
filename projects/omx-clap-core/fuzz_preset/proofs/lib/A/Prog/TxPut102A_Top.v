(* fuzz_preset lib/A, the #102 re-walk of tx_put on image A': the COMPOSITION of the four segments into the twin
   text (the image-A tx_put walk's lane, a Theorem Labs lane). No instruction is walked here. The file takes the four segment lemmas of
   TxPut102A_Base.v (tp_seg_S0, tp_seg_GROW, tp_seg_FIT, tp_seg_END) and the image facts tp_img, builds the
   continuations bottom-up (the cut graph is acyclic: S0 -> END / FIT / GROW, GROW -> FIT, FIT -> END; the batch kit's text
   has no live refused path, its refused arm is DEAD: GROW refutes the realloc's NULL), instantiates the generic memory invariant P with the memnorm
   keep tp_mn D of the entry memory, turns the END row's budgeted caller-window post into the text's fpostWbm (the
   fQmn conjunct IS `P (ms_mem (cfg_ms c'))` at that P: the END row's finding, TxPut102A_Base.v's tp_text_postW
   comment), and closes with TxPut102A_Base.tp_text_of_walk.
   rule 24: proves function tx_put (reuse search: the internal file REWALK-102-PLAN.md section T3)
   The theorem is the TWIN text TxPutCall102.ttx_put_specX_ev (the kit's ttx_put_specX, lib/A/PRH_FnTx.v
   88468bf162d8 at the batch kit c23331281d07, VERBATIM plus the ONE named premise tp_live, owner a Theorem Labs lane / the kit owner;
   TxPutCall102.v's header says why). TxPutCall102.ttx_put_specX_of_ev carries it to the kit's text wherever tp_live
   holds.
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PRH_Base PRH_Img PRH_FnTx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import TxPutCall102 TxPut102A_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
Import ListNotations.
Local Open Scope Z_scope.

Section top. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {PA : PAImg A_prog_listing}.
(* the same bindings TxPut102A_Base.v makes, so the twin text's PI / RL are the walk's *)
#[local] Instance TPT_PrhImg : PrhImg := prh_img_A.
#[local] Instance TPT_RL : PrhRoomLive := prh_room_live_a8.
#[local] Notation segs := (@pa_segs _ A_prog_listing PA).
Variable B : asyms.
Variable SK : YI16.sink_head.
Variable CTX0 : list (list Z).

(* the four rows, each in the form its file proves: `forall P, srr_inv_laws segs P -> [srr_inv_call segs P ->]
   tp_seg_* B SK CTX0 P`. A row that crosses no call (S0, END) plugs in as `fun P HL _ => H P HL`. *)
Variable SEG_S0 : forall P, srr_inv_laws segs P -> srr_inv_call segs P -> tp_seg_S0 B SK CTX0 P.
(* the realloc wrapper's callee texts (tp_AREAL is the cf layer's primed keep row with room,
   YGcfInstReallocKKeep.arealloc_realizes_cf_k_keep at every headroom k, TxPut102A_Base.v; the GROW row's statement
   TxPut102A_Base.tp_seg_GROW_stmt takes them before P), and ARX_DEPOT (AR_laws_x's field 25 at ARcfx; the instance,
   TxPut102A_Inst.v, projects it from the cf laws) *)
Variable AREAL : tp_AREAL B.
Variable AREALN : tp_AREALN B.
Variable ARX_DEPOT : tp_ARX_DEPOT B.
Variable SEG_GROW : tp_seg_GROW_stmt B SK CTX0.
Variable SEG_FIT : forall P, srr_inv_laws segs P -> srr_inv_call segs P -> tp_seg_FIT B SK CTX0 P.
Variable SEG_END : forall P, srr_inv_laws segs P -> srr_inv_call segs P -> tp_seg_END B SK CTX0 P.
(* the image facts, proved at the instance by computation (TxPut102A_Inst.v) *)
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

Print Assumptions tx_put_holds_ev.
