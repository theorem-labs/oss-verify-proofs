(* Image B's frame flag law over ARx at the cf relation (a Theorem Labs lane's law; B twin of
   a Theorem Labs lane's lib/A/W_frame_flag_cf.v), so B top_x's Section hypothesis FFL (lib/B/W_LLVMFuzzerTestOneInput_top_x.v
   :207, ReplyBTop.v's Context FFL) is a theorem.  proves no function (kind: invariant lemma).
   frame_flag_lawP_x_of_flag: lib/B/W_frame_x.v :73 frame_flag_lawP_x at any ARx with AR_laws_x and the cf flag law's
   conclusion (FLAG, YG0dcf.v :650 AR_flag_law_cf's text over ARx).  Its four parts: apresent / aowned and
   flag < alloc_ceiling are FLAG's; app_addr and 4096 <= come from in_app; ~ in_img is AR_laws_x's client-image law
   (YCbqG.v :92, the flag disjunct); zone2's band half is in_app's (kLowShadowBeg = 2147446784, kHighMemBeg =
   17594333495296 are zone2's bounds), its image half (off_img: below IMG_LO or at or above lib/Reusable/YCbq.v's
   IMG_TOP_A, the zone2 lib/B/W_frame_x.v reads) comes from the client-image law's ~ in_zr (ly_img ly) with the image
   cover of lib/B/W_img_x.v :30 fr_img_cover_x (ly_img covers [0x10000, 0x5fc000), image B's top, above IMG_TOP_A).
   frame_flag_lawP_x_ARX: the instance at top_x's ARX text (ARcf at CfParams_reply with Hp = []), FLAG from
   lib/Reusable/YG0scf.v :506 AR_flag_law_ok_cf; ARX_laws_ffl: the laws, as top_x.v :156-159.  Same shape and names
   as a Theorem Labs lane's lib/A/W_frame_flag_cf.v (a working branch fa09307e497).  Template: cgif's
   lib/A/ACed.v tfibX_FFL (origin/ossv/recipes).  Imports: A twin's, at lib/B (not top_x). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0ncf YG0dcf YG0scf YGcallcf YG0lawscf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_tbl W_listing W_kit W_img W_frame_x W_journal_x W_img_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YD2l.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import CfImgB.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section g.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx hl.
Hypothesis FLAG : forall ly S Hp (W : world segs) mem md cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  apresent (w_H W) mem (flag_addr ly cid pos) /\ aowned B ly S (flag_addr ly cid pos) /\
  in_app (flag_addr ly cid pos) 1 /\ flag_addr ly cid pos < alloc_ceiling.

Lemma frame_flag_lawP_x_of_flag : frame_flag_lawP_x segs B ARx.
Proof.
  intros ly S Hp W mem md cid pos HAR Hin.
  destruct (FLAG ly S Hp W mem md cid pos HAR Hin) as (Hpr & Ho & Happ & Hceil).
  destruct (alx_client_img _ _ _ LAWS ly S Hp W mem md (flag_addr ly cid pos) HAR) as [Hhull Himg].
  { right. right. exists cid, pos. split; [exact Hin | reflexivity]. }
  destruct (fr_img_cover_x B ARx LAWS ly S Hp W mem md HAR) as [C1 C2].
  unfold in_zr in Hhull.
  split; [exact Hpr|]. split; [exact Ho|]. split.
  - split; [|exact Himg]. unfold app_addr, in_app, ASAN_CEIL in *. lia.
  - split; [unfold in_app in Happ; lia|]. split; [|exact Hceil].
    assert (EL : YImgTop.IMG_LO = 65536) by reflexivity.
    assert (ET : YImgTop.IMG_TOP_B = 6275072) by reflexivity.
    assert (EK1 : kLowShadowBeg = 2147446784) by reflexivity.
    assert (EK2 : kHighMemBeg = 17594333495296) by reflexivity.
    unfold zone2, off_img, in_app in *. rewrite ?EL, ?ET in *. rewrite EK1, EK2 in Happ. lia.
Qed.
End g.

(* The instance: lib/B/W_LLVMFuzzerTestOneInput_top_x.v Definition ARX (:154-155) at its segs (:148, pa_segs PB_fr),
   written out verbatim (as a Theorem Labs lane's A file: top_x may Require this file, not the reverse), so top_x's FFL
   (:207) and ReplyBTop.v :70's Context FFL are `frame_flag_lawP_x_ARX`; the laws as top_x.v :156-159 ARX_laws proves
   them. *)
Section i.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma ARX_laws_ffl : AR_laws_x (@pa_segs _ fr_prog_listing PB_fr) TfibB
  (fun ly S Hp W mem md => ARcf (ci := CfImg_B) (cp := CfParams_reply) (@pa_segs _ fr_prog_listing PB_fr) TfibB ly S Hp W mem md /\ Hp = [])
  (@cf_head CfParams_reply).
Proof.
  apply AR_laws_x_and_hp.
  exact (AR_laws_x_cf (cp := CfParams_reply) (@pa_segs _ fr_prog_listing PB_fr) TfibB
    (AR_laws_ok_cf (cp := CfParams_reply) (@pa_segs _ fr_prog_listing PB_fr) TfibB)).
Qed.
Theorem frame_flag_lawP_x_ARX : frame_flag_lawP_x (@pa_segs _ fr_prog_listing PB_fr) TfibB
  (fun ly S Hp W mem md => ARcf (ci := CfImg_B) (cp := CfParams_reply) (@pa_segs _ fr_prog_listing PB_fr) TfibB ly S Hp W mem md /\ Hp = []).
Proof.
  apply (frame_flag_lawP_x_of_flag TfibB _ ARX_laws_ffl).
  intros ly S Hp W mem md cid pos [HAR _] Hin.
  exact (YG0scf.AR_flag_law_ok_cf (cp := CfParams_reply) (@pa_segs _ fr_prog_listing PB_fr) TfibB ly S Hp W mem md cid pos
    HAR Hin).
Qed.
End i.
