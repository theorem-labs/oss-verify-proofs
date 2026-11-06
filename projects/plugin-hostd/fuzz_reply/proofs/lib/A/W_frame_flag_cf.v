(* Theorem Labs, 2026-10: W_frame_x.v:71's flag law frame_flag_lawP_x at reply image A's cf allocator relation, the
   relation of W_LLVMFuzzerTestOneInput_top_x.v Definition ARX (ARcf at CfParams_reply, ghost list empty). lib/A/W_LLVMFuzzerTestOneInput_top_x.v takes
   it as the Section hypothesis FFL (and pro_x / exit_x / relay_add / relay_finish_h as FFL), since no lemma concluded
   it at the cf instance.
   - frame_flag_lawP_x_of_flag: for ANY ARx with AR_laws_x over image A's segments and the cf instance's flag law shape
     (YG0dcf.v:650 AR_flag_law_cf: present, owned, in_app flag 1, below alloc_ceiling), the full law. The extra
     conjuncts: app_addr and 4096 <= from in_app (YG0f.in_app_addr); ~ in_img from the laws' client-image field
     (YCbqG.v:192 field alx_client_img = YCbqG.v:92 ARx_client_img_law, its flag disjunct :86); zone2's band from app_addr (kLowShadowBeg 0x7fff7000 and
     kHighMemBeg 0x10007fff8000 are its bounds), zone2's off_img from the client-image field's ~ in_zr (ly_img ly) and
     W_img_x.fr_img_cover_x (ly_img covers [IMG_LO, IMG_TOP_A) = [0x10000, 0x5fb000)). cgif's template:
     proofs/cgif/cgif_file_fuzzer/lib/A/ACed.v tfibX_FFL (al_flag, al_client_img, tfib_img_cover).
   - frame_flag_lawP_x_ARX: the instance, from AR_flag_law_ok_cf (YG0scf.v) and the laws as lib/A/W_LLVMFuzzerTestOneInput_top_x.v's ARX_laws proves
     them (AR_laws_x_and_hp over AR_laws_x_cf over AR_laws_ok_cf).
   rule 24: no function proved (kind: an allocator-instance frame law; proof-index frame_flag_lawP_x, 07:30Z
   index: 0 released, the unreleased hits are its Definition only). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0ncf YG0dcf YG0scf YGcallcf YG0lawscf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_tbl W_listing W_kit W_img W_frame_x W_journal_x W_img_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AD2l CfImgA CfParamsReply.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world frsegs -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x frsegs B ARx hl.
(* YG0dcf.v:650 AR_flag_law_cf's shape over ARx *)
Hypothesis FLAG : forall ly S Hp (W : world frsegs) mem md cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  apresent (w_H W) mem (flag_addr ly cid pos) /\ aowned B ly S (flag_addr ly cid pos) /\
  in_app (flag_addr ly cid pos) 1 /\ flag_addr ly cid pos < alloc_ceiling.
Lemma frame_flag_lawP_x_of_flag : frame_flag_lawP_x frsegs B ARx.
Proof.
intros ly S Hp W mem md cid pos HAR Hin.
destruct (FLAG ly S Hp W mem md cid pos HAR Hin) as (Hpres & Hown & Happ & Hceil).
destruct (alx_client_img _ _ _ LAWS ly S Hp W mem md (flag_addr ly cid pos) HAR) as [Hhull Himg].
{ right. right. exists cid, pos. split; [exact Hin | reflexivity]. }
destruct (fr_img_cover_x B ARx LAWS ly S Hp W mem md HAR) as [C1 C2].
pose proof (in_app_addr _ _ (flag_addr ly cid pos) Happ ltac:(lia)) as AA.
unfold in_zr in Hhull.
split; [exact Hpres|]. split; [exact Hown|]. split.
- split; [exact AA | exact Himg].
- unfold app_addr in AA. split; [lia|]. split; [|exact Hceil].
  unfold zone2, off_img, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
End g.

(* The instance: W_LLVMFuzzerTestOneInput_top_x.v Definition ARX (:161-162) at its segs (:155, pa_segs PB_fr = frsegs),
   written out verbatim (top_x Requires this file, not the reverse), so FFL (:391) is `exact frame_flag_lawP_x_ARX`. *)
Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance CfImg_A.
Lemma ARX_laws_ffl : AR_laws_x (@pa_segs _ fr_prog_listing PB_fr) TfibB
  (fun ly S Hp W mem md => ARcf (cp := CfParams_reply) (@pa_segs _ fr_prog_listing PB_fr) TfibB ly S Hp W mem md /\ Hp = [])
  (@cf_head CfParams_reply).
Proof.
apply AR_laws_x_and_hp.
exact (AR_laws_x_cf (cp := CfParams_reply) frsegs TfibB (AR_laws_ok_cf (cp := CfParams_reply) frsegs TfibB)).
Qed.
Theorem frame_flag_lawP_x_ARX : frame_flag_lawP_x (@pa_segs _ fr_prog_listing PB_fr) TfibB
  (fun ly S Hp W mem md => ARcf (cp := CfParams_reply) (@pa_segs _ fr_prog_listing PB_fr) TfibB ly S Hp W mem md /\ Hp = []).
Proof.
apply (frame_flag_lawP_x_of_flag TfibB _ ARX_laws_ffl).
intros ly S Hp W mem md cid pos [HAR _] Hin.
exact (AR_flag_law_ok_cf (cp := CfParams_reply) frsegs TfibB ly S Hp W mem md cid pos HAR Hin).
Qed.
End i.
