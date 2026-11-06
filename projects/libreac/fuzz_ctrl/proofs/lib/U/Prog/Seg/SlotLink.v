(* The statement ubsan_halts of fuzz_ctrl from frame_ubsan (BUILD.md 6.5, 6.9; the twin of lib/Prog/Seg/SlotLink.v):
   destruct frame_ubsan and apply its slot obligation with G = [] (= frame_G), GI = fun _ _ => True and the slot
   theorem (U/Prog/Seg/Slot.v). The callee contracts the segment lemmas take come from the _holds theorems of
   lib/U/Prog (malloc and free from frame_allocator, inside frame_facts), and reac_ctrl_identity_fragment's
   contract from its _holds theorem. The premise left: the segment lemmas still to prove (seg_lemmas, under
   frame_facts, the callee contracts and the fragment contract, as each segment lemma is stated). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YK11 YM05 YO0f YO0d YO09 YL0g YL0i YI14 YI16 YL01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require
  reac_box_catalogue_c reac_box_catalogue reac_identity_init_c reac_identity_init
  memset_c memset memset_ro_c memset_ro memcpy_c memcpy memcpy_ro_c memcpy_ro
  memcpy_same_c memcpy_same memcpy_same_ro_c memcpy_same_ro
  bcmp_c bcmp bcmp_ro_c bcmp_ro memcmp_c memcmp memcmp_ro_c memcmp_ro memchr_c memchr memchr_ro_c memchr_ro
  strcmp_c strcmp kind_of_link1_c kind_of_link1 reac_ctrl_parse_c reac_ctrl_parse
  reac_ctrl_record_cksum_verify_c reac_ctrl_record_cksum_verify
  reac_ctrl_record_cksum_stamp_c reac_ctrl_record_cksum_stamp
  reac_ctrl_block_cksum_stamp_c reac_ctrl_block_cksum_stamp
  reac_ctrl_identity_reply_c reac_ctrl_identity_reply reac_identity_ingest_c reac_identity_ingest
  dt1_head_c dt1_head name_field_c name_field
  build_dt1_single_c build_dt1_single reac_box_model_block_c reac_box_model_block
  reac_box_catalogue_match_c reac_box_catalogue_match reac_ports_parse_c reac_ports_parse
  declaration_of_c declaration_of reac_ports_unknown_c reac_ports_unknown
  reac_ctrl_kind_name_c reac_ctrl_kind_name reac_ctrl_checksum_verify_c reac_ctrl_checksum_verify
  reac_ctrl_headamp_record_verify_c reac_ctrl_headamp_record_verify
  reac_ctrl_classify_box_frame_c reac_ctrl_classify_box_frame
  ctrl_lay_block_c ctrl_lay_block reac_braid_encode_ns0_c reac_braid_encode_ns0 ctrl_finish_c ctrl_finish
  ctrl_emit_as_c ctrl_emit_as reac_box_model_upstream_width_c reac_box_model_upstream_width
  reac_ctrl_build_as_c reac_ctrl_build_as reac_ctrl_identity_fragment_c reac_ctrl_identity_fragment
  record_sum_closes_c record_sum_closes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.Seg Require Import Slot.
From OSSVerify.libreac.fuzz_ctrl Require Statements.
Import ListNotations.

(* The contracts of the callees of LLVMFuzzerTestOneInput (callee-claims.md, plan-ubsan section 4), the _ro
   variants and the two model facts declaration_of_rows and reac_identity_ingest_id_ok_kept, except malloc and
   free (frame_allocator) and reac_ctrl_identity_fragment; record_sum_closes is the ubsan build's extra callee. *)
Definition callee_contracts : Prop :=
  reac_box_catalogue_c.reac_box_catalogue_contract /\
  reac_identity_init_c.reac_identity_init_contract /\
  memset_c.memset_contract /\ memset_ro_c.memset_ro_contract /\
  memcpy_c.memcpy_contract /\ memcpy_ro_c.memcpy_ro_contract /\
  memcpy_same_c.memcpy_same_contract /\ memcpy_same_ro_c.memcpy_same_ro_contract /\
  bcmp_c.bcmp_contract /\ bcmp_ro_c.bcmp_ro_contract /\
  memcmp_c.memcmp_contract /\ memcmp_ro_c.memcmp_ro_contract /\
  memchr_c.memchr_contract /\ memchr_ro_c.memchr_ro_contract /\
  strcmp_c.strcmp_contract /\
  reac_ctrl_build_as_c.reac_ctrl_build_as_contract /\
  reac_ctrl_parse_c.reac_ctrl_parse_contract /\
  reac_ctrl_identity_reply_c.reac_ctrl_identity_reply_contract /\
  reac_identity_ingest_c.reac_identity_ingest_contract /\
  reac_identity_ingest_c.reac_identity_ingest_id_ok_kept /\
  reac_box_catalogue_match_c.reac_box_catalogue_match_contract /\
  reac_ports_parse_c.reac_ports_parse_contract /\
  declaration_of_c.declaration_of_contract /\ declaration_of_c.declaration_of_rows /\
  reac_ports_unknown_c.reac_ports_unknown_contract /\
  reac_ctrl_kind_name_c.reac_ctrl_kind_name_contract /\
  reac_ctrl_checksum_verify_c.reac_ctrl_checksum_verify_contract /\
  reac_ctrl_headamp_record_verify_c.reac_ctrl_headamp_record_verify_contract /\
  reac_ctrl_classify_box_frame_c.reac_ctrl_classify_box_frame_contract /\
  record_sum_closes_c.record_sum_closes_contract.

Theorem callee_contracts_holds : callee_contracts.
Proof.
  pose proof memset.memset_holds as MSET.
  pose proof memcpy.memcpy_holds as MCPY.
  pose proof bcmp.bcmp_holds as BCMP.
  pose proof reac_ctrl_record_cksum_verify.reac_ctrl_record_cksum_verify_holds as CKV.
  pose proof dt1_head.dt1_head_holds as DT1.
  pose proof (reac_ctrl_parse.reac_ctrl_parse_holds MSET MCPY BCMP kind_of_link1.kind_of_link1_holds) as PARSE.
  pose proof (reac_box_model_block.reac_box_model_block_holds MSET MCPY DT1 (name_field.name_field_holds MSET)
                (build_dt1_single.build_dt1_single_holds DT1 MCPY)) as MBLK.
  pose proof (ctrl_finish.ctrl_finish_holds reac_ctrl_record_cksum_stamp.reac_ctrl_record_cksum_stamp_holds
                reac_ctrl_block_cksum_stamp.reac_ctrl_block_cksum_stamp_holds) as FIN.
  pose proof (ctrl_emit_as.ctrl_emit_as_holds MSET MCPY (ctrl_lay_block.ctrl_lay_block_holds MSET MCPY MBLK)
                reac_braid_encode_ns0.reac_braid_encode_ns0_holds FIN) as EMIT.
  unfold callee_contracts.
  split; [exact reac_box_catalogue.reac_box_catalogue_holds|].
  split; [exact (reac_identity_init.reac_identity_init_holds MSET)|].
  split; [exact MSET|]. split; [exact memset_ro.memset_ro_holds|].
  split; [exact MCPY|]. split; [exact memcpy_ro.memcpy_ro_holds|].
  split; [exact memcpy_same.memcpy_same_holds|]. split; [exact memcpy_same_ro.memcpy_same_ro_holds|].
  split; [exact BCMP|]. split; [exact bcmp_ro.bcmp_ro_holds|].
  split; [exact memcmp.memcmp_holds|]. split; [exact memcmp_ro.memcmp_ro_holds|].
  split; [exact memchr.memchr_holds|]. split; [exact memchr_ro.memchr_ro_holds|].
  split; [exact strcmp.strcmp_holds|].
  split; [exact (reac_ctrl_build_as.reac_ctrl_build_as_holds EMIT
                   reac_box_model_upstream_width.reac_box_model_upstream_width_holds)|].
  split; [exact PARSE|].
  split; [exact (reac_ctrl_identity_reply.reac_ctrl_identity_reply_holds PARSE CKV)|].
  split; [exact reac_identity_ingest.reac_identity_ingest_holds|].
  split; [exact reac_identity_ingest.reac_identity_ingest_id_ok_kept_holds|].
  split; [exact (reac_box_catalogue_match.reac_box_catalogue_match_holds PARSE MBLK BCMP)|].
  split; [exact reac_ports_parse.reac_ports_parse_holds|].
  split; [exact (declaration_of.declaration_of_holds MCPY)|].
  split; [exact declaration_of.declaration_of_rows_holds|].
  split; [exact reac_ports_unknown.reac_ports_unknown_holds|].
  split; [exact reac_ctrl_kind_name.reac_ctrl_kind_name_holds|].
  split; [exact reac_ctrl_checksum_verify.reac_ctrl_checksum_verify_holds|].
  split; [exact reac_ctrl_headamp_record_verify.reac_ctrl_headamp_record_verify_holds|].
  split; [exact (reac_ctrl_classify_box_frame.reac_ctrl_classify_box_frame_holds PARSE BCMP
                   reac_ctrl_checksum_verify.reac_ctrl_checksum_verify_holds)|].
  exact record_sum_closes.record_sum_closes_holds.
Qed.

Theorem fragment_contract_holds : reac_ctrl_identity_fragment_c.reac_ctrl_identity_fragment_contract.
Proof.
  exact (reac_ctrl_identity_fragment.reac_ctrl_identity_fragment_holds memcpy.memcpy_holds bcmp.bcmp_holds
           reac_ctrl_record_cksum_verify.reac_ctrl_record_cksum_verify_holds).
Qed.

Section Link.
(* The segment lemmas, as a segment file states each of them once its Section closes. *)
Hypothesis SEGS : forall (fx : FPState) (rc : RunCeil) (B : malloc_syms) (APIf : forall rc : RunCeil, AllocAPI B)
    (LS : lib_shape) (SH : sink_head) (SK : sink_syms) (ra empty : Z),
  frame_facts B APIf LS SH SK ra empty -> callee_contracts ->
  reac_ctrl_identity_fragment_c.reac_ctrl_identity_fragment_contract ->
  seg_lemmas B APIf ra empty.

Theorem ubsan_halts_of_frame : frame_ubsan -> Statements.ubsan_halts.
Proof.
  intros HF. destruct (frame_ubsan_split HF) as (B & API & LS & SH & SK & ra & empty & FF & OBL).
  apply (OBL [] (fun _ _ => True)).
  - intros a Ha. exact Ha.
  - intros j m m' _ _. exact I.
  - intros mem _. exact I.
  - intros rc fx j Hj.
    exact (slot_of_lemmas B API ra empty FF
             (SEGS fx rc B API LS SH SK ra empty FF callee_contracts_holds fragment_contract_holds) j Hj).
Qed.

End Link.
