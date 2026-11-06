From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libreac.fuzz_grant Require Statements.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
  YK11 YM05 YO0d YO0f YO09 YP09 YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s YN03 YN2b YN33.
From OSSVerify.Proofs.libreac.fuzz_grant.lib Require Import
  ZAllocator SlotTopG Contract FrameAPI AllocSlots AllocRoom FrameProof AgreeFrame.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import SlotAgreePlain.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require LayLink ctrl_lay_block reac_box_model_block
  build_dt1_single memset memcpy.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require SlotAgree AgreeZlib ZAllocator SlotTopG FrameProof
  AllocCf.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Reusable Require YH02 YI5b YI5c YL0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require SlotTopCf LayLink ctrl_lay_block
  reac_box_model_block dt1_head name_field build_dt1_single memset memcpy.
Import ListNotations.
Open Scope Z_scope.

(* fuzz_grant ubsan_agrees: the frame's ubsan_agrees_of_slots (AgreeFrame.v) for the agreement shape (silent output,
   the agreement room of SBD_AG), the plain halts slot on that shape (Prog/SlotAgreePlain.grant_slot_plain_ag) and the
   ubsan cut-free slot (U/Prog/SlotTopCf.grant_slot_cg) with the zlib allocator's cut-free contracts (U/AllocCf.v) and
   the frame's budget law on the ubsan zlib allocator relation (U/AgreeZlib.zlib_limit: vm_limit at least
   SRC_LIM_MIN = 2 ^ 34). The plain names are imported; the ubsan names carry the prefix U. *)

#[local] Instance ag_shape : lib_shape.
Proof.
  refine {| LIBK := fun pl fs K => K (LL 0 fs []);
    lib_delta := fun n b => b;
    lib_room := fun b n => sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\ sb_cap b = U.SlotAgree.CAP_AG |}.
  intros pl fs K K' H. apply H.
Defined.

Lemma ag_room_calls : forall n k, @room_calls ag_shape n k U.AgreeZlib.SBD_AG.
Proof.
  intros n k. induction k as [|k IH]; cbn [room_calls]; [exact I|].
  split; [|exact IH]. cbn. unfold U.AgreeZlib.SBD_AG. cbn. lia.
Qed.

(* The plain frame facts as in FrameProof.frame_plain_holds, with the agreement room (128 <= CAP_AG <= CAPMAX). *)
Lemma facts_plain_ag :
  frame_facts_plain_ag src0_msyms (@zlib_API) ag_shape src0_sink_head src0_sink RA_LIB EMPTY.
Proof.
  split; [exact ms_segs_rsegs|].
  split; [vm_compute; reflexivity|].
  do 4 (split; [reflexivity|]).
  split; [exact errno_below_ceiling|].
  do 14 (split; [reflexivity|]).
  do 3 (split; [reflexivity|]).
  split; [reflexivity|].
  split; [split; vm_compute; reflexivity|].
  split; [exact ctx_not_ro|].
  split; [exact frame_G_facts|].
  split; [exact frame_RELRO_facts|].
  split; [intros pl fs K; reflexivity|].
  split; [intros n b; reflexivity|].
  split.
  { intros b n H. hnf in H. destruct H as (H1 & H2 & H3).
    refine (conj H1 (conj H2 _)). rewrite H3. split; apply Z.leb_le; vm_compute; reflexivity. }
  exact zlib_frame_allocator.
Qed.

(* The ubsan frame facts as in U/FrameProof.frame_ubsan_holds, with the agreement room. *)
Lemma facts_ubsan_ag :
  U.Prog.SlotTopCf.frame_facts_ubsan_ag U.Reusable.YH02.src0_msyms (@U.ZAllocator.zlib_API) ag_shape
    U.Reusable.YI5b.src0_sink_head U.Reusable.YI5c.src0_sink U.Reusable.YL0s.RA_LIB U.Reusable.YL0s.EMPTY.
Proof.
  split; [exact U.SlotTopG.ms_segs_rsegs|].
  split; [vm_compute; reflexivity|].
  do 4 (split; [reflexivity|]).
  split; [exact U.FrameProof.errno_below_ceiling|].
  do 14 (split; [reflexivity|]).
  do 3 (split; [reflexivity|]).
  split; [reflexivity|].
  split; [split; vm_compute; reflexivity|].
  split; [exact U.FrameProof.ctx_not_ro|].
  split; [exact U.FrameProof.frame_G_facts|].
  split; [exact U.FrameProof.frame_RELRO_facts|].
  split; [intros pl fs K; reflexivity|].
  split; [intros n b; reflexivity|].
  split.
  { intros b n H. hnf in H. destruct H as (H1 & H2 & H3).
    refine (conj H1 (conj H2 _)). rewrite H3. split; apply Z.leb_le; vm_compute; reflexivity. }
  exact U.FrameProof.zlib_frame_allocator.
Qed.

Theorem ubsan_agrees_holds : Statements.ubsan_agrees.
Proof.
  pose proof (lib.Prog.LayLink.ctrl_lay_block_link
    (lib.Prog.ctrl_lay_block.ctrl_lay_block_holds lib.Prog.memset.memset_holds lib.Prog.memcpy.memcpy_holds
      (lib.Prog.reac_box_model_block.reac_box_model_block_holds lib.Prog.memset.memset_holds
        lib.Prog.memcpy.memcpy_holds
        (lib.Prog.build_dt1_single.build_dt1_single_holds lib.Prog.memcpy.memcpy_holds)))) as LAYp.
  pose proof (U.Prog.LayLink.ctrl_lay_block_link
    (U.Prog.ctrl_lay_block.ctrl_lay_block_holds U.Prog.memset.memset_holds U.Prog.memcpy.memcpy_holds
      (U.Prog.reac_box_model_block.reac_box_model_block_holds U.Prog.memset.memset_holds U.Prog.memcpy.memcpy_holds
        U.Prog.dt1_head.dt1_head_holds (U.Prog.name_field.name_field_holds U.Prog.memset.memset_holds)
        (U.Prog.build_dt1_single.build_dt1_single_holds U.Prog.dt1_head.dt1_head_holds
          U.Prog.memcpy.memcpy_holds)))) as LAYu.
  apply (ubsan_agrees_of_slots ag_shape [] (fun _ _ => True) [] (fun _ _ => True)).
  - intros a (lo & len & [] & _).
  - intros j m m' _ _. exact I.
  - intros mem _. exact I.
  - intros rc fx j Hj.
    exact (grant_slot_plain_ag LAYp src0_msyms (@zlib_API) ag_shape src0_sink_head src0_sink RA_LIB EMPTY
      facts_plain_ag rc fx j Hj).
  - intros data. apply ag_room_calls.
  - intros a (lo & len & [] & _).
  - intros j m m' _ _. exact I.
  - intros mem _. exact I.
  - intros rc fx j Hj.
    exact (U.Prog.SlotTopCf.grant_slot_cg LAYu U.Reusable.YH02.src0_msyms (@U.ZAllocator.zlib_API) ag_shape
      U.Reusable.YI5b.src0_sink_head U.Reusable.YI5c.src0_sink U.Reusable.YL0s.RA_LIB U.Reusable.YL0s.EMPTY
      facts_ubsan_ag (fun rc' fx' => @U.AllocCf.zlib_malloc_contract_cf fx' rc')
      (fun rc' fx' => @U.AllocCf.zlib_free_contract_cf fx' rc') U.AgreeZlib.zlib_limit rc fx j Hj).
Qed.
