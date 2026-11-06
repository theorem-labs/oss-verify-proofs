(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith List Lia Bool. From stdpp.bitvector Require definitions. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Plain. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BMode.
Module PnSpecsS.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMS.
Abbreviation RSEGS := Plain.M.loaded_segments.
Abbreviation AD := PnLayoutS.ADDR_S.

(* [comment removed for export] *)
Record layout (L : heap_layout) : Prop := LAY {
  ly_segs : hl_segs L = RSEGS;
  ly_tp : hl_tp L = pa_tp AD;
  ly_img_lo : hl_img_lo L = 0x10000;
  ly_img_hi : hl_img_hi L = 0xfa000;
  ly_stack : hl_stack L = 8224;
  ly_ro : forall a, hl_alloc_ro L a -> (hl_img_lo L <= a < hl_img_hi L) \/ hl_sptop L <= a;
  ly_errno : hl_errno L = 0xd87ac;
  ly_static : forall a, hl_alloc_static L a -> 0xf8c58 <= a < 0xf9000;        (* [comment removed for export] *)
  ly_kpm : 0 <= hl_k_per_malloc L <= 8;
  ly_bov : 0 <= hl_b_overhead L <= 6350523;
  ly_malloc : hl_malloc L = 0xab2b4;                                          (* [comment removed for export] *)
  ly_free : hl_free L = 0xab174;
  ly_ro_foot : forall a, hl_alloc_ro L a -> ~ (0xc6cc0 <= a < 0xf8ab8)                 (* [comment removed for export] *)
}.

Lemma addrs_wf_S : PMST.addrs_wf AD.
Proof.
  constructor; cbn; try lia.
  - intros iv [<-|[<-|[]]]; cbn; lia.
  - exists (0xd7082, 0xd77c0). cbn. split; [auto| lia].
Qed.

Section Names.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Definition opnew_spec := PMSP.opnew_spec RSEGS AD L HI.
Definition opdel_spec := PMSP.opdel_spec RSEGS AD L HI.
Definition opdel_sized_spec := PMSP.opdel_sized_spec RSEGS AD L HI.
Definition str_ctor_spec := PMSP.str_ctor_spec RSEGS AD L HI.
Definition locale_ctor_spec := PMSP.locale_ctor_spec RSEGS AD L HI.
Definition locale_dtor_spec := PMSP.locale_dtor_spec RSEGS AD L.
Definition iss_ctor_spec := PMSP.iss_ctor_spec RSEGS AD L HI.
Definition reader_ctor_spec := PMSP.reader_ctor_spec RSEGS AD L HI.
Definition syscat_spec := PMSP.syscat_spec RSEGS AD L HI.
Definition reset_spec := PMSP.reset_spec RSEGS AD L HI.
Definition make_ec_spec := PMSP.make_ec_spec RSEGS AD L HI.
Definition src_dtor_spec := PMSP.src_dtor_spec RSEGS AD L HI.
Definition ios_dtor_spec := PMSP.ios_dtor_spec RSEGS AD L HI.
Definition rtv_spec := PMSP.rtv_spec RSEGS AD L HI.
Definition read_value_spec := PMSP.read_value_spec RSEGS AD L HI.
Definition read_key_spec := PMSP.read_key_spec RSEGS AD L HI.
Definition begin_array_spec := PMSP.begin_array_spec RSEGS AD L HI.
Definition begin_object_spec := PMSP.begin_object_spec RSEGS AD L HI.
Definition end_array_spec := PMSP.end_array_spec RSEGS AD L HI.
Definition end_object_spec := PMSP.end_object_spec RSEGS AD L HI.
Definition get_length_spec := PMSP.get_length_spec RSEGS AD L HI.
Definition read_span_spec := PMSP.read_span_spec RSEGS AD L HI.
Definition parse_spec := PMSP.parse_spec RSEGS AD L HI.
Definition peek_spec := PMSP.peek_spec RSEGS AD L HI.
Definition ignore_spec := PMSP.ignore_spec RSEGS AD L HI.
Definition src_read_spec := PMSP.src_read_spec RSEGS AD L HI.
Definition fill_buffer_spec := PMSP.fill_buffer_spec RSEGS AD L HI.
Definition validate_spec := PMSP.validate_spec RSEGS AD L.
Definition is_base10_spec := PMSP.is_base10_spec RSEGS AD L.
Definition str_resize_spec := PMSP.str_resize_spec RSEGS AD L HI.
End Names.
End PMS.

End PnSpecsS.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.
Module PnTopS.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.LibIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PnQStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0104.PnSpecsS.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PQTS.
Abbreviation AQ := PnLayoutQS.QADDR_S.
Import PMS. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition TOPK : Z := 1024.
Definition TOPB (len : Z) : Z := 15 * 2 ^ 28.

Definition TopLay (L : heap_layout) : lib_layout := {|
  ll_heap := L;
  ll_entry := 0x390cc;
  ll_gp := 0x10800;
  ll_empty := 0xd6e30;
  ll_initc := [(0xd8788, 0xd8850); (0xf8ac0, 0xf8ac8); (0xf8ae8, 0xf8af0); (0xf8b18, 0xf8b48); (0xf8ae3, 0xf8ae4); (0xf8bb8, 0xf8bbc)];
  ll_init_cells := [(0xf88a0, 4, 1); (0xf88a8, 8, 0xf88b0); (0xf88b8, 8, 0xa927c); (0xf89b8, 8, 0x39054)];
  ll_init_img := [(0x10000, 0xc6dd0); (0xd6e21, 0xd6e24); (0xd6e25, 0xd8780); (0xf8858, 0xf8878);
                  (0xf8898, 0xf88a0); (0xf88a4, 0xf88a8); (0xf88b0, 0xf88b8); (0xf88c0, 0xf89b8); (0xf89c0, 0xf8ab8);
                  (0xf8ae3, 0xf8ae4); (0xf8bb8, 0xf8bbc)];
  ll_td_self := 0xd8788; ll_td_tid := 0xd87a8; ll_td_locale := 0xd8820; ll_locale := 0xf8b18; ll_td_canary := 0xd8840;
  ll_guard := 0xf8ac0; ll_auxvp := 0xf8ae8;
  ll_phdr := 0x10040; ll_phent := 56; ll_phnum := 10;
  ll_rw_lo := 0xc6cc0;
  ll_stack := 65536;
  ll_credit := fun len => (TOPK, TOPB len);
  ll_foot := pm_foot AD |}.

Definition TopLS : lib_statics := PQST.TopLS RSEGS AD AQ.

Lemma lay_ok_S L : PMS.layout L -> PQST.lay_ok RSEGS AD AQ (TopLay L).
Proof.
  intros LY. constructor; cbn [TopLay ll_heap ll_foot ll_rw_lo ll_guard ll_initc ll_init_img ll_init_cells].
  - exact (ly_segs L LY).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exists (0xf8ac0, 0xf8ac8). cbn. split; [auto 14| lia].
  - intros iv [<-|[<-|[]]]; cbn [fst snd].
    + exists (0xf8ae3, 0xf8ae4). cbn. split; [auto 14| lia].
    + exists (0xf8bb8, 0xf8bbc). cbn. split; [auto 14| lia].
  - intros iv [<-|[<-|[]]]; cbn [fst snd].
    + exists (0xf8ae3, 0xf8ae4). cbn. split; [auto 14| lia].
    + exists (0xf8bb8, 0xf8bbc). cbn. split; [auto 14| lia].
  - exists (0x10000, 0xc6dd0). cbn. split; [auto 14| lia].
  - intros iv Hin. unfold PQST.pm_foot_lib in Hin. cbn in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd].
    + exists (0xd6e25, 0xd8780). cbn. split; [auto 14| lia].
    + exists (0xd6e25, 0xd8780). cbn. split; [auto 14| lia].
    + exists (0xd6e25, 0xd8780). cbn. split; [auto 14| lia].
    + exists (0xd6e25, 0xd8780). cbn. split; [auto 14| lia].
  - intros iv Hin. unfold PQST.ax_img in Hin. cbn in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd].
    + exists (0xf8898, 0xf88a0). cbn. split; [auto 14| lia].
    + exists (0xf88a4, 0xf88a8). cbn. split; [auto 14| lia].
    + exists (0xf88b0, 0xf88b8). cbn. split; [auto 14| lia].
    + exists (0xf88c0, 0xf89b8). cbn. split; [auto 14| lia].
    + exists (0xf89c0, 0xf8ab8). cbn. split; [auto 14| lia].
  - intros c Hin. unfold PQST.ax_cells in Hin. cbn in Hin. cbn.
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; auto 14.
Qed.

Section Top.
Variable scfg : SpuriousCfg. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.

(* [comment removed for export] *)
Theorem top_iface_ok : lib_call_ok (TopLay L) scfg HI TopLS -> lib_iface_ok (TopLay L) scfg HI TopLS.
Proof.
  intros CALL. constructor.
  - exact CALL.
  - exact (PQST.pm_statics_init RSEGS AD AQ (TopLay L) addrs_wf_S (lay_ok_S L LY)).
  - exact (PQST.pm_statics_frame RSEGS AD AQ (TopLay L) addrs_wf_S (lay_ok_S L LY)).
Qed.

(* [comment removed for export] *)
Theorem top_statics_exit : forall g M, ls_ok TopLS g M -> PQST.atexit_st RSEGS AD AQ M (PMST.st_err g).
Proof. intros g M H. exact (PQST.pm_statics_exit RSEGS AD AQ g M H). Qed.
End Top.
End PQTS.

End PnTopS.
