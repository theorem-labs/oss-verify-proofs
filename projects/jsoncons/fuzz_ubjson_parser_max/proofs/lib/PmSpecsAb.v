(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec StoreOk HeapIface HeapIfaceA L5Defs PmLayout PmLayoutA PmModel PmStatics PmStaticsA HeapIfaceAJx L5DefsAB0 PmSpecsA PmSpecsAX.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMB.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation AD := PmLayoutA.ADDR_B.
Abbreviation AAD := PmLayoutA.AADDR_B.
Definition EXT : HAJ.ext_consts := HAJ.EXTC (paa_annotate AAD) 2304 (paa_cxa_atexit_icpt AAD) 1024 (pa_atexit AD) (paa_atexit_f0 AAD) (paa_atexit_a0 AAD) (pa_atexit_call AD) (pa_exit_guard AD) (paa_at_cxa_atexit AAD) (pa_need_locks AD).
Definition SM_PC (k : Z) : Z := nth (Z.to_nat k) [0x5d4fc; 0x5d670; 0x5d800; 0x5d99c; 0x5db48] 0.
Record layout (L : asan_layout) (C : asan_statics_cells) : Prop := LAY {
ly_as0 : L5A.as0_layout L C;
ly_tp : hl_tp L = pa_tp AD;
ly_sm : forall k, In k [0; 1; 2; 3; 4] -> hl_stack_malloc L k = SM_PC k;
ly_cost : hl_k_per_malloc L = 8 /\ hl_b_lin L = 3 /\ hl_b_overhead L = 2 ^ 21;
ly_static : forall a, PMST.dep AD a -> ~ hl_rt_static L a;
ly_static_data : forall a, 0x138ac0 <= a < 0x139380 -> ~ hl_rt_static L a;
ly_ro : forall a, hl_rt_ro L a -> 0x10000 <= a < 0x136000;
ly_cxa_cells : In (0x136350, 8, 0x11557c) (asc_cells C) /\ In (0x670ad0, 4, 0) (asc_cells C)
;
ly_ctr_static : forall a, hl_tp L + 16 <= a < hl_tp L + 20 -> hl_rt_static L a
}.
Lemma addrs_wf_A : PMST.addrs_wf AD.
Proof.
constructor; cbn; try lia.
- intros iv [<-|[<-|[]]]; cbn; lia.
- exists (0x66f2f2, 0x66fa30). cbn. split; [auto| lia].
Qed.
Section Names.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Definition opnew_spec := @PMSPA.opnew_spec SCFG_P RSEGS AD L ar HI.
Definition opdel_spec := @PMSPA.opdel_spec SCFG_P RSEGS AD L ar HI.
Definition opdel_sized_spec := @PMSPA.opdel_sized_spec SCFG_P RSEGS AD L ar HI.
Definition str_ctor_spec := @PMSPA.str_ctor_spec SCFG_P RSEGS AD L ar HI.
Definition locale_ctor_spec := @PMSPA.locale_ctor_spec SCFG_P RSEGS AD L ar HI.
Definition locale_dtor_spec := @PMSPA.locale_dtor_spec SCFG_P RSEGS AD L ar HI.
Definition iss_ctor_spec := @PMSPA.iss_ctor_spec SCFG_P RSEGS AD L ar HI.
Definition reader_ctor_spec := @PMSPA.reader_ctor_spec SCFG_P RSEGS AD L ar HI.
Definition syscat_spec := @PMSPA.syscat_spec SCFG_P RSEGS AD L ar HI.
Definition reset_spec := @PMSPA.reset_spec SCFG_P RSEGS AD L ar HI.
Definition make_ec_spec := @PMSPA.make_ec_spec SCFG_P RSEGS AD AAD L ar HI.
Definition src_dtor_spec := @PMSPA.src_dtor_spec SCFG_P RSEGS AD L ar HI.
Definition ios_dtor_spec := @PMSPA.ios_dtor_spec SCFG_P RSEGS AD L ar HI.
Definition rtv_spec := @PMSPA.rtv_spec SCFG_P RSEGS AD AAD L ar HI.
Definition read_value_spec := @PMSPA.read_value_spec SCFG_P RSEGS AD AAD L ar HI.
Definition read_key_spec := @PMSPA.read_key_spec SCFG_P RSEGS AD AAD L ar HI.
Definition begin_array_spec := @PMSPA.begin_array_spec SCFG_P RSEGS AD AAD L ar HI.
Definition begin_object_spec := @PMSPA.begin_object_spec SCFG_P RSEGS AD AAD L ar HI.
Definition end_array_spec := @PMSPA.end_array_spec SCFG_P RSEGS AD AAD L ar HI.
Definition end_object_spec := @PMSPA.end_object_spec SCFG_P RSEGS AD AAD L ar HI.
Definition get_length_spec := @PMSPA.get_length_spec SCFG_P RSEGS AD AAD L ar HI.
Definition read_span_spec := @PMSPA.read_span_spec SCFG_P RSEGS AD L ar HI.
Definition parse_spec := @PMSPA.parse_spec SCFG_P RSEGS AD AAD L ar HI.
Definition validate_spec := @PMSPA.validate_spec SCFG_P RSEGS AD L ar HI.
Definition is_base10_spec := @PMSPA.is_base10_spec SCFG_P RSEGS AD L ar HI.
Definition str_resize_spec := @PMSPA.str_resize_spec SCFG_P RSEGS AD L ar HI.
Definition xsgetn_spec := @PMSPA.xsgetn_spec SCFG_P RSEGS AD L ar HI.
Definition fill_buffer_spec := @PMSPA.fill_buffer_spec SCFG_P RSEGS AD L ar HI.
Definition peek_spec := @PMSPA.peek_spec SCFG_P RSEGS AD L ar HI.
Definition ignore_spec := @PMSPA.ignore_spec SCFG_P RSEGS AD L ar HI.
Definition src_read_spec := @PMSPA.src_read_spec SCFG_P RSEGS AD L ar HI.
Definition fill_buffer_tb_spec := @PMSPA.fill_buffer_tb_spec SCFG_P RSEGS AD L ar HI.
Definition srd_read_spec := @PMSPA.srd_read_spec SCFG_P RSEGS AD L ar HI.
Definition reader_read_spec := @PMSPA.reader_read_spec SCFG_P RSEGS AD AAD L ar HI.
Definition vec_dtor_spec := @PMSPA.vec_dtor_spec SCFG_P RSEGS AD L ar HI.
Definition push_mi_spec := @PMSAX.push_mi_spec SCFG_P RSEGS AD AAD L ar HI.
Definition push_miu_spec := @PMSAX.push_miu_spec SCFG_P RSEGS AD AAD L ar HI.
Definition push_ms_spec := @PMSAX.push_ms_spec SCFG_P RSEGS AD AAD L ar HI.
Definition push_msu_spec := @PMSAX.push_msu_spec SCFG_P RSEGS AD AAD L ar HI.
Definition ann_shrink_spec := @PMSAX.ann_shrink_spec SCFG_P RSEGS AD AAD L ar HI.
Definition ann_delete_spec := @PMSAX.ann_delete_spec SCFG_P RSEGS AD AAD L ar HI.
End Names.
End PMB.
