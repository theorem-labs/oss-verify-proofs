(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (2 recorded proofs replaced by written proofs (carve_st_regions, dec_mprotect_rw_weaken)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk Arr ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import F_mm_syscalls MallocRep F_malloc_free MallocTree.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_B MallocModel_B MallocKit_B3 F_ntf_B.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import F_am_A F_am_K F_am_C.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_F_am_F () := "C59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_tailC1?~~~~~~~~~~~~~~~I35stdpp4gmap4gmap00C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC35stdpp4gmapBgmap_partial_alterC35stdpp8fin_maps:map_insertC35stdpp4gmap;gmap_lookupK47Corelib7Numbers7BinNums1Z02C59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocGc_avail_meta_area_countC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec6MallocIset_avail_meta_area_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocDset_avail_meta_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7upd_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7a_checkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8a_nslotsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4area01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9set_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBset_meta_area_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBset_meta_area_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8c_secretC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes2idK47Corelib4Init9Datatypes6option02C35stdpp6option;from_optionC59OSSVerify5KrLib4Spec6Malloc6a_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01C59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc6F_am_K8carve_stC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01K47Corelib7Numbers7BinNums8positive02C35stdpp4base6lookupC35stdpp4base6insertC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00I47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib4Spec6Malloc6NSLOTSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6Decode<dec_mprotectC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbK59OSSVerify5KrLib3Lib6Decode9range_ans01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib6Decode9range_ans02C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc6F_am_F9mp_strictC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notC47Corelib4Init5Logic7f_equalI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums8positive01K47Corelib4Init5Logic3and01C47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes?RelationClasses;reflexivityC59OSSVerify5KrLib6Malloc8ProgDeps?dec_mprotect_rwC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib6Decode9range_ans00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6ENOSYSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4respC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01K47Corelib4Init9Datatypes4bool02".
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac showregs := lazymatch goal with |- evt _ _ (MS ?R _ ?pc _ _ ?m _) => idtac "REGS" R "PC" pc "MEM" m end.

Section CANSEC1. Context {rc : runConstT}.
Lemma carve_st_regions st p : s_regions (carve_st st p) = s_regions st.
Proof.
  unfold carve_st. cbn [ctx upd_ctx s_ctx set_avail_meta_areas set_avail_meta_area_count c_meta_area_tail].
  destruct (c_meta_area_tail (s_ctx st)); reflexivity.
Qed.

(* [comment removed for export] *)
Definition mp_strict (a : range_ans) : Prop := match a with RgErr e => e <> 38 | RgDone b => b = true end.
Lemma dec_mprotect_rw_weaken A L rsp a : dec_mprotect_rw A L rsp = Some a -> dec_mprotect A L rsp = Some a /\ mp_strict a.
Proof.
  unfold dec_mprotect_rw. destruct (dec_mprotect A L rsp) as [[e|b]|]; [| | discriminate].
  - destruct (Z.eqb_spec e ENOSYS); [discriminate|]. intros H; inversion H; subst. split; [reflexivity|]. cbn. unfold ENOSYS in *. exact n.
  - destruct b; [| discriminate]. intros H; inversion H; subst. split; reflexivity.
Qed.


End CANSEC1.
