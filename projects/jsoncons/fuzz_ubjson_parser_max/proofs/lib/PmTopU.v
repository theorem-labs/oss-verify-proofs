(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec StoreOk ShapeAlg SpinAlg HeapIface LibIface L5Defs L5Core
PmLayout PmLayoutU PmModel PmStatics PmSpecs PmSpecsU.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMTU.
Import PMU.
Definition TOPK : Z := 512.
Definition TOPB (len : Z) : Z := 2 ^ 29 + 8 * len.
Definition TopLay (L : heap_layout) : lib_layout := {|
ll_heap := L;
ll_entry := 0x342bc;
ll_gp := 0x10800;
ll_empty := 0xc7290;
ll_initc := [(0xc8be8, 0xc8cb0); (0xe8f20, 0xe8f28); (0xe8f48, 0xe8f50); (0xe8f78, 0xe8fa8); (0xe8f43, 0xe8f44); (0xe9018, 0xe901c)];
ll_init_cells := [(0xe8d00, 4%nat, 1); (0xe8d08, 8%nat, 0xe8d10); (0xe8d18, 8%nat, 0x99ad0); (0xe8e18, 8%nat, 0x34244)];
ll_init_img := [(0x10000, 0xb7230); (0xc7285, 0xc8be0); (0xe8cb8, 0xe8cd8);
(0xe8cf8, 0xe8d00); (0xe8d04, 0xe8d08); (0xe8d10, 0xe8d18); (0xe8d20, 0xe8e18); (0xe8e20, 0xe8f18);
(0xe8f43, 0xe8f44); (0xe9018, 0xe901c)];
ll_td_self := 0xc8be8; ll_td_tid := 0xc8c08; ll_td_locale := 0xc8c80; ll_locale := 0xe8f78; ll_td_canary := 0xc8ca0;
ll_guard := 0xe8f20; ll_auxvp := 0xe8f48;
ll_phdr := 0x10040; ll_phent := 56; ll_phnum := 10;
ll_rw_lo := 0xb7120;
ll_stack := 65536;
ll_credit := fun len => (TOPK, TOPB len);
ll_foot := pm_foot AD |}.
Definition TopLS : lib_statics := PMST.TopLS RSEGS AD.
Lemma lay_ok_U L : PMU.layout L -> PMST.lay_ok RSEGS AD (TopLay L).
Proof.
intros LY. constructor; cbn [TopLay ll_heap ll_foot ll_rw_lo ll_guard ll_initc ll_init_img ll_init_cells].
- exact (ly_segs L LY).
- reflexivity.
- reflexivity.
- reflexivity.
- exists (0xe8f20, 0xe8f28). cbn. split; [auto| lia].
- intros iv [<-|[<-|[]]]; cbn [fst snd].
+ exists (0xe8f43, 0xe8f44). cbn. split; [auto 7| lia].
+ exists (0xe9018, 0xe901c). cbn. split; [auto 8| lia].
- intros iv [<-|[<-|[]]]; cbn [fst snd].
+ exists (0xe8f43, 0xe8f44). cbn. split; [auto 10| lia].
+ exists (0xe9018, 0xe901c). cbn. split; [auto 11| lia].
- exists (0x10000, 0xb7230). cbn. split; [auto| lia].
- intros iv Hin. unfold PMST.pm_foot_lib in Hin. cbn in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd].
+ exists (0xc7285, 0xc8be0). cbn. split; [auto| lia].
+ exists (0xc7285, 0xc8be0). cbn. split; [auto| lia].
+ exists (0xc7285, 0xc8be0). cbn. split; [auto| lia].
+ exists (0xc7285, 0xc8be0). cbn. split; [auto| lia].
- intros iv Hin. unfold PMST.ax_img in Hin. cbn in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd].
+ exists (0xe8cf8, 0xe8d00). cbn. split; [auto 6| lia].
+ exists (0xe8d04, 0xe8d08). cbn. split; [auto 7| lia].
+ exists (0xe8d10, 0xe8d18). cbn. split; [auto 8| lia].
+ exists (0xe8d20, 0xe8e18). cbn. split; [auto 9| lia].
+ exists (0xe8e20, 0xe8f18). cbn. split; [auto 10| lia].
- intros c Hin. unfold PMST.ax_cells in Hin. cbn in Hin. cbn.
destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; auto 6.
Qed.
Section Top.
Variable scfg : SpuriousCfg.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMU.layout L.
Theorem top_iface_ok : lib_call_ok (TopLay L) scfg HI TopLS -> lib_iface_ok (TopLay L) scfg HI TopLS.
Proof.
intros CALL. constructor.
- exact CALL.
- exact (PMST.pm_statics_init RSEGS AD (TopLay L) addrs_wf_U (lay_ok_U L LY)).
- exact (PMST.pm_statics_frame RSEGS AD (TopLay L) addrs_wf_U (lay_ok_U L LY)).
Qed.
Theorem top_statics_exit : forall g M, ls_ok TopLS g M -> PMST.atexit_st RSEGS AD M (PMST.st_err g).
Proof. intros g M H. exact (PMST.pm_statics_exit RSEGS AD g M H). Qed.
End Top.
End PMTU.
