(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec StoreOk ShapeAlg SpinAlg HeapIface LibIface L5Defs L5Core
PmLayout PmLayoutS PmModel PmStatics PmSpecs PmSpecsS.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMTS.
Import PMS.
Definition TOPK : Z := 512.
Definition TOPB (len : Z) : Z := 2 ^ 29 + 8 * len.
Definition TopLay (L : heap_layout) : lib_layout := {|
ll_heap := L;
ll_entry := 0x3404c;
ll_gp := 0x10800;
ll_empty := 0xc6240;
ll_initc := [(0xc7b98, 0xc7c60); (0xe7ed0, 0xe7ed8); (0xe7ef8, 0xe7f00); (0xe7f28, 0xe7f58); (0xe7ef3, 0xe7ef4); (0xe7fc8, 0xe7fcc)];
ll_init_cells := [(0xe7cb0, 4%nat, 1); (0xe7cb8, 8%nat, 0xe7cc0); (0xe7cc8, 8%nat, 0x98a7c); (0xe7dc8, 8%nat, 0x33fd4)];
ll_init_img := [(0x10000, 0xb61e0); (0xc6235, 0xc7b90); (0xe7c68, 0xe7c88);
(0xe7ca8, 0xe7cb0); (0xe7cb4, 0xe7cb8); (0xe7cc0, 0xe7cc8); (0xe7cd0, 0xe7dc8); (0xe7dd0, 0xe7ec8);
(0xe7ef3, 0xe7ef4); (0xe7fc8, 0xe7fcc)];
ll_td_self := 0xc7b98; ll_td_tid := 0xc7bb8; ll_td_locale := 0xc7c30; ll_locale := 0xe7f28; ll_td_canary := 0xc7c50;
ll_guard := 0xe7ed0; ll_auxvp := 0xe7ef8;
ll_phdr := 0x10040; ll_phent := 56; ll_phnum := 10;
ll_rw_lo := 0xb60d0;
ll_stack := 65536;
ll_credit := fun len => (TOPK, TOPB len);
ll_foot := pm_foot AD |}.
Definition TopLS : lib_statics := PMST.TopLS RSEGS AD.
Lemma lay_ok_S L : PMS.layout L -> PMST.lay_ok RSEGS AD (TopLay L).
Proof.
intros LY. constructor; cbn [TopLay ll_heap ll_foot ll_rw_lo ll_guard ll_initc ll_init_img ll_init_cells].
- exact (ly_segs L LY).
- reflexivity.
- reflexivity.
- reflexivity.
- exists (0xe7ed0, 0xe7ed8). cbn. split; [auto| lia].
- intros iv [<-|[<-|[]]]; cbn [fst snd].
+ exists (0xe7ef3, 0xe7ef4). cbn. split; [auto 7| lia].
+ exists (0xe7fc8, 0xe7fcc). cbn. split; [auto 8| lia].
- intros iv [<-|[<-|[]]]; cbn [fst snd].
+ exists (0xe7ef3, 0xe7ef4). cbn. split; [auto 10| lia].
+ exists (0xe7fc8, 0xe7fcc). cbn. split; [auto 11| lia].
- exists (0x10000, 0xb61e0). cbn. split; [auto| lia].
- intros iv Hin. unfold PMST.pm_foot_lib in Hin. cbn in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd].
+ exists (0xc6235, 0xc7b90). cbn. split; [auto| lia].
+ exists (0xc6235, 0xc7b90). cbn. split; [auto| lia].
+ exists (0xc6235, 0xc7b90). cbn. split; [auto| lia].
+ exists (0xc6235, 0xc7b90). cbn. split; [auto| lia].
- intros iv Hin. unfold PMST.ax_img in Hin. cbn in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd].
+ exists (0xe7ca8, 0xe7cb0). cbn. split; [auto 6| lia].
+ exists (0xe7cb4, 0xe7cb8). cbn. split; [auto 7| lia].
+ exists (0xe7cc0, 0xe7cc8). cbn. split; [auto 8| lia].
+ exists (0xe7cd0, 0xe7dc8). cbn. split; [auto 9| lia].
+ exists (0xe7dd0, 0xe7ec8). cbn. split; [auto 10| lia].
- intros c Hin. unfold PMST.ax_cells in Hin. cbn in Hin. cbn.
destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; auto 6.
Qed.
Section Top.
Variable scfg : SpuriousCfg.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Theorem top_iface_ok : lib_call_ok (TopLay L) scfg HI TopLS -> lib_iface_ok (TopLay L) scfg HI TopLS.
Proof.
intros CALL. constructor.
- exact CALL.
- exact (PMST.pm_statics_init RSEGS AD (TopLay L) addrs_wf_S (lay_ok_S L LY)).
- exact (PMST.pm_statics_frame RSEGS AD (TopLay L) addrs_wf_S (lay_ok_S L LY)).
Qed.
Theorem top_statics_exit : forall g M, ls_ok TopLS g M -> PMST.atexit_st RSEGS AD M (PMST.st_err g).
Proof. intros g M H. exact (PMST.pm_statics_exit RSEGS AD g M H). Qed.
End Top.
End PMTS.
