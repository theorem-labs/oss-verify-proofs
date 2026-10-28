(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec StoreOk ShapeAlg SpinAlg HeapIface LibIface L5Defs L5Core
     PmLayout PmModel PmStatics PmSpecs PgV8 PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnModel PnStatics. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnRunS_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNTS.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Abbreviation AD := PnLayoutS_u.ADDR_S.
Abbreviation AN := PnLayoutS_u.NADDR_S.

Definition TOPK : Z := 1024.
Definition TOPB (len : Z) : Z := 2 ^ 30 + 2 ^ 29 + 4 * len.

Definition TopLay (L : heap_layout) : lib_layout := {|
  ll_heap := L;
  ll_entry := 0x3471c;
  ll_gp := 0x10800;
  ll_empty := 0xc8560;
  ll_initc := [(0xc9ef8, 0xc9fc0); (0xea230, 0xea238); (0xea258, 0xea260); (0xea288, 0xea2b8); (0xea253, 0xea254); (0xea328, 0xea32c)];
  (* [comment removed for export] *)
  ll_init_img := [(0x10000, 0xb8500); (0xc8551, 0xc8554); (0xc8555, 0xc9ef0); (0xe9fc8, 0xe9fe8);
                  (0xea008, 0xea010); (0xea014, 0xea018); (0xea020, 0xea028); (0xea030, 0xea128); (0xea130, 0xea228);
                  (0xea253, 0xea254); (0xea328, 0xea32c)];
  ll_td_self := 0xc9ef8; ll_td_tid := 0xc9f18; ll_td_locale := 0xc9f90; ll_locale := 0xea288; ll_td_canary := 0xc9fb0;
  ll_guard := 0xea230; ll_auxvp := 0xea258;
  ll_phdr := 0x10040; ll_phent := 56; ll_phnum := 10;
  ll_rw_lo := 0xb83f0;
  ll_stack := 65536;
  ll_credit := fun len => (TOPK, TOPB len);
  ll_foot := PNST.pn_foot AD AN;
  ll_init_cells := [(0xea010, 4, 1); (0xea018, 8, 0xea020); (0xea028, 8, 0x9ad9c); (0xea128, 8, 0x346a4)] |}.

Definition TopLS : lib_statics := PNST.TopLS RSEGS AD AN.

Lemma lay_ok_B L : PMS.layout L -> PNST.lay_ok RSEGS AD AN (TopLay L).
Proof.
  intros LY. constructor; cbn [TopLay ll_heap ll_foot ll_rw_lo ll_guard ll_initc ll_init_img ll_init_cells].
  - exact (PMS.ly_segs L LY).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exists (0xea230, 0xea238). cbn. split; [auto 8| lia].
  - intros iv Hin. unfold pm_initc in Hin. cbn in Hin. destruct Hin as [<-|[<-|[]]]; cbn [fst snd].
    + exists (0xea253, 0xea254). cbn. split; [auto 8| lia].
    + exists (0xea328, 0xea32c). cbn. split; [auto 8| lia].
  - intros iv Hin. unfold pm_initc in Hin. cbn in Hin. destruct Hin as [<-|[<-|[]]]; cbn [fst snd].
    + exists (0xea253, 0xea254). cbn. split; [auto 12| lia].
    + exists (0xea328, 0xea32c). cbn. split; [auto 12| lia].
  - exists (0x10000, 0xb8500). cbn. split; [auto| lia].
  - (* [comment removed for export] *)
    intros iv Hin. unfold PNST.pn_foot, pm_foot, PNL.pn_d128_foot in Hin. cbn in Hin.
    repeat (destruct Hin as [<-|Hin]; [cbn [fst snd]; first [left; reflexivity
                                                  | right; exists (0xc8555, 0xc9ef0); cbn; split; [auto 12| lia]]|]).
    destruct Hin.
  - (* [comment removed for export] *)
    intros iv Hin. unfold PNST.drv_init_clear in Hin. cbn in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd];
      [ exists (0xea008, 0xea010) | exists (0xea014, 0xea018) | exists (0xea020, 0xea028) | exists (0xea030, 0xea128) | exists (0xea130, 0xea228) ];
      cbn; (split; [auto 12| lia]).
  - (* [comment removed for export] *) reflexivity.
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
  - exact (PNST.pn_statics_init RSEGS AD AN (TopLay L) PNRS.addrs_wf_B (lay_ok_B L LY)).
  - exact (PNST.pn_statics_frame RSEGS AD AN (TopLay L) PNRS.addrs_wf_B (lay_ok_B L LY)).
Qed.
End Top.

(* [comment removed for export] *)
Lemma pot_callB_le L n : PMS.layout L -> 0 <= n < 2 ^ 26 -> PMSP.credit_le (PNR.pot_callB L n) (TOPK, TOPB n).
Proof.
  intros LY Hn. pose proof (PMS.ly_kpm L LY) as K. pose proof (PMS.ly_bov L LY) as B.
  unfold PNR.pot_callB, PNR.pot_bstack, PM.pot_text, PGV8.pot_v8, PM.cost1, PM.credit_add, PMSP.credit_le, TOPK, TOPB, PM.vs_cap, PGV8.v8_cap, PM.CHUNK, PNM.BSZ.
  cbn [fst snd]. change (2 ^ 12) with 4096. change (2 ^ (0 + 1)) with 2. change (2 ^ 28) with 268435456. change (2 ^ 30) with 1073741824.
  change (2 ^ 29) with 536870912. change (2 ^ 26) with 67108864 in Hn. nia.
Qed.

(* [comment removed for export] *)
Theorem top_statics_exit : forall g M, ls_ok TopLS g M ->
  PNST.batexit_st RSEGS AD AN M (PNST.st_ax g) /\ PNST.bdec_ok RSEGS AN M (PNST.bax_dec (PNST.st_ax g)).
Proof. intros g M H. exact (PNST.pn_statics_exit RSEGS AD AN g M H). Qed.
End PNTS.
