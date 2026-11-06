(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec StoreOk ShapeAlg SpinAlg HeapIface LibIface L5Defs L5Core
     PmLayout PmModel PmStatics PmSpecs PgV8 PnLayout PnLayoutS PnModel PnStatics PnSpecsS PnRun PnRunS.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNTS.
Abbreviation RSEGS := Plain.M.loaded_segments.
Abbreviation AD := PnLayoutS.ADDR_S.
Abbreviation AN := PnLayoutS.NADDR_S.

Definition TOPK : Z := 1024.
Definition TOPB (len : Z) : Z := 2 ^ 30 + 2 ^ 29 + 4 * len.

Definition TopLay (L : heap_layout) : lib_layout := {|
  ll_heap := L;
  ll_entry := 0x343f4;
  ll_gp := 0x10800;
  ll_empty := 0xc6f80;
  ll_initc := [(0xc8918, 0xc89e0); (0xe8c50, 0xe8c58); (0xe8c78, 0xe8c80); (0xe8ca8, 0xe8cd8); (0xe8c73, 0xe8c74); (0xe8d48, 0xe8d4c)];
  (* [comment removed for export] *)
  ll_init_img := [(0x10000, 0xb6f20); (0xc6f71, 0xc6f74); (0xc6f75, 0xc8910); (0xe89e8, 0xe8a08);
                  (0xe8a28, 0xe8a30); (0xe8a34, 0xe8a38); (0xe8a40, 0xe8a48); (0xe8a50, 0xe8b48); (0xe8b50, 0xe8c48);
                  (0xe8c73, 0xe8c74); (0xe8d48, 0xe8d4c)];
  ll_td_self := 0xc8918; ll_td_tid := 0xc8938; ll_td_locale := 0xc89b0; ll_locale := 0xe8ca8; ll_td_canary := 0xc89d0;
  ll_guard := 0xe8c50; ll_auxvp := 0xe8c78;
  ll_phdr := 0x10040; ll_phent := 56; ll_phnum := 10;
  ll_rw_lo := 0xb6e08;
  ll_stack := 65536;
  ll_credit := fun len => (TOPK, TOPB len);
  ll_foot := PNST.pn_foot AD AN;
  ll_init_cells := [(0xe8a30, 4, 1); (0xe8a38, 8, 0xe8a40); (0xe8a48, 8, 0x997b4); (0xe8b48, 8, 0x3437c)] |}.

Definition TopLS : lib_statics := PNST.TopLS RSEGS AD AN.

Lemma lay_ok_B L : PMS.layout L -> PNST.lay_ok RSEGS AD AN (TopLay L).
Proof.
  intros LY. constructor; cbn [TopLay ll_heap ll_foot ll_rw_lo ll_guard ll_initc ll_init_img ll_init_cells].
  - exact (PMS.ly_segs L LY).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exists (0xe8c50, 0xe8c58). cbn. split; [auto 8| lia].
  - intros iv Hin. unfold pm_initc in Hin. cbn in Hin. destruct Hin as [<-|[<-|[]]]; cbn [fst snd].
    + exists (0xe8c73, 0xe8c74). cbn. split; [auto 8| lia].
    + exists (0xe8d48, 0xe8d4c). cbn. split; [auto 8| lia].
  - intros iv Hin. unfold pm_initc in Hin. cbn in Hin. destruct Hin as [<-|[<-|[]]]; cbn [fst snd].
    + exists (0xe8c73, 0xe8c74). cbn. split; [auto 12| lia].
    + exists (0xe8d48, 0xe8d4c). cbn. split; [auto 12| lia].
  - exists (0x10000, 0xb6f20). cbn. split; [auto| lia].
  - (* [comment removed for export] *)
    intros iv Hin. unfold PNST.pn_foot, pm_foot, PNL.pn_d128_foot in Hin. cbn in Hin.
    repeat (destruct Hin as [<-|Hin]; [cbn [fst snd]; first [left; reflexivity
                                                  | right; exists (0xc6f75, 0xc8910); cbn; split; [auto 12| lia]]|]).
    destruct Hin.
  - (* [comment removed for export] *)
    intros iv Hin. unfold PNST.drv_init_clear in Hin. cbn in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd];
      [ exists (0xe8a28, 0xe8a30) | exists (0xe8a34, 0xe8a38) | exists (0xe8a40, 0xe8a48) | exists (0xe8a50, 0xe8b48) | exists (0xe8b50, 0xe8c48) ];
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
