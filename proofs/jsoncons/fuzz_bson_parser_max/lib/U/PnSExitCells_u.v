(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec StepTac StoreOk HeapIface LibIface L5Defs L5Core
     PmLayout PmModel PmStatics PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnStatics. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnTopS_u Bs0Exit_run1_u.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNSXC.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Abbreviation AD := PnLayoutS_u.ADDR_S.
Abbreviation AN := PnLayoutS_u.NADDR_S.

(* [comment removed for export] *)
Lemma img_lock : rdn RSEGS (fun _ => None) (Z_to_bv 64 0xea00c) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
Lemma img_next : rdn RSEGS (fun _ => None) (Z_to_bv 64 0xea020) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.

(* [comment removed for export] *)
Lemma rdn_clear (M : word -> option byte) lo hi a (n : nat) :
  L5.img_clear M lo hi -> lo <= a -> a + Z.of_nat n <= hi -> 0 <= a < 2 ^ 64 -> hi <= 2 ^ 64 ->
  rdn RSEGS M (Z_to_bv 64 a) n = rdn RSEGS (fun _ => None) (Z_to_bv 64 a) n.
Proof.
  intros C H1 H2 H3 H4. apply rdn_ext.
  - rewrite L5.unsigned_lit by lia. lia.
  - intros x Hx. rewrite L5.unsigned_lit in Hx by lia. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply C. lia.
Qed.

(* [comment removed for export] *)
Definition axmap (ax : PNST.bax) : axv :=
  match ax with PNST.AX0 => AXg | PNST.AXc => AXgc | PNST.AXs => AXgs | PNST.AXcs => AXgcs | PNST.AXsc => AXgsc end.

Lemma atexit_cells_of_st M ax : PNST.batexit_st RSEGS AD AN M ax -> PNST.bdec_ok RSEGS AN M (PNST.bax_dec ax) -> atexit_cells M (axmap ax).
Proof.
  unfold PNST.batexit_st, PNST.bdec_ok, atexit_cells. cbv zeta.
  destruct ax; cbn [PNST.bax_list PNST.bax_drv PNST.bax_dec axmap length Z.of_nat Pos.of_succ_nat Pos.succ app fst snd pa_atexit pa_errcat_dtor pa_errcat_obj AD PnLayoutS_u.ADDR_S AN PnLayoutS_u.NADDR_S
                   PNL.pn_str_dtor PNL.pn_inf_obj PNL.pn_nan_obj PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_drv_call PNL.pn_drv_guard PNST.slots_at].
  - intros (C0 & S1 & _ & HD & C24 & (F0 & A0 & _) & _ & _) _.
    split; [rewrite (rdn_clear M _ _ 0xea00c 4 C0) by lia; exact img_lock|].
    split; [exact HD|]. split; [exact S1|].
    split; [rewrite (rdn_clear M _ _ 0xea020 8 C24) by lia; exact img_next|].
    split; [exact F0|]. exact A0.
  - intros (C0 & S1 & _ & HD & C24 & (F0 & A0 & F1 & A1 & _) & _ & _) _.
    split; [rewrite (rdn_clear M _ _ 0xea00c 4 C0) by lia; exact img_lock|].
    split; [exact HD|]. split; [exact S1|].
    split; [rewrite (rdn_clear M _ _ 0xea020 8 C24) by lia; exact img_next|].
    split; [exact F0|]. split; [exact A0|]. split; [exact F1|]. exact A1.
  - intros (C0 & S1 & _ & HD & C24 & (F0 & A0 & F1 & A1 & F2 & A2 & _) & _ & _) DEC.
    destruct DEC as (_ & _ & (I0 & _) & (N0 & _)).
    split; [rewrite (rdn_clear M _ _ 0xea00c 4 C0) by lia; exact img_lock|].
    split; [exact HD|]. split; [exact S1|].
    split; [rewrite (rdn_clear M _ _ 0xea020 8 C24) by lia; exact img_next|].
    split; [exact F0|]. split; [exact A0|]. split; [exact F1|]. split; [exact A1|]. split; [exact F2|]. split; [exact A2|]. split; [exact I0|]. exact N0.
  - intros (C0 & S1 & _ & HD & C24 & (F0 & A0 & F1 & A1 & F2 & A2 & F3 & A3 & _) & _ & _) DEC.
    destruct DEC as (_ & _ & (I0 & _) & (N0 & _)).
    split; [rewrite (rdn_clear M _ _ 0xea00c 4 C0) by lia; exact img_lock|].
    split; [exact HD|]. split; [exact S1|].
    split; [rewrite (rdn_clear M _ _ 0xea020 8 C24) by lia; exact img_next|].
    split; [exact F0|]. split; [exact A0|]. split; [exact F1|]. split; [exact A1|]. split; [exact F2|]. split; [exact A2|].
    split; [exact F3|]. split; [exact A3|]. split; [exact I0|]. exact N0.
  - intros (C0 & S1 & _ & HD & C24 & (F0 & A0 & F1 & A1 & F2 & A2 & F3 & A3 & _) & _ & _) DEC.
    destruct DEC as (_ & _ & (I0 & _) & (N0 & _)).
    split; [rewrite (rdn_clear M _ _ 0xea00c 4 C0) by lia; exact img_lock|].
    split; [exact HD|]. split; [exact S1|].
    split; [rewrite (rdn_clear M _ _ 0xea020 8 C24) by lia; exact img_next|].
    split; [exact F0|]. split; [exact A0|]. split; [exact F1|]. split; [exact A1|]. split; [exact F2|]. split; [exact A2|].
    split; [exact F3|]. split; [exact A3|]. split; [exact I0|]. exact N0.
Qed.

(* [comment removed for export] *)
Theorem top_lsx : forall g M, ls_ok PNTS.TopLS g M -> exists ax : axv, atexit_cells M ax.
Proof. intros g M H. destruct (PNTS.top_statics_exit g M H) as [X D]. exists (axmap (PNST.st_ax g)). apply atexit_cells_of_st; assumption. Qed.
End PNSXC.
