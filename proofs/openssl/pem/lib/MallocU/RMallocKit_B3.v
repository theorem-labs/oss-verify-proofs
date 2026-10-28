(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OssFuzzTheorems.openssl.pem.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import F_malloc_free MallocModel_B.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Export MallocKit_B3.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMallocKit_B.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.


Ltac rctx_same := intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.

(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.ZBridge.flia ::= first [ assumption | OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Lemma rmrep_set_usage : forall st m sc v,
  rmrep st m -> 0 <= sc < 48 ->
  rmrep (set_usage sc v st) (write_to_mem m (wa (RCTX + 464 + 8 * sc)) (le8 (wz v))).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros st m sc v MR Hsc. pose proof MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6) & _).
  pose proof (length_le8 (wz v)) as L8.
  pose proof (munch_write [(RCTX + 464 + 8 * sc, RCTX + 464 + 8 * sc + 8)] m m (RCTX + 464 + 8 * sc) (le8 (wz v)) (munch_refl _ m)
                ltac:(unfold RCTX; lia) ltac:(rewrite L8; unfold RCTX; lia) ltac:(rewrite L8; cbn [inside]; lia)) as MU.
  pose proof (wmono_write usegs m m (wa (RCTX + 464 + 8 * sc)) (le8 (wz v)) (wmono_refl usegs m)) as WM.
  eapply (rmrep_ctx_frameW st (set_usage sc v st) m _ _ MR MU WM); try reflexivity.
  - rctx_same.
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - left. rewrite usages_set_usage by lia. replace (RCTX + 464 + 8 * sc) with ((RCTX + 464) + 8 * sc) by lia.
    apply u64arr_write; [exact X3| rewrite usages_length; lia].
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - right. split; [| rctx_same].
    unfold ctx_tail_cells, brk_word, ctx. cbn [s_ctx set_usage upd_ctx c_seq c_brk set_usage_map]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rmrep_set_seq : forall st m v,
  rmrep st m -> 0 <= v < 256 ->
  rmrep (upd_ctx (set_seq v) st) (write_to_mem m (wa (RCTX + 912)) [b8 v]).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros st m v MR Hv. pose proof MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6) & _).
  pose proof (munch_write [(RCTX + 912, RCTX + 913)] m m (RCTX + 912) [b8 v] (munch_refl _ m)
                ltac:(unfold RCTX; lia) ltac:(cbn; unfold RCTX; lia) ltac:(cbn; lia)) as MU.
  pose proof (wmono_write usegs m m (wa (RCTX + 912)) [b8 v] (wmono_refl usegs m)) as WM.
  eapply (rmrep_ctx_frameW st (upd_ctx (set_seq v) st) m _ _ MR MU WM); try reflexivity.
  - rctx_same.
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - left.
    pose proof (rw_cells_write usegs m (RCTX + 912) (ctx_tail_cells st) 0 (C1 (b8 (c_seq (ctx st)))) (C1 (b8 v)) X6 eq_refl eq_refl I) as W.
    rewrite Z.add_0_r in W. cbn [cbytes cell_upd ctx_tail_cells Nat.eqb] in W.
    unfold ctx_tail_cells, brk_word, ctx in *. cbn [s_ctx upd_ctx set_seq c_seq c_brk]. exact W.
Qed.

(* [comment removed for export] *)
Lemma rmrep_set_unmap_seq : forall st m i v,
  rmrep st m -> 0 <= i < 32 ->
  rmrep (upd_ctx (fun c => set_unmap_seq_map (<[i := v]> (c_unmap_seq c)) c) st) (write_to_mem m (wa (RCTX + 848 + i)) [b8 v]).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros st m i v MR Hi. pose proof MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6) & _).
  pose proof (munch_write [(RCTX + 848 + i, RCTX + 848 + i + 1)] m m (RCTX + 848 + i) [b8 v] (munch_refl _ m)
                ltac:(unfold RCTX; lia) ltac:(cbn; unfold RCTX; lia) ltac:(cbn; lia)) as MU.
  pose proof (wmono_write usegs m m (wa (RCTX + 848 + i)) [b8 v] (wmono_refl usegs m)) as WM.
  eapply (rmrep_ctx_frameW st _ m _ _ MR MU WM); try reflexivity.
  - rctx_same.
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - left. rewrite unmap_seqs_set by lia. replace (RCTX + 848 + i) with ((RCTX + 848) + i) by lia.
    apply (u8arr_write usegs m (RCTX + 848) (unmap_seqs st) i (b8 v)); [exact X4| rewrite unmap_seqs_length; lia].
  - right. split; [reflexivity| rctx_same].
  - right. split; [| rctx_same].
    unfold ctx_tail_cells, brk_word, ctx. cbn [s_ctx upd_ctx c_seq c_brk set_unmap_seq_map]. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rmrep_group_hdr_zero : forall st m p gh bs,
  rmrep st m -> (s_groups st) !! p = Some gh ->
  (forall o, 0 <= o < 12 -> exists h, cell_read (get_shadow st (fst p)) (snd p + o) = Unknown h) ->
  length bs = 8%nat ->
  rmrep (del_group p st) (write_to_mem m (wa (conc st p)) bs).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros st m p gh bs MR Hp UNK L8.
  pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG).
  destruct (rgroup_conc st p gh WF Hp) as (r & Hr & Cp & Kr & Sp0 & Sp1 & SpA & RB0 & RBC).
  destruct (WR _ r Hr) as (_ & RBAL & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2].
  pose proof (round_up_pg_ge (r_len r)) as RU. unfold OssFuzzTheorems.Proofs.openssl.pem.lib.Spec.Malloc.MCEIL in RBC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
  eapply rmrep_transport_unowned.
  - apply rmrep_del_group. exact MR.
  - apply (munch_write [(conc st p, conc st p + 8)] m m (conc st p) bs (munch_refl _ m)); [lia| rewrite L8; cbn; lia| rewrite L8; cbn [inside]; lia].
  - apply wmono_write. apply wmono_refl.
  - intros lo hi a [E|[]] Ha. inversion E; subst lo hi. clear E.
    intros [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
    + unfold RCTX in C. lia.
    + unfold RMLOCK in C. lia.
    + unfold RNEED_LOCKS in C. lia.
    + unfold RPAGE_SIZE in C. lia.
    + destruct C as (ak & ar & Hak & Hin). cbn in Hak.
      destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & _).
      assert (NE : fst ak <> fst p) by (intros E; rewrite E, Hr in Hra; inversion Hra; subst; congruence).
      change (conc (del_group p st) ak) with (conc st ak) in Hin.
      pose proof (rarea_lr_lo st ak ar ra WF Hak Hra). pose proof (lr_lo_group r Kr).
      destruct (DJ (fst ak) ra (fst p) r Hra Hr NE); lia.
    + destruct C as (b & gh' & Hb & Hin). cbn in Hb. apply lookup_delete_Some in Hb. destruct Hb as [NEb Hb].
      change (conc (del_group p st) b) with (conc st b) in Hin.
      destruct (rgroup_conc st b gh' WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & _).
      destruct (N.eq_dec (fst b) (fst p)) as [E|NE].
      * rewrite E, Hr in Hrb. inversion Hrb; subst rb.
        assert (snd b <> snd p) by (intros E2; apply NEb; destruct b, p; cbn in *; congruence).
        Z.div_mod_to_equations. lia.
      * pose proof (lr_lo_group rb Krb). pose proof (lr_lo_group r Kr). destruct (DJ (fst b) rb (fst p) r Hrb Hr NE); lia.
    + destruct C as (rid & r' & v & Hr' & Hk' & Hin & HC). cbn in Hr'. change (get_shadow (del_group p st) rid) with (get_shadow st rid) in HC.
      destruct (N.eq_dec rid (fst p)) as [E|NE].
      * subst rid. rewrite Hr in Hr'. inversion Hr'; subst r'.
        destruct (UNK (a - r_base r - snd p) ltac:(lia)) as [h Hh].
        replace (snd p + (a - r_base r - snd p)) with (a - r_base r) in Hh by lia. rewrite Hh in HC. discriminate.
      * pose proof (lr_lo_group r' Hk'). pose proof (lr_lo_group r Kr). destruct (DJ rid r' (fst p) r Hr' Hr NE); lia.
    + unfold RGOT_SSP in C. lia.
    + unfold RSSP_GUARD, RVMLOCK in C. lia.
Qed.

Lemma rmrep_grp_del_eq : forall st m g p, rmrep (del_group p st) m -> rmrep (grp_del st g p) m.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros. unfold grp_del. apply rmrep_del_slots. exact H. Qed.
End WithCeiling0.
