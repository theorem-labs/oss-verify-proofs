(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec StoreOk AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import MState FP.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PIosRegs.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegLin SegTmpl SegCall.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import ST.
Open Scope Z_scope.

Module AGL.
Section Glue.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition rt_keep (E : env) (PR PRW : list SC.wn) (m m' : word -> option byte) : Prop :=
  (forall x : word, SC.in_PR E (Some PR) (bv_unsigned x) -> m' x = m x) /\
  (forall x : word, SC.in_PR E (Some PRW) (bv_unsigned x) -> wview segs m x <> None -> wview segs m' x <> None).

(* [comment removed for export] *)
Definition survR (kn : list kentry) (PR PRW : list SC.wn) (K : kentry) : bool :=
  match K with
  | KRange _ _ _ | KAlign _ _ | KDisj _ _ _ _ => true
  | KWord a w _ => (Nat.leb w 8 && SC.pres_in kn (Some PR) (a_base a) (a_off a) (elen w))%bool
  | KZero a n | KBlob a n _ | KFill a n _ | KUnk a n => SC.pres_in kn (Some PR) (a_base a) (a_off a) n
  | KWr a n => SC.pres_in kn (Some PRW) (a_base a) (a_off a) n
  | KImg lo hi => (Z.ltb (hi - lo) (2^64) && SC.pres_in kn (Some PR) (ELit 0) lo (ELit (hi - lo)))%bool
  end.

Lemma survR_ok : forall E M1 M2 kn PR PRW K,
  know_ok segs E M1 kn -> rt_keep E PR PRW M1 M2 ->
  kentry_ok segs E M1 K -> survR kn PR PRW K = true -> kentry_ok segs E M2 K.
Proof.
  intros E M1 M2 kn PR PRW K HK (FR & FW) HK1 Hs.
  (* [comment removed for export] *)
  assert (OUTR : forall b k n, SC.pres_in kn (Some PR) b k n = true -> flat E (SA b k) (elenZ E n) ->
            forall i, 0 <= i < elenZ E n ->
              M2 (Z_to_bv 64 (estart E (SA b k) + i)) = M1 (Z_to_bv 64 (estart E (SA b k) + i))).
  { intros b k n Hp Hfl i Hi. apply FR.
    rewrite u_small by (destruct Hfl as (?&?&?&?); lia). apply (SC.pres_in_ok segs E M1 kn (Some PR) b k n HK Hp). lia. }
  assert (OUTW : forall b k n, SC.pres_in kn (Some PRW) b k n = true -> flat E (SA b k) (elenZ E n) ->
            forall i, 0 <= i < elenZ E n ->
              (wview segs M1 (Z_to_bv 64 (estart E (SA b k) + i)) <> None ->
               wview segs M2 (Z_to_bv 64 (estart E (SA b k) + i)) <> None)).
  { intros b k n Hp Hfl i Hi. apply FW.
    rewrite u_small by (destruct Hfl as (?&?&?&?); lia). apply (SC.pres_in_ok segs E M1 kn (Some PRW) b k n HK Hp). lia. }
  destruct K as [[kb kk] w v|[kb kk] n|[kb kk] n bk|lo hi|ae am|re rlo rhi|[wb wk] wn0|da1 dn1 da2 dn2|[kb kk] n fc|[kb kk] n];
    cbn [survR kentry_ok a_base a_off] in Hs, HK1 |- *.
  - (* [comment removed for export] *) apply andb_prop in Hs as [Hw8 Hp]. apply Nat.leb_le in Hw8. destruct HK1 as (Hw & Hfl & Hrd).
    split; [exact Hw|]. split; [exact Hfl|]. rewrite <- Hrd. apply rdn_ext.
    + rewrite (flat_u E _ _ Hfl). destruct Hfl as (?&?&?&?). lia.
    + intros x Hx. rewrite (flat_u E _ _ Hfl) in Hx. apply FR.
      apply (SC.pres_in_ok segs E M1 kn (Some PR) kb kk (elen w) HK Hp). rewrite elenZ_elen by exact Hw8. lia.
  - (* [comment removed for export] *) destruct HK1 as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. rewrite (OUTR kb kk n Hs Hfl i Hi). apply Hz. exact Hi.
  - (* [comment removed for export] *) destruct HK1 as (Hfl & Hl & Hz). split; [exact Hfl|]. split; [exact Hl|].
    intros i Hi. rewrite (OUTR kb kk n Hs Hfl i Hi). apply Hz. exact Hi.
  - (* [comment removed for export] *) apply andb_prop in Hs as [Hsz Hp]. apply Z.ltb_lt in Hsz. destruct HK1 as (Hlo & Hhi & Hn).
    split; [exact Hlo|]. split; [exact Hhi|]. intros i Hi.
    assert (E0 : estart E (SA (ELit 0) lo) = lo) by (unfold estart; cbn [a_base a_off edenot]; rewrite Z_to_bv_unsigned; reflexivity).
    assert (E1 : elenZ E (ELit (hi - lo)) = hi - lo)
      by (unfold elenZ; cbn [edenot]; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn; apply Z.mod_small; lia).
    assert (HP : SC.in_PR E (Some PR) (bv_unsigned (Z_to_bv 64 i))).
    { rewrite u_small by lia. apply (SC.pres_in_ok segs E M1 kn (Some PR) (ELit 0) lo (ELit (hi - lo)) HK Hp). rewrite E0, E1. lia. }
    rewrite (FR _ HP). apply Hn. exact Hi.
  - exact HK1.
  - exact HK1.
  - (* [comment removed for export] *) destruct HK1 as [Hfl Hs0]. split; [exact Hfl|]. intros d m Hd Hm.
    destruct m as [|m']; [reflexivity|]. remember (S m') as m eqn:Hmm.
    pose proof (flat_u E _ _ Hfl) as Hu. destruct Hfl as (F1 & F2 & F3 & F4).
    specialize (Hs0 d m Hd Hm).
    assert (Hb : bv_unsigned (Z_to_bv 64 (estart E (SA wb wk) + d)) = estart E (SA wb wk) + d) by (rewrite u_small; [reflexivity | lia]).
    apply store_ok_of_all; [rewrite Hb; lia|]. intros x Hx. rewrite Hb in Hx.
    pose proof (store_ok_all segs M1 m _ ltac:(rewrite Hb; lia) Hs0 x ltac:(rewrite Hb; exact Hx)) as Hv1.
    replace x with (Z_to_bv 64 (estart E (SA wb wk) + (bv_unsigned x - estart E (SA wb wk))))
      by (apply bv_eq; rewrite u_small by lia; lia).
    apply (OUTW wb wk wn0 Hs ltac:(split; [exact F1|]; split; [exact F2|]; split; [exact F3 | exact F4]) (bv_unsigned x - estart E (SA wb wk))
                    ltac:(lia)).
    replace (Z_to_bv 64 (estart E (SA wb wk) + (bv_unsigned x - estart E (SA wb wk)))) with x by (apply bv_eq; rewrite u_small by lia; lia).
    exact Hv1.
  - exact HK1.
  - (* [comment removed for export] *) destruct HK1 as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. rewrite (OUTR kb kk n Hs Hfl i Hi). apply Hz. exact Hi.
  - (* [comment removed for export] *) destruct HK1 as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. rewrite (OUTR kb kk n Hs Hfl i Hi). apply Hz. exact Hi.
Qed.

Lemma survR_all_ok : forall E M1 M2 kn PR PRW,
  know_ok segs E M1 kn -> rt_keep E PR PRW M1 M2 -> know_ok segs E M2 (List.filter (survR kn PR PRW) kn).
Proof.
  intros E M1 M2 kn PR PRW HK FR. unfold know_ok. apply Forall_forall. intros K HKin. apply filter_In in HKin as [HKin Hs].
  exact (survR_ok E M1 M2 kn PR PRW K HK FR (proj1 (Forall_forall _ _) HK K HKin) Hs).
Qed.

(* [comment removed for export] *)
Definition bridge_ok (knX : list kentry) (PR PRW : list SC.wn) (knP : list kentry) (sg : list expr) (knT : list kentry) : bool :=
  let kn := List.filter (survR knX PR PRW) knX ++ knP in
  forallb (kimplied segs kn) (map (ksub sg) knT).

Lemma bridge_know : forall E M1 M2 knX PR PRW knP sg knT,
  know_ok segs E M1 knX -> rt_keep E PR PRW M1 M2 -> know_ok segs E M2 knP ->
  bridge_ok knX PR PRW knP sg knT = true -> know_ok segs (senv E sg) M2 knT.
Proof.
  intros E M1 M2 knX PR PRW knP sg knT HK FR HP H. apply know_ok_ksub.
  apply (kimplied_all_ok segs E M2 (List.filter (survR knX PR PRW) knX ++ knP)); [|exact H].
  unfold know_ok. apply Forall_app. split; [exact (survR_all_ok E M1 M2 knX PR PRW HK FR) | exact HP].
Qed.

(* [comment removed for export] *)
Lemma bridge_tm : forall E M1 M2 knX PR PRW knP postregs sg T (R2 : bvmap 5 word) F2 fc2 rom ms2,
  know_ok segs E M1 knX -> rt_keep E PR PRW M1 M2 -> know_ok segs E M2 knP -> regs_ok E postregs R2 ->
  regs_match (List.filter (survR knX PR PRW) knX ++ knP) postregs (map (esub sg) (t_regs T)) = true ->
  bridge_ok knX PR PRW knP sg (t_know T) = true ->
  ms2 = MS R2 F2 (Z_to_bv 64 (t_pc T)) fc2 None M2 rom -> frm0 fc2 -> PIosRegs.rfull R2 ->
  tm_okF segs T (senv E sg) M2 rom ms2.
Proof.
  intros E M1 M2 knX PR PRW knP postregs sg T R2 F2 fc2 rom ms2 HK FR HP HR HM HB -> HZ HF.
  assert (HKall : know_ok segs E M2 (List.filter (survR knX PR PRW) knX ++ knP)).
  { unfold know_ok. apply Forall_app. split; [exact (survR_all_ok E M1 M2 knX PR PRW HK FR) | exact HP]. }
  split; [exact HZ|]. split; [exact HF|]. exists R2. cbn [tstate s_pc s_regs s_log s_know mem_denot].
  split; [reflexivity|]. split.
  - intros r. rewrite (HR r). rewrite (regs_match_ok segs E M2 _ _ _ HKall HM r). unfold sr_get.
    destruct (bv_eqb r 0); [reflexivity|]. rewrite esub_den.
    replace (nth (ridx r) (map (esub sg) (t_regs T)) (ELit 0)) with (esub sg (nth (ridx r) (t_regs T) (ELit 0)));
      [reflexivity | rewrite <- (map_nth (esub sg) (t_regs T) (ELit 0) (ridx r)); reflexivity].
  - split; [exact I|]. exact (bridge_know E M1 M2 knX PR PRW knP sg (t_know T) HK FR HP HB).
Qed.

End Glue.
End AGL.
