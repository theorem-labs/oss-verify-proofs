(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec StoreOk AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import MState FP Mem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PIosRegs.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegLin SegTmpl SegCall.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import ST.
Open Scope Z_scope.

Module AGM.
Section Glue.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition munch_keep (lo hi : Z) (m m' : word -> option byte) : Prop :=
  (forall x : word, ~ (lo <= bv_unsigned x < hi) -> m' x = m x) /\
  (forall x : word, wview segs m x <> None -> wview segs m' x <> None).

(* [comment removed for export] *)
Definition survM (kn : list kentry) (s : sentry) (K : kentry) : bool :=
  match K with
  | KRange _ _ _ | KAlign _ _ | KDisj _ _ _ _ | KWr _ _ => true
  | KWord a w _ => (Nat.leb w 8 && st_apart kn s a (elen w))%bool
  | KZero a n | KBlob a n _ | KFill a n _ | KUnk a n => st_apart kn s a n
  | KImg lo hi => (Z.ltb (hi - lo) (2^64) && Z.leb 0 lo && st_apart kn s (SA (ELit 0) lo) (ELit (hi - lo)))%bool
  end.

Lemma apart_out : forall E M kn s a n, know_ok segs E M kn -> st_apart kn s a n = true -> flat E a (elenZ E n) ->
  forall i, 0 <= i < elenZ E n -> ~ (estart E (e_addr s) <= estart E a + i < estart E (e_addr s) + elenZ E (elen (e_width s))).
Proof.
  intros E M kn s a n HK H Hfl i Hi. pose proof (st_apart_ok segs E M kn s a n HK H) as D. lia.
Qed.

Lemma survM_ok : forall E M1 M2 kn s K,
  know_ok segs E M1 kn -> munch_keep (estart E (e_addr s)) (estart E (e_addr s) + elenZ E (elen (e_width s))) M1 M2 ->
  kentry_ok segs E M1 K -> survM kn s K = true -> kentry_ok segs E M2 K.
Proof.
  intros E M1 M2 kn s K HK (FR & FW) HK1 Hs.
  set (lo := estart E (e_addr s)) in *. set (hi := estart E (e_addr s) + elenZ E (elen (e_width s))) in *.
  assert (OUT : forall a n, st_apart kn s a n = true -> flat E a (elenZ E n) ->
            forall i, 0 <= i < elenZ E n -> M2 (Z_to_bv 64 (estart E a + i)) = M1 (Z_to_bv 64 (estart E a + i))).
  { intros a n Hp Hfl i Hi. apply FR. rewrite u_small by (destruct Hfl as (?&?&?&?); lia).
    exact (apart_out E M1 kn s a n HK Hp Hfl i Hi). }
  destruct K as [[kb kk] w v|[kb kk] n|[kb kk] n bk|lo' hi'|ae am|re rlo rhi|[wb wk] wn0|da1 dn1 da2 dn2|[kb kk] n fc|[kb kk] n];
    cbn [survM kentry_ok a_base a_off] in Hs, HK1 |- *.
  - (* [comment removed for export] *) apply andb_prop in Hs as [Hw8 Hp]. apply Nat.leb_le in Hw8. destruct HK1 as (Hw & Hfl & Hrd).
    split; [exact Hw|]. split; [exact Hfl|]. rewrite <- Hrd. apply rdn_ext.
    + rewrite (flat_u E _ _ Hfl). destruct Hfl as (?&?&?&?). lia.
    + intros x Hx. rewrite (flat_u E _ _ Hfl) in Hx. apply FR.
      assert (Hfl' : flat E (SA kb kk) (elenZ E (elen w))) by (rewrite elenZ_elen by exact Hw8; exact Hfl).
      pose proof (apart_out E M1 kn s (SA kb kk) (elen w) HK Hp Hfl' (bv_unsigned x - estart E (SA kb kk))) as A.
      rewrite elenZ_elen in A by exact Hw8. specialize (A ltac:(lia)). fold lo hi in A.
      replace (estart E (SA kb kk) + (bv_unsigned x - estart E (SA kb kk))) with (bv_unsigned x) in A by lia. exact A.
  - (* [comment removed for export] *) destruct HK1 as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. rewrite (OUT _ _ Hs Hfl i Hi). apply Hz. exact Hi.
  - (* [comment removed for export] *) destruct HK1 as (Hfl & Hl & Hz). split; [exact Hfl|]. split; [exact Hl|].
    intros i Hi. rewrite (OUT _ _ Hs Hfl i Hi). apply Hz. exact Hi.
  - (* [comment removed for export] *) apply andb_prop in Hs as [Hs Hp]. apply andb_prop in Hs as [Hsz _]. apply Z.ltb_lt in Hsz.
    destruct HK1 as (Hlo' & Hhi & Hn). split; [exact Hlo'|]. split; [exact Hhi|]. intros i Hi.
    assert (E0 : estart E (SA (ELit 0) lo') = lo') by (unfold estart; cbn [a_base a_off edenot]; rewrite Z_to_bv_unsigned; reflexivity).
    assert (E1 : elenZ E (ELit (hi' - lo')) = hi' - lo')
      by (unfold elenZ; cbn [edenot]; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn; apply Z.mod_small; lia).
    assert (Hfl : flat E (SA (ELit 0) lo') (elenZ E (ELit (hi' - lo')))) by (rewrite E1; unfold flat; rewrite E0; lia).
    pose proof (OUT _ _ Hp Hfl (i - lo') ltac:(rewrite E1; lia)) as O. rewrite E0 in O.
    replace (lo' + (i - lo')) with i in O by lia. rewrite O. apply Hn. exact Hi.
  - exact HK1.
  - exact HK1.
  - (* [comment removed for export] *) destruct HK1 as [Hfl Hs0]. split; [exact Hfl|]. intros d m Hd Hm.
    destruct m as [|m']; [reflexivity|]. remember (S m') as m eqn:Hmm.
    pose proof (flat_u E _ _ Hfl) as Hu. destruct Hfl as (F1 & F2 & F3 & F4).
    specialize (Hs0 d m Hd Hm).
    assert (Hb : bv_unsigned (Z_to_bv 64 (estart E (SA wb wk) + d)) = estart E (SA wb wk) + d) by (rewrite u_small; [reflexivity | lia]).
    apply store_ok_of_all; [rewrite Hb; lia|]. intros x Hx. rewrite Hb in Hx.
    pose proof (store_ok_all segs M1 m _ ltac:(rewrite Hb; lia) Hs0 x ltac:(rewrite Hb; exact Hx)) as Hv1.
    exact (FW x Hv1).
  - exact HK1.
  - (* [comment removed for export] *) destruct HK1 as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. rewrite (OUT _ _ Hs Hfl i Hi). apply Hz. exact Hi.
  - (* [comment removed for export] *) destruct HK1 as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. rewrite (OUT _ _ Hs Hfl i Hi). apply Hz. exact Hi.
Qed.

Lemma survM_all_ok : forall E M1 M2 kn s,
  know_ok segs E M1 kn -> munch_keep (estart E (e_addr s)) (estart E (e_addr s) + elenZ E (elen (e_width s))) M1 M2 ->
  know_ok segs E M2 (List.filter (survM kn s) kn).
Proof.
  intros E M1 M2 kn s HK FR. unfold know_ok. apply Forall_forall. intros K HKin. apply filter_In in HKin as [HKin Hs].
  exact (survM_ok E M1 M2 kn s K HK FR (proj1 (Forall_forall _ _) HK K HKin) Hs).
Qed.

Definition bridge_okM (knX : list kentry) (s : sentry) (knP : list kentry) (sg : list expr) (knT : list kentry) : bool :=
  let kn := List.filter (survM knX s) knX ++ knP in
  forallb (kimplied segs kn) (map (ksub sg) knT).

Lemma bridge_knowM : forall E M1 M2 knX s knP sg knT,
  know_ok segs E M1 knX -> munch_keep (estart E (e_addr s)) (estart E (e_addr s) + elenZ E (elen (e_width s))) M1 M2 ->
  know_ok segs E M2 knP -> bridge_okM knX s knP sg knT = true -> know_ok segs (senv E sg) M2 knT.
Proof.
  intros E M1 M2 knX s knP sg knT HK FR HP H. apply know_ok_ksub.
  apply (kimplied_all_ok segs E M2 (List.filter (survM knX s) knX ++ knP)); [|exact H].
  unfold know_ok. apply Forall_app. split; [exact (survM_all_ok E M1 M2 knX s HK FR) | exact HP].
Qed.

Lemma bridge_tmM : forall E M1 M2 knX s knP postregs sg T (R2 : bvmap 5 word) F2 fc2 rom ms2,
  know_ok segs E M1 knX ->
  munch_keep (estart E (e_addr s)) (estart E (e_addr s) + elenZ E (elen (e_width s))) M1 M2 ->
  know_ok segs E M2 knP -> regs_ok E postregs R2 ->
  regs_match (List.filter (survM knX s) knX ++ knP) postregs (map (esub sg) (t_regs T)) = true ->
  bridge_okM knX s knP sg (t_know T) = true ->
  ms2 = MS R2 F2 (Z_to_bv 64 (t_pc T)) fc2 None M2 rom -> frm0 fc2 -> PIosRegs.rfull R2 ->
  tm_okF segs T (senv E sg) M2 rom ms2.
Proof.
  intros E M1 M2 knX s knP postregs sg T R2 F2 fc2 rom ms2 HK FR HP HR HM HB -> HZ HF.
  assert (HKall : know_ok segs E M2 (List.filter (survM knX s) knX ++ knP)).
  { unfold know_ok. apply Forall_app. split; [exact (survM_all_ok E M1 M2 knX s HK FR) | exact HP]. }
  split; [exact HZ|]. split; [exact HF|]. exists R2. cbn [tstate s_pc s_regs s_log s_know mem_denot].
  split; [reflexivity|]. split.
  - intros r. rewrite (HR r). rewrite (regs_match_ok segs E M2 _ _ _ HKall HM r). unfold sr_get.
    destruct (bv_eqb r 0); [reflexivity|]. rewrite esub_den.
    replace (nth (ridx r) (map (esub sg) (t_regs T)) (ELit 0)) with (esub sg (nth (ridx r) (t_regs T) (ELit 0)));
      [reflexivity | rewrite <- (map_nth (esub sg) (t_regs T) (ELit 0) (ridx r)); reflexivity].
  - split; [exact I|]. exact (bridge_knowM E M1 M2 knX s knP sg (t_know T) HK FR HP HB).
Qed.

End Glue.
End AGM.
