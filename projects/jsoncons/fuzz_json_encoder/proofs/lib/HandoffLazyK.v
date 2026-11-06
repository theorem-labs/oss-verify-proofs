(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AgentLib AxSymExec3K AxSymExec3SoundK AsanPlanCoreK AsanPlanK AsanPlanSoundK HandoffLedgerK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK.
Open Scope Z_scope.

Lemma hl_iv_subtract_apart : forall (a sz : word) lo hi q,
  bv_unsigned a + bv_unsigned sz <= 2 ^ 64 ->
  In q (iv_subtract a sz lo hi) ->
  bv_unsigned (fst q) + bv_unsigned (snd q) <= lo \/ hi <= bv_unsigned (fst q).
Proof.
  intros a sz lo hi q Hwf Hin. unfold iv_subtract in Hin.
  pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs.
  apply in_app_or in Hin as [Hin|Hin].
  - destruct (bv_unsigned a <? lo) eqn:Hc; [|destruct Hin]. apply Z.ltb_lt in Hc.
    destruct Hin as [<-|[]]. cbn [fst snd]. rewrite u64_lit by lia. left. lia.
  - destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:Hc; [|destruct Hin]. apply Z.ltb_lt in Hc.
    destruct Hin as [<-|[]]. cbn [fst snd]. rewrite (u64_lit (Z.max (bv_unsigned a) hi)) by lia. right. lia.
Qed.

Lemma hl_maps_subtract_apart : forall l lo hi q,
  (forall p, In p l -> bv_unsigned (fst p) + bv_unsigned (snd p) <= 2 ^ 64) ->
  In q (maps_subtract l lo hi) ->
  bv_unsigned (fst q) + bv_unsigned (snd q) <= lo \/ hi <= bv_unsigned (fst q).
Proof.
  induction l as [|[a sz] l IH]; intros lo hi q Hl Hin; [destruct Hin|].
  cbn [maps_subtract] in Hin. apply in_app_or in Hin as [Hin|Hin].
  - exact (hl_iv_subtract_apart a sz lo hi q (Hl (a, sz) (or_introl eq_refl)) Hin).
  - exact (IH lo hi q (fun p Hp => Hl p (or_intror Hp)) Hin).
Qed.

(* [comment removed for export] *)
Lemma hl_replay_sub : forall E h1 bS nS h2,
  (forall b n, In (HCons b n) (h1 ++ HSub bS nS :: h2) -> uE E b + uE E n <= 2 ^ 64 /\ 0 < uE E n) ->
  (forall b n, In (HCons b n) h1 -> uE E b + uE E n <= uE E bS \/ uE E bS + uE E nS <= uE E b) ->
  forall q, In q (hreplay E (h1 ++ HSub bS nS :: h2)) ->
    bv_unsigned (fst q) + bv_unsigned (snd q) <= uE E bS \/ uE E bS + uE E nS <= bv_unsigned (fst q).
Proof.
  intros E h1 bS nS h2. induction h1 as [|hop h1 IH]; intros Hwf Hap q Hin.
  - cbn [app hreplay] in Hin.
    apply (hl_maps_subtract_apart (hreplay E h2) _ _ q); [|exact Hin].
    intros p Hp. destruct (hl_replay E h2 (fun b n H => Hwf b n (or_intror H)) p Hp) as (_ & P2 & _). exact P2.
  - assert (IH' := IH (fun b n H => Hwf b n (or_intror H)) (fun b n H => Hap b n (or_intror H))).
    destruct hop as [b n|b n]; cbn [app hreplay] in Hin.
    + destruct Hin as [<-|Hin]; [|exact (IH' q Hin)]. cbn [fst snd]. exact (Hap b n (or_introl eq_refl)).
    + assert (WF : forall p, In p (hreplay E (h1 ++ HSub bS nS :: h2)) ->
                     0 < bv_unsigned (snd p) /\ bv_unsigned (fst p) + bv_unsigned (snd p) <= 2 ^ 64).
      { intros p Hp. destruct (hl_replay E _ (fun b' n' H => Hwf b' n' (or_intror H)) p Hp) as (P1 & P2 & _). auto. }
      destruct (hl_maps_subtract (hreplay E (h1 ++ HSub bS nS :: h2)) _ _ q (fun p Hp => let '(conj P1 P2) := WF p Hp in conj P2 P1) Hin)
        as (_ & p & Hp & Q2 & Q3).
      destruct (IH' p Hp) as [X|X]; [left | right]; lia.
Qed.

(* [comment removed for export] *)
Lemma hl_page_piece : forall (w : word) lazy, page_in_ranges (page_base w) lazy = true ->
  exists q, In q lazy /\ bv_unsigned (fst q) <= bv_unsigned (page_base w) /\ bv_unsigned (page_base w) + 4096 <= bv_unsigned (fst q) + bv_unsigned (snd q).
Proof.
  intros w lazy H. unfold page_in_ranges in H. apply existsb_exists in H as (q & Hq & Hb). apply andb_prop in Hb as [B1 B2].
  apply Z.leb_le in B1. apply Z.leb_le in B2. exists q. unfold page_size in B2. auto.
Qed.
