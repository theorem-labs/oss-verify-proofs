(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCct.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition unw_short_ok : Prop :=
forall (ly : alayout) (rd : reader) (regs : bvmap 5 word) (r : Z),
4096 <= raZ regs -> frame0_ok ly regs = true -> bad_next (spZ regs) (ly_top ly) (s0Z regs) = false ->
spZ regs + 16 <= s0Z regs -> rdword rd (s0Z regs - 8) = Some r -> 0 <= r < 4096 ->
chain_pre ly rd regs [].
Lemma unw_short_ok_holds : unw_short_ok.
Proof.
intros ly rd regs r Hra Hf0 Hbn Hsp Hrd Hr. unfold chain_pre. rewrite Hf0, Hbn. split; [exact Hra|]. split; [exact Hsp|].
cbn [fpchain]. exists r. split; [exact Hrd | exact Hr].
Qed.
Lemma rrfc_chain : unw_short_ok ->
forall (ly : alayout) (rd : reader) (regs : bvmap 5 word) (U : list (list Z)) (st nb pdata site pc0 : Z),
s0Z regs = st + 16 -> raZ regs = site -> 4096 <= site -> site <> pc0 ->
spZ regs <= st -> st mod 8 = 0 ->
rdword rd (st + 8) = Some nb -> rdword rd st = Some pdata -> pdata <= st -> 0 <= nb ->
In [pc0; site] U -> (4096 <= nb -> In (rrfc_trace pc0 site nb) U) ->
exists ch, chain_pre ly rd regs ch /\ In (call_trace0 pc0 regs ch) U.
Proof.
intros USH ly rd regs U st nb pdata site pc0 Hs0 Hra Hsite Hne Hsp Hst8 Hnb Hpd Hpdlo Hnb0 HU2 HU3.
assert (Hsne : (site =? pc0) = false) by (apply Z.eqb_neq; exact Hne).
assert (T0 : call_trace0 pc0 regs [] = [pc0; site]) by (rewrite call_trace_nil, Hra, Hsne; reflexivity).
assert (Hm8 : (st + 16) mod 8 = 0) by (rewrite <- Z.add_mod_idemp_l, Hst8 by lia; reflexivity).
destruct (frame0_ok ly regs) eqn:Hf0.
2:{ exists []. split; [|rewrite T0; exact HU2]. unfold chain_pre. rewrite Hf0. split; [rewrite Hra; exact Hsite | reflexivity]. }
destruct (bad_next (spZ regs) (ly_top ly) (s0Z regs)) eqn:Hbn.
{ exists []. split; [|rewrite T0; exact HU2]. unfold chain_pre. rewrite Hf0, Hbn. split; [rewrite Hra; exact Hsite | reflexivity]. }
destruct (Z_lt_ge_dec nb 4096) as [Hlt | Hge].
-   exists []. split; [|rewrite T0; exact HU2].
apply (USH ly rd regs nb); [rewrite Hra; exact Hsite | exact Hf0 | exact Hbn | rewrite Hs0; lia | rewrite Hs0; replace (st + 16 - 8) with (st + 8) by lia; exact Hnb | lia].
-   exists [(st + 16, nb, pdata)]. split.
+ unfold chain_pre. rewrite Hf0, Hbn. split; [rewrite Hra; exact Hsite|]. split; [rewrite Hs0; lia|].
rewrite Hs0. cbn [fpchain]. split; [reflexivity|]. split; [exact Hm8|].
replace (st + 16 - 8) with (st + 8) by lia. replace (st + 16 - 16) with st by lia.
split; [exact Hnb|]. split; [exact Hpd|]. split; [lia|].
replace (bad_next (st + 16) (ly_top ly) pdata) with true; [reflexivity|].
symmetry. unfold bad_next. replace (pdata <=? st + 16) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
+ rewrite call_trace_cons, Hra, Hsne. cbn [flat_map app]. unfold rrfc_trace in HU3. specialize (HU3 ltac:(lia)).
unfold kUnwindMax. destruct (nb =? pc0); cbn [firstn app]; exact HU3.
Qed.
End a.
