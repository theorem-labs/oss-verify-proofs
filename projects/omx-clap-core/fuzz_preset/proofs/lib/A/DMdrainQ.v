(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainQ.v (commit 67deba317dfb, blob c7b28d675768) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YP0m YP0e YP09 YP0l YP06 YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG06 YG03 YG0f YG0v YG0n YG0d YG0k.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG00cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AFeu AFey AFer.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import DMwalkIFA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma lcn_nth : forall ly iw m l z i b,
lcn ly iw m l z -> nth_error l i = Some b ->
bcell ly iw m b (fa ly (skipn (S i) l) z).
Proof.
intros ly iw m l z i. revert l. induction i as [|i IH]; intros [|b0 t] b HL HN; cbn [nth_error] in HN;
try discriminate; cbn [lcn skipn] in *.
- injection HN as <-. exact (proj1 HL).
- exact (IH t b (proj2 HL) HN).
Qed.

Lemma fa_skipn : forall ly l i, fa ly (skipn (S i) l) 0 = next_addr ly l i.
Proof.
intros ly l. unfold next_addr, fa, addrb.
induction l as [|b t IH]; intros [|i]; cbn [skipn nth_error]; try reflexivity.
- destruct t as [|b1 t1]; reflexivity.
- exact (IH i).
Qed.

Lemma lcn_next : forall ly iw m l i b,
lcn ly iw m l 0 -> nth_error l i = Some b ->
val_mem tfibsegs m (addrb ly b) 8 (next_addr ly l i).
Proof.
intros ly iw m l i b HL HN. pose proof (lcn_nth ly iw m l 0 i b HL HN) as HC.
rewrite fa_skipn in HC. exact (proj1 HC).
Qed.

Lemma lcn_size : forall ly iw m l z i b,
lcn ly iw m l z -> nth_error l i = Some b ->
val_mem tfibsegs m (addrb ly b + 8) 8 (b_bytes b).
Proof.
intros ly iw m l z i b HL HN. pose proof (lcn_nth ly iw m l z i b HL HN) as HC.
exact (proj1 (proj2 HC)).
Qed.

Lemma lcn_count : forall ly iw m l z i b,
lcn ly iw m l z -> nth_error l i = Some b ->
val_mem tfibsegs m (addrb ly b + 16) 8 (Z.of_nat (length (b_items b))).
Proof.
intros ly iw m l z i b HL HN. pose proof (lcn_nth ly iw m l z i b HL HN) as HC.
exact (proj1 (proj2 (proj2 HC))).
Qed.

Lemma fa_firstaddr : forall ly l, fa ly l 0 = AFer.firstaddr ly l.
Proof. intros ly [|b t]; reflexivity. Qed.

Lemma la_lastaddr : forall ly l, la ly l = AFer.lastaddr ly l.
Proof. intros ly l. unfold la, AFer.lastaddr, addrb, AFer.addr. destruct (rev l); reflexivity. Qed.

Lemma b_bytes_lb : forall b, (forall k, In k (b_items b) -> 0 <= ck_n k) -> kBatchBytes <= b_bytes b.
Proof.
intros b H. unfold b_bytes.
assert (A : 0 <= fold_right (fun k acc => ck_n k + acc) 0 (b_items b)).
{ induction (b_items b) as [|k l IH]; cbn [fold_right]; [lia|].
  pose proof (H k (or_introl eq_refl)). pose proof (IH (fun k' Hk => H k' (or_intror Hk))). lia. }
lia.
Qed.

Lemma sum_bytes_app_q : forall l1 l2, sum_bytes (l1 ++ l2) = sum_bytes l1 + sum_bytes l2.
Proof.
induction l1 as [|b l IH]; intros l2; cbn [app]; [reflexivity|].
rewrite !AFey.sum_bytes_cons, IH. lia.
Qed.

Lemma sum_split : forall L0 Lk ex,
sum_bytes Lk + kBatchBytes * Z.of_nat (length ex) = sum_bytes L0 ->
(forall b, In b ex -> b_items b = []) ->
sum_bytes L0 <= 2 ^ 31 -> (forall b, In b Lk -> forall k, In k (b_items b) -> 0 <= ck_n k) ->
sum_bytes (ex ++ Lk) <= 2 ^ 31.
Proof.
intros L0 Lk ex HS HE HB HN. rewrite sum_bytes_app_q.
assert (AE : sum_bytes ex = kBatchBytes * Z.of_nat (length ex)).
{ clear HS. induction ex as [|b t IH]; cbn [length]; [reflexivity|].
  rewrite AFey.sum_bytes_cons, (IH (fun b' Hb' => HE b' (or_intror Hb'))).
  unfold b_bytes. rewrite (HE b (or_introl eq_refl)). cbn [fold_right]. lia. }
rewrite AE. lia.
Qed.

Lemma nodup_of_stdpp : forall (l : list Z), NoDup l -> List.NoDup l.
Proof. intros l H. apply NoDup_ListNoDup. exact H. Qed.

Lemma nodup_app_of_in : forall (L0 Lk ex : list batch),
List.NoDup (map b_self L0) ->
(forall s, In s (map b_self L0) <-> In s (map b_self Lk ++ map b_self ex)) ->
length L0 = (length Lk + length ex)%nat ->
List.NoDup (map b_self (ex ++ Lk)).
Proof.
intros L0 Lk ex HND HIN HL.
assert (HP : forall s, In s (map b_self L0) -> In s (map b_self (ex ++ Lk))).
{ intros s H. rewrite map_app. apply HIN in H. apply in_app_iff.
  apply in_app_iff in H as [H|H]; [right | left]; exact H. }
assert (HLen : length (map b_self (ex ++ Lk)) = length (map b_self L0)).
{ rewrite !length_map, length_app. lia. }
apply (NoDup_incl_NoDup HND); [lia | exact HP].
Qed.

End d.
