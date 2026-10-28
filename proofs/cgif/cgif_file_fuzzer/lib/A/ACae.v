(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0y YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACbk AC8a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8h AC8j ACbc ACbf ACbd.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Lemma chunk_ok_reexpr : forall {segs : list Segment} E m base off (n : N) (e e' : sv),
sv_denot E e' = sv_denot E e ->
YP09.chunk_ok segs E m base (YP09.mkChunk off (CVal n e)) -> YP09.chunk_ok segs E m base (YP09.mkChunk off (CVal n e')).
Proof.
intros segs E m base off n e e' Hd Hc i Hi. destruct (Hc i Hi) as (b & Hb & Hm).
exists b. split; [|exact Hm]. cbn [YP09.cbyte YP09.c_val YP09.c_off] in *. rewrite Hd. exact Hb.
Qed.
Lemma region_ok_rechunk : forall {segs : list Segment} E m r ci off (n : N) (e e' : sv),
region_ok segs E m r ->
nth_error (YP09.r_chunks r) ci = Some (YP09.mkChunk off (CVal n e)) ->
sv_denot E e' = sv_denot E e ->
region_ok segs E m (YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) (YP09.r_hi r) (YP09.r_wlo r) (YP09.r_whi r)
(list_upd (YP09.r_chunks r) ci (YP09.mkChunk off (CVal n e')))).
Proof.
intros segs E m r ci off n e e' (H1 & H2 & H3 & H4) Hci Hd. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
revert ci Hci H4. generalize (YP09.r_chunks r) as cs. induction cs as [|c cs IH]; intros [|ci] Hci H4; cbn in Hci |- *.
- discriminate. - discriminate.
- injection Hci as ->. inversion H4; subst. constructor; [|assumption]. eapply chunk_ok_reexpr; eassumption.
- inversion H4; subst. constructor; [assumption|]. apply IH; assumption.
Qed.
Ltac ra_rechunk HS k v ri ci Hval Ek :=
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
let HS3 := fresh "HS3" in
pose proof (st_ok_pi_havoc_hi k Ev ssx msx [Z_to_bv 64 v] HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
assert (Ek : ew (havoc Ev k [Z_to_bv 64 v]) k = Z_to_bv 64 v)
by (rewrite <- (Nat.add_0_r k) at 2; rewrite (ew_havoc_new _ k [Z_to_bv 64 v] 0 (Z_to_bv 64 0)) by (cbn; lia); reflexivity);
lazymatch type of HS with st_ok_pi _ _ ?Ev2 ?ss2 ?ms2 =>
let rs := eval cbv in (ss_mem ss2) in
let r := eval cbv in (nth ri rs got_regionP) in
let c := eval cbv in (nth ci (YP09.r_chunks r) (YP09.mkChunk 0 (CZero 0))) in
lazymatch c with YP09.mkChunk ?off (CVal ?n ?e) =>
let r' := eval cbv in (YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) (YP09.r_hi r) (YP09.r_wlo r) (YP09.r_whi r)
(list_upd (YP09.r_chunks r) ci (YP09.mkChunk off (CVal n (SOff k 0))))) in
let HS4 := fresh "HS4" in
pose proof (ast_ok_pi_set_region Ev2 ss2 ms2 ri r r' HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rechunk Ev2 (ms_mem ms2) r ci off n e (SOff k 0) (st_ok_pi_region_nth Ev2 ss2 ms2 ri r HS ltac:(vm_compute; reflexivity)) eq_refl
ltac:(cbn [sv_denot]; rewrite Ek, Z.add_0_r, Z_to_bv_bv_unsigned;
rewrite <- Hval; apply (sv_denot_agree k Ev (havoc Ev k [Z_to_bv 64 v]) e (env_agree_havoc_ge k k Ev Ev [Z_to_bv 64 v] ltac:(lia) (env_agree_refl k Ev))); vm_compute; reflexivity))) as HS4;
clear HS; rename HS4 into HS
end
end | st_ok _ ?Ev ?ssx ?msx =>
let HS3 := fresh "HS3" in
pose proof (st_ok_havoc _ k Ev ssx msx [Z_to_bv 64 v] HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
assert (Ek : ew (havoc Ev k [Z_to_bv 64 v]) k = Z_to_bv 64 v)
by (rewrite <- (Nat.add_0_r k) at 2; rewrite (ew_havoc_new _ k [Z_to_bv 64 v] 0 (Z_to_bv 64 0)) by (cbn; lia); reflexivity);
lazymatch type of HS with st_ok _ ?Ev2 ?ss2 ?ms2 =>
let rs := eval cbv in (ss_mem ss2) in
let r := eval cbv in (nth ri rs got_regionP) in
let c := eval cbv in (nth ci (YP09.r_chunks r) (YP09.mkChunk 0 (CZero 0))) in
lazymatch c with YP09.mkChunk ?off (CVal ?n ?e) =>
let r' := eval cbv in (YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) (YP09.r_hi r) (YP09.r_wlo r) (YP09.r_whi r)
(list_upd (YP09.r_chunks r) ci (YP09.mkChunk off (CVal n (SOff k 0))))) in
let HS4 := fresh "HS4" in
pose proof (ast_ok_set_region _ Ev2 ss2 ms2 ri r r' HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rechunk Ev2 (ms_mem ms2) r ci off n e (SOff k 0) (st_ok_region_nth Ev2 ss2 ms2 ri r HS ltac:(vm_compute; reflexivity)) eq_refl
ltac:(cbn [sv_denot]; rewrite Ek, Z.add_0_r, Z_to_bv_bv_unsigned;
rewrite <- Hval; apply (sv_denot_agree k Ev (havoc Ev k [Z_to_bv 64 v]) e (env_agree_havoc_ge k k Ev Ev [Z_to_bv 64 v] ltac:(lia) (env_agree_refl k Ev))); vm_compute; reflexivity))) as HS4;
clear HS; rename HS4 into HS
end
end  end.
Ltac ra_setreg HS r e Hv :=
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_reg_fp Ev ssx msx r e HS ltac:(vm_compute; reflexivity) Hv) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ev ?ssx ?msx =>
let HS3 := fresh "HS3" in
pose proof (ast_ok_set_reg_fp _ Ev ssx msx r e HS ltac:(vm_compute; reflexivity) Hv) as HS3;
clear HS; rename HS3 into HS  end.
