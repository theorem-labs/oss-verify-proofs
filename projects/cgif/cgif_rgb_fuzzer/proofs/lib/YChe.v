(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01 YI04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCfr YCdv YCe9 YCgi YChv YChx YChw.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Lemma chunk_ok_reexpr : forall E m base off (n : N) (e e' : sv),
sv_denot E e' = sv_denot E e ->
YQ0b.chunk_ok trbsegs E m base (YQ0b.mkChunk off (CVal n e)) -> YQ0b.chunk_ok trbsegs E m base (YQ0b.mkChunk off (CVal n e')).
Proof.
intros E m base off n e e' Hd Hc i Hi. destruct (Hc i Hi) as (b & Hb & Hm).
exists b. split; [|exact Hm]. cbn [YQ0b.cbyte YQ0b.c_val YQ0b.c_off] in *. rewrite Hd. exact Hb.
Qed.
Lemma region_ok_rechunk : forall E m r ci off (n : N) (e e' : sv),
region_ok trbsegs E m r ->
nth_error (YQ0b.r_chunks r) ci = Some (YQ0b.mkChunk off (CVal n e)) ->
sv_denot E e' = sv_denot E e ->
region_ok trbsegs E m (YQ0b.mkRegion (YQ0b.r_base r) (YQ0b.r_lo r) (YQ0b.r_hi r) (YQ0b.r_wlo r) (YQ0b.r_whi r)
(list_upd (YQ0b.r_chunks r) ci (YQ0b.mkChunk off (CVal n e')))).
Proof.
intros E m r ci off n e e' (H1 & H2 & H3 & H4) Hci Hd. unfold region_ok.
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks].
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
revert ci Hci H4. generalize (YQ0b.r_chunks r) as cs. induction cs as [|c cs IH]; intros [|ci] Hci H4; cbn in Hci |- *.
- discriminate. - discriminate.
- injection Hci as ->. inversion H4; subst. constructor; [|assumption]. eapply chunk_ok_reexpr; eassumption.
- inversion H4; subst. constructor; [assumption|]. apply IH; assumption.
Qed.
Ltac ra_rechunk HS k v ri ci Hval Ek :=
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
let HS3 := fresh "HS3" in
pose proof (st_ok_havoc trbsegs k Ev ssx msx [Z_to_bv 64 v] HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
assert (Ek : ew (havoc Ev k [Z_to_bv 64 v]) k = Z_to_bv 64 v)
by (rewrite <- (Nat.add_0_r k) at 2; rewrite (ew_havoc_new _ k [Z_to_bv 64 v] 0 (Z_to_bv 64 0)) by (cbn; lia); reflexivity);
lazymatch type of HS with st_ok _ ?Ev2 ?ss2 ?ms2 =>
let rs := eval cbv in (ss_mem ss2) in
let r := eval cbv in (nth ri rs got_region) in
let c := eval cbv in (nth ci (YQ0b.r_chunks r) (YQ0b.mkChunk 0 (CZero 0))) in
lazymatch c with YQ0b.mkChunk ?off (CVal ?n ?e) =>
let r' := eval cbv in (YQ0b.mkRegion (YQ0b.r_base r) (YQ0b.r_lo r) (YQ0b.r_hi r) (YQ0b.r_wlo r) (YQ0b.r_whi r)
(list_upd (YQ0b.r_chunks r) ci (YQ0b.mkChunk off (CVal n (SOff k 0))))) in
let HS4 := fresh "HS4" in
pose proof (ast_ok_set_region trbsegs Ev2 ss2 ms2 ri r r' HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rechunk Ev2 (ms_mem ms2) r ci off n e (SOff k 0) (st_ok_region_nth Ev2 ss2 ms2 ri r HS ltac:(vm_compute; reflexivity)) eq_refl
ltac:(cbn [sv_denot]; rewrite Ek, Z.add_0_r, Z_to_bv_bv_unsigned;
rewrite <- Hval; apply (sv_denot_agree k Ev (havoc Ev k [Z_to_bv 64 v]) e (env_agree_havoc_ge k k Ev Ev [Z_to_bv 64 v] ltac:(lia) (env_agree_refl k Ev))); vm_compute; reflexivity))) as HS4;
clear HS; rename HS4 into HS
end
end
end.
Ltac ra_setreg HS r e Hv :=
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
let HS3 := fresh "HS3" in
pose proof (ast_ok_set_reg_fp trbsegs Ev ssx msx r e HS ltac:(vm_compute; reflexivity) Hv) as HS3;
clear HS; rename HS3 into HS
end.
