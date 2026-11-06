(* owed_counter_text at image A: what the release keeps of seg[8] and *dots, and their bytes when the call fails. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YC85 YCeo.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgChkC CPgWalk CPgWalkKept CPgWalkFrame CPgWalkCall.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import owed_counter_text_A_base owed_counter_text_A_Lt owed_counter_text_A_wr owed_counter_text_A_Qb.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require AE36.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.


Section rk. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma oc_val_mem_kept : forall E rs (m m' : word -> option byte) a n v,
  frame_of E rs m m' -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall k, (k < n)%nat -> ~ in_wrange E rs (a + Z.of_nat k)) -> val_mem tfibsegs m a n v -> val_mem tfibsegs m' a n v.
Proof.
intros E rs m m' a n v HF Ha Han Hn Hv k Hk. unfold mbyte. rewrite (HF (Z_to_bv 64 (a + Z.of_nat k))).
- exact (Hv k Hk).
- rewrite unsigned_lit_small by lia. exact (Hn k Hk).
Qed.
Lemma oc_garr8_kept : forall E rs (m m' : word -> option byte) q l,
  frame_of E rs m m' -> 0 <= q -> q + Z.of_nat (length l) <= 2 ^ 64 ->
  (forall j, (j < length l)%nat -> ~ in_wrange E rs (q + Z.of_nat j)) -> garr8 tfibsegs m q l -> garr8 tfibsegs m' q l.
Proof.
intros E rs m m' q l HF Hq Hql Hn Hg j Hj. destruct (Hg j Hj) as (Hv & Hb). split; [|exact Hb].
apply (oc_val_mem_kept E rs m m' (q + Z.of_nat j) 1 (nth j l 0) HF ltac:(lia) ltac:(lia)); [|exact Hv].
intros k Hk. replace k with 0%nat by lia. rewrite Z.add_0_r. exact (Hn j Hj).
Qed.
Lemma oc_garr8_exists : forall (H : word -> bool) (m : word -> option byte) q,
  (forall j, 0 <= j < 8 -> apresent H m (q + j)) -> exists l, garr8 tfibsegs (mrestrict H m) q l /\ length l = 8%nat.
Proof.
intros H m q Hp.
exists (map (fun j => match aview tfibsegs H m (q + Z.of_nat j) with Some v => v | None => 0 end) (seq 0 8)).
split; [|rewrite length_map, length_seq; reflexivity].
intros j Hj. rewrite length_map, length_seq in Hj. rewrite oc_nth_map_seq0 by exact Hj.
pose proof (aview_some_of_apresent tfibsegs H m (q + Z.of_nat j) (Hp (Z.of_nat j) ltac:(lia))) as Hs.
destruct (aview tfibsegs H m (q + Z.of_nat j)) as [v|] eqn:Ev; [|contradiction].
destruct (aview_byte tfibsegs H m _ v Ev) as (_ & _ & _ & Hv).
split; [exact (AE36.val_mem1_of_aview _ _ _ _ Ev) | exact Hv].
Qed.
Lemma oc_byte_exists : forall (H : word -> bool) (m : word -> option byte) q,
  apresent H m q -> exists d, val_mem tfibsegs (mrestrict H m) q 1 d.
Proof.
intros H m q Hp. pose proof (aview_some_of_apresent tfibsegs H m q Hp) as Hs.
destruct (aview tfibsegs H m q) as [v|] eqn:Ev; [|contradiction].
exists v. exact (AE36.val_mem1_of_aview _ _ _ _ Ev).
Qed.
End rk.
(* lia case-splits every disjunction in the context: hide the walk's disjunctive facts (cw_hold) and let oc_dl
   unhide them one at a time as a goal needs them *)
Ltac oc_hide_disj :=
  repeat match goal with
  | H : _ \/ _ |- _ => cw_hide H
  | H : ~ (_ /\ _) |- _ => cw_hide H
  end.
Ltac oc_dl1 := first [ lia | match goal with H : cw_hold _ |- _ => unfold cw_hold in H; lia end ].
Ltac oc_dl := first [ oc_dl1 | match goal with H : cw_hold _ |- _ => unfold cw_hold in H; oc_dl1 end ].

(* a byte the walk does not write in the release: none of its regions' write windows (enumerated) holds it *)
Ltac oc_notwin :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
  intros (r & Hr & Hb);
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
  cbn [In] in Hr;
  repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
    lazymatch goal with AGx : forall n, (n < 33)%nat -> _ |- _ => revert Hb; evalE AGx; intros Hb end; oc_dl | ]);
  destruct Hr.


Lemma oc_ct2_len : forall n s dot k i seg d s' d', DgnLib.ct2_go n s dot i k seg d = (0, s', d') -> length s' = (length seg + k)%nat.
Proof.
intros n s dot k. induction k as [|k IH]; intros i seg d s' d' H.
- cbn in H. injection H as <- <-. lia.
- cbn [DgnLib.ct2_go] in H.
  destruct ((0 <=? i - (8 - n)) && negb (nth (Z.to_nat (i - (8 - n))) dot 0 =? 0)).
  + destruct (i =? 7); [injection H as H; unfold DgnSpec.E_RANGE in H; discriminate H|].
    apply IH in H. rewrite length_app in H. cbn in H. lia.
  + apply IH in H. rewrite length_app in H. cbn in H. lia.
Qed.
Lemma oc_spec_len : forall tb s d, codec_owe.owed_counter_text_spec tb = (0, s, d) -> length s = 8%nat.
Proof.
intros tb s d H. unfold codec_owe.owed_counter_text_spec in H.
destruct (codec_owe.ct1_owe tb 0 [] (repeat 0 8)) as [[[n s0] dot]|].
- unfold DgnLib.ct2 in H. apply oc_ct2_len in H. exact H.
- injection H as H. unfold DgnSpec.E_RANGE in H. discriminate H.
Qed.
