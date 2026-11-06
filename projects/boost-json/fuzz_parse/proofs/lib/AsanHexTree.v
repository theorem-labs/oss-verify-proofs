(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "57Corelib7Numbers6Cyclic5Int639PrimInt6303int37Corelib7StringsaPrimStringid6string69OSSVerify6Proofsaboost_jsonafuzz_parse3libbAsanHexTree~~~~~~l23ztr03lsl03lorid3getid6length37Corelib4Init9Datatypesqf3orb03eqb03ltb03subl22ZLqf3natl25gleafl25rtreeqf4true37Corelib4Init5Logicve2eql25ctreeqf4bool37Corelib7Numbers7BinNumshi64Npos3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshk7ahex_nybblel25canon46Stdlib6NArith6BinNat1Nhp43ltbl25vleaf57Corelib7Numbers6Cyclic5Int63cUint63Axiomshrbaof_pos_rec37Corelib4Init3Nathv43addhi68positivel23ext35stdpp9bitvectorbdefinitionsihf2bvqf4Someqf6optionhk7bhex_byte_atihf7Z_to_bvqf4Noneve3notve3andhi61Nhp43mulhp46of_nathp43powve2exhp43addhp42lehp42ltqf4listqf4prodl26coversl24galll23zptl25gallvl23vptqf4consqf3nilhrb4to_Zhk7fsegment_byte_at46Stdlib6ZArith6BinInt1Zjge3divjge4to_N" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Inductive ztr : Set := ZL (b : bool) (c1 c2 : int) | ZN (l r : ztr).

(* [comment removed for export] *)
Fixpoint rtree (leaf : int -> ztr) (d : nat) (acc : int) : ztr :=
  match d with
  | O => leaf acc
  | S d' => ZN (rtree leaf d' (acc << 1)%uint63) (rtree leaf d' ((acc << 1) lor 1)%uint63)
  end.

(* [comment removed for export] *)
Definition gleaf : ltac2:(zQ "30!i8!k9!p0>1s$1>3acc$0$2") := ltac2:(zQ "b0!p6!pb!q0!q6!s7!sd!i8!t2!t7!k9!tc\1s$9\3acc$6@3$a@2$4@2$7@2$1@2$0^1I1I1@1$3^2@2$5@2$1@2$0^1I1I1@2$8@1$3^2I1@2$2^2@2$0^1I1@2$2^2@2$1@2$0^1I1I1").
Definition gtree : ltac2:(zQ "40!u1!i8!k9!p0>1s$2>0$0>0$1$3") := ltac2:(zQ "30!k9!u7!uf\1s$0@1$2@1$1^1").

(* [comment removed for export] *)
Fixpoint ctree (d : nat) : ztr := match d with O => ZL true 48%uint63 48%uint63 | S d' => let t := ctree d' in ZN t t end.
Lemma ctree_rtree : ltac2:(zQ "80!i8!u1!v7!hh2!tc!hh7!uf!p0>1d$1>3acc$0@3$3$7@1$5^2@3$6\0$0@3$4$2Ij0Ij0^2^1").
Proof. induction d as [|d IH]; intros acc; [reflexivity|]. cbn [ctree rtree]. cbv zeta. rewrite <- !IH. reflexivity. Qed.

(* [comment removed for export] *)
Definition canon : ltac2:(zQ "10!i8>1c$0$0") := ltac2:(zQ "30!hhf!i8!t2\1c$1M0\0$0$1@2$2^1IjaM0\0$0$1@2$2^1Ij4M0\0$0$1@2$2^1Ij2M0\0$0$1@2$2^1Ij1Ij0Ij1M0\0$0$1@2$2^1Ij3Ij2Ij3M0\0$0$1@2$2^1Ij8M0\0$0$1@2$2^1Ij6M0\0$0$1@2$2^1Ij5Ij4Ij5M0\0$0$1@2$2^1Ij7Ij6Ij7M0\0$0$1@2$2^1Ij9Ij8Ij9M0\0$0$1@2$2^1Im4M0\0$0$1@2$2^1Im2Im1M0\0$0$1@2$2^1Im3Im2Im3M0\0$0$1@2$2^1Im5Im4M0\0$0$1@2$2^1Im6Im5Im6").
Lemma canon_hex : ltac2:(zQ "80!hh2!i8!hhf!v7!hjf!hne!hoc!hqc>1c$1>0@3$0$1^1@1$6^1@3$0$2@2$7@1$5^2@1$4#h0$3").
Proof.
  intros c H. unfold canon in H.
  repeat match type of H with context [if ?b then _ else _] => destruct b end; rewrite H; vm_compute; reflexivity.
Qed.
Definition vleaf : ltac2:(zQ "30!i8!k9!p0>1s$1>3acc$0$2") := ltac2:(zQ "80!p6!q0!hoc!v7!i8!pb!k9!tc\1s$6\3acc$4@3$7$3@1$2@2$1^2@2$0^1I1@1$2@2$1^2@2$5@2$0^1I1I1").
Definition vtree : ltac2:(zQ "40!u1!i8!k9!p0>1s$2>0$0>0$1$3") := ltac2:(zQ "30!k9!uf!hr3\1s$0@1$1@1$2^1").

(* [comment removed for export] *)
Fixpoint ext (d : nat) (q pi : positive) : Prop :=
  match d with O => pi = q | S d' => ext d' (xO q) pi \/ ext d' (xI q) pi end.

Lemma rtree_inv : ltac2:(zQ "90!i8!p0!hh2!hu6!u1!ig6!igd!uf!ih9>3lf1>0$0$1>3lf2>0$0$1>1d$4>1f$4>1q$6>3acc$0>0@3$2$0^1@2$3^3^2>0@3$2$1@3$7^7^5^2@3$7^6^5^2>2pi$6>0@3$8^7^5^1@3$2$1@1^a@2$3@2$5^8^7^2@1^9@2$3@2$5^8^7^2").
Proof.
  intros lf1 lf2 d. induction d as [|d IH]; intros f q acc Hacc HT pi HX.
  - cbn [rtree] in HT. cbn [ext] in HX. subst pi. cbn [Nat.add]. rewrite <- Hacc. exact HT.
  - cbn [rtree] in HT. injection HT as EL ER. rewrite (Nat.add_succ_comm d f). destruct HX as [HX|HX].
    + apply (IH (S f) (xO q) (acc << 1)%uint63); [subst acc; reflexivity| exact EL| exact HX].
    + apply (IH (S f) (xI q) ((acc << 1) lor 1)%uint63); [subst acc; reflexivity| exact ER| exact HX].
Qed.

(* [comment removed for export] *)
Lemma hex_byte_at_zero : ltac2:(zQ "e0!hjf!hh2!ijc!ik2!ik9!v7!igd!hu6!k9!il2!tc!u7!p0!im1>1s$8>2pi$6>0@3$1$c@2$b^2@2$7Nje^1@3$a$5Ij0Ij0@3$1@1$4@1$2@1$0#8@2$9^3@1$0^2@2$3@1$2@1$0#8@2$d@1$0#8Z").
Proof.
  intros s pi H. unfold gleaf in H. injection H as HB H1 H2. unfold hex_byte_at.
  change (Uint63.of_Z (Z.of_N (2 * N.pos pi))) with (of_pos_rec 62 pi << 1)%uint63.
  change (Uint63.of_Z (Z.of_N (2 * N.pos pi + 1))) with ((of_pos_rec 62 pi << 1) lor 1)%uint63.
  cbv zeta. rewrite HB, H1, H2. reflexivity.
Qed.
Lemma hex_byte_at_some : ltac2:(zQ "d0!hjf!hh2!hu6!ijc!imc!ik9!in3!igd!k9!il2!u7!hr3!p0>1s$8>2pi$7>0@3$1$c@2$a^2@2$2Nje^1@2$b^2@2$2Nje^1@1$6@3$1@1$5@1$3@1$0#8@2$9^3@1$0^2@1$4@1$3@1$0#8").
Proof.
  intros s pi H. unfold gleaf, vleaf in H. injection H as HB H1 H2. apply canon_hex in H1, H2. unfold hex_byte_at.
  change (Uint63.of_Z (Z.of_N (2 * N.pos pi))) with (of_pos_rec 62 pi << 1)%uint63.
  change (Uint63.of_Z (Z.of_N (2 * N.pos pi + 1))) with ((of_pos_rec 62 pi << 1) lor 1)%uint63.
  cbv zeta. rewrite HB, H1, H2. cbn [andb]. discriminate.
Qed.

(* [comment removed for export] *)
Lemma ext_of_range : ltac2:(zQ "e0!hjf!igd!in9!inf!io4!iob!ip5!u1!hh2!ipc!ih9!iq1!iq8!iqe>1d$7>1q$1>1i$3>0@2$2@2$c@2$4@1$0^2@2$6@1$0#2@1$5^3^1@2$d^1@2$4@2$b@1$0^2@1$0#1@2$6@1$0#2@1$5^3@2$9$1\2pi$1@2$2@3$8$3^3@1$0^1@3$a^5^4^1").
Proof.
  induction d as [|d IH]; intros q i Hi.
  - change (2 ^ N.of_nat 0)%N with 1%N in Hi. exists q. split; [lia| reflexivity].
  - rewrite Nat2N.inj_succ, N.pow_succ_r' in Hi. set (P := (2 ^ N.of_nat d)%N) in *.
    destruct (N.lt_ge_cases i ((N.pos q~0 + 1) * P)%N) as [Hl|Hg].
    + ndestruct (IH (q~0)%positive i) as (pi & E & X); [fold P; nia|]. exists pi. split; [exact E| left; exact X].
    + ndestruct (IH (q~1)%positive i) as (pi & E & X); [fold P; nia|]. exists pi. split; [exact E| right; exact X].
Qed.

(* [comment removed for export] *)
Fixpoint covers (bl : list (positive * nat)) (cur stop : N) : bool :=
  match bl with
  | [] => N.eqb cur stop
  | (q, d) :: bl' => (Nat.leb d 62 && N.eqb (N.pos q * 2 ^ N.of_nat d) cur && covers bl' (cur + 2 ^ N.of_nat d) stop)%bool
  end.
(* [comment removed for export] *)
Fixpoint gall (s : PrimString.string) (bl : list (positive * nat)) : Prop :=
  match bl with [] => True | (q, d) :: bl' => gtree s d (of_pos_rec (62 - d) q) = ctree d /\ gall s bl' end.
Fixpoint gallv (s : PrimString.string) (bl : list (positive * nat)) : Prop :=
  match bl with [] => True | (q, d) :: bl' => gtree s d (of_pos_rec (62 - d) q) = vtree s d (of_pos_rec (62 - d) q) /\ gallv s bl' end.

Lemma blocks_sound : forall (Q : N -> Prop) (R : positive -> nat -> Prop),
  (forall q d, (d <= 62)%nat -> R q d -> forall pi, ext d q pi -> Q (N.pos pi)) ->
  forall bl base n, (fix all bl := match bl with [] => True | (q, d) :: bl' => R q d /\ all bl' end) bl -> covers bl base (base + n) = true ->
  forall i, (i < n)%N -> Q (base + i)%N.
Proof.
  intros Q R HR bl. induction bl as [|[q d] bl IH]; intros base n HG HC i Hi.
  - cbn [covers] in HC. apply N.eqb_eq in HC. lia.
  - cbn [covers] in HC. apply andb_prop in HC as [HC HC3]. apply andb_prop in HC as [HC1 HC2].
    apply Nat.leb_le in HC1. apply N.eqb_eq in HC2. destruct HG as [HT HG].
    destruct (N.lt_ge_cases (base + i) (base + 2 ^ N.of_nat d)) as [Hl|Hg].
    + ndestruct (ext_of_range d q (base + i)%N) as (pi & E & X); [lia|]. rewrite E. exact (HR q d HC1 HT pi X).
    + assert (HP : (0 < 2 ^ N.of_nat d)%N) by (apply N.neq_0_lt_0, N.pow_nonzero; lia).
      replace (base + i)%N with ((base + 2 ^ N.of_nat d) + (i - 2 ^ N.of_nat d))%N by lia.
      apply (IH (base + 2 ^ N.of_nat d)%N (n - 2 ^ N.of_nat d)%N HG); [| lia].
      replace (base + 2 ^ N.of_nat d + (n - 2 ^ N.of_nat d))%N with (base + n)%N by lia. exact HC3.
Qed.

(* [comment removed for export] *)
Definition zpt : ltac2:(zQ "20!inf!k9>1s$1>4base$0>1n$0P") := ltac2:(zQ "b0!inf!hjf!ijc!ik2!ik9!hh2!k9!il2!iq1!iqe!im1\1s$6\4base$0\1n$0>1i$0>0@2$9^1^2@3$5@1$4@1$2@1$1#8@2$7^5@2$8^4^2@2$3@1$2@1$1#8@2$a@1$1#8Z").
Definition vpt : ltac2:(zQ "20!inf!k9>1s$1>4base$0>1n$0P") := ltac2:(zQ "b0!inf!hjf!ijc!imc!ik9!hh2!in3!k9!il2!iq1!iqe\1s$7\4base$0\1n$0>1i$0>0@2$a^1^2@1$6@3$5@1$4@1$2@1$1#8@2$8^5@2$9^4^2@1$3@1$2@1$1#8").

Theorem ztree_scan_sound : ltac2:(zQ "d0!inf!hhf!ir4!u1!irb!v7!hh2!igd!k9!is2!isb!it2!iq1>1s$8>2bl@1$2@2$4$7$3>4base$0>1n$0>0@2$a^4^3>0@3$6$1@3$9^4^3@2$c^3^2$5@3$b^6^4^3").
Proof.
  intros s bl base n HG HC. unfold zpt.
  apply (blocks_sound (fun i => hex_byte_at s i = Some (Z_to_bv 8 0)) (fun q d => gtree s d (of_pos_rec (62 - d) q) = ctree d)) with (bl := bl); [| | exact HC].
  - intros q d Hd HT pi X. apply hex_byte_at_zero. unfold gtree in HT. rewrite (ctree_rtree d (of_pos_rec (62 - d) q)) in HT.
    pose proof (rtree_inv _ _ d (62 - d) q _ eq_refl HT pi X) as K. replace (d + (62 - d))%nat with 62%nat in K by lia. exact K.
  - clear HC. induction bl as [|[q d] bl IH]; [exact I|]. destruct HG as [H1 H2]. split; [exact H1| exact (IH H2)].
Qed.
Theorem vtree_scan_sound : ltac2:(zQ "d0!inf!hhf!ir4!u1!irb!v7!hh2!igd!k9!is2!it8!iu0!iq1>1s$8>2bl@1$2@2$4$7$3>4base$0>1n$0>0@2$a^4^3>0@3$6$1@3$9^4^3@2$c^3^2$5@3$b^6^4^3").
Proof.
  intros s bl base n HG HC. unfold vpt.
  apply (blocks_sound (fun i => hex_byte_at s i <> None) (fun q d => gtree s d (of_pos_rec (62 - d) q) = vtree s d (of_pos_rec (62 - d) q))) with (bl := bl); [| | exact HC].
  - intros q d Hd HT pi X. apply hex_byte_at_some. unfold gtree, vtree in HT.
    pose proof (rtree_inv _ _ d (62 - d) q _ eq_refl HT pi X) as K. replace (d + (62 - d))%nat with 62%nat in K by lia. exact K.
  - clear HC. induction bl as [|[q d] bl IH]; [exact I|]. destruct HG as [H1 H2]. split; [exact H1| exact (IH H2)].
Qed.

Lemma zpt_vpt : ltac2:(zQ "40!inf!k9!iu0!it2>1s$1>4base$0>1n$0>0@3$3^3^2^1@3$2^4^3^2").
Proof. intros s base n H i Hi. rewrite (H i Hi). discriminate. Qed.
Lemma vpt_app : ltac2:(zQ "40!inf!iu0!iq1!k9>1s$3>4base$0>2n1$0>2n2$0>0@3$1^4^3^2>0@3$1^5@2$2^4^3^2@3$1^6^5@2$2^4^3").
Proof.
  intros s base n1 n2 H1 H2 i Hi. destruct (N.lt_ge_cases i n1) as [Hl|Hg]; [exact (H1 i Hl)|].
  replace (base + i)%N with (base + n1 + (i - n1))%N by lia. apply H2. lia.
Qed.

(* [comment removed for export] *)
Lemma segment_byte_at_zero_pt : ltac2:(zQ "h40!inf!hjf!k9!iq1!iq8!ijc!ik2!iu6!iud!ik9!in9!hh2!iv3!q6!ivb!it2!iqe!ji6!jid!im1>1s$2>4base$0>1n$0>3off$0>0@3$f^4^3^2>0@2$4@2$3^4^3@1$h2@2$h1@1$c@1$d^5+2>0@2$a@2$4^5^3@2$h0^3@2$3^5^4@3$b@1$9@1$5@1$1#8@2$e@3$7$2^7@1$8$2^4@2$6@1$5@1$1#8@2$h3@1$1#8Z").
Proof.
  intros s base n off Hs Hn Hoff. cbn [segment_byte_at].
  replace (off <? Z.to_N (Uint63.to_Z (PrimString.length s) / 2))%N with true by (symmetry; apply N.ltb_lt; lia).
  replace off with (base + (off - base))%N by lia. apply Hs. lia.
Qed.

(* [comment removed for export] *)
Ltac gall_vm :=
  cbn [gall]; repeat match goal with |- _ /\ _ => split end; try exact I;
  match goal with |- gtree _ ?d _ = _ => vm_cast_no_check (@eq_refl ztr (ctree d)) end.
Ltac gallv_vm :=
  cbn [gallv]; repeat match goal with |- _ /\ _ => split end; try exact I;
  match goal with |- gtree ?s ?d ?a = _ => vm_cast_no_check (@eq_refl ztr (vtree s d a)) end.
