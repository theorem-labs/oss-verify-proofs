(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Prelude Instr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound AsanPlanCore.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require EntryKn StdioSymDrive.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymRun3__Common.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module AsanBootKn2.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound AsanPlanCore. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlanCore.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require Import EntryKn StdioSymDrive.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint findk (k0 : kentry) (l : list kentry) (i : nat) {struct l} : option nat :=
  match l with
  | nil => None
  | k :: t => if APC.kentry_eqb k k0 then Some i else findk k0 t (i + 1)%nat
  end.
Definition findk0 (k0 : kentry) (l : list kentry) : nat := match findk k0 l 0%nat with Some i => i | None => 0%nat end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition byte_of (v : expr) (i : nat) (e : expr) : bool :=
  match e with
  | EExt false lo 1%nat v' => Nat.eqb lo i && expr_eqb v' v
  | ELit c => match v with ELit z => Z.leb 0 z && Z.ltb z (2 ^ 64) && Z.eqb c ((z / 2 ^ (8 * Z.of_nat i)) mod 256) | _ => false end
  | _ => false
  end.
Definition has_byte (kn : list kentry) (b : expr) (o : Z) (v : expr) (i : nat) : bool :=
  existsb (fun k => match k with
                    | KWord (SA b' o') 1%nat e => expr_eqb b' b && Z.eqb o' (o + Z.of_nat i) && byte_of v i e
                    | _ => false end) kn.
Definition merge8_ok (kn : list kentry) (b : expr) (o : Z) (v : expr) : bool :=
  forallb (has_byte kn b o v) (seq 0 8).
Definition kn_merge8 (kn : list kentry) (b : expr) (o : Z) (v : expr) : list kentry := KWord (SA b o) 8%nat v :: kn.

Lemma firstn1_skipn_nth' : forall {A} (l : list A) (i : nat) (d : A), (i < length l)%nat -> firstn 1 (skipn i l) = [nth i l d].
Proof.
  intros A l; induction l as [|x l IH]; intros i d Hi; cbn in Hi; [lia|].
  destruct i as [|i]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.

Lemma rdn_bytes : forall segs m n (a : word) (bs : list byte) (d : byte),
  length bs = n -> (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
  (forall i : nat, (i < n)%nat -> rdn segs m (Z_to_bv 64 (bv_unsigned a + Z.of_nat i)) 1 = Some [nth i bs d]) ->
  rdn segs m a n = Some bs.
Proof.
  intros segs m n; induction n as [|n IH]; intros a bs d Hlen Hnw Hall.
  - destruct bs; [reflexivity | discriminate].
  - destruct bs as [|b0 bs]; [discriminate|]. cbn in Hlen.
    pose proof (Hall 0%nat ltac:(lia)) as R0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in R0. cbn [rdn nth] in R0 |- *.
    destruct (match m a with Some b1 => Some b1 | None => seg_rom segs a end) as [b1|]; [|discriminate].
    injection R0 as ->.
    destruct n as [|n'].
    { destruct bs; [reflexivity | cbn in Hlen; lia]. }
    assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (apply u_add1; lia).
    rewrite (IH (a + 1)%bv bs d ltac:(lia) ltac:(rewrite Hu1; lia)); [reflexivity|].
    intros i Hi. rewrite Hu1. replace (bv_unsigned a + 1 + Z.of_nat i)%Z with (bv_unsigned a + Z.of_nat (S i))%Z by lia.
    rewrite (Hall (S i) ltac:(lia)). reflexivity.
Qed.

Lemma nth_w2lb8 : forall (i : nat) (V : word) (d : byte), (i < 8)%nat ->
  [nth i (word_to_le_bytes 8 V) d] = [Z_to_bv 8 ((bv_unsigned V / 2 ^ (8 * Z.of_nat i)) mod 256)].
Proof.
  intros i V d Hi. rewrite <- (firstn1_skipn_nth' (word_to_le_bytes 8 V) i d) by (rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec.length_N_to_le_bytes; lia).
  rewrite <- (word_slice_bytes 8 i 1 V) by lia. rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec.N_to_le_bytes_1_small. unfold ext_val, ext_Z.
  pose proof (u64_range V). pose proof (Z.mod_pos_bound (bv_unsigned V / 2 ^ (8 * Z.of_nat i)) (2 ^ (8 * Z.of_nat 1)) ltac:(lia)).
  rewrite u_small by (change (2 ^ (8 * Z.of_nat 1))%Z with 256%Z in *; lia). reflexivity.
Qed.

Lemma byte_of_sound : forall E v i e, (i < 8)%nat -> byte_of v i e = true ->
  word_to_le_bytes 1 (edenot E e) = [nth i (word_to_le_bytes 8 (edenot E v)) (Z_to_bv 8 0)].
Proof.
  intros E v i e Hi Hb. unfold byte_of in Hb. destruct e; try discriminate.
  - destruct v; try discriminate. apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
    apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.eqb_eq in H3. cbn [edenot].
    rewrite nth_w2lb8 by exact Hi. rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec.N_to_le_bytes_1_small. rewrite !u_small; [subst z; reflexivity | lia |].
    pose proof (Z.mod_pos_bound (z0 / 2 ^ (8 * Z.of_nat i)) 256 ltac:(lia)). lia.
  - destruct sx; [discriminate|]. destruct n as [|[|]]; try discriminate. apply andb_prop in Hb as [H1 H2].
    apply Nat.eqb_eq in H1. apply expr_eqb_eq in H2. subst lo e. cbn [edenot].
    rewrite (word_slice_bytes 8 i 1 (edenot E v)) by lia. apply firstn1_skipn_nth'. rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec.length_N_to_le_bytes. lia.
Qed.

Lemma has_byte_sound : forall segs E M kn b o v i, (i < 8)%nat -> has_byte kn b o v i = true -> know_ok segs E M kn ->
  flat E (SA b (o + Z.of_nat i)) 1 /\
  rdn segs M (Z_to_bv 64 (bv_unsigned (edenot E b) + o + Z.of_nat i)) 1 = Some [nth i (word_to_le_bytes 8 (edenot E v)) (Z_to_bv 8 0)].
Proof.
  intros segs E M kn b o v i Hi Hb HK. unfold has_byte in Hb. apply existsb_exists in Hb as (k & Hk & Hm).
  destruct k; try discriminate. destruct a as [b' o']. destruct w as [|[|]]; try discriminate.
  apply andb_prop in Hm as [Hm H3]. apply andb_prop in Hm as [H1 H2]. apply expr_eqb_eq in H1. apply Z.eqb_eq in H2. subst b' o'.
  pose proof (proj1 (Forall_forall _ _) HK _ Hk) as KO. cbn [kentry_ok] in KO. destruct KO as (_ & Hfl & Hrd).
  split; [exact Hfl|]. rewrite adenot_SA in Hrd. rewrite Z.add_assoc in Hrd. rewrite Hrd. f_equal. apply (byte_of_sound E v i _ Hi H3).
Qed.

Lemma kn_merge8_sound : forall segs E M kn b o v,
  merge8_ok kn b o v = true -> know_ok segs E M kn -> know_ok segs E M (kn_merge8 kn b o v).
Proof.
  intros segs E M kn b o v Hok HK. unfold kn_merge8. constructor; [| exact HK].
  unfold merge8_ok in Hok.
  assert (HB : forall i, (i < 8)%nat -> has_byte kn b o v i = true).
  { intros i Hi. apply (proj1 (forallb_forall _ _) Hok i). apply in_seq. lia. }
  pose proof (has_byte_sound segs E M kn b o v 0 ltac:(lia) (HB 0%nat ltac:(lia)) HK) as [F0 _].
  pose proof (has_byte_sound segs E M kn b o v 7 ltac:(lia) (HB 7%nat ltac:(lia)) HK) as [F7 _].
  unfold flat, estart in F0, F7. cbn [a_base a_off] in F0, F7.
  cbn [kentry_ok]. split; [lia|]. split.
  - unfold flat, estart. cbn [a_base a_off]. lia.
  - rewrite adenot_SA. apply (rdn_bytes segs M 8 _ _ (Z_to_bv 8 0)); [apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec.length_N_to_le_bytes | rewrite u_small by lia; lia |].
    intros i Hi. rewrite u_small by lia. exact (proj2 (has_byte_sound segs E M kn b o v i Hi (HB i Hi) HK)).
Qed.
End AsanBootKn2.

(* [comment removed for export] *)
Module AsanBootKn4.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound AsanPlanCore. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymRun3__Common. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanPlanCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.KnApart.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require Import EntryKn StdioSymDrive.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.

Fixpoint bytes_eqb (l1 l2 : list byte) : bool :=
  match l1, l2 with
  | [], [] => true
  | x :: r1, y :: r2 => (bv_unsigned x =? bv_unsigned y) && bytes_eqb r1 r2
  | _, _ => false
  end.
Lemma bytes_eqb_eq : forall l1 l2, bytes_eqb l1 l2 = true -> l1 = l2.
Proof.
  induction l1 as [|x r1 IH]; intros [|y r2] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.

Definition merged44 (lo hi : Z) : Z := lo + hi * 2 ^ 32.
Definition merge44_ok (kn : list kentry) (b : expr) (o lo hi : Z) : bool :=
  existsb (APC.kentry_eqb (KWord (SA b o) 4%nat (ELit lo))) kn
  && existsb (APC.kentry_eqb (KWord (SA b (o + 4)) 4%nat (ELit hi))) kn
  && bytes_eqb (word_to_le_bytes 8 (Z_to_bv 64 (merged44 lo hi))) (word_to_le_bytes 4 (Z_to_bv 64 lo) ++ word_to_le_bytes 4 (Z_to_bv 64 hi)).
Definition kn_merge44 (kn : list kentry) (b : expr) (o lo hi : Z) : list kentry :=
  KWord (SA b o) 8%nat (ELit (merged44 lo hi)) :: kn.

Lemma kn_merge44_sound : forall segs E M kn b o lo hi,
  merge44_ok kn b o lo hi = true -> know_ok segs E M kn -> know_ok segs E M (kn_merge44 kn b o lo hi).
Proof.
  intros segs E M kn b o lo hi Hok HK. unfold kn_merge44. constructor; [| exact HK].
  unfold merge44_ok in Hok. apply andb_prop in Hok as [Hok HB]. apply andb_prop in Hok as [H1 H2].
  apply existsb_exists in H1 as (k1 & I1 & Q1). apply KNA.kentry_eqb_eq in Q1. subst k1.
  apply existsb_exists in H2 as (k2 & I2 & Q2). apply KNA.kentry_eqb_eq in Q2. subst k2.
  pose proof (proj1 (Forall_forall _ _) HK _ I1) as K1. pose proof (proj1 (Forall_forall _ _) HK _ I2) as K2.
  cbn [kentry_ok] in K1, K2 |- *. destruct K1 as (_ & F1 & R1). destruct K2 as (_ & F2 & R2).
  unfold flat, estart in *. cbn [a_base a_off] in *.
  split; [lia|]. split; [lia|].
  apply bytes_eqb_eq in HB. cbn [edenot] in R1, R2 |- *. rewrite HB.
  change 8%nat with (4 + 4)%nat. apply rdn_app; [exact R1|].
  rewrite adenot_SA in R2 |- *. 
  replace (Z_to_bv 64 (bv_unsigned (edenot E b) + o) + nat_to_word 4)%bv with (Z_to_bv 64 (bv_unsigned (edenot E b) + (o + 4))); [exact R2|].
  apply bv_eq. rewrite bv_add_unsigned, bv_wrap64_mod. unfold nat_to_word. cbn [Z.of_nat Pos.of_succ_nat Pos.succ].
  pose proof (u64_range (edenot E b)) as Ub.
  rewrite !u_small by lia. rewrite Z.mod_small by lia. lia.
Qed.
End AsanBootKn4.
