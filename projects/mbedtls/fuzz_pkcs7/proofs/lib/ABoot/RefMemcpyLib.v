(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_RefMemcpyLib () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.ABoot.Hoare.at_"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.ABoot.CatExec.wbytes"; "Corelib.Init.Datatypes.app"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Logic.or"; "Corelib.Lists.ListDef.firstn"; "sub"; "Corelib.Init.Nat.add"; "Corelib.Init.Peano.lt"; "Corelib.Init.Peano.le"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "OSSVerify.KrLib.ABoot.PropExec.rdn"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Nat.sub"; "Corelib.Lists.ListDef.skipn"; "Corelib.Init.Logic.and"; "Corelib.Init.Datatypes.bool"; "Stdlib.ZArith.BinInt.Z.testbit"; "LWv"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.bytes_le_to_Z"; "Stdlib.ZArith.BinInt.Z.mul"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Lists.ListDef.nth"; "OSSVerify.KrLib.ABoot.PropExec.v_srli"; "OSSVerify.KrLib.ABoot.PropExec.v_or"; "Corelib.Init.Datatypes.orb"; "OSSVerify.KrLib.ABoot.PropExec.v_slli"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.ABoot.PropExec.v_srliw"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "Corelib.Init.Datatypes.true"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "keeps"; "Corelib.Init.Logic.not"; "Stdlib.Lists.List.In"; "callee_kept"; "OSSVerify.KrLib.ABoot.PropExec.regupd"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "OSSVerify.KrLib.ABoot.CatSim.msteps"; "keeps_cs"; "callee_saved"; "OSSVerify.KrLib.ABoot.PropExec.getr"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition sub {A} (bs : list A) (j k : nat) : list A := firstn k (skipn j bs).

Lemma firstn_add : forall {A} (l : list A) a b,
  firstn (a + b) l = firstn a l ++ firstn b (skipn a l).
Proof.
  intros A l a. revert l. induction a as [|a IH]; intros l b.
  - cbn. reflexivity.
  - destruct l as [|x l]; cbn.
    + destruct b; reflexivity.
    + rewrite IH. reflexivity.
Qed.

Lemma firstn_sub_app : forall {A} (bs : list A) j k,
  firstn j bs ++ sub bs j k = firstn (j + k) bs.
Proof. intros. unfold sub. rewrite firstn_add. reflexivity. Qed.

Lemma skipn_add : forall {A} (l : list A) a b, skipn (a + b) l = skipn b (skipn a l).
Proof.
  intros A l a. revert l. induction a as [|a IH]; intros l b; [reflexivity|].
  destruct l as [|x l]; cbn; [destruct b; reflexivity|]. apply IH.
Qed.

Lemma sub_length : forall {A} (bs : list A) j k,
  (j + k <= length bs)%nat -> length (sub bs j k) = k.
Proof.
  intros A bs j k H. unfold sub. rewrite length_firstn, length_skipn. lia.
Qed.

Lemma sub_split : forall {A} (bs : list A) j a b,
  sub bs j (a + b) = sub bs j a ++ sub bs (j + a) b.
Proof.
  intros A bs j a b. unfold sub. rewrite firstn_add. f_equal.
  rewrite <- skipn_add. f_equal; lia.
Qed.

Lemma sub_0_all : forall {A} (bs : list A), sub bs 0 (length bs) = bs.
Proof. intros. unfold sub. cbn. apply firstn_all. Qed.

Lemma length_firstn_id : forall {A} (bs : list A) k, k = length bs -> firstn k bs = bs.
Proof. intros A bs k ->. apply firstn_all. Qed.

Lemma sub_nth : forall (bs : list byte) j,
  (j < length bs)%nat -> sub bs j 1 = [nth j bs (Z_to_bv 8 0)].
Proof.
  intros bs j. revert bs. induction j as [|j IH]; intros bs H.
  - destruct bs; cbn in *; [lia|reflexivity].
  - destruct bs; cbn in *; [lia|]. unfold sub in IH. apply IH. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma at_succ : forall (a : word) d, (at_ a d + 1)%bv = at_ a (d + 1).
Proof.
  intros a d. unfold at_. apply bv_eq.
  rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_unsigned (1 : word)) with 1.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma word_succ_at : forall (a : word), (a + 1)%bv = at_ a 1.
Proof. intros a. rewrite <- (at_0 a) at 1. rewrite at_succ. reflexivity. Qed.

Lemma at_u : ltac2:(CDefT.buildp (gd_tbl_RefMemcpyLib ()) "Pa,(0.&40.)Pd,$1.P,(2.=(3.(4.&40.R2.)R1.))P,(5.(3.(4.&40.R3.)R2.)(6.+2.+40.))(7.$1.(4.&40.(8.R4.R3.))(3.(4.&40.R4.)R3.))")
(* [comment removed for export] *).
Proof. intros a d H1 H2. unfold at_. apply u_Z2bv; lia. Qed.

Lemma at_nat : forall (a : word) (j : nat), (a + nat_to_word j)%bv = at_ a (Z.of_nat j).
Proof.
  intros a j. unfold at_, nat_to_word. apply bv_eq.
  rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Zplus_mod_idemp_r. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wbytes_app : ltac2:(CDefT.buildp (gd_tbl_RefMemcpyLib ()) "Pbs1,(9.(0.&8.))Pbs2,(9.(0.&8.))Pm,P,(0.&40.)(:.(0.&8.))Pa,(0.&40.)(7.P,(0.&40.)(:.(0.&8.))(;.R2.R1.(<.(0.&8.)R4.R3.))(;.(;.R2.R1.R4.)(8.R1.(=.(>.(0.&8.)R4.)))R3.))")
(* [comment removed for export] *).
Proof.
  induction bs1 as [|b r IH]; intros bs2 m a.
  - cbn [app wbytes length Z.of_nat]. rewrite at_0. reflexivity.
  - cbn [app wbytes length]. rewrite IH. f_equal.
    rewrite word_succ_at, at_at. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma wbytes_extend : ltac2:(CDefT.buildp (gd_tbl_RefMemcpyLib ()) "Pm,P,(0.&40.)(:.(0.&8.))Pdst,(0.&40.)Pbs,(9.(0.&8.))Pj,$?.Pk,$?.(10.(7.P,(0.&40.)(:.(0.&8.))(;.(;.R5.R4.(11.(0.&8.)R2.R3.))(8.R4.(=.R2.))(12.(0.&8.)R3.R2.R1.))(;.R5.R4.(11.(0.&8.)(13.R2.R1.)R3.)))(14.(>.(0.&8.)R3.)R2.))")
(* [comment removed for export] *).
Proof.
  intros m dst bs j k.
  destruct (Nat.le_gt_cases j (length bs)) as [H|H]; [left|right; exact H].
  rewrite <- firstn_sub_app, wbytes_app. rewrite length_firstn. f_equal. f_equal. f_equal. lia.
Qed.

Lemma wbytes_extend' : ltac2:(CDefT.buildp (gd_tbl_RefMemcpyLib ()) "Pm,P,(0.&40.)(:.(0.&8.))Pdst,(0.&40.)Pbs,(9.(0.&8.))Pj,$?.Pk,$?.P,(15.R2.(>.(0.&8.)R3.))(7.P,(0.&40.)(:.(0.&8.))(;.(;.R6.R5.(11.(0.&8.)R3.R4.))(8.R5.(=.R3.))(12.(0.&8.)R4.R3.R2.))(;.R6.R5.(11.(0.&8.)(13.R3.R2.)R4.)))")
(* [comment removed for export] *).
Proof.
  intros m dst bs j k H. destruct (wbytes_extend m dst bs j k) as [E|E]; [exact E|lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rdn_skipn : ltac2:(CDefT.buildp (gd_tbl_RefMemcpyLib ()) "Psegs,(9.$16.)Pmem,P,(0.&40.)(:.(0.&8.))Pn,$?.Pa,(0.&40.)Pbs,(9.(0.&8.))Pj,$?.P,(7.(:.(9.(0.&8.)))(17.R6.R5.R3.R4.)(18.(9.(0.&8.))R2.))P,(15.R2.R5.)(7.(:.(9.(0.&8.)))(17.R8.R7.(8.R5.(=.R3.))(19.R6.R3.))(18.(9.(0.&8.))(1:.(0.&8.)R3.R4.)))")
(* [comment removed for export] *).
Proof.
  intros segs mem n. induction n as [|n IH]; intros a bs j H Hj.
  - assert (j = 0)%nat by lia. subst j. cbn in H. injection H as <-.
    rewrite at_0. reflexivity.
  - cbn [rdn] in H.
    destruct (match mem a with Some b => Some b | None => seg_rom segs a end) as [b|] eqn:Eb; [|discriminate].
    destruct (rdn segs mem (a+1)%bv n) as [rest|] eqn:Er; [|discriminate].
    injection H as <-.
    destruct j as [|j].
    + rewrite at_0. cbn [Nat.sub skipn rdn]. rewrite Eb, Er. reflexivity.
    + cbn [skipn]. replace (S n - S j)%nat with (n - j)%nat by lia.
      replace (at_ a (Z.of_nat (S j))) with (at_ (a + 1)%bv (Z.of_nat j))
        by (rewrite word_succ_at, at_at; f_equal; lia).
      apply IH; [exact Er|lia].
Qed.

Lemma rdn_sub : ltac2:(CDefT.buildp (gd_tbl_RefMemcpyLib ()) "Psegs,(9.$16.)Pmem,P,(0.&40.)(:.(0.&8.))Pn,$?.Pa,(0.&40.)Pbs,(9.(0.&8.))Pj,$?.Pk,$?.P,(7.(:.(9.(0.&8.)))(17.R7.R6.R4.R5.)(18.(9.(0.&8.))R3.))P,(15.(13.R3.R2.)R6.)(7.(:.(9.(0.&8.)))(17.R9.R8.(8.R6.(=.R4.))R3.)(18.(9.(0.&8.))(12.(0.&8.)R5.R4.R3.)))")
(* [comment removed for export] *).
Proof.
  intros segs mem n a bs j k H Hjk. unfold sub.
  apply (rdn_firstn segs mem (n - j)); [|lia].
  apply rdn_skipn; [exact H|lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Abbreviation lez := bytes_le_to_Z.

(* [comment removed for export] *)
Definition LWv (l : list byte) : word := v_lw (Z_to_bv 64 (lez l)).

Lemma lez_bound_len : forall bs k, length bs = k -> 0 <= lez bs < 2 ^ (8 * Z.of_nat k).
Proof. intros bs k <-. split; [apply bytes_le_to_Z_nonneg | apply bytes_le_to_Z_bound]. Qed.
Lemma lez4_range : forall l, length l = 4%nat -> 0 <= lez l < 2 ^ 32.
Proof. intros l H. pose proof (lez_bound_len l 4%nat H). change (8 * Z.of_nat 4) with 32 in H0. lia. Qed.
Lemma u_lez4 : forall l, length l = 4%nat -> bv_unsigned (Z_to_bv 64 (lez l)) = lez l.
Proof. intros l H. pose proof (lez4_range l H). apply u_Z2bv; lia. Qed.

Lemma testbit_u_LWv : ltac2:(CDefT.buildp (gd_tbl_RefMemcpyLib ()) "Pl,(9.(0.&8.))Pi,$1.P,(7.$?.(>.(0.&8.)R2.)#4.)P,(1;.(2.=R2.)(5.R2.+20.))(7.$1<.(1=.(4.&40.(1>.R4.))R3.)(1=.(1?.R4.)R3.))")
(* [comment removed for export] *).
Proof.
  intros l i H Hi. unfold LWv, v_lw. rewrite Z_to_bv_unsigned, u_lez4 by exact H.
  rewrite bv_wrap_spec_low by lia.
  rewrite bv_swrap_spec by lia.
  case_bool_decide; [reflexivity|].
  replace i with 31 by lia. reflexivity.
Qed.

Lemma u_vlw_mod32 : forall l, length l = 4%nat -> bv_unsigned (LWv l) mod 2 ^ 32 = lez l.
Proof.
  intros l H. pose proof (lez4_range l H) as R.
  apply Z.bits_inj'. intros i Hi.
  destruct (Z.lt_ge_cases i 32) as [Hl|Hh].
  - rewrite Z.mod_pow2_bits_low by lia. apply testbit_u_LWv; [exact H|lia].
  - rewrite Z.mod_pow2_bits_high by lia. symmetry. apply (Z_testbit_high 32); lia.
Qed.

Lemma lez_cons : forall b bs, lez (b :: bs) = Z.lor (bv_unsigned b) (Z.shiftl (lez bs) 8).
Proof. reflexivity. Qed.

Lemma testbit_lez_high : forall bs i, 8 * Z.of_nat (length bs) <= i -> Z.testbit (lez bs) i = false.
Proof.
  intros bs i Hi. apply (Z_testbit_high (8 * Z.of_nat (length bs))); try lia.
  apply lez_bound_len. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma testbit_lez_skipn : ltac2:(CDefT.buildp (gd_tbl_RefMemcpyLib ()) "Pq,$?.Pbs,(9.(0.&8.))Pi,$1.P,(2.=R1.)(7.$1<.(1=.(1?.(1:.(0.&8.)R4.R3.))R2.)(1=.(1?.R3.)(3.R2.(20.+8.(=.R4.)))))")
(* [comment removed for export] *).
Proof.
  induction q as [|q IH]; intros bs i Hi.
  - cbn [skipn]. f_equal. lia.
  - destruct bs as [|b bs].
    + cbn [skipn lez]. rewrite !Z.bits_0. reflexivity.
    + cbn [skipn]. rewrite IH by lia. rewrite lez_cons.
      rewrite Z.lor_spec, Z.shiftl_spec by lia.
      pose proof (u8_range b).
      rewrite (Z_testbit_high 8 (bv_unsigned b)) by lia. cbn [orb]. f_equal. lia.
Qed.

Lemma testbit_lez_firstn : forall q bs i, 0 <= i ->
  Z.testbit (lez (firstn q bs)) i = if i <? 8 * Z.of_nat q then Z.testbit (lez bs) i else false.
Proof.
  induction q as [|q IH]; intros bs i Hi.
  - cbn [firstn lez]. rewrite Z.bits_0. destruct (Z.ltb_spec i (8 * Z.of_nat 0)); [lia|reflexivity].
  - destruct bs as [|b bs].
    + cbn [firstn lez]. rewrite !Z.bits_0. destruct (i <? _); reflexivity.
    + cbn [firstn]. rewrite !lez_cons, !Z.lor_spec, !Z.shiftl_spec by lia.
      destruct (Z.lt_ge_cases i 8) as [H8|H8].
      * rewrite !(Z.testbit_neg_r _ (i - 8)) by lia.
        destruct (Z.ltb_spec i (8 * Z.of_nat (S q))); [reflexivity|lia].
      * rewrite IH by lia.
        destruct (Z.ltb_spec (i - 8) (8 * Z.of_nat q)), (Z.ltb_spec i (8 * Z.of_nat (S q))); try lia; try reflexivity.
        pose proof (u8_range b). rewrite (Z_testbit_high 8 (bv_unsigned b)) by lia. reflexivity.
Qed.

Lemma testbit_lez_app : forall xs ys i, 0 <= i ->
  Z.testbit (lez (xs ++ ys)) i =
  if i <? 8 * Z.of_nat (length xs) then Z.testbit (lez xs) i else Z.testbit (lez ys) (i - 8 * Z.of_nat (length xs)).
Proof.
  intros xs ys i Hi. rewrite bytes_le_app, Z.lor_spec, Z.shiftl_spec by lia.
  destruct (Z.ltb_spec i (8 * Z.of_nat (length xs))).
  - rewrite (Z.testbit_neg_r (lez ys)) by lia. apply orb_false_r.
  - rewrite testbit_lez_high by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma Z_to_le_bytes_lez : forall bs, Z_to_le_bytes (length bs) (lez bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes].
  replace (Z.shiftr (lez (b :: bs)) 8) with (lez bs).
  2:{ apply Z.bits_inj'. intros i Hi. rewrite Z.shiftr_spec by lia.
      pose proof (testbit_lez_skipn 1 (b :: bs) i Hi) as E. change (skipn 1 (b :: bs)) with bs in E.
      rewrite E. reflexivity. }
  rewrite IH. f_equal.
  apply bv_eq. rewrite Z_to_bv_unsigned.
  apply Z.bits_inj'. intros i Hi. pose proof (u8_range b).
  destruct (Z.lt_ge_cases i 8).
  - rewrite bv_wrap_spec_low by lia. rewrite lez_cons, Z.lor_spec, Z.shiftl_spec by lia.
    rewrite (Z.testbit_neg_r _ (i - 8)) by lia. apply orb_false_r.
  - rewrite bv_wrap_spec_high by lia. symmetry. apply (Z_testbit_high 8); lia.
Qed.

Lemma word_to_le_bytes_4_eq : ltac2:(CDefT.buildp (gd_tbl_RefMemcpyLib ()) "Pv,(0.&40.)Pl,(9.(0.&8.))P,(7.$?.(>.(0.&8.)R1.)#4.)P,Pi,$1.P,(1;.(2.=R1.)(5.R1.+20.))(7.$1<.(1=.(4.&40.R5.)R2.)(1=.(1?.R4.)R2.))(7.(9.(0.&8.))(21.#4.R4.)R3.)")
(* [comment removed for export] *).
Proof.
  intros v l Hl Hb. unfold word_to_le_bytes.
  rewrite <- (Z_to_le_bytes_wrap 4 32) by (cbn; lia).
  rewrite <- Hl at 1. rewrite <- (Z_to_le_bytes_lez l). rewrite Hl. f_equal.
  apply Z.bits_inj'. intros i Hi.
  destruct (Z.lt_ge_cases i 32).
  - rewrite bv_wrap_spec_low by lia. apply Hb. lia.
  - rewrite bv_wrap_spec_high by lia. symmetry. apply testbit_lez_high. rewrite Hl. cbn. lia.
Qed.

(* [comment removed for export] *)
Lemma sw_bytes_LWv : forall l, length l = 4%nat -> word_to_le_bytes 4 (LWv l) = l.
Proof.
  intros l H. apply word_to_le_bytes_4_eq; [exact H|]. intros i Hi. apply testbit_u_LWv; assumption.
Qed.

(* [comment removed for export] *)
Definition LBv (b : byte) : word := Z_to_bv 64 (bv_unsigned b).

Lemma sb_byte_LBv : forall b : byte, Z_to_bv 8 (bv_unsigned (LBv b)) = b.
Proof.
  intros b. unfold LBv. pose proof (u8_range b). rewrite u_Z2bv by lia.
  apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
Qed.

(* [comment removed for export] *)
Lemma sb_byte_eq : ltac2:(CDefT.buildp (gd_tbl_RefMemcpyLib ()) "Pv,(0.&40.)Pb,(0.&8.)P,Pi,$1.P,(1;.(2.=R1.)(5.R1.+8.))(7.$1<.(1=.(4.&40.R4.)R2.)(1=.(4.&8.R3.)R2.))(7.(0.&8.)(22.&8.(4.&40.R3.))R2.)")
(* [comment removed for export] *).
Proof.
  intros v b Hb. apply bv_eq. rewrite Z_to_bv_unsigned.
  apply Z.bits_inj'. intros i Hi. pose proof (u8_range b).
  destruct (Z.lt_ge_cases i 8).
  - rewrite bv_wrap_spec_low by lia. apply Hb. lia.
  - rewrite bv_wrap_spec_high by lia. symmetry. apply (Z_testbit_high 8); lia.
Qed.

Lemma testbit_nth_lez : ltac2:(CDefT.buildp (gd_tbl_RefMemcpyLib ()) "Pl,(9.(0.&8.))Pq,$?.Pi,$1.P,(1;.(2.=R1.)(5.R1.+8.))P,(14.R3.(>.(0.&8.)R4.))(7.$1<.(1=.(4.&8.(23.(0.&8.)R4.R5.(22.&8.=)))R3.)(1=.(1?.R5.)(3.R3.(20.+8.(=.R4.)))))")
(* [comment removed for export] *).
Proof.
  intros l q i Hi Hq. rewrite <- testbit_lez_skipn by lia.
  revert l Hq. induction q as [|q IH]; intros l Hq.
  - destruct l as [|b l]; [cbn in Hq; lia|]. cbn [nth skipn]. rewrite lez_cons.
    rewrite Z.lor_spec, Z.shiftl_spec, (Z.testbit_neg_r _ (i - 8)) by lia. symmetry. apply orb_false_r.
  - destruct l as [|b l]; [cbn in Hq; lia|]. cbn [nth skipn]. apply IH. cbn in Hq. lia.
Qed.

(* [comment removed for export] *)
Lemma sb_byte_srli_LWv : ltac2:(CDefT.buildp (gd_tbl_RefMemcpyLib ()) "Pl,(9.(0.&8.))Pq,$?.P,(7.$?.(>.(0.&8.)R2.)#4.)P,(15.R2.#3.)(7.(0.&8.)(22.&8.(4.&40.(24.(1>.R4.)(20.+8.(=.R3.)))))(23.(0.&8.)R3.R4.(22.&8.=)))")
(* [comment removed for export] *).
Proof.
  intros l q H Hq. apply sb_byte_eq. intros i Hi.
  unfold v_srli. rewrite Z_to_bv_unsigned, bv_wrap_spec_low, Z.shiftr_spec by lia.
  rewrite testbit_u_LWv by (try exact H; lia).
  rewrite testbit_nth_lez by (try rewrite H; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma testbit_u_srliw_LWv : forall l s i, length l = 4%nat -> 1 <= s -> 0 <= i ->
  Z.testbit (bv_unsigned (v_srliw (LWv l) s)) i = if i + s <? 32 then Z.testbit (lez l) (i + s) else false.
Proof.
  intros l s i H Hs Hi. unfold v_srliw. rewrite Z_to_bv_unsigned.
  assert (Sh : forall j, 0 <= j -> Z.testbit (Z.shiftr (bv_wrap 32 (bv_unsigned (LWv l))) s) j
                              = if j + s <? 32 then Z.testbit (lez l) (j + s) else false).
  { intros j Hj. rewrite Z.shiftr_spec by lia.
    destruct (Z.ltb_spec (j + s) 32).
    - rewrite bv_wrap_spec_low by lia. apply testbit_u_LWv; [exact H|lia].
    - apply bv_wrap_spec_high. lia. }
  destruct (Z.lt_ge_cases i 64).
  - rewrite bv_wrap_spec_low by lia. rewrite bv_swrap_spec by lia.
    case_bool_decide.
    + apply Sh. lia.
    + rewrite Sh by lia.
      destruct (Z.ltb_spec (Z.of_N 32 - 1 + s) 32), (Z.ltb_spec (i + s) 32); try lia; reflexivity.
  - rewrite bv_wrap_spec_high by lia. destruct (Z.ltb_spec (i + s) 32); [lia|reflexivity].
Qed.

(* [comment removed for export] *)
Lemma testbit_u_slli_LWv : forall l s i, length l = 4%nat -> 0 <= s -> 0 <= i < 32 ->
  Z.testbit (bv_unsigned (v_slli (LWv l) s)) i = if i <? s then false else Z.testbit (lez l) (i - s).
Proof.
  intros l s i H Hs Hi. unfold v_slli. rewrite Z_to_bv_unsigned.
  rewrite bv_wrap_spec_low by lia. rewrite Z.shiftl_spec by lia.
  destruct (Z.ltb_spec i s).
  - apply Z.testbit_neg_r. lia.
  - apply testbit_u_LWv; [exact H|lia].
Qed.

Lemma testbit_u_vor : ltac2:(CDefT.buildp (gd_tbl_RefMemcpyLib ()) "Px,(0.&40.)Py,(0.&40.)Pi,$1.P,(2.=R1.)(7.$1<.(1=.(4.&40.(25.R4.R3.))R2.)(26.(1=.(4.&40.R4.)R2.)(1=.(4.&40.R3.)R2.)))")
(* [comment removed for export] *).
Proof.
  intros x y i Hi. unfold v_or. rewrite Z_to_bv_unsigned.
  destruct (Z.lt_ge_cases i 64).
  - rewrite bv_wrap_spec_low by lia. apply Z.lor_spec.
  - rewrite bv_wrap_spec_high by lia.
    pose proof (u64_range x). pose proof (u64_range y).
    rewrite (Z_testbit_high 64 (bv_unsigned x)) by lia. rewrite (Z_testbit_high 64 (bv_unsigned y)) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sw_bytes_merge : ltac2:(CDefT.buildp (gd_tbl_RefMemcpyLib ()) "Pl1,(9.(0.&8.))Pl2,(9.(0.&8.))Pq,$?.Pv,(0.&40.)P,(7.$?.(>.(0.&8.)R4.)#4.)P,(7.$?.(>.(0.&8.)R4.)#4.)P,(1;.(15.#1.R4.)(15.R4.#3.))P,(7.(0.&40.)R4.(25.(27.(1>.R6.)(28.+20.(20.+8.(=.R5.))))(29.(1>.R7.)(20.+8.(=.R5.)))))(7.(9.(0.&8.))(21.#4.R5.)(<.(0.&8.)(1:.(0.&8.)R6.R8.)(11.(0.&8.)R6.R7.)))")
(* [comment removed for export] *).
Proof.
  intros l1 l2 q v H1 H2 Hq ->.
  apply word_to_le_bytes_4_eq.
  { rewrite length_app, length_skipn, length_firstn, H1, H2. lia. }
  intros i Hi.
  rewrite testbit_u_vor by lia.
  rewrite testbit_u_slli_LWv by (try exact H2; lia).
  rewrite testbit_u_srliw_LWv by (try exact H1; lia).
  rewrite testbit_lez_app by lia. rewrite length_skipn, H1.
  rewrite testbit_lez_skipn by lia.
  destruct (Z.ltb_spec i (32 - 8 * Z.of_nat q)), (Z.ltb_spec i (8 * Z.of_nat (4 - q))),
           (Z.ltb_spec (i + 8 * Z.of_nat q) 32); try lia.
  - reflexivity.
  - rewrite testbit_lez_firstn by lia.
    destruct (Z.ltb_spec (i - 8 * Z.of_nat (4 - q)) (8 * Z.of_nat q)); [|lia].
    rewrite orb_false_r. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma sw_bytes_merge' : ltac2:(CDefT.buildp (gd_tbl_RefMemcpyLib ()) "Pl1,(9.(0.&8.))Pl2,(9.(0.&8.))Pq,$?.Pv,(0.&40.)P,(7.$?.(>.(0.&8.)R4.)#4.)P,(7.$?.(>.(0.&8.)R4.)#4.)P,(1;.(15.#1.R4.)(15.R4.#3.))P,(7.(0.&40.)R4.(25.(29.(1>.R7.)(20.+8.(=.R5.)))(27.(1>.R6.)(28.+20.(20.+8.(=.R5.))))))(7.(9.(0.&8.))(21.#4.R5.)(<.(0.&8.)(1:.(0.&8.)R6.R8.)(11.(0.&8.)R6.R7.)))")
(* [comment removed for export] *).
Proof.
  intros l1 l2 q v H1 H2 Hq ->. apply (sw_bytes_merge l1 l2 q); try assumption.
  unfold v_or. f_equal. apply Z.lor_comm.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma store_ok_at : ltac2:(CDefT.buildp (gd_tbl_RefMemcpyLib ()) "Psegs,(9.$16.)Pm,P,(0.&40.)(:.(0.&8.))Pdst,(0.&40.)PN,$?.Pbsw,(9.(0.&8.))Pj,$1.Pk,$?.P,(2.(3.(4.&40.R5.)(=.R4.))(6.+2.+40.))P,(7.$1<.(2:.R8.R7.R6.R5.)$2;.)P,(2.=R4.)P,(2.(3.R5.(=.R4.))(=.R7.))(7.$1<.(2:.R;.(;.R:.R9.R7.)(8.R9.R6.)R5.)$2;.)")
(* [comment removed for export] *).
Proof.
  intros segs m dst N bsw j k Hnw Hok Hj Hk.
  destruct k as [|k]; [reflexivity|].
  pose proof (u64_range dst).
  apply (store_ok_mono segs (S k) m); [apply wbytes_grows|].
  apply (store_ok_sub segs m dst (at_ dst j) N (S k) Hnw Hok); rewrite at_u; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition callee_kept : list reg :=
  [1; 2; 3; 4; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Definition keeps (regs regs' : bvmap 5 word) : Prop :=
  forall r : reg, In r callee_kept -> getr regs' r = getr regs r.

Lemma keeps_refl : forall regs, keeps regs regs.
Proof. intros regs r _. reflexivity. Qed.

Lemma keeps_trans : forall r1 r2 r3, keeps r1 r2 -> keeps r2 r3 -> keeps r1 r3.
Proof. intros r1 r2 r3 A B r Hr. rewrite (B r Hr). apply A, Hr. Qed.

(* [comment removed for export] *)
Lemma keeps_upd : ltac2:(CDefT.buildp (gd_tbl_RefMemcpyLib ()) "Pregs,(2<.&5.(0.&40.))Pregs',(2<.&5.(0.&40.))Prd,(0.&5.)Pv,(0.&40.)P,(2=.R4.R3.)P,(2>.(2?.(0.&5.)R3.$30.))(2=.R6.(31.R5.R4.R3.))")
(* [comment removed for export] *).
Proof.
  intros regs regs' rd v K Hn r Hr.
  rewrite getr_other; [apply K, Hr|]. intros ->. exact (Hn Hr).
Qed.

(* [comment removed for export] *)
Lemma keeps_getr : forall regs regs' (r : reg), keeps regs regs' -> In r callee_kept -> getr regs' r = getr regs r.
Proof. intros regs regs' r K Hr. apply K, Hr. Qed.

Ltac kept_reg := cbv [callee_kept In]; intuition congruence.

Example keeps_sp_example : forall regs regs', keeps regs regs' -> getr regs' 2 = getr regs 2.
Proof. intros regs regs' K. apply (keeps_getr _ _ 2 K). kept_reg. Qed.

(* [comment removed for export] *)
Ltac not_kept := cbv; intuition discriminate.

(* [comment removed for export] *)
Ltac solve_keeps :=
  repeat (apply keeps_upd; [| not_kept]); first [apply keeps_refl | assumption].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma runs_trans : ltac2:(CDefT.buildp (gd_tbl_RefMemcpyLib ()) "Psegs,(9.$16.)Ps0,$32.Pst1,P,(2<.&5.(0.&40.))$32.PP1,P,(2<.&5.(0.&40.))SpPst2,P,(2<.&5.(0.&40.))$32.PP2,P,(2<.&5.(0.&40.))SpP,(33.(2<.&5.(0.&40.))Lr1,(2<.&5.(0.&40.))(1;.(34.R7.R6.A1.R5.R1.)A1.R4.R1.))P,Pr1,(2<.&5.(0.&40.))P,A1.R5.R1.(33.(2<.&5.(0.&40.))Lr2,(2<.&5.(0.&40.))(1;.(34.R:.A1.R8.R3.A1.R6.R1.)A1.R5.R1.))(33.(2<.&5.(0.&40.))Lr2,(2<.&5.(0.&40.))(1;.(34.R9.R8.A1.R5.R1.)A1.R4.R1.))")
(* [comment removed for export] *).
Proof.
  intros segs s0 st1 P1 st2 P2 (r1 & R1 & H1) K.
  destruct (K r1 H1) as (r2 & R2 & H2).
  exists r2. split; [eapply msteps_trans; eassumption | exact H2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition callee_saved : list reg :=
  [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Definition keeps_cs (regs regs' : bvmap 5 word) : Prop :=
  forall r : reg, In r callee_saved -> getr regs' r = getr regs r.

Lemma keeps_cs_refl : forall regs, keeps_cs regs regs.
Proof. intros regs r _. reflexivity. Qed.

Lemma keeps_cs_trans : forall r1 r2 r3, keeps_cs r1 r2 -> keeps_cs r2 r3 -> keeps_cs r1 r3.
Proof. intros r1 r2 r3 A B r Hr. rewrite (B r Hr). apply A, Hr. Qed.

Lemma keeps_cs_upd : ltac2:(CDefT.buildp (gd_tbl_RefMemcpyLib ()) "Pregs,(2<.&5.(0.&40.))Pregs',(2<.&5.(0.&40.))Prd,(0.&5.)Pv,(0.&40.)P,(35.R4.R3.)P,(2>.(2?.(0.&5.)R3.$36.))(35.R6.(31.R5.R4.R3.))")
(* [comment removed for export] *).
Proof.
  intros regs regs' rd v K Hn r Hr.
  rewrite getr_other; [apply K, Hr|]. intros ->. exact (Hn Hr).
Qed.

(* [comment removed for export] *)
Lemma keeps_cs_upd_same : ltac2:(CDefT.buildp (gd_tbl_RefMemcpyLib ()) "Pregs,(2<.&5.(0.&40.))Pregs',(2<.&5.(0.&40.))Prd,(0.&5.)Pv,(0.&40.)P,(35.R4.R3.)P,(7.(0.&40.)(37.R5.R3.)R2.)P,(2>.(7.(0.&5.)R4.(38.&5.=$39.)))(35.R7.(31.R6.R5.R4.))")
(* [comment removed for export] *).
Proof.
  intros regs regs' rd v K Hv Hnz r Hr.
  destruct (decide (r = rd)) as [->|Hne].
  - rewrite getr_same by exact Hnz. symmetry. exact Hv.
  - rewrite getr_other by exact Hne. apply K, Hr.
Qed.

Lemma keeps_keeps_cs : forall regs regs', keeps regs regs' -> keeps_cs regs regs'.
Proof.
  intros regs regs' K r Hr. apply K. unfold callee_saved, callee_kept in *. cbn [In] in *. intuition.
Qed.

Lemma keeps_cs_getr : ltac2:(CDefT.buildp (gd_tbl_RefMemcpyLib ()) "Pregs,(2<.&5.(0.&40.))Pregs',(2<.&5.(0.&40.))Pr,(0.&5.)P,(35.R3.R2.)P,(2?.(0.&5.)R2.$36.)(7.(0.&40.)(37.R4.R3.)(37.R5.R3.))")
(* [comment removed for export] *).
Proof. intros regs regs' r K Hr. apply K, Hr. Qed.

Ltac solve_keeps_cs :=
  repeat (first [ apply keeps_cs_upd; [| not_kept]
                | apply keeps_cs_upd_same; [| solve [eauto | symmetry; eauto] | let X := fresh in intro X; discriminate X ] ]);
  first [apply keeps_cs_refl | assumption | apply keeps_keeps_cs; assumption].
