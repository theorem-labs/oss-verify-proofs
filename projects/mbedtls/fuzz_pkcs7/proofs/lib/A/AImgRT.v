(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Cells Mem Step Statics.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AImgRT () : Init.string Init.list := ["Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "AGLOB_LO"; "AGLOB_HI"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "asan_rtc"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "OSSVerify.KrLib.Lib.Statics.img_bytes_b"; "OSSVerify.KrLib.A.AImg.asegs"; "Corelib.Init.Datatypes.true"; "in_ranges_b"; "rtc_pristine"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "OSSVerify.KrLib.Lib.Step.ro_cells"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.CB"].


(* [comment removed for export] *)
Definition rtc_cell : Type := (Z * nat * Z)%type.

Definition rtc_cells : list rtc_cell := ltac2:(CDefT.buildp (gd_tbl_AImgRT ()) "(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?2:60.#8.)+==<<0.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?2:68.#8.)=)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?2:70.#8.)+1960:0.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?2:80.#8.)+198128.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?2:88.#8.)+103=?8.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?2:90.#8.)+1065?8.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?2:98.#8.)+1072>8.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?2::0.#8.)+1072?0.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?2::8.#8.)+1072>0.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?2:;0.#8.)+?4910.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?35?8.#8.)+1072=9.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?36?0.#8.)+?2988.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?36?8.#8.)=)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?3710.#8.)+?73<0.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?3718.#8.)+102?40.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?3720.#8.)+6596=0.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?3750.#8.)+>==60.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?3758.#8.)+>==50.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?2988.#8.)+?70<8.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+>==50.#8.)+98>?8.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+>==58.#8.)+46398.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?47:0.#8.)+?47:0.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?47=0.#8.)+>74?8.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?47>0.#8.)+><<?8.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?47>8.#8.)+>3;:8.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?4800.#8.)+>6?40.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?4808.#8.)+>3>30.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?48;8.#8.)+>7>80.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?4908.#8.)+>75?4.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?4910.#8.)+>79?8.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+102?40.#8.)+1.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+103>10.#4.)+1.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+103>;0.#8.)=)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+105>5<.#1.)+1.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+1065?8.#8.)+7???8000.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+1072=8.#1.)+1.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+1072=9.#1.)+1.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+1072>0.#8.)+7???????????.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+1072>8.#8.)=)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+1072?0.#8.)=)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+19817<.#1.)+1.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+1981:0.#8.)+????????????????.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+198223.#1.)+1.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+1984:0.#1.)=)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+638<80.#1.)+1.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+638<81.#1.)+1.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+638<82.#1.)+1.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+638<83.#1.)+1.)(5.(1.(1.$2.$3.)$2.))))))))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition rtc_mkcell (n : nat) (v : Z) : cell :=
  match n with
  | 1%nat => C1 (Z_to_bv 8 v)
  | 4%nat => C4 (Z_to_bv 64 v)
  | _ => C8 (Z_to_bv 64 v)
  end.

Definition rtc_holds (m : mem) (c : rtc_cell) : Prop :=
  let '(a, n, v) := c in ro_cells asegs m a [rtc_mkcell n v].

(* [comment removed for export] *)
Definition AGLOB_LO : Z := 0x0f73c0.
Definition AGLOB_HI : Z := 0x102f40.

(* [comment removed for export] *)
Definition rtc_pristine : list (Z * Z) := ltac2:(CDefT.buildp (gd_tbl_AImgRT ()) "(0.(1.$2.$2.)(4.$2.$2.+>>160.+?2900.)(0.(1.$2.$2.)(4.$2.$2.+?2:30.+?3790.)(0.(1.$2.$2.)(4.$2.$2.+?7040.+?70:0.)(0.(1.$2.$2.)(4.$2.$2.$6.$7.)(5.(1.$2.$2.))))))")
(* [comment removed for export] *).

Definition rtc_prist (x : Z) : Prop := Exists (fun r => fst r <= x < snd r) rtc_pristine.

Fixpoint in_ranges_b (l : list (Z * Z)) (A B : Z) : bool :=
  match l with
  | [] => false
  | (lo, hi) :: l' => (Z.leb lo A && Z.leb B hi) || in_ranges_b l' A B
  end.

Lemma in_ranges_b_sound : forall l A B x, in_ranges_b l A B = true -> A <= x < B ->
  Exists (fun r => fst r <= x < snd r) l.
Proof.
  induction l as [|[lo hi] l IH]; intros A B x H Hx; cbn in H; [discriminate|].
  apply Bool.orb_prop in H. destruct H as [H|H].
  - apply andb_prop in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    apply Exists_cons_hd. cbn. lia.
  - apply Exists_cons_tl. eapply IH; eauto.
Qed.

Definition asan_rtc (m : mem) : Prop :=
  Forall (rtc_holds m) rtc_cells
  /\ (forall a, rtc_prist a -> m (wa a) = None).

(* [comment removed for export] *)
Lemma asan_rtc_cell : forall m a n v, asan_rtc m -> In (a, n, v) rtc_cells -> ro_cells asegs m a [rtc_mkcell n v].
Proof.
  intros m a n v [H _] Hin. apply Forall_forall with (x := (a, n, v)) in H; [exact H | exact Hin].
Qed.

(* [comment removed for export] *)
Lemma asan_rtc_aglob : forall m a, asan_rtc m -> AGLOB_LO <= a < AGLOB_HI -> m (wa a) = None.
Proof.
  intros m a [_ H] Ha. apply H. unfold rtc_prist, rtc_pristine.
  do 3 apply Exists_cons_tl. apply Exists_cons_hd. cbn. exact Ha.
Qed.

(* [comment removed for export] *)
Lemma asan_rtc_const : ltac2:(CDefT.buildp (gd_tbl_AImgRT ()) "Pm,P,(8.&40.)(9.(8.&8.))PA,$2.Pbs,(:.(8.&8.))P,(;.R3.)P,(<.$=.(>.$?.R3.R2.)$10.)P,(<.$=.(11.$12.R4.(13.R4.(14.(15.(8.&8.)R3.))))$10.)(16.$?.R6.R5.(0.$17.(18.(15.(8.&8.)R4.)R4.)(5.$17.)))")
(* [comment removed for export] *).
Proof.
  intros m A bs [_ HP] Hb HR.
  eapply (Statics.pristine_cells asegs A (A + Z.of_nat (length bs)) (fun x => ~ rtc_prist x));
    [ | exact Hb | lia | lia | ].
  - split; [|split].
    + cbn in HR. unfold AGLOB_LO, AGLOB_HI in HR. lia.
    + cbn in HR. unfold AGLOB_LO, AGLOB_HI in HR. lia.
    + intros a Ha Hn. apply HP.
      destruct (Exists_dec (fun r => fst r <= a < snd r) rtc_pristine
                  ltac:(intros [lo hi]; cbn; destruct (Z_le_dec lo a); destruct (Z_lt_dec a hi);
                        first [left; lia | right; lia])) as [Y|N]; [exact Y| exfalso; exact (Hn N)].
  - intros a Ha Hn. apply Hn. eapply in_ranges_b_sound; eauto.
Qed.

(* [comment removed for export] *)
Lemma asan_rtc_memset_func : forall m, asan_rtc m -> ro_cells asegs m 0x0ee180 [C8 (Z_to_bv 64 0x67840)].
Proof.
  intros m H.
  pose proof (asan_rtc_const m 0x0ee180 (le8 (Z_to_bv 64 0x67840)) H
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as [_ RO].
  split; [cbn; split; [reflexivity| exact I] | exact RO].
Qed.

(* [comment removed for export] *)
Definition rtc_addr (x : Z) : Prop :=
  (exists a n v, In (a, n, v) rtc_cells /\ a <= x < a + Z.of_nat n) \/ rtc_prist x.
