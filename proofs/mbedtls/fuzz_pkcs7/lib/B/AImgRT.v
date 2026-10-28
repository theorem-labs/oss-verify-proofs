(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Cells Mem Step Statics.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AImgRT () : Init.string Init.list := ["Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "AGLOB_LO"; "AGLOB_HI"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "asan_rtc"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.Lib.Statics.img_bytes_b"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Datatypes.true"; "in_ranges_b"; "rtc_pristine"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"].


(* [comment removed for export] *)
Definition rtc_cell : Type := (Z * nat * Z)%type.

Definition rtc_cells : list rtc_cell := ltac2:(CDefT.buildp (gd_tbl_AImgRT ()) "(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?5>20.#8.)+>108<.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?5>28.#8.)=)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?5>30.#8.)+1994:0.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?5>40.#8.)+19;528.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?5>48.#8.)+1071?8.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?5>50.#8.)+1099?8.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?5>58.#8.)+10:6>8.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?5>60.#8.)+10:6?0.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?5>68.#8.)+10:6>0.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?5>70.#8.)+?7<=0.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?69;8.#8.)+10:6=9.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?6:;0.#8.)+?5=48.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?6:;8.#8.)=)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?6:=0.#8.)+?:780.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?6:=8.#8.)+106340.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?6:>0.#8.)+65<:=0.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?6;10.#8.)+?1128.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?6;18.#8.)+?1118.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?5=48.#8.)+?:488.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?1118.#8.)+996?4.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?1120.#8.)+4690<.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?7;60.#8.)+?7;60.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?7;90.#8.)+>:8<4.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?7;:0.#8.)+?00<4.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?7;:8.#8.)+>6?74.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?7;<0.#8.)+>:30<.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?7;<8.#8.)+>71?<.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?7<78.#8.)+>;24<.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?7<<8.#8.)+>:9<0.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+?7<=0.#8.)+>:=<4.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+106340.#8.)+1.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+107210.#4.)+1.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+1072;0.#8.)=)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+10925<.#1.)+1.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+1099?8.#8.)+7???8000.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+10:6=8.#1.)+1.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+10:6=9.#1.)+1.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+10:6>0.#8.)+7???????????.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+10:6>8.#8.)=)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+10:6?0.#8.)=)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+19;57<.#1.)+1.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+19;5:0.#8.)+????????????????.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+19;623.#1.)+1.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+19;8:0.#1.)=)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+63<080.#1.)+1.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+63<081.#1.)+1.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+63<082.#1.)+1.)(0.(1.(1.$2.$3.)$2.)(4.(1.$2.$3.)$2.(4.$2.$3.+63<083.#1.)+1.)(5.(1.(1.$2.$3.)$2.))))))))))))))))))))))))))))))))))))))))))))))))))")
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
Definition AGLOB_LO : Z := 0x0fa780.
Definition AGLOB_HI : Z := 0x106340.

(* [comment removed for export] *)
Definition rtc_pristine : list (Z * Z) := ltac2:(CDefT.buildp (gd_tbl_AImgRT ()) "(0.(1.$2.$2.)(4.$2.$2.+?1520.+?5<<0.)(0.(1.$2.$2.)(4.$2.$2.+?5=?0.+?6;50.)(0.(1.$2.$2.)(4.$2.$2.+?:400.+?:460.)(0.(1.$2.$2.)(4.$2.$2.$6.$7.)(5.(1.$2.$2.))))))")
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
Lemma asan_rtc_memset_func : forall m, asan_rtc m -> ro_cells asegs m 0x0f1540 [C8 (Z_to_bv 64 0x67db4)].
Proof.
  intros m H.
  pose proof (asan_rtc_const m 0x0f1540 (le8 (Z_to_bv 64 0x67db4)) H
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as [_ RO].
  split; [cbn; split; [reflexivity| exact I] | exact RO].
Qed.

(* [comment removed for export] *)
Definition rtc_addr (x : Z) : Prop :=
  (exists a n v, In (a, n, v) rtc_cells /\ a <= x < a + Z.of_nat n) \/ rtc_prist x.
