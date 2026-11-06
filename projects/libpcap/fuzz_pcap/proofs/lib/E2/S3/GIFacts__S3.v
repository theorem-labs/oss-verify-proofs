(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Arr Bytes ITree Nodes Decode SysStep ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad StdioCore Stdio Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI.
From OSSVerify.libpcap.fuzz_pcap.images Require Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Fmt PcapPrelim PcapTypes PcapPure Pcap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module GIFacts.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad StdioCore Stdio Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require GI. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.Exit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section WithCeil.
Context {CEILV : CEIL}.
Section Facts.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr).
  Notation cblk := (@cblock hptr).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma GI_blocks : forall R s CL m, GI K R s CL m -> Forall (block_ok (utp R)) CL /\ blocks_apart CL.
  Proof using Type. pin_using tt. ceil_facts.
    intros R s CL m (FB & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [BO BA] & _).
    apply Forall_app in BO as [BO _]. apply blocks_apart_app_inv in BA as (BA & _ & _). auto.
  Qed.

  Lemma GI_tls : forall R s CL m, GI K R s CL m -> ps_tls s = utp R - 200 /\ tls_block_ok (utp R - 200).
  Proof using Type. pin_using tt. ceil_facts. intros R s CL m (FB & _ & _ & _ & _ & _ & _ & _ & _ & _ & E & T & _). auto. Qed.

  Lemma GI_core : forall R s CL m, GI K R s CL m ->
    CORE_TLS R m /\ PCAP_TLS R m /\ CORE_LIBC R m /\ CORE_MISC m /\ CORE_EXIT (rc_cb R) m /\ CORE_STK R m.
  Proof using Type. pin_using tt. ceil_facts.
    intros R s CL m (FB & _ & _ & _ & A & B & C & D & E & F & _).
    split; [exact A|]. split; [exact B|]. split; [exact C|]. split; [exact D|]. split; [exact E|exact F].
  Qed.

  Lemma GI_spw : forall R s CL m, GI K R s CL m -> 0x7fff80000000 <= usp0 R.
  Proof using Type. pin_using tt. ceil_facts. intros R s CL m (FB & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SPW & _). exact (proj1 SPW). Qed.
  Lemma GI_sp47 : forall R s CL m, GI K R s CL m -> usp0 R <= 2^47.
  Proof using Type. pin_using tt. ceil_facts. intros R s CL m (FB & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SPW & _). exact (proj2 SPW). Qed.
  (* [comment removed for export] *)
  Lemma GI_ceil_lo : forall R s CL m, GI K R s CL m -> CEILZ <= rc_lo R.
  Proof using Type. pin_using tt. ceil_facts. intros R s CL m (FB & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CLO). exact CLO. Qed.

  Lemma in_block_facts : forall u (CL : list cblk) a,
    Forall (block_ok u) CL -> in_block CL a ->
    0 < a /\ a < CEILZ /\ (a < 0x10000 \/ 0x55000 <= a) /\ (a < u - 200 \/ u - 200 + 4096 <= a).
  Proof using Type. pin_using tt. ceil_facts.
    intros u CL a BO Hin. unfold in_block in Hin. apply Exists_exists in Hin as (b & Hb & Hr).
    pose proof (proj1 (Forall_forall _ _) BO b Hb) as (K1 & K2 & K3 & K4 & K5 & K6). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma client_range_bounds : forall R s (CL : list cblk) m A n,
    GI K R s CL m -> (forall a, A <= a < A + n -> in_block CL a) -> 0 < n ->
    0 < A /\ A + n <= CEILZ /\ (A + n <= 0x10000 \/ 0x55000 <= A) /\ (A + n <= utp R - 200 \/ utp R - 200 + 4096 <= A).
  Proof using Type. pin_using tt. ceil_facts.
    intros R s CL m A n G HR Hn. destruct (GI_blocks _ _ _ _ G) as [BO _].
    destruct (in_block_facts _ _ A BO (HR A ltac:(lia))) as (A1 & A2 & A3 & A4).
    destruct (in_block_facts _ _ (A + n - 1) BO (HR (A + n - 1) ltac:(lia))) as (B1 & B2 & B3 & B4).
    split; [lia|]. split; [lia|]. split.
    - destruct (Z_le_gt_dec (A + n) 0x10000); [left; lia|]. destruct (Z_le_gt_dec 0x55000 A); [right; lia|]. exfalso.
      destruct (in_block_facts _ _ (Z.max A 0x10000) BO (HR (Z.max A 0x10000) ltac:(lia))) as (C1 & C2 & C3 & C4). lia.
    - destruct (Z_le_gt_dec (A + n) (utp R - 200)); [left; lia|]. destruct (Z_le_gt_dec (utp R - 200 + 4096) A); [right; lia|]. exfalso.
      destruct (in_block_facts _ _ (Z.max A (utp R - 200)) BO (HR (Z.max A (utp R - 200)) ltac:(lia))) as (C1 & C2 & C3 & C4). lia.
  Qed.

  Lemma GI_harn : forall R s CL m, GI K R s CL m -> exists FB, HARNR (ps_outfile s) FB m.
  Proof using Type. pin_using tt. ceil_facts. intros R s CL m (FB & _ & _ & A & _). exists FB. exact A. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition client_iv (R : rctx) (CL : list cblk) (iv : Z * Z) : Prop :=
    (rc_lo R <= fst iv /\ snd iv <= rc_spmain R) \/ iv_in_block CL iv.

  Lemma outside_of_Forall : forall (P : Z * Z -> Prop) W a,
    Forall P W -> (forall iv, P iv -> ~ (fst iv <= a < snd iv)) -> outside W a.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
    induction W as [|[lo hi] W IH]; intros a HF HP; cbn; [exact I|].
    apply Forall_cons_iff in HF as [H1 H2]. split; [exact (HP _ H1) | apply IH; assumption].
  Qed.

  Lemma GI_client_frame : forall R s CL m m' W,
    GI K R s CL m -> munch W m m' -> wmono ssegs m m' ->
    Forall (client_iv R CL) W ->
    GI K R s CL m'.
  Proof using HFL SFL. pin_using (fun (HFL SFL : unit) => tt). ceil_facts.
    intros R s CL m m' W G MU WM HW.
    destruct G as (FB & HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK & SPW).
    pose proof BOK as BOK'. destruct BOK' as [BO BA].
    pose proof (blocks_apart_app_inv _ _ BA) as (BA1 & BA2 & BAX).
    apply Forall_app in BO. destruct BO as [BO1 BO2].
    pose proof TB as TB'. unfold tls_block_ok in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    (* [comment removed for export] *)
    assert (OUT : forall a, 0 <= a < 2^64 ->
              (a < rc_lo R \/ (rc_spmain R <= a)) -> ~ in_block CL a -> outside W a).
    { intros a Ha H1 H2. eapply outside_of_Forall; [exact HW|]. intros [lo hi] [Hs|Hb]; [cbn [fst snd] in Hs |- *; lia|]. cbn [fst snd].
      intros Hin. apply H2. unfold iv_in_block in Hb. apply Exists_exists in Hb as (b & HbIn & Hb1 & Hb2). cbn [fst snd] in Hb1, Hb2.
      unfold in_block. apply Exists_exists. exists b. split; [exact HbIn | lia]. }
    assert (NIB : forall a, (0x10000 <= a < 0x55000 \/ CEILZ <= a \/ (utp R - 200 <= a < utp R - 200 + 4096) \/ in_block FB a) -> ~ in_block CL a).
    { intros a Ha Hin. unfold in_block in Hin. apply Exists_exists in Hin as (b & HbIn & Hb).
      pose proof (proj1 (Forall_forall _ _) BO1 b HbIn) as (K1 & K2 & K3 & K4 & K5 & K6).
      destruct Ha as [Ha|[Ha|[Ha|Ha]]]; try lia.
      apply Exists_exists in Ha as (b' & Hb'In & Hb'). pose proof (BAX b b' HbIn Hb'In) as AP. unfold apart in AP. lia. }
    assert (LO : usp0 R - 8388608 >= CEILZ). { pose proof (proj2 SPW) as CLO__. unfold rc_lo in CLO__. lia. }
    unfold rc_spmain in *.
    exists FB. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [exact Etls|split; [exact TB|split; [exact BOK|exact SPW]]]]]]]]]]]].
    - (* [comment removed for export] *) eapply HFL; [exact HH|exact MU|exact WM|].
      apply Forall_forall. intros [lo' hi'] Hiv. unfold heap_client_iv. pose proof (proj1 (Forall_forall _ _) HW _ Hiv) as [Hs|Hb]; cbn [fst snd] in *.
      + left. unfold rc_lo in *. lia.
      + right; left. unfold iv_in_block in *. rewrite Exists_app. left. exact Hb.
    - (* [comment removed for export] *) eapply SFL; [exact HS|]. eapply agrees_on_of_munch; [exact MU|exact WM|].
      intros a Ha Hfp. unfold stdio_fp, stdio_static in Hfp.
      destruct Hfp as [Hst|Hfb].
      + apply OUT; [exact Ha| left; lia | apply NIB; lia].
      + apply Exists_exists in Hfb as (b & HbIn & Hb). pose proof (proj1 (Forall_forall _ _) BO2 b HbIn) as (K1 & K2 & K3 & K4 & K5 & K6).
        apply OUT; [exact Ha| left; lia | apply NIB]. right; right; right. apply Exists_exists. exists b. auto.
    - (* [comment removed for export] *) eapply HARNR_agree; [| |exact HA]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold harn_fp, harn_static in Hp. apply OUT; [exact Ha|left; lia|apply NIB; lia].
    - eapply CORE_TLS_agree; [| |exact CT]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_tls_fp in Hp. apply OUT; [exact Ha|left; lia|apply NIB; lia].
    - eapply PCAP_TLS_agree; [| |exact PT]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold pcap_tls_fp in Hp. apply OUT; [exact Ha|left; lia|apply NIB; lia].
    - eapply CORE_LIBC_agree; [| |exact CLI]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_libc_fp in Hp. apply OUT; [exact Ha|left; lia|apply NIB; lia].
    - eapply CORE_MISC_agree; [| |exact CM]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_misc_fp in Hp. apply OUT; [exact Ha|left; lia|apply NIB; lia].
    - eapply CORE_EXIT_agree; [| |exact CE]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_exit_fp in Hp. apply OUT; [exact Ha|left; lia|apply NIB; lia].
    - eapply CORE_STK_agree; [| |exact CS]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_stk_fp in Hp. apply OUT; [exact Ha|right; lia|apply NIB; lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma GI_initflag : forall R s CL m, GI K R s CL m ->
    (exists ib : byte, rw_cells ssegs m 0x33990 [C1 ib]) /\ rw_cells ssegs m 0x225c0 [C8 (Z_to_bv 64 0)].
  Proof using Type. pin_using tt. ceil_facts.
    intros R s CL m (FB & _ & _ & (HAi & _ & _) & _ & _ & _ & (_ & _ & _ & _ & CM & _) & _). split; [exact HAi | exact CM].
  Qed.

  (* [comment removed for export] *)
  Hypothesis HCB : heap_cb_law K.
  Hypothesis SCB : stdio_cb_law K.
  Lemma GI_atx_frame : forall R s CL m m' W (b : bool),
    GI K R s CL m -> munch ((0x33990, 0x33995) :: (0x53ae0, 0x53d00) :: W) m m' -> wmono ssegs m m' ->
    Forall (client_iv R CL) W ->
    ATX b m' ->
    GI K (set_cb R b) s CL m'.
  Proof using HFL SFL HCB SCB. pin_using (fun (HFL SFL HCB SCB : unit) => tt). ceil_facts.
    intros R s CL m m' W b G MU WM HW HATX.
    destruct G as (FB & HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK & SPW).
    pose proof BOK as BOK'. destruct BOK' as [BO BA].
    pose proof (blocks_apart_app_inv _ _ BA) as (BA1 & BA2 & BAX).
    apply Forall_app in BO. destruct BO as [BO1 BO2].
    pose proof TB as TB'. unfold tls_block_ok in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    assert (OUT : forall a, 0 <= a < 2^64 -> ~ (0x33990 <= a < 0x33995) -> ~ (0x53ae0 <= a < 0x53d00) ->
              (a < rc_lo R \/ (rc_spmain R <= a)) -> ~ in_block CL a -> outside ((0x33990, 0x33995) :: (0x53ae0, 0x53d00) :: W) a).
    { intros a Ha Hne1 Hne2 H1 H2. cbn [outside]. split; [lia|]. split; [lia|]. eapply outside_of_Forall; [exact HW|]. intros [lo hi] [Hs|Hb]; [cbn [fst snd] in Hs |- *; lia|]. cbn [fst snd].
      intros Hin. apply H2. unfold iv_in_block in Hb. apply Exists_exists in Hb as (b0 & HbIn & Hb1 & Hb2). cbn [fst snd] in Hb1, Hb2.
      unfold in_block. apply Exists_exists. exists b0. split; [exact HbIn | lia]. }
    assert (NIB : forall a, (0x10000 <= a < 0x55000 \/ CEILZ <= a \/ (utp R - 200 <= a < utp R - 200 + 4096) \/ in_block FB a) -> ~ in_block CL a).
    { intros a Ha Hin. unfold in_block in Hin. apply Exists_exists in Hin as (b0 & HbIn & Hb).
      pose proof (proj1 (Forall_forall _ _) BO1 b0 HbIn) as (K1 & K2 & K3 & K4 & K5 & K6).
      destruct Ha as [Ha|[Ha|[Ha|Ha]]]; try lia.
      apply Exists_exists in Ha as (b' & Hb'In & Hb'). pose proof (BAX b0 b' HbIn Hb'In) as AP. unfold apart in AP. lia. }
    assert (LO : usp0 R - 8388608 >= CEILZ). { pose proof (proj2 SPW) as CLO__. unfold rc_lo in CLO__. lia. }
    unfold rc_spmain in *.
    pose proof HATX as HATX'. destruct HATX' as (reg & pad & f0 & g0 & j1 & j2 & X1 & X2 & X3 & X4).
    exists FB. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [exact Etls|split; [exact TB|split; [exact BOK|exact SPW]]]]]]]]]]]].
    - apply HCB. eapply HFL; [exact HH|exact MU|exact WM|].
      apply Forall_cons; [unfold heap_client_iv; right; right; left; cbn [fst snd]; lia|].
      apply Forall_cons; [unfold heap_client_iv; right; right; left; cbn [fst snd]; lia|].
      apply Forall_forall. intros [lo' hi'] Hiv. unfold heap_client_iv. pose proof (proj1 (Forall_forall _ _) HW _ Hiv) as [Hs|Hb]; cbn [fst snd] in *.
      + left. unfold rc_lo in *. lia.
      + right; left. unfold iv_in_block in *. rewrite Exists_app. left. exact Hb.
    - apply SCB. eapply SFL; [exact HS|]. eapply agrees_on_of_munch; [exact MU|exact WM|].
      intros a Ha Hfp. unfold stdio_fp, stdio_static in Hfp.
      destruct Hfp as [Hst|Hfb].
      + apply OUT; [exact Ha| lia | lia | left; lia | apply NIB; lia].
      + apply Exists_exists in Hfb as (b0 & HbIn & Hb). pose proof (proj1 (Forall_forall _ _) BO2 b0 HbIn) as (K1 & K2 & K3 & K4 & K5 & K6).
        apply OUT; [exact Ha| lia | lia | left; lia | apply NIB]. right; right; right. apply Exists_exists. exists b0. auto.
    - (* [comment removed for export] *)
      destruct HA as (_ & (ej & HAe) & HAo). split.
      { exists (bool8 reg). apply (proj1 (rw_cells_app ssegs m' _ [_] [_; _])) in X1 as [X1 _]. exact X1. }
      split.
      + exists ej. eapply agrees_rw_cells; [eapply agrees_on_of_munch; [exact MU|exact WM|intros a Ha Hp; exact (Hp Ha)] | exact HAe |].
        intros a Hp Ha. cbn in Hp. apply OUT; [exact Ha|lia|lia|left; lia|apply NIB; lia].
      + destruct (ps_outfile s) as [q|].
        * destruct HAo as (A & HA1 & HAo). exists A. split; [exact HA1|].
          eapply agrees_rw_cells; [eapply agrees_on_of_munch; [exact MU|exact WM|intros a Ha Hp; exact (Hp Ha)] | exact HAo |].
          intros a Hp Ha; cbn in Hp; apply OUT; [exact Ha|lia|lia|left; lia|apply NIB; lia].
        * eapply agrees_rw_cells; [eapply agrees_on_of_munch; [exact MU|exact WM|intros a Ha Hp; exact (Hp Ha)] | exact HAo |].
          intros a Hp Ha; cbn in Hp; apply OUT; [exact Ha|lia|lia|left; lia|apply NIB; lia].
    - change (CORE_TLS R m'). eapply CORE_TLS_agree; [| |exact CT]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_tls_fp in Hp. apply OUT; [exact Ha|lia|lia|left; lia|apply NIB; lia].
    - change (PCAP_TLS R m'). eapply PCAP_TLS_agree; [| |exact PT]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold pcap_tls_fp in Hp. apply OUT; [exact Ha|lia|lia|left; lia|apply NIB; lia].
    - change (CORE_LIBC R m'). eapply CORE_LIBC_agree; [| |exact CLI]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_libc_fp in Hp. apply OUT; [exact Ha|lia|lia|left; lia|apply NIB; lia].
    - eapply CORE_MISC_agree; [| |exact CM]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_misc_fp in Hp. apply OUT; [exact Ha|lia|lia|left; lia|apply NIB; lia].
    - (* [comment removed for export] *)
      change (CORE_EXIT b m'). destruct CE as (A1 & _ & A3 & A4 & A5 & A6 & A7).
      assert (AGo : agrees_on (fun a => (0x53d00 <= a < 0x53d04) \/ (0x22628 <= a < 0x22638) \/ (0x22558 <= a < 0x22560)
                                        \/ (0x23988 <= a < 0x23989) \/ (0x225a8 <= a < 0x225b8) \/ (0x23638 <= a < 0x23640)) m m').
      { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. apply OUT; [exact Ha|lia|lia|left; lia|apply NIB; lia]. }
      split; [eapply agrees_rw_cells; [exact AGo | exact A1 | intros a Ha; sl_lit_sizes_in Ha; cbn in Ha; lia]|].
      split; [exact HATX|].
      split; [eapply agrees_rw_cells; [exact AGo | exact A3 | intros a Ha; sl_lit_sizes_in Ha; cbn in Ha; lia]|].
      split; [eapply agrees_rw_cells; [exact AGo | exact A4 | intros a Ha; sl_lit_sizes_in Ha; cbn in Ha; lia]|].
      split; [eapply agrees_rw_cells; [exact AGo | exact A5 | intros a Ha; sl_lit_sizes_in Ha; cbn in Ha; lia]|].
      split; [eapply agrees_rw_cells; [exact AGo | exact A6 | intros a Ha; sl_lit_sizes_in Ha; cbn in Ha; lia]|].
      eapply agrees_rw_cells; [exact AGo | exact A7 | intros a Ha; sl_lit_sizes_in Ha; cbn in Ha; lia].
    - change (CORE_STK R m'). eapply CORE_STK_agree; [| |exact CS]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_stk_fp in Hp. apply OUT; [exact Ha|lia|lia|right; lia|apply NIB; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma GI_atx : forall R s CL m, GI K R s CL m -> ATX (rc_cb R) m.
  Proof using Type. pin_using tt. ceil_facts.
    intros R s CL m (FB & _ & _ & _ & _ & _ & _ & _ & (_ & X & _) & _). exact X.
  Qed.

  (* [comment removed for export] *)
  Lemma GI_client_frame_errno : forall R s CL m m' W (e : word),
    GI K R s CL m -> munch ((utp R - 164, utp R - 160) :: W) m m' -> wmono ssegs m m' ->
    Forall (client_iv R CL) W ->
    rw_cells ssegs m' (utp R + -164) [C4 e] ->
    GI K R s CL m'.
  Proof using HFL SFL. pin_using (fun (HFL SFL : unit) => tt). ceil_facts.
    intros R s CL m m' W e G MU WM HW HE.
    destruct G as (FB & HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK & SPW).
    pose proof BOK as BOK'. destruct BOK' as [BO BA].
    pose proof (blocks_apart_app_inv _ _ BA) as (BA1 & BA2 & BAX).
    apply Forall_app in BO. destruct BO as [BO1 BO2].
    pose proof TB as TB'. unfold tls_block_ok in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    assert (OUT : forall a, 0 <= a < 2^64 -> ~ (utp R - 164 <= a < utp R - 160) ->
              (a < rc_lo R \/ (rc_spmain R <= a)) -> ~ in_block CL a -> outside ((utp R - 164, utp R - 160) :: W) a).
    { intros a Ha Hne H1 H2. cbn [outside]. split; [lia|]. eapply outside_of_Forall; [exact HW|]. intros [lo hi] [Hs|Hb]; [cbn [fst snd] in Hs |- *; lia|]. cbn [fst snd].
      intros Hin. apply H2. unfold iv_in_block in Hb. apply Exists_exists in Hb as (b & HbIn & Hb1 & Hb2). cbn [fst snd] in Hb1, Hb2.
      unfold in_block. apply Exists_exists. exists b. split; [exact HbIn | lia]. }
    assert (NIB : forall a, (0x10000 <= a < 0x55000 \/ CEILZ <= a \/ (utp R - 200 <= a < utp R - 200 + 4096) \/ in_block FB a) -> ~ in_block CL a).
    { intros a Ha Hin. unfold in_block in Hin. apply Exists_exists in Hin as (b & HbIn & Hb).
      pose proof (proj1 (Forall_forall _ _) BO1 b HbIn) as (K1 & K2 & K3 & K4 & K5 & K6).
      destruct Ha as [Ha|[Ha|[Ha|Ha]]]; try lia.
      apply Exists_exists in Ha as (b' & Hb'In & Hb'). pose proof (BAX b b' HbIn Hb'In) as AP. unfold apart in AP. lia. }
    assert (LO : usp0 R - 8388608 >= CEILZ). { pose proof (proj2 SPW) as CLO__. unfold rc_lo in CLO__. lia. }
    unfold rc_spmain in *.
    exists FB. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [exact Etls|split; [exact TB|split; [exact BOK|exact SPW]]]]]]]]]]]].
    - eapply HFL; [exact HH|exact MU|exact WM|].
      apply Forall_cons; [unfold heap_client_iv; right; right; right; cbn [fst snd]; lia|].
      apply Forall_forall. intros [lo' hi'] Hiv. unfold heap_client_iv. pose proof (proj1 (Forall_forall _ _) HW _ Hiv) as [Hs|Hb]; cbn [fst snd] in *.
      + left. unfold rc_lo in *. lia.
      + right; left. unfold iv_in_block in *. rewrite Exists_app. left. exact Hb.
    - eapply SFL; [exact HS|]. eapply agrees_on_of_munch; [exact MU|exact WM|].
      intros a Ha Hfp. unfold stdio_fp, stdio_static in Hfp.
      destruct Hfp as [Hst|Hfb].
      + apply OUT; [exact Ha| lia | left; lia | apply NIB; lia].
      + apply Exists_exists in Hfb as (b & HbIn & Hb). pose proof (proj1 (Forall_forall _ _) BO2 b HbIn) as (K1 & K2 & K3 & K4 & K5 & K6).
        apply OUT; [exact Ha| lia | left; lia | apply NIB]. right; right; right. apply Exists_exists. exists b. auto.
    - eapply HARNR_agree; [| |exact HA]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold harn_fp, harn_static in Hp. apply OUT; [exact Ha|lia|left; lia|apply NIB; lia].
    - (* [comment removed for export] *)
      unfold CORE_TLS in CT. let z := fresh "sblz" in let x := fresh "sbl" in pose (z := repeat (Z_to_bv 8 0) 3616); change (repeat (Z_to_bv 8 0) 3616) with z in CT; pose (x := 3616%nat); change 3616%nat with x in CT; destruct CT as (t & e0 & T1 & T2 & T3 & T4 & T5 & T6 & Ht); subst z x. exists t, e.
      assert (AGo : agrees_on (fun a => outside ((utp R - 164, utp R - 160) :: W) a) m m').
      { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact Hp. }
      Ltac trt AGo OUT NIB T := eapply agrees_rw_cells; [exact AGo | exact T | intros a Ha; sl_lit_sizes_in Ha; cbn -[Z.add Z.mul Z.of_nat] in Ha; apply OUT; [lia|lia|left; lia|apply NIB; lia]].
      split; [trt AGo OUT NIB T1|]. split; [exact HE|]. split; [trt AGo OUT NIB T3|]. split; [trt AGo OUT NIB T4|]. split; [trt AGo OUT NIB T5|]. split; [trt AGo OUT NIB T6| exact Ht].
    - eapply PCAP_TLS_agree; [| |exact PT]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold pcap_tls_fp in Hp. apply OUT; [exact Ha|lia|left; lia|apply NIB; lia].
    - eapply CORE_LIBC_agree; [| |exact CLI]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_libc_fp in Hp. apply OUT; [exact Ha|lia|left; lia|apply NIB; lia].
    - eapply CORE_MISC_agree; [| |exact CM]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_misc_fp in Hp. apply OUT; [exact Ha|lia|left; lia|apply NIB; lia].
    - eapply CORE_EXIT_agree; [| |exact CE]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_exit_fp in Hp. apply OUT; [exact Ha|lia|left; lia|apply NIB; lia].
    - eapply CORE_STK_agree; [| |exact CS]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_stk_fp in Hp. apply OUT; [exact Ha|lia|right; lia|apply NIB; lia].
  Qed.

  (* [comment removed for export] *)
  Definition rs_iv (iv : Z * Z) : Prop := 0x23989 <= fst iv /\ snd iv <= 0x33989.

  Lemma GI_client_frame_errno_rs : forall R s CL m m' W (e : word),
    GI K R s CL m -> munch ((utp R - 164, utp R - 160) :: W) m m' -> wmono ssegs m m' ->
    Forall (fun iv => client_iv R CL iv \/ rs_iv iv) W ->
    rw_cells ssegs m' (utp R + -164) [C4 e] ->
    GI K R s CL m'.
  Proof using HFL SFL. pin_using (fun (HFL SFL : unit) => tt). ceil_facts.
    intros R s CL m m' W e G MU WM HW HE.
    destruct G as (FB & HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK & SPW).
    pose proof BOK as BOK'. destruct BOK' as [BO BA].
    pose proof (blocks_apart_app_inv _ _ BA) as (BA1 & BA2 & BAX).
    apply Forall_app in BO. destruct BO as [BO1 BO2].
    pose proof TB as TB'. unfold tls_block_ok in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    unfold rs_iv in HW.
    assert (OUT : forall a, 0 <= a < 2^64 -> ~ (utp R - 164 <= a < utp R - 160) -> ~ (0x23989 <= a < 0x33989) ->
              (a < rc_lo R \/ (rc_spmain R <= a)) -> ~ in_block CL a -> outside ((utp R - 164, utp R - 160) :: W) a).
    { intros a Ha Hne Hrs H1 H2. cbn [outside]. split; [lia|]. eapply outside_of_Forall; [exact HW|]. intros [lo hi] [[Hs|Hb]|Hr]; [cbn [fst snd] in Hs |- *; lia| |cbn [fst snd] in Hr |- *; lia]. cbn [fst snd].
      intros Hin. apply H2. unfold iv_in_block in Hb. apply Exists_exists in Hb as (b & HbIn & Hb1 & Hb2). cbn [fst snd] in Hb1, Hb2.
      unfold in_block. apply Exists_exists. exists b. split; [exact HbIn | lia]. }
    assert (NIB : forall a, (0x10000 <= a < 0x55000 \/ CEILZ <= a \/ (utp R - 200 <= a < utp R - 200 + 4096) \/ in_block FB a) -> ~ in_block CL a).
    { intros a Ha Hin. unfold in_block in Hin. apply Exists_exists in Hin as (b & HbIn & Hb).
      pose proof (proj1 (Forall_forall _ _) BO1 b HbIn) as (K1 & K2 & K3 & K4 & K5 & K6).
      destruct Ha as [Ha|[Ha|[Ha|Ha]]]; try lia.
      apply Exists_exists in Ha as (b' & Hb'In & Hb'). pose proof (BAX b b' HbIn Hb'In) as AP. unfold apart in AP. lia. }
    assert (LO : usp0 R - 8388608 >= CEILZ). { pose proof (proj2 SPW) as CLO__. unfold rc_lo in CLO__. lia. }
    unfold rc_spmain in *.
    exists FB. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [exact Etls|split; [exact TB|split; [exact BOK|exact SPW]]]]]]]]]]]].
    - eapply HFL; [exact HH|exact MU|exact WM|].
      apply Forall_cons; [unfold heap_client_iv; right; right; right; cbn [fst snd]; lia|].
      apply Forall_forall. intros [lo' hi'] Hiv. unfold heap_client_iv. pose proof (proj1 (Forall_forall _ _) HW _ Hiv) as [[Hs|Hb]|Hr]; cbn [fst snd] in *.
      + left. unfold rc_lo in *. lia.
      + right; left. unfold iv_in_block in *. rewrite Exists_app. left. exact Hb.
      + right; right; left. lia.
    - eapply SFL; [exact HS|]. eapply agrees_on_of_munch; [exact MU|exact WM|].
      intros a Ha Hfp. unfold stdio_fp, stdio_static in Hfp.
      destruct Hfp as [Hst|Hfb].
      + apply OUT; [exact Ha| lia | lia | left; lia | apply NIB; lia].
      + apply Exists_exists in Hfb as (b & HbIn & Hb). pose proof (proj1 (Forall_forall _ _) BO2 b HbIn) as (K1 & K2 & K3 & K4 & K5 & K6).
        apply OUT; [exact Ha| lia | lia | left; lia | apply NIB]. right; right; right. apply Exists_exists. exists b. auto.
    - eapply HARNR_agree; [| |exact HA]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold harn_fp, harn_static in Hp. apply OUT; [exact Ha|lia|lia|left; lia|apply NIB; lia].
    - (* [comment removed for export] *)
      unfold CORE_TLS in CT. let z := fresh "sblz" in let x := fresh "sbl" in pose (z := repeat (Z_to_bv 8 0) 3616); change (repeat (Z_to_bv 8 0) 3616) with z in CT; pose (x := 3616%nat); change 3616%nat with x in CT; destruct CT as (t & e0 & T1 & T2 & T3 & T4 & T5 & T6 & Ht); subst z x. exists t, e.
      assert (AGo : agrees_on (fun a => outside ((utp R - 164, utp R - 160) :: W) a) m m').
      { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact Hp. }
      Ltac trt_rs AGo OUT NIB T := eapply agrees_rw_cells; [exact AGo | exact T | intros a Ha; sl_lit_sizes_in Ha; cbn -[Z.add Z.mul Z.of_nat] in Ha; apply OUT; [lia|lia|lia|left; lia|apply NIB; lia]].
      split; [trt_rs AGo OUT NIB T1|]. split; [exact HE|]. split; [trt_rs AGo OUT NIB T3|]. split; [trt_rs AGo OUT NIB T4|]. split; [trt_rs AGo OUT NIB T5|]. split; [trt_rs AGo OUT NIB T6| exact Ht].
    - eapply PCAP_TLS_agree; [| |exact PT]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold pcap_tls_fp in Hp. apply OUT; [exact Ha|lia|lia|left; lia|apply NIB; lia].
    - eapply CORE_LIBC_agree; [| |exact CLI]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_libc_fp in Hp. apply OUT; [exact Ha|lia|lia|left; lia|apply NIB; lia].
    - eapply CORE_MISC_agree; [| |exact CM]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_misc_fp in Hp. apply OUT; [exact Ha|lia|lia|left; lia|apply NIB; lia].
    - eapply CORE_EXIT_agree; [| |exact CE]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_exit_fp in Hp. apply OUT; [exact Ha|lia|lia|left; lia|apply NIB; lia].
    - eapply CORE_STK_agree; [| |exact CS]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_stk_fp in Hp. apply OUT; [exact Ha|lia|lia|right; lia|apply NIB; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma keeps_rw_cells_stack : forall (CL : list cblk) SP m m' A cs,
    agrees_on (client_keeps CL SP) m m' -> rw_cells ssegs m A cs -> SP <= A -> rw_cells ssegs m' A cs.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros CL SP m m' A cs AG HC HA. eapply agrees_rw_cells; [exact AG|exact HC|]. intros a Ha. left. lia. Qed.
  Lemma keeps_bytes_at_stack : forall (CL : list cblk) SP m m' A bs,
    agrees_on (client_keeps CL SP) m m' -> bytes_at ssegs m A bs -> SP <= A -> bytes_at ssegs m' A bs.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros CL SP m m' A bs AG HC HA. eapply agrees_bytes_at; [exact AG|exact HC|]. intros a Ha. left. lia. Qed.
  Lemma keeps_rw_cells_block : forall (CL : list cblk) SP m m' A cs,
    agrees_on (client_keeps CL SP) m m' -> rw_cells ssegs m A cs ->
    (forall a, A <= a < A + Z.of_nat (cells_size cs) -> in_block CL a) -> rw_cells ssegs m' A cs.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros CL SP m m' A cs AG HC HA. eapply agrees_rw_cells; [exact AG|exact HC|]. intros a Ha. right. apply HA. exact Ha. Qed.
  Lemma keeps_bytes_at_block : forall (CL : list cblk) SP m m' A bs,
    agrees_on (client_keeps CL SP) m m' -> bytes_at ssegs m A bs ->
    (forall a, A <= a < A + Z.of_nat (length bs) -> in_block CL a) -> bytes_at ssegs m' A bs.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros CL SP m m' A bs AG HC HA. eapply agrees_bytes_at; [exact AG|exact HC|]. intros a Ha. right. apply HA. exact Ha. Qed.

  Lemma client_keeps_weaken : forall (CL CL' : list cblk) SP SP' m m',
    agrees_on (client_keeps CL SP) m m' -> SP <= SP' -> (forall a, in_block CL' a -> in_block CL a) ->
    agrees_on (client_keeps CL' SP') m m'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros CL CL' SP SP' m m' AG HS HB. eapply agrees_on_weaken; [exact AG|]. intros a [Ha|Ha]; [left; lia | right; apply HB; exact Ha]. Qed.

  Lemma in_block_cons : forall (b : cblk) CL a, in_block CL a -> in_block (b :: CL) a.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros b CL a Hin. unfold in_block in *. apply Exists_cons_tl. exact Hin. Qed.

  (* [comment removed for export] *)
  Lemma keeps_of_munch : forall R s (CL : list cblk) m m0 W SP,
    GI K R s CL m -> munch W m m0 -> wmono ssegs m m0 ->
    Forall (fun iv => (CEILZ <= fst iv /\ snd iv <= SP) \/ (0x10000 <= fst iv /\ snd iv <= 0x55000)) W ->
    CEILZ <= SP ->
    agrees_on (client_keeps CL SP) m m0.
  Proof using Type. pin_using tt. ceil_facts.
    intros R s CL m m0 W SP G MU WM HW HSP. destruct (GI_blocks _ _ _ _ G) as [BO _].
    eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hk.
    eapply outside_of_Forall; [exact HW|]. intros [lo hi] Hiv; cbn [fst snd] in *.
    destruct Hk as [Hk|Hk]; [lia|]. destruct (in_block_facts _ _ _ BO Hk) as (F1 & F2 & F3 & F4). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma keeps_of_block_write : forall R s (b : cblk) (CL : list cblk) m0 m m' SP,
    GI K R s (b :: CL) m0 -> munch [(cb_addr b, cb_addr b + cb_size b)] m m' -> wmono ssegs m m' -> CEILZ <= SP ->
    agrees_on (client_keeps CL SP) m m'.
  Proof using Type. pin_using tt. ceil_facts.
    intros R s b CL m0 m m' SP G MU WM HSP. destruct (GI_blocks _ _ _ _ G) as [BO BA].
    apply Forall_cons_iff in BO as [Bb BO]. destruct BA as [AP _].
    eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hk. cbn [outside]. split; [|exact I].
    destruct Bb as (K1 & K2 & K3 & K4 & K5 & K6).
    destruct Hk as [Hk|Hk]; [lia|]. unfold in_block in Hk. apply Exists_exists in Hk as (b' & Hb' & Hr).
    pose proof (proj1 (Forall_forall _ _) AP _ Hb') as A1. unfold apart in A1. lia.
  Qed.

  Lemma keeps_trans : forall (CL CL' : list cblk) SP SP' m m0 m',
    agrees_on (client_keeps CL SP) m m0 -> agrees_on (client_keeps CL' SP') m0 m' -> SP' <= SP ->
    (forall a, in_block CL a -> in_block CL' a) ->
    agrees_on (client_keeps CL SP) m m'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
    intros CL CL' SP SP' m m0 m' A1 A2 HS HB. eapply agrees_on_trans; [exact A1|].
    eapply client_keeps_weaken; [exact A2| exact HS| exact HB].
  Qed.
End Facts.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.Exit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB.
Import OSSVerify.libpcap.fuzz_pcap.images.Ubsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section WithCeil.
Context {CEILV : CEIL}.
Section Facts.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr).
  Notation cblk := (@cblock hptr).
  Hypothesis HFL : heap_frame_law K.
  Hypothesis SFL : stdio_fp_law K.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma GI_blocks : forall R s CL m, GI K R s CL m -> Forall (block_ok (utp R)) CL /\ blocks_apart CL.
  Proof using Type. pin_using tt. ceil_facts.
    intros R s CL m (FB & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [BO BA] & _).
    apply Forall_app in BO as [BO _]. apply blocks_apart_app_inv in BA as (BA & _ & _). auto.
  Qed.

  Lemma GI_tls : forall R s CL m, GI K R s CL m -> ps_tls s = utp R - 200 /\ tls_block_ok_u (utp R - 200).
  Proof using Type. pin_using tt. ceil_facts. intros R s CL m (FB & _ & _ & _ & _ & _ & _ & _ & _ & _ & E & T & _). auto. Qed.

  Lemma GI_core : forall R s CL m, GI K R s CL m ->
    CORE_TLS R m /\ PCAP_TLS R m /\ CORE_LIBC R m /\ CORE_MISC m /\ CORE_EXIT (rc_cb R) m /\ CORE_STK R m.
  Proof using Type. pin_using tt. ceil_facts.
    intros R s CL m (FB & _ & _ & _ & A & B & C & D & E & F & _).
    split; [exact A|]. split; [exact B|]. split; [exact C|]. split; [exact D|]. split; [exact E|exact F].
  Qed.

  Lemma GI_spw : forall R s CL m, GI K R s CL m -> 0x7fff80000000 <= usp0 R.
  Proof using Type. pin_using tt. ceil_facts. intros R s CL m (FB & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SPW & _). exact (proj1 SPW). Qed.
  Lemma GI_sp47 : forall R s CL m, GI K R s CL m -> usp0 R <= 2^47.
  Proof using Type. pin_using tt. ceil_facts. intros R s CL m (FB & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SPW & _). exact (proj2 SPW). Qed.
  (* [comment removed for export] *)
  Lemma GI_ceil_lo : forall R s CL m, GI K R s CL m -> CEILZ <= rc_lo R.
  Proof using Type. pin_using tt. ceil_facts. intros R s CL m (FB & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CLO). exact CLO. Qed.

  Lemma in_block_facts : forall u (CL : list cblk) a,
    Forall (block_ok u) CL -> in_block CL a ->
    0 < a /\ a < CEILZ /\ (a < 0x10000 \/ 0x56000 <= a) /\ (a < u - 200 \/ u - 200 + 4096 <= a).
  Proof using Type. pin_using tt. ceil_facts.
    intros u CL a BO Hin. unfold in_block in Hin. apply Exists_exists in Hin as (b & Hb & Hr).
    pose proof (proj1 (Forall_forall _ _) BO b Hb) as (K1 & K2 & K3 & K4 & K5 & K6). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma client_range_bounds : forall R s (CL : list cblk) m A n,
    GI K R s CL m -> (forall a, A <= a < A + n -> in_block CL a) -> 0 < n ->
    0 < A /\ A + n <= CEILZ /\ (A + n <= 0x10000 \/ 0x56000 <= A) /\ (A + n <= utp R - 200 \/ utp R - 200 + 4096 <= A).
  Proof using Type. pin_using tt. ceil_facts.
    intros R s CL m A n G HR Hn. destruct (GI_blocks _ _ _ _ G) as [BO _].
    destruct (in_block_facts _ _ A BO (HR A ltac:(lia))) as (A1 & A2 & A3 & A4).
    destruct (in_block_facts _ _ (A + n - 1) BO (HR (A + n - 1) ltac:(lia))) as (B1 & B2 & B3 & B4).
    split; [lia|]. split; [lia|]. split.
    - destruct (Z_le_gt_dec (A + n) 0x10000); [left; lia|]. destruct (Z_le_gt_dec 0x56000 A); [right; lia|]. exfalso.
      destruct (in_block_facts _ _ (Z.max A 0x10000) BO (HR (Z.max A 0x10000) ltac:(lia))) as (C1 & C2 & C3 & C4). lia.
    - destruct (Z_le_gt_dec (A + n) (utp R - 200)); [left; lia|]. destruct (Z_le_gt_dec (utp R - 200 + 4096) A); [right; lia|]. exfalso.
      destruct (in_block_facts _ _ (Z.max A (utp R - 200)) BO (HR (Z.max A (utp R - 200)) ltac:(lia))) as (C1 & C2 & C3 & C4). lia.
  Qed.

  Lemma GI_harn : forall R s CL m, GI K R s CL m -> exists FB, HARNR (ps_outfile s) FB m.
  Proof using Type. pin_using tt. ceil_facts. intros R s CL m (FB & _ & _ & A & _). exists FB. exact A. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition client_iv (R : rctx) (CL : list cblk) (iv : Z * Z) : Prop :=
    (rc_lo R <= fst iv /\ snd iv <= rc_spmain R) \/ iv_in_block CL iv.

  Lemma outside_of_Forall : forall (P : Z * Z -> Prop) W a,
    Forall P W -> (forall iv, P iv -> ~ (fst iv <= a < snd iv)) -> outside W a.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
    induction W as [|[lo hi] W IH]; intros a HF HP; cbn; [exact I|].
    apply Forall_cons_iff in HF as [H1 H2]. split; [exact (HP _ H1) | apply IH; assumption].
  Qed.

  Lemma GI_client_frame : forall R s CL m m' W,
    GI K R s CL m -> munch W m m' -> wmono usegs m m' ->
    Forall (client_iv R CL) W ->
    GI K R s CL m'.
  Proof using HFL SFL. pin_using (fun (HFL SFL : unit) => tt). ceil_facts.
    intros R s CL m m' W G MU WM HW.
    destruct G as (FB & HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK & SPW).
    pose proof BOK as BOK'. destruct BOK' as [BO BA].
    pose proof (blocks_apart_app_inv _ _ BA) as (BA1 & BA2 & BAX).
    apply Forall_app in BO. destruct BO as [BO1 BO2].
    pose proof TB as TB'. unfold tls_block_ok_u in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    (* [comment removed for export] *)
    assert (OUT : forall a, 0 <= a < 2^64 ->
              (a < rc_lo R \/ (rc_spmain R <= a)) -> ~ in_block CL a -> outside W a).
    { intros a Ha H1 H2. eapply outside_of_Forall; [exact HW|]. intros [lo hi] [Hs|Hb]; [cbn [fst snd] in Hs |- *; lia|]. cbn [fst snd].
      intros Hin. apply H2. unfold iv_in_block in Hb. apply Exists_exists in Hb as (b & HbIn & Hb1 & Hb2). cbn [fst snd] in Hb1, Hb2.
      unfold in_block. apply Exists_exists. exists b. split; [exact HbIn | lia]. }
    assert (NIB : forall a, (0x10000 <= a < 0x56000 \/ CEILZ <= a \/ (utp R - 200 <= a < utp R - 200 + 4096) \/ in_block FB a) -> ~ in_block CL a).
    { intros a Ha Hin. unfold in_block in Hin. apply Exists_exists in Hin as (b & HbIn & Hb).
      pose proof (proj1 (Forall_forall _ _) BO1 b HbIn) as (K1 & K2 & K3 & K4 & K5 & K6).
      destruct Ha as [Ha|[Ha|[Ha|Ha]]]; try lia.
      apply Exists_exists in Ha as (b' & Hb'In & Hb'). pose proof (BAX b b' HbIn Hb'In) as AP. unfold apart in AP. lia. }
    assert (LO : usp0 R - 8388608 >= CEILZ). { pose proof (proj2 SPW) as CLO__. unfold rc_lo in CLO__. lia. }
    unfold rc_spmain in *.
    exists FB. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [exact Etls|split; [exact TB|split; [exact BOK|exact SPW]]]]]]]]]]]].
    - (* [comment removed for export] *) eapply HFL; [exact HH|exact MU|exact WM|].
      apply Forall_forall. intros [lo' hi'] Hiv. unfold heap_client_iv. pose proof (proj1 (Forall_forall _ _) HW _ Hiv) as [Hs|Hb]; cbn [fst snd] in *.
      + left. unfold rc_lo in *. lia.
      + right; left. unfold iv_in_block in *. rewrite Exists_app. left. exact Hb.
    - (* [comment removed for export] *) eapply SFL; [exact HS|]. eapply agrees_on_of_munch; [exact MU|exact WM|].
      intros a Ha Hfp. unfold stdio_fp, stdio_static in Hfp.
      destruct Hfp as [Hst|Hfb].
      + apply OUT; [exact Ha| left; lia | apply NIB; lia].
      + apply Exists_exists in Hfb as (b & HbIn & Hb). pose proof (proj1 (Forall_forall _ _) BO2 b HbIn) as (K1 & K2 & K3 & K4 & K5 & K6).
        apply OUT; [exact Ha| left; lia | apply NIB]. right; right; right. apply Exists_exists. exists b. auto.
    - (* [comment removed for export] *) eapply HARNR_agree; [| |exact HA]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold harn_fp, harn_static in Hp. apply OUT; [exact Ha|left; lia|apply NIB; lia].
    - eapply CORE_TLS_agree; [| |exact CT]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_tls_fp in Hp. apply OUT; [exact Ha|left; lia|apply NIB; lia].
    - eapply PCAP_TLS_agree; [| |exact PT]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold pcap_tls_fp in Hp. apply OUT; [exact Ha|left; lia|apply NIB; lia].
    - eapply CORE_LIBC_agree; [| |exact CLI]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_libc_fp in Hp. apply OUT; [exact Ha|left; lia|apply NIB; lia].
    - eapply CORE_MISC_agree; [| |exact CM]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_misc_fp in Hp. apply OUT; [exact Ha|left; lia|apply NIB; lia].
    - eapply CORE_EXIT_agree; [| |exact CE]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_exit_fp in Hp. apply OUT; [exact Ha|left; lia|apply NIB; lia].
    - eapply CORE_STK_agree; [| |exact CS]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_stk_fp in Hp. apply OUT; [exact Ha|right; lia|apply NIB; lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma GI_initflag : forall R s CL m, GI K R s CL m ->
    (exists ib : byte, rw_cells usegs m 0x34150 [C1 ib]) /\ rw_cells usegs m 0x22d80 [C8 (Z_to_bv 64 0)].
  Proof using Type. pin_using tt. ceil_facts.
    intros R s CL m (FB & _ & _ & (HAi & _ & _) & _ & _ & _ & (_ & _ & _ & _ & CM & _) & _). split; [exact HAi | exact CM].
  Qed.

  (* [comment removed for export] *)
  Hypothesis HCB : heap_cb_law K.
  Hypothesis SCB : stdio_cb_law K.
  Lemma GI_atx_frame : forall R s CL m m' W (b : bool),
    GI K R s CL m -> munch ((0x34150, 0x34155) :: (0x542a0, 0x544c0) :: W) m m' -> wmono usegs m m' ->
    Forall (client_iv R CL) W ->
    ATX b m' ->
    GI K (set_cb R b) s CL m'.
  Proof using HFL SFL HCB SCB. pin_using (fun (HFL SFL HCB SCB : unit) => tt). ceil_facts.
    intros R s CL m m' W b G MU WM HW HATX.
    destruct G as (FB & HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK & SPW).
    pose proof BOK as BOK'. destruct BOK' as [BO BA].
    pose proof (blocks_apart_app_inv _ _ BA) as (BA1 & BA2 & BAX).
    apply Forall_app in BO. destruct BO as [BO1 BO2].
    pose proof TB as TB'. unfold tls_block_ok_u in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    assert (OUT : forall a, 0 <= a < 2^64 -> ~ (0x34150 <= a < 0x34155) -> ~ (0x542a0 <= a < 0x544c0) ->
              (a < rc_lo R \/ (rc_spmain R <= a)) -> ~ in_block CL a -> outside ((0x34150, 0x34155) :: (0x542a0, 0x544c0) :: W) a).
    { intros a Ha Hne1 Hne2 H1 H2. cbn [outside]. split; [lia|]. split; [lia|]. eapply outside_of_Forall; [exact HW|]. intros [lo hi] [Hs|Hb]; [cbn [fst snd] in Hs |- *; lia|]. cbn [fst snd].
      intros Hin. apply H2. unfold iv_in_block in Hb. apply Exists_exists in Hb as (b0 & HbIn & Hb1 & Hb2). cbn [fst snd] in Hb1, Hb2.
      unfold in_block. apply Exists_exists. exists b0. split; [exact HbIn | lia]. }
    assert (NIB : forall a, (0x10000 <= a < 0x56000 \/ CEILZ <= a \/ (utp R - 200 <= a < utp R - 200 + 4096) \/ in_block FB a) -> ~ in_block CL a).
    { intros a Ha Hin. unfold in_block in Hin. apply Exists_exists in Hin as (b0 & HbIn & Hb).
      pose proof (proj1 (Forall_forall _ _) BO1 b0 HbIn) as (K1 & K2 & K3 & K4 & K5 & K6).
      destruct Ha as [Ha|[Ha|[Ha|Ha]]]; try lia.
      apply Exists_exists in Ha as (b' & Hb'In & Hb'). pose proof (BAX b0 b' HbIn Hb'In) as AP. unfold apart in AP. lia. }
    assert (LO : usp0 R - 8388608 >= CEILZ). { pose proof (proj2 SPW) as CLO__. unfold rc_lo in CLO__. lia. }
    unfold rc_spmain in *.
    pose proof HATX as HATX'. destruct HATX' as (reg & pad & f0 & g0 & j1 & j2 & X1 & X2 & X3 & X4).
    exists FB. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [exact Etls|split; [exact TB|split; [exact BOK|exact SPW]]]]]]]]]]]].
    - apply HCB. eapply HFL; [exact HH|exact MU|exact WM|].
      apply Forall_cons; [unfold heap_client_iv; right; right; left; cbn [fst snd]; lia|].
      apply Forall_cons; [unfold heap_client_iv; right; right; left; cbn [fst snd]; lia|].
      apply Forall_forall. intros [lo' hi'] Hiv. unfold heap_client_iv. pose proof (proj1 (Forall_forall _ _) HW _ Hiv) as [Hs|Hb]; cbn [fst snd] in *.
      + left. unfold rc_lo in *. lia.
      + right; left. unfold iv_in_block in *. rewrite Exists_app. left. exact Hb.
    - apply SCB. eapply SFL; [exact HS|]. eapply agrees_on_of_munch; [exact MU|exact WM|].
      intros a Ha Hfp. unfold stdio_fp, stdio_static in Hfp.
      destruct Hfp as [Hst|Hfb].
      + apply OUT; [exact Ha| lia | lia | left; lia | apply NIB; lia].
      + apply Exists_exists in Hfb as (b0 & HbIn & Hb). pose proof (proj1 (Forall_forall _ _) BO2 b0 HbIn) as (K1 & K2 & K3 & K4 & K5 & K6).
        apply OUT; [exact Ha| lia | lia | left; lia | apply NIB]. right; right; right. apply Exists_exists. exists b0. auto.
    - (* [comment removed for export] *)
      destruct HA as (_ & (ej & HAe) & HAo). split.
      { exists (bool8 reg). apply (proj1 (rw_cells_app usegs m' _ [_] [_; _])) in X1 as [X1 _]. exact X1. }
      split.
      + exists ej. eapply agrees_rw_cells; [eapply agrees_on_of_munch; [exact MU|exact WM|intros a Ha Hp; exact (Hp Ha)] | exact HAe |].
        intros a Hp Ha. cbn in Hp. apply OUT; [exact Ha|lia|lia|left; lia|apply NIB; lia].
      + destruct (ps_outfile s) as [q|].
        * destruct HAo as (A & HA1 & HAo). exists A. split; [exact HA1|].
          eapply agrees_rw_cells; [eapply agrees_on_of_munch; [exact MU|exact WM|intros a Ha Hp; exact (Hp Ha)] | exact HAo |].
          intros a Hp Ha; cbn in Hp; apply OUT; [exact Ha|lia|lia|left; lia|apply NIB; lia].
        * eapply agrees_rw_cells; [eapply agrees_on_of_munch; [exact MU|exact WM|intros a Ha Hp; exact (Hp Ha)] | exact HAo |].
          intros a Hp Ha; cbn in Hp; apply OUT; [exact Ha|lia|lia|left; lia|apply NIB; lia].
    - change (CORE_TLS R m'). eapply CORE_TLS_agree; [| |exact CT]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_tls_fp in Hp. apply OUT; [exact Ha|lia|lia|left; lia|apply NIB; lia].
    - change (PCAP_TLS R m'). eapply PCAP_TLS_agree; [| |exact PT]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold pcap_tls_fp in Hp. apply OUT; [exact Ha|lia|lia|left; lia|apply NIB; lia].
    - change (CORE_LIBC R m'). eapply CORE_LIBC_agree; [| |exact CLI]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_libc_fp in Hp. apply OUT; [exact Ha|lia|lia|left; lia|apply NIB; lia].
    - eapply CORE_MISC_agree; [| |exact CM]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_misc_fp in Hp. apply OUT; [exact Ha|lia|lia|left; lia|apply NIB; lia].
    - (* [comment removed for export] *)
      change (CORE_EXIT b m'). destruct CE as (A1 & _ & A3 & A4 & A5 & A6 & A7).
      assert (AGo : agrees_on (fun a => (0x544c0 <= a < 0x544c4) \/ (0x22de8 <= a < 0x22df8) \/ (0x22d18 <= a < 0x22d20)
                                        \/ (0x24148 <= a < 0x24149) \/ (0x22d68 <= a < 0x22d78) \/ (0x23df8 <= a < 0x23e00)) m m').
      { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. apply OUT; [exact Ha|lia|lia|left; lia|apply NIB; lia]. }
      split; [eapply agrees_rw_cells; [exact AGo | exact A1 | intros a Ha; sl_lit_sizes_in Ha; cbn in Ha; lia]|].
      split; [exact HATX|].
      split; [eapply agrees_rw_cells; [exact AGo | exact A3 | intros a Ha; sl_lit_sizes_in Ha; cbn in Ha; lia]|].
      split; [eapply agrees_rw_cells; [exact AGo | exact A4 | intros a Ha; sl_lit_sizes_in Ha; cbn in Ha; lia]|].
      split; [eapply agrees_rw_cells; [exact AGo | exact A5 | intros a Ha; sl_lit_sizes_in Ha; cbn in Ha; lia]|].
      split; [eapply agrees_rw_cells; [exact AGo | exact A6 | intros a Ha; sl_lit_sizes_in Ha; cbn in Ha; lia]|].
      eapply agrees_rw_cells; [exact AGo | exact A7 | intros a Ha; sl_lit_sizes_in Ha; cbn in Ha; lia].
    - change (CORE_STK R m'). eapply CORE_STK_agree; [| |exact CS]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_stk_fp in Hp. apply OUT; [exact Ha|lia|lia|right; lia|apply NIB; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma GI_atx : forall R s CL m, GI K R s CL m -> ATX (rc_cb R) m.
  Proof using Type. pin_using tt. ceil_facts.
    intros R s CL m (FB & _ & _ & _ & _ & _ & _ & _ & (_ & X & _) & _). exact X.
  Qed.

  (* [comment removed for export] *)
  Lemma GI_client_frame_errno : forall R s CL m m' W (e : word),
    GI K R s CL m -> munch ((utp R - 164, utp R - 160) :: W) m m' -> wmono usegs m m' ->
    Forall (client_iv R CL) W ->
    rw_cells usegs m' (utp R + -164) [C4 e] ->
    GI K R s CL m'.
  Proof using HFL SFL. pin_using (fun (HFL SFL : unit) => tt). ceil_facts.
    intros R s CL m m' W e G MU WM HW HE.
    destruct G as (FB & HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK & SPW).
    pose proof BOK as BOK'. destruct BOK' as [BO BA].
    pose proof (blocks_apart_app_inv _ _ BA) as (BA1 & BA2 & BAX).
    apply Forall_app in BO. destruct BO as [BO1 BO2].
    pose proof TB as TB'. unfold tls_block_ok_u in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    assert (OUT : forall a, 0 <= a < 2^64 -> ~ (utp R - 164 <= a < utp R - 160) ->
              (a < rc_lo R \/ (rc_spmain R <= a)) -> ~ in_block CL a -> outside ((utp R - 164, utp R - 160) :: W) a).
    { intros a Ha Hne H1 H2. cbn [outside]. split; [lia|]. eapply outside_of_Forall; [exact HW|]. intros [lo hi] [Hs|Hb]; [cbn [fst snd] in Hs |- *; lia|]. cbn [fst snd].
      intros Hin. apply H2. unfold iv_in_block in Hb. apply Exists_exists in Hb as (b & HbIn & Hb1 & Hb2). cbn [fst snd] in Hb1, Hb2.
      unfold in_block. apply Exists_exists. exists b. split; [exact HbIn | lia]. }
    assert (NIB : forall a, (0x10000 <= a < 0x56000 \/ CEILZ <= a \/ (utp R - 200 <= a < utp R - 200 + 4096) \/ in_block FB a) -> ~ in_block CL a).
    { intros a Ha Hin. unfold in_block in Hin. apply Exists_exists in Hin as (b & HbIn & Hb).
      pose proof (proj1 (Forall_forall _ _) BO1 b HbIn) as (K1 & K2 & K3 & K4 & K5 & K6).
      destruct Ha as [Ha|[Ha|[Ha|Ha]]]; try lia.
      apply Exists_exists in Ha as (b' & Hb'In & Hb'). pose proof (BAX b b' HbIn Hb'In) as AP. unfold apart in AP. lia. }
    assert (LO : usp0 R - 8388608 >= CEILZ). { pose proof (proj2 SPW) as CLO__. unfold rc_lo in CLO__. lia. }
    unfold rc_spmain in *.
    exists FB. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [exact Etls|split; [exact TB|split; [exact BOK|exact SPW]]]]]]]]]]]].
    - eapply HFL; [exact HH|exact MU|exact WM|].
      apply Forall_cons; [unfold heap_client_iv; right; right; right; cbn [fst snd]; lia|].
      apply Forall_forall. intros [lo' hi'] Hiv. unfold heap_client_iv. pose proof (proj1 (Forall_forall _ _) HW _ Hiv) as [Hs|Hb]; cbn [fst snd] in *.
      + left. unfold rc_lo in *. lia.
      + right; left. unfold iv_in_block in *. rewrite Exists_app. left. exact Hb.
    - eapply SFL; [exact HS|]. eapply agrees_on_of_munch; [exact MU|exact WM|].
      intros a Ha Hfp. unfold stdio_fp, stdio_static in Hfp.
      destruct Hfp as [Hst|Hfb].
      + apply OUT; [exact Ha| lia | left; lia | apply NIB; lia].
      + apply Exists_exists in Hfb as (b & HbIn & Hb). pose proof (proj1 (Forall_forall _ _) BO2 b HbIn) as (K1 & K2 & K3 & K4 & K5 & K6).
        apply OUT; [exact Ha| lia | left; lia | apply NIB]. right; right; right. apply Exists_exists. exists b. auto.
    - eapply HARNR_agree; [| |exact HA]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold harn_fp, harn_static in Hp. apply OUT; [exact Ha|lia|left; lia|apply NIB; lia].
    - (* [comment removed for export] *)
      unfold CORE_TLS in CT. let z := fresh "sblz" in let x := fresh "sbl" in pose (z := repeat (Z_to_bv 8 0) 3616); change (repeat (Z_to_bv 8 0) 3616) with z in CT; pose (x := 3616%nat); change 3616%nat with x in CT; destruct CT as (t & e0 & T1 & T2 & T3 & T4 & T5 & T6 & Ht); subst z x. exists t, e.
      assert (AGo : agrees_on (fun a => outside ((utp R - 164, utp R - 160) :: W) a) m m').
      { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact Hp. }
      Ltac trt AGo OUT NIB T := eapply agrees_rw_cells; [exact AGo | exact T | intros a Ha; sl_lit_sizes_in Ha; cbn -[Z.add Z.mul Z.of_nat] in Ha; apply OUT; [lia|lia|left; lia|apply NIB; lia]].
      split; [trt AGo OUT NIB T1|]. split; [exact HE|]. split; [trt AGo OUT NIB T3|]. split; [trt AGo OUT NIB T4|]. split; [trt AGo OUT NIB T5|]. split; [trt AGo OUT NIB T6| exact Ht].
    - eapply PCAP_TLS_agree; [| |exact PT]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold pcap_tls_fp in Hp. apply OUT; [exact Ha|lia|left; lia|apply NIB; lia].
    - eapply CORE_LIBC_agree; [| |exact CLI]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_libc_fp in Hp. apply OUT; [exact Ha|lia|left; lia|apply NIB; lia].
    - eapply CORE_MISC_agree; [| |exact CM]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_misc_fp in Hp. apply OUT; [exact Ha|lia|left; lia|apply NIB; lia].
    - eapply CORE_EXIT_agree; [| |exact CE]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_exit_fp in Hp. apply OUT; [exact Ha|lia|left; lia|apply NIB; lia].
    - eapply CORE_STK_agree; [| |exact CS]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_stk_fp in Hp. apply OUT; [exact Ha|lia|right; lia|apply NIB; lia].
  Qed.

  (* [comment removed for export] *)
  Definition rs_iv (iv : Z * Z) : Prop := 0x24149 <= fst iv /\ snd iv <= 0x34149.

  Lemma GI_client_frame_errno_rs : forall R s CL m m' W (e : word),
    GI K R s CL m -> munch ((utp R - 164, utp R - 160) :: W) m m' -> wmono usegs m m' ->
    Forall (fun iv => client_iv R CL iv \/ rs_iv iv) W ->
    rw_cells usegs m' (utp R + -164) [C4 e] ->
    GI K R s CL m'.
  Proof using HFL SFL. pin_using (fun (HFL SFL : unit) => tt). ceil_facts.
    intros R s CL m m' W e G MU WM HW HE.
    destruct G as (FB & HH & HS & HA & CT & PT & CLI & CM & CE & CS & Etls & TB & BOK & SPW).
    pose proof BOK as BOK'. destruct BOK' as [BO BA].
    pose proof (blocks_apart_app_inv _ _ BA) as (BA1 & BA2 & BAX).
    apply Forall_app in BO. destruct BO as [BO1 BO2].
    pose proof TB as TB'. unfold tls_block_ok_u in TB'. destruct TB' as (TBA & TB0 & TBC & TBI).
    unfold rs_iv in HW.
    assert (OUT : forall a, 0 <= a < 2^64 -> ~ (utp R - 164 <= a < utp R - 160) -> ~ (0x24149 <= a < 0x34149) ->
              (a < rc_lo R \/ (rc_spmain R <= a)) -> ~ in_block CL a -> outside ((utp R - 164, utp R - 160) :: W) a).
    { intros a Ha Hne Hrs H1 H2. cbn [outside]. split; [lia|]. eapply outside_of_Forall; [exact HW|]. intros [lo hi] [[Hs|Hb]|Hr]; [cbn [fst snd] in Hs |- *; lia| |cbn [fst snd] in Hr |- *; lia]. cbn [fst snd].
      intros Hin. apply H2. unfold iv_in_block in Hb. apply Exists_exists in Hb as (b & HbIn & Hb1 & Hb2). cbn [fst snd] in Hb1, Hb2.
      unfold in_block. apply Exists_exists. exists b. split; [exact HbIn | lia]. }
    assert (NIB : forall a, (0x10000 <= a < 0x56000 \/ CEILZ <= a \/ (utp R - 200 <= a < utp R - 200 + 4096) \/ in_block FB a) -> ~ in_block CL a).
    { intros a Ha Hin. unfold in_block in Hin. apply Exists_exists in Hin as (b & HbIn & Hb).
      pose proof (proj1 (Forall_forall _ _) BO1 b HbIn) as (K1 & K2 & K3 & K4 & K5 & K6).
      destruct Ha as [Ha|[Ha|[Ha|Ha]]]; try lia.
      apply Exists_exists in Ha as (b' & Hb'In & Hb'). pose proof (BAX b b' HbIn Hb'In) as AP. unfold apart in AP. lia. }
    assert (LO : usp0 R - 8388608 >= CEILZ). { pose proof (proj2 SPW) as CLO__. unfold rc_lo in CLO__. lia. }
    unfold rc_spmain in *.
    exists FB. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [exact Etls|split; [exact TB|split; [exact BOK|exact SPW]]]]]]]]]]]].
    - eapply HFL; [exact HH|exact MU|exact WM|].
      apply Forall_cons; [unfold heap_client_iv; right; right; right; cbn [fst snd]; lia|].
      apply Forall_forall. intros [lo' hi'] Hiv. unfold heap_client_iv. pose proof (proj1 (Forall_forall _ _) HW _ Hiv) as [[Hs|Hb]|Hr]; cbn [fst snd] in *.
      + left. unfold rc_lo in *. lia.
      + right; left. unfold iv_in_block in *. rewrite Exists_app. left. exact Hb.
      + right; right; left. lia.
    - eapply SFL; [exact HS|]. eapply agrees_on_of_munch; [exact MU|exact WM|].
      intros a Ha Hfp. unfold stdio_fp, stdio_static in Hfp.
      destruct Hfp as [Hst|Hfb].
      + apply OUT; [exact Ha| lia | lia | left; lia | apply NIB; lia].
      + apply Exists_exists in Hfb as (b & HbIn & Hb). pose proof (proj1 (Forall_forall _ _) BO2 b HbIn) as (K1 & K2 & K3 & K4 & K5 & K6).
        apply OUT; [exact Ha| lia | lia | left; lia | apply NIB]. right; right; right. apply Exists_exists. exists b. auto.
    - eapply HARNR_agree; [| |exact HA]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold harn_fp, harn_static in Hp. apply OUT; [exact Ha|lia|lia|left; lia|apply NIB; lia].
    - (* [comment removed for export] *)
      unfold CORE_TLS in CT. let z := fresh "sblz" in let x := fresh "sbl" in pose (z := repeat (Z_to_bv 8 0) 3616); change (repeat (Z_to_bv 8 0) 3616) with z in CT; pose (x := 3616%nat); change 3616%nat with x in CT; destruct CT as (t & e0 & T1 & T2 & T3 & T4 & T5 & T6 & Ht); subst z x. exists t, e.
      assert (AGo : agrees_on (fun a => outside ((utp R - 164, utp R - 160) :: W) a) m m').
      { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact Hp. }
      Ltac trt_rs AGo OUT NIB T := eapply agrees_rw_cells; [exact AGo | exact T | intros a Ha; sl_lit_sizes_in Ha; cbn -[Z.add Z.mul Z.of_nat] in Ha; apply OUT; [lia|lia|lia|left; lia|apply NIB; lia]].
      split; [trt_rs AGo OUT NIB T1|]. split; [exact HE|]. split; [trt_rs AGo OUT NIB T3|]. split; [trt_rs AGo OUT NIB T4|]. split; [trt_rs AGo OUT NIB T5|]. split; [trt_rs AGo OUT NIB T6| exact Ht].
    - eapply PCAP_TLS_agree; [| |exact PT]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold pcap_tls_fp in Hp. apply OUT; [exact Ha|lia|lia|left; lia|apply NIB; lia].
    - eapply CORE_LIBC_agree; [| |exact CLI]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_libc_fp in Hp. apply OUT; [exact Ha|lia|lia|left; lia|apply NIB; lia].
    - eapply CORE_MISC_agree; [| |exact CM]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_misc_fp in Hp. apply OUT; [exact Ha|lia|lia|left; lia|apply NIB; lia].
    - eapply CORE_EXIT_agree; [| |exact CE]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_exit_fp in Hp. apply OUT; [exact Ha|lia|lia|left; lia|apply NIB; lia].
    - eapply CORE_STK_agree; [| |exact CS]. { eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hp. exact (Hp Ha). }
      intros a Hp Ha. unfold core_stk_fp in Hp. apply OUT; [exact Ha|lia|lia|right; lia|apply NIB; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma keeps_rw_cells_stack : forall (CL : list cblk) SP m m' A cs,
    agrees_on (client_keeps CL SP) m m' -> rw_cells usegs m A cs -> SP <= A -> rw_cells usegs m' A cs.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros CL SP m m' A cs AG HC HA. eapply agrees_rw_cells; [exact AG|exact HC|]. intros a Ha. left. lia. Qed.
  Lemma keeps_bytes_at_stack : forall (CL : list cblk) SP m m' A bs,
    agrees_on (client_keeps CL SP) m m' -> bytes_at usegs m A bs -> SP <= A -> bytes_at usegs m' A bs.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros CL SP m m' A bs AG HC HA. eapply agrees_bytes_at; [exact AG|exact HC|]. intros a Ha. left. lia. Qed.
  Lemma keeps_rw_cells_block : forall (CL : list cblk) SP m m' A cs,
    agrees_on (client_keeps CL SP) m m' -> rw_cells usegs m A cs ->
    (forall a, A <= a < A + Z.of_nat (cells_size cs) -> in_block CL a) -> rw_cells usegs m' A cs.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros CL SP m m' A cs AG HC HA. eapply agrees_rw_cells; [exact AG|exact HC|]. intros a Ha. right. apply HA. exact Ha. Qed.
  Lemma keeps_bytes_at_block : forall (CL : list cblk) SP m m' A bs,
    agrees_on (client_keeps CL SP) m m' -> bytes_at usegs m A bs ->
    (forall a, A <= a < A + Z.of_nat (length bs) -> in_block CL a) -> bytes_at usegs m' A bs.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros CL SP m m' A bs AG HC HA. eapply agrees_bytes_at; [exact AG|exact HC|]. intros a Ha. right. apply HA. exact Ha. Qed.

  Lemma client_keeps_weaken : forall (CL CL' : list cblk) SP SP' m m',
    agrees_on (client_keeps CL SP) m m' -> SP <= SP' -> (forall a, in_block CL' a -> in_block CL a) ->
    agrees_on (client_keeps CL' SP') m m'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros CL CL' SP SP' m m' AG HS HB. eapply agrees_on_weaken; [exact AG|]. intros a [Ha|Ha]; [left; lia | right; apply HB; exact Ha]. Qed.

  Lemma in_block_cons : forall (b : cblk) CL a, in_block CL a -> in_block (b :: CL) a.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. intros b CL a Hin. unfold in_block in *. apply Exists_cons_tl. exact Hin. Qed.

  (* [comment removed for export] *)
  Lemma keeps_of_munch : forall R s (CL : list cblk) m m0 W SP,
    GI K R s CL m -> munch W m m0 -> wmono usegs m m0 ->
    Forall (fun iv => (CEILZ <= fst iv /\ snd iv <= SP) \/ (0x10000 <= fst iv /\ snd iv <= 0x56000)) W ->
    CEILZ <= SP ->
    agrees_on (client_keeps CL SP) m m0.
  Proof using Type. pin_using tt. ceil_facts.
    intros R s CL m m0 W SP G MU WM HW HSP. destruct (GI_blocks _ _ _ _ G) as [BO _].
    eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hk.
    eapply outside_of_Forall; [exact HW|]. intros [lo hi] Hiv; cbn [fst snd] in *.
    destruct Hk as [Hk|Hk]; [lia|]. destruct (in_block_facts _ _ _ BO Hk) as (F1 & F2 & F3 & F4). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma keeps_of_block_write : forall R s (b : cblk) (CL : list cblk) m0 m m' SP,
    GI K R s (b :: CL) m0 -> munch [(cb_addr b, cb_addr b + cb_size b)] m m' -> wmono usegs m m' -> CEILZ <= SP ->
    agrees_on (client_keeps CL SP) m m'.
  Proof using Type. pin_using tt. ceil_facts.
    intros R s b CL m0 m m' SP G MU WM HSP. destruct (GI_blocks _ _ _ _ G) as [BO BA].
    apply Forall_cons_iff in BO as [Bb BO]. destruct BA as [AP _].
    eapply agrees_on_of_munch; [exact MU|exact WM|]. intros a Ha Hk. cbn [outside]. split; [|exact I].
    destruct Bb as (K1 & K2 & K3 & K4 & K5 & K6).
    destruct Hk as [Hk|Hk]; [lia|]. unfold in_block in Hk. apply Exists_exists in Hk as (b' & Hb' & Hr).
    pose proof (proj1 (Forall_forall _ _) AP _ Hb') as A1. unfold apart in A1. lia.
  Qed.

  Lemma keeps_trans : forall (CL CL' : list cblk) SP SP' m m0 m',
    agrees_on (client_keeps CL SP) m m0 -> agrees_on (client_keeps CL' SP') m0 m' -> SP' <= SP ->
    (forall a, in_block CL a -> in_block CL' a) ->
    agrees_on (client_keeps CL SP) m m'.
  Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts.
    intros CL CL' SP SP' m m0 m' A1 A2 HS HB. eapply agrees_on_trans; [exact A1|].
    eapply client_keeps_weaken; [exact A2| exact HS| exact HB].
  Qed.
End Facts.

End WithCeil.
End TwB.
End GIFacts.

(* [comment removed for export] *)
Module Ifaces.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prog. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Import GI.
From OSSVerify.libpcap.fuzz_pcap.images Require Import Plain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Definition MALLOC_ENTRY : Z := 0x188cc.
Definition FREE_ENTRY : Z := 0x1878c.
Definition FPRINTF_ENTRY : Z := 0x1b584.
Definition FWRITE_ENTRY : Z := 0x1b85c.
Definition VPRINTF_ENTRY : Z := 0x20550.
Definition FUZZ_ONE_ENTRY : Z := 0x13fb0.      (* [comment removed for export] *)
Definition TARGET_RUN_ENTRY : Z := 0x13de0.
Definition STDERR_FILE : Z := 0x23660.         (* [comment removed for export] *)
Definition FMT_D : Z := 0x10508.               (* [comment removed for export] *)
Definition FMT_USAGE : Z := 0x106d4.           (* [comment removed for export] *)
Definition FMT_CANNOT_OPEN : Z := 0x10c1b.     (* [comment removed for export] *)
Definition FMT_READ_ERROR : Z := 0x10c30.      (* [comment removed for export] *)
Definition FMT_TOO_BIG : Z := 0x1093d.         (* [comment removed for export] *)
Definition MSG_OOM : Z := 0x104f4.             (* [comment removed for export] *)
Definition MSG_SHORT_HDR : Z := 0x10e00.       (* [comment removed for export] *)
Definition MSG_CFG_OVERRUN : Z := 0x106e5.     (* [comment removed for export] *)

Definition MALLOC_STACK : Z := 0x10000.
Definition FREE_STACK : Z := 0x10000.
Definition STDIO_STACK : Z := 0x10000.         (* [comment removed for export] *)
Definition FUZZ_STACK : Z := 0x100000.         (* [comment removed for export] *)
Definition TARGET_RUN_STACK : Z := FUZZ_STACK + 80 + STDIO_STACK.   (* [comment removed for export] *)

Section Ifaces.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr).
  Notation cblk := (@cblock hptr).
  Notation PS := (PState H hptr).

  (* [comment removed for export] *)
  Definition std_pre (sp tp : word) (R : rctx) (s : PS) (CL : list cblk) (lo budget : Z) (m : mem) : Prop :=
    GI K R s CL m /\ stk ssegs m lo (bv_unsigned sp) /\ rc_lo R <= lo /\ lo + budget <= bv_unsigned sp
    /\ bv_unsigned sp <= rc_spmain R /\ mem_inv ssegs m /\ tp = rc_tp R /\ bv_unsigned sp mod 16 = 0.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition malloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (R : rctx) (CL : list cblk) (lo n : Z) (m : mem) : option hptr -> PS -> machine_state -> Prop :=
    fun r s' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom ssegs)
      /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp)
      /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
      /\ match r with
         | None => a0 = Z_to_bv 64 0 /\ GI K R s' CL m'
         | Some q => exists A junk, a0 = Z_to_bv 64 A /\ GI K R s' ((q, A, n) :: CL) m'
                       /\ rw_cells ssegs m' A [CB (Z.to_nat n) junk] /\ block_ok (utp R) (q, A, n)
                       /\ ho_addr HO (ps_heap s') q = A
         end.

  Definition malloc_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL : list cblk) (lo n : Z),
      std_pre sp tp R s CL lo MALLOC_STACK m ->
      a0 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
      implM ssegs (pmalloc HO n) s
        (malloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo n m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 MALLOC_ENTRY) fc None m (seg_rom ssegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition free_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (R : rctx) (CL' : list cblk) (lo : Z) (m : mem) : unit -> PS -> machine_state -> Prop :=
    fun _ s' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom ssegs)
      /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp)
      /\ agrees_on (client_keeps CL' (bv_unsigned sp)) m m'
      /\ GI K R s' CL' m'.

  Definition free_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (C1 C2 : list cblk) (q : hptr) (A n lo : Z),
      std_pre sp tp R s (C1 ++ (q, A, n) :: C2) lo FREE_STACK m ->
      a0 = Z_to_bv 64 A ->
      implM ssegs (pfree HO q) s
        (free_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R (C1 ++ C2) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FREE_ENTRY) fc None m (seg_rom ssegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition out_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (R : rctx) (CL : list cblk) (lo : Z) (m : mem) : unit -> PS -> machine_state -> Prop :=
    fun _ s' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom ssegs)
      /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp)
      /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
      /\ GI K R s' CL m'.

  (* [comment removed for export] *)
  Definition eprintf_s_stmt (FMT : Z) (mk : list Z -> list (list Z)) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL : list cblk) (lo P : Z) (str slack : list byte),
      std_pre sp tp R s CL lo STDIO_STACK m ->
      a0 = Z_to_bv 64 STDERR_FILE -> a1 = Z_to_bv 64 FMT -> a2 = Z_to_bv 64 P ->
      bytes_at ssegs m P (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str -> Z.of_nat (length str) < 2^24 ->
      (- (P + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->   (* [comment removed for export] *)
      (forall a, P <= a < P + Z.of_nat (length str) + 1 -> client_keeps CL (bv_unsigned sp) a) ->
      implM ssegs (@eprintf PS hptr ps_libc set_libc (mk (map bv_unsigned str))) s
        (out_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FPRINTF_ENTRY) fc None m (seg_rom ssegs)).

  (* [comment removed for export] *)
  Definition eprintf_i_stmt (FMT v : Z) (ps : list (list Z)) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL : list cblk) (lo : Z),
      std_pre sp tp R s CL lo STDIO_STACK m ->
      a0 = Z_to_bv 64 STDERR_FILE -> a1 = Z_to_bv 64 FMT -> a2 = Z_to_bv 64 v ->
      implM ssegs (@eprintf PS hptr ps_libc set_libc ps) s
        (out_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FPRINTF_ENTRY) fc None m (seg_rom ssegs)).

  (* [comment removed for export] *)
  Definition efwrite_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL : list cblk) (lo MSG : Z) (bs : list byte),
      std_pre sp tp R s CL lo STDIO_STACK m ->
      a0 = Z_to_bv 64 MSG -> a1 = Z_to_bv 64 (Z.of_nat (length bs)) -> a2 = Z_to_bv 64 1 -> a3 = Z_to_bv 64 STDERR_FILE ->
      bytes_at ssegs m MSG bs -> (0x10000 <= MSG /\ MSG + Z.of_nat (length bs) <= 0x13000) (* [comment removed for export] *) -> (1 <= length bs)%nat ->
      implM ssegs (@efwrite PS hptr ps_libc set_libc (map bv_unsigned bs)) s
        (out_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FWRITE_ENTRY) fc None m (seg_rom ssegs)).

  (* [comment removed for export] *)
  Definition vprintf_d_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL : list cblk) (lo AP v : Z) (rest : list byte),
      std_pre sp tp R s CL lo STDIO_STACK m ->
      a0 = Z_to_bv 64 FMT_D -> a1 = Z_to_bv 64 AP -> -2^31 <= v < 2^31 ->
      rw_cells ssegs m AP [C8 (Z_to_bv 64 v); CB 48 rest] -> bv_unsigned sp <= AP -> AP + 56 <= rc_spmain R ->
      implM ssegs (@printf PS hptr ps_libc set_libc (pieces_emit_d v)) s
        (out_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 VPRINTF_ENTRY) fc None m (seg_rom ssegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition fuzz_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (R : rctx) (CL : list cblk) (lo : Z) (m : mem) : Z -> PS -> machine_state -> Prop :=
    fun r s' ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom ssegs)
      /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp)
      /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
      /\ GI K R s' CL m' /\ r = 0.

  (* [comment removed for export] *)
  Definition fuzz_one_stmt (sites_of : Z -> stack_site -> Z) (stk : stack_site -> Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL : list cblk) (lo D : Z) (data : list byte),
      std_pre sp tp R s CL lo FUZZ_STACK m -> stk = sites_of (bv_unsigned sp) ->
      a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 (Z.of_nat (length data)) ->
      bytes_at ssegs m D data -> (forall a, D <= a < D + Z.of_nat (length data) -> in_block CL a) ->
      Z.of_nat (length data) < 2^26 ->
      implM ssegs (harness_call HO fo_nop stk (map bv_unsigned data)) s
        (fuzz_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FUZZ_ONE_ENTRY) fc None m (seg_rom ssegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition target_run_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (R : rctx) (CL : list cblk) (lo : Z) (m : mem) : Z -> PS -> machine_state -> Prop :=
    fun r s' ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom ssegs)
      /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp)
      /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
      /\ GI K R s' CL m' /\ 0 <= r <= 2.

  Definition target_run_stmt (sites_of : Z -> stack_site -> Z) (stk : stack_site -> Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL : list cblk) (lo A L : Z) (content : list byte),
      std_pre sp tp R s CL lo TARGET_RUN_STACK m -> rc_cb R = false -> stk = sites_of (bv_unsigned sp + -80) ->
      bytes_at ssegs m A content -> 0 <= L -> 6 + L <= Z.of_nat (length content) -> Z.of_nat (length content) <= 2^26 ->
      (forall a, A <= a < A + Z.of_nat (length content) -> in_block CL a) ->
      a0 = Z_to_bv 64 (A + 2) -> a1 = Z_to_bv 64 L -> a2 = Z_to_bv 64 (A + 6 + L) -> a3 = Z_to_bv 64 (Z.of_nat (length content) - 6 - L) ->
      implM ssegs (run HO fo_nop stk (firstn (Z.to_nat L) (skipn 2 (map bv_unsigned content)))
                               (skipn (Z.to_nat (6 + L)) (map bv_unsigned content))) s
        (target_run_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 TARGET_RUN_ENTRY) fc None m (seg_rom ssegs)).
End Ifaces.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.libpcap.fuzz_pcap.images Require Ubsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.GI.TwB.
Import OSSVerify.libpcap.fuzz_pcap.images.Ubsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL}.
Definition MALLOC_ENTRY : Z := 0x1908c.
Definition FREE_ENTRY : Z := 0x18f4c.
Definition FPRINTF_ENTRY : Z := 0x1bd44.
Definition FWRITE_ENTRY : Z := 0x1c01c.
Definition VPRINTF_ENTRY : Z := 0x20d10.
Definition FUZZ_ONE_ENTRY : Z := 0x14024.      (* [comment removed for export] *)
Definition TARGET_RUN_ENTRY : Z := 0x13e54.
Definition STDERR_FILE : Z := 0x23e20.         (* [comment removed for export] *)
Definition FMT_D : Z := 0x10508.               (* [comment removed for export] *)
Definition FMT_USAGE : Z := 0x106d4.           (* [comment removed for export] *)
Definition FMT_CANNOT_OPEN : Z := 0x10c1b.     (* [comment removed for export] *)
Definition FMT_READ_ERROR : Z := 0x10c30.      (* [comment removed for export] *)
Definition FMT_TOO_BIG : Z := 0x1093d.         (* [comment removed for export] *)
Definition MSG_OOM : Z := 0x104f4.             (* [comment removed for export] *)
Definition MSG_SHORT_HDR : Z := 0x10e00.       (* [comment removed for export] *)
Definition MSG_CFG_OVERRUN : Z := 0x106e5.     (* [comment removed for export] *)

Definition MALLOC_STACK : Z := 0x10000.
Definition FREE_STACK : Z := 0x10000.
Definition STDIO_STACK : Z := 0x10000.         (* [comment removed for export] *)
Definition FUZZ_STACK : Z := 0x100000.         (* [comment removed for export] *)
Definition TARGET_RUN_STACK : Z := FUZZ_STACK + 80 + STDIO_STACK.   (* [comment removed for export] *)

Section Ifaces.
  Context {H hptr : Type} (HO : HeapOps H hptr) (K : modkit H hptr).
  Notation cblk := (@cblock hptr).
  Notation PS := (PState H hptr).

  (* [comment removed for export] *)
  Definition std_pre (sp tp : word) (R : rctx) (s : PS) (CL : list cblk) (lo budget : Z) (m : mem) : Prop :=
    GI K R s CL m /\ stk usegs m lo (bv_unsigned sp) /\ rc_lo R <= lo /\ lo + budget <= bv_unsigned sp
    /\ bv_unsigned sp <= rc_spmain R /\ mem_inv usegs m /\ tp = rc_tp R /\ bv_unsigned sp mod 16 = 0.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition malloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (R : rctx) (CL : list cblk) (lo n : Z) (m : mem) : option hptr -> PS -> machine_state -> Prop :=
    fun r s' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
      /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
      /\ match r with
         | None => a0 = Z_to_bv 64 0 /\ GI K R s' CL m'
         | Some q => exists A junk, a0 = Z_to_bv 64 A /\ GI K R s' ((q, A, n) :: CL) m'
                       /\ rw_cells usegs m' A [CB (Z.to_nat n) junk] /\ block_ok (utp R) (q, A, n)
                       /\ ho_addr HO (ps_heap s') q = A
         end.

  Definition malloc_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL : list cblk) (lo n : Z),
      std_pre sp tp R s CL lo MALLOC_STACK m ->
      a0 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
      implM usegs (pmalloc HO n) s
        (malloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo n m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 MALLOC_ENTRY) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition free_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (R : rctx) (CL' : list cblk) (lo : Z) (m : mem) : unit -> PS -> machine_state -> Prop :=
    fun _ s' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
      /\ agrees_on (client_keeps CL' (bv_unsigned sp)) m m'
      /\ GI K R s' CL' m'.

  Definition free_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (C1 C2 : list cblk) (q : hptr) (A n lo : Z),
      std_pre sp tp R s (C1 ++ (q, A, n) :: C2) lo FREE_STACK m ->
      a0 = Z_to_bv 64 A ->
      implM usegs (pfree HO q) s
        (free_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R (C1 ++ C2) lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FREE_ENTRY) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition out_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (R : rctx) (CL : list cblk) (lo : Z) (m : mem) : unit -> PS -> machine_state -> Prop :=
    fun _ s' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
      /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
      /\ GI K R s' CL m'.

  (* [comment removed for export] *)
  Definition eprintf_s_stmt (FMT : Z) (mk : list Z -> list (list Z)) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL : list cblk) (lo P : Z) (str slack : list byte),
      std_pre sp tp R s CL lo STDIO_STACK m ->
      a0 = Z_to_bv 64 STDERR_FILE -> a1 = Z_to_bv 64 FMT -> a2 = Z_to_bv 64 P ->
      bytes_at usegs m P (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str -> Z.of_nat (length str) < 2^24 ->
      (- (P + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->   (* [comment removed for export] *)
      (forall a, P <= a < P + Z.of_nat (length str) + 1 -> client_keeps CL (bv_unsigned sp) a) ->
      implM usegs (@eprintf PS hptr ps_libc set_libc (mk (map bv_unsigned str))) s
        (out_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FPRINTF_ENTRY) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition eprintf_i_stmt (FMT v : Z) (ps : list (list Z)) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL : list cblk) (lo : Z),
      std_pre sp tp R s CL lo STDIO_STACK m ->
      a0 = Z_to_bv 64 STDERR_FILE -> a1 = Z_to_bv 64 FMT -> a2 = Z_to_bv 64 v ->
      implM usegs (@eprintf PS hptr ps_libc set_libc ps) s
        (out_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FPRINTF_ENTRY) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition efwrite_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL : list cblk) (lo MSG : Z) (bs : list byte),
      std_pre sp tp R s CL lo STDIO_STACK m ->
      a0 = Z_to_bv 64 MSG -> a1 = Z_to_bv 64 (Z.of_nat (length bs)) -> a2 = Z_to_bv 64 1 -> a3 = Z_to_bv 64 STDERR_FILE ->
      bytes_at usegs m MSG bs -> (0x10000 <= MSG /\ MSG + Z.of_nat (length bs) <= 0x13000) (* [comment removed for export] *) -> (1 <= length bs)%nat ->
      implM usegs (@efwrite PS hptr ps_libc set_libc (map bv_unsigned bs)) s
        (out_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FWRITE_ENTRY) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition vprintf_d_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL : list cblk) (lo AP v : Z) (rest : list byte),
      std_pre sp tp R s CL lo STDIO_STACK m ->
      a0 = Z_to_bv 64 FMT_D -> a1 = Z_to_bv 64 AP -> -2^31 <= v < 2^31 ->
      rw_cells usegs m AP [C8 (Z_to_bv 64 v); CB 48 rest] -> bv_unsigned sp <= AP -> AP + 56 <= rc_spmain R ->
      implM usegs (@printf PS hptr ps_libc set_libc (pieces_emit_d v)) s
        (out_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 VPRINTF_ENTRY) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition fuzz_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (R : rctx) (CL : list cblk) (lo : Z) (m : mem) : Z -> PS -> machine_state -> Prop :=
    fun r s' ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
      /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
      /\ GI K R s' CL m' /\ r = 0.

  (* [comment removed for export] *)
  Definition fuzz_one_stmt (sites_of : Z -> stack_site -> Z) (stk : stack_site -> Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL : list cblk) (lo D : Z) (data : list byte),
      std_pre sp tp R s CL lo FUZZ_STACK m -> stk = sites_of (bv_unsigned sp) ->
      a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 (Z.of_nat (length data)) ->
      bytes_at usegs m D data -> (forall a, D <= a < D + Z.of_nat (length data) -> in_block CL a) ->
      Z.of_nat (length data) < 2^26 ->
      implM usegs (harness_call HO fo_nop stk (map bv_unsigned data)) s
        (fuzz_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FUZZ_ONE_ENTRY) fc None m (seg_rom usegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition target_run_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (R : rctx) (CL : list cblk) (lo : Z) (m : mem) : Z -> PS -> machine_state -> Prop :=
    fun r s' ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
      /\ agrees_on (client_keeps CL (bv_unsigned sp)) m m'
      /\ GI K R s' CL m' /\ 0 <= r <= 2.

  Definition target_run_stmt (sites_of : Z -> stack_site -> Z) (stk : stack_site -> Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (R : rctx) (s : PS) (CL : list cblk) (lo A L : Z) (content : list byte),
      std_pre sp tp R s CL lo TARGET_RUN_STACK m -> rc_cb R = false -> stk = sites_of (bv_unsigned sp + -80) ->
      bytes_at usegs m A content -> 0 <= L -> 6 + L <= Z.of_nat (length content) -> Z.of_nat (length content) <= 2^26 ->
      (forall a, A <= a < A + Z.of_nat (length content) -> in_block CL a) ->
      a0 = Z_to_bv 64 (A + 2) -> a1 = Z_to_bv 64 L -> a2 = Z_to_bv 64 (A + 6 + L) -> a3 = Z_to_bv 64 (Z.of_nat (length content) - 6 - L) ->
      implM usegs (run HO fo_nop stk (firstn (Z.to_nat L) (skipn 2 (map bv_unsigned content)))
                               (skipn (Z.to_nat (6 + L)) (map bv_unsigned content))) s
        (target_run_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R CL lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 TARGET_RUN_ENTRY) fc None m (seg_rom usegs)).
End Ifaces.

End WithCeil.
End TwB.
End Ifaces.
