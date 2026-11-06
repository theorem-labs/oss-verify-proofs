(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require MmapSim AllocSim. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanAcct__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.MmapSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.AsanAcct OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require Import DriverKnow EntryGlue.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mrestrict_none : forall M, mrestrict (fun _ => false) M = M.
Proof. intros M. extensionality a. reflexivity. Qed.

Definition hull_agree (E : env) (H H' : word -> bool) (h : hull) : Prop :=
  let b := bv_unsigned (edenot E (h_base h)) in
  forall x : word, b + h_lo h <= bv_unsigned x < b + h_hi h -> H x = H' x.

Lemma hulls_sem_restrict : forall E (H H' : word -> bool) M hs,
  Forall (hull_agree E H H') hs -> hulls_sem E (mrestrict H M) (mrestrict H' M) hs.
Proof.
  intros E H H' M hs Hall. unfold hulls_sem. apply Forall_forall. intros h Hin.
  pose proof (proj1 (Forall_forall _ _) Hall h Hin) as Hh. unfold hull_agree in Hh. unfold hull_sem.
  intros x Hx. specialize (Hh x Hx). unfold mrestrict. rewrite Hh.
  destruct (h_same h); [reflexivity|]. destruct (H' x); [reflexivity | intros X; exact X].
Qed.

Section WithSegs.
  Variable segs : list Segment.

  (* [comment removed for export] *)
  #[using="Type"] Theorem know_restrict_transport : forall E (H H' : word -> bool) M hs kn,
    kn_in_hulls_b hs kn = true ->
    Forall (hull_agree E H H') hs ->
    know_ok segs E (mrestrict H M) kn -> know_ok segs E (mrestrict H' M) kn.
  Proof.
    intros E H H' M hs kn Hb Hall HK.
    eapply know_hulls_sound; [apply hulls_sem_restrict; exact Hall | exact Hb | exact HK].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Corollary know_restrict_in : forall E (H : word -> bool) M hs kn,
    kn_in_hulls_b hs kn = true ->
    Forall (hull_agree E (fun _ => false) H) hs ->
    know_ok segs E M kn -> know_ok segs E (mrestrict H M) kn.
  Proof.
    intros E H M hs kn Hb Hall HK. eapply know_restrict_transport; [exact Hb | exact Hall |].
    rewrite mrestrict_none. exact HK.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Corollary know_restrict_out : forall E (H : word -> bool) M hs kn,
    kn_in_hulls_b hs kn = true ->
    Forall (hull_agree E H (fun _ => false)) hs ->
    know_ok segs E (mrestrict H M) kn -> know_ok segs E M kn.
  Proof.
    intros E H M hs kn Hb Hall HK. rewrite <- (mrestrict_none M).
    eapply know_restrict_transport; [exact Hb | exact Hall | exact HK].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma hull_agree_visible : forall E (H H' : word -> bool) b lo hi sm,
    (forall x : word, bv_unsigned (edenot E b) + lo <= bv_unsigned x < bv_unsigned (edenot E b) + hi -> H x = false) ->
    (forall x : word, bv_unsigned (edenot E b) + lo <= bv_unsigned x < bv_unsigned (edenot E b) + hi -> H' x = false) ->
    hull_agree E H H' (HULL b lo hi sm).
  Proof. intros E H H' b lo hi sm H1 H2 x Hx. cbn in Hx. rewrite (H1 x Hx), (H2 x Hx). reflexivity. Qed.
End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition range_visible (H : word -> bool) (a : word) (n : Z) : Prop :=
  forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + n -> H x = false.

Lemma mrestrict_zfill : forall H (a n : word) M,
  range_visible H a (bv_unsigned n) -> mrestrict H (zfill a n M) = zfill a n (mrestrict H M).
Proof.
  intros H a n M Hv. extensionality x. unfold mrestrict, zfill, zmem.
  destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned a + bv_unsigned n)); cbn [andb];
    try reflexivity.
  rewrite (Hv x ltac:(lia)). reflexivity.
Qed.

Lemma mrestrict_unfill : forall H (a n : word) M, mrestrict H (unfill a n M) = unfill a n (mrestrict H M).
Proof.
  intros H a n M. extensionality x. unfold mrestrict, unfill.
  destruct (H x); destruct (_ && _)%bool; reflexivity.
Qed.

Lemma mrestrict_upd : forall H M (a : word) v,
  H a = false -> mrestrict H (fun x => if bv_eqb x a then v else M x) a = v.
Proof. intros H M a v Ha. unfold mrestrict. rewrite Ha, bv_eqb_refl. reflexivity. Qed.

Lemma mrestrict_wbytes : forall H bs (a : word) M,
  range_visible H a (Z.of_nat (length bs)) -> bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64 ->
  mrestrict H (wbytes M a bs) = wbytes (mrestrict H M) a bs.
Proof.
  intros H bs. induction bs as [|b bs IH]; intros a M Hv Hend; cbn [wbytes]; [reflexivity|].
  cbn [length] in Hv, Hend. pose proof (u64_range a) as Ra.
  assert (Ha : H a = false) by (apply Hv; lia).
  assert (Hstep : mrestrict H (fun x : word => if bv_eqb x a then Some b else M x)
                  = (fun x : word => if bv_eqb x a then Some b else mrestrict H M x)).
  { extensionality x. unfold mrestrict. destruct (bv_eqb x a) eqn:Ex; [|reflexivity].
    apply bv_eqb_eq in Ex. subst x. rewrite Ha. reflexivity. }
  destruct bs as [|b2 bs2].
  - cbn [wbytes]. exact Hstep.
  - assert (Ha1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; cbn [length] in Hend; lia).
    rewrite (IH (a + 1)%bv _).
    + rewrite Hstep. reflexivity.
    + intros x Hx. apply Hv. rewrite Ha1 in Hx. cbn [length] in *. lia.
    + rewrite Ha1. cbn [length] in Hend |- *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma munrestrict_denot_in_wins : forall (H : word -> bool) E M log wins (x : word),
  log_in_wins_b wins log = true -> wins_ok E wins -> out_of_wins E wins x ->
  munrestrict H M (mem_denot E (mrestrict H M) log) x = M x.
Proof.
  intros H E M log wins x Hb Hw Hx. unfold munrestrict. destruct (H x) eqn:EH; [reflexivity|].
  rewrite (mem_denot_in_wins E (mrestrict H M) log wins x Hb Hw Hx). unfold mrestrict. rewrite EH. reflexivity.
Qed.

Lemma munrestrict_denot_above : forall (H : word -> bool) E M log spi lows bound (x : word),
  log_below_b spi lows log = true ->
  2 ^ 41 <= bv_unsigned (ev E spi) -> bv_unsigned (ev E spi) <= bound -> bound <= 2 ^ 64 - 2 ^ 41 ->
  lows_ok E bound lows -> bound <= bv_unsigned x ->
  munrestrict H M (mem_denot E (mrestrict H M) log) x = M x.
Proof.
  intros H E M log spi lows bound x Hb S1 S2 S3 Hl Hx. unfold munrestrict. destruct (H x) eqn:EH; [reflexivity|].
  rewrite (mem_denot_above E (mrestrict H M) log spi lows bound x Hb S1 S2 S3 Hl Hx). unfold mrestrict. rewrite EH. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma munrestrict_denot_grows : forall (H : word -> bool) E M log (x : word),
  M x <> None -> munrestrict H M (mem_denot E (mrestrict H M) log) x <> None.
Proof.
  intros H E M log x Hd. unfold munrestrict. destruct (H x) eqn:EH; [exact Hd|].
  apply mem_denot_grows. unfold mrestrict. rewrite EH. exact Hd.
Qed.
