(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ACLIENT_LO : Z := 0x84120.
Definition ACLIENT_HI : Z := 0x8dd94.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ucallerA (d : nat) (L : alayout) (m : amem) (sp s0 ra : word) (trC : list Z) : Prop :=
  (forall PC k, ~ (ACLIENT_LO <= PC < ACLIENT_HI) -> (length trC < k)%nat ->
     uchain m (al_top L) PC (bv_unsigned sp) (bv_unsigned s0) k trC)
  /\ (length trC + d <= 12)%nat
  /\ bv_unsigned s0 <> bv_unsigned sp + 8
  /\ ACLIENT_LO <= bv_unsigned ra < ACLIENT_HI
  /\ (bv_unsigned s0 <= bv_unsigned sp \/ bv_unsigned sp + 16 <= bv_unsigned s0).

(* [comment removed for export] *)
Definition unw_okA (L : alayout) (RNG : footprint) (m : amem) (lo PC : Z) (sp s0 ra : word) : Prop :=
  (exists tr, aunw m L RNG lo PC sp s0 ra tr)
  /\ bv_unsigned s0 <> bv_unsigned sp + 8 /\ 4096 <= bv_unsigned ra /\ bv_unsigned ra <> PC.

(* [comment removed for export] *)
#[using="Type"] Lemma unw_of_ucaller : forall d L RNG m lo PC (sp s0 ra : word) trC,
  ucallerA d L m sp s0 ra trC -> ~ (ACLIENT_LO <= PC < ACLIENT_HI) ->
  bv_unsigned sp + 16 < al_top L -> In (PC :: bv_unsigned ra :: trC) (al_U L) -> rng RNG lo (al_top L - lo) ->
  unw_okA L RNG m lo PC sp s0 ra.
Proof.
  intros d L RNG m lo PC sp s0 ra trC (UC & LEN & S8 & RA & _) HPC HT HU HR. unfold unw_okA, ACLIENT_LO, ACLIENT_HI in *.
  split; [| repeat split; lia].
  exists trC. left. split; [exact HT|]. split; [apply UC; [exact HPC| unfold UDEPTH; lia]|]. split; [lia|]. split; [exact HU| exact HR].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ucaller_data : forall d L m (sp s0 ra : word) X,
  bv_unsigned s0 <= bv_unsigned sp -> ra = Z_to_bv 64 X -> ACLIENT_LO <= X < ACLIENT_HI -> (d <= 12)%nat ->
  ucallerA d L m sp s0 ra [].
Proof.
  intros d L m sp s0 ra X HS -> HX HD. unfold ucallerA, ACLIENT_LO, ACLIENT_HI in *.
  assert (EX : bv_unsigned (Z_to_bv 64 X) = X) by (apply unsigned_lit; lia).
  split; [intros PC k _ _; apply uc_stop; intros (A & _); lia|]. split; [cbn; lia|]. split; [lia|]. split; [rewrite EX; lia| left; exact HS].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ucaller_keep : forall d L m m' (sp s0 ra : word) trC,
  ucallerA d L m sp s0 ra trC -> al_top L <= 2^47 ->
  (forall a, bv_unsigned sp <= a < 2^64 -> m' (wa a) = m (wa a)) ->
  ucallerA d L m' sp s0 ra trC.
Proof.
  intros d L m m' sp s0 ra trC (UC & LEN & S8 & RA & HS0) HT HM.
  split; [| split; [exact LEN| split; [exact S8| split; [exact RA| exact HS0]]]].
  intros PC k HPC HK. specialize (UC PC k HPC HK). destruct HS0 as [HS0|HS0].
  - inversion UC; subst; try (exfalso; lia). apply uc_stop. assumption.
  - eapply uchain_frame; [exact UC|]. intros a Ha. apply HM. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ucaller_frame : forall d d' L m (sp s0 ra sp' ra' : word) trC X,
  ucallerA d L m sp s0 ra trC ->
  bv_unsigned sp' + 16 <= bv_unsigned sp -> bv_unsigned sp < al_top L - 16 -> bv_unsigned sp mod 8 = 0 ->
  bytes_at asegs m (bv_unsigned sp - 16) (le8 s0) -> bytes_at asegs m (bv_unsigned sp - 8) (le8 ra) ->
  ra' = Z_to_bv 64 X -> ACLIENT_LO <= X < ACLIENT_HI -> (S d' <= d)%nat ->
  ucallerA d' L m sp' sp ra' (bv_unsigned ra :: trC).
Proof.
  intros d d' L m sp s0 ra sp' ra' trC X (UC & LEN & S8 & RA & HS0) HSP HTOP HAL B1 B2 -> HX HL.
  unfold ucallerA, ACLIENT_LO, ACLIENT_HI in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  pose proof (bv_unsigned_in_range 64 sp') as RSP'. unfold bv_modulus in RSP'.
  pose proof (bv_unsigned_in_range 64 s0) as RS0. unfold bv_modulus in RS0.
  assert (EX : bv_unsigned (Z_to_bv 64 X) = X) by (apply unsigned_lit; lia).
  split; [| split; [cbn [length]; lia| split; [lia| split; [rewrite EX; lia| right; lia]]]].
  intros PC k HPC HK. cbn [length] in HK.
  replace (bv_unsigned ra :: trC) with ((if bv_unsigned ra =? PC then [] else [bv_unsigned ra]) ++ trC).
  2:{ destruct (Z.eqb_spec (bv_unsigned ra) PC) as [E|NE]; [exfalso; apply HPC; rewrite <- E; lia| reflexivity]. }
  eapply (uc_step m (al_top L) PC (bv_unsigned sp') (bv_unsigned sp) k (bv_unsigned s0) (bv_unsigned ra) trC); try lia.
  - rewrite Z_to_bv_bv_unsigned. exact B1.
  - rewrite Z_to_bv_bv_unsigned. exact B2.
  - destruct (Z.eqb_spec (bv_unsigned ra) PC) as [E|NE]; [exfalso; apply HPC; rewrite <- E; lia|].
    apply UC; [exact HPC| lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ucaller_weaken : forall d d' L m (sp s0 ra : word) trC, ucallerA d L m sp s0 ra trC -> (d' <= d)%nat -> ucallerA d' L m sp s0 ra trC.
Proof. intros d d' L m sp s0 ra trC (UC & LEN & R) HD. split; [exact UC|]. split; [lia| exact R]. Qed.

End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ACLIENT_LO : Z := 0x84188.
Definition ACLIENT_HI : Z := 0x8e178.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ucallerA (d : nat) (L : alayout) (m : amem) (sp s0 ra : word) (trC : list Z) : Prop :=
  (forall PC k, ~ (ACLIENT_LO <= PC < ACLIENT_HI) -> (length trC < k)%nat ->
     uchain m (al_top L) PC (bv_unsigned sp) (bv_unsigned s0) k trC)
  /\ (length trC + d <= 12)%nat
  /\ bv_unsigned s0 <> bv_unsigned sp + 8
  /\ ACLIENT_LO <= bv_unsigned ra < ACLIENT_HI
  /\ (bv_unsigned s0 <= bv_unsigned sp \/ bv_unsigned sp + 16 <= bv_unsigned s0).

(* [comment removed for export] *)
Definition unw_okA (L : alayout) (RNG : footprint) (m : amem) (lo PC : Z) (sp s0 ra : word) : Prop :=
  (exists tr, aunw m L RNG lo PC sp s0 ra tr)
  /\ bv_unsigned s0 <> bv_unsigned sp + 8 /\ 4096 <= bv_unsigned ra /\ bv_unsigned ra <> PC.

(* [comment removed for export] *)
#[using="Type"] Lemma unw_of_ucaller : forall d L RNG m lo PC (sp s0 ra : word) trC,
  ucallerA d L m sp s0 ra trC -> ~ (ACLIENT_LO <= PC < ACLIENT_HI) ->
  bv_unsigned sp + 16 < al_top L -> In (PC :: bv_unsigned ra :: trC) (al_U L) -> rng RNG lo (al_top L - lo) ->
  unw_okA L RNG m lo PC sp s0 ra.
Proof.
  intros d L RNG m lo PC sp s0 ra trC (UC & LEN & S8 & RA & _) HPC HT HU HR. unfold unw_okA, ACLIENT_LO, ACLIENT_HI in *.
  split; [| repeat split; lia].
  exists trC. left. split; [exact HT|]. split; [apply UC; [exact HPC| unfold UDEPTH; lia]|]. split; [lia|]. split; [exact HU| exact HR].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ucaller_data : forall d L m (sp s0 ra : word) X,
  bv_unsigned s0 <= bv_unsigned sp -> ra = Z_to_bv 64 X -> ACLIENT_LO <= X < ACLIENT_HI -> (d <= 12)%nat ->
  ucallerA d L m sp s0 ra [].
Proof.
  intros d L m sp s0 ra X HS -> HX HD. unfold ucallerA, ACLIENT_LO, ACLIENT_HI in *.
  assert (EX : bv_unsigned (Z_to_bv 64 X) = X) by (apply unsigned_lit; lia).
  split; [intros PC k _ _; apply uc_stop; intros (A & _); lia|]. split; [cbn; lia|]. split; [lia|]. split; [rewrite EX; lia| left; exact HS].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ucaller_keep : forall d L m m' (sp s0 ra : word) trC,
  ucallerA d L m sp s0 ra trC -> al_top L <= 2^47 ->
  (forall a, bv_unsigned sp <= a < 2^64 -> m' (wa a) = m (wa a)) ->
  ucallerA d L m' sp s0 ra trC.
Proof.
  intros d L m m' sp s0 ra trC (UC & LEN & S8 & RA & HS0) HT HM.
  split; [| split; [exact LEN| split; [exact S8| split; [exact RA| exact HS0]]]].
  intros PC k HPC HK. specialize (UC PC k HPC HK). destruct HS0 as [HS0|HS0].
  - inversion UC; subst; try (exfalso; lia). apply uc_stop. assumption.
  - eapply uchain_frame; [exact UC|]. intros a Ha. apply HM. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ucaller_frame : forall d d' L m (sp s0 ra sp' ra' : word) trC X,
  ucallerA d L m sp s0 ra trC ->
  bv_unsigned sp' + 16 <= bv_unsigned sp -> bv_unsigned sp < al_top L - 16 -> bv_unsigned sp mod 8 = 0 ->
  bytes_at asegs m (bv_unsigned sp - 16) (le8 s0) -> bytes_at asegs m (bv_unsigned sp - 8) (le8 ra) ->
  ra' = Z_to_bv 64 X -> ACLIENT_LO <= X < ACLIENT_HI -> (S d' <= d)%nat ->
  ucallerA d' L m sp' sp ra' (bv_unsigned ra :: trC).
Proof.
  intros d d' L m sp s0 ra sp' ra' trC X (UC & LEN & S8 & RA & HS0) HSP HTOP HAL B1 B2 -> HX HL.
  unfold ucallerA, ACLIENT_LO, ACLIENT_HI in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  pose proof (bv_unsigned_in_range 64 sp') as RSP'. unfold bv_modulus in RSP'.
  pose proof (bv_unsigned_in_range 64 s0) as RS0. unfold bv_modulus in RS0.
  assert (EX : bv_unsigned (Z_to_bv 64 X) = X) by (apply unsigned_lit; lia).
  split; [| split; [cbn [length]; lia| split; [lia| split; [rewrite EX; lia| right; lia]]]].
  intros PC k HPC HK. cbn [length] in HK.
  replace (bv_unsigned ra :: trC) with ((if bv_unsigned ra =? PC then [] else [bv_unsigned ra]) ++ trC).
  2:{ destruct (Z.eqb_spec (bv_unsigned ra) PC) as [E|NE]; [exfalso; apply HPC; rewrite <- E; lia| reflexivity]. }
  eapply (uc_step m (al_top L) PC (bv_unsigned sp') (bv_unsigned sp) k (bv_unsigned s0) (bv_unsigned ra) trC); try lia.
  - rewrite Z_to_bv_bv_unsigned. exact B1.
  - rewrite Z_to_bv_bv_unsigned. exact B2.
  - destruct (Z.eqb_spec (bv_unsigned ra) PC) as [E|NE]; [exfalso; apply HPC; rewrite <- E; lia|].
    apply UC; [exact HPC| lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ucaller_weaken : forall d d' L m (sp s0 ra : word) trC, ucallerA d L m sp s0 ra trC -> (d' <= d)%nat -> ucallerA d' L m sp s0 ra trC.
Proof. intros d d' L m sp s0 ra trC (UC & LEN & R) HD. split; [exact UC|]. split; [lia| exact R]. Qed.

End CANSEC1.
End TwB.
