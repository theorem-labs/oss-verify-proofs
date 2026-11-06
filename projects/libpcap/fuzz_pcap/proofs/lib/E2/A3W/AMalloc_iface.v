(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg AProto.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Export ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section Client.
Variable CI : list (Z * Z).     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition aclient_addr (LB : list ablock) (SP : Z) (a : Z) : Prop :=
  (SP <= a)          (* [comment removed for export] *)
  \/ in_ranges CI a
  \/ in_block LB a
  \/ (exists a', ((ATOP <= a' < 2^47) \/ in_ranges CI a' \/ in_fake LB a') /\ a = shad a').   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition atls_addr (a : Z) : Prop :=
  (ATPv + -200 <= a < ATPv + 312) \/ (exists a', ATPv + -200 <= a' < ATPv + 312 /\ a = shad a').

(* [comment removed for export] *)
Definition AIMSH_LO : Z := 0x7fffa000.
Definition AIMSH_LEN : Z := 779776.
(* [comment removed for export] *)
Definition AAHM_SZ : Z := 3727360.
Definition aextra_addr (a : Z) : Prop :=
  atls_addr a \/ (AIMSH_LO <= a < AIMSH_LO + AIMSH_LEN) \/ (AAHMv <= a < AAHMv + AAHM_SZ).

Definition aheap_pres (LB : list ablock) (SP : Z) (m m' : amem) : Prop :=
  forall a, 0 <= a < 2^64 -> aclient_addr LB SP a \/ aextra_addr a ->
    m' (wa a) = m (wa a) /\ (wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None).

#[using="Type"] Lemma aheap_pres_refl : forall LB SP m, aheap_pres LB SP m m.
Proof. intros LB SP m a _ _. auto. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma aheap_pres_of_munch : forall LB SP (W : list (Z * Z)) m m',
  munch W m m' -> wmono asegs m m' ->
  (forall a, 0 <= a < 2^64 -> aclient_addr LB SP a -> outside W a) ->
  (forall a, 0 <= a < 2^64 -> aextra_addr a -> outside W a) ->
  aheap_pres LB SP m m'.
Proof.
  intros LB SP W m m' MU WM HC HT a Ha CL. split; [| intros Hw; apply WM; exact Hw].
  apply MU. rewrite wa_unsigned by exact Ha. destruct CL as [CL|TL]; [apply HC| apply HT]; assumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tls_shadow_band : forall a', ATPv + -200 <= a' < ATPv + 312 -> 2147450880 + 512 <= shad a' /\ shad a' + 449 <= shad ATOP.
Proof.
  intros a' Ha'. pose proof atp_lin as ((TL & _) & _). pose proof ATOP_al16 as A16. unfold shad, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
  clear -Ha' TL A16. Z.div_mod_to_equations. lia.
Qed.
#[using="Type"] Lemma tls_shadow_apart : forall a' B n, ATPv + -200 <= a' < ATPv + 312 -> 0 <= n ->
  (ATPv + 312 <= B \/ (B + n <= ATPv + -200 /\ B mod 8 = 0)) -> shad a' + 1 <= shad B \/ shad B + shlen n <= shad a'.
Proof.
  intros a' B n Ha' Hn D. pose proof ATPv_pg as TPG. unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
  destruct D as [D|[D M8]]; [left; clear -Ha' Hn D TPG | right; clear -Ha' Hn D TPG M8]; Z.div_mod_to_equations; lia.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma atls_not_app : forall A B a, (B <= ATPv + -200 \/ ATPv + 312 <= A) -> (B <= 2147446784 \/ 17594333495296 <= A) -> A <= a < B -> ~ atls_addr a.
Proof.
  intros A B a D SB Ha [T|(a' & Ha' & ->)]; [clear -D Ha T; lia|].
  pose proof (tls_shadow_band a' Ha') as (S1 & S2). pose proof atop_range as AR.
  assert (SA : shad ATOP <= 17594332446720) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear -AR; Z.div_mod_to_equations; lia).
  clear -SB Ha S1 S2 SA. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma atls_outside : forall (W : list (Z * Z)) a,
  (forall A k, ATPv + -200 <= A -> A + k <= ATPv + 312 -> 0 <= k -> disjoint_from W A k) ->
  (forall a', ATPv + -200 <= a' < ATPv + 312 -> disjoint_from W (shad a') 1) ->
  atls_addr a -> outside W a.
Proof.
  intros W a TK TS [TB|(a' & Ha' & ->)].
  - eapply disjoint_outside; [apply (TK a 1); lia| lia].
  - eapply disjoint_outside; [apply (TS a' Ha')| lia].
Qed.
#[using="Type"] Lemma aextra_outside : forall (W : list (Z * Z)) a,
  (forall A k, ATPv + -200 <= A -> A + k <= ATPv + 312 -> 0 <= k -> disjoint_from W A k) ->
  (forall a', ATPv + -200 <= a' < ATPv + 312 -> disjoint_from W (shad a') 1) ->
  disjoint_from W AIMSH_LO AIMSH_LEN ->
  disjoint_from W AAHMv AAHM_SZ ->
  aextra_addr a -> outside W a.
Proof.
  intros W a TK TS IM AH [T|[I|H]]; [exact (atls_outside W a TK TS T)| |].
  - eapply disjoint_outside; [exact IM| exact I].
  - eapply disjoint_outside; [exact AH| exact H].
Qed.

#[using="Type"] Lemma aheap_pres_trans : forall LB SP m1 m2 m3,
  aheap_pres LB SP m1 m2 -> aheap_pres LB SP m2 m3 -> aheap_pres LB SP m1 m3.
Proof.
  intros LB SP m1 m2 m3 H1 H2 a Ha Hc. destruct (H1 a Ha Hc) as [E1 W1]. destruct (H2 a Ha Hc) as [E2 W2].
  split; [congruence| auto].
Qed.

#[using="Type"] Lemma aheap_pres_weaken : forall LB LB' SP SP' m m',
  aheap_pres LB SP m m' -> SP <= SP' -> (forall b, In b LB' -> In b LB) -> aheap_pres LB' SP' m m'.
Proof.
  intros LB LB' SP SP' m m' H HS HL a Ha Hc. apply H; [exact Ha|].
  destruct Hc as [Hc|HT]; [left| right; exact HT].
  destruct Hc as [Hc|[Hc|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
  - left; lia.
  - right; left; exact Hc.
  - right; right; left. exists b. split; [apply HL; exact Hb| exact Hr].
  - right; right; right. exists a'. split; [|reflexivity].
    destruct Ha' as [X|[X|(c & A & n & Hin & X)]]; [left; lia| right; left; exact X| right; right].
    exists c, A, n. split; [apply HL; exact Hin| exact X].
Qed.

(* [comment removed for export] *)
Definition aclient_app_range (LB : list ablock) (SP : Z) (A n : Z) : Prop :=
  (SP <= A)          (* [comment removed for export] *)
  \/ (exists iv, In iv CI /\ fst iv <= A /\ A + n <= snd iv)
  \/ (exists cls FA fn, In (mkABlock (ABFake cls) FA fn) LB /\ FA <= A /\ A + n <= FA + fn).

(* [comment removed for export] *)
Definition aclient_range (LB : list ablock) (SP : Z) (A n : Z) : Prop :=
  aclient_app_range LB SP A n
  \/ (exists b, In b LB /\ ab_addr b <= A /\ A + n <= ab_addr b + ab_size b)
  \/ ((ATOP <= 8 * (A - ASHOFF) /\ 8 * (A - ASHOFF) + 8 * n <= 2^47)      (* [comment removed for export] *)
      \/ (exists iv, In iv CI /\ fst iv <= 8 * (A - ASHOFF) /\ 8 * (A - ASHOFF) + 8 * n <= snd iv)
      \/ (exists cls FA fn, In (mkABlock (ABFake cls) FA fn) LB /\ FA <= 8 * (A - ASHOFF) /\ 8 * (A - ASHOFF) + 8 * n <= FA + fn)).

(* [comment removed for export] *)
Definition atls_client (A n : Z) : Prop :=
  (ATPv + -200 <= A /\ A + n <= ATPv + -88) \/ (ATPv + -80 <= A /\ A + n <= ATPv + -8) \/ (ATPv + 20 <= A /\ A + n <= ATPv + 288).
(* [comment removed for export] *)
Definition aahm_client (A n : Z) : Prop := AAHMv <= A /\ A + n <= AAHMv + AAHM_SZ.

#[using="Type"] Lemma shad_unshad : forall a, shad (8 * (a - ASHOFF)) = a.
Proof. intros a. unfold shad. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mul_comm, Z.div_mul by lia. lia. Qed.

#[using="Type"] Lemma aclient_range_addr : forall LB SP A n a,
  aclient_range LB SP A n -> A <= a < A + n -> aclient_addr LB SP a.
Proof.
  intros LB SP A n a HR Ha. unfold aclient_range, aclient_app_range, aclient_addr, in_ranges, in_block, in_fake in *.
  destruct HR as [[H|[(iv & Hiv & H1 & H2)|(c & FA & fn & Hb & H1 & H2)]] | [(b & Hb & H1 & H2) | HS]].
  - left; lia.
  - right; left; exists iv; split; [exact Hiv|lia].
  - right; right; left. exists (mkABlock (ABFake c) FA fn). split; [exact Hb| cbn; lia].
  - right; right; left; exists b; split; [exact Hb|lia].
  - right; right; right. exists (8 * (a - ASHOFF)). split; [| symmetry; apply shad_unshad].
    destruct HS as [H|[(iv & Hiv & H1 & H2)|(c & FA & fn & Hb & H1 & H2)]].
    + left; lia.
    + right; left; exists iv; split; [exact Hiv|lia].
    + right; right. exists c, FA, fn. split; [exact Hb|lia].
Qed.

#[using="Type"] Lemma aheap_pres_bytes_at : forall LB SP m m' A bs,
  aheap_pres LB SP m m' -> bytes_at asegs m A bs -> aclient_range LB SP A (Z.of_nat (length bs)) ->
  bytes_at asegs m' A bs.
Proof.
  intros LB SP m m' A bs HP (H0 & H1 & HB) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(left; eapply aclient_range_addr; [exact HR|lia])) as [E _].
  rewrite E. reflexivity.
Qed.

#[using="Type"] Lemma aheap_pres_wr_at : forall LB SP m m' A n,
  aheap_pres LB SP m m' -> wr_at asegs m A n -> aclient_range LB SP A n -> wr_at asegs m' A n.
Proof.
  intros LB SP m m' A n HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(left; eapply aclient_range_addr; [exact HR|lia])) as [_ W].
  apply W. apply HW. exact Hi.
Qed.

#[using="Type"] Lemma aheap_pres_rw_cells : forall LB SP m m' A cs,
  aheap_pres LB SP m m' -> rw_cells asegs m A cs -> aclient_range LB SP A (Z.of_nat (cells_size cs)) ->
  rw_cells asegs m' A cs.
Proof.
  intros LB SP m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
  - eapply aheap_pres_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HR.
  - eapply aheap_pres_wr_at; eauto.
Qed.

#[using="Type"] Lemma aheap_pres_stk : forall LB SP m m' lo hi,
  aheap_pres LB SP m m' -> stk asegs m lo hi -> SP <= lo -> hi <= 2^47 -> stk asegs m' lo hi.
Proof.
  intros LB SP m m' lo hi HP ST HS HH. (nd_pre ST 3%nat; intros H0 H1 HW; nd_post). split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP i ltac:(lia) ltac:(left; left; lia)) as [E W]. destruct (HW i Hi) as [W0 [b Hb]].
  split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma aheap_pres_shadow : forall LB SP m m' a',
  aheap_pres LB SP m m' ->
  ((ATOP <= a' < 2^47) \/ in_ranges CI a' \/ in_fake LB a') ->
  0 <= shad a' < 2^64 ->
  m' (wa (shad a')) = m (wa (shad a')).
Proof.
  intros LB SP m m' a' HP Ha Hs. destruct (HP (shad a') Hs ltac:(left; right; right; right; exists a'; split; [exact Ha|reflexivity])) as [E _]. exact E.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma aheap_pres_tls_bytes_at : forall LB SP m m' A bs,
  aheap_pres LB SP m m' -> bytes_at asegs m A bs -> ATPv + -200 <= A -> A + Z.of_nat (length bs) <= ATPv + 312 ->
  bytes_at asegs m' A bs.
Proof.
  intros LB SP m m' A bs HP (H0 & H1 & HB) HA HE. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(right; left; left; lia)) as [E _].
  rewrite E. reflexivity.
Qed.

#[using="Type"] Lemma aheap_pres_tls_wr_at : forall LB SP m m' A n,
  aheap_pres LB SP m m' -> wr_at asegs m A n -> ATPv + -200 <= A -> A + n <= ATPv + 312 -> wr_at asegs m' A n.
Proof.
  intros LB SP m m' A n HP (H0 & H1 & HW) HA HE. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(right; left; left; lia)) as [_ W].
  apply W. apply HW. exact Hi.
Qed.

#[using="Type"] Lemma aheap_pres_tls_rw_cells : forall LB SP m m' A cs,
  aheap_pres LB SP m m' -> rw_cells asegs m A cs -> ATPv + -200 <= A -> A + Z.of_nat (cells_size cs) <= ATPv + 312 ->
  rw_cells asegs m' A cs.
Proof.
  intros LB SP m m' A cs HP [[Hwf HB] HW] HA HE. split; [split; [exact Hwf|]|].
  - eapply aheap_pres_tls_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HE.
  - eapply aheap_pres_tls_wr_at; eauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma aheap_pres_tls_shadow : forall LB SP m m' a',
  aheap_pres LB SP m m' -> ATPv + -200 <= a' < ATPv + 312 -> 0 <= shad a' < 2^64 ->
  m' (wa (shad a')) = m (wa (shad a')) /\ (wview asegs m (wa (shad a')) <> None -> wview asegs m' (wa (shad a')) <> None).
Proof. intros LB SP m m' a' HP Ha Hs. apply (HP (shad a') Hs). right. left. right. exists a'. split; [exact Ha| reflexivity]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma aheap_pres_imsh_bytes_at : forall LB SP m m' A bs,
  aheap_pres LB SP m m' -> bytes_at asegs m A bs -> AIMSH_LO <= A -> A + Z.of_nat (length bs) <= AIMSH_LO + AIMSH_LEN ->
  bytes_at asegs m' A bs.
Proof.
  intros LB SP m m' A bs HP (H0 & H1 & HB) HA HE. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(right; right; left; lia)) as [E _].
  rewrite E. reflexivity.
Qed.
#[using="Type"] Lemma aheap_pres_imsh_wr_at : forall LB SP m m' A n,
  aheap_pres LB SP m m' -> wr_at asegs m A n -> AIMSH_LO <= A -> A + n <= AIMSH_LO + AIMSH_LEN -> wr_at asegs m' A n.
Proof.
  intros LB SP m m' A n HP (H0 & H1 & HW) HA HE. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(right; right; left; lia)) as [_ W].
  apply W. apply HW. exact Hi.
Qed.
#[using="Type"] Lemma aheap_pres_imsh_rw_cells : forall LB SP m m' A cs,
  aheap_pres LB SP m m' -> rw_cells asegs m A cs -> AIMSH_LO <= A -> A + Z.of_nat (cells_size cs) <= AIMSH_LO + AIMSH_LEN ->
  rw_cells asegs m' A cs.
Proof.
  intros LB SP m m' A cs HP [[Hwf HB] HW] HA HE. split; [split; [exact Hwf|]|].
  - eapply aheap_pres_imsh_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HE.
  - eapply aheap_pres_imsh_wr_at; eauto.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma aheap_pres_imsh_byte : forall LB SP m m' a,
  aheap_pres LB SP m m' -> AIMSH_LO <= a < AIMSH_LO + AIMSH_LEN ->
  m' (wa a) = m (wa a) /\ (wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None).
Proof. intros LB SP m m' a HP Ha. apply (HP a); [unfold AIMSH_LO, AIMSH_LEN in Ha; lia|]. right. right. left. exact Ha. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma aheap_pres_ahm_bytes_at : forall LB SP m m' A bs,
  aheap_pres LB SP m m' -> bytes_at asegs m A bs -> AAHMv <= A -> A + Z.of_nat (length bs) <= AAHMv + AAHM_SZ ->
  bytes_at asegs m' A bs.
Proof.
  intros LB SP m m' A bs HP (H0 & H1 & HB) HA HE. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(right; right; right; lia)) as [E _].
  rewrite E. reflexivity.
Qed.
#[using="Type"] Lemma aheap_pres_ahm_wr_at : forall LB SP m m' A n,
  aheap_pres LB SP m m' -> wr_at asegs m A n -> AAHMv <= A -> A + n <= AAHMv + AAHM_SZ -> wr_at asegs m' A n.
Proof.
  intros LB SP m m' A n HP (H0 & H1 & HW) HA HE. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(right; right; right; lia)) as [_ W].
  apply W. apply HW. exact Hi.
Qed.
#[using="Type"] Lemma aheap_pres_ahm_rw_cells : forall LB SP m m' A cs,
  aheap_pres LB SP m m' -> rw_cells asegs m A cs -> AAHMv <= A -> A + Z.of_nat (cells_size cs) <= AAHMv + AAHM_SZ ->
  rw_cells asegs m' A cs.
Proof.
  intros LB SP m m' A cs HP [[Hwf HB] HW] HA HE. split; [split; [exact Hwf|]|].
  - eapply aheap_pres_ahm_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HE.
  - eapply aheap_pres_ahm_wr_at; eauto.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma aheap_pres_ahm_byte : forall LB SP m m' a,
  aheap_pres LB SP m m' -> 0 <= a < 2^64 -> AAHMv <= a < AAHMv + AAHM_SZ ->
  m' (wa a) = m (wa a) /\ (wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None).
Proof. intros LB SP m m' a HP R Ha. apply (HP a R). right. right. right. exact Ha. Qed.

End Client.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pcov (RESV : list (Z * Z)) (lo hi : Z) : Prop :=
  forall x, lo <= x < hi -> exists iv, In iv RESV /\ fst iv <= x < snd iv.
Definition aresv_ok (L : alayout) (RESV : list (Z * Z)) : Prop :=
     pcov RESV 0x10000 AIMG_HI                                            (* [comment removed for export] *)
  /\ pcov RESV 0x7fff7000 0x10007fff8000                                  (* [comment removed for export] *)
  /\ pcov RESV (4096 * al_V L 221%nat) (4096 * al_V L 221%nat + 137439023104)   (* [comment removed for export] *)
  /\ pcov RESV (al_ptr_array L) (al_ptr_array L + 0x800000)              (* [comment removed for export] *)
  /\ pcov RESV (al_t L) (al_t L + 4096) /\ pcov RESV (al_ctx L) (al_ctx L + 65536)
  /\ pcov RESV (al_nodes L) (al_nodes L + 1048576) /\ pcov RESV (al_store L) (al_store L + 8388608)
  /\ pcov RESV (al_fake L) (al_fake L + 11571200) /\ pcov RESV (4096 * al_V L 323%nat) (4096 * al_V L 323%nat + 4096)   (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ pcov RESV (4096 * al_V L 91%nat) (4096 * al_V L 91%nat + 0x10000)
  /\ pcov RESV (4096 * al_V L 220%nat) (4096 * al_V L 220%nat + 0x38e000)
  /\ pcov RESV (4096 * al_V L 258%nat) (4096 * al_V L 258%nat + 4096)
  /\ pcov RESV (4096 * al_V L 503%nat) (4096 * al_V L 503%nat + 4096)
  /\ pcov RESV (4096 * al_V L 584%nat) (4096 * al_V L 584%nat + 4096)
  /\ pcov RESV (ATPv + -200) (ATPv + 312).      (* [comment removed for export] *)

#[using="Type"] Lemma pcov_clear : forall RESV lo hi a n,
  pcov RESV lo hi -> avoids_all a n RESV = true -> lo < hi -> 0 < n -> a + n <= lo \/ hi <= a.
Proof.
  intros RESV lo hi a n PC AV LH N.
  destruct (Z_lt_le_dec a hi) as [L1|]; [| right; lia]. destruct (Z_lt_le_dec lo (a + n)) as [L2|]; [| left; lia]. exfalso.
  (nd_pre (PC (Z.max a lo) ltac:(lia)) 3%nat; intros iv Hin R; nd_post).
  unfold avoids_all in AV. rewrite forallb_forall in AV. specialize (AV iv Hin). unfold iv_clear in AV.
  apply orb_prop in AV. destruct AV as [AV|AV]; apply Z.leb_le in AV; lia.
Qed.

Section Stmts.
Variable CI : list (Z * Z).
(* [comment removed for export] *)
Variable AHEAP : alayout -> footprint -> astate -> list ablock -> amem -> Prop.

(* [comment removed for export] *)
Definition aunw (m : amem) (L : alayout) (RNG : footprint) (lo PC : Z) (sp s0 ra : word) (tr : list Z) : Prop :=
     (bv_unsigned sp + 16 < al_top L
      /\ uchain m (al_top L) PC (bv_unsigned sp) (bv_unsigned s0) UDEPTH tr /\ (length tr <= 28)%nat
      /\ In (PC :: bv_unsigned ra :: tr) (al_U L)
      /\ rng RNG lo (al_top L - lo))            (* [comment removed for export] *)
  \/ (al_top L <= bv_unsigned sp + 16 /\ bv_unsigned sp < 2^47 /\ In [PC] (al_U L)).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition amalloc_post (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (n lo : Z) (m : amem)
    (r : astate * option aptr) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI LB (bv_unsigned sp) m m'
    /\ match snd r with
       | None => False      (* [comment removed for export] *)
       | Some p => exists A junk,
           a0 = Z_to_bv 64 A /\ ablock_range A n
           /\ AHEAP L RNG' (fst r) (HB p A n :: LB) m'
           /\ rw_cells asegs m' A [CB (Z.to_nat n) junk]
           /\ rng RNG' A n /\ rng RNG' (shad A) (shlen (n + 7))
           /\ (is_primary n = false -> A = aptr_addr (fst r) p)
       end.

Definition amalloc_stmt : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem)
         (st : astate) (LB : list ablock) (n lo : Z) (tr : list Z) (RESV : list (Z * Z)),
  AHEAP L RNG st LB m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 n -> 1 <= n <= AREQMAX ->                    (* [comment removed for export] *)
  (* [comment removed for export] *)
  aunw m L RNG lo AMALLOC_PC sp s0 ra tr ->
  (* [comment removed for export] *)
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AMALLOC_PC ->
  bv_unsigned sp mod 16 = 0 ->
  (* [comment removed for export] *)
  rng RNG lo (bv_unsigned sp - lo) ->
  (* [comment removed for export] *)
  aresv_ok L RESV ->
  implS asegs RNG (aembed ATOP (amalloc ATOP RESV st n))
        (epostF (amalloc_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AMALLOC_SYM) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
Definition afree_post (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (p : aptr) (lo : Z) (m : amem)
    (r : astate) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI (lb_remove p LB) (bv_unsigned sp) m m'
    /\ AHEAP L RNG' r (lb_remove p LB) m'.

Definition afree_stmt : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem)
         (st : astate) (LB : list ablock) (p : aptr) (A n lo : Z) (tr : list Z),
  AHEAP L RNG st LB m -> In (HB p A n) LB ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 A ->
  aunw m L RNG lo AFREE_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  implS asegs RNG (aembed ATOP (afree st (Some p)))
        (epostF (afree_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
Definition afree_null_post (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI LB (bv_unsigned sp) m m'
    /\ AHEAP L RNG st LB m'.

Definition afree_null_stmt : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem)
         (st : astate) (LB : list ablock) (lo : Z) (tr : list Z),
  AHEAP L RNG st LB m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 0 ->
  aunw m L RNG lo AFREE_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (afree_null_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom asegs)).
End Stmts.

Record AMallocIface := mkAMallocIface {
  aci : list (Z * Z);          (* [comment removed for export] *)
  AHEAP : alayout -> footprint -> astate -> list ablock -> amem -> Prop;
  (* [comment removed for export] *)
  AI_aci_img : forall iv, In iv aci -> snd iv <= AIMG_HI;      (* [comment removed for export] *)
  AI_aci_lo : forall iv, In iv aci -> 0 <= fst iv;            (* [comment removed for export] *)
  AI_rng_mono : forall L RNG RNG' st LB m, fp_le RNG RNG' -> AHEAP L RNG st LB m -> AHEAP L RNG' st LB m;
  AI_perm : forall L RNG st LB LB' m, Permutation.Permutation LB LB' -> AHEAP L RNG st LB m -> AHEAP L RNG st LB' m;
  AI_frame : forall L RNG st LB m m' (W : list ivl),
      AHEAP L RNG st LB m -> munch W m m' -> wmono asegs m m' ->
      Forall (fun iv => aclient_range aci LB (ATOP + 4096) (fst iv) (snd iv - fst iv) \/ atls_client (fst iv) (snd iv - fst iv)
                        \/ aahm_client (fst iv) (snd iv - fst iv)) W ->
      AHEAP L RNG st LB m';          (* [comment removed for export] *)
  (* A client write set plus the 4-byte TLS cell at ATP + 16, which is back at zero afterwards. *)
  AI_frame_lsan : forall L RNG st LB m m' (W : list ivl),
      AHEAP L RNG st LB m -> munch (W ++ [(ATP + 16, ATP + 20)]) m m' -> wmono asegs m m' ->
      Forall (fun iv => aclient_range aci LB (ATOP + 4096) (fst iv) (snd iv - fst iv) \/ atls_client (fst iv) (snd iv - fst iv)
                        \/ aahm_client (fst iv) (snd iv - fst iv)) W ->
      rw_cells asegs m' (ATP + 16) [C4 (Z_to_bv 64 0)] ->
      AHEAP L RNG st LB m';
  AI_block : forall L RNG st LB m p A n,
      AHEAP L RNG st LB m -> In (HB p A n) LB ->
      1 <= n <= AREQMAX /\                                        (* [comment removed for export] *)
      ablock_range A n /\ rng RNG A n /\ rng RNG (shad A) (shlen (n + 7)) /\ ablock_shadow m A n
      /\ wr_at asegs m A n
      /\ (exists ch, (a_live st) !! p = Some ch /\ chunk_size ch = n /\ (is_primary n = false -> A = chunk_user_beg ch))
      (* [comment removed for export] *)
      /\ exists RLO RHI, RLO mod 4096 = 0 /\ RHI mod 4096 = 0 /\ RLO + 64 <= A /\ A + n + 64 <= RHI
           /\ rng RNG (shad RLO) (shlen (RHI - RLO)) /\ wr_at asegs m (shad RLO) (shlen (RHI - RLO));
  (* [comment removed for export] *)
  AI_block_bounds : forall L RNG st LB m b,
      AHEAP L RNG st LB m -> In b LB -> AIMG_HI <= ab_addr b /\ 0 <= ab_size b /\ ab_addr b + ab_size b <= ATOP;
  AI_blocks_disjoint : forall L RNG st LB m b1 b2,
      AHEAP L RNG st LB m -> In b1 LB -> In b2 LB -> b1 <> b2 ->
      ab_addr b1 + ab_size b1 <= ab_addr b2 \/ ab_addr b2 + ab_size b2 <= ab_addr b1;
  AI_blocks_nodup : forall L RNG st LB m, AHEAP L RNG st LB m -> List.NoDup LB;
  AI_hb_ids : forall L RNG st LB m, AHEAP L RNG st LB m -> List.NoDup (hb_ids LB);   (* [comment removed for export] *)
  AI_layout : forall L RNG st LB m, AHEAP L RNG st LB m ->
      al_bot L + 0x800000 = al_top L /\ al_top L mod 4096 = 0 /\ al_top L <= 2^47 /\ (ATOP <= al_bot L <= ATOP + 4096)
      /\ a_space_beg st = al_space_beg L /\ (length (al_U L) <= Z.to_nat AUMAX)%nat
      /\ AIMG_HI <= al_fake L /\ al_fake L + 0xb09000 <= ATOP;
  (* [comment removed for export] *)
  AI_relro : forall L RNG st LB m, AHEAP L RNG st LB m -> forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None;
  AI_rtcells : forall L RNG st LB m, AHEAP L RNG st LB m -> artcells m;
  (* [comment removed for export] *)
  AI_malloc : amalloc_stmt aci AHEAP;
  AI_free : afree_stmt aci AHEAP;
  AI_free_null : afree_null_stmt aci AHEAP
}.

(* [comment removed for export] *)
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB.
Export OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section Client.
Variable CI : list (Z * Z).     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition aclient_addr (LB : list ablock) (SP : Z) (a : Z) : Prop :=
  (SP <= a)          (* [comment removed for export] *)
  \/ in_ranges CI a
  \/ in_block LB a
  \/ (exists a', ((ATOP <= a' < 2^47) \/ in_ranges CI a' \/ in_fake LB a') /\ a = shad a').   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition atls_addr (a : Z) : Prop :=
  (ATPv + -200 <= a < ATPv + 312) \/ (exists a', ATPv + -200 <= a' < ATPv + 312 /\ a = shad a').

(* [comment removed for export] *)
Definition AIMSH_LO : Z := 0x7fffa000.
Definition AIMSH_LEN : Z := 780288.
(* [comment removed for export] *)
Definition AAHM_SZ : Z := 3727360.
Definition aextra_addr (a : Z) : Prop :=
  atls_addr a \/ (AIMSH_LO <= a < AIMSH_LO + AIMSH_LEN) \/ (AAHMv <= a < AAHMv + AAHM_SZ).

Definition aheap_pres (LB : list ablock) (SP : Z) (m m' : amem) : Prop :=
  forall a, 0 <= a < 2^64 -> aclient_addr LB SP a \/ aextra_addr a ->
    m' (wa a) = m (wa a) /\ (wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None).

#[using="Type"] Lemma aheap_pres_refl : forall LB SP m, aheap_pres LB SP m m.
Proof. intros LB SP m a _ _. auto. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma aheap_pres_of_munch : forall LB SP (W : list (Z * Z)) m m',
  munch W m m' -> wmono asegs m m' ->
  (forall a, 0 <= a < 2^64 -> aclient_addr LB SP a -> outside W a) ->
  (forall a, 0 <= a < 2^64 -> aextra_addr a -> outside W a) ->
  aheap_pres LB SP m m'.
Proof.
  intros LB SP W m m' MU WM HC HT a Ha CL. split; [| intros Hw; apply WM; exact Hw].
  apply MU. rewrite wa_unsigned by exact Ha. destruct CL as [CL|TL]; [apply HC| apply HT]; assumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tls_shadow_band : forall a', ATPv + -200 <= a' < ATPv + 312 -> 2147450880 + 512 <= shad a' /\ shad a' + 449 <= shad ATOP.
Proof.
  intros a' Ha'. pose proof atp_lin as ((TL & _) & _). pose proof ATOP_al16 as A16. unfold shad, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
  clear -Ha' TL A16. Z.div_mod_to_equations. lia.
Qed.
#[using="Type"] Lemma tls_shadow_apart : forall a' B n, ATPv + -200 <= a' < ATPv + 312 -> 0 <= n ->
  (ATPv + 312 <= B \/ (B + n <= ATPv + -200 /\ B mod 8 = 0)) -> shad a' + 1 <= shad B \/ shad B + shlen n <= shad a'.
Proof.
  intros a' B n Ha' Hn D. pose proof ATPv_pg as TPG. unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
  destruct D as [D|[D M8]]; [left; clear -Ha' Hn D TPG | right; clear -Ha' Hn D TPG M8]; Z.div_mod_to_equations; lia.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma atls_not_app : forall A B a, (B <= ATPv + -200 \/ ATPv + 312 <= A) -> (B <= 2147446784 \/ 17594333495296 <= A) -> A <= a < B -> ~ atls_addr a.
Proof.
  intros A B a D SB Ha [T|(a' & Ha' & ->)]; [clear -D Ha T; lia|].
  pose proof (tls_shadow_band a' Ha') as (S1 & S2). pose proof atop_range as AR.
  assert (SA : shad ATOP <= 17594332446720) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear -AR; Z.div_mod_to_equations; lia).
  clear -SB Ha S1 S2 SA. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma atls_outside : forall (W : list (Z * Z)) a,
  (forall A k, ATPv + -200 <= A -> A + k <= ATPv + 312 -> 0 <= k -> disjoint_from W A k) ->
  (forall a', ATPv + -200 <= a' < ATPv + 312 -> disjoint_from W (shad a') 1) ->
  atls_addr a -> outside W a.
Proof.
  intros W a TK TS [TB|(a' & Ha' & ->)].
  - eapply disjoint_outside; [apply (TK a 1); lia| lia].
  - eapply disjoint_outside; [apply (TS a' Ha')| lia].
Qed.
#[using="Type"] Lemma aextra_outside : forall (W : list (Z * Z)) a,
  (forall A k, ATPv + -200 <= A -> A + k <= ATPv + 312 -> 0 <= k -> disjoint_from W A k) ->
  (forall a', ATPv + -200 <= a' < ATPv + 312 -> disjoint_from W (shad a') 1) ->
  disjoint_from W AIMSH_LO AIMSH_LEN ->
  disjoint_from W AAHMv AAHM_SZ ->
  aextra_addr a -> outside W a.
Proof.
  intros W a TK TS IM AH [T|[I|H]]; [exact (atls_outside W a TK TS T)| |].
  - eapply disjoint_outside; [exact IM| exact I].
  - eapply disjoint_outside; [exact AH| exact H].
Qed.

#[using="Type"] Lemma aheap_pres_trans : forall LB SP m1 m2 m3,
  aheap_pres LB SP m1 m2 -> aheap_pres LB SP m2 m3 -> aheap_pres LB SP m1 m3.
Proof.
  intros LB SP m1 m2 m3 H1 H2 a Ha Hc. destruct (H1 a Ha Hc) as [E1 W1]. destruct (H2 a Ha Hc) as [E2 W2].
  split; [congruence| auto].
Qed.

#[using="Type"] Lemma aheap_pres_weaken : forall LB LB' SP SP' m m',
  aheap_pres LB SP m m' -> SP <= SP' -> (forall b, In b LB' -> In b LB) -> aheap_pres LB' SP' m m'.
Proof.
  intros LB LB' SP SP' m m' H HS HL a Ha Hc. apply H; [exact Ha|].
  destruct Hc as [Hc|HT]; [left| right; exact HT].
  destruct Hc as [Hc|[Hc|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
  - left; lia.
  - right; left; exact Hc.
  - right; right; left. exists b. split; [apply HL; exact Hb| exact Hr].
  - right; right; right. exists a'. split; [|reflexivity].
    destruct Ha' as [X|[X|(c & A & n & Hin & X)]]; [left; lia| right; left; exact X| right; right].
    exists c, A, n. split; [apply HL; exact Hin| exact X].
Qed.

(* [comment removed for export] *)
Definition aclient_app_range (LB : list ablock) (SP : Z) (A n : Z) : Prop :=
  (SP <= A)          (* [comment removed for export] *)
  \/ (exists iv, In iv CI /\ fst iv <= A /\ A + n <= snd iv)
  \/ (exists cls FA fn, In (mkABlock (ABFake cls) FA fn) LB /\ FA <= A /\ A + n <= FA + fn).

(* [comment removed for export] *)
Definition aclient_range (LB : list ablock) (SP : Z) (A n : Z) : Prop :=
  aclient_app_range LB SP A n
  \/ (exists b, In b LB /\ ab_addr b <= A /\ A + n <= ab_addr b + ab_size b)
  \/ ((ATOP <= 8 * (A - ASHOFF) /\ 8 * (A - ASHOFF) + 8 * n <= 2^47)      (* [comment removed for export] *)
      \/ (exists iv, In iv CI /\ fst iv <= 8 * (A - ASHOFF) /\ 8 * (A - ASHOFF) + 8 * n <= snd iv)
      \/ (exists cls FA fn, In (mkABlock (ABFake cls) FA fn) LB /\ FA <= 8 * (A - ASHOFF) /\ 8 * (A - ASHOFF) + 8 * n <= FA + fn)).

(* [comment removed for export] *)
Definition atls_client (A n : Z) : Prop :=
  (ATPv + -200 <= A /\ A + n <= ATPv + -88) \/ (ATPv + -80 <= A /\ A + n <= ATPv + -8) \/ (ATPv + 20 <= A /\ A + n <= ATPv + 288).
(* [comment removed for export] *)
Definition aahm_client (A n : Z) : Prop := AAHMv <= A /\ A + n <= AAHMv + AAHM_SZ.

#[using="Type"] Lemma shad_unshad : forall a, shad (8 * (a - ASHOFF)) = a.
Proof. intros a. unfold shad. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mul_comm, Z.div_mul by lia. lia. Qed.

#[using="Type"] Lemma aclient_range_addr : forall LB SP A n a,
  aclient_range LB SP A n -> A <= a < A + n -> aclient_addr LB SP a.
Proof.
  intros LB SP A n a HR Ha. unfold aclient_range, aclient_app_range, aclient_addr, in_ranges, in_block, in_fake in *.
  destruct HR as [[H|[(iv & Hiv & H1 & H2)|(c & FA & fn & Hb & H1 & H2)]] | [(b & Hb & H1 & H2) | HS]].
  - left; lia.
  - right; left; exists iv; split; [exact Hiv|lia].
  - right; right; left. exists (mkABlock (ABFake c) FA fn). split; [exact Hb| cbn; lia].
  - right; right; left; exists b; split; [exact Hb|lia].
  - right; right; right. exists (8 * (a - ASHOFF)). split; [| symmetry; apply shad_unshad].
    destruct HS as [H|[(iv & Hiv & H1 & H2)|(c & FA & fn & Hb & H1 & H2)]].
    + left; lia.
    + right; left; exists iv; split; [exact Hiv|lia].
    + right; right. exists c, FA, fn. split; [exact Hb|lia].
Qed.

#[using="Type"] Lemma aheap_pres_bytes_at : forall LB SP m m' A bs,
  aheap_pres LB SP m m' -> bytes_at asegs m A bs -> aclient_range LB SP A (Z.of_nat (length bs)) ->
  bytes_at asegs m' A bs.
Proof.
  intros LB SP m m' A bs HP (H0 & H1 & HB) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(left; eapply aclient_range_addr; [exact HR|lia])) as [E _].
  rewrite E. reflexivity.
Qed.

#[using="Type"] Lemma aheap_pres_wr_at : forall LB SP m m' A n,
  aheap_pres LB SP m m' -> wr_at asegs m A n -> aclient_range LB SP A n -> wr_at asegs m' A n.
Proof.
  intros LB SP m m' A n HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(left; eapply aclient_range_addr; [exact HR|lia])) as [_ W].
  apply W. apply HW. exact Hi.
Qed.

#[using="Type"] Lemma aheap_pres_rw_cells : forall LB SP m m' A cs,
  aheap_pres LB SP m m' -> rw_cells asegs m A cs -> aclient_range LB SP A (Z.of_nat (cells_size cs)) ->
  rw_cells asegs m' A cs.
Proof.
  intros LB SP m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
  - eapply aheap_pres_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HR.
  - eapply aheap_pres_wr_at; eauto.
Qed.

#[using="Type"] Lemma aheap_pres_stk : forall LB SP m m' lo hi,
  aheap_pres LB SP m m' -> stk asegs m lo hi -> SP <= lo -> hi <= 2^47 -> stk asegs m' lo hi.
Proof.
  intros LB SP m m' lo hi HP ST HS HH. (nd_pre ST 3%nat; intros H0 H1 HW; nd_post). split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP i ltac:(lia) ltac:(left; left; lia)) as [E W]. destruct (HW i Hi) as [W0 [b Hb]].
  split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma aheap_pres_shadow : forall LB SP m m' a',
  aheap_pres LB SP m m' ->
  ((ATOP <= a' < 2^47) \/ in_ranges CI a' \/ in_fake LB a') ->
  0 <= shad a' < 2^64 ->
  m' (wa (shad a')) = m (wa (shad a')).
Proof.
  intros LB SP m m' a' HP Ha Hs. destruct (HP (shad a') Hs ltac:(left; right; right; right; exists a'; split; [exact Ha|reflexivity])) as [E _]. exact E.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma aheap_pres_tls_bytes_at : forall LB SP m m' A bs,
  aheap_pres LB SP m m' -> bytes_at asegs m A bs -> ATPv + -200 <= A -> A + Z.of_nat (length bs) <= ATPv + 312 ->
  bytes_at asegs m' A bs.
Proof.
  intros LB SP m m' A bs HP (H0 & H1 & HB) HA HE. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(right; left; left; lia)) as [E _].
  rewrite E. reflexivity.
Qed.

#[using="Type"] Lemma aheap_pres_tls_wr_at : forall LB SP m m' A n,
  aheap_pres LB SP m m' -> wr_at asegs m A n -> ATPv + -200 <= A -> A + n <= ATPv + 312 -> wr_at asegs m' A n.
Proof.
  intros LB SP m m' A n HP (H0 & H1 & HW) HA HE. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(right; left; left; lia)) as [_ W].
  apply W. apply HW. exact Hi.
Qed.

#[using="Type"] Lemma aheap_pres_tls_rw_cells : forall LB SP m m' A cs,
  aheap_pres LB SP m m' -> rw_cells asegs m A cs -> ATPv + -200 <= A -> A + Z.of_nat (cells_size cs) <= ATPv + 312 ->
  rw_cells asegs m' A cs.
Proof.
  intros LB SP m m' A cs HP [[Hwf HB] HW] HA HE. split; [split; [exact Hwf|]|].
  - eapply aheap_pres_tls_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HE.
  - eapply aheap_pres_tls_wr_at; eauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma aheap_pres_tls_shadow : forall LB SP m m' a',
  aheap_pres LB SP m m' -> ATPv + -200 <= a' < ATPv + 312 -> 0 <= shad a' < 2^64 ->
  m' (wa (shad a')) = m (wa (shad a')) /\ (wview asegs m (wa (shad a')) <> None -> wview asegs m' (wa (shad a')) <> None).
Proof. intros LB SP m m' a' HP Ha Hs. apply (HP (shad a') Hs). right. left. right. exists a'. split; [exact Ha| reflexivity]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma aheap_pres_imsh_bytes_at : forall LB SP m m' A bs,
  aheap_pres LB SP m m' -> bytes_at asegs m A bs -> AIMSH_LO <= A -> A + Z.of_nat (length bs) <= AIMSH_LO + AIMSH_LEN ->
  bytes_at asegs m' A bs.
Proof.
  intros LB SP m m' A bs HP (H0 & H1 & HB) HA HE. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(right; right; left; lia)) as [E _].
  rewrite E. reflexivity.
Qed.
#[using="Type"] Lemma aheap_pres_imsh_wr_at : forall LB SP m m' A n,
  aheap_pres LB SP m m' -> wr_at asegs m A n -> AIMSH_LO <= A -> A + n <= AIMSH_LO + AIMSH_LEN -> wr_at asegs m' A n.
Proof.
  intros LB SP m m' A n HP (H0 & H1 & HW) HA HE. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(right; right; left; lia)) as [_ W].
  apply W. apply HW. exact Hi.
Qed.
#[using="Type"] Lemma aheap_pres_imsh_rw_cells : forall LB SP m m' A cs,
  aheap_pres LB SP m m' -> rw_cells asegs m A cs -> AIMSH_LO <= A -> A + Z.of_nat (cells_size cs) <= AIMSH_LO + AIMSH_LEN ->
  rw_cells asegs m' A cs.
Proof.
  intros LB SP m m' A cs HP [[Hwf HB] HW] HA HE. split; [split; [exact Hwf|]|].
  - eapply aheap_pres_imsh_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HE.
  - eapply aheap_pres_imsh_wr_at; eauto.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma aheap_pres_imsh_byte : forall LB SP m m' a,
  aheap_pres LB SP m m' -> AIMSH_LO <= a < AIMSH_LO + AIMSH_LEN ->
  m' (wa a) = m (wa a) /\ (wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None).
Proof. intros LB SP m m' a HP Ha. apply (HP a); [unfold AIMSH_LO, AIMSH_LEN in Ha; lia|]. right. right. left. exact Ha. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma aheap_pres_ahm_bytes_at : forall LB SP m m' A bs,
  aheap_pres LB SP m m' -> bytes_at asegs m A bs -> AAHMv <= A -> A + Z.of_nat (length bs) <= AAHMv + AAHM_SZ ->
  bytes_at asegs m' A bs.
Proof.
  intros LB SP m m' A bs HP (H0 & H1 & HB) HA HE. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(right; right; right; lia)) as [E _].
  rewrite E. reflexivity.
Qed.
#[using="Type"] Lemma aheap_pres_ahm_wr_at : forall LB SP m m' A n,
  aheap_pres LB SP m m' -> wr_at asegs m A n -> AAHMv <= A -> A + n <= AAHMv + AAHM_SZ -> wr_at asegs m' A n.
Proof.
  intros LB SP m m' A n HP (H0 & H1 & HW) HA HE. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(right; right; right; lia)) as [_ W].
  apply W. apply HW. exact Hi.
Qed.
#[using="Type"] Lemma aheap_pres_ahm_rw_cells : forall LB SP m m' A cs,
  aheap_pres LB SP m m' -> rw_cells asegs m A cs -> AAHMv <= A -> A + Z.of_nat (cells_size cs) <= AAHMv + AAHM_SZ ->
  rw_cells asegs m' A cs.
Proof.
  intros LB SP m m' A cs HP [[Hwf HB] HW] HA HE. split; [split; [exact Hwf|]|].
  - eapply aheap_pres_ahm_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HE.
  - eapply aheap_pres_ahm_wr_at; eauto.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma aheap_pres_ahm_byte : forall LB SP m m' a,
  aheap_pres LB SP m m' -> 0 <= a < 2^64 -> AAHMv <= a < AAHMv + AAHM_SZ ->
  m' (wa a) = m (wa a) /\ (wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None).
Proof. intros LB SP m m' a HP R Ha. apply (HP a R). right. right. right. exact Ha. Qed.

End Client.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pcov (RESV : list (Z * Z)) (lo hi : Z) : Prop :=
  forall x, lo <= x < hi -> exists iv, In iv RESV /\ fst iv <= x < snd iv.
Definition aresv_ok (L : alayout) (RESV : list (Z * Z)) : Prop :=
     pcov RESV 0x10000 AIMG_HI                                            (* [comment removed for export] *)
  /\ pcov RESV 0x7fff7000 0x10007fff8000                                  (* [comment removed for export] *)
  /\ pcov RESV (4096 * al_V L 221%nat) (4096 * al_V L 221%nat + 137439023104)   (* [comment removed for export] *)
  /\ pcov RESV (al_ptr_array L) (al_ptr_array L + 0x800000)              (* [comment removed for export] *)
  /\ pcov RESV (al_t L) (al_t L + 4096) /\ pcov RESV (al_ctx L) (al_ctx L + 65536)
  /\ pcov RESV (al_nodes L) (al_nodes L + 1048576) /\ pcov RESV (al_store L) (al_store L + 8388608)
  /\ pcov RESV (al_fake L) (al_fake L + 11571200) /\ pcov RESV (4096 * al_V L 323%nat) (4096 * al_V L 323%nat + 4096)   (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ pcov RESV (4096 * al_V L 91%nat) (4096 * al_V L 91%nat + 0x10000)
  /\ pcov RESV (4096 * al_V L 220%nat) (4096 * al_V L 220%nat + 0x38e000)
  /\ pcov RESV (4096 * al_V L 258%nat) (4096 * al_V L 258%nat + 4096)
  /\ pcov RESV (4096 * al_V L 503%nat) (4096 * al_V L 503%nat + 4096)
  /\ pcov RESV (4096 * al_V L 584%nat) (4096 * al_V L 584%nat + 4096)
  /\ pcov RESV (ATPv + -200) (ATPv + 312).      (* [comment removed for export] *)

#[using="Type"] Lemma pcov_clear : forall RESV lo hi a n,
  pcov RESV lo hi -> avoids_all a n RESV = true -> lo < hi -> 0 < n -> a + n <= lo \/ hi <= a.
Proof.
  intros RESV lo hi a n PC AV LH N.
  destruct (Z_lt_le_dec a hi) as [L1|]; [| right; lia]. destruct (Z_lt_le_dec lo (a + n)) as [L2|]; [| left; lia]. exfalso.
  (nd_pre (PC (Z.max a lo) ltac:(lia)) 3%nat; intros iv Hin R; nd_post).
  unfold avoids_all in AV. rewrite forallb_forall in AV. specialize (AV iv Hin). unfold iv_clear in AV.
  apply orb_prop in AV. destruct AV as [AV|AV]; apply Z.leb_le in AV; lia.
Qed.

Section Stmts.
Variable CI : list (Z * Z).
(* [comment removed for export] *)
Variable AHEAP : alayout -> footprint -> astate -> list ablock -> amem -> Prop.

(* [comment removed for export] *)
Definition aunw (m : amem) (L : alayout) (RNG : footprint) (lo PC : Z) (sp s0 ra : word) (tr : list Z) : Prop :=
     (bv_unsigned sp + 16 < al_top L
      /\ uchain m (al_top L) PC (bv_unsigned sp) (bv_unsigned s0) UDEPTH tr /\ (length tr <= 28)%nat
      /\ In (PC :: bv_unsigned ra :: tr) (al_U L)
      /\ rng RNG lo (al_top L - lo))            (* [comment removed for export] *)
  \/ (al_top L <= bv_unsigned sp + 16 /\ bv_unsigned sp < 2^47 /\ In [PC] (al_U L)).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition amalloc_post (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (n lo : Z) (m : amem)
    (r : astate * option aptr) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI LB (bv_unsigned sp) m m'
    /\ match snd r with
       | None => False      (* [comment removed for export] *)
       | Some p => exists A junk,
           a0 = Z_to_bv 64 A /\ ablock_range A n
           /\ AHEAP L RNG' (fst r) (HB p A n :: LB) m'
           /\ rw_cells asegs m' A [CB (Z.to_nat n) junk]
           /\ rng RNG' A n /\ rng RNG' (shad A) (shlen (n + 7))
           /\ (is_primary n = false -> A = aptr_addr (fst r) p)
       end.

Definition amalloc_stmt : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem)
         (st : astate) (LB : list ablock) (n lo : Z) (tr : list Z) (RESV : list (Z * Z)),
  AHEAP L RNG st LB m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 n -> 1 <= n <= AREQMAX ->                    (* [comment removed for export] *)
  (* [comment removed for export] *)
  aunw m L RNG lo AMALLOC_PC sp s0 ra tr ->
  (* [comment removed for export] *)
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AMALLOC_PC ->
  bv_unsigned sp mod 16 = 0 ->
  (* [comment removed for export] *)
  rng RNG lo (bv_unsigned sp - lo) ->
  (* [comment removed for export] *)
  aresv_ok L RESV ->
  implS asegs RNG (aembed ATOP (amalloc ATOP RESV st n))
        (epostF (amalloc_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AMALLOC_SYM) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
Definition afree_post (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (p : aptr) (lo : Z) (m : amem)
    (r : astate) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI (lb_remove p LB) (bv_unsigned sp) m m'
    /\ AHEAP L RNG' r (lb_remove p LB) m'.

Definition afree_stmt : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem)
         (st : astate) (LB : list ablock) (p : aptr) (A n lo : Z) (tr : list Z),
  AHEAP L RNG st LB m -> In (HB p A n) LB ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 A ->
  aunw m L RNG lo AFREE_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  implS asegs RNG (aembed ATOP (afree st (Some p)))
        (epostF (afree_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
Definition afree_null_post (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI LB (bv_unsigned sp) m m'
    /\ AHEAP L RNG st LB m'.

Definition afree_null_stmt : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem)
         (st : astate) (LB : list ablock) (lo : Z) (tr : list Z),
  AHEAP L RNG st LB m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 0 ->
  aunw m L RNG lo AFREE_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (afree_null_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom asegs)).
End Stmts.

Record AMallocIface := mkAMallocIface {
  aci : list (Z * Z);          (* [comment removed for export] *)
  AHEAP : alayout -> footprint -> astate -> list ablock -> amem -> Prop;
  (* [comment removed for export] *)
  AI_aci_img : forall iv, In iv aci -> snd iv <= AIMG_HI;      (* [comment removed for export] *)
  AI_aci_lo : forall iv, In iv aci -> 0 <= fst iv;            (* [comment removed for export] *)
  AI_rng_mono : forall L RNG RNG' st LB m, fp_le RNG RNG' -> AHEAP L RNG st LB m -> AHEAP L RNG' st LB m;
  AI_perm : forall L RNG st LB LB' m, Permutation.Permutation LB LB' -> AHEAP L RNG st LB m -> AHEAP L RNG st LB' m;
  AI_frame : forall L RNG st LB m m' (W : list ivl),
      AHEAP L RNG st LB m -> munch W m m' -> wmono asegs m m' ->
      Forall (fun iv => aclient_range aci LB (ATOP + 4096) (fst iv) (snd iv - fst iv) \/ atls_client (fst iv) (snd iv - fst iv)
                        \/ aahm_client (fst iv) (snd iv - fst iv)) W ->
      AHEAP L RNG st LB m';          (* [comment removed for export] *)
  (* A client write set plus the 4-byte TLS cell at ATP + 16, which is back at zero afterwards. *)
  AI_frame_lsan : forall L RNG st LB m m' (W : list ivl),
      AHEAP L RNG st LB m -> munch (W ++ [(ATP + 16, ATP + 20)]) m m' -> wmono asegs m m' ->
      Forall (fun iv => aclient_range aci LB (ATOP + 4096) (fst iv) (snd iv - fst iv) \/ atls_client (fst iv) (snd iv - fst iv)
                        \/ aahm_client (fst iv) (snd iv - fst iv)) W ->
      rw_cells asegs m' (ATP + 16) [C4 (Z_to_bv 64 0)] ->
      AHEAP L RNG st LB m';
  AI_block : forall L RNG st LB m p A n,
      AHEAP L RNG st LB m -> In (HB p A n) LB ->
      1 <= n <= AREQMAX /\                                        (* [comment removed for export] *)
      ablock_range A n /\ rng RNG A n /\ rng RNG (shad A) (shlen (n + 7)) /\ ablock_shadow m A n
      /\ wr_at asegs m A n
      /\ (exists ch, (a_live st) !! p = Some ch /\ chunk_size ch = n /\ (is_primary n = false -> A = chunk_user_beg ch))
      (* [comment removed for export] *)
      /\ exists RLO RHI, RLO mod 4096 = 0 /\ RHI mod 4096 = 0 /\ RLO + 64 <= A /\ A + n + 64 <= RHI
           /\ rng RNG (shad RLO) (shlen (RHI - RLO)) /\ wr_at asegs m (shad RLO) (shlen (RHI - RLO));
  (* [comment removed for export] *)
  AI_block_bounds : forall L RNG st LB m b,
      AHEAP L RNG st LB m -> In b LB -> AIMG_HI <= ab_addr b /\ 0 <= ab_size b /\ ab_addr b + ab_size b <= ATOP;
  AI_blocks_disjoint : forall L RNG st LB m b1 b2,
      AHEAP L RNG st LB m -> In b1 LB -> In b2 LB -> b1 <> b2 ->
      ab_addr b1 + ab_size b1 <= ab_addr b2 \/ ab_addr b2 + ab_size b2 <= ab_addr b1;
  AI_blocks_nodup : forall L RNG st LB m, AHEAP L RNG st LB m -> List.NoDup LB;
  AI_hb_ids : forall L RNG st LB m, AHEAP L RNG st LB m -> List.NoDup (hb_ids LB);   (* [comment removed for export] *)
  AI_layout : forall L RNG st LB m, AHEAP L RNG st LB m ->
      al_bot L + 0x800000 = al_top L /\ al_top L mod 4096 = 0 /\ al_top L <= 2^47 /\ (ATOP <= al_bot L <= ATOP + 4096)
      /\ a_space_beg st = al_space_beg L /\ (length (al_U L) <= Z.to_nat AUMAX)%nat
      /\ AIMG_HI <= al_fake L /\ al_fake L + 0xb09000 <= ATOP;
  (* [comment removed for export] *)
  AI_relro : forall L RNG st LB m, AHEAP L RNG st LB m -> forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None;
  AI_rtcells : forall L RNG st LB m, AHEAP L RNG st LB m -> artcells m;
  (* [comment removed for export] *)
  AI_malloc : amalloc_stmt aci AHEAP;
  AI_free : afree_stmt aci AHEAP;
  AI_free_null : afree_null_stmt aci AHEAP
}.

(* [comment removed for export] *)
End CANSEC1.
End TwB.
