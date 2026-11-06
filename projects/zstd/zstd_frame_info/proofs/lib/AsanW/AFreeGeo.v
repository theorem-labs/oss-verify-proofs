(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import ExecF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg ABase ARep ARepQ ARepFrame ALayout AHeapP AModelFacts.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Section Slot.
Variables (L : alayout) (st : astate) (X : aconc) (c k : Z).
Hypothesis ALO : alayout_ok L.
Hypothesis WF : awf L st X.
Hypothesis HC : 1 <= c < K_NUM_CLASSES.
Hypothesis KR : 0 <= k < ndist st c.

Let S := size_of_class c.
Let AB := aslot_addr L c k.

#[using="X ALO WF HC KR"] Lemma slot_geo :
     16 <= S <= 65536 /\ S mod 16 = 0 /\ AB mod 16 = 0
  /\ aregion L c <= AB /\ AB + S <= aregion L c + c_allocated_user (get_cls st c)
  /\ c_allocated_user (get_cls st c) <= c_mapped_user (get_cls st c) /\ c_mapped_user (get_cls st c) <= K_FREEARR_OFF
  /\ al_space_beg L <= AB /\ AB + S <= al_space_beg L + K_SPACE_SIZE
  /\ 0x10007fff8000 <= AB /\ AB + S <= ATOP
  /\ aregion L c mod 8 = 0 /\ c_mapped_user (get_cls st c) mod 8 = 0.
Proof.
  pose proof (size_of_class_facts c HC) as [S1 S2].
  destruct WF as (SBE & PAE & SAL & SLO & SHI & PERC & _).
  destruct (PERC c HC) as (A1 & A2 & A3 & A4 & _).
  Local Ltac2 Set LiaHints.tbl := fun () => "00B0>12286147471.3 26495912578.1831230612291.1840195879397.1842759597720.1844418030651.1847364683017.1849358547692.185005358905.5  52492059678.2554568885446.1854946959492.1865978943657.1867129717870.189132738077.18 9188870684.18 941664721.18  9696685615.25 00000400800<00@00D00H00Y00]00e00i01401;01?01L01R01V01Z01eS2HCS2G1S2G2S2S1S2S2S2R8S2A12A22G23SP22RSS2A1S3SAL2A4S2A1S2G13SP12RSS2G12RSS2R8S2A12A22G22RSS4AL16S2A2S2S1S2S13SLO2A1".
pose proof (slot_in_region L st c k ltac:(fold S; lia) ltac:(lia) KR) as (G1 & G2 & G3).
  pose proof (slot_aligned L c k SAL HC) as AL16.
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  assert (R8 : aregion L c mod 8 = 0 /\ c_mapped_user (get_cls st c) mod 8 = 0).
  { generalize SAL A4. clear. unfold aregion, K_REGION, K_USER_MAP, K_ALIGN. intros. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  assert (RS : al_space_beg L <= aregion L c /\ aregion L c + K_FREEARR_OFF <= al_space_beg L + K_SPACE_SIZE).
  { generalize HC. clear. unfold aregion, K_REGION, K_FREEARR_OFF, K_SPACE_SIZE, K_NUM_CLASSES. change (2^37) with 137438953472. change (2^32) with 4294967296. intros. lia. }
  subst S AB. generalize S1 S2 A1 A2 G1 G2 G3 AL16 SP1 SP2 R8 RS. clear. unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_FREEARR_OFF. intros. repeat split; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="rc st X ALO WF HC KR"] Lemma slot_sep_objects :
     (al_t L + 4096 <= AB \/ AB + S <= al_t L) /\ (al_ctx L + 65536 <= AB \/ AB + S <= al_ctx L)
  /\ (al_nodes L + 1048576 <= AB \/ AB + S <= al_nodes L) /\ (al_store L + 8388608 <= AB \/ AB + S <= al_store L)
  /\ (al_fake L + 11571200 <= AB \/ AB + S <= al_fake L).
Proof.
  pose proof slot_geo as (S1 & _ & _ & _ & _ & _ & _ & G7 & G8 & _).
  Local Ltac2 Set LiaHints.tbl := fun () => "0010=9690175007.15000004S2S1".
exact (alayout_slot_disj L AB S ALO G7 G8 ltac:(lia)).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="rc X ALO WF HC KR"] Lemma slot_rng : forall RNG, arng L RNG st -> rng RNG AB S /\ rng RNG (shad AB) (shlen S).
Proof.
  intros RNG (_ & _ & _ & _ & _ & _ & _ & _ & _ & RC & _). destruct (RC c HC) as (R1 & R2 & _).
  pose proof slot_geo as (S1 & S2 & AL & G1 & G2 & G3 & G4 & _ & _ & _ & _ & R8 & M8).
  split.
  - Local Ltac2 Set LiaHints.tbl := fun () => "0040>14847261774.6 18721193045.2545392738668.2547826094970.1200000700D00H00US2G12R8S2S12G12G22G3S2G1S2G22G32R82M8".
eapply rng_sub; [exact R1| lia| lia].
  - eapply rng_sub; [exact R2| |].
    + rewrite !shad_div. generalize G1 R8. clear. intros. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
    + rewrite !shad_div, !shlen_div. generalize G1 G2 G3 R8 M8 S1. clear. intros. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Slot.

(* [comment removed for export] *)
#[using="Type"] Lemma slots_sep_any : forall L st X c1 k1 c2 k2,
  alayout_ok L -> awf L st X -> 1 <= c1 < K_NUM_CLASSES -> 1 <= c2 < K_NUM_CLASSES ->
  0 <= k1 < ndist st c1 -> 0 <= k2 < ndist st c2 -> (c1 <> c2 \/ k1 <> k2) ->
  aslot_addr L c1 k1 + size_of_class c1 <= aslot_addr L c2 k2 \/ aslot_addr L c2 k2 + size_of_class c2 <= aslot_addr L c1 k1.
Proof.
  intros L st X c1 k1 c2 k2 ALO WF H1 H2 K1 K2 NE.
  pose proof (slot_geo L st X c1 k1 ALO WF H1 K1) as (S1 & _ & _ & G1 & G2 & G3 & G4 & _).
  pose proof (slot_geo L st X c2 k2 ALO WF H2 K2) as (T1 & _ & _ & F1 & F2 & F3 & F4 & _).
  destruct (Z.eq_dec c1 c2) as [<-|NC].
  - Local Ltac2 Set LiaHints.tbl := fun () => "0060>10641384007.183076733508.24 44706587370.244529011490.18 53446432886.248922087071.24 00000B00F00J00Y00]00aS2G12F22F32F42NC1HS2S1S2K1S2G22G32G42F11HS2NES2K2".
apply (slots_disjoint L c1 k1 k2); lia.
  - generalize S1 G1 G2 G3 G4 T1 F1 F2 F3 F4 NC. clear. unfold aregion, K_REGION, K_FREEARR_OFF. change (2^32) with 4294967296.
    intros. destruct (Z.lt_ge_cases c1 c2); [left| right]; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma rz_log_range : forall n, 0 <= rz_log n <= 7.
Proof. intros n. unfold rz_log. repeat (destruct (_ <=? _)); lia. Qed.
#[using="Type"] Lemma rz_size_facts : forall n, 0 <= n -> 16 <= rz_size n <= 2048 /\ rz_size n mod 16 = 0.
Proof.
  intros n Hn. rewrite rz_size_eq. pose proof (rz_log_range n) as R.
  Local Ltac2 Set LiaHints.tbl := fun () => "0040=59377535926.559377535926.661606304554.49072447440.4 00000400800;00>S2HiS2HiS1RS1R".
assert (E : exists i, (i <= 7)%nat /\ rz_log n = Z.of_nat i) by (exists (Z.to_nat (rz_log n)); split; lia).
  destruct E as (i & Hi & ->). do 8 (destruct i as [|i]; [cbn; lia|]). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma rounded_size_facts : forall n, 0 <= n -> n <= rounded_size n /\ 8 <= rounded_size n /\ rounded_size n mod 8 = 0 /\ rup n 8 <= rounded_size n
  /\ rounded_size n <= n + 15.
Proof.
  intros n Hn. unfold rounded_size, rup. Z.div_mod_to_equations. nia.
Qed.

Section Chunk.
Variables (L : alayout) (st : astate) (X : aconc) (c k n : Z).
Hypothesis ALO : alayout_ok L.
Hypothesis WF : awf L st X.
Hypothesis HC : 1 <= c < K_NUM_CLASSES.
Hypothesis KR : 0 <= k < ndist st c.
Hypothesis N0 : 0 <= n.
Hypothesis FIT : rounded_size n + rz_size n <= size_of_class c.
Let S := size_of_class c.
Let AB := aslot_addr L c k.
Let UB := AB + rz_size n.
Let hm := UB - 16.

#[using="st X ALO WF HC KR N0 FIT"] Lemma chunk_geo :
     hm mod 16 = 0 /\ UB mod 16 = 0 /\ AB + 16 <= UB /\ AB <= hm
  /\ 0x10007fff8000 <= hm /\ UB + rup n 8 <= AB + S /\ AB + S <= ATOP /\ hm + 16 + rup n 8 <= ATOP /\ n <= 65536 /\ n <= Q_MAX
  /\ 0x10007fff8000 <= AB /\ n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0 /\ 8 <= S - rz_size n.
Proof.
  pose proof (slot_geo L st X c k ALO WF HC KR) as (S1 & S2 & AL & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
  pose proof (rz_size_facts n N0) as [RZ1 RZ2]. pose proof (rounded_size_facts n N0) as (RS1 & RS2 & RS3 & RS4 & RS5).
  subst S AB UB hm. generalize S1 S2 AL G1 G2 G7 G8 RZ1 RZ2 RS1 RS2 RS3 RS4 RS5 FIT N0. clear. unfold Q_MAX, rup. intros. Local Ltac2 Set LiaHints.tbl := fun () => "0010>54818981033.2200000XS2S12S22AL2G72G83RZ13RZ23RS13RS23RS43FIT".
OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="rc X ALO WF HC KR N0 FIT"] Lemma chunk_shadow_geo :
     shad UB = shad AB + shlen (rz_size n) /\ 2 <= shlen (rz_size n)
  /\ shlen (rup n 8) = granules n /\ 0 <= shlen (rup n 8)
  /\ shlen (rz_size n) + granules n <= shlen S
  /\ 0x2008fff7000 <= shad AB /\ shad AB + shlen S <= 0x10007fff8000
  /\ shad (aregion L c) <= shad AB /\ shad AB + shlen S <= shad (aregion L c) + shlen (c_mapped_user (get_cls st c)).
Proof.
  pose proof (slot_geo L st X c k ALO WF HC KR) as (S1 & S2 & AL & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & R8 & M8).
  pose proof (rz_size_facts n N0) as [RZ1 RZ2]. pose proof (rounded_size_facts n N0) as (RS1 & RS2 & RS3 & RS4 & RS5).
  subst S AB UB hm. unfold granules. rewrite !shad_div, !shlen_div.
  generalize S1 S2 AL G1 G2 G3 G4 G5 G6 G7 G8 R8 M8 RZ1 RZ2 RS1 RS2 RS3 RS4 RS5 FIT N0. clear. unfold ASHOFF, rup, K_FREEARR_OFF, K_SPACE_SIZE. intros.
  Local Ltac2 Set LiaHints.tbl := fun () => "0010>20910900231.2800000cS2S22AL2G12G22G32G72G82R82M83RZ13RZ23RS13RS33FIT2N0".
OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Chunk.
End CANSEC1.
