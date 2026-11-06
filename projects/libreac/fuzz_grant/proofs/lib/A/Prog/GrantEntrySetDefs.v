(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySetDefs), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/AC8j.v. *)
(* The set loop of fuzz_grant's entry function LLVMFuzzerTestOneInput on the ASan build
   (the slots 0x80aa4 .. 0x80cd0, GP_set .. GP_unset0, and the error slots they branch
   to): the cuts inside one turn, the symbolic states the turn's pieces run on, and the
   facts every piece uses. GrantEntrySet.v composes the pieces into ge_set.

   One turn of `for (i = 0; i < nset; i++)` (fuzz/fuzz_grant.c:201-230) reads the three
   bytes of a cell (channel, parameter, value; a short input reads 0 for the bytes it
   lacks), calls reac_headamp_tx_set, and checks: for a parameter of 3 or more that
   reac_headamp_tx_effective and reac_headamp_default both answer 0; that the answer of
   the set is 0 exactly when the channel is below 48 and the value is legal; and after an
   accepted set that reac_headamp_tx_effective gives back the value. It then stores 1 in
   was_set[ch][param] and the value in set_to[ch][param] of this function's own frame.

   The turn is cut after each call it makes (a semantic cut, as GrantEntryDefs.v cuts the
   phases), so that each piece builds its own symbolic state:
     GIn n ─ HEAD ─> GA0 | GA1 | GA2   (the returns of reac_headamp_tx_set at 0x80b0c,
                                        0x80bb8, 0x80b58: the cell had 0, 1, 2+ bytes)
     GA0 | GA1 | GA2 ─> GE2 (accepted: the return of reac_headamp_tx_effective at
                             0x80c24) | G78 (refused, 0x80c78)
     GE2 ─> G78 (the two stores, seg_e2)   G78 ─> GIn (n - 1) | GI_unset0 (seg78).
   The pieces are stated as `seg_*_stmt` below. The loop is an induction on the turns
   left, which s11 holds. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI16 YC5d YM05 YG0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal GrantSyms GrantList GrantPa GrantPaLib GrantBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import YC1g YC1h YC85 YC88 GrantFrame.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import GrantEntryDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import HeadampTxEffective HeadampDefault.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require
GrantSlotPlan SlotNeeds_c SegSetModel HeadampSched reac_headamp_tx_set_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Lemma mod16_8 : forall x, x mod 16 = 0 -> x mod 8 = 0.
Proof.
  intros x H. rewrite (Z.div_mod x 16) by lia. rewrite H, Z.add_0_r.
  replace (16 * (x / 16)) with ((2 * (x / 16)) * 8) by lia. apply Z_mod_mult.
Qed.
Lemma mod_sub16 : forall a b, a mod 32 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof.
  intros a b Ha Hb. rewrite (Z.div_mod a 32), (Z.div_mod b 16) by lia. rewrite Ha, Hb, !Z.add_0_r.
  replace (32 * (a / 32) - 16 * (b / 16)) with ((2 * (a / 32) - b / 16) * 16) by lia. apply Z_mod_mult.
Qed.

Ltac splits := repeat match goal with |- _ /\ _ => split end.
Ltac gshow := match goal with |- ?g => idtac "GOAL:" g end.

(* The shadow offset as the loop loads it from slot 152, and the band of the shadow. *)
Definition GSB : Z := 0x7fff8000.
Definition GBx : sv := SLit GSB.
Definition GBspan : Z * Z := (GSB, GSB + 2 ^ 44 - 1).
Lemma GSB_SHADOW_OFF : GSB = SHADOW_OFF.
Proof. reflexivity. Qed.

(* ---- the model of one turn, over the input bytes ---- *)
Section m.
Variable pl : list byte.
Definition gpos (i : nat) : nat := snd (GrantSlotPlan.cells_upto pl i).
Definition gcell (i : nat) : Z * Z * Z := fst (SegSetModel.cell_rd pl (gpos i)).
Definition gc (i : nat) : Z := fst (fst (gcell i)).
Definition gq (i : nat) : Z := snd (fst (gcell i)).
Definition gv (i : nat) : Z := snd (gcell i).
Definition gTi (i : nat) : list byte := fst (fst (GrantSlotPlan.tables_at pl i)).
Definition gwsi (i : nat) : list byte := snd (fst (GrantSlotPlan.tables_at pl i)).
Definition gsti (i : nat) : list byte := snd (GrantSlotPlan.tables_at pl i).
Definition gacc (i : nat) : bool := (gc i <? 48) && legalb (gq i) (gv i).
End m.

Lemma gtables_eta : forall pl i, GrantSlotPlan.tables_at pl i = (gTi pl i, gwsi pl i, gsti pl i).
Proof. intros pl i. unfold gTi, gwsi, gsti. destruct (GrantSlotPlan.tables_at pl i) as [[a b] c]. reflexivity. Qed.

Lemma gtables_inv : forall pl i,
  length (gTi pl i) = 460%nat /\ length (gwsi pl i) = 144%nat /\ length (gsti pl i) = 144%nat /\
  SlotNeeds_c.I1 (gTi pl i) /\ GrantSlotPlan.Hrel (gTi pl i) (gwsi pl i) (gsti pl i).
Proof.
  intros pl i. pose proof (SegSetModel.tables_at_inv pl i) as H. rewrite gtables_eta in H. exact H.
Qed.

Lemma gcell_ok : forall pl i, 0 <= gc pl i < 256 /\ 0 <= gq pl i < 256 /\ 0 <= gv pl i < 256.
Proof.
  intros pl i. pose proof (SegSetModel.cell_rd_ok pl (gpos pl i)) as H.
  unfold gc, gq, gv, gcell. destruct (fst (SegSetModel.cell_rd pl (gpos pl i))) as [[c q] v]. exact H.
Qed.

Lemma gpos_S : forall pl i, gpos pl (S i) = snd (SegSetModel.cell_rd pl (gpos pl i)).
Proof. intros pl i. unfold gpos. apply SegSetModel.pos_S. Qed.

Lemma gpos_le : forall pl i, (gpos pl i <= length pl)%nat.
Proof. intros pl i. unfold gpos. apply SegSetModel.cells_upto_le. Qed.

(* The tables one turn leaves: the set cell when the set is accepted, else the same. *)
Lemma gtables_S : forall pl i,
  gTi pl (S i) = (if gacc pl i then reac_headamp_tx_set_c.set_T (gTi pl i) (gc pl i) (gq pl i) (gv pl i) else gTi pl i) /\
  gwsi pl (S i) = (if gacc pl i then GrantSlotPlan.ws_put (gwsi pl i) (gc pl i) (gq pl i) 1 else gwsi pl i) /\
  gsti pl (S i) = (if gacc pl i then GrantSlotPlan.ws_put (gsti pl i) (gc pl i) (gq pl i) (gv pl i) else gsti pl i).
Proof.
  intros pl i. pose proof (SegSetModel.tables_at_S pl i) as E.
  rewrite (gtables_eta pl (S i)), (gtables_eta pl i) in E.
  change (fst (SegSetModel.cell_rd pl (snd (GrantSlotPlan.cells_upto pl i)))) with (gcell pl i) in E.
  unfold gacc, gc, gq, gv. destruct (gcell pl i) as [[c q] v]. cbn [fst snd].
  rewrite SegSetModel.set_step_cell in E.
  destruct ((c <? 48) && legalb q v); injection E as E1 E2 E3; auto.
Qed.

(* The bytes a turn reads: three when they are there, 0 for each one past the end. *)
Lemma gcell_cases : forall pl i,
  let p := gpos pl i in
  ((p + 3 <= length pl)%nat /\ gcell pl i = (GrantSlotPlan.pbz pl p, GrantSlotPlan.pbz pl (S p), GrantSlotPlan.pbz pl (S (S p))) /\ gpos pl (S i) = S (S (S p))) \/
  (length pl = (p + 2)%nat /\ gcell pl i = (GrantSlotPlan.pbz pl p, GrantSlotPlan.pbz pl (S p), 0) /\ gpos pl (S i) = S (S p)) \/
  (length pl = (p + 1)%nat /\ gcell pl i = (GrantSlotPlan.pbz pl p, 0, 0) /\ gpos pl (S i) = S p) \/
  (length pl = p /\ gcell pl i = (0, 0, 0) /\ gpos pl (S i) = p).
Proof.
  intros pl i p. pose proof (gpos_le pl i) as Hle. fold p in Hle. unfold gcell. rewrite gpos_S. fold p.
  destruct (Nat.le_gt_cases (p + 3) (length pl)) as [H3|H3].
  - left. rewrite (SegSetModel.cell_rd_3 pl p H3). auto.
  - destruct (Nat.eq_dec (length pl) (p + 2)) as [H2|H2].
    + right; left. rewrite (SegSetModel.cell_rd_2 pl p H2). auto.
    + destruct (Nat.eq_dec (length pl) (p + 1)) as [H1|H1].
      * right; right; left. rewrite (SegSetModel.cell_rd_1 pl p H1). auto.
      * right; right; right. assert (length pl = p) by lia.
        rewrite (SegSetModel.cell_rd_0 pl p ltac:(lia)). auto.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.

(* ---- the state at the cuts of a turn ---- *)

(* The machine part every cut of the turn shares. *)
Definition gmach (cx : ecx) (ms3 : machine_state) (pc : Z) : Prop :=
  ms_pc_val ms3 = w64 (BASE + pc) /\ ms_resv ms3 = None /\ ms_svc_pending ms3 = None /\
  ms_rom ms3 = seg_rom SEGS /\ ms_fregs ms3 = fp_regs /\ ms_fcsr ms3 = fp_csr /\ gregs cx ms3.

(* The bytes of the table's fields (all but the padding 438, 439, 451), as gtab has them. *)
Definition gtabb (W3 : world SEGS) (ms3 : machine_state) (t : Z) (T : list byte) : Prop :=
  forall i, 0 <= i < 460 -> i <> 438 -> i <> 439 -> i <> 451 ->
    aview SEGS (w_H W3) (ms_mem ms3) (t + i) = Some (tb T i).

(* The memory the turn keeps or changes: the saved registers, the frame's shadow and
   flag, the input, the spill slots (slot 120: the bytes left), the table and the two
   arrays. *)
Definition gmem (cx : ecx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) (t : Z)
  (T ws st : list byte) (v120 : Z) : Prop :=
  gsaved cx W3 ms3 /\ gshadow cx fp W3 ms3 GSH_tables /\
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (gF cx fp + 1016) = Some (gFL cx fp) /\
  garr8 SEGS (mrestrict (w_H W3) (ms_mem ms3)) (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) /\
  gslots_mid cx fp W3 ms3 /\ gslot cx W3 ms3 64 (GrantSlotPlan.h_in (GrantSlotPlan.header (c_pl cx))) /\
  gslot cx W3 ms3 120 v120 /\ gtabb W3 ms3 t T /\
  gfarr cx fp W3 ms3 GO_WAS ws /\ gfarr cx fp W3 ms3 GO_SET st.

(* What every cut of turn i (with n turns left after it) holds. *)
Definition gcore (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (ms3 : machine_state)
  (pc : Z) (n i : nat) (t : Z) : Prop :=
  gmach cx ms3 pc /\ k <= 1 /\ acc <= GE_A1 MT /\ gblk1 B cx ly3 S3 t /\ 0 < t /\ c_n cx < 2 ^ 26 /\
  GrantSlotPlan.nset (c_pl cx) = Z.of_nat i + Z.of_nat (S n) /\
  getr (ms_regs ms3) 19 = w64 (gF cx fp) /\ getr (ms_regs ms3) 20 = w64 t /\
  getr (ms_regs ms3) 22 = w64 (gF cx fp) /\ getr (ms_regs ms3) 27 = w64 (Z.of_nat (S n)).

(* GI_set with n + 1 turns left (nset is a byte, so n < 255). *)
Definition GIn (n : nat) (cx : ecx) (fp k acc : Z) ly3 S3 W3 (ms3 : machine_state) md3 : Prop :=
  GI_set B MT cx fp k acc ly3 S3 W3 ms3 md3 /\ getr (ms_regs ms3) 27 = w64 (Z.of_nat (S n)) /\ (n < 255)%nat.

(* 0x80c78: turn i is done, s11 is not yet decremented. *)
Definition G78 (n i : nat) (cx : ecx) (fp k acc : Z) ly3 S3 W3 (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t, gcore cx fp k acc ly3 S3 ms3 0x5c8 n i t /\
  gmem cx fp W3 ms3 t (gTi (c_pl cx) (S i)) (gwsi (c_pl cx) (S i)) (gsti (c_pl cx) (S i))
       (c_n cx - Z.of_nat (gpos (c_pl cx) (S i))) /\
  getr (ms_regs ms3) 21 = w64 (c_p cx + Z.of_nat (gpos (c_pl cx) (S i))).

(* ---- general facts ---- *)

Lemma gmach_mkst : forall cx ms3 pc, gmach cx ms3 pc ->
  ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + pc)) (ms_mem ms3) (seg_rom SEGS).
Proof.
  intros cx ms3 pc (Hpc & Hrv & Hsv & Hro & Hfr & Hfc & _).
  destruct ms3. cbn in *. unfold mkst. rewrite Hpc, Hrv, Hsv, Hro, Hfr, Hfc. reflexivity.
Qed.

Lemma rdword_tr : forall (rd rd' : reader) a, (forall j, 0 <= j < 8 -> rd' (a + j) = rd (a + j)) ->
  rdword rd' a = rdword rd a.
Proof.
  intros rd rd' a H. unfold rdword.
  rewrite <- (Z.add_0_r a) at 1 2. rewrite (H 0), (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia.
  rewrite Z.add_0_r. reflexivity.
Qed.

(* Every memory fact of the turn carries over to a memory whose view agrees on its bytes. *)
Lemma gmem_tr : forall cx fp W3 ms3 ms4 t T ws st v,
  (forall a, aview SEGS (w_H W3) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  gmem cx fp W3 ms3 t T ws st v -> gmem cx fp W3 ms4 t T ws st v.
Proof.
  intros cx fp W3 ms3 ms4 t T ws st v HA (Hsv & Hsh & Hfl & Hin & Hmid & H64 & H120 & HT & Hws & Hst).
  assert (RD : forall a v0, rdword (aview SEGS (w_H W3) (ms_mem ms3)) a = Some v0 ->
                 rdword (aview SEGS (w_H W3) (ms_mem ms4)) a = Some v0)
    by (intros a v0 H; rewrite (rdword_tr _ _ a (fun j _ => HA (a + j))); exact H).
  assert (GA : forall p L, garr8 SEGS (mrestrict (w_H W3) (ms_mem ms3)) p L -> garr8 SEGS (mrestrict (w_H W3) (ms_mem ms4)) p L)
    by (intros p L H; apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) (ms_mem ms3) (ms_mem ms4) p L); [intros a _; apply HA | exact H]).
  destruct Hsv as [Hra Hsv]. destruct Hmid as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8).
  unfold gmem, gsaved, gshadow, gslots_mid, gslot, gfarr, gtabb in *.
  split; [split; [apply RD, Hra | intros j Hj; apply RD, Hsv, Hj]|].
  split; [intros j Hj; rewrite HA; apply Hsh, Hj|].
  split; [apply RD, Hfl|].
  split; [apply GA, Hin|].
  split; [splits; apply RD; assumption|].
  split; [apply RD, H64|]. split; [apply RD, H120|].
  split; [intros j H1 H2 H3 H4; rewrite HA; apply HT; assumption|]. split; apply GA; assumption.
Qed.

Lemma gst_ok_mach : forall E ss (H : word -> bool) ms, st_ok_pi SEGS VAL E ss (restrict H ms) -> ss_resv ss = None ->
  ms_pc_val ms = w64 (BASE + ss_pc ss) /\ ms_resv ms = None /\ ms_svc_pending ms = None /\
  ms_rom ms = seg_rom SEGS /\ ms_fregs ms = fp_regs /\ ms_fcsr ms = fp_csr.
Proof.
  intros E ss H ms HS Hrv. unfold st_ok_pi, st_ok in HS.
  destruct HS as (H1 & H2 & H3 & H4 & H5 & H6 & _).
  cbn [restrict ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom] in *.
  unfold abs_ss, setpc in H2, H4. cbn in H2, H4. rewrite Hrv in H4. cbn in H4.
  unfold w64. splits; assumption.
Qed.


Lemma GSH_tables_len : length GSH_tables = GE_NSH.
Proof. vm_compute. reflexivity. Qed.

Lemma frame_nil_eq : forall E rs (H : word -> bool) (m m' : word -> option byte), rs = [] ->
  frame_of E rs m m' -> forall a, aview SEGS H m' a = aview SEGS H m a.
Proof.
  intros E rs H m m' -> HF a. apply aview_eq_of. unfold mrestrict.
  rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. intros (r & Hr & _). destruct Hr.
Qed.

(* The cuts of GrantEntryDefs.v, from the turn's own facts. *)
Lemma fin_unset0 : forall cx fp k acc ly3 S3 W3 ms md i t,
  gmach cx ms GP_unset0 -> k <= 1 -> acc <= GE_A1 MT -> gblk1 B cx ly3 S3 t -> 0 < t -> c_n cx < 2 ^ 26 ->
  GrantSlotPlan.nset (c_pl cx) = Z.of_nat (S i) ->
  getr (ms_regs ms) 19 = w64 (gF cx fp) -> getr (ms_regs ms) 20 = w64 t ->
  getr (ms_regs ms) 21 = w64 (c_p cx + Z.of_nat (gpos (c_pl cx) (S i))) ->
  getr (ms_regs ms) 22 = w64 (gF cx fp) ->
  gmem cx fp W3 ms t (gTi (c_pl cx) (S i)) (gwsi (c_pl cx) (S i)) (gsti (c_pl cx) (S i))
    (c_n cx - Z.of_nat (gpos (c_pl cx) (S i))) ->
  GI_unset0 B MT cx fp k acc ly3 S3 W3 ms md.
Proof.
  intros cx fp k acc ly3 S3 W3 ms md i t (Pc & Prv & Psv & Pro & Pfr & Pfc & G2 & G8 & G9 & G3 & G4) Hk Hacc Hbl Ht0 Hn Hns
    R19 R20 R21 R22 ((Hsv1 & Hsv2) & Hsh & Hfl & Hin & (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8) & H64 & H120 & HT & Hws & Hst).
  assert (Enat : Z.to_nat (GrantSlotPlan.nset (c_pl cx)) = S i) by lia.
  pose proof (SegSetModel.tables_end_inv (c_pl cx)) as (L1 & L2 & L3 & I1e & Hre).
  assert (HinT : In (t, 460) (ablocks B ly3 S3)) by (unfold gblk1 in Hbl; rewrite Hbl; apply in_or_app; right; left; reflexivity).
  exists t. unfold ge_body, gtab, gregs, gsaved, gslots_mid. unfold gtabb in HT.
  unfold GrantSlotPlan.pos_end, GrantSlotPlan.T_end, GrantSlotPlan.ws_end, GrantSlotPlan.st_end,
    GrantSlotPlan.tables_end in *. rewrite Enat in *.
  splits; try assumption; apply GSH_tables_len.
Qed.

Lemma fin_set : forall cx fp k acc ly3 S3 W3 ms md i t,
  gmach cx ms GP_set -> k <= 1 -> acc <= GE_A1 MT -> gblk1 B cx ly3 S3 t -> 0 < t -> c_n cx < 2 ^ 26 ->
  Z.of_nat i < GrantSlotPlan.nset (c_pl cx) ->
  getr (ms_regs ms) 19 = w64 (gF cx fp) -> getr (ms_regs ms) 20 = w64 t ->
  getr (ms_regs ms) 21 = w64 (c_p cx + Z.of_nat (gpos (c_pl cx) i)) ->
  getr (ms_regs ms) 22 = w64 (gF cx fp) ->
  getr (ms_regs ms) 27 = w64 (GrantSlotPlan.nset (c_pl cx) - Z.of_nat i) ->
  gmem cx fp W3 ms t (gTi (c_pl cx) i) (gwsi (c_pl cx) i) (gsti (c_pl cx) i) (c_n cx - Z.of_nat (gpos (c_pl cx) i)) ->
  GI_set B MT cx fp k acc ly3 S3 W3 ms md.
Proof.
  intros cx fp k acc ly3 S3 W3 ms md i t (Pc & Prv & Psv & Pro & Pfr & Pfc & G2 & G8 & G9 & G3 & G4) Hk Hacc Hbl Ht0 Hn Hi
    R19 R20 R21 R22 R27 ((Hsv1 & Hsv2) & Hsh & Hfl & Hin & (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8) & H64 & H120 & HT & Hws & Hst).
  pose proof (gtables_inv (c_pl cx) i) as (L1 & L2 & L3 & I1i & Hri).
  assert (HinT : In (t, 460) (ablocks B ly3 S3)) by (unfold gblk1 in Hbl; rewrite Hbl; apply in_or_app; right; left; reflexivity).
  exists i, t. rewrite gtables_eta. unfold ge_body, gtab, gregs, gsaved, gslots_mid. unfold gtabb in HT.
  splits; try assumption; apply GSH_tables_len.
Qed.

(* The turn's own facts, from GI_set. *)
Lemma of_set : forall cx fp k acc ly3 S3 W3 ms md,
  GI_set B MT cx fp k acc ly3 S3 W3 ms md -> exists i t,
  gmach cx ms GP_set /\ k <= 1 /\ acc <= GE_A1 MT /\ gblk1 B cx ly3 S3 t /\ 0 < t /\ c_n cx < 2 ^ 26 /\
  Z.of_nat i < GrantSlotPlan.nset (c_pl cx) /\
  getr (ms_regs ms) 19 = w64 (gF cx fp) /\ getr (ms_regs ms) 20 = w64 t /\
  getr (ms_regs ms) 21 = w64 (c_p cx + Z.of_nat (gpos (c_pl cx) i)) /\
  getr (ms_regs ms) 22 = w64 (gF cx fp) /\
  getr (ms_regs ms) 27 = w64 (GrantSlotPlan.nset (c_pl cx) - Z.of_nat i) /\
  gmem cx fp W3 ms t (gTi (c_pl cx) i) (gwsi (c_pl cx) i) (gsti (c_pl cx) i) (c_n cx - Z.of_nat (gpos (c_pl cx) i)).
Proof.
  intros cx fp k acc ly3 S3 W3 ms md (i & t & Hb & Hk & Hacc & Hbl & Hn & Hi & R19 & R20 & R21 & R22 & R27 &
    H120 & H64 & Hmid & HTAB).
  rewrite gtables_eta in HTAB. destruct HTAB as ((Hin & Ht0 & HL & HT) & Hws & Hst & _ & _).
  destruct Hb as (Pc & Prv & Psv & Pro & Pfr & Pfc & (G2 & G8 & G9 & G3 & G4) & (Hsv1 & Hsv2) & Hsh & Hfl & _ & Hinp).
  destruct Hmid as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8).
  exists i, t. unfold gmach, gregs, gmem, gsaved, gslots_mid, gtabb. splits; assumption.
Qed.

Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* The value of a register the run left as an atom of the entry registers. *)
Ltac rr_atom HS HE regs r R :=
  prreg HS r R; rewrite HE, Eimg_low in R by (unfold A_TEXT; lia);
  let nn := eval vm_compute in (Z.to_nat (bv_unsigned r)) in
  rewrite (ew_Ereg_nat regs _ nn r eq_refl) in R.

Ltac cur_ms HS := lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => m end.

(* ---- 0x80c78: the end of a turn ---- *)
Definition ss78 : sstate := mkSS 0x5c8 sr_atoms [] None (mkFacts [(27%nat, mkAF 1 255 0)] [] []).

Lemma seg78 : forall POST n i,
  ge_from B MT POST (GI_unset0 B MT) -> (forall n', n = S n' -> ge_from B MT POST (GIn n')) ->
  ge_from B MT POST (G78 n i).
Proof.
  intros POST n i HU HI cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO (t & HC & HM & H21).
  pose proof HC as (HMA & Hk & Hacc & Hbl & Ht0 & Hn & Hns & H19 & H20 & H22 & H27).
  pose proof HMA as (_ & _ & _ & _ & _ & _ & G2 & G8 & G9 & G3 & G4).
  pose proof (SegSetModel.rd8_range (c_pl cx) (GrantSlotPlan.h_pos (GrantSlotPlan.header (c_pl cx)))) as Hnr.
  change (fst (GrantSlotPlan.rd8 (c_pl cx) (GrantSlotPlan.h_pos (GrantSlotPlan.header (c_pl cx))))) with (GrantSlotPlan.nset (c_pl cx)) in Hnr.
  pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
  rewrite (gmach_mkst cx ms3 _ HMA).
  remember (ms_regs ms3) as regs eqn:Eregs. remember (ms_mem ms3) as mem eqn:Emem.
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (E27 : ew E 27 = w64 (Z.of_nat (S n)))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); subst regs; exact H27).
  assert (HS : st_ok_pi SEGS VAL E ss78 (restrict (w_H W3) (mkst regs (Z_to_bv 64 (BASE + 0x5c8)) mem (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold ss78. apply pa_entry_st_ok_full.
    - rewrite HE. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - constructor.
    - exact I.
    - split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E27. unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia. }
  assert (SHOK : sh_ok SEGS GBx [] E (mrestrict (w_H W3) mem)) by constructor.
  subst mem.
  paj_run_tok RUN HS HJ SHOK GBspan; [first [apply awr_ok_nil | gshow] |].
  psrr_branch_tok RUN BR HS SHOK GBspan;
    (rewrite branch_eq_U, (U_atom_off E 27 (Z.of_nat (S n)) (-1) E27), U_lit in Hc by lia).
  - apply Z.eqb_eq in Hc. assert (n = 0%nat) by lia. subst n.
    paj_run_to_tok RUNTO HS HJ SHOK GBspan 0x620; [first [apply awr_ok_nil | gshow] |].
    let msF := cur_ms HS in
    assert (HMEQ : forall a, aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem ms3) a);
    [ intros a; match goal with H1 : frame_of _ _ (ms_mem ms3) (ms_mem ?m1), H2 : frame_of _ _ (ms_mem ?m1) (ms_mem msF) |- _ =>
        rewrite (frame_nil_eq _ _ _ _ _ eq_refl H2 a), (frame_nil_eq _ _ _ _ _ eq_refl H1 a); reflexivity end
    | apply (HU cx fp k acc ly3 S3 W3 msF _ HB HJ HFR HMO) ].
    destruct (gst_ok_mach _ _ _ _ HS eq_refl) as (Pc & Prv & Psv & Pro & Pfr & Pfc). cbn [ss_pc] in Pc.
    rr_atom HS HE regs (2%bv : bv 5) R2. rr_atom HS HE regs (8%bv : bv 5) R8. rr_atom HS HE regs (9%bv : bv 5) R9.
    rr_atom HS HE regs (3%bv : bv 5) R3. rr_atom HS HE regs (4%bv : bv 5) R4.
    rr_atom HS HE regs (19%bv : bv 5) R19. rr_atom HS HE regs (20%bv : bv 5) R20.
    rr_atom HS HE regs (21%bv : bv 5) R21. rr_atom HS HE regs (22%bv : bv 5) R22.
    subst regs.
    apply (fin_unset0 cx fp k acc ly3 S3 W3 _ _ i t); try assumption.
    + unfold gmach, gregs. splits; try assumption; congruence.
    + lia.
    + congruence. + congruence. + congruence. + congruence.
    + exact (gmem_tr cx fp W3 ms3 _ t _ _ _ _ HMEQ HM).
  - apply Z.eqb_neq in Hc. destruct n as [|n']; [lia|].
    paj_run_to_tok RUNTO HS HJ SHOK GBspan 0x3f4; [first [apply awr_ok_nil | gshow] |].
    let msF := cur_ms HS in
    assert (HMEQ : forall a, aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem ms3) a);
    [ intros a; match goal with H1 : frame_of _ _ (ms_mem ms3) (ms_mem ?m1), H2 : frame_of _ _ (ms_mem ?m1) (ms_mem msF) |- _ =>
        rewrite (frame_nil_eq _ _ _ _ _ eq_refl H2 a), (frame_nil_eq _ _ _ _ _ eq_refl H1 a); reflexivity end
    | apply (HI n' eq_refl cx fp k acc ly3 S3 W3 msF _ HB HJ HFR HMO) ].
    destruct (gst_ok_mach _ _ _ _ HS eq_refl) as (Pc & Prv & Psv & Pro & Pfr & Pfc). cbn [ss_pc] in Pc.
    rr_atom HS HE regs (2%bv : bv 5) R2. rr_atom HS HE regs (8%bv : bv 5) R8. rr_atom HS HE regs (9%bv : bv 5) R9.
    rr_atom HS HE regs (3%bv : bv 5) R3. rr_atom HS HE regs (4%bv : bv 5) R4.
    rr_atom HS HE regs (19%bv : bv 5) R19. rr_atom HS HE regs (20%bv : bv 5) R20.
    rr_atom HS HE regs (21%bv : bv 5) R21. rr_atom HS HE regs (22%bv : bv 5) R22.
    prreg HS (27%bv : bv 5) R27.
    subst regs.
    let msF := cur_ms HS in
    assert (R27' : getr (ms_regs msF) 27 = w64 (Z.of_nat (S n')))
      by (rewrite R27, E27; unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia).
    split; [|split; [exact R27' | lia]].
    apply (fin_set cx fp k acc ly3 S3 W3 _ _ (S i) t); try assumption.
    + unfold gmach, gregs. splits; try assumption; congruence.
    + lia.
    + congruence. + congruence. + congruence. + congruence.
    + rewrite R27'. f_equal. lia.
    + exact (gmem_tr cx fp W3 ms3 _ t _ _ _ _ HMEQ HM).
Qed.

(* ---- where things are: the numbers every transport of the turn's memory rests on ---- *)
Lemma g_ly : forall cx fp k ly3 S3 W3 mem md,
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 mem md k ->
  ly_top ly3 = ly_top (c_ly cx) /\ (forall cid pos, frame_addr ly3 cid pos = frame_addr (c_ly cx) cid pos).
Proof.
  intros cx fp k ly3 S3 W3 mem md HJ. pose proof HJ as (_ & Hly & _).
  destruct Hly as (_ & _ & _ & _ & _ & EF & _ & _ & Etop & _).
  split; [exact Etop|]. intros cid pos. unfold frame_addr. rewrite EF. reflexivity.
Qed.

Definition glayout (cx : ecx) (fp t : Z) (ly3 : alayout) : Prop :=
  alloc_ceiling + 32768 <= spZ (c_regs cx) /\ spZ (c_regs cx) mod 16 = 0 /\ spZ (c_regs cx) <= 2 ^ 47 /\
  spZ (c_regs cx) - 320 <= c_sp1 cx <= spZ (c_regs cx) - 288 /\ c_sp1 cx mod 32 = 0 /\
  frame_addr ly3 GE_CID fp = gF cx fp /\ 4096 <= gF cx fp /\ gF cx fp + 1024 <= alloc_ceiling /\
  gF cx fp mod 64 = 0 /\ (gF cx fp + 1024 <= kLowShadowBeg \/ kHighMemBeg <= gF cx fp) /\
  gSH cx fp = SHADOW_OFF + gF cx fp / 8 /\
  4096 <= t /\ t + 460 <= alloc_ceiling /\ (t + 460 <= kLowShadowBeg \/ kHighMemBeg <= t) /\
  (t + 460 <= gF cx fp \/ gF cx fp + 1024 <= t) /\
  (0 < c_n cx -> 4096 <= c_p cx /\ c_p cx + c_n cx <= alloc_ceiling /\
     (c_p cx + c_n cx <= kLowShadowBeg \/ kHighMemBeg <= c_p cx) /\
     (c_p cx + c_n cx <= gF cx fp \/ gF cx fp + 1024 <= c_p cx) /\ (c_p cx + c_n cx <= t \/ t + 460 <= c_p cx)).

Lemma glay : forall cx fp k ly3 S3 W3 mem md t,
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 mem md k ->
  frames S3 = [(GE_CID, fp)] -> gblk1 B cx ly3 S3 t -> glayout cx fp t ly3.
Proof.
  intros cx fp k ly3 S3 W3 mem md t HB HJ HFR Hbl.
  pose proof HB as (HPRE & _ & _ & Hpn & _ & _ & _ & _ & _ & Hsp1 & _).
  pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (proj1 HJ) as HAR.
  destruct (g_ly cx fp k ly3 S3 W3 mem md HJ) as [Etop EF].
  assert (Hfin : In (GE_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
  destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem md GE_CID fp HAR Hfin) as (Hf0 & Hfc & Happ).
  destruct (frame_al64 SEGS B ly3 S3 W3 mem md GE_CID fp HAR Hfin) as (Hf64 & _).
  assert (FB : fs_frame_bytes GE_CID = 1024) by reflexivity.
  assert (EgF : frame_addr ly3 GE_CID fp = gF cx fp) by (unfold gF; apply EF).
  rewrite FB, EgF in *.
  assert (HinT : In (t, 460) (ablocks B ly3 S3)) by (unfold gblk1 in Hbl; rewrite Hbl; apply in_or_app; right; left; reflexivity).
  destruct (al_blocks _ _ LAWS ly3 S3 W3 mem md t 460 HAR HinT) as (_ & Ht4096 & Htc & Htapp & _).
  pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 mem md t 460 GE_CID fp HAR HinT Hfin) as HTF.
  change (req_size 460) with 460 in *. rewrite FB, EgF in HTF. unfold zdisjoint in HTF; cbn [fst snd] in HTF.
  assert (S1 : spZ (c_regs cx) - 320 <= c_sp1 cx <= spZ (c_regs cx) - 288).
  { rewrite Hsp1. pose proof (Z.div_mod (spZ (c_regs cx) + -288) 32 ltac:(lia)).
    pose proof (Z.mod_pos_bound (spZ (c_regs cx) + -288) 32 ltac:(lia)). lia. }
  assert (S2 : c_sp1 cx mod 32 = 0) by (rewrite Hsp1, Z.mul_comm; apply Z_mod_mult).
  unfold in_app in Happ, Htapp. unfold GE_STK in *.
  unfold glayout. splits; try lia; try assumption.
  - unfold gSH, shadow_of_addr. reflexivity.
  - intros Hn. destruct Hpn as [[Hn0 _] | [_ Hin0]]; [lia|].
    assert (HinP : In (c_p cx, c_n cx) (ablocks B ly3 S3)) by (unfold gblk1 in Hbl; rewrite Hbl; apply in_or_app; left; exact Hin0).
    destruct (al_blocks _ _ LAWS ly3 S3 W3 mem md _ _ HAR HinP) as (_ & Hp4096 & Hpc & Hpapp & _).
    pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq].
    pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 mem md _ _ GE_CID fp HAR HinP Hfin) as HPF.
    rewrite FB, EgF in HPF. unfold zdisjoint in HPF; cbn [fst snd] in HPF. unfold in_app in Hpapp.
    assert (HPT : c_p cx + c_n cx <= t \/ t + 460 <= c_p cx).
    { apply in_split in Hin0 as (l1 & l2 & El).
      pose proof (sep_blocks_pos SEGS B LAWS ly3 S3 W3 mem md (c_p cx, c_n cx) (t, 460) l1 l2 [] HAR
        ltac:(unfold gblk1 in Hbl; rewrite Hbl, El, <- app_assoc; reflexivity)) as HD.
      unfold zdisjoint, block_rng in HD; cbn [fst snd] in HD. change (req_size 460) with 460 in HD. lia. }
    splits; lia.
Qed.

(* ---- a call of a program function from the turn ---- *)

(* The call chain the callee gets: this function's frame pushed on the caller's. *)
Lemma g_chain : forall cx fp k ly3 S3 W3 mem md,
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 mem md k ->
  rdword (aview SEGS (w_H W3) mem) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)) ->
  rdword (aview SEGS (w_H W3) mem) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)) ->
  achain ly3 (aview SEGS (w_H W3) mem) (c_sp1 cx) (spZ (c_regs cx)) (gch cx).
Proof.
  intros cx fp k ly3 S3 W3 mem md HB HJ H8 H16.
  pose proof HB as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1 & _).
  pose proof HPRE as (HAR & Hret & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (g_ly cx fp k ly3 S3 W3 mem md HJ) as [Etop _].
  assert (S1 : spZ (c_regs cx) - 320 <= c_sp1 cx <= spZ (c_regs cx) - 288).
  { rewrite Hsp1. pose proof (Z.div_mod (spZ (c_regs cx) + -288) 32 ltac:(lia)).
    pose proof (Z.mod_pos_bound (spZ (c_regs cx) + -288) 32 ltac:(lia)). lia. }
  apply (achain_ly_top (c_ly cx) ly3 _ _ _ _ Etop).
  unfold gch. destruct (Z.ltb_spec (spZ (c_regs cx) + 16) (ly_top (c_ly cx))) as [Hlt | Hge].
  - apply (achain_push (c_ly cx) (aview SEGS (w_H (c_W cx)) (c_mem cx)) (aview SEGS (w_H W3) mem)
        (spZ (c_regs cx)) (s0Z (c_regs cx)) (raZ (c_regs cx)) [] (c_sp1 cx) Hch).
    all: first [ lia | exact H8 | exact H16 | (apply mod16_8; exact Hal16)
               | (intros a Ha; exact (aview_above_of_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ a Ha)) | gshow ].
  - left. split; [right; left; lia | reflexivity].
Qed.

(* A call: the callee's contract, at this function's sp (s1) with the return address
   BASE + retk, gives back the journal of the whole body and the callee's own. *)
Lemma gcall : forall (STK1 : Z) (FP1 : list (Z * Z))
    (Q : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
    (pcf : word) (retk : Z) (POST : ecx -> world SEGS -> config -> Prop) cx fp k ly3 S3 W3 (regs : bvmap 5 word) mem md,
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 mem md k ->
  getr regs 2 = w64 (c_sp1 cx) -> getr regs 8 = w64 (spZ (c_regs cx)) ->
  getr regs 3 = getr (c_regs cx) 3 -> getr regs 4 = getr (c_regs cx) 4 ->
  getr regs 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  rdword (aview SEGS (w_H W3) mem) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)) ->
  rdword (aview SEGS (w_H W3) mem) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)) ->
  0 <= STK1 <= 16384 ->
  (forall a, inFP FP1 a -> in_tmp_block (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) a) ->
  (afn_pre SEGS B STK1 ly3 S3 W3 regs mem md (gch cx) ->
     SRr SEGS W3 (mkCfg (mkst regs pcf mem (seg_rom SEGS)) md)
       (apost_base SEGS B STK1 FP1 regs ly3 S3 W3 mem md 0 Q)) ->
  (forall W2 ly2 S2 regs2 mem2 md2,
     ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
       [(GE_CID, fp)] ly2 S2 W2 mem2 md2 k ->
     ajournal SEGS B STK1 (c_sp1 cx) FP1 ly3 S3 W3 mem md [] ly2 S2 W2 mem2 md2 0 ->
     aregs_preserved regs regs2 -> Q ly2 S2 W2 regs2 mem2 md2 ->
     SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2) (POST cx)) ->
  SRr SEGS W3 (mkCfg (mkst regs pcf mem (seg_rom SEGS)) md) (POST cx).
Proof.
  intros STK1 FP1 Q pcf retk POST cx fp k ly3 S3 W3 regs mem md HB HJ R2 R8 R3 R4 R1 Hrk Hrk2 H8 H16 HSTK HFP HCALL HK.
  pose proof HB as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1 & _).
  pose proof HPRE as (HAR & Hret & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof pa_B_ok as HBASE. pose proof (pa_base_lo (L := grant_listing)) as HBlo.
  pose proof (proj1 alloc_ceiling_val) as AC.
  assert (S1 : spZ (c_regs cx) - 320 <= c_sp1 cx <= spZ (c_regs cx) - 288).
  { rewrite Hsp1. pose proof (Z.div_mod (spZ (c_regs cx) + -288) 32 ltac:(lia)).
    pose proof (Z.mod_pos_bound (spZ (c_regs cx) + -288) 32 ltac:(lia)). lia. }
  assert (S2 : c_sp1 cx mod 32 = 0) by (rewrite Hsp1, Z.mul_comm; apply Z_mod_mult).
  assert (Hsp : spZ regs = c_sp1 cx) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
  assert (FFS : GE_STK = 32768) by reflexivity.
  eapply SRr_bind.
  - eapply (cl_callS B LAWS W3 regs mem pcf GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(GE_CID, fp)] ly3 S3 md k STK1 FP1 0 (c_sp1 cx - spZ (c_regs cx)) (getr regs 1) (gch cx) Q HJ).
    + lia.
    + exact (mod_sub16 _ _ S2 Hal16).
    + lia.
    + lia.
    + lia.
    + rewrite R3. exact Hgp.
    + rewrite R4. exact Htp.
    + reflexivity.
    + rewrite R1. apply ret_ok_codeptr_v; lia.
    + rewrite R1, unsigned_lit_small by lia. lia.
    + unfold s0Z at 1. rewrite R8. unfold w64. rewrite unsigned_lit_small by lia.
      replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) by lia.
      exact (g_chain cx fp k ly3 S3 W3 mem md HB HJ H8 H16).
    + exact HCALL.
    + intros a Ha. right. exact (HFP a Ha).
  - cbv beta. intros W2 c2 _ (ly2 & S2' & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP & HQ).
    rewrite R1. replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) in HJc by lia.
    rewrite Z.add_0_r in HJ2. exact (HK W2 ly2 S2' regs2 mem2 md2 HJ2 HJc HP HQ).
Qed.

(* ---- reading the symbolic state back ---- *)
Lemma field_of_regionG : forall E m n b cs lo hi wlo whi od (w : N) e v,
  region_ok SEGS E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 v ->
  0 <= v < 2 ^ (8 * Z.of_N w) -> (Z.of_N w <= 8) ->
  val_mem SEGS m (b + od) (N.to_nat w) v.
Proof.
  intros E m n b cs lo hi wlo whi od w e v (_ & _ & _ & Hcs) Hn Hc He Hv Hw.
  pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
  exact (val_of_chunk_ok SEGS E m b od w e v Hck He Hv Hw).
Qed.

Lemma frame_wins : forall E rs (H : word -> bool) (m m' : word -> option byte) (P : Z -> Prop),
  frame_of E rs (mrestrict H m) (mrestrict H m') -> (forall a, in_wrange E rs a -> P a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS H m' a = aview SEGS H m a.
Proof.
  intros E rs H m m' P HF HP a Ha HnP. apply aview_eq_of. apply HF.
  rewrite unsigned_lit_small by lia. intros Hw. exact (HnP (HP a Hw)).
Qed.

Lemma GSH_tables_zero : forall j : nat, (4 <= j < 22)%nat \/ (30 <= j < 48)%nat -> nth j GSH_tables 0 = 0.
Proof.
  intros j H. do 48 (destruct j as [|j]; [vm_compute; first [reflexivity | lia] |]). lia.
Qed.

(* A byte of the frame's two arrays is marked usable. *)
Lemma g_arr_usable : forall cx fp t ly3 W3 ms off j,
  glayout cx fp t ly3 -> gshadow cx fp W3 ms GSH_tables -> (off = GO_WAS \/ off = GO_SET) -> 0 <= j < 144 ->
  range_addressable (rd_of SEGS (mrestrict (w_H W3) (ms_mem ms))) SHADOW_OFF (gF cx fp + off + j) 1.
Proof.
  intros cx fp t ly3 W3 ms off j HL Hsh Hoff Hj x Hx.
  pose proof HL as (_ & _ & _ & _ & _ & _ & L7 & _ & L9 & _ & L11 & _).
  assert (Ex : x = gF cx fp + off + j) by lia. subst x.
  assert (Hg8 : gF cx fp mod 8 = 0).
  { rewrite (Z.div_mod (gF cx fp) 64) by lia. rewrite L9, Z.add_0_r.
    replace (64 * (gF cx fp / 64)) with ((8 * (gF cx fp / 64)) * 8) by lia. apply Z_mod_mult. }
  assert (Ejj : (gF cx fp + off + j) / 8 = gF cx fp / 8 + (off + j) / 8).
  { rewrite (Z.div_mod (gF cx fp) 8) at 1 by lia. rewrite Hg8, Z.add_0_r.
    replace (8 * (gF cx fp / 8) + off + j) with ((off + j) + (gF cx fp / 8) * 8) by lia.
    rewrite Z.div_add by lia. lia. }
  assert (Hjr : 4 <= (off + j) / 8 < 22 \/ 30 <= (off + j) / 8 < 48).
  { destruct Hoff as [-> | ->]; unfold GO_WAS, GO_SET; [left | right]; split;
      first [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia]. }
  exists 0. split; [|left; reflexivity].
  rewrite <- (aview_rd_of SEGS). unfold shadow_of_addr. rewrite Ejj.
  pose proof (Hsh (Z.to_nat ((off + j) / 8))) as Hs.
  rewrite Z2Nat.id in Hs by lia. rewrite L11 in Hs.
  replace (SHADOW_OFF + (gF cx fp / 8 + (off + j) / 8)) with (SHADOW_OFF + gF cx fp / 8 + (off + j) / 8) by lia.
  rewrite Hs by (rewrite GSH_tables_len; unfold GE_NSH; lia).
  rewrite GSH_tables_zero; [reflexivity | lia].
Qed.

(* The turn's memory, after a run whose windows were slot 120 and one byte of each array. *)
Lemma gmem_win3 : forall cx fp t ly3 W3 ms ms' T ws st v ws' st' a1 a2,
  glayout cx fp t ly3 -> c_n cx < 2 ^ 26 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 120 <= a < c_sp1 cx + 128 \/ a = a1 \/ a = a2) ->
     aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms) a) ->
  gF cx fp + 32 <= a1 < gF cx fp + 176 -> gF cx fp + 240 <= a2 < gF cx fp + 384 ->
  gslot cx W3 ms' 120 v -> gfarr cx fp W3 ms' GO_WAS ws' -> gfarr cx fp W3 ms' GO_SET st' ->
  gmem cx fp W3 ms t T ws st v -> gmem cx fp W3 ms' t T ws' st' v.
Proof.
  intros cx fp t ly3 W3 ms ms' T ws st v ws' st' a1 a2 HL Hn HK Ha1 Ha2 H120' Hws' Hst'
    (Hsv & Hsh & Hfl & Hin & Hmid & H64 & H120 & HT & Hws & Hst).
  pose proof HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15 & L16).
  pose proof (proj1 alloc_ceiling_val) as AC. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *.
  assert (HgF8 : 0 <= gF cx fp / 8 /\ gF cx fp / 8 + 1024 < 2 ^ 44)
    by (split; [apply Z.div_pos; lia | assert (gF cx fp / 8 < 2 ^ 44 - 1024) by (apply Z.div_lt_upper_bound; lia); lia]).
  assert (KS : forall a, c_sp1 cx <= a < 2 ^ 64 -> ~ (c_sp1 cx + 120 <= a < c_sp1 cx + 128) ->
     aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms) a)
    by (intros a Ha Hw; apply HK; [lia | intros [H|[H|H]]; [exact (Hw H) | lia | lia]]).
  assert (RDK : forall a v0, c_sp1 cx <= a -> a + 8 <= 2 ^ 64 ->
     (a + 8 <= c_sp1 cx + 120 \/ c_sp1 cx + 128 <= a) ->
     rdword (aview SEGS (w_H W3) (ms_mem ms)) a = Some v0 -> rdword (aview SEGS (w_H W3) (ms_mem ms')) a = Some v0).
  { intros a v0 H1 H2 H3 H. rewrite (rdword_tr (aview SEGS (w_H W3) (ms_mem ms)) (aview SEGS (w_H W3) (ms_mem ms')) a); [exact H|].
    intros j Hj. apply KS; lia. }
  destruct Hsv as [Hra Hsv]. destruct Hmid as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8).
  unfold gmem, gsaved, gshadow, gslots_mid, gslot, gfarr, gtabb in *.
  split; [split|].
  { apply RDK; [lia | lia | lia | exact Hra]. }
  { intros j Hj. apply RDK; [lia | lia | lia | apply Hsv, Hj]. }
  split; [intros j Hj; rewrite GSH_tables_len in Hj; unfold GE_NSH in Hj; rewrite HK; [apply Hsh; rewrite GSH_tables_len; unfold GE_NSH; exact Hj | lia | lia]|].
  split.
  { rewrite (rdword_tr (aview SEGS (w_H W3) (ms_mem ms)) (aview SEGS (w_H W3) (ms_mem ms')) (gF cx fp + 1016)); [exact Hfl|].
    intros j Hj. apply HK; lia. }
  split.
  { apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) (ms_mem ms) (ms_mem ms') (c_p cx) _); [|exact Hin].
    intros a Ha. rewrite length_map in Ha. fold (c_n cx) in Ha.
    destruct (L16 ltac:(lia)) as (P1 & P2 & P3 & P4 & P5). apply HK; lia. }
  split; [splits; apply RDK; first [lia | assumption]|].
  split; [apply RDK; [lia | lia | lia | exact H64]|]. split; [exact H120'|].
  split; [|split; assumption].
  intros j Hj H1 H2 H3. rewrite HK; [apply HT; assumption | lia | lia].
Qed.

(* One byte of an array of the frame changed. *)
Lemma gfarr_put : forall cx fp W3 ms ms' off (l : list byte) c q b,
  length l = 144%nat -> 0 <= c < 48 -> 0 <= q < 3 -> 0 <= b < 256 ->
  gfarr cx fp W3 ms off l ->
  (forall a, gF cx fp + off <= a < gF cx fp + off + 144 -> a <> gF cx fp + off + (3 * c + q) ->
     aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms) a) ->
  aview SEGS (w_H W3) (ms_mem ms') (gF cx fp + off + (3 * c + q)) = Some b ->
  gfarr cx fp W3 ms' off (GrantSlotPlan.ws_put l c q b).
Proof.
  intros cx fp W3 ms ms' off l c q b HL Hc Hq Hb HG HK Hnew. unfold gfarr in *.
  intros j Hj. rewrite length_map, SegSetModel.len_ws_put in Hj by assumption.
  assert (Enth : forall L : list byte, (j < length L)%nat -> nth j (map (fun x : byte => bv_unsigned x) L) 0 = tb L (Z.of_nat j)).
  { intros L HjL. unfold tb. rewrite Nat2Z.id. rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact HjL).
    rewrite map_nth. reflexivity. }
  rewrite Enth by (rewrite SegSetModel.len_ws_put; assumption).
  rewrite SegSetModel.tb_ws_put by (try assumption; lia).
  destruct (Z.eqb_spec (Z.of_nat j) (3 * c + q)) as [Ej | Ej].
  - rewrite <- Ej in Hnew. destruct (val_mem1_of_aview SEGS (w_H W3) (ms_mem ms') _ b Hnew) as [Hv Hr]. split; assumption.
  - destruct (HG j ltac:(rewrite length_map; lia)) as [Hv Hr]. rewrite Enth in Hv, Hr by lia.
    split; [|exact Hr].
    apply (val_mem_aview_kept_x SEGS (w_H W3) (w_H W3) (ms_mem ms) (ms_mem ms')); [|exact Hv].
    intros x Hx. cbn [Z.of_nat] in Hx. apply HK; lia.
Qed.

Lemma gsv0 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v H Hv. cbn [sv_denot]. rewrite H, unsigned_lit_small, Z.add_0_r by lia. reflexivity. Qed.

(* ---- the symbolic state of the turn's cuts ---- *)
(* The stack slots the turn reads, at s1 (x9): the bytes left (atom 32), the addresses of
   set_to and was_set (atoms 33, 34) and the shadow offset. *)
Definition R_stk : YP09.region :=
  YP09.mkRegion (Some 9%nat) 120 160 120 128
    [YP09.mkChunk 120 (CVal 8 (SOff 32 0)); YP09.mkChunk 136 (CVal 8 (SOff 33 0));
     YP09.mkChunk 144 (CVal 8 (SOff 34 0)); YP09.mkChunk 152 (CVal 8 (SLit GSB))].

Lemma R_stk_ok : forall cx fp t ly3 W3 ms3 E v120,
  glayout cx fp t ly3 ->
  (forall a, spZ (c_regs cx) - GE_STK <= a < spZ (c_regs cx) -> apresent (w_H W3) (ms_mem ms3) a) ->
  ew E 9 = w64 (c_sp1 cx) -> ew E 32 = w64 v120 -> ew E 33 = w64 (gF cx fp + GO_SET) ->
  ew E 34 = w64 (gF cx fp + GO_WAS) -> 0 <= v120 < 2 ^ 26 ->
  gslot cx W3 ms3 120 v120 -> gslots_mid cx fp W3 ms3 ->
  region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3)) R_stk.
Proof.
  intros cx fp t ly3 W3 ms3 E v120 HL HP E9 E32 E33 E34 Hv H120 (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8).
  pose proof HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & _).
  pose proof (proj1 alloc_ceiling_val) as AC. unfold GE_STK in HP.
  unfold region_ok, R_stk. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E9. unfold w64. rewrite unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split.
  { intros o Ho. apply (apresent_writable SEGS). apply HP. lia. }
  unfold gslot in *.
  repeat apply Forall_cons; try apply Forall_nil.
  - apply (chunk_ok_val SEGS E _ (c_sp1 cx) 120 8 (SOff 32 0) v120); [apply gsv0; [exact E32 | lia] | cbn; lia | cbn; lia |].
    exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ H120).
  - apply (chunk_ok_val SEGS E _ (c_sp1 cx) 136 8 (SOff 33 0) (gF cx fp + GO_SET));
      [apply gsv0; [exact E33 | unfold GO_SET; lia] | cbn; unfold GO_SET; lia | cbn; lia |].
    exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ M5).
  - apply (chunk_ok_val SEGS E _ (c_sp1 cx) 144 8 (SOff 34 0) (gF cx fp + GO_WAS));
      [apply gsv0; [exact E34 | unfold GO_WAS; lia] | cbn; unfold GO_WAS; lia | cbn; lia |].
    exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ M6).
  - apply (chunk_ok_val SEGS E _ (c_sp1 cx) 152 8 (SLit GSB) SHADOW_OFF); [reflexivity | cbn; unfold SHADOW_OFF; lia | cbn; lia |].
    exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ M7).
Qed.

(* ---- 0x80c24 .. 0x80c78: an accepted set's value read back, and the two stores ---- *)
(* The return of reac_headamp_tx_effective after an accepted set: a0 holds the value
   read back, which is the value set. *)
Definition GE2 (n i : nat) (cx : ecx) (fp k acc : Z) ly3 S3 W3 (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t, gcore cx fp k acc ly3 S3 ms3 0x574 n i t /\ gacc (c_pl cx) i = true /\
  gmem cx fp W3 ms3 t (gTi (c_pl cx) (S i)) (gwsi (c_pl cx) i) (gsti (c_pl cx) i)
       (c_n cx - Z.of_nat (gpos (c_pl cx) (S i))) /\
  getr (ms_regs ms3) 10 = w64 (gv (c_pl cx) i) /\ getr (ms_regs ms3) 18 = w64 (gc (c_pl cx) i) /\
  getr (ms_regs ms3) 23 = w64 (gq (c_pl cx) i) /\ getr (ms_regs ms3) 24 = w64 (gv (c_pl cx) i) /\
  getr (ms_regs ms3) 21 = w64 (c_p cx + Z.of_nat (gpos (c_pl cx) (S i))).

(* The two cells the turn stores into, each a one-byte region at its own atom (35 for
   was_set[ch][param], 36 for set_to[ch][param]); the addresses the code computes are
   aliased to those atoms. *)
Definition R_c1 : YP09.region := YP09.mkRegion (Some 35%nat) 0 1 0 1 [].
Definition R_c2 : YP09.region := YP09.mkRegion (Some 36%nat) 0 1 0 1 [].
Definition SV3 : sv := SAlu ALU_ADD (SAlu ALU_SLL (SOff 18 0) (SLit 1)) (SOff 18 0).
Definition XW : sv := SAlu ALU_ADD (SAlu ALU_ADD (SOff 34 0) (SOff 23 0)) SV3.
Definition XS : sv := SAlu ALU_ADD (SAlu ALU_ADD (SOff 33 0) SV3) (SOff 23 0).
Definition PTRA (al : Z) : afact := mkAF 4096 140737479966720 al.
Definition F_e2 : facts :=
  mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (18%nat, mkAF 0 47 0); (23%nat, mkAF 0 2 0);
            (24%nat, mkAF 0 255 0); (35%nat, PTRA 0); (36%nat, PTRA 0) ] []
          [ (XW, SOff 35 0); (XS, SOff 36 0) ].
(* a0 is set to s8's atom: the two are equal, which is what the check at 0x80c24 tests. *)
Definition ss_e2a : sstate := mkSS 0x574 sr_atoms [R_stk; R_c1; R_c2] None F_e2.
Definition ss_e2 : sstate := mkSS 0x574 (sr_set sr_atoms 10%bv (SOff 24 0)) [R_stk; R_c1; R_c2] None F_e2.
Definition SH_e2 : list shent := [mkSHE 35 0 1; mkSHE 36 0 1].

Lemma denot_cells : forall E b c q,
  ew E 18 = Z_to_bv 64 c -> ew E 23 = Z_to_bv 64 q -> 0 <= c < 48 -> 0 <= q < 3 ->
  0 <= b -> b + 3 * c + q < 2 ^ 64 ->
  (ew E 34 = Z_to_bv 64 b -> sv_denot E XW = Z_to_bv 64 (b + (3 * c + q))) /\
  (ew E 33 = Z_to_bv 64 b -> sv_denot E XS = Z_to_bv 64 (b + (3 * c + q))).
Proof.
  intros E b c q Hc Hq Hcr Hqr Hb Hlt.
  assert (U3 : U E SV3 = 3 * c).
  { unfold SV3. rewrite !U_SAlu. cbn [zalu_raw].
    rewrite (U_atom E 18 c Hc) by lia. rewrite U_SLit, (zcanon_id 1) by (unfold M64; lia).
    change (Z.land 1 63) with 1. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
    rewrite (zcanon_id (c * 2)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia. }
  split; intros Hb'; rewrite denot_lit_U; f_equal.
  - unfold XW. rewrite U_SAlu. rewrite U3. rewrite U_SAlu. cbn [zalu_raw].
    rewrite (U_atom E 34 b Hb'), (U_atom E 23 q Hq) by lia.
    rewrite (zcanon_id (b + q)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
  - unfold XS. rewrite U_SAlu. rewrite U_SAlu. rewrite U3. cbn [zalu_raw].
    rewrite (U_atom E 33 b Hb'), (U_atom E 23 q Hq) by lia.
    rewrite (zcanon_id (b + 3 * c)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

Ltac ewE := cbn [ew ewset Nat.eqb] in *; rewrite ?ew_ewset_other in * by lia.

(* ---- the returns of reac_headamp_tx_set ---- *)
(* Common to the three: the cut holds turn i, the table is the one the set left
   (gTi (S i): the set cell when the set is accepted), the two arrays are still those of
   turn i, and a0 is the set's answer. *)

(* 0x80b58, the return of the call at 0x80b54 (the cell had two bytes or more): s2, s7
   and s8 hold the channel, the parameter and the value (0 for a byte past the end),
   s10 the cursor past the cell, slot 120 the bytes left after it. *)
Definition GA2 (n i : nat) (cx : ecx) (fp k acc : Z) ly3 S3 W3 (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t, gcore cx fp k acc ly3 S3 ms3 0x4a8 n i t /\
  (gpos (c_pl cx) i + 2 <= length (c_pl cx))%nat /\
  gmem cx fp W3 ms3 t (gTi (c_pl cx) (S i)) (gwsi (c_pl cx) i) (gsti (c_pl cx) i)
       (c_n cx - Z.of_nat (gpos (c_pl cx) (S i))) /\
  getr (ms_regs ms3) 10 = w64 (if gacc (c_pl cx) i then 0 else -1) /\
  getr (ms_regs ms3) 18 = w64 (gc (c_pl cx) i) /\ getr (ms_regs ms3) 23 = w64 (gq (c_pl cx) i) /\
  getr (ms_regs ms3) 24 = w64 (gv (c_pl cx) i) /\
  getr (ms_regs ms3) 26 = w64 (c_p cx + Z.of_nat (gpos (c_pl cx) (S i))).

(* 0x80bb8, the return of the call at 0x80bb4 (the cell had one byte): s2 holds the
   channel, s10 the cursor past it; slot 120 still holds the bytes left before it (1). *)
Definition GA1 (n i : nat) (cx : ecx) (fp k acc : Z) ly3 S3 W3 (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t, gcore cx fp k acc ly3 S3 ms3 0x508 n i t /\
  length (c_pl cx) = (gpos (c_pl cx) i + 1)%nat /\
  gmem cx fp W3 ms3 t (gTi (c_pl cx) (S i)) (gwsi (c_pl cx) i) (gsti (c_pl cx) i)
       (c_n cx - Z.of_nat (gpos (c_pl cx) i)) /\
  getr (ms_regs ms3) 10 = w64 (if gacc (c_pl cx) i then 0 else -1) /\
  getr (ms_regs ms3) 18 = w64 (gc (c_pl cx) i) /\
  getr (ms_regs ms3) 26 = w64 (c_p cx + Z.of_nat (gpos (c_pl cx) (S i))).

(* 0x80b0c, the return of the call at 0x80b08 (no byte left): s5 is the cursor, slot 120
   holds 0. *)
Definition GA0 (n i : nat) (cx : ecx) (fp k acc : Z) ly3 S3 W3 (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t, gcore cx fp k acc ly3 S3 ms3 0x45c n i t /\
  length (c_pl cx) = gpos (c_pl cx) i /\
  gmem cx fp W3 ms3 t (gTi (c_pl cx) (S i)) (gwsi (c_pl cx) i) (gsti (c_pl cx) i)
       (c_n cx - Z.of_nat (gpos (c_pl cx) i)) /\
  getr (ms_regs ms3) 10 = w64 (if gacc (c_pl cx) i then 0 else -1) /\
  getr (ms_regs ms3) 21 = w64 (c_p cx + Z.of_nat (gpos (c_pl cx) i)).

(* ---- the pieces of a turn, as GrantEntrySet.v composes them ---- *)
(* HEAD: 0x80aa4 → the call of reac_headamp_tx_set at 0x80b08, 0x80bb4 or 0x80b54. *)
Definition seg_head_stmt : Prop := forall POST n,
  (forall i, ge_from B MT POST (GA0 n i)) -> (forall i, ge_from B MT POST (GA1 n i)) ->
  (forall i, ge_from B MT POST (GA2 n i)) -> ge_from B MT POST (GIn n).
(* GA0, GA1, GA2 → the check of the set's answer at 0x80c0c → 0x80c78 (refused) or the
   call of reac_headamp_tx_effective at 0x80c20 (accepted); GA2 first calls
   reac_headamp_tx_effective at 0x80b70 and reac_headamp_default at 0x80b7c when the
   parameter is 3 or more. *)
Definition seg_ga0_stmt : Prop := forall POST n i,
  ge_from B MT POST (G78 n i) -> ge_from B MT POST (GE2 n i) -> ge_from B MT POST (GA0 n i).
Definition seg_ga1_stmt : Prop := forall POST n i,
  ge_from B MT POST (G78 n i) -> ge_from B MT POST (GE2 n i) -> ge_from B MT POST (GA1 n i).
Definition seg_ga2_stmt : Prop := forall POST n i,
  ge_from B MT POST (G78 n i) -> ge_from B MT POST (GE2 n i) -> ge_from B MT POST (GA2 n i).

(* The call of reac_headamp_tx_effective at 0x80c20 after an accepted set, which GA0, GA1
   and GA2 all reach: at the callee's entry, with a0 a1 a2 = the table, the channel and
   the parameter and the return address BASE + 0x574, it lands in GE2. *)
Definition call_e2_stmt : Prop := forall (POST : ecx -> world SEGS -> config -> Prop) n i
    cx fp k acc ly3 S3 W3 (regs : bvmap 5 word) mem md t,
  ge_from B MT POST (GE2 n i) ->
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 mem md k ->
  frames S3 = [(GE_CID, fp)] -> mo_le MT (c_S cx) S3 acc ->
  k <= 1 -> acc <= GE_A1 MT -> gblk1 B cx ly3 S3 t -> 0 < t -> c_n cx < 2 ^ 26 ->
  GrantSlotPlan.nset (c_pl cx) = Z.of_nat i + Z.of_nat (S n) -> gacc (c_pl cx) i = true ->
  getr regs 1 = Z_to_bv 64 (BASE + 0x574) ->
  getr regs 2 = w64 (c_sp1 cx) -> getr regs 8 = w64 (spZ (c_regs cx)) -> getr regs 9 = w64 (c_sp1 cx) ->
  getr regs 3 = getr (c_regs cx) 3 -> getr regs 4 = getr (c_regs cx) 4 ->
  getr regs 10 = w64 t -> getr regs 11 = w64 (gc (c_pl cx) i) -> getr regs 12 = w64 (gq (c_pl cx) i) ->
  getr regs 18 = w64 (gc (c_pl cx) i) -> getr regs 19 = w64 (gF cx fp) -> getr regs 20 = w64 t ->
  getr regs 21 = w64 (c_p cx + Z.of_nat (gpos (c_pl cx) (S i))) -> getr regs 22 = w64 (gF cx fp) ->
  getr regs 23 = w64 (gq (c_pl cx) i) -> getr regs 24 = w64 (gv (c_pl cx) i) ->
  getr regs 27 = w64 (Z.of_nat (S n)) ->
  gmem cx fp W3 (mkst regs (Z_to_bv 64 (BASE + AF_reac_headamp_tx_effective)) mem (seg_rom SEGS)) t
    (gTi (c_pl cx) (S i)) (gwsi (c_pl cx) i) (gsti (c_pl cx) i) (c_n cx - Z.of_nat (gpos (c_pl cx) (S i))) ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_reac_headamp_tx_effective)) mem (seg_rom SEGS)) md) (POST cx).

(* ---- GE2 → G78: 0x80c24 .. 0x80c78 ---- *)
(* The check at 0x80c24 (`bne a0, s8` into 0x81a0c) is decided by the seat: a0 and s8 are
   the same atom, since GE2 holds both equal to the value set. The two stores are
   shadow-checked (0x80c48, 0x80c6c): the cells are covered by the shadow entries SH_e2,
   which g_arr_usable proves from the frame's shadow GSH_tables. *)
Lemma seg_e2 : forall POST n i, ge_from B MT POST (G78 n i) -> ge_from B MT POST (GE2 n i).
Proof.
  intros POST n i HN cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO (t & HC & HA & HM & R10 & R18 & R23 & R24 & R21).
  pose proof HC as (HMA & Hk & Hacc & Hbl & Ht0 & Hn & Hns & H19 & H20 & H22 & H27).
  pose proof HMA as (_ & _ & _ & _ & _ & _ & G2 & G8 & G9 & G3 & G4).
  pose proof (glay cx fp k ly3 S3 W3 (ms_mem ms3) md3 t HB HJ HFR Hbl) as HL.
  pose proof HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15 & L16).
  pose proof (proj1 alloc_ceiling_val) as AC.
  pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
  pose proof (gcell_ok (c_pl cx) i) as (Hc0 & Hq0 & Hv0).
  pose proof (gtables_inv (c_pl cx) i) as (LT & LW & LS & _ & _).
  pose proof (gpos_le (c_pl cx) (S i)) as Hpl.
  pose proof HA as HAcc.
  unfold gacc in HA. apply andb_true_iff in HA as [HAc HAq]. apply Z.ltb_lt in HAc.
  pose proof (SegSetModel.legalb_legal (gq (c_pl cx) i) (gv (c_pl cx) i) ltac:(lia) ltac:(lia) HAq) as Hleg.
  destruct (SegSetModel.legal_bound _ _ Hleg) as [Hq3 _].
  destruct (gtables_S (c_pl cx) i) as (_ & EW & ES). rewrite HAcc in EW, ES.
  remember (gc (c_pl cx) i) as c eqn:Ec. remember (gq (c_pl cx) i) as q eqn:Eq. remember (gv (c_pl cx) i) as v eqn:Ev.
  set (X1 := gF cx fp + GO_WAS + (3 * c + q)). set (X2 := gF cx fp + GO_SET + (3 * c + q)).
  set (v120 := c_n cx - Z.of_nat (gpos (c_pl cx) (S i))).
  assert (Hv120 : 0 <= v120 < 2 ^ 26) by (unfold v120, c_n in *; lia).
  pose proof HM as (_ & Hsh & _ & _ & Hmid & _ & H120 & _ & HWS & HST).
  pose proof (g_arr_usable cx fp t ly3 W3 ms3 GO_WAS (3 * c + q) HL Hsh (or_introl eq_refl) ltac:(lia)) as RA1.
  pose proof (g_arr_usable cx fp t ly3 W3 ms3 GO_SET (3 * c + q) HL Hsh (or_intror eq_refl) ltac:(lia)) as RA2.
  pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSP & _).
  assert (Hfin : In (GE_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
  destruct (al_frames _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 GE_CID fp HAR Hfin) as (_ & _ & HFb & _).
  rewrite L6 in HFb. change (fs_frame_bytes GE_CID) with 1024 in HFb.
  pose proof (R_stk_ok cx fp t ly3 W3 ms3) as RSTK.
  rewrite (gmach_mkst cx ms3 _ HMA).
  remember (ms_regs ms3) as regs eqn:Eregs. remember (ms_mem ms3) as mem eqn:Emem.
  remember (Eimg (Ereg regs (map (Z_to_bv 64) [v120; gF cx fp + GO_SET; gF cx fp + GO_WAS; X1; X2]))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (ER : forall (n0 : nat) (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr regs r)
    by (intros n0 r Hr; subst E; apply ew_Eimg_Ereg_nat; exact Hr).
  assert (EX : forall j, (j < 5)%nat -> ew E (32 + j) =
      nth j (map (Z_to_bv 64) [v120; gF cx fp + GO_SET; gF cx fp + GO_WAS; X1; X2]) (Z_to_bv 64 0))
    by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  assert (E9 : ew E 9 = w64 (c_sp1 cx)) by (rewrite (ER 9%nat 9%bv eq_refl); subst regs; exact G9).
  assert (E18 : ew E 18 = w64 c) by (rewrite (ER 18%nat 18%bv eq_refl); subst regs; exact R18).
  assert (E23 : ew E 23 = w64 q) by (rewrite (ER 23%nat 23%bv eq_refl); subst regs; exact R23).
  assert (E24 : ew E 24 = w64 v) by (rewrite (ER 24%nat 24%bv eq_refl); subst regs; exact R24).
  assert (E32 : ew E 32 = w64 v120) by exact (EX 0%nat ltac:(lia)).
  assert (E33 : ew E 33 = w64 (gF cx fp + GO_SET)) by exact (EX 1%nat ltac:(lia)).
  assert (E34 : ew E 34 = w64 (gF cx fp + GO_WAS)) by exact (EX 2%nat ltac:(lia)).
  assert (E35 : ew E 35 = w64 X1) by exact (EX 3%nat ltac:(lia)).
  assert (E36 : ew E 36 = w64 X2) by exact (EX 4%nat ltac:(lia)).
  unfold GO_WAS, GO_SET in *.
  assert (HS0 : st_ok_pi SEGS VAL E ss_e2a (restrict (w_H W3) (mkst regs (Z_to_bv 64 (BASE + 0x574)) mem (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold ss_e2a. apply pa_entry_st_ok_full.
    - rewrite HE. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [subst mem; apply (RSTK E v120 HL HSP E9 E32 E33 E34 Hv120 H120 Hmid)|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
        unfold region_ok, R_c1, R_c2; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
        [rewrite E35 | rewrite E36]; unfold w64; rewrite unsigned_lit_small by (unfold X1, X2; lia);
        (split; [unfold X1, X2; lia|]); (split; [unfold X1, X2; lia|]); (split; [|apply Forall_nil]);
        intros o Ho; apply (apresent_writable SEGS); subst mem;
        match goal with |- apresent _ _ ?a => apply (proj1 (HFb a ltac:(unfold X1, X2; lia))) end.
    - apply pairwise_disjoint_of_extents.
      unfold R_stk, R_c1, R_c2, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
      rewrite E9, E35, E36. unfold w64. rewrite !unsigned_lit_small by (unfold X1, X2; lia).
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold X1, X2. splits; lia.
    - unfold F_e2. split; [|split; [exact I|]].
      + cbn [f_atoms atoms_ok]. unfold afact_ok, PTRA. cbn [af_lo af_hi af_al2].
        rewrite E9, E18, E23, E24, E35, E36. unfold w64.
        rewrite !unsigned_lit_small by (unfold X1, X2; lia).
        change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
        unfold X1, X2. splits; try lia.
      + cbn [f_alias alias_ok].
        destruct (denot_cells E (gF cx fp + 32) c q E18 E23 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [DW _].
        destruct (denot_cells E (gF cx fp + 240) c q E18 E23 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [_ DS].
        split; [|split; [|exact I]].
        * rewrite (DW E34), (gsv0 E 35 X1 E35) by (unfold X1; lia). reflexivity.
        * rewrite (DS E33), (gsv0 E 36 X2 E36) by (unfold X2; lia). reflexivity. }
  assert (HS : st_ok_pi SEGS VAL E ss_e2 (restrict (w_H W3) (mkst regs (Z_to_bv 64 (BASE + 0x574)) mem (seg_rom SEGS)))).
  { apply (st_ok_pi_set_reg E ss_e2a _ (10%bv : bv 5) (SOff 24 0) HS0); [discriminate|].
    cbn [ms_regs restrict mkst]. rewrite (gsv0 E 24 v E24) by lia. subst regs. rewrite R10. reflexivity. }
  clear HS0.
  assert (SHOK : sh_ok SEGS GBx SH_e2 E (mrestrict (w_H W3) mem)).
  { unfold sh_ok, SH_e2. constructor; [|constructor; [|constructor]];
    unfold shent_ok, app_apart; cbn [she_m she_lo she_hi];
    unfold GBx; rewrite U_lit by (unfold GSB; lia);
    [rewrite (U_atom E 35 X1 E35) by (unfold X1; lia) | rewrite (U_atom E 36 X2 E36) by (unfold X2; lia)];
    rewrite Z.add_0_r; replace GSB with SHADOW_OFF by reflexivity; (split; [subst mem; assumption|]);
    intros a Ha; unfold X1, X2, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *; lia. }
  subst mem.
  paj_run_to_tok RUNTO HS HJ SHOK GBspan 0x5c8.
  - (* the run writes slot 120 and the two cells *)
    change (ss_mem ss_e2) with [R_stk; R_c1; R_c2].
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
      [reflexivity | rewrite E9; unfold w64; rewrite unsigned_lit_small by lia; lia
      | cbn [YP09.r_wlo R_stk]; unfold GE_STK; lia | cbn [YP09.r_whi R_stk]; lia |].
    eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 35%nat X1);
      [reflexivity | rewrite E35; unfold w64; apply unsigned_lit_small; unfold X1; lia | |].
    { intros a Ha. right; right; right. exists GE_CID, fp. split; [left; reflexivity|]. left.
      unfold in_zr; cbn [fst snd YP09.r_wlo YP09.r_whi R_c1 R_c2] in *. rewrite L6. change (fs_frame_bytes GE_CID) with 1024. unfold X1 in Ha. lia. }
    eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 36%nat X2);
      [reflexivity | rewrite E36; unfold w64; apply unsigned_lit_small; unfold X2; lia | |].
    { intros a Ha. right; right; right. exists GE_CID, fp. split; [left; reflexivity|]. left.
      unfold in_zr; cbn [fst snd YP09.r_wlo YP09.r_whi R_c1 R_c2] in *. rewrite L6. change (fs_frame_bytes GE_CID) with 1024. unfold X2 in Ha. lia. }
    apply awr_ok_nil.
  - (* at 0x80c78 *)
    let msF := cur_ms HS in
    assert (HWIN : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 120 <= a < c_sp1 cx + 128 \/ a = X1 \/ a = X2) ->
                   aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem ms3) a);
    [ intros a Ha Hw;
      match goal with HFr : frame_of _ _ (mrestrict _ (ms_mem ms3)) (mrestrict _ (ms_mem msF)) |- _ =>
        apply (frame_wins E _ _ _ _ (fun a => c_sp1 cx + 120 <= a < c_sp1 cx + 128 \/ a = X1 \/ a = X2) HFr); [|exact Ha | exact Hw] end;
      intros x (r & Hr & Hx); cbn [ss_mem ss_e2 In] in Hr;
      destruct Hr as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val R_stk R_c1 R_c2] in Hx;
      [rewrite E9 in Hx | rewrite E35 in Hx | rewrite E36 in Hx]; unfold w64 in Hx;
      rewrite unsigned_lit_small in Hx by (unfold X1, X2; lia); lia
    | apply (HN cx fp k acc ly3 S3 W3 msF _ HB HJ HFR HMO) ].
    destruct (gst_ok_mach _ _ _ _ HS eq_refl) as (Pc & Prv & Psv & Pro & Pfr & Pfc). cbn [ss_pc] in Pc.
    rr_atom HS HE regs (2%bv : bv 5) Q2. rr_atom HS HE regs (8%bv : bv 5) Q8. rr_atom HS HE regs (9%bv : bv 5) Q9.
    rr_atom HS HE regs (3%bv : bv 5) Q3. rr_atom HS HE regs (4%bv : bv 5) Q4.
    rr_atom HS HE regs (19%bv : bv 5) Q19. rr_atom HS HE regs (20%bv : bv 5) Q20.
    rr_atom HS HE regs (21%bv : bv 5) Q21. rr_atom HS HE regs (22%bv : bv 5) Q22.
    rr_atom HS HE regs (27%bv : bv 5) Q27.
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
      pose proof (st_ok_pi_region_nth Ex ssx (restrict Hh msx) 0 R_stk HS ltac:(vm_compute; reflexivity)) as FR0;
      pose proof (st_ok_pi_region_nth Ex ssx (restrict Hh msx) 1
        (YP09.mkRegion (Some 35%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SLit 1))]) HS ltac:(vm_compute; reflexivity)) as FR1;
      pose proof (st_ok_pi_region_nth Ex ssx (restrict Hh msx) 2
        (YP09.mkRegion (Some 36%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SOff 24 0))]) HS ltac:(vm_compute; reflexivity)) as FR2;
      assert (X9 : bv_unsigned (ew Ex 9) = c_sp1 cx)
        by (cbn [ew ewset Nat.eqb]; rewrite E9; unfold w64; apply unsigned_lit_small; lia);
      assert (X35 : bv_unsigned (ew Ex 35) = X1)
        by (cbn [ew ewset Nat.eqb]; rewrite E35; unfold w64; apply unsigned_lit_small; unfold X1; lia);
      assert (X36 : bv_unsigned (ew Ex 36) = X2)
        by (cbn [ew ewset Nat.eqb]; rewrite E36; unfold w64; apply unsigned_lit_small; unfold X2; lia);
      assert (D32 : sv_denot Ex (SOff 32 0) = Z_to_bv 64 v120)
        by (apply gsv0; [cbn [ew ewset Nat.eqb]; exact E32 | lia]);
      assert (D24 : sv_denot Ex (SOff 24 0) = Z_to_bv 64 v)
        by (apply gsv0; [cbn [ew ewset Nat.eqb]; exact E24 | lia])
    end.
    cbn [ms_mem restrict] in FR0, FR1, FR2.
    let msF := cur_ms HS in
    assert (S120 : gslot cx W3 msF 120 v120);
    [ unfold gslot; apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem msF)); [|lia];
      exact (field_of_regionG _ _ 9%nat (c_sp1 cx) _ _ _ _ _ 120 8%N (SOff 32 0) v120 FR0 X9
               ltac:(cbn; tauto) D32 ltac:(cbn; lia) ltac:(cbn; lia))
    | ].
    let msF := cur_ms HS in
    assert (C1 : aview SEGS (w_H W3) (ms_mem msF) (gF cx fp + 32 + (3 * c + q)) = Some 1);
    [ apply (aview_of_val_mem1 SEGS (w_H W3) (ms_mem msF)); [|lia];
      replace (gF cx fp + 32 + (3 * c + q)) with (X1 + 0) by (unfold X1; lia);
      exact (field_of_regionG _ _ 35%nat X1 _ _ _ _ _ 0 1%N (SLit 1) 1 FR1 X35
               ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))
    | ].
    let msF := cur_ms HS in
    assert (C2 : aview SEGS (w_H W3) (ms_mem msF) (gF cx fp + 240 + (3 * c + q)) = Some v);
    [ apply (aview_of_val_mem1 SEGS (w_H W3) (ms_mem msF)); [|lia];
      replace (gF cx fp + 240 + (3 * c + q)) with (X2 + 0) by (unfold X2; lia);
      exact (field_of_regionG _ _ 36%nat X2 _ _ _ _ _ 0 1%N (SOff 24 0) v FR2 X36
               ltac:(cbn; tauto) D24 ltac:(cbn; lia) ltac:(cbn; lia))
    | ].
    let msF := cur_ms HS in
    assert (NWS : gfarr cx fp W3 msF 32 (GrantSlotPlan.ws_put (gwsi (c_pl cx) i) c q 1));
    [ apply (gfarr_put cx fp W3 ms3 msF 32 _ c q 1 LW ltac:(lia) ltac:(lia) ltac:(lia) HWS); [|exact C1];
      intros a Ha Hne; apply HWIN; [lia | unfold X1, X2 in *; lia]
    | ].
    let msF := cur_ms HS in
    assert (NST : gfarr cx fp W3 msF 240 (GrantSlotPlan.ws_put (gsti (c_pl cx) i) c q v));
    [ apply (gfarr_put cx fp W3 ms3 msF 240 _ c q v LS ltac:(lia) ltac:(lia) ltac:(lia) HST); [|exact C2];
      intros a Ha Hne; apply HWIN; [lia | unfold X1, X2 in *; lia]
    | ].
    subst regs.
    exists t. split; [|split].
    + unfold gcore, gmach, gregs. splits; try assumption; try congruence.
    + rewrite EW, ES.
      exact (gmem_win3 cx fp t ly3 W3 ms3 _ _ _ _ _ _ _ X1 X2 HL Hn HWIN ltac:(unfold X1; lia) ltac:(unfold X2; lia) S120 NWS NST HM).
    + congruence.
Qed.

(* ---- the table as the callees' contracts speak of it ---- *)
(* The image's read-only bytes are kept since the call began. *)
Lemma garo : forall cx fp k ly3 S3 W3 mem3 md3,
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 mem3 md3 k ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W3) mem3).
Proof.
  intros cx fp k ly3 S3 W3 mem3 md3 HB HJ a Hro Ho He.
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & HRO & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
  rewrite (F3 a); [exact (HRO a Hro Ho He) | | exact Ho | exact He | apply fp_spares_closed; intros (r & Hr & _); destruct Hr].
  destruct Hro as [(s & Hs & _ & Hr) | Hgot]; [exists s; split; [exact Hs | exact Hr]|].
  exact (pa_relro_img a Hgot).
Qed.

(* The bytes LAY_TX names are the table's bytes but its three padding bytes. *)
Lemma fbyte_iff : forall i, tx_fbyte i = true <-> (0 <= i < 460 /\ i <> 438 /\ i <> 439 /\ i <> 451).
Proof.
  intros i. split.
  - intros H. pose proof (tx_fbyte_range i H) as Hr.
    split; [exact Hr|]. split; [|split]; intros ->; vm_compute in H; discriminate H.
  - intros (Hr & H1 & H2 & H3).
    assert (Hb : forallb (fun n => orb (orb (orb (Nat.eqb n 438) (Nat.eqb n 439)) (Nat.eqb n 451)) (tx_fbyte (Z.of_nat n)))
                   (seq 0 460) = true) by (vm_compute; reflexivity).
    rewrite forallb_forall in Hb.
    specialize (Hb (Z.to_nat i) (proj2 (in_seq 460 0 (Z.to_nat i)) ltac:(lia))).
    rewrite Z2Nat.id in Hb by lia.
    apply orb_prop in Hb as [Hb | Hb]; [|exact Hb]. exfalso.
    repeat (apply orb_prop in Hb as [Hb | Hb]); apply Nat.eqb_eq in Hb; lia.
Qed.

Lemma gtabb_obj : forall W3 ms3 t T,
  gtabb W3 ms3 t T -> obj_at SEGS (mrestrict (w_H W3) (ms_mem ms3)) t LAY_TX (tx_vals T).
Proof.
  intros W3 ms3 t T H4. apply (proj2 (tx_obj_bytes SEGS _ t T)).
  intros i Hi. apply fbyte_iff in Hi as (Hr & H1 & H2 & H3).
  specialize (H4 i Hr H1 H2 H3). unfold aview in H4.
  destruct (mbyte SEGS (mrestrict (w_H W3) (ms_mem ms3)) (t + i)) as [b|]; [|discriminate H4].
  cbn [option_map] in H4. injection H4 as H4. f_equal. apply bv_eq. rewrite H4. reflexivity.
Qed.

Lemma gtab_obj : forall cx ly3 S3 W3 ms3 t T,
  gtab B cx ly3 S3 W3 ms3 t T -> obj_at SEGS (mrestrict (w_H W3) (ms_mem ms3)) t LAY_TX (tx_vals T).
Proof. intros cx ly3 S3 W3 ms3 t T (_ & _ & _ & H4). exact (gtabb_obj W3 ms3 t T H4). Qed.

Lemma obj_gtabb : forall W3 ms3 t T,
  obj_at SEGS (mrestrict (w_H W3) (ms_mem ms3)) t LAY_TX (tx_vals T) -> gtabb W3 ms3 t T.
Proof.
  intros W3 ms3 t T HO i Hr H1 H2 H3.
  assert (Hf : tx_fbyte i = true) by (apply fbyte_iff; auto).
  pose proof (proj1 (tx_obj_bytes SEGS _ t T) HO i Hf) as Hm.
  unfold aview. rewrite Hm. reflexivity.
Qed.

(* ---- the turn's memory across a call that writes nothing of it ---- *)
(* The bytes the turn's facts speak about: at or above s1, the input, the frame and its
   shadow, and the table. *)
Definition gkeep_at (cx : ecx) (fp t a : Z) : Prop :=
  c_sp1 cx <= a < 2 ^ 64 \/ c_p cx <= a < c_p cx + c_n cx \/ gF cx fp <= a < gF cx fp + 1024 \/
  gSH cx fp <= a < gSH cx fp + 128 \/ t <= a < t + 460.

Lemma gmem_trK : forall cx fp t ly3 W3 ms ms' T ws st v,
  glayout cx fp t ly3 -> length ws = 144%nat -> length st = 144%nat ->
  (forall a, gkeep_at cx fp t a -> aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms) a) ->
  gmem cx fp W3 ms t T ws st v -> gmem cx fp W3 ms' t T ws st v.
Proof.
  intros cx fp t ly3 W3 ms ms' T ws st v HL Hlw Hls HK (Hsv & Hsh & Hfl & Hin & Hmid & H64 & H120 & HT & Hws & Hst).
  pose proof HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & _).
  pose proof (proj1 alloc_ceiling_val) as AC.
  assert (RDK : forall a v0, c_sp1 cx <= a -> a + 8 <= 2 ^ 64 ->
     rdword (aview SEGS (w_H W3) (ms_mem ms)) a = Some v0 -> rdword (aview SEGS (w_H W3) (ms_mem ms')) a = Some v0).
  { intros a v0 H1 H2 H. rewrite (rdword_tr (aview SEGS (w_H W3) (ms_mem ms)) (aview SEGS (w_H W3) (ms_mem ms')) a); [exact H|].
    intros j Hj. apply HK. left. lia. }
  assert (GAK : forall p L, (forall a, p <= a < p + Z.of_nat (length L) -> gkeep_at cx fp t a) ->
     garr8 SEGS (mrestrict (w_H W3) (ms_mem ms)) p L -> garr8 SEGS (mrestrict (w_H W3) (ms_mem ms')) p L).
  { intros p L Hp H. apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) (ms_mem ms) (ms_mem ms') p L); [|exact H].
    intros a Ha. apply HK, Hp, Ha. }
  destruct Hsv as [Hra Hsv]. destruct Hmid as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8).
  unfold gmem, gsaved, gshadow, gslots_mid, gslot, gfarr, gtabb in *.
  split; [split|].
  { apply RDK; [lia | lia | exact Hra]. }
  { intros j Hj. apply RDK; [lia | lia | apply Hsv, Hj]. }
  split; [intros j Hj; rewrite HK; [apply Hsh, Hj|]; rewrite GSH_tables_len in Hj; unfold GE_NSH in Hj;
    right; right; right; left; lia|].
  split.
  { rewrite (rdword_tr (aview SEGS (w_H W3) (ms_mem ms)) (aview SEGS (w_H W3) (ms_mem ms')) (gF cx fp + 1016)); [exact Hfl|].
    intros j Hj. apply HK. right; right; left. lia. }
  split.
  { apply GAK; [|exact Hin]. intros a Ha. rewrite length_map in Ha. right; left. unfold c_n. lia. }
  split; [splits; apply RDK; first [lia | assumption]|].
  split; [apply RDK; [lia | lia | exact H64]|]. split; [apply RDK; [lia | lia | exact H120]|].
  split; [intros j Hj H1 H2 H3; rewrite HK; [apply HT; assumption | right; right; right; right; lia]|].
  split; [apply GAK; [|exact Hws] | apply GAK; [|exact Hst]]; intros a Ha; rewrite length_map in Ha;
    right; right; left; unfold GO_WAS, GO_SET in *; lia.
Qed.

(* A callee that takes no frame, writes nothing of the caller's (FP = []) and leaves the
   layout and the blocks as they were keeps every byte the turn's facts speak about. *)
Lemma gkeep_call0 : forall cx fp k ly3 S3 W3 mem md STK1 mem2 md2 t,
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 mem md k ->
  frames S3 = [(GE_CID, fp)] -> gblk1 B cx ly3 S3 t -> 0 <= STK1 ->
  ajournal SEGS B STK1 (c_sp1 cx) [] ly3 S3 W3 mem md [] ly3 S3 W3 mem2 md2 0 ->
  forall a, gkeep_at cx fp t a -> aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) mem a.
Proof.
  intros cx fp k ly3 S3 W3 mem md STK1 mem2 md2 t HB HJ HFR Hbl HSTK1 HJc a Ha.
  pose proof (glay cx fp k ly3 S3 W3 mem md t HB HJ HFR Hbl) as HL.
  pose proof HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & _).
  pose proof (proj1 alloc_ceiling_val) as AC.
  pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & _ & F4 & _).
  assert (Hfin : In (GE_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
  assert (HinT : In (t, 460) (ablocks B ly3 S3)) by (unfold gblk1 in Hbl; rewrite Hbl; apply in_or_app; right; left; reflexivity).
  destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]].
  - apply F1; lia.
  - destruct HB as (_ & _ & _ & Hpn & _). destruct Hpn as [[Hn0 _] | [Hn Hin0]]; [unfold c_n in *; lia|].
    assert (HinP : In (c_p cx, c_n cx) (ablocks B ly3 S3)) by (unfold gblk1 in Hbl; rewrite Hbl; apply in_or_app; left; exact Hin0).
    pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hq].
    replace a with (c_p cx + (a - c_p cx)) by lia.
    apply (F2 (c_p cx) (c_n cx) (a - c_p cx) HinP HinP); [lia | apply inFP_nil].
  - apply (F4 GE_CID fp a Hfin); [|apply inFP_nil]. left. unfold in_zr, frame_rng. cbn [fst snd].
    rewrite L6. change (fs_frame_bytes GE_CID) with 1024. lia.
  - apply (F4 GE_CID fp a Hfin); [|apply inFP_nil]. right. unfold in_zr. cbn [fst snd].
    rewrite L6. unfold shadow_addr. change (fs_frame_bytes GE_CID / 8) with 128. rewrite <- L11. lia.
  - replace a with (t + (a - t)) by lia.
    apply (F2 t 460 (a - t) HinT HinT); [change (req_size 460) with 460; lia | apply inFP_nil].
Qed.

(* A callee whose footprint lies in the table keeps every byte of the turn's facts but
   the table's, and the table's bytes outside its footprint. *)
Lemma gkeep_callT : forall cx fp k ly3 S3 W3 mem md STK1 FP1 mem2 md2 t,
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 mem md k ->
  frames S3 = [(GE_CID, fp)] -> gblk1 B cx ly3 S3 t -> 0 <= STK1 ->
  (forall a, inFP FP1 a -> t <= a < t + 460) ->
  ajournal SEGS B STK1 (c_sp1 cx) FP1 ly3 S3 W3 mem md [] ly3 S3 W3 mem2 md2 0 ->
  forall a, gkeep_at cx fp t a -> ~ inFP FP1 a -> aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) mem a.
Proof.
  intros cx fp k ly3 S3 W3 mem md STK1 FP1 mem2 md2 t HB HJ HFR Hbl HSTK1 HFP HJc a Ha HnF.
  pose proof (glay cx fp k ly3 S3 W3 mem md t HB HJ HFR Hbl) as HL.
  pose proof HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & _).
  pose proof (proj1 alloc_ceiling_val) as AC.
  pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & _ & F4 & _).
  assert (Hfin : In (GE_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
  assert (HinT : In (t, 460) (ablocks B ly3 S3)) by (unfold gblk1 in Hbl; rewrite Hbl; apply in_or_app; right; left; reflexivity).
  destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]].
  - apply F1; lia.
  - destruct HB as (_ & _ & _ & Hpn & _). destruct Hpn as [[Hn0 _] | [Hn Hin0]]; [unfold c_n in *; lia|].
    assert (HinP : In (c_p cx, c_n cx) (ablocks B ly3 S3)) by (unfold gblk1 in Hbl; rewrite Hbl; apply in_or_app; left; exact Hin0).
    pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hq].
    replace a with (c_p cx + (a - c_p cx)) by lia.
    apply (F2 (c_p cx) (c_n cx) (a - c_p cx) HinP HinP); [lia|].
    replace (c_p cx + (a - c_p cx)) with a by lia. exact HnF.
  - apply (F4 GE_CID fp a Hfin); [|exact HnF]. left. unfold in_zr, frame_rng. cbn [fst snd].
    rewrite L6. change (fs_frame_bytes GE_CID) with 1024. lia.
  - apply (F4 GE_CID fp a Hfin); [|exact HnF]. right. unfold in_zr. cbn [fst snd].
    rewrite L6. unfold shadow_addr. change (fs_frame_bytes GE_CID / 8) with 128. rewrite <- L11. lia.
  - replace a with (t + (a - t)) by lia.
    apply (F2 t 460 (a - t) HinT HinT); [change (req_size 460) with 460; lia|].
    replace (t + (a - t)) with a by lia. exact HnF.
Qed.

(* ---- the call of reac_headamp_tx_effective at 0x80c20, which lands in GE2 ---- *)
Hypothesis EFFH : theadamp_tx_effective_spec B.

(* The check at 0x80c24 compares the value read back with the value set: GE2 holds a0 =
   the value set, by HeadampSched.eff_set_T_same (lib/Prog/HeadampSched.v:219). *)
Lemma call_e2 : call_e2_stmt.
Proof.
  intros POST n i cx fp k acc ly3 S3 W3 regs mem md t HN HB HJ HFR HMO Hk Hacc Hbl Ht0 Hn Hns HA
    R1 R2 R8 R9 R3 R4 R10 R11 R12 R18 R19 R20 R21 R22 R23 R24 R27 HM.
  pose proof (glay cx fp k ly3 S3 W3 mem md t HB HJ HFR Hbl) as HL.
  pose proof HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & _).
  pose proof (proj1 alloc_ceiling_val) as AC.
  pose proof (gcell_ok (c_pl cx) i) as (Hc0 & Hq0 & Hv0).
  pose proof (gtables_inv (c_pl cx) i) as (LT & LW & LS & _ & _).
  pose proof (gtables_inv (c_pl cx) (S i)) as (LT1 & _ & _ & _ & _).
  pose proof HA as HA'. unfold gacc in HA'. apply andb_true_iff in HA' as [HAc HAq]. apply Z.ltb_lt in HAc.
  pose proof (SegSetModel.legalb_legal (gq (c_pl cx) i) (gv (c_pl cx) i) ltac:(lia) ltac:(lia) HAq) as Hleg.
  destruct (SegSetModel.legal_bound _ _ Hleg) as [Hq3 _].
  destruct (gtables_S (c_pl cx) i) as (ET & _ & _). rewrite HA in ET.
  pose proof HM as ((Hra & Hsv) & _ & _ & _ & _ & _ & _ & HT & _).
  assert (Hs0 : rdword (aview SEGS (w_H W3) mem) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx))).
  { pose proof (Hsv 0 ltac:(lia)) as H0. replace (spZ (c_regs cx) - 16 - 8 * 0) with (spZ (c_regs cx) - 16) in H0 by lia.
    exact H0. }
  assert (HinT : In (t, TX_SIZE) (ablocks B ly3 S3)) by (unfold gblk1 in Hbl; rewrite Hbl; apply in_or_app; right; left; reflexivity).
  eapply (gcall TEFF_STK []
    (fun ly' S' W' regs' mem' md' => ly' = ly3 /\ S' = S3 /\ W' = W3 /\
       getr regs' 10 = w64 (eff (gTi (c_pl cx) (S i)) t (gc (c_pl cx) i) (gq (c_pl cx) i)) /\
       obj_at SEGS (mrestrict (w_H W3) mem') t LAY_TX (tx_vals (gTi (c_pl cx) (S i))))
    _ 0x574 POST cx fp k ly3 S3 W3 regs mem md HB HJ R2 R8 R3 R4 R1 ltac:(lia) eq_refl Hra Hs0
    ltac:(unfold TEFF_STK, ESTACK; lia) ltac:(intros a Ha; destruct (inFP_nil a Ha))).
  - intros HPRE. exact (EFFH ly3 S3 W3 regs mem md (gch cx) t (gc (c_pl cx) i) (gq (c_pl cx) i) (gTi (c_pl cx) (S i))
      HPRE R10 R11 R12 ltac:(lia) ltac:(lia) HinT LT1 (gtabb_obj W3 _ t _ HT)).
  - intros W2 ly2 S2 regs2 mem2 md2 HJ2 HJc HP (-> & -> & -> & H10 & _).
    apply (HN cx fp k acc ly3 S3 W3 (mkst regs2 (Z_to_bv 64 (BASE + 0x574)) mem2 (seg_rom SEGS)) md2 HB HJ2 HFR HMO).
    assert (P2 : getr regs2 2 = getr regs 2) by exact (HP 2 ltac:(unfold acallee_saved; lia)).
    assert (P3 : getr regs2 3 = getr regs 3) by exact (HP 3 ltac:(unfold acallee_saved; lia)).
    assert (P4 : getr regs2 4 = getr regs 4) by exact (HP 4 ltac:(unfold acallee_saved; lia)).
    assert (P8 : getr regs2 8 = getr regs 8) by exact (HP 8 ltac:(unfold acallee_saved; lia)).
    assert (P9 : getr regs2 9 = getr regs 9) by exact (HP 9 ltac:(unfold acallee_saved; lia)).
    assert (P18 : getr regs2 18 = getr regs 18) by exact (HP 18 ltac:(unfold acallee_saved; lia)).
    assert (P19 : getr regs2 19 = getr regs 19) by exact (HP 19 ltac:(unfold acallee_saved; lia)).
    assert (P20 : getr regs2 20 = getr regs 20) by exact (HP 20 ltac:(unfold acallee_saved; lia)).
    assert (P21 : getr regs2 21 = getr regs 21) by exact (HP 21 ltac:(unfold acallee_saved; lia)).
    assert (P22 : getr regs2 22 = getr regs 22) by exact (HP 22 ltac:(unfold acallee_saved; lia)).
    assert (P23 : getr regs2 23 = getr regs 23) by exact (HP 23 ltac:(unfold acallee_saved; lia)).
    assert (P24 : getr regs2 24 = getr regs 24) by exact (HP 24 ltac:(unfold acallee_saved; lia)).
    assert (P27 : getr regs2 27 = getr regs 27) by exact (HP 27 ltac:(unfold acallee_saved; lia)).
    exists t. split; [|split; [exact HA | split; [|split]]].
    + unfold gcore, gmach, gregs. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs mkst].
      rewrite P2, P3, P4, P8, P9, P19, P20, P22, P27.
      splits; try reflexivity; try assumption; gshow; fail.
    + apply (gmem_trK cx fp t ly3 W3 (mkst regs (Z_to_bv 64 (BASE + AF_reac_headamp_tx_effective)) mem (seg_rom SEGS)));
        [exact HL | exact LW | exact LS | | exact HM].
      intros a Ha. exact (gkeep_call0 cx fp k ly3 S3 W3 mem md TEFF_STK mem2 md2 t HB HJ HFR Hbl
        ltac:(unfold TEFF_STK, ESTACK; lia) HJc a Ha).
    + cbn [ms_regs mkst]. rewrite H10. rewrite ET. f_equal.
      apply HeadampSched.eff_set_T_same; lia.
    + cbn [ms_regs mkst]. rewrite P18, P23, P24, P21. splits; assumption.
Qed.

End c.
End b.
End a.
