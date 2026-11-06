(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySchedSetupDefs), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v. *)
(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/Prog/GrantEntrySchedSetupDefs.v. *)
(* Image B (fuzz_grant.asan-ubsan) twin of
   lib/A/Prog/GrantEntrySchedSetupDefs.v, ported from a working branch 7c8c67da870 (blob
   c6145aadb59): image A's shape over image B's listing, with image B's own cut pcs
   (0x81944 .. 0x81bb0), its register file (s3 the frame's shadow, s6 the address of
   `ch`, s7 the bytes left, s4 the table), its spill slots (48 the input cursor, 144 the
   shadow offset, 152 the table), an atom of its own for the table, image B's
   IMG_LO_B / IMG_TOP_B in place of image A's `off_img`, and the objects 35 / 36 for
   image A's 32 / 33. *)

(* The scheduler's setup in fuzz_grant's entry function LLVMFuzzerTestOneInput on the
   ASan+UBSan build (image B), slots 0x81944 .. 0x81bb0 (fuzz_grant.c:389-396): the data
   its segments share.

   The block marks `raw` unusable again (shadow byte 70 of the frame), reads the
   scene's base and width, calls reac_headamp_tx_arm_scene, reads the re-assert period,
   calls reac_headamp_tx_set_resweep, reads the frame count and takes it modulo 4097,
   marks `unset_sent` usable (shadow bytes 72..89) and zeroes it with __asan_memset, and
   enters the frame loop at 0x81bb0, or goes to 0x81da4 (the free of the table) when
   the count is 0. The input bytes are read only while bytes are left; each read checks
   the shadow byte of its address, and, image B being the UBSan build, each read is
   preceded by a pointer-overflow guard `bgeu 1,cursor+1` whose taken side is the trap
   0x81f48 (`unimp`).

   The phase is cut at the return of each call, so that one segment ends where the
   next begins:
   - `GI_sched0` 0x81944 (LLVMFEntryDefs.v) -> `GI_sch1a` 0x81a20 (at most one byte
     left) or `GI_sch1b` 0x819c0 (two or more): the shadow store, the scene's two
     bytes and reac_headamp_tx_arm_scene;
   - `GI_sch1a` / `GI_sch1b` -> `GI_sch2` 0x81a50: the period's bytes and
     reac_headamp_tx_set_resweep;
   - `GI_sch2` -> `GI_sch3` 0x81b1c: the frame count's bytes, the shadow stores of
     unset_sent and __asan_memset;
   - `GI_sch3` -> `GI_sched` 0x81bb0 or `GI_freeT` 0x81da4 (LLVMFEntryDefs.v): the
     count modulo 4097, the five spill slots and the branch.
   `sch_seat` seats the first cut for the walk engine. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s YI16.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YC5d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YCkd.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaRun PaShadow PaStep.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantAddr GrantPa GrantPaLib GrantFrame.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
YC1g YC1h YC1i YC45 YC85 GrantACjr ACj1 GrantACja.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import LLVMFEntryDefs LLVMFEntrySeat.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampLayout.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require
HeadampModel GrantSlotPlan SlotNeeds_c HeadampSched Seg_sched_setup Seg_sched_lib SegSetModel.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac sch_splits := repeat match goal with |- _ /\ _ => split end.

(* ---- the symbolic state at 0x81944 ---- *)
(* Atoms (LLVMFEntrySeat.v's numbering): 0..31 the entry registers, 32 SHADOW_OFF,
   60 the realigned stack pointer, 516 the frame, 528 its flag, 529 its shadow; this
   phase's own: 33 the input cursor (slot 48: c_p + pos_raw), 34..41 the eight bytes the
   block may read (0 past the end of the input), 42 the head-amp table (slot 152),
   531..561 the registers at the cut (x_r is atom 530 + r). *)
Definition SCH_SB : Z := 0x7fff8000.
Definition sch_Bx : sv := SOff 32 0.
Definition sch_span : Z * Z := (SCH_SB, SCH_SB + 2 ^ 44 - 1).

Definition rin_chunks (m : nat) : list YP09.chunk :=
  map (fun j => YP09.mkChunk (Z.of_nat j) (CVal 1 (SOff (34 + j) 0))) (seq 0 m).
Definition rin (m : nat) : YP09.region := YP09.mkRegion (Some 33%nat) 0 (Z.of_nat m) 0 0 (rin_chunks m).
Definition sch_ex (m : nat) : smem := match m with O => [] | S _ => [rin m] end.
Definition sch_SH (m : nat) : list shent := match m with O => [] | S _ => [mkSHE 33 0 (Z.of_nat m)] end.
Definition sch_atoms : list (nat * afact) :=
  [(32%nat, mkAF SCH_SB SCH_SB 0); (33%nat, mkAF 4096 140737479966720 0);
   (60%nat, mkAF (2 ^ 46) (2 ^ 47) 5)]
  ++ map (fun j => ((34 + j)%nat, mkAF 0 255 0)) (seq 0 8).
Definition sch_G : facts := mkFacts sch_atoms [] [].
(* The register file at the cut: sp and s1 the realigned stack pointer, s0 the
   caller's sp, gp and tp as at entry, s3 the frame's shadow, s6 the address of `ch`;
   the others their own atoms. *)
Definition sch_sr : list sv :=
  [ SLit 0; SOff 531 0; SOff 60 0; SOff 3 0; SOff 4 0; SOff 535 0; SOff 536 0; SOff 537 0;
    SOff 2 0; SOff 60 0; SOff 540 0; SOff 541 0; SOff 542 0; SOff 543 0; SOff 544 0; SOff 545 0;
    SOff 546 0; SOff 547 0; SOff 548 0; SOff 529 0; SOff 550 0; SOff 551 0; SOff 516 784; SOff 553 0;
    SOff 554 0; SOff 555 0; SOff 556 0; SOff 557 0; SOff 558 0; SOff 559 0; SOff 560 0; SOff 561 0 ].
(* The spill slots the block reads: unset_sent's address, the input cursor, value's and
   par's addresses, was_set's address, the shadow offset and the table. *)
Definition sch_spill : YP09.region :=
  YP09.mkRegion (Some 60%nat) 0 184 0 0
    [ YP09.mkChunk 40 (CVal 8 (SOff 516 576)); YP09.mkChunk 48 (CVal 8 (SOff 33 0));
      YP09.mkChunk 96 (CVal 8 (SOff 516 816)); YP09.mkChunk 112 (CVal 8 (SOff 516 800));
      YP09.mkChunk 136 (CVal 8 (SOff 516 32)); YP09.mkChunk 144 (CVal 8 (SOff 32 0));
      YP09.mkChunk 152 (CVal 8 (SOff 42 0)) ].

(* The bytes the block may read, as GrantSlotPlan reads them: 0 past the end. *)
Definition sbat (pl : list byte) (j : nat) : Z := Seg_sched_setup.bat pl (GrantSlotPlan.pos_raw pl + j).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
#[local] Notation SIGMA := (pa_sigma).
#[local] Notation BASE := (pa_val A_TEXT).

Definition SCH_P (cx : ecx) : Z := c_p cx + Z.of_nat (GrantSlotPlan.pos_raw (c_pl cx)).
Definition sch_env (cx : ecx) (fp t : Z) (regs : bvmap 5 word) : env :=
  Eimg (mkEnv (fun n =>
    if (n <? 33)%nat then ew (c_E0 cx) n
    else if (n =? 33)%nat then Z_to_bv 64 (SCH_P cx)
    else if (n <? 42)%nat then Z_to_bv 64 (sbat (c_pl cx) (n - 34))
    else if (n =? 42)%nat then Z_to_bv 64 t
    else if (n =? 60)%nat then Z_to_bv 64 (c_sp1 cx)
    else if (n =? 516)%nat then Z_to_bv 64 (gF cx fp)
    else if (n =? 528)%nat then Z_to_bv 64 (gFL cx fp)
    else if (n =? 529)%nat then Z_to_bv 64 (gSH cx fp)
    else if ((530 <=? n) && (n <? 562))%nat then getr regs (Z_to_bv 5 (Z.of_nat (n - 530)))
    else Z_to_bv 64 0) (fun _ => [])).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.

Lemma sbat_range : forall pl j, 0 <= sbat pl j < 256.
Proof. intros pl j. apply Seg_sched_setup.bat_range. Qed.

Lemma sch_env_low : forall cx fp t regs n, (n < 33)%nat -> ew (sch_env cx fp t regs) n = ew (c_E0 cx) n.
Proof.
intros cx fp t regs n Hn. unfold sch_env. rewrite Eimg_low by (unfold A_TEXT; lia). cbn [ew].
rewrite (proj2 (Nat.ltb_lt n 33) Hn). reflexivity.
Qed.

Lemma sch_env_33 : forall cx fp t regs, ew (sch_env cx fp t regs) 33 = Z_to_bv 64 (SCH_P cx).
Proof. intros. unfold sch_env. rewrite Eimg_low by (unfold A_TEXT; lia). reflexivity. Qed.

Lemma sch_env_b : forall cx fp t regs j, (j < 8)%nat ->
  ew (sch_env cx fp t regs) (34 + j) = Z_to_bv 64 (sbat (c_pl cx) j).
Proof.
intros cx fp t regs j Hj. unfold sch_env. rewrite Eimg_low by (unfold A_TEXT; lia). cbn [ew].
replace ((34 + j) <? 33)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
replace ((34 + j) =? 33)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
replace ((34 + j) <? 42)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
replace (34 + j - 34)%nat with j by lia. reflexivity.
Qed.

Lemma sch_env_42 : forall cx fp t regs, ew (sch_env cx fp t regs) 42 = Z_to_bv 64 t.
Proof. intros. unfold sch_env. rewrite Eimg_low by (unfold A_TEXT; lia). reflexivity. Qed.

Lemma sch_env_60 : forall cx fp t regs, ew (sch_env cx fp t regs) 60 = Z_to_bv 64 (c_sp1 cx).
Proof. intros. unfold sch_env. rewrite Eimg_low by (unfold A_TEXT; lia). reflexivity. Qed.

Lemma sch_env_hi : forall cx fp t regs n, (512 <= n)%nat -> ew (sch_env cx fp t regs) n =
  if (n =? 516)%nat then Z_to_bv 64 (gF cx fp)
  else if (n =? 528)%nat then Z_to_bv 64 (gFL cx fp)
  else if (n =? 529)%nat then Z_to_bv 64 (gSH cx fp)
  else if ((530 <=? n) && (n <? 562))%nat then getr regs (Z_to_bv 5 (Z.of_nat (n - 530)))
  else Z_to_bv 64 0.
Proof.
intros cx fp t regs n Hn. unfold sch_env. cbn [Eimg ew].
replace ((A_TEXT <=? n) && (n <? A_LIM))%nat with false
  by (symmetry; apply andb_false_intro2; apply Nat.ltb_ge; unfold A_LIM; lia).
replace (n <? 33)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
replace (n =? 33)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
replace (n <? 42)%nat with false by (symmetry; apply Nat.ltb_ge; lia).
replace (n =? 42)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
replace (n =? 60)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
reflexivity.
Qed.

Lemma sch_env_E : forall cx fp t regs, ge_base B MT cx -> ge_E cx fp (sch_env cx fp t regs).
Proof.
intros cx fp t regs HB. pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H32 & _).
split; [exact (sch_env_low cx fp t regs)|].
split; [unfold GA_SB; rewrite (sch_env_low cx fp t regs 32 ltac:(lia)); exact H32|].
split; [exact (sch_env_60 cx fp t regs)|].
unfold GA_F, GA_FL, GA_FSH. rewrite !(sch_env_hi cx fp t regs) by lia. cbn.
split; [reflexivity|]. split; reflexivity.
Qed.

Lemma sch_env_reg : forall cx fp t regs (r : bv 5), (Z.to_nat (bv_unsigned r) <> 0)%nat ->
  ew (sch_env cx fp t regs) (530 + Z.to_nat (bv_unsigned r)) = getr regs r.
Proof.
intros cx fp t regs r Hr. pose proof (bv_unsigned_in_range 5 r) as R. change (bv_modulus 5) with 32 in R.
rewrite (sch_env_hi cx fp t regs) by lia.
replace ((530 + Z.to_nat (bv_unsigned r)) =? 516)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
replace ((530 + Z.to_nat (bv_unsigned r)) =? 528)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
replace ((530 + Z.to_nat (bv_unsigned r)) =? 529)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
replace ((530 <=? 530 + Z.to_nat (bv_unsigned r)) && (530 + Z.to_nat (bv_unsigned r) <? 562))%nat with true
  by (symmetry; apply andb_true_intro; split; [apply Nat.leb_le | apply Nat.ltb_lt]; lia).
f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
rewrite Nat2Z.inj_sub by lia. rewrite Nat2Z.inj_add, Z2Nat.id by lia. rewrite Z.mod_small; lia.
Qed.

Lemma regions_wf_app : forall l1 l2, YP09.regions_wf (l1 ++ l2) = YP09.regions_wf l1 && YP09.regions_wf l2.
Proof. intros l1 l2. induction l1 as [|r l1 IH]; [reflexivity|]. cbn [app YP09.regions_wf]. rewrite IH, andb_assoc. reflexivity. Qed.

Lemma rin_wf : forall m, YP09.region_wf (rin m) = true.
Proof.
intros m. unfold YP09.region_wf, rin. cbn [YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
apply andb_true_intro. split; [apply andb_true_intro; split; [apply Z.leb_le; lia | apply orb_true_intro; left; apply Z.leb_le; lia]|].
apply forallb_forall. intros c Hc. unfold rin_chunks in Hc. apply in_map_iff in Hc as (j & <- & Hj). apply in_seq in Hj.
unfold YP09.chunk_inside. cbn [YP09.r_lo YP09.r_hi YP09.c_off YP09.c_len YP09.c_val YP09.cv_len]. change (Z.of_N 1) with 1.
apply andb_true_intro. split; [apply andb_true_intro; split|]; apply Z.leb_le; lia.
Qed.

(* ---- the cuts between the segments ---- *)
(* The input bytes left at 0x81944, and the j-th byte the block may read from there
   (0 past the end of the input, as GrantSlotPlan.sched_rd reads it). *)
Definition sch_L (cx : ecx) : Z := c_n cx - Z.of_nat (GrantSlotPlan.pos_raw (c_pl cx)).
Definition sch_b (cx : ecx) (j : nat) : Z := sbat (c_pl cx) j.
(* The table once reac_headamp_tx_arm_scene (t, b0, b1) has run. *)
Definition sch_T1 (cx : ecx) : list byte :=
  if (sch_b cx 1 =? 0) || (48 <=? sch_b cx 0) then GrantSlotPlan.T_end (c_pl cx)
  else reac_headamp_tx_arm_scene_c.arm_T (GrantSlotPlan.T_end (c_pl cx)) (sch_b cx 0) (sch_b cx 1).
(* The frame's shadow once `raw` is marked unusable again (0x81948); GSH_sched then
   adds unset_sent (0x81ac0 .. 0x81b08). *)
Definition GSH_c : list Z := gsh_set GSH_a 70 1 248.

(* What every cut of this phase carries. On image B the table is NOT in a register
   across the whole phase (0x81b00 overwrites s4), so it is carried in slot 152. *)
Definition sch_common (cx : ecx) (fp : Z) (pc : Z) (sh : list Z) (k acc : Z) (ly3 : alayout)
  (S3 : astate) (W3 : world SEGS) (ms3 : machine_state) (t : Z) : Prop :=
  ge_body cx fp pc W3 ms3 sh /\ k <= 5 /\ acc <= GE_A3 MT /\
  gblk1 B cx ly3 S3 t /\ c_n cx < 2 ^ 26 /\
  getr (ms_regs ms3) 19 = w64 (gSH cx fp) /\
  getr (ms_regs ms3) 22 = w64 (gF cx fp + GO_CH) /\
  gslot cx W3 ms3 8 (gF cx fp) /\ gslot cx W3 ms3 40 (gF cx fp + GO_UNSET) /\
  gslot cx W3 ms3 48 (SCH_P cx) /\
  gslot cx W3 ms3 64 (gF cx fp + GO_CH) /\ gslot cx W3 ms3 72 (gF cx fp) /\
  gslot cx W3 ms3 96 (gF cx fp + GO_VAL) /\ gslot cx W3 ms3 112 (gF cx fp + GO_PAR) /\
  gslot cx W3 ms3 128 (gF cx fp + GO_SET) /\ gslot cx W3 ms3 136 (gF cx fp + GO_WAS) /\
  gslot cx W3 ms3 144 SHADOW_OFF /\ gslot cx W3 ms3 152 t /\
  gfarr cx fp W3 ms3 GO_WAS (GrantSlotPlan.ws_end (c_pl cx)) /\
  gfarr cx fp W3 ms3 GO_SET (GrantSlotPlan.st_end (c_pl cx)) /\
  GrantSlotPlan.Hrel (GrantSlotPlan.T_end (c_pl cx)) (GrantSlotPlan.ws_end (c_pl cx))
    (GrantSlotPlan.st_end (c_pl cx)) /\
  SlotNeeds_c.I1 (GrantSlotPlan.T_end (c_pl cx)).

Definition GP_sch1a : Z := 0xfe4.  (* 0x81a20, the return of the call of arm_scene at 0x81a1c *)
Definition GP_sch1b : Z := 0xf84.  (* 0x819c0, the return of the call of arm_scene at 0x819bc *)
Definition GP_sch2 : Z := 0x1014.  (* 0x81a50, the return of reac_headamp_tx_set_resweep *)
Definition GP_sch3 : Z := 0x10e0.  (* 0x81b1c, the return of __asan_memset             *)

(* 0x81a20: at most one byte was left; s5 holds the scene's base (0 if none), s4 the
   table. *)
Definition GI_sch1a (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t : Z,
  sch_common cx fp GP_sch1a GSH_c k acc ly3 S3 W3 ms3 t /\
  sch_L cx <= 1 /\
  getr (ms_regs ms3) 20 = w64 t /\
  getr (ms_regs ms3) 21 = w64 (sch_b cx 0) /\
  gtab B cx ly3 S3 W3 ms3 t (sch_T1 cx).

(* 0x819c0: two or more bytes were left; s5 and s8 hold the scene's base and width,
   s11 the cursor past them, s2 the bytes left less two, s7 the bytes left (the period
   block reads it at 0x81eb8 and 0x81f34; nothing in 0x81944 .. 0x819c0 writes it). *)
Definition GI_sch1b (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t : Z,
  sch_common cx fp GP_sch1b GSH_c k acc ly3 S3 W3 ms3 t /\
  2 <= sch_L cx /\
  getr (ms_regs ms3) 20 = w64 t /\
  getr (ms_regs ms3) 21 = w64 (sch_b cx 0) /\
  getr (ms_regs ms3) 24 = w64 (sch_b cx 1) /\
  getr (ms_regs ms3) 27 = w64 (SCH_P cx + 2) /\
  getr (ms_regs ms3) 18 = w64 (sch_L cx - 2) /\
  getr (ms_regs ms3) 23 = w64 (sch_L cx) /\
  gtab B cx ly3 S3 W3 ms3 t (sch_T1 cx).

(* 0x81a50: the table is GrantSlotPlan.T_sched0; s7 holds the bytes left for the frame
   count, s11 the cursor when there are any, s5 and s8 the scene's base and width. *)
Definition GI_sch2 (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t : Z,
  sch_common cx fp GP_sch2 GSH_c k acc ly3 S3 W3 ms3 t /\
  getr (ms_regs ms3) 20 = w64 t /\
  getr (ms_regs ms3) 21 = w64 (sch_b cx 0) /\
  getr (ms_regs ms3) 24 = w64 (sch_b cx 1) /\
  getr (ms_regs ms3) 23 = w64 (Z.max (sch_L cx - 6) 0) /\
  (6 <= sch_L cx -> getr (ms_regs ms3) 27 = w64 (SCH_P cx + 6)) /\
  gtab B cx ly3 S3 W3 ms3 t (GrantSlotPlan.T_sched0 (c_pl cx)).

(* 0x81b1c: unset_sent is usable and zero; s2 and s5 hold the frame count's two bytes
   (the high one shifted), s4 the count, s7 and s8 the scene's base and width. *)
Definition GI_sch3 (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t : Z,
  sch_common cx fp GP_sch3 GSH_sched k acc ly3 S3 W3 ms3 t /\
  getr (ms_regs ms3) 18 = w64 (sch_b cx 6) /\
  getr (ms_regs ms3) 20 = w64 (sch_b cx 6 + 256 * sch_b cx 7) /\
  getr (ms_regs ms3) 21 = w64 (256 * sch_b cx 7) /\
  getr (ms_regs ms3) 23 = w64 (sch_b cx 0) /\
  getr (ms_regs ms3) 24 = w64 (sch_b cx 1) /\
  gtab B cx ly3 S3 W3 ms3 t (GrantSlotPlan.T_sched0 (c_pl cx)) /\
  gfarr cx fp W3 ms3 GO_UNSET GrantSlotPlan.Z144.

(* ---- the segments ---- *)
Definition sch_segA_stmt (POST : ecx -> world SEGS -> config -> Prop) : Prop :=
  ge_from B MT POST GI_sch1a -> ge_from B MT POST GI_sch1b -> ge_from B MT POST (GI_sched0 B MT).
Definition sch_segB1_stmt (POST : ecx -> world SEGS -> config -> Prop) : Prop :=
  ge_from B MT POST GI_sch2 -> ge_from B MT POST GI_sch1a.
Definition sch_segB2_stmt (POST : ecx -> world SEGS -> config -> Prop) : Prop :=
  ge_from B MT POST GI_sch2 -> ge_from B MT POST GI_sch1b.
Definition sch_segC_stmt (POST : ecx -> world SEGS -> config -> Prop) : Prop :=
  ge_from B MT POST GI_sch3 -> ge_from B MT POST GI_sch2.
Definition sch_segD_stmt (POST : ecx -> world SEGS -> config -> Prop) : Prop :=
  ge_from B MT POST (GI_sched B MT) -> ge_from B MT POST (GI_freeT B MT) -> ge_from B MT POST GI_sch3.

(* The phase from its segments. *)
Lemma sch_compose : forall POST,
  sch_segA_stmt POST -> sch_segB1_stmt POST -> sch_segB2_stmt POST -> sch_segC_stmt POST -> sch_segD_stmt POST ->
  ge_from B MT POST (GI_sched B MT) -> ge_from B MT POST (GI_freeT B MT) -> ge_from B MT POST (GI_sched0 B MT).
Proof.
intros POST SA SB1 SB2 SC SD HN HF.
pose proof (SC (SD HN HF)) as H2.
exact (SA (SB1 H2) (SB2 H2)).
Qed.

(* ---- the machine state at 0x81944, seated ---- *)
Definition sch_ss0 (m : nat) : sstate :=
  mkSS GP_sched0 sch_sr
    (ge_saved_region :: sch_spill :: set_window (ge_frame_region []) 0 0
     :: ge_shadow_region 70 71 (ge_sh_chunks GSH_raw) :: ge_obj_regions ++ sch_ex m) None sch_G.

Lemma sch_seat : forall cx fp (k : Z) ly3 S3 W3 (ms3 : machine_state) md3 (m : nat) (t : Z),
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(GE_CID, fp)] ->
  ge_body cx fp GP_sched0 W3 ms3 GSH_raw ->
  gblk1 B cx ly3 S3 t ->
  getr (ms_regs ms3) 19 = w64 (gSH cx fp) ->
  getr (ms_regs ms3) 22 = w64 (gF cx fp + GO_CH) ->
  gslot cx W3 ms3 40 (gF cx fp + GO_UNSET) -> gslot cx W3 ms3 48 (SCH_P cx) ->
  gslot cx W3 ms3 96 (gF cx fp + GO_VAL) -> gslot cx W3 ms3 112 (gF cx fp + GO_PAR) ->
  gslot cx W3 ms3 136 (gF cx fp + GO_WAS) -> gslot cx W3 ms3 144 SHADOW_OFF ->
  gslot cx W3 ms3 152 t ->
  (m <= 8)%nat -> Z.of_nat (GrantSlotPlan.pos_raw (c_pl cx)) + Z.of_nat m <= c_n cx ->
  st_ok_pi SEGS VAL (sch_env cx fp t (ms_regs ms3)) (sch_ss0 m) (restrict (w_H W3) ms3).
Proof.
intros cx fp k ly3 S3 W3 ms3 md3 m t HB HJ Hfrs Hbody Hblk R19 R22 S40 S48 S96 S112 S136 S144 S152 Hm8 Hmn.
pose proof Hbody as (_ & _ & _ & _ & _ & _ & Hgr & _ & _ & _ & _ & Hinp).
pose proof Hgr as (R2 & R8 & R9 & R3 & R4).
pose proof HB as (HPRE & H10 & H11 & Hpn & _ & _ & _ & _ & _ & _ & HE0 & Husp & H32 & _).
pose proof HJ as (HAR & _).
pose proof (ge_sp_facts B MT cx HB) as (Hal16 & Hlo & Hhi & Hsp1).
pose proof (ge_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ Hfrs) as (HF0 & HFc & HFia & HFo & HSHeq).
pose proof (ge_sh_range B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ Hfrs) as (Hs0 & Hs1).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof IMG_LO_B_val as HIL. pose proof IMG_TOP_B_val as HIT.
pose proof (pa_obj_img 0 ltac:(lia)) as Ho0. pose proof (pa_obj_img 1 ltac:(lia)) as Ho1.
pose proof (pa_obj_img 35 ltac:(lia)) as Ho35. pose proof (pa_obj_img 36 ltac:(lia)) as Ho36.
assert (Hsp1m : c_sp1 cx mod 32 = 0).
{ pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hs1d & _). rewrite Hs1d. rewrite Z.mul_comm. apply Z_mod_mult. }
assert (Hsp0r : 0 <= spZ (c_regs cx) < 2 ^ 64) by apply u64_range.
(* the input cursor *)
assert (HP : 4096 <= SCH_P cx /\ SCH_P cx + Z.of_nat m <= 140737479966720 /\
             (m <> 0%nat -> In (c_p cx, c_n cx) (ablocks B ly3 S3))).
{ unfold SCH_P. destruct Hpn as [(Hn0 & Hp0) | (Hn0 & Hin0)].
  - unfold c_n in Hn0, Hmn. assert (Hm0 : m = 0%nat) by lia. subst m.
    pose proof (Seg_sched_setup.pos_raw_le (c_pl cx)) as Hpr.
    rewrite Hp0. unfold GE_EMPTY, GrantBContracts.A_EMPTY_B. cbn [Z.of_nat] in *.
    assert (Hz : GrantSlotPlan.pos_raw (c_pl cx) = 0%nat) by lia. rewrite Hz. cbn [Z.of_nat].
    split; [lia|]. split; [lia | intros H; exfalso; exact (H eq_refl)].
  - assert (Hin : In (c_p cx, c_n cx) (ablocks B ly3 S3)) by (unfold gblk1 in Hblk; rewrite Hblk; apply in_or_app; left; exact Hin0).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Hp4096 & Hpceil & _).
    pose proof (req_size_pos' (c_n cx) ltac:(lia)) as [_ Hrq].
    split; [lia|]. split; [lia | intros _; exact Hin]. }
destruct HP as (HP0 & HP1 & HPin).
remember (sch_env cx fp t (ms_regs ms3)) as E eqn:HEdef.
assert (HE : ge_E cx fp E) by (subst E; apply sch_env_E; exact HB).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E33 : ew E 33 = Z_to_bv 64 (SCH_P cx)) by (subst E; apply sch_env_33).
assert (E42 : ew E 42 = Z_to_bv 64 t) by (subst E; apply sch_env_42).
assert (EB : forall j, (j < 8)%nat -> ew E (34 + j) = Z_to_bv 64 (sbat (c_pl cx) j)) by (subst E; apply sch_env_b).
assert (EREG : forall r : bv 5, (Z.to_nat (bv_unsigned r) <> 0)%nat -> ew E (530 + Z.to_nat (bv_unsigned r)) = getr (ms_regs ms3) r)
  by (subst E; apply sch_env_reg).
clear HEdef.
pose proof HE as (AG & E32 & E60 & E516 & E528 & E529).
unfold GA_SB, GA_SP1, GA_F, GA_FL, GA_FSH in E32, E60, E516, E528, E529.
(* the table's bounds *)
assert (HinT : In (t, 460) (ablocks B ly3 S3))
  by (unfold gblk1 in Hblk; rewrite Hblk; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR HinT) as (_ & Ht4096 & Htceil & Htapp & _).
change (req_size 460) with 460 in Ht4096, Htceil, Htapp.
(* the register file *)
assert (HREG : regs_ok E sch_sr (ms_regs ms3)).
{ assert (P2 : getr (ms_regs ms3) 2 = sv_denot E (SOff 60 0)) by (rewrite ge_sv_SOff0, E60; exact R2).
  assert (P9 : getr (ms_regs ms3) 9 = sv_denot E (SOff 60 0)) by (rewrite ge_sv_SOff0, E60; exact R9).
  assert (P8 : getr (ms_regs ms3) 8 = sv_denot E (SOff 2 0)).
  { rewrite ge_sv_SOff0, (AG 2%nat ltac:(lia)), (HE0 2%nat 2%bv eq_refl), R8. unfold w64, spZ. apply Z_to_bv_bv_unsigned. }
  assert (P3 : getr (ms_regs ms3) 3 = sv_denot E (SOff 3 0))
    by (rewrite ge_sv_SOff0, (AG 3%nat ltac:(lia)), (HE0 3%nat 3%bv eq_refl); exact R3).
  assert (P4 : getr (ms_regs ms3) 4 = sv_denot E (SOff 4 0))
    by (rewrite ge_sv_SOff0, (AG 4%nat ltac:(lia)), (HE0 4%nat 4%bv eq_refl); exact R4).
  assert (P19 : getr (ms_regs ms3) 19 = sv_denot E (SOff 529 0)) by (rewrite ge_sv_SOff0; rewrite E529; exact R19).
  assert (P22 : getr (ms_regs ms3) 22 = sv_denot E (SOff 516 784)).
  { cbn [sv_denot]. rewrite E516. unfold w64. rewrite unsigned_lit_small by lia. unfold GO_CH in R22. exact R22. }
  apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
  repeat (destruct Hr as [<-|Hr];
    [ match goal with |- _ = sv_denot ?E0 (sr_get ?sr ?r) =>
        let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
      first [ exact P2 | exact P9 | exact P8 | exact P3 | exact P4 | exact P19 | exact P22
            | rewrite getr_zero; reflexivity
            | lazymatch goal with |- getr _ ?r = _ =>
                rewrite ge_sv_SOff0; symmetry; exact (EREG r ltac:(vm_compute; discriminate)) end ]
    | ]).
  destruct Hr. }
assert (HS0 : st_ok_pi SEGS VAL E (ge_ss cx fp GP_sched0 sch_sr GSH_raw (ge_slot_chunks []) [] 70 71 (sch_ex m) sch_G)
                (restrict (w_H W3) ms3)).
{ apply (ge_seat B MT LAWS TL TLF cx fp W3 ms3 ly3 S3 md3 k HB HJ Hfrs); try assumption.
  - apply Forall_nil.
  - apply Forall_nil.
  - lia.
  - lia.
  - unfold ge_regions. rewrite regions_wf_app. apply andb_true_intro. split; [vm_compute; reflexivity|].
    destruct m as [|m']; [reflexivity|]. cbn [sch_ex YP09.regions_wf]. rewrite rin_wf. reflexivity.
  - destruct m as [|m']; cbn [sch_ex]; [apply Forall_nil|]. apply Forall_cons; [|apply Forall_nil].
    specialize (HPin ltac:(discriminate)).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR HPin) as (_ & Hp4096 & Hpceil & _).
    unfold YP09.region_ok, rin. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
    rewrite E33, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_forall. intros c Hc. unfold rin_chunks in Hc. apply in_map_iff in Hc as (j & <- & Hj). apply in_seq in Hj.
    apply (chunk_ok_val SEGS E _ (SCH_P cx) (Z.of_nat j) 1 (SOff (34 + j) 0) (sbat (c_pl cx) j)).
    + rewrite ge_sv_SOff0, (EB j ltac:(lia)). reflexivity.
    + pose proof (sbat_range (c_pl cx) j). change (2 ^ (8 * Z.of_N 1)) with 256. lia.
    + cbn. lia.
    + set (pr := GrantSlotPlan.pos_raw (c_pl cx)) in *.
      assert (Hj' : (pr + j < length (map (fun b : byte => bv_unsigned b) (c_pl cx)))%nat)
        by (rewrite length_map; unfold c_n in Hmn; lia).
      destruct (Hinp (pr + j)%nat Hj') as [Hv _].
      unfold SCH_P. fold pr.
      replace (c_p cx + Z.of_nat pr + Z.of_nat j) with (c_p cx + Z.of_nat (pr + j)) by lia.
      replace (sbat (c_pl cx) j) with (nth (pr + j) (map (fun b : byte => bv_unsigned b) (c_pl cx)) 0); [exact Hv|].
      unfold sbat. fold pr. rewrite Seg_sched_setup.bat_in by (rewrite length_map in Hj'; exact Hj').
      unfold GrantSlotPlan.pbz. rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by exact Hj'.
      apply (map_nth (fun b : byte => bv_unsigned b)).
  - destruct m as [|m']; cbn [sch_ex YP09.pairwise_disjoint YP09.all_disjoint]; repeat split.
  - destruct m as [|m']; cbn [sch_ex].
    + apply Forall_forall. intros r _. exact I.
    + specialize (HPin ltac:(discriminate)).
      destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR HPin) as (_ & Hp4096 & Hpceil & Hpapp & _).
      pose proof (req_size_pos' (c_n cx) ltac:(lia)) as [_ Hrq].
      pose proof (blk_off_imgB B ly3 S3 W3 (ms_mem ms3) md3 _ _ HAR HPin) as Hpimg.
      pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 _ _ GE_CID fp HAR HPin
                    (ge_fin fp S3 Hfrs)) as Hpf.
      rewrite (ge_frame_addr_eq B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ) in Hpf.
      change (fs_frame_bytes GE_CID) with 1024 in Hpf. unfold zdisjoint in Hpf. cbn [fst snd] in Hpf.
      assert (EA : forall n, (A_TEXT <= n < A_LIM)%nat -> YP09.base_val E (Some n) = VAL n).
      { intros n Hn. cbn [YP09.base_val]. rewrite (img_env_atomP E n HEI Hn). apply unsigned_lit_small. apply pa_val_range. }
      pose proof (ge_base_sp B MT cx fp HB E HE) as Ub2.
      unfold ge_regions0, ge_saved_region, ge_spill_region, ge_frame_region, fframe_region,
        ge_shadow_region, fshadow_region, ge_obj_regions, got_regionP, bcell_regionP,
        uar_got_regionP, uar_cell_regionP, rin.
      repeat apply Forall_cons; try apply Forall_nil;
        cbn [YP09.all_disjoint]; (split; [|exact I]); unfold YP09.extent_disjoint;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi].
      all: rewrite ?Ub2, ?(EA (A_OBJ 1)), ?(EA (A_OBJ 35)), ?(EA (A_OBJ 0)), ?(EA (A_OBJ 36))
             by (unfold A_OBJ, A_TEXT, A_LIM; lia).
      all: cbn [YP09.base_val]; rewrite ?E33, ?E60, ?E516, ?E529; unfold GA_SP1, GA_F, GA_FSH in *;
        rewrite ?E60, ?E516, ?E529.
      all: unfold w64; rewrite ?unsigned_lit_small by lia; change (fs_frame_bytes GE_CID) with 1024;
        change (1024 / 8) with 128; rewrite ?HSHeq.
      all: unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF, SCH_P in *; lia.
  - split; [|split; exact I].
    unfold sch_G, sch_atoms. cbn [f_atoms app map seq atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    unfold GA_SB, GA_SP1 in E32, E60. rewrite E32, E33, E60, !EB by lia.
    pose proof (sbat_range (c_pl cx) 0) as B0. pose proof (sbat_range (c_pl cx) 1) as B1.
    pose proof (sbat_range (c_pl cx) 2) as B2. pose proof (sbat_range (c_pl cx) 3) as B3.
    pose proof (sbat_range (c_pl cx) 4) as B4. pose proof (sbat_range (c_pl cx) 5) as B5.
    pose proof (sbat_range (c_pl cx) 6) as B6. pose proof (sbat_range (c_pl cx) 7) as B7.
    unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia). rewrite !Z.pow_0_r, !Z.mod_1_r.
    change (2 ^ 5) with 32. unfold SCH_SB, SHADOW_OFF.
    revert B0 B1 B2 B3 B4 B5 B6 B7 HP0 HP1 Hlo Hhi Hsp1 Hsp1m C1. clear. intros.
    repeat match goal with |- _ /\ _ => split end; lia. }
(* the spill slots the block reads, as atoms; the frame read-only *)
pose proof (st_ok_pi_region_nth E _ _ 2%nat _ HS0 eq_refl) as RF.
assert (RS : YP09.region_ok SEGS E (ms_mem (restrict (w_H W3) ms3)) sch_spill).
{ cbn [ms_mem restrict]. unfold YP09.region_ok, sch_spill.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
  rewrite E60, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  assert (V516 : forall c, sv_denot E (SOff 516 c) = Z_to_bv 64 (gF cx fp + c))
    by (intros c; cbn [sv_denot]; rewrite E516; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
  assert (VR : forall v, 0 <= v < 2 ^ 64 -> 0 <= v < 2 ^ (8 * Z.of_N 8)) by (intros v Hv; exact Hv).
  assert (V8 : Z.of_N 8 <= 8) by (cbn; lia).
  unfold GO_UNSET, GO_VAL, GO_PAR, GO_WAS in *.
  repeat apply Forall_cons; try apply Forall_nil.
  - apply (chunk_ok_val SEGS E _ (c_sp1 cx) 40 8 (SOff 516 576) (gF cx fp + 576)); [rewrite V516; reflexivity | apply VR; lia | exact V8 |].
    exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ S40).
  - apply (chunk_ok_val SEGS E _ (c_sp1 cx) 48 8 (SOff 33 0) (SCH_P cx)); [rewrite ge_sv_SOff0, E33; reflexivity | apply VR; lia | exact V8 |].
    exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ S48).
  - apply (chunk_ok_val SEGS E _ (c_sp1 cx) 96 8 (SOff 516 816) (gF cx fp + 816)); [rewrite V516; reflexivity | apply VR; lia | exact V8 |].
    exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ S96).
  - apply (chunk_ok_val SEGS E _ (c_sp1 cx) 112 8 (SOff 516 800) (gF cx fp + 800)); [rewrite V516; reflexivity | apply VR; lia | exact V8 |].
    exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ S112).
  - apply (chunk_ok_val SEGS E _ (c_sp1 cx) 136 8 (SOff 516 32) (gF cx fp + 32)); [rewrite V516; reflexivity | apply VR; lia | exact V8 |].
    exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ S136).
  - apply (chunk_ok_val SEGS E _ (c_sp1 cx) 144 8 (SOff 32 0) SHADOW_OFF);
      [rewrite ge_sv_SOff0, E32; reflexivity | apply VR; unfold SHADOW_OFF; lia | exact V8 |].
    exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ S144).
  - apply (chunk_ok_val SEGS E _ (c_sp1 cx) 152 8 (SOff 42 0) t); [rewrite ge_sv_SOff0, E42; reflexivity | apply VR; lia | exact V8 |].
    exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ S152). }
pose proof (ast_ok_pi_set_region E _ _ 1%nat _ sch_spill HS0 eq_refl eq_refl
  ltac:(unfold ge_ss, ge_regions; cbn [ss_mem list_upd ge_regions0 app]; cbn [YP09.regions_wf];
        rewrite regions_wf_app; apply andb_true_intro; split; [vm_compute; reflexivity|];
        destruct m as [|m']; [reflexivity|]; cbn [sch_ex YP09.regions_wf]; rewrite rin_wf; reflexivity) RS) as HS1.
pose proof (ast_ok_pi_set_region E _ _ 2%nat _ (set_window (ge_frame_region []) 0 0) HS1 eq_refl eq_refl
  ltac:(unfold ge_ss, ge_regions; cbn [ss_mem ss_pc ss_regs ss_resv ss_facts list_upd ge_regions0 app]; cbn [YP09.regions_wf];
        rewrite regions_wf_app; apply andb_true_intro; split; [vm_compute; reflexivity|];
        destruct m as [|m']; [reflexivity|]; cbn [sch_ex YP09.regions_wf]; rewrite rin_wf; reflexivity)
  (region_ok_rewindow SEGS E _ _ 0 0 RF ltac:(intros o Ho; lia))) as HS2.
exact HS2.
Qed.

(* ---- the head-amp table, as gtab speaks of it and as the writers' posts do ---- *)
Lemma tx_fbyte_all : forall i, 0 <= i < 460 -> i <> 438 -> i <> 439 -> i <> 451 -> tx_fbyte i = true.
Proof.
intros i Hi H1 H2 H3.
assert (HA : forallb (fun n => let z := Z.of_nat n in ((z =? 438) || (z =? 439) || (z =? 451) || tx_fbyte z)%bool) (seq 0 460) = true)
  by (vm_compute; reflexivity).
rewrite forallb_forall in HA. specialize (HA (Z.to_nat i) ltac:(apply in_seq; lia)). cbv zeta in HA.
rewrite Z2Nat.id in HA by lia.
rewrite (proj2 (Z.eqb_neq i 438) H1), (proj2 (Z.eqb_neq i 439) H2), (proj2 (Z.eqb_neq i 451) H3) in HA. exact HA.
Qed.

Lemma tx_fbyte_pad : forall i, tx_fbyte i = true -> i <> 438 /\ i <> 439 /\ i <> 451.
Proof. intros i Hi. repeat split; intros ->; vm_compute in Hi; discriminate. Qed.

Lemma gtab_obj : forall cx ly3 S3 W3 ms3 t T, gtab B cx ly3 S3 W3 ms3 t T ->
  obj_at SEGS (mrestrict (w_H W3) (ms_mem ms3)) t LAY_TX (tx_vals T).
Proof.
intros cx ly3 S3 W3 ms3 t T (_ & _ & _ & Hb). apply (proj2 (tx_obj_bytes SEGS _ t T)). intros i Hi.
pose proof (tx_fbyte_range i Hi) as Hr. destruct (tx_fbyte_pad i Hi) as (H1 & H2 & H3).
specialize (Hb i Hr H1 H2 H3). unfold aview in Hb.
destruct (YP09.mbyte SEGS (mrestrict (w_H W3) (ms_mem ms3)) (t + i)) as [b|] eqn:Hm; [|discriminate Hb].
cbn in Hb. injection Hb as Hb. f_equal. rewrite <- tb_nth, <- Hb. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma obj_gtab : forall cx ly3 S3 W3 ms3 t T,
  In (t, 460) (ablocks B ly3 S3) -> 0 < t -> length T = 460%nat ->
  obj_at SEGS (mrestrict (w_H W3) (ms_mem ms3)) t LAY_TX (tx_vals T) ->
  gtab B cx ly3 S3 W3 ms3 t T.
Proof.
intros cx ly3 S3 W3 ms3 t T Hin Ht Hl Ho. split; [exact Hin|]. split; [exact Ht|]. split; [exact Hl|].
intros i Hi H1 H2 H3. pose proof (proj1 (tx_obj_bytes SEGS _ t T) Ho i (tx_fbyte_all i Hi H1 H2 H3)) as Hm.
unfold aview. rewrite Hm. reflexivity.
Qed.

Lemma sch_T1_len : forall cx, length (GrantSlotPlan.T_end (c_pl cx)) = 460%nat -> length (sch_T1 cx) = 460%nat.
Proof. intros cx H. exact (Seg_sched_lib.len_Tarm _ _ _ H). Qed.

(* ---- the table is not one of the caller's blocks ---- *)
Lemma sch_notin_base : forall cx ly3 S3 W3 mem3 md3 t,
  AR SEGS B ly3 S3 W3 mem3 md3 -> gblk1 B cx ly3 S3 t -> ~ In (t, 460) (ablocks B (c_ly cx) (c_S cx)).
Proof.
intros cx ly3 S3 W3 mem3 md3 t HAR Hblk Hin.
assert (Hin3 : In (t, 460) (ablocks B ly3 S3)) by (unfold gblk1 in Hblk; rewrite Hblk; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin3) as (_ & _ & _ & _ & _ & Hpw & _).
unfold gblk1 in Hblk. rewrite Hblk in Hpw. apply in_split in Hin as (l1 & l2 & Hl).
rewrite Hl in Hpw. rewrite <- app_assoc, map_app in Hpw. cbn [app map fst snd] in Hpw. rewrite map_app in Hpw. cbn [map fst snd] in Hpw.
pose proof (pairwise_In2 zdisjoint _ _ _ _ _ _ Hpw eq_refl) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
change (req_size 460) with 460 in Hd. lia.
Qed.

(* ---- a writer of the table keeps every byte this phase's facts speak about ---- *)
Lemma sch_keep_call : forall cx fp W3 ms3 ly3 S3 md3 k t STK1 FP1 memc mdc mem2 md2 k1,
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(GE_CID, fp)] -> gblk1 B cx ly3 S3 t ->
  AR SEGS B ly3 S3 W3 memc mdc ->
  (forall a, inFP FP1 a -> t <= a < t + 460) ->
  ajournal SEGS B STK1 (c_sp1 cx) FP1 ly3 S3 W3 memc mdc [] ly3 S3 W3 mem2 md2 k1 ->
  ge_keep cx fp W3 [] memc mem2.
Proof.
intros cx fp W3 ms3 ly3 S3 md3 k t STK1 FP1 memc mdc mem2 md2 k1 HB HJ Hfrs Hblk HARc HFP HJ1 a Ha.
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & _ & F4 & _).
pose proof (ge_sp_facts B MT cx HB) as (Hal & Hlo & Hhi & Hsp1).
pose proof (ge_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ Hfrs) as (HF0 & HFc & HFia & HFo & HSHeq).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Hfb : fs_frame_bytes GE_CID = 1024) by (vm_compute; reflexivity).
assert (Hfin : In (GE_CID, fp) (frames S3)) by (rewrite Hfrs; left; reflexivity).
assert (Hfa : frame_addr ly3 GE_CID fp = gF cx fp)
  by exact (ge_frame_addr_eq B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ).
assert (Hin3 : In (t, 460) (ablocks B ly3 S3)) by (unfold gblk1 in Hblk; rewrite Hblk; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Hin3) as (_ & Ht4096 & Htceil & Htapp & _).
change (req_size 460) with 460 in Htceil, Htapp.
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 memc mdc t 460 GE_CID fp HARc Hin3 Hfin) as Htf.
rewrite Hfa, Hfb in Htf. unfold zdisjoint in Htf. cbn [fst snd] in Htf. change (req_size 460) with 460 in Htf.
assert (Hsa : shadow_addr (gF cx fp) = gSH cx fp) by (unfold shadow_addr; rewrite HSHeq; reflexivity).
unfold ge_keep_at in Ha. rewrite Hfb in Ha. change (1024 / 8) with 128 in Ha.
destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]].
- apply F1; lia.
- pose proof HB as (_ & _ & _ & Hpn & _).
  destruct Hpn as [[Hn0 _] | [Hn Hin0]]; [lia|].
  assert (Hin : In (c_p cx, c_n cx) (ablocks B ly3 S3)) by (unfold gblk1 in Hblk; rewrite Hblk; apply in_or_app; left; exact Hin0).
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hq].
  assert (Hne : (c_p cx, c_n cx) <> (t, 460)).
  { intros Heq. apply (sch_notin_base cx ly3 S3 W3 memc mdc t HARc Hblk). rewrite <- Heq. exact Hin0. }
  pose proof (sep_blocks SEGS B LAWS ly3 S3 W3 memc mdc _ _ _ _ HARc Hin Hin3 Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (req_size 460) with 460 in Hd.
  replace a with (c_p cx + (a - c_p cx)) by lia.
  apply (F2 (c_p cx) (c_n cx) (a - c_p cx) Hin Hin); [lia|].
  intros HF. pose proof (HFP _ HF). lia.
- apply (F4 GE_CID fp a Hfin).
  + left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Hfa, Hfb. lia.
  + intros HF. pose proof (HFP _ HF). lia.
- apply (F4 GE_CID fp a Hfin).
  + right. unfold in_zr. cbn [fst snd]. rewrite Hfa, Hsa, Hfb. change (1024 / 8) with 128. exact Ha.
  + intros HF. pose proof (HFP _ HF). rewrite HSHeq in Ha.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
    assert (0 <= gF cx fp / 8) by (apply Z.div_pos; lia).
    assert (gF cx fp / 8 <= 0xFFFFFF00000) by (apply Z.div_le_upper_bound; lia). lia.
- apply Exists_exists in Ha as (r & Hr & _). destruct Hr.
Qed.

Lemma achain_top : forall ly ly' rd sp v ch, ly_top ly' = ly_top ly -> achain ly rd sp v ch -> achain ly' rd sp v ch.
Proof. intros ly ly' rd sp v ch E H. unfold achain in *. rewrite E. exact H. Qed.

(* ======================= LOCAL BLOCK: image A's GrantEntrySetDefs.v lemmas ==========================
   The lemmas of lib/A/Prog/GrantEntrySetDefs.v (a working branch 7c8c67da870, blob 7818e2549e1) that this
   phase uses, copied here with image A's names and statements. The image-B twin of that file
   (lib/B/Prog/LLVMFEntrySetDefs.v) is in this tree; this file does not Require it,
   so this block stays. *)
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

(* The machine part every cut of a stretch shares. *)
Definition gmach (cx : ecx) (ms3 : machine_state) (pc : Z) : Prop :=
  ms_pc_val ms3 = w64 (BASE + pc) /\ ms_resv ms3 = None /\ ms_svc_pending ms3 = None /\
  ms_rom ms3 = seg_rom SEGS /\ ms_fregs ms3 = fp_regs /\ ms_fcsr ms3 = fp_csr /\ gregs cx ms3.

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

Lemma frame_wins : forall E rs (H : word -> bool) (m m' : word -> option byte) (P : Z -> Prop),
  frame_of E rs (mrestrict H m) (mrestrict H m') -> (forall a, in_wrange E rs a -> P a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS H m' a = aview SEGS H m a.
Proof.
  intros E rs H m m' P HF HP a Ha HnP. apply aview_eq_of. apply HF.
  rewrite unsigned_lit_small by lia. intros Hw. exact (HnP (HP a Hw)).
Qed.

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
  unfold in_app in Happ, Htapp. unfold GE_STK, GrantBContracts.STK_LLVMFuzzerTestOneInput in *.
  unfold glayout. sch_splits; try lia; try assumption.
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
    sch_splits; lia.
Qed.

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
               | (intros a Ha; exact (aview_above_of_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ a Ha)) ].
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
  pose proof pa_B_ok as HBASE. pose proof (pa_base_lo (L := grant_listing)) as HBlo. rewrite IMG_LO_B_val in HBlo.
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
(* ===================== end of the LOCAL BLOCK ===================================================== *)

End c.
End b.
End a.
