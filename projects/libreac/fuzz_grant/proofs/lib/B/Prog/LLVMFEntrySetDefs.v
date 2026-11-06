(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySetDefs), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/AC8j.v. *)
(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/Prog/GrantEntrySetDefs.v. *)
(* Image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/GrantEntrySetDefs.v, ported from a working branch 7c8c67da870
   (blob 7818e2549e1; the image-A file carries no licence lines, so none are copied).
   Every lemma name is image A's, so that the phase files need no
   renaming; every address, register and spill slot is image B's own, read from fuzz_grant.asan-ubsan
   (entry 0x80a3c). What image B makes different, and the measurement behind it:
   - the set loop runs 0x80ef8..0x8114c, not image A's 0x80aa4..0x80c80, so every cut pc is image B's offset
     from 0x80a3c;
   - image B keeps the bytes left in a2 (x12) at the loop head and spills it to slot 104 only across the third
     call site, where image A kept it in slot 120 the whole turn; so `gmem` carries slot 104, not slot 120;
   - the registers are renamed: the channel is still s2 (x18), but the parameter is s8 (x24), the value s9 (x25),
     the set's answer s10 (x26), the cursor s7 (x23), the cursor past the cell s11 (x27), the turns left s5 (x21),
     the frame's shadow base s3 (x19) and the `channel < 48` flag s6 (x22), which image A has not got at all;
   - image B is the UBSan build, so the turn carries seven guards image A has not: the three pointer-overflow
     checks on the input cursor (0x80f00, 0x80f28, 0x80fbc, each falling into the trap 0x81f48), the array-bound
     flag test 0x810b8, and the four pointer-overflow checks on the two stores (0x810c8, 0x810d0, 0x810e0 and
     0x81108, 0x81118). Slots 112 and 120 hold the bitwise NOT of the two array addresses, which those guards
     compare against, so `gslots_set` carries them;
   - the callee contracts are image B's (GrantBContracts.v): `tb_reac_headamp_tx_set_spec` leaves
     `thd_set_T T ch p v` and writes `thd_set_fp t ch p v`, and `tb_reac_headamp_tx_effective_spec` ALLOWS
     `tx = 0`, which image A's does not, and guards its `obj_at` by `tx <> 0`. The walk always passes a live
     table (`gtab` gives `0 < t`), so it takes the right disjunct and gets the `obj_at` back. *)
(* The set loop of fuzz_grant's entry function LLVMFuzzerTestOneInput on the ASan+UBSan
   build (image B, the slots 0x80ef8 .. 0x81224, GP_set .. GP_unset0, and the error
   slots they branch to): the cuts inside one turn, the symbolic states the turn's
   pieces run on, and the facts every piece uses. LLVMFEntrySet.v composes the pieces
   into ge_set.

   One turn of `for (i = 0; i < nset; i++)` (fuzz/fuzz_grant.c:201-230) reads the three
   bytes of a cell (channel, parameter, value; a short input reads 0 for the bytes it
   lacks), calls reac_headamp_tx_set, and checks: for a parameter of 3 or more that
   reac_headamp_tx_effective and reac_headamp_default both answer 0; that the answer of
   the set is 0 exactly when the channel is below 48 and the value is legal; and after an
   accepted set that reac_headamp_tx_effective gives back the value. It then stores 1 in
   was_set[ch][param] and the value in set_to[ch][param] of this function's own frame.

   The turn is cut after each call it makes (a semantic cut, as LLVMFEntryDefs.v cuts the
   phases), so that each piece builds its own symbolic state:
     GIn n ─ HEAD ─> GA0 | GA1 | GA2   (the returns of reac_headamp_tx_set at 0x80f70,
                                        0x80f9c, 0x80ffc: the cell had 0, 1, 2+ bytes)
     GA0 | GA1 | GA2 ─> GE2 (accepted: the return of reac_headamp_tx_effective at
                             0x810b4) | G78 (refused, 0x81140)
     GE2 ─> G78 (the two stores, seg_e2)   G78 ─> GIn (n - 1) | GI_unset0 (seg78).
   The pieces are stated as `seg_*_stmt` below. The loop is an induction on the turns
   left, which s5 holds. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YC5d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05 YG0s.
(* The walk ENGINE is image-independent and comes from lib.Reusable; the image-DEPENDENT
   layer comes from lib.B.Prog. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaShadow PaRun PaStep.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC88.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantAddr GrantPa GrantPaLib GrantFrame GrantBContracts.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC1g YC1h YC85 HeadampDefault.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import LLVMFEntryDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require
GrantSlotPlan SlotNeeds_c SegSetModel HeadampSched reac_headamp_tx_set_c HeadampLayout.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* With zify's euclidean-division flag false, `lia` does not turn `mod` and `/` into equations and fails
   on goals that need them; this file sets it to true itself, whatever its Require closure leaves. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Module ALay := OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog.HeadampLayout.

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

(* ---- the bitwise NOT image B's UBSan guards take of the two array addresses ---- *)
(* `not rd,rs` is `xori rd,rs,-1`; the walk sees SAlu ALU_XOR _ (SLit (-1)). *)
Lemma g_lxor_ones : forall a n, 0 < n -> 0 <= a < 2 ^ n -> Z.lxor a (Z.ones n) = Z.ones n - a.
Proof.
  intros a n Hn Ha.
  assert (Hlog : Z.log2 a < n).
  { destruct (Z.eq_dec a 0) as [->|Hz]; [rewrite Z.log2_nonpos; lia|].
    apply (proj1 (Z.log2_lt_pow2 a n ltac:(lia))). lia. }
  rewrite <- (Z.ldiff_ones_l_low a n) by lia.
  rewrite Z.ldiff_land.
  assert (E : Z.land (Z.ones n) (Z.lnot a) = Z.land (Z.lnot a) (Z.ones n)) by apply Z.land_comm. rewrite E.
  rewrite Z.land_ones by lia. unfold Z.lnot, Z.ones. rewrite Z.shiftl_1_l.
  replace (Z.pred (- a)) with ((2 ^ n - 1 - a) + (-1) * 2 ^ n) by lia. rewrite Z.mod_add by lia.
  rewrite Z.mod_small by lia. lia.
Qed.
Lemma g_U_not : forall E v, U E (SAlu ALU_XOR v (SLit (-1))) = 2 ^ 64 - 1 - U E v.
Proof.
  intros E v. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon (-1)) with (Z.ones 64).
  pose proof (U_range E v) as Hr. unfold M64 in Hr. rewrite g_lxor_ones by lia.
  change (Z.ones 64) with (2 ^ 64 - 1). rewrite zcanon_id by (unfold M64; lia). reflexivity.
Qed.

(* The shadow offset as the loop loads it from slot 144, and the band of the shadow. *)
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

(* The table reac_headamp_tx_set leaves, as image B's contract names it. *)
Lemma gthd_set : forall pl i,
  thd_set_T (gTi pl i) (gc pl i) (gq pl i) (gv pl i) = gTi pl (S i).
Proof.
  intros pl i. destruct (gtables_S pl i) as (ET & _ & _). rewrite ET.
  unfold thd_set_T, gacc. reflexivity.
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

(* The spill slots the whole set loop keeps, measured on image B: the four header fields
   (slots 0, 24, 32, 88), the frame twice (8 and 72), the shadow offset (144), the table
   (152), the two arrays the harness keeps itself (128 and 136) and the bitwise NOT of
   those two addresses (112 and 120), which image B's pointer-overflow guards read. *)
Definition gslots_set (cx : ecx) (fp t : Z) (W3 : world SEGS) (ms3 : machine_state) : Prop :=
  gslot cx W3 ms3 0 (GrantSlotPlan.h_rows (GrantSlotPlan.header (c_pl cx))) /\
  gslot cx W3 ms3 8 (gF cx fp) /\
  gslot cx W3 ms3 24 (256 * (GrantSlotPlan.h_u16 (GrantSlotPlan.header (c_pl cx)) / 256)) /\
  gslot cx W3 ms3 32 (GrantSlotPlan.h_in (GrantSlotPlan.header (c_pl cx))) /\
  gslot cx W3 ms3 72 (gF cx fp) /\
  gslot cx W3 ms3 88 (GrantSlotPlan.h_base (GrantSlotPlan.header (c_pl cx)) mod 2 ^ 64) /\
  gslot cx W3 ms3 112 (2 ^ 64 - 1 - (gF cx fp + GO_SET)) /\
  gslot cx W3 ms3 120 (2 ^ 64 - 1 - (gF cx fp + GO_WAS)) /\
  gslot cx W3 ms3 128 (gF cx fp + GO_SET) /\
  gslot cx W3 ms3 136 (gF cx fp + GO_WAS) /\
  gslot cx W3 ms3 144 SHADOW_OFF /\
  gslot cx W3 ms3 152 t.

(* The memory the turn keeps or changes: the saved registers, the frame's shadow and
   flag, the input, the spill slots (slot 104: the bytes left, the one slot the turn
   writes), the table and the two arrays. *)
Definition gmem (cx : ecx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) (t : Z)
  (T ws st : list byte) : Prop :=
  gsaved cx W3 ms3 /\ gshadow cx fp W3 ms3 GSH_tables /\
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (gF cx fp + 1016) = Some (gFL cx fp) /\
  garr8 SEGS (mrestrict (w_H W3) (ms_mem ms3)) (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) /\
  gslots_set cx fp t W3 ms3 /\ gtabb W3 ms3 t T /\
  gfarr cx fp W3 ms3 GO_WAS ws /\ gfarr cx fp W3 ms3 GO_SET st.

(* What every cut of turn i (with n turns left after it) holds: the pc, the frame's
   shadow base in s3, the table in s4 and the turns left in s5. *)
Definition gcore (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (ms3 : machine_state)
  (pc : Z) (n i : nat) (t : Z) : Prop :=
  gmach cx ms3 pc /\ k <= 1 /\ acc <= GE_A1 MT /\ gblk1 B cx ly3 S3 t /\ 0 < t /\ c_n cx < 2 ^ 26 /\
  GrantSlotPlan.nset (c_pl cx) = Z.of_nat i + Z.of_nat (S n) /\
  getr (ms_regs ms3) 19 = w64 (gSH cx fp) /\ getr (ms_regs ms3) 20 = w64 t /\
  getr (ms_regs ms3) 21 = w64 (Z.of_nat (S n)).

(* GI_set with n + 1 turns left (nset is a byte, so n < 255). *)
Definition GIn (n : nat) (cx : ecx) (fp k acc : Z) ly3 S3 W3 (ms3 : machine_state) md3 : Prop :=
  GI_set B MT cx fp k acc ly3 S3 W3 ms3 md3 /\ getr (ms_regs ms3) 21 = w64 (Z.of_nat (S n)) /\ (n < 255)%nat.

(* 0x81140 (offset 0x704): turn i is done, s5 is not yet decremented. *)
Definition G78 (n i : nat) (cx : ecx) (fp k acc : Z) ly3 S3 W3 (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t, gcore cx fp k acc ly3 S3 ms3 0x704 n i t /\
  gmem cx fp W3 ms3 t (gTi (c_pl cx) (S i)) (gwsi (c_pl cx) (S i)) (gsti (c_pl cx) (S i)) /\
  getr (ms_regs ms3) 23 = w64 (c_p cx + Z.of_nat (gpos (c_pl cx) (S i))) /\
  getr (ms_regs ms3) 12 = w64 (c_n cx - Z.of_nat (gpos (c_pl cx) (S i))).

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
Lemma gmem_tr : forall cx fp W3 ms3 ms4 t T ws st,
  (forall a, aview SEGS (w_H W3) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  gmem cx fp W3 ms3 t T ws st -> gmem cx fp W3 ms4 t T ws st.
Proof.
  intros cx fp W3 ms3 ms4 t T ws st HA (Hsv & Hsh & Hfl & Hin & Hmid & HT & Hws & Hst).
  assert (RD : forall a v0, rdword (aview SEGS (w_H W3) (ms_mem ms3)) a = Some v0 ->
                 rdword (aview SEGS (w_H W3) (ms_mem ms4)) a = Some v0)
    by (intros a v0 H; rewrite (rdword_tr _ _ a (fun j _ => HA (a + j))); exact H).
  assert (GA : forall p L, garr8 SEGS (mrestrict (w_H W3) (ms_mem ms3)) p L -> garr8 SEGS (mrestrict (w_H W3) (ms_mem ms4)) p L)
    by (intros p L H; apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) (ms_mem ms3) (ms_mem ms4) p L); [intros a _; apply HA | exact H]).
  destruct Hsv as [Hra Hsv]. destruct Hmid as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12).
  unfold gmem, gsaved, gshadow, gslots_set, gslot, gfarr, gtabb in *.
  split; [split; [apply RD, Hra | intros j Hj; apply RD, Hsv, Hj]|].
  split; [intros j Hj; rewrite HA; apply Hsh, Hj|].
  split; [apply RD, Hfl|].
  split; [apply GA, Hin|].
  split; [splits; apply RD; assumption|].
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

(* The cuts of LLVMFEntryDefs.v, from the turn's own facts. *)
Lemma fin_unset0 : forall cx fp k acc ly3 S3 W3 ms md i t,
  gmach cx ms GP_unset0 -> k <= 1 -> acc <= GE_A1 MT -> gblk1 B cx ly3 S3 t -> 0 < t -> c_n cx < 2 ^ 26 ->
  GrantSlotPlan.nset (c_pl cx) = Z.of_nat (S i) ->
  getr (ms_regs ms) 19 = w64 (gSH cx fp) ->
  getr (ms_regs ms) 23 = w64 (c_p cx + Z.of_nat (gpos (c_pl cx) (S i))) ->
  getr (ms_regs ms) 12 = w64 (c_n cx - Z.of_nat (gpos (c_pl cx) (S i))) ->
  gmem cx fp W3 ms t (gTi (c_pl cx) (S i)) (gwsi (c_pl cx) (S i)) (gsti (c_pl cx) (S i)) ->
  GI_unset0 B MT cx fp k acc ly3 S3 W3 ms md.
Proof.
  intros cx fp k acc ly3 S3 W3 ms md i t (Pc & Prv & Psv & Pro & Pfr & Pfc & G2 & G8 & G9 & G3 & G4)
    Hk Hacc Hbl Ht0 Hn Hns R19 R23 R12
    ((Hsv1 & Hsv2) & Hsh & Hfl & Hin & (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12) & HT & Hws & Hst).
  assert (Enat : Z.to_nat (GrantSlotPlan.nset (c_pl cx)) = S i) by lia.
  pose proof (SegSetModel.tables_end_inv (c_pl cx)) as (L1 & L2 & L3 & I1e & Hre).
  assert (HinT : In (t, 460) (ablocks B ly3 S3)) by (unfold gblk1 in Hbl; rewrite Hbl; apply in_or_app; right; left; reflexivity).
  exists t. unfold ge_body, gtab, gregs, gsaved. unfold gtabb in HT.
  unfold GrantSlotPlan.pos_end, GrantSlotPlan.T_end, GrantSlotPlan.ws_end, GrantSlotPlan.st_end,
    GrantSlotPlan.tables_end in *. rewrite Enat in *.
  splits; try assumption; apply GSH_tables_len.
Qed.

Lemma fin_set : forall cx fp k acc ly3 S3 W3 ms md i t,
  gmach cx ms GP_set -> k <= 1 -> acc <= GE_A1 MT -> gblk1 B cx ly3 S3 t -> 0 < t -> c_n cx < 2 ^ 26 ->
  Z.of_nat i < GrantSlotPlan.nset (c_pl cx) ->
  getr (ms_regs ms) 19 = w64 (gSH cx fp) -> getr (ms_regs ms) 20 = w64 t ->
  getr (ms_regs ms) 21 = w64 (GrantSlotPlan.nset (c_pl cx) - Z.of_nat i) ->
  getr (ms_regs ms) 23 = w64 (c_p cx + Z.of_nat (gpos (c_pl cx) i)) ->
  getr (ms_regs ms) 12 = w64 (c_n cx - Z.of_nat (gpos (c_pl cx) i)) ->
  getr (ms_regs ms) 13 = w64 1 ->
  gmem cx fp W3 ms t (gTi (c_pl cx) i) (gwsi (c_pl cx) i) (gsti (c_pl cx) i) ->
  GI_set B MT cx fp k acc ly3 S3 W3 ms md.
Proof.
  intros cx fp k acc ly3 S3 W3 ms md i t (Pc & Prv & Psv & Pro & Pfr & Pfc & G2 & G8 & G9 & G3 & G4)
    Hk Hacc Hbl Ht0 Hn Hi R19 R20 R21 R23 R12 R13
    ((Hsv1 & Hsv2) & Hsh & Hfl & Hin & (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12) & HT & Hws & Hst).
  pose proof (gtables_inv (c_pl cx) i) as (L1 & L2 & L3 & I1i & Hri).
  assert (HinT : In (t, 460) (ablocks B ly3 S3)) by (unfold gblk1 in Hbl; rewrite Hbl; apply in_or_app; right; left; reflexivity).
  exists i, t. rewrite gtables_eta. unfold ge_body, gtab, gregs, gsaved. unfold gtabb in HT.
  unfold gpos in *.
  splits; try assumption; apply GSH_tables_len.
Qed.

(* The turn's own facts, from GI_set. *)
Lemma of_set : forall cx fp k acc ly3 S3 W3 ms md,
  GI_set B MT cx fp k acc ly3 S3 W3 ms md -> exists i t,
  gmach cx ms GP_set /\ k <= 1 /\ acc <= GE_A1 MT /\ gblk1 B cx ly3 S3 t /\ 0 < t /\ c_n cx < 2 ^ 26 /\
  Z.of_nat i < GrantSlotPlan.nset (c_pl cx) /\
  getr (ms_regs ms) 19 = w64 (gSH cx fp) /\ getr (ms_regs ms) 20 = w64 t /\
  getr (ms_regs ms) 21 = w64 (GrantSlotPlan.nset (c_pl cx) - Z.of_nat i) /\
  getr (ms_regs ms) 23 = w64 (c_p cx + Z.of_nat (gpos (c_pl cx) i)) /\
  getr (ms_regs ms) 12 = w64 (c_n cx - Z.of_nat (gpos (c_pl cx) i)) /\
  getr (ms_regs ms) 13 = w64 1 /\
  gmem cx fp W3 ms t (gTi (c_pl cx) i) (gwsi (c_pl cx) i) (gsti (c_pl cx) i).
Proof.
  intros cx fp k acc ly3 S3 W3 ms md (i & t & Hb & Hk & Hacc & Hbl & Hn & Hi & R19 & R20 & R21 & R23 & R12 & R13 &
    M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & HTAB).
  rewrite gtables_eta in HTAB. destruct HTAB as ((Hin & Ht0 & HL & HT) & Hws & Hst & _ & _).
  destruct Hb as (Pc & Prv & Psv & Pro & Pfr & Pfc & (G2 & G8 & G9 & G3 & G4) & (Hsv1 & Hsv2) & Hsh & Hfl & _ & Hinp).
  exists i, t. unfold gmach, gregs, gmem, gsaved, gslots_set, gtabb, gpos. splits; assumption.
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
  unfold in_app in Happ, Htapp. unfold GE_STK, STK_LLVMFuzzerTestOneInput in *.
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
  rewrite IMG_LO_B_val in HBlo.
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

(* The turn's memory after a run whose only window was slot 104, which now holds v'. *)
Lemma gmem_w104 : forall cx fp t ly3 W3 ms ms' T ws st,
  glayout cx fp t ly3 -> c_n cx < 2 ^ 26 -> length ws = 144%nat -> length st = 144%nat ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 104 <= a < c_sp1 cx + 112) ->
     aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms) a) ->
  gmem cx fp W3 ms t T ws st -> gmem cx fp W3 ms' t T ws st.
Proof.
  intros cx fp t ly3 W3 ms ms' T ws st HL Hn LW LS HK
    (Hsv & Hsh & Hfl & Hin & Hmid & HT & Hws & Hst).
  pose proof HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15 & L16).
  pose proof (proj1 alloc_ceiling_val) as AC. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *.
  assert (HgF8 : 0 <= gF cx fp / 8 /\ gF cx fp / 8 + 1024 < 2 ^ 44)
    by (split; [apply Z.div_pos; lia | assert (gF cx fp / 8 < 2 ^ 44 - 1024) by (apply Z.div_lt_upper_bound; lia); lia]).
  assert (RDK : forall a v0, c_sp1 cx <= a -> a + 8 <= 2 ^ 64 ->
     (a + 8 <= c_sp1 cx + 104 \/ c_sp1 cx + 112 <= a) ->
     rdword (aview SEGS (w_H W3) (ms_mem ms)) a = Some v0 -> rdword (aview SEGS (w_H W3) (ms_mem ms')) a = Some v0).
  { intros a v0 H1 H2 H3 H. rewrite (rdword_tr (aview SEGS (w_H W3) (ms_mem ms)) (aview SEGS (w_H W3) (ms_mem ms')) a); [exact H|].
    intros j Hj. apply HK; lia. }
  assert (GA : forall p L, (forall a, p <= a < p + Z.of_nat (length L) -> 0 <= a < c_sp1 cx + 104) ->
     garr8 SEGS (mrestrict (w_H W3) (ms_mem ms)) p L -> garr8 SEGS (mrestrict (w_H W3) (ms_mem ms')) p L).
  { intros p L HR HG. apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) (ms_mem ms) (ms_mem ms') p L); [|exact HG].
    intros a Ha. pose proof (HR a Ha). apply HK; lia. }
  destruct Hsv as [Hra Hsv]. destruct Hmid as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12).
  unfold gmem, gsaved, gshadow, gslots_set, gslot, gfarr, gtabb in *.
  split; [split|].
  { apply RDK; [lia | lia | lia | exact Hra]. }
  { intros j Hj. apply RDK; [lia | lia | lia | apply Hsv, Hj]. }
  split.
  { intros j Hj. rewrite GSH_tables_len in Hj. unfold GE_NSH in Hj.
    rewrite HK; [apply Hsh; rewrite GSH_tables_len; unfold GE_NSH; exact Hj | lia | lia]. }
  split.
  { rewrite (rdword_tr (aview SEGS (w_H W3) (ms_mem ms)) (aview SEGS (w_H W3) (ms_mem ms')) (gF cx fp + 1016)); [exact Hfl|].
    intros j Hj. apply HK; lia. }
  split.
  { apply GA; [|exact Hin]. intros a Ha. rewrite length_map in Ha. fold (c_n cx) in Ha.
    destruct (L16 ltac:(lia)) as (P1 & P2 & P3 & P4 & P5). lia. }
  split; [splits; apply RDK; first [lia | assumption]|].
  split; [intros j H1 H2 H3 H4; rewrite HK; [apply HT; assumption | lia | lia]|].
  split; apply GA; first [assumption | intros a Ha; rewrite length_map in Ha; unfold GO_WAS, GO_SET in Ha; lia].
Qed.

(* The turn's memory, after a run whose windows were slot 104 and one byte of each array. *)
Lemma gmem_win3 : forall cx fp t ly3 W3 ms ms' T ws st ws' st' a1 a2,
  glayout cx fp t ly3 -> c_n cx < 2 ^ 26 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 104 <= a < c_sp1 cx + 112 \/ a = a1 \/ a = a2) ->
     aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms) a) ->
  gF cx fp + 32 <= a1 < gF cx fp + 176 -> gF cx fp + 240 <= a2 < gF cx fp + 384 ->
  gfarr cx fp W3 ms' GO_WAS ws' -> gfarr cx fp W3 ms' GO_SET st' ->
  gmem cx fp W3 ms t T ws st -> gmem cx fp W3 ms' t T ws' st'.
Proof.
  intros cx fp t ly3 W3 ms ms' T ws st ws' st' a1 a2 HL Hn HK Ha1 Ha2 Hws' Hst'
    (Hsv & Hsh & Hfl & Hin & Hmid & HT & Hws & Hst).
  pose proof HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15 & L16).
  pose proof (proj1 alloc_ceiling_val) as AC. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *.
  assert (HgF8 : 0 <= gF cx fp / 8 /\ gF cx fp / 8 + 1024 < 2 ^ 44)
    by (split; [apply Z.div_pos; lia | assert (gF cx fp / 8 < 2 ^ 44 - 1024) by (apply Z.div_lt_upper_bound; lia); lia]).
  assert (KS : forall a, c_sp1 cx <= a < 2 ^ 64 -> ~ (c_sp1 cx + 104 <= a < c_sp1 cx + 112) ->
     aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms) a)
    by (intros a Ha Hw; apply HK; [lia | intros [H|[H|H]]; [exact (Hw H) | lia | lia]]).
  assert (RDK : forall a v0, c_sp1 cx <= a -> a + 8 <= 2 ^ 64 ->
     (a + 8 <= c_sp1 cx + 104 \/ c_sp1 cx + 112 <= a) ->
     rdword (aview SEGS (w_H W3) (ms_mem ms)) a = Some v0 -> rdword (aview SEGS (w_H W3) (ms_mem ms')) a = Some v0).
  { intros a v0 H1 H2 H3 H. rewrite (rdword_tr (aview SEGS (w_H W3) (ms_mem ms)) (aview SEGS (w_H W3) (ms_mem ms')) a); [exact H|].
    intros j Hj. apply KS; lia. }
  destruct Hsv as [Hra Hsv]. destruct Hmid as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12).
  unfold gmem, gsaved, gshadow, gslots_set, gslot, gfarr, gtabb in *.
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
(* The stack slots the accepted path of a turn reads, at s1 (x9): the bitwise NOT of the
   two array addresses (slots 112, 120; atoms 32, 33), the two array addresses (slots
   128, 136; atoms 34, 35), the shadow offset (slot 144) and the table (slot 152; atom
   36). The turn writes none of them, so the region has no write window. *)
Definition R_stk : YP09.region :=
  YP09.mkRegion (Some 9%nat) 112 160 112 112
    [YP09.mkChunk 112 (CVal 8 (SOff 32 0)); YP09.mkChunk 120 (CVal 8 (SOff 33 0));
     YP09.mkChunk 128 (CVal 8 (SOff 34 0)); YP09.mkChunk 136 (CVal 8 (SOff 35 0));
     YP09.mkChunk 144 (CVal 8 (SLit GSB)); YP09.mkChunk 152 (CVal 8 (SOff 36 0))].

Lemma R_stk_ok : forall cx fp t ly3 W3 ms3 E,
  glayout cx fp t ly3 ->
  ew E 9 = w64 (c_sp1 cx) ->
  ew E 32 = w64 (2 ^ 64 - 1 - (gF cx fp + GO_SET)) -> ew E 33 = w64 (2 ^ 64 - 1 - (gF cx fp + GO_WAS)) ->
  ew E 34 = w64 (gF cx fp + GO_SET) -> ew E 35 = w64 (gF cx fp + GO_WAS) -> ew E 36 = w64 t ->
  gslots_set cx fp t W3 ms3 ->
  region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3)) R_stk.
Proof.
  intros cx fp t ly3 W3 ms3 E HL E9 E32 E33 E34 E35 E36
    (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12).
  pose proof HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & _ & _ & _ & L12 & L13 & _).
  pose proof (proj1 alloc_ceiling_val) as AC.
  unfold region_ok, R_stk. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E9. unfold w64. rewrite unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  unfold gslot in *.
  repeat apply Forall_cons; try apply Forall_nil.
  - apply (chunk_ok_val SEGS E _ (c_sp1 cx) 112 8 (SOff 32 0) (2 ^ 64 - 1 - (gF cx fp + GO_SET)));
      [apply gsv0; [exact E32 | unfold GO_SET; lia] | cbn; unfold GO_SET; lia | cbn; lia |].
    exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ M7).
  - apply (chunk_ok_val SEGS E _ (c_sp1 cx) 120 8 (SOff 33 0) (2 ^ 64 - 1 - (gF cx fp + GO_WAS)));
      [apply gsv0; [exact E33 | unfold GO_WAS; lia] | cbn; unfold GO_WAS; lia | cbn; lia |].
    exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ M8).
  - apply (chunk_ok_val SEGS E _ (c_sp1 cx) 128 8 (SOff 34 0) (gF cx fp + GO_SET));
      [apply gsv0; [exact E34 | unfold GO_SET; lia] | cbn; unfold GO_SET; lia | cbn; lia |].
    exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ M9).
  - apply (chunk_ok_val SEGS E _ (c_sp1 cx) 136 8 (SOff 35 0) (gF cx fp + GO_WAS));
      [apply gsv0; [exact E35 | unfold GO_WAS; lia] | cbn; unfold GO_WAS; lia | cbn; lia |].
    exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ M10).
  - apply (chunk_ok_val SEGS E _ (c_sp1 cx) 144 8 (SLit GSB) SHADOW_OFF); [reflexivity | cbn; unfold SHADOW_OFF; lia | cbn; lia |].
    exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ M11).
  - apply (chunk_ok_val SEGS E _ (c_sp1 cx) 152 8 (SOff 36 0) t);
      [apply gsv0; [exact E36 | lia] | cbn; lia | cbn; lia |].
    exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ M12).
Qed.

(* ---- 0x810b4 .. 0x81140: an accepted set's value read back, and the two stores ---- *)
(* The return of reac_headamp_tx_effective after an accepted set: a0 holds the value
   read back, which is the value set; s6 holds 1, the `channel < 48` flag image B's
   array-bound guard at 0x810b8 tests. *)
Definition GE2 (n i : nat) (cx : ecx) (fp k acc : Z) ly3 S3 W3 (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t, gcore cx fp k acc ly3 S3 ms3 0x678 n i t /\ gacc (c_pl cx) i = true /\
  gmem cx fp W3 ms3 t (gTi (c_pl cx) (S i)) (gwsi (c_pl cx) i) (gsti (c_pl cx) i) /\
  getr (ms_regs ms3) 10 = w64 (gv (c_pl cx) i) /\ getr (ms_regs ms3) 18 = w64 (gc (c_pl cx) i) /\
  getr (ms_regs ms3) 22 = w64 1 /\
  getr (ms_regs ms3) 24 = w64 (gq (c_pl cx) i) /\ getr (ms_regs ms3) 25 = w64 (gv (c_pl cx) i) /\
  getr (ms_regs ms3) 23 = w64 (c_p cx + Z.of_nat (gpos (c_pl cx) (S i))) /\
  getr (ms_regs ms3) 26 = w64 (c_n cx - Z.of_nat (gpos (c_pl cx) (S i))).

(* The two cells the turn stores into, each a one-byte region at its own atom (37 for
   was_set[ch][param], 38 for set_to[ch][param]); the addresses the code computes
   (0x810d4..0x810e4 and 0x8110c..0x8111c: the array's slot, plus 3ch, plus the
   parameter) are aliased to those atoms. *)
Definition R_c1 : YP09.region := YP09.mkRegion (Some 37%nat) 0 1 0 1 [].
Definition R_c2 : YP09.region := YP09.mkRegion (Some 38%nat) 0 1 0 1 [].
Definition SV3 : sv := SAlu ALU_ADD (SAlu ALU_SLL (SOff 18 0) (SLit 1)) (SOff 18 0).
Definition XW : sv := SAlu ALU_ADD (SAlu ALU_ADD (SOff 35 0) SV3) (SOff 24 0).
Definition XS : sv := SAlu ALU_ADD (SAlu ALU_ADD (SOff 34 0) SV3) (SOff 24 0).
Definition PTRA (al : Z) : afact := mkAF 4096 140737479966720 al.

Lemma denot_cells : forall E b c q,
  ew E 18 = Z_to_bv 64 c -> ew E 24 = Z_to_bv 64 q -> 0 <= c < 48 -> 0 <= q < 3 ->
  0 <= b -> b + 3 * c + q < 2 ^ 64 ->
  (ew E 35 = Z_to_bv 64 b -> sv_denot E XW = Z_to_bv 64 (b + (3 * c + q))) /\
  (ew E 34 = Z_to_bv 64 b -> sv_denot E XS = Z_to_bv 64 (b + (3 * c + q))).
Proof.
  intros E b c q Hc Hq Hcr Hqr Hb Hlt.
  assert (U3 : U E SV3 = 3 * c).
  { unfold SV3. rewrite !U_SAlu. cbn [zalu_raw].
    rewrite (U_atom E 18 c Hc) by lia. rewrite U_SLit, (zcanon_id 1) by (unfold M64; lia).
    change (Z.land 1 63) with 1. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
    rewrite (zcanon_id (c * 2)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia. }
  split; intros Hb'; rewrite denot_lit_U; f_equal.
  - unfold XW. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu, U3. cbn [zalu_raw].
    rewrite (U_atom E 35 b Hb'), (U_atom E 24 q Hq) by lia.
    rewrite (zcanon_id (b + 3 * c)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
  - unfold XS. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu, U3. cbn [zalu_raw].
    rewrite (U_atom E 34 b Hb'), (U_atom E 24 q Hq) by lia.
    rewrite (zcanon_id (b + 3 * c)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

Ltac ewE := cbn [ew ewset Nat.eqb] in *; rewrite ?ew_ewset_other in * by lia.

(* ---- the returns of reac_headamp_tx_set ---- *)
(* Common to the three: the cut holds turn i, the table is the one the set left
   (gTi (S i): the set cell when the set is accepted), the two arrays are still those of
   turn i, and a0 is the set's answer. *)

(* 0x80ffc (offset 0x5c0), the return of the call at 0x80ff8 (the cell had two bytes or
   more): s2, s8 and s9 hold the channel, the parameter and the value (0 for a byte past
   the end), s11 the cursor past the cell, slot 104 the bytes left after it. *)
Definition GA2 (n i : nat) (cx : ecx) (fp k acc : Z) ly3 S3 W3 (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t, gcore cx fp k acc ly3 S3 ms3 0x5c0 n i t /\
  (gpos (c_pl cx) i + 2 <= length (c_pl cx))%nat /\
  gmem cx fp W3 ms3 t (gTi (c_pl cx) (S i)) (gwsi (c_pl cx) i) (gsti (c_pl cx) i) /\
  gslot cx W3 ms3 104 (c_n cx - Z.of_nat (gpos (c_pl cx) (S i))) /\
  getr (ms_regs ms3) 10 = w64 (if gacc (c_pl cx) i then 0 else -1) /\
  getr (ms_regs ms3) 18 = w64 (gc (c_pl cx) i) /\ getr (ms_regs ms3) 24 = w64 (gq (c_pl cx) i) /\
  getr (ms_regs ms3) 25 = w64 (gv (c_pl cx) i) /\
  getr (ms_regs ms3) 27 = w64 (c_p cx + Z.of_nat (gpos (c_pl cx) (S i))).

(* 0x80f9c (offset 0x560), the return of the call at 0x80f98 (the cell had one byte): s2
   holds the channel, s11 the cursor past it; slot 104 is not read on this path. *)
Definition GA1 (n i : nat) (cx : ecx) (fp k acc : Z) ly3 S3 W3 (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t, gcore cx fp k acc ly3 S3 ms3 0x560 n i t /\
  length (c_pl cx) = (gpos (c_pl cx) i + 1)%nat /\
  gmem cx fp W3 ms3 t (gTi (c_pl cx) (S i)) (gwsi (c_pl cx) i) (gsti (c_pl cx) i) /\
  getr (ms_regs ms3) 10 = w64 (if gacc (c_pl cx) i then 0 else -1) /\
  getr (ms_regs ms3) 18 = w64 (gc (c_pl cx) i) /\
  getr (ms_regs ms3) 27 = w64 (c_p cx + Z.of_nat (gpos (c_pl cx) (S i))).

(* 0x80f70 (offset 0x534), the return of the call at 0x80f6c (no byte left): s7 is still
   the cursor, which does not move, and slot 104 is not read on this path. *)
Definition GA0 (n i : nat) (cx : ecx) (fp k acc : Z) ly3 S3 W3 (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t, gcore cx fp k acc ly3 S3 ms3 0x534 n i t /\
  length (c_pl cx) = gpos (c_pl cx) i /\
  gmem cx fp W3 ms3 t (gTi (c_pl cx) (S i)) (gwsi (c_pl cx) i) (gsti (c_pl cx) i) /\
  getr (ms_regs ms3) 10 = w64 (if gacc (c_pl cx) i then 0 else -1) /\
  getr (ms_regs ms3) 23 = w64 (c_p cx + Z.of_nat (gpos (c_pl cx) i)).

(* What 0x81018, 0x81024 and 0x81028 share: turn i, the table the set left, the arrays
   of turn i, s10 = the set's answer, s2 s8 s9 = the channel, the parameter and the
   value, s11 = the cursor past the cell, slot 104 = the bytes left after it. *)
Definition gb_at (pc : Z) (n i : nat) (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate)
  (W3 : world SEGS) (ms3 : machine_state) (t : Z) : Prop :=
  gcore cx fp k acc ly3 S3 ms3 pc n i t /\
  gmem cx fp W3 ms3 t (gTi (c_pl cx) (S i)) (gwsi (c_pl cx) i) (gsti (c_pl cx) i) /\
  gslot cx W3 ms3 104 (c_n cx - Z.of_nat (gpos (c_pl cx) (S i))) /\
  getr (ms_regs ms3) 26 = w64 (if gacc (c_pl cx) i then 0 else -1) /\
  getr (ms_regs ms3) 18 = w64 (gc (c_pl cx) i) /\ getr (ms_regs ms3) 24 = w64 (gq (c_pl cx) i) /\
  getr (ms_regs ms3) 25 = w64 (gv (c_pl cx) i) /\
  getr (ms_regs ms3) 27 = w64 (c_p cx + Z.of_nat (gpos (c_pl cx) (S i))).

(* 0x81028 (offset 0x5ec): the harness computes its own answer. *)
Definition GAB (n i : nat) (cx : ecx) (fp k acc : Z) ly3 S3 W3 (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t, gb_at 0x5ec n i cx fp k acc ly3 S3 W3 ms3 t.

(* 0x81018 (offset 0x5dc) and 0x81024 (offset 0x5e8): a callee returned 0 for a parameter
   of 3 or more. *)
Definition GAR (pc : Z) (n i : nat) (cx : ecx) (fp k acc : Z) ly3 S3 W3 (ms3 : machine_state) (md3 : Model) : Prop :=
  exists t, gb_at pc n i cx fp k acc ly3 S3 W3 ms3 t /\ 3 <= gq (c_pl cx) i /\ getr (ms_regs ms3) 10 = w64 0.

(* ---- the pieces of a turn, as LLVMFEntrySet.v composes them ---- *)
(* HEAD: 0x80ef8 → the call of reac_headamp_tx_set at 0x80f6c, 0x80f98 or 0x80ff8. *)
Definition seg_head_stmt : Prop := forall POST n,
  (forall i, ge_from B MT POST (GA0 n i)) -> (forall i, ge_from B MT POST (GA1 n i)) ->
  (forall i, ge_from B MT POST (GA2 n i)) -> ge_from B MT POST (GIn n).
(* GA0, GA1, GA2 → the check of the set's answer at 0x81064 / 0x81098 / 0x8107c → 0x81140
   (refused) or the call of reac_headamp_tx_effective at 0x810b0 (accepted); GA2 first
   calls reac_headamp_tx_effective at 0x81014 and reac_headamp_default at 0x81020 when
   the parameter is 3 or more. *)
Definition seg_ga0_stmt : Prop := forall POST n i,
  ge_from B MT POST (G78 n i) -> ge_from B MT POST (GE2 n i) -> ge_from B MT POST (GA0 n i).
Definition seg_ga1_stmt : Prop := forall POST n i,
  ge_from B MT POST (G78 n i) -> ge_from B MT POST (GE2 n i) -> ge_from B MT POST (GA1 n i).
Definition seg_ga2_stmt : Prop := forall POST n i,
  ge_from B MT POST (G78 n i) -> ge_from B MT POST (GE2 n i) -> ge_from B MT POST (GA2 n i).

(* The call of reac_headamp_tx_effective at 0x810b0 after an accepted set, which GA0, GA1
   and GA2 all reach: at the callee's entry, with a0 a1 a2 = the table, the channel and
   the parameter and the return address BASE + 0x678, it lands in GE2. *)
Definition call_e2_stmt : Prop := forall (POST : ecx -> world SEGS -> config -> Prop) n i
    cx fp k acc ly3 S3 W3 (regs : bvmap 5 word) mem md t,
  ge_from B MT POST (GE2 n i) ->
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 mem md k ->
  frames S3 = [(GE_CID, fp)] -> mo_le MT (c_S cx) S3 acc ->
  k <= 1 -> acc <= GE_A1 MT -> gblk1 B cx ly3 S3 t -> 0 < t -> c_n cx < 2 ^ 26 ->
  GrantSlotPlan.nset (c_pl cx) = Z.of_nat i + Z.of_nat (S n) -> gacc (c_pl cx) i = true ->
  getr regs 1 = Z_to_bv 64 (BASE + 0x678) ->
  getr regs 2 = w64 (c_sp1 cx) -> getr regs 8 = w64 (spZ (c_regs cx)) -> getr regs 9 = w64 (c_sp1 cx) ->
  getr regs 3 = getr (c_regs cx) 3 -> getr regs 4 = getr (c_regs cx) 4 ->
  getr regs 10 = w64 t -> getr regs 11 = w64 (gc (c_pl cx) i) -> getr regs 12 = w64 (gq (c_pl cx) i) ->
  getr regs 18 = w64 (gc (c_pl cx) i) -> getr regs 19 = w64 (gSH cx fp) -> getr regs 20 = w64 t ->
  getr regs 21 = w64 (Z.of_nat (S n)) -> getr regs 22 = w64 1 ->
  getr regs 23 = w64 (c_p cx + Z.of_nat (gpos (c_pl cx) (S i))) ->
  getr regs 24 = w64 (gq (c_pl cx) i) -> getr regs 25 = w64 (gv (c_pl cx) i) ->
  getr regs 26 = w64 (c_n cx - Z.of_nat (gpos (c_pl cx) (S i))) ->
  gmem cx fp W3 (mkst regs (Z_to_bv 64 (BASE + AF_reac_headamp_tx_effective)) mem (seg_rom SEGS)) t
    (gTi (c_pl cx) (S i)) (gwsi (c_pl cx) i) (gsti (c_pl cx) i) ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_reac_headamp_tx_effective)) mem (seg_rom SEGS)) md) (POST cx).

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
Lemma fbyte_iff : forall i, ALay.tx_fbyte i = true <-> (0 <= i < 460 /\ i <> 438 /\ i <> 439 /\ i <> 451).
Proof.
  intros i. split.
  - intros H. pose proof (ALay.tx_fbyte_range i H) as Hr.
    split; [exact Hr|]. split; [|split]; intros ->; vm_compute in H; discriminate H.
  - intros (Hr & H1 & H2 & H3).
    assert (Hb : forallb (fun n => orb (orb (orb (Nat.eqb n 438) (Nat.eqb n 439)) (Nat.eqb n 451)) (ALay.tx_fbyte (Z.of_nat n)))
                   (seq 0 460) = true) by (vm_compute; reflexivity).
    rewrite forallb_forall in Hb.
    specialize (Hb (Z.to_nat i) (proj2 (in_seq 460 0 (Z.to_nat i)) ltac:(lia))).
    rewrite Z2Nat.id in Hb by lia.
    apply orb_prop in Hb as [Hb | Hb]; [|exact Hb]. exfalso.
    repeat (apply orb_prop in Hb as [Hb | Hb]); apply Nat.eqb_eq in Hb; lia.
Qed.

Lemma gtabb_obj : forall W3 ms3 t T,
  gtabb W3 ms3 t T -> obj_at SEGS (mrestrict (w_H W3) (ms_mem ms3)) t ALay.LAY_TX (ALay.tx_vals T).
Proof.
  intros W3 ms3 t T H4. apply (proj2 (ALay.tx_obj_bytes SEGS _ t T)).
  intros i Hi. apply fbyte_iff in Hi as (Hr & H1 & H2 & H3).
  specialize (H4 i Hr H1 H2 H3). unfold aview in H4.
  destruct (mbyte SEGS (mrestrict (w_H W3) (ms_mem ms3)) (t + i)) as [b|]; [|discriminate H4].
  cbn [option_map] in H4. injection H4 as H4. f_equal. apply bv_eq. rewrite H4. reflexivity.
Qed.

Lemma gtab_obj : forall cx ly3 S3 W3 ms3 t T,
  gtab B cx ly3 S3 W3 ms3 t T -> obj_at SEGS (mrestrict (w_H W3) (ms_mem ms3)) t ALay.LAY_TX (ALay.tx_vals T).
Proof. intros cx ly3 S3 W3 ms3 t T (_ & _ & _ & H4). exact (gtabb_obj W3 ms3 t T H4). Qed.

Lemma obj_gtabb : forall W3 ms3 t T,
  obj_at SEGS (mrestrict (w_H W3) (ms_mem ms3)) t ALay.LAY_TX (ALay.tx_vals T) -> gtabb W3 ms3 t T.
Proof.
  intros W3 ms3 t T HO i Hr H1 H2 H3.
  assert (Hf : ALay.tx_fbyte i = true) by (apply fbyte_iff; auto).
  pose proof (proj1 (ALay.tx_obj_bytes SEGS _ t T) HO i Hf) as Hm.
  unfold aview. rewrite Hm. reflexivity.
Qed.

(* ---- the turn's memory across a call that writes nothing of it ---- *)
(* The bytes the turn's facts speak about: at or above s1, the input, the frame and its
   shadow, and the table. *)
Definition gkeep_at (cx : ecx) (fp t a : Z) : Prop :=
  c_sp1 cx <= a < 2 ^ 64 \/ c_p cx <= a < c_p cx + c_n cx \/ gF cx fp <= a < gF cx fp + 1024 \/
  gSH cx fp <= a < gSH cx fp + 128 \/ t <= a < t + 460.

Lemma gmem_trK : forall cx fp t ly3 W3 ms ms' T ws st,
  glayout cx fp t ly3 -> length ws = 144%nat -> length st = 144%nat ->
  (forall a, gkeep_at cx fp t a -> aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms) a) ->
  gmem cx fp W3 ms t T ws st -> gmem cx fp W3 ms' t T ws st.
Proof.
  intros cx fp t ly3 W3 ms ms' T ws st HL Hlw Hls HK (Hsv & Hsh & Hfl & Hin & Hmid & HT & Hws & Hst).
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
  destruct Hsv as [Hra Hsv]. destruct Hmid as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12).
  unfold gmem, gsaved, gshadow, gslots_set, gslot, gfarr, gtabb in *.
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

End c.
End b.
End a.
