(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySchedTurnCr), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AF0s.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySchedTurnCr.v, with its module paths, module names and numbers changed; 439 of its 538 lines of code are new or changed and 248 lines of the source are left out. *)
(* The image-B (UBSan) walk of the frame-loop turn's segment E,
   over image B's own addresses, registers, spill slots and UBSan guards; the shape is image A's.
   Ported from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySchedTurnE.v at e6bd82f51c9. *)
(* The frame-loop turn of LLVMFuzzerTestOneInput (0x80a3c) on the ASan+UBSan build, segment E:
   0x81c48 (GP_scn: want_of has agreed with the value) .. 0x81d5c (GP_end, the cut TF)
   (LLVMFEntrySchedTurnDefs.v). The stretch reads was_set[3c+p] twice, checks the scheduler's scene
   window when the input left that cell unset, and counts the cell in unset_sent[3c+p]: the `sb` at
   0x81d4c is the only memory write of the turn outside the three cells and their shadow bytes.

   Every check is refuted from HeadampSched.frame_ok, never assumed:
     0x81ca8 beqz s7      the scheduler's flag is 0: on this path frame_ok gives sw <> 0 and sb < 48
     0x81cb0 bltu a1,a0   c < sb (slot 120): frame_ok gives sb <= c
     0x81cb8 bgeu a1,a0   c >= sb + sw (slot 104): frame_ok gives c < sb + sw
     0x81d58 bnez a1      the old unset_sent[3c+p] is not 0: frame_ok gives tb us (3c+p) = 0
   are split with psrr_branch_tok and refuted by hand. 0x81c50 and 0x81cbc (c > 47), 0x81c5c and
   0x81cc8 (p > 2) are decided not taken by the interval facts of the atoms the loads of ch and
   param give (0 <= c < 48 and 0 <= p < 3, from frame_ok); the second test of was_set at 0x81d10 by
   the condition the first test at 0x81ca4 added. The three shadow tokens 0x81c94, 0x81d00 and
   0x81d40 are taken by the token engine from the two shadow entries of the cells it reads: the
   frame-shadow bytes of was_set (4..21) and of unset_sent (72..89) are 0 in GSH_turn.

   Image B against image A's 0x816ac .. 0x81774:
   - The six UBSan pointer-overflow guards to the trap `unimp` at 0x81f48, which image A has not
     got. 0x81c6c, 0x81cd8 and 0x81d18 compare slot 88 = not (F + 32) and slot 80 = not (F + 576)
     against 3c; those slots become the atoms 40 and 41 with the interval [2^64 - 2^47, 2^64 - 1],
     so the facts decide the three against 3c <= 141. 0x81c7c, 0x81ce8 and 0x81d28 compare the
     `not` of was_set + 3c and of unset_sent + 3c against p; the engine has no interval for
     `x XOR -1`, so the two `not` values are aliased to the atoms 42 and 43 with the same interval
     (alias_ok is proved from lin_of_sound and PaNot.U_not_gen), and the facts decide the three
     against p <= 2.
   - The registers: 47 in s2 (A: s7), 2 in s11 (both), &ch in s6 (A: slot 104 into s3), the frame's
     shadow base in s3 (A: s6), the turn counter in s5 (A: s2), the scheduler's flag in s7 (A: the
     spill slot 120), and s4 and s6 are reloaded from slots 152 (the table) and 64 (&ch) after each
     read of was_set and after the count, so the cut TF finds the table in s4.
   - The slots: &param from slot 112 (A: the register s5), &was_set from slot 136 (A: 144),
     SHADOW_OFF from slot 144 (A: 152), sb from slot 120 (A: 96), sb + sw from slot 104 (A: 88),
     &unset_sent from slot 40 (A: 80). *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YC5d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaShadow PaRun.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantPa GrantPaLib.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC85 GrantFrame YC1h YC1g ACj1 GrantACjr.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantBContracts LLVMFEntryDefs LLVMFEntrySeat LLVMFEntrySchedTurnDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import PaNot.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require
HeadampModel NextModel GrantModel SlotNeeds_c GrantSlotPlan HeadampSched SegSetModel Seg_sched_turn HeadampLayout.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* As image A's segment E does for its whole file: no lia below reasons about / or mod (the two
   division facts are posed by hand with `dm` and `div8E`), and the cut's context carries several
   (gF mod 64, gF / 8, c_sp1 mod 32), which the euclidean-division translation would expand into
   every lia call; with the flag off they stay atoms. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* ---- the symbolic state at 0x81c48 ----
   Atoms past the registers: 32 ch, 33 param, 34 the address of was_set[ch][param]
   (F + 32 + 3 ch + param), 35 was_set[ch][param], 36 unset_sent[ch][param], 37 sb (slot 120),
   38 sb + sw (slot 104), 39 the table (slot 152), 40 not (F + 32) (slot 88), 41 not (F + 576)
   (slot 80), 42 not (F + 32 + 3 ch), 43 not (F + 576 + 3 ch). s6 (atom 22) holds F + 784. *)

(* The spill slots the segment reads: 40 &unset_sent, 64 &ch, 80 not &unset_sent, 88 not &was_set,
   104 sb + sw, 112 &param, 120 sb, 136 &was_set, 144 the shadow offset, 152 the table. *)
Definition stkE : YP09.region :=
  YP09.mkRegion (Some 9%nat) 40 160 0 0
    [ YP09.mkChunk 40 (CVal 8 (SOff 22 (-208))); YP09.mkChunk 64 (CVal 8 (SOff 22 0));
      YP09.mkChunk 80 (CVal 8 (SOff 41 0)); YP09.mkChunk 88 (CVal 8 (SOff 40 0));
      YP09.mkChunk 104 (CVal 8 (SOff 38 0)); YP09.mkChunk 112 (CVal 8 (SOff 22 16));
      YP09.mkChunk 120 (CVal 8 (SOff 37 0)); YP09.mkChunk 136 (CVal 8 (SOff 22 (-752)));
      YP09.mkChunk 144 (CVal 8 (SLit SHADOW_OFF)); YP09.mkChunk 152 (CVal 8 (SOff 39 0)) ].
(* A one-byte cell the segment only reads. *)
Definition cellE (n : nat) (o : Z) (a : nat) : YP09.region :=
  YP09.mkRegion (Some n) o (o + 1) 0 0 [YP09.mkChunk o (CVal 1 (SOff a 0))].
(* unset_sent[ch][param], at F + 576 + 3 ch + param = (atom 34) + 544: the segment writes it. *)
Definition unsetE : YP09.region :=
  YP09.mkRegion (Some 34%nat) 544 545 544 545 [YP09.mkChunk 544 (CVal 1 (SOff 36 0))].
Definition rs_E : YP09.smem := [stkE; cellE 22 0 32; cellE 22 16 33; cellE 34 0 35; unsetE].
(* The values the code builds, in the engine's linear normal form: 3 ch (`slli; add`), then
   F + 32 + 3 ch (slot 136 plus 3 ch) and F + 576 + 3 ch (slot 40 plus 3 ch). *)
Definition M3E : sv := SMd M_MUL (SOff 32 0) (SLit 3).
Definition WWE : sv := SAlu ALU_ADD (SOff 22 (-752)) M3E.
Definition WUE : sv := SAlu ALU_ADD (SOff 22 (-208)) M3E.
(* F + 32 + 3 ch + param, the address of was_set[ch][param]; the engine finds
   unset_sent[ch][param] through the same alias, 544 bytes on. *)
Definition XEa : sv := SAlu ALU_ADD WWE (SOff 33 0).
Definition G_E : facts :=
  mkFacts [ (32%nat, mkAF 0 47 0); (33%nat, mkAF 0 2 0); (34%nat, mkAF 4096 (2 ^ 47 - 32768) 0);
            (35%nat, mkAF 0 255 0); (36%nat, mkAF 0 255 0); (37%nat, mkAF 0 255 0);
            (38%nat, mkAF 0 510 0);
            (40%nat, mkAF (2 ^ 64 - 2 ^ 47) (2 ^ 64 - 1) 0); (41%nat, mkAF (2 ^ 64 - 2 ^ 47) (2 ^ 64 - 1) 0);
            (42%nat, mkAF (2 ^ 64 - 2 ^ 47) (2 ^ 64 - 1) 0); (43%nat, mkAF (2 ^ 64 - 2 ^ 47) (2 ^ 64 - 1) 0) ]
          []
          [ (XEa, SOff 34 0); (SAlu ALU_XOR WWE (SLit (-1)), SOff 42 0);
            (SAlu ALU_XOR WUE (SLit (-1)), SOff 43 0) ].
(* The shadow entries of the two cells the code checks: one byte each, and the unset_sent
   entry covers that cell's write window. *)
Definition SH_E : list shent := [ mkSHE 34 0 1; mkSHE 34 544 545 ].
Definition SpanE : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

Lemma tbrE : forall T k, 0 <= HeadampModel.tb T k < 256.
Proof.
  intros T k. unfold HeadampModel.tb.
  pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat k) T (Z_to_bv 8 0))) as H.
  change (bv_modulus 8) with 256 in H. exact H.
Qed.

Lemma nth_map_tbE : forall (l : list byte) j,
  nth j (map (fun b : byte => bv_unsigned b) l) 0 = HeadampModel.tb l (Z.of_nat j).
Proof.
  intros l j. unfold HeadampModel.tb. rewrite Nat2Z.id.
  rewrite <- (map_nth (fun b : byte => bv_unsigned b) l (Z_to_bv 8 0) j). reflexivity.
Qed.

Lemma div8E : forall F j, F mod 64 = 0 -> 0 <= j -> (F + j) / 8 = F / 8 + j / 8.
Proof.
  intros F j HF Hj. apply Z.mod_divide in HF; [|lia]. destruct HF as [q ->].
  replace (q * 64 + j) with (j + (8 * q) * 8) by lia. rewrite Z.div_add by lia.
  replace (q * 64) with ((8 * q) * 8) by lia. rewrite Z.div_mul by lia. lia.
Qed.

(* The shadow bytes of was_set and unset_sent are 0 while a turn runs. *)
Lemma GSH_turn_zeroE : forall j, (4 <= j < 22 \/ 72 <= j < 90) -> nth (Z.to_nat j) GSH_turn 0 = 0.
Proof.
  intros j Hj.
  assert (Hb : forallb (fun n => Z.eqb (nth n GSH_turn 0) 0) (seq 4 18 ++ seq 72 18) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in Hb. apply Z.eqb_eq. apply Hb. apply in_app_iff.
  destruct Hj as [Hj | Hj]; [left | right]; apply in_seq; lia.
Qed.

(* The linear normal forms of the three values the aliases name. *)
Lemma lin_XEa : lin_of XEa = Some ([(22%nat, 1); (32%nat, 3); (33%nat, 1)], -752).
Proof. vm_compute. reflexivity. Qed.
Lemma lin_WWE : lin_of WWE = Some ([(22%nat, 1); (32%nat, 3)], -752).
Proof. vm_compute. reflexivity. Qed.
Lemma lin_WUE : lin_of WUE = Some ([(22%nat, 1); (32%nat, 3)], -208).
Proof. vm_compute. reflexivity. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
#[local] Notation SIGMA := (pa_sigma).
#[local] Notation BASE := (pa_val A_TEXT).

(* A byte the runtime's view shows, as a one-byte value in memory. *)
Lemma val1E : forall H mem a v, aview SEGS H mem a = Some v ->
  val_mem SEGS (mrestrict H mem) a 1 v /\ 0 <= v < 256.
Proof.
  intros H mem a v Hv. unfold aview in Hv.
  destruct (mbyte SEGS (mrestrict H mem) a) as [b|] eqn:Hb; [|discriminate Hv].
  cbn [option_map] in Hv. injection Hv as <-.
  pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr. split; [|exact Hr].
  intros kk Hkk. assert (kk = 0%nat) by lia. subst kk. cbn [Z.of_nat]. rewrite Z.add_0_r, Hb. f_equal.
  rewrite (le_byte_small (bv_unsigned b) 1 0) by first [change (2 ^ (8 * Z.of_nat 1)) with 256; lia | lia].
  cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.shiftr_0_r.
  symmetry. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* A run keeps every byte outside its one write window. *)
Lemma keptE1 : forall E rs H (m m' : word -> option byte) A,
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  (forall a, in_wrange E rs a -> a = A) ->
  forall a, 0 <= a < 2 ^ 64 -> a <> A -> aview SEGS H m' a = aview SEGS H m a.
Proof.
  intros E rs H m m' A HF HW a Ha HA. apply (aview_kept_out E rs H m m' HF a Ha).
  intros Hw. exact (HA (HW a Hw)).
Qed.

Lemma cellE_ok : forall E m n o a b x, bv_unsigned (ew E n) = b -> ew E a = w64 x -> 0 <= x < 256 ->
  0 <= b + o -> b + o + 1 <= 2 ^ 64 -> val_mem SEGS m (b + o) 1 x -> region_ok SEGS E m (cellE n o a).
Proof.
  intros E m n o a b x Hb Ha Hx H0 H1 Hv. unfold region_ok, cellE.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Hb.
  split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|]. constructor; [|constructor].
  apply (chunk_ok_val SEGS E m b o 1 (SOff a 0) x).
  - rewrite ge_sv_SOff0, Ha. reflexivity.
  - cbn. lia.
  - cbn. lia.
  - exact Hv.
Qed.

Lemma unsetE_ok : forall E m b x, bv_unsigned (ew E 34) = b -> ew E 36 = w64 x -> 0 <= x < 256 ->
  0 <= b -> b + 545 <= 2 ^ 64 -> writable_at SEGS m (b + 544) -> val_mem SEGS m (b + 544) 1 x ->
  region_ok SEGS E m unsetE.
Proof.
  intros E m b x Hb Ha Hx H0 H1 Hw Hv. unfold region_ok, unsetE.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Hb.
  split; [lia|]. split; [lia|]. split; [intros o' Ho'; replace o' with 544 by lia; exact Hw|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E m b 544 1 (SOff 36 0) x).
  - rewrite ge_sv_SOff0, Ha. reflexivity.
  - cbn. lia.
  - cbn. lia.
  - exact Hv.
Qed.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Variable POST : ecx -> world SEGS -> config -> Prop.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
(* The names of LLVMFEntrySchedTurnDefs.v at this section's asyms, meter and laws. Image B has
   no segment D, so image A's TD has no twin. The lane's own names this file uses (`gslots_turn`,
   `gtregs`, `gwr`, `BxL`, `GSH_turn`) take none of B, MT and LAWS, so they need no abbreviation. *)
#[local] Notation tbody := (tbody B MT).
#[local] Notation tcom := (tcom B MT).
#[local] Notation GSn := (GSn B MT).
#[local] Notation TB := (TB B MT).
#[local] Notation trec := (trec B MT).
#[local] Notation TC := (TC B MT).
#[local] Notation TCr := (TCr B MT).
#[local] Notation TE := (TE B MT).
#[local] Notation TF := (TF B MT).
#[local] Notation gtracked := (gtracked B).
#[local] Notation gctx := (gctx B MT LAWS).
#[local] Notation gaddr_ok := (gaddr_ok B).
#[local] Notation ginput_ok := (ginput_ok B MT LAWS).
#[local] Notation tbody_keep := (tbody_keep B MT).
#[local] Notation tcom_keep := (tcom_keep B MT).
#[local] Notation gpres := (gpres B MT LAWS).
#[local] Notation gtracked_rng := (gtracked_rng B MT LAWS).
#[local] Notation table_out := (table_out B MT LAWS).
#[local] Notation gtab_keep := (gtab_keep B).

(* One byte of the frame's checked cells: its shadow byte is 0, so the byte is addressable,
   and the byte lies apart from the shadow. *)
Lemma shentE : forall cx fp W3 ms3 E (n : nat) lo off k,
  gshadow cx fp W3 ms3 GSH_turn -> gF cx fp mod 64 = 0 -> in_app (gF cx fp) 1024 ->
  U E (SOff n 0) = gF cx fp + off + k - lo -> 0 <= off + k < 1024 ->
  (4 <= (off + k) / 8 < 22 \/ 72 <= (off + k) / 8 < 90) ->
  shent_ok SEGS BxL E (mrestrict (w_H W3) (ms_mem ms3)) (mkSHE n lo (lo + 1)).
Proof.
  intros cx fp W3 ms3 E n lo off k Hsh HF64 HFapp HU Hr Hj.
  pose proof asan_consts as (C1 & _).
  assert (HBx : U E BxL = SHADOW_OFF)
    by (unfold BxL; rewrite U_SLit; apply zcanon_id; unfold M64, SHADOW_OFF; lia).
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HBx, HU. split.
  - intros x Hx. replace x with (gF cx fp + (off + k)) by lia.
    exists 0. split; [|left; reflexivity].
    unfold shadow_of_addr. rewrite (div8E _ _ HF64) by lia.
    assert (Hjl : (Z.to_nat ((off + k) / 8) < length GSH_turn)%nat)
      by (rewrite GSH_turn_len; unfold GE_NSH; lia).
    pose proof (Hsh _ Hjl) as Hv. rewrite Z2Nat.id in Hv by lia.
    rewrite (GSH_turn_zeroE ((off + k) / 8) Hj) in Hv.
    change (rd_of SEGS (mrestrict (w_H W3) (ms_mem ms3))) with (aview SEGS (w_H W3) (ms_mem ms3)).
    unfold gSH, shadow_of_addr in Hv. rewrite Z.add_assoc. exact Hv.
  - intros a Ha. rewrite Z.min_l in Ha by lia. rewrite Z.max_r in Ha by lia.
    unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

(* A branch condition as an arithmetic fact on the atoms' values. *)
Ltac hczE Hc :=
  rewrite ?branch_ne_U, ?branch_eq_U, ?branch_ltu_U, ?branch_geu_U in Hc;
  rewrite ?U_SOff, ?U_SLit in Hc;
  cbn [ew ewset Nat.eqb] in Hc;
  repeat match goal with Hu : bv_unsigned (ew ?Ex ?n) = _ |- _ =>
    match type of Hc with context [bv_unsigned (ew Ex n)] => rewrite Hu in Hc end end;
  rewrite ?Z.add_0_r in Hc;
  repeat (rewrite zcanon_id in Hc by (unfold M64; lia));
  first [ apply negb_true_iff, Z.eqb_neq in Hc | apply negb_false_iff, Z.eqb_eq in Hc
        | apply negb_true_iff, Z.ltb_ge in Hc | apply negb_false_iff, Z.ltb_lt in Hc
        | apply Z.eqb_eq in Hc | apply Z.eqb_neq in Hc | apply Z.ltb_lt in Hc | apply Z.ltb_ge in Hc ].

(* The write windows of a run, as one address. *)
Ltac inwE U34 :=
  let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hw := fresh "Hw" in
  intros a (r & Hr & Hw);
  lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
  repeat (destruct Hr as [<- | Hr];
          [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val ew ewset Nat.eqb] in Hw; rewrite ?U34 in Hw; lia | ]);
  destruct Hr.

(* The runs since 0x81c48 keep every byte but unset_sent[ch][param]. *)
Ltac keptE U34 A :=
  let a := fresh "a" in let Ha := fresh "Ha" in let HA := fresh "HA" in
  intros a Ha HA;
  repeat match goal with
  | HFx : frame_of ?Ex ?rsx (mrestrict ?Hh (ms_mem ?m0)) (mrestrict ?Hh (ms_mem ?m1)) |- aview _ _ (ms_mem ?m1) a = _ =>
      rewrite (keptE1 Ex rsx Hh (ms_mem m0) (ms_mem m1) A HFx ltac:(inwE U34) a Ha HA); clear HFx
  end; reflexivity.

(* A register at the end of a run, from the symbolic state: an atom register of the run's start
   (EE), the table reloaded from slot 152 (atom 39), or a literal the cut's register holds. *)
Ltac gregE HS EE :=
  lazymatch goal with |- getr (ms_regs ?m) ?r = ?rhs =>
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ m) =>
      let R := fresh "R" in
      pose proof (st_ok_pi_restrict_reg _ Ex ssx m r HS) as R;
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in change (sr_get (ss_regs ssx) r) with e in R;
      cbn [ms_regs restrict] in R; rewrite R; clear R;
      first [ rewrite ge_sv_SOff0; cbn [ew ewset Nat.eqb]; first [apply EE; reflexivity | assumption]
            | cbn [sv_denot]; lazymatch rhs with getr (ms_regs ?m0) r =>
                match goal with H : getr (ms_regs m0) r = w64 _ |- _ => rewrite H; reflexivity end end ]
    end
  end.

(* 0x81c48 .. 0x81d5c: the scene check and the unset_sent count. *)
Lemma segE : seg_E_ok B MT POST.
Proof.
  intros m HTF cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfr HMLE
    (i & t & T & us & c & p & v & T' & HT & Hm & Hsch & Hnx & Htab & Hlus & Hus & Cc & Cp & Cv).
  destruct (gctx cx fp k ly3 S3 W3 (ms_mem ms3) md3 HB HJ Hfr)
    as (EFA & HF4096 & HFceil & HFapp & HF64 & HSH & Hceil & H47 & Hal16 & Hsp1 & Hsp32).
  destruct (gpres cx fp k ly3 S3 W3 (ms_mem ms3) md3 HB HJ Hfr) as (HFP & HSP).
  pose proof HT as (HTB0 & Hi & R21).
  pose proof HTB0 as (HBD & Hk & Hacc & Hbl & Hn & R18 & R19 & R22 & R23 & R24 & R25 & R26 & R27 &
    HSC & HSL & HWS & HST & HH).
  pose proof (ginput_ok cx fp k ly3 S3 W3 (ms_mem ms3) md3 t HB HJ Hfr Hbl) as HIN.
  pose proof (table_out cx fp k ly3 S3 W3 (ms_mem ms3) md3 t HB HJ Hfr Hbl) as HTO.
  pose proof HBD as (Hpc & Hrv & Hsvc & Hrom & Hfrg & Hfc & HG & HSV & HSHW & HFL & Hlen & HINP).
  pose proof HG as (G2 & G8 & G9 & G3 & G4).
  pose proof HSL as (L8 & L40 & L64 & L72 & L80 & L88 & L96 & L112 & L128 & L136 & L144 & L152).
  pose proof Htab as (Htin & Ht0 & HTl & HTb).
  destruct (HTO 0 ltac:(lia)) as (_ & Ht64). rewrite Z.add_0_r in Ht64.
  pose proof (proj1 (proj2 (SegSetModel.tables_end_inv (c_pl cx)))) as Lws.
  pose proof (HeadampSched.frame_ok (c_pl cx) t i Ht0) as FO.
  pose proof (HeadampSched.sched_rd_range (c_pl cx)) as SRR.
  pose proof (Seg_sched_turn.sched_flag_spec (c_pl cx)) as SFS.
  destruct (GrantSlotPlan.sched_rd (c_pl cx)) as [[[[sb sw] per] fr] pe] eqn:Hsrd.
  destruct SRR as (Rsb & Rsw).
  destruct (SFS sb sw per fr pe eq_refl) as (SF1 & SF01). clear SFS.
  destruct HSC as (S120 & S104).
  rewrite Hsch, Hnx in FO.
  destruct FO as (FL1 & FL2 & FL3 & FLT' & FI1 & FSch & _ & FR1).
  destruct (FR1 eq_refl) as (Hc48 & Hp3 & _ & _ & _ & FWZ). clear FR1.
  pose proof asan_consts as (C1 & _).
  assert (GS : GE_STK = 32768) by reflexivity.
  assert (HSHr : 2147450880 <= gSH cx fp /\ gSH cx fp + 128 <= 2147450880 + 2 ^ 44).
  { rewrite HSH. dm (gF cx fp) 8. unfold SHADOW_OFF. lia. }
  assert (Hsep : gSH cx fp + 128 <= gF cx fp \/ gF cx fp + 1024 <= gSH cx fp).
  { rewrite HSH. dm (gF cx fp) 8. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *.
    destruct HFapp as (_ & [Hlo | (Hhi & _)]); [right | left]; lia. }
  pose proof (tbrE (GrantSlotPlan.ws_end (c_pl cx)) (3 * c + p)) as Raw.
  pose proof (tbrE us (3 * c + p)) as Rau.
  (* the frame bytes the segment reads *)
  destruct (val1E _ _ _ _ Cc) as (VCc & Rc).
  destruct (val1E _ _ _ _ Cp) as (VCp & Rp).
  destruct (HWS (Z.to_nat (3 * c + p)) ltac:(rewrite length_map, Lws; lia)) as (VW & _).
  rewrite nth_map_tbE, Z2Nat.id in VW by lia.
  destruct (Hus (Z.to_nat (3 * c + p)) ltac:(rewrite length_map, Hlus; lia)) as (VU & _).
  rewrite nth_map_tbE, Z2Nat.id in VU by lia.
  (* the environment *)
  remember (Eimg (Ereg (ms_regs ms3)
    [w64 c; w64 p; w64 (gF cx fp + 32 + (3 * c + p));
     w64 (HeadampModel.tb (GrantSlotPlan.ws_end (c_pl cx)) (3 * c + p));
     w64 (HeadampModel.tb us (3 * c + p)); w64 sb; w64 (sb + sw); w64 t;
     w64 (2 ^ 64 - 1 - (gF cx fp + GO_WAS)); w64 (2 ^ 64 - 1 - (gF cx fp + GO_UNSET));
     w64 (2 ^ 64 - 1 - (gF cx fp + 32 + 3 * c)); w64 (2 ^ 64 - 1 - (gF cx fp + 576 + 3 * c))])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EE : forall (n : nat) (r0 : bv 5), Z.of_nat n = bv_unsigned r0 -> ew E n = getr (ms_regs ms3) r0)
    by (intros n0 r0 Hr; subst E; apply ew_Eimg_Ereg_nat; exact Hr).
  assert (E32 : ew E 32 = w64 c)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
  assert (E33 : ew E 33 = w64 p)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
  assert (E34 : ew E 34 = w64 (gF cx fp + 32 + (3 * c + p)))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 2)).
  assert (E35 : ew E 35 = w64 (HeadampModel.tb (GrantSlotPlan.ws_end (c_pl cx)) (3 * c + p)))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 3)).
  assert (E36 : ew E 36 = w64 (HeadampModel.tb us (3 * c + p)))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 4)).
  assert (E37 : ew E 37 = w64 sb)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 5)).
  assert (E38 : ew E 38 = w64 (sb + sw))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 6)).
  assert (E39 : ew E 39 = w64 t)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 7)).
  assert (E40 : ew E 40 = w64 (2 ^ 64 - 1 - (gF cx fp + GO_WAS)))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 8)).
  assert (E41 : ew E 41 = w64 (2 ^ 64 - 1 - (gF cx fp + GO_UNSET)))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 9)).
  assert (E42 : ew E 42 = w64 (2 ^ 64 - 1 - (gF cx fp + 32 + 3 * c)))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 10)).
  assert (E43 : ew E 43 = w64 (2 ^ 64 - 1 - (gF cx fp + 576 + 3 * c)))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 11)).
  assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite (EE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
  assert (U22 : bv_unsigned (ew E 22) = gF cx fp + 784)
    by (rewrite (EE 22%nat 22%bv eq_refl), R22; unfold GO_CH; apply unsigned_lit_small; lia).
  assert (U23 : bv_unsigned (ew E 23) = GrantSlotPlan.sched_flag (c_pl cx))
    by (rewrite (EE 23%nat 23%bv eq_refl), R23; apply unsigned_lit_small; lia).
  assert (U32 : bv_unsigned (ew E 32) = c) by (rewrite E32; apply unsigned_lit_small; lia).
  assert (U33 : bv_unsigned (ew E 33) = p) by (rewrite E33; apply unsigned_lit_small; lia).
  assert (U34 : bv_unsigned (ew E 34) = gF cx fp + 32 + (3 * c + p)) by (rewrite E34; apply unsigned_lit_small; lia).
  assert (U35 : bv_unsigned (ew E 35) = HeadampModel.tb (GrantSlotPlan.ws_end (c_pl cx)) (3 * c + p))
    by (rewrite E35; apply unsigned_lit_small; lia).
  assert (U36 : bv_unsigned (ew E 36) = HeadampModel.tb us (3 * c + p)) by (rewrite E36; apply unsigned_lit_small; lia).
  assert (U37 : bv_unsigned (ew E 37) = sb) by (rewrite E37; apply unsigned_lit_small; lia).
  assert (U38 : bv_unsigned (ew E 38) = sb + sw) by (rewrite E38; apply unsigned_lit_small; lia).
  assert (U40 : bv_unsigned (ew E 40) = 2 ^ 64 - 1 - (gF cx fp + 32))
    by (rewrite E40; unfold GO_WAS; apply unsigned_lit_small; lia).
  assert (U41 : bv_unsigned (ew E 41) = 2 ^ 64 - 1 - (gF cx fp + 576))
    by (rewrite E41; unfold GO_UNSET; apply unsigned_lit_small; lia).
  assert (U42 : bv_unsigned (ew E 42) = 2 ^ 64 - 1 - (gF cx fp + 32 + 3 * c))
    by (rewrite E42; apply unsigned_lit_small; lia).
  assert (U43 : bv_unsigned (ew E 43) = 2 ^ 64 - 1 - (gF cx fp + 576 + 3 * c))
    by (rewrite E43; apply unsigned_lit_small; lia).
  assert (HS0 : st_ok_pi SEGS VAL E (mkSS GP_scn sr_atoms rs_E None G_E) (restrict (w_H W3) ms3)).
  { rewrite (gms_eq (w_H W3) GP_scn ms3 Hpc Hrv Hsvc Hrom Hfrg Hfc). apply pa_entry_st_ok_full.
    - rewrite HE. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - unfold rs_E. apply Forall_cons.
      { unfold region_ok, stkE.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons.
        { apply (chunk_ok_val SEGS E _ (c_sp1 cx) 40 8 (SOff 22 (-208)) (gF cx fp + GO_UNSET));
            [cbn [sv_denot]; rewrite U22; unfold GO_UNSET; f_equal; lia | cbn; unfold GO_UNSET; lia | cbn; lia
            | apply val_mem_of_rdword; exact L40]. }
        apply Forall_cons.
        { apply (chunk_ok_val SEGS E _ (c_sp1 cx) 64 8 (SOff 22 0) (gF cx fp + GO_CH));
            [cbn [sv_denot]; rewrite U22; unfold GO_CH; f_equal; lia | cbn; unfold GO_CH; lia | cbn; lia
            | apply val_mem_of_rdword; exact L64]. }
        apply Forall_cons.
        { apply (chunk_ok_val SEGS E _ (c_sp1 cx) 80 8 (SOff 41 0) (2 ^ 64 - 1 - (gF cx fp + GO_UNSET)));
            [rewrite ge_sv_SOff0, E41; reflexivity | cbn; unfold GO_UNSET; lia | cbn; lia
            | apply val_mem_of_rdword; exact L80]. }
        apply Forall_cons.
        { apply (chunk_ok_val SEGS E _ (c_sp1 cx) 88 8 (SOff 40 0) (2 ^ 64 - 1 - (gF cx fp + GO_WAS)));
            [rewrite ge_sv_SOff0, E40; reflexivity | cbn; unfold GO_WAS; lia | cbn; lia
            | apply val_mem_of_rdword; exact L88]. }
        apply Forall_cons.
        { apply (chunk_ok_val SEGS E _ (c_sp1 cx) 104 8 (SOff 38 0) (sb + sw));
            [rewrite ge_sv_SOff0, E38; reflexivity | cbn; lia | cbn; lia | apply val_mem_of_rdword; exact S104]. }
        apply Forall_cons.
        { apply (chunk_ok_val SEGS E _ (c_sp1 cx) 112 8 (SOff 22 16) (gF cx fp + GO_PAR));
            [cbn [sv_denot]; rewrite U22; unfold GO_PAR; f_equal; lia | cbn; unfold GO_PAR; lia | cbn; lia
            | apply val_mem_of_rdword; exact L112]. }
        apply Forall_cons.
        { apply (chunk_ok_val SEGS E _ (c_sp1 cx) 120 8 (SOff 37 0) sb);
            [rewrite ge_sv_SOff0, E37; reflexivity | cbn; lia | cbn; lia | apply val_mem_of_rdword; exact S120]. }
        apply Forall_cons.
        { apply (chunk_ok_val SEGS E _ (c_sp1 cx) 136 8 (SOff 22 (-752)) (gF cx fp + GO_WAS));
            [cbn [sv_denot]; rewrite U22; unfold GO_WAS; f_equal; lia | cbn; unfold GO_WAS; lia | cbn; lia
            | apply val_mem_of_rdword; exact L136]. }
        apply Forall_cons.
        { apply (chunk_ok_val SEGS E _ (c_sp1 cx) 144 8 (SLit SHADOW_OFF) SHADOW_OFF);
            [reflexivity | cbn; unfold SHADOW_OFF; lia | cbn; lia | apply val_mem_of_rdword; exact L144]. }
        apply Forall_cons.
        { apply (chunk_ok_val SEGS E _ (c_sp1 cx) 152 8 (SOff 39 0) t);
            [rewrite ge_sv_SOff0, E39; reflexivity | cbn; lia | cbn; lia | apply val_mem_of_rdword; exact L152]. }
        apply Forall_nil. }
      apply Forall_cons; [eapply cellE_ok; [exact U22 | exact E32 | lia | lia | lia |
        replace (gF cx fp + 784 + 0) with (gF cx fp + GO_CH) by (unfold GO_CH; lia); exact VCc]|].
      apply Forall_cons; [eapply cellE_ok; [exact U22 | exact E33 | lia | lia | lia |
        replace (gF cx fp + 784 + 16) with (gF cx fp + GO_PAR) by (unfold GO_PAR; lia); exact VCp]|].
      apply Forall_cons; [eapply cellE_ok; [exact U34 | exact E35 | lia | lia | lia |
        replace (gF cx fp + 32 + (3 * c + p) + 0) with (gF cx fp + GO_WAS + (3 * c + p)) by (unfold GO_WAS; lia); exact VW]|].
      apply Forall_cons; [eapply unsetE_ok; [exact U34 | exact E36 | lia | lia | lia | |
        replace (gF cx fp + 32 + (3 * c + p) + 544) with (gF cx fp + GO_UNSET + (3 * c + p)) by (unfold GO_UNSET; lia); exact VU]|].
      { replace (gF cx fp + 32 + (3 * c + p) + 544) with (gF cx fp + (576 + (3 * c + p))) by lia.
        apply (apresent_writable SEGS). apply HFP. lia. }
      apply Forall_nil.
    - apply pairwise_disjoint_of_extents. unfold extent_of_region, rs_E, stkE, cellE, unsetE.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U22, U34.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
    - split; [|split; [exact I|]].
      + cbn [G_E f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite U32, U33, U34, U35, U36, U37, U38, U40, U41, U42, U43. rewrite !Z.pow_0_r, !Z.mod_1_r.
        repeat split; lia.
      + cbn [G_E f_alias alias_ok]. split; [|split; [|split; [|exact I]]].
        * (* was_set + 3 ch + param is atom 34 *)
          apply U_inj. rewrite (lin_of_sound E XEa _ _ lin_XEa), (U_atom E 34 _ E34) by lia.
          cbn [lin_denot]. rewrite U22, U32, U33. unfold M64. rewrite Z.mod_small by lia. lia.
        * (* not (was_set + 3 ch) is atom 42 *)
          apply U_inj. rewrite U_not_gen, (lin_of_sound E WWE _ _ lin_WWE), (U_atom E 42 _ E42) by lia.
          cbn [lin_denot]. rewrite U22, U32. unfold M64. rewrite Z.mod_small by lia. lia.
        * (* not (unset_sent + 3 ch) is atom 43 *)
          apply U_inj. rewrite U_not_gen, (lin_of_sound E WUE _ _ lin_WUE), (U_atom E 43 _ E43) by lia.
          cbn [lin_denot]. rewrite U22, U32. unfold M64. rewrite Z.mod_small by lia. lia. }
  clear HE.
  pose proof (ast_ok_pi_set_reg_fp E _ _ 18%bv (SLit 47) HS0 eq_refl
    ltac:(cbn [sv_denot ms_regs restrict]; rewrite R18; reflexivity)) as HS1.
  pose proof (ast_ok_pi_set_reg_fp E _ _ 27%bv (SLit 2) HS1 eq_refl
    ltac:(cbn [sv_denot ms_regs restrict]; rewrite R27; reflexivity)) as HS.
  clear HS0 HS1.
  assert (SHOK : sh_ok SEGS BxL SH_E E (mrestrict (w_H W3) (ms_mem ms3))).
  { unfold sh_ok, SH_E. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    - apply (shentE cx fp W3 ms3 E 34 0 32 (3 * c + p) HSHW HF64 HFapp).
      + rewrite (U_atom E 34 _ E34) by lia. lia.
      + lia.
      + left. dm (32 + (3 * c + p)) 8. lia.
    - change (544 + 1) with 545.
      apply (shentE cx fp W3 ms3 E 34 544 576 (3 * c + p) HSHW HF64 HFapp).
      + rewrite (U_atom E 34 _ E34) by lia. lia.
      + lia.
      + right. dm (576 + (3 * c + p)) 8. lia. }
  (* the end of the turn, from what the walk leaves at 0x81d5c *)
  assert (FIN : forall msF mdF us' nv,
    ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(GE_CID, fp)] ly3 S3 W3 (ms_mem msF) mdF k ->
    (forall a, 0 <= a < 2 ^ 64 -> a <> gF cx fp + 576 + (3 * c + p) ->
       aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
    aview SEGS (w_H W3) (ms_mem msF) (gF cx fp + 576 + (3 * c + p)) = Some nv ->
    GrantSlotPlan.sched_at (c_pl cx) t (S i) = (T', us') -> length us' = 144%nat ->
    (forall j, 0 <= j < 144 -> HeadampModel.tb us' j = if j =? 3 * c + p then nv else HeadampModel.tb us j) ->
    ms_pc_val msF = w64 (BASE + GP_end) -> ms_resv msF = None -> ms_svc_pending msF = None ->
    ms_rom msF = seg_rom SEGS -> ms_fregs msF = fp_regs -> ms_fcsr msF = fp_csr ->
    gtregs (ms_regs ms3) (ms_regs msF) -> getr (ms_regs msF) 21 = getr (ms_regs ms3) 21 ->
    getr (ms_regs msF) 20 = w64 t ->
    SRr SEGS W3 (mkCfg msF mdF) (POST cx)).
  { intros msF mdF us' nv HJF FK FV FS FL FU Fpc Frv Fsvc From Ffr Ffc FR F21 F20.
    apply (HTF cx fp k acc ly3 S3 W3 msF mdF HB HJF Hfr HMLE).
    exists i, t, T', us'.
    split.
    { eapply tcom_keep; [exact HF4096 | exact HFceil | exact HFapp | lia | lia | exact HIN | exact HT
        | exact Fpc | exact Frv | exact Fsvc | exact From | exact Ffr | exact Ffc | exact FR | exact Hi
        | rewrite F21; exact R21
        | intros a Ha Hw; apply FK; [eapply gtracked_rng; eauto; lia
                                    | intros Hq; apply Hw; unfold gwr, GO_UNSET, GO_CH, GO_PAR, GO_VAL; lia]
        | | exact GSH_turn_len ].
      intros j Hj. rewrite GSH_turn_len in Hj. unfold GE_NSH in Hj.
      rewrite FK; [apply HSHW; rewrite GSH_turn_len; unfold GE_NSH; exact Hj | lia | lia]. }
    split; [exact Hm|]. split; [exact F20|]. split; [exact FS|].
    split.
    { eapply gtab_keep; [exact Htab|]. intros j Hj. destruct (HTO j Hj) as (Hw & Hr). apply FK; [exact Hr|].
      intros Hq; apply Hw; unfold gwr, GO_UNSET, GO_CH, GO_PAR, GO_VAL; lia. }
    split; [exact FI1|]. split; [exact FL|].
    unfold gfarr. intros j Hj. rewrite length_map in Hj.
    rewrite nth_map_tbE. split; [|exact (tbrE us' (Z.of_nat j))].
    rewrite (FU (Z.of_nat j)) by lia.
    destruct (Z.eqb_spec (Z.of_nat j) (3 * c + p)) as [Ej | Nj].
    - replace (gF cx fp + GO_UNSET + Z.of_nat j) with (gF cx fp + 576 + (3 * c + p)) by (unfold GO_UNSET; lia).
      exact (proj1 (val1E _ _ _ _ FV)).
    - destruct (Hus j ltac:(rewrite length_map; lia)) as (Hv & _). rewrite nth_map_tbE in Hv.
      intros kk Hkk. assert (kk = 0%nat) by lia. subst kk.
      rewrite (mbyte_of_aview SEGS (w_H W3) (w_H W3) (ms_mem ms3) (ms_mem msF)); [apply Hv; lia|].
      apply FK; unfold GO_UNSET; lia. }
  (* the run: 0x81c48 .. 0x81ca4, the first read of was_set[ch][param] *)
  paj_run_tok RUN HS HJ SHOK SpanE.
  { awr_fr fp EFA HSH. }
  psrr_branch_tok RUN BR HS SHOK SpanE.
  - (* 0x81ca4 taken: the input set the cell; the second read at 0x81d04 finds it set again
       (0x81d10 taken), no scene check and no count *)
    hczE Hc. rename Hc into Hwnz.
    paj_run_to_tok RUNTO HS HJ SHOK SpanE GP_end.
    { awr_fr fp EFA HSH. }
    lazymatch goal with HSx : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msF) |- SRr _ _ (mkCfg ?msF ?mdF) _ =>
      destruct (stf _ _ _ _ HSx eq_refl) as (Fpc & Frv & Fsvc & From & Ffr & Ffc);
      assert (U34F : bv_unsigned (ew Ex 34) = gF cx fp + 32 + (3 * c + p)) by (cbn [ew ewset Nat.eqb]; exact U34);
      pose proof (st_ok_pi_region_nth _ _ _ 4 _ HSx eq_refl) as RG;
      cbn [ms_mem restrict] in RG;
      pose proof (chunk1_aview _ _ _ _ _ _ _ _ _ _ _ _ RG (or_introl eq_refl) U34F) as V;
      rewrite ge_sv_SOff0 in V; cbn [ew ewset Nat.eqb] in V; rewrite U36, Z.mod_small in V by lia;
      apply (FIN msF mdF us (HeadampModel.tb us (3 * c + p)) HJ);
      [ keptE U34 (gF cx fp + 576 + (3 * c + p))
      | replace (gF cx fp + 576 + (3 * c + p)) with (gF cx fp + 32 + (3 * c + p) + 544) by lia; exact V
      | rewrite FSch, (Seg_sched_turn.us_step_ws _ _ _ _ _ Hwnz); reflexivity
      | exact Hlus
      | intros j Hj; destruct (Z.eqb_spec j (3 * c + p)) as [-> | _]; reflexivity
      | exact Fpc | exact Frv | exact Fsvc | exact From | exact Ffr | exact Ffc
      | repeat split; gregE HSx EE
      | gregE HSx EE
      | gregE HSx EE ]
    end.
  - (* 0x81ca4 not taken: a cell the input left unset; the scene check and the count *)
    hczE Hc. rename Hc into Hwz.
    destruct (FWZ Hwz) as (_ & Hsw0 & Hsb48 & Hcsb & Hu0).
    pose proof (SF1 Hsw0 Hsb48) as Hfl.
    paj_run_tok RUN HS HJ SHOK SpanE.
    { awr_fr fp EFA HSH. }
    psrr_branch_tok RUN BR HS SHOK SpanE.
    + (* 0x81ca8 to the abort: the scheduler's flag is 0 *)
      exfalso. hczE Hc. lia.
    + hczE Hc. rename Hc into Hfl0.
      paj_run_tok RUN HS HJ SHOK SpanE.
      { awr_fr fp EFA HSH. }
      psrr_branch_tok RUN BR HS SHOK SpanE.
      * (* 0x81cb0 to the abort: ch < sb *)
        exfalso. hczE Hc. lia.
      * hczE Hc. rename Hc into Hsbc.
        paj_run_tok RUN HS HJ SHOK SpanE.
        { awr_fr fp EFA HSH. }
        psrr_branch_tok RUN BR HS SHOK SpanE.
        -- (* 0x81cb8 to the abort: ch >= sb + sw *)
           exfalso. hczE Hc. lia.
        -- hczE Hc. rename Hc into Hswc.
           (* 0x81cb8 .. 0x81d58: the second read of was_set, the count *)
           paj_run_tok RUN HS HJ SHOK SpanE.
           { awr_fr fp EFA HSH. }
           psrr_branch_tok RUN BR HS SHOK SpanE.
           ++ (* 0x81d58 to the abort: unset_sent[ch][param] was not 0 *)
              exfalso. hczE Hc. lia.
           ++ hczE Hc. rename Hc into Hu0c.
              paj_run_to_tok RUNTO HS HJ SHOK SpanE GP_end.
              { awr_fr fp EFA HSH. }
              lazymatch goal with HSx : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msF) |- SRr _ _ (mkCfg ?msF ?mdF) _ =>
                destruct (stf _ _ _ _ HSx eq_refl) as (Fpc & Frv & Fsvc & From & Ffr & Ffc);
                assert (U34F : bv_unsigned (ew Ex 34) = gF cx fp + 32 + (3 * c + p)) by (cbn [ew ewset Nat.eqb]; exact U34);
                pose proof (st_ok_pi_region_nth _ _ _ 4 _ HSx eq_refl) as RG;
                cbn [ms_mem restrict] in RG;
                pose proof (chunk1_aview _ _ _ _ _ _ _ _ _ _ _ _ RG (or_introl eq_refl) U34F) as V;
                cbn [sv_denot ew ewset Nat.eqb] in V; rewrite U36, Hu0 in V;
                apply (FIN msF mdF (GrantSlotPlan.ws_put us c p 1) 1 HJ);
                [ keptE U34 (gF cx fp + 576 + (3 * c + p))
                | replace (gF cx fp + 576 + (3 * c + p)) with (gF cx fp + 32 + (3 * c + p) + 544) by lia;
                  rewrite V; reflexivity
                | rewrite FSch, (Seg_sched_turn.us_step_put _ _ _ _ _ Hc48 Hp3 Hwz Hu0); reflexivity
                | apply SegSetModel.len_ws_put; [exact Hlus | lia | lia]
                | intros j Hj; apply SegSetModel.tb_ws_put; [exact Hlus | lia | lia | lia | lia]
                | exact Fpc | exact Frv | exact Fsvc | exact From | exact Ffr | exact Ffc
                | repeat split; gregE HSx EE
                | gregE HSx EE
                | gregE HSx EE ]
              end.
Qed.

End c.
End b.
End a.
