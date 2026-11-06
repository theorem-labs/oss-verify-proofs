(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: image-B walk segment; lines 228-235 follow the shape of cgif_file_fuzzer lib/A/AC8a.v:29 (licscan run). *)
(* Segment 2 of the sweep phase of fuzz_grant's entry function on IMAGE B:
   0x81450 .. 0x815d0 (listing 0xa14 .. 0xb94), the inlined check_row loop
   (fuzz_grant.c:313-314, check_row at :94-113), by induction on the rows left.

   Adapted from lib/A/Prog/GrantEntrySweepS2.v (a working branch afd75724b5b, blob
   38868c298, 425 lines), which carries no licence header of its own.
   Image B hoists twelve constants where image A
   hoists seven, holds the buffer in s11 and the row in s8, reads the shadow offset
   back from spill slot 144 at every shadow check, keeps the one's complement of the
   buffer in slot 88, counts the rows with addiw, sends a failed row check to the abort
   block 0x81d98 instead of image A's error path, and adds five UBSan pointer-overflow
   guards into the trap 0x81f48, which the engine refutes from the row's address range.

   One turn of the loop, row j of the sweep at s + 34 * j, is walked on the
   position-abstract listing from 0x81450. Every instruction of the range:
   - 0x81450 `mul a1,a3,a6` (34 j); 0x81454 `ld a2,88(s1)` (slot 88, -1 - s);
     0x81458 `bltu a2,a1,trap`: GUARD 1, false because 34 j <= 8670 < 2^64 - 1 - s;
   - 0x8145c `mv s9,zero` (the sum); 0x81460 `sub a2,a5,s8` (-2 - row);
     0x81464 `add a1,s11,a1` (the row, atom 32 by the alias s11 + a3 * 34);
     0x81468..0x81474 `addi s2,a2,1; seqz s2,s2; addi s2,s2,-1; and s2,s2,a2` (s2 = -2 - row
     because -1 - row is not 0); 0x81478 `li s4,32`; 0x8147c `mv s6,a4`; 0x81480 `mv a2,s5`;
   - the sum of bytes 2..33, 0x81484..0x814b4, 32 turns that the engine unrolls:
     0x81484 `add s7,s2,s4`; 0x81488 `beq s7,a7,trap`: GUARD 2, false because
     -2 - row + s4 = 32 needs row = 2^64 - 34 + s4; 0x8148c..0x8149c the shadow check of
     a2 (`srli`, `ld s10,144(s1)`, `add`, `lb`, `bnez` to the slow block 0x814bc..0x814c4,
     `andi s10,a2,7; blt s10,s7` back to 0x814a0, else `j` to the report);
     0x814a0 `lbu s7,0(s6)`; 0x814a4 `addi s4,s4,-1`; 0x814a8 `addi a2,a2,1`;
     0x814ac `add s9,s9,s7`; 0x814b0 `addi s6,s6,1`; 0x814b4 `bnez s4` back; 0x814b8 `j 0x814c8`;
   - row[0], 0x814c8..0x814e0: the shadow check of a1 (slow block 0x81570..0x81578),
     `lbu a2,0(a1)`, `bne a2,t0,abort` (0xcd); 0x814e4 `beq a1,t1,trap`: GUARD 3 (row = -1);
   - row[1], 0x814e8..0x81504: `addi a2,a1,1`, the shadow check (slow block
     0x8157c..0x81584), `lbu`, `bne a2,t2,abort` (0xea); 0x81508 `bltu t3,a1,trap`: GUARD 4
     (row > -3);
   - row[2], 0x8150c..0x81528: `addi a2,a1,2`, the shadow check (slow block
     0x81588..0x81590), `lbu`, `bne a2,t4,abort` (4); 0x8152c `bltu t5,a1,trap`: GUARD 5
     (row > -4);
   - row[3], 0x81530..0x8154c: `addi a1,a1,3`, the shadow check (slow block
     0x81594..0x81598, whose fall-through 0x8159c `mv a0,a1; jal __asan_report_load1` is the
     report the shadow engine refutes), `lbu a1,0(a1)`, `bne a1,t6,abort` (3);
   - 0x81550 `andi a1,s9,0xff`; 0x81554 `bnez a1,abort`: the low byte of the sum;
   - 0x81558 `addiw a3,a3,1`; 0x8155c..0x81564 `addi s8/s5/a4,...,34`;
     0x81568 `bne a3,a0` back to 0x81450; 0x8156c `j 0x815d0`, the cut GIS_rowex.
   The code 0x815a4 .. 0x815cc is a tail the compiler merged with another phase's
   (it ends `j 0x80db0`, and its `bgeu` 0x815a8 into the trap is that tail's); no path of
   this range reaches it.

   The row's 34 bytes are data slot 0 of the environment and its address is atom 32;
   atom 33 is slot 88's -1 - s, atom 34 is -1 - row (the alias -1 - atom 32, through
   which the engine reads 0x81460's -2 - row as atom 34 - 1), atom 35 is slot 144's
   SHADOW_OFF, the shadow base. The shadow bytes of the row are read through the shadow
   entry (atom 32, 0, 34), which the sweep block's own shadow gives. The five guards are
   decided by the engine from the ranges of atoms 13, 32, 33 and 34. The branches to the
   abort block are not taken because every row of the sweep is a `rowok` row of
   fuzz_grant's own model (SweepRowCheck.sweep_rows_ok, rowok_split). The loop writes no
   memory, so every memory fact of the cut is kept. *)
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
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YC5d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaShadow PaRun PaStep.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantPa GrantPaLib GrantRo GrantBContracts
LLVMFEntryDefs LLVMFEntrySweepDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC1g YC1h YC45 YC85 GrantFrame GrantACja.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import LLVMFEntrySeat.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import
HeadampModel GrantModel GrantSweepModel BuildSweepModel SweepRowCheck GrantSlotPlan.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require SlotNeeds_c.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* Image A's text was written with this flag false; `Local` keeps the setting here. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import LLVMFEntrySweepS1c.

(* ---- the symbolic state at 0x81450 ---- *)
(* Image B reads the shadow offset back from spill slot 144 at every shadow check
   (`ld s10,144(s1)` and its three twins): atom 35, slot 144's value, is the shadow base.
   Image A kept it in s7. *)
Definition rw_Bx : sv := SOff 35 0.
Definition rw_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* The 34 bytes of the row are addressable. *)
Definition rw_SH : list shent := [mkSHE 32 0 34].
(* a1 = s11 + a3 * 34 (0x81450, 0x81464) is the row's address, atom 32. *)
Definition rw_alias : sv := SAlu ALU_ADD (SOff 27 0) (SMd M_MUL (SOff 13 0) (SLit 34)).
(* -1 - row is atom 34; the engine reads every value -1 * row + c through it. *)
Definition rw_alias_not : sv := SAlu ALU_SUB (SLit (-1)) (SOff 32 0).
(* The row, read-only: its bytes are data slot 0. *)
Definition rw_region : YP09.region := YP09.mkRegion (Some 32%nat) 0 34 0 0 [YP09.mkChunk 0 (CData 0 0 34)].
(* The two spill slots the loop reads, read-only: 88 (-1 - s, atom 33) and 144 (atom 35). *)
Definition rw_slots : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 192 0 0
    [YP09.mkChunk 88 (CVal 8 (SOff 33 0)); YP09.mkChunk 144 (CVal 8 (SOff 35 0))].
Definition rw_facts : facts :=
  mkFacts [(13%nat, mkAF 0 255 0); (32%nat, mkAF 4096 0x7fffff800000 0);
           (33%nat, mkAF (2 ^ 64 - 1 - 0x7fffff800000) (2 ^ 64 - 1 - 4096) 0);
           (34%nat, mkAF (2 ^ 64 - 1 - 0x7fffff800000) (2 ^ 64 - 1 - 4096) 0);
           (35%nat, mkAF SHADOW_OFF SHADOW_OFF 0)]
          [] [(rw_alias, SOff 32 0); (rw_alias_not, SOff 34 0)].
(* a4 and s5 hold row + 2, s8 the row; the twelve hoisted constants are literals; every
   other register is its own atom. *)
Definition rw_sr : list sv :=
  fold_left (fun sr p => sr_set sr (Z_to_bv 5 (fst p)) (snd p))
    [(5, SLit 205); (6, SLit (-1)); (7, SLit 234); (14, SOff 32 2); (15, SLit (-2)); (16, SLit 34);
     (17, SLit 32); (21, SOff 32 2); (24, SOff 32 0); (28, SLit (-3)); (29, SLit 4); (30, SLit (-4));
     (31, SLit 3)] sr_atoms.
Definition ss_rw : sstate := mkSS GPS_rowhd rw_sr [rw_region; rw_slots] None rw_facts.

(* The sum the loop at 0x81484..0x814b4 leaves in s9, and its value. *)
Fixpoint rw_sum (n : nat) : sv :=
  match n with O => SLit 0 | S n' => SAlu ALU_ADD (rw_sum n') (SData 0 (2 + Z.of_nat n') 1) end.
Fixpoint rw_zsum (RB : list byte) (n : nat) : Z :=
  match n with O => 0 | S n' => rw_zsum RB n' + bv_unsigned (nth (2 + n') RB (Z_to_bv 8 0)) end.

(* ---- list and value facts ---- *)
Lemma rw_zsum_range : forall RB n, 0 <= rw_zsum RB n <= 255 * Z.of_nat n.
Proof.
intros RB n. induction n as [|n IH]; cbn [rw_zsum]; [lia|].
pose proof (u8_range (nth (2 + n) RB (Z_to_bv 8 0))). lia.
Qed.

Lemma U_rw_sum : forall E n, (forall k, (k < n)%nat -> (2 + k < length (ed E 0))%nat) -> (n <= 32)%nat ->
  U E (rw_sum n) = rw_zsum (ed E 0) n.
Proof.
intros E n. induction n as [|n IH]; intros Hl Hn.
- cbn [rw_sum rw_zsum]. rewrite U_SLit. reflexivity.
- cbn [rw_sum rw_zsum]. rewrite U_SAlu. cbn [zalu_raw].
  rewrite IH by first [lia | intros kk Hkk; apply Hl; lia].
  rewrite (gs_U_data1 E (2 + Z.of_nat n) (nth (2 + n) (ed E 0) (Z_to_bv 8 0))).
  + pose proof (rw_zsum_range (ed E 0) n). pose proof (u8_range (nth (2 + n) (ed E 0) (Z_to_bv 8 0))).
    apply zcanon_id. unfold M64. lia.
  + lia.
  + replace (Z.to_nat (2 + Z.of_nat n)) with (2 + n)%nat by lia. apply nth_error_nth'. apply Hl. lia.
Qed.

Lemma rw_zsum_row : forall rest, length rest = 30%nat ->
  rw_zsum (Z_to_bv 8 205 :: Z_to_bv 8 234 :: Z_to_bv 8 4 :: Z_to_bv 8 3 :: rest) 32 =
  SweepRowCheck.bsum (Z_to_bv 8 4 :: Z_to_bv 8 3 :: rest).
Proof.
intros rest H.
do 30 (destruct rest as [|? rest]; [discriminate H | cbn [length] in H; injection H as H]).
destruct rest; [|discriminate H].
unfold SweepRowCheck.bsum. cbn [rw_zsum nth Nat.add map fold_right]. lia.
Qed.

Lemma land255 : forall x, Z.land x 255 = x mod 256.
Proof. intros x. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma nth_error_concat34 : forall (L : list (list byte)) j i,
  Forall (fun r => length r = 34%nat) L -> (j < length L)%nat -> (i < 34)%nat ->
  nth_error (concat L) (34 * j + i) = nth_error (nth j L []) i.
Proof.
induction L as [|r L IH]; intros j i HL Hj Hi; cbn [length] in Hj; [lia|].
inversion HL as [|r0 L0 Hr HL']; subst r0 L0.
cbn [concat]. destruct j as [|j].
- cbn [nth]. replace (34 * 0 + i)%nat with i by lia. apply nth_error_app1. lia.
- cbn [nth]. rewrite nth_error_app2 by lia. rewrite Hr.
  replace (34 * S j + i - 34)%nat with (34 * j + i)%nat by lia. apply IH; [exact HL' | lia | exact Hi].
Qed.

Lemma length_sweep_rows_ge : forall base w vals, 8 + 3 * Z.of_nat w <= Z.of_nat (length (sweep_rows base w vals)).
Proof.
intros base w vals. unfold sweep_rows. cbn [length]. rewrite length_app. cbn [length].
rewrite length_flat_rows, length_seq. unfold ga_rows. cbn [length]. lia.
Qed.

(* ---- the tactics of the walk ---- *)
(* After a run of the engine: the regions are read-only, so the memory is the one the
   walk started from. *)
Ltac rw_mem mem0 :=
  lazymatch goal with HF : frame_of _ ?rs ?m (ms_mem ?msn) |- _ =>
    let H := fresh "HM" in
    pose proof (frame_of_read_only _ rs m (ms_mem msn) ltac:(vm_compute; reflexivity) HF) as H;
    tryif constr_eq m mem0 then idtac else
      (lazymatch m with ms_mem ?o =>
         lazymatch goal with HMo : ms_mem o = mem0 |- _ => rewrite HMo in H; clear HMo end end)
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* A register of the state the walk stopped in. *)
Ltac rw_reg HS :=
  lazymatch goal with |- getr (ms_regs ?ms0) ?r = _ =>
    let R := fresh "R" in prreg HS r R; rewrite R; clear R end.
Ltac rw_close :=
  repeat match goal with H : ew ?E ?n = _ |- context [ew ?E ?n] => rewrite H end;
  first [ reflexivity | unfold w64; rewrite ?unsigned_lit_small by lia; f_equal; lia ].
Ltac rw_keep HS ER := cbn [ms_regs mkst]; rw_reg HS; apply ER; reflexivity.
Ltac rw_val HS := cbn [ms_regs mkst]; rw_reg HS; rw_close.
(* The branch at 0x814e0 / 0x81504 / 0x81528 / 0x8154c into the abort block: byte k of
   the row is V, the literal the cut holds in t0 / t2 / t4 / t6. *)
Ltac rw_byte Hc k V ED :=
  rewrite branch_ne_U in Hc;
  rewrite (gs_U_data1 _ k (Z_to_bv 8 V)) in Hc; [| lia | cbn [ed ewset]; rewrite ED; reflexivity];
  rewrite U_lit in Hc by lia;
  vm_compute in Hc; discriminate Hc.
(* The branch at 0x81554 into the abort block: the low byte of the sum of bytes 2..33 is 0. *)
Ltac rw_sum_abort Hc ED Hrest Hsum :=
  rewrite branch_ne_U in Hc;
  rewrite U_and_lit in Hc by lia;
  rewrite U_lit in Hc by lia;
  lazymatch type of Hc with context [U ?E0 ?X] =>
    replace (U E0 X) with (U E0 (rw_sum 32)) in Hc by reflexivity end;
  rewrite U_rw_sum in Hc; [| intros kk Hkk; cbn [ed ewset]; rewrite ED; cbn [length]; rewrite Hrest; lia | lia];
  cbn [ed ewset] in Hc; rewrite ED in Hc;
  rewrite rw_zsum_row in Hc by exact Hrest;
  rewrite land255, Hsum in Hc; vm_compute in Hc; discriminate Hc.
(* An atom fact of `rw_facts`: the atom's value and its range. *)
Ltac rw_afact EN :=
  unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite EN; unfold w64;
  rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia);
  rewrite Z.pow_0_r, Z.mod_1_r; unfold SHADOW_OFF; lia.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

(* Byte i of row j of the sweep, from the sweep's bytes and fuzz_grant's row model. *)
Lemma rw_row_mem : forall (m : word -> option byte) s pl t j i,
  garr8 SEGS m s (map (fun b : byte => bv_unsigned b) (sw_bytes pl t)) ->
  (j < length (sweep_rows (sw_base pl) (Z.to_nat (sw_in pl)) (sw_vals pl t)))%nat -> 0 <= i < 34 ->
  mbyte SEGS m (s + 34 * Z.of_nat j + i) =
  Some (nth (Z.to_nat i) (nth j (sweep_rows (sw_base pl) (Z.to_nat (sw_in pl)) (sw_vals pl t)) []) (Z_to_bv 8 0)).
Proof.
intros m s pl t j i HSW Hj Hi.
set (rows := sweep_rows (sw_base pl) (Z.to_nat (sw_in pl)) (sw_vals pl t)) in *.
assert (HL : Forall (fun r => length r = 34%nat) rows) by (apply Forall_rowok_len, sweep_rows_ok).
assert (Hlr : length (nth j rows []) = 34%nat).
{ rewrite Forall_forall in HL. apply HL. apply nth_In. exact Hj. }
unfold sw_bytes in HSW. rewrite SWEEP_rows in HSW. fold rows in HSW.
pose proof (nth_error_concat34 rows j (Z.to_nat i) HL Hj ltac:(lia)) as Hq.
rewrite (nth_error_nth' (nth j rows []) (Z_to_bv 8 0)) in Hq by lia.
assert (Hq' : (34 * j + Z.to_nat i < length (concat rows))%nat) by (apply nth_error_Some; rewrite Hq; discriminate).
pose proof (garr8_mbyte SEGS m s _ (34 * j + Z.to_nat i) HSW ltac:(rewrite length_map; exact Hq')) as Hb.
rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) in Hb by (rewrite length_map; exact Hq').
rewrite map_nth in Hb.
rewrite (nth_error_nth _ _ _ Hq) in Hb.
rewrite Z_to_bv_bv_unsigned in Hb.
replace (s + 34 * Z.of_nat j + i) with (s + Z.of_nat (34 * j + Z.to_nat i)) by lia. exact Hb.
Qed.

(* What a cut keeps when the machine moves on without writing memory. *)
Lemma ge_body_step : forall (cx : ecx) fp pc pc' W (ms ms' : machine_state) sh,
  ge_body cx fp pc W ms sh -> ms_mem ms' = ms_mem ms -> ms_pc_val ms' = w64 (BASE + pc') ->
  ms_resv ms' = None -> ms_svc_pending ms' = None -> ms_rom ms' = seg_rom SEGS ->
  ms_fregs ms' = fp_regs -> ms_fcsr ms' = fp_csr ->
  getr (ms_regs ms') 2 = getr (ms_regs ms) 2 -> getr (ms_regs ms') 8 = getr (ms_regs ms) 8 ->
  getr (ms_regs ms') 9 = getr (ms_regs ms) 9 -> getr (ms_regs ms') 3 = getr (ms_regs ms) 3 ->
  getr (ms_regs ms') 4 = getr (ms_regs ms) 4 ->
  ge_body cx fp pc' W ms' sh.
Proof.
intros cx fp pc pc' W ms ms' sh (_ & _ & _ & _ & _ & _ & (G2 & G8 & G9 & G3 & G4) & HSV & HSH & HFL & HLEN & HIN)
  Hm Hpc Hrv Hsv Hrom Hfr Hfc R2 R8 R9 R3 R4.
unfold ge_body, gregs, gsaved, gshadow in *. rewrite Hm, R2, R8, R9, R3, R4.
exact (conj Hpc (conj Hrv (conj Hsv (conj Hrom (conj Hfr (conj Hfc (conj (conj G2 (conj G8 (conj G9 (conj G3 G4))))
  (conj HSV (conj HSH (conj HFL (conj HLEN HIN))))))))))).
Qed.

Lemma gsw_rows_step : forall (cx : ecx) W (ms ms' : machine_state) t s,
  gsw_rows cx W ms t s -> ms_mem ms' = ms_mem ms -> gsw_rows cx W ms' t s.
Proof. intros cx W ms ms' t s H Hm. unfold gsw_rows in *. rewrite Hm. exact H. Qed.

Lemma gslot_step : forall (cx : ecx) W (ms ms' : machine_state) off v,
  gslot cx W ms off v -> ms_mem ms' = ms_mem ms -> gslot cx W ms' off v.
Proof. intros cx W ms ms' off v H Hm. unfold gslot in *. rewrite Hm. exact H. Qed.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

Lemma gsw_blk_step : forall (cx : ecx) fp ly S W (ms ms' : machine_state) t s,
  gsw_blk B cx fp ly S W ms t s -> ms_mem ms' = ms_mem ms -> gsw_blk B cx fp ly S W ms' t s.
Proof.
intros cx fp ly S W ms ms' t s H Hm.
unfold gsw_blk, gtab, gfarr, gsw_slots, gslot, gfb in *. rewrite Hm. exact H.
Qed.

(* The loop, by induction on the rows left (cgif lib/A/AC8c.v:47, tcbl_loop). *)
Lemma gsw_rows_loop : forall (POST : ecx -> world SEGS -> config -> Prop),
  ge_from B MT POST (GIS_rowex B MT) ->
  forall (m : nat) (cx : ecx) (fp k acc : Z) ly3 S3 W3 (ms3 : machine_state) md3,
  Z.to_nat (sw_n (c_pl cx) - bv_unsigned (getr (ms_regs ms3) 13)) = m ->
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  YG01.frames S3 = [(GE_CID, fp)] ->
  mo_le MT (c_S cx) S3 acc ->
  GIS_rowhd B MT cx fp k acc ly3 S3 W3 ms3 md3 ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
intros POST NEXT m. induction m as [|m IH];
intros cx fp k acc ly3 S3 W3 ms3 md3 Hm Hbase HJ Hfr Hmo HGI;
destruct HGI as (t & s & j & HBODY & Hk & Hacc & HBLK & HROWS & SL88 & Hj & R13 & R10 & R14 & R21 & R24
  & R27 & R19 & R15 & R16 & R17 & R5 & R6 & R7 & R28 & R29 & R30 & R31);
pose proof HBLK as (_ & Hin & _ & _ & _ & _ & _ & SLOTS & _ & Ht0 & Hs0 & _ & _ & _);
pose proof SLOTS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SL144 & _);
pose proof HROWS as (Hwant & HSW);
pose proof (proj1 HJ) as HAR;
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (Hal16 & H4096 & Hceil & Happ & _ & _ & Hmax);
pose proof asan_consts as (C1 & _);
pose proof (gs_rows_range (c_pl cx)) as Hrws;
assert (Hn : sw_n (c_pl cx) = sw_want (c_pl cx)) by (unfold sw_n; rewrite (proj2 (Z.leb_le _ _) Hwant); reflexivity);
assert (Hmb : sw_mbytes (c_pl cx) = 34 * sw_rows (c_pl cx))
  by (unfold sw_mbytes; rewrite (proj2 (Z.ltb_lt 0 _)) by lia; reflexivity);
pose proof (req_size_pos (sw_mbytes (c_pl cx)) ltac:(lia)) as Hreq;
rewrite R13 in Hm; unfold w64 in Hm; rewrite unsigned_lit_small in Hm by lia.
{ lia. }
(* ---- the realigned stack pointer, where the spill slots are ---- *)
pose proof Hbase as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1d & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16s & Hstk0 & Hceils & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (FFS : GE_STK = 32768) by reflexivity.
assert (Has : ASTACK = 16384) by reflexivity.
assert (Hsp288 : 0 <= spZ (c_regs cx) + -288) by lia.
assert (Hmod288 : (spZ (c_regs cx) + -288) mod 16 = 0)
  by (rewrite <- Zplus_mod_idemp_l, Hal16s; reflexivity).
destruct (sp1_facts (spZ (c_regs cx) + -288) Hsp288 Hmod288) as (Hsp1r & Hsp1al32 & Hsp1al16).
rewrite <- Hsp1d in Hsp1r, Hsp1al32, Hsp1al16.
assert (Hsp1lo : alloc_ceiling <= c_sp1 cx) by lia.
assert (Hsp1hi : c_sp1 cx + 192 <= 2 ^ 64) by lia.
(* ---- the machine state the walk starts from ---- *)
pose proof HBODY as (Hpc & Hrv & Hsv & Hrom & Hfrg & Hfcsr & (G2 & G8 & G9 & G3 & G4) & _).
destruct ms3 as [regs3 fregs3 pc3 svc3 resv3 fcsr3 mem3 rom3].
cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in *.
subst fregs3 pc3 svc3 resv3 fcsr3 rom3.
change (SRr SEGS W3 (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + GPS_rowhd)) mem3 (seg_rom SEGS)) md3) (POST cx)).
(* ---- row j of the sweep, from fuzz_grant's model ---- *)
assert (Lj : (j < length (sweep_rows (sw_base (c_pl cx)) (Z.to_nat (sw_in (c_pl cx))) (sw_vals (c_pl cx) t)))%nat).
{ pose proof (length_sweep_rows_ge (sw_base (c_pl cx)) (Z.to_nat (sw_in (c_pl cx))) (sw_vals (c_pl cx) t)) as HL.
  assert (Hw : sw_want (c_pl cx) = 8 + 3 * sw_in (c_pl cx)) by reflexivity. lia. }
assert (HRok : rowok (nth j (sweep_rows (sw_base (c_pl cx)) (Z.to_nat (sw_in (c_pl cx))) (sw_vals (c_pl cx) t)) [])).
{ apply (proj1 (Forall_forall _ _) (sweep_rows_ok (sw_base (c_pl cx)) (Z.to_nat (sw_in (c_pl cx))) (sw_vals (c_pl cx) t))).
  apply nth_In. exact Lj. }
pose proof (fun i Hi => rw_row_mem _ s (c_pl cx) t j i HSW Lj Hi) as MEMB.
destruct (rowok_split _ HRok) as (rest & HRB & Hrest & Hsum). rewrite HRB in MEMB. clear HRok.
(* ---- the environment: the registers, the row's address (atom 32), -1 - s (33), -1 - row
   (34), the shadow offset (35), the row's bytes (slot 0) ---- *)
remember (Eimg (edset (Ereg regs3 [w64 (s + 34 * Z.of_nat j); w64 (2 ^ 64 - 1 - s);
  w64 (2 ^ 64 - 1 - (s + 34 * Z.of_nat j)); w64 SHADOW_OFF]) 0
  (Z_to_bv 8 205 :: Z_to_bv 8 234 :: Z_to_bv 8 4 :: Z_to_bv 8 3 :: rest))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (ER : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs3 r).
{ intros n r Hnr. subst E. pose proof (u5_range r). rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_nat regs3 _ n r Hnr). }
assert (E32 : ew E 32 = w64 (s + 34 * Z.of_nat j)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
assert (E33 : ew E 33 = w64 (2 ^ 64 - 1 - s)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
assert (E34 : ew E 34 = w64 (2 ^ 64 - 1 - (s + 34 * Z.of_nat j)))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
assert (E35 : ew E 35 = w64 SHADOW_OFF) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
assert (ED : ed E 0 = Z_to_bv 8 205 :: Z_to_bv 8 234 :: Z_to_bv 8 4 :: Z_to_bv 8 3 :: rest) by (subst E; reflexivity).
clear HE.
assert (E9 : ew E 9 = w64 (c_sp1 cx)) by (transitivity (getr regs3 9); [apply ER; reflexivity | exact G9]).
assert (E10 : ew E 10 = w64 (sw_n (c_pl cx))) by (transitivity (getr regs3 10); [apply ER; reflexivity | exact R10]).
assert (E13 : ew E 13 = w64 (Z.of_nat j)) by (transitivity (getr regs3 13); [apply ER; reflexivity | exact R13]).
assert (E19 : ew E 19 = w64 (gSH cx fp)) by (transitivity (getr regs3 19); [apply ER; reflexivity | exact R19]).
assert (E27 : ew E 27 = w64 s) by (transitivity (getr regs3 27); [apply ER; reflexivity | exact R27]).
assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = s + 34 * Z.of_nat j) by (rewrite E32; apply unsigned_lit_small; lia).
(* ---- the symbolic state and the shadow entry of the row ---- *)
assert (HS : st_ok_pi SEGS VAL E ss_rw (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + GPS_rowhd)) mem3 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_rw. apply pa_entry_st_ok_full.
  - apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
    repeat (destruct Hr as [<-|Hr];
      [ match goal with |- _ = sv_denot ?E0 (sr_get ?sr ?r0) =>
          let v := eval vm_compute in (sr_get sr r0) in change (sr_get sr r0) with v end;
        first [ rewrite getr_zero; reflexivity
              | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; symmetry; apply ER; reflexivity
              | cbn [sv_denot]; first [ exact R5 | exact R6 | exact R7 | exact R15 | exact R16 | exact R17
                                      | exact R28 | exact R29 | exact R30 | exact R31 ]
              | cbn [sv_denot]; rewrite E32; unfold w64; rewrite unsigned_lit_small by lia;
                first [ transitivity (w64 (s + 34 * Z.of_nat j + 2)); [first [exact R14 | exact R21] | unfold w64; f_equal; lia]
                      | transitivity (w64 (s + 34 * Z.of_nat j)); [exact R24 | unfold w64; f_equal; lia] ]
              | match goal with |- ?g => fail 100 "rw regs_ok" g end ]
      | ]).
    destruct Hr.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold rw_region, YP09.region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
      rewrite U32.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      intros i Hi. cbn [YP09.c_len YP09.c_val YP09.c_off YP09.cv_len] in Hi |- *.
      exists (nth (Z.to_nat i) (Z_to_bv 8 205 :: Z_to_bv 8 234 :: Z_to_bv 8 4 :: Z_to_bv 8 3 :: rest) (Z_to_bv 8 0)).
      cbn [YP09.cbyte]. rewrite ED. split.
      * rewrite Z.add_0_l. apply nth_error_nth'. cbn [length]. lia.
      * rewrite Z.add_0_r. exact (MEMB i Hi).
    + unfold rw_slots.
      apply (gs_slotreg_ok W3 E mem3 _ (c_sp1 cx) 0 0 U9 ltac:(lia) ltac:(lia) ltac:(intros o Ho; lia)).
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * exact (gs_slot_chunk W3 E mem3 88 33%nat (2 ^ 64 - 1 - s) (c_sp1 cx) E33 U9 SL88).
      * exact (gs_slot_chunk W3 E mem3 144 35%nat SHADOW_OFF (c_sp1 cx) E35 U9 SL144).
  - cbn [YP09.pairwise_disjoint YP09.all_disjoint].
    split; [split; [|exact I] | split; exact I].
    unfold YP09.extent_disjoint, rw_region, rw_slots.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val]. rewrite U32, U9. lia.
  - split; [|split; [exact I|]].
    + cbn [rw_facts f_atoms atoms_ok].
      split; [rw_afact E13|]. split; [rw_afact E32|]. split; [rw_afact E33|].
      split; [rw_afact E34|]. split; [rw_afact E35 | exact I].
    + cbn [rw_facts f_alias alias_ok]. split; [|split; [|exact I]].
      * apply U_inj. unfold rw_alias.
        rewrite U_SAlu, U_SMd. cbn [zalu_raw zmd_raw].
        rewrite (U_atom E 27 s) by first [exact E27 | lia].
        rewrite (U_atom E 13 (Z.of_nat j)) by first [exact E13 | lia].
        rewrite (U_lit E 34) by lia.
        rewrite (U_atom E 32 (s + 34 * Z.of_nat j)) by first [exact E32 | lia].
        rewrite (zcanon_id (Z.of_nat j * 34)) by (unfold M64; lia).
        rewrite zcanon_id by (unfold M64; lia). lia.
      * apply U_inj. unfold rw_alias_not.
        rewrite U_SAlu, U_SLit. cbn [zalu_raw].
        rewrite (U_atom E 32 (s + 34 * Z.of_nat j)) by first [exact E32 | lia].
        rewrite (U_atom E 34 (2 ^ 64 - 1 - (s + 34 * Z.of_nat j))) by first [exact E34 | lia].
        change (zcanon (-1)) with (2 ^ 64 - 1).
        apply zcanon_id. unfold M64. lia. }
assert (SHOK : sh_ok SEGS rw_Bx rw_SH E (mrestrict (w_H W3) mem3)).
{ unfold sh_ok, rw_SH. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H W3) mem3 E rw_Bx 32 (s + 34 * Z.of_nat j) 34 (s + 34 * Z.of_nat j) 0 34).
  - eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR Hin); lia.
  - unfold rw_Bx. apply U_atom; [exact E35 | unfold SHADOW_OFF; lia].
  - apply U_atom; [exact E32 | lia].
  - lia.
  - lia.
  - intros x Hx. revert Happ Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia. }
(* ---- the walk: guard 1, the sum with guard 2, then row[0] = 0xcd (0x814e0) ---- *)
paj_run_tok RUN HS HJ SHOK rw_Bspan; [awr_ok_tac |].
rw_mem mem3.
psrr_branch_tok RUN BR HS SHOK rw_Bspan; [rw_byte Hc 0 205 ED | clear Hc].
(* guard 3, row[1] = 0xea (0x81504) *)
paj_run_tok RUN HS HJ SHOK rw_Bspan; [awr_ok_tac |].
rw_mem mem3.
psrr_branch_tok RUN BR HS SHOK rw_Bspan; [rw_byte Hc 1 234 ED | clear Hc].
(* guard 4, row[2] = 4 (0x81528) *)
paj_run_tok RUN HS HJ SHOK rw_Bspan; [awr_ok_tac |].
rw_mem mem3.
psrr_branch_tok RUN BR HS SHOK rw_Bspan; [rw_byte Hc 2 4 ED | clear Hc].
(* guard 5, row[3] = 3 (0x8154c) *)
paj_run_tok RUN HS HJ SHOK rw_Bspan; [awr_ok_tac |].
rw_mem mem3.
psrr_branch_tok RUN BR HS SHOK rw_Bspan; [rw_byte Hc 3 3 ED | clear Hc].
(* the low byte of the sum is 0 (0x81554) *)
paj_run_tok RUN HS HJ SHOK rw_Bspan; [awr_ok_tac |].
rw_mem mem3.
psrr_branch_tok RUN BR HS SHOK rw_Bspan; [rw_sum_abort Hc ED Hrest Hsum | clear Hc].
(* the loop test at 0x81568 *)
paj_run_tok RUN HS HJ SHOK rw_Bspan; [awr_ok_tac |].
rw_mem mem3.
psrr_branch_tok RUN BR HS SHOK rw_Bspan.
- (* j + 1 < n: back to the head with j + 1 rows checked *)
  rewrite branch_ne_U in Hc.
  rewrite (U_atom_off _ 13 (Z.of_nat j) 1) in Hc; [| cbn [ew ewset Nat.eqb]; exact E13 | lia | lia].
  rewrite (U_atom _ 10 (sw_n (c_pl cx))) in Hc; [| cbn [ew ewset Nat.eqb]; exact E10 | lia].
  apply negb_true_iff, Z.eqb_neq in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK rw_Bspan GPS_rowhd; [awr_ok_tac |].
  rw_mem mem3. pmkst HS.
  lazymatch goal with HM : ms_mem ?msf = mem3 |- _ => rewrite HM in HJ |- * end.
  apply (IH cx fp k acc ly3 S3 W3).
  + cbn [ms_regs mkst].
    lazymatch type of HS with context [restrict _ ?msf] =>
      assert (X : getr (ms_regs msf) 13 = w64 (Z.of_nat (S j))) by rw_val HS; rewrite X end.
    unfold w64. rewrite unsigned_lit_small by lia. lia.
  + exact Hbase.
  + exact HJ.
  + exact Hfr.
  + exact Hmo.
  + unfold GIS_rowhd. exists t, s, (S j).
    split; [eapply ge_body_step; [exact HBODY | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
      | reflexivity | reflexivity | rw_keep HS ER | rw_keep HS ER | rw_keep HS ER | rw_keep HS ER | rw_keep HS ER] |].
    split; [exact Hk|]. split; [exact Hacc|].
    split; [eapply gsw_blk_step; [exact HBLK | reflexivity] |].
    split; [eapply gsw_rows_step; [exact HROWS | reflexivity] |].
    split; [eapply gslot_step; [exact SL88 | reflexivity] |].
    split; [lia|].
    repeat (split; [rw_val HS|]). rw_val HS.
- (* j + 1 = n: on to 0x815d0, every row checked *)
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK rw_Bspan GPS_rowex; [awr_ok_tac |].
  rw_mem mem3. pmkst HS.
  lazymatch goal with HM : ms_mem ?msf = mem3 |- _ => rewrite HM in HJ |- * end.
  apply (NEXT cx fp k acc ly3 S3 W3); [exact Hbase | exact HJ | exact Hfr | exact Hmo |].
  unfold GIS_rowex. exists t, s.
  split; [eapply ge_body_step; [exact HBODY | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
    | reflexivity | reflexivity | rw_keep HS ER | rw_keep HS ER | rw_keep HS ER | rw_keep HS ER | rw_keep HS ER] |].
  split; [exact Hk|]. split; [exact Hacc|].
  split; [eapply gsw_blk_step; [exact HBLK | reflexivity] |].
  split; [eapply gsw_rows_step; [exact HROWS | reflexivity] |].
  split; [eapply gslot_step; [exact SL88 | reflexivity] |].
  split; rw_val HS.
Qed.

End c.
End b.
End a.

Section z. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section zb.
Context {PI : PAImg grant_listing}.

Lemma gsw_seg_rows : forall (B : asyms) (MT : ameter_ops), @SEG_rows fx rc SK PI B MT.
Proof.
intros B MT RT NEXT.
destruct RT as (LAWS & TL & TLF & ML & MTL & MTF & AMALLOC4 & AFREE4 & ABCMP & HIMG & HGL & RO).
intros cx fp k acc ly3 S3 W3 ms3 md3 Hbase HJ Hfr Hmo HGI.
exact (gsw_rows_loop B MT LAWS (ge_post B MT) NEXT _ cx fp k acc ly3 S3 W3 ms3 md3 eq_refl Hbase HJ Hfr Hmo HGI).
Qed.

End zb.
End z.
