(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of rec_calls_equal on the ASan+UBSan build of plugin-hostd/fuzz_command
   (0x89ef8, 164 instructions, frame 144 bytes), ported from the ASan walk lib/A/Prog/rec_calls_equal.v (0x89968). The
   shape is the A walk's: the symbolic executor over the position-abstract listing (CmdPaLib.v), the inline checks removed
   by the shadow tokens (PaShadow.v), the strcmp wrapper's call stepped through by its Theorem Labs lane contract (PaArt.v
   aj_art_at), the two loops cut at their heads (0x89f98, 0x8a064) and at the outer latch (0x8a0b4), each piece re-seeded
   from the concrete state there, the loops proved by induction. What B changes:
   - the frame (144 bytes) keeps n at 0(sp), the UBSan predicates `b mod 8 = 0 && b <> 0`, `b <> 0`,
     `a mod 8 = 0 && a <> 0` at 8(sp), 16(sp), 24(sp), and b at 32(sp); a stays in a5/s11 and `a <> 0` in a4/s8;
   - the inner loop counts s5 = 8k up to s2 = 8 * nargs and forms both argument addresses from s3/s10 (a[i].args) and
     s1/s9 (b[i].args) plus s5 (the seed's alias facts name the two sums);
   - eight UBSan trap branches, all to the `unimp` at 0x8a168, are refuted from the run's facts: 0x89fac, 0x89fbc,
     0x89fe4, 0x89ff4 are decided by the executor (a4 = 1 and the three predicate slots = 1 at the outer seed, which the
     entry derives from rce_calls' `a mod 8 = 0` and rce_home's 4096 <= a; a + 56i >= 4096 by the seed's atom fact);
     0x89fb4 and 0x89fec (a + 56i < a, b + 56i < b unsigned) and 0x8a064, 0x8a068 (~(a[i].args) < 8k, ~(b[i].args) < 8k)
     are refuted at the branch from the values of their operands. *)
(* Section hypotheses besides the statement's own ASTRCMP: TL (the shadow GOT and cell, CmdPaLib.v); HB (the
   allocator record's zero-shadow ranges, for g_rec and record.spill), from which CmdRecFacts.v's cmd_heap_tail_vis
   gives the readable word tail after a heap string (every argument string is a live block). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YG0p YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaDenot PaSB PaLibG PaLibH PaLibF PaCallRun PaCall.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdZsh PaArt PaNoChain rec_calls_equal_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecFacts.
Import ListNotations.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- the result: calls_eqb of the plain contract (lib/Prog/rec_calls_equal_c.v:32-47) ---------- *)
Lemma rce_map_unsigned_inj : forall (x y : list byte), map bv_unsigned x = map bv_unsigned y -> x = y.
Proof.
induction x as [|u x IH]; intros [|v y] H; cbn in H; try discriminate; [reflexivity|].
injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.
Lemma rce_cstr_eqb : forall x y, PRce.cstr_eqb x y = true <-> x = y.
Proof.
intros x y. unfold PRce.cstr_eqb. destruct (list_eq_dec Z.eq_dec _ _) as [H|H]; split; intros E.
- exact (rce_map_unsigned_inj x y H).
- reflexivity.
- discriminate E.
- exfalso. apply H. rewrite E. reflexivity.
Qed.
Lemma rce_args_eqb_true : forall x y, length x = length y ->
(forall k p q, nth_error x k = Some p -> nth_error y k = Some q -> snd p = snd q) -> PRce.args_eqb x y = true.
Proof.
induction x as [|p x IH]; intros [|q y] Hl H; cbn in Hl |- *; try discriminate; [reflexivity|].
apply andb_true_intro. split.
- apply rce_cstr_eqb. exact (H 0%nat p q eq_refl eq_refl).
- apply IH; [lia|]. intros k p' q' H1 H2. exact (H (S k) p' q' H1 H2).
Qed.
Lemma rce_args_eqb_len : forall x y, length x <> length y -> PRce.args_eqb x y = false.
Proof.
induction x as [|p x IH]; intros [|q y] Hl; cbn in Hl |- *; try reflexivity; [exfalso; lia|].
rewrite IH by lia. apply andb_false_r.
Qed.
Lemma rce_args_eqb_diff : forall x y k p q, nth_error x k = Some p -> nth_error y k = Some q -> snd p <> snd q ->
PRce.args_eqb x y = false.
Proof.
induction x as [|p0 x IH]; intros [|q0 y] k p q H1 H2 Hne; destruct k; cbn in H1, H2 |- *; try discriminate.
- injection H1 as <-. injection H2 as <-. destruct (PRce.cstr_eqb (snd p0) (snd q0)) eqn:E; [|reflexivity].
  apply rce_cstr_eqb in E. contradiction.
- rewrite (IH y k p q H1 H2 Hne). apply andb_false_r.
Qed.
Definition rce_slot_eq (e f : PRce.rc_entry) : Prop := fst e = fst f /\ PRce.args_eqb (snd e) (snd f) = true.
Lemma rce_calls_eqb_true : forall x y, length x = length y ->
(forall i e f, nth_error x i = Some e -> nth_error y i = Some f -> rce_slot_eq e f) -> PRce.calls_eqb x y = true.
Proof.
induction x as [|e x IH]; intros [|f y] Hl H; cbn in Hl |- *; try discriminate; [reflexivity|].
destruct (H 0%nat e f eq_refl eq_refl) as [H1 H2]. rewrite H1, Z.eqb_refl, H2. cbn [andb].
apply IH; [lia|]. intros i e' f' A1 A2. exact (H (S i) e' f' A1 A2).
Qed.
Lemma rce_calls_eqb_len : forall x y, length x <> length y -> PRce.calls_eqb x y = false.
Proof.
induction x as [|e x IH]; intros [|f y] Hl; cbn in Hl |- *; try reflexivity; [exfalso; lia|].
rewrite IH by lia. apply andb_false_r.
Qed.
Lemma rce_calls_eqb_diff : forall x y i e f, nth_error x i = Some e -> nth_error y i = Some f -> ~ rce_slot_eq e f ->
PRce.calls_eqb x y = false.
Proof.
induction x as [|e0 x IH]; intros [|f0 y] i e f H1 H2 Hn; destruct i; cbn in H1, H2 |- *; try discriminate.
- injection H1 as <-. injection H2 as <-.
  destruct (fst e0 =? fst f0) eqn:E1; [|reflexivity]. destruct (PRce.args_eqb (snd e0) (snd f0)) eqn:E2; [|reflexivity].
  exfalso. apply Hn. split; [apply Z.eqb_eq; exact E1 | exact E2].
- rewrite (IH y i e f H1 H2 Hn). apply andb_false_r.
Qed.

(* ---------- small facts about bytes, words and readers ---------- *)
Lemma rce_val_mem_of_aval : forall segs H mem a n v,
aval_mem (aview segs H mem) a n v -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem a n v Hr k Hk. pose proof (Hr k Hk) as Hb.
destruct (aview_byte segs H mem _ _ Hb) as (b & Hm & Hbv & Hrange). rewrite Hm. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Hbv. rewrite Z.mod_small; [reflexivity|].
change (bv_modulus 8) with 256. exact Hrange.
Qed.
Lemma rce_aval_kept : forall (rd rd' : reader) a n v, (forall k, (k < n)%nat -> rd' (a + Z.of_nat k) = rd (a + Z.of_nat k)) ->
aval_mem rd a n v -> aval_mem rd' a n v.
Proof. intros rd rd' a n v Hk H k Hkn. rewrite (Hk k Hkn). exact (H k Hkn). Qed.
Lemma rce_le_byte_mod : forall v n k, le_byte (v mod 2 ^ (8 * Z.of_nat n)) n k = le_byte v n k.
Proof. intros v n k. unfold le_byte. rewrite Z.mod_mod by (apply Z.pow_nonzero; lia). reflexivity. Qed.
Lemma rce_aval_mod : forall rd a n v, aval_mem rd a n v -> aval_mem rd a n (v mod 2 ^ (8 * Z.of_nat n)).
Proof. intros rd a n v H k Hk. rewrite rce_le_byte_mod. exact (H k Hk). Qed.
Lemma rce_astr_some : forall (rd : reader) p x a, astr_atR rd p x -> p <= a < p + (Z.of_nat (length x) + 1) -> rd a <> None.
Proof.
intros rd p x a [Hb _] Ha. replace a with (p + Z.of_nat (Z.to_nat (a - p))) by lia. rewrite Hb; [discriminate|].
rewrite length_app; cbn; lia.
Qed.


(* ---------- word facts of the B code: its `not`, `slli 3`, the UBSan predicates, the inner loop's sums ---------- *)
(* Z.lxor with all ones (as lib/Reusable/YI08.v:163-176, lxor_allones) *)
Lemma rce_lxor_allones : forall x, 0 <= x < 2 ^ 64 -> Z.lxor x (2 ^ 64 - 1) = 2 ^ 64 - 1 - x.
Proof.
intros x Hx.
assert (E : 2 ^ 64 - 1 - x = Z.lnot x mod 2 ^ 64).
{ rewrite Z.lnot_eq_pred_opp. apply Z.mod_unique_pos with (q := -1); lia. }
rewrite E. apply Z.bits_inj'. intros i Hi.
rewrite Z.lxor_spec. replace (2 ^ 64 - 1) with (Z.ones 64) by reflexivity.
rewrite Z.testbit_mod_pow2, Z.lnot_spec by lia.
destruct (Z.ltb_spec i 64).
- rewrite Z.ones_spec_low by lia. replace (i <? 64) with true by (symmetry; apply Z.ltb_lt; lia).
  destruct (Z.testbit x i); reflexivity.
- rewrite Z.ones_spec_high by lia. replace (i <? 64) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite (Z_testbit_high 64 x i) by lia. reflexivity.
Qed.
Lemma rce_xor_m1 : forall x, 0 <= x < 2 ^ 64 -> alu64 ALU_XOR (Z_to_bv 64 x) (Z_to_bv 64 (-1)) = Z_to_bv 64 (2 ^ 64 - 1 - x).
Proof.
intros x Hx. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite unsigned_lit_small by lia.
replace (bv_unsigned (Z_to_bv 64 (-1))) with (2 ^ 64 - 1) by (rewrite Z_to_bv_unsigned; reflexivity).
rewrite rce_lxor_allones by lia. rewrite unsigned_lit_small by lia.
apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.
Lemma rce_sll3 : forall x, 0 <= x < 2 ^ 60 -> alu64 ALU_SLL (Z_to_bv 64 x) (Z_to_bv 64 3) = Z_to_bv 64 (8 * x).
Proof.
intros x Hx. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !unsigned_lit_small by lia.
change (Z.land 3 63) with 3. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
rewrite bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). lia.
Qed.
Lemma rce_sltu0 : forall x, 0 < x < 2 ^ 64 -> alu64 ALU_SLTU (Z_to_bv 64 0) (Z_to_bv 64 x) = Z_to_bv 64 1.
Proof.
intros x Hx. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !unsigned_lit_small by lia.
destruct (Z.ltb_spec 0 x); [reflexivity | lia].
Qed.
(* the predicate `x mod 8 = 0 && x <> 0` the entry spills to 8(sp) (x = b) and 24(sp) (x = a) *)
Lemma rce_flag : forall x, 0 < x < 2 ^ 64 -> x mod 8 = 0 ->
alu64 ALU_AND (alu64 ALU_SLTU (alu64 ALU_AND (Z_to_bv 64 x) (Z_to_bv 64 7)) (Z_to_bv 64 1))
  (alu64 ALU_SLTU (Z_to_bv 64 0) (Z_to_bv 64 x)) = Z_to_bv 64 1.
Proof.
intros x Hx H8. rewrite (rce_sltu0 x Hx).
assert (HA : alu64 ALU_AND (Z_to_bv 64 x) (Z_to_bv 64 7) = Z_to_bv 64 0).
{ apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !unsigned_lit_small by lia.
  change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8. rewrite H8. reflexivity. }
rewrite HA. apply bv_eq. vm_compute. reflexivity.
Qed.
Lemma rce_add64 : forall x y, 0 <= x -> 0 <= y -> x + y < 2 ^ 64 -> alu64 ALU_ADD (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x + y).
Proof.
intros x y Hx Hy Hxy. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !unsigned_lit_small by lia.
apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.
(* the inner loop's sums s10 + s5, s3 + s5 (a[i].args + 8k) and s9 + s5, s1 + s5 (b[i].args + 8k) *)
Lemma rce_alias_add : forall E n m p x c y, ew E n = w64 x -> ew E m = w64 y -> ew E p = w64 (x + c + y) ->
0 <= x < 2 ^ 64 -> 0 <= y -> 0 <= x + c -> x + c + y < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SOff n c) (SOff m 0)) = sv_denot E (SOff p 0).
Proof.
intros E n m p x c y Hn Hm Hp Hx Hy Hxc Hs. cbn [sv_denot]. rewrite Hn, Hm, Hp. unfold w64.
rewrite !unsigned_lit_small by lia. rewrite !Z.add_0_r. apply rce_add64; lia.
Qed.


Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the listing offsets of the cut points (BASE + AF_rec_calls_equal = 0x89ef8) *)
Definition RCE_OH : Z := 14952.   (* 0x89f98, the outer loop's head *)
Definition RCE_IH : Z := 15156.   (* 0x8a064, the inner loop's head (its two wrap traps) *)
Definition RCE_LT : Z := 15236.   (* 0x8a0b4, the outer loop's latch *)
Definition RCE_EPI : Z := 15348.  (* 0x8a124, the epilogue, a0 already set *)
(* the frame: ra and s0..s11 saved at sp0-8 .. sp0-104 *)
Definition rce_saved : list Z := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition rce_PTRF : afact := mkAF 4096 (2 ^ 47 - 64) 0.
Definition rce_NF : afact := mkAF 0 6 0.
Definition rce_spF : afact := mkAF (2 ^ 46) (2 ^ 47) 4.
Definition rce_SBF : afact := mkAF SB SB 0.
Definition rce_Bx : sv := SOff 32 0.

(* the symbolic states of the cut points; atoms 32.. are the seed's extra words *)
Definition rce_estack : YP09.region := YP09.mkRegion (Some 2%nat) 0 144 0 0
  (map (fun j => YP09.mkChunk (136 - 8 * Z.of_nat j) (CVal 8 (SOff (32 + j) 0))) (seq 0 13)).
Definition rce_ss_epi : sstate := mkSS RCE_EPI sr_atoms [rce_estack] None (mkFacts [(2%nat, rce_spF)] [] []).
(* the frame slots every loop state keeps: n, the three UBSan predicates (all 1 on this path), b *)
Definition rce_fstack : YP09.region := YP09.mkRegion (Some 2%nat) 0 144 0 0
  [YP09.mkChunk 0 (CVal 8 (SOff 35 0)); YP09.mkChunk 8 (CVal 8 (SLit 1)); YP09.mkChunk 16 (CVal 8 (SLit 1));
   YP09.mkChunk 24 (CVal 8 (SLit 1)); YP09.mkChunk 32 (CVal 8 (SOff 34 0))].
(* outer head: a5 = a, a4 = (a <> 0) = 1, s4 = i, s7 = the shadow base, s3 = s10 = a + 56i + 8, s1 = s9 = b + 56i + 8 *)
Definition rce_o_regs : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms
   15 (SOff 33 0)) 14 (SLit 1)) 20 (SOff 36 0)) 23 (SOff 32 0)) 19 (SOff 37 8)) 26 (SOff 37 8))
   9 (SOff 38 8)) 25 (SOff 38 8).
Definition rce_slotA : YP09.region := YP09.mkRegion (Some 37%nat) 0 8 0 0
  [YP09.mkChunk 0 (CVal 4 (SOff 39 0)); YP09.mkChunk 4 (CVal 4 (SOff 41 0))].
Definition rce_slotB : YP09.region := YP09.mkRegion (Some 38%nat) 0 8 0 0
  [YP09.mkChunk 0 (CVal 4 (SOff 40 0)); YP09.mkChunk 4 (CVal 4 (SOff 42 0))].
Definition rce_o_facts : facts := mkFacts
  [(2%nat, rce_spF); (32%nat, rce_SBF); (37%nat, rce_PTRF); (38%nat, rce_PTRF); (41%nat, rce_NF); (42%nat, rce_NF)] []
  [(SAlu ALU_ADD (SOff 33 0) (SMd M_MUL (SOff 36 0) (SLit 56)), SOff 37 0);
   (SAlu ALU_ADD (SOff 34 0) (SMd M_MUL (SOff 36 0) (SLit 56)), SOff 38 0)].
Definition rce_o_SH : list shent := [mkSHE 37 0 56; mkSHE 38 0 56].
Definition rce_ss_outer : sstate := mkSS RCE_OH rce_o_regs [rce_fstack] None rce_o_facts.
(* inner head: s5 = 8k, s2 = 8 * nargs, s6 = ~(a + 56i + 8), s0 = ~(b + 56i + 8), s8 = 1, s11 = a *)
Definition rce_i_regs : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms
   20 (SOff 36 0)) 23 (SOff 32 0)) 19 (SOff 37 8)) 26 (SOff 37 8)) 9 (SOff 38 8)) 25 (SOff 38 8))
   21 (SOff 45 0)) 18 (SOff 46 0)) 22 (SOff 41 0)) 8 (SOff 42 0)) 24 (SLit 1)) 27 (SOff 33 0).
Definition rce_argA : YP09.region := YP09.mkRegion (Some 43%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 39 0))].
Definition rce_argB : YP09.region := YP09.mkRegion (Some 44%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 40 0))].
Definition rce_i_facts : facts := mkFacts
  [(2%nat, rce_spF); (32%nat, rce_SBF); (43%nat, rce_PTRF); (44%nat, rce_PTRF)] []
  [(SAlu ALU_ADD (SOff 37 8) (SOff 45 0), SOff 43 0); (SAlu ALU_ADD (SOff 38 8) (SOff 45 0), SOff 44 0)].
Definition rce_i_SH : list shent := [mkSHE 43 0 8; mkSHE 44 0 8].
Definition rce_ss_inner : sstate := mkSS RCE_IH rce_i_regs [rce_argA] None rce_i_facts.
(* outer latch: s8 = 1 and s11 = a, which the latch moves back to a4 and a5 *)
Definition rce_l_regs : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms
   20 (SOff 36 0)) 23 (SOff 32 0)) 19 (SOff 37 8)) 26 (SOff 37 8)) 9 (SOff 38 8)) 25 (SOff 38 8))
   24 (SLit 1)) 27 (SOff 33 0).
Definition rce_ss_latch : sstate := mkSS RCE_LT rce_l_regs [rce_fstack] None (mkFacts [(2%nat, rce_spF); (32%nat, rce_SBF)] [] []).
Definition rce_ss_entry : sstate := mkSS AF_rec_calls_equal sr_atoms [stack_region 144; got_regionP; bcell_regionP 32] None
  (mkFacts [(2%nat, rce_spF); (32%nat, rce_SBF)] [] []).
(* swap the one table region of a state *)
Definition rce_swap (r : YP09.region) (ss : sstate) : sstate := mkSS (ss_pc ss) (ss_regs ss) [r] (ss_resv ss) (ss_facts ss).
Lemma rce_swap_ok : forall E ss ms r,
st_ok_pi SEGS VAL E ss ms -> region_wf r = true -> region_ok SEGS E (ms_mem ms) r ->
st_ok_pi SEGS VAL E (rce_swap r ss) ms.
Proof.
intros E ss ms r HS Hwf Hr.
pose proof (st_ok_pi_submem E ss ms [] HS (submem_nil _) eq_refl) as HS0.
pose proof (st_ok_pi_add_region E _ ms r HS0 Hwf Hr I) as HS1. exact HS1.
Qed.

Section e.
Variable B : asyms.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis ASTRCMP : forall fx0 : YK11.FPState, @astrcmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcmp).
Hypothesis TL : PALib B.
Hypothesis HB : CmdBSyms B.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let cmd_heap_tail_vis : forall ly S (W : world SEGS) mem md p n e, AR SEGS B ly S W mem md ->
  In (p, n) (ablocks B ly S) -> p <= e < p + req_size n -> atail_vis SEGS W mem e :=
  cmd_heap_tail_vis SEGS B LAWS HB.
Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).

Ltac rce_regs_ok EE eqs :=
  apply regs_ok_by_cases; intros rr Hrr; cbv [all_regs In] in Hrr;
  repeat (destruct Hrr as [<- | Hrr];
    [ lazymatch goal with |- getr _ _ = sv_denot _ (sr_get ?a0 ?rr2) =>
        let v := eval vm_compute in (sr_get a0 rr2) in change (sr_get a0 rr2) with v end;
      cbn [sv_denot];
      first [ reflexivity
            | rewrite Z.add_0_r, Z_to_bv_bv_unsigned; symmetry; apply EE; reflexivity
            | rewrite ?Z.add_0_r; eqs; assumption ]
    | ]); try (destruct Hrr).
Ltac rce_md :=
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?md2 _ |- _ =>
    lazymatch md2 with with_vm_backing _ _ _ => let m := fresh "mdv" in set (m := md2) in *; clearbody m | _ => idtac end end.
Ltac rce_keep_empty HFr K lo hi :=
  lazymatch type of HFr with frame_of _ _ (mrestrict ?H ?m1) (mrestrict ?H ?m2) =>
  assert (K : kept_out (aview SEGS H m1) (aview SEGS H m2) lo hi)
  by (intros x0 Hx0 Hn0; apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr);
      [ intros b0 wlo whi a0 Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|]); destruct Hin
      | exact Hx0 | tauto ]) end.

(* a table's home: g_rec's call table, record.spill or a side-stack object; its bytes lie below the stack and its
   shadow says usable *)
Lemma rce_home_facts : forall ly S W mem md t n,
AR SEGS B ly S W mem md -> rce_home B ly S W mem t n -> 0 < n ->
4096 <= t /\ t + n <= alloc_ceiling /\ range_addressable (rdW W mem) SHADOW_OFF t n /\
(forall x, t <= x < t + n -> ~ (SB <= x < SB + 2 ^ 44)).
Proof.
intros ly S W mem md t n HAR Hh Hn. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HZ : forall r a0 n0, In r Tfib_zero_shadow -> fst r mod 8 = 0 -> snd r mod 8 = 0 -> fst r <= a0 -> a0 + n0 <= fst r + snd r ->
  range_addressable (rdW W mem) SHADOW_OFF a0 n0).
{ intros r a0 n0 Hr H0 H1 H2 H3. exact (cmd_addressable_in SEGS B LAWS HB ly S W mem md r a0 n0 HAR Hr H0 H1 H2 H3). }
destruct Hh as [Hg | [Hs | ((cid & pos & Hfin & Hcid & Hfal & Hf1 & Hf2) & Hp8 & Hra)]].
- unfold A_G_REC, OFF_CALLS, REC_SIZE in Hg. split; [lia|]. split; [lia|].
  split; [apply (HZ (0xad560, 0x5e3680 - 0xad560)); [vm_compute; repeat first [left; reflexivity | right] | reflexivity | reflexivity | cbn; lia | cbn; lia]|].
  intros x Hx. unfold SB. lia.
- unfold A_REC_SPILL, SC_SIZE in Hs. split; [lia|]. split; [lia|].
  split; [apply (HZ (0x5e3760, 0x5e3798 - 0x5e3760)); [vm_compute; repeat first [left; reflexivity | right] | reflexivity | reflexivity | cbn; lia | cbn; lia]|].
  intros x Hx. unfold SB. lia.
- destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Hfapp).
  split; [lia|]. split; [lia|]. split; [exact Hra|].
  intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB in *. lia.
Qed.


(* ---------- one call of rec_calls_equal ---------- *)
Section w.
Variables (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (a b : Z) (ca cb : list PRce.rc_entry).
Hypothesis HPRE : afn_pre_na SEGS B REC_CALLS_EQUAL_STK ly S W regs mem md.
Hypothesis HROD : arodata_okP SEGS RLO RHI B (rdW W mem).
Hypothesis H10 : getr regs 10 = w64 a.
Hypothesis H11 : getr regs 11 = w64 (Z.of_nat (length ca)).
Hypothesis H12 : getr regs 12 = w64 b.
Hypothesis H13 : getr regs 13 = w64 (Z.of_nat (length cb)).
Hypothesis HCA : rce_calls B ly S W mem a ca.
Hypothesis HCB : rce_calls B ly S W mem b cb.

Definition rce_Q : world SEGS -> config -> Prop :=
apost_base SEGS B REC_CALLS_EQUAL_STK [] regs ly S W mem md EV_REC_CALLS_EQUAL
(fun ly' S' W' regs' mem' md' =>
 getr regs' 10 = w64 (if PRce.calls_eqb ca cb then 1 else 0) /\
 Permutation (ablocks B ly' S') (ablocks B ly S) /\ ly' = ly /\ S' = S).
(* the saved registers in the frame *)
Definition rce_frame (rd : reader) : Prop :=
forall j r, nth_error rce_saved j = Some r ->
aval_mem rd (spZ regs - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).
(* a cut point: the journal from the entry, the memory below the stack window unchanged, the frame, sp, gp, tp *)
Definition rce_cut (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
ajournal SEGS B REC_CALLS_EQUAL_STK (spZ regs) [] ly S W mem md [] ly S W mem1 md1 0 /\
kept_out (rdW W mem) (rdW W mem1) (spZ regs - REC_CALLS_EQUAL_STK) (spZ regs) /\
rce_frame (rdW W mem1) /\
getr regs1 2 = w64 (spZ regs - 144) /\ getr regs1 3 = getr regs 3 /\ getr regs1 4 = getr regs 4.
(* the frame slots of the loop: 0(sp) = n, 8(sp) = 16(sp) = 24(sp) = 1 (the UBSan predicates), 32(sp) = b *)
Definition rce_slots (rd : reader) : Prop :=
aval_mem rd (spZ regs - 144) 8 (Z.of_nat (length ca)) /\ aval_mem rd (spZ regs - 136) 8 1 /\
aval_mem rd (spZ regs - 128) 8 1 /\ aval_mem rd (spZ regs - 120) 8 1 /\ aval_mem rd (spZ regs - 112) 8 b.

Lemma rce_sp : spZ regs mod 16 = 0 /\ alloc_ceiling + REC_CALLS_EQUAL_STK <= spZ regs /\ spZ regs <= 2 ^ 47.
Proof.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2). lia.
Qed.

(* ---------- the epilogue: 0x8a124 .. 0x8a15c, ra and s0..s11 restored, ret ---------- *)
Definition rce_e_extra : list word := map (fun r => getr regs (Z_to_bv 5 r)) rce_saved.
Lemma rce_e_nth : forall j r, nth_error rce_saved j = Some r -> nth j rce_e_extra (Z_to_bv 64 0) = getr regs (Z_to_bv 5 r).
Proof. intros j r H. unfold rce_e_extra. apply nth_error_nth. rewrite (map_nth_error (fun r0 => getr regs (Z_to_bv 5 r0)) j rce_saved H). reflexivity. Qed.
Lemma rce_epi_seed : forall regs1 mem1, getr regs1 2 = w64 (spZ regs - 144) -> rce_frame (rdW W mem1) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 rce_e_extra)) rce_ss_epi
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + RCE_EPI)) mem1 (seg_rom SEGS)))
/\ sh_ok SEGS rce_Bx [] (Eimg (Ereg regs1 rce_e_extra)) (mrestrict (w_H W) mem1).
Proof.
intros regs1 mem1 R2 HFR. pose proof rce_sp as (Hal16 & Hlo & Hhi).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HST : REC_CALLS_EQUAL_STK = 8336) by reflexivity.
set (E := Eimg (Ereg regs1 rce_e_extra)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 144).
{ subst E. rewrite (ew_Eimg_Ereg_nat regs1 _ 2 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
split; [|apply Forall_nil].
rewrite restrict_mkst_fx. unfold rce_ss_epi. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok, rce_estack.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (j & <- & Hj). apply in_seq in Hj.
  destruct (nth_error rce_saved j) as [r|] eqn:Hr; [| apply nth_error_None in Hr; cbn in Hr; lia].
  pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HRr. change (bv_modulus 64) with (2 ^ 64) in HRr.
  apply (chunk_ok_val SEGS E _ (spZ regs - 144) (136 - 8 * Z.of_nat j) 8 (SOff (32 + j) 0) (bv_unsigned (getr regs (Z_to_bv 5 r)))).
  + cbn [sv_denot]. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra, (rce_e_nth j r Hr).
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact HRr.
  + cbn. lia.
  + replace (spZ regs - 144 + (136 - 8 * Z.of_nat j)) with (spZ regs - 8 - 8 * Z.of_nat j) by lia.
    apply rce_val_mem_of_aval. exact (HFR j r Hr).
- cbn. tauto.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|exact I]. unfold afact_ok, rce_spF. cbn [af_lo af_hi af_al2]. rewrite Usp.
  change (2 ^ 4) with 16. split; [lia|]. split; [|lia]. rewrite Zminus_mod, Hal16. reflexivity.
Qed.
Lemma rce_epi : forall v regs1 mem1 md1, rce_cut regs1 mem1 md1 -> getr regs1 10 = w64 v ->
v = (if PRce.calls_eqb ca cb then 1 else 0) ->
SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + RCE_EPI)) mem1 (seg_rom SEGS)) md1) rce_Q.
Proof.
intros v regs1 mem1 md1 (HJ & HK & HFR & R2 & R3 & R4) R10 Hv.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & HQT).
pose proof rce_sp as (Hal16 & Hlo & Hhi).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HST : REC_CALLS_EQUAL_STK = 8336) by reflexivity.
destruct (rce_epi_seed regs1 mem1 R2 HFR) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs1 rce_e_extra))) by apply Eimg_env.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (Eimg (Ereg regs1 rce_e_extra)) n = getr regs1 r)
  by (intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j r, nth_error rce_saved j = Some r -> ew (Eimg (Ereg regs1 rce_e_extra)) (32 + j) = getr regs (Z_to_bv 5 r)).
{ intros j r Hr. assert (Hj : (j < 13)%nat) by (change 13%nat with (length rce_saved); apply (proj1 (nth_error_Some rce_saved j)); rewrite Hr; discriminate).
  rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra. exact (rce_e_nth j r Hr). }
assert (Usp : bv_unsigned (ew (Eimg (Ereg regs1 rce_e_extra)) 2) = spZ regs - 144).
{ rewrite (EE 2%nat 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
pose proof (EX 0%nat 1 eq_refl) as E32. pose proof (EX 1%nat 8 eq_refl) as E33. pose proof (EX 2%nat 9 eq_refl) as E34.
pose proof (EX 3%nat 18 eq_refl) as E35. pose proof (EX 4%nat 19 eq_refl) as E36. pose proof (EX 5%nat 20 eq_refl) as E37.
pose proof (EX 6%nat 21 eq_refl) as E38. pose proof (EX 7%nat 22 eq_refl) as E39. pose proof (EX 8%nat 23 eq_refl) as E40.
pose proof (EX 9%nat 24 eq_refl) as E41. pose proof (EX 10%nat 25 eq_refl) as E42. pose proof (EX 11%nat 26 eq_refl) as E43.
pose proof (EX 12%nat 27 eq_refl) as E44.
cbn [Nat.add] in E32, E33, E34, E35, E36, E37, E38, E39, E40, E41, E42, E43, E44.
pose proof (EE 3%nat 3%bv eq_refl) as E3. pose proof (EE 4%nat 4%bv eq_refl) as E4. pose proof (EE 10%nat 10%bv eq_refl) as E10.
clear EX.
remember (Eimg (Ereg regs1 rce_e_extra)) as E eqn:HE. clear HE.
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; exact Usp. }
rce_md.
prreg HS (1%bv : bv 5) F1. prreg HS (10%bv : bv 5) F10.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold rce_Q, apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly, S, r, m, d end.
split.
{ rewrite F1, E32. change (getr regs (Z_to_bv 5 1)) with (getr regs 1). unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split.
{ apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ. }
split.
{ unfold aregs_preserved. intros r Hr.
  assert (Hcases : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
    r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (unfold acallee_saved in Hr; lia).
  clear Hr.
  repeat (destruct Hcases as [-> | Hcases]); [..| subst r];
  rewrite (st_ok_pi_restrict_reg (w_H W) E _ _ _ HS); cbn [ms_regs];
  lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
  cbn [sv_denot];
  first
  [ rewrite Usp; replace (spZ regs - 144 + 144) with (spZ regs) by lia; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity
  | rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
    first [ rewrite E3, R3; reflexivity | rewrite E4, R4; reflexivity
          | rewrite E33; reflexivity | rewrite E34; reflexivity | rewrite E35; reflexivity | rewrite E36; reflexivity
          | rewrite E37; reflexivity | rewrite E38; reflexivity | rewrite E39; reflexivity | rewrite E40; reflexivity
          | rewrite E41; reflexivity | rewrite E42; reflexivity | rewrite E43; reflexivity | rewrite E44; reflexivity ] ]. }
split; [|split; [apply Permutation_refl | split; reflexivity]].
rewrite F10, E10, R10, Hv. reflexivity.
Qed.


(* ---------- the tables, the loop invariant ---------- *)
Lemma rce_tab : forall t cs, rce_calls B ly S W mem t cs -> (0 < length cs)%nat ->
(length cs <= 16)%nat /\ 4096 <= t /\ t + 56 * Z.of_nat (length cs) <= alloc_ceiling /\
range_addressable (rdW W mem) SHADOW_OFF t (56 * Z.of_nat (length cs)) /\
(forall x, t <= x < t + 56 * Z.of_nat (length cs) -> ~ (SB <= x < SB + 2 ^ 44)).
Proof.
intros t cs (Hl & _ & Hh & _) Hn. pose proof HPRE as (HAR & _).
destruct (rce_home_facts ly S W mem md t (CALL_SIZE * Z.of_nat (length cs)) HAR Hh ltac:(unfold CALL_SIZE; lia))
  as (H1 & H2 & H3 & H4).
unfold CALL_SIZE in *. auto.
Qed.
Definition rce_pre (i : nat) : Prop :=
forall j e f, (j < i)%nat -> nth_error ca j = Some e -> nth_error cb j = Some f -> rce_slot_eq e f.
Definition rce_loop (i : nat) (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
rce_cut regs1 mem1 md1 /\ (i < length ca)%nat /\ length cb = length ca /\ rce_pre i /\ rce_slots (rdW W mem1) /\
getr regs1 23 = w64 SB /\ getr regs1 20 = w64 (Z.of_nat i) /\
getr regs1 19 = w64 (a + 56 * Z.of_nat i + 8) /\ getr regs1 26 = w64 (a + 56 * Z.of_nat i + 8) /\
getr regs1 9 = w64 (b + 56 * Z.of_nat i + 8) /\ getr regs1 25 = w64 (b + 56 * Z.of_nat i + 8).
Definition rce_OH (i : nat) (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
rce_loop i regs1 mem1 md1 /\ getr regs1 15 = w64 a /\ getr regs1 14 = w64 1.
Definition rce_LT (i : nat) (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
rce_loop i regs1 mem1 md1 /\ rce_pre (Datatypes.S i) /\ getr regs1 24 = w64 1 /\ getr regs1 27 = w64 a.
(* a cut carried to a later state whose memory differs only in a window below the frame *)
Lemma rce_cut_kept : forall regs1 mem1 md1 regs2 mem2 md2 lo hi,
rce_cut regs1 mem1 md1 ->
ajournal SEGS B REC_CALLS_EQUAL_STK (spZ regs) [] ly S W mem md [] ly S W mem2 md2 0 ->
kept_out (rdW W mem1) (rdW W mem2) lo hi -> spZ regs - REC_CALLS_EQUAL_STK <= lo -> hi <= spZ regs - 144 ->
getr regs2 2 = getr regs1 2 -> getr regs2 3 = getr regs1 3 -> getr regs2 4 = getr regs1 4 ->
rce_cut regs2 mem2 md2.
Proof.
intros regs1 mem1 md1 regs2 mem2 md2 lo hi (HJ & HK & HFR & R2 & R3 & R4) HJ2 HK2 Hlo Hhi Q2 Q3 Q4.
pose proof rce_sp as (Hal16 & Hslo & Hshi). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HST : REC_CALLS_EQUAL_STK = 8336) by reflexivity.
split; [exact HJ2|]. split.
{ intros x Hx Hn. destruct (Z_lt_le_dec x lo) as [Hl|Hl]; [rewrite (HK2 x Hx) by lia; exact (HK x Hx Hn)|].
  destruct (Z_lt_le_dec x hi) as [Hh|Hh]; [exfalso; apply Hn; lia|]. rewrite (HK2 x Hx) by lia. exact (HK x Hx Hn). }
split.
{ intros j r Hr. assert (Hj : (j < 13)%nat) by (change 13%nat with (length rce_saved); apply (proj1 (nth_error_Some rce_saved j)); rewrite Hr; discriminate).
  apply (rce_aval_kept (rdW W mem1)); [|exact (HFR j r Hr)]. intros k Hk. apply HK2; lia. }
split; [rewrite Q2; exact R2|]. split; [rewrite Q3; exact R3 | rewrite Q4; exact R4].
Qed.
Lemma rce_aval_keep : forall rd rd' lo hi x n v, kept_out rd rd' lo hi -> aval_mem rd x n v ->
0 <= x -> (hi <= x \/ x + Z.of_nat n <= lo) -> x + Z.of_nat n < 2 ^ 64 -> aval_mem rd' x n v.
Proof. intros rd rd' lo hi x n v HK H Hx Hw Hr. apply (rce_aval_kept rd); [|exact H]. intros k Hk. apply HK; lia. Qed.
Lemma rce_slots_keep : forall rd rd' lo hi, kept_out rd rd' lo hi -> hi <= spZ regs - 144 -> rce_slots rd -> rce_slots rd'.
Proof.
intros rd rd' lo hi HK Hhi (S0 & S1 & S2 & S3 & S4). pose proof rce_sp as (Hal16 & Hslo & Hshi).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HST : REC_CALLS_EQUAL_STK = 8336) by reflexivity.
split; [apply (rce_aval_keep _ _ _ _ _ _ _ HK S0); lia|].
split; [apply (rce_aval_keep _ _ _ _ _ _ _ HK S1); lia|].
split; [apply (rce_aval_keep _ _ _ _ _ _ _ HK S2); lia|].
split; [apply (rce_aval_keep _ _ _ _ _ _ _ HK S3); lia|].
apply (rce_aval_keep _ _ _ _ _ _ _ HK S4); lia.
Qed.
(* the frame slots as the region rce_fstack of a seed whose sp is spZ regs - 144 *)
Lemma rce_fstack_ok : forall E m, bv_unsigned (ew E 2) = spZ regs - 144 ->
bv_unsigned (ew E 34) = b -> bv_unsigned (ew E 35) = Z.of_nat (length ca) -> 0 <= b < 2 ^ 64 -> (length ca <= 16)%nat ->
rce_slots (rdW W m) -> region_ok SEGS E (mrestrict (w_H W) m) rce_fstack.
Proof.
intros E m Usp E34u E35u Hb Hl (S0 & S1 & S2 & S3 & S4). pose proof rce_sp as (Hal16 & Hslo & Hshi).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HST : REC_CALLS_EQUAL_STK = 8336) by reflexivity.
unfold region_ok, rce_fstack.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; try apply Forall_nil.
- apply (chunk_ok_val SEGS E _ (spZ regs - 144) 0 8 (SOff 35 0) (Z.of_nat (length ca)));
    [cbn [sv_denot]; rewrite E35u, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
  rewrite Z.add_0_r. apply rce_val_mem_of_aval. exact S0.
- apply (chunk_ok_val SEGS E _ (spZ regs - 144) 8 8 (SLit 1) 1); [reflexivity | cbn; lia | cbn; lia |].
  replace (spZ regs - 144 + 8) with (spZ regs - 136) by lia. apply rce_val_mem_of_aval. exact S1.
- apply (chunk_ok_val SEGS E _ (spZ regs - 144) 16 8 (SLit 1) 1); [reflexivity | cbn; lia | cbn; lia |].
  replace (spZ regs - 144 + 16) with (spZ regs - 128) by lia. apply rce_val_mem_of_aval. exact S2.
- apply (chunk_ok_val SEGS E _ (spZ regs - 144) 24 8 (SLit 1) 1); [reflexivity | cbn; lia | cbn; lia |].
  replace (spZ regs - 144 + 24) with (spZ regs - 120) by lia. apply rce_val_mem_of_aval. exact S3.
- apply (chunk_ok_val SEGS E _ (spZ regs - 144) 32 8 (SOff 34 0) b);
    [cbn [sv_denot]; rewrite E34u, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
  replace (spZ regs - 144 + 32) with (spZ regs - 112) by lia. apply rce_val_mem_of_aval. exact S4.
Qed.
(* the extra words of a seed *)
Lemma rce_ex_w64 : forall regs1 (l : list Z) j, (32 + j < A_TEXT)%nat -> (j < length l)%nat ->
ew (Eimg (Ereg regs1 (map w64 l))) (32 + j) = w64 (nth j l 0).
Proof.
intros regs1 l j H1 H2. rewrite Eimg_low by exact H1. rewrite ew_Ereg_extra.
rewrite (nth_indep _ _ (w64 0)) by (rewrite length_map; exact H2). apply map_nth.
Qed.

(* ---------- the outer latch: 0x8a0b4 .. 0x8a0d4, then the outer head or 0x8a160 (a0 := 1) ---------- *)
Definition rce_l_extra (i : nat) : list word :=
map w64 [SB; a; b; Z.of_nat (length ca); Z.of_nat i; a + 56 * Z.of_nat i; b + 56 * Z.of_nat i].
Lemma rce_latch_seed : forall i regs1 mem1, (i < length ca)%nat -> length cb = length ca ->
getr regs1 2 = w64 (spZ regs - 144) -> rce_slots (rdW W mem1) ->
getr regs1 23 = w64 SB -> getr regs1 20 = w64 (Z.of_nat i) ->
getr regs1 19 = w64 (a + 56 * Z.of_nat i + 8) -> getr regs1 26 = w64 (a + 56 * Z.of_nat i + 8) ->
getr regs1 9 = w64 (b + 56 * Z.of_nat i + 8) -> getr regs1 25 = w64 (b + 56 * Z.of_nat i + 8) ->
getr regs1 24 = w64 1 -> getr regs1 27 = w64 a ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (rce_l_extra i))) rce_ss_latch
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + RCE_LT)) mem1 (seg_rom SEGS)))
/\ sh_ok SEGS rce_Bx [] (Eimg (Ereg regs1 (rce_l_extra i))) (mrestrict (w_H W) mem1).
Proof.
intros i regs1 mem1 Hi Hlen R2 SLT R23 R20 R19 R26 R9 R25 R24 R27.
pose proof rce_sp as (Hal16 & Hslo & Hshi). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HST : REC_CALLS_EQUAL_STK = 8336) by reflexivity.
destruct (rce_tab a ca HCA ltac:(lia)) as (Hca16 & Ha4 & Hah & _).
destruct (rce_tab b cb HCB ltac:(lia)) as (_ & Hb4 & Hbh & _). rewrite Hlen in Hbh.
set (E := Eimg (Ereg regs1 (rce_l_extra i))).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) by (intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 144) by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (EX : forall j v, nth_error [SB; a; b; Z.of_nat (length ca); Z.of_nat i; a + 56 * Z.of_nat i; b + 56 * Z.of_nat i] j = Some v ->
  ew E (32 + j) = w64 v).
{ intros j v Hj. assert (Hj7 : (j < 7)%nat) by (change 7%nat with (length [SB; a; b; Z.of_nat (length ca); Z.of_nat i; a + 56 * Z.of_nat i; b + 56 * Z.of_nat i]); apply (proj1 (nth_error_Some _ j)); rewrite Hj; discriminate).
  subst E. unfold rce_l_extra. rewrite rce_ex_w64 by (cbn; unfold A_TEXT; lia). f_equal. apply nth_error_nth. exact Hj. }
pose proof (EX 0%nat _ eq_refl) as E32. pose proof (EX 1%nat _ eq_refl) as E33. pose proof (EX 2%nat _ eq_refl) as E34.
pose proof (EX 3%nat _ eq_refl) as E35. pose proof (EX 4%nat _ eq_refl) as E36. pose proof (EX 5%nat _ eq_refl) as E37.
pose proof (EX 6%nat _ eq_refl) as E38.
cbn [Nat.add] in E32, E33, E34, E35, E36, E37, E38. clear EX.
assert (E32u : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (E33u : bv_unsigned (ew E 33) = a) by (rewrite E33; apply unsigned_lit_small; lia).
assert (E34u : bv_unsigned (ew E 34) = b) by (rewrite E34; apply unsigned_lit_small; lia).
assert (E35u : bv_unsigned (ew E 35) = Z.of_nat (length ca)) by (rewrite E35; apply unsigned_lit_small; lia).
assert (E36u : bv_unsigned (ew E 36) = Z.of_nat i) by (rewrite E36; apply unsigned_lit_small; lia).
assert (E37u : bv_unsigned (ew E 37) = a + 56 * Z.of_nat i) by (rewrite E37; apply unsigned_lit_small; lia).
assert (E38u : bv_unsigned (ew E 38) = b + 56 * Z.of_nat i) by (rewrite E38; apply unsigned_lit_small; lia).
split; [|apply Forall_nil].
rewrite restrict_mkst_fx. unfold rce_ss_latch. apply pa_entry_st_ok_full.
- rce_regs_ok EE ltac:(rewrite ?E32u, ?E33u, ?E34u, ?E35u, ?E36u, ?E37u, ?E38u).
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. apply (rce_fstack_ok E mem1 Usp E34u E35u); [lia | lia | exact SLT].
- cbn. tauto.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok, rce_spF, rce_SBF. cbn [af_lo af_hi af_al2].
  rewrite Usp, E32u. change (2 ^ 4) with 16. rewrite Z.pow_0_r, Z.mod_1_r.
  repeat split; try lia. rewrite Zminus_mod, Hal16. reflexivity.
Qed.
Lemma rce_latch : forall i regs1 mem1 md1, rce_LT i regs1 mem1 md1 ->
((Datatypes.S i < length ca)%nat -> forall r m d, rce_OH (Datatypes.S i) r m d ->
  SRr SEGS W (mkCfg (mkst r (Z_to_bv 64 (BASE + RCE_OH)) m (seg_rom SEGS)) d) rce_Q) ->
SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + RCE_LT)) mem1 (seg_rom SEGS)) md1) rce_Q.
Proof.
intros i regs1 mem1 md1 ((HCUT & Hi & Hlen & Hpre & SLT & R23 & R20 & R19 & R26 & R9 & R25) & Hpre1 & R24 & R27) IH.
pose proof HCUT as (HJ & HK & HFR & R2 & R3 & R4).
pose proof rce_sp as (Hal16 & Hslo & Hshi). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HST : REC_CALLS_EQUAL_STK = 8336) by reflexivity.
destruct (rce_tab a ca HCA ltac:(lia)) as (Hca16 & Ha4 & Hah & _).
destruct (rce_tab b cb HCB ltac:(lia)) as (_ & Hb4 & Hbh & _). rewrite Hlen in Hbh.
destruct (rce_latch_seed i regs1 mem1 Hi Hlen R2 SLT R23 R20 R19 R26 R9 R25 R24 R27) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs1 (rce_l_extra i)))) by apply Eimg_env.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (Eimg (Ereg regs1 (rce_l_extra i))) n = getr regs1 r)
  by (intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
assert (Usp : bv_unsigned (ew (Eimg (Ereg regs1 (rce_l_extra i))) 2) = spZ regs - 144)
  by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (EX : forall j v, nth_error [SB; a; b; Z.of_nat (length ca); Z.of_nat i; a + 56 * Z.of_nat i; b + 56 * Z.of_nat i] j = Some v ->
  ew (Eimg (Ereg regs1 (rce_l_extra i))) (32 + j) = w64 v).
{ intros j v Hj. assert (Hj7 : (j < 7)%nat) by (change 7%nat with (length [SB; a; b; Z.of_nat (length ca); Z.of_nat i; a + 56 * Z.of_nat i; b + 56 * Z.of_nat i]); apply (proj1 (nth_error_Some _ j)); rewrite Hj; discriminate).
  unfold rce_l_extra. rewrite rce_ex_w64 by (cbn; unfold A_TEXT; lia). f_equal. apply nth_error_nth. exact Hj. }
pose proof (EX 0%nat _ eq_refl) as E32. pose proof (EX 1%nat _ eq_refl) as E33. pose proof (EX 2%nat _ eq_refl) as E34.
pose proof (EX 3%nat _ eq_refl) as E35. pose proof (EX 4%nat _ eq_refl) as E36. pose proof (EX 5%nat _ eq_refl) as E37.
pose proof (EX 6%nat _ eq_refl) as E38.
cbn [Nat.add] in E32, E33, E34, E35, E36, E37, E38. clear EX.
pose proof (EE 3%nat 3%bv eq_refl) as E3. pose proof (EE 4%nat 4%bv eq_refl) as E4.
remember (Eimg (Ereg regs1 (rce_l_extra i))) as E eqn:HE. clear HE.
assert (E32u : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (E33u : bv_unsigned (ew E 33) = a) by (rewrite E33; apply unsigned_lit_small; lia).
assert (E34u : bv_unsigned (ew E 34) = b) by (rewrite E34; apply unsigned_lit_small; lia).
assert (E35u : bv_unsigned (ew E 35) = Z.of_nat (length ca)) by (rewrite E35; apply unsigned_lit_small; lia).
assert (E36u : bv_unsigned (ew E 36) = Z.of_nat i) by (rewrite E36; apply unsigned_lit_small; lia).
assert (E37u : bv_unsigned (ew E 37) = a + 56 * Z.of_nat i) by (rewrite E37; apply unsigned_lit_small; lia).
assert (E38u : bv_unsigned (ew E 38) = b + 56 * Z.of_nat i) by (rewrite E38; apply unsigned_lit_small; lia).
(* 0x8a0b4 .. 0x8a0d4: i + 1, the four cursors + 56, n reloaded, a4/a5 from s8/s11, bne s4,a1 *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; exact Usp. }
rce_md.
rce_keep_empty HFr KEEP1 (spZ regs - REC_CALLS_EQUAL_STK) (spZ regs - 144). clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* i + 1 <> N: back to the outer head *)
  assert (HiN : (Datatypes.S i <> length ca)%nat).
  { rewrite branch_ne_U, !U_SOff, E36u, E35u in Hc. rewrite !zcanon_small in Hc by lia.
    apply negb_true_iff, Z.eqb_neq in Hc. lia. }
  paj_run_to_tok RUNTO HS HJ SHOK Bspan RCE_OH.
  { awr_ok_tac; exact Usp. }
  rce_md.
  rce_keep_empty HFr KEEP2 (spZ regs - REC_CALLS_EQUAL_STK) (spZ regs - 144). clear HF HFr HG.
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (9%bv : bv 5) P9.
  prreg HS (14%bv : bv 5) P14. prreg HS (15%bv : bv 5) P15. prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20.
  prreg HS (23%bv : bv 5) P23. prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mT _) _) _ =>
  assert (KEEP : kept_out (rdW W mem1) (rdW W mT) (spZ regs - REC_CALLS_EQUAL_STK) (spZ regs - 144))
    by (apply (kept_out_trans _ _ _ _ _ _ _ KEEP1 KEEP2); lia) end.
  apply IH; [lia|]. split; [split|].
  + apply (rce_cut_kept regs1 mem1 md1 _ _ _ _ _ HCUT HJ KEEP); [lia | lia | rewrite P2, (EE 2%nat 2%bv eq_refl); reflexivity
    | rewrite P3, E3; reflexivity | rewrite P4, E4; reflexivity].
  + split; [lia|]. split; [exact Hlen|].
    split; [exact Hpre1|].
    split; [apply (rce_slots_keep _ _ _ _ KEEP); [lia | exact SLT]|].
    split; [rewrite P23, E32; reflexivity|].
    split; [rewrite P20, E36u; unfold w64; f_equal; lia|].
    split; [rewrite P19, E37u; unfold w64; f_equal; lia|].
    split; [rewrite P26, E37u; unfold w64; f_equal; lia|].
    split; [rewrite P9, E38u; unfold w64; f_equal; lia|].
    rewrite P25, E38u; unfold w64; f_equal; lia.
  + split; [rewrite P15, E33; reflexivity|]. rewrite P14. reflexivity.
- (* i + 1 = N: every slot matched; 0x8a0d8 jumps to 0x8a160, a0 := 1 *)
  assert (HiN : Datatypes.S i = length ca).
  { rewrite branch_ne_U, !U_SOff, E36u, E35u in Hc. rewrite !zcanon_small in Hc by lia.
    apply negb_false_iff, Z.eqb_eq in Hc. lia. }
  paj_run_to_tok RUNTO HS HJ SHOK Bspan RCE_EPI.
  { awr_ok_tac; exact Usp. }
  rce_md.
  rce_keep_empty HFr KEEP2 (spZ regs - REC_CALLS_EQUAL_STK) (spZ regs - 144). clear HF HFr HG.
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (10%bv : bv 5) P10.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mT _) _) _ =>
  assert (KEEP : kept_out (rdW W mem1) (rdW W mT) (spZ regs - REC_CALLS_EQUAL_STK) (spZ regs - 144))
    by (apply (kept_out_trans _ _ _ _ _ _ _ KEEP1 KEEP2); lia) end.
  apply (rce_epi 1).
  + apply (rce_cut_kept regs1 mem1 md1 _ _ _ _ _ HCUT HJ KEEP); [lia | lia | rewrite P2, (EE 2%nat 2%bv eq_refl); reflexivity
    | rewrite P3, E3; reflexivity | rewrite P4, E4; reflexivity].
  + rewrite P10. reflexivity.
  + rewrite rce_calls_eqb_true; [reflexivity | lia |]. intros j e f Hj1 Hj2.
    apply (Hpre1 j e f); [|exact Hj1 | exact Hj2]. rewrite HiN. apply (proj1 (nth_error_Some ca j)). rewrite Hj1. discriminate.
Qed.


(* ---------- a string argument at the strcmp call ---------- *)
Lemma rce_str_call : forall x s regsc memc,
in_blockA (ablocks B ly S) x (Z.of_nat (length s) + 1) /\ astr_atR (rdW W mem) x s ->
kept_out (rdW W mem) (rdW W memc) (spZ regs - REC_CALLS_EQUAL_STK) (spZ regs) ->
spZ regsc = spZ regs - 144 ->
0 < x /\ astr_at SEGS W memc x s /\ aread_ok SEGS (2 * ESTACK) W regsc memc x (astr_len s + 1) /\
atail_vis SEGS W memc (x + astr_len s).
Proof.
intros x s regsc memc HA HK Hsp.
pose proof HPRE as (HAR & _). pose proof rce_sp as (Hal16 & Hslo & Hshi).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HST : REC_CALLS_EQUAL_STK = 8336) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity. pose proof alloc_ceiling_value as [_ HAC].
destruct HA as ((p & k & Hpk & Hp1 & Hp2) & Hstr).
destruct (al_blocks _ _ LAWS ly S W mem md p k HAR Hpk) as (Hp16 & Hp4096 & Hpceil & Hpapp & Hppres & _ & Hkr).
pose proof (req_size_pos k ltac:(lia)) as [_ Hreq].
split; [lia|]. split.
{ apply (astr_atR_view SEGS). apply (astr_atR_kept _ _ _ _ x s HK Hstr); lia. }
split.
{ unfold astr_len.
  apply (aread_ok_kept SEGS 0 (2 * ESTACK) W regs regsc mem memc (spZ regs - REC_CALLS_EQUAL_STK) (spZ regs) x _ HK);
    [| lia | lia | lia | rewrite Hsp, Hes; lia | lia].
  apply (aread_ok_of_block SEGS B LAWS 0 ly S W regs mem md p k x _ HAR Hpk Hp1); lia. }
{ assert (Hxe : 0 <= x + astr_len s < alloc_ceiling) by (unfold astr_len; lia).
  pose proof (tail_below _ _ Hxe HAC) as HTB.
  apply (atail_vis_kept SEGS W mem memc _ _ _ HK); [| unfold astr_len; lia | lia | lia].
  apply (cmd_heap_tail_vis ly S W mem md p k); [exact HAR | exact Hpk | unfold astr_len; lia]. }
Qed.
(* the image bytes a runtime entry reads, at a state whose low memory is the entry's *)
Lemma rce_rom_at : forall memc, kept_out (rdW W mem) (rdW W memc) (spZ regs - REC_CALLS_EQUAL_STK) (spZ regs) ->
rt_rom_view SEGS B W memc.
Proof.
intros memc HK x Hx Ho He. pose proof rce_sp as (Hal16 & Hslo & Hshi).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HST : REC_CALLS_EQUAL_STK = 8336) by reflexivity.
destruct Hx as (sg & Hsg & Hw & Hr).
assert (Himg : in_img SEGS x) by (exists sg; split; [exact Hsg | exact Hr]).
pose proof (pa_img_range _ Himg) as HR. rewrite (HK x) by lia.
apply HROD; [left; exists sg; split; [exact Hsg | split; [exact Hw | exact Hr]] | exact Ho | exact He].
Qed.
(* one table slot's fields and argument words, at the entry *)
Lemma rce_slot : forall t cs i e, rce_calls B ly S W mem t cs -> nth_error cs i = Some e ->
-2^31 <= fst e < 2^31 /\ (length (snd e) <= 6)%nat /\
aval_mem (rdW W mem) (t + 56 * Z.of_nat i) 4 (fst e) /\
aval_mem (rdW W mem) (t + 56 * Z.of_nat i + 4) 4 (Z.of_nat (length (snd e))) /\
forall k p, nth_error (snd e) k = Some p ->
  aval_mem (rdW W mem) (t + 56 * Z.of_nat i + 8 + 8 * Z.of_nat k) 8 (bv_unsigned (fst p)) /\
  in_blockA (ablocks B ly S) (bv_unsigned (fst p)) (Z.of_nat (length (snd p)) + 1) /\
  astr_atR (rdW W mem) (bv_unsigned (fst p)) (snd p).
Proof.
intros t cs i e (_ & _ & _ & H) Hi. destruct (H i e Hi) as (H1 & H2 & H3 & H4 & H5).
unfold CALL_SIZE, CALL_OFF_FN, CALL_OFF_NARGS, CALL_OFF_ARGS in *. rewrite Z.add_0_r in H3.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. exact H5.
Qed.
(* the shadow of a range the walk's checks read *)
Lemma rce_shent_ok : forall E m n x lo hi, ew E 32 = w64 SB -> bv_unsigned (ew E n) = x -> 0 <= x + lo -> x + hi < 2 ^ 64 -> lo <= hi ->
range_addressable (rd_of SEGS m) SHADOW_OFF (x + lo) (hi - lo) ->
(forall y, x + lo <= y < x + hi -> ~ (SB <= y < SB + 2 ^ 44)) ->
shent_ok SEGS rce_Bx E m (mkSHE n lo hi).
Proof.
intros E m n x lo hi H32 Hn H0 H1 Hlh Hra Hband. unfold shent_ok, app_apart, rce_Bx. cbn [she_m she_lo she_hi].
assert (U32 : U E (SOff 32 0) = SB).
{ rewrite U_SOff, H32, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). apply zcanon_small. unfold SB; lia. }
assert (Hxr : 0 <= x < 2 ^ 64) by (rewrite <- Hn; pose proof (bv_unsigned_in_range 64 (ew E n)) as HR; change (bv_modulus 64) with (2 ^ 64) in HR; exact HR).
assert (Un : U E (SOff n 0) = x) by (rewrite U_SOff, Hn, Z.add_0_r; apply zcanon_small; exact Hxr).
rewrite U32, Un. split; [exact Hra|].
intros y Hy. rewrite Z.min_l, Z.max_r in Hy by lia. apply Hband. lia.
Qed.

(* ---------- the inner loop: 0x8a064 .. 0x8a0b0, the strcmp call at 0x8a0a4 ---------- *)
Definition rce_i_extra (i k : nat) (xa xb nn : Z) : list word :=
map w64 [SB; a; b; Z.of_nat (length ca); Z.of_nat i; a + 56 * Z.of_nat i; b + 56 * Z.of_nat i; xa; xb;
  2 ^ 64 - 1 - (a + 56 * Z.of_nat i + 8); 2 ^ 64 - 1 - (b + 56 * Z.of_nat i + 8);
  a + 56 * Z.of_nat i + 8 + 8 * Z.of_nat k; b + 56 * Z.of_nat i + 8 + 8 * Z.of_nat k; 8 * Z.of_nat k; nn].
Definition rce_IH (i k : nat) (e f : PRce.rc_entry) (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
rce_loop i regs1 mem1 md1 /\ getr regs1 24 = w64 1 /\ getr regs1 27 = w64 a /\
nth_error ca i = Some e /\ nth_error cb i = Some f /\ fst e = fst f /\
length (snd f) = length (snd e) /\ (k < length (snd e))%nat /\
(forall j p q, (j < k)%nat -> nth_error (snd e) j = Some p -> nth_error (snd f) j = Some q -> snd p = snd q) /\
getr regs1 21 = w64 (8 * Z.of_nat k) /\ getr regs1 18 = w64 (8 * Z.of_nat (length (snd e))) /\
getr regs1 22 = w64 (2 ^ 64 - 1 - (a + 56 * Z.of_nat i + 8)) /\ getr regs1 8 = w64 (2 ^ 64 - 1 - (b + 56 * Z.of_nat i + 8)).


Lemma rce_inner_seed : forall (i k : nat) xa xb nn regs1 mem1,
(i < length ca)%nat -> length cb = length ca -> 0 <= xa < 2 ^ 64 -> 0 <= xb < 2 ^ 64 -> 0 <= 8 * Z.of_nat k -> 0 <= nn <= 48 ->
4096 <= a + 56 * Z.of_nat i + 8 + 8 * Z.of_nat k -> a + 56 * Z.of_nat i + 8 + 8 * Z.of_nat k + 8 <= alloc_ceiling ->
4096 <= b + 56 * Z.of_nat i + 8 + 8 * Z.of_nat k -> b + 56 * Z.of_nat i + 8 + 8 * Z.of_nat k + 8 <= alloc_ceiling ->
getr regs1 2 = w64 (spZ regs - 144) ->
getr regs1 23 = w64 SB -> getr regs1 20 = w64 (Z.of_nat i) ->
getr regs1 19 = w64 (a + 56 * Z.of_nat i + 8) -> getr regs1 26 = w64 (a + 56 * Z.of_nat i + 8) ->
getr regs1 9 = w64 (b + 56 * Z.of_nat i + 8) -> getr regs1 25 = w64 (b + 56 * Z.of_nat i + 8) ->
getr regs1 24 = w64 1 -> getr regs1 27 = w64 a ->
getr regs1 21 = w64 (8 * Z.of_nat k) -> getr regs1 18 = w64 nn ->
getr regs1 22 = w64 (2 ^ 64 - 1 - (a + 56 * Z.of_nat i + 8)) -> getr regs1 8 = w64 (2 ^ 64 - 1 - (b + 56 * Z.of_nat i + 8)) ->
aval_mem (rdW W mem1) (a + 56 * Z.of_nat i + 8 + 8 * Z.of_nat k) 8 xa ->
range_addressable (rdW W mem1) SHADOW_OFF (a + 56 * Z.of_nat i + 8 + 8 * Z.of_nat k) 8 ->
range_addressable (rdW W mem1) SHADOW_OFF (b + 56 * Z.of_nat i + 8 + 8 * Z.of_nat k) 8 ->
(forall y, a + 56 * Z.of_nat i + 8 + 8 * Z.of_nat k <= y < a + 56 * Z.of_nat i + 8 + 8 * Z.of_nat k + 8 -> ~ (SB <= y < SB + 2 ^ 44)) ->
(forall y, b + 56 * Z.of_nat i + 8 + 8 * Z.of_nat k <= y < b + 56 * Z.of_nat i + 8 + 8 * Z.of_nat k + 8 -> ~ (SB <= y < SB + 2 ^ 44)) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (rce_i_extra i k xa xb nn))) rce_ss_inner
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + RCE_IH)) mem1 (seg_rom SEGS)))
/\ sh_ok SEGS rce_Bx rce_i_SH (Eimg (Ereg regs1 (rce_i_extra i k xa xb nn))) (mrestrict (w_H W) mem1).
Proof.
intros i k xa xb nn regs1 mem1 Hi Hlen Hxa Hxb Hk Hnn HQa1 HQa2 HQb1 HQb2 R2 R23 R20 R19 R26 R9 R25 R24 R27 R21 R18 R22 R8
  VXA RAa RAb BDa BDb.
pose proof rce_sp as (Hal16 & Hslo & Hshi). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HST : REC_CALLS_EQUAL_STK = 8336) by reflexivity.
destruct (rce_tab a ca HCA ltac:(lia)) as (Hca16 & Ha4 & Hah & _).
destruct (rce_tab b cb HCB ltac:(lia)) as (_ & Hb4 & Hbh & _). rewrite Hlen in Hbh.
set (QA := a + 56 * Z.of_nat i + 8 + 8 * Z.of_nat k) in *. set (QB := b + 56 * Z.of_nat i + 8 + 8 * Z.of_nat k) in *.
set (E := Eimg (Ereg regs1 (rce_i_extra i k xa xb nn))).
set (NA := 2 ^ 64 - 1 - (a + 56 * Z.of_nat i + 8)) in *. set (NB := 2 ^ 64 - 1 - (b + 56 * Z.of_nat i + 8)) in *.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) by (intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 144) by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (EX : forall j v, nth_error [SB; a; b; Z.of_nat (length ca); Z.of_nat i; a + 56 * Z.of_nat i; b + 56 * Z.of_nat i; xa; xb; NA; NB; QA; QB; 8 * Z.of_nat k; nn] j = Some v ->
  ew E (32 + j) = w64 v).
{ intros j v Hj. assert (Hj15 : (j < 15)%nat) by (change 15%nat with (length [SB; a; b; Z.of_nat (length ca); Z.of_nat i; a + 56 * Z.of_nat i; b + 56 * Z.of_nat i; xa; xb; NA; NB; QA; QB; 8 * Z.of_nat k; nn]); apply (proj1 (nth_error_Some _ j)); rewrite Hj; discriminate).
  subst E. unfold rce_i_extra. fold QA QB NA NB. rewrite rce_ex_w64 by (cbn; unfold A_TEXT; lia). f_equal. apply nth_error_nth. exact Hj. }
pose proof (EX 0%nat _ eq_refl) as E32. pose proof (EX 1%nat _ eq_refl) as E33. pose proof (EX 4%nat _ eq_refl) as E36.
pose proof (EX 5%nat _ eq_refl) as E37. pose proof (EX 6%nat _ eq_refl) as E38. pose proof (EX 7%nat _ eq_refl) as E39.
pose proof (EX 9%nat _ eq_refl) as E41. pose proof (EX 10%nat _ eq_refl) as E42. pose proof (EX 11%nat _ eq_refl) as E43.
pose proof (EX 12%nat _ eq_refl) as E44. pose proof (EX 13%nat _ eq_refl) as E45. pose proof (EX 14%nat _ eq_refl) as E46.
cbn [Nat.add] in E32, E33, E36, E37, E38, E39, E41, E42, E43, E44, E45, E46. clear EX.
assert (E32u : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (E33u : bv_unsigned (ew E 33) = a) by (rewrite E33; apply unsigned_lit_small; lia).
assert (E36u : bv_unsigned (ew E 36) = Z.of_nat i) by (rewrite E36; apply unsigned_lit_small; lia).
assert (E37u : bv_unsigned (ew E 37) = a + 56 * Z.of_nat i) by (rewrite E37; apply unsigned_lit_small; lia).
assert (E38u : bv_unsigned (ew E 38) = b + 56 * Z.of_nat i) by (rewrite E38; apply unsigned_lit_small; lia).
assert (E39u : bv_unsigned (ew E 39) = xa) by (rewrite E39; apply unsigned_lit_small; lia).
assert (E41u : bv_unsigned (ew E 41) = NA) by (rewrite E41; apply unsigned_lit_small; subst NA; lia).
assert (E42u : bv_unsigned (ew E 42) = NB) by (rewrite E42; apply unsigned_lit_small; subst NB; lia).
assert (E43u : bv_unsigned (ew E 43) = QA) by (rewrite E43; apply unsigned_lit_small; lia).
assert (E44u : bv_unsigned (ew E 44) = QB) by (rewrite E44; apply unsigned_lit_small; lia).
assert (E45u : bv_unsigned (ew E 45) = 8 * Z.of_nat k) by (rewrite E45; apply unsigned_lit_small; lia).
assert (E46u : bv_unsigned (ew E 46) = nn) by (rewrite E46; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold rce_ss_inner. apply pa_entry_st_ok_full.
  + rce_regs_ok EE ltac:(rewrite ?E32u, ?E33u, ?E36u, ?E37u, ?E38u, ?E41u, ?E42u, ?E45u, ?E46u).
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil]. unfold region_ok, rce_argA.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E43u.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ QA 0 8 (SOff 39 0) xa); [cbn [sv_denot]; rewrite E39u, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. apply rce_val_mem_of_aval. exact VXA.
  + cbn. tauto.
  + split; [|split; [exact I|]].
    * cbn [f_atoms atoms_ok rce_i_facts]. unfold afact_ok, rce_spF, rce_SBF, rce_PTRF. cbn [af_lo af_hi af_al2].
      rewrite Usp, E32u, E43u, E44u. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat split; try lia. rewrite Zminus_mod, Hal16. reflexivity.
    * cbn [f_alias alias_ok rce_i_facts]. split; [|split; [|exact I]].
      -- apply (rce_alias_add E 37 45 43 (a + 56 * Z.of_nat i) 8 (8 * Z.of_nat k) E37 E45); [rewrite E43; subst QA; f_equal; lia | lia..].
      -- apply (rce_alias_add E 38 45 44 (b + 56 * Z.of_nat i) 8 (8 * Z.of_nat k) E38 E45); [rewrite E44; subst QB; f_equal; lia | lia..].
- unfold sh_ok, rce_i_SH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + apply (rce_shent_ok E _ 43 QA 0 8 E32 E43u); try lia; [rewrite Z.add_0_r; exact RAa | intros y Hy; apply BDa; lia].
  + apply (rce_shent_ok E _ 44 QB 0 8 E32 E44u); try lia; [rewrite Z.add_0_r; exact RAb | intros y Hy; apply BDb; lia].
Qed.


Lemma rce_inner_step : forall i k e f regs1 mem1 md1,
(forall r m d, rce_LT i r m d -> SRr SEGS W (mkCfg (mkst r (Z_to_bv 64 (BASE + RCE_LT)) m (seg_rom SEGS)) d) rce_Q) ->
((Datatypes.S k < length (snd e))%nat -> forall r m d, rce_IH i (Datatypes.S k) e f r m d ->
  SRr SEGS W (mkCfg (mkst r (Z_to_bv 64 (BASE + RCE_IH)) m (seg_rom SEGS)) d) rce_Q) ->
rce_IH i k e f regs1 mem1 md1 ->
SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + RCE_IH)) mem1 (seg_rom SEGS)) md1) rce_Q.
Proof.
intros i k e f regs1 mem1 md1 LTK NXT
  ((HCUT & Hi & Hlen & Hpre & SLT & R23 & R20 & R19 & R26 & R9 & R25) & R24 & R27 & He & Hf & Hfn & Hnl & Hk & Hargs
   & R21 & R18 & R22 & R8).
pose proof HCUT as (HJ & HK & HFR & R2 & R3 & R4).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & HQT).
pose proof rce_sp as (Hal16 & Hslo & Hshi). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HST : REC_CALLS_EQUAL_STK = 8336) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
destruct (rce_tab a ca HCA ltac:(lia)) as (Hca16 & Ha4 & Hah & HaRA & HaBD).
destruct (rce_tab b cb HCB ltac:(lia)) as (_ & Hb4 & Hbh & HbRA & HbBD). rewrite Hlen in Hbh, HbRA, HbBD.
destruct (rce_slot a ca i e HCA He) as (Hfe & Hle & VFa & VNa & VAa).
destruct (rce_slot b cb i f HCB Hf) as (Hff & Hlf & VFb & VNb & VAb).
destruct (nth_error (snd e) k) as [pa|] eqn:Hpa; [|apply nth_error_None in Hpa; lia].
destruct (nth_error (snd f) k) as [pb|] eqn:Hpb; [|apply nth_error_None in Hpb; lia].
destruct (VAa k pa Hpa) as (VXa & SXa). destruct (VAb k pb Hpb) as (VXb & SXb). clear VAa VAb.
pose proof (bv_unsigned_in_range 64 (fst pa)) as Rxa. pose proof (bv_unsigned_in_range 64 (fst pb)) as Rxb.
change (bv_modulus 64) with (2 ^ 64) in Rxa, Rxb.
set (xa := bv_unsigned (fst pa)) in *. set (xb := bv_unsigned (fst pb)) in *.
set (nn := 8 * Z.of_nat (length (snd e))) in *.
assert (Hnn : 0 <= nn <= 48) by (subst nn; lia).
assert (HQa : 4096 <= a + 56 * Z.of_nat i + 8 + 8 * Z.of_nat k /\ a + 56 * Z.of_nat i + 8 + 8 * Z.of_nat k + 8 <= a + 56 * Z.of_nat (length ca)) by lia.
assert (HQb : 4096 <= b + 56 * Z.of_nat i + 8 + 8 * Z.of_nat k /\ b + 56 * Z.of_nat i + 8 + 8 * Z.of_nat k + 8 <= b + 56 * Z.of_nat (length ca)) by lia.
set (QA := a + 56 * Z.of_nat i + 8 + 8 * Z.of_nat k) in *. set (QB := b + 56 * Z.of_nat i + 8 + 8 * Z.of_nat k) in *.
set (NA := 2 ^ 64 - 1 - (a + 56 * Z.of_nat i + 8)) in *. set (NB := 2 ^ 64 - 1 - (b + 56 * Z.of_nat i + 8)) in *.
assert (VXa1 : aval_mem (rdW W mem1) QA 8 xa) by (apply (rce_aval_keep _ _ _ _ _ _ _ HK VXa); lia).
assert (RAa1 : range_addressable (rdW W mem1) SHADOW_OFF QA 8).
{ apply (range_addressable_kept_win (rdW W mem) (rdW W mem1) (spZ regs - REC_CALLS_EQUAL_STK) (spZ regs)); [exact HK | lia | lia | lia |].
  apply (range_addressable_sub _ _ a (56 * Z.of_nat (length ca))); [exact HaRA | lia | lia]. }
assert (RAb1 : range_addressable (rdW W mem1) SHADOW_OFF QB 8).
{ apply (range_addressable_kept_win (rdW W mem) (rdW W mem1) (spZ regs - REC_CALLS_EQUAL_STK) (spZ regs)); [exact HK | lia | lia | lia |].
  apply (range_addressable_sub _ _ b (56 * Z.of_nat (length ca))); [exact HbRA | lia | lia]. }
destruct (rce_inner_seed i k xa xb nn regs1 mem1 Hi Hlen Rxa Rxb ltac:(lia) Hnn ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
  R2 R23 R20 R19 R26 R9 R25 R24 R27 R21 R18 R22 R8 VXa1 RAa1 RAb1 ltac:(intros y Hy; apply HaBD; lia) ltac:(intros y Hy; apply HbBD; lia))
  as [HS SHOK].
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs1 (rce_i_extra i k xa xb nn)))) by apply Eimg_env.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (Eimg (Ereg regs1 (rce_i_extra i k xa xb nn))) n = getr regs1 r)
  by (intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j v, nth_error [SB; a; b; Z.of_nat (length ca); Z.of_nat i; a + 56 * Z.of_nat i; b + 56 * Z.of_nat i; xa; xb; NA; NB; QA; QB; 8 * Z.of_nat k; nn] j = Some v ->
  ew (Eimg (Ereg regs1 (rce_i_extra i k xa xb nn))) (32 + j) = w64 v).
{ intros j v Hj. assert (Hj15 : (j < 15)%nat) by (change 15%nat with (length [SB; a; b; Z.of_nat (length ca); Z.of_nat i; a + 56 * Z.of_nat i; b + 56 * Z.of_nat i; xa; xb; NA; NB; QA; QB; 8 * Z.of_nat k; nn]); apply (proj1 (nth_error_Some _ j)); rewrite Hj; discriminate).
  unfold rce_i_extra. fold QA QB NA NB. rewrite rce_ex_w64 by (cbn; unfold A_TEXT; lia). f_equal. apply nth_error_nth. exact Hj. }
pose proof (EX 0%nat _ eq_refl) as E32. pose proof (EX 1%nat _ eq_refl) as E33. pose proof (EX 4%nat _ eq_refl) as E36.
pose proof (EX 5%nat _ eq_refl) as E37. pose proof (EX 6%nat _ eq_refl) as E38. pose proof (EX 7%nat _ eq_refl) as E39.
pose proof (EX 8%nat _ eq_refl) as E40. pose proof (EX 9%nat _ eq_refl) as E41. pose proof (EX 10%nat _ eq_refl) as E42.
pose proof (EX 11%nat _ eq_refl) as E43. pose proof (EX 12%nat _ eq_refl) as E44. pose proof (EX 13%nat _ eq_refl) as E45.
pose proof (EX 14%nat _ eq_refl) as E46.
cbn [Nat.add] in E32, E33, E36, E37, E38, E39, E40, E41, E42, E43, E44, E45, E46. clear EX.
pose proof (EE 2%nat 2%bv eq_refl) as E2. pose proof (EE 3%nat 3%bv eq_refl) as E3. pose proof (EE 4%nat 4%bv eq_refl) as E4.
remember (Eimg (Ereg regs1 (rce_i_extra i k xa xb nn))) as E eqn:HE. clear HE.
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 144) by (rewrite E2, R2; apply unsigned_lit_small; lia).
assert (E36u : bv_unsigned (ew E 36) = Z.of_nat i) by (rewrite E36; apply unsigned_lit_small; lia).
assert (E37u : bv_unsigned (ew E 37) = a + 56 * Z.of_nat i) by (rewrite E37; apply unsigned_lit_small; lia).
assert (E38u : bv_unsigned (ew E 38) = b + 56 * Z.of_nat i) by (rewrite E38; apply unsigned_lit_small; lia).
assert (E40u : bv_unsigned (ew E 40) = xb) by (rewrite E40; apply unsigned_lit_small; lia).
assert (E43u : bv_unsigned (ew E 43) = QA) by (rewrite E43; apply unsigned_lit_small; lia).
assert (E44u : bv_unsigned (ew E 44) = QB) by (rewrite E44; apply unsigned_lit_small; lia).
assert (E45u : bv_unsigned (ew E 45) = 8 * Z.of_nat k) by (rewrite E45; apply unsigned_lit_small; lia).
assert (E46u : bv_unsigned (ew E 46) = nn) by (rewrite E46; apply unsigned_lit_small; lia).
(* 0x8a064: bltu s6,s5 to the unimp (UBSan, recorder.c:173): taken when a[i].args + 8k wraps, i.e. ~(a + 56i + 8) < 8k
   unsigned; a + 56i + 8 < 2 ^ 47 and 8k <= 40 *)
psrr_branch_tok RUN BR HS SHOK Bspan.
{ exfalso. rewrite branch_ltu_U, (U_atom E 41 NA), (U_atom E 45 (8 * Z.of_nat k)) in Hc by (first [exact E41 | exact E45 | subst NA; lia | lia]).
  apply Z.ltb_lt in Hc. subst NA. lia. }
clear Hc.
(* 0x8a068: bltu s0,s5 to the unimp, the same for b[i].args *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; exact Usp. }
rce_md.
rce_keep_empty HFr KEEP0 (spZ regs - REC_CALLS_EQUAL_STK) (spZ regs - 144). clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ exfalso. rewrite branch_ltu_U, (U_atom E 42 NB), (U_atom E 45 (8 * Z.of_nat k)) in Hc by (first [exact E42 | exact E45 | subst NB; lia | lia]).
  apply Z.ltb_lt in Hc. subst NB. lia. }
clear Hc.
(* 0x8a06c .. 0x8a0a0: both shadow checks, a's argument word; b's word needs b's region *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; exact Usp. }
rce_md.
rce_keep_empty HFr KEEP1 (spZ regs - REC_CALLS_EQUAL_STK) (spZ regs - 144). clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
  assert (RB : region_ok SEGS E (ms_mem (restrict (w_H W) msx)) rce_argB);
  [ cbn [ms_mem restrict]; unfold region_ok, rce_argB;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite E44u;
    split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
    apply Forall_cons; [|apply Forall_nil];
    apply (chunk_ok_val SEGS E _ QB 0 8 (SOff 40 0) xb); [cbn [sv_denot]; rewrite E40u, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |];
    rewrite Z.add_0_r; apply rce_val_mem_of_aval;
    apply (rce_aval_keep (rdW W mem) _ (spZ regs - REC_CALLS_EQUAL_STK) (spZ regs));
    [ apply (kept_out_trans _ _ _ _ _ _ _ HK (kept_out_trans _ _ _ _ _ _ _ KEEP0 KEEP1 ltac:(lia) ltac:(lia))); lia | exact VXb | lia | lia | lia ]
  | ] end.
pose proof (rce_swap_ok E _ _ rce_argB HS eq_refl RB) as HS'. clear HS RB. rename HS' into HS.
(* 0x8a0a0 .. 0x8a0a4: b's word, the call of the strcmp wrapper *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; exact Usp. }
rce_md.
rce_keep_empty HFr KEEP2 (spZ regs - REC_CALLS_EQUAL_STK) (spZ regs - 144). clear HF HFr HG.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) _) _ =>
  set (rT0 := rT) in *; set (mT0 := mT) in * end.
assert (KEEP01 : kept_out (rdW W mem1) (rdW W mT0) (spZ regs - REC_CALLS_EQUAL_STK) (spZ regs - 144)).
{ apply (kept_out_trans _ _ _ _ _ _ _ (kept_out_trans _ _ _ _ _ _ _ KEEP0 KEEP1 ltac:(lia) ltac:(lia)) KEEP2); lia. }
assert (KEEPc : kept_out (rdW W mem) (rdW W mT0) (spZ regs - REC_CALLS_EQUAL_STK) (spZ regs)).
{ apply (kept_out_trans _ _ _ _ _ _ _ HK KEEP01); lia. }
assert (HspT : spZ rT0 = spZ regs + -144) by (unfold spZ at 1; rewrite P2, Usp; lia).
assert (HspT' : spZ rT0 = spZ regs - 144) by lia.
assert (P3' : getr rT0 3 = w64 (as_gp B)) by (rewrite P3, E3, R3; exact Hgp).
assert (P4' : getr rT0 4 = w64 (as_tp B)) by (rewrite P4, E4, R4; exact Htp).
assert (HraT : YK0s.ret_ok (getr rT0 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (P10' : getr rT0 10 = w64 xa) by (rewrite P10, E39; reflexivity).
assert (P11' : getr rT0 11 = w64 xb) by (rewrite P11, E40; reflexivity).
destruct (rce_str_call xa (snd pa) rT0 mT0 SXa KEEPc HspT') as (Hxa0 & STRa & RDa & TLa).
destruct (rce_str_call xb (snd pb) rT0 mT0 SXb KEEPc HspT') as (Hxb0 & STRb & RDb & TLb).
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS pa_segs_low errno_low (2 * ESTACK) (fun _ => False) (SIG CS___interceptor_trampoline_strcmp)
    W rT0 mT0 REC_CALLS_EQUAL_STK (spZ regs) [] ly S W mem md [] ly S _ 0 (-144) (Z_to_bv 64 (BASE + 15224)) _ HJ HspT eq_refl
    ltac:(lia) ltac:(lia) ltac:(rewrite HST, Hes; lia) P1 (fun a0 (H : False) => False_ind _ H)).
  apply (ASTRCMP fx ly S W rT0 mT0 _ xa xb (snd pa) (snd pb)).
  - exact (ecall_pre_stk_at SEGS B (2 * ESTACK) REC_CALLS_EQUAL_STK (spZ regs) [] ly S W mem md [] ly S W mT0 _ 0 rT0 (-144)
      HJ HspT eq_refl ltac:(lia) ltac:(rewrite Hes; lia) ltac:(rewrite HST, Hes; lia) HraT P3' P4').
  - exact P10'. - exact P11'. - lia. - lia.
  - exact STRa. - exact STRb. - exact RDa. - exact RDb. - exact TLa. - exact TLb.
  - exact (rce_rom_at mT0 KEEPc). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ2 & HK2).
(* back at 0x8a0a8 *)
jafter_call_keep_pi HS 48%nat regs2 (mrestrict (w_H W) mem2) HP2 (@nil nat) HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ apply Forall_nil. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
assert (A52 : ew (havoc E 48 (map (getr regs2) CLOB)) 52 = getr regs2 10) by reflexivity.
remember (havoc E 48 (map (getr regs2) CLOB)) as Ec eqn:HEc.
assert (HEI3 : img_env VAL A_LIM Ec) by (rewrite HEc; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD3 : forall n, (n < 48)%nat -> ew Ec n = ew E n) by (intros n Hn; rewrite HEc; apply YN3v.ew_havoc_old; exact Hn).
clear HEc.
assert (Usp3 : bv_unsigned (ew Ec 2) = spZ regs - 144) by (rewrite OLD3 by lia; exact Usp).
assert (SHOK3 : sh_ok SEGS rce_Bx [] Ec (mrestrict (w_H W) mem2)) by apply Forall_nil.
assert (KEEPk : kept_out (rdW W mT0) (rdW W mem2) (spZ regs - REC_CALLS_EQUAL_STK) (spZ regs - 144))
  by (intros x0 Hx0 Hn0; apply HK2; [exact Hx0 | rewrite Hes; lia | tauto]).
clear HK2. clear HJ. rename HJ2 into HJ.
assert (KEEPm : kept_out (rdW W mem1) (rdW W mem2) (spZ regs - REC_CALLS_EQUAL_STK) (spZ regs - 144)).
{ apply (kept_out_trans _ _ _ _ _ _ _ KEEP01 KEEPk); lia. }
clear KEEP0 KEEP1 KEEP2 KEEP01 KEEPk KEEPc.
(* 0x8a0a8: bnez a0, the wrapper's answer *)
psrr_branch_tok RUN BR HS SHOK3 Bspan.
- (* the strings differ: 0x8a120 returns 0 *)
  assert (HNE : snd pa <> snd pb).
  { intros Heq. rewrite branch_ne_U in Hc. apply negb_true_iff, Z.eqb_neq in Hc. apply Hc. unfold U. f_equal. cbn [sv_denot].
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned, A52, (proj2 HQ2 Heq). reflexivity. }
  paj_run_to_tok RUNTO HS HJ SHOK3 Bspan RCE_EPI.
  { awr_ok_tac; exact Usp3. }
  rce_md.
  rce_keep_empty HFr KEEP3 (spZ regs - REC_CALLS_EQUAL_STK) (spZ regs - 144). clear HF HFr HG.
  pmkst HS.
  prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4. prreg HS (10%bv : bv 5) F10.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mF _) _) _ =>
    assert (KEEP : kept_out (rdW W mem1) (rdW W mF) (spZ regs - REC_CALLS_EQUAL_STK) (spZ regs - 144))
      by (apply (kept_out_trans _ _ _ _ _ _ _ KEEPm KEEP3); lia) end.
  apply (rce_epi 0).
  + apply (rce_cut_kept regs1 mem1 md1 _ _ _ _ _ HCUT HJ KEEP); [lia | lia | rewrite F2, OLD3, E2 by lia; reflexivity
    | rewrite F3, OLD3, E3 by lia; reflexivity | rewrite F4, OLD3, E4 by lia; reflexivity].
  + exact F10.
  + rewrite (rce_calls_eqb_diff ca cb i e f He Hf); [reflexivity|].
    intros (_ & Hae). rewrite (rce_args_eqb_diff (snd e) (snd f) k pa pb Hpa Hpb HNE) in Hae. discriminate.
- (* equal strings *)
  assert (HEQ : snd pa = snd pb).
  { apply HQ2. rewrite branch_ne_U in Hc. apply negb_false_iff, Z.eqb_eq in Hc. unfold U in Hc. apply bv_eq in Hc.
    cbn [sv_denot] in Hc. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Hc. rewrite A52 in Hc. exact Hc. }
  clear Hc.
  paj_run_tok RUN HS HJ SHOK3 Bspan.
  { awr_ok_tac; exact Usp3. }
  rce_md.
  rce_keep_empty HFr KEEP3 (spZ regs - REC_CALLS_EQUAL_STK) (spZ regs - 144). clear HF HFr HG.
  assert (Hargs' : forall j p q, (j < Datatypes.S k)%nat -> nth_error (snd e) j = Some p -> nth_error (snd f) j = Some q -> snd p = snd q).
  { intros j p q Hj H1 H2. destruct (Nat.eq_dec j k) as [->|Hjk]; [|apply (Hargs j p q); [lia | exact H1 | exact H2]].
    rewrite Hpa in H1. rewrite Hpb in H2. injection H1 as <-. injection H2 as <-. exact HEQ. }
  (* 0x8a0b0: bne s2,s5, 8 * nargs against 8 (k + 1) *)
  psrr_branch_tok RUN BR HS SHOK3 Bspan.
  + (* more arguments: back to 0x8a064 *)
    assert (HkS : (Datatypes.S k < length (snd e))%nat).
    { rewrite branch_ne_U, !U_SOff in Hc. rewrite !OLD3 in Hc by lia. rewrite E46u, E45u in Hc.
      apply negb_true_iff, Z.eqb_neq in Hc. rewrite !zcanon_small in Hc by lia. subst nn. lia. }
    paj_run_to_tok RUNTO HS HJ SHOK3 Bspan RCE_IH.
    { awr_ok_tac; exact Usp3. }
    rce_md.
    rce_keep_empty HFr KEEP4 (spZ regs - REC_CALLS_EQUAL_STK) (spZ regs - 144). clear HF HFr HG.
    pmkst HS.
    prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
    prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
    prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
    prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
    rewrite ?OLD3 in Q2, Q3, Q4, Q8, Q9, Q18, Q19, Q20, Q21, Q22, Q23, Q25, Q26, Q27 by lia.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mF _) _) _ =>
      assert (KEEP : kept_out (rdW W mem1) (rdW W mF) (spZ regs - REC_CALLS_EQUAL_STK) (spZ regs - 144))
        by (apply (kept_out_trans _ _ _ _ _ _ _ (kept_out_trans _ _ _ _ _ _ _ KEEPm KEEP3 ltac:(lia) ltac:(lia)) KEEP4); lia) end.
    apply NXT; [exact HkS|].
    split; [split|].
    { apply (rce_cut_kept regs1 mem1 md1 _ _ _ _ _ HCUT HJ KEEP); [lia | lia | rewrite Q2, E2; reflexivity
      | rewrite Q3, E3; reflexivity | rewrite Q4, E4; reflexivity]. }
    { split; [exact Hi|]. split; [exact Hlen|]. split; [exact Hpre|].
      split; [apply (rce_slots_keep _ _ _ _ KEEP); [lia | exact SLT]|].
      split; [rewrite Q23, E32; reflexivity|].
      split; [rewrite Q20, E36; reflexivity|].
      split; [rewrite Q19, E37u; reflexivity|]. split; [rewrite Q26, E37u; reflexivity|].
      split; [rewrite Q9, E38u; reflexivity|]. rewrite Q25, E38u; reflexivity. }
    split; [rewrite Q24; reflexivity|]. split; [rewrite Q27, E33; reflexivity|].
    split; [exact He|]. split; [exact Hf|]. split; [exact Hfn|]. split; [exact Hnl|]. split; [exact HkS|].
    split; [exact Hargs'|].
    split; [rewrite Q21, E45u; unfold w64; f_equal; lia|].
    split; [rewrite Q18, E46; reflexivity|].
    split; [rewrite Q22, E41; reflexivity|].
    rewrite Q8, E42; reflexivity.
  + (* the last argument: to the latch 0x8a0b4 *)
    assert (HkS : Datatypes.S k = length (snd e)).
    { rewrite branch_ne_U, !U_SOff in Hc. rewrite !OLD3 in Hc by lia. rewrite E46u, E45u in Hc.
      apply negb_false_iff, Z.eqb_eq in Hc. rewrite !zcanon_small in Hc by lia. subst nn. lia. }
    paj_run_to_tok RUNTO HS HJ SHOK3 Bspan RCE_LT.
    { awr_ok_tac; exact Usp3. }
    rce_md.
    rce_keep_empty HFr KEEP4 (spZ regs - REC_CALLS_EQUAL_STK) (spZ regs - 144). clear HF HFr HG.
    pmkst HS.
    prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (9%bv : bv 5) Q9.
    prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
    prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
    rewrite ?OLD3 in Q2, Q3, Q4, Q9, Q19, Q20, Q23, Q25, Q26, Q27 by lia.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mF _) _) _ =>
      assert (KEEP : kept_out (rdW W mem1) (rdW W mF) (spZ regs - REC_CALLS_EQUAL_STK) (spZ regs - 144))
        by (apply (kept_out_trans _ _ _ _ _ _ _ (kept_out_trans _ _ _ _ _ _ _ KEEPm KEEP3 ltac:(lia) ltac:(lia)) KEEP4); lia) end.
    apply LTK. split; [split|].
    { apply (rce_cut_kept regs1 mem1 md1 _ _ _ _ _ HCUT HJ KEEP); [lia | lia | rewrite Q2, E2; reflexivity
      | rewrite Q3, E3; reflexivity | rewrite Q4, E4; reflexivity]. }
    { split; [exact Hi|]. split; [exact Hlen|]. split; [exact Hpre|].
      split; [apply (rce_slots_keep _ _ _ _ KEEP); [lia | exact SLT]|].
      split; [rewrite Q23, E32; reflexivity|].
      split; [rewrite Q20, E36; reflexivity|].
      split; [rewrite Q19, E37u; reflexivity|]. split; [rewrite Q26, E37u; reflexivity|].
      split; [rewrite Q9, E38u; reflexivity|]. rewrite Q25, E38u; reflexivity. }
    split; [|split; [rewrite Q24; reflexivity | rewrite Q27, E33; reflexivity]].
    intros j e' f' Hj H1 H2. destruct (Nat.eq_dec j i) as [->|Hji]; [|apply (Hpre j e' f'); [lia | exact H1 | exact H2]].
    rewrite He in H1. rewrite Hf in H2. injection H1 as <-. injection H2 as <-.
    split; [exact Hfn|]. apply rce_args_eqb_true; [lia|].
    intros j p q H1 H2. apply (Hargs' j p q); [|exact H1 | exact H2].
    rewrite HkS. apply (proj1 (nth_error_Some (snd e) j)). rewrite H1. discriminate.
Qed.
Lemma rce_inner : forall i e f,
(forall r m d, rce_LT i r m d -> SRr SEGS W (mkCfg (mkst r (Z_to_bv 64 (BASE + RCE_LT)) m (seg_rom SEGS)) d) rce_Q) ->
forall dd k regs1 mem1 md1, (k + Datatypes.S dd = length (snd e))%nat -> rce_IH i k e f regs1 mem1 md1 ->
SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + RCE_IH)) mem1 (seg_rom SEGS)) md1) rce_Q.
Proof.
intros i e f LTK dd. induction dd as [|dd IHd]; intros k regs1 mem1 md1 Hk HIH.
- apply (rce_inner_step i k e f regs1 mem1 md1 LTK); [intros Hk2; lia | exact HIH].
- apply (rce_inner_step i k e f regs1 mem1 md1 LTK); [|exact HIH].
  intros _ r m d HIH2. apply (IHd (Datatypes.S k) r m d); [lia | exact HIH2].
Qed.


(* ---------- the outer loop's body: 0x89f98 .. 0x8a064 ---------- *)
Lemma rce_U_sext32 : forall E a0 r, U E a0 = r -> 0 <= r < 2 ^ 32 ->
U E (SExt true 32 a0) = (if r <? 2 ^ 31 then r else r - 2 ^ 32 + 2 ^ 64).
Proof.
intros E a0 r Ha Hr. rewrite U_SExt, Ha. change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small r) by lia.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ 32 / 2) with (2 ^ 31).
destruct (Z.ltb_spec r (2 ^ 31)) as [Hl | Hh].
- rewrite (Z.mod_small (r + 2 ^ 31)) by lia. replace (r + 2 ^ 31 - 2 ^ 31) with r by lia. apply zcanon_id. unfold M64. lia.
- replace ((r + 2 ^ 31) mod 2 ^ 32) with (r + 2 ^ 31 - 2 ^ 32).
  2:{ replace (r + 2 ^ 31) with ((r + 2 ^ 31 - 2 ^ 32) + 1 * 2 ^ 32) at 2 by lia. rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. reflexivity. }
  unfold zcanon, M64. replace (r + 2 ^ 31 - 2 ^ 32 - 2 ^ 31) with ((r - 2 ^ 32 + 2 ^ 64) + (-1) * 2 ^ 64) by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma rce_sext_eq : forall E n m x y, ew E n = w64 (x mod 2 ^ 32) -> ew E m = w64 (y mod 2 ^ 32) ->
-2^31 <= x < 2^31 -> -2^31 <= y < 2^31 ->
(U E (SExt true 32 (SOff n 0)) = U E (SExt true 32 (SOff m 0)) <-> x = y).
Proof.
intros E n m x y Hn Hm Hx Hy.
assert (Hxr : 0 <= x mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
assert (Hyr : 0 <= y mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
rewrite (rce_U_sext32 E _ (x mod 2 ^ 32)) by (first [exact Hxr | apply U_atom; [exact Hn | lia]]).
rewrite (rce_U_sext32 E _ (y mod 2 ^ 32)) by (first [exact Hyr | apply U_atom; [exact Hm | lia]]).
assert (Ex : x mod 2 ^ 32 = if x <? 0 then x + 2 ^ 32 else x).
{ destruct (Z.ltb_spec x 0); [replace x with ((x + 2 ^ 32) + (-1) * 2 ^ 32) at 1 by lia; rewrite Z_mod_plus_full |]; apply Z.mod_small; lia. }
assert (Ey : y mod 2 ^ 32 = if y <? 0 then y + 2 ^ 32 else y).
{ destruct (Z.ltb_spec y 0); [replace y with ((y + 2 ^ 32) + (-1) * 2 ^ 32) at 1 by lia; rewrite Z_mod_plus_full |]; apply Z.mod_small; lia. }
rewrite Ex, Ey. split; intros H.
- destruct (Z.ltb_spec x 0), (Z.ltb_spec y 0);
  repeat match type of H with context [if ?c then _ else _] => destruct c eqn:?; rewrite ?Z.ltb_lt, ?Z.ltb_ge in * end; lia.
- subst y. reflexivity.
Qed.
Lemma rce_swrap_small : forall z, 0 <= z < 2 ^ 63 -> bv_swrap 64 z = z.
Proof.
intros z Hz. unfold bv_swrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). change (2 ^ 64 / 2) with (2 ^ 63).
rewrite bv_wrap_small; [lia|]. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.
Lemma rce_bge0 : forall E n v, ew E n = w64 v -> 0 <= v < 2 ^ 63 ->
branch_taken BC_GE (sv_denot E (SLit 0)) (sv_denot E (SOff n 0)) = (v <=? 0).
Proof.
intros E n v Hn Hv. cbn [branch_taken sv_denot]. rewrite Hn, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia.
unfold bv_lts. rewrite !signed_lit. rewrite !zcanon_small by lia. rewrite !rce_swrap_small by lia.
destruct (Z.ltb_spec 0 v); destruct (Z.leb_spec v 0); try reflexivity; lia.
Qed.
Lemma rce_alias_den : forall E na ni np av iv, ew E na = w64 av -> ew E ni = w64 iv -> ew E np = w64 (av + 56 * iv) ->
0 <= av -> 0 <= iv -> av + 56 * iv < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SOff na 0) (SMd M_MUL (SOff ni 0) (SLit 56))) = sv_denot E (SOff np 0).
Proof.
intros E na ni np av iv Ha Hi Hp H0 H1 H2. cbn [sv_denot]. rewrite Ha, Hi, Hp. unfold w64.
rewrite !unsigned_lit_small by lia. rewrite !Z.add_0_r.
apply bv_eq. rewrite alu64_unsigned, mul_div_unsigned. cbn [zalu_raw zmd_raw]. rewrite !unsigned_lit_small by lia.
rewrite (bv_wrap_small 64 (iv * 56)) by (change (bv_modulus 64) with (2 ^ 64); lia).
rewrite bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). lia.
Qed.
Definition rce_o_extra (i : nat) (fa fb na nb : Z) : list word :=
map w64 [SB; a; b; Z.of_nat (length ca); Z.of_nat i; a + 56 * Z.of_nat i; b + 56 * Z.of_nat i; fa; fb; na; nb].
Lemma rce_outer_seed : forall (i : nat) fa na regs1 mem1,
(i < length ca)%nat -> length cb = length ca -> 0 <= fa < 2 ^ 32 -> 0 <= na <= 6 ->
getr regs1 2 = w64 (spZ regs - 144) -> rce_slots (rdW W mem1) ->
getr regs1 23 = w64 SB -> getr regs1 20 = w64 (Z.of_nat i) ->
getr regs1 19 = w64 (a + 56 * Z.of_nat i + 8) -> getr regs1 26 = w64 (a + 56 * Z.of_nat i + 8) ->
getr regs1 9 = w64 (b + 56 * Z.of_nat i + 8) -> getr regs1 25 = w64 (b + 56 * Z.of_nat i + 8) ->
getr regs1 15 = w64 a -> getr regs1 14 = w64 1 ->
range_addressable (rdW W mem1) SHADOW_OFF (a + 56 * Z.of_nat i) 56 ->
range_addressable (rdW W mem1) SHADOW_OFF (b + 56 * Z.of_nat i) 56 ->
forall fb nb, 0 <= fb < 2 ^ 32 -> 0 <= nb <= 6 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (rce_o_extra i fa fb na nb))) rce_ss_outer
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + RCE_OH)) mem1 (seg_rom SEGS)))
/\ sh_ok SEGS rce_Bx rce_o_SH (Eimg (Ereg regs1 (rce_o_extra i fa fb na nb))) (mrestrict (w_H W) mem1).
Proof.
intros i fa na regs1 mem1 Hi Hlen Hfa Hna R2 SLT R23 R20 R19 R26 R9 R25 R15 R14 RAa RAb fb nb Hfb Hnb.
pose proof rce_sp as (Hal16 & Hslo & Hshi). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HST : REC_CALLS_EQUAL_STK = 8336) by reflexivity.
destruct (rce_tab a ca HCA ltac:(lia)) as (Hca16 & Ha4 & Hah & _ & HaBD).
destruct (rce_tab b cb HCB ltac:(lia)) as (_ & Hb4 & Hbh & _ & HbBD). rewrite Hlen in Hbh, HbBD.
set (E := Eimg (Ereg regs1 (rce_o_extra i fa fb na nb))).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) by (intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 144) by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (EX : forall j v, nth_error [SB; a; b; Z.of_nat (length ca); Z.of_nat i; a + 56 * Z.of_nat i; b + 56 * Z.of_nat i; fa; fb; na; nb] j = Some v ->
  ew E (32 + j) = w64 v).
{ intros j v Hj. assert (Hj11 : (j < 11)%nat) by (change 11%nat with (length [SB; a; b; Z.of_nat (length ca); Z.of_nat i; a + 56 * Z.of_nat i; b + 56 * Z.of_nat i; fa; fb; na; nb]); apply (proj1 (nth_error_Some _ j)); rewrite Hj; discriminate).
  subst E. unfold rce_o_extra. rewrite rce_ex_w64 by (cbn; unfold A_TEXT; lia). f_equal. apply nth_error_nth. exact Hj. }
pose proof (EX 0%nat _ eq_refl) as E32. pose proof (EX 1%nat _ eq_refl) as E33. pose proof (EX 2%nat _ eq_refl) as E34.
pose proof (EX 3%nat _ eq_refl) as E35. pose proof (EX 4%nat _ eq_refl) as E36. pose proof (EX 5%nat _ eq_refl) as E37.
pose proof (EX 6%nat _ eq_refl) as E38. pose proof (EX 9%nat _ eq_refl) as E41. pose proof (EX 10%nat _ eq_refl) as E42.
cbn [Nat.add] in E32, E33, E34, E35, E36, E37, E38, E41, E42. clear EX.
assert (E32u : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (E33u : bv_unsigned (ew E 33) = a) by (rewrite E33; apply unsigned_lit_small; lia).
assert (E34u : bv_unsigned (ew E 34) = b) by (rewrite E34; apply unsigned_lit_small; lia).
assert (E35u : bv_unsigned (ew E 35) = Z.of_nat (length ca)) by (rewrite E35; apply unsigned_lit_small; lia).
assert (E36u : bv_unsigned (ew E 36) = Z.of_nat i) by (rewrite E36; apply unsigned_lit_small; lia).
assert (E37u : bv_unsigned (ew E 37) = a + 56 * Z.of_nat i) by (rewrite E37; apply unsigned_lit_small; lia).
assert (E38u : bv_unsigned (ew E 38) = b + 56 * Z.of_nat i) by (rewrite E38; apply unsigned_lit_small; lia).
assert (E41u : bv_unsigned (ew E 41) = na) by (rewrite E41; apply unsigned_lit_small; lia).
assert (E42u : bv_unsigned (ew E 42) = nb) by (rewrite E42; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold rce_ss_outer. apply pa_entry_st_ok_full.
  + rce_regs_ok EE ltac:(rewrite ?E32u, ?E33u, ?E34u, ?E35u, ?E36u, ?E37u, ?E38u).
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil]. apply (rce_fstack_ok E mem1 Usp E34u E35u); [lia | lia | exact SLT].
  + cbn. tauto.
  + split; [|split; [exact I|]].
    * cbn [f_atoms atoms_ok rce_o_facts]. unfold afact_ok, rce_spF, rce_SBF, rce_PTRF, rce_NF. cbn [af_lo af_hi af_al2].
      rewrite Usp, E32u, E37u, E38u, E41u, E42u. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat split; try lia. rewrite Zminus_mod, Hal16. reflexivity.
    * cbn [f_alias alias_ok rce_o_facts]. split; [|split; [|exact I]].
      -- apply (rce_alias_den E 33 36 37 a (Z.of_nat i) E33 E36 E37); lia.
      -- apply (rce_alias_den E 34 36 38 b (Z.of_nat i) E34 E36 E38); lia.
- unfold sh_ok, rce_o_SH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + apply (rce_shent_ok E _ 37 (a + 56 * Z.of_nat i) 0 56 E32 E37u); try lia; [rewrite Z.add_0_r; exact RAa | intros y Hy; apply HaBD; lia].
  + apply (rce_shent_ok E _ 38 (b + 56 * Z.of_nat i) 0 56 E32 E38u); try lia; [rewrite Z.add_0_r; exact RAb | intros y Hy; apply HbBD; lia].
Qed.


Lemma rce_outer_body : forall i,
(forall r m d, rce_LT i r m d -> SRr SEGS W (mkCfg (mkst r (Z_to_bv 64 (BASE + RCE_LT)) m (seg_rom SEGS)) d) rce_Q) ->
forall regs1 mem1 md1, rce_OH i regs1 mem1 md1 ->
SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + RCE_OH)) mem1 (seg_rom SEGS)) md1) rce_Q.
Proof.
intros i LTK regs1 mem1 md1 ((HCUT & Hi & Hlen & Hpre & SLT & R23 & R20 & R19 & R26 & R9 & R25) & R15 & R14).
pose proof HCUT as (HJ & HK & HFR & R2 & R3 & R4).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & HQT).
pose proof rce_sp as (Hal16 & Hslo & Hshi). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HST : REC_CALLS_EQUAL_STK = 8336) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
destruct (rce_tab a ca HCA ltac:(lia)) as (Hca16 & Ha4 & Hah & HaRA & HaBD).
destruct (rce_tab b cb HCB ltac:(lia)) as (_ & Hb4 & Hbh & HbRA & HbBD). rewrite Hlen in Hbh, HbRA, HbBD.
destruct (nth_error ca i) as [e|] eqn:He; [|apply nth_error_None in He; lia].
destruct (nth_error cb i) as [f|] eqn:Hf; [|apply nth_error_None in Hf; lia].
destruct (rce_slot a ca i e HCA He) as (Hfe & Hle & VFa & VNa & _).
destruct (rce_slot b cb i f HCB Hf) as (Hff & Hlf & VFb & VNb & _).
pose proof (rce_aval_mod _ _ _ _ VFa) as VFa'. pose proof (rce_aval_mod _ _ _ _ VFb) as VFb'.
change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in VFa', VFb'. clear VFa VFb.
set (fa := fst e mod 2 ^ 32) in *. set (fb := fst f mod 2 ^ 32) in *.
set (na := Z.of_nat (length (snd e))) in *. set (nb := Z.of_nat (length (snd f))) in *.
assert (Hfa : 0 <= fa < 2 ^ 32) by (apply Z.mod_pos_bound; lia). assert (Hfb : 0 <= fb < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
assert (Hna : 0 <= na <= 6) by (subst na; lia). assert (Hnb : 0 <= nb <= 6) by (subst nb; lia).
assert (RAa1 : range_addressable (rdW W mem1) SHADOW_OFF (a + 56 * Z.of_nat i) 56).
{ apply (range_addressable_kept_win (rdW W mem) (rdW W mem1) (spZ regs - REC_CALLS_EQUAL_STK) (spZ regs)); [exact HK | lia | lia | lia |].
  apply (range_addressable_sub _ _ a (56 * Z.of_nat (length ca))); [exact HaRA | lia | lia]. }
assert (RAb1 : range_addressable (rdW W mem1) SHADOW_OFF (b + 56 * Z.of_nat i) 56).
{ apply (range_addressable_kept_win (rdW W mem) (rdW W mem1) (spZ regs - REC_CALLS_EQUAL_STK) (spZ regs)); [exact HK | lia | lia | lia |].
  apply (range_addressable_sub _ _ b (56 * Z.of_nat (length ca))); [exact HbRA | lia | lia]. }
destruct (rce_outer_seed i fa na regs1 mem1 Hi Hlen Hfa Hna R2 SLT R23 R20 R19 R26 R9 R25 R15 R14 RAa1 RAb1 fb nb Hfb Hnb) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs1 (rce_o_extra i fa fb na nb)))) by apply Eimg_env.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (Eimg (Ereg regs1 (rce_o_extra i fa fb na nb))) n = getr regs1 r)
  by (intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j v, nth_error [SB; a; b; Z.of_nat (length ca); Z.of_nat i; a + 56 * Z.of_nat i; b + 56 * Z.of_nat i; fa; fb; na; nb] j = Some v ->
  ew (Eimg (Ereg regs1 (rce_o_extra i fa fb na nb))) (32 + j) = w64 v).
{ intros j v Hj. assert (Hj11 : (j < 11)%nat) by (change 11%nat with (length [SB; a; b; Z.of_nat (length ca); Z.of_nat i; a + 56 * Z.of_nat i; b + 56 * Z.of_nat i; fa; fb; na; nb]); apply (proj1 (nth_error_Some _ j)); rewrite Hj; discriminate).
  unfold rce_o_extra. rewrite rce_ex_w64 by (cbn; unfold A_TEXT; lia). f_equal. apply nth_error_nth. exact Hj. }
pose proof (EX 0%nat _ eq_refl) as E32. pose proof (EX 1%nat _ eq_refl) as E33. pose proof (EX 2%nat _ eq_refl) as E34.
pose proof (EX 3%nat _ eq_refl) as E35. pose proof (EX 4%nat _ eq_refl) as E36. pose proof (EX 5%nat _ eq_refl) as E37.
pose proof (EX 6%nat _ eq_refl) as E38. pose proof (EX 7%nat _ eq_refl) as E39. pose proof (EX 8%nat _ eq_refl) as E40.
pose proof (EX 9%nat _ eq_refl) as E41. pose proof (EX 10%nat _ eq_refl) as E42.
cbn [Nat.add] in E32, E33, E34, E35, E36, E37, E38, E39, E40, E41, E42. clear EX.
pose proof (EE 2%nat 2%bv eq_refl) as E2. pose proof (EE 3%nat 3%bv eq_refl) as E3. pose proof (EE 4%nat 4%bv eq_refl) as E4.
remember (Eimg (Ereg regs1 (rce_o_extra i fa fb na nb))) as E eqn:HE. clear HE.
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 144) by (rewrite E2, R2; apply unsigned_lit_small; lia).
assert (E33u : bv_unsigned (ew E 33) = a) by (rewrite E33; apply unsigned_lit_small; lia).
assert (E36u : bv_unsigned (ew E 36) = Z.of_nat i) by (rewrite E36; apply unsigned_lit_small; lia).
assert (E37u : bv_unsigned (ew E 37) = a + 56 * Z.of_nat i) by (rewrite E37; apply unsigned_lit_small; lia).
assert (E38u : bv_unsigned (ew E 38) = b + 56 * Z.of_nat i) by (rewrite E38; apply unsigned_lit_small; lia).
assert (E39u : bv_unsigned (ew E 39) = fa) by (rewrite E39; apply unsigned_lit_small; lia).
assert (E40u : bv_unsigned (ew E 40) = fb) by (rewrite E40; apply unsigned_lit_small; lia).
assert (E41u : bv_unsigned (ew E 41) = na) by (rewrite E41; apply unsigned_lit_small; lia).
assert (E42u : bv_unsigned (ew E 42) = nb) by (rewrite E42; apply unsigned_lit_small; lia).
assert (RA : forall m', kept_out (rdW W mem1) (rdW W m') (spZ regs - REC_CALLS_EQUAL_STK) (spZ regs - 144) ->
  region_ok SEGS E (mrestrict (w_H W) m') rce_slotA /\ region_ok SEGS E (mrestrict (w_H W) m') rce_slotB).
{ intros m' Hm'.
  assert (HKm : forall x n v, aval_mem (rdW W mem) x n v -> 0 <= x -> x + Z.of_nat n <= alloc_ceiling -> aval_mem (rdW W m') x n v)
    by (intros x n v H Hx Hxn; apply (rce_aval_keep _ _ _ _ _ _ _ (kept_out_trans _ _ _ _ _ _ _ HK Hm' ltac:(lia) ltac:(lia)) H); lia).
  split.
  - unfold region_ok, rce_slotA. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E37u.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (chunk_ok_val SEGS E _ (a + 56 * Z.of_nat i) 0 4 (SOff 39 0) fa); [cbn [sv_denot]; rewrite E39u, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. apply rce_val_mem_of_aval. apply HKm; [exact VFa' | lia | cbn; lia].
    + apply (chunk_ok_val SEGS E _ (a + 56 * Z.of_nat i) 4 4 (SOff 41 0) na); [cbn [sv_denot]; rewrite E41u, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
      apply rce_val_mem_of_aval. apply HKm; [exact VNa | lia | cbn; lia].
  - unfold region_ok, rce_slotB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E38u.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (chunk_ok_val SEGS E _ (b + 56 * Z.of_nat i) 0 4 (SOff 40 0) fb); [cbn [sv_denot]; rewrite E40u, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. apply rce_val_mem_of_aval. apply HKm; [exact VFb' | lia | cbn; lia].
    + apply (chunk_ok_val SEGS E _ (b + 56 * Z.of_nat i) 4 4 (SOff 42 0) nb); [cbn [sv_denot]; rewrite E42u, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
      apply rce_val_mem_of_aval. apply HKm; [exact VNb | lia | cbn; lia]. }
(* the cut at a later state *)
assert (CUT : forall regs2 mem2 md2,
  ajournal SEGS B REC_CALLS_EQUAL_STK (spZ regs) [] ly S W mem md [] ly S W mem2 md2 0 ->
  kept_out (rdW W mem1) (rdW W mem2) (spZ regs - REC_CALLS_EQUAL_STK) (spZ regs - 144) ->
  getr regs2 2 = ew E 2 -> getr regs2 3 = ew E 3 -> getr regs2 4 = ew E 4 ->
  rce_cut regs2 mem2 md2 /\ rce_slots (rdW W mem2)).
{ intros regs2 mem2 md2 HJ2 HK2 Q2 Q3 Q4. split.
  - apply (rce_cut_kept regs1 mem1 md1 _ _ _ _ _ HCUT HJ2 HK2); [lia | lia | rewrite Q2, E2; reflexivity
    | rewrite Q3, E3; reflexivity | rewrite Q4, E4; reflexivity].
  - apply (rce_slots_keep _ _ _ _ HK2); [lia | exact SLT]. }
(* 0x89f98 .. 0x89fb4: a + 56i formed, the null pair 0x89fac decided (a4 = 1, a + 56i >= 4096), bltu a0,a5 *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; exact Usp. }
rce_md.
rce_keep_empty HFr KEEP1 (spZ regs - REC_CALLS_EQUAL_STK) (spZ regs - 144). clear HF HFr HG.
(* 0x89fb4: bltu a0,a5 to the unimp (UBSan, recorder.c:170): taken when a + 56i wraps; a + 56 n < 2 ^ 47 *)
psrr_branch_tok RUN BR HS SHOK Bspan.
{ exfalso. rewrite branch_ltu_U, (U_atom E 37 (a + 56 * Z.of_nat i)), (U_atom E 33 a) in Hc by (first [exact E37 | exact E33 | lia]).
  apply Z.ltb_lt in Hc. lia. }
clear Hc.
(* .. 0x89fec: 0x89fbc decided (24(sp) = 1), the check of a[i], b + 56i formed, 0x89fe4 decided (16(sp) = 1,
   b + 56i >= 4096), bltu a1,a2 *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; exact Usp. }
rce_md.
rce_keep_empty HFr KEEP2 (spZ regs - REC_CALLS_EQUAL_STK) (spZ regs - 144). clear HF HFr HG.
pose proof (kept_out_trans _ _ _ _ _ _ _ KEEP1 KEEP2 (Z.le_refl _) (Z.le_refl _)) as K12. clear KEEP1 KEEP2.
(* 0x89fec: bltu a1,a2 to the unimp: taken when b + 56i wraps *)
psrr_branch_tok RUN BR HS SHOK Bspan.
{ exfalso. rewrite branch_ltu_U, (U_atom E 38 (b + 56 * Z.of_nat i)), (U_atom E 34 b) in Hc by (first [exact E38 | exact E34 | lia]).
  apply Z.ltb_lt in Hc. lia. }
clear Hc.
(* .. 0x8a004: 0x89ff4 decided (8(sp) = 1), the check of b[i]; a[i].fn needs a's region *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; exact Usp. }
rce_md.
rce_keep_empty HFr KEEP2 (spZ regs - REC_CALLS_EQUAL_STK) (spZ regs - 144). clear HF HFr HG.
pose proof (kept_out_trans _ _ _ _ _ _ _ K12 KEEP2 (Z.le_refl _) (Z.le_refl _)) as K13. clear K12 KEEP2.
pose proof (rce_swap_ok E _ _ rce_slotA HS eq_refl (proj1 (RA _ K13))) as HS'. clear HS. rename HS' into HS.
(* .. 0x8a00c: a[i].fn; b[i].fn needs b's region *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; exact Usp. }
rce_md.
rce_keep_empty HFr KEEP3 (spZ regs - REC_CALLS_EQUAL_STK) (spZ regs - 144). clear HF HFr HG.
pose proof (kept_out_trans _ _ _ _ _ _ _ K13 KEEP3 (Z.le_refl _) (Z.le_refl _)) as K14. clear K13 KEEP3.
pose proof (rce_swap_ok E _ _ rce_slotB HS eq_refl (proj2 (RA _ K14))) as HS'. clear HS. rename HS' into HS.
(* .. 0x8a010: b[i].fn, bne a2,a3 *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; exact Usp. }
rce_md.
rce_keep_empty HFr KEEP4 (spZ regs - REC_CALLS_EQUAL_STK) (spZ regs - 144). clear HF HFr HG.
pose proof (kept_out_trans _ _ _ _ _ _ _ K14 KEEP4 (Z.le_refl _) (Z.le_refl _)) as K15. clear K14 KEEP4.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* the function numbers differ: 0x8a120 returns 0 *)
  assert (HNE : fst e <> fst f).
  { intros Heq. rewrite branch_ne_U in Hc. apply negb_true_iff, Z.eqb_neq in Hc. apply Hc.
    apply (rce_sext_eq E 39 40 (fst e) (fst f) E39 E40 Hfe Hff). exact Heq. }
  paj_run_to_tok RUNTO HS HJ SHOK Bspan RCE_EPI.
  { awr_ok_tac; exact Usp. }
  rce_md.
  rce_keep_empty HFr KEEP5 (spZ regs - REC_CALLS_EQUAL_STK) (spZ regs - 144). clear HF HFr HG.
  pmkst HS.
  prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4. prreg HS (10%bv : bv 5) F10.
  destruct (CUT _ _ _ HJ ltac:(apply (kept_out_trans _ _ _ _ _ _ _ K15 KEEP5); lia) F2 F3 F4) as (HC & _).
  apply (rce_epi 0 _ _ _ HC F10).
  rewrite (rce_calls_eqb_diff ca cb i e f He Hf); [reflexivity|]. intros (H1 & _). exact (HNE H1).
- assert (HEQf : fst e = fst f).
  { apply (rce_sext_eq E 39 40 _ _ E39 E40 Hfe Hff). rewrite branch_ne_U in Hc. apply negb_false_iff, Z.eqb_eq in Hc. exact Hc. }
  clear Hc.
  (* .. 0x8a038: the checks of the counts; a[i].nargs needs a's region *)
  paj_run_tok RUN HS HJ SHOK Bspan.
  { awr_ok_tac; exact Usp. }
  rce_md.
  rce_keep_empty HFr KEEP5 (spZ regs - REC_CALLS_EQUAL_STK) (spZ regs - 144). clear HF HFr HG.
  pose proof (kept_out_trans _ _ _ _ _ _ _ K15 KEEP5 (Z.le_refl _) (Z.le_refl _)) as K16. clear K15 KEEP5.
  pose proof (rce_swap_ok E _ _ rce_slotA HS eq_refl (proj1 (RA _ K16))) as HS'. clear HS. rename HS' into HS.
  paj_run_tok RUN HS HJ SHOK Bspan.
  { awr_ok_tac; exact Usp. }
  rce_md.
  rce_keep_empty HFr KEEP6 (spZ regs - REC_CALLS_EQUAL_STK) (spZ regs - 144). clear HF HFr HG.
  pose proof (kept_out_trans _ _ _ _ _ _ _ K16 KEEP6 (Z.le_refl _) (Z.le_refl _)) as K17. clear K16 KEEP6.
  pose proof (rce_swap_ok E _ _ rce_slotB HS eq_refl (proj2 (RA _ K17))) as HS'. clear HS. rename HS' into HS.
  (* .. 0x8a044: b[i].nargs, bne s2,a2 *)
  paj_run_tok RUN HS HJ SHOK Bspan.
  { awr_ok_tac; exact Usp. }
  rce_md.
  rce_keep_empty HFr KEEP7 (spZ regs - REC_CALLS_EQUAL_STK) (spZ regs - 144). clear HF HFr HG.
  pose proof (kept_out_trans _ _ _ _ _ _ _ K17 KEEP7 (Z.le_refl _) (Z.le_refl _)) as K18. clear K17 KEEP7.
  assert (U41 : U E (SOff 41 0) = na) by (apply U_atom; [exact E41 | lia]).
  assert (U42 : U E (SOff 42 0) = nb) by (apply U_atom; [exact E42 | lia]).
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* the argument counts differ: return 0 *)
    assert (HNE : length (snd e) <> length (snd f)).
    { intros Heq. rewrite branch_ne_U, U41, U42 in Hc. apply negb_true_iff, Z.eqb_neq in Hc. apply Hc. subst na nb. rewrite Heq. reflexivity. }
    paj_run_to_tok RUNTO HS HJ SHOK Bspan RCE_EPI.
    { awr_ok_tac; exact Usp. }
    rce_md.
    rce_keep_empty HFr KEEP8 (spZ regs - REC_CALLS_EQUAL_STK) (spZ regs - 144). clear HF HFr HG.
    pmkst HS.
    prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4. prreg HS (10%bv : bv 5) F10.
    destruct (CUT _ _ _ HJ ltac:(apply (kept_out_trans _ _ _ _ _ _ _ K18 KEEP8); lia) F2 F3 F4) as (HC & _).
    apply (rce_epi 0 _ _ _ HC F10).
    rewrite (rce_calls_eqb_diff ca cb i e f He Hf); [reflexivity|]. intros (_ & H2).
    rewrite (rce_args_eqb_len (snd e) (snd f) HNE) in H2. discriminate.
  + assert (HEQn : length (snd e) = length (snd f)).
    { rewrite branch_ne_U, U41, U42 in Hc. apply negb_false_iff, Z.eqb_eq in Hc. subst na nb. lia. }
    clear Hc.
    (* 0x8a048: blez s2 *)
    paj_run_tok RUN HS HJ SHOK Bspan.
    { awr_ok_tac; exact Usp. }
    rce_md.
    rce_keep_empty HFr KEEP8 (spZ regs - REC_CALLS_EQUAL_STK) (spZ regs - 144). clear HF HFr HG.
    pose proof (kept_out_trans _ _ _ _ _ _ _ K18 KEEP8 (Z.le_refl _) (Z.le_refl _)) as K19. clear K18 KEEP8.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * (* no arguments: the slot matches; to the latch *)
      assert (H0 : length (snd e) = 0%nat).
      { rewrite (rce_bge0 E 41 na E41) in Hc by lia. apply Z.leb_le in Hc. subst na. lia. }
      clear Hc.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan RCE_LT.
      { awr_ok_tac; exact Usp. }
      rce_md.
      rce_keep_empty HFr KEEP9 (spZ regs - REC_CALLS_EQUAL_STK) (spZ regs - 144). clear HF HFr HG.
      pmkst HS.
      prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (9%bv : bv 5) Q9.
      prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
      prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
      destruct (CUT _ _ _ HJ ltac:(apply (kept_out_trans _ _ _ _ _ _ _ K19 KEEP9); lia) Q2 Q3 Q4) as (HC & SL2).
      apply LTK. split; [split|].
      { exact HC. }
      { split; [exact Hi|]. split; [exact Hlen|]. split; [exact Hpre|]. split; [exact SL2|].
        split; [rewrite Q23, E32; reflexivity|]. split; [rewrite Q20, E36; reflexivity|].
        split; [rewrite Q19, E37u; reflexivity|]. split; [rewrite Q26, E37u; reflexivity|].
        split; [rewrite Q9, E38u; reflexivity|]. rewrite Q25, E38u; reflexivity. }
      split; [|split; [rewrite Q24; reflexivity | rewrite Q27, E33; reflexivity]].
      intros j e' f' Hj H1 H2. destruct (Nat.eq_dec j i) as [->|Hji]; [|apply (Hpre j e' f'); [lia | exact H1 | exact H2]].
      rewrite He in H1. rewrite Hf in H2. injection H1 as <-. injection H2 as <-.
      split; [exact HEQf|]. apply rce_args_eqb_true; [lia|].
      intros j p q H1 _. exfalso. assert (Hjl : (j < length (snd e))%nat) by (apply (proj1 (nth_error_Some (snd e) j)); rewrite H1; discriminate). lia.
    * (* arguments: 0x8a04c .. 0x8a060 set s5 = 0, s6 = ~(a[i].args), s0 = ~(b[i].args), s2 = 8 * nargs; the inner loop *)
      assert (H0 : (0 < length (snd e))%nat).
      { rewrite (rce_bge0 E 41 na E41) in Hc by lia. apply Z.leb_gt in Hc. subst na. lia. }
      clear Hc.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan RCE_IH.
      { awr_ok_tac; exact Usp. }
      rce_md.
      rce_keep_empty HFr KEEP9 (spZ regs - REC_CALLS_EQUAL_STK) (spZ regs - 144). clear HF HFr HG.
      pmkst HS.
      prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
      prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
      prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
      prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
      destruct (CUT _ _ _ HJ ltac:(apply (kept_out_trans _ _ _ _ _ _ _ K19 KEEP9); lia) Q2 Q3 Q4) as (HC & SL2).
      apply (rce_inner i e f LTK (length (snd e) - 1) 0); [lia|].
      split; [split|].
      { exact HC. }
      { split; [exact Hi|]. split; [exact Hlen|]. split; [exact Hpre|]. split; [exact SL2|].
        split; [rewrite Q23, E32; reflexivity|]. split; [rewrite Q20, E36; reflexivity|].
        split; [rewrite Q19, E37u; reflexivity|]. split; [rewrite Q26, E37u; reflexivity|].
        split; [rewrite Q9, E38u; reflexivity|]. rewrite Q25, E38u; reflexivity. }
      split; [rewrite Q24; reflexivity|]. split; [rewrite Q27, E33; reflexivity|].
      split; [exact He|]. split; [exact Hf|]. split; [exact HEQf|]. split; [lia|]. split; [exact H0|].
      split; [intros j p q Hj; lia|].
      split; [rewrite Q21; reflexivity|].
      split; [rewrite Q18, E41; unfold w64; rewrite rce_sll3 by (subst na; lia); subst na; f_equal; lia|].
      split; [rewrite Q22, E37u; unfold w64; rewrite rce_xor_m1 by lia; f_equal; lia|].
      rewrite Q8, E38u; unfold w64; rewrite rce_xor_m1 by lia; f_equal; lia.
Qed.


(* ---------- the loop ---------- *)
Lemma rce_loop_all : forall dd i, (i + dd = length ca)%nat -> (i < length ca)%nat -> forall r m d, rce_OH i r m d ->
SRr SEGS W (mkCfg (mkst r (Z_to_bv 64 (BASE + RCE_OH)) m (seg_rom SEGS)) d) rce_Q.
Proof.
induction dd as [|dd IH]; intros i Hd Hi r m d HOH; [lia|].
apply (rce_outer_body i); [|exact HOH].
intros r' m' d' HLT. apply (rce_latch i r' m' d' HLT). intros Hsi r'' m'' d'' HOH'.
apply (IH (Datatypes.S i)); [lia | exact Hsi | exact HOH'].
Qed.

(* ---------- the entry: 0x89ef8 .. 0x89f98 ---------- *)
Lemma rce_aval_of_val_mem : forall segs H m0 x n v, val_mem segs (mrestrict H m0) x n v -> aval_mem (aview segs H m0) x n v.
Proof.
intros segs H m0 x n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia.
Qed.
Lemma rce_stack_field : forall E H mem' cs off v e,
region_ok SEGS E (mrestrict H mem') (YP09.mkRegion (Some 2%nat) (-144) 0 (-144) 0 cs) -> bv_unsigned (ew E 2) = spZ regs ->
In (YP09.mkChunk off (CVal 8 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
aval_mem (aview SEGS H mem') (spZ regs + off) 8 v.
Proof.
intros E H mem' cs off v e HR Hsp Hin He Hv. apply rce_aval_of_val_mem.
change 8%nat with (N.to_nat 8).
apply (field_of_region E _ 2 (spZ regs) cs (-144) 0 (-144) 0 off 8 e v HR Hsp Hin He).
- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Hv.
- cbn. lia.
Qed.
Lemma rce_entry_seed :
st_ok_pi SEGS VAL (Eimg (Ereg regs [w64 SB])) rce_ss_entry
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_rec_calls_equal)) mem (seg_rom SEGS)))
/\ sh_ok SEGS rce_Bx [] (Eimg (Ereg regs [w64 SB])) (mrestrict (w_H W) mem).
Proof.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & HQT).
pose proof rce_sp as (Hal16 & Hslo & Hshi). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HST : REC_CALLS_EQUAL_STK = 8336) by reflexivity.
set (E := Eimg (Ereg regs [w64 SB])).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Eimg_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E32 : ew E 32 = w64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_val_range (A_OBJ 0)) as R0. pose proof (pa_val_range (A_OBJ 12)) as R12.
assert (U241 : bv_unsigned (ew E (A_OBJ 0)) = VAL (A_OBJ 0)) by (rewrite E241; apply unsigned_lit_small; lia).
assert (U253 : bv_unsigned (ew E (A_OBJ 12)) = VAL (A_OBJ 12)) by (rewrite E253; apply unsigned_lit_small; lia).
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR. pose proof (pal_got_cell B TL) as HgcD.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
split; [|apply Forall_nil].
rewrite restrict_mkst_fx. unfold rce_ss_entry. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold stack_region, got_regionP, bcell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + rewrite U241. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
  + rewrite U253. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by (unfold SB; lia); reflexivity
      | unfold SB; cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
- apply pairwise_disjoint_of_extents. unfold stack_region, got_regionP, bcell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, U241, U253.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok, rce_spF, rce_SBF. cbn [af_lo af_hi af_al2].
  rewrite Usp, E32. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). change (2 ^ 4) with 16. rewrite Z.pow_0_r, Z.mod_1_r.
  repeat split; try lia; exact Hal16.
Qed.
Ltac rce_keep_win HFr K lo hi Usp :=
  lazymatch type of HFr with frame_of _ _ (mrestrict ?H ?m1) (mrestrict ?H ?m2) =>
  assert (K : kept_out (aview SEGS H m1) (aview SEGS H m2) lo hi)
  by (intros x0 Hx0 Hn0; apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun x => lo <= x < hi) HFr);
      [ intros b0 wlo whi a0 Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp in Hrr; lia|]); destruct Hin
      | exact Hx0 | exact Hn0 ]) end.
Lemma rce_entry : SRr SEGS W (cfg_at SEGS (BASE + AF_rec_calls_equal) regs mem md) rce_Q.
Proof.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & HQT).
pose proof rce_sp as (Hal16 & Hslo & Hshi). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HST : REC_CALLS_EQUAL_STK = 8336) by reflexivity.
pose proof HCA as (HlA & Ha8 & _). pose proof HCB as (HlB & Hb8 & _).
destruct rce_entry_seed as [HS SHOK].
pose proof (ajournal_init_na SEGS B REC_CALLS_EQUAL_STK [] ly S W regs mem md HPRE) as HJ.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs [w64 SB]))) by apply Eimg_env.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (Eimg (Ereg regs [w64 SB])) n = getr regs r)
  by (intros n r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew (Eimg (Ereg regs [w64 SB])) 32 = w64 SB) by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
remember (Eimg (Ereg regs [w64 SB])) as E eqn:HE. clear HE.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (U11 : U E (SOff 11 0) = Z.of_nat (length ca)) by (apply U_atom; [rewrite (EE 11%nat 11%bv eq_refl); exact H11 | lia]).
assert (U13 : U E (SOff 13 0) = Z.of_nat (length cb)) by (apply U_atom; [rewrite (EE 13%nat 13%bv eq_refl); exact H13 | lia]).
assert (E11 : ew E 11 = w64 (Z.of_nat (length ca))) by (rewrite (EE 11%nat 11%bv eq_refl); exact H11).
assert (FRM : forall H mem' cs, region_ok SEGS E (mrestrict H mem') (YP09.mkRegion (Some 2%nat) (-144) 0 (-144) 0 cs) ->
  (forall j r, nth_error rce_saved j = Some r -> In (YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (Z.to_nat r) 0))) cs) ->
  rce_frame (aview SEGS H mem')).
{ intros H mem' cs HR Hin j r Hr.
  assert (Hr' : 1 <= r <= 27) by (apply nth_error_In in Hr; cbn in Hr; intuition lia).
  replace (spZ regs - 8 - 8 * Z.of_nat j) with (spZ regs + (-8 - 8 * Z.of_nat j)) by lia.
  apply (rce_stack_field E H mem' cs _ _ (SOff (Z.to_nat r) 0)); [exact HR | exact Usp | exact (Hin j r Hr) | |
    pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HRr; change (bv_modulus 64) with (2 ^ 64) in HRr; exact HRr].
  cbn [sv_denot]. rewrite Z.add_0_r, !Z_to_bv_bv_unsigned.
  apply (EE (Z.to_nat r) (Z_to_bv 5 r)).
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia. }
unfold cfg_at. change (w64 (BASE + AF_rec_calls_equal)) with (Z_to_bv 64 (BASE + AF_rec_calls_equal)).
(* 0x89ef8 .. 0x89f34: the frame, b spilled to 32(sp), bne a1,a3 *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; exact Usp. }
rce_md.
rce_keep_win HFr KEEP0 (spZ regs - REC_CALLS_EQUAL_STK) (spZ regs) Usp. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* the counts differ: 0x8a120 returns 0 *)
  assert (HNE : length ca <> length cb).
  { intros Heq. rewrite branch_ne_U, U11, U13 in Hc. apply negb_true_iff, Z.eqb_neq in Hc. apply Hc. rewrite Heq. reflexivity. }
  paj_run_to_tok RUNTO HS HJ SHOK Bspan RCE_EPI.
  { awr_ok_tac; exact Usp. }
  rce_md.
  rce_keep_win HFr KEEP1 (spZ regs - REC_CALLS_EQUAL_STK) (spZ regs) Usp. clear HF HFr HG.
  pmkst HS.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
    let r := eval vm_compute in (nth 0 (ss_mem ssx) (stack_region 0)) in
    pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 0 r HS ltac:(vm_compute; reflexivity)) as HRg;
    cbn [ms_mem restrict] in HRg end.
  prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4. prreg HS (10%bv : bv 5) F10.
  apply (rce_epi 0); [| exact F10 | rewrite rce_calls_eqb_len by exact HNE; reflexivity].
  split; [exact HJ|]. split; [apply (kept_out_trans _ _ _ _ _ _ _ KEEP0 KEEP1); lia|].
  split.
  { apply (FRM _ _ _ HRg). intros j r Hr. do 13 (destruct j as [|j]; [cbn in Hr; injection Hr as <-; vm_compute; repeat first [left; reflexivity | right] |]).
    cbn in Hr; destruct j; discriminate Hr. }
  split; [rewrite F2, Usp; reflexivity|]. split; [rewrite F3; apply EE; reflexivity | rewrite F4; apply EE; reflexivity].
- assert (HEQ : length ca = length cb).
  { rewrite branch_ne_U, U11, U13 in Hc. apply negb_false_iff, Z.eqb_eq in Hc. lia. }
  clear Hc.
  (* 0x89f38 .. 0x89f40: a5 := a, a0 := 1, blez a1 *)
  paj_run_tok RUN HS HJ SHOK Bspan.
  { awr_ok_tac; exact Usp. }
  rce_md.
  rce_keep_win HFr KEEP1 (spZ regs - REC_CALLS_EQUAL_STK) (spZ regs) Usp. clear HF HFr HG.
  pose proof (kept_out_trans _ _ _ _ _ _ _ KEEP0 KEEP1 (Z.le_refl _) (Z.le_refl _)) as K01. clear KEEP0 KEEP1.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* no calls: 0x8a124 returns 1 *)
    assert (H0 : length ca = 0%nat).
    { rewrite (rce_bge0 E 11 (Z.of_nat (length ca)) E11) in Hc by lia. apply Z.leb_le in Hc. lia. }
    paj_run_to_tok RUNTO HS HJ SHOK Bspan RCE_EPI.
    { awr_ok_tac; exact Usp. }
    rce_md.
    rce_keep_win HFr KEEP2 (spZ regs - REC_CALLS_EQUAL_STK) (spZ regs) Usp. clear HF HFr HG.
    pmkst HS.
    lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
      let r := eval vm_compute in (nth 0 (ss_mem ssx) (stack_region 0)) in
      pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 0 r HS ltac:(vm_compute; reflexivity)) as HRg;
      cbn [ms_mem restrict] in HRg end.
    prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4. prreg HS (10%bv : bv 5) F10.
    apply (rce_epi 1); [| exact F10 |].
    * split; [exact HJ|]. split; [apply (kept_out_trans _ _ _ _ _ _ _ K01 KEEP2); lia|].
      split.
      { apply (FRM _ _ _ HRg). intros j r Hr. do 13 (destruct j as [|j]; [cbn in Hr; injection Hr as <-; vm_compute; repeat first [left; reflexivity | right] |]).
        cbn in Hr; destruct j; discriminate Hr. }
      split; [rewrite F2, Usp; reflexivity|]. split; [rewrite F3; apply EE; reflexivity | rewrite F4; apply EE; reflexivity].
    * rewrite rce_calls_eqb_true; [reflexivity | lia|]. intros j e f Hj. exfalso.
      assert (Hjl : (j < length ca)%nat) by (apply (proj1 (nth_error_Some ca j)); rewrite Hj; discriminate). lia.
  + (* calls: 0x89f44 .. 0x89f94, i := 0, the shadow base, the UBSan predicates spilled, the cursors, n spilled; the
       outer loop *)
    assert (H0 : (0 < length ca)%nat).
    { rewrite (rce_bge0 E 11 (Z.of_nat (length ca)) E11) in Hc by lia. apply Z.leb_gt in Hc. lia. }
    paj_run_to_tok RUNTO HS HJ SHOK Bspan RCE_OH.
    { awr_ok_tac; exact Usp. }
    rce_md.
    rce_keep_win HFr KEEP2 (spZ regs - REC_CALLS_EQUAL_STK) (spZ regs) Usp. clear HF HFr HG.
    pmkst HS.
    lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
      let r := eval vm_compute in (nth 0 (ss_mem ssx) (stack_region 0)) in
      pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 0 r HS ltac:(vm_compute; reflexivity)) as HRg;
      cbn [ms_mem restrict] in HRg end.
    prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (9%bv : bv 5) Q9.
    prreg HS (14%bv : bv 5) Q14. prreg HS (15%bv : bv 5) Q15. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
    prreg HS (23%bv : bv 5) Q23. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
    destruct (rce_tab a ca HCA H0) as (_ & Ha4 & Hah & _).
    destruct (rce_tab b cb HCB ltac:(lia)) as (_ & Hb4 & Hbh & _).
    assert (Ua : bv_unsigned (ew E 10) = a) by (rewrite (EE 10%nat 10%bv eq_refl), H10; apply unsigned_lit_small; lia).
    assert (Ub : bv_unsigned (ew E 12) = b) by (rewrite (EE 12%nat 12%bv eq_refl), H12; apply unsigned_lit_small; lia).
    assert (E10 : ew E 10 = Z_to_bv 64 a) by (rewrite (EE 10%nat 10%bv eq_refl), H10; reflexivity).
    assert (E12 : ew E 12 = Z_to_bv 64 b) by (rewrite (EE 12%nat 12%bv eq_refl), H12; reflexivity).
    apply (rce_loop_all (length ca) 0); [lia | exact H0|].
    split; [split|].
    * split; [exact HJ|]. split; [apply (kept_out_trans _ _ _ _ _ _ _ K01 KEEP2); lia|].
      split.
      { apply (FRM _ _ _ HRg). intros j r Hr. do 13 (destruct j as [|j]; [cbn in Hr; injection Hr as <-; vm_compute; repeat first [left; reflexivity | right] |]).
        cbn in Hr; destruct j; discriminate Hr. }
      split; [rewrite Q2, Usp; reflexivity|]. split; [rewrite Q3; apply EE; reflexivity | rewrite Q4; apply EE; reflexivity].
    * split; [exact H0|]. split; [lia|]. split; [intros j e f Hj; lia|].
      split.
      { (* the frame slots: n, the predicates of b (b <> 0, b mod 8 = 0) and a (a mod 8 = 0, rce_calls), b *)
        split; [replace (spZ regs - 144) with (spZ regs + -144) by lia;
          apply (rce_stack_field E _ _ _ (-144) _ (SOff 11 0) HRg Usp);
          [vm_compute; repeat first [left; reflexivity | right]
          | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact E11 | lia]|].
        split; [replace (spZ regs - 136) with (spZ regs + -136) by lia;
          apply (rce_stack_field E _ _ _ (-136) 1
            (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff 12 0) (SLit 7)) (SLit 1)) (SAlu ALU_SLTU (SLit 0) (SOff 12 0))) HRg Usp);
          [vm_compute; repeat first [left; reflexivity | right]
          | cbn [sv_denot]; rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned, E12; apply rce_flag; lia | lia]|].
        split; [replace (spZ regs - 128) with (spZ regs + -128) by lia;
          apply (rce_stack_field E _ _ _ (-128) 1 (SAlu ALU_SLTU (SLit 0) (SOff 12 0)) HRg Usp);
          [vm_compute; repeat first [left; reflexivity | right]
          | cbn [sv_denot]; rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned, E12; apply rce_sltu0; lia | lia]|].
        split; [replace (spZ regs - 120) with (spZ regs + -120) by lia;
          apply (rce_stack_field E _ _ _ (-120) 1
            (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff 10 0) (SLit 7)) (SLit 1)) (SAlu ALU_SLTU (SLit 0) (SOff 10 0))) HRg Usp);
          [vm_compute; repeat first [left; reflexivity | right]
          | cbn [sv_denot]; rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned, E10; apply rce_flag; lia | lia]|].
        replace (spZ regs - 112) with (spZ regs + -112) by lia.
        apply (rce_stack_field E _ _ _ (-112) _ (SOff 12 0) HRg Usp);
          [vm_compute; repeat first [left; reflexivity | right]
          | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact E12 | lia]. }
      split; [rewrite Q23, E32; reflexivity|]. split; [rewrite Q20; reflexivity|].
      split; [rewrite Q19, Ua; unfold w64; f_equal; lia|]. split; [rewrite Q26, Ua; unfold w64; f_equal; lia|].
      split; [rewrite Q9, Ub; unfold w64; f_equal; lia|]. rewrite Q25, Ub; unfold w64; f_equal; lia.
    * split; [rewrite Q15, E10; reflexivity|].
      rewrite Q14, E10. unfold w64. apply rce_sltu0. lia.
Qed.

End w.

Variable MT : ameter_ops.
Theorem trec_calls_equal_spec_holds : trec_calls_equal_spec B MT.
Proof.
unfold trec_calls_equal_spec. intros ly S W regs mem md a b ca cb HPRE HROD H10 H11 H12 H13 HCA HCB Hev.
exact (rce_entry ly S W regs mem md a b ca cb HPRE HROD H10 H11 H12 H13 HCA HCB).
Qed.


End e.
End d.
End b.
