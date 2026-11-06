(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v aj_intrin_at at 28fdc66416e (the call of
   __asan_memcpy in the journal) restated as hd_memcpy with the wrapper's same_but_materialized kept in the post as
   same_io, and proofs/reac-pw/fuzz_role/lib/A/RPgM02Base.v at 9e73ed57244 (m2_img_zone, m2_cstr_kept, the .rodata
   zone of m2_szone) restated as hd_img_zone / hd_cstr_kept / hd_szone for the .rodata range only; the rest of the
   file is new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgScanHead.v at cdde2c4d95b for
   reac-pw/fuzz_headamp image A: its start-fact record hd_c3 / hd_c3_of, its bounds lemma hd_bounds and its walk hd_A
   (a nonzero test of a block, a register move, a zero test of the length, the __asan_memcpy, its return) restated for
   headamp's segment M04a (C7 0x83744 -> C8 0x83764) as h4a_c7 / h4a_c7_of / h4a_bounds / h4a_copy over HPgSeg.hs_scx,
   with headamp's registers and real-frame cells; its helpers hd_getr_z, hd_reg_atom, hd_aview_some and hd_frame_ro
   taken renamed (h4a_); role's own memcpy step replaced by the shared lib/A/HPgIntrin.v hd_memcpy_at; the arm with
   no copy (h4a_zero), the extra-atom register lemma h4a_reg_at and the post construction h4a_close are new; role's
   parse step, .rodata zone and string lemmas are not taken (M04a calls no parse). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgM04a.v, with its module names changed; 490 of its 534 lines of code are new or changed and 425 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgScanInner.v at e39c26ea588 (role's "one
   turn of the inner scan", si_blk and rk_inner_A); module paths fuzz_role -> fuzz_headamp, the si_ / rk_ prefixes
   -> hs_ / hb_, role's code 0x821e0 .. 0x822a4 replaced by headamp's 0x830a0 .. 0x83164 (the same pod_next_pair
   turn with other registers: a3 = 104 at0, a4 = a5 = the entry table's moving base, a1 = that + 4, a2 = a6 = that
   + 8, t3 = n_ent - 1, s4 = m, s5 = m + 1, t4 = 8; the key's body goes to s2, not a0), the alias list restated for
   headamp's operand order, the exits ABS / I / KM replaced by HPgSegM's RC / SCAN / KEY, the cut rebuilt over
   HPgSegM's hq_cut_SCAN / hq_cut_KEY / hq_cut_RC and Pod/Headamp.v's fold. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address measured on the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, the same loaded bytes except .note.gnu.build-id): the piece "one turn of
   the scan" of the walk of LLVMFuzzerTestOneInput, lib/A/HPgSegM.v hq_piece_M3b_scan_stmt. Proves no function
   (kind: segment lemma).

   THE CODE (SCAN 0x830a0 .. 0x83164, the inlined pod_next_pair's loop with pod_string inlined, pod.h:90-96 and
   :134-142)
     0x830a0 .. 0x830b0  a7 := a3 + a5; the instrumented check of &ent[m].type (its slow block 0x8313c)
     0x830b4 .. 0x830bc  a7 := a4 + a3; lw t0,0(a7); bne t0,t4 (t4 = 8): not a String, to 0x83110
     0x830c0 .. 0x830d0  t0 := a3 + a1; the check of &ent[m].size (slow block 0x8314c)
     0x830d4 .. 0x830d8  lw a7,4(a7); beqz a7: size 0, to 0x83110
     0x830dc .. 0x830fc  a7 := zext32 (size - 1); t0 := a3 + a2 + a7; the check of &ent[m].body[size - 1] (slow
                         block 0x8315c)
     0x83100 .. 0x8310c  s2 := a6 + a3 (the body); lbu of body[size - 1]; beqz: a key, to 0x83114 with s2 = body
     0x83110             mv s2,zero: not a key
     0x83114             beq t3,s4 (t3 = n_ent - 1, s4 = m): the last entry starts no pair, to RC 0x83694
     0x83118 .. 0x83130  s4 := m + 1; addiw s5 := m + 2; the five bases a5, a6, a2, a1, a4 advance by 104
     0x83134             beqz s2: not a key, back to SCAN 0x830a0 with m + 1
     0x83138             j 0x83168: a key, to KEY
   with a3 = 104 at0, a4 = a5 = &ent[0] + 104 (m - at0), a1 = that + 4, a2 = a6 = that + 8, so that a3 + a5 is
   &ent[m] (Layout.ent_mem: type at +0, size at +4, body at +8). No store and no call: the turn writes no byte and
   changes no float register.

   HOW. hs_blk is the turn as a block lemma over the machine state at SCAN (lib/Reusable: the token engine YCbn.v,
   the journal YCbq.v), stated for any float state. Its entry state has the registers as atoms and six more atoms:
   A = &ent[m] (32), the type t (33), the size z (34), D = (z - 1) mod 2^32 (35), P = A + 8 + max (z - 1, 0) (36)
   and the byte lb at P (37). Alias facts make every address the code computes an atom plus a constant: a3 + a5
   and a4 + a3 are A, a3 + a1 is A + 4, a3 + a2 and a6 + a3 are A + 8, the zero extension of size - 1 is D, and
   (added once size <> 0 is known, when D = z - 1) A + D is P - 8. Two read-only regions hold the two words at A
   and the byte at P. The shadow base is s7 itself (atom 23, SHADOW_OFF), and the two shadow entries [A - 4,
   A + 108) and [P, P + 8) cover the 8 bytes from each check's address, so the engine reads each shadow byte as 0
   and decides each `bnez` not taken (the entries are paid from the pp block's shadow, HPgMem.hm_blk_ra). The engine
   splits the four branches it cannot decide (the type, the size, the last byte, m = n_ent - 1) and runs each arm
   to its end pc. The post is HPgM3bBase.hb_post (the journal, the memory and the 20 registers of hs_kept as at
   SCAN). hb_scan_A reads SCAN's cut, reads the three fields out of the pp block's image (HPgMem.hm_pp_ent), runs
   hs_blk at the run's own float state, and rebuilds the cut of the arm: RC (the entry is the last one: no pair is
   left, HPgM3bBase.hb_fold_last), SCAN at m + 1 (the entry is not a key) or KEY (the entry is a key: the three
   tests are Accessors.key_of's three conjuncts). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Model Layout Accessors Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Spa Cursor.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgSeg HPgSegM.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require HPgSteps HPgMem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgM3bBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Arguments x_STK {segs}. #[local] Arguments x_sp0 {segs}. #[local] Arguments x_FP {segs}.
#[local] Arguments x_ly {segs}. #[local] Arguments x_S {segs}. #[local] Arguments x_W0 {segs}.
#[local] Arguments x_mem0 {segs}. #[local] Arguments x_md0 {segs}. #[local] Arguments x_own {segs}.
#[local] Arguments x_k {segs}. #[local] Arguments x_regs {segs}. #[local] Arguments x_lyc {segs}.
#[local] Arguments x_Sc {segs}. #[local] Arguments x_W {segs}. #[local] Arguments x_memc {segs}.
#[local] Arguments x_mdc {segs}. #[local] Arguments x_RLO {segs}. #[local] Arguments x_RHI {segs}.
#[local] Arguments x_e {segs}. #[local] Arguments x_pos {segs}.

(* ================================ the code table and the entry state ================================ *)
(* the 50 words 0x830a0 .. 0x83164 (the three slow blocks included); the end pcs SCAN 0x830a0 is its first word,
   KEY 0x83168 and RC 0x83694 lie outside it *)
Definition hs_tbl : ctable := build_table rsegs HQ_SCAN 50 TEmpty.
Lemma hs_tbl_ok : table_ok rsegs hs_tbl.
Proof. apply build_table_ok0. unfold HQ_SCAN. lia. Qed.

(* the registers the turn does not write: all but t0, t1, a1, a2, a4, a5, a6, a7, s2, s4, s5 *)
Definition hs_kept : list (bv 5) :=
map (Z_to_bv 5) [1; 2; 3; 4; 7; 8; 9; 10; 13; 19; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31].

(* the shadow base: register s7 (atom 23) holds SHADOW_OFF *)
Definition HSSB : Z := 0x7fff8000.
Definition HSBx : sv := SOff 23 0.
Definition HSBspan : Z * Z := (HSSB, HSSB + 2 ^ 44 - 1).

(* the two read-only regions: the type and size words at A (atom 32), the byte at P (atom 36) *)
Definition hs_R1 : YP09.region := YP09.mkRegion (Some 32%nat) 0 8 0 0
  [YP09.mkChunk 0 (CVal 4 (SOff 33 0)); YP09.mkChunk 4 (CVal 4 (SOff 34 0))].
Definition hs_R2 : YP09.region := YP09.mkRegion (Some 36%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 37 0))].
(* the zero extension of size - 1, in the form the engine builds for 0x830dc .. 0x830e4 *)
Definition hs_zx : sv :=
  SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL (SOff 34 0) (SLit 32)) (SLit (-4294967296))) (SLit 32).
Definition hs_alias : list (sv * sv) :=
  [ (SAlu ALU_ADD (SOff 13 0) (SOff 15 0), SOff 32 0);
    (SAlu ALU_ADD (SOff 14 0) (SOff 13 0), SOff 32 0);
    (SAlu ALU_ADD (SOff 13 0) (SOff 11 0), SOff 32 4);
    (SAlu ALU_ADD (SOff 13 0) (SOff 12 0), SOff 32 8);
    (SAlu ALU_ADD (SOff 16 0) (SOff 13 0), SOff 32 8);
    (hs_zx, SOff 35 0) ].
(* added once size <> 0 is known *)
Definition hs_aP : sv := SAlu ALU_ADD (SOff 32 0) (SOff 35 0).
Definition hs_aP' : sv := SOff 36 (-8).
Definition hs_facts : facts :=
  mkFacts [ (23%nat, mkAF HSSB HSSB 0); (32%nat, mkAF 0x4014 (2 ^ 47 - 0x200) 0);
            (33%nat, mkAF 0 (2 ^ 32 - 1) 0); (34%nat, mkAF 0 45 0); (35%nat, mkAF 0 (2 ^ 32 - 1) 0);
            (36%nat, mkAF 0x401c (2 ^ 47 - 0x100) 0); (37%nat, mkAF 0 255 0); (21%nat, mkAF 1 32 0) ]
          [] hs_alias.
Definition hs_ss0 : sstate := mkSS HQ_SCAN sr_atoms [hs_R1; hs_R2] None hs_facts.
Definition hs_SH : list shent := [mkSHE 32 (-4) 108; mkSHE 36 0 8].
(* the six atoms after the registers *)
Definition hs_D (z : Z) : Z := (z - 1) mod 2 ^ 32.
Definition hs_P (A z : Z) : Z := A + 8 + Z.of_nat (Z.to_nat (z - 1)).
Definition hs_extra (A t z lb : Z) : list word :=
  [w64 A; w64 t; w64 z; w64 (hs_D z); w64 (hs_P A z); w64 lb].
(* the three tests of pod_string *)
Definition hs_key (t z lb : Z) : bool := (t =? 8) && (1 <=? z) && (lb =? 0).

(* ================================ arithmetic ================================ *)
Lemma hs_zx_U : forall E z, ew E 34 = Z_to_bv 64 z -> 0 <= z <= 45 -> U E hs_zx = hs_D z.
Proof.
intros E z H Hz. unfold hs_zx, hs_D.
rewrite !U_SAlu, !U_SLit, (U_atom E 34 z H) by lia. cbn [zalu_raw].
rewrite (zcanon_id 32) by (unfold M64; lia). change (Z.land 32 63) with 32.
rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
unfold zcanon, M64. change (-4294967296 mod 2 ^ 64) with (2 ^ 64 - 2 ^ 32).
rewrite (Z.mod_small (z * 2 ^ 32)) by lia.
destruct (Z.eq_dec z 0) as [->|Hz0]; [reflexivity|].
replace (z * 2 ^ 32 + (2 ^ 64 - 2 ^ 32)) with ((z - 1) * 2 ^ 32 + 1 * 2 ^ 64) by ring.
rewrite Z.mod_add by lia. rewrite (Z.mod_small ((z - 1) * 2 ^ 32)) by lia. rewrite Z.div_mul by lia.
rewrite (Z.mod_small (z - 1) (2 ^ 32)) by lia. apply Z.mod_small. lia.
Qed.

Lemma hs_sext_U : forall E t, ew E 33 = Z_to_bv 64 t -> 0 <= t < 2 ^ 32 ->
(U E (SExt true 32 (SOff 33 0)) =? 8) = (t =? 8).
Proof.
intros E t H Ht. rewrite U_SExt, (U_atom E 33 t H) by lia. cbv iota.
change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small t) by lia.
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
unfold zcanon, M64.
destruct (Z.ltb_spec t (2 ^ 31)) as [Hl|Hg].
- rewrite (Z.mod_small (t + 2 ^ 31)) by lia. replace (t + 2 ^ 31 - 2 ^ 31) with t by lia.
  rewrite Z.mod_small by lia. reflexivity.
- replace (t + 2 ^ 31) with ((t + 2 ^ 31 - 2 ^ 32) + 1 * 2 ^ 32) by ring.
  rewrite Z.mod_add by lia. rewrite (Z.mod_small (t + 2 ^ 31 - 2 ^ 32)) by lia.
  replace (t + 2 ^ 31 - 2 ^ 32 - 2 ^ 31) with ((t + 2 ^ 64 - 2 ^ 32) + (-1) * 2 ^ 64) by ring.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
  destruct (Z.eqb_spec (t + 2 ^ 64 - 2 ^ 32) 8); [lia|]. destruct (Z.eqb_spec t 8); [lia | reflexivity].
Qed.

Lemma hs_soff : forall E (n : nat) v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
sv_denot E (SOff n c) = w64 (v + c).
Proof. intros E n v c H Hv Hc. rewrite denot_lit_U, (U_atom_off E n v c H Hv Hc). reflexivity. Qed.

(* ================================ the entry's bytes ================================ *)
Lemma hs_firstn4 : forall (a b : list byte), length a = 4%nat -> firstn 4 (a ++ b) = a.
Proof. intros a b H. rewrite firstn_app, H, Nat.sub_diag, firstn_O, app_nil_r. apply firstn_all2. lia. Qed.
Lemma hs_slice_type : forall e, HPgMem.hm_slice (ent_mem e) 0 4 = Z_to_le_bytes 4 (e_type e).
Proof. intros e. unfold HPgMem.hm_slice, ent_mem. cbn [skipn]. apply hs_firstn4. apply Cursor.length_le32. Qed.
Lemma hs_slice_size : forall e, HPgMem.hm_slice (ent_mem e) 4 4 = Z_to_le_bytes 4 (e_size e).
Proof.
intros e. unfold HPgMem.hm_slice, ent_mem. rewrite skipn_app, Cursor.length_le32, Nat.sub_diag, skipn_O.
rewrite skipn_all2 by (rewrite Cursor.length_le32; lia). cbn [app]. apply hs_firstn4. apply Cursor.length_le32.
Qed.
Lemma hs_nth_zeros : forall (l : list byte) n k, nth k (l ++ Cursor.zeros n) Cursor.NUL = nth k l Cursor.NUL.
Proof.
intros l n k. destruct (Nat.lt_ge_cases k (length l)) as [Hk|Hk].
- apply app_nth1. exact Hk.
- rewrite app_nth2 by exact Hk. rewrite (nth_overflow l) by exact Hk. unfold Cursor.zeros. apply nth_repeat.
Qed.
Lemma hs_nth_body : forall e k, nth (8 + k) (ent_mem e) (Z_to_bv 8 0) = nth k (e_body e) Cursor.NUL.
Proof.
intros e k. change (Z_to_bv 8 0) with Cursor.NUL. unfold ent_mem.
rewrite app_nth2 by (rewrite Cursor.length_le32; lia). rewrite Cursor.length_le32.
rewrite app_nth2 by (rewrite Cursor.length_le32; lia). rewrite Cursor.length_le32.
replace (8 + k - 4 - 4)%nat with k by lia. apply hs_nth_zeros.
Qed.

(* ================================ the run tactics ================================ *)
Ltac hs_run := lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  aj_run_tok hs_tbl_ok HS HJ SHOK HSBspan; [awr_ok_tac | ] end.
Ltac hs_run_to pc := lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  aj_run_to_tok hs_tbl_ok HS HJ SHOK HSBspan pc; [awr_ok_tac | ] end.
Ltac hs_branch Hc := lazymatch goal with HS : st_ok _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  srr_branch_tok hs_tbl_ok HS SHOK HSBspan end;
  lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.

(* what the back edge computes *)
Definition hs_I_R (regs : bvmap 5 word) (A x j : Z) (regs2 : bvmap 5 word) : Prop :=
getr regs2 (Z_to_bv 5 13) = getr regs (Z_to_bv 5 13) /\
getr regs2 (Z_to_bv 5 20) = w64 (j + 1) /\ getr regs2 (Z_to_bv 5 21) = w64 (j + 2) /\
getr regs2 (Z_to_bv 5 15) = w64 (A - x + 104) /\ getr regs2 (Z_to_bv 5 14) = w64 (A - x + 104) /\
getr regs2 (Z_to_bv 5 11) = w64 (A + 4 - x + 104) /\ getr regs2 (Z_to_bv 5 12) = w64 (A + 8 - x + 104) /\
getr regs2 (Z_to_bv 5 16) = w64 (A + 8 - x + 104).
(* what the exit to KEY computes *)
Definition hs_KM_R (A j : Z) (regs2 : bvmap 5 word) : Prop :=
getr regs2 (Z_to_bv 5 18) = w64 (A + 8) /\ getr regs2 (Z_to_bv 5 20) = w64 (j + 1) /\
getr regs2 (Z_to_bv 5 21) = w64 (j + 2).

(* the leaves of the run tree (used inside hs_blk only: they name its hypotheses) *)
(* a register the arm advanced: SOff n c over the atom n, whose value En gives *)
Ltac hs_adv :=
hb_sv;
lazymatch goal with |- sv_denot _ (SOff ?n ?c) = w64 ?v =>
  lazymatch goal with En : ew _ n = Z_to_bv 64 ?v0 |- _ =>
    rewrite (hs_soff _ n v0 c En) by lia; unfold w64; f_equal; lia end end.
Ltac hs_post_intro := hb_post_intro B hs_kept.
(* the `beq t3,s4` at 0x83114, then the arm's end *)
Ltac hs_abs Hl :=
hs_run_to HQ_RC; hb_mem; apply SRr_ret; left;
split; [apply Z.eqb_eq in Hl; exact Hl|];
hs_post_intro; exact I.
Ltac hs_Ileaf Hk Hl :=
hs_run_to HQ_SCAN; hb_mem; apply SRr_ret; right; left;
split; [apply Z.eqb_neq in Hl; exact Hl|];
split; [exact Hk|];
hs_post_intro;
lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms) |- _ =>
  unfold hs_I_R; rewrite !(st_ok_restrict_reg rsegs _ E' ss' ms _ HS) end;
split; [hb_sv; rewrite hb_denot0; lazymatch goal with E13 : ew _ 13 = _, H13 : getr _ (Z_to_bv 5 13) = _ |- _ =>
  rewrite E13, H13; reflexivity end|];
repeat split; hs_adv.
Ltac hs_KMleaf Hk Hl :=
hs_run_to HQ_KEY; hb_mem; apply SRr_ret; right; right;
split; [apply Z.eqb_neq in Hl; exact Hl|];
split; [exact Hk|];
hs_post_intro;
lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms) |- _ =>
  unfold hs_KM_R; rewrite !(st_ok_restrict_reg rsegs _ E' ss' ms _ HS) end;
repeat split; hs_adv.
Ltac hs_last Hl :=
hs_branch Hl;
lazymatch goal with E28 : ew ?E 28 = Z_to_bv 64 ?n, E20 : ew ?E 20 = Z_to_bv 64 ?j |- _ =>
  rewrite branch_eq_U, (U_atom E 28 n E28), (U_atom E 20 j E20) in Hl by lia end.
(* an entry that is not a key: 0x83110 s2 := 0, then the `beq` *)
Ltac hs_nk Hk := hs_run; hb_mem; let Hl := fresh "Hl" in hs_last Hl; [hs_abs Hl | hs_Ileaf Hk Hl].

Lemma hs_blk : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(x A t z lb j nm1 : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 13) = w64 x ->
getr regs (Z_to_bv 5 15) = w64 (A - x) -> getr regs (Z_to_bv 5 14) = w64 (A - x) ->
getr regs (Z_to_bv 5 11) = w64 (A + 4 - x) ->
getr regs (Z_to_bv 5 12) = w64 (A + 8 - x) -> getr regs (Z_to_bv 5 16) = w64 (A + 8 - x) ->
getr regs (Z_to_bv 5 20) = w64 j -> getr regs (Z_to_bv 5 21) = w64 (j + 1) ->
getr regs (Z_to_bv 5 28) = w64 nm1 -> getr regs (Z_to_bv 5 29) = w64 8 ->
getr regs (Z_to_bv 5 23) = w64 SHADOW_OFF ->
0 <= x <= A -> 0x4014 <= A <= 2 ^ 47 - 0x200 -> 0 <= t < 2 ^ 32 -> 0 <= z <= 45 -> 0 <= lb < 256 ->
0 <= j <= 31 -> 0 <= nm1 <= 31 ->
val_mem rsegs (mrestrict (w_H W) memc) A 4 t ->
val_mem rsegs (mrestrict (w_H W) memc) (A + 4) 4 z ->
val_mem rsegs (mrestrict (w_H W) memc) (hs_P A z) 1 lb ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF (A - 4) 112 ->
(forall a, A - 4 <= a < A + 108 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)) ->
SRr rsegs W (cfg_at rsegs HQ_SCAN regs memc mdc)
(fun W2 c2 =>
 (nm1 = j /\ hb_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HQ_RC hs_kept (fun _ => True) W2 c2) \/
 (nm1 <> j /\ hs_key t z lb = false /\
  hb_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HQ_SCAN hs_kept (hs_I_R regs A x j) W2 c2) \/
 (nm1 <> j /\ hs_key t z lb = true /\
  hb_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HQ_KEY hs_kept (hs_KM_R A j) W2 c2)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs x A t z lb j nm1 HJ
  H13 H15 H14 H11 H12 H16 H20 H21 H28 H29 H23 Hx HA Ht Hz Hlb Hj Hn Vt Vz Vb HRA Happ.
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
remember (hs_extra A t z lb) as ex eqn:Hex.
assert (EA : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (Ereg regs ex) n = getr regs r)
  by (intros n r Hr; exact (ew_Ereg_nat regs _ n r Hr)).
assert (E13 : ew (Ereg regs ex) 13 = Z_to_bv 64 x) by (rewrite (EA 13%nat (Z_to_bv 5 13) eq_refl); exact H13).
assert (E15 : ew (Ereg regs ex) 15 = Z_to_bv 64 (A - x)) by (rewrite (EA 15%nat (Z_to_bv 5 15) eq_refl); exact H15).
assert (E14 : ew (Ereg regs ex) 14 = Z_to_bv 64 (A - x)) by (rewrite (EA 14%nat (Z_to_bv 5 14) eq_refl); exact H14).
assert (E11 : ew (Ereg regs ex) 11 = Z_to_bv 64 (A + 4 - x)) by (rewrite (EA 11%nat (Z_to_bv 5 11) eq_refl); exact H11).
assert (E12 : ew (Ereg regs ex) 12 = Z_to_bv 64 (A + 8 - x)) by (rewrite (EA 12%nat (Z_to_bv 5 12) eq_refl); exact H12).
assert (E16 : ew (Ereg regs ex) 16 = Z_to_bv 64 (A + 8 - x)) by (rewrite (EA 16%nat (Z_to_bv 5 16) eq_refl); exact H16).
assert (E20 : ew (Ereg regs ex) 20 = Z_to_bv 64 j) by (rewrite (EA 20%nat (Z_to_bv 5 20) eq_refl); exact H20).
assert (E21 : ew (Ereg regs ex) 21 = Z_to_bv 64 (j + 1)) by (rewrite (EA 21%nat (Z_to_bv 5 21) eq_refl); exact H21).
assert (E28 : ew (Ereg regs ex) 28 = Z_to_bv 64 nm1) by (rewrite (EA 28%nat (Z_to_bv 5 28) eq_refl); exact H28).
assert (E29 : ew (Ereg regs ex) 29 = Z_to_bv 64 8) by (rewrite (EA 29%nat (Z_to_bv 5 29) eq_refl); exact H29).
assert (E23 : ew (Ereg regs ex) 23 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EA 23%nat (Z_to_bv 5 23) eq_refl); exact H23).
assert (E32 : ew (Ereg regs ex) 32 = Z_to_bv 64 A) by (subst ex; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew (Ereg regs ex) 33 = Z_to_bv 64 t) by (subst ex; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew (Ereg regs ex) 34 = Z_to_bv 64 z) by (subst ex; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew (Ereg regs ex) 35 = Z_to_bv 64 (hs_D z)) by (subst ex; exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew (Ereg regs ex) 36 = Z_to_bv 64 (hs_P A z)) by (subst ex; exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew (Ereg regs ex) 37 = Z_to_bv 64 lb) by (subst ex; exact (ew_Ereg_extra regs _ 5)).
assert (HD : 0 <= hs_D z < 2 ^ 32) by (unfold hs_D; apply Z.mod_pos_bound; lia).
assert (HP : A + 8 <= hs_P A z <= A + 52) by (unfold hs_P; lia).
assert (HS : st_ok rsegs (Ereg regs ex) hs_ss0 (restrict (w_H W) (mkst regs (Z_to_bv 64 HQ_SCAN) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold hs_ss0. apply entry_st_ok_full.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold hs_R1, hs_R2. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite E32, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val rsegs _ _ A 0 4 (SOff 33 0) t); [rewrite hb_denot0; exact E33 | cbn; lia | cbn; lia |].
        rewrite Z.add_0_r. exact Vt.
      * apply (chunk_ok_val rsegs _ _ A 4 4 (SOff 34 0) z); [rewrite hb_denot0; exact E34 | cbn; lia | cbn; lia |].
        exact Vz.
    + rewrite E36, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val rsegs _ _ (hs_P A z) 0 1 (SOff 37 0) lb); [rewrite hb_denot0; exact E37 | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact Vb.
  - cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; exact I].
    unfold extent_disjoint, hs_R1, hs_R2. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite E32, E36, !unsigned_lit_small by lia. left. lia.
  - split; [|split; [exact I|]].
    + cbn [hs_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E23, E32, E33, E34, E35, E36, E37, E21, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 0) with 1. rewrite !Z.mod_1_r. unfold HSSB, SHADOW_OFF. repeat split; lia.
    + cbn [hs_facts f_alias alias_ok hs_alias]. unfold hs_zx.
      repeat split; apply U_inj.
      * rewrite U_SAlu, (U_atom _ 13 x E13), (U_atom _ 15 (A - x) E15), (U_atom _ 32 A E32) by lia.
        cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia). lia.
      * rewrite U_SAlu, (U_atom _ 14 (A - x) E14), (U_atom _ 13 x E13), (U_atom _ 32 A E32) by lia.
        cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia). lia.
      * rewrite U_SAlu, (U_atom _ 13 x E13), (U_atom _ 11 (A + 4 - x) E11), (U_atom_off _ 32 A 4 E32) by lia.
        cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia). lia.
      * rewrite U_SAlu, (U_atom _ 13 x E13), (U_atom _ 12 (A + 8 - x) E12), (U_atom_off _ 32 A 8 E32) by lia.
        cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia). lia.
      * rewrite U_SAlu, (U_atom _ 16 (A + 8 - x) E16), (U_atom _ 13 x E13), (U_atom_off _ 32 A 8 E32) by lia.
        cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia). lia.
      * fold hs_zx. rewrite (hs_zx_U _ z E34 Hz), (U_atom _ 35 (hs_D z) E35) by lia. reflexivity. }
assert (U23 : U (Ereg regs ex) HSBx = SHADOW_OFF) by (apply U_atom; [exact E23 | unfold SHADOW_OFF; lia]).
assert (SHOK : sh_ok rsegs HSBx hs_SH (Ereg regs ex) (mrestrict (w_H W) memc)).
{ unfold sh_ok, hs_SH. constructor; [|constructor; [|constructor]].
  - apply (shent_ok_of_range rsegs (w_H W) memc _ HSBx 32 (A - 4) 112 A (-4) 108 HRA U23); [| lia | lia |].
    + apply U_atom; [exact E32 | lia].
    + intros a Ha. rewrite Z.min_l, Z.max_r in Ha by lia. apply Happ. lia.
  - apply (shent_ok_of_range rsegs (w_H W) memc _ HSBx 36 (A - 4) 112 (hs_P A z) 0 8 HRA U23); [| lia | lia |].
    + apply U_atom; [exact E36 | lia].
    + intros a Ha. rewrite Z.min_l, Z.max_r in Ha by lia. apply Happ. lia. }
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE EA Hex.
unfold cfg_at. change (w64 HQ_SCAN) with (Z_to_bv 64 HQ_SCAN).
(* 0x830a0 .. 0x830b8: the type's check and load; stop at 0x830bc bne t0,t4 *)
hs_run. hb_mem.
hs_branch Hty; rewrite branch_ne_U, (U_atom E 29 8 E29), (hs_sext_U E t E33 Ht) in Hty by lia.
- (* taken: not a String *)
  apply negb_true_iff in Hty.
  assert (Hk : hs_key t z lb = false) by (unfold hs_key; rewrite Hty; reflexivity).
  hs_nk Hk.
- (* the type is 8: 0x830c0 .. 0x830d4, the size's check and load; stop at 0x830d8 beqz a7 *)
  apply negb_false_iff in Hty.
  hs_run. hb_mem.
  hs_branch Hsz; rewrite branch_eq_U, (U_atom E 34 z E34), (U_lit E 0) in Hsz by lia.
  + (* size 0: not a key *)
    assert (Hk : hs_key t z lb = false).
    { unfold hs_key. replace (1 <=? z) with false by (symmetry; apply Z.leb_gt; apply Z.eqb_eq in Hsz; lia).
      rewrite andb_false_r. reflexivity. }
    hs_nk Hk.
  + (* size >= 1: A + D is P - 8; 0x830dc .. 0x83108, the last byte's check and load; stop at 0x8310c beqz a7 *)
    apply Z.eqb_neq in Hsz.
    assert (HaP : sv_denot E hs_aP = sv_denot E hs_aP').
    { apply U_inj. unfold hs_aP, hs_aP'.
      rewrite U_SAlu, (U_atom E 32 A E32), (U_atom E 35 (hs_D z) E35), (U_atom_off E 36 (hs_P A z) (-8) E36) by lia.
      cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia).
      unfold hs_D, hs_P. rewrite (Z.mod_small (z - 1) (2 ^ 32)) by lia. lia. }
    pose proof (st_ok_add_alias rsegs E _ _ hs_aP hs_aP' HS HaP) as HS'. clear HS. rename HS' into HS.
    hs_run. hb_mem.
    hs_branch Hb; rewrite branch_eq_U, (U_atom E 37 lb E37), (U_lit E 0) in Hb by lia.
    * (* the byte is NUL: a key; 0x83114 beq t3,s4 *)
      assert (Hk : hs_key t z lb = true).
      { unfold hs_key. rewrite Hty, Hb. replace (1 <=? z) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
      hs_run. hb_mem.
      let Hl := fresh "Hl" in hs_last Hl; [hs_abs Hl | hs_KMleaf Hk Hl].
    * (* not a key *)
      assert (Hk : hs_key t z lb = false) by (unfold hs_key; rewrite Hb, andb_false_r; reflexivity).
      hs_nk Hk.
Qed.

End d.
End b.

(* ================================ the cuts ================================ *)
Lemma hs_key_of : forall e, key_of e = if hs_key (e_type e) (e_size e) (last_body_byte e) then Some (Cursor.cstr (e_body e)) else None.
Proof. intros e. reflexivity. Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

Theorem hb_scan_A : hq_piece_M3b_scan_stmt rsegs B MT.
Proof.
unfold hq_piece_M3b_scan_stmt. intros cx POST r ev at0 m HS HSC HKEY HRC.
unfold hq_from_SCAN. intros fx2 ly2 S2 W2 regs2 mem2 md2 cs keys rf Hcut.
pose proof Hcut as (Hb3 & Hat & Hf1 & Hf2 & Hlive & [Hat0 Hm] & Hrun & Hx & Hfold).
pose proof Hb3 as (Hcore & _ & _ & _ & Hpp & _).
pose proof Hcore as (HJ & _ & _ & Hperm & _).
pose proof (hb_start_wf B cx r ev HS) as Hwf.
pose proof (hb_start_pp B cx r ev HS) as (Hppin & Hal16 & Hp4k & Hpc & Hceil).
(* the pp block at the cut: its place and its shadow *)
pose proof (Permutation_in _ (Permutation_sym Hperm) Hppin) as Hin2.
pose proof HJ as (HAR & _).
pose proof (al_blocks rsegs B (AR_laws_ok rsegs B) ly2 S2 W2 mem2 md2 _ _ HAR Hin2) as (_ & _ & _ & Happ & _).
assert (Hrq : req_size PP_SIZE = PP_SIZE) by reflexivity. rewrite Hrq in Happ.
unfold PP_SIZE in Hpc, Happ.
(* entry m of the record *)
pose proof (proj1 (ents_wf r Hwf)) as Hn32.
pose proof (proj2 (ents_wf r Hwf)) as Hews.
assert (Hewm : ent_wf (nth m (ents r) (Ent 0 0 []))).
{ rewrite Forall_forall in Hews. apply Hews. apply nth_In. exact Hm. }
destruct Hewm as (Htw & Hbl & Hzw).
assert (Hb : Z.of_nat (length (buf r)) <= POD_BUF_MAX)
  by (pose proof (Spa.buf_header r Hwf) as (_ & _ & _ & HL); unfold POD_BUF_MAX; lia).
assert (Hs : Forall (fun e => (length (e_body e) <= 96)%nat) (ents r)).
{ eapply Forall_impl; [|exact Hews]. intros e (_ & He & Hz). lia. }
pose proof (HPgMem.hm_pp_ent rsegs (buf r) (is_props r) (has_params r) (params_struct r) (ents r) (corrupt r)
  Hb Hn32 Hs (w_H W2) mem2 (e_pp (x_e cx)) m Hpp Hm) as Hent.
pose proof (length_ent_mem (nth m (ents r) (Ent 0 0 [])) ltac:(lia)) as HL104.
pose proof (HPgMem.hm_bytes_field rsegs _ _ _ _ 0 4 _ Hent (hs_slice_type _) ltac:(lia)) as Vt.
pose proof (HPgMem.hm_bytes_field rsegs _ _ _ _ 4 4 _ Hent (hs_slice_size _) ltac:(lia)) as Vz.
pose proof (HPgMem.hm_bytes_byte rsegs _ _ _ _ (8 + Z.to_nat (e_size (nth m (ents r) (Ent 0 0 [])) - 1)) Hent
  ltac:(lia)) as Vb.
rewrite hs_nth_body in Vb.
set (A := e_pp (x_e cx) + 0x4014 + 104 * Z.of_nat m).
replace (e_pp (x_e cx) + (OFF_ENT + ENT_SIZE * Z.of_nat m) + Z.of_nat 0) with A in Vt
  by (unfold A, OFF_ENT, ENT_SIZE; lia).
replace (e_pp (x_e cx) + (OFF_ENT + ENT_SIZE * Z.of_nat m) + Z.of_nat 4) with (A + 4) in Vz
  by (unfold A, OFF_ENT, ENT_SIZE; lia).
replace (e_pp (x_e cx) + (OFF_ENT + ENT_SIZE * Z.of_nat m) + Z.of_nat (8 + Z.to_nat (e_size (nth m (ents r) (Ent 0 0 [])) - 1)))
  with (hs_P A (e_size (nth m (ents r) (Ent 0 0 [])))) in Vb by (unfold A, hs_P, OFF_ENT, ENT_SIZE; lia).
assert (HRA : range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (A - 4) 112).
{ apply (proj1 (HPgMem.hm_blk_ra rsegs B ly2 S2 W2 mem2 md2 (e_pp (x_e cx)) PP_SIZE (A - 4) 112 HAR Hin2
    ltac:(unfold A; lia) ltac:(rewrite Hrq; unfold A, PP_SIZE; lia))). }
(* the registers at SCAN *)
unfold hs_at_cx in Hat.
pose proof (hb_at_get _ _ _ _ _ 13 (104 * Z.of_nat at0) Hat ltac:(hb_in)) as R13.
pose proof (hb_at_get _ _ _ _ _ 15 (e_pp (x_e cx) + HQ_ENT0 + 104 * (Z.of_nat m - Z.of_nat at0)) Hat ltac:(hb_in)) as R15.
pose proof (hb_at_get _ _ _ _ _ 14 (e_pp (x_e cx) + HQ_ENT0 + 104 * (Z.of_nat m - Z.of_nat at0)) Hat ltac:(hb_in)) as R14.
pose proof (hb_at_get _ _ _ _ _ 11 (e_pp (x_e cx) + HQ_ENT_SZ + 104 * (Z.of_nat m - Z.of_nat at0)) Hat ltac:(hb_in)) as R11.
pose proof (hb_at_get _ _ _ _ _ 12 (e_pp (x_e cx) + HQ_ENT_BODY + 104 * (Z.of_nat m - Z.of_nat at0)) Hat ltac:(hb_in)) as R12.
pose proof (hb_at_get _ _ _ _ _ 16 (e_pp (x_e cx) + HQ_ENT_BODY + 104 * (Z.of_nat m - Z.of_nat at0)) Hat ltac:(hb_in)) as R16.
pose proof (hb_at_get _ _ _ _ _ 20 (Z.of_nat m) Hat ltac:(hb_in)) as R20.
pose proof (hb_at_get _ _ _ _ _ 21 (Z.of_nat m + 1) Hat ltac:(hb_in)) as R21.
pose proof (hb_at_get _ _ _ _ _ 28 (hq_nent r - 1) Hat ltac:(hb_in)) as R28.
pose proof (hb_at_get _ _ _ _ _ 29 8 Hat ltac:(hb_in)) as R29.
pose proof (hb_at_get _ _ _ _ _ 23 SHADOW_OFF Hat ltac:(hb_in)) as R23.
assert (Hat' : hs_at rsegs (w_H W2) mem2 regs2 (x_e cx)
  (hq_L_seg rsegs cx ++ hq_L_loopc rsegs cx ++ hq_L_loopr rsegs cx ++
   [(LReg 13, 104 * Z.of_nat at0); (LReg 7, hq_nent r); (LReg 28, hq_nent r - 1)])) by hb_sub Hat.
unfold hq_nent in R28.
(* the turn *)
eapply SRr_bind.
{ apply (hs_blk (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 (104 * Z.of_nat at0) A
    (e_type (nth m (ents r) (Ent 0 0 []))) (e_size (nth m (ents r) (Ent 0 0 [])))
    (last_body_byte (nth m (ents r) (Ent 0 0 []))) (Z.of_nat m) (Z.of_nat (length (ents r)) - 1) HJ R13);
  try (rewrite ?R15, ?R14, ?R11, ?R12, ?R16; unfold w64, A, HQ_ENT0, HQ_ENT_SZ, HQ_ENT_BODY; f_equal; lia);
  try assumption; try (unfold A; lia).
  - apply HPgMem.hm_byte_range.
  - intros a Ha. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, A in *. lia. }
intros W3 c3 _ [(Hl & -> & regs3 & md3 & -> & HJ3 & Hio3 & Hk3 & _)
  | [(Hl & Hkey & -> & regs3 & md3 & -> & HJ3 & Hio3 & Hk3 & HR) | (Hl & Hkey & -> & regs3 & md3 & -> & HJ3 & Hio3 & Hk3 & HR)]].
- (* RC: entry m is the last one, no pair is left *)
  destruct (hb_fold_last cx r at0 m cs keys rf Hfold Hat0 Hm ltac:(lia) Hrun) as (-> & -> & ->).
  pose proof (hb_at_keep _ _ _ _ _ Hat' regs3 hs_kept Hk3 ltac:(vm_compute; reflexivity)) as Hat3.
  apply (HRC fx2 ly2 S2 W2 regs3 mem2 md3).
  split.
  { apply (hb_base3_regs B MT cx fx2 r hq_shX ly2 S2 W2 regs2 mem2 md2 regs3 md3 Hb3 HJ3 Hio3).
    intros q Hq. destruct Hq as [->|[->| ->]]; apply Hk3; unfold hs_kept; hb_kin. }
  split; [unfold hs_at_cx; hb_sub Hat3|].
  split; [exact (proj1 (proj2 Hlive))|].
  split; [exact (hb_exp_rc cx r Hlive) | exact Hx].
- (* SCAN at m + 1: entry m is not a key *)
  destruct HR as (Q13 & Q20 & Q21 & Q15 & Q14 & Q11 & Q12 & Q16).
  assert (Hk : key_of (nth m (ents r) (Ent 0 0 [])) = None) by (rewrite hs_key_of, Hkey; reflexivity).
  pose proof (hb_at_keep _ _ _ _ _ Hat' regs3 hs_kept Hk3 ltac:(vm_compute; reflexivity)) as Hat3.
  apply (HSC fx2 ly2 S2 W2 regs3 mem2 md3 cs keys rf).
  split.
  { apply (hb_base3_regs B MT cx fx2 r hq_shX ly2 S2 W2 regs2 mem2 md2 regs3 md3 Hb3 HJ3 Hio3).
    intros q Hq. destruct Hq as [->|[->| ->]]; apply Hk3; unfold hs_kept; hb_kin. }
  split.
  { unfold hs_at_cx. apply hb_at_app; split; [hb_sub Hat3|].
    apply hb_at_app; split; [hb_sub Hat3|].
    apply hb_at_app; split; [hb_sub Hat3|].
    apply hb_at_app; split; [|hb_sub Hat3].
    unfold hq_L_scan, hs_at. cbv zeta. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [hd_at fst snd].
    - rewrite Q13. exact R13.
    - rewrite Q11. unfold w64, A, HQ_ENT_SZ. f_equal. lia.
    - rewrite Q12. unfold w64, A, HQ_ENT_BODY. f_equal. lia.
    - rewrite Q16. unfold w64, A, HQ_ENT_BODY. f_equal. lia.
    - rewrite Q14. unfold w64, A, HQ_ENT0. f_equal. lia.
    - rewrite Q15. unfold w64, A, HQ_ENT0. f_equal. lia.
    - rewrite Q20. unfold w64. f_equal. lia.
    - rewrite Q21. unfold w64. f_equal. lia. }
  split; [exact Hf1|]. split; [exact Hf2|]. split; [exact Hlive|].
  split; [lia|].
  split; [intros q Hq; destruct (Nat.eq_dec q m) as [->|Hqm]; [exact Hk | apply Hrun; lia]|].
  split; [exact Hx | exact Hfold].
- (* KEY: entry m is a key, entry m + 1 its value *)
  destruct HR as (Q18 & Q20 & Q21).
  assert (Hk : key_of (nth m (ents r) (Ent 0 0 [])) = Some (Cursor.cstr (e_body (nth m (ents r) (Ent 0 0 [])))))
    by (rewrite hs_key_of, Hkey; reflexivity).
  pose proof (hb_at_keep _ _ _ _ _ Hat' regs3 hs_kept Hk3 ltac:(vm_compute; reflexivity)) as Hat3.
  apply (HKEY fx2 ly2 S2 W2 regs3 mem2 md3 (Cursor.cstr (e_body (nth m (ents r) (Ent 0 0 [])))) cs keys rf).
  split.
  { apply (hb_base3_regs B MT cx fx2 r hq_shX ly2 S2 W2 regs2 mem2 md2 regs3 md3 Hb3 HJ3 Hio3).
    intros q Hq. destruct Hq as [->|[->| ->]]; apply Hk3; unfold hs_kept; hb_kin. }
  split.
  { unfold hs_at_cx. apply hb_at_app; split; [hb_sub Hat3|].
    apply hb_at_app; split; [hb_sub Hat3|].
    assert (Hpre : hs_at rsegs (w_H W2) mem2 regs3 (x_e cx)
      [(LReg 1, e_pp (x_e cx) + HQ_ENT0); (LReg 31, e_pp (x_e cx) + HQ_ENT0); (LReg 30, -1);
       (LReg 7, hq_nent r); (LReg 28, hq_nent r - 1)]) by hb_sub Hat3.
    unfold hs_at in Hpre |- *. cbn [app].
    repeat (apply Forall_cons_iff in Hpre as [? Hpre]; apply Forall_cons; [assumption|]).
    repeat apply Forall_cons; [..|apply Forall_nil]; cbn [hd_at fst snd].
    - rewrite Q18. unfold w64, A, HQ_ENT_BODY. f_equal. lia.
    - exact Q20.
    - exact Q21. }
  split; [exact Hf1|]. split; [exact Hf2|]. split; [exact Hlive|].
  split; [lia|]. split; [lia|]. split; [exact Hrun|]. split; [exact Hk|].
  split; [exact Hx | exact Hfold].
Qed.
End c.

Print Assumptions hb_scan_A.
