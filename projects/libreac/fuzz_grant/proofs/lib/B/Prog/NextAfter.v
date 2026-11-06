(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a segment of reac_headamp_tx_next on fuzz_grant.asan (NextAfter), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/AE3m.v. *)
(* Modified by Theorem Labs, 2026-10: image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/NextAfter.v at a working branch af735a950e2 (blob 9eb63e2990f; the walk was ported from blob e91a36749de at a working branch afd75724b5b, which differs from it only by 4 added and 0 removed lines, the licence header), restated over image B's listing, addresses and walk layer (lib/B/Prog) against GrantBContracts.v; image B has two signed tests (0x86174 sets a4 = max(replay_idx, 3w), 0x8617c exits), so the exhausted-scan exit is proved twice; no I1 *)
(* reac_headamp_tx_next (image B 0x85efc): the segment of its walk from AFTR (0x86100), where the
   edge scan over the 144 cells found none changed, to the next cut or to the return.
   C source src/reac_headamp_tx.c:137-146.

   The segment reads replay_width (offset 437). If it is 0 it jumps to the re-assert tail RSWP
   (0x8626c). Otherwise it reads replay_wait (444); if that is positive it stores replay_wait - 1
   and returns 0 (through the epilogue at 0x862cc). Otherwise it reads replay_idx (440): if
   replay_idx >= 3 * replay_width it clears replay_width through the check at 0x86260 and falls
   into RSWP; otherwise it reads replay_base (436) and replay_set_only (448), sets up the replay
   scan's constants and reaches the scan's head LOOPR (0x861cc). The two cuts after this one are
   nx_resweep_spec and nx_rloop_spec (lib/B/Prog/HeadampTxNext.v), taken here as the theorem's two
   leading implications; the table's new state is the model's after_scan (lib/Prog/NextModel.v).

   Image B against image A, for this segment:
     - the frame is 96 bytes and twelve registers are saved (ra, s0..s10), so nx_saved has twelve
       slots and the epilogue's twelve `ld` run from 88(sp) down to 0(sp);
     - the table is in s0 and the value pointer in s1 (image A: a0 and a3), the shadow base is in
       s5 (image A: t0), and chp/parp stay in a1/a2;
     - the cut's register file is the env's atom file (atom 2 = the cut sp = entry sp - 96, atom 8
       = tx, atom 9 = valp, atom 11 = chp, atom 12 = parp, atom 21 = the shadow base), so the
       shadow expression of this segment is SOff 21 0, not the entry state's BxN = SOff 32 0;
     - the contract gives only thd_replay_ok T, never image A's I1, so replay_idx and replay_wait
       are seated as their plain machine ranges 0..2^32-1 and every `lw` of them leaves a sign
       extension in the register, which den_lw turns back into s32; the bound 0 <= replay_idx that
       the replay scan needs is introduced here, out of thd_replay_ok and the width test.

   The memory-checking runtime: every access of this segment is to the table at a constant offset,
   so the shadow entry for the table's 460 bytes (shadow byte at (a >> 3) + s5 marked usable for
   each byte of the block) makes the walk discharge the shadow check of each instrumented access.
   The report branch (a jal of an __asan_report_ function) is not reached from any of them
   (analysis rows 10..15 and 18, all fast-path):
     replay_width, lbu at 0x86114: shadow read 0x8610c, branch 0x86110 to 0x864bc;
     replay_wait, lw at 0x86130: shadow read 0x86128, branch 0x8612c to 0x864d8;
     replay_wait, sw at 0x86148: shadow read 0x86138, branch 0x8613c to 0x864fc;
     replay_idx, lw at 0x86164: shadow read 0x8615c, branch 0x86160 to 0x8651c;
     replay_base, lbu at 0x861a4: shadow read 0x8618c, branch 0x86190 to 0x86550;
     replay_set_only, lbu at 0x861b0: shadow read 0x861a0, branch 0x861a8 to 0x8655c;
     replay_width, sb at 0x86268: shadow read 0x86260, branch 0x86264 to 0x86540.
   No UBSan trap guard lies in this segment: T1..T11 are the entry and the edge scan, T12..T15 the
   replay loop past LOOPR, T16..T18 the replay emit. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0f YI16 YI0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaRun PaShadow PaStep.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantAddr GrantPa GrantPaLib GrantFrame GrantRo YC1g.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import Mem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require ZBridge.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import
HeadampModel NextModel NextLemmas SlotNeeds_c HeadampI1.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantBContracts HeadampTxNext.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YO0b YO0c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the table's bytes, and the two writes this segment makes ------------------------------- *)

(* A four-byte field of the table, as an unsigned value. *)
Lemma na_u32at_range : forall T k, 0 <= u32at T k < 4294967296.
Proof.
  intros T k. unfold u32at.
  pose proof (ATx.tb_range T k). pose proof (ATx.tb_range T (k + 1)).
  pose proof (ATx.tb_range T (k + 2)). pose proof (ATx.tb_range T (k + 3)). lia.
Qed.

(* A byte of a field value, as the region's chunk gives it. *)
Lemma bw_tb : forall T k, YP09.byte_of_word (Z_to_bv 64 (tb T k)) 0 = nth (Z.to_nat k) T (Z_to_bv 8 0).
Proof.
  intros T k. unfold YP09.byte_of_word. pose proof (ATx.tb_range T k).
  rewrite unsigned_lit_small by lia. rewrite Z.mul_0_r, Z.shiftr_0_r. apply Z_to_bv8_tb.
Qed.

Lemma bw_u32 : forall T k j, 0 <= j < 4 ->
  YP09.byte_of_word (Z_to_bv 64 (u32at T k)) j = nth (Z.to_nat (k + j)) T (Z_to_bv 8 0).
Proof.
  intros T k j Hj. unfold YP09.byte_of_word. pose proof (na_u32at_range T k) as Hu.
  rewrite unsigned_lit_small by lia. rewrite <- Z_to_bv8_tb.
  pose proof (ATx.tb_range T k). pose proof (ATx.tb_range T (k + 1)).
  pose proof (ATx.tb_range T (k + 2)). pose proof (ATx.tb_range T (k + 3)).
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  rewrite Z.shiftr_div_pow2 by lia.
  assert (j = 0 \/ j = 1 \/ j = 2 \/ j = 3) as [-> | [-> | [-> | ->]]] by lia; unfold u32at.
  - rewrite !Z.add_0_r. change (2 ^ (8 * 0)) with 1. rewrite Z.div_1_r.
    Z.div_mod_to_equations. lia.
  - change (2 ^ (8 * 1)) with 256. Z.div_mod_to_equations. lia.
  - change (2 ^ (8 * 2)) with 65536. Z.div_mod_to_equations. lia.
  - change (2 ^ (8 * 3)) with 16777216. Z.div_mod_to_equations. lia.
Qed.

(* Writing the cursor's own value back leaves every byte of the table as it was. *)
Lemma set4_self_nth : forall T k i, length T = 460%nat -> 0 <= k -> k + 4 <= 460 -> 0 <= i < 460 ->
  nth (Z.to_nat i) (set4 T k (u32 T k)) (Z_to_bv 8 0) = nth (Z.to_nat i) T (Z_to_bv 8 0).
Proof.
  intros T k i HL Hk Hk4 Hi. rewrite <- !Z_to_bv8_tb. f_equal.
  pose proof (u32_range T k) as Hu.
  pose proof (NextLemmas.tb_range T k). pose proof (NextLemmas.tb_range T (k + 1)).
  pose proof (NextLemmas.tb_range T (k + 2)). pose proof (NextLemmas.tb_range T (k + 3)).
  destruct (Z_lt_le_dec i k) as [Hlo | Hlo]; [apply tb_set4_out; lia|].
  destruct (Z_lt_le_dec i (k + 4)) as [Hhi | Hhi]; [|apply tb_set4_out; lia].
  replace i with (k + (i - k)) by lia.
  rewrite (tb_set4_in T k (u32 T k) (i - k)) by lia.
  assert (i - k = 0 \/ i - k = 1 \/ i - k = 2 \/ i - k = 3) as [E | [E | [E | E]]] by lia;
    rewrite E; unfold u32.
  - change (Z.to_nat 0) with 0%nat. cbn [nth]. rewrite ?Z.add_0_r. Z.div_mod_to_equations. lia.
  - change (Z.to_nat 1) with 1%nat. cbn [nth]. Z.div_mod_to_equations. lia.
  - change (Z.to_nat 2) with 2%nat. cbn [nth]. Z.div_mod_to_equations. lia.
  - change (Z.to_nat 3) with 3%nat. cbn [nth]. Z.div_mod_to_equations. lia.
Qed.

Lemma walk_set4_self : forall n T t bs o total j, length T = 460%nat ->
  walk T t bs o total j (S n) = walk (set4 T 440 j) t bs o total j (S n).
Proof.
  intros n T t bs o total j HL. cbn [walk].
  rewrite set4_set4 by (first [exact HL | lia]). reflexivity.
Qed.

(* ---- the sign extension of a four-byte load -------------------------------------------------
   The contract bounds replay_idx and replay_wait only by their machine width, so the atom of each
   is its plain unsigned value and the `lw` that reads it leaves a sign extension in the register.
   This is the one place where image B's walk differs from image A's arithmetic, where I1 made the
   extension the identity. *)
Lemma s32_of_u32 : forall T k, s32 T k = (if u32 T k <? 2147483648 then u32 T k else u32 T k - 4294967296).
Proof. intros T k. reflexivity. Qed.

(* A cursor the table invariant has already placed at or above zero is its own unsigned value. *)
Lemma s32_u32_nonneg : forall T k, 0 <= s32 T k -> s32 T k = u32 T k.
Proof.
  intros T k H. rewrite s32_of_u32 in *.
  destruct (Z.ltb_spec (u32 T k) 2147483648) as [Hlt|Hge];
    [reflexivity | exfalso; pose proof (u32_range T k); lia].
Qed.

(* The signed reading of a four-byte field, as a plain bound. *)
Lemma s32_bound : forall T k, - (2 ^ 31) <= s32 T k < 2 ^ 31.
Proof.
  intros T k. rewrite s32_of_u32. pose proof (u32_range T k).
  destruct (Z.ltb_spec (u32 T k) 2147483648); lia.
Qed.

Lemma na_sx : forall x, 0 <= x < 4294967296 ->
  zcanon (bv_swrap 32 x) = if x <? 2147483648 then x else x + 18446744069414584320.
Proof.
  intros x Hx. unfold zcanon, M64, bv_swrap, bv_wrap.
  change (2 ^ 64) with 18446744073709551616.
  change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  destruct (Z.ltb_spec x 2147483648) as [Hl|Hl].
  - rewrite (Z.mod_small (x + 2147483648) 4294967296) by lia.
    replace (x + 2147483648 - 2147483648) with x by lia. apply Z.mod_small. lia.
  - assert (Hm : (x + 2147483648) mod 4294967296 = x - 2147483648)
      by (first [apply (Z.mod_unique _ _ 1) | symmetry; apply (Z.mod_unique _ _ 1)]; lia).
    rewrite Hm.
    first [apply (Z.mod_unique _ _ (-1)) | symmetry; apply (Z.mod_unique _ _ (-1))]; lia.
Qed.

(* The register a `lw` of a four-byte field leaves: the field's signed reading. *)
Lemma den_lw : forall (E : env) n u, ew E n = Z_to_bv 64 u -> 0 <= u < 4294967296 ->
  sv_denot E (SExt true 32 (SOff n 0))
  = w64 (if u <? 2147483648 then u else u - 4294967296).
Proof.
  intros E n u Hn Hu. rewrite denot_lit_U, U_SExt, (U_atom E n u Hn ltac:(lia)).
  change (2 ^ Z.of_N 32) with 4294967296. rewrite (Z.mod_small u) by lia.
  rewrite (na_sx u Hu). unfold w64.
  destruct (Z.ltb_spec u 2147483648) as [H|H]; [reflexivity|].
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616.
  rewrite <- (Z.mod_add (u - 4294967296) 1 18446744073709551616) by lia.
  f_equal; lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).
#[local] Notation TX_SIZE := ATx.TX_SIZE.
#[local] Notation LAY_TX := ATx.LAY_TX.
#[local] Notation tx_vals := ATx.tx_vals.
#[local] Notation tx_fbyte := ATx.tx_fbyte.

(* ---- the symbolic state at AFTR -------------------------------------------------------------
   The env is the cut's own register file (atom r = the register r holds at 0x86100), as every
   mid-function state of this walk is seated. So atom 2 is the machine sp there, which is the
   entry sp less the 96-byte frame, and the twelve registers the prologue saved are extra atoms
   56..67: the frame runs UP from atom 2, and the epilogue reads the twelve back.
   The extra list is the walk layer's own nx_extra (atoms 32..55: the shadow base, the table's ten
   scalar fields and the scan constants) followed by those twelve. *)
Definition na_extra (regs : bvmap 5 word) (tx : Z) (T : list byte) : list word :=
  nx_extra tx T
  ++ [ getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20;
       getr regs 21; getr regs 22; getr regs 23; getr regs 24; getr regs 25; getr regs 26 ].

Definition STKA : YP09.region := YP09.mkRegion (Some 2%nat) 0 NX_FRAME 0 0
  [ YP09.mkChunk 88 (CVal 8 (SOff 56 0)); YP09.mkChunk 80 (CVal 8 (SOff 57 0));
    YP09.mkChunk 72 (CVal 8 (SOff 58 0)); YP09.mkChunk 64 (CVal 8 (SOff 59 0));
    YP09.mkChunk 56 (CVal 8 (SOff 60 0)); YP09.mkChunk 48 (CVal 8 (SOff 61 0));
    YP09.mkChunk 40 (CVal 8 (SOff 62 0)); YP09.mkChunk 32 (CVal 8 (SOff 63 0));
    YP09.mkChunk 24 (CVal 8 (SOff 64 0)); YP09.mkChunk 16 (CVal 8 (SOff 65 0));
    YP09.mkChunk 8 (CVal 8 (SOff 66 0)); YP09.mkChunk 0 (CVal 8 (SOff 67 0)) ].
(* The two windows of the table this segment reads and writes: replay_base/replay_width, with
   replay_width the one byte it may write, and replay_idx/replay_wait/replay_set_only, with
   replay_wait the four bytes it may write. *)
Definition TXA : YP09.region := YP09.mkRegion (Some 8%nat) 436 438 437 438
  [ YP09.mkChunk 436 (CVal 1 (SOff 34 0)); YP09.mkChunk 437 (CVal 1 (SOff 35 0)) ].
Definition TXB : YP09.region := YP09.mkRegion (Some 8%nat) 440 449 444 448
  [ YP09.mkChunk 440 (CVal 4 (SOff 36 0)); YP09.mkChunk 444 (CVal 4 (SOff 37 0));
    YP09.mkChunk 448 (CVal 1 (SOff 38 0)) ].
Definition na_regs : list YP09.region := [ STKA; TXA; TXB ].
Definition na_atoms : list (nat * afact) :=
  [ (2%nat, mkAF (2 ^ 46 - NX_FRAME) (2 ^ 47 - NX_FRAME) 4); (8%nat, PTRN 4);
    (32%nat, mkAF SB_NX SB_NX 0);
    (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0);
    (36%nat, mkAF 0 4294967295 0); (37%nat, mkAF 0 4294967295 0); (38%nat, mkAF 0 255 0) ].
Definition na_SH : list shent := [ mkSHE 8 0 460 ].
(* The shadow base is the register s5 holds at the cut; the symbolic register file pins x21 to
   atom 32, so the walk's shadow expressions are the entry state's BxN. *)
Definition na_sr : list sv := sr_set sr_atoms (21%bv : bv 5) (SOff 32 0).
Definition ss_a : sstate := mkSS AFTR na_sr na_regs None (mkFacts na_atoms [] []).

Lemma na_r21_nz : (21%bv : bv 5) <> 0%bv.
Proof. intros X. apply (f_equal (@bv_unsigned 5)) in X. vm_compute in X. discriminate X. Qed.

Definition EA (regs : bvmap 5 word) (tx : Z) (T : list byte) (regsA : bvmap 5 word) : env :=
  Eimg (Ereg regsA (na_extra regs tx T)).

(* ---- denotations of the expressions the walk leaves in registers and chunks ------------------ *)
Lemma den0 : forall (E : env) n w, ew E n = w -> sv_denot E (SOff n 0) = w.
Proof. intros E n w H. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.

Lemma denk : forall (E : env) n v k, bv_unsigned (ew E n) = v -> sv_denot E (SOff n k) = w64 (v + k).
Proof. intros E n v k H. cbn [sv_denot]. rewrite H. reflexivity. Qed.

Lemma den_shadow : forall (E : env) tx k, bv_unsigned (ew E 8) = tx -> ew E 32 = w64 SB_NX ->
  0 <= tx + k < 2 ^ 47 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 k) (SLit 3)) (SOff 32 0))
  = w64 (SHADOW_OFF + (tx + k) / 8).
Proof.
  intros E tx k U8 E32 Hr. rewrite denot_lit_U. unfold w64. f_equal.
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
  rewrite !U_SOff, U_SLit, U8, E32. unfold w64.
  rewrite unsigned_lit_small by (unfold SB_NX; lia).
  unfold zcanon, M64.
  change (Z.land (3 mod 2 ^ 64) 63) with 3.
  rewrite (Z.mod_small (tx + k)) by lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  assert (0 <= (tx + k) / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  rewrite (Z.mod_small ((tx + k) / 8)) by lia.
  rewrite (Z.mod_small (SB_NX + 0)) by (unfold SB_NX; lia).
  rewrite Z.mod_small by (unfold SB_NX; lia).
  unfold SHADOW_OFF, SB_NX. lia.
Qed.

(* Three times the replay width: image B computes it with a shift and an add, which the engine
   folds into the same multiply image A's byte multiply gives. *)
Lemma den_mul3 : forall (E : env) x, ew E 35 = w64 x -> 0 <= x < 256 ->
  sv_denot E (SMd M_MUL (SOff 35 0) (SLit 3)) = w64 (3 * x).
Proof.
  intros E x H Hx. rewrite denot_lit_U. unfold w64. f_equal.
  rewrite U_SMd. cbn [zmd_raw]. rewrite (U_atom E 35 x H ltac:(lia)), U_SLit.
  unfold zcanon, M64. rewrite (Z.mod_small 3) by lia. rewrite Z.mod_small by lia. lia.
Qed.

(* The one's complement of the set array's base, which the replay scan's pointer-overflow guard
   compares against. *)
Lemma den_not : forall (E : env) tx k, bv_unsigned (ew E 8) = tx -> 0 <= tx + k < 2 ^ 47 ->
  sv_denot E (SAlu ALU_XOR (SOff 8 k) (SLit (-1)))
  = w64 (18446744073709551615 - (tx + k)).
Proof.
  intros E tx k U8 Hr. rewrite denot_lit_U. unfold w64. f_equal.
  rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, U8.
  unfold zcanon, M64.
  rewrite (Z.mod_small (tx + k)) by lia.
  replace ((-1) mod 2 ^ 64) with 18446744073709551615 by reflexivity.
  rewrite ZBridge.zb_lxor_ones by lia.
  apply Z.mod_small. lia.
Qed.

(* The decrement the wait path stores: addi on the sign-extended field. *)
Lemma den_sub1 : forall (E : env) (a : sv) v, sv_denot E a = w64 v -> 0 <= v < 2 ^ 64 ->
  0 <= v + -1 < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD a (SLit (-1))) = w64 (v + -1).
Proof.
  intros E a v Ha H0 H1. rewrite denot_lit_U. unfold w64. f_equal.
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
  replace (U E a) with v
    by (unfold U; rewrite Ha; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
  unfold zcanon, M64. replace ((-1) mod 2 ^ 64) with 18446744073709551615 by reflexivity.
  change (2 ^ 64) with 18446744073709551616.
  replace (v + 18446744073709551615) with ((v + -1) + 1 * 18446744073709551616) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

(* The branches this segment stops at, as conditions on the table's fields. *)
Lemma bt_eq0 : forall (E : env) n v, ew E n = w64 v -> 0 <= v < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = (v =? 0).
Proof. intros E n v H Hv. rewrite branch_eq_U, (U_atom E n v H Hv), U_lit by lia. reflexivity. Qed.

(* A signed 64-bit reading of a literal, which the two signed tests of this segment need on a
   replay_wait or a replay_idx the contract does not bound below. *)
Lemma s64_lit : forall z, - (2 ^ 63) <= z < 2 ^ 63 -> YO0b.s64 (bv_unsigned (Z_to_bv 64 z)) = z.
Proof.
  intros z Hz. rewrite YO0c.lit64_unsigned. unfold YO0b.s64.
  destruct (Z_lt_le_dec z 0) as [Hneg | Hpos].
  - rewrite <- (Z.mod_add z 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia.
    destruct (Z.ltb_spec (z + 1 * 2 ^ 64) (2 ^ 63)); lia.
  - rewrite Z.mod_small by lia. destruct (Z.ltb_spec z (2 ^ 63)); lia.
Qed.

Lemma bt_ge : forall (E : env) a b x y, sv_denot E a = w64 x -> sv_denot E b = w64 y ->
  - (2 ^ 63) <= x < 2 ^ 63 -> - (2 ^ 63) <= y < 2 ^ 63 ->
  branch_taken BC_GE (sv_denot E a) (sv_denot E b) = negb (x <? y).
Proof.
  intros E a b x y Ha Hb Hx Hy. rewrite Ha, Hb, YO0c.branch_ge. unfold w64.
  rewrite !s64_lit by lia. reflexivity.
Qed.

Lemma bt_lt : forall (E : env) a b x y, sv_denot E a = w64 x -> sv_denot E b = w64 y ->
  - (2 ^ 63) <= x < 2 ^ 63 -> - (2 ^ 63) <= y < 2 ^ 63 ->
  branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (x <? y).
Proof.
  intros E a b x y Ha Hb Hx Hy. rewrite Ha, Hb, YO0c.branch_lt. unfold w64.
  rewrite !s64_lit by lia. reflexivity.
Qed.

Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_grant) (PI := PI).

(* ---- what the segment's runs keep ------------------------------------------------------------
   The seating above gives the stack region no writable window — this segment writes no byte of
   its own frame — and the table only the two fields it may write, so a run's frame_of keeps the
   twelve saved registers, the three bytes the caller holds and every other byte of the table. *)
Definition na_win (tx a : Z) : Prop := a = tx + 437 \/ (tx + 444 <= a < tx + 448).

(* A byte the caller holds: the contract places it outside the table and inside the address
   space, which is all this segment needs of it. *)
Definition na_out (tx q : Z) : Prop := 0 <= q < 2 ^ 64 /\ ~ (tx <= q < tx + 460).

Definition na_meq (W : world SEGS) (m1 m2 : word -> option byte) (tx : Z) : Prop :=
  forall x : word, ~ na_win tx (bv_unsigned x) -> mrestrict (w_H W) m2 x = mrestrict (w_H W) m1 x.

Definition na_pres (W : world SEGS) (m1 m2 : word -> option byte) : Prop :=
  forall a, apresent (w_H W) m1 a -> apresent (w_H W) m2 a.

Lemma na_meq_refl : forall W m tx, na_meq W m m tx.
Proof. intros W m tx x _. reflexivity. Qed.

Lemma na_meq_trans : forall W m1 m2 m3 tx, na_meq W m1 m2 tx -> na_meq W m2 m3 tx -> na_meq W m1 m3 tx.
Proof. intros W m1 m2 m3 tx H1 H2 x Hx. rewrite (H2 x Hx). exact (H1 x Hx). Qed.

Lemma na_inw : forall (E : env) (rs : smem) (sp tx a : Z),
  skeleton rs = skeleton na_regs ->
  bv_unsigned (ew E 2) = sp -> bv_unsigned (ew E 8) = tx ->
  in_wrange E rs a -> na_win tx a.
Proof.
  intros E rs sp tx a Hsk U2 U8 Hw.
  destruct (in_wrange_skeleton E rs na_regs a Hsk Hw) as (r & Hin & Ha).
  unfold na_regs in Hin. cbn [In] in Hin. unfold na_win.
  destruct Hin as [<- | [<- | [<- | []]]]; unfold STKA, TXA, TXB in Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?U2, ?U8 in Ha; lia.
Qed.

Lemma na_meq_of_frame : forall (E : env) (rs : smem) (W : world SEGS) m1 m2 sp tx,
  skeleton rs = skeleton na_regs ->
  bv_unsigned (ew E 2) = sp -> bv_unsigned (ew E 8) = tx ->
  frame_of E rs (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) -> na_meq W m1 m2 tx.
Proof.
  intros E rs W m1 m2 sp tx Hsk U2 U8 HF x Hx. apply HF. intros Hw. apply Hx.
  exact (na_inw E rs sp tx _ Hsk U2 U8 Hw).
Qed.

Lemma na_grows : forall (W : world SEGS) m1 m2 a,
  mem_grows (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  apresent (w_H W) m1 a -> apresent (w_H W) m2 a.
Proof.
  intros W m1 m2 a HG (Hh & b & Hb). split; [exact Hh|].
  specialize (HG (Z_to_bv 64 a)). unfold mrestrict in HG. rewrite Hh, Hb in HG.
  destruct (m2 (Z_to_bv 64 a)) as [b'|] eqn:E2; [exists b'; reflexivity|].
  exfalso. apply HG; [discriminate | first [reflexivity | exact E2]].
Qed.

Lemma na_pres_step : forall (W : world SEGS) m0 m1 m2,
  na_pres W m0 m1 -> mem_grows (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) -> na_pres W m0 m2.
Proof. intros W m0 m1 m2 HP HG a Ha. exact (na_grows W m1 m2 a HG (HP a Ha)). Qed.

Lemma na_mbyte : forall W m1 m2 tx a, na_meq W m1 m2 tx -> 0 <= a < 2 ^ 64 -> ~ na_win tx a ->
  mbyte SEGS (mrestrict (w_H W) m2) a = mbyte SEGS (mrestrict (w_H W) m1) a.
Proof.
  intros W m1 m2 tx a HM Ha Hn. unfold mbyte. rewrite (HM (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit_small by lia. exact Hn.
Qed.

Lemma na_aview : forall W m1 m2 tx a, na_meq W m1 m2 tx -> 0 <= a < 2 ^ 64 -> ~ na_win tx a ->
  aview SEGS (w_H W) m2 a = aview SEGS (w_H W) m1 a.
Proof.
  intros W m1 m2 tx a HM Ha Hn. unfold aview.
  rewrite (na_mbyte W m1 m2 tx a HM Ha Hn). reflexivity.
Qed.

Lemma na_val : forall W m1 m2 tx a n v, na_meq W m1 m2 tx -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (a + Z.of_nat n <= tx + 437 \/ tx + 448 <= a) ->
  val_mem SEGS (mrestrict (w_H W) m1) a n v -> val_mem SEGS (mrestrict (w_H W) m2) a n v.
Proof.
  intros W m1 m2 tx a n v HM Ha Hn Hd HV kk Hk.
  rewrite (na_mbyte W m1 m2 tx (a + Z.of_nat kk) HM) by (unfold na_win; lia). exact (HV kk Hk).
Qed.

(* The twelve saved registers are below the table and above nothing this segment writes. *)
Lemma na_saved : forall W m1 m2 (regs : bvmap 5 word) tx,
  na_meq W m1 m2 tx -> 0 <= tx -> tx + 460 <= spZ regs - NX_STK -> spZ regs <= 2 ^ 47 ->
  nx_saved W m1 regs (spZ regs) -> nx_saved W m2 regs (spZ regs).
Proof.
  intros W m1 m2 regs tx HM H0 H1 H2 HS. rewrite nx_stk_val in H1.
  destruct HS as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12).
  unfold nx_saved. repeat split; (eapply na_val; [exact HM | | | | eassumption]);
    try change (Z.of_nat 8) with 8; lia.
Qed.

(* nx_same and nx_outq, from the bytes the runs left alone. *)
Lemma na_same : forall W memc m1 m2 sp tx chp parp valp,
  nx_same W memc m1 sp tx chp parp valp (tx + 432) -> na_meq W m1 m2 tx ->
  nx_same W memc m2 sp tx chp parp valp (tx + 432).
Proof.
  intros W memc m1 m2 sp tx chp parp valp HS HM x H1 H2.
  rewrite (HM x); [exact (HS x H1 H2)|]. intros Hx. apply H2. unfold nx_touch2.
  unfold na_win in Hx. left. lia.
Qed.

Lemma na_outq : forall W memc m1 m2 tx chp parp valp,
  nx_outq W memc m1 chp parp valp -> na_meq W m1 m2 tx ->
  na_out tx chp -> na_out tx parp -> na_out tx valp ->
  nx_outq W memc m2 chp parp valp.
Proof.
  intros W memc m1 m2 tx chp parp valp (Q1 & Q2 & Q3) HM Hc Hp Hv.
  unfold nx_outq. unfold na_out in Hc, Hp, Hv.
  split; [|split].
  - rewrite (na_aview W m1 m2 tx chp HM ltac:(lia) ltac:(unfold na_win; lia)). exact Q1.
  - rewrite (na_aview W m1 m2 tx parp HM ltac:(lia) ltac:(unfold na_win; lia)). exact Q2.
  - rewrite (na_aview W m1 m2 tx valp HM ltac:(lia) ltac:(unfold na_win; lia)). exact Q3.
Qed.

(* The table after a run: the two fields from the regions' chunks, every other byte kept. *)
Lemma na_obj_eq : forall m tx T T',
  (forall i, 0 <= i < 460 -> nth (Z.to_nat i) T' (Z_to_bv 8 0) = nth (Z.to_nat i) T (Z_to_bv 8 0)) ->
  obj_at SEGS m tx LAY_TX (tx_vals T) -> obj_at SEGS m tx LAY_TX (tx_vals T').
Proof.
  intros m tx T T' H HO. apply (proj2 (ATx.tx_obj_bytes SEGS _ _ _)). intros i Hi.
  rewrite H by (apply ATx.tx_fbyte_range; exact Hi).
  exact (proj1 (ATx.tx_obj_bytes SEGS _ _ _) HO i Hi).
Qed.

Lemma na_table : forall (E : env) (W : world SEGS) m0 m (tx : Z) (T T' : list byte) cs1 cs2 e1 e2,
  obj_at SEGS (mrestrict (w_H W) m0) tx LAY_TX (tx_vals T) ->
  na_meq W m0 m tx -> 0 <= tx -> tx + 460 <= 2 ^ 64 ->
  bv_unsigned (ew E 8) = tx ->
  region_ok SEGS E (mrestrict (w_H W) m) (YP09.mkRegion (Some 8%nat) 436 438 437 438 cs1) ->
  region_ok SEGS E (mrestrict (w_H W) m) (YP09.mkRegion (Some 8%nat) 440 449 444 448 cs2) ->
  In (YP09.mkChunk 437 (CVal 1 e1)) cs1 -> In (YP09.mkChunk 444 (CVal 4 e2)) cs2 ->
  (forall i, 0 <= i < 460 -> i <> 437 -> ~ (444 <= i < 448) ->
     nth (Z.to_nat i) T' (Z_to_bv 8 0) = nth (Z.to_nat i) T (Z_to_bv 8 0)) ->
  YP09.byte_of_word (sv_denot E e1) 0 = nth (Z.to_nat 437) T' (Z_to_bv 8 0) ->
  (forall j, 0 <= j < 4 ->
     YP09.byte_of_word (sv_denot E e2) j = nth (Z.to_nat (444 + j)) T' (Z_to_bv 8 0)) ->
  obj_at SEGS (mrestrict (w_H W) m) tx LAY_TX (tx_vals T').
Proof.
  intros E W m0 m tx T T' cs1 cs2 e1 e2 HO HM H0 H1 U8 R1 R2 I1 I2 Hout B1 B2.
  apply (proj2 (ATx.tx_obj_bytes SEGS _ tx T')). intros i Hi.
  pose proof (ATx.tx_fbyte_range i Hi) as Hir.
  destruct (Z.eq_dec i 437) as [-> | Hn].
  - replace (tx + 437) with (tx + 437 + 0) by lia.
    rewrite (ATx.byte_of_region SEGS E _ 8%nat tx cs1 436 438 437 438 437 1 e1 0 R1 U8 I1 ltac:(cbn; lia)).
    rewrite B1. reflexivity.
  - destruct (Z_lt_le_dec i 444) as [Hlo | Hlo]; [| destruct (Z_lt_le_dec i 448) as [Hhi | Hhi]].
    + rewrite (na_mbyte W m0 m tx (tx + i) HM) by (unfold na_win; lia).
      rewrite (proj1 (ATx.tx_obj_bytes SEGS _ tx T) HO i Hi). rewrite Hout by lia. reflexivity.
    + replace (tx + i) with (tx + 444 + (i - 444)) by lia.
      rewrite (ATx.byte_of_region SEGS E _ 8%nat tx cs2 440 449 444 448 444 4 e2 (i - 444) R2 U8 I2
                 ltac:(cbn; lia)).
      rewrite B2 by lia. replace (444 + (i - 444)) with i by lia. reflexivity.
    + rewrite (na_mbyte W m0 m tx (tx + i) HM) by (unfold na_win; lia).
      rewrite (proj1 (ATx.tx_obj_bytes SEGS _ tx T) HO i Hi). rewrite Hout by lia. reflexivity.
Qed.

(* The field values of the table, as the regions' chunks need them. *)
Lemma na_val1 : forall m tx (T : list byte) k,
  (forall i, tx_fbyte i = true -> mbyte SEGS m (tx + i) = Some (nth (Z.to_nat i) T (Z_to_bv 8 0))) ->
  tx_fbyte k = true -> val_mem SEGS m (tx + k) 1 (tb T k).
Proof.
  intros m tx T k HBY Hk kk Hkk. replace kk with 0%nat by lia. cbn [Z.of_nat].
  rewrite Z.add_0_r, (HBY k Hk). f_equal.
  rewrite le_byte_small by (pose proof (ATx.tb_range T k); cbn [Z.of_nat]; lia).
  rewrite Z.mul_0_r, Z.shiftr_0_r. symmetry. apply Z_to_bv8_tb.
Qed.

Lemma na_val4 : forall m tx (T : list byte) k,
  (forall i, tx_fbyte i = true -> mbyte SEGS m (tx + i) = Some (nth (Z.to_nat i) T (Z_to_bv 8 0))) ->
  (forall d, 0 <= d < 4 -> tx_fbyte (k + d) = true) ->
  val_mem SEGS m (tx + k) 4 (u32at T k).
Proof.
  intros m tx T k HBY Hk kk Hkk.
  pose proof (na_u32at_range T k) as Hu.
  replace (tx + k + Z.of_nat kk) with (tx + (k + Z.of_nat kk)) by lia.
  rewrite (HBY (k + Z.of_nat kk) (Hk (Z.of_nat kk) ltac:(lia))). f_equal.
  rewrite le_byte_small by (cbn [Z.of_nat]; lia).
  rewrite <- (bw_u32 T k (Z.of_nat kk) ltac:(lia)). unfold YP09.byte_of_word.
  rewrite unsigned_lit_small by lia. reflexivity.
Qed.

Lemma na_chunk_saved : forall (E : env) m sp n off (r : bv 5) (regs : bvmap 5 word),
  ew E n = getr regs r -> val_mem SEGS m (sp + off) 8 (bv_unsigned (getr regs r)) ->
  YP09.chunk_ok SEGS E m sp (YP09.mkChunk off (CVal 8 (SOff n 0))).
Proof.
  intros E m sp n off r regs H HV.
  apply (chunk_ok_val SEGS E m sp off 8 (SOff n 0) (bv_unsigned (getr regs r)));
    [ cbn [sv_denot]; rewrite H, Z.add_0_r; reflexivity
    | exact (bv_unsigned_in_range 64 (getr regs r))
    | cbn; lia | exact HV ].
Qed.

(* The engine's write permission at each run: the two fields of the table, which the caller lets
   the call write. *)
Lemma na_awr : forall (E : env) (rs : smem) STK sp0 FP ly S lyc Sc own sp tx,
  skeleton rs = skeleton na_regs ->
  bv_unsigned (ew E 2) = sp -> bv_unsigned (ew E 8) = tx ->
  (forall a, tx <= a < tx + TX_SIZE -> nx_may_write B STK sp0 FP ly S lyc Sc own a) ->
  awr_ok E rs STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own.
Proof.
  intros E rs STK sp0 FP ly S lyc Sc own sp tx Hsk U2 U8 HW a Ha. apply HW.
  pose proof (na_inw E rs sp tx a Hsk U2 U8 Ha) as Hw.
  unfold na_win in Hw. unfold TX_SIZE, ATx.TX_SIZE. lia.
Qed.

Ltac na_env_facts E HE regs regsA tx T :=
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regsA (na_extra regs tx T)) n)
    by (intros n Hn; rewrite HE; unfold EA; apply Eimg_low; exact Hn);
  assert (E2 : ew E 2 = getr regsA 2)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsA _ 2 2%bv eq_refl));
  assert (E3 : ew E 3 = getr regsA 3)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsA _ 3 3%bv eq_refl));
  assert (E4 : ew E 4 = getr regsA 4)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsA _ 4 4%bv eq_refl));
  assert (E8 : ew E 8 = getr regsA 8)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsA _ 8 8%bv eq_refl));
  assert (E9 : ew E 9 = getr regsA 9)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsA _ 9 9%bv eq_refl));
  assert (E11 : ew E 11 = getr regsA 11)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsA _ 11 11%bv eq_refl));
  assert (E12 : ew E 12 = getr regsA 12)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsA _ 12 12%bv eq_refl));
  assert (E21 : ew E 21 = getr regsA 21)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsA _ 21 21%bv eq_refl));
  assert (E27 : ew E 27 = getr regsA 27)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsA _ 27 27%bv eq_refl));
  assert (E32 : ew E 32 = w64 SB_NX)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsA _ 0));
  assert (E34 : ew E 34 = w64 (tb T 436))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsA _ 2));
  assert (E35 : ew E 35 = w64 (tb T 437))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsA _ 3));
  assert (E36 : ew E 36 = w64 (u32at T 440))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsA _ 4));
  assert (E37 : ew E 37 = w64 (u32at T 444))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsA _ 5));
  assert (E38 : ew E 38 = w64 (tb T 448))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsA _ 6));
  assert (X56 : ew E 56 = getr regs 1)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsA _ 24));
  assert (X57 : ew E 57 = getr regs 8)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsA _ 25));
  assert (X58 : ew E 58 = getr regs 9)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsA _ 26));
  assert (X59 : ew E 59 = getr regs 18)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsA _ 27));
  assert (X60 : ew E 60 = getr regs 19)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsA _ 28));
  assert (X61 : ew E 61 = getr regs 20)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsA _ 29));
  assert (X62 : ew E 62 = getr regs 21)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsA _ 30));
  assert (X63 : ew E 63 = getr regs 22)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsA _ 31));
  assert (X64 : ew E 64 = getr regs 23)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsA _ 32));
  assert (X65 : ew E 65 = getr regs 24)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsA _ 33));
  assert (X66 : ew E 66 = getr regs 25)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsA _ 34));
  assert (X67 : ew E 67 = getr regs 26)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsA _ 35)).

(* ---- the symbolic state at AFTR -------------------------------------------------------------- *)
Lemma na_seat_aftr : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
    (regs regsA : bvmap 5 word) memA mdA (tx chp parp valp : Z) (T : list byte),
  nx_ctx B STK sp0 FP ly S lyc Sc own W memc mdc regs tx chp parp valp T ->
  nx_mid B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs memA mdA tx chp parp valp (tx + 432) true ->
  nx_saved W memA regs (spZ regs) ->
  obj_at SEGS (mrestrict (w_H W) memA) tx LAY_TX (tx_vals T) ->
  nx_at_aftr regs regsA tx chp parp valp ->
  st_ok_pi SEGS VAL (EA regs tx T regsA) ss_a
    (restrict (w_H W) (mkst regsA (Z_to_bv 64 (BASE + AFTR)) memA (seg_rom SEGS)))
  /\ sh_ok SEGS BxN na_SH (EA regs tx T regsA) (mrestrict (w_H W) memA).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsA memA mdA tx chp parp valp T
    HCTX HMID HSAV HOBJ HAT.
  destruct HAT as (HKEEP & R2 & R8 & R9 & R11 & R12 & R21).
  pose proof HCTX as (HAR & Hg & Hoc & Hop & Hov & Dcp & Dcv & Dpv & Pc & Pp & Pv & Rac & Rap & Rav &
    Rt456 & Hspr & Hceil & Hsp16 & Hslo & Hshi & Hwtab & Hwc & Hwp & Hwv & Hret & Hra4 & Hgp & Htp &
    Q8 & Q11 & Q12 & Q13 & HTL & HTHD & Hobjc & Hpresc).
  pose proof HMID as (HJ & HSAME & HpresS & HpresK & HQ).
  pose proof (proj1 HJ) as HARj.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (al_blocks _ _ LAWS lyc Sc W memA mdA tx TX_SIZE HARj Hg)
    as (Hg16 & Hg4096 & Hgceil & Hgia & Hgpres & _).
  change (req_size TX_SIZE) with 460 in Hgceil, Hgia, Hgpres.
  pose proof (ATx.tb_range T 436) as R34.
  pose proof (ATx.tb_range T 437) as R35.
  pose proof (ATx.tb_range T 448) as R38.
  pose proof (na_u32at_range T 440) as R36. pose proof (na_u32at_range T 444) as R37.
  pose proof (proj1 (ATx.tx_obj_bytes SEGS _ _ _) HOBJ) as HBY.
  remember (EA regs tx T regsA) as E eqn:HE.
  na_env_facts E HE regs regsA tx T.
  assert (Usp : bv_unsigned (ew E 2) = spZ regs - NX_FRAME)
    by (rewrite E2, R2; apply unsigned_lit_small; rewrite nx_stk_val in Hceil;
        unfold NX_FRAME; lia).
  assert (U8 : bv_unsigned (ew E 8) = tx)
    by (rewrite E8, R8; apply unsigned_lit_small; rewrite nx_stk_val in Hceil; lia).
  assert (U32 : bv_unsigned (ew E 32) = SB_NX)
    by (rewrite E32; apply unsigned_lit_small; unfold SB_NX; lia).
  assert (U34 : bv_unsigned (ew E 34) = tb T 436) by (rewrite E34; apply unsigned_lit_small; lia).
  assert (U35 : bv_unsigned (ew E 35) = tb T 437) by (rewrite E35; apply unsigned_lit_small; lia).
  assert (U36 : bv_unsigned (ew E 36) = u32at T 440) by (rewrite E36; apply unsigned_lit_small; lia).
  assert (U37 : bv_unsigned (ew E 37) = u32at T 444) by (rewrite E37; apply unsigned_lit_small; lia).
  assert (U38 : bv_unsigned (ew E 38) = tb T 448) by (rewrite E38; apply unsigned_lit_small; lia).
  rewrite nx_stk_val in Hceil, Hslo.
  split.
  - rewrite restrict_mkst_fx. unfold ss_a. apply pa_entry_st_ok_full.
    + unfold na_sr. apply regs_ok_pin;
        [ rewrite HE; unfold EA; apply regs_ok_Eimg_Ereg | exact na_r21_nz |].
      rewrite (den0 E 32 _ E32). exact R21.
    + vm_compute. reflexivity.
    + unfold na_regs, STKA, TXA, TXB.
      repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      * rewrite Usp. split; [unfold NX_FRAME; lia|]. split; [unfold NX_FRAME; lia|].
        split; [intros o Ho; lia|].
        pose proof HSAV as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12).
        repeat apply Forall_cons; try apply Forall_nil.
        -- apply (na_chunk_saved E _ (spZ regs - NX_FRAME) 56 88 1%bv regs X56).
           replace (spZ regs - NX_FRAME + 88) with (spZ regs - 8) by (unfold NX_FRAME; lia). exact S1.
        -- apply (na_chunk_saved E _ (spZ regs - NX_FRAME) 57 80 8%bv regs X57).
           replace (spZ regs - NX_FRAME + 80) with (spZ regs - 16) by (unfold NX_FRAME; lia). exact S2.
        -- apply (na_chunk_saved E _ (spZ regs - NX_FRAME) 58 72 9%bv regs X58).
           replace (spZ regs - NX_FRAME + 72) with (spZ regs - 24) by (unfold NX_FRAME; lia). exact S3.
        -- apply (na_chunk_saved E _ (spZ regs - NX_FRAME) 59 64 18%bv regs X59).
           replace (spZ regs - NX_FRAME + 64) with (spZ regs - 32) by (unfold NX_FRAME; lia). exact S4.
        -- apply (na_chunk_saved E _ (spZ regs - NX_FRAME) 60 56 19%bv regs X60).
           replace (spZ regs - NX_FRAME + 56) with (spZ regs - 40) by (unfold NX_FRAME; lia). exact S5.
        -- apply (na_chunk_saved E _ (spZ regs - NX_FRAME) 61 48 20%bv regs X61).
           replace (spZ regs - NX_FRAME + 48) with (spZ regs - 48) by (unfold NX_FRAME; lia). exact S6.
        -- apply (na_chunk_saved E _ (spZ regs - NX_FRAME) 62 40 21%bv regs X62).
           replace (spZ regs - NX_FRAME + 40) with (spZ regs - 56) by (unfold NX_FRAME; lia). exact S7.
        -- apply (na_chunk_saved E _ (spZ regs - NX_FRAME) 63 32 22%bv regs X63).
           replace (spZ regs - NX_FRAME + 32) with (spZ regs - 64) by (unfold NX_FRAME; lia). exact S8.
        -- apply (na_chunk_saved E _ (spZ regs - NX_FRAME) 64 24 23%bv regs X64).
           replace (spZ regs - NX_FRAME + 24) with (spZ regs - 72) by (unfold NX_FRAME; lia). exact S9.
        -- apply (na_chunk_saved E _ (spZ regs - NX_FRAME) 65 16 24%bv regs X65).
           replace (spZ regs - NX_FRAME + 16) with (spZ regs - 80) by (unfold NX_FRAME; lia). exact S10.
        -- apply (na_chunk_saved E _ (spZ regs - NX_FRAME) 66 8 25%bv regs X66).
           replace (spZ regs - NX_FRAME + 8) with (spZ regs - 88) by (unfold NX_FRAME; lia). exact S11.
        -- apply (na_chunk_saved E _ (spZ regs - NX_FRAME) 67 0 26%bv regs X67).
           replace (spZ regs - NX_FRAME + 0) with (spZ regs - 96) by (unfold NX_FRAME; lia). exact S12.
      * rewrite U8. split; [lia|]. split; [lia|].
        split; [intros o Ho; apply (apresent_writable SEGS); exact (proj1 (Hgpres (tx + o) ltac:(lia)))|].
        repeat apply Forall_cons; try apply Forall_nil.
        -- apply (chunk_ok_val SEGS E _ tx 436 1 (SOff 34 0) (tb T 436));
             [ exact (den0 E 34 _ E34) | cbn; lia | cbn; lia
             | apply (na_val1 (mrestrict (w_H W) memA) tx T 436 HBY); vm_compute; reflexivity ].
        -- apply (chunk_ok_val SEGS E _ tx 437 1 (SOff 35 0) (tb T 437));
             [ exact (den0 E 35 _ E35) | cbn; lia | cbn; lia
             | apply (na_val1 (mrestrict (w_H W) memA) tx T 437 HBY); vm_compute; reflexivity ].
      * rewrite U8. split; [lia|]. split; [lia|].
        split; [intros o Ho; apply (apresent_writable SEGS); exact (proj1 (Hgpres (tx + o) ltac:(lia)))|].
        repeat apply Forall_cons; try apply Forall_nil.
        -- apply (chunk_ok_val SEGS E _ tx 440 4 (SOff 36 0) (u32at T 440));
             [ exact (den0 E 36 _ E36) | cbn; lia | cbn; lia
             | apply (na_val4 (mrestrict (w_H W) memA) tx T 440 HBY);
               intros d Hd; assert (d = 0 \/ d = 1 \/ d = 2 \/ d = 3) as [-> | [-> | [-> | ->]]] by lia;
               vm_compute; reflexivity ].
        -- apply (chunk_ok_val SEGS E _ tx 444 4 (SOff 37 0) (u32at T 444));
             [ exact (den0 E 37 _ E37) | cbn; lia | cbn; lia
             | apply (na_val4 (mrestrict (w_H W) memA) tx T 444 HBY);
               intros d Hd; assert (d = 0 \/ d = 1 \/ d = 2 \/ d = 3) as [-> | [-> | [-> | ->]]] by lia;
               vm_compute; reflexivity ].
        -- apply (chunk_ok_val SEGS E _ tx 448 1 (SOff 38 0) (tb T 448));
             [ exact (den0 E 38 _ E38) | cbn; lia | cbn; lia
             | apply (na_val1 (mrestrict (w_H W) memA) tx T 448 HBY); vm_compute; reflexivity ].
    + apply pairwise_disjoint_of_extents.
      unfold na_regs, STKA, TXA, TXB, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, U8.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold NX_FRAME in *. repeat split; lia.
    + split; [|split; [exact I | exact I]].
      cbn [na_atoms f_atoms atoms_ok]. unfold afact_ok, PTRN. cbn [af_lo af_hi af_al2].
      rewrite Usp, U8, U32, U34, U35, U36, U37, U38.
      change (2 ^ 4) with 16. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
      unfold TX_SIZE, ATx.TX_SIZE, NX_FRAME, SB_NX in *.
      repeat match goal with |- _ /\ _ => split end; try lia;
        (replace (spZ regs - 96) with (spZ regs + (-6) * 16) by lia;
         rewrite Z_mod_plus_full; exact Hsp16).
  - unfold sh_ok, na_SH. constructor; [|constructor].
    apply (shent_ok_of_block SEGS B LAWS lyc Sc W memA mdA E BxN 8 tx TX_SIZE 0 460 HARj Hg).
    + unfold U, BxN. rewrite (den0 E 32 _ E32). unfold w64, SHADOW_OFF, SB_NX.
      apply unsigned_lit_small. lia.
    + unfold U. rewrite (den0 E 8 _ E8), R8. unfold w64. apply unsigned_lit_small. lia.
    + lia.
    + change (req_size TX_SIZE) with 460. lia.
Qed.

Ltac na_awr_tac U2 U8 Hwtab :=
  lazymatch goal with |- awr_ok ?Ey ?rs _ _ _ _ _ _ _ =>
    eapply (na_awr Ey rs); [vm_compute; reflexivity | exact U2 | exact U8 | exact Hwtab] end.

(* After a run: the bytes outside the two fields stay, and what was present stays present. *)
Ltac na_carry E U2 U8 :=
  lazymatch goal with
  | HFr : frame_of E ?rs (mrestrict (w_H ?W) ?m1) (mrestrict (w_H ?W) ?m2),
    HG : mem_grows (mrestrict (w_H ?W) ?m1) (mrestrict (w_H ?W) ?m2),
    HM : na_meq ?W ?m0 ?m1 ?tx, HPR : na_pres ?W ?m0 ?m1 |- _ =>
      let HM' := fresh "HM" in let HPR' := fresh "HPR" in
      pose proof (na_meq_trans W m0 m1 m2 tx HM
                    (na_meq_of_frame E rs W m1 m2 _ tx ltac:(vm_compute; reflexivity) U2 U8 HFr)) as HM';
      pose proof (na_pres_step W m0 m1 m2 HPR HG) as HPR';
      clear HM HPR HFr HG; rename HM' into HM; rename HPR' into HPR
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end.

Ltac na_reg HS r v pf H :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?vl ?Ex ?ss (restrict ?Hh ?ms) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    assert (H : getr (ms_regs ms) r = v)
      by (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ss ms r HS) _);
          change (sv_denot Ex e = v); pf)
  end.

Ltac na_region HS i H :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
    let r := eval vm_compute in (nth_error (ss_mem ssx) i) in
    lazymatch r with Some ?rr =>
      pose proof (st_ok_pi_region_nth Ex ssx msx i rr HS ltac:(vm_compute; reflexivity)) as H
    end
  end;
  cbn [restrict ms_mem] in H.

Ltac na_inlist := repeat (first [left; reflexivity | right]).

Ltac na_mid HJ HSAME HM HPR HpresS HpresK HQ Hoc Hop Hov :=
  unfold nx_mid; split; [exact HJ|]; split; [exact (na_same _ _ _ _ _ _ _ _ _ HSAME HM)|];
  split; [intros a Ha; exact (HPR a (HpresS a Ha))|];
  split; [intros a Ha; exact (HPR a (HpresK a Ha))|];
  exact (na_outq _ _ _ _ _ _ _ _ HQ HM Hoc Hop Hov).

(* ---- the segment ----------------------------------------------------------------------------- *)
Theorem nx_after : nx_rloop_spec B -> nx_resweep_spec B -> nx_after_stmt B.
Proof.
  intros RLOOP RSWEEP.
  unfold nx_after_stmt.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsA memA mdA tx chp parp valp T
    HCTX HMID HSAV HOBJ Hact Hz HAT.
  destruct (na_seat_aftr STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsA memA mdA
    tx chp parp valp T HCTX HMID HSAV HOBJ HAT) as [HS SHOK].
  pose proof HAT as (HKEEP & R2 & R8 & R9 & R11 & R12 & R21).
  pose proof HCTX as (HAR & Hg & Hoc & Hop & Hov & Dcp & Dcv & Dpv & Pc & Pp & Pv & Rac & Rap & Rav &
    Rt456 & Hspr & Hceil & Hsp16 & Hslo & Hshi & Hwtab & Hwc & Hwp & Hwv & Hret & Hra4 & Hgp & Htp &
    Q8 & Q11 & Q12 & Q13 & HTL & HTHD & Hobjc & Hpresc).
  pose proof HMID as (HJ & HSAME & HpresS & HpresK & HQ).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (al_blocks _ _ LAWS lyc Sc W memc mdc tx TX_SIZE HAR Hg) as (Hg16 & Hg4096 & Hgceil & _ & _ & _).
  change (req_size TX_SIZE) with 460 in Hgceil.
  rewrite nx_stk_val in Hceil, Hslo.
  pose proof (ATx.tb_range T 436) as R34. pose proof (ATx.tb_range T 437) as R35.
  pose proof (ATx.tb_range T 448) as R38.
  pose proof (na_u32at_range T 440) as R36. pose proof (na_u32at_range T 444) as R37.
  pose proof (s32_bound T 440) as S440. pose proof (s32_bound T 444) as S444.
  (* the table is 16-aligned, so the cursor's granule offset is 0 and the four-byte check's
     bound register is the literal 3 *)
  assert (Hal8 : (tx + 440) mod 8 = 0).
  { apply Z.mod_divide; [lia|]. apply Z.divide_add_r.
    - apply (Z.divide_trans 8 16 tx); [exists 2; reflexivity|].
      apply Z.mod_divide; [lia | exact Hg16].
    - exists 55; reflexivity. }
  assert (Hoc' : na_out tx chp)
    by (destruct Hoc as (A1 & A2 & A3 & _); unfold na_out, ATx.TX_SIZE in *; split; lia).
  assert (Hop' : na_out tx parp)
    by (destruct Hop as (A1 & A2 & A3 & _); unfold na_out, ATx.TX_SIZE in *; split; lia).
  assert (Hov' : na_out tx valp)
    by (destruct Hov as (A1 & A2 & A3 & _); unfold na_out, ATx.TX_SIZE in *; split; lia).
  remember (EA regs tx T regsA) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (rewrite HE; unfold EA; apply Eimg_env).
  na_env_facts E HE regs regsA tx T.
  assert (HAE : env_agree 32 (Ereg regsA (na_extra regs tx T)) E)
    by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | rewrite HE; reflexivity]).
  clear HE EL.
  assert (Usp : bv_unsigned (ew E 2) = spZ regs - NX_FRAME)
    by (rewrite E2, R2; apply unsigned_lit_small; unfold NX_FRAME; lia).
  assert (U8 : bv_unsigned (ew E 8) = tx)
    by (rewrite E8, R8; apply unsigned_lit_small; lia).
  assert (U35 : bv_unsigned (ew E 35) = tb T 437) by (rewrite E35; apply unsigned_lit_small; lia).
  assert (U36 : bv_unsigned (ew E 36) = u32at T 440) by (rewrite E36; apply unsigned_lit_small; lia).
  assert (U37 : bv_unsigned (ew E 37) = u32at T 444) by (rewrite E37; apply unsigned_lit_small; lia).
  assert (HM : na_meq W memA memA tx) by apply na_meq_refl.
  assert (HPR : na_pres W memA memA) by (intros a Ha; exact Ha).
  unfold cfg_at. change (w64 (BASE + AFTR)) with (Z_to_bv 64 (BASE + AFTR)).
  (* the shadow check of replay_width and its test, 0x86118 *)
  paj_run_tok RUN HS HJ SHOK BspanN; [na_awr_tac Usp U8 Hwtab |].
  na_carry E Usp U8.
  psrr_branch_tok RUN BR HS SHOK BspanN.
  - (* replay_width = 0: on to the re-assert tail *)
    rewrite (bt_eq0 E 35 (tb T 437) E35 ltac:(lia)) in Hc. apply Z.eqb_eq in Hc. rename Hc into Hw0.
    paj_run_to_tok RUNTO HS HJ SHOK BspanN RSWP; [na_awr_tac Usp U8 Hwtab |].
    na_carry E Usp U8.
    na_region HS 1%nat HRA. na_region HS 2%nat HRB.
    na_reg HS (2%bv : bv 5) (w64 (spZ regs - NX_FRAME)) ltac:(exact (den0 E 2 _ (eq_trans E2 R2))) G2.
    na_reg HS (3%bv : bv 5) (getr regsA 3) ltac:(exact (den0 E 3 _ E3)) G3.
    na_reg HS (4%bv : bv 5) (getr regsA 4) ltac:(exact (den0 E 4 _ E4)) G4.
    na_reg HS (27%bv : bv 5) (getr regsA 27) ltac:(exact (den0 E 27 _ E27)) G27.
    na_reg HS (8%bv : bv 5) (w64 tx) ltac:(exact (den0 E 8 _ (eq_trans E8 R8))) G8.
    na_reg HS (9%bv : bv 5) (w64 valp) ltac:(exact (den0 E 9 _ (eq_trans E9 R9))) G9.
    na_reg HS (11%bv : bv 5) (w64 chp) ltac:(exact (den0 E 11 _ (eq_trans E11 R11))) G11.
    na_reg HS (12%bv : bv 5) (w64 parp) ltac:(exact (den0 E 12 _ (eq_trans E12 R12))) G12.
    na_reg HS (21%bv : bv 5) (w64 SB_NX) ltac:(exact (den0 E 32 _ E32)) G21.
    na_reg HS (18%bv : bv 5) (w64 (tx + 437)) ltac:(exact (denk E 8 tx 437 U8)) G18.
    na_reg HS (22%bv : bv 5) (w64 (SHADOW_OFF + (tx + 437) / 8))
      ltac:(apply den_shadow; [exact U8 | exact E32 | lia]) G22.
    rewrite (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rj _ ?mj _) ?dj) _ =>
      refine (RSWEEP STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs rj mj dj
                tx chp parp valp T T HCTX _ _ _ _ _ _ _ _) end.
    + na_mid HJ HSAME HM HPR HpresS HpresK HQ Hoc' Hop' Hov'.
    + exact (na_saved W memA _ regs tx HM ltac:(lia) ltac:(rewrite nx_stk_val; lia) ltac:(lia) HSAV).
    + eapply (na_table E W memA _ tx T T _ _ _ _ HOBJ HM);
        [ lia | lia | exact U8 | exact HRA | exact HRB | na_inlist | na_inlist
        | intros i _ _ _; reflexivity
        | rewrite (den0 E 35 _ E35); exact (bw_tb T 437)
        | intros j Hj; rewrite (den0 E 37 _ E37); exact (bw_u32 T 444 j Hj) ].
    + exact HTL.
    + exact Hw0.
    + intros l Hl. reflexivity.
    + rewrite (nx_model_after T tx Hact Hz). apply nx_after_w0. exact Hw0.
    + unfold nx_at_rswp, nx_keep_gp.
      split; [intros r Hr; cbv [In] in Hr; destruct Hr as [<-|[<-|[<-|[]]]];
              first [exact (eq_trans G3 (HKEEP 3%bv ltac:(na_inlist)))
                    | exact (eq_trans G4 (HKEEP 4%bv ltac:(na_inlist)))
                    | exact (eq_trans G27 (HKEEP 27%bv ltac:(na_inlist)))]|].
      repeat split; assumption.
  - rewrite (bt_eq0 E 35 (tb T 437) E35 ltac:(lia)) in Hc. apply Z.eqb_neq in Hc. rename Hc into Hw.
    (* the shadow check of replay_wait and its test, 0x86134 *)
    paj_run_tok RUN HS HJ SHOK BspanN; [na_awr_tac Usp U8 Hwtab |].
    na_carry E Usp U8.
    psrr_branch_tok RUN BR HS SHOK BspanN.
    + (* replay_wait <= 0 *)
      rewrite (bt_ge E (SLit 0) (SExt true 32 (SOff 37 0)) 0 (s32 T 444) eq_refl
                 ltac:(rewrite (den_lw E 37 (u32at T 444) E37 ltac:(lia));
                       rewrite s32_of_u32; reflexivity)
                 ltac:(lia) ltac:(lia)) in Hc.
      apply negb_true_iff, Z.ltb_ge in Hc. rename Hc into Hwait.
      (* the shadow check of replay_idx, then the bound register a4 = max(replay_idx,
         3 * replay_width) at 0x86174, and the scan's own test at 0x8617c *)
      paj_run_tok RUN HS HJ SHOK BspanN; [na_awr_tac Usp U8 Hwtab |].
      na_carry E Usp U8.
      assert (Hidx0 : 0 <= s32 T 440) by (exact (HTHD Hw)).
      assert (D36 : sv_denot E (SExt true 32 (SOff 36 0)) = w64 (s32 T 440))
        by (rewrite (den_lw E 36 (u32at T 440) E36 ltac:(lia)); rewrite s32_of_u32; reflexivity).
      assert (D35 : sv_denot E (SMd M_MUL (SOff 35 0) (SLit 3))
                    = w64 (3 * tb T 437))
        by (apply den_mul3; [exact E35 | lia]).
      psrr_branch_tok RUN BR HS SHOK BspanN.
      * (* 3 * replay_width < replay_idx: a4 keeps replay_idx, and the scan is exhausted *)
        rewrite (bt_lt E (SMd M_MUL (SOff 35 0) (SLit 3))
                   (SExt true 32 (SOff 36 0)) (3 * tb T 437) (s32 T 440) D35 D36
                   ltac:(lia) ltac:(lia)) in Hc.
        apply Z.ltb_lt in Hc. rename Hc into Hgt.
        paj_run_tok RUN HS HJ SHOK BspanN; [na_awr_tac Usp U8 Hwtab |].
        try na_carry E Usp U8.
        psrr_branch_tok RUN BR HS SHOK BspanN;
          [| exfalso;
             rewrite (bt_ge E (SExt true 32 (SOff 36 0))
                        (SMd M_MUL (SOff 35 0) (SLit 3))
                        (s32 T 440) (3 * tb T 437) D36 D35 ltac:(lia) ltac:(lia)) in Hc;
             apply negb_false_iff, Z.ltb_lt in Hc; lia ].
        rewrite (bt_ge E (SExt true 32 (SOff 36 0))
                   (SMd M_MUL (SOff 35 0) (SLit 3))
                   (s32 T 440) (3 * tb T 437) D36 D35 ltac:(lia) ltac:(lia)) in Hc.
        apply negb_true_iff, Z.ltb_ge in Hc. rename Hc into Hidx.
        paj_run_to_tok RUNTO HS HJ SHOK BspanN RSWP; [na_awr_tac Usp U8 Hwtab |].
        na_carry E Usp U8.
        na_region HS 1%nat HRA. na_region HS 2%nat HRB.
        na_reg HS (2%bv : bv 5) (w64 (spZ regs - NX_FRAME)) ltac:(exact (den0 E 2 _ (eq_trans E2 R2))) G2.
        na_reg HS (3%bv : bv 5) (getr regsA 3) ltac:(exact (den0 E 3 _ E3)) G3.
        na_reg HS (4%bv : bv 5) (getr regsA 4) ltac:(exact (den0 E 4 _ E4)) G4.
        na_reg HS (27%bv : bv 5) (getr regsA 27) ltac:(exact (den0 E 27 _ E27)) G27.
        na_reg HS (8%bv : bv 5) (w64 tx) ltac:(exact (den0 E 8 _ (eq_trans E8 R8))) G8.
        na_reg HS (9%bv : bv 5) (w64 valp) ltac:(exact (den0 E 9 _ (eq_trans E9 R9))) G9.
        na_reg HS (11%bv : bv 5) (w64 chp) ltac:(exact (den0 E 11 _ (eq_trans E11 R11))) G11.
        na_reg HS (12%bv : bv 5) (w64 parp) ltac:(exact (den0 E 12 _ (eq_trans E12 R12))) G12.
        na_reg HS (21%bv : bv 5) (w64 SB_NX) ltac:(exact (den0 E 32 _ E32)) G21.
        na_reg HS (18%bv : bv 5) (w64 (tx + 437)) ltac:(exact (denk E 8 tx 437 U8)) G18.
        na_reg HS (22%bv : bv 5) (w64 (SHADOW_OFF + (tx + 437) / 8))
          ltac:(apply den_shadow; [exact U8 | exact E32 | lia]) G22.
        rewrite (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
        lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rj _ ?mj _) ?dj) _ =>
          refine (RSWEEP STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs rj mj dj
                    tx chp parp valp T (setb T 437 0) HCTX _ _ _ _ _ _ _ _) end.
        -- na_mid HJ HSAME HM HPR HpresS HpresK HQ Hoc' Hop' Hov'.
        -- exact (na_saved W memA _ regs tx HM ltac:(lia) ltac:(rewrite nx_stk_val; lia) ltac:(lia) HSAV).
        -- eapply (na_table E W memA _ tx T (setb T 437 0) _ _ _ _ HOBJ HM);
             [ lia | lia | exact U8 | exact HRA | exact HRB | na_inlist | na_inlist
             | intros i Hi H1 H2; rewrite <- !Z_to_bv8_tb; f_equal;
               apply tb_setb_out; [exact HTL | lia | lia | lia]
             | rewrite <- Z_to_bv8_tb, (tb_setb_in T 437 0 HTL ltac:(lia) ltac:(lia)); reflexivity
             | intros j Hj; rewrite (den0 E 37 _ E37); unfold w64; rewrite (bw_u32 T 444 j Hj);
               rewrite <- !Z_to_bv8_tb; f_equal; symmetry;
               apply tb_setb_out; [exact HTL | lia | lia | lia] ].
        -- apply len_setb; [exact HTL | lia].
        -- apply tb_setb_in; [exact HTL | lia | lia].
        -- intros l Hl. apply tb_setb_out; [exact HTL | lia | lia | lia].
        -- rewrite (nx_model_after T tx Hact Hz). apply nx_after_done; [exact Hw | exact Hwait | exact Hidx].
        -- unfold nx_at_rswp, nx_keep_gp.
           split; [intros r Hr; cbv [In] in Hr; destruct Hr as [<-|[<-|[<-|[]]]];
                   first [exact (eq_trans G3 (HKEEP 3%bv ltac:(na_inlist)))
                         | exact (eq_trans G4 (HKEEP 4%bv ltac:(na_inlist)))
                         | exact (eq_trans G27 (HKEEP 27%bv ltac:(na_inlist)))]|].
           repeat split; assumption.
      * (* replay_idx <= 3 * replay_width: the bound register takes 3 * replay_width, and the
           test at 0x8617c decides between the exhausted scan and the scan's head *)
        rewrite (bt_lt E (SMd M_MUL (SOff 35 0) (SLit 3))
                   (SExt true 32 (SOff 36 0)) (3 * tb T 437) (s32 T 440) D35 D36
                   ltac:(lia) ltac:(lia)) in Hc.
        apply Z.ltb_ge in Hc. rename Hc into Hle.
        paj_run_tok RUN HS HJ SHOK BspanN; [na_awr_tac Usp U8 Hwtab |].
        na_carry E Usp U8.
        psrr_branch_tok RUN BR HS SHOK BspanN.
        -- (* replay_idx >= 3 * replay_width, so it is equal: the scan is exhausted *)
           rewrite (bt_ge E (SExt true 32 (SOff 36 0))
                      (SMd M_MUL (SOff 35 0) (SLit 3))
                      (s32 T 440) (3 * tb T 437) D36 D35 ltac:(lia) ltac:(lia)) in Hc.
           apply negb_true_iff, Z.ltb_ge in Hc. rename Hc into Hidx.
           paj_run_to_tok RUNTO HS HJ SHOK BspanN RSWP; [na_awr_tac Usp U8 Hwtab |].
           na_carry E Usp U8.
           na_region HS 1%nat HRA. na_region HS 2%nat HRB.
           na_reg HS (2%bv : bv 5) (w64 (spZ regs - NX_FRAME))
             ltac:(exact (den0 E 2 _ (eq_trans E2 R2))) G2.
           na_reg HS (3%bv : bv 5) (getr regsA 3) ltac:(exact (den0 E 3 _ E3)) G3.
           na_reg HS (4%bv : bv 5) (getr regsA 4) ltac:(exact (den0 E 4 _ E4)) G4.
           na_reg HS (27%bv : bv 5) (getr regsA 27) ltac:(exact (den0 E 27 _ E27)) G27.
           na_reg HS (8%bv : bv 5) (w64 tx) ltac:(exact (den0 E 8 _ (eq_trans E8 R8))) G8.
           na_reg HS (9%bv : bv 5) (w64 valp) ltac:(exact (den0 E 9 _ (eq_trans E9 R9))) G9.
           na_reg HS (11%bv : bv 5) (w64 chp) ltac:(exact (den0 E 11 _ (eq_trans E11 R11))) G11.
           na_reg HS (12%bv : bv 5) (w64 parp) ltac:(exact (den0 E 12 _ (eq_trans E12 R12))) G12.
           na_reg HS (21%bv : bv 5) (w64 SB_NX) ltac:(exact (den0 E 32 _ E32)) G21.
           na_reg HS (18%bv : bv 5) (w64 (tx + 437)) ltac:(exact (denk E 8 tx 437 U8)) G18.
           na_reg HS (22%bv : bv 5) (w64 (SHADOW_OFF + (tx + 437) / 8))
             ltac:(apply den_shadow; [exact U8 | exact E32 | lia]) G22.
           rewrite (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
           lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rj _ ?mj _) ?dj) _ =>
             refine (RSWEEP STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs rj mj dj
                       tx chp parp valp T (setb T 437 0) HCTX _ _ _ _ _ _ _ _) end.
           ++ na_mid HJ HSAME HM HPR HpresS HpresK HQ Hoc' Hop' Hov'.
           ++ exact (na_saved W memA _ regs tx HM ltac:(lia) ltac:(rewrite nx_stk_val; lia)
                       ltac:(lia) HSAV).
           ++ eapply (na_table E W memA _ tx T (setb T 437 0) _ _ _ _ HOBJ HM);
                [ lia | lia | exact U8 | exact HRA | exact HRB | na_inlist | na_inlist
                | intros i Hi H1 H2; rewrite <- !Z_to_bv8_tb; f_equal;
                  apply tb_setb_out; [exact HTL | lia | lia | lia]
                | rewrite <- Z_to_bv8_tb, (tb_setb_in T 437 0 HTL ltac:(lia) ltac:(lia)); reflexivity
                | intros j Hj; rewrite (den0 E 37 _ E37); unfold w64; rewrite (bw_u32 T 444 j Hj);
                  rewrite <- !Z_to_bv8_tb; f_equal; symmetry;
                  apply tb_setb_out; [exact HTL | lia | lia | lia] ].
           ++ apply len_setb; [exact HTL | lia].
           ++ apply tb_setb_in; [exact HTL | lia | lia].
           ++ intros l Hl. apply tb_setb_out; [exact HTL | lia | lia | lia].
           ++ rewrite (nx_model_after T tx Hact Hz).
              apply nx_after_done; [exact Hw | exact Hwait | exact Hidx].
           ++ unfold nx_at_rswp, nx_keep_gp.
              split; [intros r Hr; cbv [In] in Hr; destruct Hr as [<-|[<-|[<-|[]]]];
                      first [exact (eq_trans G3 (HKEEP 3%bv ltac:(na_inlist)))
                            | exact (eq_trans G4 (HKEEP 4%bv ltac:(na_inlist)))
                            | exact (eq_trans G27 (HKEEP 27%bv ltac:(na_inlist)))]|].
              repeat split; assumption.
        -- (* replay_idx < 3 * replay_width: on to the replay scan's head *)
           rewrite (bt_ge E (SExt true 32 (SOff 36 0))
                      (SMd M_MUL (SOff 35 0) (SLit 3))
                      (s32 T 440) (3 * tb T 437) D36 D35 ltac:(lia) ltac:(lia)) in Hc.
           apply negb_false_iff, Z.ltb_lt in Hc. rename Hc into Hidx.
           paj_run_to_tok RUNTO HS HJ SHOK BspanN LOOPR; [na_awr_tac Usp U8 Hwtab |].
           na_carry E Usp U8.
           na_region HS 1%nat HRA. na_region HS 2%nat HRB.
           na_reg HS (2%bv : bv 5) (w64 (spZ regs - NX_FRAME))
             ltac:(exact (den0 E 2 _ (eq_trans E2 R2))) G2.
           na_reg HS (3%bv : bv 5) (getr regsA 3) ltac:(exact (den0 E 3 _ E3)) G3.
           na_reg HS (4%bv : bv 5) (getr regsA 4) ltac:(exact (den0 E 4 _ E4)) G4.
           na_reg HS (27%bv : bv 5) (getr regsA 27) ltac:(exact (den0 E 27 _ E27)) G27.
           na_reg HS (8%bv : bv 5) (w64 tx) ltac:(exact (den0 E 8 _ (eq_trans E8 R8))) G8.
           na_reg HS (9%bv : bv 5) (w64 valp) ltac:(exact (den0 E 9 _ (eq_trans E9 R9))) G9.
           na_reg HS (11%bv : bv 5) (w64 chp) ltac:(exact (den0 E 11 _ (eq_trans E11 R11))) G11.
           na_reg HS (12%bv : bv 5) (w64 parp) ltac:(exact (den0 E 12 _ (eq_trans E12 R12))) G12.
           na_reg HS (21%bv : bv 5) (w64 SB_NX) ltac:(exact (den0 E 32 _ E32)) G21.
           na_reg HS (18%bv : bv 5) (w64 (tx + 437)) ltac:(exact (denk E 8 tx 437 U8)) G18.
           na_reg HS (22%bv : bv 5) (w64 (SHADOW_OFF + (tx + 437) / 8))
             ltac:(apply den_shadow; [exact U8 | exact E32 | lia]) G22.
           na_reg HS (19%bv : bv 5) (w64 (tx + 444)) ltac:(exact (denk E 8 tx 444 U8)) G19.
           na_reg HS (23%bv : bv 5) (w64 (SHADOW_OFF + (tx + 444) / 8))
             ltac:(apply den_shadow; [exact U8 | exact E32 | lia]) G23.
           na_reg HS (20%bv : bv 5) (w64 (tx + 440)) ltac:(exact (denk E 8 tx 440 U8)) G20.
           na_reg HS (24%bv : bv 5) (w64 (SHADOW_OFF + (tx + 440) / 8))
             ltac:(apply den_shadow; [exact U8 | exact E32 | lia]) G24.
           na_reg HS (25%bv : bv 5) (w64 (3 * tb T 437)) ltac:(exact D35) G25.
           na_reg HS (26%bv : bv 5) (w64 ((tx + 440) mod 8 + 3))
             ltac:(rewrite Hal8; reflexivity) G26.
           na_reg HS (5%bv : bv 5) (w64 (s32 T 440)) ltac:(exact D36) G5.
           na_reg HS (14%bv : bv 5) (w64 (Z.max (s32 T 440) (3 * tb T 437)))
             ltac:(rewrite Z.max_r by lia; exact D35) G14.
           na_reg HS (15%bv : bv 5) (w64 (tb T 436)) ltac:(exact (den0 E 34 _ E34)) G15.
           na_reg HS (13%bv : bv 5) (w64 (tb T 448)) ltac:(exact (den0 E 38 _ E38)) G13.
           na_reg HS (16%bv : bv 5) (w64 (tx + 144)) ltac:(exact (denk E 8 tx 144 U8)) G16.
           na_reg HS (6%bv : bv 5) (w64 (18446744073709551615 - (tx + 144)))
             ltac:(apply den_not; [exact U8 | lia]) G6.
           na_reg HS (7%bv : bv 5) (w64 1431655766) ltac:(reflexivity) G7.
           na_reg HS (28%bv : bv 5) (w64 47) ltac:(reflexivity) G28.
           rewrite (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
           assert (Hnz : 0 < 3 * tb T 437 - s32 T 440) by lia.
           destruct (Z.to_nat (3 * tb T 437 - s32 T 440)) as [|n'] eqn:Hn; [lia|].
           lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rj _ ?mj _) ?dj) _ =>
             refine (RLOOP (Datatypes.S n') STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
                       rj mj dj tx chp parp valp T (s32 T 440) HCTX _ _ _ _ _ _ _ _ _) end.
           ++ na_mid HJ HSAME HM HPR HpresS HpresK HQ Hoc' Hop' Hov'.
           ++ exact (na_saved W memA _ regs tx HM ltac:(lia) ltac:(rewrite nx_stk_val; lia)
                       ltac:(lia) HSAV).
           ++ apply (na_obj_eq _ tx T);
                [ intros i Hi; rewrite (s32_u32_nonneg T 440 Hidx0);
                  apply set4_self_nth; [exact HTL | lia | lia | lia]
                | eapply (na_table E W memA _ tx T T _ _ _ _ HOBJ HM);
                  [ lia | lia | exact U8 | exact HRA | exact HRB | na_inlist | na_inlist
                  | intros i _ _ _; reflexivity
                  | rewrite (den0 E 35 _ E35); exact (bw_tb T 437)
                  | intros j Hj; rewrite (den0 E 37 _ E37); exact (bw_u32 T 444 j Hj) ] ].
           ++ exact Hw.
           ++ exact Hidx0.
           ++ lia.
           ++ rewrite <- Hn. rewrite Z2Nat.id by lia. reflexivity.
           ++ rewrite (nx_model_after T tx Hact Hz), (nx_after_walk T tx Hw Hwait Hidx), Hn.
              apply walk_set4_self. exact HTL.
           ++ unfold nx_at_loopr, nx_keep_gp.
              split; [intros r Hr; cbv [In] in Hr; destruct Hr as [<-|[<-|[<-|[]]]];
                      first [exact (eq_trans G3 (HKEEP 3%bv ltac:(na_inlist)))
                            | exact (eq_trans G4 (HKEEP 4%bv ltac:(na_inlist)))
                            | exact (eq_trans G27 (HKEEP 27%bv ltac:(na_inlist)))]|].
              repeat split; assumption.
    + (* replay_wait > 0: replay_wait := replay_wait - 1, and the call returns 0 *)
      rewrite (bt_ge E (SLit 0) (SExt true 32 (SOff 37 0)) 0 (s32 T 444) eq_refl
                 ltac:(rewrite (den_lw E 37 (u32at T 444) E37 ltac:(lia));
                       rewrite s32_of_u32; reflexivity)
                 ltac:(lia) ltac:(lia)) in Hc.
      apply negb_false_iff, Z.ltb_lt in Hc. rename Hc into Hwait.
      assert (D37 : sv_denot E (SExt true 32 (SOff 37 0)) = w64 (s32 T 444))
        by (rewrite (den_lw E 37 (u32at T 444) E37 ltac:(lia)); rewrite s32_of_u32; reflexivity).
      paj_run_tok RUN HS HJ SHOK BspanN; [na_awr_tac Usp U8 Hwtab |].
      na_carry E Usp U8.
      na_region HS 1%nat HRA. na_region HS 2%nat HRB.
      na_reg HS (1%bv : bv 5) (getr regs 1) ltac:(exact (den0 E 56 _ X56)) G1.
      na_reg HS (10%bv : bv 5) (w64 0) ltac:(reflexivity) G10.
      (* the epilogue's twelve reloads give the caller's registers back *)
      na_reg HS (2%bv : bv 5) (getr regs 2)
        ltac:(rewrite (denk E 2 _ 96 Usp);
              replace (spZ regs - NX_FRAME + 96) with (spZ regs) by (unfold NX_FRAME; lia);
              unfold w64, spZ; apply Z_to_bv_bv_unsigned) R2f.
      na_reg HS (3%bv : bv 5) (getr regs 3)
        ltac:(rewrite (den0 E 3 _ E3); apply HKEEP; na_inlist) R3f.
      na_reg HS (4%bv : bv 5) (getr regs 4)
        ltac:(rewrite (den0 E 4 _ E4); apply HKEEP; na_inlist) R4f.
      na_reg HS (8%bv : bv 5) (getr regs 8) ltac:(exact (den0 E 57 _ X57)) R8f.
      na_reg HS (9%bv : bv 5) (getr regs 9) ltac:(exact (den0 E 58 _ X58)) R9f.
      na_reg HS (18%bv : bv 5) (getr regs 18) ltac:(exact (den0 E 59 _ X59)) R18f.
      na_reg HS (19%bv : bv 5) (getr regs 19) ltac:(exact (den0 E 60 _ X60)) R19f.
      na_reg HS (20%bv : bv 5) (getr regs 20) ltac:(exact (den0 E 61 _ X61)) R20f.
      na_reg HS (21%bv : bv 5) (getr regs 21) ltac:(exact (den0 E 62 _ X62)) R21f.
      na_reg HS (22%bv : bv 5) (getr regs 22) ltac:(exact (den0 E 63 _ X63)) R22f.
      na_reg HS (23%bv : bv 5) (getr regs 23) ltac:(exact (den0 E 64 _ X64)) R23f.
      na_reg HS (24%bv : bv 5) (getr regs 24) ltac:(exact (den0 E 65 _ X65)) R24f.
      na_reg HS (25%bv : bv 5) (getr regs 25) ltac:(exact (den0 E 66 _ X66)) R25f.
      na_reg HS (26%bv : bv 5) (getr regs 26) ltac:(exact (den0 E 67 _ X67)) R26f.
      na_reg HS (27%bv : bv 5) (getr regs 27)
        ltac:(rewrite (den0 E 27 _ E27); apply HKEEP; na_inlist) R27f.
      pose proof (aregs_preserved_eqs regs _ R2f R3f R4f R8f R9f R18f R19f R20f R21f R22f
                    R23f R24f R25f R26f R27f) as HP.
      eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
      intros matB. cbn [ms_regs ms_mem]. rewrite G1, Hret.
      lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
        apply (nx_finish B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs (ms_regs msx)
                 (ms_mem msx) _ tx chp parp valp (tx + 432) T (set4 T 444 (s32 T 444 - 1)) 0 0 0 0) end.
      * unfold TX_SIZE, ATx.TX_SIZE. lia.
      * exact HAR.
      * exact Hg.
      * exact Hoc.
      * exact Hop.
      * exact Hov.
      * exact Hspr.
      * rewrite nx_stk_val. lia.
      * rewrite (nx_model_after T tx Hact Hz), (nx_after_wait T tx Hw Hwait). reflexivity.
      * apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ.
      * exact HP.
      * exact (na_same _ _ _ _ _ _ _ _ _ HSAME HM).
      * intros a Ha. exact (HPR a (HpresS a Ha)).
      * intros a Ha. exact (HPR a (HpresK a Ha)).
      * exact G10.
      * eapply (na_table E W memA _ tx T (set4 T 444 (s32 T 444 - 1)) _ _ _ _ HOBJ HM);
          [ lia | lia | exact U8 | exact HRA | exact HRB | na_inlist | na_inlist
          | intros i Hi H1 H2; rewrite <- !Z_to_bv8_tb; f_equal;
            apply tb_set4_out; [exact HTL | lia | lia | lia | lia]
          | rewrite (den0 E 35 _ E35); unfold w64; rewrite (bw_tb T 437);
            rewrite <- !Z_to_bv8_tb; f_equal; symmetry;
            apply tb_set4_out; [exact HTL | lia | lia | lia | lia]
          | intros j Hj;
            rewrite (den_sub1 E (SExt true 32 (SOff 37 0)) (s32 T 444) D37 ltac:(lia) ltac:(lia));
            unfold w64;
            replace (s32 T 444 + -1) with (u32at (set4 T 444 (s32 T 444 - 1)) 444);
            [ exact (bw_u32 _ 444 j Hj)
            | rewrite u32at_u32,
                (u32_set4 T 444 (s32 T 444 - 1) HTL ltac:(lia) ltac:(lia) ltac:(lia)); lia ] ].
      * apply thd_ok_set4_out; [exact HTL | lia | lia | right; lia | exact HTHD].
      * intros H01. discriminate H01.
      * intros _. exact (na_outq _ _ _ _ _ _ _ _ HQ HM Hoc' Hop' Hov').
Qed.

End h.
End f.
End d.
