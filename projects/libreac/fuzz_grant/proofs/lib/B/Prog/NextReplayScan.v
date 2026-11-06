(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a segment of reac_headamp_tx_next on fuzz_grant.asan (NextReplayScan), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Modified by Theorem Labs, 2026-10: image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/NextReplayScan.v at a working branch af735a950e2 (blob 2b7617b54e2; the walk was ported from blob 0dda94ac0b9 at a working branch afd75724b5b, which differs from it only by 4 added and 0 removed lines, the licence header), restated over image B's listing, addresses and walk layer (lib/B/Prog) against GrantBContracts.v; UBSan traps T12..T15, refuted from thd_replay_ok; the cell > 47 branch is reachable without I1 *)
(* The replay scan of reac_headamp_tx_next on the ASan+UBSan build (fuzz_grant.asan-ubsan, from the cut
   LOOPR 0x861cc to where the scan leaves it): the proof of nx_rloop_spec (lib/B/Prog/HeadampTxNext.v).

   One pass of the loop handles one cursor value j (Pau Aliagas's walk, lib/Prog/NextModel.v): the cell
   c = tb T 436 + j / 3 and its parameter p = j mod 3 come out of the multiply by 0x55555556, the cursor
   440 is stored as j + 1 (0x861f8), and then
     - the set-only flag 448 is 0 (0x861fc), or c <= 47 and the cell's set byte 144 + 3c + p is not 0
       (0x8623c): the code branches to the emit block 0x863a0, and the walk applies the emit cut
       (nx_emit_spec);
     - else (c > 47 at 0x86200, or the set byte is 0), if j + 1 is three times the replay width 437
       (0x86244), the code stores 0 to the width (0x86268) and falls into the re-assert tail RSWP
       0x8626c (nx_resweep_spec);
     - else it goes back to LOOPR with j + 1, and the walk applies itself (induction on the number of
       passes left).

   Where image B differs from image A (0x852e4) and this file from its donor:
     - the table is in s0 (atom 8; image A: a0, atom 10), the shadow base in s5 (x21, pinned to atom 32),
       the cursor in t0 (x5, pinned to atom 51), and the scan's prologue holds the field addresses, their
       shadow addresses, 3 * width, the loop bound, tx + 144 and ~(tx + 144) in registers;
     - the contract gives no I1, so `c <= 47` no longer follows from the table: the branch 0x86200
       (`blt t3,a7`) is a real path, to the loop's continue 0x86240, and agrees with the model's
       `carried` (lib/Prog/NextModel.v:39). The proof splits on c <= 47 before it seats the state:
       only then is the set byte inside the table, so only then is it seated (atom 52, SREG, the alias
       and the shadow entry mkSHE 52 0 1);
     - the cursor reaches 3 * 255 - 1 = 764 (image A: 143), so the division lemmas carry j < 765;
     - the four UBSan guards of the loop all jump to the one `unimp` 0x8644c, and each is refuted:
         T12 0x86204 `bltu t3,a7`: c is not above 47 unsigned, as 0 <= c <= 47 (0 <= j);
         T13 0x86210 `bltu t1,a0`: ~(tx + 144) is not below 3c, as tx + 144 + 3c < 2 ^ 64;
         T14 0x86214 `bltz t0`:    p = j mod 3 is not negative (0 <= j);
         T15 0x86220 `bltu t5,t0`: ~(tx + 144 + 3c) is not below p, as tx + 144 + 3c + p < 2 ^ 64.
       0 <= j is the cut's premise; it holds at the scan's entry by thd_replay_ok and the width <> 0.
   The memory-checking runtime's checks in this range are the shadow byte of the cursor (0x861cc, its
   slow block 0x8624c reports through 0x86638), of the set byte (0x86230, slow block 0x86254 reporting
   at 0x8625c) and of the width (0x86260, slow block 0x86540 reporting at 0x8654c). The symbolic engine
   decides each inside the run from the shadow entries ns_SH: the table's 460 bytes (mkSHE 8 0 460) and
   the set byte (mkSHE 52 0 1). So none of the three __asan_report_ calls is reached. *)
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
GrantTop GrantSyms GrantList GrantAddr GrantPa GrantPaLib GrantFrame GrantRo.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import Mem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import
HeadampModel NextModel NextLemmas SlotNeeds_c HeadampI1.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require GrantModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantBContracts HeadampTxNext.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Notation TX_SIZE := ATx.TX_SIZE.
#[local] Notation LAY_TX := ATx.LAY_TX.
#[local] Notation tx_vals := ATx.tx_vals.
#[local] Notation tx_fbyte := ATx.tx_fbyte.

(* ---------------------------------------------------------------- *)
(* The symbolic state at LOOPR.                                       *)

(* The address of a shadow byte, as the engine builds it from `srli; add s5`. *)
Definition ns_sha (o : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 o) (SLit 3)) (SOff 32 0).
(* j / 3 and j mod 3 by the multiply by 0x55555556 (atom 51 the cursor), as the engine builds them. *)
Definition ns_J : sv := SOff 51 0.
Definition ns_MJ : sv := SMd M_MUL ns_J (SLit 1431655766).
Definition ns_D3 : sv := SAlu ALU_ADD (SAlu ALU_SRL ns_MJ (SLit 32)) (SAlu ALU_SRL ns_MJ (SLit 63)).
Definition ns_PP : sv := SAlu ALU_SUB (SAlu ALU_SUB ns_J ns_D3) (SAlu ALU_SLL ns_D3 (SLit 1)).
(* The cell tb T 436 + j / 3 (atom 34 the replay base), three times it, and the set byte's address
   tx + 144 + 3c + j mod 3. *)
Definition ns_c : sv := SAlu ALU_ADD ns_D3 (SOff 34 0).
Definition ns_c3 : sv := SAlu ALU_ADD (SAlu ALU_SLL ns_c (SLit 1)) ns_c.
Definition ns_set1 : sv := SAlu ALU_ADD (SAlu ALU_ADD (SOff 8 144) ns_c3) ns_PP.

Definition sr_r : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms
    (21%bv : bv 5) (SOff 32 0))
    (18%bv : bv 5) (SOff 8 437))
    (22%bv : bv 5) (ns_sha 437))
    (19%bv : bv 5) (SOff 8 444))
    (23%bv : bv 5) (ns_sha 444))
    (20%bv : bv 5) (SOff 8 440))
    (24%bv : bv 5) (ns_sha 440))
    (5%bv : bv 5) (SOff 51 0))
    (15%bv : bv 5) (SOff 34 0))
    (16%bv : bv 5) (SOff 8 144))
    (7%bv : bv 5) (SLit 1431655766))
    (28%bv : bv 5) (SLit 47).

(* The two table bytes the scan may write: the cursor (440..443) and the width (437, with its
   current value as atom 35); and the set byte it reads (atom 52, value atom 53). *)
Definition ns_W440 : YP09.region := YP09.mkRegion (Some 8%nat) 440 444 440 444 [].
Definition ns_W437 : YP09.region :=
  YP09.mkRegion (Some 8%nat) 437 438 437 438 [YP09.mkChunk 437 (CVal 1 (SOff 35 0))].
Definition ns_regs : list YP09.region := [ ns_W440; ns_W437; SREG ].
Definition ns_regs_b : list YP09.region := [ ns_W440; ns_W437 ].
(* The same two regions after the cursor store, and after the width store. *)
Definition ns_W440f : YP09.region :=
  YP09.mkRegion (Some 8%nat) 440 444 440 444 [YP09.mkChunk 440 (CVal 4 (SOff 51 1))].
Definition ns_W437z : YP09.region :=
  YP09.mkRegion (Some 8%nat) 437 438 437 438 [YP09.mkChunk 437 (CVal 1 (SLit 0))].

Definition ns_atoms_b : list (nat * afact) :=
  [ (8%nat, PTRN 4); (32%nat, mkAF SB_NX SB_NX 0); (34%nat, mkAF 0 255 0); (51%nat, mkAF 0 764 0) ].
Definition ns_atoms : list (nat * afact) :=
  ns_atoms_b ++ [ (52%nat, PTRN 0); (53%nat, mkAF 0 255 0) ].
Definition ns_alias : list (sv * sv) := [ (ns_set1, SOff 52 0) ].
Definition ns_SH_b : list shent := [ mkSHE 8 0 460 ].
Definition ns_SH : list shent := [ mkSHE 8 0 460; mkSHE 52 0 1 ].
(* The state when the cell is at most 47 (the set byte is a table byte), and when it is above. *)
Definition ss_r : sstate := mkSS LOOPR sr_r ns_regs None (mkFacts ns_atoms [] ns_alias).
Definition ss_rb : sstate := mkSS LOOPR sr_r ns_regs_b None (mkFacts ns_atoms_b [] []).

(* The set byte's offset in the table, and the atoms' values. *)
Definition ns_cell (T : list byte) (j : Z) : Z := 144 + 3 * (tb T 436 + j / 3) + j mod 3.
Definition ns_extra (tx j : Z) (T : list byte) : list word :=
  map (Z_to_bv 64)
    [ SB_NX; 0; tb T 436; tb T 437; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
      j; tx + ns_cell T j; tb T (ns_cell T j) ].

(* The windows a run of this segment may write. *)
Definition ns_wok (r : YP09.region) : bool :=
  (YP09.r_whi r <=? YP09.r_wlo r) ||
  (match YP09.r_base r with Some n => Nat.eqb n 8 | None => false end &&
   (((437 <=? YP09.r_wlo r) && (YP09.r_whi r <=? 438)) ||
    ((440 <=? YP09.r_wlo r) && (YP09.r_whi r <=? 444))))%bool.

(* ---------------------------------------------------------------- *)
(* Values of the engine's expressions.                               *)

Lemma ns_denot_atom : forall E n w, ew E n = w -> sv_denot E (SOff n 0) = w.
Proof. intros E n w H. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.

Lemma ns_denot_off : forall E n v c, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
  sv_denot E (SOff n c) = w64 (v + c).
Proof. intros E n v c H Hv Hc. rewrite denot_lit_U, (U_atom_off E n v c H Hv Hc). reflexivity. Qed.

Lemma ns_U_sha : forall E tx o, ew E 8 = Z_to_bv 64 tx -> ew E 32 = Z_to_bv 64 SB_NX ->
  0 <= tx -> 0 <= o -> tx + o < 2 ^ 47 -> U E (ns_sha o) = SHADOW_OFF + (tx + o) / 8.
Proof.
  intros E tx o H8 H32 Htx Ho Hlt.
  assert (Hq : 0 <= (tx + o) / 8 <= tx + o)
    by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  assert (US : U E (SAlu ALU_SRL (SOff 8 o) (SLit 3)) = (tx + o) / 8).
  { rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom_off E 8 tx o H8) by lia. rewrite U_SLit.
    change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    apply zcanon_id. unfold M64. lia. }
  unfold ns_sha. rewrite U_SAlu. cbn [zalu_raw].
  rewrite US, (U_atom E 32 SB_NX H32) by (unfold SB_NX; lia).
  unfold SHADOW_OFF, SB_NX. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

Lemma ns_U_J : forall E j, ew E 51 = Z_to_bv 64 j -> 0 <= j < 765 -> U E ns_J = j.
Proof. intros E j Hj R. unfold ns_J. apply (U_atom E 51 j Hj). lia. Qed.

Lemma ns_U_MJ : forall E j, ew E 51 = Z_to_bv 64 j -> 0 <= j < 765 -> U E ns_MJ = j * 1431655766.
Proof.
  intros E j Hj R. unfold ns_MJ. rewrite (U_SMd E M_MUL ns_J (SLit 1431655766)). cbn [zmd_raw].
  rewrite (ns_U_J E j Hj R), U_SLit. change (zcanon 1431655766) with 1431655766.
  apply zcanon_id. unfold M64. lia.
Qed.

Lemma ns_U_D3 : forall E j, ew E 51 = Z_to_bv 64 j -> 0 <= j < 765 -> U E ns_D3 = j / 3.
Proof.
  intros E j Hj R. unfold ns_D3.
  rewrite (U_SAlu E ALU_ADD (SAlu ALU_SRL ns_MJ (SLit 32)) (SAlu ALU_SRL ns_MJ (SLit 63))). cbn [zalu_raw].
  rewrite (U_SAlu E ALU_SRL ns_MJ (SLit 32)), (U_SAlu E ALU_SRL ns_MJ (SLit 63)). cbn [zalu_raw].
  rewrite (ns_U_MJ E j Hj R), !U_SLit.
  change (Z.land (zcanon 32) 63) with 32. change (Z.land (zcanon 63) 63) with 63.
  rewrite !Z.shiftr_div_pow2 by lia.
  change (2 ^ 32) with 4294967296. change (2 ^ 63) with 9223372036854775808.
  rewrite (div3_hi j), (div3_sign j) by lia.
  change (zcanon 0) with 0. rewrite Z.add_0_r.
  rewrite (zcanon_id (j / 3)) by (unfold M64; Z.div_mod_to_equations; lia).
  apply zcanon_id. unfold M64. Z.div_mod_to_equations. lia.
Qed.

Lemma ns_U_PP : forall E j, ew E 51 = Z_to_bv 64 j -> 0 <= j < 765 -> U E ns_PP = j mod 3.
Proof.
  intros E j Hj R. unfold ns_PP.
  rewrite (U_SAlu E ALU_SUB (SAlu ALU_SUB ns_J ns_D3) (SAlu ALU_SLL ns_D3 (SLit 1))). cbn [zalu_raw].
  rewrite (U_SAlu E ALU_SUB ns_J ns_D3), (U_SAlu E ALU_SLL ns_D3 (SLit 1)). cbn [zalu_raw].
  rewrite (ns_U_J E j Hj R), (ns_U_D3 E j Hj R), U_SLit. change (Z.land (zcanon 1) 63) with 1.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
  rewrite (zcanon_id (j - j / 3)) by (unfold M64; Z.div_mod_to_equations; lia).
  rewrite (zcanon_id (j / 3 * 2)) by (unfold M64; Z.div_mod_to_equations; lia).
  rewrite zcanon_id by (unfold M64; Z.div_mod_to_equations; lia). rewrite Z.mod_eq by lia. lia.
Qed.

Lemma ns_U_c : forall E j b, ew E 51 = Z_to_bv 64 j -> 0 <= j < 765 ->
  ew E 34 = Z_to_bv 64 b -> 0 <= b < 256 -> U E ns_c = j / 3 + b.
Proof.
  intros E j b H51 Hj H34 Hb.
  assert (Hq : 0 <= j / 3 <= j) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  unfold ns_c. rewrite U_SAlu. cbn [zalu_raw].
  rewrite (ns_U_D3 E j H51 Hj), (U_atom E 34 b H34) by lia.
  apply zcanon_id. unfold M64. lia.
Qed.

Lemma ns_U_c3 : forall E j b, ew E 51 = Z_to_bv 64 j -> 0 <= j < 765 ->
  ew E 34 = Z_to_bv 64 b -> 0 <= b < 256 -> U E ns_c3 = 3 * (j / 3 + b).
Proof.
  intros E j b H51 Hj H34 Hb.
  assert (Hq : 0 <= j / 3 <= j) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  pose proof (ns_U_c E j b H51 Hj H34 Hb) as Hc.
  assert (UC : U E (SAlu ALU_SLL ns_c (SLit 1)) = 2 * (j / 3 + b)).
  { rewrite U_SAlu. cbn [zalu_raw]. rewrite Hc, U_SLit. change (Z.land (zcanon 1) 63) with 1.
    rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
    rewrite zcanon_id by (unfold M64; lia). lia. }
  unfold ns_c3. rewrite U_SAlu. cbn [zalu_raw]. rewrite UC, Hc.
  rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

Lemma ns_U_a144 : forall E tx j b, ew E 8 = Z_to_bv 64 tx -> 0 <= tx -> tx + 460 <= 2 ^ 47 ->
  ew E 51 = Z_to_bv 64 j -> 0 <= j < 765 -> ew E 34 = Z_to_bv 64 b -> 0 <= b < 256 ->
  U E (SAlu ALU_ADD (SOff 8 144) ns_c3) = tx + 144 + 3 * (j / 3 + b).
Proof.
  intros E tx j b H8 Htx Htx2 H51 Hj H34 Hb.
  assert (Hq : 0 <= j / 3 <= j) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom_off E 8 tx 144 H8) by lia.
  rewrite (ns_U_c3 E j b H51 Hj H34 Hb). apply zcanon_id. unfold M64. lia.
Qed.

Lemma ns_U_set1 : forall E tx j b, ew E 8 = Z_to_bv 64 tx -> 0 <= tx -> tx + 460 <= 2 ^ 47 ->
  ew E 51 = Z_to_bv 64 j -> 0 <= j < 765 -> ew E 34 = Z_to_bv 64 b -> 0 <= b < 256 ->
  U E ns_set1 = tx + 144 + 3 * (b + j / 3) + j mod 3.
Proof.
  intros E tx j b H8 Htx Htx2 H51 Hj H34 Hb.
  assert (Hq : 0 <= j / 3 <= j) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  pose proof (Z.mod_pos_bound j 3 ltac:(lia)) as Hm.
  unfold ns_set1. rewrite U_SAlu. cbn [zalu_raw].
  rewrite (ns_U_a144 E tx j b H8 Htx Htx2 H51 Hj H34 Hb), (ns_U_PP E j H51 Hj).
  rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

Lemma ns_bt_lt : forall E a b, branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (Sg E a <? Sg E b).
Proof. intros E a b. first [reflexivity | cbn [branch_taken]; unfold bv_lts, Sg; reflexivity]. Qed.

Lemma ns_Sg : forall E v z, U E v = z -> 0 <= z < 2 ^ 63 -> Sg E v = z.
Proof. intros E v z H Hz. unfold Sg. rewrite denot_lit_U, H. apply GrantModel.signed64_small. lia. Qed.

(* ---------------------------------------------------------------- *)
(* The model's side.                                                  *)

Lemma ns_arith : forall T j, tb T 437 <> 0 -> 0 <= j < 3 * tb T 437 ->
  0 <= j < 765 /\ 0 <= tb T 436 < 256 /\ 0 <= j / 3 < 255 /\ 0 <= j mod 3 < 3.
Proof.
  intros T j Hw Hj.
  pose proof (tb_range T 436). pose proof (tb_range T 437).
  assert (Hq0 : 0 <= j / 3) by (apply Z.div_pos; lia).
  assert (Hq : j / 3 < tb T 437) by (apply Z.div_lt_upper_bound; lia).
  pose proof (Z.mod_pos_bound j 3 ltac:(lia)). lia.
Qed.

Lemma ns_cell_rng : forall T j, tb T 436 + j / 3 <= 47 -> 0 <= tb T 436 -> 0 <= j / 3 ->
  0 <= j mod 3 < 3 -> 144 <= ns_cell T j < 288.
Proof. intros T j H1 H2 H3 H4. unfold ns_cell. lia. Qed.

Lemma ns_model_step : forall T t j n, length T = 460%nat -> 0 <= j ->
  walk (set4 T 440 j) t (tb T 436) (tb T 448) (3 * tb T 437) j (S n) =
  if carried T (tb T 436) (tb T 448) j
  then emit_res (set4 T 440 (j + 1)) t (tb T 436 + j / 3) (j mod 3) j (3 * tb T 437)
  else if j + 1 =? 3 * tb T 437 then resweep (setb (set4 T 440 (j + 1)) 437 0)
  else walk (set4 T 440 (j + 1)) t (tb T 436) (tb T 448) (3 * tb T 437) (j + 1) n.
Proof.
  intros T t j n HL Hj. rewrite walk_step. cbv zeta.
  rewrite set4_set4 by lia.
  rewrite carried_set4_440 by (pose proof (tb_range T 436); lia).
  reflexivity.
Qed.

Lemma ns_carried_o0 : forall T j, tb T 448 = 0 -> carried T (tb T 436) (tb T 448) j = true.
Proof. intros T j H. unfold carried. rewrite H. reflexivity. Qed.

Lemma ns_carried_set : forall T j, tb T 436 + j / 3 <= 47 -> tb T (ns_cell T j) <> 0 ->
  carried T (tb T 436) (tb T 448) j = true.
Proof.
  intros T j H1 H2. unfold carried. unfold ns_cell in H2.
  rewrite (proj2 (Z.leb_le _ _) H1), (proj2 (Z.eqb_neq _ _) H2). cbn [andb negb].
  apply orb_true_r.
Qed.

Lemma ns_carried_unset : forall T j, tb T 448 <> 0 -> tb T (ns_cell T j) = 0 ->
  carried T (tb T 436) (tb T 448) j = false.
Proof.
  intros T j H1 H2. unfold carried. unfold ns_cell in H2.
  rewrite (proj2 (Z.eqb_neq _ 0) H1), H2.
  destruct (tb T 436 + j / 3 <=? 47); reflexivity.
Qed.

(* Image B's own case: the cell is above 47, so it is not carried whatever its set byte holds. *)
Lemma ns_carried_big : forall T j, tb T 448 <> 0 -> 47 < tb T 436 + j / 3 ->
  carried T (tb T 436) (tb T 448) j = false.
Proof.
  intros T j H1 H2. unfold carried.
  rewrite (proj2 (Z.eqb_neq _ 0) H1), (proj2 (Z.leb_gt _ _) H2). reflexivity.
Qed.

(* ---------------------------------------------------------------- *)
(* The table's bytes.                                                 *)

Lemma ns_nth_set4_in : forall T k v jj, length T = 460%nat -> 0 <= k -> k + 4 <= 460 -> 0 <= jj < 4 ->
  nth (Z.to_nat (k + jj)) (set4 T k v) (Z_to_bv 8 0) = YP09.byte_of_word (Z_to_bv 64 v) jj.
Proof.
  intros T k v jj HL Hk Hk4 Hj. unfold set4. rewrite nth_as_error.
  rewrite upd_bytes_nth by (rewrite ?length_le4; lia).
  rewrite length_le4.
  replace (Nat.leb (Z.to_nat k) (Z.to_nat (k + jj)) && Nat.ltb (Z.to_nat (k + jj)) (Z.to_nat k + 4))%bool
    with true by (symmetry; apply andb_true_iff; split; [apply Nat.leb_le | apply Nat.ltb_lt]; lia).
  replace (Z.to_nat (k + jj) - Z.to_nat k)%nat with (Z.to_nat jj) by lia.
  rewrite <- nth_as_error.
  rewrite (ATx.le4_byte_of_word (Z_to_bv 64 v) (Z.to_nat jj)) by lia.
  rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma ns_nth_setb_in : forall T k v, length T = 460%nat -> 0 <= k < 460 ->
  nth (Z.to_nat k) (setb T k v) (Z_to_bv 8 0) = YP09.byte_of_word (Z_to_bv 64 v) 0.
Proof.
  intros T k v HL Hk. unfold setb. rewrite nth_as_error.
  rewrite upd_bytes_nth by (rewrite ?length_le1; lia).
  rewrite length_le1.
  replace (Nat.leb (Z.to_nat k) (Z.to_nat k) && Nat.ltb (Z.to_nat k) (Z.to_nat k + 1))%bool with true
    by (symmetry; apply andb_true_iff; split; [apply Nat.leb_le | apply Nat.ltb_lt]; lia).
  rewrite Nat.sub_diag. rewrite <- nth_as_error. apply ATx.le1_byte_of_word.
Qed.

Lemma ns_bow0 : forall z, 0 <= z < 2 ^ 64 -> YP09.byte_of_word (Z_to_bv 64 z) 0 = Z_to_bv 8 z.
Proof.
  intros z Hz. unfold YP09.byte_of_word. rewrite Z.mul_0_r, Z.shiftr_0_r, unsigned_lit_small by lia.
  reflexivity.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

Definition NS (regsj : bvmap 5 word) (tx j : Z) (T : list byte) : env :=
  Eimg (Ereg regsj (ns_extra tx j T)).

Definition ns_env_ok (E : env) (regsj : bvmap 5 word) (tx j : Z) (T : list byte) : Prop :=
  ew E 2 = getr regsj 2 /\ ew E 3 = getr regsj 3 /\ ew E 4 = getr regsj 4 /\
  ew E 6 = getr regsj 6 /\ ew E 8 = getr regsj 8 /\ ew E 9 = getr regsj 9 /\
  ew E 11 = getr regsj 11 /\ ew E 12 = getr regsj 12 /\ ew E 13 = getr regsj 13 /\
  ew E 14 = getr regsj 14 /\ ew E 25 = getr regsj 25 /\ ew E 26 = getr regsj 26 /\
  ew E 27 = getr regsj 27 /\
  ew E 32 = w64 SB_NX /\ ew E 34 = w64 (tb T 436) /\ ew E 35 = w64 (tb T 437) /\
  ew E 51 = w64 j /\ ew E 52 = w64 (tx + ns_cell T j) /\ ew E 53 = w64 (tb T (ns_cell T j)).

Lemma ns_env : forall regsj tx j T, ns_env_ok (NS regsj tx j T) regsj tx j T.
Proof.
  intros regsj tx j T. unfold ns_env_ok, NS.
  repeat match goal with |- _ /\ _ => split end;
    rewrite Eimg_low by (unfold A_TEXT; lia);
    first [ lazymatch goal with
            | |- ew (Ereg _ _) ?n = getr _ ?r => exact (ew_Ereg_nat regsj _ n r eq_refl)
            end
          | exact (ew_Ereg_extra regsj _ 0) | exact (ew_Ereg_extra regsj _ 2)
          | exact (ew_Ereg_extra regsj _ 3) | exact (ew_Ereg_extra regsj _ 19)
          | exact (ew_Ereg_extra regsj _ 20) | exact (ew_Ereg_extra regsj _ 21) ].
Qed.

Lemma ns_st_region : forall E ss ms r, st_ok_pi SEGS VAL E ss ms -> In r (ss_mem ss) ->
  region_ok SEGS E (ms_mem ms) r.
Proof.
  intros E ss ms r HS Hin.
  destruct (st_ok_mem_ok SEGS E (abs_ss VAL ss) ms HS) as (_ & HF & _).
  cbn [abs_ss setpc ss_mem] in HF. exact (proj1 (Forall_forall _ _) HF r Hin).
Qed.

Lemma ns_at : forall (W : world SEGS) (pc pc' : Z) R M D Q, pc' = pc ->
  SRr SEGS W (cfg_at SEGS pc' R M D) Q -> SRr SEGS W (mkCfg (mkst R (Z_to_bv 64 pc) M (seg_rom SEGS)) D) Q.
Proof. intros W pc pc' R M D Q -> H. exact H. Qed.

Lemma ns_val1 : forall m tx T' k, obj_at SEGS m tx LAY_TX (tx_vals T') -> tx_fbyte k = true ->
  val_mem SEGS m (tx + k) 1 (tb T' k).
Proof.
  intros m tx T' k HO Hk jj Hj. destruct jj as [|jj]; [|lia].
  pose proof (tb_range T' k) as Hr.
  rewrite le_byte_small by (cbn; lia).
  change (Z.of_nat 0%nat) with 0. rewrite Z.mul_0_r, Z.shiftr_0_r, Z.add_0_r.
  rewrite Z_to_bv8_tb. exact (proj1 (ATx.tx_obj_bytes SEGS _ _ _) HO k Hk).
Qed.

(* What the runs of this segment leave: every byte outside the two windows. *)
Definition ns_inv (W : world SEGS) (memj m : word -> option byte) (tx : Z) : Prop :=
  (forall x : word, ~ (tx + 437 <= bv_unsigned x < tx + 438) -> ~ (tx + 440 <= bv_unsigned x < tx + 444) ->
     mrestrict (w_H W) m x = mrestrict (w_H W) memj x) /\
  mem_grows (mrestrict (w_H W) memj) (mrestrict (w_H W) m).

Lemma ns_inv_refl : forall W m tx, ns_inv W m m tx.
Proof. intros W m tx. split; [intros; reflexivity | apply mem_grows_refl]. Qed.

Lemma ns_wr : forall E rs tx a, forallb ns_wok rs = true -> bv_unsigned (ew E 8) = tx ->
  in_wrange E rs a -> (tx + 437 <= a < tx + 438) \/ (tx + 440 <= a < tx + 444).
Proof.
  intros E rs tx a Hok H8 (r & Hin & Ha).
  pose proof (proj1 (forallb_forall _ _) Hok r Hin) as Hr. clear Hok Hin.
  destruct r as [b lo hi wlo whi cs]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha.
  unfold ns_wok in Hr. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr.
  apply orb_prop in Hr as [Hr|Hr]; [apply Z.leb_le in Hr; lia|].
  destruct b as [n|]; [|discriminate Hr].
  apply andb_prop in Hr as [Hn Hw]. apply Nat.eqb_eq in Hn. subst n.
  cbn [base_val] in Ha. rewrite H8 in Ha.
  apply orb_prop in Hw as [Hw|Hw]; apply andb_prop in Hw as [Hw1 Hw2];
    apply Z.leb_le in Hw1; apply Z.leb_le in Hw2; lia.
Qed.

Lemma ns_inv_step : forall W memj m1 m2 tx E rs,
  ns_inv W memj m1 tx -> bv_unsigned (ew E 8) = tx ->
  frame_of E rs (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  mem_grows (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  forallb ns_wok rs = true ->
  ns_inv W memj m2 tx.
Proof.
  intros W memj m1 m2 tx E rs (HI1 & HG1) H8 HF HG Hok. split.
  - intros x H1 H2. rewrite (HF x); [exact (HI1 x H1 H2)|].
    intros Hw. destruct (ns_wr E rs tx _ Hok H8 Hw); lia.
  - intros x Hx. apply HG. apply HG1. exact Hx.
Qed.

Lemma ns_grows_pres : forall (W : world SEGS) m1 m2 a,
  mem_grows (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  apresent (w_H W) m1 a -> apresent (w_H W) m2 a.
Proof.
  intros W m1 m2 a HG (Hh & b & Hb). split; [exact Hh|].
  assert (HN : mrestrict (w_H W) m1 (Z_to_bv 64 a) <> None)
    by (unfold mrestrict; rewrite Hh, Hb; discriminate).
  pose proof (HG _ HN) as H2. unfold mrestrict in H2. rewrite Hh in H2.
  destruct (m2 (Z_to_bv 64 a)) as [b2|] eqn:Hb2; [exists b2; reflexivity | exfalso; exact (H2 eq_refl)].
Qed.

Lemma ns_inv_mbyte : forall W memj m tx a, ns_inv W memj m tx -> 0 <= a < 2 ^ 64 ->
  ~ (tx + 437 <= a < tx + 438) -> ~ (tx + 440 <= a < tx + 444) ->
  mbyte SEGS (mrestrict (w_H W) m) a = mbyte SEGS (mrestrict (w_H W) memj) a.
Proof.
  intros W memj m tx a (HK & _) Ha H1 H2. unfold mbyte.
  rewrite HK; [reflexivity | rewrite unsigned_lit_small by lia; exact H1 | rewrite unsigned_lit_small by lia; exact H2].
Qed.

Lemma ns_val_keep : forall (W : world SEGS) m1 m2 a n v,
  (forall i, 0 <= i < Z.of_nat n -> mbyte SEGS (mrestrict (w_H W) m2) (a + i) = mbyte SEGS (mrestrict (w_H W) m1) (a + i)) ->
  val_mem SEGS (mrestrict (w_H W) m1) a n v -> val_mem SEGS (mrestrict (w_H W) m2) a n v.
Proof. intros W m1 m2 a n v HK HV kk Hk. rewrite HK by lia. exact (HV kk Hk). Qed.

(* The table at the end of a run, byte by byte. *)
Lemma ns_tab : forall W memj m tx T j T',
  length T = 460%nat -> 0 <= tx -> tx + 460 <= 2 ^ 47 ->
  obj_at SEGS (mrestrict (w_H W) memj) tx LAY_TX (tx_vals (set4 T 440 j)) ->
  ns_inv W memj m tx ->
  (forall i, 0 <= i < 460 -> i <> 437 -> ~ (440 <= i < 444) -> tb T' i = tb T i) ->
  mbyte SEGS (mrestrict (w_H W) m) (tx + 437) = Some (nth (Z.to_nat 437) T' (Z_to_bv 8 0)) ->
  (forall d, 0 <= d < 4 ->
     mbyte SEGS (mrestrict (w_H W) m) (tx + 440 + d) = Some (nth (Z.to_nat (440 + d)) T' (Z_to_bv 8 0))) ->
  obj_at SEGS (mrestrict (w_H W) m) tx LAY_TX (tx_vals T').
Proof.
  intros W memj m tx T j T' HL Htx Htx2 HO HINV Hsame H437 H440.
  apply (proj2 (ATx.tx_obj_bytes SEGS _ _ _)). intros i Hi. pose proof (ATx.tx_fbyte_range i Hi) as Hir.
  destruct (Z.eq_dec i 437) as [->|N1]; [exact H437|].
  assert (Hout : ~ (440 <= i < 444) ->
            mbyte SEGS (mrestrict (w_H W) m) (tx + i) = Some (nth (Z.to_nat i) T' (Z_to_bv 8 0))).
  { intros N2. rewrite (ns_inv_mbyte W memj m tx (tx + i) HINV) by lia.
    rewrite (proj1 (ATx.tx_obj_bytes SEGS _ _ _) HO i Hi).
    rewrite <- !Z_to_bv8_tb. rewrite (Hsame i) by lia. rewrite tb_set4_out by lia. reflexivity. }
  destruct (Z_le_dec 440 i) as [H1|H1]; [destruct (Z_lt_dec i 444) as [H2|H2]|].
  - pose proof (H440 (i - 440) ltac:(lia)) as X.
    replace (tx + 440 + (i - 440)) with (tx + i) in X by lia.
    replace (440 + (i - 440)) with i in X by lia. exact X.
  - apply Hout. lia.
  - apply Hout. lia.
Qed.

Lemma ns_tab_next : forall W memj m tx T j,
  length T = 460%nat -> 0 <= tx -> tx + 460 <= 2 ^ 47 ->
  obj_at SEGS (mrestrict (w_H W) memj) tx LAY_TX (tx_vals (set4 T 440 j)) ->
  ns_inv W memj m tx ->
  mbyte SEGS (mrestrict (w_H W) m) (tx + 437) = Some (Z_to_bv 8 (tb T 437)) ->
  (forall d, 0 <= d < 4 ->
     mbyte SEGS (mrestrict (w_H W) m) (tx + 440 + d) = Some (YP09.byte_of_word (Z_to_bv 64 (j + 1)) d)) ->
  obj_at SEGS (mrestrict (w_H W) m) tx LAY_TX (tx_vals (set4 T 440 (j + 1))).
Proof.
  intros W memj m tx T j HL Htx Htx2 HO HINV H437 H440.
  apply (ns_tab W memj m tx T j _ HL Htx Htx2 HO HINV).
  - intros i Hi N1 N2. apply tb_set4_out; lia.
  - rewrite <- Z_to_bv8_tb, tb_set4_out by lia. exact H437.
  - intros d Hd. rewrite (ns_nth_set4_in T 440 (j + 1) d) by lia. exact (H440 d Hd).
Qed.

Lemma ns_tab_rsw : forall W memj m tx T j,
  length T = 460%nat -> 0 <= tx -> tx + 460 <= 2 ^ 47 ->
  obj_at SEGS (mrestrict (w_H W) memj) tx LAY_TX (tx_vals (set4 T 440 j)) ->
  ns_inv W memj m tx ->
  mbyte SEGS (mrestrict (w_H W) m) (tx + 437) = Some (YP09.byte_of_word (Z_to_bv 64 0) 0) ->
  (forall d, 0 <= d < 4 ->
     mbyte SEGS (mrestrict (w_H W) m) (tx + 440 + d) = Some (YP09.byte_of_word (Z_to_bv 64 (j + 1)) d)) ->
  obj_at SEGS (mrestrict (w_H W) m) tx LAY_TX (tx_vals (setb (set4 T 440 (j + 1)) 437 0)).
Proof.
  intros W memj m tx T j HL Htx Htx2 HO HINV H437 H440.
  assert (HL4 : length (set4 T 440 (j + 1)) = 460%nat) by L460.
  apply (ns_tab W memj m tx T j _ HL Htx Htx2 HO HINV).
  - intros i Hi N1 N2. rewrite tb_setb_out by lia. apply tb_set4_out; lia.
  - rewrite (ns_nth_setb_in (set4 T 440 (j + 1)) 437 0) by lia. exact H437.
  - intros d Hd. rewrite <- Z_to_bv8_tb, tb_setb_out by lia. rewrite Z_to_bv8_tb.
    rewrite (ns_nth_set4_in T 440 (j + 1) d) by lia. exact (H440 d Hd).
Qed.

(* The bytes the regions hold after a run. *)
Lemma ns_b440 : forall E m tx j, bv_unsigned (ew E 8) = tx -> ew E 51 = w64 j -> 0 <= j < 765 ->
  region_ok SEGS E m ns_W440f ->
  forall d, 0 <= d < 4 -> mbyte SEGS m (tx + 440 + d) = Some (YP09.byte_of_word (Z_to_bv 64 (j + 1)) d).
Proof.
  intros E m tx j H8 H51 Hj HR d Hd. unfold ns_W440f in HR.
  rewrite (ATx.byte_of_region SEGS E m 8%nat tx _ 440 444 440 444 440 4%N (SOff 51 1) d HR H8
             (or_introl eq_refl) ltac:(cbn; lia)).
  rewrite (ns_denot_off E 51 j 1 H51) by lia. reflexivity.
Qed.

Lemma ns_b437 : forall E m tx T, bv_unsigned (ew E 8) = tx -> ew E 35 = w64 (tb T 437) ->
  region_ok SEGS E m ns_W437 -> mbyte SEGS m (tx + 437) = Some (Z_to_bv 8 (tb T 437)).
Proof.
  intros E m tx T H8 H35 HR. unfold ns_W437 in HR.
  pose proof (ATx.byte_of_region SEGS E m 8%nat tx _ 437 438 437 438 437 1%N (SOff 35 0) 0 HR H8
                (or_introl eq_refl) ltac:(cbn; lia)) as X.
  rewrite Z.add_0_r in X. rewrite X, (ns_denot_atom E 35 _ H35).
  unfold w64. rewrite ns_bow0 by (pose proof (tb_range T 437); lia). reflexivity.
Qed.

Lemma ns_b437z : forall E m tx, bv_unsigned (ew E 8) = tx ->
  region_ok SEGS E m ns_W437z -> mbyte SEGS m (tx + 437) = Some (YP09.byte_of_word (Z_to_bv 64 0) 0).
Proof.
  intros E m tx H8 HR. unfold ns_W437z in HR.
  pose proof (ATx.byte_of_region SEGS E m 8%nat tx _ 437 438 437 438 437 1%N (SLit 0) 0 HR H8
                (or_introl eq_refl) ltac:(cbn; lia)) as X.
  rewrite Z.add_0_r in X. exact X.
Qed.

Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
#[local] Notation tnext_post := (tb_reac_headamp_tx_next_post B).

(* What the walk uses of the call's facts. *)
Lemma ns_ctx : forall STK sp0 FP ly S lyc Sc own (W : world SEGS) memc mdc (regs : bvmap 5 word)
    tx chp parp valp T,
  nx_ctx B STK sp0 FP ly S lyc Sc own W memc mdc regs tx chp parp valp T ->
  AR SEGS B lyc Sc W memc mdc /\ In (tx, TX_SIZE) (ablocks B lyc Sc) /\
  thd_out_ok (spZ regs) tx chp /\ thd_out_ok (spZ regs) tx parp /\ thd_out_ok (spZ regs) tx valp /\
  2 ^ 46 <= spZ regs <= 2 ^ 47 /\ alloc_ceiling <= spZ regs - NX_STK /\
  (forall a, tx <= a < tx + TX_SIZE -> nx_may_write B STK sp0 FP ly S lyc Sc own a) /\
  length T = 460%nat /\ thd_replay_ok T.
Proof.
  intros STK sp0 FP ly S lyc Sc own W memc mdc regs tx chp parp valp T H.
  destruct H as (HAR & Hg & Hoc & Hop & Hov & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hspr & Hceil &
    _ & _ & _ & Hw & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HL & HR & _ & _).
  exact (conj HAR (conj Hg (conj Hoc (conj Hop (conj Hov (conj Hspr (conj Hceil (conj Hw (conj HL HR))))))))).
Qed.

Lemma ns_tx : forall STK sp0 FP ly S lyc Sc own (W : world SEGS) memc mdc (regs : bvmap 5 word)
    tx chp parp valp T,
  nx_ctx B STK sp0 FP ly S lyc Sc own W memc mdc regs tx chp parp valp T ->
  tx mod 16 = 0 /\ 4096 <= tx /\ tx + 460 <= alloc_ceiling /\ alloc_ceiling <= 0x7fffff800000.
Proof.
  intros STK sp0 FP ly S lyc Sc own W memc mdc regs tx chp parp valp T HCTX.
  destruct (ns_ctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HCTX) as (HAR & Hg & _).
  destruct (al_blocks _ _ LAWS lyc Sc W memc mdc tx TX_SIZE HAR Hg) as (H16 & H4096 & Hceil & _).
  change (req_size TX_SIZE) with 460 in Hceil.
  pose proof asan_consts as (C1 & _). repeat split; lia.
Qed.

Lemma ns_awr : forall E rs STK sp0 FP ly S lyc Sc own tx,
  forallb ns_wok rs = true -> bv_unsigned (ew E 8) = tx ->
  (forall a, tx <= a < tx + TX_SIZE -> nx_may_write B STK sp0 FP ly S lyc Sc own a) ->
  awr_ok E rs STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own.
Proof.
  intros E rs STK sp0 FP ly S lyc Sc own tx Hok H8 Hw a Ha.
  apply Hw. unfold TX_SIZE, ATx.TX_SIZE. destruct (ns_wr E rs tx a Hok H8 Ha); lia.
Qed.

(* The shadow entry of a run of bytes inside a live block (image A's HeadampTxEffective.v states it
   over image A's listing; this is the same proof over image B's). *)
Lemma ns_shent_at : forall ly S (W : world SEGS) mem md Ex (n : nat) (q b sz lo hi : Z),
  AR SEGS B ly S W mem md -> In (b, sz) (ablocks B ly S) ->
  U Ex BxN = SHADOW_OFF -> U Ex (SOff n 0) = q ->
  b <= q + lo -> lo <= hi -> q + hi <= b + req_size sz ->
  shent_ok SEGS BxN Ex (mrestrict (w_H W) mem) (mkSHE n lo hi).
Proof.
  intros ly S W mem md Ex n q b sz lo hi HAR Hin HB Hq Hlo Hlh Hhi.
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
  destruct (al_blocks _ _ LAWS ly S W mem md b sz HAR Hin) as (_ & Hb4096 & Hbceil & Hbia & _ & _).
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hq.
  rewrite <- (aview_rd_of SEGS). split.
  - eapply (range_addressable_of_block SEGS B LAWS ly S W mem md b sz (q + lo) (hi - lo) HAR Hin); lia.
  - intros a Ha. rewrite Z.min_l in Ha by lia. rewrite Z.max_r in Ha by lia.
    revert Ha. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
    revert Hbia Hb4096 Hbceil Hlo Hlh Hhi C1 C3 C5. clear. intros. lia.
Qed.

(* The facts a cut asks for about memory, at the end of a run. The scan writes no caller byte, so the
   three still read as at the call (q = true). *)
Lemma ns_cut_mem : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
    (regs : bvmap 5 word) memj mdj m md (tx chp parp valp : Z) (T : list byte),
  nx_ctx B STK sp0 FP ly S lyc Sc own W memc mdc regs tx chp parp valp T ->
  nx_mid B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs memj mdj tx chp parp valp (tx + 432) true ->
  nx_saved W memj regs (spZ regs) ->
  ns_inv W memj m tx ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m md k ->
  nx_mid B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs m md tx chp parp valp (tx + 432) true
  /\ nx_saved W m regs (spZ regs).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs memj mdj m md tx chp parp valp T
    HCTX HMID HSAV HINV HJ.
  destruct (ns_ctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HCTX) as (_ & _ & Hoc & Hop & Hov & Hspr & Hceil & _).
  destruct (ns_tx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HCTX) as (_ & H4096 & Htxc & C1).
  pose proof HMID as (_ & HSAME & HpresS & HpresK & HQ). cbv iota beta in HQ.
  pose proof HINV as (HK & HG).
  pose proof nx_stk_val as HSTK.
  assert (HKs : forall a, spZ regs - NX_STK <= a < spZ regs ->
            mbyte SEGS (mrestrict (w_H W) m) a = mbyte SEGS (mrestrict (w_H W) memj) a).
  { intros a Ha. apply (ns_inv_mbyte W memj m tx a HINV); lia. }
  assert (HKo : forall a, thd_out_ok (spZ regs) tx a ->
            aview SEGS (w_H W) m a = aview SEGS (w_H W) memj a).
  { intros a (Ha1 & Ha2 & Ha3 & _). unfold TX_SIZE, ATx.TX_SIZE in Ha3. unfold aview.
    rewrite (ns_inv_mbyte W memj m tx a HINV) by lia. reflexivity. }
  split.
  - split; [exact HJ|]. split; [|split].
    + intros x H1 H2. rewrite HK.
      * exact (HSAME x H1 H2).
      * intros Hx. apply H2. unfold nx_touch2. lia.
      * intros Hx. apply H2. unfold nx_touch2. lia.
    + intros a Ha. apply (ns_grows_pres W memj m a HG). apply HpresS. exact Ha.
    + split.
      * intros a Ha. apply (ns_grows_pres W memj m a HG). apply HpresK. exact Ha.
      * cbv iota beta. destruct HQ as (Q1 & Q2 & Q3). unfold nx_outq.
        rewrite (HKo chp Hoc), (HKo parp Hop), (HKo valp Hov). exact (conj Q1 (conj Q2 Q3)).
  - pose proof HSAV as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12).
    unfold nx_saved. repeat match goal with |- _ /\ _ => split end;
      (eapply ns_val_keep; [intros i Hi; apply HKs; lia | eassumption]).
Qed.

(* The symbolic state at LOOPR, when the cell is at most 47. *)
Lemma ns_seat : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS)
    memc mdc k (regs regsj : bvmap 5 word) memj mdj (tx chp parp valp : Z) (T : list byte) (j : Z),
  nx_ctx B STK sp0 FP ly S lyc Sc own W memc mdc regs tx chp parp valp T ->
  nx_mid B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs memj mdj tx chp parp valp (tx + 432) true ->
  obj_at SEGS (mrestrict (w_H W) memj) tx LAY_TX (tx_vals (set4 T 440 j)) ->
  tb T 437 <> 0 -> 0 <= j < 3 * tb T 437 -> tb T 436 + j / 3 <= 47 ->
  nx_at_loopr regs regsj tx chp parp valp T j ->
  st_ok_pi SEGS VAL (NS regsj tx j T) ss_r
    (restrict (w_H W) (mkst regsj (Z_to_bv 64 (BASE + LOOPR)) memj (seg_rom SEGS)))
  /\ sh_ok SEGS BxN ns_SH (NS regsj tx j T) (mrestrict (w_H W) memj).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsj memj mdj
    tx chp parp valp T j HCTX HMID HOBJ Hw0 Hj Hc47 HAT.
  destruct (ns_ctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HCTX) as (HAR & Hg & _ & _ & _ & _ & _ & _ & HL & _).
  destruct (ns_tx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HCTX) as (Hg16 & H4096 & Htxc & C1).
  pose proof HMID as (HJ & _).
  pose proof (proj1 HJ) as HARj.
  destruct (al_blocks _ _ LAWS lyc Sc W memj mdj tx TX_SIZE HARj Hg) as (_ & _ & _ & _ & Hgpres & _).
  change (req_size TX_SIZE) with 460 in Hgpres.
  destruct (ns_arith T j Hw0 Hj) as (Hj765 & R436 & Hq & Hp3).
  pose proof (ns_cell_rng T j Hc47 ltac:(lia) ltac:(lia) Hp3) as Hcell.
  pose proof (tb_range T 437) as R437.
  pose proof (tb_range T (ns_cell T j)) as Rcell.
  destruct HAT as (HK & R2 & R8 & R9 & R11 & R12 & R21 & R18 & R22 & R19 & R23 & R20 & R24 &
    R25 & R26 & R5 & R14 & R15 & R13 & R16 & R6 & R7 & R28).
  pose proof (ns_env regsj tx j T) as HE.
  set (E := NS regsj tx j T) in *.
  destruct HE as (E2 & E3 & E4 & E6 & E8 & E9 & E11 & E12 & E13 & E14 & E25 & E26 & E27 &
    E32 & E34 & E35 & E51 & E52 & E53).
  rewrite R8 in E8.
  assert (U8 : bv_unsigned (ew E 8) = tx) by (rewrite E8; unfold w64; apply unsigned_lit_small; lia).
  assert (U32 : bv_unsigned (ew E 32) = SB_NX) by (rewrite E32; unfold w64, SB_NX; apply unsigned_lit_small; lia).
  assert (U34 : bv_unsigned (ew E 34) = tb T 436) by (rewrite E34; unfold w64; apply unsigned_lit_small; lia).
  assert (U51 : bv_unsigned (ew E 51) = j) by (rewrite E51; unfold w64; apply unsigned_lit_small; lia).
  assert (U52 : bv_unsigned (ew E 52) = tx + ns_cell T j)
    by (rewrite E52; unfold w64; apply unsigned_lit_small; lia).
  assert (U53 : bv_unsigned (ew E 53) = tb T (ns_cell T j))
    by (rewrite E53; unfold w64; apply unsigned_lit_small; lia).
  assert (HUB : U E BxN = SHADOW_OFF)
    by (unfold BxN; rewrite (U_atom E 32 SB_NX E32) by (unfold SB_NX; lia); reflexivity).
  split.
  - rewrite restrict_mkst_fx. unfold ss_r. apply pa_entry_st_ok_full.
    + unfold sr_r.
      apply regs_ok_pin; [| intros X; discriminate X | refine (eq_trans R28 (eq_sym _)); reflexivity ].
      apply regs_ok_pin; [| intros X; discriminate X | refine (eq_trans R7 (eq_sym _)); reflexivity ].
      apply regs_ok_pin; [| intros X; discriminate X |
        refine (eq_trans R16 (eq_sym _)); apply (ns_denot_off E 8 tx 144 E8); lia ].
      apply regs_ok_pin; [| intros X; discriminate X |
        refine (eq_trans R15 (eq_sym _)); apply ns_denot_atom; exact E34 ].
      apply regs_ok_pin; [| intros X; discriminate X |
        refine (eq_trans R5 (eq_sym _)); apply ns_denot_atom; exact E51 ].
      apply regs_ok_pin; [| intros X; discriminate X |
        refine (eq_trans R24 (eq_sym _)); rewrite denot_lit_U, (ns_U_sha E tx 440 E8 E32) by lia;
        reflexivity ].
      apply regs_ok_pin; [| intros X; discriminate X |
        refine (eq_trans R20 (eq_sym _)); apply (ns_denot_off E 8 tx 440 E8); lia ].
      apply regs_ok_pin; [| intros X; discriminate X |
        refine (eq_trans R23 (eq_sym _)); rewrite denot_lit_U, (ns_U_sha E tx 444 E8 E32) by lia;
        reflexivity ].
      apply regs_ok_pin; [| intros X; discriminate X |
        refine (eq_trans R19 (eq_sym _)); apply (ns_denot_off E 8 tx 444 E8); lia ].
      apply regs_ok_pin; [| intros X; discriminate X |
        refine (eq_trans R22 (eq_sym _)); rewrite denot_lit_U, (ns_U_sha E tx 437 E8 E32) by lia;
        reflexivity ].
      apply regs_ok_pin; [| intros X; discriminate X |
        refine (eq_trans R18 (eq_sym _)); apply (ns_denot_off E 8 tx 437 E8); lia ].
      apply regs_ok_pin; [| intros X; discriminate X |
        refine (eq_trans R21 (eq_sym _)); apply ns_denot_atom; exact E32 ].
      unfold E, NS. apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + unfold ns_regs, ns_W440, ns_W437, SREG.
      repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      * rewrite U8. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable SEGS). apply (proj1 (Hgpres (tx + o) ltac:(lia))).
      * rewrite U8. split; [lia|]. split; [lia|]. split.
        -- intros o Ho. apply (apresent_writable SEGS). apply (proj1 (Hgpres (tx + o) ltac:(lia))).
        -- constructor; [|constructor].
           apply (chunk_ok_val SEGS E _ tx 437 1 (SOff 35 0) (tb T 437));
             [ apply ns_denot_atom; exact E35 | cbn; lia | cbn; lia | ].
           rewrite <- (tb_set4_out T 440 j 437) by lia.
           apply (ns_val1 _ tx (set4 T 440 j) 437 HOBJ). vm_compute. reflexivity.
      * rewrite U52. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ (tx + ns_cell T j) 0 1 (SOff 53 0) (tb T (ns_cell T j)));
          [ apply ns_denot_atom; exact E53 | cbn; lia | cbn; lia | ].
        rewrite Z.add_0_r. rewrite <- (tb_set4_out T 440 j (ns_cell T j)) by lia.
        exact (ATx.tx_cell_val SEGS _ tx (set4 T 440 j) (ns_cell T j) ltac:(lia) HOBJ).
    + apply pairwise_disjoint_of_extents.
      unfold ns_regs, ns_W440, ns_W437, SREG, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U8, U52.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      repeat split; lia.
    + split; [| split; [exact I |]].
      * cbn [ns_atoms ns_atoms_b app f_atoms atoms_ok]. unfold afact_ok, PTRN. cbn [af_lo af_hi af_al2].
        rewrite U8, U32, U34, U51, U52, U53.
        change (2 ^ 4) with 16. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
        unfold SB_NX. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
      * cbn [ns_alias f_alias alias_ok]. split; [| exact I].
        rewrite (denot_lit_U E ns_set1), (denot_lit_U E (SOff 52 0)). f_equal.
        rewrite (ns_U_set1 E tx j (tb T 436) E8 ltac:(lia) ltac:(lia) E51 Hj765 E34 ltac:(lia)).
        rewrite (U_atom E 52 _ E52) by lia. unfold ns_cell. lia.
  - unfold sh_ok, ns_SH.
    constructor; [| constructor; [| constructor]].
    + apply (ns_shent_at lyc Sc W memj mdj E 8 tx tx TX_SIZE 0 460 HARj Hg HUB).
      * exact (U_atom E 8 tx E8 ltac:(lia)).
      * lia.
      * lia.
      * change (req_size TX_SIZE) with 460. lia.
    + apply (ns_shent_at lyc Sc W memj mdj E 52 (tx + ns_cell T j) tx TX_SIZE 0 1 HARj Hg HUB).
      * exact (U_atom E 52 _ E52 ltac:(lia)).
      * lia.
      * lia.
      * change (req_size TX_SIZE) with 460. lia.
Qed.

(* The symbolic state at LOOPR, when the cell is above 47: the set byte is never read, so it is not
   seated. *)
Lemma ns_seat_b : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS)
    memc mdc k (regs regsj : bvmap 5 word) memj mdj (tx chp parp valp : Z) (T : list byte) (j : Z),
  nx_ctx B STK sp0 FP ly S lyc Sc own W memc mdc regs tx chp parp valp T ->
  nx_mid B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs memj mdj tx chp parp valp (tx + 432) true ->
  obj_at SEGS (mrestrict (w_H W) memj) tx LAY_TX (tx_vals (set4 T 440 j)) ->
  tb T 437 <> 0 -> 0 <= j < 3 * tb T 437 ->
  nx_at_loopr regs regsj tx chp parp valp T j ->
  st_ok_pi SEGS VAL (NS regsj tx j T) ss_rb
    (restrict (w_H W) (mkst regsj (Z_to_bv 64 (BASE + LOOPR)) memj (seg_rom SEGS)))
  /\ sh_ok SEGS BxN ns_SH_b (NS regsj tx j T) (mrestrict (w_H W) memj).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsj memj mdj
    tx chp parp valp T j HCTX HMID HOBJ Hw0 Hj HAT.
  destruct (ns_ctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HCTX) as (HAR & Hg & _ & _ & _ & _ & _ & _ & HL & _).
  destruct (ns_tx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HCTX) as (Hg16 & H4096 & Htxc & C1).
  pose proof HMID as (HJ & _).
  pose proof (proj1 HJ) as HARj.
  destruct (al_blocks _ _ LAWS lyc Sc W memj mdj tx TX_SIZE HARj Hg) as (_ & _ & _ & _ & Hgpres & _).
  change (req_size TX_SIZE) with 460 in Hgpres.
  destruct (ns_arith T j Hw0 Hj) as (Hj765 & R436 & Hq & Hp3).
  pose proof (tb_range T 437) as R437.
  destruct HAT as (HK & R2 & R8 & R9 & R11 & R12 & R21 & R18 & R22 & R19 & R23 & R20 & R24 &
    R25 & R26 & R5 & R14 & R15 & R13 & R16 & R6 & R7 & R28).
  pose proof (ns_env regsj tx j T) as HE.
  set (E := NS regsj tx j T) in *.
  destruct HE as (E2 & E3 & E4 & E6 & E8 & E9 & E11 & E12 & E13 & E14 & E25 & E26 & E27 &
    E32 & E34 & E35 & E51 & E52 & E53).
  rewrite R8 in E8.
  assert (U8 : bv_unsigned (ew E 8) = tx) by (rewrite E8; unfold w64; apply unsigned_lit_small; lia).
  assert (U32 : bv_unsigned (ew E 32) = SB_NX) by (rewrite E32; unfold w64, SB_NX; apply unsigned_lit_small; lia).
  assert (U34 : bv_unsigned (ew E 34) = tb T 436) by (rewrite E34; unfold w64; apply unsigned_lit_small; lia).
  assert (U51 : bv_unsigned (ew E 51) = j) by (rewrite E51; unfold w64; apply unsigned_lit_small; lia).
  assert (HUB : U E BxN = SHADOW_OFF)
    by (unfold BxN; rewrite (U_atom E 32 SB_NX E32) by (unfold SB_NX; lia); reflexivity).
  split.
  - rewrite restrict_mkst_fx. unfold ss_rb. apply pa_entry_st_ok_full.
    + unfold sr_r.
      apply regs_ok_pin; [| intros X; discriminate X | refine (eq_trans R28 (eq_sym _)); reflexivity ].
      apply regs_ok_pin; [| intros X; discriminate X | refine (eq_trans R7 (eq_sym _)); reflexivity ].
      apply regs_ok_pin; [| intros X; discriminate X |
        refine (eq_trans R16 (eq_sym _)); apply (ns_denot_off E 8 tx 144 E8); lia ].
      apply regs_ok_pin; [| intros X; discriminate X |
        refine (eq_trans R15 (eq_sym _)); apply ns_denot_atom; exact E34 ].
      apply regs_ok_pin; [| intros X; discriminate X |
        refine (eq_trans R5 (eq_sym _)); apply ns_denot_atom; exact E51 ].
      apply regs_ok_pin; [| intros X; discriminate X |
        refine (eq_trans R24 (eq_sym _)); rewrite denot_lit_U, (ns_U_sha E tx 440 E8 E32) by lia;
        reflexivity ].
      apply regs_ok_pin; [| intros X; discriminate X |
        refine (eq_trans R20 (eq_sym _)); apply (ns_denot_off E 8 tx 440 E8); lia ].
      apply regs_ok_pin; [| intros X; discriminate X |
        refine (eq_trans R23 (eq_sym _)); rewrite denot_lit_U, (ns_U_sha E tx 444 E8 E32) by lia;
        reflexivity ].
      apply regs_ok_pin; [| intros X; discriminate X |
        refine (eq_trans R19 (eq_sym _)); apply (ns_denot_off E 8 tx 444 E8); lia ].
      apply regs_ok_pin; [| intros X; discriminate X |
        refine (eq_trans R22 (eq_sym _)); rewrite denot_lit_U, (ns_U_sha E tx 437 E8 E32) by lia;
        reflexivity ].
      apply regs_ok_pin; [| intros X; discriminate X |
        refine (eq_trans R18 (eq_sym _)); apply (ns_denot_off E 8 tx 437 E8); lia ].
      apply regs_ok_pin; [| intros X; discriminate X |
        refine (eq_trans R21 (eq_sym _)); apply ns_denot_atom; exact E32 ].
      unfold E, NS. apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + unfold ns_regs_b, ns_W440, ns_W437.
      repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      * rewrite U8. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable SEGS). apply (proj1 (Hgpres (tx + o) ltac:(lia))).
      * rewrite U8. split; [lia|]. split; [lia|]. split.
        -- intros o Ho. apply (apresent_writable SEGS). apply (proj1 (Hgpres (tx + o) ltac:(lia))).
        -- constructor; [|constructor].
           apply (chunk_ok_val SEGS E _ tx 437 1 (SOff 35 0) (tb T 437));
             [ apply ns_denot_atom; exact E35 | cbn; lia | cbn; lia | ].
           rewrite <- (tb_set4_out T 440 j 437) by lia.
           apply (ns_val1 _ tx (set4 T 440 j) 437 HOBJ). vm_compute. reflexivity.
    + apply pairwise_disjoint_of_extents.
      unfold ns_regs_b, ns_W440, ns_W437, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U8.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      repeat split; lia.
    + split; [| split; exact I].
      cbn [ns_atoms_b f_atoms atoms_ok]. unfold afact_ok, PTRN. cbn [af_lo af_hi af_al2].
      rewrite U8, U32, U34, U51.
      change (2 ^ 4) with 16. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
      unfold SB_NX. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
  - unfold sh_ok, ns_SH_b.
    constructor; [| constructor].
    apply (ns_shent_at lyc Sc W memj mdj E 8 tx tx TX_SIZE 0 460 HARj Hg HUB).
    + exact (U_atom E 8 tx E8 ltac:(lia)).
    + lia.
    + lia.
    + change (req_size TX_SIZE) with 460. lia.
Qed.

(* The exit to the emit block. *)
Lemma ns_emit_close : nx_emit_spec B ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
    (regs R : bvmap 5 word) memj mdj m md (tx chp parp valp : Z) (T : list byte) (j : Z) (n : nat),
  nx_ctx B STK sp0 FP ly S lyc Sc own W memc mdc regs tx chp parp valp T ->
  nx_mid B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs memj mdj tx chp parp valp (tx + 432) true ->
  nx_saved W memj regs (spZ regs) ->
  obj_at SEGS (mrestrict (w_H W) memj) tx LAY_TX (tx_vals (set4 T 440 j)) ->
  tb T 437 <> 0 -> 0 <= j < 3 * tb T 437 ->
  next_model T tx = walk (set4 T 440 j) tx (tb T 436) (tb T 448) (3 * tb T 437) j (Datatypes.S n) ->
  carried T (tb T 436) (tb T 448) j = true ->
  ns_inv W memj m tx ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m md k ->
  mbyte SEGS (mrestrict (w_H W) m) (tx + 437) = Some (Z_to_bv 8 (tb T 437)) ->
  (forall d, 0 <= d < 4 ->
     mbyte SEGS (mrestrict (w_H W) m) (tx + 440 + d) = Some (YP09.byte_of_word (Z_to_bv 64 (j + 1)) d)) ->
  nx_at_emit regs R tx chp parp valp T (tb T 436 + j / 3) (j mod 3) ->
  SRr SEGS W (cfg_at SEGS (BASE + EMIT) R m md)
    (tnext_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs tx chp parp valp T).
Proof.
  intros EMI STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R memj mdj m md
    tx chp parp valp T j n HCTX HMID HSAV HOBJ Hw0 Hj Hmodel Hcar HINV HJ H437 H440 HR.
  destruct (ns_ctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HCTX) as (_ & _ & _ & _ & _ & _ & _ & _ & HL & _).
  destruct (ns_tx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HCTX) as (_ & H4096 & Htxc & C1).
  destruct (ns_cut_mem STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs memj mdj m md
              tx chp parp valp T HCTX HMID HSAV HINV HJ) as [HMID2 HSAV2].
  apply (EMI STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R m md tx chp parp valp T j true
           HCTX HMID2 HSAV2).
  - apply (ns_tab_next W memj m tx T j HL ltac:(lia) ltac:(lia) HOBJ HINV H437 H440).
  - exact Hw0.
  - exact Hj.
  - rewrite carried_set4_440 by (pose proof (tb_range T 436); lia). exact Hcar.
  - rewrite Hmodel, ns_model_step by lia. rewrite Hcar. reflexivity.
  - exact HR.
Qed.

(* The state at LOOPR, seated by the case of the cell. *)
Lemma ns_seat_any : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS)
    memc mdc k (regs regsj : bvmap 5 word) memj mdj (tx chp parp valp : Z) (T : list byte) (j : Z),
  nx_ctx B STK sp0 FP ly S lyc Sc own W memc mdc regs tx chp parp valp T ->
  nx_mid B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs memj mdj tx chp parp valp (tx + 432) true ->
  obj_at SEGS (mrestrict (w_H W) memj) tx LAY_TX (tx_vals (set4 T 440 j)) ->
  tb T 437 <> 0 -> 0 <= j < 3 * tb T 437 ->
  nx_at_loopr regs regsj tx chp parp valp T j ->
  (tb T 436 + j / 3 <= 47 /\
   st_ok_pi SEGS VAL (NS regsj tx j T) ss_r
     (restrict (w_H W) (mkst regsj (Z_to_bv 64 (BASE + LOOPR)) memj (seg_rom SEGS))) /\
   sh_ok SEGS BxN ns_SH (NS regsj tx j T) (mrestrict (w_H W) memj)) \/
  (47 < tb T 436 + j / 3 /\
   st_ok_pi SEGS VAL (NS regsj tx j T) ss_rb
     (restrict (w_H W) (mkst regsj (Z_to_bv 64 (BASE + LOOPR)) memj (seg_rom SEGS))) /\
   sh_ok SEGS BxN ns_SH_b (NS regsj tx j T) (mrestrict (w_H W) memj)).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsj memj mdj
    tx chp parp valp T j HCTX HMID HOBJ Hw0 Hj HAT.
  destruct (Z_le_gt_dec (tb T 436 + j / 3) 47) as [Hc|Hc].
  - left. split; [exact Hc|].
    exact (ns_seat STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsj memj mdj
             tx chp parp valp T j HCTX HMID HOBJ Hw0 Hj Hc HAT).
  - right. split; [lia|].
    exact (ns_seat_b STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsj memj mdj
             tx chp parp valp T j HCTX HMID HOBJ Hw0 Hj HAT).
Qed.

(* ---------------------------------------------------------------- *)
(* The walk's tactics.                                                *)

(* A register's value at the end of a run: the engine's expression e, then tac. *)
Ltac ns_reg HS e tac :=
  lazymatch goal with |- getr _ ?r = ?v =>
  lazymatch type of HS with
  | st_ok_pi ?segs ?vl ?Ex ?ss (restrict ?Hh ?ms) =>
    refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ss ms r HS) (_ : sv_denot Ex e = v)); tac
  end end.

(* The three registers the function never writes. *)
Ltac ns_keep HS G3 G4 G27 :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; destruct Hr as [<- | [<- | [<- | []]]];
  [ ns_reg HS (SOff 3 0) ltac:(apply ns_denot_atom; exact G3)
  | ns_reg HS (SOff 4 0) ltac:(apply ns_denot_atom; exact G4)
  | ns_reg HS (SOff 27 0) ltac:(apply ns_denot_atom; exact G27) ].

(* After a run: the bytes it may have written are the two windows; keep the journal in the
   goal's form. *)
Ltac ns_step HINV U8 HJ :=
  lazymatch goal with
  | HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), HG : mem_grows _ _ |- _ =>
    let H := fresh "HINV" in
    pose proof (ns_inv_step _ _ _ _ _ _ _ HINV U8 HFr HG ltac:(vm_compute; reflexivity)) as H;
    clear HINV HFr HG; rename H into HINV
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end;
  rewrite ?wvb_collapse in HJ.

(* After a run that took fresh atoms (the set byte's shadow check does), the environment
   is E extended above atom 511: carry the facts about atoms below 512 over, and call the
   extended environment E again. *)
Ltac ns_shift HS E :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?E2 _ _ =>
    lazymatch E2 with
    | E => idtac
    | _ =>
      let Hag := fresh "Hag" in
      assert (Hag : forall nn, (nn < 512)%nat -> ew E2 nn = ew E nn)
        by (intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity);
      repeat match goal with
      | H : context [ew E ?n] |- _ => rewrite <- (Hag n ltac:(lia)) in H
      end;
      repeat match goal with H : img_env _ _ E |- _ => clear H end;
      let E' := fresh "E'" in
      set (E' := E2) in *; clearbody E'; clear Hag; clear E; rename E' into E
    end
  end.

Ltac ns_awr_tac U8 Hwtab :=
  eapply ns_awr; [vm_compute; reflexivity | exact U8 | exact Hwtab].

(* One run to the next stop, or to the slot stop, with the bookkeeping. *)
Ltac ns_run RUN HS HJ SHOK HINV U8 Hwtab E :=
  paj_run_tok RUN HS HJ SHOK BspanN; [ns_awr_tac U8 Hwtab |];
  ns_step HINV U8 HJ; ns_shift HS E.

Ltac ns_run_to RUNTO stop HS HJ SHOK HINV U8 Hwtab E :=
  paj_run_to_tok RUNTO HS HJ SHOK BspanN stop; [ns_awr_tac U8 Hwtab |];
  ns_step HINV U8 HJ; ns_shift HS E.

(* The registers every cut after the scan's prologue names: gp, tp, s11, sp, the table, the value,
   channel and parameter pointers, and the shadow base. *)
Ltac ns_regs_head HS A2 A8 A9 A11 A12 E32 G3 G4 G27 :=
  split; [unfold nx_keep_gp; ns_keep HS G3 G4 G27|];
  split; [ns_reg HS (SOff 2 0) ltac:(apply ns_denot_atom; exact A2)|];
  split; [ns_reg HS (SOff 8 0) ltac:(apply ns_denot_atom; exact A8)|];
  split; [ns_reg HS (SOff 9 0) ltac:(apply ns_denot_atom; exact A9)|];
  split; [ns_reg HS (SOff 11 0) ltac:(apply ns_denot_atom; exact A11)|];
  split; [ns_reg HS (SOff 12 0) ltac:(apply ns_denot_atom; exact A12)|];
  split; [ns_reg HS (SOff 32 0) ltac:(apply ns_denot_atom; exact E32)|].

(* s2..s4, s6..s8 (the three field addresses and their shadow addresses), s9 and s10. *)
Ltac ns_regs_fields HS E tx A8 E32 A25 A26 :=
  split; [ns_reg HS (SOff 8 437) ltac:(apply (ns_denot_off E 8 tx 437 A8); lia)|];
  split; [ns_reg HS (ns_sha 437) ltac:(rewrite denot_lit_U, (ns_U_sha E tx 437 A8 E32) by lia; reflexivity)|];
  split; [ns_reg HS (SOff 8 444) ltac:(apply (ns_denot_off E 8 tx 444 A8); lia)|];
  split; [ns_reg HS (ns_sha 444) ltac:(rewrite denot_lit_U, (ns_U_sha E tx 444 A8 E32) by lia; reflexivity)|];
  split; [ns_reg HS (SOff 8 440) ltac:(apply (ns_denot_off E 8 tx 440 A8); lia)|];
  split; [ns_reg HS (ns_sha 440) ltac:(rewrite denot_lit_U, (ns_U_sha E tx 440 A8 E32) by lia; reflexivity)|];
  split; [ns_reg HS (SOff 25 0) ltac:(apply ns_denot_atom; exact A25)|];
  split; [ns_reg HS (SOff 26 0) ltac:(apply ns_denot_atom; exact A26)|].

(* The registers at the emit block: the above, then the cell in a7 and the parameter in t0. *)
Ltac ns_emit_regs HS E tx j T A2 A8 A9 A11 A12 A25 A26 E32 E34 E51 Hj765 G3 G4 G27 :=
  ns_regs_head HS A2 A8 A9 A11 A12 E32 G3 G4 G27;
  ns_regs_fields HS E tx A8 E32 A25 A26;
  split; [ns_reg HS ns_c ltac:(rewrite denot_lit_U, (ns_U_c E j (tb T 436) E51 Hj765 E34) by lia;
                                unfold w64; f_equal; lia)|];
  ns_reg HS ns_PP ltac:(rewrite denot_lit_U, (ns_U_PP E j E51 Hj765); reflexivity).

Theorem pb_nx_rloop : nx_emit_spec B -> nx_resweep_spec B -> nx_rloop_spec B.
Proof.
  intros EMI RSW. unfold nx_rloop_spec.
  induction n as [|n IH];
    intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsj memj mdj
      tx chp parp valp T j HCTX HMID HSAV HOBJ Hw0 Hj0 Hjr Hn Hmodel HAT; [lia|].
  destruct (ns_ctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HCTX)
    as (HAR & Hg & Hoc & Hop & Hov & Hspr & Hceil & Hwtab & HL & HRok).
  destruct (ns_tx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HCTX) as (Hg16 & H4096 & Htxc & C1).
  assert (Htx0 : 0 <= tx) by lia. assert (Htx47 : tx + 460 <= 2 ^ 47) by lia.
  assert (Hj : 0 <= j < 3 * tb T 437) by lia.
  destruct (ns_arith T j Hw0 Hj) as (Hj765 & R436 & Hq & Hp3).
  pose proof (tb_range T 437) as R437.
  pose proof (tb_range T 448) as R448.
  assert (Hmax : Z.max (s32 T 440) (3 * tb T 437) = 3 * tb T 437) by lia.
  pose proof (ns_seat_any STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsj memj mdj
                tx chp parp valp T j HCTX HMID HOBJ Hw0 Hj HAT) as Hseat.
  pose proof (ns_env regsj tx j T) as HE.
  remember (NS regsj tx j T) as E eqn:HEdef.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  clear HEdef.
  destruct HE as (E2 & E3 & E4 & E6 & E8 & E9 & E11 & E12 & E13 & E14 & E25 & E26 & E27 &
    E32 & E34 & E35 & E51 & E52 & E53).
  pose proof HAT as (HK & R2 & R8 & R9 & R11 & R12 & R21 & R18 & R22 & R19 & R23 & R20 & R24 &
    R25 & R26 & R5 & R14 & R15 & R13 & R16 & R6 & R7 & R28).
  assert (A2 : ew E 2 = w64 (spZ regs - NX_FRAME)) by (rewrite E2; exact R2).
  assert (A6 : ew E 6 = w64 (18446744073709551615 - (tx + 144))) by (rewrite E6; exact R6).
  assert (A8 : ew E 8 = w64 tx) by (rewrite E8; exact R8).
  assert (A9 : ew E 9 = w64 valp) by (rewrite E9; exact R9).
  assert (A11 : ew E 11 = w64 chp) by (rewrite E11; exact R11).
  assert (A12 : ew E 12 = w64 parp) by (rewrite E12; exact R12).
  assert (A13 : ew E 13 = w64 (tb T 448)) by (rewrite E13; exact R13).
  assert (A14 : ew E 14 = w64 (Z.max (s32 T 440) (3 * tb T 437))) by (rewrite E14; exact R14).
  assert (A14b : ew E 14 = w64 (3 * tb T 437)) by (rewrite A14, Hmax; reflexivity).
  assert (A25 : ew E 25 = w64 (3 * tb T 437)) by (rewrite E25; exact R25).
  assert (A26 : ew E 26 = w64 ((tx + 440) mod 8 + 3)) by (rewrite E26; exact R26).
  assert (G3 : ew E 3 = getr regs 3) by (rewrite E3; apply HK; cbn [In]; repeat (first [left; reflexivity | right])).
  assert (G4 : ew E 4 = getr regs 4) by (rewrite E4; apply HK; cbn [In]; repeat (first [left; reflexivity | right])).
  assert (G27 : ew E 27 = getr regs 27) by (rewrite E27; apply HK; cbn [In]; repeat (first [left; reflexivity | right])).
  clear E2 E3 E4 E6 E8 E9 E11 E12 E13 E14 E25 E26 E27.
  assert (U8 : bv_unsigned (ew E 8) = tx) by (rewrite A8; unfold w64; apply unsigned_lit_small; lia).
  pose proof HMID as (HJ & _).
  pose proof (ns_inv_refl W memj tx) as HINV.
  unfold cfg_at. change (w64 (BASE + LOOPR)) with (Z_to_bv 64 (BASE + LOOPR)).
  destruct Hseat as [(Hc47 & HS & SHOK) | (Hc47 & HS & SHOK)].
  - (* the cell is at most 47: the set byte is a table byte, and is seated *)
    pose proof (tb_range T (ns_cell T j)) as Rcell.
    (* LOOPR .. 0x861fc: the cursor's shadow byte, the division by 3, the cursor store *)
    ns_run RUN HS HJ SHOK HINV U8 Hwtab E.
    psrr_branch_tok RUN BR HS SHOK BspanN.
    + (* 0x861fc taken: the set-only flag is 0 *)
      assert (Ho0 : branch_taken BC_EQ (sv_denot E (SOff 13 0)) (sv_denot E (SLit 0)) = true) by exact Hc.
      clear Hc.
      rewrite branch_eq_U, (U_atom E 13 (tb T 448) A13), U_SLit in Ho0 by lia.
      change (zcanon 0) with 0 in Ho0. apply Z.eqb_eq in Ho0.
      ns_run_to RUNTO EMIT HS HJ SHOK HINV U8 Hwtab E.
      lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
        pose proof (ns_st_region E _ _ ns_W440f HS ltac:(cbn [ss_mem]; left; reflexivity)) as RW440;
        pose proof (ns_st_region E _ _ ns_W437 HS ltac:(cbn [ss_mem]; right; left; reflexivity)) as RW437;
        cbn [restrict ms_mem] in RW440, RW437;
        pose proof (ns_b440 E _ tx j U8 E51 Hj765 RW440) as H440;
        pose proof (ns_b437 E _ tx T U8 E35 RW437) as H437
      end.
      pmkst HS.
      apply (ns_at W _ (BASE + EMIT)); [unfold EMIT, AF_reac_headamp_tx_next; lia|].
      eapply (ns_emit_close EMI STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs _ memj mdj
                _ _ tx chp parp valp T j n HCTX HMID HSAV HOBJ Hw0 Hj Hmodel (ns_carried_o0 T j Ho0) HINV HJ H437 H440).
      ns_emit_regs HS E tx j T A2 A8 A9 A11 A12 A25 A26 E32 E34 E51 Hj765 G3 G4 G27.
    + (* 0x861fc not taken *)
      assert (Ho : branch_taken BC_EQ (sv_denot E (SOff 13 0)) (sv_denot E (SLit 0)) = false) by exact Hc.
      clear Hc.
      rewrite branch_eq_U, (U_atom E 13 (tb T 448) A13), U_SLit in Ho by lia.
      change (zcanon 0) with 0 in Ho. apply Z.eqb_neq in Ho.
      ns_run RUN HS HJ SHOK HINV U8 Hwtab E.
      psrr_branch_tok RUN BR HS SHOK BspanN.
      * (* 0x86200 taken: 47 < c, which this case excludes *)
        assert (Hc' : branch_taken BC_LT (sv_denot E (SLit 47)) (sv_denot E ns_c) = true) by exact Hc.
        clear Hc. exfalso. rewrite ns_bt_lt in Hc'.
        rewrite (ns_Sg E (SLit 47) 47 ltac:(rewrite U_SLit; apply zcanon_id; unfold M64; lia) ltac:(lia)) in Hc'.
        rewrite (ns_Sg E ns_c (tb T 436 + j / 3)
                   ltac:(rewrite (ns_U_c E j (tb T 436) E51 Hj765 E34) by lia; lia) ltac:(lia)) in Hc'.
        apply Z.ltb_lt in Hc'. lia.
      * (* 0x86200 not taken *)
        clear Hc. ns_run RUN HS HJ SHOK HINV U8 Hwtab E.
        psrr_branch_tok RUN BR HS SHOK BspanN.
        -- (* T12 0x86204 taken: 47 < c unsigned; but 0 <= c <= 47 *)
           assert (Hc' : branch_taken BC_LTU (sv_denot E (SLit 47)) (sv_denot E ns_c) = true) by exact Hc.
           clear Hc. exfalso.
           rewrite branch_ltu_U, U_SLit, (ns_U_c E j (tb T 436) E51 Hj765 E34) in Hc' by lia.
           change (zcanon 47) with 47 in Hc'. apply Z.ltb_lt in Hc'. lia.
        -- clear Hc. ns_run RUN HS HJ SHOK HINV U8 Hwtab E.
           psrr_branch_tok RUN BR HS SHOK BspanN.
           ++ (* T13 0x86210 taken: ~(tx + 144) < 3c unsigned; but tx + 144 + 3c < 2 ^ 64 *)
              assert (Hc' : branch_taken BC_LTU (sv_denot E (SOff 6 0)) (sv_denot E ns_c3) = true)
                by exact Hc.
              clear Hc. exfalso.
              rewrite branch_ltu_U, (U_atom E 6 _ A6), (ns_U_c3 E j (tb T 436) E51 Hj765 E34) in Hc' by lia.
              apply Z.ltb_lt in Hc'. lia.
           ++ clear Hc. ns_run RUN HS HJ SHOK HINV U8 Hwtab E.
              psrr_branch_tok RUN BR HS SHOK BspanN.
              ** (* T14 0x86214 taken: p < 0; but p = j mod 3 *)
                 assert (Hc' : branch_taken BC_LT (sv_denot E ns_PP) (sv_denot E (SLit 0)) = true)
                   by exact Hc.
                 clear Hc. exfalso. rewrite ns_bt_lt in Hc'.
                 rewrite (ns_Sg E ns_PP (j mod 3) (ns_U_PP E j E51 Hj765) ltac:(lia)) in Hc'.
                 rewrite (ns_Sg E (SLit 0) 0 ltac:(rewrite U_SLit; reflexivity) ltac:(lia)) in Hc'.
                 apply Z.ltb_lt in Hc'. lia.
              ** clear Hc. ns_run RUN HS HJ SHOK HINV U8 Hwtab E.
                 psrr_branch_tok RUN BR HS SHOK BspanN.
                 --- (* T15 0x86220 taken: ~(tx + 144 + 3c) < p unsigned; but the sum stays below
                        2 ^ 64 *)
                     assert (Hc' : branch_taken BC_LTU
                                     (sv_denot E (SAlu ALU_XOR (SAlu ALU_ADD (SOff 8 144) ns_c3) (SLit (-1))))
                                     (sv_denot E ns_PP) = true) by exact Hc.
                     clear Hc. exfalso.
                     rewrite branch_ltu_U, (ns_U_PP E j E51 Hj765) in Hc'.
                     rewrite U_SAlu in Hc'. cbn [zalu_raw] in Hc'.
                     rewrite (ns_U_a144 E tx j (tb T 436) A8 Htx0 Htx47 E51 Hj765 E34) in Hc' by lia.
                     rewrite U_SLit in Hc'. change (zcanon (-1)) with (2 ^ 64 - 1) in Hc'.
                     rewrite lxor_allones in Hc' by lia.
                     rewrite zcanon_id in Hc' by (unfold M64; lia).
                     apply Z.ltb_lt in Hc'. lia.
                 --- (* 0x86220 not taken: the set byte's shadow byte, then the set byte *)
                     clear Hc. ns_run RUN HS HJ SHOK HINV U8 Hwtab E.
                     psrr_branch_tok RUN BR HS SHOK BspanN.
                     +++ (* 0x8623c taken: the cell is set *)
                         assert (Hc' : branch_taken BC_NE (sv_denot E (SOff 53 0)) (sv_denot E (SLit 0)) = true)
                           by exact Hc. clear Hc.
                         rewrite branch_ne_U, (U_atom E 53 (tb T (ns_cell T j)) E53), U_SLit in Hc' by lia.
                         change (zcanon 0) with 0 in Hc'. apply (proj1 (negb_true_iff _)), Z.eqb_neq in Hc'.
                         ns_run_to RUNTO EMIT HS HJ SHOK HINV U8 Hwtab E.
                         lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
                           pose proof (ns_st_region E _ _ ns_W440f HS ltac:(cbn [ss_mem]; left; reflexivity)) as RW440;
                           pose proof (ns_st_region E _ _ ns_W437 HS ltac:(cbn [ss_mem]; right; left; reflexivity)) as RW437;
                           cbn [restrict ms_mem] in RW440, RW437;
                           pose proof (ns_b440 E _ tx j U8 E51 Hj765 RW440) as H440;
                           pose proof (ns_b437 E _ tx T U8 E35 RW437) as H437
                         end.
                         pmkst HS.
                         apply (ns_at W _ (BASE + EMIT)); [unfold EMIT, AF_reac_headamp_tx_next; lia|].
                         eapply (ns_emit_close EMI STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs _ memj mdj
                                   _ _ tx chp parp valp T j n HCTX HMID HSAV HOBJ Hw0 Hj Hmodel (ns_carried_set T j Hc47 Hc') HINV HJ H437 H440).
                         ns_emit_regs HS E tx j T A2 A8 A9 A11 A12 A25 A26 E32 E34 E51 Hj765 G3 G4 G27.
                     +++ (* 0x8623c not taken: the cell is not set *)
                         assert (Hc' : branch_taken BC_NE (sv_denot E (SOff 53 0)) (sv_denot E (SLit 0)) = false)
                           by exact Hc. clear Hc.
                         rewrite branch_ne_U, (U_atom E 53 (tb T (ns_cell T j)) E53), U_SLit in Hc' by lia.
                         change (zcanon 0) with 0 in Hc'. apply (proj1 (negb_false_iff _)), Z.eqb_eq in Hc'.
                         pose proof (ns_carried_unset T j Ho Hc') as Hcar.
                         rewrite ns_model_step, Hcar in Hmodel by lia.
                         ns_run RUN HS HJ SHOK HINV U8 Hwtab E.
                         psrr_branch_tok RUN BR HS SHOK BspanN.
                         { (* 0x86244 taken: j + 1 is not the end; back to LOOPR *)
                           assert (Hc2 : branch_taken BC_NE (sv_denot E (SOff 14 0)) (sv_denot E (SOff 51 1)) = true) by exact Hc.
                           clear Hc.
                           rewrite branch_ne_U, (U_atom E 14 (3 * tb T 437) A14b), (U_atom_off E 51 j 1 E51) in Hc2 by lia.
                           apply (proj1 (negb_true_iff _)), Z.eqb_neq in Hc2.
                           rewrite (proj2 (Z.eqb_neq (j + 1) (3 * tb T 437)) ltac:(lia)) in Hmodel.
                           ns_run_to RUNTO LOOPR HS HJ SHOK HINV U8 Hwtab E.
                           lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
                             pose proof (ns_st_region E _ _ ns_W440f HS ltac:(cbn [ss_mem]; left; reflexivity)) as RW440;
                             pose proof (ns_st_region E _ _ ns_W437 HS ltac:(cbn [ss_mem]; right; left; reflexivity)) as RW437;
                             cbn [restrict ms_mem] in RW440, RW437;
                             pose proof (ns_b440 E _ tx j U8 E51 Hj765 RW440) as H440;
                             pose proof (ns_b437 E _ tx T U8 E35 RW437) as H437
                           end.
                           pmkst HS.
                           apply (ns_at W _ (BASE + LOOPR)); [unfold LOOPR, AF_reac_headamp_tx_next; lia|].
                           lazymatch goal with |- SRr _ _ (cfg_at _ _ ?Rx ?Mx ?Dx) _ =>
                             destruct (ns_cut_mem STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs memj mdj
                                         Mx Dx tx chp parp valp T HCTX HMID HSAV HINV HJ) as [HMID2 HSAV2];
                             apply (IH STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Rx Mx Dx
                                      tx chp parp valp T (j + 1) HCTX HMID2 HSAV2)
                           end.
                           - exact (ns_tab_next W memj _ tx T j HL Htx0 Htx47 HOBJ HINV H437 H440).
                           - exact Hw0.
                           - lia.
                           - lia.
                           - lia.
                           - exact Hmodel.
                           - ns_regs_head HS A2 A8 A9 A11 A12 E32 G3 G4 G27.
                             ns_regs_fields HS E tx A8 E32 A25 A26.
                             split; [ns_reg HS (SOff 51 1) ltac:(apply (ns_denot_off E 51 j 1 E51); lia)|].
                             split; [ns_reg HS (SOff 14 0) ltac:(apply ns_denot_atom; exact A14)|].
                             split; [ns_reg HS (SOff 34 0) ltac:(apply ns_denot_atom; exact E34)|].
                             split; [ns_reg HS (SOff 13 0) ltac:(apply ns_denot_atom; exact A13)|].
                             split; [ns_reg HS (SOff 8 144) ltac:(apply (ns_denot_off E 8 tx 144 A8); lia)|].
                             split; [ns_reg HS (SOff 6 0) ltac:(apply ns_denot_atom; exact A6)|].
                             split; [ns_reg HS (SLit 1431655766) ltac:(reflexivity)|].
                             ns_reg HS (SLit 47) ltac:(reflexivity). }
                         { (* 0x86244 not taken: j + 1 = 3 * width; the width is cleared (0x86268), then RSWP *)
                           assert (Hc2 : branch_taken BC_NE (sv_denot E (SOff 14 0)) (sv_denot E (SOff 51 1)) = false) by exact Hc.
                           clear Hc.
                           rewrite branch_ne_U, (U_atom E 14 (3 * tb T 437) A14b), (U_atom_off E 51 j 1 E51) in Hc2 by lia.
                           apply (proj1 (negb_false_iff _)), Z.eqb_eq in Hc2.
                           rewrite (proj2 (Z.eqb_eq (j + 1) (3 * tb T 437)) ltac:(lia)) in Hmodel.
                           ns_run_to RUNTO RSWP HS HJ SHOK HINV U8 Hwtab E.
                           lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
                             pose proof (ns_st_region E _ _ ns_W440f HS ltac:(cbn [ss_mem]; left; reflexivity)) as RW440;
                             pose proof (ns_st_region E _ _ ns_W437z HS ltac:(cbn [ss_mem]; right; left; reflexivity)) as RW437;
                             cbn [restrict ms_mem] in RW440, RW437;
                             pose proof (ns_b440 E _ tx j U8 E51 Hj765 RW440) as H440;
                             pose proof (ns_b437z E _ tx U8 RW437) as H437
                           end.
                           pmkst HS.
                           apply (ns_at W _ (BASE + RSWP)); [unfold RSWP, AF_reac_headamp_tx_next; lia|].
                           assert (HL4 : length (set4 T 440 (j + 1)) = 460%nat) by (apply len_set4; lia).
                           lazymatch goal with |- SRr _ _ (cfg_at _ _ ?Rx ?Mx ?Dx) _ =>
                             destruct (ns_cut_mem STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs memj mdj
                                         Mx Dx tx chp parp valp T HCTX HMID HSAV HINV HJ) as [HMID2 HSAV2];
                             apply (RSW STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Rx Mx Dx
                                      tx chp parp valp T (setb (set4 T 440 (j + 1)) 437 0) HCTX HMID2 HSAV2)
                           end.
                           - exact (ns_tab_rsw W memj _ tx T j HL Htx0 Htx47 HOBJ HINV H437 H440).
                           - apply len_setb; [exact HL4 | lia].
                           - apply tb_setb_in; [exact HL4 | lia | lia].
                           - intros l Hl. rewrite tb_setb_out by lia. apply tb_set4_out; lia.
                           - exact Hmodel.
                           - ns_regs_head HS A2 A8 A9 A11 A12 E32 G3 G4 G27.
                             split; [ns_reg HS (SOff 8 437) ltac:(apply (ns_denot_off E 8 tx 437 A8); lia)|].
                             ns_reg HS (ns_sha 437) ltac:(rewrite denot_lit_U, (ns_U_sha E tx 437 A8 E32) by lia; reflexivity). }
  - (* the cell is above 47: the set byte is never read *)
    ns_run RUN HS HJ SHOK HINV U8 Hwtab E.
    psrr_branch_tok RUN BR HS SHOK BspanN.
    + (* 0x861fc taken: the set-only flag is 0 *)
      assert (Ho0 : branch_taken BC_EQ (sv_denot E (SOff 13 0)) (sv_denot E (SLit 0)) = true) by exact Hc.
      clear Hc.
      rewrite branch_eq_U, (U_atom E 13 (tb T 448) A13), U_SLit in Ho0 by lia.
      change (zcanon 0) with 0 in Ho0. apply Z.eqb_eq in Ho0.
      ns_run_to RUNTO EMIT HS HJ SHOK HINV U8 Hwtab E.
      lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
        pose proof (ns_st_region E _ _ ns_W440f HS ltac:(cbn [ss_mem]; left; reflexivity)) as RW440;
        pose proof (ns_st_region E _ _ ns_W437 HS ltac:(cbn [ss_mem]; right; left; reflexivity)) as RW437;
        cbn [restrict ms_mem] in RW440, RW437;
        pose proof (ns_b440 E _ tx j U8 E51 Hj765 RW440) as H440;
        pose proof (ns_b437 E _ tx T U8 E35 RW437) as H437
      end.
      pmkst HS.
      apply (ns_at W _ (BASE + EMIT)); [unfold EMIT, AF_reac_headamp_tx_next; lia|].
      eapply (ns_emit_close EMI STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs _ memj mdj
                _ _ tx chp parp valp T j n HCTX HMID HSAV HOBJ Hw0 Hj Hmodel (ns_carried_o0 T j Ho0) HINV HJ H437 H440).
      ns_emit_regs HS E tx j T A2 A8 A9 A11 A12 A25 A26 E32 E34 E51 Hj765 G3 G4 G27.
    + (* 0x861fc not taken *)
      assert (Ho : branch_taken BC_EQ (sv_denot E (SOff 13 0)) (sv_denot E (SLit 0)) = false) by exact Hc.
      clear Hc.
      rewrite branch_eq_U, (U_atom E 13 (tb T 448) A13), U_SLit in Ho by lia.
      change (zcanon 0) with 0 in Ho. apply Z.eqb_neq in Ho.
      ns_run RUN HS HJ SHOK HINV U8 Hwtab E.
      psrr_branch_tok RUN BR HS SHOK BspanN.
      * (* 0x86200 taken: 47 < c, so the cell is not carried; on to 0x86240 *)
        clear Hc.
        pose proof (ns_carried_big T j Ho Hc47) as Hcar.
        rewrite ns_model_step, Hcar in Hmodel by lia.
        ns_run RUN HS HJ SHOK HINV U8 Hwtab E.
        psrr_branch_tok RUN BR HS SHOK BspanN.
        { (* 0x86244 taken: j + 1 is not the end; back to LOOPR *)
          assert (Hc2 : branch_taken BC_NE (sv_denot E (SOff 14 0)) (sv_denot E (SOff 51 1)) = true) by exact Hc.
          clear Hc.
          rewrite branch_ne_U, (U_atom E 14 (3 * tb T 437) A14b), (U_atom_off E 51 j 1 E51) in Hc2 by lia.
          apply (proj1 (negb_true_iff _)), Z.eqb_neq in Hc2.
          rewrite (proj2 (Z.eqb_neq (j + 1) (3 * tb T 437)) ltac:(lia)) in Hmodel.
          ns_run_to RUNTO LOOPR HS HJ SHOK HINV U8 Hwtab E.
          lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
            pose proof (ns_st_region E _ _ ns_W440f HS ltac:(cbn [ss_mem]; left; reflexivity)) as RW440;
            pose proof (ns_st_region E _ _ ns_W437 HS ltac:(cbn [ss_mem]; right; left; reflexivity)) as RW437;
            cbn [restrict ms_mem] in RW440, RW437;
            pose proof (ns_b440 E _ tx j U8 E51 Hj765 RW440) as H440;
            pose proof (ns_b437 E _ tx T U8 E35 RW437) as H437
          end.
          pmkst HS.
          apply (ns_at W _ (BASE + LOOPR)); [unfold LOOPR, AF_reac_headamp_tx_next; lia|].
          lazymatch goal with |- SRr _ _ (cfg_at _ _ ?Rx ?Mx ?Dx) _ =>
            destruct (ns_cut_mem STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs memj mdj
                        Mx Dx tx chp parp valp T HCTX HMID HSAV HINV HJ) as [HMID2 HSAV2];
            apply (IH STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Rx Mx Dx
                     tx chp parp valp T (j + 1) HCTX HMID2 HSAV2)
          end.
          - exact (ns_tab_next W memj _ tx T j HL Htx0 Htx47 HOBJ HINV H437 H440).
          - exact Hw0.
          - lia.
          - lia.
          - lia.
          - exact Hmodel.
          - ns_regs_head HS A2 A8 A9 A11 A12 E32 G3 G4 G27.
            ns_regs_fields HS E tx A8 E32 A25 A26.
            split; [ns_reg HS (SOff 51 1) ltac:(apply (ns_denot_off E 51 j 1 E51); lia)|].
            split; [ns_reg HS (SOff 14 0) ltac:(apply ns_denot_atom; exact A14)|].
            split; [ns_reg HS (SOff 34 0) ltac:(apply ns_denot_atom; exact E34)|].
            split; [ns_reg HS (SOff 13 0) ltac:(apply ns_denot_atom; exact A13)|].
            split; [ns_reg HS (SOff 8 144) ltac:(apply (ns_denot_off E 8 tx 144 A8); lia)|].
            split; [ns_reg HS (SOff 6 0) ltac:(apply ns_denot_atom; exact A6)|].
            split; [ns_reg HS (SLit 1431655766) ltac:(reflexivity)|].
            ns_reg HS (SLit 47) ltac:(reflexivity). }
        { (* 0x86244 not taken: j + 1 = 3 * width; the width is cleared (0x86268), then RSWP *)
          assert (Hc2 : branch_taken BC_NE (sv_denot E (SOff 14 0)) (sv_denot E (SOff 51 1)) = false) by exact Hc.
          clear Hc.
          rewrite branch_ne_U, (U_atom E 14 (3 * tb T 437) A14b), (U_atom_off E 51 j 1 E51) in Hc2 by lia.
          apply (proj1 (negb_false_iff _)), Z.eqb_eq in Hc2.
          rewrite (proj2 (Z.eqb_eq (j + 1) (3 * tb T 437)) ltac:(lia)) in Hmodel.
          ns_run_to RUNTO RSWP HS HJ SHOK HINV U8 Hwtab E.
          lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
            pose proof (ns_st_region E _ _ ns_W440f HS ltac:(cbn [ss_mem]; left; reflexivity)) as RW440;
            pose proof (ns_st_region E _ _ ns_W437z HS ltac:(cbn [ss_mem]; right; left; reflexivity)) as RW437;
            cbn [restrict ms_mem] in RW440, RW437;
            pose proof (ns_b440 E _ tx j U8 E51 Hj765 RW440) as H440;
            pose proof (ns_b437z E _ tx U8 RW437) as H437
          end.
          pmkst HS.
          apply (ns_at W _ (BASE + RSWP)); [unfold RSWP, AF_reac_headamp_tx_next; lia|].
          assert (HL4 : length (set4 T 440 (j + 1)) = 460%nat) by (apply len_set4; lia).
          lazymatch goal with |- SRr _ _ (cfg_at _ _ ?Rx ?Mx ?Dx) _ =>
            destruct (ns_cut_mem STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs memj mdj
                        Mx Dx tx chp parp valp T HCTX HMID HSAV HINV HJ) as [HMID2 HSAV2];
            apply (RSW STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Rx Mx Dx
                     tx chp parp valp T (setb (set4 T 440 (j + 1)) 437 0) HCTX HMID2 HSAV2)
          end.
          - exact (ns_tab_rsw W memj _ tx T j HL Htx0 Htx47 HOBJ HINV H437 H440).
          - apply len_setb; [exact HL4 | lia].
          - apply tb_setb_in; [exact HL4 | lia | lia].
          - intros l Hl. rewrite tb_setb_out by lia. apply tb_set4_out; lia.
          - exact Hmodel.
          - ns_regs_head HS A2 A8 A9 A11 A12 E32 G3 G4 G27.
            split; [ns_reg HS (SOff 8 437) ltac:(apply (ns_denot_off E 8 tx 437 A8); lia)|].
            ns_reg HS (ns_sha 437) ltac:(rewrite denot_lit_U, (ns_U_sha E tx 437 A8 E32) by lia; reflexivity). }
      * (* 0x86200 not taken: c <= 47, which this case excludes *)
        assert (Hc' : branch_taken BC_LT (sv_denot E (SLit 47)) (sv_denot E ns_c) = false) by exact Hc.
        clear Hc. exfalso. rewrite ns_bt_lt in Hc'.
        rewrite (ns_Sg E (SLit 47) 47 ltac:(rewrite U_SLit; apply zcanon_id; unfold M64; lia) ltac:(lia)) in Hc'.
        rewrite (ns_Sg E ns_c (tb T 436 + j / 3)
                   ltac:(rewrite (ns_U_c E j (tb T 436) E51 Hj765 E34) by lia; lia) ltac:(lia)) in Hc'.
        apply Z.ltb_ge in Hc'. lia.
Qed.

End h.
End f.
End d.
