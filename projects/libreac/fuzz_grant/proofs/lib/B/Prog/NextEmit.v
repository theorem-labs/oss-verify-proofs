(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a segment of reac_headamp_tx_next on fuzz_grant.asan (NextEmit), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AE25.v. *)
(* Modified by Theorem Labs, 2026-10: image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/NextEmit.v at a working branch af735a950e2 (blob e30cc98162f; the walk was ported from blob 60069068e45 at a working branch afd75724b5b, which differs from it only by 4 added and 0 removed lines, the licence header), restated over image B's listing, addresses and walk layer (lib/B/Prog) against GrantBContracts.v; image A inlines reac_headamp_tx_effective into this block and image B calls it at 0x863dc, so the call is made through cl_callS (lib/B/Prog/YC85.v, the concrete-state form of aj_call over afn_pre_at) and the callee's contract, and UBSan traps T16..T18 are new *)
(* The replay emit block of reac_headamp_tx_next on the ASan+UBSan build (fuzz_grant.asan-ubsan
   0x863a0 .. 0x86448, the slot lib/B/Prog/HeadampTxNext.v names EMIT), the shared return tail
   0x860f4 .. 0x860fc and the epilogue 0x862cc .. 0x86300: the walk of the cut nx_emit_spec.

   The block stores the channel and the parameter into the two bytes the caller holds, calls
   reac_headamp_tx_effective (a0 = tx, a1 = c & 0xff, a2 = p & 0xff), stores its answer into the
   third byte, reads the cursor back, sets the wait (444) or clears the replay width (437), clears
   the silence counter (456) and returns 1. The answer is Pau Aliagas's emit_res.

   The walk is cut at the call. Before it, one run from EMIT to the call; after it, the state at
   EMR (0x863e0) is seated afresh from the call's post (its journal, its kept classes, the table it
   leaves) and one run to the cursor branch, then one run per arm to the epilogue's ret.

   UBSan traps (all to the `unimp` at 0x8644c):
     T16 0x863a0 `beqz a1` (chp = 0), T17 0x863b8 `beqz a2` (parp = 0), T18 0x863e0 `beqz s1`
     (valp = 0): each is decided inside a run, from the atom facts 4096 <= chp, parp, valp
     (thd_out_ok);
     T19 the fall-through of 0x86448 (`jal errpath_store4`) into 0x8644c: unreached, chk#35 passes.
   ASan report branches, each decided inside a run from the shadow entries:
     chk#29 0x863b0 (chp, store1, slow block 0x865d8) and chk#30 0x863c8 (parp, store1, slow block
       0x865e8): mkSHE 11 0 1 and mkSHE 12 0 1, from the contract's byte_ok of chp and parp, which
       still holds at EMIT because nx_same keeps the caller's shadow bytes (em_ra_keep);
     chk#31 0x863f0 (valp, store1, slow block 0x865f8): mkSHE 9 0 1, re-established after the call
       from the callee's journal and the post-call AR (em_out_ra);
     chk#32 0x863fc (tx + 440, load4), chk#33 0x8640c (tx + 444, store4), chk#34 0x86420
       (tx + 437, store1), chk#35 0x86438 / 0x86444 (tx + 456, store4, inline slow form; the
       table's last granule is partly usable, 460 = 57 * 8 + 4): mkSHE 8 0 460, from the block
       shadow law of the post-call AR (shent_ok_of_block). *)
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
GrantTop GrantSyms GrantList GrantAddr GrantPa GrantPaLib GrantFrame GrantRo YC1g GrantACjr YC85.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import Mem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import
HeadampModel NextModel NextLemmas SlotNeeds_c HeadampI1.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantBContracts HeadampTxNext.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Notation TX_SIZE := ATx.TX_SIZE.
#[local] Notation LAY_TX := ATx.LAY_TX.
#[local] Notation tx_vals := ATx.tx_vals.
#[local] Notation tx_fbyte := ATx.tx_fbyte.

(* ---- small arithmetic facts ------------------------------------------------------------ *)

Lemma em_bow0 : forall k, YP09.byte_of_word (Z_to_bv 64 0) k = Z_to_bv 8 0.
Proof.
  intros k. unfold YP09.byte_of_word. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  rewrite Z.shiftr_0_l. reflexivity.
Qed.

Lemma em_bow11 : forall d, 0 <= d < 4 ->
  YP09.byte_of_word (Z_to_bv 64 11) d = Z_to_bv 8 (nth (Z.to_nat d) [11; 0; 0; 0] 0).
Proof.
  intros d Hd. unfold YP09.byte_of_word. rewrite unsigned_lit_small by lia.
  assert (d = 0 \/ d = 1 \/ d = 2 \/ d = 3) as [-> | [-> | [-> | ->]]] by lia;
    vm_compute; reflexivity.
Qed.

Lemma em_bow1 : forall v, 0 <= v < 256 -> YP09.byte_of_word (Z_to_bv 64 v) 0 = Z_to_bv 8 v.
Proof.
  intros v Hv. unfold YP09.byte_of_word. rewrite unsigned_lit_small by lia.
  change (8 * 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
Qed.

Lemma em_bow_u32 : forall T k d, 0 <= d < 4 ->
  YP09.byte_of_word (Z_to_bv 64 (u32at T k)) d = Z_to_bv 8 (tb T (k + d)).
Proof.
  intros T k d Hd.
  pose proof (ATx.tb_range T k). pose proof (ATx.tb_range T (k + 1)).
  pose proof (ATx.tb_range T (k + 2)). pose proof (ATx.tb_range T (k + 3)).
  assert (Hr : 0 <= u32at T k < 4294967296) by (unfold u32at; lia).
  unfold YP09.byte_of_word. rewrite unsigned_lit_small by lia.
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. rewrite Z.shiftr_div_pow2 by lia.
  assert (d = 0 \/ d = 1 \/ d = 2 \/ d = 3) as [-> | [-> | [-> | ->]]] by lia.
  - change (8 * 0) with 0. rewrite Z.pow_0_r, Z.div_1_r, Z.add_0_r.
    unfold u32at. Z.div_mod_to_equations. lia.
  - change (8 * 1) with 8. change (2 ^ 8) with 256. unfold u32at. Z.div_mod_to_equations. lia.
  - change (8 * 2) with 16. change (2 ^ 16) with 65536. unfold u32at. Z.div_mod_to_equations. lia.
  - change (8 * 3) with 24. change (2 ^ 24) with 16777216. unfold u32at. Z.div_mod_to_equations. lia.
Qed.

Lemma em_eff_range : forall T t ch p, 0 <= eff T t ch p < 256.
Proof.
  intros T t ch p. unfold eff. destruct (3 <=? p); [lia|].
  destruct ((t =? 0) || (48 <=? ch))%bool; [apply dflt_range|].
  destruct (tb T (144 + 3 * ch + p) =? 0); [apply dflt_range | apply ATx.tb_range].
Qed.

Lemma em_signed_lit : forall z, - 2 ^ 63 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. assert (Hh : bv_half_modulus 64 = 2 ^ 63) by reflexivity.
  assert (Hm : bv_modulus 64 = 2 ^ 64) by reflexivity.
  unfold bv_signed, bv_swrap. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite Hh, Hm.
  rewrite Zplus_mod_idemp_l. rewrite Z.mod_small by lia. lia.
Qed.

Lemma em_bge_lit : forall a b, 0 <= a < 2 ^ 63 -> 0 <= b < 2 ^ 63 ->
  branch_taken BC_GE (Z_to_bv 64 a) (Z_to_bv 64 b) = negb (a <? b).
Proof.
  intros a b Ha Hb. cbn [branch_taken]. unfold bv_lts. rewrite !em_signed_lit by lia. reflexivity.
Qed.

Lemma em_div8 : forall lo hi a, lo mod 4096 = 0 -> hi mod 4096 = 0 -> lo <= a < hi ->
  0 <= a / 8 - lo / 8 < (hi - lo) / 8.
Proof.
  intros lo hi a Hlo Hhi Ha.
  assert (L8 : lo mod 8 = 0).
  { apply Z.mod_divide in Hlo as [q Hq]; [|lia]. rewrite Hq. replace (q * 4096) with (q * 512 * 8) by lia.
    apply Z.mod_mul. lia. }
  assert (H8 : hi mod 8 = 0).
  { apply Z.mod_divide in Hhi as [q Hq]; [|lia]. rewrite Hq. replace (q * 4096) with (q * 512 * 8) by lia.
    apply Z.mod_mul. lia. }
  pose proof (Z.div_mod lo 8 ltac:(lia)). pose proof (Z.div_mod hi 8 ltac:(lia)).
  pose proof (Z.div_mod a 8 ltac:(lia)). pose proof (Z.mod_pos_bound a 8 ltac:(lia)).
  pose proof (Z.div_mod (hi - lo) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (hi - lo) 8 ltac:(lia)).
  lia.
Qed.

(* ---- the two symbolic states ------------------------------------------------------------- *)

(* The shadow byte's address of the table's field at offset k, as the code builds it: the table
   is s0 (atom 8) and the shadow base is s5, seated as atom 32. *)
Definition SHX (k : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 k) (SLit 3)) (SOff 32 0).

(* EMR, 0x863e0: the instruction after the call. *)
Definition EMR : Z := AF_reac_headamp_tx_next + 0x4e4.

(* Before the call: the two bytes the caller holds that the block writes first, keyed to a1 and
   a2 (atoms 11 and 12). Only the shadow base is re-seated (s5 = x21 as atom 32). *)
Definition em_sr1 : list sv := sr_set sr_atoms (21%bv : bv 5) (SOff 32 0).
Definition em_rs1 : list YP09.region := [OUTC; OUTP].
Definition em_facts1 : facts :=
  mkFacts [ (5%nat, mkAF 0 2 0); (8%nat, PTRN 4); (11%nat, OUTF); (12%nat, OUTF);
            (17%nat, mkAF 0 509 0); (32%nat, mkAF SB_NX SB_NX 0) ] [] [].
Definition ss1 : sstate := mkSS EMIT em_sr1 em_rs1 None em_facts1.
Definition SH1 : list shent := [ mkSHE 11 0 1; mkSHE 12 0 1 ].
Definition em_extra1 : list word := [Z_to_bv 64 SB_NX].

(* After the call. Atom 2 is the cut sp (the entry sp less 96); 33..44 are the twelve registers the
   prologue saved (ra, s0, s1, s2..s10), which the epilogue reads back; 45 the cursor the scan
   stored, 46 the replay width, 47 the wait. *)
Definition STKR : YP09.region := YP09.mkRegion (Some 2%nat) 0 96 0 0
  [ YP09.mkChunk 88 (CVal 8 (SOff 33 0)); YP09.mkChunk 80 (CVal 8 (SOff 34 0));
    YP09.mkChunk 72 (CVal 8 (SOff 35 0)); YP09.mkChunk 64 (CVal 8 (SOff 36 0));
    YP09.mkChunk 56 (CVal 8 (SOff 37 0)); YP09.mkChunk 48 (CVal 8 (SOff 38 0));
    YP09.mkChunk 40 (CVal 8 (SOff 39 0)); YP09.mkChunk 32 (CVal 8 (SOff 40 0));
    YP09.mkChunk 24 (CVal 8 (SOff 41 0)); YP09.mkChunk 16 (CVal 8 (SOff 42 0));
    YP09.mkChunk 8 (CVal 8 (SOff 43 0)); YP09.mkChunk 0 (CVal 8 (SOff 44 0)) ].
Definition T437 : YP09.region :=
  YP09.mkRegion (Some 8%nat) 437 438 437 438 [YP09.mkChunk 437 (CVal 1 (SOff 46 0))].
Definition T440 : YP09.region :=
  YP09.mkRegion (Some 8%nat) 440 444 440 440 [YP09.mkChunk 440 (CVal 4 (SOff 45 0))].
Definition T444 : YP09.region :=
  YP09.mkRegion (Some 8%nat) 444 448 444 448 [YP09.mkChunk 444 (CVal 4 (SOff 47 0))].
Definition T456 : YP09.region := YP09.mkRegion (Some 8%nat) 456 460 456 460 [].
Definition em_rs2 : list YP09.region := [STKR; T437; T440; T444; T456; OUTV8].

(* s2..s4 are the three field addresses, s6..s8 their shadow bytes' addresses; s10 is
   (tx + 440) mod 8 + 3, which is 3 because the table is 16-aligned. *)
Definition em_sr2 : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms
    (21%bv : bv 5) (SOff 32 0))
    (18%bv : bv 5) (SOff 8 437))
    (22%bv : bv 5) (SHX 437))
    (19%bv : bv 5) (SOff 8 444))
    (23%bv : bv 5) (SHX 444))
    (20%bv : bv 5) (SOff 8 440))
    (24%bv : bv 5) (SHX 440))
    (26%bv : bv 5) (SLit 3).
Definition em_facts2 : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46 - 96) (2 ^ 47 - 96) 4); (8%nat, PTRN 4); (9%nat, OUTF);
            (10%nat, mkAF 0 255 0); (25%nat, mkAF 0 765 0); (32%nat, mkAF SB_NX SB_NX 0);
            (45%nat, mkAF 1 765 0); (46%nat, mkAF 0 255 0); (47%nat, mkAF 0 4294967295 0) ] [] [].
Definition ss2 : sstate := mkSS EMR em_sr2 em_rs2 None em_facts2.
Definition SH2 : list shent := [ mkSHE 8 0 460; mkSHE 9 0 1 ].
Definition em_extra2 (regs : bvmap 5 word) (j : Z) (T1 : list byte) : list word :=
  [ Z_to_bv 64 SB_NX; getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19;
    getr regs 20; getr regs 21; getr regs 22; getr regs 23; getr regs 24; getr regs 25;
    getr regs 26; Z_to_bv 64 (j + 1); Z_to_bv 64 (tb T1 437); Z_to_bv 64 (u32at T1 444) ].

(* The bytes the runs after the call may write. *)
Definition em_wset (tx valp a : Z) : Prop :=
  (tx + 437 <= a < tx + 438) \/ (tx + 444 <= a < tx + 448) \/ (tx + 456 <= a < tx + 460) \/ a = valp.

Lemma em_wrange1 : forall (Ex : env) (chp parp a : Z),
  bv_unsigned (ew Ex 11) = chp -> bv_unsigned (ew Ex 12) = parp ->
  in_wrange Ex em_rs1 a -> a = chp \/ a = parp.
Proof.
  intros Ex chp parp a E11 E12 (r & Hin & Ha). unfold em_rs1 in Hin. cbn [In] in Hin.
  destruct Hin as [<- | [<- | []]]; unfold OUTC, OUTP in Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?E11, ?E12 in Ha; lia.
Qed.

Lemma em_wrange2 : forall (Ex : env) (rs : smem) (tx valp a : Z),
  skeleton rs = skeleton em_rs2 ->
  bv_unsigned (ew Ex 8) = tx -> bv_unsigned (ew Ex 9) = valp ->
  in_wrange Ex rs a -> em_wset tx valp a.
Proof.
  intros Ex rs tx valp a Hsk E8 E9 (r & Hin & Ha).
  assert (Hs : In (skel r) (skeleton em_rs2))
    by (rewrite <- Hsk; apply in_map; exact Hin).
  unfold em_rs2, STKR, T437, T440, T444, T456, OUTV8, skeleton in Hs.
  cbn [map skel YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi] in Hs.
  unfold em_wset.
  destruct Hs as [Hs|[Hs|[Hs|[Hs|[Hs|[Hs|Hs]]]]]];
    try (exfalso; exact Hs);
    symmetry in Hs; unfold skel in Hs;
    injection Hs as H1 H2 H3 H4 H5;
    rewrite ?H1, ?H2, ?H3, ?H4, ?H5 in Ha; cbn [base_val] in Ha.
  - lia.
  - rewrite E8 in Ha. lia.
  - lia.
  - rewrite E8 in Ha. lia.
  - rewrite E8 in Ha. lia.
  - rewrite E9 in Ha. lia.
Qed.

Lemma denot_off0 : forall (E : env) n, sv_denot E (SOff n 0) = ew E n.
Proof.
  intros E n. rewrite denot_lit_U, U_SOff, Z.add_0_r.
  rewrite zcanon_id by (apply u64_range). apply Z_to_bv_bv_unsigned.
Qed.

Lemma denot_lit : forall (Ex : env) z, 0 <= z < 2 ^ 64 -> sv_denot Ex (SLit z) = Z_to_bv 64 z.
Proof. intros Ex z Hz. rewrite denot_lit_U, U_SLit, zcanon_id by (unfold M64; lia). reflexivity. Qed.

Lemma denot_SHX : forall (E : env) (tx k : Z),
  ew E 8 = Z_to_bv 64 tx -> ew E 32 = Z_to_bv 64 SB_NX ->
  0 <= tx -> 0 <= k -> tx + k < 2 ^ 47 ->
  sv_denot E (SHX k) = Z_to_bv 64 (SHADOW_OFF + (tx + k) / 8).
Proof.
  intros E tx k H8 H32 Ht Hk Htk. rewrite denot_lit_U. f_equal. unfold SHX.
  rewrite (U_SAlu E ALU_ADD (SAlu ALU_SRL (SOff 8 k) (SLit 3)) (SOff 32 0)). cbn [zalu_raw].
  rewrite U_srl3, (U_atom_off E 8 tx k H8 ltac:(lia) ltac:(lia)).
  rewrite (U_atom E 32 SB_NX H32) by (unfold SB_NX; lia).
  assert (Hq : 0 <= (tx + k) / 8 < 2 ^ 44)
    by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite zcanon_id by (unfold M64, SB_NX; lia). unfold SB_NX, SHADOW_OFF. lia.
Qed.

Lemma em_val1 : forall segs m tx T k,
  (forall i, tx_fbyte i = true -> mbyte segs m (tx + i) = Some (nth (Z.to_nat i) T (Z_to_bv 8 0))) ->
  tx_fbyte k = true -> val_mem segs m (tx + k) 1 (tb T k).
Proof.
  intros segs m tx T k HB Hk j Hj. destruct j as [|j]; [|lia].
  pose proof (ATx.tb_range T k) as Hr.
  rewrite le_byte_small by (cbn; lia).
  change (Z.of_nat 0%nat) with 0. rewrite Z.mul_0_r, Z.shiftr_0_r, Z.add_0_r.
  rewrite Z_to_bv8_tb. exact (HB k Hk).
Qed.

Lemma em_val4 : forall segs m tx T k,
  (forall i, tx_fbyte i = true -> mbyte segs m (tx + i) = Some (nth (Z.to_nat i) T (Z_to_bv 8 0))) ->
  (forall d, 0 <= d < 4 -> tx_fbyte (k + d) = true) ->
  val_mem segs m (tx + k) 4 (u32at T k).
Proof.
  intros segs m tx T k HB Hk j Hj.
  pose proof (ATx.tb_range T k). pose proof (ATx.tb_range T (k + 1)).
  pose proof (ATx.tb_range T (k + 2)). pose proof (ATx.tb_range T (k + 3)).
  assert (Hu : 0 <= u32at T k < 2 ^ (8 * Z.of_nat 4)).
  { change (2 ^ (8 * Z.of_nat 4)) with 4294967296. unfold u32at. lia. }
  rewrite (le_byte_small (u32at T k) 4 j Hu Hj).
  replace (Z_to_bv 8 (Z.shiftr (u32at T k) (8 * Z.of_nat j)))
    with (Z_to_bv 8 (tb T (k + Z.of_nat j))).
  2:{ apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
      change (2 ^ Z.of_N 8) with 256. rewrite Z.shiftr_div_pow2 by lia.
      destruct j as [|[|[|[|j]]]]; try lia.
      - change (8 * Z.of_nat 0%nat) with 0. change (Z.of_nat 0%nat) with 0.
        rewrite Z.add_0_r, Z.pow_0_r, Z.div_1_r. unfold u32at. Z.div_mod_to_equations. lia.
      - change (8 * Z.of_nat 1%nat) with 8. change (Z.of_nat 1%nat) with 1.
        change (2 ^ 8) with 256. unfold u32at. Z.div_mod_to_equations. lia.
      - change (8 * Z.of_nat 2%nat) with 16. change (Z.of_nat 2%nat) with 2.
        change (2 ^ 16) with 65536. unfold u32at. Z.div_mod_to_equations. lia.
      - change (8 * Z.of_nat 3%nat) with 24. change (Z.of_nat 3%nat) with 3.
        change (2 ^ 24) with 16777216. unfold u32at. Z.div_mod_to_equations. lia. }
  rewrite Z_to_bv8_tb.
  replace (tx + k + Z.of_nat j) with (tx + (k + Z.of_nat j)) by lia.
  apply HB, Hk. lia.
Qed.

(* A register of a state the engine leaves, as a value. *)
Ltac em_reg HS r v pf H :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?vl ?Ex ?ss (restrict ?Hh ?ms) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    assert (H : getr (ms_regs ms) r = v)
      by (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ss ms r HS) _);
          change (sv_denot Ex e = v); pf)
  end.
Ltac em_regc HS r v pf H :=
  lazymatch type of HS with
  | st_ok ?segs ?Ex ?ss (restrict ?Hh ?ms) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    assert (H : getr (ms_regs ms) r = v)
      by (refine (eq_trans (st_ok_restrict_reg segs Hh Ex ss ms r HS) _);
          change (sv_denot Ex e = v); pf)
  end.
Ltac em_region HS i H :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?vl ?Ex ?ss (restrict ?Hh ?ms) =>
    let r := eval vm_compute in (nth_error (ss_mem ss) i) in
    lazymatch r with
    | Some ?rr =>
      pose proof (st_ok_pi_region_nth Ex ss (restrict Hh ms) i rr HS
                    ltac:(vm_compute; reflexivity)) as H;
      cbn [restrict ms_mem] in H
    end
  end.
Ltac em_regionc HS i H :=
  lazymatch type of HS with
  | st_ok ?segs ?Ex ?ss (restrict ?Hh ?ms) =>
    let r := eval vm_compute in (nth_error (ss_mem ss) i) in
    lazymatch r with
    | Some ?rr =>
      pose proof (st_ok_region_nth Ex ss (restrict Hh ms) i rr HS
                    ltac:(vm_compute; reflexivity)) as H;
      cbn [restrict ms_mem] in H
    end
  end.
Ltac em_env H :=
  cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact H.
Ltac em_pf H :=
  rewrite denot_off0; em_env H.
Ltac em_in := cbn [In]; repeat first [left; reflexivity | right].

Section D. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section F.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

Definition EM1 (regsj : bvmap 5 word) : env := Eimg (Ereg regsj em_extra1).
Definition EM2 (regs2 regs : bvmap 5 word) (j : Z) (T1 : list byte) : env :=
  Eimg (Ereg regs2 (em_extra2 regs j T1)).

Lemma em_aview_byte : forall (W : world SEGS) m a (v : Z), 0 <= v ->
  mbyte SEGS (mrestrict (w_H W) m) a = Some (YP09.byte_of_word (Z_to_bv 64 v) 0) ->
  aview SEGS (w_H W) m a = Some (v mod 256).
Proof.
  intros W m a v Hv HM. unfold aview. rewrite HM. cbn [option_map]. f_equal.
  unfold YP09.byte_of_word. change (8 * 0) with 0. rewrite Z.shiftr_0_r.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. change (2 ^ Z.of_N 64) with 18446744073709551616.
  replace (v mod 18446744073709551616)
    with (v + (- (v / 18446744073709551616) * 72057594037927936) * 256)
    by (pose proof (Z.div_mod v 18446744073709551616 ltac:(lia)); lia).
  apply Z_mod_plus_full.
Qed.

Lemma em_out : forall (Ex : env) (W : world SEGS) m (n : nat) (b : Z) cs
    (lo hi wlo whi : Z) (e : sv) (v : Z),
  region_ok SEGS Ex (mrestrict (w_H W) m) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew Ex n) = b -> In (YP09.mkChunk 0 (CVal 1 e)) cs ->
  sv_denot Ex e = Z_to_bv 64 v -> 0 <= v ->
  aview SEGS (w_H W) m b = Some (v mod 256).
Proof.
  intros Ex W m n b cs lo hi wlo whi e v HR Hb Hin He Hv.
  assert (Hm : mbyte SEGS (mrestrict (w_H W) m) (b + 0 + 0)
               = Some (YP09.byte_of_word (sv_denot Ex e) 0))
    by (apply (ATx.byte_of_region SEGS Ex _ n b cs lo hi wlo whi 0 1 e 0 HR Hb Hin); cbn; lia).
  rewrite He in Hm. replace (b + 0 + 0) with b in Hm by lia.
  apply em_aview_byte; [exact Hv | exact Hm].
Qed.

Lemma em_out_s : forall (Ex : env) (W : world SEGS) m (n : nat) (b : Z) cs
    (lo hi wlo whi : Z) (e : sv) (v : Z),
  region_ok SEGS Ex (mrestrict (w_H W) m) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew Ex n) = b -> In (YP09.mkChunk 0 (CVal 1 e)) cs ->
  sv_denot Ex e = Z_to_bv 64 v -> 0 <= v < 256 ->
  aview SEGS (w_H W) m b = Some v.
Proof.
  intros Ex W m n b cs lo hi wlo whi e v HR Hb Hin He Hv.
  rewrite (em_out Ex W m n b cs lo hi wlo whi e v HR Hb Hin He ltac:(lia)).
  f_equal. apply Z.mod_small. lia.
Qed.

Lemma em_obj_of_bytes : forall (W : world SEGS) m (tx : Z) (T' : list byte),
  (forall i, tx_fbyte i = true ->
     mbyte SEGS (mrestrict (w_H W) m) (tx + i) = Some (Z_to_bv 8 (tb T' i))) ->
  obj_at SEGS (mrestrict (w_H W) m) tx LAY_TX (tx_vals T').
Proof.
  intros W m tx T' H. apply (proj2 (ATx.tx_obj_bytes SEGS _ tx _)).
  intros i Hi. rewrite <- ATx.tb_nth. apply H. exact Hi.
Qed.

(* A chunk of the stack region: one of the twelve registers the prologue saved. *)
Lemma em_chunk8 : forall E m (base off : Z) (n : nat) (r : word),
  ew E n = r -> val_mem SEGS m (base + off) 8 (bv_unsigned r) ->
  YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal 8 (SOff n 0))).
Proof.
  intros E m base off n r Hn HV.
  apply (chunk_ok_val SEGS E m base off 8 (SOff n 0) (bv_unsigned r)).
  - cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - pose proof (bv_unsigned_in_range 64 r) as Hr.
    change (bv_modulus 64) with 18446744073709551616 in Hr. cbn. lia.
  - cbn. lia.
  - exact HV.
Qed.

(* The twelve saved registers, carried over a memory that agrees on the frame. *)
Lemma em_saved_keep : forall (W : world SEGS) m m' regs sp,
  (forall a, sp - 96 <= a < sp -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  nx_saved W m regs sp -> nx_saved W m' regs sp.
Proof.
  intros W m m' regs sp HK (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12).
  unfold nx_saved.
  repeat split;
    (eapply (val_mem_kept SEGS); [intros d Hd; apply HK; cbn in Hd; lia | eassumption]).
Qed.

Lemma em_grows_pres : forall (W : world SEGS) m1 m2 a,
  mem_grows (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  apresent (w_H W) m1 a -> apresent (w_H W) m2 a.
Proof. intros W m1 m2 a HG Hp. exact (apresent_grows (w_H W) m1 m2 a HG Hp). Qed.

(* A byte's shadow byte lies in no range this call writes, so the caller's "marked usable"
   still holds at the walk's memory. *)
Lemma em_ra_keep : forall (W : world SEGS) memc m (sp tx chp parp valp p : Z),
  nx_same W memc m sp tx chp parp valp (tx + 432) ->
  2 ^ 46 <= sp -> 4096 <= tx -> in_app tx 460 ->
  4096 <= p -> p + 1 <= 2 ^ 47 ->
  ~ (SHADOW_OFF <= chp < SHADOW_OFF + 2 ^ 44) ->
  ~ (SHADOW_OFF <= parp < SHADOW_OFF + 2 ^ 44) ->
  ~ (SHADOW_OFF <= valp < SHADOW_OFF + 2 ^ 44) ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF p 1 ->
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF p 1.
Proof.
  intros W memc m sp tx chp parp valp p HS Hsp Htx Hia Hp0 Hp1 Hc5 Hp5 Hv5 HRA.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct Hia as (Hia0 & Hia1).
  assert (Hq : 0 <= p / 8 < 2 ^ 44)
    by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  intros x Hx. assert (x = p) as -> by lia.
  destruct (HRA p ltac:(lia)) as (s & Hs & Hok). exists s. split; [|exact Hok].
  rewrite <- Hs. unfold shadow_of_addr.
  apply (nx_same_aview W memc m sp tx chp parp valp (tx + 432) (SHADOW_OFF + p / 8));
    [exact HS | unfold SHADOW_OFF in *; lia | unfold ATx.TX_SIZE; lia
     | rewrite nx_stk_val; unfold SHADOW_OFF in *; lia |].
  unfold nx_touch, ATx.TX_SIZE, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
  intros [Hz | [Hz | [Hz | Hz]]]; lia.
Qed.

(* ---- what the runs after the call keep -------------------------------------------------- *)

(* Every byte outside the table's three written fields and the value byte is as the call left
   it, and nothing present became absent. *)
Definition em_inv2 (W : world SEGS) (m2 m : word -> option byte) (tx valp : Z) : Prop :=
  (forall x : word, ~ em_wset tx valp (bv_unsigned x) -> mrestrict (w_H W) m x = mrestrict (w_H W) m2 x) /\
  (forall a, apresent (w_H W) m2 a -> apresent (w_H W) m a).

Lemma em_inv2_refl : forall W m2 tx valp, em_inv2 W m2 m2 tx valp.
Proof. intros. split; [intros; reflexivity | intros a Ha; exact Ha]. Qed.

Lemma em_inv2_step : forall (Ex : env) (rs : smem) (W : world SEGS) m2 m1 m (tx valp : Z),
  skeleton rs = skeleton em_rs2 ->
  bv_unsigned (ew Ex 8) = tx -> bv_unsigned (ew Ex 9) = valp ->
  frame_of Ex rs (mrestrict (w_H W) m1) (mrestrict (w_H W) m) ->
  mem_grows (mrestrict (w_H W) m1) (mrestrict (w_H W) m) ->
  em_inv2 W m2 m1 tx valp -> em_inv2 W m2 m tx valp.
Proof.
  intros Ex rs W m2 m1 m tx valp Hsk E8 E9 HF HG (HK & HP). split.
  - intros x Hx. rewrite (HF x); [exact (HK x Hx)|].
    intros Hw. exact (Hx (em_wrange2 Ex rs tx valp _ Hsk E8 E9 Hw)).
  - intros a Ha. exact (em_grows_pres W m1 m a HG (HP a Ha)).
Qed.

Lemma em_inv2_aview : forall W m2 m tx valp a,
  em_inv2 W m2 m tx valp -> 0 <= a < 2 ^ 64 -> ~ em_wset tx valp a ->
  aview SEGS (w_H W) m a = aview SEGS (w_H W) m2 a.
Proof.
  intros W m2 m tx valp a (HK & _) Ha Hn. apply (aview_eq_of SEGS). apply HK.
  rewrite unsigned_lit_small by lia. exact Hn.
Qed.

Lemma em_inv2_same : forall W m2 m (sp tx chp parp valp : Z),
  em_inv2 W m2 m tx valp -> nx_same W m2 m sp tx chp parp valp (tx + 432).
Proof.
  intros W m2 m sp tx chp parp valp (HK & _) x Hst Htc. apply HK.
  intros Hw. apply Htc. unfold em_wset in Hw. unfold nx_touch2. lia.
Qed.

(* The table's bytes the runs after the call do not write. *)
Lemma em_inv2_bytes : forall W m2 m (tx valp : Z) (T1 : list byte),
  em_inv2 W m2 m tx valp -> 0 <= tx -> tx + 460 < 2 ^ 64 -> ~ (tx <= valp < tx + 460) ->
  obj_at SEGS (mrestrict (w_H W) m2) tx LAY_TX (tx_vals T1) ->
  forall i, tx_fbyte i = true -> i <> 437 -> ~ (444 <= i < 448) -> ~ (456 <= i < 460) ->
  mbyte SEGS (mrestrict (w_H W) m) (tx + i) = Some (nth (Z.to_nat i) T1 (Z_to_bv 8 0)).
Proof.
  intros W m2 m tx valp T1 (HK & _) Htx0 Htx1 Hv HO i Hi H437 H444 H456.
  pose proof (ATx.tx_fbyte_range i Hi) as Hir.
  rewrite <- (proj1 (ATx.tx_obj_bytes SEGS _ _ _) HO i Hi).
  unfold mbyte. rewrite (HK (Z_to_bv 64 (tx + i))); [reflexivity|].
  rewrite unsigned_lit_small by lia. unfold em_wset. lia.
Qed.

(* The table when the block cleared the replay width (the cursor reached the end). *)
Lemma em_obj_w : forall (Ex : env) (W : world SEGS) m (tx : Z) (T1 : list byte) cs437 cs444 cs456,
  length T1 = 460%nat ->
  (forall i, tx_fbyte i = true -> i <> 437 -> ~ (444 <= i < 448) -> ~ (456 <= i < 460) ->
     mbyte SEGS (mrestrict (w_H W) m) (tx + i) = Some (nth (Z.to_nat i) T1 (Z_to_bv 8 0))) ->
  bv_unsigned (ew Ex 8) = tx ->
  region_ok SEGS Ex (mrestrict (w_H W) m) (YP09.mkRegion (Some 8%nat) 437 438 437 438 cs437) ->
  In (YP09.mkChunk 437 (CVal 1 (SLit 0))) cs437 ->
  region_ok SEGS Ex (mrestrict (w_H W) m) (YP09.mkRegion (Some 8%nat) 444 448 444 448 cs444) ->
  In (YP09.mkChunk 444 (CVal 4 (SOff 47 0))) cs444 ->
  ew Ex 47 = Z_to_bv 64 (u32at T1 444) ->
  region_ok SEGS Ex (mrestrict (w_H W) m) (YP09.mkRegion (Some 8%nat) 456 460 456 460 cs456) ->
  In (YP09.mkChunk 456 (CVal 4 (SLit 0))) cs456 ->
  obj_at SEGS (mrestrict (w_H W) m) tx LAY_TX (tx_vals (set4 (setb T1 437 0) 456 0)).
Proof.
  intros Ex W m tx T1 cs437 cs444 cs456 HL HK E8 HR437 I437 HR444 I444 E47 HR456 I456.
  assert (HLb : length (setb T1 437 0) = 460%nat) by (apply len_setb; lia).
  apply em_obj_of_bytes. intros i Hi. pose proof (ATx.tx_fbyte_range i Hi) as Hir.
  destruct (Z.eq_dec i 437) as [-> | Hne].
  { replace (tx + 437) with (tx + 437 + 0) by lia.
    rewrite (ATx.byte_of_region SEGS Ex _ 8%nat tx cs437 437 438 437 438 437 1
               (SLit 0) 0 HR437 E8 I437 ltac:(cbn; lia)).
    rewrite (denot_lit Ex 0 ltac:(lia)), (em_bow1 0 ltac:(lia)). f_equal. f_equal.
    rewrite (tb_set4_out (setb T1 437 0) 456 0 437 HLb ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    symmetry. apply tb_setb_in; lia. }
  destruct (Z_le_gt_dec 444 i) as [Hge | Hlt]; [destruct (Z_lt_ge_dec i 448) as [Hlt4 | Hge4] |].
  { replace (tx + i) with (tx + 444 + (i - 444)) by lia.
    rewrite (ATx.byte_of_region SEGS Ex _ 8%nat tx cs444 444 448 444 448 444 4
               (SOff 47 0) (i - 444) HR444 E8 I444 ltac:(cbn; lia)).
    rewrite denot_off0, E47, (em_bow_u32 T1 444 (i - 444) ltac:(lia)). f_equal. f_equal.
    rewrite (tb_set4_out (setb T1 437 0) 456 0 i HLb ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    rewrite (tb_setb_out T1 437 0 i HL ltac:(lia) ltac:(lia) ltac:(lia)). f_equal. lia. }
  { destruct (Z_le_gt_dec 456 i) as [Hge5 | Hlt5].
    - replace (tx + i) with (tx + 456 + (i - 456)) by lia.
      rewrite (ATx.byte_of_region SEGS Ex _ 8%nat tx cs456 456 460 456 460 456 4
                 (SLit 0) (i - 456) HR456 E8 I456 ltac:(cbn; lia)).
      rewrite (denot_lit Ex 0 ltac:(lia)), em_bow0. f_equal. f_equal.
      replace i with (456 + (i - 456)) by lia.
      rewrite (tb_set4_in (setb T1 437 0) 456 0 (i - 456) HLb ltac:(lia) ltac:(lia) ltac:(lia)
                 ltac:(lia)).
      assert (i - 456 = 0 \/ i - 456 = 1 \/ i - 456 = 2 \/ i - 456 = 3)
        as [Hd | [Hd | [Hd | Hd]]] by lia; rewrite Hd; vm_compute; reflexivity.
    - rewrite (HK i Hi Hne ltac:(lia) ltac:(lia)). rewrite <- ATx.tb_nth. f_equal. f_equal.
      rewrite (tb_set4_out (setb T1 437 0) 456 0 i HLb ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
      symmetry. apply tb_setb_out; lia. }
  { destruct (Z_le_gt_dec 456 i) as [Hge5 | Hlt5]; [lia|].
    rewrite (HK i Hi Hne ltac:(lia) ltac:(lia)). rewrite <- ATx.tb_nth. f_equal. f_equal.
    rewrite (tb_set4_out (setb T1 437 0) 456 0 i HLb ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    symmetry. apply tb_setb_out; lia. }
Qed.

(* The table when the block set the cursor's wait instead. *)
Lemma em_obj_wait : forall (Ex : env) (W : world SEGS) m (tx : Z) (T1 : list byte) cs437 cs444 cs456,
  length T1 = 460%nat ->
  (forall i, tx_fbyte i = true -> i <> 437 -> ~ (444 <= i < 448) -> ~ (456 <= i < 460) ->
     mbyte SEGS (mrestrict (w_H W) m) (tx + i) = Some (nth (Z.to_nat i) T1 (Z_to_bv 8 0))) ->
  bv_unsigned (ew Ex 8) = tx ->
  region_ok SEGS Ex (mrestrict (w_H W) m) (YP09.mkRegion (Some 8%nat) 437 438 437 438 cs437) ->
  In (YP09.mkChunk 437 (CVal 1 (SOff 46 0))) cs437 ->
  ew Ex 46 = Z_to_bv 64 (tb T1 437) ->
  region_ok SEGS Ex (mrestrict (w_H W) m) (YP09.mkRegion (Some 8%nat) 444 448 444 448 cs444) ->
  In (YP09.mkChunk 444 (CVal 4 (SLit 11))) cs444 ->
  region_ok SEGS Ex (mrestrict (w_H W) m) (YP09.mkRegion (Some 8%nat) 456 460 456 460 cs456) ->
  In (YP09.mkChunk 456 (CVal 4 (SLit 0))) cs456 ->
  obj_at SEGS (mrestrict (w_H W) m) tx LAY_TX (tx_vals (set4 (set4 T1 444 11) 456 0)).
Proof.
  intros Ex W m tx T1 cs437 cs444 cs456 HL HK E8 HR437 I437 E46 HR444 I444 HR456 I456.
  assert (HLb : length (set4 T1 444 11) = 460%nat) by (apply len_set4; lia).
  pose proof (ATx.tb_range T1 437) as R437.
  apply em_obj_of_bytes. intros i Hi. pose proof (ATx.tx_fbyte_range i Hi) as Hir.
  destruct (Z.eq_dec i 437) as [-> | Hne].
  { replace (tx + 437) with (tx + 437 + 0) by lia.
    rewrite (ATx.byte_of_region SEGS Ex _ 8%nat tx cs437 437 438 437 438 437 1
               (SOff 46 0) 0 HR437 E8 I437 ltac:(cbn; lia)).
    rewrite denot_off0, E46, (em_bow1 (tb T1 437) ltac:(lia)). f_equal. f_equal.
    rewrite (tb_set4_out (set4 T1 444 11) 456 0 437 HLb ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    symmetry. apply tb_set4_out; lia. }
  destruct (Z_le_gt_dec 444 i) as [Hge | Hlt]; [destruct (Z_lt_ge_dec i 448) as [Hlt4 | Hge4] |].
  { replace (tx + i) with (tx + 444 + (i - 444)) by lia.
    rewrite (ATx.byte_of_region SEGS Ex _ 8%nat tx cs444 444 448 444 448 444 4
               (SLit 11) (i - 444) HR444 E8 I444 ltac:(cbn; lia)).
    rewrite (denot_lit Ex 11 ltac:(lia)), (em_bow11 (i - 444) ltac:(lia)). f_equal. f_equal.
    rewrite (tb_set4_out (set4 T1 444 11) 456 0 i HLb ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    replace i with (444 + (i - 444)) by lia.
    rewrite (tb_set4_in T1 444 11 (i - 444) HL ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    assert (i - 444 = 0 \/ i - 444 = 1 \/ i - 444 = 2 \/ i - 444 = 3)
      as [Hd | [Hd | [Hd | Hd]]] by lia; rewrite Hd; vm_compute; reflexivity. }
  { destruct (Z_le_gt_dec 456 i) as [Hge5 | Hlt5].
    - replace (tx + i) with (tx + 456 + (i - 456)) by lia.
      rewrite (ATx.byte_of_region SEGS Ex _ 8%nat tx cs456 456 460 456 460 456 4
                 (SLit 0) (i - 456) HR456 E8 I456 ltac:(cbn; lia)).
      rewrite (denot_lit Ex 0 ltac:(lia)), em_bow0. f_equal. f_equal.
      replace i with (456 + (i - 456)) by lia.
      rewrite (tb_set4_in (set4 T1 444 11) 456 0 (i - 456) HLb ltac:(lia) ltac:(lia) ltac:(lia)
                 ltac:(lia)).
      assert (i - 456 = 0 \/ i - 456 = 1 \/ i - 456 = 2 \/ i - 456 = 3)
        as [Hd | [Hd | [Hd | Hd]]] by lia; rewrite Hd; vm_compute; reflexivity.
    - rewrite (HK i Hi Hne ltac:(lia) ltac:(lia)). rewrite <- ATx.tb_nth. f_equal. f_equal.
      rewrite (tb_set4_out (set4 T1 444 11) 456 0 i HLb ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
      symmetry. apply tb_set4_out; lia. }
  { destruct (Z_le_gt_dec 456 i) as [Hge5 | Hlt5]; [lia|].
    rewrite (HK i Hi Hne ltac:(lia) ltac:(lia)). rewrite <- ATx.tb_nth. f_equal. f_equal.
    rewrite (tb_set4_out (set4 T1 444 11) 456 0 i HLb ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    symmetry. apply tb_set4_out; lia. }
Qed.

Lemma em_mod8 : forall tx, tx mod 16 = 0 -> (tx + 440) mod 8 = 0.
Proof.
  intros tx H. apply Z.mod_divide in H as [q Hq]; [|lia]. rewrite Hq.
  replace (q * 16 + 440) with ((2 * q + 55) * 8) by lia. apply Z.mod_mul. lia.
Qed.

Section H.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_grant) (PI := PI).

#[local] Notation tnext_post := (tb_reac_headamp_tx_next_post B).

(* ---- the call: what its journal keeps of the bytes the caller holds ----------------------- *)

(* A byte the caller may write, outside the callee's window, reads after the call as before. *)
Lemma em_out_keep : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memX mdX k
    STK1 sp1 mem2 md2 a,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memX mdX k ->
  ajournal SEGS B STK1 sp1 [] lyc Sc W memX mdX [] lyc Sc W mem2 md2 0 ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a ->
  ~ (sp1 - STK1 <= a < sp1) ->
  aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memX a.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memX mdX k STK1 sp1 mem2 md2 a HJ HJc Hw Hout.
  pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ &
    (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
  pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & _ & G4 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (awr_byte_cases SEGS B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memX mdX k a HJ Hw)
    as (_ & [(Hc & Hs) | [(Happ & b & n & Hin & Hr & _) | (cid & pos & Hin & Hr)]]).
  - apply G1; [lia | exact Hout].
  - replace a with (b + (a - b)) by lia.
    apply (G2 b n (a - b) Hin Hin); [lia|]. apply inFP_nil.
  - apply (G4 cid pos a).
    + rewrite Hfrs. apply in_or_app. left. exact Hin.
    + destruct Hr as [(_ & Hr) | (_ & Hr)]; [left | right]; exact Hr.
    + apply inFP_nil.
Qed.

(* A byte the caller may write, not in the shadow map, stays marked usable across the call. *)
Lemma em_out_ra : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memX mdX k
    STK1 sp1 mem2 md2 a,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memX mdX k ->
  ajournal SEGS B STK1 sp1 [] lyc Sc W memX mdX [] lyc Sc W mem2 md2 0 ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a ->
  ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44) ->
  range_addressable (aview SEGS (w_H W) memX) SHADOW_OFF a 1 ->
  range_addressable (aview SEGS (w_H W) mem2) SHADOW_OFF a 1.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memX mdX k STK1 sp1 mem2 md2 a HJ HJc Hw Hsh Hra.
  pose proof HJ as (HARX & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ &
    (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
  pose proof (proj1 HJc) as HAR2.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (awr_byte_cases SEGS B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memX mdX k a HJ Hw)
    as (_ & [(Hc & Hs) | [(Happ & b & n & Hin & Hr & _) | (cid & pos & Hin & Hr)]]).
  - (* the caller's machine stack: its shadow is zero *)
    destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
    pose proof HAR2 as (M & _).
    pose proof (lo_top _ (am_layout _ _ _ _ M)) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
    unfold page_aligned in T5, T6.
    pose proof (al_zshadow _ _ LAWS lyc Sc W mem2 md2 (ly_stk_lo lyc, ly_stk_hi lyc - ly_stk_lo lyc) HAR2
                  (or_introl eq_refl)) as Hz.
    cbn [fst snd] in Hz.
    intros x Hx. assert (x = a) as -> by lia. exists 0. split; [|left; reflexivity].
    pose proof (em_div8 (ly_stk_lo lyc) (ly_stk_hi lyc) a T5 T6 ltac:(rewrite Elo, Ehi; lia)) as Hi.
    pose proof (Hz (a / 8 - ly_stk_lo lyc / 8) Hi) as Hz1.
    unfold shadow_of_addr in *. replace (SHADOW_OFF + a / 8)
      with (SHADOW_OFF + ly_stk_lo lyc / 8 + (a / 8 - ly_stk_lo lyc / 8)) by lia.
    exact Hz1.
  - (* a block of the caller *)
    exact (range_addressable_of_block SEGS B LAWS lyc Sc W mem2 md2 b n a 1 HAR2 Hin ltac:(lia) ltac:(lia)).
  - (* a frame the caller owns *)
    assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hin).
    destruct Hr as [(Happ & Hr) | (Hr & _)]; [|unfold SHADOW_OFF in Hsh; lia].
    pose proof HARX as (MX & _).
    destruct (frame_facts B lyc Sc _ cid pos MX Hin') as (Fc & _).
    destruct (al_frames _ _ LAWS lyc Sc W memX mdX cid pos HARX Hin') as (F32 & _).
    unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr.
    apply (range_addressable_entry_frame SEGS B LAWS STK1 sp1 [] lyc Sc W memX mdX [] lyc Sc W mem2 md2 0
             cid pos a 1 HJc Hin' ltac:(lia) ltac:(lia) ltac:(lia)).
    + apply Z.mod_divide in F32 as [q Hq]; [|lia]. rewrite Hq.
      replace (q * 32) with ((4 * q) * 8) by lia. apply Z.mod_mul. lia.
    + intros x Hx. destruct (inFP_nil x Hx).
    + exact HARX.
    + exact Hra.
Qed.

(* ---- the end of the walk ------------------------------------------------------------------ *)

(* The contract's post, from the three memories the walk passes through: the call's entry memory
   memX (the walk before the call changed only the three bytes and its window), the call's exit
   memory mem2 (the call's kept classes), and the final memory mem3 (the walk after the call
   changed only the table's fields and the value byte). This re-derives the six clauses of
   tcj_kept that nx_finish derives from one nx_same, which a call cannot give. *)
Lemma em_finish : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
    (regs regs3 : bvmap 5 word) memX mem2 mem3 md3 (tx chp parp valp : Z) (T T' : list byte)
    (c p v slo shi : Z),
  AR SEGS B lyc Sc W memc mdc ->
  In (tx, TX_SIZE) (ablocks B lyc Sc) ->
  thd_out_ok (spZ regs) tx chp -> thd_out_ok (spZ regs) tx parp -> thd_out_ok (spZ regs) tx valp ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> alloc_ceiling <= spZ regs - NX_STK ->
  sp0 - STK <= spZ regs - NX_STK -> spZ regs <= sp0 ->
  next_model T tx = (1, (c, p, v), T') ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem3 md3 k ->
  aregs_preserved regs regs3 ->
  nx_same W memc memX (spZ regs) tx chp parp valp (tx + 432) ->
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) memX a) ->
  acall_kept SEGS B lyc Sc W memX W mem2 slo shi (fun _ => False) ->
  spZ regs - NX_STK <= slo -> shi <= spZ regs ->
  nx_same W mem2 mem3 (spZ regs) tx chp parp valp (tx + 432) ->
  (forall a, apresent (w_H W) mem2 a -> apresent (w_H W) mem3 a) ->
  getr regs3 10 = w64 1 ->
  obj_at SEGS (mrestrict (w_H W) mem3) tx LAY_TX (tx_vals T') ->
  thd_replay_ok T' ->
  aview SEGS (w_H W) mem3 chp = Some c ->
  aview SEGS (w_H W) mem3 parp = Some p ->
  aview SEGS (w_H W) mem3 valp = Some v ->
  tnext_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs tx chp parp valp T
    W (mkCfg (mkst regs3 (getr regs 1) mem3 (seg_rom SEGS)) md3).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regs3 memX mem2 mem3 md3
    tx chp parp valp T T' c p v slo shi HAR Hg Hoc Hop Hov Hspr Hac Hslo Hshi HMOD HJ3 HP
    HS1 HP1 HK Hlo Hhi HS2 HP2 H10 Hobj Hrok Hc Hp Hv.
  destruct Hoc as (Hc0 & Hc1 & Hc2 & Hc3 & Hc4 & Hc5).
  destruct Hop as (Hp0 & Hp1 & Hp2 & Hp3 & Hp4 & Hp5).
  destruct Hov as (Hv0 & Hv1 & Hv2 & Hv3 & Hv4 & Hv5).
  destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
  pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPJ & _).
  pose proof (blk_off_imgB B lyc Sc W memc mdc tx TX_SIZE HAR Hg) as Hgimg.
  change (req_size TX_SIZE) with 460 in Hgimg.
  rewrite IMG_LO_B_val, IMG_TOP_B_val in Hgimg.
  unfold ATx.TX_SIZE in Hc2, Hp2, Hv2.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  unfold NX_STK in *.
  assert (Hd : tx <= tx + 432 < tx + TX_SIZE) by (unfold ATx.TX_SIZE; lia).
  (* the chain of the three memories, for a byte the walk does not touch *)
  assert (CH : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK_reac_headamp_tx_next <= a < spZ regs) ->
            ~ nx_touch tx chp parp valp a ->
            aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memX a ->
            aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) memc a).
  { intros a Ha Hst Htc Hm.
    rewrite (nx_same_aview W mem2 mem3 (spZ regs) tx chp parp valp (tx + 432) a HS2 Ha Hd Hst Htc), Hm.
    exact (nx_same_aview W memc memX (spZ regs) tx chp parp valp (tx + 432) a HS1 Ha Hd Hst Htc). }
  unfold tb_reac_headamp_tx_next_post. split; [reflexivity|].
  exists regs3, mem3, md3.
  split; [reflexivity|]. split; [exact HJ3|]. split; [exact HP|].
  split.
  { unfold tcj_kept. split; [|split; [|split; [|split; [|split]]]].
    - intros a Ha Hst Htc. apply CH; [lia | exact Hst | exact Htc |].
      apply K1; [exact Ha | lia].
    - intros b m i Hb Hi Htc.
      destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & Hb4096 & Hbceil & _ & _ & _).
      apply CH; [lia | lia | exact Htc |].
      exact (K2 b m i Hb Hi (fun f => f)).
    - intros a Hi Ho He.
      pose proof (pa_img_range a Hi) as Hir. rewrite IMG_LO_B_val, IMG_TOP_B_val in Hir.
      apply CH; [lia | lia | |].
      + unfold nx_touch, ATx.TX_SIZE.
        intros [Hx | [Hx | [Hx | Hx]]]; [lia | | |];
          subst a; [exact (Hc4 Hi) | exact (Hp4 Hi) | exact (Hv4 Hi)].
      + exact (K3 a Hi Ho He).
    - intros cid pos a Hf Hzr Htc.
      destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hf) as (Hf0 & Hfc & Hfa).
      pose proof (fs_frame_bytes_nonneg cid) as Hfb.
      pose proof (Z.div_mod (frame_addr lyc cid pos) 8 ltac:(lia)) as D1.
      pose proof (Z.mod_pos_bound (frame_addr lyc cid pos) 8 ltac:(lia)) as M1.
      pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia)) as D2.
      pose proof (Z.mod_pos_bound (fs_frame_bytes cid) 8 ltac:(lia)) as M2.
      apply CH; [| | exact Htc | exact (K4 cid pos a Hf Hzr (fun f => f))].
      + destruct Hzr as [Hzr | Hzr]; unfold in_zr, frame_rng, shadow_addr, SHADOW_OFF in Hzr;
          cbn [fst snd] in Hzr; lia.
      + destruct Hzr as [Hzr | Hzr]; unfold in_zr, frame_rng, shadow_addr, SHADOW_OFF in Hzr;
          cbn [fst snd] in Hzr; lia.
    - intros a Ha Hst Hpr. apply HP2. apply (K5 a Ha ltac:(lia)). apply HP1. exact Hpr.
    - intros a Ha. apply HPJ. lia. }
  rewrite HMOD.
  split; [exact H10|]. split; [exact Hobj|]. split; [exact Hrok|].
  split; [intros _; split; [exact Hc | split; [exact Hp | exact Hv]]|].
  intros H0. discriminate H0.
Qed.

(* ---- the seat at EMIT ---------------------------------------------------------------------- *)

Lemma em_entry1 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
    (regs regsj : bvmap 5 word) memj mdj (tx chp parp valp : Z) (T : list byte) (c p : Z) (q : bool),
  nx_ctx B STK sp0 FP ly S lyc Sc own W memc mdc regs tx chp parp valp T ->
  nx_mid B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs memj mdj tx chp parp valp (tx + 432) q ->
  nx_at_emit regs regsj tx chp parp valp T c p ->
  0 <= c <= 509 -> 0 <= p < 3 ->
  st_ok_pi SEGS VAL (EM1 regsj) ss1
    (restrict (w_H W) (mkst regsj (Z_to_bv 64 (BASE + EMIT)) memj (seg_rom SEGS)))
  /\ sh_ok SEGS BxN SH1 (EM1 regsj) (mrestrict (w_H W) memj).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsj memj mdj
    tx chp parp valp T c p q HCTX HMID HAT Hcr Hpr.
  pose proof HCTX as (HAR & Hg & Hoc & Hop & Hov & Dcp & Dcv & Dpv & Pc & Pp & Pv & Bc & Bp & Bv & B456 &
    Hspr & Hceil & Hsp16 & Hslo & Hshi & Hwtab & Hwc & Hwp & Hwv & Hret & Hra4 & Hgp & Htp &
    Q10 & Q11 & Q12 & Q13 & HTL0 & HI & Hobjc & Hpresc).
  pose proof HMID as (HJ & HSAME & HpresS & HpresK & _).
  pose proof HAT as (HKG & A2 & A8 & A9 & A11 & A12 & A21 & A18 & A22 & A19 & A23 & A20 & A24 &
    A25 & A26 & A17 & A5).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (proj1 HJ) as HARj.
  destruct (al_blocks _ _ LAWS lyc Sc W memj mdj tx TX_SIZE HARj Hg)
    as (Hg16 & Hg4096 & Hgceil & Hgia & _).
  change (req_size TX_SIZE) with 460 in Hgceil, Hgia.
  destruct Hoc as (Hc0 & Hc1 & Hc2 & Hc3 & Hc4 & Hc5).
  destruct Hop as (Hp0 & Hp1 & Hp2 & Hp3 & Hp4 & Hp5).
  destruct Hov as (Hv0 & Hv1 & Hv2 & Hv3 & Hv4 & Hv5).
  destruct Hspr as (Hsp46 & Hsp47).
  set (E := EM1 regsj).
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regsj em_extra1) n)
    by (intros n Hn; unfold E, EM1; apply Eimg_low; exact Hn).
  assert (E5 : ew E 5 = w64 p)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 5 5%bv eq_refl); exact A5).
  assert (E8 : ew E 8 = w64 tx)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 8 8%bv eq_refl); exact A8).
  assert (E11 : ew E 11 = w64 chp)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 11 11%bv eq_refl); exact A11).
  assert (E12 : ew E 12 = w64 parp)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 12 12%bv eq_refl); exact A12).
  assert (E17 : ew E 17 = w64 c)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 17 17%bv eq_refl); exact A17).
  assert (E32 : ew E 32 = w64 SB_NX)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsj _ 0)).
  assert (U5 : bv_unsigned (ew E 5) = p) by (rewrite E5; apply unsigned_lit_small; lia).
  assert (U8 : bv_unsigned (ew E 8) = tx) by (rewrite E8; apply unsigned_lit_small; lia).
  assert (U11 : bv_unsigned (ew E 11) = chp) by (rewrite E11; apply unsigned_lit_small; lia).
  assert (U12 : bv_unsigned (ew E 12) = parp) by (rewrite E12; apply unsigned_lit_small; lia).
  assert (U17 : bv_unsigned (ew E 17) = c) by (rewrite E17; apply unsigned_lit_small; lia).
  assert (U32 : bv_unsigned (ew E 32) = SB_NX)
    by (rewrite E32; apply unsigned_lit_small; unfold SB_NX; lia).
  assert (HUB : U E BxN = SHADOW_OFF)
    by (unfold U, BxN; cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned;
        rewrite unsigned_lit_small by (unfold SB_NX; lia); reflexivity).
  split.
  - rewrite restrict_mkst_fx. unfold ss1. apply pa_entry_st_ok_full.
    + unfold em_sr1.
      apply regs_ok_pin; [| intros X; discriminate X |].
      2:{ rewrite A21. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
      unfold E, EM1. apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + unfold em_rs1, OUTC, OUTP.
      repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      * rewrite U11. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. replace (chp + o) with chp by lia.
        apply (apresent_writable SEGS). apply HpresK. exact Pc.
      * rewrite U12. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. replace (parp + o) with parp by lia.
        apply (apresent_writable SEGS). apply HpresK. exact Pp.
    + apply pairwise_disjoint_of_extents.
      unfold em_rs1, OUTC, OUTP, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      cbn [base_val]. rewrite U11, U12.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      repeat split; lia.
    + split; [| split; [exact I | exact I]].
      cbn [em_facts1 f_atoms atoms_ok]. unfold afact_ok, PTRN, OUTF.
      cbn [af_lo af_hi af_al2].
      rewrite U5, U8, U11, U12, U17, U32.
      change (2 ^ 4) with 16. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
      unfold SB_NX in *.
      repeat match goal with |- _ /\ _ => split end; lia.
  - unfold sh_ok, SH1. constructor; [|constructor; [|constructor]].
    + apply (shent_ok_of_range SEGS (w_H W) memj E BxN 11 chp 1 chp 0 1).
      * exact (em_ra_keep W memc memj (spZ regs) tx chp parp valp chp HSAME
                 ltac:(lia) ltac:(lia) Hgia ltac:(lia) ltac:(lia) Hc5 Hp5 Hv5 Bc).
      * exact HUB.
      * unfold U. cbn [sv_denot]. rewrite U11, Z.add_0_r. apply unsigned_lit_small. lia.
      * lia.
      * lia.
      * cbn [Z.min Z.max]. intros x Hx. replace x with chp by lia. exact Hc5.
    + apply (shent_ok_of_range SEGS (w_H W) memj E BxN 12 parp 1 parp 0 1).
      * exact (em_ra_keep W memc memj (spZ regs) tx chp parp valp parp HSAME
                 ltac:(lia) ltac:(lia) Hgia ltac:(lia) ltac:(lia) Hc5 Hp5 Hv5 Bp).
      * exact HUB.
      * unfold U. cbn [sv_denot]. rewrite U12, Z.add_0_r. apply unsigned_lit_small. lia.
      * lia.
      * lia.
      * cbn [Z.min Z.max]. intros x Hx. replace x with parp by lia. exact Hp5.
Qed.

(* ---- the seat at EMR, after the call -------------------------------------------------------- *)

Lemma em_awr2 : forall (Ex : env) (rs : smem) STK sp0 FP ly S lyc Sc own (tx valp : Z),
  skeleton rs = skeleton em_rs2 ->
  bv_unsigned (ew Ex 8) = tx -> bv_unsigned (ew Ex 9) = valp ->
  (forall a, tx <= a < tx + TX_SIZE -> nx_may_write B STK sp0 FP ly S lyc Sc own a) ->
  nx_may_write B STK sp0 FP ly S lyc Sc own valp ->
  awr_ok Ex rs STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own.
Proof.
  intros Ex rs STK sp0 FP ly S lyc Sc own tx valp Hsk E8 E9 Htab Hv a Hw.
  destruct (em_wrange2 Ex rs tx valp a Hsk E8 E9 Hw) as [H | [H | [H | ->]]];
    first [exact Hv | apply Htab; unfold ATx.TX_SIZE; lia].
Qed.

Lemma em_entry2 : forall lyc Sc (W : world SEGS) mem2 md2 (regs regs2 : bvmap 5 word)
    (tx valp v w3 : Z) (T1 : list byte) (j : Z),
  AR SEGS B lyc Sc W mem2 md2 ->
  In (tx, TX_SIZE) (ablocks B lyc Sc) ->
  obj_at SEGS (mrestrict (w_H W) mem2) tx LAY_TX (tx_vals T1) ->
  u32at T1 440 = j + 1 -> 0 <= j < 765 -> 0 <= w3 <= 765 -> 0 <= v < 256 ->
  nx_saved W mem2 regs (spZ regs) ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 -> alloc_ceiling <= spZ regs - NX_STK ->
  4096 <= valp -> valp + 1 <= 2 ^ 47 -> ~ (SHADOW_OFF <= valp < SHADOW_OFF + 2 ^ 44) ->
  ~ (tx <= valp < tx + TX_SIZE) ->
  (valp + 1 <= spZ regs - NX_STK \/ spZ regs <= valp) ->
  apresent (w_H W) mem2 valp ->
  range_addressable (aview SEGS (w_H W) mem2) SHADOW_OFF valp 1 ->
  getr regs2 2 = w64 (spZ regs - NX_FRAME) -> getr regs2 8 = w64 tx -> getr regs2 9 = w64 valp ->
  getr regs2 10 = w64 v ->
  getr regs2 18 = w64 (tx + 437) -> getr regs2 22 = w64 (SHADOW_OFF + (tx + 437) / 8) ->
  getr regs2 19 = w64 (tx + 444) -> getr regs2 23 = w64 (SHADOW_OFF + (tx + 444) / 8) ->
  getr regs2 20 = w64 (tx + 440) -> getr regs2 24 = w64 (SHADOW_OFF + (tx + 440) / 8) ->
  getr regs2 21 = w64 SB_NX -> getr regs2 25 = w64 w3 -> getr regs2 26 = w64 3 ->
  st_ok_pi SEGS VAL (EM2 regs2 regs j T1) ss2
    (restrict (w_H W) (mkst regs2 (Z_to_bv 64 (BASE + EMR)) mem2 (seg_rom SEGS)))
  /\ sh_ok SEGS BxN SH2 (EM2 regs2 regs j T1) (mrestrict (w_H W) mem2).
Proof.
  intros lyc Sc W mem2 md2 regs regs2 tx valp v w3 T1 j HAR Hg HOBJ HCUR Hj Hw3 Hv HSAV
    Hspr Hsp16 Hceil Hv0 Hv1 Hv5 Hv2 Hv3 Hpv Hrav R2 R8 R9 R10 R18 R22 R19 R23 R20 R24 R21 R25 R26.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof nx_stk_val as HNX. rewrite HNX in Hceil, Hv3.
  destruct Hspr as (Hsp46 & Hsp47).
  destruct (al_blocks _ _ LAWS lyc Sc W mem2 md2 tx TX_SIZE HAR Hg)
    as (Hg16 & Hg4096 & Hgceil & Hgia & Hgpres & _).
  change (req_size TX_SIZE) with 460 in Hgceil, Hgia, Hgpres.
  unfold ATx.TX_SIZE in Hv2.
  pose proof (proj1 (ATx.tx_obj_bytes SEGS _ _ _) HOBJ) as HBY.
  pose proof (ATx.tb_range T1 437) as R437.
  assert (R444 : 0 <= u32at T1 444 < 4294967296).
  { unfold u32at. pose proof (ATx.tb_range T1 444). pose proof (ATx.tb_range T1 (444 + 1)).
    pose proof (ATx.tb_range T1 (444 + 2)). pose proof (ATx.tb_range T1 (444 + 3)). lia. }
  set (E := EM2 regs2 regs j T1).
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs2 (em_extra2 regs j T1)) n)
    by (intros n Hn; unfold E, EM2; apply Eimg_low; exact Hn).
  assert (E2 : ew E 2 = w64 (spZ regs - NX_FRAME))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl); exact R2).
  assert (E8 : ew E 8 = w64 tx)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs2 _ 8 8%bv eq_refl); exact R8).
  assert (E9 : ew E 9 = w64 valp)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl); exact R9).
  assert (E10 : ew E 10 = w64 v)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs2 _ 10 10%bv eq_refl); exact R10).
  assert (E25 : ew E 25 = w64 w3)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs2 _ 25 25%bv eq_refl); exact R25).
  assert (E32 : ew E 32 = w64 SB_NX)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
  assert (E33 : ew E 33 = getr regs 1)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
  assert (E34 : ew E 34 = getr regs 8)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
  assert (E35 : ew E 35 = getr regs 9)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 3)).
  assert (E36 : ew E 36 = getr regs 18)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 4)).
  assert (E37 : ew E 37 = getr regs 19)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 5)).
  assert (E38 : ew E 38 = getr regs 20)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 6)).
  assert (E39 : ew E 39 = getr regs 21)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 7)).
  assert (E40 : ew E 40 = getr regs 22)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 8)).
  assert (E41 : ew E 41 = getr regs 23)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 9)).
  assert (E42 : ew E 42 = getr regs 24)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 10)).
  assert (E43 : ew E 43 = getr regs 25)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 11)).
  assert (E44 : ew E 44 = getr regs 26)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 12)).
  assert (E45 : ew E 45 = w64 (j + 1))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 13)).
  assert (E46 : ew E 46 = w64 (tb T1 437))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 14)).
  assert (E47 : ew E 47 = w64 (u32at T1 444))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 15)).
  assert (U2 : bv_unsigned (ew E 2) = spZ regs - NX_FRAME)
    by (rewrite E2; apply unsigned_lit_small; unfold NX_FRAME; lia).
  assert (U8 : bv_unsigned (ew E 8) = tx) by (rewrite E8; apply unsigned_lit_small; lia).
  assert (U9 : bv_unsigned (ew E 9) = valp) by (rewrite E9; apply unsigned_lit_small; lia).
  assert (U10 : bv_unsigned (ew E 10) = v) by (rewrite E10; apply unsigned_lit_small; lia).
  assert (U25 : bv_unsigned (ew E 25) = w3) by (rewrite E25; apply unsigned_lit_small; lia).
  assert (U32 : bv_unsigned (ew E 32) = SB_NX)
    by (rewrite E32; apply unsigned_lit_small; unfold SB_NX; lia).
  assert (U45 : bv_unsigned (ew E 45) = j + 1) by (rewrite E45; apply unsigned_lit_small; lia).
  assert (U46 : bv_unsigned (ew E 46) = tb T1 437) by (rewrite E46; apply unsigned_lit_small; lia).
  assert (U47 : bv_unsigned (ew E 47) = u32at T1 444) by (rewrite E47; apply unsigned_lit_small; lia).
  assert (HUB : U E BxN = SHADOW_OFF)
    by (unfold U, BxN; cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned;
        rewrite unsigned_lit_small by (unfold SB_NX; lia); reflexivity).
  assert (Hal : (spZ regs - NX_FRAME) mod 16 = 0).
  { unfold NX_FRAME. replace (spZ regs - 96) with (spZ regs + (-6) * 16) by lia.
    rewrite Z_mod_plus_full. exact Hsp16. }
  split.
  - rewrite restrict_mkst_fx. unfold ss2. apply pa_entry_st_ok_full.
    + unfold em_sr2.
      apply regs_ok_pin; [| intros X; discriminate X |].
      2:{ rewrite R26. symmetry. apply denot_lit. lia. }
      apply regs_ok_pin; [| intros X; discriminate X |].
      2:{ rewrite R24. symmetry. apply denot_SHX; [exact E8 | exact E32 | lia | lia | lia]. }
      apply regs_ok_pin; [| intros X; discriminate X |].
      2:{ rewrite R20. cbn [sv_denot]. rewrite U8. reflexivity. }
      apply regs_ok_pin; [| intros X; discriminate X |].
      2:{ rewrite R23. symmetry. apply denot_SHX; [exact E8 | exact E32 | lia | lia | lia]. }
      apply regs_ok_pin; [| intros X; discriminate X |].
      2:{ rewrite R19. cbn [sv_denot]. rewrite U8. reflexivity. }
      apply regs_ok_pin; [| intros X; discriminate X |].
      2:{ rewrite R22. symmetry. apply denot_SHX; [exact E8 | exact E32 | lia | lia | lia]. }
      apply regs_ok_pin; [| intros X; discriminate X |].
      2:{ rewrite R18. cbn [sv_denot]. rewrite U8. reflexivity. }
      apply regs_ok_pin; [| intros X; discriminate X |].
      2:{ rewrite R21. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
      unfold E, EM2. apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + unfold em_rs2, STKR, T437, T440, T444, T456, OUTV8.
      repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      * (* the twelve saved registers *)
        rewrite U2. unfold NX_FRAME in *.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        pose proof HSAV as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12).
        repeat apply Forall_cons; try apply Forall_nil.
        -- apply (em_chunk8 E _ _ 88 33 _ E33).
           replace (spZ regs - 96 + 88) with (spZ regs - 8) by lia. exact S1.
        -- apply (em_chunk8 E _ _ 80 34 _ E34).
           replace (spZ regs - 96 + 80) with (spZ regs - 16) by lia. exact S2.
        -- apply (em_chunk8 E _ _ 72 35 _ E35).
           replace (spZ regs - 96 + 72) with (spZ regs - 24) by lia. exact S3.
        -- apply (em_chunk8 E _ _ 64 36 _ E36).
           replace (spZ regs - 96 + 64) with (spZ regs - 32) by lia. exact S4.
        -- apply (em_chunk8 E _ _ 56 37 _ E37).
           replace (spZ regs - 96 + 56) with (spZ regs - 40) by lia. exact S5.
        -- apply (em_chunk8 E _ _ 48 38 _ E38).
           replace (spZ regs - 96 + 48) with (spZ regs - 48) by lia. exact S6.
        -- apply (em_chunk8 E _ _ 40 39 _ E39).
           replace (spZ regs - 96 + 40) with (spZ regs - 56) by lia. exact S7.
        -- apply (em_chunk8 E _ _ 32 40 _ E40).
           replace (spZ regs - 96 + 32) with (spZ regs - 64) by lia. exact S8.
        -- apply (em_chunk8 E _ _ 24 41 _ E41).
           replace (spZ regs - 96 + 24) with (spZ regs - 72) by lia. exact S9.
        -- apply (em_chunk8 E _ _ 16 42 _ E42).
           replace (spZ regs - 96 + 16) with (spZ regs - 80) by lia. exact S10.
        -- apply (em_chunk8 E _ _ 8 43 _ E43).
           replace (spZ regs - 96 + 8) with (spZ regs - 88) by lia. exact S11.
        -- apply (em_chunk8 E _ _ 0 44 _ E44).
           replace (spZ regs - 96 + 0) with (spZ regs - 96) by lia. exact S12.
      * (* 437 *)
        rewrite U8. split; [lia|]. split; [lia|]. split.
        { intros o Ho. apply (apresent_writable SEGS). exact (proj1 (Hgpres (tx + o) ltac:(lia))). }
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS E _ tx 437 1 (SOff 46 0) (tb T1 437)).
        -- rewrite denot_off0, E46. reflexivity.
        -- change (2 ^ (8 * Z.of_N 1)) with 256. lia.
        -- cbn. lia.
        -- apply (em_val1 SEGS (mrestrict (w_H W) mem2) tx T1 437 HBY). vm_compute. reflexivity.
      * (* 440, read only *)
        rewrite U8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS E _ tx 440 4 (SOff 45 0) (j + 1)).
        -- rewrite denot_off0, E45. reflexivity.
        -- change (2 ^ (8 * Z.of_N 4)) with 4294967296. lia.
        -- cbn. lia.
        -- rewrite <- HCUR. apply (em_val4 SEGS (mrestrict (w_H W) mem2) tx T1 440 HBY).
           intros d Hd. assert (d = 0 \/ d = 1 \/ d = 2 \/ d = 3) as [-> | [-> | [-> | ->]]] by lia;
             vm_compute; reflexivity.
      * (* 444 *)
        rewrite U8. split; [lia|]. split; [lia|]. split.
        { intros o Ho. apply (apresent_writable SEGS). exact (proj1 (Hgpres (tx + o) ltac:(lia))). }
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS E _ tx 444 4 (SOff 47 0) (u32at T1 444)).
        -- rewrite denot_off0, E47. reflexivity.
        -- change (2 ^ (8 * Z.of_N 4)) with 4294967296. lia.
        -- cbn. lia.
        -- apply (em_val4 SEGS (mrestrict (w_H W) mem2) tx T1 444 HBY).
           intros d Hd. assert (d = 0 \/ d = 1 \/ d = 2 \/ d = 3) as [-> | [-> | [-> | ->]]] by lia;
             vm_compute; reflexivity.
      * (* 456 *)
        rewrite U8. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable SEGS). exact (proj1 (Hgpres (tx + o) ltac:(lia))).
      * (* the value byte *)
        rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. replace (valp + o) with valp by lia.
        apply (apresent_writable SEGS). exact Hpv.
    + apply pairwise_disjoint_of_extents.
      unfold em_rs2, STKR, T437, T440, T444, T456, OUTV8, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      cbn [base_val]. rewrite U2, U8, U9.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold NX_FRAME in *.
      repeat split; lia.
    + split; [| split; [exact I | exact I]].
      cbn [em_facts2 f_atoms atoms_ok]. unfold afact_ok, PTRN, OUTF.
      cbn [af_lo af_hi af_al2].
      rewrite U2, U8, U9, U10, U25, U32, U45, U46, U47.
      change (2 ^ 4) with 16. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
      unfold SB_NX, NX_FRAME in *.
      repeat match goal with |- _ /\ _ => split end; lia.
  - unfold sh_ok, SH2. constructor; [|constructor; [|constructor]].
    + apply (shent_ok_of_block SEGS B LAWS lyc Sc W mem2 md2 E BxN 8 tx TX_SIZE 0 460 HAR Hg HUB).
      * unfold U. cbn [sv_denot]. rewrite U8, Z.add_0_r. apply unsigned_lit_small. lia.
      * lia.
      * change (req_size TX_SIZE) with 460. lia.
    + apply (shent_ok_of_range SEGS (w_H W) mem2 E BxN 9 valp 1 valp 0 1 Hrav HUB).
      * unfold U. cbn [sv_denot]. rewrite U9, Z.add_0_r. apply unsigned_lit_small. lia.
      * lia.
      * lia.
      * cbn [Z.min Z.max]. intros x Hx. replace x with valp by lia. exact Hv5.
Qed.

(* carry the invariant of the runs after the call over one run *)
Ltac em_adv2 U8v U9v :=
  lazymatch goal with
  | [ HFR : frame_of ?Ex ?rs (mrestrict _ ?m1) (mrestrict _ ?m2),
      HGR : mem_grows (mrestrict _ ?m1) (mrestrict _ ?m2),
      HIV : em_inv2 ?Wv ?mbv ?m1 ?txv ?valpv |- _ ] =>
    let H2 := fresh "HINV" in
    assert (H2 : em_inv2 Wv mbv m2 txv valpv)
      by (apply (em_inv2_step Ex rs Wv mbv m1 m2 txv valpv);
          [ vm_compute; reflexivity | em_env U8v | em_env U9v | exact HFR | exact HGR | exact HIV ]);
    clear HIV HFR HGR; rename H2 into HINV
  end.

(* ---- the walk after the call ---------------------------------------------------------------- *)

Lemma em_tail : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
    (regs regs2 : bvmap 5 word) memX mem2 md2 (tx chp parp valp : Z) (T : list byte) (j slo shi : Z),
  nx_ctx B STK sp0 FP ly S lyc Sc own W memc mdc regs tx chp parp valp T ->
  0 <= j < 3 * tb T 437 ->
  next_model T tx = emit_res (set4 T 440 (j + 1)) tx (tb T 436 + j / 3) (j mod 3) j (3 * tb T 437) ->
  nx_same W memc memX (spZ regs) tx chp parp valp (tx + 432) ->
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) memX a) ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k ->
  acall_kept SEGS B lyc Sc W memX W mem2 slo shi (fun _ => False) ->
  spZ regs - NX_STK <= slo -> shi <= spZ regs - NX_FRAME ->
  obj_at SEGS (mrestrict (w_H W) mem2) tx LAY_TX (tx_vals (set4 T 440 (j + 1))) ->
  nx_saved W mem2 regs (spZ regs) ->
  apresent (w_H W) mem2 valp ->
  range_addressable (aview SEGS (w_H W) mem2) SHADOW_OFF valp 1 ->
  aview SEGS (w_H W) mem2 chp = Some ((tb T 436 + j / 3) mod 256) ->
  aview SEGS (w_H W) mem2 parp = Some (j mod 3) ->
  getr regs2 2 = w64 (spZ regs - NX_FRAME) ->
  getr regs2 3 = getr regs 3 -> getr regs2 4 = getr regs 4 -> getr regs2 27 = getr regs 27 ->
  getr regs2 8 = w64 tx -> getr regs2 9 = w64 valp ->
  getr regs2 10 = w64 (eff (set4 T 440 (j + 1)) tx ((tb T 436 + j / 3) mod 256) (j mod 3)) ->
  getr regs2 18 = w64 (tx + 437) -> getr regs2 22 = w64 (SHADOW_OFF + (tx + 437) / 8) ->
  getr regs2 19 = w64 (tx + 444) -> getr regs2 23 = w64 (SHADOW_OFF + (tx + 444) / 8) ->
  getr regs2 20 = w64 (tx + 440) -> getr regs2 24 = w64 (SHADOW_OFF + (tx + 440) / 8) ->
  getr regs2 21 = w64 SB_NX ->
  getr regs2 25 = w64 (3 * tb T 437) -> getr regs2 26 = w64 ((tx + 440) mod 8 + 3) ->
  SRr SEGS W (cfg_at SEGS (BASE + EMR) regs2 mem2 md2)
    (tnext_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs tx chp parp valp T).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regs2 memX mem2 md2
    tx chp parp valp T j slo shi HCTX Hj3 HMOD HS1 HP1 HJ HK Hlo Hhi HOBJ2 HSAV2 Hpv Hrav Hac Hap
    R2 R3 R4 R27 R8 R9 R10 R18 R22 R19 R23 R20 R24 R21 R25 R26.
  pose proof HCTX as (HAR & Hg & Hoc & Hop & Hov & Dcp & Dcv & Dpv & Pc & Pp & Pv & Bc & Bp & Bv & B456 &
    Hspr & Hceil & Hsp16 & Hslo & Hshi & Hwtab & Hwc & Hwp & Hwv & Hret & Hra4 & Hgp & Htp &
    Q10 & Q11 & Q12 & Q13 & HTL0 & HI & Hobjc & Hpresc).
  pose proof Hoc as (Hc0 & Hc1 & Hc2 & Hc3 & Hc4 & Hc5).
  pose proof Hop as (Hp0 & Hp1 & Hp2 & Hp3 & Hp4 & Hp5).
  pose proof Hov as (Hv0 & Hv1 & Hv2 & Hv3 & Hv4 & Hv5).
  pose proof Hspr as (Hsp46 & Hsp47).
  unfold ATx.TX_SIZE in Hc2, Hp2, Hv2.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof nx_stk_val as HNX.
  pose proof (proj1 HJ) as HAR2.
  destruct (al_blocks _ _ LAWS lyc Sc W mem2 md2 tx TX_SIZE HAR2 Hg) as (Hg16 & Hg4096 & Hgceil & Hgia & _).
  change (req_size TX_SIZE) with 460 in Hgceil, Hgia.
  pose proof (ATx.tb_range T 436) as R436. pose proof (ATx.tb_range T 437) as R437.
  assert (HL1 : length (set4 T 440 (j + 1)) = 460%nat) by (apply len_set4; lia).
  assert (HCUR : u32at (set4 T 440 (j + 1)) 440 = j + 1)
    by (rewrite u32at_u32; apply u32_set4; lia).
  assert (Hpr : 0 <= j mod 3 < 3) by (apply Z.mod_pos_bound; lia).
  assert (Hcm : 0 <= (tb T 436 + j / 3) mod 256 < 256) by (apply Z.mod_pos_bound; lia).
  assert (R26' : getr regs2 26 = w64 3) by (rewrite R26, (em_mod8 tx Hg16); reflexivity).
  set (T1 := set4 T 440 (j + 1)) in *.
  set (CM := (tb T 436 + j / 3) mod 256) in *.
  set (P := j mod 3) in *.
  set (V := eff T1 tx CM P) in *.
  pose proof (em_eff_range T1 tx CM P) as HVr. fold V in HVr.
  destruct (em_entry2 lyc Sc W mem2 md2 regs regs2 tx valp V (3 * tb T 437) T1 j HAR2 Hg HOBJ2 HCUR
    ltac:(lia) ltac:(lia) HVr HSAV2 Hspr Hsp16 Hceil Hv0 Hv1 Hv5 Hv2 Hv3 Hpv Hrav
    R2 R8 R9 R10 R18 R22 R19 R23 R20 R24 R21 R25 R26') as [HS SHOK].
  remember (EM2 regs2 regs j T1) as E eqn:HEdef.
  assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EM2; apply Eimg_env).
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs2 (em_extra2 regs j T1)) n)
    by (intros n Hn; subst E; unfold EM2; apply Eimg_low; exact Hn).
  assert (E2 : ew E 2 = w64 (spZ regs - NX_FRAME))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl); exact R2).
  assert (E3 : ew E 3 = getr regs 3)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs2 _ 3 3%bv eq_refl); exact R3).
  assert (E4 : ew E 4 = getr regs 4)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs2 _ 4 4%bv eq_refl); exact R4).
  assert (E27 : ew E 27 = getr regs 27)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs2 _ 27 27%bv eq_refl); exact R27).
  assert (E8 : ew E 8 = w64 tx)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs2 _ 8 8%bv eq_refl); exact R8).
  assert (E9 : ew E 9 = w64 valp)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl); exact R9).
  assert (E10 : ew E 10 = w64 V)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs2 _ 10 10%bv eq_refl); exact R10).
  assert (E25 : ew E 25 = w64 (3 * tb T 437))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs2 _ 25 25%bv eq_refl); exact R25).
  assert (E33 : ew E 33 = getr regs 1)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
  assert (E34 : ew E 34 = getr regs 8)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
  assert (E35 : ew E 35 = getr regs 9)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 3)).
  assert (E36 : ew E 36 = getr regs 18)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 4)).
  assert (E37 : ew E 37 = getr regs 19)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 5)).
  assert (E38 : ew E 38 = getr regs 20)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 6)).
  assert (E39 : ew E 39 = getr regs 21)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 7)).
  assert (E40 : ew E 40 = getr regs 22)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 8)).
  assert (E41 : ew E 41 = getr regs 23)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 9)).
  assert (E42 : ew E 42 = getr regs 24)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 10)).
  assert (E43 : ew E 43 = getr regs 25)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 11)).
  assert (E44 : ew E 44 = getr regs 26)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 12)).
  assert (E45 : ew E 45 = Z_to_bv 64 (j + 1))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 13)).
  assert (E46 : ew E 46 = Z_to_bv 64 (tb T1 437))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 14)).
  assert (E47 : ew E 47 = Z_to_bv 64 (u32at T1 444))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 15)).
  assert (U2 : bv_unsigned (ew E 2) = spZ regs - NX_FRAME)
    by (rewrite E2; apply unsigned_lit_small; unfold NX_FRAME; lia).
  assert (U8 : bv_unsigned (ew E 8) = tx) by (rewrite E8; apply unsigned_lit_small; lia).
  assert (U9 : bv_unsigned (ew E 9) = valp) by (rewrite E9; apply unsigned_lit_small; lia).
  clear HEdef EL.
  assert (HBY3 : forall m, em_inv2 W mem2 m tx valp ->
            forall i, tx_fbyte i = true -> i <> 437 -> ~ (444 <= i < 448) -> ~ (456 <= i < 460) ->
            mbyte SEGS (mrestrict (w_H W) m) (tx + i) = Some (nth (Z.to_nat i) T1 (Z_to_bv 8 0)))
    by (intros m HIm; exact (em_inv2_bytes W mem2 m tx valp T1 HIm ltac:(lia) ltac:(lia) Hv2 HOBJ2)).
  assert (HROKg : forall T', next_model T tx = (1, (CM, P, V), T') -> thd_replay_ok T')
    by (intros T' HM; pose proof (thd_ok_next T tx HTL0 HI) as Hok; rewrite HM in Hok; exact Hok).
  assert (Hd2 : spZ regs - NX_STK <= slo) by exact Hlo.
  assert (Hd3 : shi <= spZ regs) by (unfold NX_FRAME in Hhi; lia).
  pose proof (em_inv2_refl W mem2 tx valp) as HINV.
  unfold cfg_at. change (w64 (BASE + EMR)) with (Z_to_bv 64 (BASE + EMR)).
  paj_run_tok RUN HS HJ SHOK BspanN;
    [ apply (em_awr2 _ _ STK sp0 FP ly S lyc Sc own tx valp);
      [vm_compute; reflexivity | em_env U8 | em_env U9 | exact Hwtab | exact Hwv] | ].
  em_adv2 U8 U9.
  psrr_branch_tok RUN BR HS SHOK BspanN.
  - (* the cursor reached three times the width: the width is cleared *)
    lazymatch type of HS with
    | st_ok_pi _ _ ?Ex _ _ =>
      assert (X45 : ew Ex 45 = Z_to_bv 64 (j + 1)) by em_env E45;
      assert (X25 : ew Ex 25 = Z_to_bv 64 (3 * tb T 437)) by em_env E25
    end.
    rewrite !denot_off0, X45, X25, em_bge_lit in Hc by lia.
    apply (proj1 (negb_true_iff _)), Z.ltb_ge in Hc.
    assert (HMOD' : next_model T tx = (1, (CM, P, V), set4 (setb T1 437 0) 456 0)).
    { rewrite HMOD. unfold emit_res. rewrite (proj2 (Z.ltb_ge (j + 1) (3 * tb T 437)) Hc). reflexivity. }
    paj_run_tok RUN HS HJ SHOK BspanN;
      [ apply (em_awr2 _ _ STK sp0 FP ly S lyc Sc own tx valp);
        [vm_compute; reflexivity | em_env U8 | em_env U9 | exact Hwtab | exact Hwv] | ].
    em_adv2 U8 U9.
    lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into msF end.
    em_region HS 1%nat HR437. em_region HS 3%nat HR444. em_region HS 4%nat HR456.
    em_region HS 5%nat HRV.
    em_reg HS (1%bv : bv 5) (getr regs 1) ltac:(em_pf E33) R1f.
    em_reg HS (2%bv : bv 5) (getr regs 2)
      ltac:(cbn [sv_denot]; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite U2;
            unfold NX_FRAME; rewrite Z.sub_add; unfold spZ; apply Z_to_bv_bv_unsigned) R2f.
    em_reg HS (3%bv : bv 5) (getr regs 3) ltac:(em_pf E3) R3f.
    em_reg HS (4%bv : bv 5) (getr regs 4) ltac:(em_pf E4) R4f.
    em_reg HS (8%bv : bv 5) (getr regs 8) ltac:(em_pf E34) R8f.
    em_reg HS (9%bv : bv 5) (getr regs 9) ltac:(em_pf E35) R9f.
    em_reg HS (18%bv : bv 5) (getr regs 18) ltac:(em_pf E36) R18f.
    em_reg HS (19%bv : bv 5) (getr regs 19) ltac:(em_pf E37) R19f.
    em_reg HS (20%bv : bv 5) (getr regs 20) ltac:(em_pf E38) R20f.
    em_reg HS (21%bv : bv 5) (getr regs 21) ltac:(em_pf E39) R21f.
    em_reg HS (22%bv : bv 5) (getr regs 22) ltac:(em_pf E40) R22f.
    em_reg HS (23%bv : bv 5) (getr regs 23) ltac:(em_pf E41) R23f.
    em_reg HS (24%bv : bv 5) (getr regs 24) ltac:(em_pf E42) R24f.
    em_reg HS (25%bv : bv 5) (getr regs 25) ltac:(em_pf E43) R25f.
    em_reg HS (26%bv : bv 5) (getr regs 26) ltac:(em_pf E44) R26f.
    em_reg HS (27%bv : bv 5) (getr regs 27) ltac:(em_pf E27) R27f.
    em_reg HS (10%bv : bv 5) (w64 1) ltac:(apply denot_lit; lia) R10f.
    pose proof (aregs_preserved_eqs regs (ms_regs msF) R2f R3f R4f R8f R9f
      R18f R19f R20f R21f R22f R23f R24f R25f R26f R27f) as HPRES.
    assert (HOBJ3 : obj_at SEGS (mrestrict (w_H W) (ms_mem msF)) tx LAY_TX
                      (tx_vals (set4 (setb T1 437 0) 456 0))).
    { lazymatch type of HS with
      | st_ok_pi _ _ ?Ex _ _ =>
        exact (em_obj_w Ex W _ tx T1 _ _ _ HL1 (HBY3 _ HINV) ltac:(em_env U8)
                 HR437 ltac:(em_in) HR444 ltac:(em_in) ltac:(em_env E47) HR456 ltac:(em_in))
      end. }
    assert (Hav3 : aview SEGS (w_H W) (ms_mem msF) valp = Some V).
    { lazymatch type of HS with
      | st_ok_pi _ _ ?Ex _ _ =>
        exact (em_out_s Ex W _ 9%nat valp _ 0 1 0 1 (SOff 10 0) V HRV ltac:(em_env U9) ltac:(em_in)
                 ltac:(em_pf E10) HVr)
      end. }
    assert (Hac3 : aview SEGS (w_H W) (ms_mem msF) chp = Some CM)
      by (rewrite (em_inv2_aview W mem2 (ms_mem msF) tx valp chp HINV ltac:(lia)
                     ltac:(unfold em_wset; lia)); exact Hac).
    assert (Hap3 : aview SEGS (w_H W) (ms_mem msF) parp = Some P)
      by (rewrite (em_inv2_aview W mem2 (ms_mem msF) tx valp parp HINV ltac:(lia)
                     ltac:(unfold em_wset; lia)); exact Hap).
    eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
    intros matX. cbn [ms_regs ms_mem]. unfold YK0s.ret_ok in Hret. rewrite R1f, Hret.
    exact (em_finish STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs (ms_regs msF)
             memX mem2 (ms_mem msF) _ tx chp parp valp T _ CM P V slo shi
             HAR Hg Hoc Hop Hov Hspr Hceil Hslo Hshi HMOD'
             ltac:(apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ)
             HPRES HS1 HP1 HK Hd2 Hd3
             (em_inv2_same W mem2 (ms_mem msF) (spZ regs) tx chp parp valp HINV) (proj2 HINV)
             R10f HOBJ3 (HROKg _ HMOD') Hac3 Hap3 Hav3).
  - (* the cursor is below three times the width: the wait is set *)
    lazymatch type of HS with
    | st_ok_pi _ _ ?Ex _ _ =>
      assert (X45 : ew Ex 45 = Z_to_bv 64 (j + 1)) by em_env E45;
      assert (X25 : ew Ex 25 = Z_to_bv 64 (3 * tb T 437)) by em_env E25
    end.
    rewrite !denot_off0, X45, X25, em_bge_lit in Hc by lia.
    apply (proj1 (negb_false_iff _)), Z.ltb_lt in Hc.
    assert (HMOD' : next_model T tx = (1, (CM, P, V), set4 (set4 T1 444 11) 456 0)).
    { rewrite HMOD. unfold emit_res. rewrite (proj2 (Z.ltb_lt (j + 1) (3 * tb T 437)) Hc). reflexivity. }
    paj_run_tok RUN HS HJ SHOK BspanN;
      [ apply (em_awr2 _ _ STK sp0 FP ly S lyc Sc own tx valp);
        [vm_compute; reflexivity | em_env U8 | em_env U9 | exact Hwtab | exact Hwv] | ].
    em_adv2 U8 U9.
    lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into msF end.
    em_region HS 1%nat HR437. em_region HS 3%nat HR444. em_region HS 4%nat HR456.
    em_region HS 5%nat HRV.
    em_reg HS (1%bv : bv 5) (getr regs 1) ltac:(em_pf E33) R1f.
    em_reg HS (2%bv : bv 5) (getr regs 2)
      ltac:(cbn [sv_denot]; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite U2;
            unfold NX_FRAME; rewrite Z.sub_add; unfold spZ; apply Z_to_bv_bv_unsigned) R2f.
    em_reg HS (3%bv : bv 5) (getr regs 3) ltac:(em_pf E3) R3f.
    em_reg HS (4%bv : bv 5) (getr regs 4) ltac:(em_pf E4) R4f.
    em_reg HS (8%bv : bv 5) (getr regs 8) ltac:(em_pf E34) R8f.
    em_reg HS (9%bv : bv 5) (getr regs 9) ltac:(em_pf E35) R9f.
    em_reg HS (18%bv : bv 5) (getr regs 18) ltac:(em_pf E36) R18f.
    em_reg HS (19%bv : bv 5) (getr regs 19) ltac:(em_pf E37) R19f.
    em_reg HS (20%bv : bv 5) (getr regs 20) ltac:(em_pf E38) R20f.
    em_reg HS (21%bv : bv 5) (getr regs 21) ltac:(em_pf E39) R21f.
    em_reg HS (22%bv : bv 5) (getr regs 22) ltac:(em_pf E40) R22f.
    em_reg HS (23%bv : bv 5) (getr regs 23) ltac:(em_pf E41) R23f.
    em_reg HS (24%bv : bv 5) (getr regs 24) ltac:(em_pf E42) R24f.
    em_reg HS (25%bv : bv 5) (getr regs 25) ltac:(em_pf E43) R25f.
    em_reg HS (26%bv : bv 5) (getr regs 26) ltac:(em_pf E44) R26f.
    em_reg HS (27%bv : bv 5) (getr regs 27) ltac:(em_pf E27) R27f.
    em_reg HS (10%bv : bv 5) (w64 1) ltac:(apply denot_lit; lia) R10f.
    pose proof (aregs_preserved_eqs regs (ms_regs msF) R2f R3f R4f R8f R9f
      R18f R19f R20f R21f R22f R23f R24f R25f R26f R27f) as HPRES.
    assert (HOBJ3 : obj_at SEGS (mrestrict (w_H W) (ms_mem msF)) tx LAY_TX
                      (tx_vals (set4 (set4 T1 444 11) 456 0))).
    { lazymatch type of HS with
      | st_ok_pi _ _ ?Ex _ _ =>
        exact (em_obj_wait Ex W _ tx T1 _ _ _ HL1 (HBY3 _ HINV) ltac:(em_env U8)
                 HR437 ltac:(em_in) ltac:(em_env E46) HR444 ltac:(em_in) HR456 ltac:(em_in))
      end. }
    assert (Hav3 : aview SEGS (w_H W) (ms_mem msF) valp = Some V).
    { lazymatch type of HS with
      | st_ok_pi _ _ ?Ex _ _ =>
        exact (em_out_s Ex W _ 9%nat valp _ 0 1 0 1 (SOff 10 0) V HRV ltac:(em_env U9) ltac:(em_in)
                 ltac:(em_pf E10) HVr)
      end. }
    assert (Hac3 : aview SEGS (w_H W) (ms_mem msF) chp = Some CM)
      by (rewrite (em_inv2_aview W mem2 (ms_mem msF) tx valp chp HINV ltac:(lia)
                     ltac:(unfold em_wset; lia)); exact Hac).
    assert (Hap3 : aview SEGS (w_H W) (ms_mem msF) parp = Some P)
      by (rewrite (em_inv2_aview W mem2 (ms_mem msF) tx valp parp HINV ltac:(lia)
                     ltac:(unfold em_wset; lia)); exact Hap).
    eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
    intros matX. cbn [ms_regs ms_mem]. unfold YK0s.ret_ok in Hret. rewrite R1f, Hret.
    exact (em_finish STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs (ms_regs msF)
             memX mem2 (ms_mem msF) _ tx chp parp valp T _ CM P V slo shi
             HAR Hg Hoc Hop Hov Hspr Hceil Hslo Hshi HMOD'
             ltac:(apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ)
             HPRES HS1 HP1 HK Hd2 Hd3
             (em_inv2_same W mem2 (ms_mem msF) (spZ regs) tx chp parp valp HINV) (proj2 HINV)
             R10f HOBJ3 (HROKg _ HMOD') Hac3 Hap3 Hav3).
Qed.

(* ---- the walk of the cut ---------------------------------------------------------------- *)

Theorem pb_nx_emit : tb_reac_headamp_tx_effective_spec B -> nx_emit_spec B.
Proof.
  intros EFF. unfold nx_emit_spec.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsj memj mdj
    tx chp parp valp T j q HCTX HMID HSAV HOBJ Hw0 Hj3 HCAR HMOD HAT.
  pose proof HCTX as (HAR & Hg & Hoc & Hop & Hov & Dcp & Dcv & Dpv & Pc & Pp & Pv & Bc & Bp & Bv & B456 &
    Hspr & Hceil & Hsp16 & Hslo & Hshi & Hwtab & Hwc & Hwp & Hwv & Hret & Hra4 & Hgp & Htp &
    Q10 & Q11 & Q12 & Q13 & HTL0 & HI & Hobjc & Hpresc).
  pose proof HMID as (HJ & HSAME & HpresS & HpresK & _).
  pose proof HAT as (HKG & A2 & A8 & A9 & A11 & A12 & A21 & A18 & A22 & A19 & A23 & A20 & A24 &
    A25 & A26 & A17 & A5).
  pose proof Hoc as (Hc0 & Hc1 & Hc2 & Hc3 & Hc4 & Hc5).
  pose proof Hop as (Hp0 & Hp1 & Hp2 & Hp3 & Hp4 & Hp5).
  pose proof Hov as (Hv0 & Hv1 & Hv2 & Hv3 & Hv4 & Hv5).
  pose proof Hspr as (Hsp46 & Hsp47).
  unfold ATx.TX_SIZE in Hc2, Hp2, Hv2.
  assert (HSTK : STK_reac_headamp_tx_next = 4208) by reflexivity.
  rewrite HSTK in Hc3, Hp3, Hv3.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof nx_stk_val as HNX.
  pose proof HJ as (HARj & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hal0 & _) & _).
  destruct (al_blocks _ _ LAWS lyc Sc W memj mdj tx TX_SIZE HARj Hg) as (Hg16 & Hg4096 & Hgceil & Hgia & _).
  change (req_size TX_SIZE) with 460 in Hgceil, Hgia.
  pose proof (ATx.tb_range T 436) as R436. pose proof (ATx.tb_range T 437) as R437.
  assert (Hcr : 0 <= tb T 436 + j / 3 <= 509).
  { split; [pose proof (Z.div_pos j 3 ltac:(lia) ltac:(lia)); lia|].
    assert (j / 3 < 255) by (apply Z.div_lt_upper_bound; lia). lia. }
  assert (Hpr : 0 <= j mod 3 < 3) by (apply Z.mod_pos_bound; lia).
  assert (HL1 : length (set4 T 440 (j + 1)) = 460%nat) by (apply len_set4; lia).
  destruct (em_entry1 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regsj memj mdj
    tx chp parp valp T (tb T 436 + j / 3) (j mod 3) q HCTX HMID HAT Hcr Hpr) as [HS SHOK].
  set (C := tb T 436 + j / 3) in *. set (P := j mod 3) in *. set (T1 := set4 T 440 (j + 1)) in *.
  remember (EM1 regsj) as E eqn:HEdef.
  assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EM1; apply Eimg_env).
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regsj em_extra1) n)
    by (intros n Hn; subst E; unfold EM1; apply Eimg_low; exact Hn).
  assert (E2 : ew E 2 = w64 (spZ regs - NX_FRAME))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 2 2%bv eq_refl); exact A2).
  assert (E3 : ew E 3 = getr regs 3)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 3 3%bv eq_refl);
        apply (HKG 3%bv); em_in).
  assert (E4 : ew E 4 = getr regs 4)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 4 4%bv eq_refl);
        apply (HKG 4%bv); em_in).
  assert (E27 : ew E 27 = getr regs 27)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 27 27%bv eq_refl);
        apply (HKG 27%bv); em_in).
  assert (E5 : ew E 5 = w64 P)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 5 5%bv eq_refl); exact A5).
  assert (E8 : ew E 8 = w64 tx)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 8 8%bv eq_refl); exact A8).
  assert (E9 : ew E 9 = w64 valp)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 9 9%bv eq_refl); exact A9).
  assert (E11 : ew E 11 = w64 chp)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 11 11%bv eq_refl); exact A11).
  assert (E12 : ew E 12 = w64 parp)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 12 12%bv eq_refl); exact A12).
  assert (E17 : ew E 17 = w64 C)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 17 17%bv eq_refl); exact A17).
  assert (E18 : ew E 18 = w64 (tx + 437))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 18 18%bv eq_refl); exact A18).
  assert (E19 : ew E 19 = w64 (tx + 444))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 19 19%bv eq_refl); exact A19).
  assert (E20 : ew E 20 = w64 (tx + 440))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 20 20%bv eq_refl); exact A20).
  assert (E22 : ew E 22 = w64 (SHADOW_OFF + (tx + 437) / 8))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 22 22%bv eq_refl); exact A22).
  assert (E23 : ew E 23 = w64 (SHADOW_OFF + (tx + 444) / 8))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 23 23%bv eq_refl); exact A23).
  assert (E24 : ew E 24 = w64 (SHADOW_OFF + (tx + 440) / 8))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 24 24%bv eq_refl); exact A24).
  assert (E25 : ew E 25 = w64 (3 * tb T 437))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 25 25%bv eq_refl); exact A25).
  assert (E26 : ew E 26 = w64 ((tx + 440) mod 8 + 3))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsj _ 26 26%bv eq_refl); exact A26).
  assert (E32 : ew E 32 = w64 SB_NX)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsj _ 0)).
  assert (U11 : bv_unsigned (ew E 11) = chp) by (rewrite E11; apply unsigned_lit_small; lia).
  assert (U12 : bv_unsigned (ew E 12) = parp) by (rewrite E12; apply unsigned_lit_small; lia).
  clear HEdef EL.
  unfold cfg_at. change (w64 (BASE + EMIT)) with (Z_to_bv 64 (BASE + EMIT)).
  (* One run from EMIT to the call: T16 and T17 and the two slow shadow checks are decided in it. *)
  paj_run_tok RUN HS HJ SHOK BspanN;
    [ intros a Hw; destruct (em_wrange1 E chp parp a U11 U12 Hw) as [-> | ->]; [exact Hwc | exact Hwp] | ].
  lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into msX end.
  (* the registers at the call *)
  em_regc HS (1%bv : bv 5) (Z_to_bv 64 (BASE + EMR)) ltac:(eapply codeptr_val; eassumption) R1X.
  em_regc HS (2%bv : bv 5) (w64 (spZ regs - NX_FRAME)) ltac:(em_pf E2) R2X.
  em_regc HS (3%bv : bv 5) (getr regs 3) ltac:(em_pf E3) R3X.
  em_regc HS (4%bv : bv 5) (getr regs 4) ltac:(em_pf E4) R4X.
  em_regc HS (8%bv : bv 5) (w64 tx) ltac:(em_pf E8) R8X.
  em_regc HS (9%bv : bv 5) (w64 valp) ltac:(em_pf E9) R9X.
  em_regc HS (10%bv : bv 5) (w64 tx) ltac:(em_pf E8) R10X.
  em_regc HS (11%bv : bv 5) (w64 (C mod 256))
    ltac:(rewrite denot_lit_U; unfold w64; f_equal; rewrite U_and_lit by lia;
          lazymatch goal with |- context [U ?Ex (SOff 17 0)] =>
            rewrite (U_atom Ex 17 C ltac:(em_env E17) ltac:(lia)) end;
          apply land_mod256) R11X.
  em_regc HS (12%bv : bv 5) (w64 P)
    ltac:(rewrite denot_lit_U; unfold w64; f_equal; rewrite U_and_lit by lia;
          lazymatch goal with |- context [U ?Ex (SOff 5 0)] =>
            rewrite (U_atom Ex 5 P ltac:(em_env E5) ltac:(lia)) end;
          rewrite land_mod256; apply Z.mod_small; lia) R12X.
  em_regc HS (18%bv : bv 5) (w64 (tx + 437)) ltac:(em_pf E18) R18X.
  em_regc HS (19%bv : bv 5) (w64 (tx + 444)) ltac:(em_pf E19) R19X.
  em_regc HS (20%bv : bv 5) (w64 (tx + 440)) ltac:(em_pf E20) R20X.
  em_regc HS (21%bv : bv 5) (w64 SB_NX) ltac:(em_pf E32) R21X.
  em_regc HS (22%bv : bv 5) (w64 (SHADOW_OFF + (tx + 437) / 8)) ltac:(em_pf E22) R22X.
  em_regc HS (23%bv : bv 5) (w64 (SHADOW_OFF + (tx + 444) / 8)) ltac:(em_pf E23) R23X.
  em_regc HS (24%bv : bv 5) (w64 (SHADOW_OFF + (tx + 440) / 8)) ltac:(em_pf E24) R24X.
  em_regc HS (25%bv : bv 5) (w64 (3 * tb T 437)) ltac:(em_pf E25) R25X.
  em_regc HS (26%bv : bv 5) (w64 ((tx + 440) mod 8 + 3)) ltac:(em_pf E26) R26X.
  em_regc HS (27%bv : bv 5) (getr regs 27) ltac:(em_pf E27) R27X.
  (* the two bytes the block stored, and what it left alone *)
  em_regionc HS 0%nat HRC. em_regionc HS 1%nat HRP.
  assert (HacX : aview SEGS (w_H W) (ms_mem msX) chp = Some (C mod 256)).
  { lazymatch type of HS with
    | st_ok _ ?Ex _ _ =>
      exact (em_out Ex W _ 11%nat chp _ 0 1 0 1 (SOff 17 0) C HRC ltac:(em_env U11) ltac:(em_in)
               ltac:(em_pf E17) ltac:(lia))
    end. }
  assert (HapX : aview SEGS (w_H W) (ms_mem msX) parp = Some P).
  { lazymatch type of HS with
    | st_ok _ ?Ex _ _ =>
      exact (em_out_s Ex W _ 12%nat parp _ 0 1 0 1 (SOff 5 0) P HRP ltac:(em_env U12) ltac:(em_in)
               ltac:(em_pf E5) ltac:(lia))
    end. }
  assert (HPRE : forall x : word, ~ (bv_unsigned x = chp \/ bv_unsigned x = parp) ->
            mrestrict (w_H W) (ms_mem msX) x = mrestrict (w_H W) memj x).
  { intros x Hx. apply HFr. intros Hw. exact (Hx (em_wrange1 E chp parp _ U11 U12 Hw)). }
  (* the machine at the call, then drop the run's large state *)
  pmkst HS. rewrite pa_sigma_reac_headamp_tx_effective.
  clear HS SHOK HF HFr HRC HRP.
  assert (HKX : forall a, 0 <= a < 2 ^ 64 -> a <> chp -> a <> parp ->
            aview SEGS (w_H W) (ms_mem msX) a = aview SEGS (w_H W) memj a).
  { intros a Ha H1 H2. apply (aview_eq_of SEGS). apply HPRE. rewrite unsigned_lit_small by exact Ha.
    intros [Hx | Hx]; [exact (H1 Hx) | exact (H2 Hx)]. }
  assert (HSAMEX : nx_same W memc (ms_mem msX) (spZ regs) tx chp parp valp (tx + 432)).
  { intros x Hst Htc. rewrite (HPRE x); [exact (HSAME x Hst Htc)|].
    intros Hx. apply Htc. unfold nx_touch2.
    destruct Hx as [Hx | Hx]; [right; left; exact Hx | right; right; left; exact Hx]. }
  assert (HP1 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem msX) a)
    by (intros a Ha; exact (em_grows_pres W memj (ms_mem msX) a HG (HpresK a Ha))).
  assert (HOBJX : obj_at SEGS (mrestrict (w_H W) (ms_mem msX)) tx LAY_TX (tx_vals T1)).
  { apply (proj2 (ATx.tx_obj_bytes SEGS _ tx _)). intros i Hi.
    pose proof (ATx.tx_fbyte_range i Hi) as Hir.
    rewrite <- (proj1 (ATx.tx_obj_bytes SEGS _ _ _) HOBJ i Hi).
    unfold mbyte. rewrite (HPRE (Z_to_bv 64 (tx + i))); [reflexivity|].
    rewrite unsigned_lit_small by (clear - Hir Hg4096 Hgceil C1; lia).
    intros [Hx | Hx]; [apply Hc2 | apply Hp2]; clear - Hx Hir; lia. }
  assert (HSAVX : nx_saved W (ms_mem msX) regs (spZ regs)).
  { apply (em_saved_keep W memj); [|exact HSAV].
    intros a Ha. apply HKX;
      [clear - Ha Hsp46 Hsp47; lia | clear - Ha Hc3; lia | clear - Ha Hp3; lia]. }
  eapply SRr_bind.
  { eapply (cl_callS B LAWS W (ms_regs msX) (ms_mem msX) _ STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k
      STK_reac_headamp_tx_effective [] 0 (spZ regs - NX_FRAME - sp0) (getr (ms_regs msX) 1) []
      (fun ly' S' W' regs' mem' md' => ly' = lyc /\ S' = Sc /\ W' = W /\
         getr regs' 10 = w64 (eff T1 tx (C mod 256) P) /\
         (tx <> 0 -> obj_at SEGS (mrestrict (w_H W) mem') tx ATx.LAY_TX (ATx.tx_vals T1))) HJ).
    - unfold spZ at 1. rewrite R2X. unfold w64.
      rewrite unsigned_lit_small by (unfold NX_FRAME; clear - Hsp46 Hsp47; lia). clear; lia.
    - unfold NX_FRAME. replace (spZ regs - 96 - sp0) with (spZ regs + (-6 - sp0 / 16) * 16)
        by (pose proof (Z.div_mod sp0 16 ltac:(clear; lia)) as Hd16; clear - Hd16 Hal0; lia).
      rewrite Z_mod_plus_full. exact Hsp16.
    - unfold NX_FRAME. clear - Hshi Hsp46. lia.
    - unfold STK_reac_headamp_tx_effective, ESTACK. clear; lia.
    - unfold STK_reac_headamp_tx_effective, ESTACK, NX_FRAME. unfold NX_STK in Hslo. rewrite HSTK in Hslo.
      clear - Hslo. lia.
    - rewrite R3X. exact Hgp.
    - rewrite R4X. exact Htp.
    - reflexivity.
    - rewrite R1X. apply ret_ok_codeptr_v; [unfold EMR, AF_reac_headamp_tx_next; clear; lia | reflexivity].
    - rewrite R1X. pose proof pa_B_ok as HB.
      rewrite unsigned_lit_small by (unfold EMR, AF_reac_headamp_tx_next; clear - HB; lia).
      unfold EMR, AF_reac_headamp_tx_next. clear - HB. lia.
    - apply achain_low. unfold s0Z. rewrite R8X. unfold w64.
      rewrite unsigned_lit_small by (clear - Hg4096 Hgceil C1; lia). clear - Hgceil. lia.
    - intros HPRE7.
      lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg ?pcx ?mm ?rom) ?mdd) _ =>
        change (mkCfg (mkst rg pcx mm rom) mdd)
          with (cfg_at SEGS (BASE + AF_reac_headamp_tx_effective) rg mm mdd) end.
      exact (EFF lyc Sc W (ms_regs msX) (ms_mem msX) _ [] tx (C mod 256) P T1 HPRE7 R10X R11X R12X
               ltac:(apply Z.mod_pos_bound; clear; lia) ltac:(clear - Hpr; lia) HL1 (or_intror (conj Hg HOBJX))).
    - intros a (rg & [] & _). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJ2c & HP2 & (-> & -> & -> & Ha0 & HT2)).
  rewrite Z.add_0_r in HJ2.
  replace (sp0 + (spZ regs - NX_FRAME - sp0)) with (spZ regs - NX_FRAME) in HJ2c by (clear; lia).
  pose proof (acall_kept_of_journal SEGS B pa_segs_low STK_reac_headamp_tx_effective (spZ regs - NX_FRAME)
    [] [] lyc Sc W (ms_mem msX) _ lyc Sc W mem2 md2 0 (fun _ => False) HJ2c (proj1 HJ)
    (fun a Ha => inFP_nil a Ha) (fun b m i Hb _ _ => Hb) sink_closed_nil) as HK.
  pose proof HK as (K1 & _).
  assert (HSAV2 : nx_saved W mem2 regs (spZ regs)).
  { apply (em_saved_keep W (ms_mem msX)); [|exact HSAVX].
    intros a Ha. apply K1.
    - unfold NX_STK in Hceil. rewrite HSTK in Hceil. clear - Ha Hceil Hsp47. lia.
    - unfold STK_reac_headamp_tx_effective, ESTACK, NX_FRAME. clear - Ha. lia. }
  assert (Hpv2 : apresent (w_H W) mem2 valp)
    by exact (proj1 (awr_byte_present SEGS B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k
                       valp HJ2 Hwv)).
  assert (Hrav2 : range_addressable (aview SEGS (w_H W) mem2) SHADOW_OFF valp 1).
  { apply (em_out_ra STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem msX) _ k _ _ mem2 md2 valp
             HJ HJ2c Hwv Hv5).
    exact (em_ra_keep W memc (ms_mem msX) (spZ regs) tx chp parp valp valp HSAMEX
             Hsp46 Hg4096 Hgia Hv0 Hv1 Hc5 Hp5 Hv5 Bv). }
  assert (Hac2 : aview SEGS (w_H W) mem2 chp = Some (C mod 256)).
  { rewrite (em_out_keep STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem msX) _ k _ _ mem2 md2 chp
               HJ HJ2c Hwc ltac:(unfold STK_reac_headamp_tx_effective, ESTACK, NX_FRAME; clear - Hc3; lia)).
    exact HacX. }
  assert (Hap2 : aview SEGS (w_H W) mem2 parp = Some P).
  { rewrite (em_out_keep STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem msX) _ k _ _ mem2 md2 parp
               HJ HJ2c Hwp ltac:(unfold STK_reac_headamp_tx_effective, ESTACK, NX_FRAME; clear - Hp3; lia)).
    exact HapX. }
  (* the registers after the call: the callee keeps sp, gp, tp and s0..s11 *)
  assert (P2 : getr regs2 2 = getr (ms_regs msX) 2) by exact (HP2 2 ltac:(unfold acallee_saved; clear; lia)).
  assert (P3 : getr regs2 3 = getr (ms_regs msX) 3) by exact (HP2 3 ltac:(unfold acallee_saved; clear; lia)).
  assert (P4 : getr regs2 4 = getr (ms_regs msX) 4) by exact (HP2 4 ltac:(unfold acallee_saved; clear; lia)).
  assert (P8 : getr regs2 8 = getr (ms_regs msX) 8) by exact (HP2 8 ltac:(unfold acallee_saved; clear; lia)).
  assert (P9 : getr regs2 9 = getr (ms_regs msX) 9) by exact (HP2 9 ltac:(unfold acallee_saved; clear; lia)).
  assert (P18 : getr regs2 18 = getr (ms_regs msX) 18)
    by exact (HP2 18 ltac:(unfold acallee_saved; clear; lia)).
  assert (P19 : getr regs2 19 = getr (ms_regs msX) 19)
    by exact (HP2 19 ltac:(unfold acallee_saved; clear; lia)).
  assert (P20 : getr regs2 20 = getr (ms_regs msX) 20)
    by exact (HP2 20 ltac:(unfold acallee_saved; clear; lia)).
  assert (P21 : getr regs2 21 = getr (ms_regs msX) 21)
    by exact (HP2 21 ltac:(unfold acallee_saved; clear; lia)).
  assert (P22 : getr regs2 22 = getr (ms_regs msX) 22)
    by exact (HP2 22 ltac:(unfold acallee_saved; clear; lia)).
  assert (P23 : getr regs2 23 = getr (ms_regs msX) 23)
    by exact (HP2 23 ltac:(unfold acallee_saved; clear; lia)).
  assert (P24 : getr regs2 24 = getr (ms_regs msX) 24)
    by exact (HP2 24 ltac:(unfold acallee_saved; clear; lia)).
  assert (P25 : getr regs2 25 = getr (ms_regs msX) 25)
    by exact (HP2 25 ltac:(unfold acallee_saved; clear; lia)).
  assert (P26 : getr regs2 26 = getr (ms_regs msX) 26)
    by exact (HP2 26 ltac:(unfold acallee_saved; clear; lia)).
  assert (P27 : getr regs2 27 = getr (ms_regs msX) 27)
    by exact (HP2 27 ltac:(unfold acallee_saved; clear; lia)).
  rewrite R2X in P2. rewrite R3X in P3. rewrite R4X in P4. rewrite R8X in P8. rewrite R9X in P9.
  rewrite R18X in P18. rewrite R19X in P19. rewrite R20X in P20. rewrite R21X in P21.
  rewrite R22X in P22. rewrite R23X in P23. rewrite R24X in P24. rewrite R25X in P25.
  rewrite R26X in P26. rewrite R27X in P27.
  rewrite R1X.
  change (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + EMR)) mem2 (seg_rom SEGS)) md2)
    with (cfg_at SEGS (BASE + EMR) regs2 mem2 md2).
  exact (em_tail STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regs2 (ms_mem msX) mem2 md2
           tx chp parp valp T j _ _ HCTX Hj3 HMOD HSAMEX HP1 HJ2 HK
           ltac:(unfold NX_STK, STK_reac_headamp_tx_next, NX_FRAME; clear; lia) ltac:(clear; lia)
           (HT2 ltac:(clear - Hg4096; lia)) HSAV2 Hpv2 Hrav2 Hac2 Hap2
           P2 P3 P4 P27 P8 P9 Ha0 P18 P22 P19 P23 P20 P24 P21 P25 P26).
Qed.

End H.
End F.
End D.
