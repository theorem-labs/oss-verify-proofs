(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACfk.v:174-178
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACh9.v:103-105, 131-135 [Apache-2.0];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YCcc.v:33-37 [Apache-2.0 OR MIT], for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/YC86.v:38-42 [Apache-2.0 OR MIT]. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput_seg_D5.v, with its module paths, module names and numbers changed; 1675 of its 1805 lines of code are new or changed and 1207 lines of the source are left out. *)
(* seg_D3 of the build-B (fuzz_identity.asan-ubsan) walk of LLVMFuzzerTestOneInput (0x80774): the REAC-version
   case of the record loop, listing slots +0x888 .. +0xe24 (0x80ffc .. 0x81598), from inv_caseV to inv_tail
   (LLVMFuzzerTestOneInput_inv.v, seg_D3_stmt).

   What the case does (the neutral listing of fuzz_identity.asan-ubsan): it checks the record length (s6 >= 8) and the
   identity's has-version byte (a0), compares the identity's 8 raw version bytes with the payload (bcmp at
   0x8101c), compares the three 16-bit big-endian payload fields with the decoded major/minor/patch (s8, s9, s5;
   UBSan traps 0x81038, 0x81084, 0x810d0 are the pointer-overflow checks of pl + 3, pl + 5, pl + 7), unpoisons
   the shadow of `v` (SF+224, 20 bytes) and `ev` (SF+288, 24 bytes), builds "ma.mi" and pa (two digits at
   least) in `ev` with put_dec (0x81144, 0x81190, 0x811a4; the counter at mf+208; UBSan traps 0x8115c, 0x81168,
   0x811b4, 0x811c0 bound the counter), calls reac_identity_reac_ver_str into `v` (0x811e8), compares the two
   (bcmp at 0x81208), copies the 8 payload bytes into `hw` (0x81284 .. 0x8128c), poisons `v` and `ev` again
   and sets hw.have (mf+24) to 1.

   The walk is the plain symbolic engine (IdentBFrame.v SRr_run_pi_AJ / SRr_run_to_pi_AJ, YC45.v
   SRr_run_pi_AJ_call): every load hits a known chunk, the payload's shadow byte is a known chunk (0, from the
   block's shadow law), and the shadow address arithmetic and the three field compares are aliases. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentBase IdentRo YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require put_dec reac_identity_reac_ver_str.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import LLVMFuzzerTestOneInput_seg_D3_hand_stmt.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require LLVMFuzzerTestOneInput_seg_D3_hand
  LLVMFuzzerTestOneInput_seg_D3_tl.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec put_dec_c
write_uint_c reac_identity_reac_ver_str_c.
Import ListNotations.
(* reac_box_name_seg_*.v set lia's euclidean-division flag to false for every file that loads reac_box_name
   (through the contract); this file was proved with it on, so it turns it back on. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the symbolic state at +0x888 ------------------------------------------------------------------------ *)
(* Atoms 0..31 are the registers (x9 = s1 = mf, x22 = s6 = the payload length, x27 = s11 = the payload copy pl,
   x10 = a0 = the identity's has-version byte, x24 / x25 / x21 = s8 / s9 / s5 = major / minor / patch). The
   extra atoms (d3_vals): 32 the shadow offset; 33 SF+432 (&hw); 34 SF+224 (v); 35 the 64-bit complement of
   SF+288 (mf+56, the UBSan bound of `ev`); 36 SF+288 (ev); 37 SF+380 (id+28); 38 the frame's shadow address;
   39 SF+352 (id); 40 pl / 8; 41 the shadow address of pl; 42..49 the 8 payload bytes; 50 the counter after the
   first put_dec (d1); 51 d1 + 1; 52 after the second; 53 after the third (n3); 54 ev + d1 (the '.'); 55
   ev + n3 (the NUL). *)
Definition d3_ch (o : Z) (w : N) (v : sv) : YP09.chunk := YP09.mkChunk o (CVal w v).
Definition d3_rmf_hw : YP09.region := YP09.mkRegion (Some 9%nat) 24 32 24 32 [].
Definition d3_rmf_ro : YP09.region :=
  YP09.mkRegion (Some 9%nat) 32 192 0 0
    [d3_ch 32 8 (SOff 33 0); d3_ch 48 8 (SOff 34 0); d3_ch 56 8 (SOff 35 0); d3_ch 72 8 (SOff 36 0);
     d3_ch 104 8 (SOff 37 0); d3_ch 160 8 (SOff 38 0); d3_ch 168 8 (SOff 32 0); d3_ch 184 8 (SOff 39 0)].
Definition d3_rmf_n (cs : list YP09.chunk) : YP09.region := YP09.mkRegion (Some 9%nat) 208 216 208 216 cs.
Definition d3_rhw : YP09.region := YP09.mkRegion (Some 33%nat) 4 12 4 12 [].
Definition d3_rid : YP09.region :=
  YP09.mkRegion (Some 39%nat) 22 28 0 0 [d3_ch 22 2 (SOff 24 0); d3_ch 24 2 (SOff 25 0); d3_ch 26 2 (SOff 21 0)].
Definition d3_rshv : YP09.region := YP09.mkRegion (Some 38%nat) 28 31 28 31 [].
Definition d3_rshe : YP09.region := YP09.mkRegion (Some 38%nat) 36 39 36 39 [].
Definition d3_rpl : YP09.region :=
  YP09.mkRegion (Some 27%nat) 0 8 0 0
    [d3_ch 0 1 (SOff 42 0); d3_ch 1 1 (SOff 43 0); d3_ch 2 1 (SOff 44 0); d3_ch 3 1 (SOff 45 0);
     d3_ch 4 1 (SOff 46 0); d3_ch 5 1 (SOff 47 0); d3_ch 6 1 (SOff 48 0); d3_ch 7 1 (SOff 49 0)].
Definition d3_rpsh : YP09.region := YP09.mkRegion (Some 41%nat) 0 1 0 0 [d3_ch 0 1 (SLit 0)].
Definition d3_rdot : YP09.region := YP09.mkRegion (Some 54%nat) 0 1 0 1 [].
Definition d3_rnul : YP09.region := YP09.mkRegion (Some 55%nat) 0 1 0 1 [].
Definition d3_rs : smem :=
  [d3_rmf_hw; d3_rmf_ro; d3_rmf_n []; d3_rhw; d3_rid; d3_rshv; d3_rshe; d3_rpl; d3_rpsh; d3_rdot; d3_rnul].
Definition d3_atoms : list (nat * afact) :=
  [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5);
    (10%nat, mkAF 1 1 0); (22%nat, mkAF 8 255 0); (27%nat, mkAF 4096 140737479966720 4);
    (24%nat, mkAF 0 65535 0); (25%nat, mkAF 0 65535 0); (21%nat, mkAF 0 65535 0);
    (32%nat, mkAF 0x7fff8000 0x7fff8000 0); (35%nat, mkAF (2 ^ 63) (2 ^ 64 - 1) 0);
    (42%nat, mkAF 0 255 0); (43%nat, mkAF 0 255 0); (44%nat, mkAF 0 255 0); (45%nat, mkAF 0 255 0);
    (46%nat, mkAF 0 255 0); (47%nat, mkAF 0 255 0); (48%nat, mkAF 0 255 0); (49%nat, mkAF 0 255 0);
    (50%nat, mkAF 1 5 0); (53%nat, mkAF 4 16 0) ].
Definition d3_srl (c : Z) : sv * sv := (SAlu ALU_SRL (SOff 27 c) (SLit 3), SOff 40 0).
Definition d3_be16 (hi lo dst : nat) : sv * sv := (SAlu ALU_OR (SAlu ALU_SLL (SOff hi 0) (SLit 8)) (SOff lo 0), SOff dst 0).
Definition d3_alias : list (sv * sv) :=
  [ d3_srl 0; d3_srl 2; d3_srl 3; d3_srl 4; d3_srl 5; d3_srl 6; d3_srl 7;
    (SAlu ALU_ADD (SOff 40 0) (SOff 32 0), SOff 41 0);
    d3_be16 44 45 24; d3_be16 46 47 25; d3_be16 48 49 21;
    (SAlu ALU_ADD (SOff 36 0) (SOff 50 0), SOff 54 0); (SAlu ALU_ADD (SOff 36 0) (SOff 53 0), SOff 55 0) ].
Definition d3_G : facts := mkFacts d3_atoms [] d3_alias.
Definition d3_ss0 : sstate := mkSS 0x888 sr_atoms d3_rs None d3_G.

(* ---- small arithmetic ------------------------------------------------------------------------------------ *)
Lemma d3_le_byte_mod : forall z w k, YO0f.le_byte (z mod 2 ^ (8 * Z.of_nat w)) w k = YO0f.le_byte z w k.
Proof. intros z w k. unfold YO0f.le_byte. rewrite Z.mod_mod by (apply Z.pow_nonzero; lia). reflexivity. Qed.
Lemma d3_lnot64 : forall x, 0 <= x < 2 ^ 64 -> Z.lnot x mod 2 ^ 64 = 2 ^ 64 - 1 - x.
Proof.
intros x Hx. assert (E : Z.lnot x = (2 ^ 64 - 1 - x) + (-1) * 2 ^ 64) by (unfold Z.lnot; lia).
rewrite E, Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

(* ---- the model of the case (the plain files) --------------------------------------------------------------- *)
Lemma d3_bz_zb : forall x, RcIdentModel.bz (RcIdentModel.zb x) = x mod 256.
Proof. intros x. unfold RcIdentModel.bz, RcIdentModel.zb. rewrite Z_to_bv_unsigned. reflexivity. Qed.

Lemma d3_le16 : forall v, 0 <= v < 65536 ->
  RcIdentModel.bz (nth 0 (RcIdentModel.le16 v) (RcIdentModel.zb 0)) +
  256 * RcIdentModel.bz (nth 1 (RcIdentModel.le16 v) (RcIdentModel.zb 0)) = v.
Proof. intros v Hv. unfold RcIdentModel.le16. cbn [nth]. rewrite !d3_bz_zb. Z.div_mod_to_equations. lia. Qed.

Definition d3_U (l r A M C : list byte) : list byte :=
  RcIdentModel.upd (RcIdentModel.upd (RcIdentModel.upd (RcIdentModel.upd (RcIdentModel.upd l 28 r) 22 A) 24 M)
    26 C) 36 [RcIdentModel.zb 1].

Lemma d3_nth_ver : forall (l r A M C : list byte) j,
  length l = 38%nat -> length r = 8%nat -> length A = 2%nat -> length M = 2%nat -> length C = 2%nat -> (j < 2)%nat ->
  RcIdentModel.nthb (d3_U l r A M C) (22 + j) = nth j A (RcIdentModel.zb 0) /\
  RcIdentModel.nthb (d3_U l r A M C) (24 + j) = nth j M (RcIdentModel.zb 0) /\
  RcIdentModel.nthb (d3_U l r A M C) (26 + j) = nth j C (RcIdentModel.zb 0).
Proof.
  intros l r A M C j Hl Hr HA HM HC Hj. unfold d3_U, RcIdentModel.nthb.
  assert (L1 : length (RcIdentModel.upd l 28 r) = 38%nat) by (rewrite RcIdentModel.upd_length; lia).
  assert (L2 : length (RcIdentModel.upd (RcIdentModel.upd l 28 r) 22 A) = 38%nat)
    by (rewrite RcIdentModel.upd_length; lia).
  assert (L3 : length (RcIdentModel.upd (RcIdentModel.upd (RcIdentModel.upd l 28 r) 22 A) 24 M) = 38%nat)
    by (rewrite RcIdentModel.upd_length; lia).
  assert (L4 : length (RcIdentModel.upd (RcIdentModel.upd (RcIdentModel.upd (RcIdentModel.upd l 28 r) 22 A) 24 M)
    26 C) = 38%nat) by (rewrite RcIdentModel.upd_length; lia).
  split; [|split].
  - rewrite SlotModel.nth_upd_before by lia. rewrite SlotModel.nth_upd_before by lia.
    rewrite SlotModel.nth_upd_before by lia. rewrite SlotModel.nth_upd_in by lia. f_equal. lia.
  - rewrite SlotModel.nth_upd_before by lia. rewrite SlotModel.nth_upd_before by lia.
    rewrite SlotModel.nth_upd_in by lia. f_equal. lia.
  - rewrite SlotModel.nth_upd_before by lia. rewrite SlotModel.nth_upd_in by lia. f_equal. lia.
Qed.

Lemma d3_vb : forall inp i, SlotModel.rec_r inp i = 1 -> SlotModel.rec_addr inp i = RcIdentModel.ADDR_REAC_VERSION ->
  (8 <= length (SlotModel.rec_pl inp i))%nat /\
  RcIdentModel.has_reac_version (SlotModel.rec_id inp (S i)) = 1 /\
  RcIdentModel.raw (SlotModel.rec_id inp (S i)) = firstn 8 (SlotModel.rec_pl inp i) /\
  RcIdentModel.major (SlotModel.rec_id inp (S i)) =
    RcIdentModel.be16 (RcIdentModel.nthb (SlotModel.rec_pl inp i) 2) (RcIdentModel.nthb (SlotModel.rec_pl inp i) 3) /\
  RcIdentModel.minor (SlotModel.rec_id inp (S i)) =
    RcIdentModel.be16 (RcIdentModel.nthb (SlotModel.rec_pl inp i) 4) (RcIdentModel.nthb (SlotModel.rec_pl inp i) 5) /\
  RcIdentModel.patch (SlotModel.rec_id inp (S i)) =
    RcIdentModel.be16 (RcIdentModel.nthb (SlotModel.rec_pl inp i) 6) (RcIdentModel.nthb (SlotModel.rec_pl inp i) 7).
Proof.
  intros inp i Hr Ha. unfold SlotModel.rec_r in Hr. cbn [SlotModel.rec_id]. rewrite Ha in *.
  pose proof (SlotModel.rec_id_length inp i) as Hl.
  destruct (Nat.lt_ge_cases (length (SlotModel.rec_pl inp i)) 8) as [Hs|Hs].
  { rewrite (SlotModel.ING_ver_short _ _ Hs) in Hr. cbn [fst] in Hr. discriminate. }
  destruct (SlotModel.ING_ver_long _ _ Hl Hs) as (H1 & H2 & _).
  split; [exact Hs|]. split; [exact H1|]. split; [exact H2|].
  rewrite SlotModel.ING_ver_dispatch. unfold RcIdentModel.ing_version.
  destruct (Nat.leb_spec RcIdentModel.REAC_VER_LEN (length (SlotModel.rec_pl inp i))) as [E|E];
    [|unfold RcIdentModel.REAC_VER_LEN in E; lia].
  cbn [snd]. unfold RcIdentModel.OFF_RAW, RcIdentModel.OFF_MAJOR, RcIdentModel.OFF_MINOR, RcIdentModel.OFF_PATCH,
    RcIdentModel.OFF_HAS_VER, RcIdentModel.REAC_VER_LEN.
  set (pv := SlotModel.rec_pl inp i) in *.
  assert (Hr8 : length (firstn 8 pv) = 8%nat) by (rewrite length_firstn; lia).
  destruct (d3_nth_ver (SlotModel.rec_id inp i) (firstn 8 pv)
    (RcIdentModel.le16 (RcIdentModel.be16 (RcIdentModel.nthb pv 2) (RcIdentModel.nthb pv 3)))
    (RcIdentModel.le16 (RcIdentModel.be16 (RcIdentModel.nthb pv 4) (RcIdentModel.nthb pv 5)))
    (RcIdentModel.le16 (RcIdentModel.be16 (RcIdentModel.nthb pv 6) (RcIdentModel.nthb pv 7))) 0
    Hl Hr8 eq_refl eq_refl eq_refl ltac:(lia)) as (A0 & M0 & C0).
  destruct (d3_nth_ver (SlotModel.rec_id inp i) (firstn 8 pv)
    (RcIdentModel.le16 (RcIdentModel.be16 (RcIdentModel.nthb pv 2) (RcIdentModel.nthb pv 3)))
    (RcIdentModel.le16 (RcIdentModel.be16 (RcIdentModel.nthb pv 4) (RcIdentModel.nthb pv 5)))
    (RcIdentModel.le16 (RcIdentModel.be16 (RcIdentModel.nthb pv 6) (RcIdentModel.nthb pv 7))) 1
    Hl Hr8 eq_refl eq_refl eq_refl ltac:(lia)) as (A1 & M1 & C1).
  unfold d3_U in A0, M0, C0, A1, M1, C1. cbn [Nat.add] in A0, M0, C0, A1, M1, C1.
  unfold RcIdentModel.major, RcIdentModel.minor, RcIdentModel.patch.
  rewrite A0, A1, M0, M1, C0, C1.
  pose proof (SlotModel.bz_range (RcIdentModel.nthb pv 2)). pose proof (SlotModel.bz_range (RcIdentModel.nthb pv 3)).
  pose proof (SlotModel.bz_range (RcIdentModel.nthb pv 4)). pose proof (SlotModel.bz_range (RcIdentModel.nthb pv 5)).
  pose proof (SlotModel.bz_range (RcIdentModel.nthb pv 6)). pose proof (SlotModel.bz_range (RcIdentModel.nthb pv 7)).
  unfold RcIdentModel.be16. split; [|split]; apply d3_le16; lia.
Qed.

Lemma d3_ver : forall inp i, SlotModel.rec_r inp i = 1 -> SlotModel.rec_addr inp i = RcIdentModel.ADDR_REAC_VERSION ->
  8 <= SlotModel.rec_k inp i /\
  (8 <= length (SlotModel.rec_pl inp i))%nat /\
  RcIdentModel.has_reac_version (SlotModel.rec_id inp (S i)) = 1 /\
  RcIdentModel.raw (SlotModel.rec_id inp (S i)) = firstn 8 (SlotModel.rec_pl inp i) /\
  RcIdentModel.major (SlotModel.rec_id inp (S i)) =
    256 * RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl inp i) 2) + RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl inp i) 3) /\
  RcIdentModel.minor (SlotModel.rec_id inp (S i)) =
    256 * RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl inp i) 4) + RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl inp i) 5) /\
  RcIdentModel.patch (SlotModel.rec_id inp (S i)) =
    256 * RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl inp i) 6) + RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl inp i) 7).
Proof.
  intros inp i Hr Ha. destruct (d3_vb inp i Hr Ha) as (L & H1 & H2 & H3 & H4 & H5).
  assert (Hk : 8 <= SlotModel.rec_k inp i).
  { clear -L. pose proof (SlotModel.rec_pl_length inp i) as E. pose proof (SlotModel.rec_k_range inp i). lia. }
  unfold RcIdentModel.be16 in H3, H4, H5.
  split; [exact Hk|]. split; [exact L|]. split; [exact H1|]. split; [exact H2|].
  split; [rewrite H3; ring|]. split; [rewrite H4; ring|]. rewrite H5; ring.
Qed.

Lemma d3_hw : forall inp i, SlotModel.rec_r inp i = 1 -> SlotModel.rec_addr inp i = RcIdentModel.ADDR_REAC_VERSION ->
  SlotModel.rec_have inp (S i) = 1 /\ SlotModel.rec_hwb inp (S i) = firstn 8 (SlotModel.rec_pl inp i).
Proof.
  intros inp i Hr Ha. destruct (d3_ver inp i Hr Ha) as (Hk & _).
  unfold SlotModel.rec_have, SlotModel.rec_hwb. cbn [SlotModel.rec_hw].
  rewrite Ha, Z.eqb_refl. destruct (Z.leb_spec 8 (SlotModel.rec_k inp i)) as [_|E]; [|lia].
  split; reflexivity.
Qed.

Lemma d3_mmp : forall idb, 0 <= RcIdentModel.major idb < 65536 /\ 0 <= RcIdentModel.minor idb < 65536 /\
  0 <= RcIdentModel.patch idb < 65536.
Proof.
  intros idb. unfold RcIdentModel.major, RcIdentModel.minor, RcIdentModel.patch.
  pose proof (SlotModel.bz_range (RcIdentModel.nthb idb 22)). pose proof (SlotModel.bz_range (RcIdentModel.nthb idb 23)).
  pose proof (SlotModel.bz_range (RcIdentModel.nthb idb 24)). pose proof (SlotModel.bz_range (RcIdentModel.nthb idb 25)).
  pose proof (SlotModel.bz_range (RcIdentModel.nthb idb 26)). pose proof (SlotModel.bz_range (RcIdentModel.nthb idb 27)).
  lia.
Qed.

Lemma d3_dec_all : IdentSpec.z_all (fun v => IdentSpec.bytes_eqb (IdentSpec.DEC v 1) (write_uint_c.write_uint_D v) &&
    IdentSpec.bytes_eqb (IdentSpec.DEC v 2) (reac_identity_reac_ver_str_c.reac_ver_str_DEC2 v)) (Z.to_nat 65536) 0 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma d3_dec : forall v, 0 <= v < 65536 ->
  IdentSpec.DEC v 1 = write_uint_c.write_uint_D v /\ IdentSpec.DEC v 2 = reac_identity_reac_ver_str_c.reac_ver_str_DEC2 v.
Proof.
  intros v Hv. pose proof (IdentSpec.z_all_spec _ _ _ d3_dec_all v ltac:(rewrite Z2Nat.id by lia; lia)) as H.
  cbv beta in H. apply andb_true_iff in H as [H1 H2]. split; apply IdentSpec.bytes_eqb_eq; assumption.
Qed.

Lemma d3_lsd_len : forall k v, (length (write_uint_c.write_uint_lsd k v) <= k)%nat.
Proof.
  induction k as [|k IH]; intros v; cbn [write_uint_c.write_uint_lsd length]; [lia|].
  destruct (v <? 10); cbn [length]; [lia|]. specialize (IH (v / 10)). lia.
Qed.

Lemma d3_lsd_ge1 : forall k v, (1 <= length (write_uint_c.write_uint_lsd (S k) v))%nat.
Proof. intros k v. cbn [write_uint_c.write_uint_lsd length]. lia. Qed.

Lemma d3_lsd_ge2 : forall k v, 10 <= v -> (2 <= length (write_uint_c.write_uint_lsd (S (S k)) v))%nat.
Proof.
  intros k v Hv. cbn [write_uint_c.write_uint_lsd]. destruct (Z.ltb_spec v 10) as [E|_]; [lia|].
  cbn [length]. lia.
Qed.

Lemma d3_D2_len : forall v, (2 <= length (reac_identity_reac_ver_str_c.reac_ver_str_DEC2 v) <= 5)%nat.
Proof.
  intros v. unfold reac_identity_reac_ver_str_c.reac_ver_str_DEC2.
  destruct (Z.ltb_spec v 10) as [E|E]; [cbn [length]; lia|].
  unfold write_uint_c.write_uint_D. rewrite length_rev.
  pose proof (d3_lsd_len 5 v). pose proof (d3_lsd_ge2 3 v E). lia.
Qed.

Lemma d3_dec_len : forall v, 0 <= v < 65536 ->
  1 <= put_dec_c.dec_len v 1 <= 5 /\ 2 <= put_dec_c.dec_len v 2 <= 5.
Proof.
  intros v Hv. destruct (d3_dec v Hv) as [D1 D2]. unfold put_dec_c.dec_len. rewrite D1, D2.
  pose proof (d3_D2_len v) as L2.
  assert (L1 : (1 <= length (write_uint_c.write_uint_D v) <= 5)%nat).
  { unfold write_uint_c.write_uint_D. rewrite length_rev.
    pose proof (d3_lsd_len 5 v). pose proof (d3_lsd_ge1 4 v). lia. }
  clear -L1 L2. lia.
Qed.

Lemma d3_ev : forall ma mi pa, 0 <= ma < 65536 -> 0 <= mi < 65536 -> 0 <= pa < 65536 ->
  IdentSpec.DEC ma 1 ++ [Z_to_bv 8 46] ++ IdentSpec.DEC mi 1 ++ IdentSpec.DEC pa 2 =
    reac_identity_reac_ver_str_c.reac_ver_str_VER ma mi pa /\
  put_dec_c.dec_len ma 1 + 1 + put_dec_c.dec_len mi 1 + put_dec_c.dec_len pa 2 =
    reac_identity_reac_ver_str_c.reac_ver_str_LV ma mi pa.
Proof.
  intros ma mi pa Ha Hi Hp.
  destruct (d3_dec ma Ha) as [A1 _]. destruct (d3_dec mi Hi) as [A2 _]. destruct (d3_dec pa Hp) as [_ A3].
  assert (E : IdentSpec.DEC ma 1 ++ [Z_to_bv 8 46] ++ IdentSpec.DEC mi 1 ++ IdentSpec.DEC pa 2 =
    reac_identity_reac_ver_str_c.reac_ver_str_VER ma mi pa).
  { unfold reac_identity_reac_ver_str_c.reac_ver_str_VER. rewrite A1, A2, A3. reflexivity. }
  split; [exact E|].
  unfold put_dec_c.dec_len, reac_identity_reac_ver_str_c.reac_ver_str_LV. rewrite <- E.
  rewrite !length_app. cbn [length]. lia.
Qed.

Lemma d3_rec_k_len : forall inp i, Z.of_nat (length (SlotModel.rec_pl inp i)) = SlotModel.rec_k inp i.
Proof.
  intros inp i. rewrite SlotModel.rec_pl_length. pose proof (SlotModel.rec_k_range inp i). lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
(* The Section of the contract (LLVMFuzzerTestOneInput.v), the variables seg_D3_stmt is stated over. *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
#[local] Notation ECOMMON := (ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).

(* ---- the values of the extra atoms ------------------------------------------------------------------------ *)
Definition d3_pb (g : ectx) (i j : nat) : Z := RcIdentModel.bz (RcIdentModel.nthb (SlotModel.rec_pl (e_pl g) i) j).
Definition d3_ma (g : ectx) (i : nat) : Z := RcIdentModel.major (m_id g (S i)).
Definition d3_mi (g : ectx) (i : nat) : Z := RcIdentModel.minor (m_id g (S i)).
Definition d3_pa (g : ectx) (i : nat) : Z := RcIdentModel.patch (m_id g (S i)).
Definition d3_d1 (g : ectx) (i : nat) : Z := put_dec_c.dec_len (d3_ma g i) 1.
Definition d3_n2 (g : ectx) (i : nat) : Z := d3_d1 g i + 1 + put_dec_c.dec_len (d3_mi g i) 1.
Definition d3_n3 (g : ectx) (i : nat) : Z := d3_n2 g i + put_dec_c.dec_len (d3_pa g i) 2.
Definition d3_vals (g : ectx) (pos : Z) (i : nat) (pl : Z) : list Z :=
  [SHADOW_OFF; SFa g pos + 432; SFa g pos + 224; 2 ^ 64 - 1 - (SFa g pos + 288); SFa g pos + 288;
   SFa g pos + 380; shadow_addr (SFa g pos); SFa g pos + 352; pl / 8; SHADOW_OFF + pl / 8;
   d3_pb g i 0; d3_pb g i 1; d3_pb g i 2; d3_pb g i 3; d3_pb g i 4; d3_pb g i 5; d3_pb g i 6; d3_pb g i 7;
   d3_d1 g i; d3_d1 g i + 1; d3_n2 g i; d3_n3 g i; SFa g pos + 288 + d3_d1 g i; SFa g pos + 288 + d3_n3 g i].
Definition d3_E (g : ectx) (pos : Z) (i : nat) (pl : Z) (regs : bvmap 5 word) : env :=
  Eimg (Ereg regs (map (Z_to_bv 64) (d3_vals g pos i pl))).
(* The registers the switch leaves for the case (seg_D2, 0x80e10 .. 0x80e70), as inv_caseV states them. *)
Definition d3_regs (g : ectx) (i : nat) (regs2 : bvmap 5 word) : Prop :=
  getr regs2 10 = w64 (RcIdentModel.has_reac_version (m_id g (S i))) /\
  getr regs2 24 = w64 (d3_ma g i) /\ getr regs2 25 = w64 (d3_mi g i) /\ getr regs2 21 = w64 (d3_pa g i).

Lemma d3_ew_extra : forall g pos i pl regs j, (j < 24)%nat ->
  ew (d3_E g pos i pl regs) (32 + j) = Z_to_bv 64 (nth j (d3_vals g pos i pl) 0).
Proof.
intros g pos i pl regs j Hj. unfold d3_E. rewrite Eimg_low by (unfold A_TEXT; lia).
rewrite ew_Ereg_extra. change (Z_to_bv 64 0) with (Z_to_bv 64 0 : word).
rewrite <- (map_nth (Z_to_bv 64) (d3_vals g pos i pl) 0 j). reflexivity.
Qed.
Lemma d3_ew_reg : forall g pos i pl regs n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (d3_E g pos i pl regs) n = getr regs r.
Proof. intros g pos i pl regs n r Hn. unfold d3_E. apply ew_Eimg_Ereg_nat. exact Hn. Qed.

(* ---- bytes and words ------------------------------------------------------------------------------------- *)
Lemma d3_lor_shift : forall a b k, 0 <= k -> 0 <= a -> 0 <= b < 2 ^ k -> Z.lor (Z.shiftl a k) b = a * 2 ^ k + b.
Proof.
intros a b k Hk Ha Hb.
assert (Hs : Z.shiftl a k = a * 2 ^ k) by (apply Z.shiftl_mul_pow2; lia).
assert (Hland : Z.land (Z.shiftl a k) b = 0).
{ apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.ltb_spec n k) as [E|E].
  - rewrite Hs, Z.mul_pow2_bits_low by lia. reflexivity.
  - replace (Z.testbit b n) with false; [apply andb_false_r|].
    symmetry. apply Z.testbit_false; [lia|]. rewrite Z.div_small; [reflexivity|].
    split; [lia|]. eapply Z.lt_le_trans; [apply Hb|]. apply Z.pow_le_mono_r; lia. }
rewrite <- Z.lxor_lor by exact Hland. rewrite <- Z.add_nocarry_lxor by exact Hland. rewrite Hs. reflexivity.
Qed.
Lemma d3_vm1 : forall H (m : word -> option byte) a v,
  aview SEGS H m a = Some v -> val_mem SEGS (mrestrict H m) a 1 v.
Proof.
intros H m a v Hv k Hk. assert (k = 0%nat) by lia. subst k. rewrite Z.add_0_r.
unfold aview in Hv. destruct (mbyte SEGS (mrestrict H m) a) as [b|] eqn:Eb; [|discriminate].
cbn [option_map] in Hv. injection Hv as <-. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. pose proof (bv_unsigned_in_range 8 b) as Hr. unfold bv_wrap.
change (bv_modulus 8) with 256 in *. change (2 ^ 8) with 256.
repeat rewrite (Z.mod_small (bv_unsigned b) 256) by lia. reflexivity.
Qed.
Lemma d3_vm2 : forall m a b0 b1, val_mem SEGS m a 1 b0 -> val_mem SEGS m (a + 1) 1 b1 ->
  0 <= b0 < 256 -> 0 <= b1 < 256 -> val_mem SEGS m a 2 (b0 + 256 * b1).
Proof.
intros m a b0 b1 H0 H1 R0 R1 k Hk.
unfold YO0f.le_byte in *. assert (k = 0 \/ k = 1)%nat as [-> | ->] by lia.
- specialize (H0 0%nat ltac:(lia)). rewrite H0. f_equal. f_equal. unfold YO0f.le_byte.
  change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 2) with 16. change (8 * Z.of_nat 0) with 0.
  rewrite !Z.shiftr_0_r. Z.div_mod_to_equations. lia.
- specialize (H1 0%nat ltac:(lia)). replace (a + Z.of_nat 1) with (a + 1 + Z.of_nat 0) by lia. rewrite H1.
  f_equal. f_equal. unfold YO0f.le_byte.
  change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 2) with 16. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r, Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. change (2 ^ 16) with 65536.
  Z.div_mod_to_equations. lia.
Qed.
Lemma d3_vm_lnot : forall m a x, 0 <= x < 2 ^ 64 ->
  val_mem SEGS m a 8 (Z.lnot x) -> val_mem SEGS m a 8 (2 ^ 64 - 1 - x).
Proof.
intros m a x Hx H k Hk. rewrite (H k Hk). rewrite <- (d3_le_byte_mod (Z.lnot x) 8 k).
change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite d3_lnot64 by lia. reflexivity.
Qed.
Lemma d3_garr8_vm1 : forall m a l j, garr8 SEGS m a (map (fun b : byte => bv_unsigned b) l) -> (j < length l)%nat ->
  val_mem SEGS m (a + Z.of_nat j) 1 (RcIdentModel.bz (RcIdentModel.nthb l j)) /\
  0 <= RcIdentModel.bz (RcIdentModel.nthb l j) < 256.
Proof.
intros m a l j H Hj. rewrite <- length_map with (f := fun b : byte => bv_unsigned b) in Hj.
destruct (H j Hj) as [Hv Hr].
assert (Ed : nth j (map (fun b : byte => bv_unsigned b) l) 0 = RcIdentModel.bz (RcIdentModel.nthb l j)).
{ unfold RcIdentModel.nthb, RcIdentModel.bz. exact (map_nth (fun b : byte => bv_unsigned b) l (RcIdentModel.zb 0) j). }
rewrite Ed in Hv, Hr. exact (conj Hv Hr).
Qed.
Lemma d3_denot : forall E n v, bv_unsigned (ew E n) = v -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v Hv. apply bv_eq. rewrite denot_SOff, Hv, Z.add_0_r. rewrite unsigned_lit. reflexivity. Qed.
Lemma d3_denotc : forall E n v c, bv_unsigned (ew E n) = v -> sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof. intros E n v c Hv. apply bv_eq. rewrite denot_SOff, Hv. rewrite unsigned_lit. reflexivity. Qed.
(* The frame address is the entry layout's in every state of the journal (layout_le keeps ly_F). *)
Lemma d3_fa : forall STK sp0 FP ly S W0 mem md own ly' S' W' mem' md' k,
  ajournal SEGS B STK sp0 FP ly S W0 mem md own ly' S' W' mem' md' k ->
  forall cid pos, frame_addr ly' cid pos = frame_addr ly cid pos.
Proof.
intros STK sp0 FP ly S W0 mem md own ly' S' W' mem' md' k (_ & Hly & _) cid pos.
unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & E1 & _). rewrite E1. reflexivity.
Qed.

(* ---- the start state holds -------------------------------------------------------------------------------- *)
Ltac d3u EX j v := let Hx := fresh "Hx" in pose proof (EX j ltac:(lia)) as Hx; cbn [Nat.add] in Hx; rewrite Hx; clear Hx;
  change (nth j _ 0) with v; apply unsigned_lit_small.
Hypothesis LAWS : AR_laws SEGS B.
Lemma d3_entry : forall g pos mf i pl (W2 : world SEGS) (regs2 : bvmap 5 word) mem2 ly2 S2 md2
  STK sp0 FP ly Sx W0 mem0 md0 own k,
  ajournal SEGS B STK sp0 FP ly Sx W0 mem0 md0 own ly2 S2 W2 mem2 md2 k ->
  frame_addr ly2 4 pos = SFa g pos -> In (4, pos) (frames S2) ->
  In (pl, SlotModel.rec_k (e_pl g) i) (ablocks B ly2 S2) ->
  sp0 - STK <= mf -> mf + 216 <= sp0 -> 2 ^ 46 <= mf <= 2 ^ 47 - 216 -> mf mod 32 = 0 -> alloc_ceiling + 8192 <= mf ->
  getr regs2 2 = w64 mf -> getr regs2 9 = w64 mf ->
  getr regs2 22 = w64 (SlotModel.rec_k (e_pl g) i) -> getr regs2 27 = w64 pl -> d3_regs g i regs2 ->
  mf_fixed g pos mf W2 mem2 -> mf_id g pos mf W2 mem2 -> val_mem SEGS (rd W2 mem2) (mf + 168) 8 SHADOW_OFF ->
  bytes_at8 W2 mem2 pl (SlotModel.rec_pl (e_pl g) i) ->
  bytes_at8 W2 mem2 (SFa g pos + V_id) (m_id g (S i)) ->
  SlotModel.rec_r (e_pl g) i = 1 -> SlotModel.rec_addr (e_pl g) i = RcIdentModel.ADDR_REAC_VERSION ->
  st_ok_pi SEGS VAL (d3_E g pos i pl regs2) d3_ss0
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x888)) mem2 (seg_rom SEGS))).
Proof.
intros g pos mf i pl W2 regs2 mem2 ly2 S2 md2 STK sp0 FP ly Sx W0 mem0 md0 own k
  HJ HFA HIN HPL Hmf1 Hmf2 Hmf3 Hmf4 Hmf5 R2 R9 R22 R27 (R10 & R24 & R25 & R21) HMF HMID H168 HBPL HBID Hr Ha.
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
destruct (d3_ver (e_pl g) i Hr Ha) as (HK8 & HL8 & HHV & HRAW & HMA & HMI & HPA).
pose proof (SlotModel.rec_k_range (e_pl g) i) as HK.
pose proof (d3_rec_k_len (e_pl g) i) as HKL.
pose proof (SlotModel.rec_id_length (e_pl g) (S i)) as HIDL. unfold RcIdentModel.ID_SIZE in HIDL.
destruct (d3_mmp (m_id g (S i))) as (Ma & Mi & Mp).
change (RcIdentModel.major (m_id g (S i))) with (d3_ma g i) in Ma.
change (RcIdentModel.minor (m_id g (S i))) with (d3_mi g i) in Mi.
change (RcIdentModel.patch (m_id g (S i))) with (d3_pa g i) in Mp.
destruct (d3_dec_len (d3_ma g i) Ma) as (D1 & _). destruct (d3_dec_len (d3_mi g i) Mi) as (D2 & _).
destruct (d3_dec_len (d3_pa g i) Mp) as (_ & D3).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pl _ HAR HPL) as (Hp16 & Hp4096 & Hpceil & Happ & Hpbyt & _).
destruct (al_shadow _ _ LAWS _ _ _ _ _ pl _ HAR HPL) as (Hpsh & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 4 pos HAR HIN) as (Hf32 & Hfapp & Hfbyt & Hfsh).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 4 pos HAR HIN) as (Hf4096 & Hfceil & _).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ pl _ 4 pos HAR HPL HIN) as Hsep.
rewrite HFA in Hf32, Hfapp, Hfbyt, Hfsh, Hf4096, Hfceil, Hsep.
change (fs_frame_bytes 4) with 1024 in *. change (1024 / 8) with 128 in Hfsh.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
assert (Hreq : req_size (SlotModel.rec_k (e_pl g) i) = SlotModel.rec_k (e_pl g) i)
  by (unfold req_size; destruct (Z.eqb_spec (SlotModel.rec_k (e_pl g) i) 0); lia).
rewrite Hreq in Hpceil, Happ, Hpbyt, Hpsh, Hsep.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (F := SFa g pos) in *.
set (K := SlotModel.rec_k (e_pl g) i) in *.
set (E := d3_E g pos i pl regs2).
(* the atoms *)
assert (EX : forall j, (j < 24)%nat -> ew E (32 + j) = Z_to_bv 64 (nth j (d3_vals g pos i pl) 0))
  by (intros j Hj; apply d3_ew_extra; exact Hj).
assert (U9 : bv_unsigned (ew E 9) = mf).
{ subst E. rewrite (d3_ew_reg g pos i pl regs2 9 9%bv eq_refl), R9. apply unsigned_lit_small. lia. }
assert (U2 : bv_unsigned (ew E 2) = mf).
{ subst E. rewrite (d3_ew_reg g pos i pl regs2 2 2%bv eq_refl), R2. apply unsigned_lit_small. lia. }
assert (U27 : bv_unsigned (ew E 27) = pl).
{ subst E. rewrite (d3_ew_reg g pos i pl regs2 27 27%bv eq_refl), R27. apply unsigned_lit_small. lia. }
assert (U10 : bv_unsigned (ew E 10) = 1).
{ subst E. rewrite (d3_ew_reg g pos i pl regs2 10 10%bv eq_refl), R10. unfold m_id. rewrite HHV. reflexivity. }
assert (U22 : bv_unsigned (ew E 22) = K).
{ subst E. rewrite (d3_ew_reg g pos i pl regs2 22 22%bv eq_refl), R22. apply unsigned_lit_small. lia. }
assert (U24 : bv_unsigned (ew E 24) = d3_ma g i).
{ subst E. rewrite (d3_ew_reg g pos i pl regs2 24 24%bv eq_refl), R24. apply unsigned_lit_small. lia. }
assert (U25 : bv_unsigned (ew E 25) = d3_mi g i).
{ subst E. rewrite (d3_ew_reg g pos i pl regs2 25 25%bv eq_refl), R25. apply unsigned_lit_small. lia. }
assert (U21 : bv_unsigned (ew E 21) = d3_pa g i).
{ subst E. rewrite (d3_ew_reg g pos i pl regs2 21 21%bv eq_refl), R21. apply unsigned_lit_small. lia. }
assert (HF64 : F + 1024 <= 2 ^ 47) by (clear - Hfceil C1; lia).
assert (HP64 : pl + K <= 2 ^ 47) by (clear - Hpceil C1; lia).
assert (PB : forall j, (j < 8)%nat ->
  val_mem SEGS (rd W2 mem2) (pl + Z.of_nat j) 1 (d3_pb g i j) /\ 0 <= d3_pb g i j < 256).
{ intros j Hj. apply (d3_garr8_vm1 _ pl (SlotModel.rec_pl (e_pl g) i) j HBPL). clear - Hj HL8. lia. }
assert (U32 : bv_unsigned (ew E 32) = SHADOW_OFF) by (d3u EX 0%nat SHADOW_OFF; unfold SHADOW_OFF; lia).
assert (U33 : bv_unsigned (ew E 33) = F + 432) by (d3u EX 1%nat (F + 432); clear - Hf4096 HF64; lia).
assert (U34 : bv_unsigned (ew E 34) = F + 224) by (d3u EX 2%nat (F + 224); clear - Hf4096 HF64; lia).
assert (U35 : bv_unsigned (ew E 35) = 2 ^ 64 - 1 - (F + 288)) by (d3u EX 3%nat (2 ^ 64 - 1 - (F + 288)); clear - Hf4096 HF64; lia).
assert (U36 : bv_unsigned (ew E 36) = F + 288) by (d3u EX 4%nat (F + 288); clear - Hf4096 HF64; lia).
assert (U37 : bv_unsigned (ew E 37) = F + 380) by (d3u EX 5%nat (F + 380); clear - Hf4096 HF64; lia).
assert (U38 : bv_unsigned (ew E 38) = shadow_addr F)
  by (d3u EX 6%nat (shadow_addr F); unfold shadow_addr, SHADOW_OFF; clear - Hf4096 HF64; lia).
assert (U39 : bv_unsigned (ew E 39) = F + 352) by (d3u EX 7%nat (F + 352); clear - Hf4096 HF64; lia).
assert (U40 : bv_unsigned (ew E 40) = pl / 8)
  by (d3u EX 8%nat (pl / 8); clear - Hp4096 HP64 HK; Z.div_mod_to_equations; lia).
assert (U41 : bv_unsigned (ew E 41) = SHADOW_OFF + pl / 8)
  by (d3u EX 9%nat (SHADOW_OFF + pl / 8); unfold SHADOW_OFF; clear - Hp4096 HP64 HK; Z.div_mod_to_equations; lia).
assert (UP : forall j, (j < 8)%nat -> bv_unsigned (ew E (42 + j)) = d3_pb g i j).
{ intros j Hj. replace (42 + j)%nat with (32 + (10 + j))%nat by lia. rewrite (EX (10 + j)%nat ltac:(lia)).
  replace (nth (10 + j) (d3_vals g pos i pl) 0) with (d3_pb g i j)
    by (do 8 (destruct j as [|j]; [reflexivity|]); lia).
  apply unsigned_lit_small. pose proof (proj2 (PB j Hj)). lia. }
assert (U50 : bv_unsigned (ew E 50) = d3_d1 g i) by (d3u EX 18%nat (d3_d1 g i); unfold d3_d1 in *; lia).
assert (U53 : bv_unsigned (ew E 53) = d3_n3 g i) by (d3u EX 21%nat (d3_n3 g i); unfold d3_n3, d3_n2, d3_d1 in *; lia).
assert (U54 : bv_unsigned (ew E 54) = F + 288 + d3_d1 g i)
  by (d3u EX 22%nat (F + 288 + d3_d1 g i); unfold d3_d1 in *; clear - Hf4096 HF64 D1; lia).
assert (U55 : bv_unsigned (ew E 55) = F + 288 + d3_n3 g i)
  by (d3u EX 23%nat (F + 288 + d3_n3 g i); unfold d3_n3, d3_n2, d3_d1 in *; clear - Hf4096 HF64 D1 D2 D3; lia).
assert (HN3 : 4 <= d3_n3 g i <= 16) by (unfold d3_n3, d3_n2, d3_d1; clear - D1 D2 D3; lia).
assert (HD1 : 1 <= d3_d1 g i <= 5) by (unfold d3_d1; clear - D1; lia).
assert (DEN : forall n v, bv_unsigned (ew E n) = v -> sv_denot E (SOff n 0) = Z_to_bv 64 v).
{ intros n v Hv. apply bv_eq. rewrite denot_SOff, Hv, Z.add_0_r. rewrite unsigned_lit. reflexivity. }
assert (PRS : forall a, sp0 - STK <= a < sp0 -> writable_at SEGS (rd W2 mem2) a)
  by (intros x Hx; apply (apresent_writable SEGS); apply Hpres; exact Hx).
assert (FRW : forall a, F <= a < F + 1024 -> writable_at SEGS (rd W2 mem2) a)
  by (intros x Hx; apply (apresent_writable SEGS); exact (proj1 (Hfbyt x Hx))).
assert (FSW : forall o, 0 <= o < 128 -> writable_at SEGS (rd W2 mem2) (shadow_addr F + o))
  by (intros o Ho; apply (apresent_writable SEGS); exact (proj1 (Hfsh o Ho))).
destruct HMF as (M32 & M48 & M56 & M72 & M80 & M88 & M104 & M136 & M144 & M160).
unfold V_hw, V_v, V_ev, V_id, V_s, V_again in M32, M48, M56, M72, M80, M88, M104, M136, M144, M160.
unfold mf_id, V_id in HMID. unfold bytes_at8, V_id in HBID.
change (SFa g pos) with F in M32, M48, M56, M72, M104, M160, HMID, HBID.
replace (F + 352 + 28) with (F + 380) in M104 by lia.
apply (d3_vm_lnot _ _ (F + 288)) in M56; [|clear - Hf4096 HF64; lia].
rewrite restrict_mkst_fx. unfold d3_ss0. apply pa_entry_st_ok_full.
- subst E. unfold d3_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold d3_rs, d3_rmf_hw, d3_rmf_ro, d3_rmf_n, d3_rhw, d3_rid, d3_rshv, d3_rshe, d3_rpl, d3_rpsh, d3_rdot, d3_rnul, d3_ch.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply PRS. clear - Ho Hmf1 Hmf2. lia.
  + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ mf 32 8 (SOff 33 0) (F + 432)); [apply DEN; exact U33 | zside | zside | exact M32].
    * apply (chunk_ok_val SEGS E _ mf 48 8 (SOff 34 0) (F + 224)); [apply DEN; exact U34 | zside | zside | exact M48].
    * apply (chunk_ok_val SEGS E _ mf 56 8 (SOff 35 0) (2 ^ 64 - 1 - (F + 288))); [apply DEN; exact U35 | zside | zside | exact M56].
    * apply (chunk_ok_val SEGS E _ mf 72 8 (SOff 36 0) (F + 288)); [apply DEN; exact U36 | zside | zside | exact M72].
    * apply (chunk_ok_val SEGS E _ mf 104 8 (SOff 37 0) (F + 380)); [apply DEN; exact U37 | zside | zside | exact M104].
    * apply (chunk_ok_val SEGS E _ mf 160 8 (SOff 38 0) (shadow_addr F)); [apply DEN; exact U38 | unfold shadow_addr, SHADOW_OFF; zside | zside | exact M160].
    * apply (chunk_ok_val SEGS E _ mf 168 8 (SOff 32 0) SHADOW_OFF); [apply DEN; exact U32 | unfold SHADOW_OFF; zside | zside | exact H168].
    * apply (chunk_ok_val SEGS E _ mf 184 8 (SOff 39 0) (F + 352)); [apply DEN; exact U39 | zside | zside | exact HMID].
  + rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply PRS. clear - Ho Hmf1 Hmf2. lia.
  + rewrite U33. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply FRW. clear - Ho. lia.
  + rewrite U39. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    assert (IDB : forall j, (j < 38)%nat ->
      val_mem SEGS (rd W2 mem2) (F + 352 + Z.of_nat j) 1 (RcIdentModel.bz (RcIdentModel.nthb (m_id g (S i)) j)) /\
      0 <= RcIdentModel.bz (RcIdentModel.nthb (m_id g (S i)) j) < 256).
    { intros j Hj. apply (d3_garr8_vm1 _ (F + 352) (m_id g (S i)) j HBID). unfold m_id. lia. }
    assert (ID2 : forall j, (j < 37)%nat -> val_mem SEGS (rd W2 mem2) (F + 352 + Z.of_nat j) 2
      (RcIdentModel.bz (RcIdentModel.nthb (m_id g (S i)) j) + 256 * RcIdentModel.bz (RcIdentModel.nthb (m_id g (S i)) (S j)))).
    { intros j Hj. destruct (IDB j ltac:(lia)) as [A1 A2]. destruct (IDB (S j) ltac:(lia)) as [B1 B2].
      apply d3_vm2; [exact A1 | | exact A2 | exact B2]. replace (F + 352 + Z.of_nat j + 1) with (F + 352 + Z.of_nat (S j)) by lia. exact B1. }
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ (F + 352) 22 2 (SOff 24 0) (d3_ma g i)); [apply DEN; exact U24 | zside | zside |].
      exact (ID2 22%nat ltac:(lia)).
    * apply (chunk_ok_val SEGS E _ (F + 352) 24 2 (SOff 25 0) (d3_mi g i)); [apply DEN; exact U25 | zside | zside |].
      exact (ID2 24%nat ltac:(lia)).
    * apply (chunk_ok_val SEGS E _ (F + 352) 26 2 (SOff 21 0) (d3_pa g i)); [apply DEN; exact U21 | zside | zside |].
      exact (ID2 26%nat ltac:(lia)).
  + rewrite U38. unfold shadow_addr, SHADOW_OFF in *. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (FSW o). lia.
  + rewrite U38. unfold shadow_addr, SHADOW_OFF in *. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (FSW o). lia.
  + rewrite U27. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil;
    match goal with |- YP09.chunk_ok _ _ _ _ {| c_off := ?o; YP09.c_val := CVal 1 (SOff ?n 0) |} =>
      let j := eval vm_compute in (Z.to_nat o) in
      apply (chunk_ok_val SEGS E _ pl o 1 (SOff n 0) (d3_pb g i j));
      [apply DEN; exact (UP j ltac:(lia)) | pose proof (proj2 (PB j ltac:(lia))); zside | zside | exact (proj1 (PB j ltac:(lia)))] end.
  + rewrite U41. split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (SHADOW_OFF + pl / 8) 0 1 (SLit 0) 0); [reflexivity | zside | zside |].
    rewrite Z.add_0_r. apply d3_vm1. destruct Hpsh as (_ & _ & Hc). specialize (Hc 0 ltac:(clear - HK8; Z.div_mod_to_equations; lia)).
    rewrite Z.add_0_r in Hc. unfold shadow_of_addr in Hc. rewrite Hc.
    replace (0 <? K / 8) with true by (symmetry; apply Z.ltb_lt; clear - HK8; Z.div_mod_to_equations; lia). reflexivity.
  + rewrite U54. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply FRW. clear - Ho HD1. lia.
  + rewrite U55. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply FRW. clear - Ho HN3. lia.
- apply pairwise_disjoint_of_extents.
  unfold d3_rs, d3_rmf_hw, d3_rmf_ro, d3_rmf_n, d3_rhw, d3_rid, d3_rshv, d3_rshe, d3_rpl, d3_rpsh, d3_rdot, d3_rnul,
    extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U9, U33, U39, U38, U27, U41, U54, U55.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold shadow_addr, SHADOW_OFF.
  assert (HFP : pl + K <= F \/ F + 1024 <= pl) by (clear - Hsep; lia).
  assert (HFM : F + 1024 <= mf) by (clear - Hfceil Hmf5; lia).
  assert (HPM : pl + K <= mf) by (clear - Hpceil Hmf5; lia).
  assert (HDN : d3_d1 g i + 3 <= d3_n3 g i) by (unfold d3_n3, d3_n2; clear - D2 D3; lia).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfapp, Happ.
  clear - HFP HFM HPM Hf4096 HF64 Hp4096 HP64 HK8 Hp16 Hf32 HD1 HN3 HDN Hmf3 Hfapp Happ C1.
  repeat split; Z.div_mod_to_equations; lia.
- split; [|split].
  + cbn [d3_G f_atoms d3_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    pose proof (UP 0%nat ltac:(lia)) as U42. pose proof (UP 1%nat ltac:(lia)) as U43.
    pose proof (UP 2%nat ltac:(lia)) as U44. pose proof (UP 3%nat ltac:(lia)) as U45.
    pose proof (UP 4%nat ltac:(lia)) as U46. pose proof (UP 5%nat ltac:(lia)) as U47.
    pose proof (UP 6%nat ltac:(lia)) as U48. pose proof (UP 7%nat ltac:(lia)) as U49.
    cbn [Nat.add] in U42, U43, U44, U45, U46, U47, U48, U49.
    rewrite U2, U9, U10, U22, U27, U24, U25, U21, U32, U35, U50, U53, U42, U43, U44, U45, U46, U47, U48, U49.
    change (2 ^ 5) with 32. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    pose proof (proj2 (PB 0%nat ltac:(lia))). pose proof (proj2 (PB 1%nat ltac:(lia))).
    pose proof (proj2 (PB 2%nat ltac:(lia))). pose proof (proj2 (PB 3%nat ltac:(lia))).
    pose proof (proj2 (PB 4%nat ltac:(lia))). pose proof (proj2 (PB 5%nat ltac:(lia))).
    pose proof (proj2 (PB 6%nat ltac:(lia))). pose proof (proj2 (PB 7%nat ltac:(lia))).
    unfold SHADOW_OFF. repeat match goal with |- _ /\ _ => split end; try exact I; try lia.
  + exact I.
  + cbn [d3_G f_alias d3_alias alias_ok d3_srl d3_be16].
    assert (SRL : forall c, 0 <= c < 8 -> sv_denot E (SAlu ALU_SRL (SOff 27 c) (SLit 3)) = sv_denot E (SOff 40 0)).
    { intros c Hc. apply U_inj. rewrite U_SAlu, !U_SOff, U_SLit, U27, U40. cbn [zalu_raw].
      change (Z.land (zcanon 3) 63) with 3. rewrite (zcanon_id (pl + c)) by (unfold M64; lia).
      rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
      rewrite !zcanon_id by (unfold M64; Z.div_mod_to_equations; lia). clear - Hp16 Hc. Z.div_mod_to_equations. lia. }
    assert (BE : forall (hi lo dst : nat) b2 b3 v, bv_unsigned (ew E hi) = b2 -> bv_unsigned (ew E lo) = b3 ->
      bv_unsigned (ew E dst) = v -> 0 <= b2 < 256 -> 0 <= b3 < 256 -> v = 256 * b2 + b3 ->
      sv_denot E (SAlu ALU_OR (SAlu ALU_SLL (SOff hi 0) (SLit 8)) (SOff lo 0)) = sv_denot E (SOff dst 0)).
    { intros hi lo dst b2 b3 v H2 H3 Hv R2' R3' Hvv. apply U_inj. rewrite !U_SAlu, !U_SOff, U_SLit, H2, H3, Hv. cbn [zalu_raw].
      change (Z.land (zcanon 8) 63) with 8. rewrite !Z.add_0_r, (zcanon_id b2), (zcanon_id b3) by (unfold M64; lia).
      rewrite (zcanon_id (Z.shiftl b2 8)) by (rewrite Z.shiftl_mul_pow2 by lia; unfold M64; lia).
      rewrite d3_lor_shift by lia. rewrite !zcanon_id by (unfold M64; lia). lia. }
    assert (ADD : forall (a b c : nat) va vb, bv_unsigned (ew E a) = va -> bv_unsigned (ew E b) = vb ->
      bv_unsigned (ew E c) = va + vb -> sv_denot E (SAlu ALU_ADD (SOff a 0) (SOff b 0)) = sv_denot E (SOff c 0)).
    { intros a b c va vb Ha' Hb' Hc'. apply U_inj. rewrite U_SAlu, !U_SOff, Ha', Hb', Hc'. cbn [zalu_raw].
      rewrite !Z.add_0_r. unfold zcanon, M64. rewrite <- Zplus_mod. reflexivity. }
    split; [apply SRL; lia|]. split; [apply SRL; lia|]. split; [apply SRL; lia|]. split; [apply SRL; lia|].
    split; [apply SRL; lia|]. split; [apply SRL; lia|]. split; [apply SRL; lia|].
    split; [apply (ADD 40%nat 32%nat 41%nat (pl / 8) SHADOW_OFF); [exact U40 | exact U32 | rewrite U41; lia]|].
    split; [apply (BE 44%nat 45%nat 24%nat (d3_pb g i 2) (d3_pb g i 3) (d3_ma g i)); [exact (UP 2%nat ltac:(lia)) | exact (UP 3%nat ltac:(lia)) | exact U24 | exact (proj2 (PB 2%nat ltac:(lia))) | exact (proj2 (PB 3%nat ltac:(lia))) | exact HMA]|].
    split; [apply (BE 46%nat 47%nat 25%nat (d3_pb g i 4) (d3_pb g i 5) (d3_mi g i)); [exact (UP 4%nat ltac:(lia)) | exact (UP 5%nat ltac:(lia)) | exact U25 | exact (proj2 (PB 4%nat ltac:(lia))) | exact (proj2 (PB 5%nat ltac:(lia))) | exact HMI]|].
    split; [apply (BE 48%nat 49%nat 21%nat (d3_pb g i 6) (d3_pb g i 7) (d3_pa g i)); [exact (UP 6%nat ltac:(lia)) | exact (UP 7%nat ltac:(lia)) | exact U21 | exact (proj2 (PB 6%nat ltac:(lia))) | exact (proj2 (PB 7%nat ltac:(lia))) | exact HPA]|].
    split; [apply (ADD 36%nat 50%nat 54%nat (F + 288) (d3_d1 g i)); [exact U36 | exact U50 | rewrite U54; lia]|].
    split; [apply (ADD 36%nat 53%nat 55%nat (F + 288) (d3_n3 g i)); [exact U36 | exact U53 | rewrite U55; lia]|].
    exact I.
Qed.

(* ---- the windows the runs may write ---------------------------------------------------------------------- *)
Definition d3_W (F sh mf d1 n3 a : Z) : Prop :=
  (mf + 24 <= a < mf + 32) \/ (mf + 208 <= a < mf + 216) \/ (F + 436 <= a < F + 444) \/
  (sh + 28 <= a < sh + 31) \/ (sh + 36 <= a < sh + 39) \/ (F + 288 + d1 <= a < F + 288 + d1 + 1) \/
  (F + 288 + n3 <= a < F + 288 + n3 + 1).
Definition d3_weqb (w w' : option nat * Z * Z) : bool :=
  match w, w' with
  | (b, lo, hi), (b', lo', hi') =>
      match b, b' with Some n, Some n' => Nat.eqb n n' | None, None => true | _, _ => false end &&
      Z.eqb lo lo' && Z.eqb hi hi'
  end.
Lemma d3_weqb_eq : forall w w', d3_weqb w w' = true -> w = w'.
Proof.
intros [[b lo] hi] [[b' lo'] hi'] H. unfold d3_weqb in H.
apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
apply Z.eqb_eq in H2, H3. subst lo' hi'.
destruct b as [n|], b' as [n'|]; try discriminate; [apply Nat.eqb_eq in H1; subst n'|]; reflexivity.
Qed.
Definition d3_win_ok (rs : smem) : bool :=
  forallb (fun w => existsb (fun w' => d3_weqb w w') (windows d3_rs)) (windows rs).
Lemma d3_win : forall E rs F sh mf d1 n3,
  d3_win_ok rs = true -> bv_unsigned (ew E 9) = mf -> bv_unsigned (ew E 33) = F + 432 ->
  bv_unsigned (ew E 38) = sh -> bv_unsigned (ew E 54) = F + 288 + d1 -> bv_unsigned (ew E 55) = F + 288 + n3 ->
  forall a, in_wrange E rs a -> d3_W F sh mf d1 n3 a.
Proof.
intros E rs F sh mf d1 n3 Hok U9 U33 U38 U54 U55 a Ha.
destruct (in_wrange_windows E rs a Ha) as (b & wlo & whi & Hin & Hr).
unfold d3_win_ok in Hok. rewrite forallb_forall in Hok. specialize (Hok _ Hin).
apply existsb_exists in Hok as (w' & Hw' & Heq). apply d3_weqb_eq in Heq. subst w'.
unfold d3_rs, windows in Hw'. cbn [map YP09.r_base YP09.r_wlo YP09.r_whi d3_rmf_hw d3_rmf_ro d3_rmf_n d3_rhw
  d3_rid d3_rshv d3_rshe d3_rpl d3_rpsh d3_rdot d3_rnul In] in Hw'.
unfold d3_W.
repeat (destruct Hw' as [Hw' | Hw']; [injection Hw' as <- <- <-; cbn [base_val] in Hr;
  rewrite ?U9, ?U33, ?U38, ?U54, ?U55 in Hr; lia |]).
destruct Hw'.
Qed.
Lemma d3_awr : forall E rs STK sp0 bl0 blc lyc pos F sh mf d1 n3,
  (forall a, in_wrange E rs a -> d3_W F sh mf d1 n3 a) ->
  frame_addr lyc 4 pos = F -> sh = shadow_addr F -> sp0 - STK <= mf -> mf + 216 <= sp0 ->
  0 <= d1 < 24 -> 0 <= n3 < 24 ->
  awr_ok E rs STK sp0 [] bl0 blc lyc [(4, pos)].
Proof.
intros E rs STK sp0 bl0 blc lyc pos F sh mf d1 n3 HW HF Hsh H1 H2 Hd Hn a Ha.
specialize (HW a Ha). unfold awr_byte.
assert (HFR : F <= a < F + 1024 -> in_frames lyc [(4, pos)] a).
{ intros Hx. exists 4, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. rewrite HF.
  change (fs_frame_bytes 4) with 1024. exact Hx. }
assert (HSH : sh <= a < sh + 128 -> in_frames lyc [(4, pos)] a).
{ intros Hx. exists 4, pos. split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd]. rewrite HF, <- Hsh.
  change (fs_frame_bytes 4 / 8) with 128. exact Hx. }
unfold d3_W in HW.
destruct HW as [HW | [HW | [HW | [HW | [HW | [HW | HW]]]]]].
- left. lia.
- left. lia.
- right; right; right. apply HFR. lia.
- right; right; right. apply HSH. lia.
- right; right; right. apply HSH. lia.
- right; right; right. apply HFR. lia.
- right; right; right. apply HFR. lia.
Qed.
Lemma d3_W_wr : forall g pos mf d1 n3 a, 0 <= d1 < 24 -> 0 <= n3 < 24 ->
  d3_W (SFa g pos) (shadow_addr (SFa g pos)) mf d1 n3 a -> d3_wr g pos mf a.
Proof.
intros g pos mf d1 n3 a Hd Hn HW. unfold d3_W in HW. unfold d3_wr, M_n1, V_v, N_v, V_ev, N_ev, V_hw. lia.
Qed.
Lemma d3_keep_run : forall g pos mf i pl W0 m0 W m1 m2 E rs d1 n3,
  frame_of E rs (rd W m1) (rd W m2) ->
  (forall a, in_wrange E rs a -> d3_W (SFa g pos) (shadow_addr (SFa g pos)) mf d1 n3 a) ->
  0 <= d1 < 24 -> 0 <= n3 < 24 ->
  (forall a, d3_zone g pos mf i pl a -> 0 <= a < 2 ^ 64) ->
  d3_keep g pos mf i pl W0 m0 W m1 -> d3_keep g pos mf i pl W0 m0 W m2.
Proof.
intros g pos mf i pl W0 m0 W m1 m2 E rs d1 n3 HFr HW Hd Hn HZ HK a Hz Hnw.
rewrite <- (HK a Hz Hnw).
apply (kept_of_frame E rs (w_H W) m1 m2 (d3_W (SFa g pos) (shadow_addr (SFa g pos)) mf d1 n3) HFr).
- intros b wlo whi x Hin Hx. apply HW. unfold in_wrange.
  unfold windows in Hin. apply in_map_iff in Hin as (r & Er & Hr). injection Er as Eb Ewl Ewh.
  exists r. split; [exact Hr|]. rewrite Eb, Ewl, Ewh. exact Hx.
- exact (HZ a Hz).
- intros Hx. apply Hnw. exact (d3_W_wr g pos mf d1 n3 a Hd Hn Hx).
Qed.
(* A region kept by a call: its bytes read the same through the new world, its window is present there. *)
Lemma d3_rk2 : forall E H H' (m m' : word -> option byte) (n : nat) b lo hi wlo whi cs,
  bv_unsigned (ew E n) = b ->
  (forall a, b + lo <= a < b + hi -> aview SEGS H' m' a = aview SEGS H m a) ->
  (forall a, b + wlo <= a < b + whi -> apresent H' m' a) ->
  region_kept SEGS E (mrestrict H m) (mrestrict H' m') (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H H' m m' n b lo hi wlo whi cs Hb Hk Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hb; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hk. exact Ha.
- intros _. apply (apresent_writable SEGS). apply Hp. exact Ha.
Qed.
(* A chunk of a state's region gives the bytes it describes. *)
Lemma d3_chunk_vm : forall E m base off (w : N) e v,
  YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal w e)) -> sv_denot E e = Z_to_bv 64 v ->
  0 <= v < 2 ^ (8 * Z.of_N w) -> (w <= 8)%N -> val_mem SEGS m (base + off) (N.to_nat w) v.
Proof.
intros E m base off w e v Hc He Hv Hw k Hk.
destruct (Hc (Z.of_nat k) ltac:(cbn [YP09.c_len YP09.c_val cv_len]; lia)) as (b & Hb1 & Hb2).
cbn [cbyte YP09.c_val YP09.c_off] in Hb1, Hb2. injection Hb1 as <-. rewrite Hb2. f_equal.
assert (H64 : 2 ^ (8 * Z.of_N w) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
rewrite He. unfold byte_of_word, YO0f.le_byte. rewrite unsigned_lit_small by lia. apply bv_eq. rewrite !Z_to_bv_unsigned.
replace (8 * Z.of_nat (N.to_nat w)) with (8 * Z.of_N w) by lia.
rewrite (Z.mod_small v (2 ^ (8 * Z.of_N w))) by lia. unfold bv_wrap. change (bv_modulus 8) with 256.
rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma d3_reg_vm : forall E ss ms idx n lo hi wlo whi cs off (w : N) e b v,
  st_ok SEGS E ss ms -> nth_error (ss_mem ss) idx = Some (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  In (YP09.mkChunk off (CVal w e)) cs -> bv_unsigned (ew E n) = b -> sv_denot E e = Z_to_bv 64 v ->
  0 <= v < 2 ^ (8 * Z.of_N w) -> (w <= 8)%N -> val_mem SEGS (ms_mem ms) (b + off) (N.to_nat w) v.
Proof.
intros E ss ms idx n lo hi wlo whi cs off w e b v HS Hn Hin Hb He Hv Hw.
pose proof (st_ok_mem_ok SEGS E ss ms HS) as (_ & HR & _).
pose proof (proj1 (Forall_forall _ _) HR _ (nth_error_In _ _ Hn)) as (_ & _ & _ & HC).
cbn [YP09.r_base YP09.r_chunks base_val] in HC. rewrite Hb in HC.
exact (d3_chunk_vm E _ b off w e v (proj1 (Forall_forall _ _) HC _ Hin) He Hv Hw).
Qed.
(* The shadow cells of ev (cells 36..38 of the frame) and v (cells 28..30) as the case sets them. *)
Lemma d3_ra_ev : forall rdr F, F mod 32 = 0 ->
  rdr (shadow_addr F + 36) = Some 0 -> rdr (shadow_addr F + 37) = Some 0 -> rdr (shadow_addr F + 38) = Some 0 ->
  range_addressable rdr SHADOW_OFF (F + 288) 24.
Proof.
intros rdr F HF H0 H1 H2 x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
unfold shadow_addr in *. assert (x / 8 = F / 8 + 36 \/ x / 8 = F / 8 + 37 \/ x / 8 = F / 8 + 38) as [E|[E|E]]
  by (clear - HF Hx; Z.div_mod_to_equations; lia); rewrite E, Z.add_assoc; assumption.
Qed.
Lemma d3_ra_v : forall rdr F, F mod 32 = 0 ->
  rdr (shadow_addr F + 28) = Some 0 -> rdr (shadow_addr F + 29) = Some 0 -> rdr (shadow_addr F + 30) = Some 4 ->
  range_addressable rdr SHADOW_OFF (F + 224) 20.
Proof.
intros rdr F HF H0 H1 H2 x Hx. unfold shadow_of_addr. unfold shadow_addr in *.
assert (x / 8 = F / 8 + 28 \/ x / 8 = F / 8 + 29 \/ (x / 8 = F / 8 + 30 /\ x mod 8 < 4)) as [E|[E|[E Em]]]
  by (clear - HF Hx; Z.div_mod_to_equations; lia); rewrite E, Z.add_assoc.
- exists 0. split; [assumption | left; reflexivity].
- exists 0. split; [assumption | left; reflexivity].
- exists 4. split; [assumption | right; lia].
Qed.
(* The payload copy's first shadow cell is 0 in every state whose blocks hold it (rec_k >= 8). *)
Lemma d3_psh : forall ly S W mem md pl K, AR SEGS B ly S W mem md -> In (pl, K) (ablocks B ly S) -> 8 <= K ->
  aview SEGS (w_H W) mem (SHADOW_OFF + pl / 8) = Some 0.
Proof.
intros ly S W mem md pl K HAR Hin HK.
destruct (al_shadow _ _ LAWS _ _ _ _ _ pl K HAR Hin) as ((_ & _ & Hc) & _).
assert (Hr : req_size K = K) by (unfold req_size; destruct (Z.eqb_spec K 0); lia). rewrite Hr in Hc.
specialize (Hc 0 ltac:(clear - HK; Z.div_mod_to_equations; lia)). rewrite Z.add_0_r in Hc. unfold shadow_of_addr in Hc.
rewrite Hc. replace (0 <? K / 8) with true by (symmetry; apply Z.ltb_lt; clear - HK; Z.div_mod_to_equations; lia).
reflexivity.
Qed.
Lemma d3_garr8_mv : forall (W W' : world SEGS) m m' a l,
  garr8 SEGS (rd W m) a l ->
  (forall x, a <= x < a + Z.of_nat (length l) -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
  garr8 SEGS (rd W' m') a l.
Proof.
intros W W' m m' a l H Hk. apply (garr8_frame SEGS _ _ a l H). intros x Hx. apply (mbyte_of_aview SEGS). exact (Hk x Hx).
Qed.
Lemma d3_vm_mv : forall (W W' : world SEGS) m m' a n v,
  val_mem SEGS (rd W m) a n v ->
  (forall x, a <= x < a + Z.of_nat n -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
  val_mem SEGS (rd W' m') a n v.
Proof.
intros W W' m m' a n v H Hk k Hkn. rewrite (mbyte_of_aview SEGS (w_H W) (w_H W') m m' (a + Z.of_nat k)); [apply H, Hkn|].
apply Hk. lia.
Qed.

(* ---- the walk -------------------------------------------------------------------------------------------- *)
(* The contract's hypotheses the walk uses (LLVMFuzzerTestOneInput.v), with its text. *)
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis HEV : EV_LLVMF <= EV_LIB.
Hypothesis PSIG : identb_prog_sig_ok (PI := PI).
Hypothesis MTL : ameter_laws MT.
Hypothesis HMT0 : forall s s' : astate, mo_le MT s s' 0.
Hypothesis AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA IB___interceptor_trampoline_bcmp).
Hypothesis HPD : put_dec.tput_dec_spec B.
Hypothesis HVS : reac_identity_reac_ver_str.treac_identity_reac_ver_str_spec B.
(* The pieces: the three calls stated in LLVMFuzzerTestOneInput_seg_D3_hand_stmt.v are proved in
   LLVMFuzzerTestOneInput_seg_D3_hand.v, and the end-state packaging is d3tl_core, stated and proved in _seg_D3_tl.v:238. *)
Let D3PD := LLVMFuzzerTestOneInput_seg_D3_hand.d3_pd B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS.
Let D3VS := LLVMFuzzerTestOneInput_seg_D3_hand.d3_vs B LLVMF_STK.
Let D3BC := LLVMFuzzerTestOneInput_seg_D3_hand.d3_bc B LLVMF_STK.
Let D3TLc := LLVMFuzzerTestOneInput_seg_D3_tl.d3tl_core B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNT := SRr_run_to_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.

Lemma d3_nth_skipn : forall (l : list byte) m n d, nth n (skipn m l) d = nth (m + n) l d.
Proof. induction l as [|x l IH]; intros [|m] n d; cbn; try reflexivity; [destruct n; reflexivity | apply IH]. Qed.
Lemma d3_raw_nth : forall (idb pll : list byte) (j : nat), RcIdentModel.raw idb = firstn 8 pll -> (j < 8)%nat ->
  RcIdentModel.nthb idb (28 + j) = RcIdentModel.nthb pll j.
Proof.
intros idb pll j H Hj. unfold RcIdentModel.raw, RcIdentModel.get, RcIdentModel.OFF_RAW, RcIdentModel.REAC_VER_LEN in H.
unfold RcIdentModel.nthb. rewrite <- (SlotModel.nth_first pll 8 j _ Hj), <- H, SlotModel.nth_first by exact Hj.
symmetry. apply d3_nth_skipn.
Qed.
(* The bytes the first bcmp compares (0x8101c): id+28 .. id+35 against the payload's first 8. *)
Lemma d3_bc1_eq : forall W m F pl idb pll,
  bytes_at8 W m (F + 352) idb -> length idb = 38%nat -> bytes_at8 W m pl pll -> (8 <= length pll)%nat ->
  RcIdentModel.raw idb = firstn 8 pll ->
  forall j, 0 <= j < 8 -> aview SEGS (w_H W) m (F + 380 + j) = aview SEGS (w_H W) m (pl + j).
Proof.
intros W m F pl idb pll HI HIl HP HPl HR j Hj.
destruct (d3_garr8_vm1 _ _ idb (28 + Z.to_nat j) HI ltac:(lia)) as [A1 A2].
destruct (d3_garr8_vm1 _ _ pll (Z.to_nat j) HP ltac:(lia)) as [B1 B2].
replace (F + 380 + j) with (F + 352 + Z.of_nat (28 + Z.to_nat j)) by lia.
replace (pl + j) with (pl + Z.of_nat (Z.to_nat j)) by lia.
rewrite (aview_of_val_mem1 SEGS _ _ _ _ A1 A2), (aview_of_val_mem1 SEGS _ _ _ _ B1 B2).
rewrite (d3_raw_nth idb pll (Z.to_nat j) HR ltac:(lia)). reflexivity.
Qed.

(* The input block is empty or a heap block of the entry state (e_pre). *)
Lemma d3_inp : forall g, e_pre B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS g ->
  e_n g = 0 \/ (4096 <= e_p g /\ e_p g + e_n g <= alloc_ceiling).
Proof.
intros g Hpre. unfold e_pre, tLLVMFuzzerTestOneInput_pre in Hpre.
destruct Hpre as (HAF & _ & _ & _ & Hpn & _).
destruct Hpn as [(Hn & _) | (Hn & Hin)]; [left; exact Hn | right].
destruct HAF as (HAR0 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hin) as (_ & H4096 & Hc & _).
pose proof (req_size_pos (e_n g) ltac:(lia)) as [_ Hr]. lia.
Qed.
Lemma d3_inp2 : forall g, e_pre B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS g ->
  e_n g = 0 \/ In (e_p g, e_n g) (ablocks B (e_ly g) (e_S g)).
Proof.
intros g Hpre. unfold e_pre, tLLVMFuzzerTestOneInput_pre in Hpre.
destruct Hpre as (_ & _ & _ & _ & Hpn & _).
destruct Hpn as [(Hn & _) | (_ & Hin)]; [left; exact Hn | right; exact Hin].
Qed.

(* ---- what a call keeps, in the zones of d3_keep and in the side-stack frame ------------------------------- *)
Lemma d3_keep_call : forall g pos mf i pl W0 m0 STKc lyc Sc (Wc : world SEGS) mc (W' : world SEGS) m' (X : Z -> Prop),
  tcj_kept B STKc lyc Sc Wc mc W' m' mf X ->
  frames Sc = [(4, pos)] -> frame_addr lyc 4 pos = SFa g pos ->
  In (pl, SlotModel.rec_k (e_pl g) i) (ablocks B lyc Sc) ->
  (e_n g = 0 \/ In (e_p g, e_n g) (ablocks B lyc Sc)) ->
  alloc_ceiling <= mf -> e_sp0 g <= 2 ^ 64 ->
  (forall a, X a -> d3_wr g pos mf a) ->
  d3_keep g pos mf i pl W0 m0 Wc mc -> d3_keep g pos mf i pl W0 m0 W' m'.
Proof.
intros g pos mf i pl W0 m0 STKc lyc Sc Wc mc W' m' X HT Hfr HF Hpl Hin Hc Hs HX HK a Hz Hnw.
rewrite <- (HK a Hz Hnw).
destruct HT as (T1 & T2 & _ & T4 & _).
assert (HnX : ~ X a) by (intros Hx; apply Hnw, HX, Hx).
unfold d3_zone in Hz. destruct Hz as [Hz|[Hz|[Hz|[Hz|Hz]]]].
- apply T1; [lia | lia | exact HnX].
- apply (T4 4 pos a); [rewrite Hfr; left; reflexivity | | exact HnX].
  left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite HF. change (fs_frame_bytes 4) with 1024. lia.
- apply (T4 4 pos a); [rewrite Hfr; left; reflexivity | | exact HnX].
  right. unfold in_zr. cbn [fst snd]. rewrite HF. change (fs_frame_bytes 4 / 8) with 128. lia.
- pose proof (req_size_pos (SlotModel.rec_k (e_pl g) i) ltac:(lia)) as [_ Hr].
  replace a with (pl + (a - pl)) by lia. apply (T2 pl (SlotModel.rec_k (e_pl g) i) (a - pl) Hpl); [lia|].
  replace (pl + (a - pl)) with a by lia. exact HnX.
- destruct Hin as [Hn0 | Hin]; [lia|].
  pose proof (req_size_pos (e_n g) ltac:(lia)) as [_ Hr].
  replace a with (e_p g + (a - e_p g)) by lia. apply (T2 (e_p g) (e_n g) (a - e_p g) Hin); [lia|].
  replace (e_p g + (a - e_p g)) with a by lia. exact HnX.
Qed.
Lemma d3_fkeep_call : forall F pos STKc lyc Sc (Wc : world SEGS) mc (W' : world SEGS) m' sp (X : Z -> Prop),
  tcj_kept B STKc lyc Sc Wc mc W' m' sp X -> frames Sc = [(4, pos)] -> frame_addr lyc 4 pos = F ->
  forall a, F <= a < F + 1024 -> ~ X a -> aview SEGS (w_H W') m' a = aview SEGS (w_H Wc) mc a.
Proof.
intros F pos STKc lyc Sc Wc mc W' m' sp X (_ & _ & _ & T4 & _) Hfr HF a Ha HnX.
apply (T4 4 pos a); [rewrite Hfr; left; reflexivity | | exact HnX].
left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite HF. change (fs_frame_bytes 4) with 1024. lia.
Qed.
Lemma d3_fkeep_run : forall E rs (W : world SEGS) m1 m2 F sh mf d1 n3,
  frame_of E rs (rd W m1) (rd W m2) -> (forall a, in_wrange E rs a -> d3_W F sh mf d1 n3 a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ d3_W F sh mf d1 n3 a -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) m1 a.
Proof.
intros E rs W m1 m2 F sh mf d1 n3 HFr HW a Ha Hn.
apply (kept_of_frame E rs (w_H W) m1 m2 (d3_W F sh mf d1 n3) HFr); [| exact Ha | exact Hn].
intros b wlo whi x Hin Hx. apply HW. unfold in_wrange.
unfold windows in Hin. apply in_map_iff in Hin as (r & Er & Hr). injection Er as Eb Ewl Ewh.
exists r. split; [exact Hr|]. rewrite Eb, Ewl, Ewh. exact Hx.
Qed.

(* ---- what a call keeps, pointwise: the machine frame above mf, the side-stack frame and its shadow, the
       payload copy and its first shadow cell (0 in both states, from the allocator's shadow law) ------------ *)
Lemma d3_tcj_pt : forall F pos mf pl K STKc lyc Sc (Wc : world SEGS) mc (W' : world SEGS) m' X md_c ly' S' md',
  tcj_kept B STKc lyc Sc Wc mc W' m' mf X -> frames Sc = [(4, pos)] -> frame_addr lyc 4 pos = F ->
  In (pl, K) (ablocks B lyc Sc) -> 8 <= K -> alloc_ceiling <= mf ->
  AR SEGS B lyc Sc Wc mc md_c -> AR SEGS B ly' S' W' m' md' -> In (pl, K) (ablocks B ly' S') ->
  forall a, ~ X a ->
  (mf <= a < 2 ^ 64 \/ (F <= a < F + 1024) \/ (shadow_addr F <= a < shadow_addr F + 128) \/ (pl <= a < pl + K) \/
   a = SHADOW_OFF + pl / 8) ->
  aview SEGS (w_H W') m' a = aview SEGS (w_H Wc) mc a.
Proof.
intros F pos mf pl K STKc lyc Sc Wc mc W' m' X md_c ly' S' md' HT Hfr HF Hpl HK Hc HA HA' Hpl' a HnX Hz.
destruct HT as (T1 & T2 & _ & T4 & _).
destruct Hz as [Hz|[Hz|[Hz|[Hz|Hz]]]].
- apply T1; [lia | lia | exact HnX].
- apply (T4 4 pos a); [rewrite Hfr; left; reflexivity | | exact HnX].
  left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite HF. change (fs_frame_bytes 4) with 1024. lia.
- apply (T4 4 pos a); [rewrite Hfr; left; reflexivity | | exact HnX].
  right. unfold in_zr. cbn [fst snd]. rewrite HF. change (fs_frame_bytes 4 / 8) with 128. lia.
- pose proof (req_size_pos K ltac:(lia)) as [_ Hr].
  replace a with (pl + (a - pl)) by lia. apply (T2 pl K (a - pl) Hpl); [lia|].
  replace (pl + (a - pl)) with a by lia. exact HnX.
- subst a. rewrite (d3_psh ly' S' W' m' md' pl K HA' Hpl' HK), (d3_psh lyc Sc Wc mc md_c pl K HA Hpl HK). reflexivity.
Qed.

(* ---- the bytes of hw at the end, and the two strings the second bcmp compares ----------------------------- *)
Lemma d3_lor_mul : forall a b k, 0 <= k -> 0 <= a -> 0 <= b < 2 ^ k -> Z.lor (a * 2 ^ k) b = a * 2 ^ k + b.
Proof. intros a b k Hk Ha Hb. pose proof (d3_lor_shift a b k Hk Ha Hb) as H. rewrite Z.shiftl_mul_pow2 in H by lia. exact H. Qed.
Lemma d3_den4 : forall E (n0 n1 n2 n3 : nat) b0 b1 b2 b3,
  bv_unsigned (ew E n0) = b0 -> bv_unsigned (ew E n1) = b1 -> bv_unsigned (ew E n2) = b2 -> bv_unsigned (ew E n3) = b3 ->
  0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
  sv_denot E (SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL (SOff n3 0) (SLit 24)) (SAlu ALU_SLL (SOff n2 0) (SLit 16)))
    (SAlu ALU_OR (SAlu ALU_SLL (SOff n1 0) (SLit 8)) (SOff n0 0))) =
  Z_to_bv 64 (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3).
Proof.
intros E n0 n1 n2 n3 b0 b1 b2 b3 H0 H1 H2 H3 R0 R1 R2 R3.
change (Z_to_bv 64 (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3)) with
  (sv_denot E (SLit (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3))).
apply U_inj. rewrite !U_SAlu, !U_SOff, !U_SLit, H0, H1, H2, H3. cbn [zalu_raw].
change (Z.land (zcanon 24) 63) with 24. change (Z.land (zcanon 16) 63) with 16. change (Z.land (zcanon 8) 63) with 8.
rewrite !Z.add_0_r, (zcanon_id b0), (zcanon_id b1), (zcanon_id b2), (zcanon_id b3) by (unfold M64; lia).
rewrite !Z.shiftl_mul_pow2 by lia.
rewrite (zcanon_id (b3 * 2 ^ 24)), (zcanon_id (b2 * 2 ^ 16)), (zcanon_id (b1 * 2 ^ 8)) by (unfold M64; lia).
rewrite (d3_lor_mul b1 b0 8) by lia.
rewrite (d3_lor_mul b3 (b2 * 2 ^ 16) 24) by lia.
rewrite (zcanon_id (b3 * 2 ^ 24 + b2 * 2 ^ 16)), (zcanon_id (b1 * 2 ^ 8 + b0)) by (unfold M64; lia).
replace (b3 * 2 ^ 24 + b2 * 2 ^ 16) with ((b3 * 2 ^ 8 + b2) * 2 ^ 16) by lia.
rewrite (d3_lor_mul (b3 * 2 ^ 8 + b2) (b1 * 2 ^ 8 + b0) 16) by lia.
f_equal. lia.
Qed.
Lemma d3_vm4 : forall m a b0 b1 b2 b3, val_mem SEGS m a 4 (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3) ->
  0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 -> garr8 SEGS m a [b0; b1; b2; b3].
Proof.
intros m a b0 b1 b2 b3 H R0 R1 R2 R3 j Hj. cbn [length] in Hj.
split; [| destruct j as [|[|[|[|j]]]]; cbn [nth]; lia].
intros k Hk. assert (k = 0%nat) by lia. subst k. rewrite Z.add_0_r.
rewrite (H j ltac:(lia)). f_equal. f_equal. unfold YO0f.le_byte.
change (8 * Z.of_nat 4) with 32. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r, Z.shiftr_div_pow2 by lia. change (2 ^ 32) with 4294967296. change (2 ^ 8) with 256.
destruct j as [|[|[|[|j]]]]; [| | | | lia]; cbn [nth Z.of_nat]; change (2 ^ (8 * 0)) with 1;
  try change (2 ^ (8 * 1)) with 256; try change (2 ^ (8 * 2)) with 65536; try change (2 ^ (8 * 3)) with 16777216;
  Z.div_mod_to_equations; lia.
Qed.
Lemma d3_first8 : forall (l : list byte), (8 <= length l)%nat ->
  map (fun b : byte => bv_unsigned b) (firstn 8 l) =
  [RcIdentModel.bz (RcIdentModel.nthb l 0); RcIdentModel.bz (RcIdentModel.nthb l 1);
   RcIdentModel.bz (RcIdentModel.nthb l 2); RcIdentModel.bz (RcIdentModel.nthb l 3);
   RcIdentModel.bz (RcIdentModel.nthb l 4); RcIdentModel.bz (RcIdentModel.nthb l 5);
   RcIdentModel.bz (RcIdentModel.nthb l 6); RcIdentModel.bz (RcIdentModel.nthb l 7)].
Proof. intros l Hl. do 8 (destruct l as [|? l]; [cbn in Hl; lia|]). reflexivity. Qed.
Lemma d3_g1 : forall m a v, val_mem SEGS m a 1 v -> 0 <= v < 256 -> garr8 SEGS m a [v].
Proof.
intros m a v H Hv j Hj. cbn [length] in Hj. assert (j = 0%nat) by lia. subst j. cbn [nth].
rewrite Z.add_0_r. split; [exact H | exact Hv].
Qed.
(* The second bcmp (0x81208): v holds VER and its NUL; ev holds DEC ma, '.', DEC mi, DEC pa, NUL. *)
Lemma d3_evv : forall H (m : word -> option byte) v ev (A Bm Cp : list byte),
  garr8 SEGS (mrestrict H m) ev (map (fun b : byte => bv_unsigned b) A) ->
  garr8 SEGS (mrestrict H m) (ev + Z.of_nat (length A) + 1) (map (fun b : byte => bv_unsigned b) Bm) ->
  garr8 SEGS (mrestrict H m) (ev + Z.of_nat (length A) + 1 + Z.of_nat (length Bm))
    (map (fun b : byte => bv_unsigned b) Cp) ->
  val_mem SEGS (mrestrict H m) (ev + Z.of_nat (length A)) 1 46 ->
  val_mem SEGS (mrestrict H m) (ev + Z.of_nat (length A) + 1 + Z.of_nat (length Bm) + Z.of_nat (length Cp)) 1 0 ->
  garr8 SEGS (mrestrict H m) v (map (fun b : byte => bv_unsigned b) (A ++ [Z_to_bv 8 46] ++ Bm ++ Cp) ++ [0]) ->
  forall j, 0 <= j < Z.of_nat (length A) + 1 + Z.of_nat (length Bm) + Z.of_nat (length Cp) + 1 ->
  aview SEGS H m (v + j) = aview SEGS H m (ev + j).
Proof.
intros H m v ev A Bm Cp GA GB GC G46 G0 GV j Hj.
set (L := map (fun b : byte => bv_unsigned b) (A ++ [Z_to_bv 8 46] ++ Bm ++ Cp) ++ [0]) in *.
assert (GE : garr8 SEGS (mrestrict H m) ev L).
{ unfold L. rewrite !map_app. cbn [map]. change (bv_unsigned (Z_to_bv 8 46)) with 46.
  rewrite <- !app_assoc.
  apply garr8_app. split; [exact GA|]. rewrite length_map.
  apply garr8_app. split; [exact (d3_g1 _ _ _ G46 ltac:(lia))|]. cbn [length Z.of_nat].
  apply garr8_app. split; [exact GB|]. rewrite length_map.
  apply garr8_app. split; [exact GC|]. rewrite length_map.
  exact (d3_g1 _ _ _ G0 ltac:(lia)). }
assert (HL : Z.of_nat (length L) = Z.of_nat (length A) + 1 + Z.of_nat (length Bm) + Z.of_nat (length Cp) + 1).
{ unfold L. rewrite length_app, length_map, !length_app. cbn [length]. lia. }
destruct (garr8_nthZ SEGS _ _ _ j GV ltac:(lia) ltac:(lia)) as [V1 V2].
destruct (garr8_nthZ SEGS _ _ _ j GE ltac:(lia) ltac:(lia)) as [E1 E2].
rewrite (aview_of_val_mem1 SEGS _ _ _ _ V1 V2), (aview_of_val_mem1 SEGS _ _ _ _ E1 E2). reflexivity.
Qed.

Lemma d3_reg5 : forall (regs : bvmap 5 word) (r : bv 5) z, bv_unsigned r = z -> getr regs (Z_to_bv 5 z) = getr regs r.
Proof.
intros regs r z <-. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma d3_walk : seg_D3_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS.
Proof.
unfold seg_D3_stmt. intros g pos mf i pl W2 c2 HV.
pose proof HV as HV0.
destruct HV as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfr & Hk & Hmle & Hmok & HEC &
  (HPB & HHW & Hr & Ha & R10 & R24 & R25 & R21)).
pose proof pa_segs_low as Hsegs. pose proof pa_wx as Hwx.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HEC as (R2 & R9 & R8 & Hmfb & Hmf32 & R3 & R4 & M16 & M64 & M192 & M168 & _).
pose proof HPB as (Hi & Hhb & Hbpl & Hid & M96 & Hfix & Hbef & Hag & Hmid & M112 & M120 & M128 & R22 & R27 & Hcur).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (WS : STK_LLVMF = 16736) by reflexivity.
assert (HFA : frame_addr ly2 4 pos = SFa g pos) by exact (d3_fa _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ 4 pos).
assert (HIN : In (4, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
assert (HPL : In (pl, SlotModel.rec_k (e_pl g) i) (ablocks B ly2 S2)).
{ destruct Hhb as [Hp _]. apply (Permutation_in _ (Permutation_sym Hp)). left. reflexivity. }
assert (Hmf1 : e_sp0 g - LLVMF_STK <= mf) by (clear - Hmfb HSTK WS; lia).
assert (Hmf2 : mf + 216 <= e_sp0 g) by (clear - Hmfb; lia).
assert (Hmf3 : 2 ^ 46 <= mf <= 2 ^ 47 - 216) by (clear - Hmfb Hceil Hslo H47 Hshi C1 HSTK WS; lia).
assert (Hmf5 : alloc_ceiling + 8192 <= mf) by (clear - Hmfb Hceil Hslo HSTK WS; lia).
destruct Hid as (Hidb & Hidz & Hidk).
pose proof (d3_entry g pos mf i pl W2 regs2 mem2 ly2 S2 md2 LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g)
  (e_mem g) (e_md g) [(4, pos)] (4 * Z.of_nat i + 3) HJ HFA HIN HPL Hmf1 Hmf2 Hmf3 Hmf32 Hmf5 R2 R9 R22 R27
  (conj R10 (conj R24 (conj R25 R21))) Hfix Hmid M168 Hbpl Hidb Hr Ha) as HS.
(* model and layout facts *)
destruct (d3_ver (e_pl g) i Hr Ha) as (HK8 & HL8 & HHV & HRAW & HMA & HMI & HPA).
pose proof (SlotModel.rec_k_range (e_pl g) i) as HK.
destruct (d3_mmp (m_id g (S i))) as (Ma & Mi & Mp).
change (RcIdentModel.major (m_id g (S i))) with (d3_ma g i) in Ma.
change (RcIdentModel.minor (m_id g (S i))) with (d3_mi g i) in Mi.
change (RcIdentModel.patch (m_id g (S i))) with (d3_pa g i) in Mp.
destruct (d3_dec_len (d3_ma g i) Ma) as (D1 & _). destruct (d3_dec_len (d3_mi g i) Mi) as (D2 & _).
destruct (d3_dec_len (d3_pa g i) Mp) as (_ & D3).
assert (HN3 : 4 <= d3_n3 g i <= 16) by (unfold d3_n3, d3_n2, d3_d1; clear - D1 D2 D3; lia).
assert (HD1 : 1 <= d3_d1 g i <= 5) by (unfold d3_d1; clear - D1; lia).
assert (HDN2 : d3_d1 g i + 2 <= d3_n2 g i <= d3_n3 g i - 2) by (unfold d3_n3, d3_n2; clear - D2 D3; lia).
destruct (al_frames _ _ LAWS _ _ _ _ _ 4 pos HAR HIN) as (Hf32 & Hfapp & _).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 4 pos HAR HIN) as (Hf4096 & Hfceil & _).
rewrite HFA in Hf32, Hfapp, Hf4096, Hfceil. change (fs_frame_bytes 4) with 1024 in *.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pl _ HAR HPL) as (Hp16 & Hp4096 & Hpceil & Happ & _).
assert (Hreq : req_size (SlotModel.rec_k (e_pl g) i) = SlotModel.rec_k (e_pl g) i)
  by (unfold req_size; destruct (Z.eqb_spec (SlotModel.rec_k (e_pl g) i) 0); lia).
rewrite Hreq in Hpceil, Happ.
set (F := SFa g pos) in *.
set (K := SlotModel.rec_k (e_pl g) i) in *.
(* the environment of the walk *)
remember (d3_E g pos i pl regs2) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold d3_E; apply Eimg_env).
assert (EX : forall j, (j < 24)%nat -> ew E (32 + j) = Z_to_bv 64 (nth j (d3_vals g pos i pl) 0))
  by (intros j Hj; subst E; apply d3_ew_extra; exact Hj).
assert (ER : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn; subst E; apply d3_ew_reg; exact Hn).
assert (HAE : env_agree 32 (Ereg regs2 (map (Z_to_bv 64) (d3_vals g pos i pl))) E)
  by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
assert (HF64 : F + 1024 <= 2 ^ 47) by (clear - Hfceil C1; lia).
assert (HP64 : pl + K <= 2 ^ 47) by (clear - Hpceil C1; lia).
assert (U9 : bv_unsigned (ew E 9) = mf) by (rewrite (ER 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = F + 432) by (d3u EX 1%nat (F + 432); clear - Hf4096 HF64; lia).
assert (U38 : bv_unsigned (ew E 38) = shadow_addr F)
  by (d3u EX 6%nat (shadow_addr F); unfold shadow_addr, SHADOW_OFF; clear - Hf4096 HF64; lia).
assert (U54 : bv_unsigned (ew E 54) = F + 288 + d3_d1 g i)
  by (d3u EX 22%nat (F + 288 + d3_d1 g i); clear - Hf4096 HF64 HD1; lia).
assert (U55 : bv_unsigned (ew E 55) = F + 288 + d3_n3 g i)
  by (d3u EX 23%nat (F + 288 + d3_n3 g i); clear - Hf4096 HF64 HN3; lia).
destruct HEC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  Hpre & Hfds & Hfs & Hinput).
assert (HZ : forall a, d3_zone g pos mf i pl a -> 0 <= a < 2 ^ 64).
{ intros a Hz. unfold d3_zone in Hz. fold F in Hz. pose proof (d3_inp g Hpre) as Hinb.
  unfold shadow_addr, SHADOW_OFF in Hz; clear - Hz Hinb Hmfb Hmf3 Hshi H47 Hf4096 HF64 Hp4096 HP64 HK C1;
  Z.div_mod_to_equations; lia. }
assert (HW : forall E' rs, (forall n, (n < 512)%nat -> ew E' n = ew E n) -> d3_win_ok rs = true ->
  forall a, in_wrange E' rs a -> d3_W F (shadow_addr F) mf (d3_d1 g i) (d3_n3 g i) a).
{ intros E' rs HE' Hrs. apply (d3_win E' rs F (shadow_addr F) mf _ _ Hrs); rewrite HE' by lia; assumption. }
assert (HW1 : forall rs, d3_win_ok rs = true ->
  forall a, in_wrange E rs a -> d3_W F (shadow_addr F) mf (d3_d1 g i) (d3_n3 g i) a)
  by (intros rs; apply HW; reflexivity).
(* run 1: the length and has-version tests, the arguments of the first bcmp (0x8101c) *)
unfold cfg_at. change (w64 (BASE + 0x888)) with (Z_to_bv 64 (BASE + 0x888)).
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 (BASE + 0x888)) mem2 (seg_rom SEGS))) in HJ.
paj_run_shc RUNP RUNC HS HJ.
{ eapply (d3_awr E _ _ _ _ _ _ _ F (shadow_addr F) mf (d3_d1 g i) (d3_n3 g i));
  [apply HW1; vm_compute; reflexivity | exact HFA | reflexivity | lia | lia | lia | lia]. }
rename ms into ms1. rename HJ into HJ1.
assert (K1 : d3_keep g pos mf i pl W2 mem2 W2 (ms_mem ms1)).
{ apply (d3_keep_run g pos mf i pl W2 mem2 W2 mem2 (ms_mem ms1) E (ss_mem d3_ss0) (d3_d1 g i) (d3_n3 g i) HFr);
  [apply HW1; vm_compute; reflexivity | lia | lia | exact HZ | intros a _ _; reflexivity]. }
clear HF HFr HG.
(* the bcmp wrapper at 0x8101c: id+28 against the payload, 8 bytes; they are equal (the model's raw bytes) *)
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
pmkst HS.
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ pl _ 4 pos HAR HPL HIN) as Hsep.
rewrite HFA, Hreq in Hsep. change (fs_frame_bytes 4) with 1024 in Hsep. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfapp, Happ.
assert (X37 : ew E 37 = Z_to_bv 64 (F + 380)) by exact (EX 5%nat ltac:(lia)).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?R (Z_to_bv 64 ?X) ?M _) ?MD) ?Q =>
  change (SRr SEGS W2 (cfg_at SEGS X R M MD) Q) end.
eapply SRr_bind.
{ apply (D3BC LAWS ABCMP HSTK g pos mf W2 (ms_regs ms1) (ms_mem ms1) _ ly2 S2 (4 * Z.of_nat i + 3)
    (F + 380) pl 8 2220 HJ1 Hfr Hmfb Hmf32 Rra ltac:(lia) eq_refl).
  - rewrite Rsp, (ER 2%nat 2%bv eq_refl). exact R2.
  - rewrite Rgp, (ER 3%nat 3%bv eq_refl). exact R3.
  - rewrite Rtp, (ER 4%nat 4%bv eq_refl). exact R4.
  - rewrite Ra0, X37. reflexivity.
  - rewrite Ra1, (ER 27%nat 27%bv eq_refl). exact R27.
  - rewrite Ra2. reflexivity.
  - lia.
  - unfold d3_inobj. left. fold F. lia.
  - unfold d3_inobj. right. exists pl, K. split; [exact HPL | pose proof (req_size_pos K ltac:(lia)) as [_ ?]; lia].
  - apply (range_addressable_agree (aview SEGS (w_H W2) mem2)).
    + intros x Hx. unfold shadow_of_addr. apply K1.
      * unfold d3_zone. right; right; left. fold F. unfold shadow_addr, SHADOW_OFF.
        clear - Hx Hf32 Hf4096 HF64. Z.div_mod_to_equations. lia.
      * unfold d3_wr. fold F. unfold shadow_addr, SHADOW_OFF, M_n1, V_v, N_v, V_ev, N_ev, V_hw.
        clear - Hx Hf32 Hf4096 HF64 Hmf5 Hmf3 Hfapp C1. Z.div_mod_to_equations. lia.
    + unfold sh_blk, V_id, N_id in Hidk. fold F in Hidk. eapply block_shadow_range; [exact Hidk | lia | lia].
  - apply (range_addressable_of_block SEGS B LAWS ly2 S2 W2 (ms_mem ms1) _ pl K pl 8 (proj1 HJ1) HPL); pose proof (req_size_pos K ltac:(lia)) as [_ ?]; lia. }
intros W3 c3 _ (-> & regs3 & mem3 & md3 & v & -> & HJ3 & HP3 & Hv & Hcmp & Hfr3 & Hpres3).
assert (Z1 : forall a, F + 380 <= a < F + 388 \/ pl <= a < pl + 8 ->
  aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha'. apply K1; unfold d3_zone, d3_wr; fold F; unfold shadow_addr, SHADOW_OFF, M_n1, V_v, N_v, V_ev, N_ev, V_hw;
  clear - Ha' Hf32 Hf4096 HF64 Hmf5 Hmf3 Hfapp Happ Hsep HK8 Hp4096 HP64 C1; Z.div_mod_to_equations; lia. }
assert (Hv0 : v = w64 0).
{ apply Hcmp. intros j Hj. rewrite (Z1 (F + 380 + j)) by lia. rewrite (Z1 (pl + j)) by lia.
  unfold V_id in Hidb. fold F in Hidb.
  exact (d3_bc1_eq W2 mem2 F pl (m_id g (S i)) (SlotModel.rec_pl (e_pl g) i) Hidb
    (SlotModel.rec_id_length (e_pl g) (S i)) Hbpl HL8 HRAW j Hj). }
clear Z1 Hcmp.
(* the state after the call: the eleven regions are kept (the wrapper writes only below mf), a0 = 0 *)
assert (U39 : bv_unsigned (ew E 39) = F + 352) by (d3u EX 7%nat (F + 352); clear - Hf4096 HF64; lia).
assert (U27 : bv_unsigned (ew E 27) = pl) by (rewrite (ER 27%nat 27%bv eq_refl), R27; apply unsigned_lit_small; lia).
assert (U41 : bv_unsigned (ew E 41) = SHADOW_OFF + pl / 8)
  by (d3u EX 9%nat (SHADOW_OFF + pl / 8); unfold SHADOW_OFF; clear - Hp4096 HP64 HK; Z.div_mod_to_equations; lia).
assert (HZW : forall a, d3_zone g pos mf i pl a -> mf <= a \/ a < mf - 8192).
{ intros a Hz. unfold d3_zone in Hz. fold F in Hz. pose proof (d3_inp g Hpre) as Hinb.
  unfold shadow_addr, SHADOW_OFF in Hz. clear - Hz Hinb Hmf5 Hmf3 Hfceil Hpceil HK C1. Z.div_mod_to_equations. lia. }
assert (K2 : d3_keep g pos mf i pl W2 mem2 W2 mem3).
{ intros a Hz Hnw. rewrite <- (K1 a Hz Hnw). apply Hfr3; [exact (HZ a Hz) | unfold ESTACK; pose proof (HZW a Hz); lia]. }
Ltac d3_pres HPR HFB HFS FF M1 M2 D1 N3 :=
  lazymatch goal with Ha' : _ <= ?a < _ |- apresent _ _ ?a =>
  first [ exfalso; clear - Ha'; lia
        | apply HPR; clear - Ha' M1 M2; lia
        | exact (proj1 (HFB a ltac:(clear - Ha' D1 N3; lia)))
        | lazymatch goal with |- apresent ?h ?m ?a =>
            let o := fresh "o" in
            assert (exists o, a = shadow_addr FF + o /\ 0 <= o < 128) as (o & -> & ?)
              by (exists (a - shadow_addr FF); clear - Ha'; lia);
            exact (proj1 (HFS o ltac:(assumption))) end ] end.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3' & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 4 pos (proj1 HJ3) HIN) as (_ & _ & Hfb3 & Hfs3).
rewrite HFA in Hfb3, Hfs3. change (fs_frame_bytes 4) with 1024 in Hfb3. change (fs_frame_bytes 4 / 8) with 128 in Hfs3.
lazymatch goal with HS : st_ok _ _ ?ssx _ |- _ =>
  let Kk := eval vm_compute in (run_K A_LIM (SLit 0) [] ssx) in
  jafter_call_keep_hi HS Kk regs3 (mrestrict (w_H W2) mem3) HP3 [0;1;2;3;4;5;6;7;8;9;10]%nat HS2 end.
match type of HS2 with ?Q -> _ => assert (HQ : Q); [ | specialize (HS2 HQ); clear HQ ] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil;
  (eapply d3_rk2; [ eassumption
    | intros a Ha'; cbn [YP09.r_lo YP09.r_hi] in Ha'; apply Hfr3; unfold ESTACK, shadow_addr, SHADOW_OFF in *;
      clear - Ha' Hmf5 Hmf3 Hf4096 HF64 Hfceil Hp4096 HP64 Hpceil HD1 HN3 HK HK8 C1; Z.div_mod_to_equations; lia
    | intros a Ha'; cbn [YP09.r_wlo YP09.r_whi] in Ha'; d3_pres Hpres3' Hfb3 Hfs3 F Hmf1 Hmf2 HD1 HN3 ]). }
rewrite <- restrict_mkst_fx in HS2.
pose proof (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) 0 HS2
  ltac:(cbn [ms_regs restrict mkst]; rewrite Hv, Hv0; reflexivity) eq_refl) as HS3.
clear HS2 HS.
lazymatch type of HS3 with st_ok_pi _ _ ?E1 ?ss _ =>
  let v := eval vm_compute in ss in change ss with v in HS3;
  assert (HE1 : forall n, (n < 512)%nat -> ew E1 n = ew E n) by (intros n Hn; apply ew_havoc_old; lia);
  assert (HEI1 : img_env VAL A_LIM E1) by (apply img_env_havoc_hi; [exact HEI | cbv; lia]) end.
(* run 2: the three field checks, the shadow of v and ev cleared, the counter zeroed, the first put_dec (0x81144) *)
unfold cfg_at. change (w64 (BASE + 2220)) with (Z_to_bv 64 (BASE + 2220)).
change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 (BASE + 2220)) mem3 (seg_rom SEGS))) in HJ3.
paj_run_shc RUNP RUNC HS3 HJ3.
{ eapply (d3_awr _ _ _ _ _ _ _ _ F (shadow_addr F) mf (d3_d1 g i) (d3_n3 g i));
  [apply (HW _ _ HE1); vm_compute; reflexivity | exact HFA | reflexivity | lia | lia | lia | lia]. }
rename ms into ms2. rename HJ3 into HJ4.
assert (K3 : d3_keep g pos mf i pl W2 mem2 W2 (ms_mem ms2)).
{ apply (d3_keep_run g pos mf i pl W2 mem2 W2 mem3 (ms_mem ms2) _ _ (d3_d1 g i) (d3_n3 g i) HFr);
  [apply (HW _ _ HE1); vm_compute; reflexivity | lia | lia | exact HZ | exact K2]. }
clear HF HFr HG.
prreg HS3 (10%bv : bv 5) Pa0. prreg HS3 (11%bv : bv 5) Pa1. prreg HS3 (12%bv : bv 5) Pa2. prreg HS3 (13%bv : bv 5) Pa3.
prreg HS3 (1%bv : bv 5) Pra. prreg HS3 (2%bv : bv 5) Psp. prreg HS3 (3%bv : bv 5) Pgp. prreg HS3 (4%bv : bv 5) Ptp.
pmkst HS3.
(* facts every call below uses *)
assert (Hmfa : alloc_ceiling <= mf) by (clear - Hmf5; lia).
assert (Hsp64 : e_sp0 g <= 2 ^ 64) by (clear - Hshi H47; lia).
assert (HINP : e_n g = 0 \/ In (e_p g, e_n g) (ablocks B ly2 S2)).
{ destruct (d3_inp2 g Hpre) as [H0 | H1]; [left; exact H0 | right].
  destruct Hhb as [Hp _]. apply (Permutation_in _ (Permutation_sym Hp)). right. exact H1. }
assert (U36 : bv_unsigned (ew E 36) = F + 288) by (d3u EX 4%nat (F + 288); clear - Hf4096 HF64; lia).
assert (U34 : bv_unsigned (ew E 34) = F + 224) by (d3u EX 2%nat (F + 224); clear - Hf4096 HF64; lia).
assert (U50 : bv_unsigned (ew E 50) = d3_d1 g i) by (d3u EX 18%nat (d3_d1 g i); clear - HD1; lia).
assert (U52 : bv_unsigned (ew E 52) = d3_n2 g i)
  by (d3u EX 20%nat (d3_n2 g i); unfold d3_n2, d3_d1 in *; clear - D1 D2; lia).
assert (U53 : bv_unsigned (ew E 53) = d3_n3 g i) by (d3u EX 21%nat (d3_n3 g i); clear - HN3; lia).
assert (U24 : bv_unsigned (ew E 24) = d3_ma g i)
  by (rewrite (ER 24%nat 24%bv eq_refl), R24; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew E 25) = d3_mi g i)
  by (rewrite (ER 25%nat 25%bv eq_refl), R25; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = d3_pa g i)
  by (rewrite (ER 21%nat 21%bv eq_refl), R21; apply unsigned_lit_small; lia).
assert (Hsp2 : spZ (ms_regs ms2) = mf)
  by (unfold spZ; rewrite Psp, (ER 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
(* the first put_dec (0x81144): b = ev, p = mf+208 holding 0, v = major, one digit at least *)
assert (VN : val_mem SEGS (rd W2 (ms_mem ms2)) (mf + 208) 8 0).
{ pose proof (d3_reg_vm _ _ _ 2 9 208 216 208 216 _ 208 8 (SLit 0) mf 0 HS3 eq_refl ltac:(left; reflexivity)
    ltac:(rewrite HE1 by lia; exact U9) eq_refl ltac:(lia) ltac:(lia)) as V. exact V. }
assert (VS : forall o, (o = 36 \/ o = 37 \/ o = 38)%nat ->
  aview SEGS (w_H W2) (ms_mem ms2) (shadow_addr F + Z.of_nat o) = Some 0).
{ intros o Ho. apply (aview_of_val_mem1 SEGS); [|lia].
  destruct Ho as [-> | [-> | ->]];
  [ exact (d3_reg_vm _ _ _ 6 38 36 39 36 39 _ 36 1 (SLit 0) (shadow_addr F) 0 HS3 eq_refl
      ltac:(cbn [In]; auto) ltac:(rewrite HE1 by lia; exact U38) eq_refl ltac:(lia) ltac:(lia))
  | exact (d3_reg_vm _ _ _ 6 38 36 39 36 39 _ 37 1 (SLit 0) (shadow_addr F) 0 HS3 eq_refl
      ltac:(cbn [In]; auto) ltac:(rewrite HE1 by lia; exact U38) eq_refl ltac:(lia) ltac:(lia))
  | exact (d3_reg_vm _ _ _ 6 38 36 39 36 39 _ 38 1 (SLit 0) (shadow_addr F) 0 HS3 eq_refl
      ltac:(cbn [In]; auto) ltac:(rewrite HE1 by lia; exact U38) eq_refl ltac:(lia) ltac:(lia)) ]. }
assert (RAE : range_addressable (aview SEGS (w_H W2) (ms_mem ms2)) SHADOW_OFF (SFa g pos + V_ev) N_ev).
{ apply d3_ra_ev; [clear - Hf32; Z.div_mod_to_equations; lia | exact (VS 36%nat ltac:(lia))
  | exact (VS 37%nat ltac:(lia)) | exact (VS 38%nat ltac:(lia))]. }
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?R (Z_to_bv 64 ?X) ?M _) ?MD) ?Q =>
  change (SRr SEGS W2 (cfg_at SEGS X R M MD) Q) end.
eapply SRr_bind.
{ apply (D3PD LAWS PSIG HPD HSTK HEV g pos mf W2 (ms_regs ms2) (ms_mem ms2) _ ly2 S2 (4 * Z.of_nat i + 3)
    0 (d3_ma g i) 1 2516 Hpre HJ4 Hfr Hk Hmfb Hmf32 Pra ltac:(lia) eq_refl).
  - rewrite Psp, (ER 2%nat 2%bv eq_refl). exact R2.
  - rewrite Pgp, (ER 3%nat 3%bv eq_refl). exact R3.
  - rewrite Ptp, (ER 4%nat 4%bv eq_refl). exact R4.
  - rewrite Pa0. exact (EX 4%nat ltac:(lia)).
  - rewrite Pa1, U9. reflexivity.
  - rewrite Pa2, (ER 24%nat 24%bv eq_refl). exact R24.
  - rewrite Pa3. reflexivity.
  - exact Ma.
  - lia.
  - lia.
  - change (put_dec_c.dec_len (d3_ma g i) 1) with (d3_d1 g i). unfold N_ev. lia.
  - exact VN.
  - exact RAE. }
intros W5 c5 _ (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & HP5 & Hfr5 & Hbl5 & HT5 & HG5 & HV5).
change put_dec.EV_PUT_DEC with 0 in HJ5. rewrite Z.add_0_r in HJ5.
rewrite Hfr in Hfr5. rewrite Hsp2 in HT5.
change (put_dec_c.dec_len (d3_ma g i) 1) with (d3_d1 g i) in HT5, HV5.
assert (HFA5 : frame_addr ly5 4 pos = F)
  by (rewrite (d3_fa _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ5 4 pos), <- (d3_fa _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4 4 pos);
      exact HFA).
assert (HPL5 : In (pl, K) (ablocks B ly5 S5)) by (rewrite Hbl5; exact HPL).
assert (HIN5 : In (4, pos) (frames S5)) by (rewrite Hfr5; left; reflexivity).
assert (K4 : d3_keep g pos mf i pl W2 mem2 W5 mem5).
{ apply (d3_keep_call g pos mf i pl W2 mem2 _ ly2 S2 W2 (ms_mem ms2) W5 mem5 _ HT5 Hfr HFA HPL HINP Hmfa Hsp64);
  [| exact K3]. intros a Ha'. unfold d3_wr, M_n1, V_ev, N_ev, V_v, N_v, V_hw in Ha' |- *. fold F in Ha' |- *. clear - Ha' HD1. lia. }
pose proof HJ5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres5 & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 4 pos (proj1 HJ5) HIN5) as (_ & _ & Hfb5 & Hfs5).
rewrite HFA5 in Hfb5, Hfs5. change (fs_frame_bytes 4) with 1024 in Hfb5. change (fs_frame_bytes 4 / 8) with 128 in Hfs5.
lazymatch goal with HS : st_ok _ _ ?ssx _ |- _ =>
  let Kk := eval vm_compute in (run_K A_LIM (SLit 0) [] ssx) in
  jafter_call_keep_hi HS Kk regs5 (mrestrict (w_H W5) mem5) HP5 [0;1;3;4;5;6;7;8;9;10]%nat HS4 end.
match type of HS4 with ?Q -> _ => assert (HQ : Q); [ | specialize (HS4 HQ); clear HQ ] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil;
  (eapply d3_rk2; [ rewrite HE1 by lia; eassumption
    | intros a Ha'; cbn [YP09.r_lo YP09.r_hi] in Ha';
      apply (d3_tcj_pt F pos mf pl K _ ly2 S2 W2 (ms_mem ms2) W5 mem5 _ _ ly5 S5 md5 HT5 Hfr HFA HPL HK8 Hmfa
        (proj1 HJ4) (proj1 HJ5) HPL5);
      [ unfold M_n1, V_ev; fold F;
        clear - Ha' Hmf3 Hmf5 Hf4096 HF64 Hfceil Hp4096 HP64 Hpceil HD1 HN3 HDN2 HK HK8 Hfapp Happ Hsep C1;
        unfold shadow_addr, SHADOW_OFF in *; Z.div_mod_to_equations; lia
      | clear - Ha' Hmf3 Hmf5 Hf4096 HF64 Hfceil Hp4096 HP64 Hpceil HD1 HN3 HDN2 HK HK8 C1;
        unfold shadow_addr, SHADOW_OFF in *; Z.div_mod_to_equations; lia ]
    | intros a Ha'; cbn [YP09.r_wlo YP09.r_whi] in Ha'; d3_pres Hpres5 Hfb5 Hfs5 F Hmf1 Hmf2 HD1 HN3 ]). }
rewrite <- restrict_mkst_fx in HS4.
assert (Hn2def : d3_n2 g i = d3_d1 g i + 1 + put_dec_c.dec_len (d3_mi g i) 1) by reflexivity.
assert (Hn3def : d3_n3 g i = d3_n2 g i + put_dec_c.dec_len (d3_pa g i) 2) by reflexivity.
pose proof (conj Hmf3 (conj Hmf5 (conj Hf4096 (conj HF64 (conj Hfceil (conj Hp4096 (conj HP64 (conj Hpceil (conj HD1 (conj HN3 (conj HDN2 (conj HK (conj HK8 (conj Hfapp (conj Happ (conj Hsep (conj C1 (conj Hf32 (conj Hp16 (conj Hn2def Hn3def)))))))))))))))))))) as HBND.
Ltac d3L FF HBN H := try fold FF in H |- *; clear - HBN H;
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end;
  unfold d3_W, d3_wr, M_n1, V_ev, N_ev, V_v, N_v, V_hw, shadow_addr, SHADOW_OFF in *; Z.div_mod_to_equations; lia.
Ltac d3_env EE HS HEp HEIp HEn HEIn :=
  lazymatch type of HS with st_ok_pi _ _ ?En _ _ =>
  assert (HEn : forall n, (n < 512)%nat -> ew En n = ew EE n)
    by (intros n Hn; rewrite ew_havoc_old by lia; apply HEp; exact Hn);
  assert (HEIn : img_env VAL A_LIM En) by (apply img_env_havoc_hi; [exact HEIp | cbv; lia]) end.
d3_env E HS4 HE1 HEI1 HE2 HEI2.
rewrite Z.add_0_l in HV5.
(* the counter mf+208 now holds d1 (put_dec's post): the region added back at the head *)
pose proof (st_ok_pi_add_region _ _ _ (d3_rmf_n [d3_ch 208 8 (SOff 50 0)]) HS4 eq_refl) as HS5.
match type of HS5 with ?A -> ?B -> _ => assert (HA : A); [|assert (HB : B); [|specialize (HS5 HA HB); clear HA HB]] end.
{ unfold region_ok, d3_rmf_n, d3_ch; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val
    ms_mem restrict mkst].
  rewrite HE2, U9 by lia. split; [clear - Hmf3; lia|]. split; [clear - Hmf3; lia|]. split.
  - intros o Ho. apply (apresent_writable SEGS). apply Hpres5. clear - Ho Hmf1 Hmf2; lia.
  - apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS _ _ mf 208 8 (SOff 50 0) (d3_d1 g i));
    [ apply d3_denot; rewrite HE2 by lia; exact U50 | clear - HD1; zside | zside | exact HV5 ]. }
{ cbn [all_disjoint ss_mem]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val d3_rmf_n].
  rewrite !HE2 by lia. rewrite U9, U33, U39, U38, U27, U41, U54, U55.
  clear - Hmfa Hfceil Hpceil Hf4096 HF64 Hp4096 HP64 HD1 HN3 HK C1.
  unfold shadow_addr, SHADOW_OFF in *. Z.div_mod_to_equations. repeat split; lia. }
clear HS4.
assert (GD1 : garr8 SEGS (rd W5 mem5) (F + 288) (map (fun b : byte => bv_unsigned b) (IdentSpec.DEC (d3_ma g i) 1))).
{ replace (F + 288) with (SFa g pos + V_ev + 0) by (unfold V_ev; fold F; lia). exact HG5. }
clear HG5.
(* run 3: the '.' at ev + d1, the counter to d1 + 1, the second put_dec (0x81190) *)
rewrite Pra. unfold cfg_at.
change mem5 with (ms_mem (mkst regs5 (Z_to_bv 64 (BASE + 2516)) mem5 (seg_rom SEGS))) in HJ5.
paj_run_shc RUNP RUNC HS5 HJ5.
{ eapply (d3_awr _ _ _ _ _ _ _ _ F (shadow_addr F) mf (d3_d1 g i) (d3_n3 g i));
  [apply (HW _ _ HE2); vm_compute; reflexivity | exact HFA5 | reflexivity | lia | lia | lia | lia]. }
rename ms into ms3. rename HJ5 into HJ6.
assert (K5 : d3_keep g pos mf i pl W2 mem2 W5 (ms_mem ms3)).
{ apply (d3_keep_run g pos mf i pl W2 mem2 W5 mem5 (ms_mem ms3) _ _ (d3_d1 g i) (d3_n3 g i) HFr);
  [apply (HW _ _ HE2); vm_compute; reflexivity | lia | lia | exact HZ | exact K4]. }
assert (GD1a : garr8 SEGS (rd W5 (ms_mem ms3)) (F + 288) (map (fun b : byte => bv_unsigned b) (IdentSpec.DEC (d3_ma g i) 1))).
{ apply (d3_garr8_mv W5 W5 mem5 (ms_mem ms3) _ _ GD1). intros x Hx. rewrite length_map in Hx.
  change (Z.of_nat (length (IdentSpec.DEC (d3_ma g i) 1))) with (d3_d1 g i) in Hx.
  apply (d3_fkeep_run _ _ W5 mem5 (ms_mem ms3) F (shadow_addr F) mf (d3_d1 g i) (d3_n3 g i) HFr);
  [apply (HW _ _ HE2); vm_compute; reflexivity | d3L F HBND Hx | d3L F HBND Hx]. }
clear HF HFr HG GD1.
prreg HS5 (10%bv : bv 5) Qa0. prreg HS5 (11%bv : bv 5) Qa1. prreg HS5 (12%bv : bv 5) Qa2. prreg HS5 (13%bv : bv 5) Qa3.
prreg HS5 (1%bv : bv 5) Qra. prreg HS5 (2%bv : bv 5) Qsp. prreg HS5 (3%bv : bv 5) Qgp. prreg HS5 (4%bv : bv 5) Qtp.
pmkst HS5.
(* the second put_dec (0x81190): b = ev, p = mf+208 holding d1 + 1, v = minor, one digit at least *)
assert (Hsp3 : spZ (ms_regs ms3) = mf)
  by (unfold spZ; rewrite Qsp, (ER 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (VN2 : val_mem SEGS (rd W5 (ms_mem ms3)) (mf + 208) 8 (d3_d1 g i + 1)).
{ exact (d3_reg_vm _ _ _ 0 9 208 216 208 216 _ 208 8 (SOff 50 1) mf (d3_d1 g i + 1) HS5 eq_refl
    ltac:(left; reflexivity) ltac:(rewrite HE2 by lia; exact U9)
    ltac:(apply d3_denotc; rewrite HE2 by lia; exact U50) ltac:(clear - HD1; lia) ltac:(lia)). }
assert (VS2 : forall o, (o = 36 \/ o = 37 \/ o = 38)%nat ->
  aview SEGS (w_H W5) (ms_mem ms3) (shadow_addr F + Z.of_nat o) = Some 0).
{ intros o Ho. apply (aview_of_val_mem1 SEGS); [|lia].
  destruct Ho as [-> | [-> | ->]];
  [ exact (d3_reg_vm _ _ _ 6 38 36 39 36 39 _ 36 1 (SLit 0) (shadow_addr F) 0 HS5 eq_refl
      ltac:(cbn [In]; auto) ltac:(rewrite HE2 by lia; exact U38) eq_refl ltac:(lia) ltac:(lia))
  | exact (d3_reg_vm _ _ _ 6 38 36 39 36 39 _ 37 1 (SLit 0) (shadow_addr F) 0 HS5 eq_refl
      ltac:(cbn [In]; auto) ltac:(rewrite HE2 by lia; exact U38) eq_refl ltac:(lia) ltac:(lia))
  | exact (d3_reg_vm _ _ _ 6 38 36 39 36 39 _ 38 1 (SLit 0) (shadow_addr F) 0 HS5 eq_refl
      ltac:(cbn [In]; auto) ltac:(rewrite HE2 by lia; exact U38) eq_refl ltac:(lia) ltac:(lia)) ]. }
assert (RAE2 : range_addressable (aview SEGS (w_H W5) (ms_mem ms3)) SHADOW_OFF (SFa g pos + V_ev) N_ev).
{ apply d3_ra_ev; [clear - Hf32; Z.div_mod_to_equations; lia | exact (VS2 36%nat ltac:(lia))
  | exact (VS2 37%nat ltac:(lia)) | exact (VS2 38%nat ltac:(lia))]. }
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?R (Z_to_bv 64 ?X) ?M _) ?MD) ?Q =>
  change (SRr SEGS W5 (cfg_at SEGS X R M MD) Q) end.
eapply SRr_bind.
{ apply (D3PD LAWS PSIG HPD HSTK HEV g pos mf W5 (ms_regs ms3) (ms_mem ms3) _ ly5 S5 (4 * Z.of_nat i + 3)
    (d3_d1 g i + 1) (d3_mi g i) 1 2592 Hpre HJ6 Hfr5 Hk Hmfb Hmf32 Qra ltac:(lia) eq_refl).
  - rewrite Qsp, (ER 2%nat 2%bv eq_refl). exact R2.
  - rewrite Qgp, (ER 3%nat 3%bv eq_refl). exact R3.
  - rewrite Qtp, (ER 4%nat 4%bv eq_refl). exact R4.
  - rewrite Qa0. exact (EX 4%nat ltac:(lia)).
  - rewrite Qa1, U9. reflexivity.
  - rewrite Qa2, (ER 25%nat 25%bv eq_refl). exact R25.
  - rewrite Qa3. reflexivity.
  - exact Mi.
  - lia.
  - clear - HD1; lia.
  - rewrite <- Hn2def. unfold N_ev. clear - HN3 HDN2; lia.
  - exact VN2.
  - exact RAE2. }
intros W7 c7 _ (ly7 & S7 & regs7 & mem7 & md7 & -> & HJ7 & HP7 & Hfr7 & Hbl7 & HT7 & HG7 & HV7).
change put_dec.EV_PUT_DEC with 0 in HJ7. rewrite Z.add_0_r in HJ7.
rewrite Hfr5 in Hfr7. rewrite Hsp3 in HT7. rewrite <- Hn2def in HV7.
assert (HFA7 : frame_addr ly7 4 pos = F)
  by (rewrite (d3_fa _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ7 4 pos), <- (d3_fa _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ6 4 pos);
      exact HFA5).
assert (HPL7 : In (pl, K) (ablocks B ly7 S7)) by (rewrite Hbl7; exact HPL5).
assert (HIN7 : In (4, pos) (frames S7)) by (rewrite Hfr7; left; reflexivity).
assert (HINP5 : e_n g = 0 \/ In (e_p g, e_n g) (ablocks B ly5 S5)) by (rewrite Hbl5; exact HINP).
assert (K6 : d3_keep g pos mf i pl W2 mem2 W7 mem7).
{ apply (d3_keep_call g pos mf i pl W2 mem2 _ ly5 S5 W5 (ms_mem ms3) W7 mem7 _ HT7 Hfr5 HFA5 HPL5 HINP5 Hmfa Hsp64);
  [| exact K5]. intros a Ha'. d3L F HBND Ha'. }
pose proof HJ7 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres7 & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 4 pos (proj1 HJ7) HIN7) as (_ & _ & Hfb7 & Hfs7).
rewrite HFA7 in Hfb7, Hfs7. change (fs_frame_bytes 4) with 1024 in Hfb7. change (fs_frame_bytes 4 / 8) with 128 in Hfs7.
assert (GD1b : garr8 SEGS (rd W7 mem7) (F + 288) (map (fun b : byte => bv_unsigned b) (IdentSpec.DEC (d3_ma g i) 1))).
{ apply (d3_garr8_mv W5 W7 (ms_mem ms3) mem7 _ _ GD1a). intros x Hx. rewrite length_map in Hx.
  change (Z.of_nat (length (IdentSpec.DEC (d3_ma g i) 1))) with (d3_d1 g i) in Hx.
  apply (d3_fkeep_call F pos _ ly5 S5 W5 (ms_mem ms3) W7 mem7 mf _ HT7 Hfr5 HFA5); d3L F HBND Hx. }
assert (GD2 : garr8 SEGS (rd W7 mem7) (F + 288 + d3_d1 g i + 1)
  (map (fun b : byte => bv_unsigned b) (IdentSpec.DEC (d3_mi g i) 1))).
{ replace (F + 288 + d3_d1 g i + 1) with (SFa g pos + V_ev + (d3_d1 g i + 1)) by (unfold V_ev; fold F; lia). exact HG7. }
clear HG7 GD1a.
lazymatch goal with HS : st_ok _ _ ?ssx _ |- _ =>
  let Kk := eval vm_compute in (run_K A_LIM (SLit 0) [] ssx) in
  jafter_call_keep_hi HS Kk regs7 (mrestrict (w_H W7) mem7) HP7 [1;2;3;4;5;6;7;8;9;10]%nat HS6 end.
match type of HS6 with ?Q -> _ => assert (HQ : Q); [ | specialize (HS6 HQ); clear HQ ] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil;
  (eapply d3_rk2; [ rewrite HE2 by lia; eassumption
    | intros a Ha'; cbn [YP09.r_lo YP09.r_hi] in Ha';
      apply (d3_tcj_pt F pos mf pl K _ ly5 S5 W5 (ms_mem ms3) W7 mem7 _ _ ly7 S7 md7 HT7 Hfr5 HFA5 HPL5 HK8 Hmfa
        (proj1 HJ6) (proj1 HJ7) HPL7); d3L F HBND Ha'
    | intros a Ha'; cbn [YP09.r_wlo YP09.r_whi] in Ha'; d3_pres Hpres7 Hfb7 Hfs7 F Hmf1 Hmf2 HD1 HN3 ]). }
rewrite <- restrict_mkst_fx in HS6.
clear HS5.
d3_env E HS6 HE2 HEI2 HE3 HEI3.
pose proof (st_ok_pi_add_region _ _ _ (d3_rmf_n [d3_ch 208 8 (SOff 52 0)]) HS6 eq_refl) as HS7.
match type of HS7 with ?A -> ?B -> _ => assert (HA : A); [|assert (HB : B); [|specialize (HS7 HA HB); clear HA HB]] end.
{ unfold region_ok, d3_rmf_n, d3_ch; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val
    ms_mem restrict mkst].
  rewrite HE3, U9 by lia. split; [clear - Hmf3; lia|]. split; [clear - Hmf3; lia|]. split.
  - intros o Ho. apply (apresent_writable SEGS). apply Hpres7. clear - Ho Hmf1 Hmf2; lia.
  - apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS _ _ mf 208 8 (SOff 52 0) (d3_n2 g i));
    [ apply d3_denot; rewrite HE3 by lia; exact U52 | clear - HD1 HN3 HDN2; zside | zside | exact HV7 ]. }
{ cbn [all_disjoint ss_mem]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val d3_rmf_n].
  rewrite !HE3 by lia. rewrite U9, U33, U39, U38, U27, U41, U54, U55.
  clear - Hmfa Hfceil Hpceil Hf4096 HF64 Hp4096 HP64 HD1 HN3 HK C1.
  unfold shadow_addr, SHADOW_OFF in *. Z.div_mod_to_equations. repeat split; lia. }
clear HS6.
(* run 4: the third put_dec's arguments (0x811a4) *)
rewrite Qra. unfold cfg_at.
change mem7 with (ms_mem (mkst regs7 (Z_to_bv 64 (BASE + 2592)) mem7 (seg_rom SEGS))) in HJ7.
paj_run_shc RUNP RUNC HS7 HJ7.
{ eapply (d3_awr _ _ _ _ _ _ _ _ F (shadow_addr F) mf (d3_d1 g i) (d3_n3 g i));
  [apply (HW _ _ HE3); vm_compute; reflexivity | exact HFA7 | reflexivity | lia | lia | lia | lia]. }
rename ms into ms4. rename HJ7 into HJ8.
assert (K7 : d3_keep g pos mf i pl W2 mem2 W7 (ms_mem ms4)).
{ apply (d3_keep_run g pos mf i pl W2 mem2 W7 mem7 (ms_mem ms4) _ _ (d3_d1 g i) (d3_n3 g i) HFr);
  [apply (HW _ _ HE3); vm_compute; reflexivity | lia | lia | exact HZ | exact K6]. }
assert (GD1c : garr8 SEGS (rd W7 (ms_mem ms4)) (F + 288) (map (fun b : byte => bv_unsigned b) (IdentSpec.DEC (d3_ma g i) 1))).
{ apply (d3_garr8_mv W7 W7 mem7 (ms_mem ms4) _ _ GD1b). intros x Hx. rewrite length_map in Hx.
  change (Z.of_nat (length (IdentSpec.DEC (d3_ma g i) 1))) with (d3_d1 g i) in Hx.
  apply (d3_fkeep_run _ _ W7 mem7 (ms_mem ms4) F (shadow_addr F) mf (d3_d1 g i) (d3_n3 g i) HFr);
  [apply (HW _ _ HE3); vm_compute; reflexivity | d3L F HBND Hx | d3L F HBND Hx]. }
assert (GD2a : garr8 SEGS (rd W7 (ms_mem ms4)) (F + 288 + d3_d1 g i + 1)
  (map (fun b : byte => bv_unsigned b) (IdentSpec.DEC (d3_mi g i) 1))).
{ apply (d3_garr8_mv W7 W7 mem7 (ms_mem ms4) _ _ GD2). intros x Hx. rewrite length_map in Hx.
  change (Z.of_nat (length (IdentSpec.DEC (d3_mi g i) 1))) with (put_dec_c.dec_len (d3_mi g i) 1) in Hx.
  apply (d3_fkeep_run _ _ W7 mem7 (ms_mem ms4) F (shadow_addr F) mf (d3_d1 g i) (d3_n3 g i) HFr);
  [apply (HW _ _ HE3); vm_compute; reflexivity | d3L F HBND Hx | d3L F HBND Hx]. }
clear HF HFr HG GD1b GD2.
prreg HS7 (10%bv : bv 5) Ta0. prreg HS7 (11%bv : bv 5) Ta1. prreg HS7 (12%bv : bv 5) Ta2. prreg HS7 (13%bv : bv 5) Ta3.
prreg HS7 (1%bv : bv 5) Tra. prreg HS7 (2%bv : bv 5) Tsp. prreg HS7 (3%bv : bv 5) Tgp. prreg HS7 (4%bv : bv 5) Ttp.
pmkst HS7.
(* the third put_dec (0x811a4): b = ev, p = mf+208 holding n2, v = patch, two digits at least *)
assert (Hsp4 : spZ (ms_regs ms4) = mf)
  by (unfold spZ; rewrite Tsp, (ER 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (VN3 : val_mem SEGS (rd W7 (ms_mem ms4)) (mf + 208) 8 (d3_n2 g i)).
{ exact (d3_reg_vm _ _ _ 0 9 208 216 208 216 _ 208 8 (SOff 52 0) mf (d3_n2 g i) HS7 eq_refl
    ltac:(left; reflexivity) ltac:(rewrite HE3 by lia; exact U9)
    ltac:(apply d3_denot; rewrite HE3 by lia; exact U52) ltac:(clear - HD1 HN3 HDN2; lia) ltac:(lia)). }
assert (VS3 : forall o, (o = 36 \/ o = 37 \/ o = 38)%nat ->
  aview SEGS (w_H W7) (ms_mem ms4) (shadow_addr F + Z.of_nat o) = Some 0).
{ intros o Ho. apply (aview_of_val_mem1 SEGS); [|lia].
  destruct Ho as [-> | [-> | ->]];
  [ exact (d3_reg_vm _ _ _ 6 38 36 39 36 39 _ 36 1 (SLit 0) (shadow_addr F) 0 HS7 eq_refl
      ltac:(cbn [In]; auto) ltac:(rewrite HE3 by lia; exact U38) eq_refl ltac:(lia) ltac:(lia))
  | exact (d3_reg_vm _ _ _ 6 38 36 39 36 39 _ 37 1 (SLit 0) (shadow_addr F) 0 HS7 eq_refl
      ltac:(cbn [In]; auto) ltac:(rewrite HE3 by lia; exact U38) eq_refl ltac:(lia) ltac:(lia))
  | exact (d3_reg_vm _ _ _ 6 38 36 39 36 39 _ 38 1 (SLit 0) (shadow_addr F) 0 HS7 eq_refl
      ltac:(cbn [In]; auto) ltac:(rewrite HE3 by lia; exact U38) eq_refl ltac:(lia) ltac:(lia)) ]. }
assert (RAE3 : range_addressable (aview SEGS (w_H W7) (ms_mem ms4)) SHADOW_OFF (SFa g pos + V_ev) N_ev).
{ apply d3_ra_ev; [clear - Hf32; Z.div_mod_to_equations; lia | exact (VS3 36%nat ltac:(lia))
  | exact (VS3 37%nat ltac:(lia)) | exact (VS3 38%nat ltac:(lia))]. }
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?R (Z_to_bv 64 ?X) ?M _) ?MD) ?Q =>
  change (SRr SEGS W7 (cfg_at SEGS X R M MD) Q) end.
eapply SRr_bind.
{ apply (D3PD LAWS PSIG HPD HSTK HEV g pos mf W7 (ms_regs ms4) (ms_mem ms4) _ ly7 S7 (4 * Z.of_nat i + 3)
    (d3_n2 g i) (d3_pa g i) 2 2612 Hpre HJ8 Hfr7 Hk Hmfb Hmf32 Tra ltac:(lia) eq_refl).
  - rewrite Tsp, (ER 2%nat 2%bv eq_refl). exact R2.
  - rewrite Tgp, (ER 3%nat 3%bv eq_refl). exact R3.
  - rewrite Ttp, (ER 4%nat 4%bv eq_refl). exact R4.
  - rewrite Ta0. exact (EX 4%nat ltac:(lia)).
  - rewrite Ta1, U9. reflexivity.
  - rewrite Ta2, (ER 21%nat 21%bv eq_refl). exact R21.
  - rewrite Ta3. reflexivity.
  - exact Mp.
  - lia.
  - clear - HD1 HDN2; lia.
  - rewrite <- Hn3def. unfold N_ev. clear - HN3; lia.
  - exact VN3.
  - exact RAE3. }
intros W9 c9 _ (ly9 & S9 & regs9 & mem9 & md9 & -> & HJ9 & HP9 & Hfr9 & Hbl9 & HT9 & HG9 & HV9).
change put_dec.EV_PUT_DEC with 0 in HJ9. rewrite Z.add_0_r in HJ9.
rewrite Hfr7 in Hfr9. rewrite Hsp4 in HT9. rewrite <- Hn3def in HV9.
assert (HFA9 : frame_addr ly9 4 pos = F)
  by (rewrite (d3_fa _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ9 4 pos), <- (d3_fa _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ8 4 pos);
      exact HFA7).
assert (HPL9 : In (pl, K) (ablocks B ly9 S9)) by (rewrite Hbl9; exact HPL7).
assert (HIN9 : In (4, pos) (frames S9)) by (rewrite Hfr9; left; reflexivity).
assert (HINP7 : e_n g = 0 \/ In (e_p g, e_n g) (ablocks B ly7 S7)) by (rewrite Hbl7; exact HINP5).
assert (K8 : d3_keep g pos mf i pl W2 mem2 W9 mem9).
{ apply (d3_keep_call g pos mf i pl W2 mem2 _ ly7 S7 W7 (ms_mem ms4) W9 mem9 _ HT9 Hfr7 HFA7 HPL7 HINP7 Hmfa Hsp64);
  [| exact K7]. intros a Ha'. d3L F HBND Ha'. }
pose proof HJ9 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres9 & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 4 pos (proj1 HJ9) HIN9) as (_ & _ & Hfb9 & Hfs9).
rewrite HFA9 in Hfb9, Hfs9. change (fs_frame_bytes 4) with 1024 in Hfb9. change (fs_frame_bytes 4 / 8) with 128 in Hfs9.
assert (GD1d : garr8 SEGS (rd W9 mem9) (F + 288) (map (fun b : byte => bv_unsigned b) (IdentSpec.DEC (d3_ma g i) 1))).
{ apply (d3_garr8_mv W7 W9 (ms_mem ms4) mem9 _ _ GD1c). intros x Hx. rewrite length_map in Hx.
  change (Z.of_nat (length (IdentSpec.DEC (d3_ma g i) 1))) with (d3_d1 g i) in Hx.
  apply (d3_fkeep_call F pos _ ly7 S7 W7 (ms_mem ms4) W9 mem9 mf _ HT9 Hfr7 HFA7); d3L F HBND Hx. }
assert (GD2b : garr8 SEGS (rd W9 mem9) (F + 288 + d3_d1 g i + 1)
  (map (fun b : byte => bv_unsigned b) (IdentSpec.DEC (d3_mi g i) 1))).
{ apply (d3_garr8_mv W7 W9 (ms_mem ms4) mem9 _ _ GD2a). intros x Hx. rewrite length_map in Hx.
  change (Z.of_nat (length (IdentSpec.DEC (d3_mi g i) 1))) with (put_dec_c.dec_len (d3_mi g i) 1) in Hx.
  apply (d3_fkeep_call F pos _ ly7 S7 W7 (ms_mem ms4) W9 mem9 mf _ HT9 Hfr7 HFA7); d3L F HBND Hx. }
assert (GD3 : garr8 SEGS (rd W9 mem9) (F + 288 + d3_n2 g i)
  (map (fun b : byte => bv_unsigned b) (IdentSpec.DEC (d3_pa g i) 2))).
{ replace (F + 288 + d3_n2 g i) with (SFa g pos + V_ev + d3_n2 g i) by (unfold V_ev; fold F; lia). exact HG9. }
clear HG9 GD1c GD2a.
lazymatch goal with HS : st_ok _ _ ?ssx _ |- _ =>
  let Kk := eval vm_compute in (run_K A_LIM (SLit 0) [] ssx) in
  jafter_call_keep_hi HS Kk regs9 (mrestrict (w_H W9) mem9) HP9 [1;2;3;4;5;6;7;8;9;10]%nat HS8 end.
match type of HS8 with ?Q -> _ => assert (HQ : Q); [ | specialize (HS8 HQ); clear HQ ] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil;
  (eapply d3_rk2; [ rewrite HE3 by lia; eassumption
    | intros a Ha'; cbn [YP09.r_lo YP09.r_hi] in Ha';
      apply (d3_tcj_pt F pos mf pl K _ ly7 S7 W7 (ms_mem ms4) W9 mem9 _ _ ly9 S9 md9 HT9 Hfr7 HFA7 HPL7 HK8 Hmfa
        (proj1 HJ8) (proj1 HJ9) HPL9); d3L F HBND Ha'
    | intros a Ha'; cbn [YP09.r_wlo YP09.r_whi] in Ha'; d3_pres Hpres9 Hfb9 Hfs9 F Hmf1 Hmf2 HD1 HN3 ]). }
rewrite <- restrict_mkst_fx in HS8.
clear HS7.
d3_env E HS8 HE3 HEI3 HE4 HEI4.
pose proof (st_ok_pi_add_region _ _ _ (d3_rmf_n [d3_ch 208 8 (SOff 53 0)]) HS8 eq_refl) as HS9.
match type of HS9 with ?A -> ?B -> _ => assert (HA : A); [|assert (HB : B); [|specialize (HS9 HA HB); clear HA HB]] end.
{ unfold region_ok, d3_rmf_n, d3_ch; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val
    ms_mem restrict mkst].
  rewrite HE4, U9 by lia. split; [clear - Hmf3; lia|]. split; [clear - Hmf3; lia|]. split.
  - intros o Ho. apply (apresent_writable SEGS). apply Hpres9. clear - Ho Hmf1 Hmf2; lia.
  - apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS _ _ mf 208 8 (SOff 53 0) (d3_n3 g i));
    [ apply d3_denot; rewrite HE4 by lia; exact U53 | clear - HN3; zside | zside | exact HV9 ]. }
{ cbn [all_disjoint ss_mem]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val d3_rmf_n].
  rewrite !HE4 by lia. rewrite U9, U33, U39, U38, U27, U41, U54, U55.
  clear - Hmfa Hfceil Hpceil Hf4096 HF64 Hp4096 HP64 HD1 HN3 HK C1.
  unfold shadow_addr, SHADOW_OFF in *. Z.div_mod_to_equations. repeat split; lia. }
clear HS8.
(* run 5: the NUL at ev + n3, reac_identity_reac_ver_str's arguments (0x811e8) *)
rewrite Tra. unfold cfg_at.
change mem9 with (ms_mem (mkst regs9 (Z_to_bv 64 (BASE + 2612)) mem9 (seg_rom SEGS))) in HJ9.
paj_run_shc RUNP RUNC HS9 HJ9.
{ eapply (d3_awr _ _ _ _ _ _ _ _ F (shadow_addr F) mf (d3_d1 g i) (d3_n3 g i));
  [apply (HW _ _ HE4); vm_compute; reflexivity | exact HFA9 | reflexivity | lia | lia | lia | lia]. }
rename ms into ms5. rename HJ9 into HJ10.
assert (K9 : d3_keep g pos mf i pl W2 mem2 W9 (ms_mem ms5)).
{ apply (d3_keep_run g pos mf i pl W2 mem2 W9 mem9 (ms_mem ms5) _ _ (d3_d1 g i) (d3_n3 g i) HFr);
  [apply (HW _ _ HE4); vm_compute; reflexivity | lia | lia | exact HZ | exact K8]. }
assert (GD1e : garr8 SEGS (rd W9 (ms_mem ms5)) (F + 288) (map (fun b : byte => bv_unsigned b) (IdentSpec.DEC (d3_ma g i) 1))).
{ apply (d3_garr8_mv W9 W9 mem9 (ms_mem ms5) _ _ GD1d). intros x Hx. rewrite length_map in Hx.
  change (Z.of_nat (length (IdentSpec.DEC (d3_ma g i) 1))) with (d3_d1 g i) in Hx.
  apply (d3_fkeep_run _ _ W9 mem9 (ms_mem ms5) F (shadow_addr F) mf (d3_d1 g i) (d3_n3 g i) HFr);
  [apply (HW _ _ HE4); vm_compute; reflexivity | d3L F HBND Hx | d3L F HBND Hx]. }
assert (GD2c : garr8 SEGS (rd W9 (ms_mem ms5)) (F + 288 + d3_d1 g i + 1)
  (map (fun b : byte => bv_unsigned b) (IdentSpec.DEC (d3_mi g i) 1))).
{ apply (d3_garr8_mv W9 W9 mem9 (ms_mem ms5) _ _ GD2b). intros x Hx. rewrite length_map in Hx.
  change (Z.of_nat (length (IdentSpec.DEC (d3_mi g i) 1))) with (put_dec_c.dec_len (d3_mi g i) 1) in Hx.
  apply (d3_fkeep_run _ _ W9 mem9 (ms_mem ms5) F (shadow_addr F) mf (d3_d1 g i) (d3_n3 g i) HFr);
  [apply (HW _ _ HE4); vm_compute; reflexivity | d3L F HBND Hx | d3L F HBND Hx]. }
assert (GD3a : garr8 SEGS (rd W9 (ms_mem ms5)) (F + 288 + d3_n2 g i)
  (map (fun b : byte => bv_unsigned b) (IdentSpec.DEC (d3_pa g i) 2))).
{ apply (d3_garr8_mv W9 W9 mem9 (ms_mem ms5) _ _ GD3). intros x Hx. rewrite length_map in Hx.
  change (Z.of_nat (length (IdentSpec.DEC (d3_pa g i) 2))) with (put_dec_c.dec_len (d3_pa g i) 2) in Hx.
  apply (d3_fkeep_run _ _ W9 mem9 (ms_mem ms5) F (shadow_addr F) mf (d3_d1 g i) (d3_n3 g i) HFr);
  [apply (HW _ _ HE4); vm_compute; reflexivity | d3L F HBND Hx | d3L F HBND Hx]. }
clear HF HFr HG GD1d GD2b GD3.
prreg HS9 (10%bv : bv 5) Va0. prreg HS9 (11%bv : bv 5) Va1. prreg HS9 (12%bv : bv 5) Va2. prreg HS9 (13%bv : bv 5) Va3.
prreg HS9 (14%bv : bv 5) Va4.
prreg HS9 (1%bv : bv 5) Vra. prreg HS9 (2%bv : bv 5) Vsp. prreg HS9 (3%bv : bv 5) Vgp. prreg HS9 (4%bv : bv 5) Vtp.
pmkst HS9.
(* reac_identity_reac_ver_str (0x811e8): ma, mi, pa into v (20 bytes); it writes VER and its NUL, returns LV = n3 *)
assert (Hsp5 : spZ (ms_regs ms5) = mf)
  by (unfold spZ; rewrite Vsp, (ER 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (VSV : forall o z, (o = 28 /\ z = 0 \/ o = 29 /\ z = 0 \/ o = 30 /\ z = 4)%nat ->
  aview SEGS (w_H W9) (ms_mem ms5) (shadow_addr F + Z.of_nat o) = Some (Z.of_nat z)).
{ intros o z Ho. apply (aview_of_val_mem1 SEGS); [|lia].
  destruct Ho as [[-> ->] | [[-> ->] | [-> ->]]];
  [ exact (d3_reg_vm _ _ _ 5 38 28 31 28 31 _ 28 1 (SLit 0) (shadow_addr F) 0 HS9 eq_refl
      ltac:(cbn [In]; auto) ltac:(rewrite HE4 by lia; exact U38) eq_refl ltac:(lia) ltac:(lia))
  | exact (d3_reg_vm _ _ _ 5 38 28 31 28 31 _ 29 1 (SLit 0) (shadow_addr F) 0 HS9 eq_refl
      ltac:(cbn [In]; auto) ltac:(rewrite HE4 by lia; exact U38) eq_refl ltac:(lia) ltac:(lia))
  | exact (d3_reg_vm _ _ _ 5 38 28 31 28 31 _ 30 1 (SLit 4) (shadow_addr F) 4 HS9 eq_refl
      ltac:(cbn [In]; auto) ltac:(rewrite HE4 by lia; exact U38) eq_refl ltac:(lia) ltac:(lia)) ]. }
assert (RAV : range_addressable (aview SEGS (w_H W9) (ms_mem ms5)) SHADOW_OFF (SFa g pos + V_v) N_v).
{ apply d3_ra_v; [clear - Hf32; Z.div_mod_to_equations; lia | exact (VSV 28%nat 0%nat ltac:(lia))
  | exact (VSV 29%nat 0%nat ltac:(lia)) | exact (VSV 30%nat 4%nat ltac:(lia))]. }
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?R (Z_to_bv 64 ?X) ?M _) ?MD) ?Q =>
  change (SRr SEGS W9 (cfg_at SEGS X R M MD) Q) end.
eapply SRr_bind.
{ apply (D3VS LAWS PSIG HVS HSTK g pos mf W9 (ms_regs ms5) (ms_mem ms5) _ ly9 S9 (4 * Z.of_nat i + 3)
    (d3_ma g i) (d3_mi g i) (d3_pa g i) 2680 HJ10 Hfr9 Hmfb Hmf32 Vra ltac:(lia) eq_refl).
  - rewrite Vsp, (ER 2%nat 2%bv eq_refl). exact R2.
  - rewrite Vgp, (ER 3%nat 3%bv eq_refl). exact R3.
  - rewrite Vtp, (ER 4%nat 4%bv eq_refl). exact R4.
  - rewrite Va0, (ER 24%nat 24%bv eq_refl). exact R24.
  - rewrite Va1, (ER 25%nat 25%bv eq_refl). exact R25.
  - rewrite Va2, (ER 21%nat 21%bv eq_refl). exact R21.
  - rewrite Va3. exact (EX 2%nat ltac:(lia)).
  - rewrite Va4. reflexivity.
  - exact Ma.
  - exact Mi.
  - exact Mp.
  - exact RAV. }
intros W11 c11 _ (-> & ly11 & S11 & regs11 & mem11 & md11 & -> & HJ11 & HP11 & Hbl11 & Hfr11 & Hif).
change reac_identity_reac_ver_str.EV_REAC_VER_STR with 0 in HJ11. rewrite Z.add_0_r in HJ11.
rewrite Hfr9 in Hfr11.
assert (Hnf : reac_identity_reac_ver_str.rvs_fails (SFa g pos + V_v) 20 = false).
{ unfold reac_identity_reac_ver_str.rvs_fails. apply orb_false_iff. split; [|reflexivity].
  apply Z.eqb_neq. unfold V_v. fold F. clear - Hf4096. lia. }
rewrite Hnf in Hif. destruct Hif as (Ha011 & HGV & HT11).
assert (HLV : reac_identity_reac_ver_str.rvs_LV (d3_ma g i) (d3_mi g i) (d3_pa g i) = d3_n3 g i).
{ unfold reac_identity_reac_ver_str.rvs_LV. rewrite <- (proj2 (d3_ev _ _ _ Ma Mi Mp)). reflexivity. }
rewrite HLV in Ha011, HT11. rewrite Hsp5 in HT11.
assert (HFA11 : frame_addr ly11 4 pos = F)
  by (rewrite (d3_fa _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ11 4 pos), <- (d3_fa _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ10 4 pos);
      exact HFA9).
assert (HPL11 : In (pl, K) (ablocks B ly11 S11)) by exact (Permutation_in _ (Permutation_sym Hbl11) HPL9).
assert (HIN11 : In (4, pos) (frames S11)) by (rewrite Hfr11; left; reflexivity).
assert (HINP9 : e_n g = 0 \/ In (e_p g, e_n g) (ablocks B ly9 S9)) by (rewrite Hbl9; exact HINP7).
assert (K10 : d3_keep g pos mf i pl W2 mem2 W9 mem11).
{ apply (d3_keep_call g pos mf i pl W2 mem2 _ ly9 S9 W9 (ms_mem ms5) W9 mem11 _ HT11 Hfr9 HFA9 HPL9 HINP9 Hmfa Hsp64);
  [| exact K9]. intros a Ha'. d3L F HBND Ha'. }
pose proof HJ11 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres11 & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 4 pos (proj1 HJ11) HIN11) as (_ & _ & Hfb11 & Hfs11).
rewrite HFA11 in Hfb11, Hfs11. change (fs_frame_bytes 4) with 1024 in Hfb11. change (fs_frame_bytes 4 / 8) with 128 in Hfs11.
assert (GD1f : garr8 SEGS (rd W9 mem11) (F + 288) (map (fun b : byte => bv_unsigned b) (IdentSpec.DEC (d3_ma g i) 1))).
{ apply (d3_garr8_mv W9 W9 (ms_mem ms5) mem11 _ _ GD1e). intros x Hx. rewrite length_map in Hx.
  change (Z.of_nat (length (IdentSpec.DEC (d3_ma g i) 1))) with (d3_d1 g i) in Hx.
  apply (d3_fkeep_call F pos _ ly9 S9 W9 (ms_mem ms5) W9 mem11 mf _ HT11 Hfr9 HFA9); d3L F HBND Hx. }
assert (GD2d : garr8 SEGS (rd W9 mem11) (F + 288 + d3_d1 g i + 1)
  (map (fun b : byte => bv_unsigned b) (IdentSpec.DEC (d3_mi g i) 1))).
{ apply (d3_garr8_mv W9 W9 (ms_mem ms5) mem11 _ _ GD2c). intros x Hx. rewrite length_map in Hx.
  change (Z.of_nat (length (IdentSpec.DEC (d3_mi g i) 1))) with (put_dec_c.dec_len (d3_mi g i) 1) in Hx.
  apply (d3_fkeep_call F pos _ ly9 S9 W9 (ms_mem ms5) W9 mem11 mf _ HT11 Hfr9 HFA9); d3L F HBND Hx. }
assert (GD3b : garr8 SEGS (rd W9 mem11) (F + 288 + d3_n2 g i)
  (map (fun b : byte => bv_unsigned b) (IdentSpec.DEC (d3_pa g i) 2))).
{ apply (d3_garr8_mv W9 W9 (ms_mem ms5) mem11 _ _ GD3a). intros x Hx. rewrite length_map in Hx.
  change (Z.of_nat (length (IdentSpec.DEC (d3_pa g i) 2))) with (put_dec_c.dec_len (d3_pa g i) 2) in Hx.
  apply (d3_fkeep_call F pos _ ly9 S9 W9 (ms_mem ms5) W9 mem11 mf _ HT11 Hfr9 HFA9); d3L F HBND Hx. }
assert (GV : garr8 SEGS (rd W9 mem11) (F + 224) (reac_identity_reac_ver_str.rvs_bytes (d3_ma g i) (d3_mi g i) (d3_pa g i))).
{ replace (F + 224) with (SFa g pos + V_v) by (unfold V_v; fold F; lia). exact HGV. }
clear HGV GD1e GD2c GD3a.
lazymatch goal with HS : st_ok _ _ ?ssx _ |- _ =>
  let Kk := eval vm_compute in (run_K A_LIM (SLit 0) [] ssx) in
  jafter_call_keep_hi HS Kk regs11 (mrestrict (w_H W9) mem11) HP11 [0;1;2;3;4;5;6;7;8;9;10]%nat HS10 end.
match type of HS10 with ?Q -> _ => assert (HQ : Q); [ | specialize (HS10 HQ); clear HQ ] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil;
  (eapply d3_rk2; [ rewrite HE4 by lia; eassumption
    | intros a Ha'; cbn [YP09.r_lo YP09.r_hi] in Ha';
      apply (d3_tcj_pt F pos mf pl K _ ly9 S9 W9 (ms_mem ms5) W9 mem11 _ _ ly11 S11 md11 HT11 Hfr9 HFA9 HPL9 HK8 Hmfa
        (proj1 HJ10) (proj1 HJ11) HPL11); d3L F HBND Ha'
    | intros a Ha'; cbn [YP09.r_wlo YP09.r_whi] in Ha'; d3_pres Hpres11 Hfb11 Hfs11 F Hmf1 Hmf2 HD1 HN3 ]). }
rewrite <- restrict_mkst_fx in HS10.
clear HS9.
d3_env E HS10 HE4 HEI4 HE5 HEI5.
pose proof (st_ok_pi_set_reg _ _ _ (10%bv : bv 5) (SOff 53 0) HS10
  ltac:(intros Hc; apply (f_equal bv_unsigned) in Hc; vm_compute in Hc; discriminate)
  ltac:(cbn [ms_regs restrict mkst]; rewrite Ha011; symmetry; apply d3_denot; rewrite HE5 by lia; exact U53)) as HS11.
clear HS10.
lazymatch type of HS11 with st_ok_pi _ _ _ ?ss _ =>
  let v := eval vm_compute in ss in change ss with v in HS11 end.
(* run 6: the arguments of the second bcmp (0x81208): v, ev, n3 + 1 *)
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ ?P _ _) _) _ => replace P with (Z_to_bv 64 (BASE + 2680)) by exact (eq_sym Vra) end.
unfold cfg_at.
change mem11 with (ms_mem (mkst regs11 (Z_to_bv 64 (BASE + 2680)) mem11 (seg_rom SEGS))) in HJ11.
paj_run_shc RUNP RUNC HS11 HJ11.
{ eapply (d3_awr _ _ _ _ _ _ _ _ F (shadow_addr F) mf (d3_d1 g i) (d3_n3 g i));
  [apply (HW _ _ HE5); vm_compute; reflexivity | exact HFA11 | reflexivity | lia | lia | lia | lia]. }
rename ms into ms6. rename HJ11 into HJ12.
assert (K11 : d3_keep g pos mf i pl W2 mem2 W9 (ms_mem ms6)).
{ apply (d3_keep_run g pos mf i pl W2 mem2 W9 mem11 (ms_mem ms6) _ _ (d3_d1 g i) (d3_n3 g i) HFr);
  [apply (HW _ _ HE5); vm_compute; reflexivity | lia | lia | exact HZ | exact K10]. }
assert (GD1g : garr8 SEGS (rd W9 (ms_mem ms6)) (F + 288) (map (fun b : byte => bv_unsigned b) (IdentSpec.DEC (d3_ma g i) 1))).
{ apply (d3_garr8_mv W9 W9 mem11 (ms_mem ms6) _ _ GD1f). intros x Hx. rewrite length_map in Hx.
  change (Z.of_nat (length (IdentSpec.DEC (d3_ma g i) 1))) with (d3_d1 g i) in Hx.
  apply (d3_fkeep_run _ _ W9 mem11 (ms_mem ms6) F (shadow_addr F) mf (d3_d1 g i) (d3_n3 g i) HFr);
  [apply (HW _ _ HE5); vm_compute; reflexivity | d3L F HBND Hx | d3L F HBND Hx]. }
assert (GD2e : garr8 SEGS (rd W9 (ms_mem ms6)) (F + 288 + d3_d1 g i + 1)
  (map (fun b : byte => bv_unsigned b) (IdentSpec.DEC (d3_mi g i) 1))).
{ apply (d3_garr8_mv W9 W9 mem11 (ms_mem ms6) _ _ GD2d). intros x Hx. rewrite length_map in Hx.
  change (Z.of_nat (length (IdentSpec.DEC (d3_mi g i) 1))) with (put_dec_c.dec_len (d3_mi g i) 1) in Hx.
  apply (d3_fkeep_run _ _ W9 mem11 (ms_mem ms6) F (shadow_addr F) mf (d3_d1 g i) (d3_n3 g i) HFr);
  [apply (HW _ _ HE5); vm_compute; reflexivity | d3L F HBND Hx | d3L F HBND Hx]. }
assert (GD3c : garr8 SEGS (rd W9 (ms_mem ms6)) (F + 288 + d3_n2 g i)
  (map (fun b : byte => bv_unsigned b) (IdentSpec.DEC (d3_pa g i) 2))).
{ apply (d3_garr8_mv W9 W9 mem11 (ms_mem ms6) _ _ GD3b). intros x Hx. rewrite length_map in Hx.
  change (Z.of_nat (length (IdentSpec.DEC (d3_pa g i) 2))) with (put_dec_c.dec_len (d3_pa g i) 2) in Hx.
  apply (d3_fkeep_run _ _ W9 mem11 (ms_mem ms6) F (shadow_addr F) mf (d3_d1 g i) (d3_n3 g i) HFr);
  [apply (HW _ _ HE5); vm_compute; reflexivity | d3L F HBND Hx | d3L F HBND Hx]. }
assert (GVa : garr8 SEGS (rd W9 (ms_mem ms6)) (F + 224)
  (reac_identity_reac_ver_str.rvs_bytes (d3_ma g i) (d3_mi g i) (d3_pa g i))).
{ apply (d3_garr8_mv W9 W9 mem11 (ms_mem ms6) _ _ GV). intros x Hx.
  assert (HLb : Z.of_nat (length (reac_identity_reac_ver_str.rvs_bytes (d3_ma g i) (d3_mi g i) (d3_pa g i))) = d3_n3 g i + 1).
  { rewrite <- HLV. unfold reac_identity_reac_ver_str.rvs_bytes, reac_identity_reac_ver_str.rvs_LV,
      reac_identity_reac_ver_str_c.reac_ver_str_LV. rewrite length_app, length_map. cbn [length]. lia. }
  rewrite HLb in Hx.
  apply (d3_fkeep_run _ _ W9 mem11 (ms_mem ms6) F (shadow_addr F) mf (d3_d1 g i) (d3_n3 g i) HFr);
  [apply (HW _ _ HE5); vm_compute; reflexivity | d3L F HBND Hx | d3L F HBND Hx]. }
clear HF HFr HG GD1f GD2d GD3b GV.
prreg HS11 (10%bv : bv 5) Wa0. prreg HS11 (11%bv : bv 5) Wa1. prreg HS11 (12%bv : bv 5) Wa2.
prreg HS11 (1%bv : bv 5) Wra. prreg HS11 (2%bv : bv 5) Wsp. prreg HS11 (3%bv : bv 5) Wgp. prreg HS11 (4%bv : bv 5) Wtp.
pmkst HS11.
(* the second bcmp (0x81208): v against ev, n3 + 1 bytes; they are equal (d3_ev) *)
assert (VDOT : val_mem SEGS (rd W9 (ms_mem ms6)) (F + 288 + d3_d1 g i) 1 46).
{ pose proof (d3_reg_vm _ _ _ 9 54 0 1 0 1 _ 0 1 (SLit 46) (F + 288 + d3_d1 g i) 46 HS11 eq_refl
    ltac:(left; reflexivity) ltac:(rewrite HE5 by lia; exact U54) eq_refl ltac:(lia) ltac:(lia)) as V.
  rewrite Z.add_0_r in V. exact V. }
assert (VNUL : val_mem SEGS (rd W9 (ms_mem ms6)) (F + 288 + d3_n3 g i) 1 0).
{ pose proof (d3_reg_vm _ _ _ 10 55 0 1 0 1 _ 0 1 (SLit 0) (F + 288 + d3_n3 g i) 0 HS11 eq_refl
    ltac:(left; reflexivity) ltac:(rewrite HE5 by lia; exact U55) eq_refl ltac:(lia) ltac:(lia)) as V.
  rewrite Z.add_0_r in V. exact V. }
assert (VSV2 : forall o z, (o = 28 /\ z = 0 \/ o = 29 /\ z = 0 \/ o = 30 /\ z = 4)%nat ->
  aview SEGS (w_H W9) (ms_mem ms6) (shadow_addr F + Z.of_nat o) = Some (Z.of_nat z)).
{ intros o z Ho. apply (aview_of_val_mem1 SEGS); [|lia].
  destruct Ho as [[-> ->] | [[-> ->] | [-> ->]]];
  [ exact (d3_reg_vm _ _ _ 5 38 28 31 28 31 _ 28 1 (SLit 0) (shadow_addr F) 0 HS11 eq_refl
      ltac:(cbn [In]; auto) ltac:(rewrite HE5 by lia; exact U38) eq_refl ltac:(lia) ltac:(lia))
  | exact (d3_reg_vm _ _ _ 5 38 28 31 28 31 _ 29 1 (SLit 0) (shadow_addr F) 0 HS11 eq_refl
      ltac:(cbn [In]; auto) ltac:(rewrite HE5 by lia; exact U38) eq_refl ltac:(lia) ltac:(lia))
  | exact (d3_reg_vm _ _ _ 5 38 28 31 28 31 _ 30 1 (SLit 4) (shadow_addr F) 4 HS11 eq_refl
      ltac:(cbn [In]; auto) ltac:(rewrite HE5 by lia; exact U38) eq_refl ltac:(lia) ltac:(lia)) ]. }
assert (VS4 : forall o, (o = 36 \/ o = 37 \/ o = 38)%nat ->
  aview SEGS (w_H W9) (ms_mem ms6) (shadow_addr F + Z.of_nat o) = Some 0).
{ intros o Ho. apply (aview_of_val_mem1 SEGS); [|lia].
  destruct Ho as [-> | [-> | ->]];
  [ exact (d3_reg_vm _ _ _ 6 38 36 39 36 39 _ 36 1 (SLit 0) (shadow_addr F) 0 HS11 eq_refl
      ltac:(cbn [In]; auto) ltac:(rewrite HE5 by lia; exact U38) eq_refl ltac:(lia) ltac:(lia))
  | exact (d3_reg_vm _ _ _ 6 38 36 39 36 39 _ 37 1 (SLit 0) (shadow_addr F) 0 HS11 eq_refl
      ltac:(cbn [In]; auto) ltac:(rewrite HE5 by lia; exact U38) eq_refl ltac:(lia) ltac:(lia))
  | exact (d3_reg_vm _ _ _ 6 38 36 39 36 39 _ 38 1 (SLit 0) (shadow_addr F) 0 HS11 eq_refl
      ltac:(cbn [In]; auto) ltac:(rewrite HE5 by lia; exact U38) eq_refl ltac:(lia) ltac:(lia)) ]. }
assert (RAV2 : range_addressable (aview SEGS (w_H W9) (ms_mem ms6)) SHADOW_OFF (F + 224) (d3_n3 g i + 1)).
{ intros x Hx. apply (d3_ra_v (aview SEGS (w_H W9) (ms_mem ms6)) F); [clear - Hf32; Z.div_mod_to_equations; lia
  | exact (VSV2 28%nat 0%nat ltac:(lia)) | exact (VSV2 29%nat 0%nat ltac:(lia)) | exact (VSV2 30%nat 4%nat ltac:(lia))
  | clear - Hx HN3; lia]. }
assert (RAE4 : range_addressable (aview SEGS (w_H W9) (ms_mem ms6)) SHADOW_OFF (F + 288) (d3_n3 g i + 1)).
{ intros x Hx. apply (d3_ra_ev (aview SEGS (w_H W9) (ms_mem ms6)) F); [clear - Hf32; Z.div_mod_to_equations; lia
  | exact (VS4 36%nat ltac:(lia)) | exact (VS4 37%nat ltac:(lia)) | exact (VS4 38%nat ltac:(lia))
  | clear - Hx HN3; lia]. }
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?R (Z_to_bv 64 ?X) ?M _) ?MD) ?Q =>
  change (SRr SEGS W9 (cfg_at SEGS X R M MD) Q) end.
eapply SRr_bind.
{ apply (D3BC LAWS ABCMP HSTK g pos mf W9 (ms_regs ms6) (ms_mem ms6) _ ly11 S11 (4 * Z.of_nat i + 3)
    (F + 224) (F + 288) (d3_n3 g i + 1) 2712 HJ12 Hfr11 Hmfb Hmf32 Wra ltac:(lia) eq_refl).
  - rewrite Wsp, (ER 2%nat 2%bv eq_refl). exact R2.
  - rewrite Wgp, (ER 3%nat 3%bv eq_refl). exact R3.
  - rewrite Wtp, (ER 4%nat 4%bv eq_refl). exact R4.
  - rewrite Wa0. exact (EX 2%nat ltac:(lia)).
  - rewrite Wa1. exact (EX 4%nat ltac:(lia)).
  - rewrite Wa2, U53. reflexivity.
  - clear - HN3; lia.
  - unfold d3_inobj. left. fold F. clear - HN3; lia.
  - unfold d3_inobj. left. fold F. clear - HN3; lia.
  - exact RAV2.
  - exact RAE4. }
intros W13 c13 _ (-> & regs13 & mem13 & md13 & v13 & -> & HJ13 & HP13 & Hv13 & Hcmp13 & Hfr13 & Hgr13).
assert (Hv13' : v13 = w64 0).
{ apply Hcmp13. intros j Hj.
  pose proof (proj1 (d3_ev _ _ _ Ma Mi Mp)) as EVER.
  apply (d3_evv (w_H W9) (ms_mem ms6) (F + 224) (F + 288) (IdentSpec.DEC (d3_ma g i) 1) (IdentSpec.DEC (d3_mi g i) 1)
    (IdentSpec.DEC (d3_pa g i) 2));
  change (Z.of_nat (length (IdentSpec.DEC (d3_ma g i) 1))) with (d3_d1 g i);
  change (Z.of_nat (length (IdentSpec.DEC (d3_mi g i) 1))) with (put_dec_c.dec_len (d3_mi g i) 1);
  change (Z.of_nat (length (IdentSpec.DEC (d3_pa g i) 2))) with (put_dec_c.dec_len (d3_pa g i) 2).
  - exact GD1g.
  - exact GD2e.
  - replace (F + 288 + d3_d1 g i + 1 + put_dec_c.dec_len (d3_mi g i) 1) with (F + 288 + d3_n2 g i)
      by (rewrite Hn2def; lia). exact GD3c.
  - exact VDOT.
  - replace (F + 288 + d3_d1 g i + 1 + put_dec_c.dec_len (d3_mi g i) 1 + put_dec_c.dec_len (d3_pa g i) 2)
      with (F + 288 + d3_n3 g i) by (rewrite Hn3def, Hn2def; lia). exact VNUL.
  - rewrite EVER. exact GVa.
  - rewrite Hn3def, Hn2def in Hj. clear - Hj. lia. }
clear Hcmp13.
pose proof HJ13 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres13 & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 4 pos (proj1 HJ13) HIN11) as (_ & _ & Hfb13 & Hfs13).
rewrite HFA11 in Hfb13, Hfs13. change (fs_frame_bytes 4) with 1024 in Hfb13. change (fs_frame_bytes 4 / 8) with 128 in Hfs13.
assert (K12 : d3_keep g pos mf i pl W2 mem2 W9 mem13).
{ intros a Hz Hnw. rewrite <- (K11 a Hz Hnw). apply Hfr13; [exact (HZ a Hz) | unfold ESTACK; pose proof (HZW a Hz); lia]. }
lazymatch goal with HS : st_ok _ _ ?ssx _ |- _ =>
  let Kk := eval vm_compute in (run_K A_LIM (SLit 0) [] ssx) in
  jafter_call_keep_hi HS Kk regs13 (mrestrict (w_H W9) mem13) HP13 [0;1;2;3;4;5;6;7;8;9;10]%nat HS12 end.
match type of HS12 with ?Q -> _ => assert (HQ : Q); [ | specialize (HS12 HQ); clear HQ ] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil;
  (eapply d3_rk2; [ rewrite HE5 by lia; eassumption
    | intros a Ha'; cbn [YP09.r_lo YP09.r_hi] in Ha'; apply Hfr13; unfold ESTACK; d3L F HBND Ha'
    | intros a Ha'; cbn [YP09.r_wlo YP09.r_whi] in Ha'; d3_pres Hpres13 Hfb13 Hfs13 F Hmf1 Hmf2 HD1 HN3 ]). }
rewrite <- restrict_mkst_fx in HS12.
clear HS11.
d3_env E HS12 HE5 HEI5 HE6 HEI6.
pose proof (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) 0 HS12
  ltac:(cbn [ms_regs restrict mkst]; rewrite Hv13, Hv13'; reflexivity) eq_refl) as HS13.
clear HS12.
lazymatch type of HS13 with st_ok_pi _ _ _ ?ss _ =>
  let v := eval vm_compute in ss in change ss with v in HS13 end.
(* run 7, to 0xe24: copy the payload's 8 bytes into hw, poison v and ev again, hw.have := 1 *)
unfold cfg_at. change (w64 (BASE + 2712)) with (Z_to_bv 64 (BASE + 2712)).
change mem13 with (ms_mem (mkst regs13 (Z_to_bv 64 (BASE + 2712)) mem13 (seg_rom SEGS))) in HJ13.
paj_run_to_shc RUNT HS13 HJ13 3620.
{ eapply (d3_awr _ _ _ _ _ _ _ _ F (shadow_addr F) mf (d3_d1 g i) (d3_n3 g i));
  [apply (HW _ _ HE6); vm_compute; reflexivity | exact HFA11 | reflexivity | lia | lia | lia | lia]. }
rename ms into ms7. rename HJ13 into HJ14.
assert (K13 : d3_keep g pos mf i pl W2 mem2 W9 (ms_mem ms7)).
{ apply (d3_keep_run g pos mf i pl W2 mem2 W9 mem13 (ms_mem ms7) _ _ (d3_d1 g i) (d3_n3 g i) HFr);
  [apply (HW _ _ HE6); vm_compute; reflexivity | lia | lia | exact HZ | exact K12]. }
clear HF HFr HG.
(* the end: inv_tail, through d3tl_core *)
assert (PB : forall j, (j < 8)%nat -> 0 <= d3_pb g i j < 256).
{ intros j Hj. exact (proj2 (d3_garr8_vm1 _ pl (SlotModel.rec_pl (e_pl g) i) j Hbpl ltac:(clear - Hj HL8; lia))). }
assert (UP : forall j, (j < 8)%nat -> bv_unsigned (ew E (42 + j)) = d3_pb g i j).
{ intros j Hj. replace (42 + j)%nat with (32 + (10 + j))%nat by lia. rewrite (EX (10 + j)%nat ltac:(lia)).
  replace (nth (10 + j) (d3_vals g pos i pl) 0) with (d3_pb g i j)
    by (do 8 (destruct j as [|j]; [reflexivity|]); lia).
  apply unsigned_lit_small. pose proof (PB j Hj). lia. }
prreg HS13 (2%bv : bv 5) Z2. prreg HS13 (3%bv : bv 5) Z3. prreg HS13 (4%bv : bv 5) Z4. prreg HS13 (8%bv : bv 5) Z8.
prreg HS13 (9%bv : bv 5) Z9. prreg HS13 (22%bv : bv 5) Z22. prreg HS13 (27%bv : bv 5) Z27.
assert (VHAVE : val_mem SEGS (rd W9 (ms_mem ms7)) (mf + 24) 8 1).
{ exact (d3_reg_vm _ _ _ 1 9 24 32 24 32 _ 24 8 (SLit 1) mf 1 HS13 eq_refl ltac:(left; reflexivity)
    ltac:(rewrite HE6 by lia; exact U9) eq_refl ltac:(lia) ltac:(lia)). }
assert (VH1 : val_mem SEGS (rd W9 (ms_mem ms7)) (F + 432 + 4) 4
  (d3_pb g i 0 + 256 * d3_pb g i 1 + 65536 * d3_pb g i 2 + 16777216 * d3_pb g i 3)).
{ pose proof (PB 0%nat ltac:(lia)). pose proof (PB 1%nat ltac:(lia)).
  pose proof (PB 2%nat ltac:(lia)). pose proof (PB 3%nat ltac:(lia)).
  eapply (d3_reg_vm _ _ _ 3 33 4 12 4 12 _ 4 4 _ (F + 432) _ HS13 eq_refl).
  - cbn [In]. right. left. reflexivity.
  - rewrite HE6 by lia. exact U33.
  - apply d3_den4; try (rewrite HE6 by lia); try assumption.
    + exact (UP 0%nat ltac:(lia)).
    + exact (UP 1%nat ltac:(lia)).
    + exact (UP 2%nat ltac:(lia)).
    + exact (UP 3%nat ltac:(lia)).
  - cbn [Z.of_N]. lia.
  - lia. }
assert (VH2 : val_mem SEGS (rd W9 (ms_mem ms7)) (F + 432 + 8) 4
  (d3_pb g i 4 + 256 * d3_pb g i 5 + 65536 * d3_pb g i 6 + 16777216 * d3_pb g i 7)).
{ pose proof (PB 4%nat ltac:(lia)). pose proof (PB 5%nat ltac:(lia)).
  pose proof (PB 6%nat ltac:(lia)). pose proof (PB 7%nat ltac:(lia)).
  eapply (d3_reg_vm _ _ _ 3 33 4 12 4 12 _ 8 4 _ (F + 432) _ HS13 eq_refl).
  - cbn [In]. left. reflexivity.
  - rewrite HE6 by lia. exact U33.
  - apply d3_den4; try (rewrite HE6 by lia); try assumption.
    + exact (UP 4%nat ltac:(lia)).
    + exact (UP 5%nat ltac:(lia)).
    + exact (UP 6%nat ltac:(lia)).
    + exact (UP 7%nat ltac:(lia)).
  - cbn [Z.of_N]. lia.
  - lia. }
assert (HWB : bytes_at8 W9 (ms_mem ms7) (SFa g pos + V_hw + 4) (firstn 8 (SlotModel.rec_pl (e_pl g) i))).
{ unfold bytes_at8. rewrite (d3_first8 _ HL8).
  change (garr8 SEGS (rd W9 (ms_mem ms7)) (SFa g pos + V_hw + 4)
    ([d3_pb g i 0; d3_pb g i 1; d3_pb g i 2; d3_pb g i 3] ++ [d3_pb g i 4; d3_pb g i 5; d3_pb g i 6; d3_pb g i 7])).
  apply garr8_app. split.
  - apply d3_vm4; [exact VH1 | exact (PB 0%nat ltac:(lia)) | exact (PB 1%nat ltac:(lia))
    | exact (PB 2%nat ltac:(lia)) | exact (PB 3%nat ltac:(lia))].
  - replace (SFa g pos + V_hw + 4 + Z.of_nat (length [d3_pb g i 0; d3_pb g i 1; d3_pb g i 2; d3_pb g i 3]))
      with (F + 432 + 8) by (cbn [length]; unfold V_hw; fold F; lia).
    apply d3_vm4; [exact VH2 | exact (PB 4%nat ltac:(lia)) | exact (PB 5%nat ltac:(lia))
    | exact (PB 6%nat ltac:(lia)) | exact (PB 7%nat ltac:(lia))]. }
pmkst HS13.
apply SRr_ret.
lazymatch goal with |- context [mkCfg (mkst ?R ?P ?M ?RO) ?MD] =>
  change (mkCfg (mkst R P M RO) MD) with (cfg_at SEGS (BASE + 0xe24) R M MD) end.
apply (D3TLc HSTK LAWS MTL HMT0 AJ_NIL_IO g pos mf i pl W2 regs2 mem2 md2 W9 (ms_regs ms7) (ms_mem ms7) _ ly11 S11
  HV0 HJ14 Hfr11).
- split; [| exact (proj2 Hhb)]. eapply Permutation_trans; [exact Hbl11 |]. rewrite Hbl9, Hbl7, Hbl5. exact (proj1 Hhb).
- intros r Hrr. cbn [In] in Hrr.
  destruct Hrr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]].
  + rewrite !(d3_reg5 _ (2%bv : bv 5) 2 eq_refl), Z2. exact (ER 2%nat 2%bv eq_refl).
  + rewrite !(d3_reg5 _ (3%bv : bv 5) 3 eq_refl), Z3. exact (ER 3%nat 3%bv eq_refl).
  + rewrite !(d3_reg5 _ (4%bv : bv 5) 4 eq_refl), Z4. exact (ER 4%nat 4%bv eq_refl).
  + rewrite !(d3_reg5 _ (8%bv : bv 5) 8 eq_refl), Z8. exact (ER 8%nat 8%bv eq_refl).
  + rewrite !(d3_reg5 _ (9%bv : bv 5) 9 eq_refl), Z9. exact (ER 9%nat 9%bv eq_refl).
  + rewrite !(d3_reg5 _ (22%bv : bv 5) 22 eq_refl), Z22. exact (ER 22%nat 22%bv eq_refl).
  + rewrite !(d3_reg5 _ (27%bv : bv 5) 27 eq_refl), Z27. exact (ER 27%nat 27%bv eq_refl).
- exact K13.
- exact VHAVE.
- exact HWB.
Qed.

Lemma seg_D3 : seg_D3_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS.
Proof. exact d3_walk. Qed.
Check (seg_D3 : seg_D3_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS).

End c.
End b.
End a.
