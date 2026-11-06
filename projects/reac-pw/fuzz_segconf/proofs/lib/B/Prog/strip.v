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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/rec_calls_equal.v, with its module paths, module names and numbers changed; 1300 of its 1467 lines of code are new or changed and 1425 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the walk of strip on fuzz_segconf.asan-ubsan (image B, pin sha256 c3796c0b38f3,
   unstripped twin 80e82127e8ca; entry 0x879cc, 420 bytes, 105 instructions, a 16-byte frame, no side-stack frame):
   strip_contract of lib/B/Prog/strip_c.v at image B's numbers, in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre
   at the entry, SRr of apost_base at the return, over `Context {PI : PAImg seg_listing}` of image B's listing
   lib/B/Prog/SegPa.v). Written new: image A inlines strip into m_file, so no walk of it exists in any image; the loop
   logic follows the segconf porter's UBSan walk lib/U/Prog/strip.v (another framework: its lead_exit / lead_all / trail_exit
   and the blank-bit table are restated below), the form follows the image-B m_file-family owner's image-B walk lib/B/Prog/ieq.v.

   The code (the neutral listing of strip in image B):
     0x879cc-0x879d0  frame of 16: ra at sp+8
     0x879d4-0x879dc  a2 := (sc | ec) & 7; bnez a2 -> the trap 0x87b3c (UBSan alignment check of the two cells)
     0x879e0-0x879e8  a3 := the shadow base (the GOT word as_got_shadow B, image B 0xa3210 = listing A_OBJ 0, holds the
                      cell A_OBJ 12 that holds it); a4 := (sc >> 3) + a3, a5 := (ec >> 3) + a3, kept for the whole call
     0x879f4-0x87a08  the instrumented checks of the cells sc and ec (a load of the shadow byte and a compare; the
                      error paths, calls of errpath_load8 at 0x87b58 / 0x87b5c, are not reached)
     0x87a0c-0x87a14  a6 := *sc = s0, a2 := *ec = e0; bgeu a6,a2 -> BK 0x87a94
     0x87a18-0x87a2c  a7 := 32, t0 := 0x100002200 (bits 9, 13, 32), t1 := 1, a2 := a6
     FW 0x87a30       beqz a6 -> trap; the instrumented check of the byte at s (slow block 0x87a84, error path
                      0x87a90 not reached); lbu t2 := *s; bltu 32,t2 -> BK; (t0 >> t2) & 1 = 0 -> BK; a2 += 1;
                      bgeu t1,a2 -> trap; the check of sc (store8), a6 += 1, sd a6 -> *sc; the check of ec, t2 := *ec;
                      bltu a6,t2 -> FW; j BK
     BK 0x87a94       the checks of ec and sc; a6 := *ec, a2 := *sc; bgeu a2,a6 -> EPI; a2 := a6 - 1, a7 := 1,
                      t0 := 32, t1 := 0x100002200, t2 := 2
     BL 0x87acc       beq a6,a7 -> trap; the check of the byte at e - 1 (slow block 0x87b20, error path 0x87b2c not
                      reached); lbu t3 := e[-1]; bltu 32,t3 -> EPI; (t1 >> t3) & 1 = 0 -> EPI; bltu a6,t2 -> trap;
                      the check of ec (store8), a6 -= 1, sd a6 -> *ec; the check of sc, t3 := *sc; a2 -= 1;
                      bltu t3,a6 -> BL; j EPI
     EPI 0x87b30      ra restored, sp += 16, ret
   The five UBSan trap branches (each to the `unimp` at 0x87b3c), each shown not taken, so the trap instruction is
   never executed:
     0x879dc bnez a2      a2 = (sc | ec) & 7: the walk splits the branch and refutes the taken side from the
                          contract's sc mod 8 = 0 and ec mod 8 = 0 (st_align_U below)
     0x87a30 beqz a6      a6 = s: decided by the symbolic executor from the loop head's fact s in [4096, 2^47 - 64]
                          (st_PTRF on atom 35; 4096 <= s0 <= s from the contract's sa_loc, st_bytes)
     0x87a5c bgeu t1,a2   t1 = 1, a2 = s + 1: decided from the same fact (s + 1 >= 4097)
     0x87acc beq a6,a7    a6 = e, a7 = 1: decided from the fact e in [4096, 2^47 - 64] (st_PTRF on atom 36;
                          e > s >= s0 >= 4096)
     0x87af4 bltu a6,t2   a6 = e, t2 = 2: decided from the same fact
   The ten instrumented checks: the eight checks of the two cells are decided by the shadow tokens (PaShadow.v)
   from 8-byte shadow entries of sc and ec (sc, ec 8-aligned, their shadow addressable: the contract's sa_addr), the
   two byte checks from 1-byte entries of s and e - 1 (the contract's sa_addr of [s0, e0)).
   Cut points (listing offsets from BASE = 0x84dc0): the entry AF_strip 0x2c0c; ST_FW 0x2c70 (0x87a30) at byte i,
   induction on the bytes left; ST_BK 0x2cd4 (0x87a94) with *sc = s0 + strip_lead; ST_BL 0x2d0c (0x87acc) with j
   trailing blanks dropped, induction on the bytes left; ST_EPI 0x2d70 (0x87b30). Each is re-seeded from the
   concrete state.
   Memory: the code writes its frame (ra at sp - 8) and the two cells, and nothing else (st_cut's st_kz below); the
   stores to the cells are allowed by awr_byte's caller-stack arm (inFP and sp <= a < ly_top, the contract's
   strip_slot).
   Image numbers: the entry BASE + AF_strip (listing term of lib/B/Prog/SegList.v) and STK_strip from
   lib/B/Prog/SegInstB.v (= 16, the frame; the error path is dead). The record hypothesis TL : PALib B (the shadow
   GOT word and cell by role) is the one Section hypothesis, as in ieq.v. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0p YC5d YG0q YG0d_tail.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaDenot PaSB PaLibG PaLibH PaLibF PaCallRun PaCall.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import strip_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Module SM := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec.SegModel.

(* image B: STK_strip (SegInstB.v: the frame of 16) *)
#[local] Notation ST_STK := SegInstB.STK_strip.

(* ---------- the model (the segconf porter's lib/U/Prog/strip.v lemmas, restated over SegModel's names) ---------- *)
Lemma st_zs_length : forall bs, length (seg_spec.zs bs) = length bs.
Proof. intros bs. unfold seg_spec.zs. apply length_map. Qed.
Lemma st_zs_nth : forall (l : list byte) i, (i < length l)%nat -> nth i (seg_spec.zs l) 0 = bv_unsigned (nth i l ZB0).
Proof.
intros l i Hi. unfold seg_spec.zs. rewrite (nth_indep _ 0 (bv_unsigned ZB0)) by (rewrite length_map; exact Hi).
apply map_nth.
Qed.
Lemma st_nth_skipn : forall k (d : list Z) i, nth i (skipn k d) 0 = nth (k + i) d 0.
Proof.
induction k as [|k IH]; intros d i; [reflexivity|].
destruct d as [|c r]; cbn [skipn Nat.add].
- destruct i; reflexivity.
- cbn [nth]. apply IH.
Qed.
Lemma st_blank_gt : forall x, 32 < x -> SM.blank x = false.
Proof.
intros x Hx. unfold SM.blank.
destruct (Z.eqb_spec x 32), (Z.eqb_spec x 9), (Z.eqb_spec x 13); try lia; reflexivity.
Qed.
(* k leading blanks, then a byte that is not blank *)
Lemma st_lead_exit : forall (d : list Z) k, (k < length d)%nat ->
  (forall i, (i < k)%nat -> SM.blank (nth i d 0) = true) -> SM.blank (nth k d 0) = false ->
  length (SM.takewhile SM.blank d) = k.
Proof.
induction d as [|c r IH]; intros k Hk HB HN; cbn [length] in Hk; [lia|].
destruct k as [|k].
- cbn [nth] in HN. cbn [SM.takewhile]. rewrite HN. reflexivity.
- assert (Hc : SM.blank c = true) by exact (HB 0%nat ltac:(lia)).
  cbn [SM.takewhile]. rewrite Hc. cbn [length].
  rewrite (IH k ltac:(lia) (fun i Hi => HB (S i) ltac:(lia)) HN). reflexivity.
Qed.
(* every byte blank *)
Lemma st_lead_all : forall (d : list Z),
  (forall i, (i < length d)%nat -> SM.blank (nth i d 0) = true) -> length (SM.takewhile SM.blank d) = length d.
Proof.
induction d as [|c r IH]; intros HB; [reflexivity|].
assert (Hc : SM.blank c = true) by exact (HB 0%nat ltac:(cbn [length]; lia)).
cbn [SM.takewhile]. rewrite Hc. cbn [length].
rewrite (IH (fun i Hi => HB (S i) ltac:(cbn [length]; lia))). reflexivity.
Qed.
(* j trailing blanks, before them a byte that is not blank *)
Lemma st_trail_exit : forall (r : list Z) j, (j < length r)%nat ->
  (forall i, (length r - j <= i < length r)%nat -> SM.blank (nth i r 0) = true) ->
  SM.blank (nth (length r - S j) r 0) = false ->
  length (SM.takewhile SM.blank (rev r)) = j.
Proof.
intros r j Hj HB HN. apply st_lead_exit.
- rewrite length_rev. exact Hj.
- intros i Hi. rewrite rev_nth by lia. apply HB. lia.
- rewrite rev_nth by lia. exact HN.
Qed.
(* every byte blank, from the back *)
Lemma st_trail_all : forall (r : list Z), (forall i, (i < length r)%nat -> SM.blank (nth i r 0) = true) ->
  length (SM.takewhile SM.blank (rev r)) = length r.
Proof.
intros r HB. rewrite <- (length_rev r). apply st_lead_all.
intros i Hi. rewrite length_rev in Hi. rewrite rev_nth by lia. apply HB. lia.
Qed.

(* ---------- the two compiled tests ---------- *)
Definition ST_MASK : Z := 0x100002200.
(* (0x100002200 >> b) & 1 for a byte b <= 32 is SegModel.blank b (bits 9, 13, 32: tab, CR, space) *)
Lemma st_bit_U : forall E k c, ew E k = Z_to_bv 64 c -> 0 <= c <= 32 ->
  U E (SAlu ALU_AND (SAlu ALU_SRL (SLit ST_MASK) (SOff k 0)) (SLit 1)) = if SM.blank c then 1 else 0.
Proof.
intros E k c Hk Hc.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SLit. rewrite (U_atom E k c Hk) by lia.
assert (Hn : exists n, (n <= 32)%nat /\ c = Z.of_nat n) by (exists (Z.to_nat c); split; lia).
destruct Hn as (n & Hn & ->). clear Hk Hc.
do 33 (destruct n as [|n]; [vm_compute; reflexivity|]). lia.
Qed.
(* (sc | ec) & 7 = 0 for two 8-aligned words: the UBSan alignment check 0x879dc *)
Lemma st_align_U : forall E a b, ew E 10 = Z_to_bv 64 a -> ew E 11 = Z_to_bv 64 b -> 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  a mod 8 = 0 -> b mod 8 = 0 -> U E (SAlu ALU_AND (SAlu ALU_OR (SOff 10 0) (SOff 11 0)) (SLit 7)) = 0.
Proof.
intros E a b Ha Hb Ra Rb Ma Mb.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite U_SLit, (U_atom E 10 a Ha Ra), (U_atom E 11 b Hb Rb).
change (zcanon 7) with 7.
assert (L : Z.land (zcanon (Z.lor a b)) 7 = 0).
{ unfold zcanon, M64. apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, Z.bits_0.
  destruct (Z_lt_le_dec k 3) as [Hk3|Hk3].
  - rewrite Z.mod_pow2_bits_low by lia. rewrite Z.lor_spec.
    assert (A : Z.testbit a k = false).
    { rewrite <- (Z.mod_pow2_bits_low a 3 k) by lia. change (2 ^ 3) with 8. rewrite Ma. apply Z.bits_0. }
    assert (Bb : Z.testbit b k = false).
    { rewrite <- (Z.mod_pow2_bits_low b 3 k) by lia. change (2 ^ 3) with 8. rewrite Mb. apply Z.bits_0. }
    rewrite A, Bb. reflexivity.
  - change 7 with (Z.ones 3). rewrite Z.ones_spec_high by lia. apply andb_false_r. }
rewrite L. reflexivity.
Qed.

(* ---------- bytes through a reader ---------- *)
Lemma st_val1 : forall (rd : reader) a v, rd a = Some v -> 0 <= v < 256 -> sa_val rd a 1 v.
Proof.
intros rd a v H Hv k Hk. assert (k = 0%nat) by lia. subst k. change (Z.of_nat 0) with 0. rewrite Z.add_0_r, H. f_equal.
unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256. rewrite !Z.mod_small by lia. reflexivity.
Qed.
Definition st_kz (Z0 : Z -> Prop) (rd rd' : reader) : Prop :=
forall x, 0 <= x < 2 ^ 64 -> ~ Z0 x -> rd' x = rd x.
Lemma st_kz_refl : forall Z0 rd, st_kz Z0 rd rd.
Proof. intros Z0 rd x _ _. reflexivity. Qed.
Lemma st_kz_trans : forall Z0 rd1 rd2 rd3, st_kz Z0 rd1 rd2 -> st_kz Z0 rd2 rd3 -> st_kz Z0 rd1 rd3.
Proof. intros Z0 rd1 rd2 rd3 H1 H2 x Hx Hn. rewrite (H2 x Hx Hn). exact (H1 x Hx Hn). Qed.
Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma st_val_mem_of_sa_val : forall segs H mem a n v,
  sa_val (aview segs H mem) a n v -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem a n v Hr k Hk. pose proof (Hr k Hk) as Hb.
destruct (aview_byte segs H mem _ _ Hb) as (b & Hm & Hbv & Hrange). rewrite Hm. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Hbv. rewrite Z.mod_small; [reflexivity|].
change (bv_modulus 8) with 256. exact Hrange.
Qed.
End r.

(* ---------- the symbolic states of the cut points ---------- *)
Definition ST_FW : Z := 0x2c70.   (* 0x87a30, the forward loop head (beqz a6) *)
Definition ST_BK : Z := 0x2cd4.   (* 0x87a94, the back part *)
Definition ST_BL : Z := 0x2d0c.   (* 0x87acc, the back loop head (beq a6,a7) *)
Definition ST_EPI : Z := 0x2d70.  (* 0x87b30, the epilogue *)
Definition st_spF : afact := mkAF (2 ^ 46) (2 ^ 47) 4.
Definition st_SBF : afact := mkAF SB SB 0.
Definition st_CELLF : afact := mkAF (2 ^ 46) (2 ^ 47 - 8) 3.
Definition st_PTRF : afact := mkAF 4096 (2 ^ 47 - 64) 0.
Definition st_BYTEF : afact := mkAF 0 255 0.
Definition st_Bx : sv := SOff 32 0.
(* the shadow address (x >> 3) + the shadow base of a cell, as the code keeps it in a4 / a5 *)
Definition st_shx (k : nat) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff k 0) (SLit 3)) (SOff 32 0).
(* a cell: 8 bytes at atom b holding atom v, writable when w = 8 *)
Definition st_cellR (b : nat) (w : Z) (v : nat) : YP09.region :=
  YP09.mkRegion (Some b) 0 8 0 w [YP09.mkChunk 0 (CVal 8 (SOff v 0))].
(* the entry: atoms 10 / 11 the cells, 32 the shadow base, 33 s0, 34 e0 *)
Definition st_ss_entry : sstate := mkSS AF_strip sr_atoms
  [stack_region 16; got_regionP; bcell_regionP 32; st_cellR 10 0 33; st_cellR 11 0 34] None
  (mkFacts [(2%nat, st_spF); (10%nat, st_CELLF); (11%nat, st_CELLF); (32%nat, st_SBF)] [] []).
Definition st_SH_entry : list shent := [mkSHE 10 0 8; mkSHE 11 0 8].
(* the forward loop head at byte i: atoms 32 the shadow base, 33 sc, 34 ec, 35 s = s0 + i, 36 the byte at s, 37 e0 *)
Definition st_fw_regs : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms
   5 (SLit ST_MASK)) 6 (SLit 1)) 10 (SOff 33 0)) 11 (SOff 34 0)) 12 (SOff 35 0)) 13 (SOff 32 0)) 14 (st_shx 33))
   15 (st_shx 34)) 16 (SOff 35 0)) 17 (SLit 32).
Definition st_ss_fw : sstate := mkSS ST_FW st_fw_regs
  [st_cellR 33 8 35; st_cellR 34 0 37; YP09.mkRegion (Some 35%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 36 0))]] None
  (mkFacts [(2%nat, st_spF); (32%nat, st_SBF); (33%nat, st_CELLF); (34%nat, st_CELLF); (35%nat, st_PTRF);
            (36%nat, st_BYTEF); (37%nat, st_PTRF)] [] []).
Definition st_SH_fw : list shent := [mkSHE 33 0 8; mkSHE 34 0 8; mkSHE 35 0 1].
(* the back part: atoms 32 the shadow base, 33 sc, 34 ec, 35 s, 36 e0 *)
Definition st_bk_regs : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 10 (SOff 33 0)) 11 (SOff 34 0)) 13 (SOff 32 0)) 14 (st_shx 33))
   15 (st_shx 34).
Definition st_ss_bk : sstate := mkSS ST_BK st_bk_regs [st_cellR 33 0 35; st_cellR 34 0 36] None
  (mkFacts [(2%nat, st_spF); (32%nat, st_SBF); (33%nat, st_CELLF); (34%nat, st_CELLF)] [] []).
Definition st_SH_bk : list shent := [mkSHE 33 0 8; mkSHE 34 0 8].
(* the back loop head with j trailing blanks dropped: atoms 32 the shadow base, 33 sc, 34 ec, 35 s, 36 e = e0 - j,
   37 the byte at e - 1 *)
Definition st_bl_regs : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms
   5 (SLit 32)) 6 (SLit ST_MASK)) 7 (SLit 2)) 10 (SOff 33 0)) 11 (SOff 34 0)) 12 (SOff 36 (-1))) 13 (SOff 32 0))
   14 (st_shx 33)) 15 (st_shx 34)) 16 (SOff 36 0)) 17 (SLit 1).
Definition st_ss_bl : sstate := mkSS ST_BL st_bl_regs
  [st_cellR 33 0 35; st_cellR 34 8 36; YP09.mkRegion (Some 36%nat) (-1) 0 0 0 [YP09.mkChunk (-1) (CVal 1 (SOff 37 0))]]
  None
  (mkFacts [(2%nat, st_spF); (32%nat, st_SBF); (33%nat, st_CELLF); (34%nat, st_CELLF); (35%nat, st_PTRF);
            (36%nat, st_PTRF); (37%nat, st_BYTEF)] [] []).
Definition st_SH_bl : list shent := [mkSHE 33 0 8; mkSHE 34 0 8; mkSHE 36 (-1) 0].
(* the epilogue: atom 32 the saved ra *)
Definition st_ss_epi : sstate := mkSS ST_EPI sr_atoms
  [YP09.mkRegion (Some 2%nat) 0 16 0 0 [YP09.mkChunk 8 (CVal 8 (SOff 32 0))]] None (mkFacts [(2%nat, st_spF)] [] []).

Ltac st_md :=
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?md2 _ |- _ =>
    lazymatch md2 with with_vm_backing _ _ _ => let m := fresh "mdv" in set (m := md2) in *; clearbody m | _ => idtac end end.
(* the registers of a seed: each entry atom, a shadow address (DSH), or a value whose U fact RWU gives *)
Ltac st_regs_ok EE RWU DSH :=
  apply regs_ok_by_cases; intros rr Hrr; cbv [all_regs In] in Hrr;
  repeat (destruct Hrr as [<- | Hrr];
    [ lazymatch goal with |- getr _ _ = sv_denot _ (sr_get ?a0 ?rr2) =>
        let v := eval vm_compute in (sr_get a0 rr2) in change (sr_get a0 rr2) with v end;
      first [ reflexivity
            | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; symmetry; apply EE; reflexivity
            | DSH; etransitivity; [eassumption | reflexivity]
            | cbn [sv_denot]; RWU; etransitivity; [eassumption | unfold w64; try unfold ST_MASK; f_equal; lia] ]
    | ]); try (destruct Hrr).

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* a register the symbolic state holds as its own entry atom *)
Lemma st_reg_atom : forall (H : word -> bool) Ex ss ms (r : bv 5) (k : nat) v,
  st_ok_pi SEGS VAL Ex ss (restrict H ms) -> Z.of_nat k = bv_unsigned r -> sr_get (ss_regs ss) r = SOff k 0 ->
  ew Ex k = v -> getr (ms_regs ms) r = v.
Proof.
intros H Ex ss ms r k v HS Hk Hr Hv. rewrite (st_ok_pi_restrict_reg H Ex ss ms r HS), Hr. cbn [sv_denot].
rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Hv.
Qed.
Ltac st_same0 HS tac :=
  lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
    let k := eval vm_compute in (Z.to_nat (bv_unsigned r)) in
    apply (st_reg_atom _ _ _ ms r k _ HS); [reflexivity | vm_compute; reflexivity | tac] end.
Ltac st_same HS EE := st_same0 HS ltac:(cbn [ew ewset Nat.eqb]; apply EE; reflexivity).
(* the value of a register at a state, from its symbolic value; RW rewrites the U facts of the seed's atoms *)
Ltac st_rv HS RW :=
  lazymatch goal with |- getr (ms_regs ?msx) ?r = w64 ?z =>
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ msx) =>
    rewrite (st_ok_pi_restrict_reg _ Ex ssx msx r HS);
    let e := eval vm_compute in (sr_get (ss_regs ssx) r) in change (sr_get (ss_regs ssx) r) with e;
    cbn [sv_denot ew ewset Nat.eqb]; RW; unfold w64; try unfold ST_MASK; f_equal; lia
  end end.
(* a shadow-address register (x >> 3) + the shadow base, Ek the atom fact of x and E32 the shadow base's *)
Ltac st_rvx HS Ek E32 v :=
  lazymatch goal with |- getr (ms_regs ?msx) ?r = w64 ?z =>
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ msx) =>
    rewrite (st_ok_pi_restrict_reg _ Ex ssx msx r HS);
    let e := eval vm_compute in (sr_get (ss_regs ssx) r) in change (sr_get (ss_regs ssx) r) with e;
    lazymatch goal with |- sv_denot _ (SAlu ALU_ADD (SAlu ALU_SRL (SOff ?n 0) (SLit 3)) (SOff ?m 0)) = _ =>
      rewrite (denot_shx Ex n m 0 v SB) by (first [ cbn [ew ewset Nat.eqb]; exact Ek | cbn [ew ewset Nat.eqb]; exact E32
                                                    | lia | unfold SB; lia ]) end;
    unfold w64; f_equal; lia
  end end.
(* a field of a region of a state, read through the world's view *)
Lemma st_field : forall E H mem' n b lo hi wlo whi cs off e v,
  region_ok SEGS E (mrestrict H mem') (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
  In (YP09.mkChunk off (CVal 8 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sa_val (aview SEGS H mem') (b + off) 8 v.
Proof.
intros E H mem' n b lo hi wlo whi cs off e v HR Hb Hin He Hv j Hj.
change 8%nat with (N.to_nat 8) in Hj |- *.
pose proof (field_of_region E _ n b cs lo hi wlo whi off 8%N e v HR Hb Hin He
  ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hv) ltac:(cbn; lia)) as HF.
unfold aview. rewrite (HF j Hj). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold YG0f.le_byte. apply Z.mod_mod. lia.
Qed.
Lemma st_reg_val2 : forall H E ss (ms : machine_state) i n lo hi wlo whi cs off e x v,
  st_ok_pi SEGS VAL E ss (restrict H ms) ->
  nth_error (ss_mem ss) i = Some (YP09.mkRegion (Some n) lo hi wlo whi cs) -> In (YP09.mkChunk off (CVal 8 e)) cs ->
  bv_unsigned (ew E n) = x -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sa_val (aview SEGS H (ms_mem ms)) (x + off) 8 v.
Proof.
intros H E ss ms i n lo hi wlo whi cs off e x v HS Hi Hin Hx He Hv.
pose proof (st_ok_pi_region_nth E ss _ i _ HS Hi) as HR. cbn [ms_mem restrict] in HR.
exact (st_field E H (ms_mem ms) n x lo hi wlo whi cs off e v HR Hx Hin He Hv).
Qed.
Lemma st_reg_val : forall H E ss (ms : machine_state) i n wlo whi e x v,
  st_ok_pi SEGS VAL E ss (restrict H ms) ->
  nth_error (ss_mem ss) i = Some (YP09.mkRegion (Some n) 0 8 wlo whi [YP09.mkChunk 0 (CVal 8 e)]) ->
  bv_unsigned (ew E n) = x -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sa_val (aview SEGS H (ms_mem ms)) x 8 v.
Proof.
intros H E ss ms i n wlo whi e x v HS Hi Hx He Hv.
pose proof (st_reg_val2 H E ss ms i n 0 8 wlo whi _ 0 e x v HS Hi ltac:(left; reflexivity) Hx He Hv) as R.
rewrite Z.add_0_r in R. exact R.
Qed.
(* the extra words of a seed *)
Lemma st_ex : forall regs1 (vals : list Z) j v, (32 + j < A_TEXT)%nat -> nth_error vals j = Some v ->
  ew (Eimg (Ereg regs1 (map w64 vals))) (32 + j) = Z_to_bv 64 v.
Proof.
intros regs1 vals j v H1 H2. rewrite Eimg_low by exact H1. rewrite ew_Ereg_extra.
assert (H3 : nth_error (map w64 vals) j = Some (w64 v)) by (rewrite nth_error_map, H2; reflexivity).
rewrite (nth_error_nth _ _ _ H3). reflexivity.
Qed.
Section e.
Variable B : asyms.
(* the record hypothesis: PALib (lib/B/Prog/SegPaLib.v: the shadow GOT word A_OBJ 0 and the shadow cell A_OBJ 12 are
   as_got_shadow B and as_shadow_cell B, by role; image B 0xa3210 and 0xac7b8) *)
Hypothesis TL : PALib B.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_seg) (PI := PI).

(* the shadow entry of a range the walk's checks read *)
Lemma st_shent_ok : forall E m n x lo hi, ew E 32 = w64 SB -> bv_unsigned (ew E n) = x -> 0 <= x + lo -> x + hi < 2 ^ 64 -> lo <= hi ->
  range_addressable (rd_of SEGS m) SHADOW_OFF (x + lo) (hi - lo) ->
  (forall y, x + lo <= y < x + hi -> ~ (SB <= y < SB + 2 ^ 44)) ->
  shent_ok SEGS st_Bx E m (mkSHE n lo hi).
Proof.
intros E m n x lo hi H32 Hn H0 H1 Hlh Hra Hband. unfold shent_ok, app_apart, st_Bx. cbn [she_m she_lo she_hi].
assert (U32 : U E (SOff 32 0) = SB).
{ rewrite U_SOff, H32, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). apply zcanon_small. unfold SB; lia. }
assert (Hxr : 0 <= x < 2 ^ 64) by (rewrite <- Hn; pose proof (bv_unsigned_in_range 64 (ew E n)) as HR; change (bv_modulus 64) with (2 ^ 64) in HR; exact HR).
assert (Un : U E (SOff n 0) = x) by (rewrite U_SOff, Hn, Z.add_0_r; apply zcanon_small; exact Hxr).
rewrite U32, Un. split; [exact Hra|].
intros y Hy. rewrite Z.min_l, Z.max_r in Hy by lia. apply Hband. lia.
Qed.
(* where an object of segconf's code lies: a live heap block, a live side-stack frame or the image, below
   alloc_ceiling and apart from the shadow band *)
Lemma st_loc : forall ly S W mem md q k, AR SEGS B ly S W mem md -> sa_loc SEGS B ly S q k -> 0 < k ->
  4096 <= q /\ q + k <= alloc_ceiling /\ (forall x, q <= x < q + k -> ~ (SB <= x < SB + 2 ^ 44)).
Proof.
intros ly S W mem md q k HAR HL Hk. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HL as [(b & m & Hin & Hb & Hbm) | [(cid & pos & Hin & Hc & Hf1 & Hf2) | Himg]].
- destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & Hb4 & Hbc & Hba & _ & _ & Hm).
  pose proof (req_size_pos m ltac:(lia)) as [_ Hr].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB in *.
  split; [lia|]. split; [lia|]. intros x Hx. lia.
- destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hin) as (Hf0 & Hfc & Hfa).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SB in *.
  split; [lia|]. split; [lia|]. intros x Hx. lia.
- destruct (Himg q ltac:(lia)) as (Hi0 & _). destruct (Himg (q + k - 1) ltac:(lia)) as (Hi1 & _).
  pose proof (pa_img_range _ Hi0) as R0. pose proof (pa_img_range _ Hi1) as R1. unfold kImgEnd in R0, R1.
  split; [lia|]. split; [lia|]. intros x Hx. unfold SB. lia.
Qed.

(* ---------- one call of strip ---------- *)
Section w.
Variables (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (ch : list (Z * Z * Z)) (sc ec s0 e0 : Z) (l : list byte).
Hypothesis HPRE : afn_pre SEGS B ST_STK ly S W regs mem md ch.
Hypothesis H10 : getr regs 10 = w64 sc.
Hypothesis Hsc64 : 0 <= sc < 2 ^ 64.
Hypothesis H11 : getr regs 11 = w64 ec.
Hypothesis Hec64 : 0 <= ec < 2 ^ 64.
(* strip_args *)
Hypothesis HSC8 : sc mod 8 = 0.
Hypothesis HEC8 : ec mod 8 = 0.
Hypothesis HDCE : sa_disj sc 8 ec 8.
Hypothesis HVS : sa_val (rdW W mem) sc 8 s0.
Hypothesis HAS : sa_addr (rdW W mem) sc 8.
Hypothesis HVE : sa_val (rdW W mem) ec 8 e0.
Hypothesis HAE : sa_addr (rdW W mem) ec 8.
Hypothesis HS0 : 0 < s0.
Hypothesis HSE : s0 <= e0.
Hypothesis HSB : sa_bytes (rdW W mem) s0 l.
Hypothesis HLN : Z.of_nat (length l) = e0 - s0.
Hypothesis HSA : sa_addr (rdW W mem) s0 (e0 - s0).
Hypothesis HDS : sa_disj s0 (e0 - s0) sc 8.
Hypothesis HDE : sa_disj s0 (e0 - s0) ec 8.
(* strip_slot of each cell, and sa_loc of the bytes *)
Hypothesis HSLS : strip_slot ly (w_H W) mem (spZ regs) sc.
Hypothesis HSLE : strip_slot ly (w_H W) mem (spZ regs) ec.
Hypothesis HSL : sa_loc SEGS B ly S s0 (e0 - s0).

Definition st_LEAD : nat := strip_lead (seg_spec.zs l).
Definition st_Q : world SEGS -> config -> Prop :=
apost_base SEGS B ST_STK [(sc, sc + 8); (ec, ec + 8)] regs ly S W mem md EV_strip
(fun ly' S' W' regs' mem' md' =>
 sa_val (aview SEGS (w_H W') mem') sc 8%nat (s0 + Z.of_nat (strip_lead (seg_spec.zs l))) /\
 sa_val (aview SEGS (w_H W') mem') ec 8%nat (e0 - Z.of_nat (strip_trail (seg_spec.zs l))) /\
 sa_kept SEGS W mem W' mem' regs ST_STK (fun a => sc <= a < sc + 8 \/ ec <= a < ec + 8) /\
 sa_noalloc B ly S ly' S').
(* the two cells, the frame window, and both *)
Definition st_cz (x : Z) : Prop := sc <= x < sc + 8 \/ ec <= x < ec + 8.
Definition st_wz (x : Z) : Prop := spZ regs - 16 <= x < spZ regs.
Definition st_xz (x : Z) : Prop := st_wz x \/ st_cz x.
(* the callee-saved registers the code never writes *)
Definition st_cs (r1 : bvmap 5 word) : Prop :=
getr r1 3 = getr regs 3 /\ getr r1 4 = getr regs 4 /\ getr r1 8 = getr regs 8 /\ getr r1 9 = getr regs 9 /\
getr r1 18 = getr regs 18 /\ getr r1 19 = getr regs 19 /\ getr r1 20 = getr regs 20 /\ getr r1 21 = getr regs 21 /\
getr r1 22 = getr regs 22 /\ getr r1 23 = getr regs 23 /\ getr r1 24 = getr regs 24 /\ getr r1 25 = getr regs 25 /\
getr r1 26 = getr regs 26 /\ getr r1 27 = getr regs 27.
(* a cut point: the journal from the entry, every byte outside the frame window and the cells unchanged, the saved
   ra, the two cells holding vs and ve and present, sp and the callee-saved registers *)
Definition st_cut (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) (vs ve : Z) : Prop :=
ajournal SEGS B ST_STK (spZ regs) [(sc, sc + 8); (ec, ec + 8)] ly S W mem md [] ly S W mem1 md1 0 /\
st_kz st_xz (rdW W mem) (rdW W mem1) /\
sa_val (rdW W mem1) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) /\
sa_val (rdW W mem1) sc 8 vs /\ sa_val (rdW W mem1) ec 8 ve /\
(forall k, 0 <= k < 8 -> apresent (w_H W) mem1 (sc + k)) /\
(forall k, 0 <= k < 8 -> apresent (w_H W) mem1 (ec + k)) /\
getr regs1 2 = w64 (spZ regs - 16) /\ st_cs regs1.

Lemma st_sp : spZ regs mod 16 = 0 /\ alloc_ceiling + 16 <= spZ regs /\ spZ regs <= 2 ^ 47 /\ ly_top ly <= 2 ^ 47.
Proof.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HST : ST_STK = 16) by reflexivity. rewrite HST in Hslo. lia.
Qed.
Lemma st_cells : 2 ^ 46 <= sc /\ sc + 8 <= 2 ^ 47 /\ 2 ^ 46 <= ec /\ ec + 8 <= 2 ^ 47 /\
  spZ regs <= sc /\ spZ regs <= ec /\ sc + 8 <= ly_top ly /\ ec + 8 <= ly_top ly.
Proof.
pose proof st_sp as (Hal16 & Hslo & Hshi & Htop). pose proof asan_consts as (A1 & _).
destruct HSLS as (L1 & L2 & _). destruct HSLE as (M1 & M2 & _). lia.
Qed.
Lemma st_bytes : 0 < e0 - s0 -> 4096 <= s0 /\ e0 <= alloc_ceiling /\ (forall x, s0 <= x < e0 -> ~ (SB <= x < SB + 2 ^ 44)).
Proof.
intros Hn. pose proof HPRE as (HAR & _).
destruct (st_loc ly S W mem md s0 (e0 - s0) HAR HSL Hn) as (L1 & L2 & L3).
split; [exact L1|]. split; [lia|]. intros x Hx. apply L3. lia.
Qed.
Lemma st_e0 : e0 <= 2 ^ 63.
Proof. destruct HSA as (_ & A1 & _). lia. Qed.
Lemma st_lead_le : (st_LEAD <= length l)%nat.
Proof. unfold st_LEAD, strip_lead. rewrite <- (st_zs_length l). apply takewhile_le. Qed.
Lemma st_trail_skipn : strip_trail (seg_spec.zs l) = length (SM.takewhile SM.blank (rev (skipn st_LEAD (seg_spec.zs l)))).
Proof. unfold strip_trail, st_LEAD, strip_lead. rewrite (dropwhile_skipn SM.blank (seg_spec.zs l)). reflexivity. Qed.

Ltac st_base :=
  pose proof st_sp as (Hal16 & Hslo & Hshi & Htop);
  pose proof st_cells as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8);
  pose proof asan_consts as (A1 & A2 & A3 & A4 & A5);
  pose proof st_e0 as He063.

(* the facts of the bytes and of the cells' shadow at a cut *)
Lemma st_byte_cut : forall regs1 mem1 md1 vs ve, st_cut regs1 mem1 md1 vs ve -> forall i, (i < length l)%nat ->
  rdW W mem1 (s0 + Z.of_nat i) = Some (bv_unsigned (nth i l ZB0)).
Proof.
intros regs1 mem1 md1 vs ve (HJ & HK & _) i Hi. st_base.
assert (Hn : 0 < e0 - s0) by lia. destruct (st_bytes Hn) as (Hs4 & Hec & Hsb).
rewrite (HK (s0 + Z.of_nat i)) by (first [lia | unfold st_xz, st_wz, st_cz; lia]).
exact (HSB i Hi).
Qed.
Lemma st_ra_cut : forall regs1 mem1 md1 vs ve, st_cut regs1 mem1 md1 vs ve -> forall a k, 0 <= a -> a + k <= 2 ^ 47 ->
  range_addressable (rdW W mem) SHADOW_OFF a k -> range_addressable (rdW W mem1) SHADOW_OFF a k.
Proof.
intros regs1 mem1 md1 vs ve (HJ & HK & _) a k Ha Hk HR. st_base.
apply (range_addressable_kept_win (rdW W mem) (rdW W mem1) (spZ regs - 16) (2 ^ 64)); [| lia | lia | lia | exact HR].
intros x Hx Hn. apply HK; [exact Hx | unfold st_xz, st_wz, st_cz; lia].
Qed.
(* a cut carried to a later state whose memory differs only in the cells *)
Lemma st_cut_next : forall regs1 mem1 md1 vs ve regs2 mem2 md2 vs' ve',
  st_cut regs1 mem1 md1 vs ve ->
  ajournal SEGS B ST_STK (spZ regs) [(sc, sc + 8); (ec, ec + 8)] ly S W mem md [] ly S W mem2 md2 0 ->
  st_kz st_cz (rdW W mem1) (rdW W mem2) ->
  (forall a, apresent (w_H W) mem1 a -> apresent (w_H W) mem2 a) ->
  sa_val (rdW W mem2) sc 8 vs' -> sa_val (rdW W mem2) ec 8 ve' ->
  getr regs2 2 = getr regs1 2 -> getr regs2 3 = getr regs1 3 -> getr regs2 4 = getr regs1 4 ->
  getr regs2 8 = getr regs1 8 -> getr regs2 9 = getr regs1 9 -> getr regs2 18 = getr regs1 18 ->
  getr regs2 19 = getr regs1 19 -> getr regs2 20 = getr regs1 20 -> getr regs2 21 = getr regs1 21 ->
  getr regs2 22 = getr regs1 22 -> getr regs2 23 = getr regs1 23 -> getr regs2 24 = getr regs1 24 ->
  getr regs2 25 = getr regs1 25 -> getr regs2 26 = getr regs1 26 -> getr regs2 27 = getr regs1 27 ->
  st_cut regs2 mem2 md2 vs' ve'.
Proof.
intros regs1 mem1 md1 vs ve regs2 mem2 md2 vs' ve'
  (HJ & HK & HFR & HCS & HCE & HPS & HPE & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27)
  HJ2 HK2 HP2 VS VE Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27.
st_base.
split; [exact HJ2|]. split.
{ intros x Hx Hn. rewrite (HK2 x Hx) by (unfold st_xz in Hn; tauto). exact (HK x Hx Hn). }
split.
{ intros k Hk. rewrite (HK2 _) by (first [lia | unfold st_cz; lia]). exact (HFR k Hk). }
split; [exact VS|]. split; [exact VE|].
split; [intros k Hk; apply HP2; exact (HPS k Hk)|].
split; [intros k Hk; apply HP2; exact (HPE k Hk)|].
rewrite Q2. split; [exact R2|].
unfold st_cs. rewrite Q3, Q4, Q8, Q9, Q18, Q19, Q20, Q21, Q22, Q23, Q24, Q25, Q26, Q27. auto 20.
Qed.
(* the first cut: the memory differs from the entry's only in the frame window *)
Lemma st_cut_entry : forall regs2 mem2 md2,
  ajournal SEGS B ST_STK (spZ regs) [(sc, sc + 8); (ec, ec + 8)] ly S W mem md [] ly S W mem2 md2 0 ->
  st_kz st_wz (rdW W mem) (rdW W mem2) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a) ->
  sa_val (rdW W mem2) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) ->
  getr regs2 2 = w64 (spZ regs - 16) ->
  getr regs2 3 = getr regs 3 -> getr regs2 4 = getr regs 4 -> getr regs2 8 = getr regs 8 -> getr regs2 9 = getr regs 9 ->
  getr regs2 18 = getr regs 18 -> getr regs2 19 = getr regs 19 -> getr regs2 20 = getr regs 20 ->
  getr regs2 21 = getr regs 21 -> getr regs2 22 = getr regs 22 -> getr regs2 23 = getr regs 23 ->
  getr regs2 24 = getr regs 24 -> getr regs2 25 = getr regs 25 -> getr regs2 26 = getr regs 26 ->
  getr regs2 27 = getr regs 27 ->
  st_cut regs2 mem2 md2 s0 e0.
Proof.
intros regs2 mem2 md2 HJ2 HK2 HP2 HFR Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27.
st_base.
destruct HSLS as (L1 & L2 & L3). destruct HSLE as (M1 & M2 & M3).
split; [exact HJ2|]. split.
{ intros x Hx Hn. apply HK2; [exact Hx | unfold st_xz in Hn; tauto]. }
split; [exact HFR|].
split; [intros k Hk; rewrite (HK2 _) by (first [lia | unfold st_wz; lia]); exact (HVS k Hk)|].
split; [intros k Hk; rewrite (HK2 _) by (first [lia | unfold st_wz; lia]); exact (HVE k Hk)|].
split; [intros k Hk; apply HP2; exact (L3 k Hk)|].
split; [intros k Hk; apply HP2; exact (M3 k Hk)|].
split; [exact Q2|].
unfold st_cs. auto 20.
Qed.

(* ---------- the tactics of the runs ---------- *)
(* the bytes a run may change, from its frame: the cells (loops) or the frame window (entry) *)
Ltac st_keep HFr K Zs rw :=
  lazymatch type of HFr with frame_of _ _ (mrestrict ?H ?m1) (mrestrict ?H ?m2) =>
  let x0 := fresh "x" in let Hx0 := fresh "Hx" in let Hn0 := fresh "Hn" in
  let b0 := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a0 := fresh "a" in
  let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
  assert (K : st_kz Zs (aview SEGS H m1) (aview SEGS H m2))
  by (intros x0 Hx0 Hn0; apply (kept_of_frame (segs := SEGS) _ _ _ _ _ Zs HFr);
      [ intros b0 wlo whi a0 Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin];
          [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset Nat.eqb] in Hrr; rw Hrr;
           unfold st_cz, st_wz; lia |]); destruct Hin
      | exact Hx0 | exact Hn0 ]) end.
Ltac st_track HFr HG KA PA Zs rw :=
  lazymatch type of HFr with frame_of _ _ (mrestrict ?H ?m1) (mrestrict ?H ?m2) =>
    let K := fresh "K" in st_keep HFr K Zs rw;
    let KA2 := fresh "KA" in pose proof (st_kz_trans _ _ _ _ KA K) as KA2; clear KA K; rename KA2 into KA;
    lazymatch type of PA with forall a, apresent _ ?m0 a -> _ =>
      let PA2 := fresh "PA" in
      assert (PA2 : forall a, apresent H m0 a -> apresent H m2 a)
        by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; eapply apresent_grows; [exact HG | exact (PA a Ha)]);
      clear PA; rename PA2 into PA end end;
  clear HFr HG.
(* every write of a loop run: the stack window or one cell (awr_byte's caller-stack arm, strip_slot) *)
Ltac st_awrc UC :=
  lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?sp0 ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk sp0 fp b0 bc fr lyx own) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [azlit_tac|]
  | eapply awr_ok_cons_gen;
    [ reflexivity | UC
    | let a0 := fresh "a" in let Ha0 := fresh "Ha" in intros a0 Ha0; cbn [YP09.r_wlo YP09.r_whi] in Ha0;
      right; right; right; right; right; left; split;
      [ first [ exists (sc, sc + 8); split; [left; reflexivity | cbn [fst snd]; lia]
              | exists (ec, ec + 8); split; [right; left; reflexivity | cbn [fst snd]; lia] ]
      | lia ]
    | ] ].

(* ---------- the epilogue: 0x87b30 .. 0x87b38, ra restored, sp += 16, ret ---------- *)
Lemma st_epi_seed : forall regs1 mem1, getr regs1 2 = w64 (spZ regs - 16) ->
  sa_val (rdW W mem1) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs1 [getr regs 1])) st_ss_epi
    (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + ST_EPI)) mem1 (seg_rom SEGS)))
  /\ sh_ok SEGS st_Bx [] (Eimg (Ereg regs1 [getr regs 1])) (mrestrict (w_H W) mem1).
Proof.
intros regs1 mem1 R2 HFR. st_base.
set (E := Eimg (Ereg regs1 [getr regs 1])).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 16).
{ subst E. rewrite (ew_Eimg_Ereg_nat regs1 _ 2 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
split; [|apply Forall_nil].
rewrite restrict_mkst_fx. unfold st_ss_epi. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  pose proof (bv_unsigned_in_range 64 (getr regs 1)) as HRr. change (bv_modulus 64) with (2 ^ 64) in HRr.
  apply (chunk_ok_val SEGS E _ (spZ regs - 16) 8 8 (SOff 32 0) (bv_unsigned (getr regs 1))).
  + cbn [sv_denot]. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_extra regs1 _ 0).
    cbn [nth]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact HRr.
  + cbn. lia.
  + replace (spZ regs - 16 + 8) with (spZ regs - 8) by lia. apply st_val_mem_of_sa_val. exact HFR.
- cbn. tauto.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|exact I]. unfold afact_ok, st_spF. cbn [af_lo af_hi af_al2].
  rewrite Usp. change (2 ^ 4) with 16. split; [lia|]. split; [|lia]. rewrite Zminus_mod, Hal16. reflexivity.
Qed.
Lemma st_epi : forall regs1 mem1 md1 vs ve, st_cut regs1 mem1 md1 vs ve ->
  vs = s0 + Z.of_nat (strip_lead (seg_spec.zs l)) -> ve = e0 - Z.of_nat (strip_trail (seg_spec.zs l)) ->
  SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + ST_EPI)) mem1 (seg_rom SEGS)) md1) st_Q.
Proof.
intros regs1 mem1 md1 vs ve
  (HJ & HK & HFR & HCS & HCE & HPS & HPE & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27)
  Evs Eve.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
st_base. assert (HST : ST_STK = 16) by reflexivity.
destruct (st_epi_seed regs1 mem1 R2 HFR) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs1 [getr regs 1]))) by apply Eimg_env.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (Eimg (Ereg regs1 [getr regs 1])) k = getr regs1 r)
  by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
assert (E32 : ew (Eimg (Ereg regs1 [getr regs 1])) 32 = getr regs 1)
  by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (Usp : bv_unsigned (ew (Eimg (Ereg regs1 [getr regs 1])) 2) = spZ regs - 16)
  by (rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
pose proof (EE 3%nat 3%bv eq_refl) as E3. pose proof (EE 4%nat 4%bv eq_refl) as E4.
pose proof (EE 8%nat 8%bv eq_refl) as E8. pose proof (EE 9%nat 9%bv eq_refl) as E9.
pose proof (EE 18%nat 18%bv eq_refl) as E18. pose proof (EE 19%nat 19%bv eq_refl) as E19.
pose proof (EE 20%nat 20%bv eq_refl) as E20. pose proof (EE 21%nat 21%bv eq_refl) as E21.
pose proof (EE 22%nat 22%bv eq_refl) as E22. pose proof (EE 23%nat 23%bv eq_refl) as E23.
pose proof (EE 24%nat 24%bv eq_refl) as E24. pose proof (EE 25%nat 25%bv eq_refl) as E25.
pose proof (EE 26%nat 26%bv eq_refl) as E26. pose proof (EE 27%nat 27%bv eq_refl) as E27.
remember (Eimg (Ereg regs1 [getr regs 1])) as E eqn:HE0. clear HE0.
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac. }
st_md.
pose proof (st_kz_refl (fun _ => False) (rdW W mem1)) as KA.
assert (PA : forall a, apresent (w_H W) mem1 a -> apresent (w_H W) mem1 a) by (intros a Ha; exact Ha).
st_track HFr HG KA PA (fun _ : Z => False) ltac:(fun H => idtac).
prreg HS (1%bv : bv 5) F1.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold st_Q, apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly, S, r, m, d end.
split.
{ rewrite F1. cbn [ew ewset Nat.eqb]. rewrite E32. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split.
{ apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ. }
split.
{ unfold aregs_preserved. intros r Hr.
  assert (Hcases : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
    r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (unfold acallee_saved in Hr; lia).
  clear Hr.
  repeat (destruct Hcases as [-> | Hcases]); [..| subst r];
  rewrite (st_ok_pi_restrict_reg (w_H W) _ _ _ _ HS); cbn [ms_regs];
  lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
  cbn [sv_denot ew ewset Nat.eqb];
  first
  [ rewrite Usp; replace (spZ regs - 16 + 16) with (spZ regs) by lia; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity
  | rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
    first [ rewrite E3, R3; reflexivity | rewrite E4, R4; reflexivity | rewrite E8, R8; reflexivity
          | rewrite E9, R9; reflexivity | rewrite E18, R18; reflexivity | rewrite E19, R19; reflexivity
          | rewrite E20, R20; reflexivity | rewrite E21, R21; reflexivity | rewrite E22, R22; reflexivity
          | rewrite E23, R23; reflexivity | rewrite E24, R24; reflexivity | rewrite E25, R25; reflexivity
          | rewrite E26, R26; reflexivity | rewrite E27, R27; reflexivity ] ]. }
split; [|split; [|split]].
- rewrite <- Evs. intros k Hk. rewrite (KA _) by (first [lia | tauto]). exact (HCS k Hk).
- rewrite <- Eve. intros k Hk. rewrite (KA _) by (first [lia | tauto]). exact (HCE k Hk).
- intros a Ha Hn Hc. rewrite (KA a Ha) by tauto. apply HK; [exact Ha|].
  rewrite HST in Hn. unfold st_xz, st_wz, st_cz. tauto.
- unfold sa_noalloc. split; [apply Permutation_refl|]. split; [reflexivity|]. exists (st_fs S). destruct S; reflexivity.
Qed.

(* ---------- the back loop head: 0x87acc with j trailing blanks dropped ---------- *)
Definition st_BLP (j : nat) (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
st_cut regs1 mem1 md1 (s0 + Z.of_nat st_LEAD) (e0 - Z.of_nat j) /\ (st_LEAD + j < length l)%nat /\
(forall i, (length l - j <= i < length l)%nat -> SM.blank (nth i (seg_spec.zs l) 0) = true) /\
getr regs1 5 = w64 32 /\ getr regs1 6 = w64 ST_MASK /\ getr regs1 7 = w64 2 /\
getr regs1 10 = w64 sc /\ getr regs1 11 = w64 ec /\ getr regs1 12 = w64 (e0 - Z.of_nat j - 1) /\
getr regs1 13 = w64 SB /\ getr regs1 14 = w64 (SB + sc / 8) /\ getr regs1 15 = w64 (SB + ec / 8) /\
getr regs1 16 = w64 (e0 - Z.of_nat j) /\ getr regs1 17 = w64 1.
Lemma st_bl_seed : forall (j : nat) c regs1 mem1, (st_LEAD + j < length l)%nat -> 0 <= c < 256 ->
  getr regs1 2 = w64 (spZ regs - 16) -> getr regs1 5 = w64 32 -> getr regs1 6 = w64 ST_MASK -> getr regs1 7 = w64 2 ->
  getr regs1 10 = w64 sc -> getr regs1 11 = w64 ec -> getr regs1 12 = w64 (e0 - Z.of_nat j - 1) ->
  getr regs1 13 = w64 SB -> getr regs1 14 = w64 (SB + sc / 8) -> getr regs1 15 = w64 (SB + ec / 8) ->
  getr regs1 16 = w64 (e0 - Z.of_nat j) -> getr regs1 17 = w64 1 ->
  sa_val (rdW W mem1) sc 8 (s0 + Z.of_nat st_LEAD) -> sa_val (rdW W mem1) ec 8 (e0 - Z.of_nat j) ->
  (forall k, 0 <= k < 8 -> apresent (w_H W) mem1 (ec + k)) ->
  rdW W mem1 (e0 - Z.of_nat j - 1) = Some c ->
  range_addressable (rdW W mem1) SHADOW_OFF sc 8 -> range_addressable (rdW W mem1) SHADOW_OFF ec 8 ->
  range_addressable (rdW W mem1) SHADOW_OFF (e0 - Z.of_nat j - 1) 1 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs1 (map w64 [SB; sc; ec; s0 + Z.of_nat st_LEAD; e0 - Z.of_nat j; c]))) st_ss_bl
    (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + ST_BL)) mem1 (seg_rom SEGS)))
  /\ sh_ok SEGS st_Bx st_SH_bl (Eimg (Ereg regs1 (map w64 [SB; sc; ec; s0 + Z.of_nat st_LEAD; e0 - Z.of_nat j; c])))
       (mrestrict (w_H W) mem1).
Proof.
intros j c regs1 mem1 Hjl Hc R2 R5 R6 R7 R10 R11 R12 R13 R14 R15 R16 R17 VC VE PE VS RAC RAE RAS.
st_base.
assert (Hn : 0 < e0 - s0) by lia. destruct (st_bytes Hn) as (Hs4 & Hec & Hsb).
pose proof (st_ex regs1 [SB; sc; ec; s0 + Z.of_nat st_LEAD; e0 - Z.of_nat j; c] 0 _ ltac:(unfold A_TEXT; lia) eq_refl) as E32.
pose proof (st_ex regs1 [SB; sc; ec; s0 + Z.of_nat st_LEAD; e0 - Z.of_nat j; c] 1 _ ltac:(unfold A_TEXT; lia) eq_refl) as E33.
pose proof (st_ex regs1 [SB; sc; ec; s0 + Z.of_nat st_LEAD; e0 - Z.of_nat j; c] 2 _ ltac:(unfold A_TEXT; lia) eq_refl) as E34.
pose proof (st_ex regs1 [SB; sc; ec; s0 + Z.of_nat st_LEAD; e0 - Z.of_nat j; c] 3 _ ltac:(unfold A_TEXT; lia) eq_refl) as E35.
pose proof (st_ex regs1 [SB; sc; ec; s0 + Z.of_nat st_LEAD; e0 - Z.of_nat j; c] 4 _ ltac:(unfold A_TEXT; lia) eq_refl) as E36.
pose proof (st_ex regs1 [SB; sc; ec; s0 + Z.of_nat st_LEAD; e0 - Z.of_nat j; c] 5 _ ltac:(unfold A_TEXT; lia) eq_refl) as E37.
cbn [Nat.add] in E32, E33, E34, E35, E36, E37.
set (E := Eimg (Ereg regs1 (map w64 [SB; sc; ec; s0 + Z.of_nat st_LEAD; e0 - Z.of_nat j; c]))) in *.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r) by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 16) by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (E32u : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (E33u : bv_unsigned (ew E 33) = sc) by (rewrite E33; apply unsigned_lit_small; lia).
assert (E34u : bv_unsigned (ew E 34) = ec) by (rewrite E34; apply unsigned_lit_small; lia).
assert (E35u : bv_unsigned (ew E 35) = s0 + Z.of_nat st_LEAD) by (rewrite E35; apply unsigned_lit_small; lia).
assert (E36u : bv_unsigned (ew E 36) = e0 - Z.of_nat j) by (rewrite E36; apply unsigned_lit_small; lia).
assert (E37u : bv_unsigned (ew E 37) = c) by (rewrite E37; apply unsigned_lit_small; lia).
assert (Dsc : sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 33 0) (SLit 3)) (SOff 32 0)) = Z_to_bv 64 (SB + sc / 8))
  by (rewrite (denot_shx E 33 32 0 sc SB E33 E32) by (unfold SB; lia); rewrite Z.add_0_r; reflexivity).
assert (Dec : sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 34 0) (SLit 3)) (SOff 32 0)) = Z_to_bv 64 (SB + ec / 8))
  by (rewrite (denot_shx E 34 32 0 ec SB E34 E32) by (unfold SB; lia); rewrite Z.add_0_r; reflexivity).
split.
- rewrite restrict_mkst_fx. unfold st_ss_bl. apply pa_entry_st_ok_full.
  + st_regs_ok EE ltac:(rewrite ?E33u, ?E34u, ?E35u, ?E36u, ?E37u, ?Usp) ltac:(first [rewrite Dsc | rewrite Dec]).
  + vm_compute. reflexivity.
  + unfold st_cellR. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite E33u. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ sc 0 8 (SOff 35 0) (s0 + Z.of_nat st_LEAD));
        [cbn [sv_denot]; rewrite E35u, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. apply st_val_mem_of_sa_val. exact VC.
    * rewrite E34u. split; [lia|]. split; [lia|]. split; [intros o Ho; apply (apresent_writable SEGS); apply PE; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ ec 0 8 (SOff 36 0) (e0 - Z.of_nat j));
        [cbn [sv_denot]; rewrite E36u, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. apply st_val_mem_of_sa_val. exact VE.
    * rewrite E36u. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ (e0 - Z.of_nat j) (-1) 1 (SOff 37 0) c);
        [cbn [sv_denot]; rewrite E37u, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
      apply st_val_mem_of_sa_val. replace (e0 - Z.of_nat j + -1) with (e0 - Z.of_nat j - 1) by lia.
      exact (st_val1 _ _ _ VS Hc).
  + apply pairwise_disjoint_of_extents. unfold st_cellR, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E33u, E34u, E36u.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj, sa_disj in *. cbn [fst snd]. repeat split; lia.
  + split; [|split; exact I]. cbn [f_atoms atoms_ok].
    unfold afact_ok, st_spF, st_SBF, st_CELLF, st_PTRF, st_BYTEF. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32u, E33u, E34u, E35u, E36u, E37u. change (2 ^ 4) with 16. change (2 ^ 3) with 8.
    rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat split; try lia; first [rewrite Zminus_mod, Hal16; reflexivity | exact HSC8 | exact HEC8].
- unfold sh_ok, st_SH_bl. repeat apply Forall_cons; try apply Forall_nil.
  + apply (st_shent_ok E _ 33 sc 0 8 E32 E33u); try lia; [rewrite Z.add_0_r; exact RAC | intros y Hy; unfold SB; lia].
  + apply (st_shent_ok E _ 34 ec 0 8 E32 E34u); try lia; [rewrite Z.add_0_r; exact RAE | intros y Hy; unfold SB; lia].
  + apply (st_shent_ok E _ 36 (e0 - Z.of_nat j) (-1) 0 E32 E36u); try lia;
      [replace (e0 - Z.of_nat j + -1) with (e0 - Z.of_nat j - 1) by lia; exact RAS | intros y Hy; apply Hsb; lia].
Qed.

Lemma st_bl_step : forall j regs1 mem1 md1,
  (forall r m d, st_BLP (Datatypes.S j) r m d -> SRr SEGS W (mkCfg (mkst r (Z_to_bv 64 (BASE + ST_BL)) m (seg_rom SEGS)) d) st_Q) ->
  st_BLP j regs1 mem1 md1 ->
  SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + ST_BL)) mem1 (seg_rom SEGS)) md1) st_Q.
Proof.
intros j regs1 mem1 md1 NXT (HCUT & Hjl & HBL & R5 & R6 & R7 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17).
pose proof HCUT as (HJ & HK & HFR & HCS & HCE & HPS & HPE & R2 & HCSR).
st_base. pose proof st_lead_le as HLL.
assert (Hn : 0 < e0 - s0) by lia. destruct (st_bytes Hn) as (Hs4 & Hec & Hsb).
set (q := (length l - Datatypes.S j)%nat).
assert (Hq : (q < length l)%nat) by (unfold q; lia).
assert (Hqv : s0 + Z.of_nat q = e0 - Z.of_nat j - 1) by (unfold q; lia).
set (c := bv_unsigned (nth q l ZB0)).
assert (VS : rdW W mem1 (e0 - Z.of_nat j - 1) = Some c) by (rewrite <- Hqv; exact (st_byte_cut _ _ _ _ _ HCUT q Hq)).
pose proof (sa_aview_rng _ _ _ _ _ VS) as Hcr.
assert (RAS : range_addressable (rdW W mem1) SHADOW_OFF (e0 - Z.of_nat j - 1) 1).
{ apply (st_ra_cut _ _ _ _ _ HCUT); [lia | lia |].
  destruct HSA as (_ & _ & _ & SA3 & _). apply (range_addressable_sub _ _ s0 (e0 - s0)); [exact SA3 | lia | lia]. }
assert (RAC : range_addressable (rdW W mem1) SHADOW_OFF sc 8)
  by (apply (st_ra_cut _ _ _ _ _ HCUT); [lia | lia | destruct HAS as (_ & _ & _ & X & _); exact X]).
assert (RAE : range_addressable (rdW W mem1) SHADOW_OFF ec 8)
  by (apply (st_ra_cut _ _ _ _ _ HCUT); [lia | lia | destruct HAE as (_ & _ & _ & X & _); exact X]).
assert (HZ : nth q (seg_spec.zs l) 0 = c) by (apply st_zs_nth; exact Hq).
clearbody c.
(* the trailing blanks when the byte at e - 1 is not blank *)
assert (TRX : SM.blank c = false -> strip_trail (seg_spec.zs l) = j).
{ intros Hb. rewrite st_trail_skipn. apply st_trail_exit.
  - rewrite length_skipn, st_zs_length. lia.
  - intros k Hk. rewrite length_skipn, st_zs_length in Hk. rewrite st_nth_skipn. apply HBL. lia.
  - rewrite length_skipn, st_zs_length, st_nth_skipn.
    replace (st_LEAD + (length l - st_LEAD - Datatypes.S j))%nat with q by (unfold q; lia). rewrite HZ. exact Hb. }
destruct (st_bl_seed j c regs1 mem1 Hjl Hcr R2 R5 R6 R7 R10 R11 R12 R13 R14 R15 R16 R17 HCS HCE HPE VS RAC RAE RAS)
  as [HS SHOK].
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs1 (map w64 [SB; sc; ec; s0 + Z.of_nat st_LEAD; e0 - Z.of_nat j; c]))))
  by apply Eimg_env.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r ->
  ew (Eimg (Ereg regs1 (map w64 [SB; sc; ec; s0 + Z.of_nat st_LEAD; e0 - Z.of_nat j; c]))) k = getr regs1 r)
  by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
pose proof (st_ex regs1 [SB; sc; ec; s0 + Z.of_nat st_LEAD; e0 - Z.of_nat j; c] 0 _ ltac:(unfold A_TEXT; lia) eq_refl) as E32.
pose proof (st_ex regs1 [SB; sc; ec; s0 + Z.of_nat st_LEAD; e0 - Z.of_nat j; c] 1 _ ltac:(unfold A_TEXT; lia) eq_refl) as E33.
pose proof (st_ex regs1 [SB; sc; ec; s0 + Z.of_nat st_LEAD; e0 - Z.of_nat j; c] 2 _ ltac:(unfold A_TEXT; lia) eq_refl) as E34.
pose proof (st_ex regs1 [SB; sc; ec; s0 + Z.of_nat st_LEAD; e0 - Z.of_nat j; c] 3 _ ltac:(unfold A_TEXT; lia) eq_refl) as E35.
pose proof (st_ex regs1 [SB; sc; ec; s0 + Z.of_nat st_LEAD; e0 - Z.of_nat j; c] 4 _ ltac:(unfold A_TEXT; lia) eq_refl) as E36.
pose proof (st_ex regs1 [SB; sc; ec; s0 + Z.of_nat st_LEAD; e0 - Z.of_nat j; c] 5 _ ltac:(unfold A_TEXT; lia) eq_refl) as E37.
cbn [Nat.add] in E32, E33, E34, E35, E36, E37.
remember (Eimg (Ereg regs1 (map w64 [SB; sc; ec; s0 + Z.of_nat st_LEAD; e0 - Z.of_nat j; c]))) as E eqn:HE0. clear HE0.
assert (E33u : bv_unsigned (ew E 33) = sc) by (rewrite E33; apply unsigned_lit_small; lia).
assert (E34u : bv_unsigned (ew E 34) = ec) by (rewrite E34; apply unsigned_lit_small; lia).
assert (E35u : bv_unsigned (ew E 35) = s0 + Z.of_nat st_LEAD) by (rewrite E35; apply unsigned_lit_small; lia).
assert (E36u : bv_unsigned (ew E 36) = e0 - Z.of_nat j) by (rewrite E36; apply unsigned_lit_small; lia).
(* 0x87acc .. 0x87ae4: beq a6,a7 (decided), the check of e[-1], lbu, bltu 32,t3 *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ st_awrc ltac:(cbn [ew ewset Nat.eqb]; exact E34u). }
st_md.
pose proof (st_kz_refl st_cz (rdW W mem1)) as KA.
assert (PA : forall a, apresent (w_H W) mem1 a -> apresent (w_H W) mem1 a) by (intros a Ha; exact Ha).
st_track HFr HG KA PA st_cz ltac:(fun H => rewrite ?E33u, ?E34u in H). clear HF.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* 32 < c: not blank, 0x87b30 *)
  assert (Hgt : 32 < c).
  { rewrite branch_ltu_U, U_SLit in Hc. rewrite (U_atom _ 37 c) in Hc by (first [cbn [ew ewset Nat.eqb]; exact E37 | lia]).
    apply Z.ltb_lt in Hc. change (zcanon 32) with 32 in Hc. exact Hc. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan ST_EPI.
  { st_awrc ltac:(cbn [ew ewset Nat.eqb]; exact E34u). }
  st_md. st_track HFr HG KA PA st_cz ltac:(fun H => rewrite ?E33u, ?E34u in H). clear HF.
  pmkst HS.
  apply (st_epi _ _ _ (s0 + Z.of_nat st_LEAD) (e0 - Z.of_nat j)).
  + eapply (st_cut_next _ _ _ _ _ _ _ _ _ _ HCUT HJ KA PA);
      [ eapply (st_reg_val _ _ _ _ 0%nat); [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; exact E33u
        | cbn [sv_denot ew ewset Nat.eqb]; rewrite E35u; f_equal; lia | lia]
      | eapply (st_reg_val _ _ _ _ 1%nat); [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; exact E34u
        | cbn [sv_denot ew ewset Nat.eqb]; rewrite E36u; f_equal; lia | lia]
      | .. ]; st_same HS EE.
  + reflexivity.
  + rewrite (TRX (st_blank_gt c Hgt)). reflexivity.
- assert (Hle : c <= 32).
  { rewrite branch_ltu_U, U_SLit in Hc. rewrite (U_atom _ 37 c) in Hc by (first [cbn [ew ewset Nat.eqb]; exact E37 | lia]).
    apply Z.ltb_ge in Hc. change (zcanon 32) with 32 in Hc. exact Hc. }
  clear Hc.
  (* 0x87ae8 .. 0x87af0: (t1 >> t3) & 1, beqz *)
  paj_run_tok RUN HS HJ SHOK Bspan.
  { st_awrc ltac:(cbn [ew ewset Nat.eqb]; exact E34u). }
  st_md. st_track HFr HG KA PA st_cz ltac:(fun H => rewrite ?E33u, ?E34u in H). clear HF.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* the bit is clear: not blank, 0x87b30 *)
    assert (Hnb : SM.blank c = false).
    { rewrite branch_eq_U, U_SLit in Hc. rewrite (st_bit_U _ 37 c) in Hc by (first [cbn [ew ewset Nat.eqb]; exact E37 | lia]).
      destruct (SM.blank c); [vm_compute in Hc; discriminate Hc | reflexivity]. }
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan ST_EPI.
    { st_awrc ltac:(cbn [ew ewset Nat.eqb]; exact E34u). }
    st_md. st_track HFr HG KA PA st_cz ltac:(fun H => rewrite ?E33u, ?E34u in H). clear HF.
    pmkst HS.
    apply (st_epi _ _ _ (s0 + Z.of_nat st_LEAD) (e0 - Z.of_nat j)).
    * eapply (st_cut_next _ _ _ _ _ _ _ _ _ _ HCUT HJ KA PA);
        [ eapply (st_reg_val _ _ _ _ 0%nat); [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; exact E33u
          | cbn [sv_denot ew ewset Nat.eqb]; rewrite E35u; f_equal; lia | lia]
        | eapply (st_reg_val _ _ _ _ 1%nat); [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; exact E34u
          | cbn [sv_denot ew ewset Nat.eqb]; rewrite E36u; f_equal; lia | lia]
        | .. ]; st_same HS EE.
    * reflexivity.
    * rewrite (TRX Hnb). reflexivity.
  + (* blank: 0x87af4 .. 0x87b18, bltu a6,t2 (decided), the store of e - 1, t3 := *sc, bltu t3,a6 *)
    assert (Hb : SM.blank c = true).
    { rewrite branch_eq_U, U_SLit in Hc. rewrite (st_bit_U _ 37 c) in Hc by (first [cbn [ew ewset Nat.eqb]; exact E37 | lia]).
      destruct (SM.blank c); [reflexivity | vm_compute in Hc; discriminate Hc]. }
    clear Hc.
    paj_run_tok RUN HS HJ SHOK Bspan.
    { st_awrc ltac:(cbn [ew ewset Nat.eqb]; exact E34u). }
    st_md. st_track HFr HG KA PA st_cz ltac:(fun H => rewrite ?E33u, ?E34u in H). clear HF.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * (* s < e - 1: the next byte from the back *)
      assert (Hlt : s0 + Z.of_nat st_LEAD < e0 - Z.of_nat j - 1).
      { rewrite branch_ltu_U in Hc.
        rewrite (U_atom _ 35 (s0 + Z.of_nat st_LEAD)) in Hc by (first [cbn [ew ewset Nat.eqb]; exact E35 | lia]).
        rewrite (U_atom_off _ 36 (e0 - Z.of_nat j) (-1)) in Hc by (first [cbn [ew ewset Nat.eqb]; exact E36 | lia]).
        apply Z.ltb_lt in Hc. lia. }
      clear Hc.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan ST_BL.
      { st_awrc ltac:(cbn [ew ewset Nat.eqb]; exact E34u). }
      st_md. st_track HFr HG KA PA st_cz ltac:(fun H => rewrite ?E33u, ?E34u in H). clear HF.
      pmkst HS.
      apply NXT. split.
      { eapply (st_cut_next _ _ _ _ _ _ _ _ _ _ HCUT HJ KA PA);
          [ eapply (st_reg_val _ _ _ _ 0%nat); [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; exact E33u
            | cbn [sv_denot ew ewset Nat.eqb]; rewrite E35u; f_equal; lia | lia]
          | eapply (st_reg_val _ _ _ _ 1%nat); [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; exact E34u
            | cbn [sv_denot ew ewset Nat.eqb]; rewrite E36u; f_equal; lia | lia]
          | .. ]; st_same HS EE. }
      split; [lia|].
      split.
      { intros k Hk. destruct (Nat.eq_dec k q) as [->|Hne]; [rewrite HZ; exact Hb | apply HBL; unfold q in *; lia]. }
      split; [st_rv HS ltac:(rewrite ?E33u, ?E34u, ?E35u, ?E36u)|].
      split; [st_rv HS ltac:(rewrite ?E33u, ?E34u, ?E35u, ?E36u)|].
      split; [st_rv HS ltac:(rewrite ?E33u, ?E34u, ?E35u, ?E36u)|].
      split; [st_rv HS ltac:(rewrite ?E33u, ?E34u, ?E35u, ?E36u)|].
      split; [st_rv HS ltac:(rewrite ?E33u, ?E34u, ?E35u, ?E36u)|].
      split; [st_rv HS ltac:(rewrite ?E33u, ?E34u, ?E35u, ?E36u)|].
      split; [st_rv HS ltac:(rewrite ?E32, ?E33u, ?E34u, ?E35u, ?E36u; unfold w64; rewrite unsigned_lit_small by (unfold SB; lia))|].
      split; [st_rvx HS E33 E32 sc|].
      split; [st_rvx HS E34 E32 ec|].
      split; st_rv HS ltac:(rewrite ?E33u, ?E34u, ?E35u, ?E36u).
    * (* s >= e - 1: every byte after the leading blanks is blank, 0x87b30 *)
      assert (Hge : e0 - Z.of_nat j - 1 <= s0 + Z.of_nat st_LEAD).
      { rewrite branch_ltu_U in Hc.
        rewrite (U_atom _ 35 (s0 + Z.of_nat st_LEAD)) in Hc by (first [cbn [ew ewset Nat.eqb]; exact E35 | lia]).
        rewrite (U_atom_off _ 36 (e0 - Z.of_nat j) (-1)) in Hc by (first [cbn [ew ewset Nat.eqb]; exact E36 | lia]).
        apply Z.ltb_ge in Hc. lia. }
      clear Hc.
      assert (HLj : (st_LEAD + Datatypes.S j = length l)%nat) by lia.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan ST_EPI.
      { st_awrc ltac:(cbn [ew ewset Nat.eqb]; exact E34u). }
      st_md. st_track HFr HG KA PA st_cz ltac:(fun H => rewrite ?E33u, ?E34u in H). clear HF.
      pmkst HS.
      apply (st_epi _ _ _ (s0 + Z.of_nat st_LEAD) (e0 - Z.of_nat (Datatypes.S j))).
      { eapply (st_cut_next _ _ _ _ _ _ _ _ _ _ HCUT HJ KA PA);
          [ eapply (st_reg_val _ _ _ _ 0%nat); [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; exact E33u
            | cbn [sv_denot ew ewset Nat.eqb]; rewrite E35u; f_equal; lia | lia]
          | eapply (st_reg_val _ _ _ _ 1%nat); [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; exact E34u
            | cbn [sv_denot ew ewset Nat.eqb]; rewrite E36u; f_equal; lia | lia]
          | .. ]; st_same HS EE. }
      { reflexivity. }
      rewrite st_trail_skipn. rewrite st_trail_all.
      { rewrite length_skipn, st_zs_length. lia. }
      intros k Hk. rewrite length_skipn, st_zs_length in Hk. rewrite st_nth_skipn.
      destruct (Nat.eq_dec (st_LEAD + k) q) as [Hq'|Hne]; [rewrite Hq', HZ; exact Hb | apply HBL; unfold q in *; lia].
Qed.
Lemma st_bl_all : forall dd j, (j + dd = length l - st_LEAD)%nat -> forall r m d, st_BLP j r m d ->
  SRr SEGS W (mkCfg (mkst r (Z_to_bv 64 (BASE + ST_BL)) m (seg_rom SEGS)) d) st_Q.
Proof.
induction dd as [|dd IH]; intros j Hd r m d HLP.
- exfalso. destruct HLP as (_ & Hjl & _). lia.
- apply (st_bl_step j); [|exact HLP].
  intros r' m' d' HLP'. apply (IH (Datatypes.S j)); [lia | exact HLP'].
Qed.

(* ---------- the back part: 0x87a94 with *sc = s0 + strip_lead ---------- *)
Definition st_BKP (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
st_cut regs1 mem1 md1 (s0 + Z.of_nat st_LEAD) e0 /\
getr regs1 10 = w64 sc /\ getr regs1 11 = w64 ec /\ getr regs1 13 = w64 SB /\
getr regs1 14 = w64 (SB + sc / 8) /\ getr regs1 15 = w64 (SB + ec / 8).
Lemma st_bk_seed : forall regs1 mem1,
  getr regs1 2 = w64 (spZ regs - 16) -> getr regs1 10 = w64 sc -> getr regs1 11 = w64 ec -> getr regs1 13 = w64 SB ->
  getr regs1 14 = w64 (SB + sc / 8) -> getr regs1 15 = w64 (SB + ec / 8) ->
  sa_val (rdW W mem1) sc 8 (s0 + Z.of_nat st_LEAD) -> sa_val (rdW W mem1) ec 8 e0 ->
  range_addressable (rdW W mem1) SHADOW_OFF sc 8 -> range_addressable (rdW W mem1) SHADOW_OFF ec 8 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs1 (map w64 [SB; sc; ec; s0 + Z.of_nat st_LEAD; e0]))) st_ss_bk
    (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + ST_BK)) mem1 (seg_rom SEGS)))
  /\ sh_ok SEGS st_Bx st_SH_bk (Eimg (Ereg regs1 (map w64 [SB; sc; ec; s0 + Z.of_nat st_LEAD; e0]))) (mrestrict (w_H W) mem1).
Proof.
intros regs1 mem1 R2 R10 R11 R13 R14 R15 VC VE RAC RAE.
st_base. pose proof st_lead_le as HLL.
pose proof (st_ex regs1 [SB; sc; ec; s0 + Z.of_nat st_LEAD; e0] 0 _ ltac:(unfold A_TEXT; lia) eq_refl) as E32.
pose proof (st_ex regs1 [SB; sc; ec; s0 + Z.of_nat st_LEAD; e0] 1 _ ltac:(unfold A_TEXT; lia) eq_refl) as E33.
pose proof (st_ex regs1 [SB; sc; ec; s0 + Z.of_nat st_LEAD; e0] 2 _ ltac:(unfold A_TEXT; lia) eq_refl) as E34.
pose proof (st_ex regs1 [SB; sc; ec; s0 + Z.of_nat st_LEAD; e0] 3 _ ltac:(unfold A_TEXT; lia) eq_refl) as E35.
pose proof (st_ex regs1 [SB; sc; ec; s0 + Z.of_nat st_LEAD; e0] 4 _ ltac:(unfold A_TEXT; lia) eq_refl) as E36.
cbn [Nat.add] in E32, E33, E34, E35, E36.
set (E := Eimg (Ereg regs1 (map w64 [SB; sc; ec; s0 + Z.of_nat st_LEAD; e0]))) in *.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r) by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 16) by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (E32u : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (E33u : bv_unsigned (ew E 33) = sc) by (rewrite E33; apply unsigned_lit_small; lia).
assert (E34u : bv_unsigned (ew E 34) = ec) by (rewrite E34; apply unsigned_lit_small; lia).
assert (E35u : bv_unsigned (ew E 35) = s0 + Z.of_nat st_LEAD) by (rewrite E35; apply unsigned_lit_small; lia).
assert (E36u : bv_unsigned (ew E 36) = e0) by (rewrite E36; apply unsigned_lit_small; lia).
assert (Dsc : sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 33 0) (SLit 3)) (SOff 32 0)) = Z_to_bv 64 (SB + sc / 8))
  by (rewrite (denot_shx E 33 32 0 sc SB E33 E32) by (unfold SB; lia); rewrite Z.add_0_r; reflexivity).
assert (Dec : sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 34 0) (SLit 3)) (SOff 32 0)) = Z_to_bv 64 (SB + ec / 8))
  by (rewrite (denot_shx E 34 32 0 ec SB E34 E32) by (unfold SB; lia); rewrite Z.add_0_r; reflexivity).
split.
- rewrite restrict_mkst_fx. unfold st_ss_bk. apply pa_entry_st_ok_full.
  + st_regs_ok EE ltac:(rewrite ?E33u, ?E34u, ?E35u, ?E36u, ?Usp) ltac:(first [rewrite Dsc | rewrite Dec]).
  + vm_compute. reflexivity.
  + unfold st_cellR. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite E33u. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ sc 0 8 (SOff 35 0) (s0 + Z.of_nat st_LEAD));
        [cbn [sv_denot]; rewrite E35u, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. apply st_val_mem_of_sa_val. exact VC.
    * rewrite E34u. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ ec 0 8 (SOff 36 0) e0);
        [cbn [sv_denot]; rewrite E36u, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. apply st_val_mem_of_sa_val. exact VE.
  + apply pairwise_disjoint_of_extents. unfold st_cellR, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E33u, E34u.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj, sa_disj in *. cbn [fst snd]. repeat split; lia.
  + split; [|split; exact I]. cbn [f_atoms atoms_ok].
    unfold afact_ok, st_spF, st_SBF, st_CELLF. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32u, E33u, E34u. change (2 ^ 4) with 16. change (2 ^ 3) with 8.
    rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat split; try lia; first [rewrite Zminus_mod, Hal16; reflexivity | exact HSC8 | exact HEC8].
- unfold sh_ok, st_SH_bk. repeat apply Forall_cons; try apply Forall_nil.
  + apply (st_shent_ok E _ 33 sc 0 8 E32 E33u); try lia; [rewrite Z.add_0_r; exact RAC | intros y Hy; unfold SB; lia].
  + apply (st_shent_ok E _ 34 ec 0 8 E32 E34u); try lia; [rewrite Z.add_0_r; exact RAE | intros y Hy; unfold SB; lia].
Qed.
Lemma st_bk : forall regs1 mem1 md1, st_BKP regs1 mem1 md1 ->
  SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + ST_BK)) mem1 (seg_rom SEGS)) md1) st_Q.
Proof.
intros regs1 mem1 md1 (HCUT & R10 & R11 & R13 & R14 & R15).
pose proof HCUT as (HJ & HK & HFR & HCS & HCE & HPS & HPE & R2 & HCSR).
st_base. pose proof st_lead_le as HLL.
assert (RAC : range_addressable (rdW W mem1) SHADOW_OFF sc 8)
  by (apply (st_ra_cut _ _ _ _ _ HCUT); [lia | lia | destruct HAS as (_ & _ & _ & X & _); exact X]).
assert (RAE : range_addressable (rdW W mem1) SHADOW_OFF ec 8)
  by (apply (st_ra_cut _ _ _ _ _ HCUT); [lia | lia | destruct HAE as (_ & _ & _ & X & _); exact X]).
destruct (st_bk_seed regs1 mem1 R2 R10 R11 R13 R14 R15 HCS HCE RAC RAE) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs1 (map w64 [SB; sc; ec; s0 + Z.of_nat st_LEAD; e0])))) by apply Eimg_env.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r ->
  ew (Eimg (Ereg regs1 (map w64 [SB; sc; ec; s0 + Z.of_nat st_LEAD; e0]))) k = getr regs1 r)
  by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
pose proof (st_ex regs1 [SB; sc; ec; s0 + Z.of_nat st_LEAD; e0] 0 _ ltac:(unfold A_TEXT; lia) eq_refl) as E32.
pose proof (st_ex regs1 [SB; sc; ec; s0 + Z.of_nat st_LEAD; e0] 1 _ ltac:(unfold A_TEXT; lia) eq_refl) as E33.
pose proof (st_ex regs1 [SB; sc; ec; s0 + Z.of_nat st_LEAD; e0] 2 _ ltac:(unfold A_TEXT; lia) eq_refl) as E34.
pose proof (st_ex regs1 [SB; sc; ec; s0 + Z.of_nat st_LEAD; e0] 3 _ ltac:(unfold A_TEXT; lia) eq_refl) as E35.
pose proof (st_ex regs1 [SB; sc; ec; s0 + Z.of_nat st_LEAD; e0] 4 _ ltac:(unfold A_TEXT; lia) eq_refl) as E36.
cbn [Nat.add] in E32, E33, E34, E35, E36.
remember (Eimg (Ereg regs1 (map w64 [SB; sc; ec; s0 + Z.of_nat st_LEAD; e0]))) as E eqn:HE0. clear HE0.
assert (E33u : bv_unsigned (ew E 33) = sc) by (rewrite E33; apply unsigned_lit_small; lia).
assert (E34u : bv_unsigned (ew E 34) = ec) by (rewrite E34; apply unsigned_lit_small; lia).
assert (E35u : bv_unsigned (ew E 35) = s0 + Z.of_nat st_LEAD) by (rewrite E35; apply unsigned_lit_small; lia).
assert (E36u : bv_unsigned (ew E 36) = e0) by (rewrite E36; apply unsigned_lit_small; lia).
(* 0x87a94 .. 0x87aac: the checks of ec and sc, e := *ec, s := *sc, bgeu s,e *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac. }
st_md.
pose proof (st_kz_refl st_cz (rdW W mem1)) as KA.
assert (PA : forall a, apresent (w_H W) mem1 a -> apresent (w_H W) mem1 a) by (intros a Ha; exact Ha).
st_track HFr HG KA PA st_cz ltac:(fun H => rewrite ?E33u, ?E34u in H). clear HF.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* s >= e0: every byte is a leading blank, 0x87b30 *)
  assert (Hge : e0 <= s0 + Z.of_nat st_LEAD).
  { rewrite branch_geu_U in Hc.
    rewrite (U_atom _ 35 (s0 + Z.of_nat st_LEAD)) in Hc by (first [cbn [ew ewset Nat.eqb]; exact E35 | lia]).
    rewrite (U_atom _ 36 e0) in Hc by (first [cbn [ew ewset Nat.eqb]; exact E36 | lia]).
    apply negb_true_iff, Z.ltb_ge in Hc. exact Hc. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan ST_EPI.
  { awr_ok_tac. }
  st_md. st_track HFr HG KA PA st_cz ltac:(fun H => rewrite ?E33u, ?E34u in H). clear HF.
  pmkst HS.
  apply (st_epi _ _ _ (s0 + Z.of_nat st_LEAD) e0).
  + eapply (st_cut_next _ _ _ _ _ _ _ _ _ _ HCUT HJ KA PA);
      [ eapply (st_reg_val _ _ _ _ 0%nat); [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; exact E33u
        | cbn [sv_denot ew ewset Nat.eqb]; rewrite E35u; f_equal; lia | lia]
      | eapply (st_reg_val _ _ _ _ 1%nat); [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; exact E34u
        | cbn [sv_denot ew ewset Nat.eqb]; rewrite E36u; f_equal; lia | lia]
      | .. ]; st_same HS EE.
  + reflexivity.
  + assert (HLn : st_LEAD = length l) by lia.
    rewrite st_trail_skipn, HLn, <- (st_zs_length l), skipn_all. cbn [rev SM.takewhile length]. lia.
- (* s < e0: the back loop at j = 0, 0x87ab0 .. 0x87ac8 *)
  assert (Hlt : s0 + Z.of_nat st_LEAD < e0).
  { rewrite branch_geu_U in Hc.
    rewrite (U_atom _ 35 (s0 + Z.of_nat st_LEAD)) in Hc by (first [cbn [ew ewset Nat.eqb]; exact E35 | lia]).
    rewrite (U_atom _ 36 e0) in Hc by (first [cbn [ew ewset Nat.eqb]; exact E36 | lia]).
    apply negb_false_iff, Z.ltb_lt in Hc. exact Hc. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan ST_BL.
  { awr_ok_tac. }
  st_md. st_track HFr HG KA PA st_cz ltac:(fun H => rewrite ?E33u, ?E34u in H). clear HF.
  pmkst HS.
  apply (st_bl_all (length l - st_LEAD) 0); [lia|].
  split.
  { replace (e0 - Z.of_nat 0) with e0 by lia.
    eapply (st_cut_next _ _ _ _ _ _ _ _ _ _ HCUT HJ KA PA);
      [ eapply (st_reg_val _ _ _ _ 0%nat); [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; exact E33u
        | cbn [sv_denot ew ewset Nat.eqb]; rewrite E35u; f_equal; lia | lia]
      | eapply (st_reg_val _ _ _ _ 1%nat); [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; exact E34u
        | cbn [sv_denot ew ewset Nat.eqb]; rewrite E36u; f_equal; lia | lia]
      | .. ]; st_same HS EE. }
  split; [lia|].
  split; [intros k Hk; lia|].
  split; [st_rv HS ltac:(rewrite ?E33u, ?E34u, ?E35u, ?E36u)|].
  split; [st_rv HS ltac:(rewrite ?E33u, ?E34u, ?E35u, ?E36u)|].
  split; [st_rv HS ltac:(rewrite ?E33u, ?E34u, ?E35u, ?E36u)|].
  split; [st_rv HS ltac:(rewrite ?E33u, ?E34u, ?E35u, ?E36u)|].
  split; [st_rv HS ltac:(rewrite ?E33u, ?E34u, ?E35u, ?E36u)|].
  split; [st_rv HS ltac:(rewrite ?E33u, ?E34u, ?E35u, ?E36u)|].
  split; [st_rv HS ltac:(rewrite ?E32, ?E33u, ?E34u, ?E35u, ?E36u; unfold w64; rewrite unsigned_lit_small by (unfold SB; lia))|].
  split; [st_rvx HS E33 E32 sc|].
  split; [st_rvx HS E34 E32 ec|].
  split; st_rv HS ltac:(rewrite ?E33u, ?E34u, ?E35u, ?E36u).
Qed.

(* ---------- the forward loop head: 0x87a30 at byte i ---------- *)
Definition st_FWP (i : nat) (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
st_cut regs1 mem1 md1 (s0 + Z.of_nat i) e0 /\ (i < length l)%nat /\
(forall j, (j < i)%nat -> SM.blank (nth j (seg_spec.zs l) 0) = true) /\
getr regs1 5 = w64 ST_MASK /\ getr regs1 6 = w64 1 /\ getr regs1 10 = w64 sc /\ getr regs1 11 = w64 ec /\
getr regs1 12 = w64 (s0 + Z.of_nat i) /\ getr regs1 13 = w64 SB /\ getr regs1 14 = w64 (SB + sc / 8) /\
getr regs1 15 = w64 (SB + ec / 8) /\ getr regs1 16 = w64 (s0 + Z.of_nat i) /\ getr regs1 17 = w64 32.
Lemma st_fw_seed : forall (i : nat) c regs1 mem1, (i < length l)%nat -> 0 <= c < 256 ->
  getr regs1 2 = w64 (spZ regs - 16) -> getr regs1 5 = w64 ST_MASK -> getr regs1 6 = w64 1 ->
  getr regs1 10 = w64 sc -> getr regs1 11 = w64 ec -> getr regs1 12 = w64 (s0 + Z.of_nat i) ->
  getr regs1 13 = w64 SB -> getr regs1 14 = w64 (SB + sc / 8) -> getr regs1 15 = w64 (SB + ec / 8) ->
  getr regs1 16 = w64 (s0 + Z.of_nat i) -> getr regs1 17 = w64 32 ->
  sa_val (rdW W mem1) sc 8 (s0 + Z.of_nat i) -> sa_val (rdW W mem1) ec 8 e0 ->
  (forall k, 0 <= k < 8 -> apresent (w_H W) mem1 (sc + k)) ->
  rdW W mem1 (s0 + Z.of_nat i) = Some c ->
  range_addressable (rdW W mem1) SHADOW_OFF sc 8 -> range_addressable (rdW W mem1) SHADOW_OFF ec 8 ->
  range_addressable (rdW W mem1) SHADOW_OFF (s0 + Z.of_nat i) 1 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs1 (map w64 [SB; sc; ec; s0 + Z.of_nat i; c; e0]))) st_ss_fw
    (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + ST_FW)) mem1 (seg_rom SEGS)))
  /\ sh_ok SEGS st_Bx st_SH_fw (Eimg (Ereg regs1 (map w64 [SB; sc; ec; s0 + Z.of_nat i; c; e0]))) (mrestrict (w_H W) mem1).
Proof.
intros i c regs1 mem1 Hil Hc R2 R5 R6 R10 R11 R12 R13 R14 R15 R16 R17 VC VE PC VS RAC RAE RAS.
st_base.
assert (Hn : 0 < e0 - s0) by lia. destruct (st_bytes Hn) as (Hs4 & Hec & Hsb).
pose proof (st_ex regs1 [SB; sc; ec; s0 + Z.of_nat i; c; e0] 0 _ ltac:(unfold A_TEXT; lia) eq_refl) as E32.
pose proof (st_ex regs1 [SB; sc; ec; s0 + Z.of_nat i; c; e0] 1 _ ltac:(unfold A_TEXT; lia) eq_refl) as E33.
pose proof (st_ex regs1 [SB; sc; ec; s0 + Z.of_nat i; c; e0] 2 _ ltac:(unfold A_TEXT; lia) eq_refl) as E34.
pose proof (st_ex regs1 [SB; sc; ec; s0 + Z.of_nat i; c; e0] 3 _ ltac:(unfold A_TEXT; lia) eq_refl) as E35.
pose proof (st_ex regs1 [SB; sc; ec; s0 + Z.of_nat i; c; e0] 4 _ ltac:(unfold A_TEXT; lia) eq_refl) as E36.
pose proof (st_ex regs1 [SB; sc; ec; s0 + Z.of_nat i; c; e0] 5 _ ltac:(unfold A_TEXT; lia) eq_refl) as E37.
cbn [Nat.add] in E32, E33, E34, E35, E36, E37.
set (E := Eimg (Ereg regs1 (map w64 [SB; sc; ec; s0 + Z.of_nat i; c; e0]))) in *.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r) by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 16) by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (E32u : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (E33u : bv_unsigned (ew E 33) = sc) by (rewrite E33; apply unsigned_lit_small; lia).
assert (E34u : bv_unsigned (ew E 34) = ec) by (rewrite E34; apply unsigned_lit_small; lia).
assert (E35u : bv_unsigned (ew E 35) = s0 + Z.of_nat i) by (rewrite E35; apply unsigned_lit_small; lia).
assert (E36u : bv_unsigned (ew E 36) = c) by (rewrite E36; apply unsigned_lit_small; lia).
assert (E37u : bv_unsigned (ew E 37) = e0) by (rewrite E37; apply unsigned_lit_small; lia).
assert (Dsc : sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 33 0) (SLit 3)) (SOff 32 0)) = Z_to_bv 64 (SB + sc / 8))
  by (rewrite (denot_shx E 33 32 0 sc SB E33 E32) by (unfold SB; lia); rewrite Z.add_0_r; reflexivity).
assert (Dec : sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 34 0) (SLit 3)) (SOff 32 0)) = Z_to_bv 64 (SB + ec / 8))
  by (rewrite (denot_shx E 34 32 0 ec SB E34 E32) by (unfold SB; lia); rewrite Z.add_0_r; reflexivity).
split.
- rewrite restrict_mkst_fx. unfold st_ss_fw. apply pa_entry_st_ok_full.
  + st_regs_ok EE ltac:(rewrite ?E33u, ?E34u, ?E35u, ?E36u, ?E37u, ?Usp) ltac:(first [rewrite Dsc | rewrite Dec]).
  + vm_compute. reflexivity.
  + unfold st_cellR. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite E33u. split; [lia|]. split; [lia|]. split; [intros o Ho; apply (apresent_writable SEGS); apply PC; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ sc 0 8 (SOff 35 0) (s0 + Z.of_nat i));
        [cbn [sv_denot]; rewrite E35u, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. apply st_val_mem_of_sa_val. exact VC.
    * rewrite E34u. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ ec 0 8 (SOff 37 0) e0);
        [cbn [sv_denot]; rewrite E37u, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. apply st_val_mem_of_sa_val. exact VE.
    * rewrite E35u. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ (s0 + Z.of_nat i) 0 1 (SOff 36 0) c);
        [cbn [sv_denot]; rewrite E36u, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
      apply st_val_mem_of_sa_val. rewrite Z.add_0_r. exact (st_val1 _ _ _ VS Hc).
  + apply pairwise_disjoint_of_extents. unfold st_cellR, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E33u, E34u, E35u.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj, sa_disj in *. cbn [fst snd]. repeat split; lia.
  + split; [|split; exact I]. cbn [f_atoms atoms_ok].
    unfold afact_ok, st_spF, st_SBF, st_CELLF, st_PTRF, st_BYTEF. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32u, E33u, E34u, E35u, E36u, E37u. change (2 ^ 4) with 16. change (2 ^ 3) with 8.
    rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat split; try lia; first [rewrite Zminus_mod, Hal16; reflexivity | exact HSC8 | exact HEC8].
- unfold sh_ok, st_SH_fw. repeat apply Forall_cons; try apply Forall_nil.
  + apply (st_shent_ok E _ 33 sc 0 8 E32 E33u); try lia; [rewrite Z.add_0_r; exact RAC | intros y Hy; unfold SB; lia].
  + apply (st_shent_ok E _ 34 ec 0 8 E32 E34u); try lia; [rewrite Z.add_0_r; exact RAE | intros y Hy; unfold SB; lia].
  + apply (st_shent_ok E _ 35 (s0 + Z.of_nat i) 0 1 E32 E35u); try lia;
      [rewrite Z.add_0_r; exact RAS | intros y Hy; apply Hsb; lia].
Qed.

Lemma st_fw_step : forall i regs1 mem1 md1,
  (forall r m d, st_FWP (Datatypes.S i) r m d -> SRr SEGS W (mkCfg (mkst r (Z_to_bv 64 (BASE + ST_FW)) m (seg_rom SEGS)) d) st_Q) ->
  st_FWP i regs1 mem1 md1 ->
  SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + ST_FW)) mem1 (seg_rom SEGS)) md1) st_Q.
Proof.
intros i regs1 mem1 md1 NXT (HCUT & Hil & HBL & R5 & R6 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17).
pose proof HCUT as (HJ & HK & HFR & HCS & HCE & HPS & HPE & R2 & HCSR).
st_base.
assert (Hn : 0 < e0 - s0) by lia. destruct (st_bytes Hn) as (Hs4 & Hec & Hsb).
set (c := bv_unsigned (nth i l ZB0)).
assert (VS : rdW W mem1 (s0 + Z.of_nat i) = Some c) by exact (st_byte_cut _ _ _ _ _ HCUT i Hil).
pose proof (sa_aview_rng _ _ _ _ _ VS) as Hcr.
assert (RAS : range_addressable (rdW W mem1) SHADOW_OFF (s0 + Z.of_nat i) 1).
{ apply (st_ra_cut _ _ _ _ _ HCUT); [lia | lia |].
  destruct HSA as (_ & _ & _ & SA3 & _). apply (range_addressable_sub _ _ s0 (e0 - s0)); [exact SA3 | lia | lia]. }
assert (RAC : range_addressable (rdW W mem1) SHADOW_OFF sc 8)
  by (apply (st_ra_cut _ _ _ _ _ HCUT); [lia | lia | destruct HAS as (_ & _ & _ & X & _); exact X]).
assert (RAE : range_addressable (rdW W mem1) SHADOW_OFF ec 8)
  by (apply (st_ra_cut _ _ _ _ _ HCUT); [lia | lia | destruct HAE as (_ & _ & _ & X & _); exact X]).
assert (HZ : nth i (seg_spec.zs l) 0 = c) by (apply st_zs_nth; exact Hil).
clearbody c.
destruct (st_fw_seed i c regs1 mem1 Hil Hcr R2 R5 R6 R10 R11 R12 R13 R14 R15 R16 R17 HCS HCE HPS VS RAC RAE RAS) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs1 (map w64 [SB; sc; ec; s0 + Z.of_nat i; c; e0])))) by apply Eimg_env.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r ->
  ew (Eimg (Ereg regs1 (map w64 [SB; sc; ec; s0 + Z.of_nat i; c; e0]))) k = getr regs1 r)
  by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
pose proof (st_ex regs1 [SB; sc; ec; s0 + Z.of_nat i; c; e0] 0 _ ltac:(unfold A_TEXT; lia) eq_refl) as E32.
pose proof (st_ex regs1 [SB; sc; ec; s0 + Z.of_nat i; c; e0] 1 _ ltac:(unfold A_TEXT; lia) eq_refl) as E33.
pose proof (st_ex regs1 [SB; sc; ec; s0 + Z.of_nat i; c; e0] 2 _ ltac:(unfold A_TEXT; lia) eq_refl) as E34.
pose proof (st_ex regs1 [SB; sc; ec; s0 + Z.of_nat i; c; e0] 3 _ ltac:(unfold A_TEXT; lia) eq_refl) as E35.
pose proof (st_ex regs1 [SB; sc; ec; s0 + Z.of_nat i; c; e0] 4 _ ltac:(unfold A_TEXT; lia) eq_refl) as E36.
pose proof (st_ex regs1 [SB; sc; ec; s0 + Z.of_nat i; c; e0] 5 _ ltac:(unfold A_TEXT; lia) eq_refl) as E37.
cbn [Nat.add] in E32, E33, E34, E35, E36, E37.
remember (Eimg (Ereg regs1 (map w64 [SB; sc; ec; s0 + Z.of_nat i; c; e0]))) as E eqn:HE0. clear HE0.
assert (E33u : bv_unsigned (ew E 33) = sc) by (rewrite E33; apply unsigned_lit_small; lia).
assert (E34u : bv_unsigned (ew E 34) = ec) by (rewrite E34; apply unsigned_lit_small; lia).
assert (E35u : bv_unsigned (ew E 35) = s0 + Z.of_nat i) by (rewrite E35; apply unsigned_lit_small; lia).
assert (E37u : bv_unsigned (ew E 37) = e0) by (rewrite E37; apply unsigned_lit_small; lia).
(* 0x87a30 .. 0x87a48: beqz a6 (decided), the check of s[i], lbu, bltu 32,t2 *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ st_awrc ltac:(cbn [ew ewset Nat.eqb]; exact E33u). }
st_md.
pose proof (st_kz_refl st_cz (rdW W mem1)) as KA.
assert (PA : forall a, apresent (w_H W) mem1 a -> apresent (w_H W) mem1 a) by (intros a Ha; exact Ha).
st_track HFr HG KA PA st_cz ltac:(fun H => rewrite ?E33u, ?E34u in H). clear HF.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* 32 < c: not blank, 0x87a94 with strip_lead = i *)
  assert (Hgt : 32 < c).
  { rewrite branch_ltu_U, U_SLit in Hc. rewrite (U_atom _ 36 c) in Hc by (first [cbn [ew ewset Nat.eqb]; exact E36 | lia]).
    apply Z.ltb_lt in Hc. change (zcanon 32) with 32 in Hc. exact Hc. }
  clear Hc.
  assert (HLD : st_LEAD = i).
  { unfold st_LEAD, strip_lead. apply st_lead_exit; [rewrite st_zs_length; exact Hil | exact HBL | rewrite HZ; apply st_blank_gt; exact Hgt]. }
  paj_run_to_tok RUNTO HS HJ SHOK Bspan ST_BK.
  { st_awrc ltac:(cbn [ew ewset Nat.eqb]; exact E33u). }
  st_md. st_track HFr HG KA PA st_cz ltac:(fun H => rewrite ?E33u, ?E34u in H). clear HF.
  pmkst HS.
  apply st_bk. split.
  { rewrite HLD. eapply (st_cut_next _ _ _ _ _ _ _ _ _ _ HCUT HJ KA PA);
      [ eapply (st_reg_val _ _ _ _ 0%nat); [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; exact E33u
        | cbn [sv_denot ew ewset Nat.eqb]; rewrite E35u; f_equal; lia | lia]
      | eapply (st_reg_val _ _ _ _ 1%nat); [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; exact E34u
        | cbn [sv_denot ew ewset Nat.eqb]; rewrite E37u; f_equal; lia | lia]
      | .. ]; st_same HS EE. }
  split; [st_rv HS ltac:(rewrite ?E33u, ?E34u, ?E35u, ?E37u)|].
  split; [st_rv HS ltac:(rewrite ?E33u, ?E34u, ?E35u, ?E37u)|].
  split; [st_rv HS ltac:(rewrite ?E32, ?E33u, ?E34u, ?E35u, ?E37u; unfold w64; rewrite unsigned_lit_small by (unfold SB; lia))|].
  split; [st_rvx HS E33 E32 sc | st_rvx HS E34 E32 ec].
- assert (Hle : c <= 32).
  { rewrite branch_ltu_U, U_SLit in Hc. rewrite (U_atom _ 36 c) in Hc by (first [cbn [ew ewset Nat.eqb]; exact E36 | lia]).
    apply Z.ltb_ge in Hc. change (zcanon 32) with 32 in Hc. exact Hc. }
  clear Hc.
  (* 0x87a4c .. 0x87a54: (t0 >> t2) & 1, beqz *)
  paj_run_tok RUN HS HJ SHOK Bspan.
  { st_awrc ltac:(cbn [ew ewset Nat.eqb]; exact E33u). }
  st_md. st_track HFr HG KA PA st_cz ltac:(fun H => rewrite ?E33u, ?E34u in H). clear HF.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* the bit is clear: not blank, 0x87a94 with strip_lead = i *)
    assert (Hnb : SM.blank c = false).
    { rewrite branch_eq_U, U_SLit in Hc. rewrite (st_bit_U _ 36 c) in Hc by (first [cbn [ew ewset Nat.eqb]; exact E36 | lia]).
      destruct (SM.blank c); [vm_compute in Hc; discriminate Hc | reflexivity]. }
    clear Hc.
    assert (HLD : st_LEAD = i).
    { unfold st_LEAD, strip_lead. apply st_lead_exit; [rewrite st_zs_length; exact Hil | exact HBL | rewrite HZ; exact Hnb]. }
    paj_run_to_tok RUNTO HS HJ SHOK Bspan ST_BK.
    { st_awrc ltac:(cbn [ew ewset Nat.eqb]; exact E33u). }
    st_md. st_track HFr HG KA PA st_cz ltac:(fun H => rewrite ?E33u, ?E34u in H). clear HF.
    pmkst HS.
    apply st_bk. split.
    { rewrite HLD. eapply (st_cut_next _ _ _ _ _ _ _ _ _ _ HCUT HJ KA PA);
        [ eapply (st_reg_val _ _ _ _ 0%nat); [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; exact E33u
          | cbn [sv_denot ew ewset Nat.eqb]; rewrite E35u; f_equal; lia | lia]
        | eapply (st_reg_val _ _ _ _ 1%nat); [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; exact E34u
          | cbn [sv_denot ew ewset Nat.eqb]; rewrite E37u; f_equal; lia | lia]
        | .. ]; st_same HS EE. }
    split; [st_rv HS ltac:(rewrite ?E33u, ?E34u, ?E35u, ?E37u)|].
    split; [st_rv HS ltac:(rewrite ?E33u, ?E34u, ?E35u, ?E37u)|].
    split; [st_rv HS ltac:(rewrite ?E32, ?E33u, ?E34u, ?E35u, ?E37u; unfold w64; rewrite unsigned_lit_small by (unfold SB; lia))|].
    split; [st_rvx HS E33 E32 sc | st_rvx HS E34 E32 ec].
  + (* blank: 0x87a58 .. 0x87a7c, bgeu t1,a2 (decided), the store of s + 1, t2 := *ec, bltu a6,t2 *)
    assert (Hb : SM.blank c = true).
    { rewrite branch_eq_U, U_SLit in Hc. rewrite (st_bit_U _ 36 c) in Hc by (first [cbn [ew ewset Nat.eqb]; exact E36 | lia]).
      destruct (SM.blank c); [reflexivity | vm_compute in Hc; discriminate Hc]. }
    clear Hc.
    paj_run_tok RUN HS HJ SHOK Bspan.
    { st_awrc ltac:(cbn [ew ewset Nat.eqb]; exact E33u). }
    st_md. st_track HFr HG KA PA st_cz ltac:(fun H => rewrite ?E33u, ?E34u in H). clear HF.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * (* s + 1 < e0: the next byte *)
      assert (Hlt : s0 + Z.of_nat i + 1 < e0).
      { rewrite branch_ltu_U in Hc.
        rewrite (U_atom_off _ 35 (s0 + Z.of_nat i) 1) in Hc by (first [cbn [ew ewset Nat.eqb]; exact E35 | lia]).
        rewrite (U_atom _ 37 e0) in Hc by (first [cbn [ew ewset Nat.eqb]; exact E37 | lia]).
        apply Z.ltb_lt in Hc. exact Hc. }
      clear Hc.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan ST_FW.
      { st_awrc ltac:(cbn [ew ewset Nat.eqb]; exact E33u). }
      st_md. st_track HFr HG KA PA st_cz ltac:(fun H => rewrite ?E33u, ?E34u in H). clear HF.
      pmkst HS.
      apply NXT. split.
      { eapply (st_cut_next _ _ _ _ _ _ _ _ _ _ HCUT HJ KA PA);
          [ eapply (st_reg_val _ _ _ _ 0%nat); [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; exact E33u
            | cbn [sv_denot ew ewset Nat.eqb]; rewrite E35u; f_equal; lia | lia]
          | eapply (st_reg_val _ _ _ _ 1%nat); [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; exact E34u
            | cbn [sv_denot ew ewset Nat.eqb]; rewrite E37u; f_equal; lia | lia]
          | .. ]; st_same HS EE. }
      split; [lia|].
      split.
      { intros k Hk. destruct (Nat.eq_dec k i) as [->|Hne]; [rewrite HZ; exact Hb | apply HBL; lia]. }
      split; [st_rv HS ltac:(rewrite ?E33u, ?E34u, ?E35u, ?E37u)|].
      split; [st_rv HS ltac:(rewrite ?E33u, ?E34u, ?E35u, ?E37u)|].
      split; [st_rv HS ltac:(rewrite ?E33u, ?E34u, ?E35u, ?E37u)|].
      split; [st_rv HS ltac:(rewrite ?E33u, ?E34u, ?E35u, ?E37u)|].
      split; [st_rv HS ltac:(rewrite ?E33u, ?E34u, ?E35u, ?E37u)|].
      split; [st_rv HS ltac:(rewrite ?E32, ?E33u, ?E34u, ?E35u, ?E37u; unfold w64; rewrite unsigned_lit_small by (unfold SB; lia))|].
      split; [st_rvx HS E33 E32 sc|].
      split; [st_rvx HS E34 E32 ec|].
      split; st_rv HS ltac:(rewrite ?E33u, ?E34u, ?E35u, ?E37u).
    * (* s + 1 >= e0: every byte blank, 0x87a80 j 0x87a94 with strip_lead = length l *)
      assert (Hge : e0 <= s0 + Z.of_nat i + 1).
      { rewrite branch_ltu_U in Hc.
        rewrite (U_atom_off _ 35 (s0 + Z.of_nat i) 1) in Hc by (first [cbn [ew ewset Nat.eqb]; exact E35 | lia]).
        rewrite (U_atom _ 37 e0) in Hc by (first [cbn [ew ewset Nat.eqb]; exact E37 | lia]).
        apply Z.ltb_ge in Hc. exact Hc. }
      clear Hc.
      assert (HLD : st_LEAD = Datatypes.S i).
      { unfold st_LEAD, strip_lead. rewrite st_lead_all; [rewrite st_zs_length; lia|].
        intros k Hk. rewrite st_zs_length in Hk.
        destruct (Nat.eq_dec k i) as [->|Hne]; [rewrite HZ; exact Hb | apply HBL; lia]. }
      paj_run_to_tok RUNTO HS HJ SHOK Bspan ST_BK.
      { st_awrc ltac:(cbn [ew ewset Nat.eqb]; exact E33u). }
      st_md. st_track HFr HG KA PA st_cz ltac:(fun H => rewrite ?E33u, ?E34u in H). clear HF.
      pmkst HS.
      apply st_bk. split.
      { rewrite HLD. eapply (st_cut_next _ _ _ _ _ _ _ _ _ _ HCUT HJ KA PA);
          [ eapply (st_reg_val _ _ _ _ 0%nat); [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; exact E33u
            | cbn [sv_denot ew ewset Nat.eqb]; rewrite E35u; f_equal; lia | lia]
          | eapply (st_reg_val _ _ _ _ 1%nat); [exact HS | reflexivity | cbn [ew ewset Nat.eqb]; exact E34u
            | cbn [sv_denot ew ewset Nat.eqb]; rewrite E37u; f_equal; lia | lia]
          | .. ]; st_same HS EE. }
      split; [st_rv HS ltac:(rewrite ?E33u, ?E34u, ?E35u, ?E37u)|].
      split; [st_rv HS ltac:(rewrite ?E33u, ?E34u, ?E35u, ?E37u)|].
      split; [st_rv HS ltac:(rewrite ?E32, ?E33u, ?E34u, ?E35u, ?E37u; unfold w64; rewrite unsigned_lit_small by (unfold SB; lia))|].
      split; [st_rvx HS E33 E32 sc | st_rvx HS E34 E32 ec].
Qed.
Lemma st_fw_all : forall dd i, (i + dd = length l)%nat -> forall r m d, st_FWP i r m d ->
  SRr SEGS W (mkCfg (mkst r (Z_to_bv 64 (BASE + ST_FW)) m (seg_rom SEGS)) d) st_Q.
Proof.
induction dd as [|dd IH]; intros i Hd r m d HLP.
- exfalso. destruct HLP as (_ & Hil & _). lia.
- apply (st_fw_step i); [|exact HLP].
  intros r' m' d' HLP'. apply (IH (Datatypes.S i)); [lia | exact HLP'].
Qed.

(* ---------- the entry: 0x879cc .. 0x87a2c ---------- *)
Lemma st_entry_seed :
  st_ok_pi SEGS VAL (Eimg (Ereg regs (map w64 [SB; s0; e0]))) st_ss_entry
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_strip)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS st_Bx st_SH_entry (Eimg (Ereg regs (map w64 [SB; s0; e0]))) (mrestrict (w_H W) mem).
Proof.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
st_base. assert (HST : ST_STK = 16) by reflexivity.
pose proof (st_ex regs [SB; s0; e0] 0 _ ltac:(unfold A_TEXT; lia) eq_refl) as E32.
pose proof (st_ex regs [SB; s0; e0] 1 _ ltac:(unfold A_TEXT; lia) eq_refl) as E33.
pose proof (st_ex regs [SB; s0; e0] 2 _ ltac:(unfold A_TEXT; lia) eq_refl) as E34.
cbn [Nat.add] in E32, E33, E34.
set (E := Eimg (Ereg regs (map w64 [SB; s0; e0]))) in *.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Eimg_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (U10 : bv_unsigned (ew E 10) = sc)
  by (subst E; rewrite (ew_Eimg_Ereg_nat regs _ 10 10%bv eq_refl), H10; unfold w64; apply unsigned_lit_small; lia).
assert (U11 : bv_unsigned (ew E 11) = ec)
  by (subst E; rewrite (ew_Eimg_Ereg_nat regs _ 11 11%bv eq_refl), H11; unfold w64; apply unsigned_lit_small; lia).
assert (E32u : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_val_range (A_OBJ 0)) as R0. pose proof (pa_val_range (A_OBJ 12)) as R12.
assert (U241 : bv_unsigned (ew E (A_OBJ 0)) = VAL (A_OBJ 0)) by (rewrite E241; apply unsigned_lit_small; lia).
assert (U253 : bv_unsigned (ew E (A_OBJ 12)) = VAL (A_OBJ 12)) by (rewrite E253; apply unsigned_lit_small; lia).
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR. pose proof (pal_got_cell B TL) as HgcD.
unfold kImgEnd in HcellR, HgotR.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
split.
- rewrite restrict_mkst_fx. unfold st_ss_entry. apply pa_entry_st_ok_full.
  + subst E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold stack_region, got_regionP, bcell_regionP, st_cellR.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite HST. lia.
    * rewrite U241. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
        [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
    * rewrite U253. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r; rewrite unsigned_lit_small by (unfold SB; lia); reflexivity
        | unfold SB; cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
    * rewrite U10. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ sc 0 8 (SOff 33 0) s0);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r; rewrite unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. apply st_val_mem_of_sa_val. exact HVS.
    * rewrite U11. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ ec 0 8 (SOff 34 0) e0);
        [cbn [sv_denot]; rewrite E34, Z.add_0_r; rewrite unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. apply st_val_mem_of_sa_val. exact HVE.
  + apply pairwise_disjoint_of_extents. unfold stack_region, got_regionP, bcell_regionP, st_cellR, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, U241, U253, U10, U11.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj, sa_disj in *. cbn [fst snd]. repeat split; lia.
  + split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok, st_spF, st_CELLF, st_SBF. cbn [af_lo af_hi af_al2].
    rewrite Usp, U10, U11, E32u. change (2 ^ 4) with 16. change (2 ^ 3) with 8.
    rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat split; try lia; first [exact Hal16 | exact HSC8 | exact HEC8].
- unfold sh_ok, st_SH_entry. repeat apply Forall_cons; try apply Forall_nil.
  + apply (st_shent_ok E _ 10 sc 0 8 E32 U10); try lia;
      [rewrite Z.add_0_r; destruct HAS as (_ & _ & _ & X & _); exact X | intros y Hy; unfold SB; lia].
  + apply (st_shent_ok E _ 11 ec 0 8 E32 U11); try lia;
      [rewrite Z.add_0_r; destruct HAE as (_ & _ & _ & X & _); exact X | intros y Hy; unfold SB; lia].
Qed.
Lemma st_entry : SRr SEGS W (cfg_at SEGS (BASE + AF_strip) regs mem md) st_Q.
Proof.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
st_base. pose proof st_lead_le as HLL.
destruct st_entry_seed as [HS SHOK].
pose proof (ajournal_init SEGS B ST_STK [(sc, sc + 8); (ec, ec + 8)] ly S W regs mem md ch HPRE) as HJ.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs (map w64 [SB; s0; e0])))) by apply Eimg_env.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (Eimg (Ereg regs (map w64 [SB; s0; e0]))) k = getr regs r)
  by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
pose proof (st_ex regs [SB; s0; e0] 0 _ ltac:(unfold A_TEXT; lia) eq_refl) as E32.
pose proof (st_ex regs [SB; s0; e0] 1 _ ltac:(unfold A_TEXT; lia) eq_refl) as E33.
pose proof (st_ex regs [SB; s0; e0] 2 _ ltac:(unfold A_TEXT; lia) eq_refl) as E34.
cbn [Nat.add] in E32, E33, E34.
assert (E10 : ew (Eimg (Ereg regs (map w64 [SB; s0; e0]))) 10 = Z_to_bv 64 sc) by (rewrite (EE 10%nat 10%bv eq_refl), H10; reflexivity).
assert (E11 : ew (Eimg (Ereg regs (map w64 [SB; s0; e0]))) 11 = Z_to_bv 64 ec) by (rewrite (EE 11%nat 11%bv eq_refl), H11; reflexivity).
assert (E1 : ew (Eimg (Ereg regs (map w64 [SB; s0; e0]))) 1 = getr regs 1) by (rewrite (EE 1%nat 1%bv eq_refl); reflexivity).
assert (Usp : bv_unsigned (ew (Eimg (Ereg regs (map w64 [SB; s0; e0]))) 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
remember (Eimg (Ereg regs (map w64 [SB; s0; e0]))) as E eqn:HE0. clear HE0.
assert (E10u : bv_unsigned (ew E 10) = sc) by (rewrite E10; apply unsigned_lit_small; lia).
assert (E11u : bv_unsigned (ew E 11) = ec) by (rewrite E11; apply unsigned_lit_small; lia).
assert (E33u : bv_unsigned (ew E 33) = s0) by (rewrite E33; apply unsigned_lit_small; lia).
assert (E34u : bv_unsigned (ew E 34) = e0) by (rewrite E34; apply unsigned_lit_small; lia).
unfold cfg_at. change (w64 (BASE + AF_strip)) with (Z_to_bv 64 (BASE + AF_strip)).
(* 0x879cc .. 0x879dc: the frame, a2 := (sc | ec) & 7, bnez a2 *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac; cbn [ew ewset Nat.eqb]; exact Usp. }
st_md.
pose proof (st_kz_refl st_wz (rdW W mem)) as KA.
assert (PA : forall a, apresent (w_H W) mem a -> apresent (w_H W) mem a) by (intros a Ha; exact Ha).
st_track HFr HG KA PA st_wz ltac:(fun H => rewrite ?Usp in H). clear HF.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* the trap edge: (sc | ec) & 7 <> 0 is false *)
  exfalso. rewrite branch_ne_U, U_SLit in Hc.
  rewrite (st_align_U _ sc ec) in Hc by (first [cbn [ew ewset Nat.eqb]; exact E10 | cbn [ew ewset Nat.eqb]; exact E11 | lia | exact HSC8 | exact HEC8]).
  vm_compute in Hc. discriminate Hc.
- clear Hc.
  (* 0x879e0 .. 0x87a14: the shadow base, the checks of sc and ec, s0 := *sc, e0 := *ec, bgeu *)
  paj_run_tok RUN HS HJ SHOK Bspan.
  { awr_ok_tac; cbn [ew ewset Nat.eqb]; exact Usp. }
  st_md. st_track HFr HG KA PA st_wz ltac:(fun H => rewrite ?Usp in H). clear HF.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* s0 >= e0: no byte, 0x87a94 with strip_lead = 0 *)
    assert (Hge : e0 <= s0).
    { rewrite branch_geu_U in Hc.
      rewrite (U_atom _ 33 s0) in Hc by (first [cbn [ew ewset Nat.eqb]; exact E33 | lia]).
      rewrite (U_atom _ 34 e0) in Hc by (first [cbn [ew ewset Nat.eqb]; exact E34 | lia]).
      apply negb_true_iff, Z.ltb_ge in Hc. exact Hc. }
    clear Hc.
    assert (Hl0 : l = []) by (apply length_zero_iff_nil; lia).
    assert (HLD : st_LEAD = 0%nat) by (unfold st_LEAD, strip_lead; rewrite Hl0; reflexivity).
    paj_run_to_tok RUNTO HS HJ SHOK Bspan ST_BK.
    { awr_ok_tac; cbn [ew ewset Nat.eqb]; exact Usp. }
    st_md. st_track HFr HG KA PA st_wz ltac:(fun H => rewrite ?Usp in H). clear HF.
    pmkst HS.
    apply st_bk. split.
    { rewrite HLD. change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
      eapply (st_cut_entry _ _ _ HJ KA PA).
      - replace (spZ regs - 8) with (spZ regs + -8) by lia.
        eapply (st_reg_val2 _ _ _ _ 0%nat); [exact HS | reflexivity | left; reflexivity | cbn [ew ewset Nat.eqb]; exact Usp
          | cbn [sv_denot ew ewset Nat.eqb]; rewrite E1, Z.add_0_r; reflexivity
          | pose proof (bv_unsigned_in_range 64 (getr regs 1)) as HRr; change (bv_modulus 64) with (2 ^ 64) in HRr; exact HRr].
      - st_rv HS ltac:(rewrite ?Usp).
      - st_same HS EE. - st_same HS EE. - st_same HS EE. - st_same HS EE. - st_same HS EE.
      - st_same HS EE. - st_same HS EE. - st_same HS EE. - st_same HS EE. - st_same HS EE.
      - st_same HS EE. - st_same HS EE. - st_same HS EE. - st_same HS EE. }
    split; [st_rv HS ltac:(rewrite ?E10u, ?E11u)|].
    split; [st_rv HS ltac:(rewrite ?E10u, ?E11u)|].
    split; [st_rv HS ltac:(rewrite ?E32; unfold w64; rewrite unsigned_lit_small by (unfold SB; lia))|].
    split; [st_rvx HS E10 E32 sc | st_rvx HS E11 E32 ec].
  + (* s0 < e0: 0x87a18 .. 0x87a2c, the constants, then the forward loop at byte 0 *)
    assert (Hlt : s0 < e0).
    { rewrite branch_geu_U in Hc.
      rewrite (U_atom _ 33 s0) in Hc by (first [cbn [ew ewset Nat.eqb]; exact E33 | lia]).
      rewrite (U_atom _ 34 e0) in Hc by (first [cbn [ew ewset Nat.eqb]; exact E34 | lia]).
      apply negb_false_iff, Z.ltb_lt in Hc. exact Hc. }
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan ST_FW.
    { awr_ok_tac; cbn [ew ewset Nat.eqb]; exact Usp. }
    st_md. st_track HFr HG KA PA st_wz ltac:(fun H => rewrite ?Usp in H). clear HF.
    pmkst HS.
    apply (st_fw_all (length l) 0); [lia|].
    split.
    { change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
      eapply (st_cut_entry _ _ _ HJ KA PA).
      - replace (spZ regs - 8) with (spZ regs + -8) by lia.
        eapply (st_reg_val2 _ _ _ _ 0%nat); [exact HS | reflexivity | left; reflexivity | cbn [ew ewset Nat.eqb]; exact Usp
          | cbn [sv_denot ew ewset Nat.eqb]; rewrite E1, Z.add_0_r; reflexivity
          | pose proof (bv_unsigned_in_range 64 (getr regs 1)) as HRr; change (bv_modulus 64) with (2 ^ 64) in HRr; exact HRr].
      - st_rv HS ltac:(rewrite ?Usp).
      - st_same HS EE. - st_same HS EE. - st_same HS EE. - st_same HS EE. - st_same HS EE.
      - st_same HS EE. - st_same HS EE. - st_same HS EE. - st_same HS EE. - st_same HS EE.
      - st_same HS EE. - st_same HS EE. - st_same HS EE. - st_same HS EE. }
    split; [lia|].
    split; [intros k Hk; lia|].
    split; [st_rv HS ltac:(rewrite ?E10u, ?E11u, ?E33u, ?E34u)|].
    split; [st_rv HS ltac:(rewrite ?E10u, ?E11u, ?E33u, ?E34u)|].
    split; [st_rv HS ltac:(rewrite ?E10u, ?E11u, ?E33u, ?E34u)|].
    split; [st_rv HS ltac:(rewrite ?E10u, ?E11u, ?E33u, ?E34u)|].
    split; [st_rv HS ltac:(rewrite ?E10u, ?E11u, ?E33u, ?E34u)|].
    split; [st_rv HS ltac:(rewrite ?E32; unfold w64; rewrite unsigned_lit_small by (unfold SB; lia))|].
    split; [st_rvx HS E10 E32 sc|].
    split; [st_rvx HS E11 E32 ec|].
    split; st_rv HS ltac:(rewrite ?E10u, ?E11u, ?E33u, ?E34u).
Qed.

End w.

(* ---------- the contract ---------- *)
Theorem strip_walkB : strip_contract SEGS B (BASE + AF_strip) SegInstB.STK_strip.
Proof.
unfold strip_contract.
intros ly S W regs mem md ch sc ec s0 e0 l HPRE H10 Hsc64 H11 Hec64 HSP HEV.
destruct HSP as ((HSC8 & HEC8 & HDCE & HVS & HAS & HVE & HAE & (HS0 & HSE) & HSB & HLN & HSA & HDS & HDE) & HSLS & HSLE & HSL).
eapply (st_entry ly S W regs mem md ch sc ec s0 e0 l); eassumption.
Qed.
End e.
End d.
End b.

About strip_walkB.
Print Assumptions strip_walkB.
