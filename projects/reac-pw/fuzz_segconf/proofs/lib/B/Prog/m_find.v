(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of rec_calls_equal on the ASan build of plugin-hostd/fuzz_command
   (0x89968, 135 instructions), in the shape of cgif_file_fuzzer's walks (lib/A/AChc.v, ACh1.v..ACh8.v): the
   symbolic executor over the position-abstract listing (CmdPaLib.v), the inline checks removed by the shadow tokens
   (PaShadow.v), and the strcmp wrapper's call stepped through by its contract (PaArt.v aj_art_at). The two loops
   are cut at their heads (0x899dc, 0x89a6c) and at the outer latch (0x89ab0); each piece is re-seeded from the
   concrete state there and the loops are proved by induction. Every call is strcmp, which writes only its stack
   window, so the memory below the frame stays the entry's (kept_out) and the read-only bytes strcmp reads
   (rt_rom_view) follow from the statement's arodata_okP. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/rec_calls_equal.v, with its module paths, module names and numbers changed; 890 of its 1010 lines of code are new or changed and 1371 lines of the source are left out. *)
(* The ASan+UBSan walk of m_find on image B of reac-pw/fuzz_segconf (fuzz_segconf.asan-ubsan, pin sha256
   c3796c0b38f3; entry BASE + AF_m_find = 0x874f4, 63 instructions, 64-byte frame, no side-stack frame, one
   instrumented check, three UBSan trap edges), against m_find_contract (lib/B/Prog/m_find_c.v) at
   A_m_find := BASE + AF_m_find, STK_m_find := SegInstB.STK_m_find (64 + 2 * ESTACK: the frame and the bcmp
   wrapper's window, the deeper of the two callees), RLO / RHI := SegInstB.RLO_A / RHI_A.
   ADAPTATION of the image-A m_file-family lane's image-A walk lib/A/Prog/m_findA.v (commit 4a8c7695a78a) at image
   B's numbers, with the UBSan trap edges added; the trap facts are the segconf porter's UBSan walk lib/U/Prog/m_find.v.

   Code (the neutral listing of m_find in image B; listing offsets from BASE, AF_m_find = 0x2734):
     0x874f4 .. 0x87518  the frame: ra s0 s1 s2 s3 s4 s5 s6 at sp0-8 .. sp0-64; s0 := c
     0x8751c .. 0x87520  andi a0,c,3; bnez a0 -> unimp 0x875dc.  TRAP 1 (UBSan: c's alignment for `c->n`): the
                         branch is decided false by the executor's fact arithmetic from m_find_pre's
                         c mod 16 = 0 (atom 10 of the entry state carries af_al2 = 4).
     0x87524 .. 0x8754c  s1 := n, s2 := name; the shadow base through the GOT word (A_OBJ 0, 0xa3210) and its cell
                         (A_OBJ 12, 0xac7b8 = __asan_shadow_memory_dynamic_address); a0 := c + 0x2000; THE
                         INSTRUMENTED CHECK of the 4-byte load of c->n (srli, add, lb, bnez to the slow block
                         0x875e0). The check vanishes: c's whole block is a shadow entry (the contract's
                         sa_addr of c), so the loaded shadow byte is 0 and the slow block and the error path
                         (a call of errpath_load4 at 0x875ec) are on no path.
     0x87550 lw a0 = c->n (= length (mc_seg mc), mconf_encp's u32 field); 0x87554 blez a0 -> NONE
     0x87558 .. 0x8756c  s3 := 0, s4 := ~c, s5 := (c->n > 0 ? c->n : 0) = c->n, s6 := 32
     LH   0x87570 beqz s6 -> unimp.  TRAP 2 (UBSan: i = 32): decided false from the loop state's fact
                         1 <= 32 - k <= 32 (k < c->n <= 32, mconf_encp).
          0x87574 bltu s4,s3 -> unimp.  TRAP 3 (UBSan: c + 256 i wraps): decided false from the loop state's
                         facts 0 <= 256 k <= 7936 and 2 ^ 64 - 2 ^ 47 <= ~c (c's block of 9236 bytes ends below
                         kHighMemEnd, so c < 2 ^ 47).
          0x87578 a0 := s0; 0x8757c jal strlen; 0x87580 bne a0,s1 -> NX
          0x87584 .. 0x87590 a0 := s0, a1 := s2, a2 := s1; jal bcmp; 0x87594 beqz a0 -> EPI
     NX   0x87598 s5 -= 1; s0 += 256; s3 += 256; s6 -= 1; 0x875a8 bnez s5 -> LH
     NONE 0x875ac s0 := 0
     EPI  0x875b0 a0 := s0; ra s0 .. s6 restored; sp += 64; ret
   The loop state at LH (mf_LH k): s0 = c + 256 k (&c->seg[k]), s1 = n, s2 = name, s3 = 256 k, s4 = ~c,
   s5 = c->n - k, s6 = 32 - k, and SegModel.m_find mc name = m_find_go (skipn k (mc_seg mc)) name k. strlen reads
   seg[k]'s name, its NUL and the rest of its 16-byte name field (c is 16-aligned, so the word tail after the NUL
   lies in the field); bcmp reads the name's n bytes and the n bytes at name.
   Section hypotheses: the two wrapper contracts (the image-A wrapper lane's interface rows 16 and 19, at image B's trampolines
   0x43a98 and 0x43ac4) and TL : PALib B (the shadow base's GOT word and cell, and the errno placement
   aj_art_at asks). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0p YC5d YG0q YG0d_tail.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_find_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ================================ the listing's cut points ================================ *)
(* listing offsets from BASE (SegList.v: AF_m_find = 0x2734, entry 0x874f4, seg_text 0x84dc0) *)
Definition MF_LH : Z := 0x27b0.   (* 0x87570, the loop head: the two trap edges, then the strlen call *)
Definition MF_NX : Z := 0x27d8.   (* 0x87598, the next entry: s5 -= 1, s0 += 256, s3 += 256, s6 -= 1 *)
Definition MF_EPI : Z := 0x27f0.  (* 0x875b0, the epilogue, s0 the result *)
(* the shadow base (SHADOW_OFF) and the span of the shadow band, as the token executor takes them *)
Definition MF_SB : Z := 0x7fff8000.
Definition MFx : sv := SOff 32 0.
Definition MFspan : Z * Z := (MF_SB, MF_SB + 2 ^ 44 - 1).
(* the highest c its block allows (sa_addr's amem_range: the block ends below kHighMemEnd) *)
Definition MF_CHI : Z := 2 ^ 47 - 1 - seg_spec.SEG_M_SIZE.
(* the frame: ra s0 s1 s2 s3 s4 s5 s6 saved at sp0 - 8 .. sp0 - 64 *)
Definition mf_saved : list Z := [1; 8; 9; 18; 19; 20; 21; 22].
(* the callee-saved registers m_find never writes: gp, tp, s7 .. s11 *)
Definition mf_kregs : list (bv 5) := [3; 4; 23; 24; 25; 26; 27]%bv.
Definition mf_spF : afact := mkAF (2 ^ 46) (2 ^ 47) 4.

(* the entry state: the 64-byte frame below sp writable, c->n (atom 33) at c + 0x2000, the shadow base's GOT word
   and cell (atom 32) *)
Definition mf_rN : YP09.region :=
YP09.mkRegion (Some 10%nat) seg_spec.MC_N (seg_spec.MC_N + 4) 0 0 [YP09.mkChunk seg_spec.MC_N (CVal 4 (SOff 33 0))].
Definition mf_regions : smem := [stack_region 64; mf_rN; got_regionP; bcell_regionP 32].
Definition mf_facts : facts :=
mkFacts [(2%nat, mf_spF); (10%nat, mkAF 0 MF_CHI 4); (32%nat, mkAF MF_SB MF_SB 0); (33%nat, mkAF 0 32 0)] [] [].
Definition ss_mf0 : sstate := mkSS AF_m_find sr_atoms mf_regions None mf_facts.
Definition mf_SH : list shent := [mkSHE 10 0 seg_spec.SEG_M_SIZE].
Definition mf_extra (N : Z) : list word := map (Z_to_bv 64) [MF_SB; N].
(* a loop point: the registers as their own atoms, no memory, and the three facts that refute the trap edges
   (s3 = 256 k the cursor, s4 = ~c, s6 = 32 - k the entry count left) *)
Definition mf_iF : afact := mkAF 0 7936 8.
Definition mf_notF : afact := mkAF (2 ^ 64 - 2 ^ 47) (2 ^ 64 - 1) 0.
Definition mf_cntF : afact := mkAF 1 32 0.
Definition mf_ss_at (pc : Z) : sstate := mkSS pc sr_atoms [] None
  (mkFacts [(2%nat, mf_spF); (19%nat, mf_iF); (20%nat, mf_notF); (22%nat, mf_cntF)] [] []).
(* the epilogue: the eight saved words as atoms 32 .. 39 *)
Definition mf_estack : YP09.region := YP09.mkRegion (Some 2%nat) 0 64 0 0
  (map (fun j => YP09.mkChunk (56 - 8 * Z.of_nat j) (CVal 8 (SOff (32 + j) 0))) (seq 0 8)).
Definition mf_ss_epi : sstate := mkSS MF_EPI sr_atoms [mf_estack] None (mkFacts [(2%nat, mf_spF)] [] []).

(* ================================ lists, bytes, words ================================ *)
Lemma mf_nth_firstn : forall {A} (l : list A) n k d, (k < n)%nat -> nth k (firstn n l) d = nth k l d.
Proof.
intros A l n. revert l. induction n as [|n IH]; intros l k d Hk; [lia|].
destruct l as [|x l]; [destruct k; reflexivity|]. destruct k as [|k]; [reflexivity|].
cbn [firstn nth]. apply IH. lia.
Qed.
Lemma mf_nth_skipn : forall {A} (l : list A) o k d, nth k (skipn o l) d = nth (o + k) l d.
Proof.
intros A l o. revert l. induction o as [|o IH]; intros l k d; [reflexivity|].
destruct l as [|x l]; [destruct k; reflexivity|]. cbn [skipn]. rewrite IH. reflexivity.
Qed.
Lemma mf_nth_zs : forall (l : list byte) i, nth i (seg_spec.zs l) 0 = bv_unsigned (nth i l ZB0).
Proof. intros l i. unfold seg_spec.zs. rewrite <- (map_nth bv_unsigned l ZB0 i). reflexivity. Qed.
Lemma mf_zs_app0 : forall sb, seg_spec.zs sb ++ [0] = seg_spec.zs (sb ++ [ZB0]).
Proof. intros sb. unfold seg_spec.zs. rewrite map_app. reflexivity. Qed.
Lemma mf_mod16 : forall c k, c mod 16 = 0 -> (c + 256 * Z.of_nat k) mod 16 = 0.
Proof. intros c k H. Z.div_mod_to_equations. lia. Qed.
(* the word tail after a NUL inside a 16-aligned 16-byte field stays in the field *)
Lemma mf_tail_bound : forall x len, x mod 16 = 0 -> 0 <= len < 16 -> x + len - (x + len) mod 8 + 8 <= x + 16.
Proof. intros x len Hx Hl. Z.div_mod_to_equations. lia. Qed.
Lemma mf_swrap_small : forall z, 0 <= z < 2 ^ 63 -> bv_swrap 64 z = z.
Proof.
intros z Hz. unfold bv_swrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). change (2 ^ 64 / 2) with (2 ^ 63).
rewrite bv_wrap_small; [lia|]. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.
(* blez on a word of small non-negative value *)
Lemma mf_bge0 : forall E e v, U E e = v -> 0 <= v < 2 ^ 63 ->
branch_taken BC_GE (sv_denot E (SLit 0)) (sv_denot E e) = (v <=? 0).
Proof.
intros E e v He Hv. rewrite (denot_lit_U E e), He. cbn [branch_taken sv_denot].
unfold bv_lts. rewrite !signed_lit. rewrite !zcanon_small by lia. rewrite !mf_swrap_small by lia.
destruct (Z.ltb_spec 0 v); destruct (Z.leb_spec v 0); try reflexivity; lia.
Qed.
(* lw of a 4-byte word below 2^31 *)
Lemma mf_U_sext : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 -> U E (SExt true 32 (SOff n 0)) = v.
Proof.
intros E n v H Hv. rewrite U_SExt, (U_atom E n v H) by lia. change (2 ^ Z.of_N 32) with (2 ^ 32).
rewrite (Z.mod_small v) by lia. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32).
change (2 ^ 32 / 2) with (2 ^ 31). rewrite (Z.mod_small (v + 2 ^ 31)) by lia. replace (v + 2 ^ 31 - 2 ^ 31) with v by lia.
apply zcanon_id. unfold M64. lia.
Qed.
(* s4 := ~c (`not s4,s0`: xor with -1), as the step leaves it in the register *)
Lemma mf_alu_not : forall (x : word) v, bv_unsigned x = v -> 0 <= v < 2 ^ 64 ->
alu64 ALU_XOR x (Z_to_bv 64 (-1)) = Z_to_bv 64 (2 ^ 64 - 1 - v).
Proof.
intros x v Hu Hv. apply bv_eq. rewrite alu64_unsigned.
rewrite (unsigned_lit_small (2 ^ 64 - 1 - v)) by lia. cbn [zalu_raw].
rewrite Hu. replace (bv_unsigned (Z_to_bv 64 (-1))) with (2 ^ 64 - 1) by reflexivity.
rewrite lxor_allones by lia. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia.
Qed.
(* s5 := (v > 0 ? v : 0) (`sgtz a1,a0; neg a1,a1; and s5,a1,a0`) *)
Lemma mf_alu_sel : forall (x : word) v, bv_unsigned x = v -> 0 < v < 2 ^ 63 ->
alu64 ALU_AND (alu64 ALU_SUB (Z_to_bv 64 0) (alu64 ALU_SLT (Z_to_bv 64 0) x)) x = Z_to_bv 64 v.
Proof.
intros x v Hu Hv.
assert (H1 : alu64 ALU_SLT (Z_to_bv 64 0) x = Z_to_bv 64 1).
{ apply bv_eq. rewrite alu64_unsigned. rewrite (unsigned_lit_small 1) by lia. cbn [zalu_raw].
  rewrite Hu. replace (bv_unsigned (Z_to_bv 64 0)) with 0 by reflexivity.
  rewrite (mf_swrap_small 0) by lia. rewrite (mf_swrap_small v) by lia.
  replace (0 <? v) with true by (symmetry; apply Z.ltb_lt; lia).
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
assert (H2 : alu64 ALU_SUB (Z_to_bv 64 0) (Z_to_bv 64 1) = Z_to_bv 64 (2 ^ 64 - 1)).
{ apply bv_eq. rewrite alu64_unsigned. rewrite (unsigned_lit_small (2 ^ 64 - 1)) by lia. cbn [zalu_raw].
  replace (bv_unsigned (Z_to_bv 64 0)) with 0 by reflexivity.
  replace (bv_unsigned (Z_to_bv 64 1)) with 1 by reflexivity.
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). reflexivity. }
rewrite H1, H2. apply bv_eq. rewrite alu64_unsigned.
rewrite (unsigned_lit_small v) by lia. cbn [zalu_raw].
rewrite Hu. replace (bv_unsigned (Z_to_bv 64 (2 ^ 64 - 1))) with (2 ^ 64 - 1)
  by (symmetry; apply unsigned_lit_small; lia).
change (2 ^ 64 - 1) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
rewrite (Z.mod_small v) by lia. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia.
Qed.

(* the 4-byte u32 field at offset off of a byte block, read through the reader *)
Lemma mf_fld : forall (rd : reader) a bs off v,
sa_bytes rd a bs -> 0 <= off -> off + 4 <= Z.of_nat (length bs) ->
seg_spec.u32_enc v (seg_spec.fldz off 4 bs) -> sa_val rd (a + off) 4 v.
Proof.
intros rd a bs off v Hb Ho Hl [Hv Hf] k Hk.
assert (Hn : nth k (seg_spec.fldz off 4 bs) ZB0 = nth (Z.to_nat off + k) bs ZB0).
{ unfold seg_spec.fldz, seg_spec.fld. rewrite mf_nth_firstn by lia. apply mf_nth_skipn. }
specialize (Hb (Z.to_nat off + k)%nat ltac:(lia)).
replace (a + Z.of_nat (Z.to_nat off + k)) with (a + off + Z.of_nat k) in Hb by lia.
rewrite Hb, <- Hn, Hf. f_equal.
unfold OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Mem.le4. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). rewrite (Z.mod_small v) by lia.
unfold le_byte. rewrite (Z.mod_small v (2 ^ (8 * Z.of_nat 4))) by (cbn; lia).
do 4 (destruct k as [|k]; [cbn [nth Z_to_le_bytes]; rewrite Z_to_bv_unsigned; unfold bv_wrap;
  change (bv_modulus 8) with 256; rewrite ?Z.shiftr_shiftr by lia; reflexivity|]).
lia.
Qed.
Lemma mf_val_of_sa : forall segs H (mem : word -> option byte) a n v,
sa_val (aview segs H mem) a n v -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte segs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb; cbn in Hv; [|discriminate Hv].
injection Hv as Hb. rewrite <- (Z_to_bv_bv_unsigned 8 b). rewrite Hb. reflexivity.
Qed.
Lemma mf_sa_of_val : forall segs H (m0 : word -> option byte) x n v,
val_mem segs (mrestrict H m0) x n v -> sa_val (aview segs H m0) x n v.
Proof.
intros segs H m0 x n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia.
Qed.

(* bcmp's answer on two byte runs: all n bytes agree exactly when the texts are equal *)
Lemma mf_cmp : forall (rd : reader) x y (s t : list byte) n,
Z.of_nat (length s) = n -> Z.of_nat (length t) = n ->
(forall i, (i < length s)%nat -> rd (x + Z.of_nat i) = Some (bv_unsigned (nth i s ZB0))) ->
(forall i, (i < length t)%nat -> rd (y + Z.of_nat i) = Some (bv_unsigned (nth i t ZB0))) ->
((forall i, 0 <= i < n -> rd (x + i) = rd (y + i)) <-> seg_spec.zs s = seg_spec.zs t).
Proof.
intros rd x y s t n Hs Ht Hx Hy. split.
- intros H. apply nth_ext with (d := 0) (d' := 0); [unfold seg_spec.zs; rewrite !length_map; lia|].
  intros j Hj. unfold seg_spec.zs in Hj. rewrite length_map in Hj. rewrite !mf_nth_zs.
  specialize (H (Z.of_nat j) ltac:(lia)). rewrite (Hx j Hj), (Hy j ltac:(lia)) in H. injection H as H. exact H.
- intros Heq i Hi. replace i with (Z.of_nat (Z.to_nat i)) by lia.
  rewrite (Hx (Z.to_nat i) ltac:(lia)), (Hy (Z.to_nat i) ltac:(lia)). f_equal.
  rewrite <- !mf_nth_zs. rewrite Heq. reflexivity.
Qed.

(* ================================ the model ================================ *)
Lemma mf_skipn_cons : forall {A} (l : list A) k d, (k < length l)%nat -> skipn k l = nth k l d :: skipn (Datatypes.S k) l.
Proof.
intros A l. induction l as [|x l IH]; intros k d H; cbn [length] in H; [lia|].
destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.
Lemma mf_go_step : forall segs nm k, (k < length segs)%nat ->
m_find_go (skipn k segs) nm k =
if (SegModel.strlen (ms_name (nth k segs mseg_d)) =? length nm)%nat &&
   SegModel.leqb (firstn (length nm) (ms_name (nth k segs mseg_d))) nm
then Some k else m_find_go (skipn (Datatypes.S k) segs) nm (Datatypes.S k).
Proof. intros segs nm k H. rewrite (mf_skipn_cons segs k mseg_d H). reflexivity. Qed.
Lemma mf_test : forall nmk nm, nulfree nmk ->
((SegModel.strlen nmk =? length nm)%nat && SegModel.leqb (firstn (length nm) nmk) nm) = SegModel.leqb nmk nm.
Proof. intros nmk nm H. rewrite strlen_id by exact H. apply len_leqb. Qed.

(* seg[k]'s name: its bytes sb (the name), the NUL after them, all inside the block's bytes *)
Lemma mf_name : forall (rd : reader) c bs mc k,
sa_bytes rd c bs -> seg_spec.mconf_encp false mc bs -> (k < length (mc_seg mc))%nat ->
exists sb : list byte, seg_spec.zs sb = ms_name (nth k (mc_seg mc) mseg_d) /\ (length sb < 16)%nat /\
nulfree (ms_name (nth k (mc_seg mc) mseg_d)) /\
forall i, (i <= length sb)%nat -> rd (c + 256 * Z.of_nat k + Z.of_nat i) = Some (nth i (seg_spec.zs sb ++ [0]) 0).
Proof.
intros rd c bs mc k HB (HL & H32 & HS & _) Hk.
destruct (HS k Hk) as (Hf & (Hf16 & Hlt & Hnz & Hpre) & _).
set (nm := ms_name (nth k (mc_seg mc) mseg_d)) in *.
set (f16 := seg_spec.fld 0 16 (seg_spec.fld (256 * k) 256 bs)) in *.
assert (HNTH : forall i, (i < 16)%nat -> nth i f16 ZB0 = nth (256 * k + i) bs ZB0).
{ intros i Hi. unfold f16, seg_spec.fld. rewrite mf_nth_firstn by lia. rewrite mf_nth_skipn.
  rewrite Nat.add_0_l. rewrite mf_nth_firstn by lia. apply mf_nth_skipn. }
unfold seg_spec.SEG_M_SIZE in HL.
assert (HR : forall i, (i < 16)%nat -> rd (c + 256 * Z.of_nat k + Z.of_nat i) = Some (nth i (seg_spec.zs f16) 0)).
{ intros i Hi. rewrite mf_nth_zs, (HNTH i Hi).
  replace (c + 256 * Z.of_nat k + Z.of_nat i) with (c + Z.of_nat (256 * k + i)) by lia.
  apply HB. lia. }
exists (firstn (length nm) f16).
assert (Hzs : seg_spec.zs (firstn (length nm) f16) = nm).
{ unfold seg_spec.zs. rewrite <- firstn_map.
  replace (firstn (length nm) (map bv_unsigned f16)) with (firstn (length nm) (firstn (Datatypes.S (length nm)) (map bv_unsigned f16)))
    by (rewrite firstn_firstn; f_equal; lia).
  unfold seg_spec.zs in Hpre. rewrite Hpre. rewrite firstn_app, firstn_all, Nat.sub_diag. cbn [firstn]. apply app_nil_r. }
assert (Hlen : length (firstn (length nm) f16) = length nm) by (rewrite length_firstn; lia).
split; [exact Hzs|]. split; [lia|]. split; [exact Hnz|].
intros i Hi. rewrite Hlen in Hi. rewrite Hzs. rewrite (HR i ltac:(lia)).
rewrite <- Hpre. rewrite mf_nth_firstn by lia. reflexivity.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
#[local] Notation MF_STK := SegInstB.STK_m_find.
#[local] Notation RLO := SegInstB.RLO_A.
#[local] Notation RHI := SegInstB.RHI_A.
Definition mf_E (regs : bvmap 5 word) (N : Z) : env := Eimg (Ereg regs (mf_extra N)).

(* the memory a run leaves, outside its write windows *)
Ltac mf_keep HFr K lo hi :=
  lazymatch type of HFr with frame_of _ _ (mrestrict ?H ?m1) (mrestrict ?H ?m2) =>
  assert (K : kept_out (aview SEGS H m1) (aview SEGS H m2) lo hi)
  by (let x0 := fresh "x0" in let Hx0 := fresh "Hx0" in let Hn0 := fresh "Hn0" in
      intros x0 Hx0 Hn0; apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun x => lo <= x < hi) HFr);
      [ let b0 := fresh "b0" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a0 := fresh "a0" in
        let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
        intros b0 wlo whi a0 Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr;
          repeat match goal with HU : bv_unsigned (ew _ _) = _ |- _ => rewrite HU in Hrr end; lia|]); destruct Hin
      | exact Hx0 | exact Hn0 ]) end.
(* the state after a wrapper call: st_ok_pi rebuilt over a fresh band of atoms for the clobbered registers *)
Ltac mf_after HS K W regs2 mem2 HP2 HS2 :=
  jafter_call_keep_hi HS K regs2 (mrestrict (w_H W) mem2) HP2 (@nil nat) HS2;
  let HRK := fresh "HRK" in
  match type of HS2 with ?P -> _ => assert (HRK : P) by (cbn [ms_mem restrict]; constructor) end;
  specialize (HS2 HRK); clear HRK; rewrite <- restrict_mkst_fx in HS2.
Ltac kin := unfold mf_kregs; cbn [In]; repeat (first [left; first [reflexivity | apply bv_eq; reflexivity] | right]).

Section e.
Variable B : asyms.
(* the record hypothesis: the listing's objects A_OBJ 0 / A_OBJ 12 are the record's GOT word and shadow-base cell,
   and the errno cell's placement (SegPaLib.v PALib) *)
Hypothesis TL : PALib B.
(* the wrappers it calls, at the listing's call targets: the image-A wrapper lane's interface row 16 (strlen, image B's
   trampoline 0x43a98) and row 19 (bcmp, the kit's text, image B's trampoline 0x43ac4) *)
Hypothesis STRLEN : forall fx0 : YK11.FPState,
  @RtString.astrlen_realizes fx0 rc SEGS B (SIGMA SS___interceptor_trampoline_strlen).
Hypothesis ABCMP : forall fx0 : YK11.FPState,
  @abcmp_realizes fx0 rc SEGS B (SIGMA SS___interceptor_trampoline_bcmp).
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_seg) (PI := PI).
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let ART := aj_art_at SEGS B LAWS pa_segs_low (pal_env B TL).

(* ================================ one call of m_find ================================ *)
Section w.
Variables (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (ch : list (Z * Z * Z)) (c name n : Z) (mc : mconf) (l : list byte).
Hypothesis HPRE : afn_pre SEGS B MF_STK ly S W regs mem md ch.
Hypothesis HROD : arodata_okP SEGS RLO RHI B (rdW W mem).
Hypothesis H10 : getr regs 10 = w64 c.
Hypothesis H11 : getr regs 11 = w64 name.
Hypothesis H12 : getr regs 12 = w64 n.
Hypothesis Hn64 : 0 <= n < 2 ^ 64.
Hypothesis HMP : m_find_pre SEGS B ly S (rdW W mem) c name n mc l.

Definition mf_Q : world SEGS -> config -> Prop :=
apost_base SEGS B MF_STK [] regs ly S W mem md EV_m_find
(fun ly' S' W' regs' mem' md' =>
 getr regs' 10 = w64 (m_find_ptr c mc (seg_spec.zs l)) /\
 sa_kept SEGS W mem W' mem' regs MF_STK (fun _ => False) /\
 sa_noalloc B ly S ly' S').
(* the saved registers in the frame *)
Definition mf_frame (rd : reader) : Prop :=
forall j r, nth_error mf_saved j = Some r ->
sa_val rd (spZ regs - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).
(* a cut point: the journal from the entry, the memory outside the stack window unchanged, the frame, sp, and the
   callee-saved registers m_find leaves alone *)
Definition mf_cut (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
ajournal SEGS B MF_STK (spZ regs) [] ly S W mem md [] ly S W mem1 md1 0 /\
kept_out (rdW W mem) (rdW W mem1) (spZ regs - MF_STK) (spZ regs) /\
mf_frame (rdW W mem1) /\ getr regs1 2 = w64 (spZ regs - 64) /\
(forall r, In r mf_kregs -> getr regs1 r = getr regs r).
(* LH with k entries passed *)
Definition mf_LH (k : nat) (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
mf_cut regs1 mem1 md1 /\ (k < length (mc_seg mc))%nat /\
SegModel.m_find mc (seg_spec.zs l) = m_find_go (skipn k (mc_seg mc)) (seg_spec.zs l) k /\
getr regs1 8 = w64 (c + 256 * Z.of_nat k) /\ getr regs1 9 = w64 n /\ getr regs1 18 = w64 name /\
getr regs1 19 = w64 (256 * Z.of_nat k) /\ getr regs1 20 = w64 (2 ^ 64 - 1 - c) /\
getr regs1 21 = w64 (Z.of_nat (length (mc_seg mc) - k)) /\ getr regs1 22 = w64 (32 - Z.of_nat k).
(* NX with entry k rejected *)
Definition mf_NX (k : nat) (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
mf_cut regs1 mem1 md1 /\ (k < length (mc_seg mc))%nat /\
SegModel.m_find mc (seg_spec.zs l) = m_find_go (skipn (Datatypes.S k) (mc_seg mc)) (seg_spec.zs l) (Datatypes.S k) /\
getr regs1 8 = w64 (c + 256 * Z.of_nat k) /\ getr regs1 9 = w64 n /\ getr regs1 18 = w64 name /\
getr regs1 19 = w64 (256 * Z.of_nat k) /\ getr regs1 20 = w64 (2 ^ 64 - 1 - c) /\
getr regs1 21 = w64 (Z.of_nat (length (mc_seg mc) - k)) /\ getr regs1 22 = w64 (32 - Z.of_nat k).

Lemma mf_sp : spZ regs mod 16 = 0 /\ alloc_ceiling + MF_STK <= spZ regs /\ spZ regs <= 2 ^ 47 /\
ly_stk_lo ly + MF_STK <= spZ regs.
Proof.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
split; [exact Hal16|]. lia.
Qed.
(* c's block *)
Lemma mf_blk : exists b m, In (b, m) (ablocks B ly S) /\ b <= c /\ c + 9236 <= b + m /\ 4096 <= c /\
c + 9236 <= alloc_ceiling.
Proof.
pose proof HPRE as (HAR & _). destruct HMP as (_ & _ & _ & (b & m & Hin & H1 & H2) & _).
destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & Hb4 & Hbc & _ & _ & _ & Hm).
unfold seg_spec.SEG_M_SIZE in H2.
pose proof (req_size_pos m ltac:(lia)) as [_ Hr]. exists b, m. split; [exact Hin|]. lia.
Qed.
Lemma mf_mc : exists bs, sa_bytes (rdW W mem) c bs /\ seg_spec.mconf_encp false mc bs.
Proof. destruct HMP as (_ & _ & HM & _). exact HM. Qed.
Lemma mf_N32 : (length (mc_seg mc) <= 32)%nat.
Proof. destruct mf_mc as (bs & _ & (_ & H32 & _)). exact H32. Qed.
Lemma mf_Rc : 0 <= c <= MF_CHI.
Proof.
destruct HMP as (_ & _ & _ & _ & (Hc0 & Hc63 & AMc & _) & _).
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in AMc. unfold MF_CHI, seg_spec.SEG_M_SIZE in *. lia.
Qed.
Lemma mf_seg : forall k, (k < length (mc_seg mc))%nat ->
exists sb : list byte, seg_spec.zs sb = ms_name (nth k (mc_seg mc) mseg_d) /\ (length sb < 16)%nat /\
nulfree (ms_name (nth k (mc_seg mc) mseg_d)) /\ astr_atR (rdW W mem) (c + 256 * Z.of_nat k) sb.
Proof.
intros k Hk. destruct mf_mc as (bs & HB & HE).
destruct (mf_name _ c bs mc k HB HE Hk) as (sb & Hzs & Hl & Hnul & HR).
exists sb. split; [exact Hzs|]. split; [exact Hl|]. split; [exact Hnul|]. split.
- intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. rewrite (HR i ltac:(lia)). f_equal.
  rewrite mf_zs_app0, mf_nth_zs. reflexivity.
- intros Hin. apply Hnul. rewrite <- Hzs. unfold seg_spec.zs.
  replace 0 with (bv_unsigned (Z_to_bv 8 0)) by reflexivity. apply in_map. exact Hin.
Qed.
(* the n bytes at name *)
Lemma mf_name_facts : sa_bytes (rdW W mem) name l /\ Z.of_nat (length l) = n /\ sa_addr (rdW W mem) name n /\
(0 < n -> name + n <= alloc_ceiling).
Proof.
pose proof HPRE as (HAR & _). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HMP as (_ & _ & _ & _ & _ & HB & HL & HA & HLOC).
split; [exact HB|]. split; [exact HL|]. split; [exact HA|]. intros Hn0.
destruct HLOC as [(b & m & Hin & H1 & H2) | [(cid & pos & Hin & Hcid & H1 & H2) | HI]].
- destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & _ & Hbc & _ & _ & _ & Hm).
  pose proof (req_size_pos m ltac:(lia)) as [_ Hr]. lia.
- destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hin) as (_ & Hf & _). lia.
- destruct (HI (name + n - 1) ltac:(lia)) as (Hi & _ & _). pose proof (pa_segs_low _ Hi) as Hlow. lia.
Qed.
(* the facts at name at a later state whose memory below the stack window is the entry's *)
Lemma mf_name_at : forall memc, kept_out (rdW W mem) (rdW W memc) (spZ regs - MF_STK) (spZ regs) ->
(forall i, (i < length l)%nat -> rdW W memc (name + Z.of_nat i) = Some (bv_unsigned (nth i l ZB0))) /\
range_addressable (rdW W memc) SHADOW_OFF name n /\ (0 < n -> shadow_hull_vis (rdW W memc) name n).
Proof.
intros memc HK. pose proof mf_sp as (Hal16 & Hslo & Hshi & Hlo). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HST : MF_STK = 8256) by reflexivity.
destruct mf_name_facts as (HB & HL & (Hy0 & Hyn & AM & RA & HV) & Hlow).
assert (Hy47 : name + n <= 2 ^ 47) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in AM; lia).
split; [|split].
- intros i Hi. pose proof (Hlow ltac:(lia)) as Hl'. rewrite (HK (name + Z.of_nat i)) by lia. exact (HB i Hi).
- exact (range_addressable_kept_win _ _ (spZ regs - MF_STK) (spZ regs) name n HK ltac:(lia) Hy0 Hy47 RA).
- intros Hn0. exact (shadow_hull_vis_kept_win _ _ (spZ regs - MF_STK) (spZ regs) name n HK ltac:(lia) Hy0 Hy47 Hn0 (HV Hn0)).
Qed.
(* the image bytes a wrapper reads, at a state whose memory below the stack window is the entry's *)
Lemma mf_rom : forall memc, kept_out (rdW W mem) (rdW W memc) (spZ regs - MF_STK) (spZ regs) ->
rt_rom_view SEGS B W memc.
Proof.
intros memc HK a Hr Ho He. pose proof mf_sp as (Hal16 & Hslo & Hshi & Hlo). pose proof asan_consts as (C1 & _).
assert (HST : MF_STK = 8256) by reflexivity.
assert (Hi : in_img SEGS a) by (destruct Hr as (sg & Hs & _ & Hsr); exists sg; split; [exact Hs | exact Hsr]).
pose proof (pa_img_range _ Hi) as R. unfold kImgEnd in R. rewrite (HK a) by lia.
exact (HROD a (or_introl Hr) Ho He).
Qed.
(* a cut carried to a later state whose memory differs only in a window below the frame *)
Lemma mf_cut_kept : forall regs1 mem1 md1 regs2 mem2 md2,
mf_cut regs1 mem1 md1 ->
ajournal SEGS B MF_STK (spZ regs) [] ly S W mem md [] ly S W mem2 md2 0 ->
kept_out (rdW W mem1) (rdW W mem2) (spZ regs - MF_STK) (spZ regs - 64) ->
getr regs2 2 = getr regs1 2 -> (forall r, In r mf_kregs -> getr regs2 r = getr regs1 r) ->
mf_cut regs2 mem2 md2.
Proof.
intros regs1 mem1 md1 regs2 mem2 md2 (HJ & HK & HFR & R2 & RK) HJ2 HK2 Q2 QK.
pose proof mf_sp as (Hal16 & Hslo & Hshi & Hlo). assert (HST : MF_STK = 8256) by reflexivity.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [exact HJ2|]. split.
{ intros a Ha Hn. rewrite (HK2 a Ha) by lia. exact (HK a Ha Hn). }
split.
{ intros j r Hr. assert (Hj : (j < 8)%nat)
    by (change 8%nat with (length mf_saved); apply (proj1 (nth_error_Some mf_saved j)); rewrite Hr; discriminate).
  intros i Hi.
  assert (A1 : 0 <= spZ regs - 8 - 8 * Z.of_nat j + Z.of_nat i < 2 ^ 64) by lia.
  assert (A2 : ~ (spZ regs - MF_STK <= spZ regs - 8 - 8 * Z.of_nat j + Z.of_nat i < spZ regs - 64)) by lia.
  rewrite (HK2 _ A1 A2). exact (HFR j r Hr i Hi). }
split; [rewrite Q2; exact R2|].
intros r Hr. rewrite (QK r Hr). exact (RK r Hr).
Qed.

(* ---------------- a loop point's seed: the registers as atoms, the three trap facts ---------------- *)
Lemma mf_seed_at : forall pc (k : nat) regs1 mem1,
(k < 32)%nat ->
getr regs1 2 = w64 (spZ regs - 64) -> getr regs1 19 = w64 (256 * Z.of_nat k) ->
getr regs1 20 = w64 (2 ^ 64 - 1 - c) -> getr regs1 22 = w64 (32 - Z.of_nat k) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 [])) (mf_ss_at pc)
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + pc)) mem1 (seg_rom SEGS))).
Proof.
intros pc k regs1 mem1 Hk R2 R19 R20 R22.
pose proof mf_sp as (Hal16 & Hslo & Hshi & Hlo). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HST : MF_STK = 8256) by reflexivity. pose proof mf_Rc as Rc. unfold MF_CHI, seg_spec.SEG_M_SIZE in Rc.
set (E := Eimg (Ereg regs1 [])).
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr regs1 r)
  by (intros n0 r Hn0; subst E; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (U2 : bv_unsigned (ew E 2) = spZ regs - 64)
  by (rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = 256 * Z.of_nat k)
  by (rewrite (EE 19%nat 19%bv eq_refl), R19; unfold w64; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = 2 ^ 64 - 1 - c)
  by (rewrite (EE 20%nat 20%bv eq_refl), R20; unfold w64; apply unsigned_lit_small; lia).
assert (U22 : bv_unsigned (ew E 22) = 32 - Z.of_nat k)
  by (rewrite (EE 22%nat 22%bv eq_refl), R22; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold mf_ss_at. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- cbn. tauto.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok, mf_spF, mf_iF, mf_notF, mf_cntF.
  cbn [af_lo af_hi af_al2]. rewrite U2, U19, U20, U22.
  change (2 ^ 4) with 16. change (2 ^ 8) with 256. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end;
  first [ exact I | lia | (rewrite Zminus_mod, Hal16; reflexivity) | (rewrite Z.mul_comm; apply Z.mod_mul; lia) ].
Qed.

(* ---------------- the epilogue: EPI 0x875b0 .. the ret ---------------- *)
Definition mf_e_extra : list word := map (fun r => getr regs (Z_to_bv 5 r)) mf_saved.
Lemma mf_e_nth : forall j r, nth_error mf_saved j = Some r -> nth j mf_e_extra (Z_to_bv 64 0) = getr regs (Z_to_bv 5 r).
Proof.
intros j r H. unfold mf_e_extra. apply nth_error_nth.
rewrite (map_nth_error (fun r0 => getr regs (Z_to_bv 5 r0)) j mf_saved H). reflexivity.
Qed.
Lemma mf_epi_seed : forall regs1 mem1, getr regs1 2 = w64 (spZ regs - 64) -> mf_frame (rdW W mem1) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 mf_e_extra)) mf_ss_epi
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + MF_EPI)) mem1 (seg_rom SEGS))).
Proof.
intros regs1 mem1 R2 HFR. pose proof mf_sp as (Hal16 & Hslo & Hshi & Hlo).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HST : MF_STK = 8256) by reflexivity.
assert (Usp : bv_unsigned (ew (Eimg (Ereg regs1 mf_e_extra)) 2) = spZ regs - 64).
{ rewrite (ew_Eimg_Ereg_nat regs1 _ 2 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. lia. }
rewrite restrict_mkst_fx. unfold mf_ss_epi. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok, mf_estack.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_forall. intros cc Hcc. apply in_map_iff in Hcc as (j & <- & Hj). apply in_seq in Hj.
  destruct (nth_error mf_saved j) as [r|] eqn:Hr; [| apply nth_error_None in Hr; cbn in Hr; lia].
  pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HRr. change (bv_modulus 64) with (2 ^ 64) in HRr.
  apply (chunk_ok_val SEGS _ _ (spZ regs - 64) (56 - 8 * Z.of_nat j) 8 (SOff (32 + j) 0) (bv_unsigned (getr regs (Z_to_bv 5 r)))).
  + cbn [sv_denot]. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra, (mf_e_nth j r Hr).
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact HRr.
  + cbn. lia.
  + replace (spZ regs - 64 + (56 - 8 * Z.of_nat j)) with (spZ regs - 8 - 8 * Z.of_nat j) by lia.
    apply mf_val_of_sa. exact (HFR j r Hr).
- cbn. tauto.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|exact I]. unfold afact_ok, mf_spF. cbn [af_lo af_hi af_al2].
  rewrite Usp. change (2 ^ 4) with 16. split; [lia|]. split; [|lia]. rewrite Zminus_mod, Hal16. reflexivity.
Qed.
Lemma mf_epi : forall v regs1 mem1 md1, mf_cut regs1 mem1 md1 -> getr regs1 8 = w64 v ->
v = m_find_ptr c mc (seg_spec.zs l) ->
SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + MF_EPI)) mem1 (seg_rom SEGS)) md1) mf_Q.
Proof.
intros v regs1 mem1 md1 (HJ & HK & HFR & R2 & RK) R8 Hv.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof mf_sp as (Hal16 & Hslo & Hshi & Hlo).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HST : MF_STK = 8256) by reflexivity.
pose proof (mf_epi_seed regs1 mem1 R2 HFR) as HS.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs1 mf_e_extra))) by apply Eimg_env.
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew (Eimg (Ereg regs1 mf_e_extra)) n0 = getr regs1 r)
  by (intros n0 r Hn0; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (EX : forall j r, nth_error mf_saved j = Some r -> ew (Eimg (Ereg regs1 mf_e_extra)) (32 + j) = getr regs (Z_to_bv 5 r)).
{ intros j r Hr. assert (Hj : (j < 8)%nat)
    by (change 8%nat with (length mf_saved); apply (proj1 (nth_error_Some mf_saved j)); rewrite Hr; discriminate).
  rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra. exact (mf_e_nth j r Hr). }
pose proof (EX 0%nat 1 eq_refl) as E32. pose proof (EX 1%nat 8 eq_refl) as E33. pose proof (EX 2%nat 9 eq_refl) as E34.
pose proof (EX 3%nat 18 eq_refl) as E35. pose proof (EX 4%nat 19 eq_refl) as E36. pose proof (EX 5%nat 20 eq_refl) as E37.
pose proof (EX 6%nat 21 eq_refl) as E38. pose proof (EX 7%nat 22 eq_refl) as E39.
cbn [Nat.add] in E32, E33, E34, E35, E36, E37, E38, E39. clear EX.
remember (Eimg (Ereg regs1 mf_e_extra)) as E eqn:HE. clear HE.
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 64)
  by (rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
(* 0x875b0 .. 0x875d4: a0 := s0, ra s0 .. s6 back from the frame, sp += 64, stopped at the ret *)
paj_run_sh RUNP HS HJ.
{ awr_ok_tac; try exact Usp. }
cbn [ms_mem mkst] in HFr.
mf_keep HFr KEEP (spZ regs - MF_STK) (spZ regs - MF_STK). clear HF HFr HG.
prreg HS (1%bv : bv 5) F1. prreg HS (10%bv : bv 5) F10.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold mf_Q, apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly, S, r, m, d end.
split.
{ rewrite F1, E32. change (getr regs (Z_to_bv 5 1)) with (getr regs 1). unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split.
{ apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ. }
split.
{ unfold aregs_preserved. intros r Hr.
  assert (Hcases : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (unfold acallee_saved in Hr; lia).
  clear Hr.
  repeat (destruct Hcases as [-> | Hcases]); [..| subst r];
  rewrite (st_ok_pi_restrict_reg (w_H W) E _ _ _ HS); cbn [ms_regs];
  lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
  cbn [sv_denot];
  first
  [ rewrite Usp; replace (spZ regs - 64 + 64) with (spZ regs) by lia; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity
  | rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
    first [ exact E33 | exact E34 | exact E35 | exact E36 | exact E37 | exact E38 | exact E39
          | lazymatch goal with |- ew _ ?n0 = getr regs (Z_to_bv 5 ?r0) =>
              rewrite (EE n0 (Z_to_bv 5 r0) eq_refl); apply RK; kin end ] ]. }
split; [rewrite F10, (EE 8%nat 8%bv eq_refl), R8, Hv; reflexivity|].
split.
{ intros a Ha Hn _. rewrite (KEEP a Ha) by lia. exact (HK a Ha Hn). }
split; [apply Permutation_refl | split; [reflexivity | exists (st_fs S); destruct S; reflexivity]].
Qed.

(* ---------------- NX 0x87598 .. 0x875a8: the next entry or NONE ---------------- *)
Lemma mf_nx : forall k regs1 mem1 md1,
((Datatypes.S k < length (mc_seg mc))%nat -> forall r m d, mf_LH (Datatypes.S k) r m d ->
  SRr SEGS W (mkCfg (mkst r (Z_to_bv 64 (BASE + MF_LH)) m (seg_rom SEGS)) d) mf_Q) ->
mf_NX k regs1 mem1 md1 ->
SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + MF_NX)) mem1 (seg_rom SEGS)) md1) mf_Q.
Proof.
intros k regs1 mem1 md1 IH (HCUT & Hk & Hmod & R8 & R9 & R18 & R19 & R20 & R21 & R22).
pose proof HCUT as (HJ & HK & HFR & R2 & RK).
pose proof mf_sp as (Hal16 & Hslo & Hshi & Hlo).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HST : MF_STK = 8256) by reflexivity.
pose proof mf_N32 as H32. pose proof mf_Rc as Rc. unfold MF_CHI, seg_spec.SEG_M_SIZE in Rc.
destruct mf_blk as (b & m & Hin & Hb1 & Hb2 & Hc4096 & Hcc).
pose proof (mf_seed_at MF_NX k regs1 mem1 ltac:(lia) R2 R19 R20 R22) as HS.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs1 []))) by apply Eimg_env.
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew (Eimg (Ereg regs1 [])) n0 = getr regs1 r)
  by (intros n0 r Hn0; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (HAE : env_agree 32 (Ereg regs1 []) (Eimg (Ereg regs1 [])))
  by (split; [intros n0 Hn0; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
remember (Eimg (Ereg regs1 [])) as E eqn:HE. clear HE.
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 64)
  by (rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
assert (E21 : ew E 21 = Z_to_bv 64 (Z.of_nat (length (mc_seg mc) - k))) by (rewrite (EE 21%nat 21%bv eq_refl); exact R21).
assert (E8 : ew E 8 = Z_to_bv 64 (c + 256 * Z.of_nat k)) by (rewrite (EE 8%nat 8%bv eq_refl); exact R8).
assert (E19 : ew E 19 = Z_to_bv 64 (256 * Z.of_nat k)) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
assert (E22 : ew E 22 = Z_to_bv 64 (32 - Z.of_nat k)) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
(* 0x87598 .. 0x875a8: s5 -= 1, s0 += 256, s3 += 256, s6 -= 1, bnez s5 *)
paj_run_shc RUNP RUNC HS HJ.
{ awr_ok_tac; try exact Usp. }
mf_keep HFr KEEP1 (spZ regs - MF_STK) (spZ regs - 64). clear HF HFr HG.
psrr_branch_pi RUNP BR HS.
- (* entries left: back to LH with k + 1 *)
  assert (HkS : (Datatypes.S k < length (mc_seg mc))%nat).
  { rewrite branch_ne_U, (U_atom_off E 21 _ (-1) E21), U_lit in Hc by lia.
    apply negb_true_iff, Z.eqb_neq in Hc. lia. }
  clear Hc.
  paj_run_to_shc RUNTOP HS HJ MF_LH.
  { awr_ok_tac; try exact Usp. }
  mf_keep HFr KEEP2 (spZ regs - MF_STK) (spZ regs - 64). clear HF HFr HG.
  pmkst HS.
  prreg HS (2%bv : bv 5) Q2. prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9.
  prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
  prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22.
  apply (IH HkS).
  split; [|split; [exact HkS|split]].
  + apply (mf_cut_kept regs1 mem1 md1 _ _ _ HCUT HJ (kept_out_trans _ _ _ _ _ _ _ KEEP1 KEEP2 ltac:(lia) ltac:(lia))).
    * rewrite Q2, (EE 2%nat 2%bv eq_refl). reflexivity.
    * intros r Hr. lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
        exact (regs_kept_of_st_ok_pi Ex ssx msx regs1 [] mf_kregs HS HAE ltac:(vm_compute; reflexivity) r Hr) end.
  + exact Hmod.
  + split; [rewrite Q8, E8; unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia|].
    split; [rewrite Q9, (EE 9%nat 9%bv eq_refl); exact R9|].
    split; [rewrite Q18, (EE 18%nat 18%bv eq_refl); exact R18|].
    split; [rewrite Q19, E19; unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia|].
    split; [rewrite Q20, (EE 20%nat 20%bv eq_refl); exact R20|].
    split; [rewrite Q21, E21; unfold w64; rewrite unsigned_lit_small by lia; f_equal; lia|].
    rewrite Q22, E22. unfold w64. rewrite unsigned_lit_small by lia. f_equal. lia.
- (* none left: NONE 0x875ac s0 := 0, then EPI *)
  assert (HkS : Datatypes.S k = length (mc_seg mc)).
  { rewrite branch_ne_U, (U_atom_off E 21 _ (-1) E21), U_lit in Hc by lia.
    apply negb_false_iff, Z.eqb_eq in Hc. lia. }
  clear Hc.
  paj_run_to_shc RUNTOP HS HJ MF_EPI.
  { awr_ok_tac; try exact Usp. }
  mf_keep HFr KEEP2 (spZ regs - MF_STK) (spZ regs - 64). clear HF HFr HG.
  pmkst HS.
  prreg HS (2%bv : bv 5) Q2. prreg HS (8%bv : bv 5) Q8.
  apply (mf_epi 0).
  + apply (mf_cut_kept regs1 mem1 md1 _ _ _ HCUT HJ (kept_out_trans _ _ _ _ _ _ _ KEEP1 KEEP2 ltac:(lia) ltac:(lia))).
    * rewrite Q2, (EE 2%nat 2%bv eq_refl). reflexivity.
    * intros r Hr. lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
        exact (regs_kept_of_st_ok_pi Ex ssx msx regs1 [] mf_kregs HS HAE ltac:(vm_compute; reflexivity) r Hr) end.
  + rewrite Q8. reflexivity.
  + unfold m_find_ptr. rewrite Hmod, HkS, skipn_all. reflexivity.
Qed.

(* ---------------- LH 0x87570 .. NX / EPI: the two trap edges and the two calls of one entry ---------------- *)
Lemma mf_lh : forall k regs1 mem1 md1,
(forall r m d, mf_NX k r m d -> SRr SEGS W (mkCfg (mkst r (Z_to_bv 64 (BASE + MF_NX)) m (seg_rom SEGS)) d) mf_Q) ->
mf_LH k regs1 mem1 md1 ->
SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + MF_LH)) mem1 (seg_rom SEGS)) md1) mf_Q.
Proof.
intros k regs1 mem1 md1 NXT (HCUT & Hk & Hmod & R8 & R9 & R18 & R19 & R20 & R21 & R22).
pose proof HCUT as (HJ & HK & HFR & R2 & RK).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof mf_sp as (Hal16 & Hslo & Hshi & Hlo).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HST : MF_STK = 8256) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof mf_N32 as H32. pose proof mf_Rc as Rc. unfold MF_CHI, seg_spec.SEG_M_SIZE in Rc.
destruct mf_blk as (b & m & Hin & Hb1 & Hb2 & Hc4096 & Hcc).
destruct mf_name_facts as (HBn & HLn & (Hy0 & Hyn & AMy & _ & _) & Hnlow).
destruct (mf_seg k Hk) as (sb & Hzs & Hsl & Hnul & STR0).
assert (Hc16 : c mod 16 = 0) by (destruct HMP as (_ & H16 & _); exact H16).
pose proof (mf_mod16 c k Hc16) as Hx16.
pose proof (mf_go_step (mc_seg mc) (seg_spec.zs l) k Hk) as STEP.
rewrite (mf_test _ _ Hnul) in STEP.
(* the seed at LH *)
pose proof (mf_seed_at MF_LH k regs1 mem1 ltac:(lia) R2 R19 R20 R22) as HS.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs1 []))) by apply Eimg_env.
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew (Eimg (Ereg regs1 [])) n0 = getr regs1 r)
  by (intros n0 r Hn0; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (HAE : env_agree 32 (Ereg regs1 []) (Eimg (Ereg regs1 [])))
  by (split; [intros n0 Hn0; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
remember (Eimg (Ereg regs1 [])) as E eqn:HE. clear HE.
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 64)
  by (rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
(* LH .. 0x8757c: the two trap edges (decided false by the facts on atoms 19, 20, 22), a0 := s0, jal strlen *)
paj_run_shc RUNP RUNC HS HJ.
{ awr_ok_tac; try exact Usp. }
mf_keep HFr KEEP1 (spZ regs - MF_STK) (spZ regs - 64). clear HF HFr HG.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msA) =>
  prreg HS (10%bv : bv 5) P10; prreg HS (1%bv : bv 5) P1; prreg HS (2%bv : bv 5) P2;
  prreg HS (3%bv : bv 5) P3; prreg HS (4%bv : bv 5) P4;
  assert (Hsp1 : spZ (ms_regs msA) = spZ regs + -64) by (unfold spZ at 1; rewrite P2, Usp; lia);
  assert (P10' : getr (ms_regs msA) 10 = w64 (c + 256 * Z.of_nat k)) by (rewrite P10, (EE 8%nat 8%bv eq_refl); exact R8);
  pose proof (kept_out_trans _ _ _ _ _ _ _ HK KEEP1 ltac:(lia) ltac:(lia)) as KEEPc;
  assert (STRT : astr_at SEGS W (ms_mem msA) (c + 256 * Z.of_nat k) sb)
    by (apply (astr_atR_view SEGS); apply (astr_atR_kept _ _ (spZ regs - MF_STK) (spZ regs) _ sb KEEPc STR0); lia);
  assert (RDT : aread_ok SEGS ESTACK W (ms_regs msA) (ms_mem msA) (c + 256 * Z.of_nat k) (astr_len sb + 1))
    by (eapply (aread_ok_of_block SEGS B LAWS ESTACK ly S W (ms_regs msA) (ms_mem msA) _ b m);
        [exact (proj1 HJ) | exact Hin | lia | unfold astr_len; lia | unfold astr_len; lia | rewrite Hsp1; lia]);
  pose proof (aread_ok_of_block SEGS B LAWS ESTACK ly S W (ms_regs msA) (ms_mem msA) _ b m (c + 256 * Z.of_nat k) 16
    (proj1 HJ) Hin ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite Hsp1; lia)) as RD16;
  assert (TLT : atail_vis SEGS W (ms_mem msA) (c + 256 * Z.of_nat k + astr_len sb))
    by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; unfold astr_len in Ha;
        pose proof (mf_tail_bound (c + 256 * Z.of_nat k) (Z.of_nat (length sb)) Hx16 ltac:(lia)) as TB;
        destruct RD16 as (_ & _ & _ & HM16 & _); exact (proj1 (HM16 a ltac:(lia))));
  pose proof (mf_rom _ KEEPc) as ROMT;
  pose proof (ecall_pre_stk_at SEGS B ESTACK MF_STK (spZ regs) [] ly S W mem md [] ly S W (ms_mem msA) _ 0 (ms_regs msA) (-64) HJ
    Hsp1 eq_refl ltac:(lia) ltac:(lia) ltac:(rewrite HST, Hes; lia)
    ltac:(rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity])
    ltac:(rewrite P3, (EE 3%nat 3%bv eq_refl), (RK 3%bv ltac:(kin)); exact Hgp)
    ltac:(rewrite P4, (EE 4%nat 4%bv eq_refl), (RK 4%bv ltac:(kin)); exact Htp)) as PRE;
  pmkst HS;
  eapply SRr_bind;
  [ eapply (ART ESTACK (fun _ => False) _ W (ms_regs msA) (ms_mem msA) MF_STK (spZ regs) [] ly S W mem md
      [] ly S _ 0 (-64) _ (fun regs' _ => getr regs' 10 = w64 (astr_len sb)) HJ);
    [ exact Hsp1 | reflexivity | lia | lia | rewrite HST, Hes; lia | exact P1 | intros ? [] |
      exact (STRLEN fx ly S W (ms_regs msA) (ms_mem msA) _ (c + 256 * Z.of_nat k) sb PRE P10' ltac:(lia) STRT RDT TLT ROMT) ]
  | ]
end.
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ2 & HFR2').
pose proof (fun a Ha Hn => HFR2' a Ha Hn (fun x0 : False => x0)) as HFR2. clear HFR2'.
lazymatch type of HFR2 with forall a, _ -> _ -> aview _ _ mem2 a = aview _ _ ?mT a =>
  assert (KEEPs : kept_out (rdW W mT) (rdW W mem2) (spZ regs - MF_STK) (spZ regs - 64))
    by (let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in intros a Ha Hn; apply HFR2; [exact Ha | lia]) end.
pose proof (kept_out_trans _ _ _ _ _ _ _ KEEP1 KEEPs ltac:(lia) ltac:(lia)) as KEEPa.
clear KEEPs KEEP1 HFR2.
(* back at 0x87580: bne a0, s1 *)
mf_after HS 1024%nat W regs2 mem2 HP2 HS2.
lazymatch type of HS2 with st_ok_pi _ _ ?E1 _ _ =>
  assert (HEI1 : img_env VAL A_LIM E1) by (apply img_env_havoc_hi; [exact HEI | cbv; lia]);
  assert (HAE1 : env_agree 32 (Ereg regs1 []) E1) by (apply env_agree_havoc_ge; [cbv; lia | exact HAE]);
  assert (A1 : ew E1 1028 = Z_to_bv 64 (astr_len sb))
    by (change 1028%nat with (1024 + 4)%nat; rewrite (ew_havoc_new _ 1024 _ 4 (Z_to_bv 64 0)) by (cbn; lia);
        unfold CLOB; cbn [map nth]; exact HQ2);
  assert (E9 : ew E1 9 = Z_to_bv 64 n)
    by (rewrite ew_havoc_old by (cbv; lia); rewrite (EE 9%nat 9%bv eq_refl); exact R9)
end.
clear HS HJ.
psrr_branch_pi RUNP BR HS2.
- (* strlen(name_k) <> n: entry k rejected, to NX *)
  rewrite branch_ne_U, (U_atom _ 1028 (astr_len sb) A1), (U_atom _ 9 n E9) in Hc by (unfold astr_len; lia).
  apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into HLEN.
  assert (EL : SegModel.leqb (ms_name (nth k (mc_seg mc) mseg_d)) (seg_spec.zs l) = false).
  { destruct (SegModel.leqb _ _) eqn:EQ; [|reflexivity]. exfalso. apply leqb_len in EQ.
    rewrite <- Hzs in EQ. unfold seg_spec.zs in EQ. rewrite !length_map in EQ. unfold astr_len in HLEN. lia. }
  rewrite EL in STEP. cbv iota in STEP.
  paj_run_to_shc RUNTOP HS2 HJ2 MF_NX.
  { awr_ok_tac; try exact Usp. }
  mf_keep HFr KEEP3 (spZ regs - MF_STK) (spZ regs - 64). clear HF HFr HG.
  pmkst HS2.
  prreg HS2 (2%bv : bv 5) Q2. prreg HS2 (8%bv : bv 5) Q8. prreg HS2 (9%bv : bv 5) Q9.
  prreg HS2 (18%bv : bv 5) Q18. prreg HS2 (19%bv : bv 5) Q19. prreg HS2 (20%bv : bv 5) Q20.
  prreg HS2 (21%bv : bv 5) Q21. prreg HS2 (22%bv : bv 5) Q22.
  apply NXT.
  split; [|split; [exact Hk|split; [rewrite Hmod; exact STEP|]]].
  + apply (mf_cut_kept regs1 mem1 md1 _ _ _ HCUT HJ2 (kept_out_trans _ _ _ _ _ _ _ KEEPa KEEP3 ltac:(lia) ltac:(lia))).
    * rewrite Q2, (EE 2%nat 2%bv eq_refl). reflexivity.
    * intros r Hr. lazymatch type of HS2 with st_ok_pi _ _ ?Ex ?ssx ?msx =>
        exact (regs_kept_of_st_ok_pi Ex ssx msx regs1 [] mf_kregs HS2 HAE1 ltac:(vm_compute; reflexivity) r Hr) end.
  + split; [rewrite Q8, (EE 8%nat 8%bv eq_refl); exact R8|].
    split; [rewrite Q9, (EE 9%nat 9%bv eq_refl); exact R9|].
    split; [rewrite Q18, (EE 18%nat 18%bv eq_refl); exact R18|].
    split; [rewrite Q19, (EE 19%nat 19%bv eq_refl); exact R19|].
    split; [rewrite Q20, (EE 20%nat 20%bv eq_refl); exact R20|].
    split; [rewrite Q21, (EE 21%nat 21%bv eq_refl); exact R21|].
    rewrite Q22, (EE 22%nat 22%bv eq_refl). exact R22.
- (* strlen(name_k) = n: bcmp(name_k, name, n) *)
  rewrite branch_ne_U, (U_atom _ 1028 (astr_len sb) A1), (U_atom _ 9 n E9) in Hc by (unfold astr_len; lia).
  apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into HLEN. unfold astr_len in HLEN.
  (* 0x87584 .. 0x87590: a0 := s0, a1 := s2, a2 := s1, jal bcmp *)
  paj_run_shc RUNP RUNC HS2 HJ2.
  { awr_ok_tac; try exact Usp. }
  mf_keep HFr KEEP3 (spZ regs - MF_STK) (spZ regs - 64). clear HF HFr HG.
  lazymatch type of HS2 with st_ok _ _ _ (restrict _ ?msB) =>
    prreg HS2 (10%bv : bv 5) U10; prreg HS2 (11%bv : bv 5) U11; prreg HS2 (12%bv : bv 5) U12;
    prreg HS2 (1%bv : bv 5) U1; prreg HS2 (2%bv : bv 5) U2; prreg HS2 (3%bv : bv 5) U3; prreg HS2 (4%bv : bv 5) U4;
    assert (Hsp2 : spZ (ms_regs msB) = spZ regs + -64) by (unfold spZ at 1; rewrite U2, Usp; lia);
    assert (V10 : getr (ms_regs msB) 10 = w64 (c + 256 * Z.of_nat k))
      by (rewrite U10, (EE 8%nat 8%bv eq_refl); exact R8);
    assert (V11 : getr (ms_regs msB) 11 = w64 name)
      by (rewrite U11, (EE 18%nat 18%bv eq_refl); exact R18);
    assert (V12 : getr (ms_regs msB) 12 = w64 n)
      by (rewrite U12, (EE 9%nat 9%bv eq_refl); exact R9);
    assert (V3 : getr (ms_regs msB) 3 = w64 (as_gp B))
      by (rewrite U3, (EE 3%nat 3%bv eq_refl), (RK 3%bv ltac:(kin)); exact Hgp);
    assert (V4 : getr (ms_regs msB) 4 = w64 (as_tp B))
      by (rewrite U4, (EE 4%nat 4%bv eq_refl), (RK 4%bv ltac:(kin)); exact Htp);
    assert (Hraw : YK0s.ret_ok (getr (ms_regs msB) 1)) by (rewrite U1; apply ret_ok_codeptr_v; [lia | reflexivity]);
    pose proof (kept_out_trans _ _ _ _ _ _ _ (kept_out_trans _ _ _ _ _ _ _ HK KEEPa ltac:(lia) ltac:(lia)) KEEP3
      ltac:(lia) ltac:(lia)) as KEEPU;
    pose proof (aread_ok_of_block SEGS B LAWS ESTACK ly S W (ms_regs msB) (ms_mem msB) _ b m (c + 256 * Z.of_nat k) n
      (proj1 HJ2) Hin ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite Hsp2; lia)) as (Hx0 & Hxn & Hn32 & HMx & AMx & RAx & HVx);
    destruct (mf_name_at _ KEEPU) as (RNy & RAy & HVy);
    assert (SRCx : src_ok SEGS W (ms_regs msB) (ms_mem msB) (c + 256 * Z.of_nat k) n)
      by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; exact (HMx a Ha));
    assert (SRCy : src_ok SEGS W (ms_regs msB) (ms_mem msB) name n)
      by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; split;
          [ replace a with (name + Z.of_nat (Z.to_nat (a - name))) by lia; rewrite (RNy (Z.to_nat (a - name)) ltac:(lia)); discriminate
          | rewrite Hsp2; pose proof (Hnlow ltac:(lia)); lia ]);
    assert (WINx : forall a, c + 256 * Z.of_nat k <= a < c + 256 * Z.of_nat k + n -> ~ (spZ regs + -64 - 2 * ESTACK <= a < spZ regs + -64))
      by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; lia);
    assert (WINy : forall a, name <= a < name + n -> ~ (spZ regs + -64 - 2 * ESTACK <= a < spZ regs + -64))
      by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; pose proof (Hnlow ltac:(lia)); lia);
    assert (CMP : (forall i, 0 <= i < n -> rdW W (ms_mem msB) (c + 256 * Z.of_nat k + i) = rdW W (ms_mem msB) (name + i)) <->
        ms_name (nth k (mc_seg mc) mseg_d) = seg_spec.zs l)
      by (rewrite <- Hzs; apply (mf_cmp _ _ _ sb l n); [lia | exact HLn | | exact RNy];
          let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; rewrite (KEEPU _) by lia; destruct STR0 as [STRb _];
          rewrite (STRb i ltac:(rewrite length_app; cbn [length]; lia)); rewrite app_nth1 by exact Hi; reflexivity);
    pmkst HS2;
    eapply SRr_bind;
    [ eapply (aj_bcmp_at SEGS B LAWS pa_segs_low _ (ABCMP fx) W (ms_regs msB) (ms_mem msB) MF_STK (spZ regs) [] ly S W mem md
        [] ly S _ 0 (c + 256 * Z.of_nat k) name n (-64) _ HJ2 V10 V11 V12 Hn32 Hx0 Hxn Hy0 Hyn Hsp2 eq_refl
        ltac:(lia) ltac:(rewrite HST, Hes; lia) V3 V4 U1);
      [ rewrite <- U1; exact Hraw | exact SRCx | exact SRCy | exact WINx | exact WINy | exact AMx | exact AMy
      | exact RAx | exact HVx | exact RAy | exact HVy ]
    | ]
  end.
  cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & v & -> & HJ3 & HP3 & Hv & Hcmp & HK3 & Hpres3).
  lazymatch type of HK3 with forall a, _ -> _ -> aview _ _ mem3 a = aview _ _ ?mU a =>
    assert (KEEPb : kept_out (rdW W mU) (rdW W mem3) (spZ regs - MF_STK) (spZ regs - 64))
      by (let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in intros a Ha Hn; apply HK3; [exact Ha | lia]) end.
  pose proof (kept_out_trans _ _ _ _ _ _ _ (kept_out_trans _ _ _ _ _ _ _ KEEPa KEEP3 ltac:(lia) ltac:(lia)) KEEPb
    ltac:(lia) ltac:(lia)) as KEEPd.
  clear KEEPb HK3.
  (* back at 0x87594: beqz a0 *)
  mf_after HS2 1040%nat W regs3 mem3 HP3 HS3.
  pose proof (bv_unsigned_in_range 64 v) as HRv. change (bv_modulus 64) with (2 ^ 64) in HRv.
  lazymatch type of HS3 with st_ok_pi _ _ ?E2 _ _ =>
    assert (HEI2 : img_env VAL A_LIM E2) by (apply img_env_havoc_hi; [exact HEI1 | cbv; lia]);
    assert (HAE2 : env_agree 32 (Ereg regs1 []) E2) by (apply env_agree_havoc_ge; [cbv; lia | exact HAE1]);
    assert (A2 : ew E2 1044 = Z_to_bv 64 (bv_unsigned v))
      by (change 1044%nat with (1040 + 4)%nat; rewrite (ew_havoc_new _ 1040 _ 4 (Z_to_bv 64 0)) by (cbn; lia);
          unfold CLOB; cbn [map nth]; rewrite Hv; symmetry; apply Z_to_bv_bv_unsigned)
  end.
  clear HS2 HJ2.
  psrr_branch_pi RUNP BR HS3.
  + (* bcmp answered 0: the names agree, the result is &c->seg[k] *)
    rewrite branch_eq_U, (U_atom _ 1044 (bv_unsigned v) A2 HRv), U_lit in Hc by lia.
    apply Z.eqb_eq in Hc.
    assert (Hv0 : v = w64 0) by (apply bv_eq; unfold w64; rewrite unsigned_lit_small by lia; exact Hc).
    pose proof (proj1 CMP (proj1 Hcmp Hv0)) as HEQ.
    assert (ET : SegModel.leqb (ms_name (nth k (mc_seg mc) mseg_d)) (seg_spec.zs l) = true) by (apply leqb_eq; exact HEQ).
    rewrite ET in STEP. cbv iota in STEP.
    paj_run_to_shc RUNTOP HS3 HJ3 MF_EPI.
    { awr_ok_tac; try exact Usp. }
    mf_keep HFr KEEP4 (spZ regs - MF_STK) (spZ regs - 64). clear HF HFr HG.
    pmkst HS3.
    prreg HS3 (2%bv : bv 5) Q2. prreg HS3 (8%bv : bv 5) Q8.
    apply (mf_epi (c + 256 * Z.of_nat k)).
    * apply (mf_cut_kept regs1 mem1 md1 _ _ _ HCUT HJ3 (kept_out_trans _ _ _ _ _ _ _ KEEPd KEEP4 ltac:(lia) ltac:(lia))).
      -- rewrite Q2, (EE 2%nat 2%bv eq_refl). reflexivity.
      -- intros r Hr. lazymatch type of HS3 with st_ok_pi _ _ ?Ex ?ssx ?msx =>
           exact (regs_kept_of_st_ok_pi Ex ssx msx regs1 [] mf_kregs HS3 HAE2 ltac:(vm_compute; reflexivity) r Hr) end.
    * rewrite Q8, (EE 8%nat 8%bv eq_refl). exact R8.
    * unfold m_find_ptr. rewrite Hmod, STEP. unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE. reflexivity.
  + (* bcmp answered nonzero: entry k rejected, to NX *)
    rewrite branch_eq_U, (U_atom _ 1044 (bv_unsigned v) A2 HRv), U_lit in Hc by lia.
    apply Z.eqb_neq in Hc.
    assert (EL : SegModel.leqb (ms_name (nth k (mc_seg mc) mseg_d)) (seg_spec.zs l) = false).
    { destruct (SegModel.leqb _ _) eqn:EQ; [|reflexivity]. exfalso. apply leqb_eq in EQ.
      apply Hc. rewrite (proj2 Hcmp (proj2 CMP EQ)). reflexivity. }
    rewrite EL in STEP. cbv iota in STEP.
    paj_run_to_shc RUNTOP HS3 HJ3 MF_NX.
    { awr_ok_tac; try exact Usp. }
    mf_keep HFr KEEP4 (spZ regs - MF_STK) (spZ regs - 64). clear HF HFr HG.
    pmkst HS3.
    prreg HS3 (2%bv : bv 5) Q2. prreg HS3 (8%bv : bv 5) Q8. prreg HS3 (9%bv : bv 5) Q9.
    prreg HS3 (18%bv : bv 5) Q18. prreg HS3 (19%bv : bv 5) Q19. prreg HS3 (20%bv : bv 5) Q20.
    prreg HS3 (21%bv : bv 5) Q21. prreg HS3 (22%bv : bv 5) Q22.
    apply NXT.
    split; [|split; [exact Hk|split; [rewrite Hmod; exact STEP|]]].
    * apply (mf_cut_kept regs1 mem1 md1 _ _ _ HCUT HJ3 (kept_out_trans _ _ _ _ _ _ _ KEEPd KEEP4 ltac:(lia) ltac:(lia))).
      -- rewrite Q2, (EE 2%nat 2%bv eq_refl). reflexivity.
      -- intros r Hr. lazymatch type of HS3 with st_ok_pi _ _ ?Ex ?ssx ?msx =>
           exact (regs_kept_of_st_ok_pi Ex ssx msx regs1 [] mf_kregs HS3 HAE2 ltac:(vm_compute; reflexivity) r Hr) end.
    * split; [rewrite Q8, (EE 8%nat 8%bv eq_refl); exact R8|].
      split; [rewrite Q9, (EE 9%nat 9%bv eq_refl); exact R9|].
      split; [rewrite Q18, (EE 18%nat 18%bv eq_refl); exact R18|].
      split; [rewrite Q19, (EE 19%nat 19%bv eq_refl); exact R19|].
      split; [rewrite Q20, (EE 20%nat 20%bv eq_refl); exact R20|].
      split; [rewrite Q21, (EE 21%nat 21%bv eq_refl); exact R21|].
      rewrite Q22, (EE 22%nat 22%bv eq_refl). exact R22.
Qed.

(* ---------------- the loop, by induction on the entries left ---------------- *)
Lemma mf_loop : forall dd k, (k + Datatypes.S dd = length (mc_seg mc))%nat -> forall r m d, mf_LH k r m d ->
SRr SEGS W (mkCfg (mkst r (Z_to_bv 64 (BASE + MF_LH)) m (seg_rom SEGS)) d) mf_Q.
Proof.
induction dd as [|dd IH]; intros k Hd r m d HLH.
- apply (mf_lh k r m d); [|exact HLH]. intros r' m' d' HNX. apply (mf_nx k r' m' d'); [intros Hk; lia | exact HNX].
- apply (mf_lh k r m d); [|exact HLH]. intros r' m' d' HNX. apply (mf_nx k r' m' d'); [|exact HNX].
  intros _ r'' m'' d'' HLH'. apply (IH (Datatypes.S k)); [lia | exact HLH'].
Qed.

(* ---------------- the entry: 0x874f4 .. the blez, then NONE or LH ---------------- *)
Lemma mf_stack_field : forall E H mem' cs off n0 v,
region_ok SEGS E (mrestrict H mem') (YP09.mkRegion (Some 2%nat) (-64) 0 (-64) 0 cs) -> bv_unsigned (ew E 2) = spZ regs ->
In (YP09.mkChunk off (CVal 8 (SOff n0 0))) cs -> ew E n0 = w64 v -> 0 <= v < 2 ^ 64 ->
sa_val (aview SEGS H mem') (spZ regs + off) 8 v.
Proof.
intros E H mem' cs off n0 v HR Hsp Hin Hn Hv. apply mf_sa_of_val.
change 8%nat with (N.to_nat 8).
apply (field_of_region E _ 2 (spZ regs) cs (-64) 0 (-64) 0 off 8 (SOff n0 0) v HR Hsp Hin).
- cbn [sv_denot]. rewrite Hn, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Hv.
- cbn. lia.
Qed.
(* the range [q, q + n) lies off the shadow band *)
Lemma mf_app_of_amem : forall q n0, amem_range q n0 ->
forall x, q <= x < q + n0 -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416).
Proof. intros q n0 Ha x Hx. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ha. unfold SHADOW_OFF. lia. Qed.
Lemma mf_entry_seed : forall N, 0 <= N <= 32 -> sa_val (rdW W mem) (c + seg_spec.MC_N) 4 N ->
st_ok_pi SEGS VAL (mf_E regs N) ss_mf0 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_m_find)) mem (seg_rom SEGS)))
/\ sh_ok SEGS MFx mf_SH (mf_E regs N) (mrestrict (w_H W) mem).
Proof.
intros N RN FN.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HST : MF_STK = 8256) by reflexivity.
destruct mf_blk as (b & m & Hin & Hb1 & Hb2 & Hc4096 & Hcc).
pose proof (blk_off_imgP B ly S W mem md b m HAR Hin) as Hoff. unfold off_img in Hoff.
destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & _ & _ & _ & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [_ Hrq].
destruct HMP as (_ & Hc16 & _ & _ & (Hc0 & Hc63 & AMc & ZC & _) & _).
pose proof (mf_app_of_amem _ _ AMc) as AC.
assert (Rc : 0 <= c <= MF_CHI) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in AMc; unfold MF_CHI, seg_spec.SEG_M_SIZE in *; lia).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (pal_got_cell B TL) as HGC.
pose proof (pa_obj_img 0 ltac:(lia)) as HO0. pose proof (pa_obj_img 12 ltac:(lia)) as HO12.
unfold MF_CHI, kImgEnd, seg_spec.SEG_M_SIZE in *.
set (E := mf_E regs N).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mf_E; apply Eimg_env).
assert (EL : forall n0, (n0 < A_TEXT)%nat -> ew E n0 = ew (Ereg regs (mf_extra N)) n0)
  by (intros n0 Hn0; subst E; unfold mf_E; apply Eimg_low; exact Hn0).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 c) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 MF_SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 N) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (EO0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; unfold mf_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; unfold mf_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n0 v, ew E n0 = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n0) = v).
{ intros n0 v Hn0 Hv. cbn [base_val]. rewrite Hn0. apply unsigned_lit_small. exact Hv. }
pose proof (pa_val_range (A_OBJ 0)) as RV0. pose proof (pa_val_range (A_OBJ 12)) as RV12.
split.
- unfold ss_mf0. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + subst E. unfold mf_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold mf_regions, mf_rN, stack_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * rewrite (VB 10%nat c E10) by lia. unfold seg_spec.MC_N. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ c 0x2000 4 _ N); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      exact (mf_val_of_sa SEGS _ mem _ 4 N FN).
    * rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO0) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
        [cbn [sv_denot]; rewrite EO12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
    * rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) EO12) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) MF_SB);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold MF_SB; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
  + apply pairwise_disjoint_of_extents. unfold mf_regions, mf_rN, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 10%nat c E10), (VB (A_OBJ 0) (VAL (A_OBJ 0)) EO0), (VB (A_OBJ 12) (VAL (A_OBJ 12)) EO12) by lia.
    cbn [base_val]. rewrite Usp. unfold seg_spec.MC_N.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert HST Hslo Hshi H47 Hceil C1 Hstk0 Hcc Hoff Hb1 Hb2 Hrq HGC HO0 HO12 Rc. clear. intros. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [mf_facts f_atoms atoms_ok]. unfold afact_ok, mf_spF, MF_CHI, seg_spec.SEG_M_SIZE. cbn [af_lo af_hi af_al2].
    rewrite Usp, E10, E32, E33, !unsigned_lit_small by (unfold MF_SB; lia).
    unfold MF_SB. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hslo Hshi H47 Hceil Hal16 C1 Hstk0 Rc Hc16 RN. clear. intros.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity].
- unfold sh_ok, mf_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem E MFx 10 c 9236 c 0 9236 ZC).
  + unfold U, MFx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold MF_SB; lia). reflexivity.
  + unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
  + lia. + lia.
  + intros x Hx. apply AC. cbn in Hx. lia.
Qed.

Lemma mf_entry : SRr SEGS W (cfg_at SEGS (BASE + AF_m_find) regs mem md) mf_Q.
Proof.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof mf_sp as (Hal16 & Hslo & Hshi & Hlo).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HST : MF_STK = 8256) by reflexivity.
pose proof mf_N32 as H32. pose proof mf_Rc as Rc. unfold MF_CHI, seg_spec.SEG_M_SIZE in Rc.
destruct mf_blk as (b & m & Hin & Hb1 & Hb2 & Hc4096 & Hcc).
(* c->n: mconf_encp's u32 field at MC_N *)
destruct mf_mc as (bs & HB & HE). pose proof HE as (HL & _ & _ & HNf & _).
set (N := Z.of_nat (length (mc_seg mc))) in *.
assert (HNdef : N = Z.of_nat (length (mc_seg mc))) by reflexivity.
assert (RN : 0 <= N <= 32) by lia.
pose proof (mf_fld _ c bs seg_spec.MC_N N HB ltac:(unfold seg_spec.MC_N; lia)
  ltac:(unfold seg_spec.MC_N, seg_spec.SEG_M_SIZE in *; lia) HNf) as FN.
clearbody N.
destruct (mf_entry_seed N RN FN) as [HS SHOK].
pose proof (ajournal_init SEGS B MF_STK [] ly S W regs mem md ch HPRE) as HJ.
assert (HEI : img_env VAL A_LIM (mf_E regs N)) by (unfold mf_E; apply Eimg_env).
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew (mf_E regs N) n0 = getr regs r)
  by (intros n0 r Hn0; unfold mf_E; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (E33 : ew (mf_E regs N) 33 = Z_to_bv 64 N)
  by (unfold mf_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E10 : ew (mf_E regs N) 10 = Z_to_bv 64 c) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
assert (HAE : env_agree 32 (Ereg regs (mf_extra N)) (mf_E regs N))
  by (split; [intros n0 Hn0; unfold mf_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
remember (mf_E regs N) as E eqn:HEq. clear HEq.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
unfold cfg_at. change (w64 (BASE + AF_m_find)) with (Z_to_bv 64 (BASE + AF_m_find)).
(* 0x874f4 .. 0x87554: the frame, the alignment trap (decided false by c mod 16 = 0), the shadow base, c->n and
   its check (vanishes: c's shadow entry), a0 := c->n, stopped at blez a0 *)
paj_run_tok RUN HS HJ SHOK MFspan.
{ awr_ok_tac. exact Usp. }
try (cbn [ms_mem mkst] in HFr). mf_keep HFr KEEP0 (spZ regs - MF_STK) (spZ regs). clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK MFspan.
- (* c->n <= 0: no entry; NONE, a0 := 0, the epilogue and the ret *)
  assert (HN0 : length (mc_seg mc) = 0%nat).
  { lazymatch type of Hc with context [branch_taken BC_GE _ (sv_denot _ ?e)] =>
      assert (UE : U E e = N) by (first [ apply (mf_U_sext E 33 N E33); lia | apply (U_atom E 33 N E33); lia ]) end.
    rewrite (mf_bge0 E _ N UE) in Hc by lia. apply Z.leb_le in Hc. lia. }
  clear Hc.
  paj_run_tok RUN HS HJ SHOK MFspan.
  { awr_ok_tac. exact Usp. }
  try (cbn [ms_mem mkst] in HFr). mf_keep HFr KEEP1 (spZ regs - MF_STK) (spZ regs). clear HF HFr HG.
  prreg HS (1%bv : bv 5) F1. prreg HS (10%bv : bv 5) F10.
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. unfold mf_Q, apost_base.
  lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly, S, r, m, d end.
  split; [rewrite F1, (EE 1%nat 1%bv eq_refl); unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
  split; [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ|].
  split; [eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs (mf_extra N) HS); [exact HAE | vm_compute; reflexivity]|].
  split.
  { rewrite F10. unfold m_find_ptr, SegModel.m_find. destruct (mc_seg mc) as [|g segs]; [reflexivity | cbn in HN0; lia]. }
  split.
  { intros a Ha Hn _. rewrite (KEEP1 a Ha Hn). exact (KEEP0 a Ha Hn). }
  split; [apply Permutation_refl | split; [reflexivity | exists (st_fs S); destruct S; reflexivity]].
- (* c->n > 0: the cursors, then LH with k = 0 *)
  assert (UE : U E (SOff 33 0) = N) by (apply (U_atom E 33 N E33); lia).
  assert (HN : (0 < length (mc_seg mc))%nat).
  { lazymatch type of Hc with context [branch_taken BC_GE _ (sv_denot _ ?e)] =>
      assert (UE' : U E e = N) by (first [ apply (mf_U_sext E 33 N E33); lia | apply (U_atom E 33 N E33); lia ]) end.
    rewrite (mf_bge0 E _ N UE') in Hc by lia. apply Z.leb_gt in Hc. lia. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK MFspan MF_LH.
  { awr_ok_tac. exact Usp. }
  try (cbn [ms_mem mkst] in HFr). mf_keep HFr KEEP1 (spZ regs - MF_STK) (spZ regs). clear HF HFr HG.
  pmkst HS.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
    let r := eval vm_compute in (nth 0 (ss_mem ssx) (stack_region 0)) in
    pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 0 r HS ltac:(vm_compute; reflexivity)) as HRg;
    cbn [ms_mem restrict] in HRg end.
  prreg HS (2%bv : bv 5) P2. prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18.
  prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21.
  prreg HS (22%bv : bv 5) P22.
  rewrite (mf_alu_not (ew E 10) c ltac:(rewrite E10; apply unsigned_lit_small; lia) ltac:(lia)) in P20.
  rewrite (mf_alu_sel (ew E 33) N ltac:(rewrite E33; apply unsigned_lit_small; lia) ltac:(lia)) in P21.
  apply (mf_loop (length (mc_seg mc) - 1) 0); [lia|].
  split; [split; [exact HJ|split; [|split; [|split]]]|].
  + intros a Ha Hn. rewrite (KEEP1 a Ha Hn). exact (KEEP0 a Ha Hn).
  + intros j r Hr.
    assert (Hr' : 1 <= r <= 22) by (apply nth_error_In in Hr; cbn in Hr; intuition lia).
    replace (spZ regs - 8 - 8 * Z.of_nat j) with (spZ regs + (-8 - 8 * Z.of_nat j)) by lia.
    apply (mf_stack_field E _ _ _ _ (Z.to_nat r) _ HRg Usp).
    * do 8 (destruct j as [|j]; [cbn in Hr; injection Hr as <-; vm_compute; repeat first [left; reflexivity | right] |]).
      cbn in Hr; destruct j; discriminate Hr.
    * rewrite (EE (Z.to_nat r) (Z_to_bv 5 r)); [unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
      rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia.
    * pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HRr. change (bv_modulus 64) with (2 ^ 64) in HRr. exact HRr.
  + rewrite P2, Usp. unfold w64. f_equal; lia.
  + intros r Hr. lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
      exact (regs_kept_of_st_ok_pi Ex ssx msx regs (mf_extra N) mf_kregs HS HAE ltac:(vm_compute; reflexivity) r Hr) end.
  + split; [exact HN|]. split; [reflexivity|].
    split; [rewrite P8, (EE 10%nat 10%bv eq_refl), H10; f_equal; lia|].
    split; [rewrite P9, (EE 12%nat 12%bv eq_refl); exact H12|].
    split; [rewrite P18, (EE 11%nat 11%bv eq_refl); exact H11|].
    split; [rewrite P19; unfold w64; f_equal; lia|].
    split; [rewrite P20; reflexivity|].
    split; [rewrite P21; unfold w64; f_equal; lia|].
    rewrite P22; unfold w64; f_equal; lia.
Qed.
End w.

(* the contract at image B's entry, stack and read-only window *)
Theorem m_find_walkB : m_find_contract SEGS B (BASE + AF_m_find) SegInstB.STK_m_find SegInstB.RLO_A SegInstB.RHI_A.
Proof.
unfold m_find_contract.
intros ly S W regs mem md ch c name n mc l HPRE HROD H10 Hc64 H11 Hname64 H12 Hn64 HMP HEV.
eapply mf_entry; eassumption.
Qed.
End e.
End f.
End d.
About m_find_walkB.
Print Assumptions m_find_walkB.
