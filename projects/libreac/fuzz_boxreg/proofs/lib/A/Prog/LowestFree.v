(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8n.v:1199-1201
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-202, 358-363, 390-392 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:207-209 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC59.v:27-30 [Apache-2.0 OR MIT], for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8k.v:388-389. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_identity_reac_ver_str.v, with its module paths and module names changed; 621 of its 678 lines of code are new or changed and 1017 lines of the source are left out. *)
(* lowest_free (fuzz_boxreg.asan 0x81524, 36 instructions): the contract of the ASan build's code. lowest_free is a
   static function of the harness (fuzz/fuzz_boxreg.c:107-113).
   The function takes a 64-byte frame on the machine stack (addi sp,sp,-64; it saves ra and s0..s5 there) and has no
   ASan check of its own. It returns -1 in a0 (addi s0,zero,-1) when fabric (a2) < nch (a1) (bltu at 0x81548);
   else, for base = 0, 1, ..., fabric - nch (the count fabric - nch + 1 is subw / addiw at 0x8155c .. 0x81560), it
   calls range_free (t, base, nch, fabric) (jal at 0x81574; lib/A/Prog/RangeFree.v, whose contract the proof takes as
   a Section hypothesis at BASE + AF_range_free) and returns the first base that range_free reports free, or -1
   when none is. The result is Pau's lowest_free_res of lib/Prog/lowest_free_c.v, used as it is with range_free_ok of
   lib/Prog/range_free_c.v and the model of lib/Prog/Boxreg.v. It reads nothing itself (the table t in a0 is passed
   to range_free unread) and writes nothing outside its own frame and range_free's.
   Where the table lies: the harness's local struct reac_boxreg prev, the registry copy at offset 0x40 of its
   416-byte side-stack frame block (a0 = ld 0x78(s1) at the calls 0x80934 (0x80928) and 0x80d0c (0x80d00) of
   LLVMFuzzerTestOneInput; see lib/A/Prog/RangeFree.v), so the premise is range_free's: afobj SEGS B ly S W mem t 288
   with the 288 bytes bs of t.
   Stack: its own 64 bytes and range_free's RANGE_FREE_STK below them.
   Hazards.
   (1) The struct is 288 bytes (rows 0..280 with stride 56, n at +280, fabric at +284).
   (2) afobj holds only on the fake-stack path of the harness (lib/A/Prog/RangeFree.v hazard (2)).
   (3) The test fabric < nch is unsigned (bltu) and the count fabric - nch + 1 and base + 1 (addiw at 0x8157c) are
       32-bit; 1 <= nch <= 40 and 1 <= fabric <= 40 make them the signed C loop `base <= fabric - nch`.
   (4) range_free's premises at each call: base in 0 .. fabric - nch, nch and fabric as given, afobj and the bytes of
       t, boxreg_B1..B3; afobj and the bytes are those of this function's pre, kept by range_free's journal (it
       keeps frames S, the frames' bytes and their shadow outside its footprint [], lib/Reusable/YCbq.v ajournal).
   (5) No f* or csr instruction occurs in the 36 instructions (measured), so the fixed {fx} is sound.
   (6) The model premises are those of the old walk (a working branch 67b70ae1ec3
       proofs/libreac/fuzz_boxreg/lib/A/Prog/lowest_free_c.v). The harness meets them from check (r, fabric) on the
       registry it copied (boxreg_B16), from legal_width (2 <= nch <= 40) and from its fabric (1..40).
   Image difference: the asan-ubsan build has no lowest_free function: it inlines the loop into
   LLVMFuzzerTestOneInput (0x80910 .. 0x80950 and 0x80960 .. 0x809a0, calling range_free at 0x80940 / 0x80994,
   lib/B/Prog/BoxBRangeFree.v), so there is no B twin of this file. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow BoxSyms BoxList BoxPa.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaJournal BoxBase.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require ReacBoxregInit.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import RangeFree.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg lowest_free_c.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import BoxPaLib YC1g YC1h YC4b YC85.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg box_listing}.
#[local] Notation SEGS := (@pa_segs _ box_listing PI).
#[local] Notation BASE := (@pa_val _ box_listing PI A_TEXT).
(* The function's address in the image and the stack it needs: its own 64-byte frame and range_free's stack (its
   16-byte frame and ESTACK) below it. *)
Definition A_lowest_freeP : Z := BASE + AF_lowest_free.
Definition LOWEST_FREE_STK : Z := 64 + RANGE_FREE_STK.
Section h.
Variable B : asyms.
Definition tlowest_free_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md (nch fabric : Z) (bs : list byte)
  : world SEGS -> config -> Prop :=
apost_base SEGS B LOWEST_FREE_STK [] regs ly S W mem md 0
(fun ly' S' W' regs' mem' md' =>
ly' = ly /\ S' = S /\ W' = W /\
exists z, getr regs' 10 = w64 z /\ lowest_free_c.lowest_free_res bs nch fabric z).
Definition tlowest_free_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (t nch fabric : Z) (bs : list byte),
afn_pre SEGS B LOWEST_FREE_STK ly S W regs mem md ch ->
getr regs 10 = w64 t -> getr regs 11 = w64 nch -> getr regs 12 = w64 fabric ->
1 <= nch <= 40 -> 1 <= fabric <= 40 ->
afobj SEGS B ly S W mem t ReacBoxregInit.REG_SIZE -> length bs = 288%nat ->
(forall i, 0 <= i < ReacBoxregInit.REG_SIZE ->
  aview SEGS (w_H W) mem (t + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) ->
Boxreg.boxreg_B1 bs -> Boxreg.boxreg_B2 bs -> Boxreg.boxreg_B3 bs ->
SRr SEGS W (cfg_at SEGS A_lowest_freeP regs mem md) (tlowest_free_post regs ly S W mem md nch fabric bs).
(* The walk. range_free's contract enters as the Section hypothesis RF of exactly its type trange_free_spec
   (lib/A/Prog/RangeFree.v), at BASE + AF_range_free: the listing's call slot is PCall BS_range_free and
   pa_sigma_range_free (BoxPa.v, from pa_xcalls) moves it to that address; YC85.v cl_callS composes its journal into
   this function's. The proof has three parts:
   - lf_entry and the first run: the prologue and the test fabric < nch (bltu at 0x81548). When it is taken the
     epilogue returns -1 at once.
   - lf_loop, by induction on the count of bases left (fabric - nch + 1 - base): a fresh symbolic state at the loop
     head 0x81564 (lf_head_ok: the registers are its first atoms, the saved ra and s0 .. s5 are atoms 32 .. 38 in the
     frame region), the run to the call, the call (cl_callS with RF; the table and its shadow stay as the entry had
     them by range_free's journal, lf_obj_kept), the state after the call (jafter_call_keep_pi; the frame region is
     kept, region_kept_stack_sub), then a0 = 1 returns base, a0 = 0 either goes back to the loop head with base + 1
     (bne at 0x81580) or, after the last base, returns -1.
   - pb_lowest_free: the entry run up to the loop head, then lf_loop with base = 0.
   lowest_free_res is Pau's (lib/Prog/lowest_free_c.v), as the plain walk lib/Prog/lowest_free.v:9 (lowest_free_holds)
   proves it from range_free's contract; the loop's induction follows the old walk's LOOP
   (a working branch 67b70ae1ec3 proofs/libreac/fuzz_boxreg/lib/A/Prog/lowest_free.v:64-114). *)
#[local] Notation VAL := (@pa_val _ box_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ box_listing PI).
Definition LF_SB : Z := 0x7fff8000.
Definition LF_Bx : sv := SLit LF_SB.
Definition LF_Bspan : Z * Z := (LF_SB, LF_SB + 2 ^ 44 - 1).
Definition lf_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition ss_lf0 : sstate := mkSS AF_lowest_free sr_atoms [stack_region 64] None lf_facts.
Definition lf_extra (regs0 : bvmap 5 word) : list word :=
  [getr regs0 1; getr regs0 8; getr regs0 9; getr regs0 18; getr regs0 19; getr regs0 20; getr regs0 21].
Definition lf_loop_region : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 64 0 0
    [YP09.mkChunk 8 (CVal 8 (SOff 38 0)); YP09.mkChunk 16 (CVal 8 (SOff 37 0)); YP09.mkChunk 24 (CVal 8 (SOff 36 0));
     YP09.mkChunk 32 (CVal 8 (SOff 35 0)); YP09.mkChunk 40 (CVal 8 (SOff 34 0)); YP09.mkChunk 48 (CVal 8 (SOff 33 0));
     YP09.mkChunk 56 (CVal 8 (SOff 32 0))].
Definition ss_lfL : sstate := mkSS (AF_lowest_free + 0x40) sr_atoms [lf_loop_region] None lf_facts.
Definition lf_frame (m : word -> option byte) (sp0 : Z) (regs0 : bvmap 5 word) : Prop :=
  val_mem SEGS m (sp0 + -8) 8 (bv_unsigned (getr regs0 1)) /\
  val_mem SEGS m (sp0 + -16) 8 (bv_unsigned (getr regs0 8)) /\
  val_mem SEGS m (sp0 + -24) 8 (bv_unsigned (getr regs0 9)) /\
  val_mem SEGS m (sp0 + -32) 8 (bv_unsigned (getr regs0 18)) /\
  val_mem SEGS m (sp0 + -40) 8 (bv_unsigned (getr regs0 19)) /\
  val_mem SEGS m (sp0 + -48) 8 (bv_unsigned (getr regs0 20)) /\
  val_mem SEGS m (sp0 + -56) 8 (bv_unsigned (getr regs0 21)).
(* The frame region the entry run leaves at the loop head (base: the entry sp). *)
Definition lf_entry_region : YP09.region :=
  YP09.mkRegion (Some 2%nat) (-64) 0 (-64) 0
    [YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
     YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
     YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
     YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].
Lemma lf_getr5 : forall (regs : bvmap 5 word) (n : Z) (r : bv 5), bv_unsigned r = n -> getr regs (Z_to_bv 5 n) = getr regs r.
Proof. intros regs n r H. subst n. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma lf_aregs : forall (regs0 regs' : bvmap 5 word),
  getr regs' 2 = getr regs0 2 -> getr regs' 3 = getr regs0 3 -> getr regs' 4 = getr regs0 4 ->
  getr regs' 8 = getr regs0 8 -> getr regs' 9 = getr regs0 9 -> getr regs' 18 = getr regs0 18 ->
  getr regs' 19 = getr regs0 19 -> getr regs' 20 = getr regs0 20 -> getr regs' 21 = getr regs0 21 ->
  getr regs' 22 = getr regs0 22 -> getr regs' 23 = getr regs0 23 -> getr regs' 24 = getr regs0 24 ->
  getr regs' 25 = getr regs0 25 -> getr regs' 26 = getr regs0 26 -> getr regs' 27 = getr regs0 27 ->
  aregs_preserved regs0 regs'.
Proof.
intros regs0 regs' H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 r Hr. unfold acallee_saved in Hr.
assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
  r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
clear Hr.
destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
- rewrite (lf_getr5 regs' 2 2%bv eq_refl), (lf_getr5 regs0 2 2%bv eq_refl). exact H2.
- rewrite (lf_getr5 regs' 3 3%bv eq_refl), (lf_getr5 regs0 3 3%bv eq_refl). exact H3.
- rewrite (lf_getr5 regs' 4 4%bv eq_refl), (lf_getr5 regs0 4 4%bv eq_refl). exact H4.
- rewrite (lf_getr5 regs' 8 8%bv eq_refl), (lf_getr5 regs0 8 8%bv eq_refl). exact H8.
- rewrite (lf_getr5 regs' 9 9%bv eq_refl), (lf_getr5 regs0 9 9%bv eq_refl). exact H9.
- rewrite (lf_getr5 regs' 18 18%bv eq_refl), (lf_getr5 regs0 18 18%bv eq_refl). exact H18.
- rewrite (lf_getr5 regs' 19 19%bv eq_refl), (lf_getr5 regs0 19 19%bv eq_refl). exact H19.
- rewrite (lf_getr5 regs' 20 20%bv eq_refl), (lf_getr5 regs0 20 20%bv eq_refl). exact H20.
- rewrite (lf_getr5 regs' 21 21%bv eq_refl), (lf_getr5 regs0 21 21%bv eq_refl). exact H21.
- rewrite (lf_getr5 regs' 22 22%bv eq_refl), (lf_getr5 regs0 22 22%bv eq_refl). exact H22.
- rewrite (lf_getr5 regs' 23 23%bv eq_refl), (lf_getr5 regs0 23 23%bv eq_refl). exact H23.
- rewrite (lf_getr5 regs' 24 24%bv eq_refl), (lf_getr5 regs0 24 24%bv eq_refl). exact H24.
- rewrite (lf_getr5 regs' 25 25%bv eq_refl), (lf_getr5 regs0 25 25%bv eq_refl). exact H25.
- rewrite (lf_getr5 regs' 26 26%bv eq_refl), (lf_getr5 regs0 26 26%bv eq_refl). exact H26.
- rewrite (lf_getr5 regs' 27 27%bv eq_refl), (lf_getr5 regs0 27 27%bv eq_refl). exact H27.
Qed.
(* A symbolic value whose signed reading is v denotes the word of v. *)
Lemma lf_sv_lit : forall E e v, Sg E e = v -> - 2 ^ 63 <= v < 2 ^ 63 -> sv_denot E e = Z_to_bv 64 v.
Proof.
intros E e v H Hv. apply bv_eq. change (bv_unsigned (sv_denot E e)) with (U E e).
rewrite U_of_S, H, Z_to_bv_unsigned. reflexivity.
Qed.
(* addiw rd, rs, 1 on a small nonnegative value (0x8157c). *)
Lemma lf_addw1 : forall E n b, ew E n = Z_to_bv 64 b -> 0 <= b < 2 ^ 30 ->
  sv_denot E (SAluw ALU_ADD (SOff n 0) (SLit 1)) = Z_to_bv 64 (b + 1).
Proof.
intros E n b H Hb. apply lf_sv_lit; [|lia].
rewrite S_SAluw, U_SOff, U_SLit, H, Z_to_bv_unsigned. cbn [zalu_raw].
unfold zcanon, M64, bv_swrap, bv_wrap.
change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
change (bv_modulus 64) with 18446744073709551616. change (2 ^ 32) with 4294967296.
change (2 ^ 64) with 18446744073709551616.
Z.div_mod_to_equations. lia.
Qed.
(* subw / addiw at 0x8155c .. 0x81560: the count fabric - nch + 1. *)
Lemma lf_cnt : forall E a b, ew E 12 = Z_to_bv 64 a -> ew E 11 = Z_to_bv 64 b -> 1 <= a <= 40 -> 1 <= b <= 40 ->
  sv_denot E (SAluw ALU_ADD (SAluw ALU_SUB (SOff 12 0) (SOff 11 0)) (SLit 1)) = Z_to_bv 64 (a - b + 1).
Proof.
intros E a b Ha Hb Ha1 Hb1. apply lf_sv_lit; [|lia].
rewrite S_SAluw, U_SLit, U_of_S, S_SAluw, !U_SOff, Ha, Hb, !Z_to_bv_unsigned. cbn [zalu_raw].
unfold zcanon, M64, bv_swrap, bv_wrap.
change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
change (bv_modulus 64) with 18446744073709551616. change (2 ^ 32) with 4294967296.
change (2 ^ 64) with 18446744073709551616.
Z.div_mod_to_equations. lia.
Qed.
Lemma lf_post : forall ly S W regs0 mem0 md0 nch fabric bs (regs' : bvmap 5 word) mem' md' z,
  ajournal SEGS B LOWEST_FREE_STK (spZ regs0) [] ly S W mem0 md0 [] ly S W mem' md' 0 ->
  aregs_preserved regs0 regs' -> getr regs' 10 = w64 z -> lowest_free_c.lowest_free_res bs nch fabric z ->
  tlowest_free_post regs0 ly S W mem0 md0 nch fabric bs W (mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom SEGS)) md').
Proof.
intros ly S W regs0 mem0 md0 nch fabric bs regs' mem' md' z HJ HP H10 HR.
unfold tlowest_free_post, apost_base. exists ly, S, regs', mem', md'.
split; [reflexivity|]. split; [exact HJ|]. split; [exact HP|].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. exists z. split; [exact H10 | exact HR].
Qed.
Lemma lf_frame_of_loop : forall E m regs0,
  region_ok SEGS E m lf_loop_region -> bv_unsigned (ew E 2) = spZ regs0 - 64 ->
  ew E 32 = getr regs0 1 -> ew E 33 = getr regs0 8 -> ew E 34 = getr regs0 9 -> ew E 35 = getr regs0 18 ->
  ew E 36 = getr regs0 19 -> ew E 37 = getr regs0 20 -> ew E 38 = getr regs0 21 ->
  lf_frame m (spZ regs0) regs0.
Proof.
intros E m regs0 HR Hb H32 H33 H34 H35 H36 H37 H38. unfold lf_loop_region in HR.
assert (Rg : forall w : word, 0 <= bv_unsigned w < 2 ^ (8 * Z.of_N 8)).
{ intros w. pose proof (bv_unsigned_in_range 64 w) as H. change (bv_modulus 64) with (2 ^ 64) in H.
  change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact H. }
unfold lf_frame.
repeat split.
- pose proof (field_of_region E m 2 _ _ _ _ _ _ 56 8%N (SOff 32 0) (bv_unsigned (getr regs0 1)) HR Hb ltac:(cbn [In]; auto 10)
    ltac:(cbn [sv_denot]; rewrite H32, Z.add_0_r; reflexivity) (Rg _) ltac:(lia)) as V.
  replace (spZ regs0 - 64 + 56) with (spZ regs0 + -8) in V by lia. exact V.
- pose proof (field_of_region E m 2 _ _ _ _ _ _ 48 8%N (SOff 33 0) (bv_unsigned (getr regs0 8)) HR Hb ltac:(cbn [In]; auto 10)
    ltac:(cbn [sv_denot]; rewrite H33, Z.add_0_r; reflexivity) (Rg _) ltac:(lia)) as V.
  replace (spZ regs0 - 64 + 48) with (spZ regs0 + -16) in V by lia. exact V.
- pose proof (field_of_region E m 2 _ _ _ _ _ _ 40 8%N (SOff 34 0) (bv_unsigned (getr regs0 9)) HR Hb ltac:(cbn [In]; auto 10)
    ltac:(cbn [sv_denot]; rewrite H34, Z.add_0_r; reflexivity) (Rg _) ltac:(lia)) as V.
  replace (spZ regs0 - 64 + 40) with (spZ regs0 + -24) in V by lia. exact V.
- pose proof (field_of_region E m 2 _ _ _ _ _ _ 32 8%N (SOff 35 0) (bv_unsigned (getr regs0 18)) HR Hb ltac:(cbn [In]; auto 10)
    ltac:(cbn [sv_denot]; rewrite H35, Z.add_0_r; reflexivity) (Rg _) ltac:(lia)) as V.
  replace (spZ regs0 - 64 + 32) with (spZ regs0 + -32) in V by lia. exact V.
- pose proof (field_of_region E m 2 _ _ _ _ _ _ 24 8%N (SOff 36 0) (bv_unsigned (getr regs0 19)) HR Hb ltac:(cbn [In]; auto 10)
    ltac:(cbn [sv_denot]; rewrite H36, Z.add_0_r; reflexivity) (Rg _) ltac:(lia)) as V.
  replace (spZ regs0 - 64 + 24) with (spZ regs0 + -40) in V by lia. exact V.
- pose proof (field_of_region E m 2 _ _ _ _ _ _ 16 8%N (SOff 37 0) (bv_unsigned (getr regs0 20)) HR Hb ltac:(cbn [In]; auto 10)
    ltac:(cbn [sv_denot]; rewrite H37, Z.add_0_r; reflexivity) (Rg _) ltac:(lia)) as V.
  replace (spZ regs0 - 64 + 16) with (spZ regs0 + -48) in V by lia. exact V.
- pose proof (field_of_region E m 2 _ _ _ _ _ _ 8 8%N (SOff 38 0) (bv_unsigned (getr regs0 21)) HR Hb ltac:(cbn [In]; auto 10)
    ltac:(cbn [sv_denot]; rewrite H38, Z.add_0_r; reflexivity) (Rg _) ltac:(lia)) as V.
  replace (spZ regs0 - 64 + 8) with (spZ regs0 + -56) in V by lia. exact V.
Qed.
Lemma lf_frame_of_entry : forall E m regs0,
  region_ok SEGS E m lf_entry_region -> bv_unsigned (ew E 2) = spZ regs0 ->
  ew E 1 = getr regs0 1 -> ew E 8 = getr regs0 8 -> ew E 9 = getr regs0 9 -> ew E 18 = getr regs0 18 ->
  ew E 19 = getr regs0 19 -> ew E 20 = getr regs0 20 -> ew E 21 = getr regs0 21 ->
  lf_frame m (spZ regs0) regs0.
Proof.
intros E m regs0 HR Hb H1 H8 H9 H18 H19 H20 H21. unfold lf_entry_region in HR.
assert (Rg : forall w : word, 0 <= bv_unsigned w < 2 ^ (8 * Z.of_N 8)).
{ intros w. pose proof (bv_unsigned_in_range 64 w) as H. change (bv_modulus 64) with (2 ^ 64) in H.
  change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact H. }
unfold lf_frame.
repeat split.
- exact (field_of_region E m 2 _ _ _ _ _ _ (-8) 8%N (SOff 1 0) (bv_unsigned (getr regs0 1)) HR Hb ltac:(cbn [In]; auto 10)
    ltac:(cbn [sv_denot]; rewrite H1, Z.add_0_r; reflexivity) (Rg _) ltac:(lia)).
- exact (field_of_region E m 2 _ _ _ _ _ _ (-16) 8%N (SOff 8 0) (bv_unsigned (getr regs0 8)) HR Hb ltac:(cbn [In]; auto 10)
    ltac:(cbn [sv_denot]; rewrite H8, Z.add_0_r; reflexivity) (Rg _) ltac:(lia)).
- exact (field_of_region E m 2 _ _ _ _ _ _ (-24) 8%N (SOff 9 0) (bv_unsigned (getr regs0 9)) HR Hb ltac:(cbn [In]; auto 10)
    ltac:(cbn [sv_denot]; rewrite H9, Z.add_0_r; reflexivity) (Rg _) ltac:(lia)).
- exact (field_of_region E m 2 _ _ _ _ _ _ (-32) 8%N (SOff 18 0) (bv_unsigned (getr regs0 18)) HR Hb ltac:(cbn [In]; auto 10)
    ltac:(cbn [sv_denot]; rewrite H18, Z.add_0_r; reflexivity) (Rg _) ltac:(lia)).
- exact (field_of_region E m 2 _ _ _ _ _ _ (-40) 8%N (SOff 19 0) (bv_unsigned (getr regs0 19)) HR Hb ltac:(cbn [In]; auto 10)
    ltac:(cbn [sv_denot]; rewrite H19, Z.add_0_r; reflexivity) (Rg _) ltac:(lia)).
- exact (field_of_region E m 2 _ _ _ _ _ _ (-48) 8%N (SOff 20 0) (bv_unsigned (getr regs0 20)) HR Hb ltac:(cbn [In]; auto 10)
    ltac:(cbn [sv_denot]; rewrite H20, Z.add_0_r; reflexivity) (Rg _) ltac:(lia)).
- exact (field_of_region E m 2 _ _ _ _ _ _ (-56) 8%N (SOff 21 0) (bv_unsigned (getr regs0 21)) HR Hb ltac:(cbn [In]; auto 10)
    ltac:(cbn [sv_denot]; rewrite H21, Z.add_0_r; reflexivity) (Rg _) ltac:(lia)).
Qed.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis RF : @trange_free_spec fx rc SK PI B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_box) (PI := PI).
(* The entry: the registers are the env's first atoms, the 64-byte frame below sp is writable. *)
Lemma lf_entry : forall ly S W (regs : bvmap 5 word) mem md ch,
  afn_pre SEGS B LOWEST_FREE_STK ly S W regs mem md ch ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [])) ss_lf0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_lowest_free)) mem (seg_rom SEGS))).
Proof.
intros ly S W regs mem md ch HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : LOWEST_FREE_STK = 4176) by reflexivity.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs [])).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
unfold ss_lf0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold stack_region. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
- apply pairwise_disjoint_of_extents. cbn. repeat constructor.
- split; [|split; exact I].
  cbn [lf_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp. change (2 ^ 4) with 16.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.
(* The table t lies in a side-stack frame of S: a journal with an empty footprint that keeps ly and S keeps its bytes
   and their shadow. *)
Lemma lf_obj_kept : forall STK sp0 ly S W mem md W' mem' md' k t,
  ajournal SEGS B STK sp0 [] ly S W mem md [] ly S W' mem' md' k ->
  afobj SEGS B ly S W mem t ReacBoxregInit.REG_SIZE ->
  afobj SEGS B ly S W' mem' t ReacBoxregInit.REG_SIZE /\
  (forall i, 0 <= i < ReacBoxregInit.REG_SIZE -> aview SEGS (w_H W') mem' (t + i) = aview SEGS (w_H W) mem (t + i)).
Proof.
intros STK sp0 ly S W mem md W' mem' md' k t HJ ((cid & pos & Hin & Hcid & Hal & Hlo & Hhi) & Hp8 & HRA).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K4 & _).
change ReacBoxregInit.REG_SIZE with 288 in *.
assert (Hfs : fs_frame_bytes cid = 8 * (8 * 2 ^ cid)) by (unfold fs_frame_bytes; rewrite Z.shiftl_mul_pow2 by lia; lia).
pose proof (Z.pow_pos_nonneg 2 cid ltac:(lia) Hcid) as Hpow.
set (F := frame_addr ly cid pos) in *.
assert (HF : F = 8 * (F / 8)) by (pose proof (Z.div_mod F 8 ltac:(lia)); lia).
split; [split; [exists cid, pos; repeat split; assumption | split; [exact Hp8 |]] |].
- apply (range_addressable_agree (aview SEGS (w_H W) mem)); [|exact HRA].
  intros x Hx. apply (K4 cid pos (shadow_of_addr SHADOW_OFF x) Hin); [right | apply inFP_nil].
  unfold in_zr, shadow_addr, shadow_of_addr. cbn [fst snd]. fold F.
  assert (Hx8 : x / 8 = F / 8 + (x - F) / 8).
  { replace x with ((x - F) + (F / 8) * 8) at 1 by lia. rewrite Z.div_add by lia. lia. }
  assert (Hq : (x - F) / 8 < 8 * 2 ^ cid) by (apply Z.div_lt_upper_bound; lia).
  assert (Hq0 : 0 <= (x - F) / 8) by (apply Z.div_pos; lia).
  rewrite Hfs. replace (8 * (8 * 2 ^ cid) / 8) with (8 * 2 ^ cid) by (rewrite (Z.mul_comm 8 (8 * 2 ^ cid)), Z.div_mul by lia; reflexivity).
  lia.
- intros i Hi. apply (K4 cid pos (t + i) Hin); [left | apply inFP_nil].
  unfold in_zr, frame_rng. cbn [fst snd]. fold F. lia.
Qed.
Lemma lf_head_ok : forall ly S W regs0 mem0 md0 ch0 (regs : bvmap 5 word) memc,
  afn_pre SEGS B LOWEST_FREE_STK ly S W regs0 mem0 md0 ch0 ->
  getr regs 2 = w64 (spZ regs0 - 64) ->
  lf_frame (mrestrict (w_H W) memc) (spZ regs0) regs0 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (lf_extra regs0))) ss_lfL
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (AF_lowest_free + 0x40))) memc (seg_rom SEGS))).
Proof.
intros ly S W regs0 mem0 md0 ch0 regs memc HPRE R2 (V1 & V8 & V9 & V18 & V19 & V20 & V21).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : LOWEST_FREE_STK = 4176) by reflexivity.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (lf_extra regs0))).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (lf_extra regs0)) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (Usp : bv_unsigned (ew E 2) = spZ regs0 - 64).
{ rewrite EL by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl), R2. unfold w64.
  apply unsigned_lit_small. lia. }
assert (X : forall j, (j < 7)%nat -> ew E (32 + j) = nth j (lf_extra regs0) (Z_to_bv 64 0))
  by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (Rg : forall w : word, 0 <= bv_unsigned w < 2 ^ (8 * Z.of_N 8)).
{ intros w. pose proof (bv_unsigned_in_range 64 w) as H. change (bv_modulus 64) with (2 ^ 64) in H.
  change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact H. }
unfold ss_lfL. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold lf_loop_region. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  assert (E32 : ew E 32 = getr regs0 1) by exact (X 0%nat ltac:(lia)).
  assert (E33 : ew E 33 = getr regs0 8) by exact (X 1%nat ltac:(lia)).
  assert (E34 : ew E 34 = getr regs0 9) by exact (X 2%nat ltac:(lia)).
  assert (E35 : ew E 35 = getr regs0 18) by exact (X 3%nat ltac:(lia)).
  assert (E36 : ew E 36 = getr regs0 19) by exact (X 4%nat ltac:(lia)).
  assert (E37 : ew E 37 = getr regs0 20) by exact (X 5%nat ltac:(lia)).
  assert (E38 : ew E 38 = getr regs0 21) by exact (X 6%nat ltac:(lia)).
  repeat apply Forall_cons; try apply Forall_nil.
  + apply (chunk_ok_val SEGS E _ _ 8 8 (SOff 38 0) (bv_unsigned (getr regs0 21)));
    [cbn [sv_denot]; rewrite E38, Z.add_0_r; reflexivity | apply Rg | zside |].
    replace (spZ regs0 - 64 + 8) with (spZ regs0 + -56) by lia. exact V21.
  + apply (chunk_ok_val SEGS E _ _ 16 8 (SOff 37 0) (bv_unsigned (getr regs0 20)));
    [cbn [sv_denot]; rewrite E37, Z.add_0_r; reflexivity | apply Rg | zside |].
    replace (spZ regs0 - 64 + 16) with (spZ regs0 + -48) by lia. exact V20.
  + apply (chunk_ok_val SEGS E _ _ 24 8 (SOff 36 0) (bv_unsigned (getr regs0 19)));
    [cbn [sv_denot]; rewrite E36, Z.add_0_r; reflexivity | apply Rg | zside |].
    replace (spZ regs0 - 64 + 24) with (spZ regs0 + -40) by lia. exact V19.
  + apply (chunk_ok_val SEGS E _ _ 32 8 (SOff 35 0) (bv_unsigned (getr regs0 18)));
    [cbn [sv_denot]; rewrite E35, Z.add_0_r; reflexivity | apply Rg | zside |].
    replace (spZ regs0 - 64 + 32) with (spZ regs0 + -32) by lia. exact V18.
  + apply (chunk_ok_val SEGS E _ _ 40 8 (SOff 34 0) (bv_unsigned (getr regs0 9)));
    [cbn [sv_denot]; rewrite E34, Z.add_0_r; reflexivity | apply Rg | zside |].
    replace (spZ regs0 - 64 + 40) with (spZ regs0 + -24) by lia. exact V9.
  + apply (chunk_ok_val SEGS E _ _ 48 8 (SOff 33 0) (bv_unsigned (getr regs0 8)));
    [cbn [sv_denot]; rewrite E33, Z.add_0_r; reflexivity | apply Rg | zside |].
    replace (spZ regs0 - 64 + 48) with (spZ regs0 + -16) by lia. exact V8.
  + apply (chunk_ok_val SEGS E _ _ 56 8 (SOff 32 0) (bv_unsigned (getr regs0 1)));
    [cbn [sv_denot]; rewrite E32, Z.add_0_r; reflexivity | apply Rg | zside |].
    replace (spZ regs0 - 64 + 56) with (spZ regs0 + -8) by lia. exact V1.
- apply pairwise_disjoint_of_extents. cbn. repeat constructor.
- split; [|split; exact I].
  cbn [lf_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp. change (2 ^ 4) with 16.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia | idtac].
  rewrite Zminus_mod, Hal16. reflexivity.
Qed.
Lemma lf_loop : forall (k : nat) ly S W regs0 mem0 md0 ch0 (t nch fabric : Z) (bs : list byte)
  (regs : bvmap 5 word) memc mdc (base : Z),
  afn_pre SEGS B LOWEST_FREE_STK ly S W regs0 mem0 md0 ch0 ->
  ajournal SEGS B LOWEST_FREE_STK (spZ regs0) [] ly S W mem0 md0 [] ly S W memc mdc 0 ->
  Z.of_nat k = fabric - nch + 1 - base -> 0 <= base <= fabric - nch -> 1 <= nch <= 40 -> 1 <= fabric <= 40 ->
  (forall b, 0 <= b < base -> ~ range_free_c.range_free_ok bs b nch fabric) ->
  getr regs 2 = w64 (spZ regs0 - 64) -> getr regs 3 = getr regs0 3 -> getr regs 4 = getr regs0 4 ->
  getr regs 8 = w64 (-1) -> getr regs 9 = w64 fabric -> getr regs 18 = w64 nch -> getr regs 19 = w64 t ->
  getr regs 20 = w64 base -> getr regs 21 = w64 (fabric - nch + 1) ->
  getr regs 22 = getr regs0 22 -> getr regs 23 = getr regs0 23 -> getr regs 24 = getr regs0 24 ->
  getr regs 25 = getr regs0 25 -> getr regs 26 = getr regs0 26 -> getr regs 27 = getr regs0 27 ->
  lf_frame (mrestrict (w_H W) memc) (spZ regs0) regs0 ->
  afobj SEGS B ly S W mem0 t ReacBoxregInit.REG_SIZE -> length bs = 288%nat ->
  (forall i, 0 <= i < ReacBoxregInit.REG_SIZE ->
    aview SEGS (w_H W) mem0 (t + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) ->
  Boxreg.boxreg_B1 bs -> Boxreg.boxreg_B2 bs -> Boxreg.boxreg_B3 bs ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + (AF_lowest_free + 0x40))) memc (seg_rom SEGS)) mdc)
    (tlowest_free_post regs0 ly S W mem0 md0 nch fabric bs).
Proof.
induction k as [|k IH]; intros ly S W regs0 mem0 md0 ch0 t nch fabric bs regs memc mdc base
  HPRE HJ Hk Hb Hn Hf Hprev R2 R3 R4 R8 R9 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 HFR HOBJ HL HBS B1 B2 B3; [lia|].
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : LOWEST_FREE_STK = 4176) by reflexivity. assert (RS : RANGE_FREE_STK = 4112) by reflexivity.
pose proof (lf_head_ok ly S W regs0 mem0 md0 ch0 regs memc HPRE R2 HFR) as HS.
remember (Eimg (Ereg regs (lf_extra regs0))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (lf_extra regs0)) n)
  by (intros n Hq; subst E; apply Eimg_low; exact Hq).
assert (ER : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hq Hr; rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ n r Hr)).
assert (X : forall j, (j < 7)%nat -> ew E (32 + j) = nth j (lf_extra regs0) (Z_to_bv 64 0))
  by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (E2 : ew E 2 = w64 (spZ regs0 - 64)) by (rewrite (ER 2%nat 2%bv) by (lia || reflexivity); exact R2).
assert (E3 : ew E 3 = getr regs0 3) by (rewrite (ER 3%nat 3%bv) by (lia || reflexivity); exact R3).
assert (E4 : ew E 4 = getr regs0 4) by (rewrite (ER 4%nat 4%bv) by (lia || reflexivity); exact R4).
assert (E8 : ew E 8 = w64 (-1)) by (rewrite (ER 8%nat 8%bv) by (lia || reflexivity); exact R8).
assert (E9 : ew E 9 = w64 fabric) by (rewrite (ER 9%nat 9%bv) by (lia || reflexivity); exact R9).
assert (E18 : ew E 18 = w64 nch) by (rewrite (ER 18%nat 18%bv) by (lia || reflexivity); exact R18).
assert (E19 : ew E 19 = w64 t) by (rewrite (ER 19%nat 19%bv) by (lia || reflexivity); exact R19).
assert (E20 : ew E 20 = w64 base) by (rewrite (ER 20%nat 20%bv) by (lia || reflexivity); exact R20).
assert (E21 : ew E 21 = w64 (fabric - nch + 1)) by (rewrite (ER 21%nat 21%bv) by (lia || reflexivity); exact R21).
assert (E32 : ew E 32 = getr regs0 1) by exact (X 0%nat ltac:(lia)).
assert (E33 : ew E 33 = getr regs0 8) by exact (X 1%nat ltac:(lia)).
assert (E34 : ew E 34 = getr regs0 9) by exact (X 2%nat ltac:(lia)).
assert (E35 : ew E 35 = getr regs0 18) by exact (X 3%nat ltac:(lia)).
assert (E36 : ew E 36 = getr regs0 19) by exact (X 4%nat ltac:(lia)).
assert (E37 : ew E 37 = getr regs0 20) by exact (X 5%nat ltac:(lia)).
assert (E38 : ew E 38 = getr regs0 21) by exact (X 6%nat ltac:(lia)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs0 - 64) by (rewrite E2; unfold w64; apply unsigned_lit_small; lia).
assert (HAE : env_agree 32 (Ereg regs (lf_extra regs0)) E) by (split; [intros n Hq; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (SHOK : sh_ok SEGS LF_Bx [] E (mrestrict (w_H W) memc)) by constructor.
clear HE EL X.
(* 1. From the loop head to the call of range_free (0x81574). *)
paj_run_tok RUN HS HJ SHOK LF_Bspan; [awr_ok_tac; exact Usp |].
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
prreg HS (13%bv : bv 5) Q13.
rewrite pa_sigma_range_free.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
  destruct (lf_obj_kept _ _ _ _ _ _ _ _ _ _ _ t HJ HOBJ) as [HOBJ1 HBK1];
  assert (HBS1 : forall i, 0 <= i < ReacBoxregInit.REG_SIZE ->
    aview SEGS (w_H W) mm (t + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0))))
    by (intros i Hi; rewrite (HBK1 i Hi); exact (HBS i Hi));
  assert (Qsp : spZ rg = spZ regs0 + -64) by (unfold spZ at 1; rewrite Q2, Usp; lia);
  assert (Hs0 : s0Z rg = 18446744073709551615) by (unfold s0Z; rewrite Q8, E8; vm_compute; reflexivity)
end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
eapply SRr_bind;
[ eapply (cl_callS B LAWS W rg mm _ LOWEST_FREE_STK (spZ regs0) [] ly S W mem0 md0 [] ly S mdq 0 RANGE_FREE_STK [] 0 (-64)
    (Z_to_bv 64 (BASE + 5676)) []
    (fun ly2 S2 W2 regs2 mem2 md2 => ly2 = ly /\ S2 = S /\ W2 = W /\
       ((range_free_c.range_free_ok bs base nch fabric /\ getr regs2 10 = w64 1) \/
        (~ range_free_c.range_free_ok bs base nch fabric /\ getr regs2 10 = w64 0))) HJ Qsp);
  [ reflexivity | lia | rewrite RS; lia | rewrite RS, WS; lia
  | rewrite Q3, E3; exact Hgp | rewrite Q4, E4; exact Htp
  | exact Q1 | apply ret_ok_codeptr_v; [lia | reflexivity] | rewrite unsigned_lit_small by lia; lia
  | rewrite Hs0; left; split; [right; right; intro HH; vm_compute in HH; discriminate HH | reflexivity]
  | intros HPRE1; eapply SRr_mono;
    [ pose proof (RF ly S W rg mm mdq [] t base nch fabric bs HPRE1) as HC;
      unfold cfg_at, A_range_freeP, w64 in HC; eapply HC;
      [ rewrite Q10, E19; reflexivity | rewrite Q11, E20; reflexivity | rewrite Q12, E18; reflexivity
      | rewrite Q13, E9; reflexivity | lia | lia | lia | exact HOBJ1 | exact HL | exact HBS1
      | exact B1 | exact B2 | exact B3 ]
    | cbv beta; intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ1 & HP & HQ);
      exists ly2, S2, regs2, mem2, md2; split; [rewrite Q1; reflexivity | split; [exact HJ1 | split; [exact HP | exact HQ]]] ]
  | intros a Ha; exfalso; exact (inFP_nil a Ha) ]
| ] end.
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP2 & (-> & -> & -> & Hres)).
change (0 + 0) with 0 in HJ2.
jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2.
cbn [ms_mem ms_regs restrict mkst] in HS2, HJc.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ repeat apply Forall_cons; [| apply Forall_nil].
  eapply (region_kept_stack_sub SEGS B); [exact HJc | exact HJ2 | exact Usp | lia | rewrite WS; lia | lia | cbn; lia | cbn; lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 40 (map (getr regs2) CLOB)) as E' eqn:HE' in HS.
assert (HEI' : img_env VAL A_LIM E') by (rewrite HE'; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD : forall n, (n < 40)%nat -> ew E' n = ew E n) by (intros n Hq; rewrite HE'; apply YN3v.ew_havoc_old; exact Hq).
assert (HAE' : env_agree 32 (Ereg regs (lf_extra regs0)) E') by (rewrite HE'; apply env_agree_havoc_ge; [lia | exact HAE]).
clear HE'.
assert (Usp' : bv_unsigned (ew E' 2) = spZ regs0 - 64) by (rewrite OLD by lia; exact Usp).
lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
clear HF HFr HG HOBJ1 HBK1 HBS1 Q1 Q2 Q3 Q4 Q8 Q10 Q11 Q12 Q13 Qsp Hs0 HJ.
destruct Hres as [[HOK Ha0] | [HNOK Ha0]].
- (* range_free found base free: a0 = 1, so the loop exits with s0 = base. *)
  pose proof (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) 1 HS ltac:(cbn [ms_regs restrict mkst]; exact Ha0) eq_refl) as HS1.
  clear HS. rename HS1 into HS.
  assert (SHOK2 : sh_ok SEGS LF_Bx [] E' (mrestrict (w_H W) mem2)) by constructor.
  paj_run_tok RUN HS HJ2 SHOK2 LF_Bspan; [awr_ok_tac; exact Usp' |].
  (* the return with a0 = s0 = base *)
  prreg HS (1%bv : bv 5) F1. prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4.
  prreg HS (8%bv : bv 5) F8. prreg HS (9%bv : bv 5) F9. prreg HS (10%bv : bv 5) F10.
  prreg HS (18%bv : bv 5) F18. prreg HS (19%bv : bv 5) F19. prreg HS (20%bv : bv 5) F20. prreg HS (21%bv : bv 5) F21.
  prreg HS (22%bv : bv 5) F22. prreg HS (23%bv : bv 5) F23. prreg HS (24%bv : bv 5) F24.
  prreg HS (25%bv : bv 5) F25. prreg HS (26%bv : bv 5) F26. prreg HS (27%bv : bv 5) F27.
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)). intros mat'.
  lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msc) _ (ms_mem ?msc) _) ?mdq] =>
    replace (v_jalr (getr (ms_regs msc) 1) 0) with (getr regs0 1)
      by (rewrite F1, (OLD 32%nat), E32 by lia; symmetry; exact Hra);
    apply (lf_post ly S W regs0 mem0 md0 nch fabric bs (ms_regs msc) (ms_mem msc) mdq base)
  end.
  + apply (ajournal_materialize SEGS B LAWS Hsegs). exact HJ2.
  + apply lf_aregs.
    * rewrite F2, Usp'. replace (spZ regs0 - 64 + 64) with (spZ regs0) by lia. unfold spZ. apply Z_to_bv_bv_unsigned.
    * rewrite F3, (OLD 3%nat) by lia. exact E3.
    * rewrite F4, (OLD 4%nat) by lia. exact E4.
    * rewrite F8, (OLD 33%nat) by lia. exact E33.
    * rewrite F9, (OLD 34%nat) by lia. exact E34.
    * rewrite F18, (OLD 35%nat) by lia. exact E35.
    * rewrite F19, (OLD 36%nat) by lia. exact E36.
    * rewrite F20, (OLD 37%nat) by lia. exact E37.
    * rewrite F21, (OLD 38%nat) by lia. exact E38.
    * rewrite F22, (OLD 22%nat), (ER 22%nat 22%bv) by (lia || reflexivity). exact R22.
    * rewrite F23, (OLD 23%nat), (ER 23%nat 23%bv) by (lia || reflexivity). exact R23.
    * rewrite F24, (OLD 24%nat), (ER 24%nat 24%bv) by (lia || reflexivity). exact R24.
    * rewrite F25, (OLD 25%nat), (ER 25%nat 25%bv) by (lia || reflexivity). exact R25.
    * rewrite F26, (OLD 26%nat), (ER 26%nat 26%bv) by (lia || reflexivity). exact R26.
    * rewrite F27, (OLD 27%nat), (ER 27%nat 27%bv) by (lia || reflexivity). exact R27.
  + rewrite F10, (OLD 20%nat) by lia. exact E20.
  + right. split; [lia|]. split; [exact HOK | exact Hprev].
- pose proof (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) 0 HS ltac:(cbn [ms_regs restrict mkst]; exact Ha0) eq_refl) as HS1.
  clear HS. rename HS1 into HS.
  assert (SHOK2 : sh_ok SEGS LF_Bx [] E' (mrestrict (w_H W) mem2)) by constructor.
  paj_run_tok RUN HS HJ2 SHOK2 LF_Bspan; [awr_ok_tac; exact Usp' |].
  psrr_branch_tok RUN BR HS SHOK2 LF_Bspan;
  rewrite branch_ne_U in Hc; unfold U in Hc;
  rewrite (lf_addw1 E' 20 base) in Hc by first [rewrite (OLD 20%nat) by lia; exact E20 | lia];
  replace (sv_denot E' (SOff 21 0)) with (Z_to_bv 64 (fabric - nch + 1)) in Hc
    by (cbn [sv_denot]; rewrite (OLD 21%nat), E21 by lia; unfold w64; rewrite unsigned_lit_small, Z.add_0_r by lia; reflexivity);
  rewrite !unsigned_lit_small in Hc by lia.
  + (* base + 1 <> fabric - nch + 1: back to the loop head with base + 1 *)
    destruct (Z.eqb_spec (fabric - nch + 1) (base + 1)) as [Heq | Hne]; [discriminate Hc|]. clear Hc.
    paj_run_to_tok RUNTO HS HJ2 SHOK2 LF_Bspan (AF_lowest_free + 0x40); [awr_ok_tac; exact Usp' |].
    pmkst HS.
    prreg HS (2%bv : bv 5) G2. prreg HS (3%bv : bv 5) G3. prreg HS (4%bv : bv 5) G4. prreg HS (8%bv : bv 5) G8.
    prreg HS (9%bv : bv 5) G9. prreg HS (18%bv : bv 5) G18. prreg HS (19%bv : bv 5) G19. prreg HS (21%bv : bv 5) G21.
    prreg HS (22%bv : bv 5) G22. prreg HS (23%bv : bv 5) G23. prreg HS (24%bv : bv 5) G24.
    prreg HS (25%bv : bv 5) G25. prreg HS (26%bv : bv 5) G26. prreg HS (27%bv : bv 5) G27.
    lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
      pose proof (st_ok_pi_restrict_reg _ E' ssx msx (20%bv : bv 5) HS) as G20;
      let e := eval vm_compute in (sr_get (ss_regs ssx) (20%bv : bv 5)) in change (sr_get (ss_regs ssx) (20%bv : bv 5)) with e in G20;
      cbn [ms_regs restrict mkst] in G20;
      rewrite (lf_addw1 E' 20 base) in G20 by first [rewrite (OLD 20%nat) by lia; exact E20 | lia];
      pose proof (st_ok_pi_region_nth E' ssx (restrict (w_H W) msx) 0 lf_loop_region HS eq_refl) as HRr;
      cbn [ms_mem restrict mkst] in HRr;
      pose proof (lf_frame_of_loop E' _ regs0 HRr Usp'
        ltac:(rewrite (OLD 32%nat) by lia; exact E32) ltac:(rewrite (OLD 33%nat) by lia; exact E33)
        ltac:(rewrite (OLD 34%nat) by lia; exact E34) ltac:(rewrite (OLD 35%nat) by lia; exact E35)
        ltac:(rewrite (OLD 36%nat) by lia; exact E36) ltac:(rewrite (OLD 37%nat) by lia; exact E37)
        ltac:(rewrite (OLD 38%nat) by lia; exact E38)) as HFR2
    end.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
      change (SRr SEGS W (mkCfg (mkst rg (Z_to_bv 64 (BASE + (AF_lowest_free + 0x40))) mm (seg_rom SEGS)) mdq)
        (tlowest_free_post regs0 ly S W mem0 md0 nch fabric bs));
      apply (IH ly S W regs0 mem0 md0 ch0 t nch fabric bs rg mm mdq (base + 1) HPRE HJ2)
    end.
    * lia.
    * lia.
    * exact Hn.
    * exact Hf.
    * intros b Hb'. destruct (Z.eq_dec b base) as [-> | Hb2]; [exact HNOK | apply Hprev; lia].
    * rewrite G2, (OLD 2%nat) by lia. exact E2.
    * rewrite G3, (OLD 3%nat) by lia. exact E3.
    * rewrite G4, (OLD 4%nat) by lia. exact E4.
    * rewrite G8, (OLD 8%nat) by lia. exact E8.
    * rewrite G9, (OLD 9%nat) by lia. exact E9.
    * rewrite G18, (OLD 18%nat) by lia. exact E18.
    * rewrite G19, (OLD 19%nat) by lia. exact E19.
    * exact G20.
    * rewrite G21, (OLD 21%nat) by lia. exact E21.
    * rewrite G22, (OLD 22%nat), (ER 22%nat 22%bv) by (lia || reflexivity). exact R22.
    * rewrite G23, (OLD 23%nat), (ER 23%nat 23%bv) by (lia || reflexivity). exact R23.
    * rewrite G24, (OLD 24%nat), (ER 24%nat 24%bv) by (lia || reflexivity). exact R24.
    * rewrite G25, (OLD 25%nat), (ER 25%nat 25%bv) by (lia || reflexivity). exact R25.
    * rewrite G26, (OLD 26%nat), (ER 26%nat 26%bv) by (lia || reflexivity). exact R26.
    * rewrite G27, (OLD 27%nat), (ER 27%nat 27%bv) by (lia || reflexivity). exact R27.
    * exact HFR2.
    * exact HOBJ.
    * exact HL.
    * exact HBS.
    * exact B1.
    * exact B2.
    * exact B3.
  + (* base + 1 = fabric - nch + 1: every base was tried; return -1 *)
    destruct (Z.eqb_spec (fabric - nch + 1) (base + 1)) as [Heq | Hne]; [|discriminate Hc]. clear Hc.
    paj_run_tok RUN HS HJ2 SHOK2 LF_Bspan; [awr_ok_tac; exact Usp' |].
    prreg HS (1%bv : bv 5) F1. prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4.
    prreg HS (8%bv : bv 5) F8. prreg HS (9%bv : bv 5) F9. prreg HS (10%bv : bv 5) F10.
    prreg HS (18%bv : bv 5) F18. prreg HS (19%bv : bv 5) F19. prreg HS (20%bv : bv 5) F20. prreg HS (21%bv : bv 5) F21.
    prreg HS (22%bv : bv 5) F22. prreg HS (23%bv : bv 5) F23. prreg HS (24%bv : bv 5) F24.
    prreg HS (25%bv : bv 5) F25. prreg HS (26%bv : bv 5) F26. prreg HS (27%bv : bv 5) F27.
    eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)). intros mat'.
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msc) _ (ms_mem ?msc) _) ?mdq] =>
      replace (v_jalr (getr (ms_regs msc) 1) 0) with (getr regs0 1)
        by (rewrite F1, (OLD 32%nat), E32 by lia; symmetry; exact Hra);
      apply (lf_post ly S W regs0 mem0 md0 nch fabric bs (ms_regs msc) (ms_mem msc) mdq (-1))
    end.
    * apply (ajournal_materialize SEGS B LAWS Hsegs). exact HJ2.
    * apply lf_aregs.
      -- rewrite F2, Usp'. replace (spZ regs0 - 64 + 64) with (spZ regs0) by lia. unfold spZ. apply Z_to_bv_bv_unsigned.
      -- rewrite F3, (OLD 3%nat) by lia. exact E3.
      -- rewrite F4, (OLD 4%nat) by lia. exact E4.
      -- rewrite F8, (OLD 33%nat) by lia. exact E33.
      -- rewrite F9, (OLD 34%nat) by lia. exact E34.
      -- rewrite F18, (OLD 35%nat) by lia. exact E35.
      -- rewrite F19, (OLD 36%nat) by lia. exact E36.
      -- rewrite F20, (OLD 37%nat) by lia. exact E37.
      -- rewrite F21, (OLD 38%nat) by lia. exact E38.
      -- rewrite F22, (OLD 22%nat), (ER 22%nat 22%bv) by (lia || reflexivity). exact R22.
      -- rewrite F23, (OLD 23%nat), (ER 23%nat 23%bv) by (lia || reflexivity). exact R23.
      -- rewrite F24, (OLD 24%nat), (ER 24%nat 24%bv) by (lia || reflexivity). exact R24.
      -- rewrite F25, (OLD 25%nat), (ER 25%nat 25%bv) by (lia || reflexivity). exact R25.
      -- rewrite F26, (OLD 26%nat), (ER 26%nat 26%bv) by (lia || reflexivity). exact R26.
      -- rewrite F27, (OLD 27%nat), (ER 27%nat 27%bv) by (lia || reflexivity). exact R27.
    * rewrite F10, (OLD 8%nat) by lia. exact E8.
    * left. split; [reflexivity|]. intros b Hb'.
      destruct (Z.eq_dec b base) as [-> | Hb2]; [exact HNOK | apply Hprev; lia].
Qed.
Theorem pb_lowest_free : tlowest_free_spec.
Proof.
unfold tlowest_free_spec.
intros ly S W regs mem md ch t nch fabric bs HPRE H10 H11 H12 Hn Hf HOBJ HL HBS B1 B2 B3.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (lf_entry ly S W regs mem md ch HPRE) as HS.
pose proof (ajournal_init SEGS B LOWEST_FREE_STK [] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (ER : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hq Hr; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ n r Hr)).
assert (HAE : env_agree 32 (Ereg regs []) E)
  by (split; [intros n Hq; subst E; apply Eimg_low; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (ER 2%nat 2%bv) by (lia || reflexivity); reflexivity).
assert (E10 : ew E 10 = w64 t) by (rewrite (ER 10%nat 10%bv) by (lia || reflexivity); exact H10).
assert (E11 : ew E 11 = w64 nch) by (rewrite (ER 11%nat 11%bv) by (lia || reflexivity); exact H11).
assert (E12 : ew E 12 = w64 fabric) by (rewrite (ER 12%nat 12%bv) by (lia || reflexivity); exact H12).
assert (SHOK : sh_ok SEGS LF_Bx [] E (mrestrict (w_H W) mem)) by constructor.
clear HE.
unfold cfg_at, A_lowest_freeP. change (w64 (BASE + AF_lowest_free)) with (Z_to_bv 64 (BASE + AF_lowest_free)).
(* 1. The prologue (saves of ra, s0 .. s5; s0 = -1), up to the test fabric < nch (bltu at 0x81548). *)
paj_run_tok RUN HS HJ SHOK LF_Bspan; [awr_ok_tac; exact Usp |].
psrr_branch_tok RUN BR HS SHOK LF_Bspan;
rewrite branch_ltu_U, !U_SOff, E12, E11 in Hc; unfold w64 in Hc;
rewrite !unsigned_lit_small, !Z.add_0_r in Hc by lia; unfold zcanon, M64 in Hc; rewrite !Z.mod_small in Hc by lia.
- (* fabric < nch: the epilogue returns s0 = -1 *)
  apply Z.ltb_lt in Hc.
  paj_run_tok RUN HS HJ SHOK LF_Bspan; [awr_ok_tac; exact Usp |].
  prreg HS (1%bv : bv 5) F1. prreg HS (10%bv : bv 5) F10.
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)). intros mat'.
  lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msc) _ (ms_mem ?msc) _) ?mdq] =>
    replace (v_jalr (getr (ms_regs msc) 1) 0) with (getr regs 1)
      by (rewrite F1, (ER 1%nat 1%bv) by (lia || reflexivity); symmetry; exact Hra);
    apply (lf_post ly S W regs mem md nch fabric bs (ms_regs msc) (ms_mem msc) mdq (-1))
  end.
  + apply (ajournal_materialize SEGS B LAWS Hsegs). exact HJ.
  + eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs [] HS); [exact HAE | vm_compute; reflexivity].
  + rewrite F10. apply bv_eq. reflexivity.
  + left. split; [reflexivity|]. intros b Hb. lia.
- (* nch <= fabric: run to the loop head (0x81564) with base = 0 and the count fabric - nch + 1 *)
  apply Z.ltb_ge in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK LF_Bspan (AF_lowest_free + 0x40); [awr_ok_tac; exact Usp |].
  pmkst HS.
  prreg HS (2%bv : bv 5) G2. prreg HS (3%bv : bv 5) G3. prreg HS (4%bv : bv 5) G4. prreg HS (8%bv : bv 5) G8.
  prreg HS (9%bv : bv 5) G9. prreg HS (18%bv : bv 5) G18. prreg HS (19%bv : bv 5) G19. prreg HS (20%bv : bv 5) G20.
  prreg HS (22%bv : bv 5) G22. prreg HS (23%bv : bv 5) G23. prreg HS (24%bv : bv 5) G24.
  prreg HS (25%bv : bv 5) G25. prreg HS (26%bv : bv 5) G26. prreg HS (27%bv : bv 5) G27.
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
    pose proof (st_ok_pi_restrict_reg _ Ex ssx msx (21%bv : bv 5) HS) as G21;
    let e := eval vm_compute in (sr_get (ss_regs ssx) (21%bv : bv 5)) in change (sr_get (ss_regs ssx) (21%bv : bv 5)) with e in G21;
    cbn [ms_regs restrict mkst] in G21;
    rewrite (lf_cnt Ex fabric nch E12 E11 Hf Hn) in G21;
    pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W) msx) 0 lf_entry_region HS eq_refl) as HRr;
    cbn [ms_mem restrict mkst] in HRr;
    pose proof (lf_frame_of_entry Ex _ regs HRr Usp
      ltac:(rewrite (ER 1%nat 1%bv) by (lia || reflexivity); reflexivity)
      ltac:(rewrite (ER 8%nat 8%bv) by (lia || reflexivity); reflexivity)
      ltac:(rewrite (ER 9%nat 9%bv) by (lia || reflexivity); reflexivity)
      ltac:(rewrite (ER 18%nat 18%bv) by (lia || reflexivity); reflexivity)
      ltac:(rewrite (ER 19%nat 19%bv) by (lia || reflexivity); reflexivity)
      ltac:(rewrite (ER 20%nat 20%bv) by (lia || reflexivity); reflexivity)
      ltac:(rewrite (ER 21%nat 21%bv) by (lia || reflexivity); reflexivity)) as HFR
  end.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
    change (SRr SEGS W (mkCfg (mkst rg (Z_to_bv 64 (BASE + (AF_lowest_free + 0x40))) mm (seg_rom SEGS)) mdq)
      (tlowest_free_post regs ly S W mem md nch fabric bs));
    apply (lf_loop (Z.to_nat (fabric - nch + 1)) ly S W regs mem md ch t nch fabric bs rg mm mdq 0 HPRE HJ)
  end.
  + lia.
  + lia.
  + exact Hn.
  + exact Hf.
  + intros b Hb. lia.
  + rewrite G2, Usp. unfold w64. f_equal; lia.
  + rewrite G3, (ER 3%nat 3%bv) by (lia || reflexivity). reflexivity.
  + rewrite G4, (ER 4%nat 4%bv) by (lia || reflexivity). reflexivity.
  + rewrite G8. apply bv_eq. reflexivity.
  + rewrite G9. exact E12.
  + rewrite G18. exact E11.
  + rewrite G19. exact E10.
  + rewrite G20. reflexivity.
  + exact G21.
  + rewrite G22, (ER 22%nat 22%bv) by (lia || reflexivity). reflexivity.
  + rewrite G23, (ER 23%nat 23%bv) by (lia || reflexivity). reflexivity.
  + rewrite G24, (ER 24%nat 24%bv) by (lia || reflexivity). reflexivity.
  + rewrite G25, (ER 25%nat 25%bv) by (lia || reflexivity). reflexivity.
  + rewrite G26, (ER 26%nat 26%bv) by (lia || reflexivity). reflexivity.
  + rewrite G27, (ER 27%nat 27%bv) by (lia || reflexivity). reflexivity.
  + exact HFR.
  + exact HOBJ.
  + exact HL.
  + exact HBS.
  + exact B1.
  + exact B2.
  + exact B3.
Qed.
End h.
End f.
End d.
