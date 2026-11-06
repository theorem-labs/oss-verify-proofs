(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACh9.v:86-90
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203, 332-335, 358-363, 460-463 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:1593-1596, 1605-1615 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:2082-2086 [Apache-2.0 OR MIT], for libreac/fuzz_identity's ASan build
   (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8b.v:393-396. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_catalogue_defect.v, with its module paths, module names and numbers changed; 3336 of its 3457 lines of code are new or changed and 534 lines of the source are left out. *)
(* check (fuzz_boxreg.asan 0x80ff0, 176 instructions): the contract of the ASan build's code of the harness's
   static void check (const struct reac_boxreg *r, int fabric) (fuzz/fuzz_boxreg.c:115-159).
   The function takes a 160-byte frame on the machine stack (addi sp,sp,-0xa0). It loads n = r->n at r + 280 and
   r->fabric at r + 284, each after the ASan check of its shadow byte, and aborts unless 0 <= n <= 5 (bltu, unsigned)
   and r->fabric = fabric (a1, compared as 64 bits with the sign-extended word). Then, for i = 0 .. n - 1, it loads
   nch_i at r + 56 i + 12 and base_i at r + 56 i + 8, each after its shadow check, and aborts unless nch_i is even,
   2 <= nch_i <= 40, nch_i <= fabric, base_i >= 0 and base_i + nch_i <= fabric; it calls memchr (r + 56 i + 24, 0, 32)
   through BS___interceptor_trampoline_memchr (0x41408, call at 0x81134) and aborts on NULL; then, for
   j = i + 1 .. n - 1, it loads base_j and nch_j (shadow checks), aborts when the two slices meet, calls bcmp
   (r + 56 i, ZERO, 6) through BS___interceptor_trampoline_bcmp (0x41404, call at 0x81198) and, when that result is
   nonzero, bcmp (r + 56 i, r + 56 j, 6) (call at 0x811ac), and aborts when the second result is 0. Every abort is
   __asan_handle_no_return then abort (0x81278, 0x8127c). It returns void and writes nothing outside its own frame
   and the wrappers' windows below it.
   No abort is reached: the pre-condition carries Pau's check facts, the facts the plain contract
   (lib/Prog/check_c.v check_contract) takes: boxreg_B16 bs over the struct's bytes (B1: 0 <= n <= 5; B2:
   1 <= fabric <= 40; B3: each row's width is even, 2 .. 40 and at most the fabric, and its slice is inside the
   fabric; B4: no two rows meet; B5: a row's MAC is zero6 or differs from each later row's; B6: each row's name field
   holds a NUL) and bx_fabric bs = fabric. Each abort branch is refuted by one of them (n: B1; fabric: the equation;
   width, base and slice: B3; memchr NULL: B6; overlap: B4; MAC: B5 with the ZERO bytes), so the post states a return
   only, as the plain contract does. The plain walk's model lemmas (lib/Prog/CheckFacts.v memchr_name, memcmp_eq)
   give the same steps.
   Stack: the own 160-byte frame and 2 * ESTACK below it: abcmp_realizes asks for 2 * ESTACK of present stack below
   the caller's sp (CONVENTIONS section 4) and memchr's contract (lib/A/Rt/MemchrDef.v amemchr_realizes, ecall_pre)
   asks for ESTACK, so the deeper is 2 * ESTACK; there is no program callee.
   Read footprint, each byte covered by a premise: the 288-byte registry struct at r, a heap block of the caller
   (In (r, REG_SIZE) (ablocks ..) and its bytes bs; the code reads r + 280 .. r + 287 and r + 56 i + 8 ..
   r + 56 i + 15 for i < n; bcmp reads the MACs r + 56 i .. r + 56 i + 5; memchr reads the name r + 56 i + 24 ..
   r + 56 i + 24 + k and the rest of the NUL's aligned 8-byte word, inside the field); ZERO, the harness's
   static const uint8_t ZERO[6] (fuzz/fuzz_boxreg.c:56), the listing's object A_OBJ 6 (0x20cc0, auipc / addi at
   0x810a8 / 0x810b8), a registered global of the read-only image (asan_globals record (0x20cc0, 6)); the shadow
   bytes of the struct (the __asan_report_load4 branches 0x81238, 0x8128c .. 0x812ac are refuted by the block's
   shadow in AR); the GOT word of the shadow base (auipc / ld at 0x81028) and the shadow cells are fixed by AR
   (AR_const_law, lib/Reusable/YG0d.v); the read-only image memchr's contract reads; the wrappers' own reads are
   inside their contracts.
   Image facts across calls: check's caller (LLVMFuzzerTestOneInput) calls check after other calls, and an ajournal
   keeps no shadow byte of the image (lib/Reusable/YCbq.v:358) and keeps an image byte only when it is neither an
   owned static nor an errno byte (:362). So ZERO and the read-only image are stated by facts that hold in every
   state, as in reac_boxreg_declare / reac_boxreg_set_name:
   - memchr's read-only view (lib/A/Rt/MemchrDef.v; asn_rom_kept of lib/A/Rt/SnprintfDef.v): arodata_okP on the
     read-only segments; arodata_okP is carried by every journal (lib/A/Prog/BoxBase.v arodata_ok_journalP);
   - ZERO's bytes: asn_rom_bytes for zero6 (state-free: read-only image bytes that are no owned static and no errno
     byte), read through that view; abcmp_realizes's src_ok and its result follow;
   - ZERO's shadow: globs_marked G with In (ZERO, 6) G (range_addressable) and img_shadow_vis with the 64-byte
     margins (shadow_hull_vis), lib/A/Prog/BoxRo.v ro_read_ok_glob; both hold in every AR state;
   - ZERO's amem_range, 0 <= ZERO and its distance from the window: from the margins and alloc_ceiling below the
     stack. Inside check the bcmp and memchr posts keep every byte outside their windows, so the view stays.
   Hazards: the struct is 288 bytes (rows 0..280, n at +280, fabric at +284; row i's MAC at 56 i, base at 56 i + 8,
   nch at 56 i + 12, name at 56 i + 24, 32 bytes); n <= 5 keeps every row access inside the block. memchr can find
   the NUL at any index k up to 31 of the 32-byte name field (a declared name is cut to 31 characters,
   fuzz/fuzz_boxreg.c:260-262), so cgif's amemchr0_realizes (k + 8 <= n) does not apply: the walk takes
   MemchrDef.v's amemchr_realizes, whose found arm asks for c = 0, 8 <= n, k < n and the NUL's aligned 8-byte word
   inside [x, x + n). B6 gives k < 32, and the field x = r + 56 i + 24 is 8-aligned because the allocator's block law
   (AR_blocks_law, lib/Reusable/YG0d.v) makes r a multiple of 16, so that word ends at x + 32 or below; the not-found
   arm (abort) is excluded by B6. The bcmp entry is the trampoline at 0x41404 (__wrap_bcmp is an alias of the same
   address), stated with abcmp_realizes, not amemcmp_realizes. No f* or csr instruction occurs in the 176
   instructions (capstone scan; the listing has no 0xc0001073 word in check), so the fixed {fx} is sound. The old
   walk's runtime cells (asan_cells, REAL_MEMCHR, REAL_BCMP, REAL_MEMCMP, GOT_CF, CF + 254/255) and its
   boxreg-measured CHECK_FRAME = 160 + BCMP_WRAP_K leave the statement: the cells are premises of the runtime
   hypotheses, not of this function.
   Image difference: the asan-ubsan build (lib/B/Prog/BoxBCheck.v) has a 144-byte frame, ZERO is its A_OBJ 4, and it
   adds UBSan traps (r misaligned, the row index, the pointer overflow of r + 56 i and r + 56 j, the signed overflow
   of base + nch); the result is the same.
   The memory model is Pau's plain one (lib/Prog/Boxreg.v boxreg_B16, bx_fabric, zero6), used as it is. *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow BoxSyms BoxList BoxPa.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaJournal BoxBase.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05.
(* REG_SIZE, the size of struct reac_boxreg, is ReacBoxregInit's. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import ReacBoxregInit BoxRo.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require Import SnprintfDef MemchrDef ConstsViewDef.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import BoxPaLib YC1g YC1h YC4b YC81 PaStep BoxFrame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg CheckFacts.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Bytes.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Spec Require StrFun.
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
#[local] Notation VAL := (@pa_val _ box_listing PI).
#[local] Notation BASE := (@pa_val _ box_listing PI A_TEXT).
(* The function's address in the image and the stack it needs: its own 160-byte frame and 2 * ESTACK below it for
   the bcmp wrapper (the memchr wrapper needs ESTACK, inside it). *)
Definition A_checkP : Z := BASE + AF_check.
Definition CHECK_STK : Z := 160 + 2 * ESTACK.
(* musl memchr's constant words, read by its word loop (loads at 0x920e0 / 0x920e8): the 32 image bytes of
   [0x10350, 0x10370) (0x10350 = 0x8080808080808080, 0x10368 = 0x0101010101010100, a read-only .rodata range of
   fuzz_boxreg.asan, not owned by the runtime), the range lib/A/Rt/MemchrDef.v amemchr_realizesM takes as lo .. hi. *)
Definition MCH_LO : Z := 0x10350.
Definition MCH_CONSTS : list Z :=
[128; 128; 128; 128; 128; 128; 128; 128; 219; 52; 182; 215; 130; 222; 27; 67;
 0; 0; 0; 0; 0; 0; 224; 63; 0; 1; 1; 1; 1; 1; 1; 1].
Section h.
Variable B : asyms.
Definition tcheck_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md (r : Z) (bs : list byte)
  : world SEGS -> config -> Prop :=
apost_base SEGS B CHECK_STK [] regs ly S W mem md 0
(fun ly' S' W' regs' mem' md' =>
ly' = ly /\ S' = S /\ W' = W /\ Permutation (ablocks B ly' S') (ablocks B ly S) /\
(forall i, 0 <= i < REG_SIZE ->
  aview SEGS (w_H W') mem' (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0))))).
Definition tcheck_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (r fabric : Z) (bs : list byte) (G : list (Z * Z)),
afn_pre SEGS B CHECK_STK ly S W regs mem md ch ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
getr regs 10 = w64 r -> getr regs 11 = w64 fabric ->
(* the registry struct: a heap block holding bs, which passes Pau's checks for this fabric *)
In (r, REG_SIZE) (ablocks B ly S) ->
(forall i, 0 <= i < REG_SIZE ->
  aview SEGS (w_H W) mem (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) ->
Boxreg.boxreg_B16 bs -> Boxreg.bx_fabric bs = fabric ->
(* facts of the image and of the runtime's symbols, true in every state *)
img_shadow_vis SEGS B -> globs_marked SEGS B G ->
(* the image's ZERO (A_OBJ 6): six zero bytes of the read-only image, a registered global *)
asn_rom_bytes SEGS B (VAL (A_OBJ 6)) (map (fun b : byte => bv_unsigned b) Boxreg.zero6) -> In (VAL (A_OBJ 6), 6) G ->
IMG_LO + 64 <= VAL (A_OBJ 6) -> VAL (A_OBJ 6) + 6 + 64 <= IMG_HI ->
(* musl memchr's constants (consts_view SEGS MCH_LO (MCH_LO + 32) at the call follows from this, state-free) *)
asn_rom_bytes SEGS B MCH_LO MCH_CONSTS ->
SRr SEGS W (cfg_at SEGS A_checkP regs mem md) (tcheck_post regs ly S W mem md r bs).
(* ---- the walk ---------------------------------------------------------------------------------------
   The symbolic state the walk runs on. The registers are the atoms of the entry state (sr_atoms); the
   shadow base is atom 32, the row count n atom 33, and the ten row words the code loads are atoms 34..43
   (row i's base at 34 + 2 i, its width at 35 + 2 i). The registry block is one region of atom 10 (a0 = r)
   with those twelve words as chunks at their offsets; the fabric's chunk is the argument's own atom 11, so
   the `bne` of 0x8107c closes by itself. The row words are the 32-bit values of the block's bytes
   (ck_u32); for a row the harness's checks cover (i < n) that value is Pau's rd4, which the walk's own
   facts then bound.
   The row index i is a literal in the walk: the code keeps it in s4, which starts at `mv s4, zero` and is
   only ever incremented, so the engine's state names row i's words as atoms, not as computed addresses;
   the loop-count tests against n (atom 33) are the engine's own branches, so the walk's case split on n
   and on the inner count is exactly the branching of the listing. *)
#[local] Notation SIGMA := (@pa_sigma _ box_listing PI).
Definition CBx : sv := SOff 32 0.
(* The unsigned 32-bit word of the block's bytes at offset k. *)
Definition ck_u32 (bs : list byte) (k : Z) : Z := bytes_le_to_Z (Boxreg.bsub bs k 4).
Definition ck_row_chunk (i : nat) : list YP09.chunk :=
[YP09.mkChunk (56 * Z.of_nat i + 8) (CVal 4 (SOff (34 + 2 * i) 0));
YP09.mkChunk (56 * Z.of_nat i + 12) (CVal 4 (SOff (35 + 2 * i) 0))].
Definition ck_reg_region : YP09.region :=
YP09.mkRegion (Some 10%nat) 0 288 0 0
([YP09.mkChunk 280 (CVal 4 (SOff 33 0)); YP09.mkChunk 284 (CVal 4 (SOff 11 0))]
 ++ ck_row_chunk 0 ++ ck_row_chunk 1 ++ ck_row_chunk 2 ++ ck_row_chunk 3 ++ ck_row_chunk 4).
Definition ck_facts : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, PTR 4); (11%nat, mkAF 1 40 0);
(32%nat, mkAF SB SB 0); (33%nat, mkAF 0 5 0)] [] [].
Definition ss_ck : sstate :=
mkSS AF_check sr_atoms [stack_region 160; got_regionP; bcell_regionP 32; ck_reg_region] None ck_facts.
Definition ck_SH : list shent := [mkSHE 10 0 288].
Definition ck_extra (bs : list byte) : list word :=
map (Z_to_bv 64)
[SB; Boxreg.bx_n bs;
ck_u32 bs 8; ck_u32 bs 12; ck_u32 bs 64; ck_u32 bs 68; ck_u32 bs 120; ck_u32 bs 124;
ck_u32 bs 176; ck_u32 bs 180; ck_u32 bs 232; ck_u32 bs 236].
Definition CE (regs : bvmap 5 word) (bs : list byte) : env := Eimg (Ereg regs (ck_extra bs)).
(* The registry block's bytes, as the statement gives them. *)
Definition ck_bytes (W : world SEGS) (mem : word -> option byte) (r : Z) (bs : list byte) : Prop :=
forall i, 0 <= i < REG_SIZE ->
aview SEGS (w_H W) mem (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0))).
Lemma ck_mbyte : forall (W : world SEGS) mem r bs i,
ck_bytes W mem r bs -> 0 <= i < 288 ->
mbyte SEGS (mrestrict (w_H W) mem) (r + i) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0)).
Proof.
intros W mem r bs i HB Hi. pose proof (HB i ltac:(unfold REG_SIZE; lia)) as H.
unfold aview in H. destruct (mbyte SEGS (mrestrict (w_H W) mem) (r + i)) as [b|] eqn:Hb; [|discriminate].
cbn [option_map] in H. injection H as H. f_equal. apply bv_eq. exact H.
Qed.
Lemma ck_byte4 : forall b0 b1 b2 b3 j, 0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
(j < 4)%nat -> YO0f.le_byte (b0 + 256 * (b1 + 256 * (b2 + 256 * b3))) 4 j = nth j [b0; b1; b2; b3] 0.
Proof.
intros b0 b1 b2 b3 j H0 H1 H2 H3 Hj. unfold YO0f.le_byte.
replace (2 ^ (8 * Z.of_nat 4)) with 4294967296 by (vm_compute; reflexivity).
rewrite (Z.mod_small (b0 + 256 * (b1 + 256 * (b2 + 256 * b3))) 4294967296) by lia.
destruct j as [|[|[|[|j]]]]; try (exfalso; lia); cbn [nth].
- replace (8 * Z.of_nat 0) with 0 by (vm_compute; reflexivity).
rewrite Z.shiftr_0_r. Z.div_mod_to_equations. lia.
- replace (8 * Z.of_nat 1) with 8 by (vm_compute; reflexivity).
rewrite Z.shiftr_div_pow2 by lia. replace (2 ^ 8) with 256 by (vm_compute; reflexivity).
Z.div_mod_to_equations. lia.
- replace (8 * Z.of_nat 2) with 16 by (vm_compute; reflexivity).
rewrite Z.shiftr_div_pow2 by lia. replace (2 ^ 16) with 65536 by (vm_compute; reflexivity).
Z.div_mod_to_equations. lia.
- replace (8 * Z.of_nat 3) with 24 by (vm_compute; reflexivity).
rewrite Z.shiftr_div_pow2 by lia. replace (2 ^ 24) with 16777216 by (vm_compute; reflexivity).
Z.div_mod_to_equations. lia.
Qed.
Lemma ck_nth_firstn : forall {A} (l : list A) k j (x : A), (j < k)%nat -> nth j (firstn k l) x = nth j l x.
Proof.
intros A l k. revert l. induction k as [|k IH]; intros l j x Hj; [exfalso; lia|].
destruct l as [|a l]; [destruct j; reflexivity|].
destruct j as [|j]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.
Lemma ck_le4 : forall (l : list byte) j, length l = 4%nat -> (j < 4)%nat ->
Z_to_bv 8 (YO0f.le_byte (bytes_le_to_Z l) 4 j) = nth j l (Z_to_bv 8 0).
Proof.
intros l j HL Hj. destruct l as [|b0 [|b1 [|b2 [|b3 [|b4 l]]]]]; try discriminate.
pose proof (CheckFacts.byte_range b0) as R0. pose proof (CheckFacts.byte_range b1) as R1.
pose proof (CheckFacts.byte_range b2) as R2. pose proof (CheckFacts.byte_range b3) as R3.
rewrite Bytes.bytes_le_to_Z_le_val. cbn [map Bytes.le_val].
replace (bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * (bv_unsigned b3 + 256 * 0))))
with (bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * bv_unsigned b3))) by lia.
rewrite (ck_byte4 _ _ _ _ j R0 R1 R2 R3 Hj).
destruct j as [|[|[|[|j]]]]; try (exfalso; lia); cbn [nth]; apply Z_to_bv_bv_unsigned.
Qed.
(* A 4-byte field of the registry block reads as the unsigned word of its bytes, and, when Pau's signed
   reading of it is non-negative and below 2 ^ 31, as that reading. *)
Lemma ck_val4u : forall (W : world SEGS) mem r bs k,
ck_bytes W mem r bs -> length bs = 288%nat -> 0 <= k -> k + 4 <= 288 ->
val_mem SEGS (mrestrict (w_H W) mem) (r + k) 4 (ck_u32 bs k).
Proof.
intros W mem r bs k HB HL Hk Hk4 j Hj.
assert (HS : length (Boxreg.bsub bs k 4) = 4%nat) by (apply Boxreg.bsub_length; lia).
replace (r + k + Z.of_nat j) with (r + (k + Z.of_nat j)) by lia.
rewrite (ck_mbyte W mem r bs (k + Z.of_nat j) HB ltac:(lia)).
f_equal. unfold ck_u32. rewrite (ck_le4 (Boxreg.bsub bs k 4) j HS Hj).
unfold Boxreg.bsub. rewrite ck_nth_firstn by lia. rewrite nth_skipn.
f_equal. lia.
Qed.
Lemma ck_u32_range : forall bs k, length bs = 288%nat -> 0 <= k -> k + 4 <= 288 ->
0 <= ck_u32 bs k < 2 ^ 32.
Proof.
intros bs k HL Hk Hk4. unfold ck_u32.
apply Boxreg.le4_range. apply Boxreg.bsub_length; lia.
Qed.
(* Pau's signed reading and the unsigned word agree while the signed one is non-negative. *)
Lemma ck_u32_rd4 : forall bs k, length bs = 288%nat -> 0 <= k -> k + 4 <= 288 ->
0 <= Boxreg.rd4 bs k -> ck_u32 bs k = Boxreg.rd4 bs k.
Proof.
intros bs k HL Hk Hk4 Hpos. pose proof (ck_u32_range bs k HL Hk Hk4) as Hu.
pose proof (Boxreg.rd4_range bs k) as Hr.
unfold Boxreg.rd4, bv_swrap, bv_wrap in Hpos, Hr |- *. unfold ck_u32 in *.
change (bv_half_modulus 32) with 2147483648 in *. change (bv_modulus 32) with 4294967296 in *.
change (2 ^ 32) with 4294967296 in Hu. change (2 ^ 31) with 2147483648 in Hr.
Z.div_mod_to_equations. lia.
Qed.
(* Small arithmetic steps, proved away from the walk's context. *)
Lemma ck_u32_base : forall bs i k, length bs = 288%nat -> 0 <= i <= 4 -> k = 56 * i + 8 ->
0 <= Boxreg.bx_base bs i -> ck_u32 bs k = Boxreg.bx_base bs i.
Proof.
intros bs i k HL Hi Hk Hp. subst k. unfold Boxreg.bx_base in *. apply ck_u32_rd4; lia.
Qed.
Lemma ck_u32_nch : forall bs i k, length bs = 288%nat -> 0 <= i <= 4 -> k = 56 * i + 12 ->
0 <= Boxreg.bx_nch bs i -> ck_u32 bs k = Boxreg.bx_nch bs i.
Proof.
intros bs i k HL Hi Hk Hp. subst k. unfold Boxreg.bx_nch in *. apply ck_u32_rd4; lia.
Qed.
(* Branch conditions as arithmetic on the values the atoms hold. *)
Lemma ck_br_lt : forall (E : env) (ka kb : nat) (x y : Z), ew E ka = Z_to_bv 64 x -> ew E kb = Z_to_bv 64 y ->
0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
branch_taken BC_LT (sv_denot E (SOff ka 0)) (sv_denot E (SOff kb 0)) = (x <? y).
Proof.
intros E ka kb x y Ha Hb Hx Hy. rewrite YO0c.branch_lt.
change (bv_unsigned (sv_denot E (SOff ka 0))) with (U E (SOff ka 0)).
change (bv_unsigned (sv_denot E (SOff kb 0))) with (U E (SOff kb 0)).
rewrite (U_atom E ka x Ha ltac:(lia)), (U_atom E kb y Hb ltac:(lia)).
rewrite !YO0b.s64_small by lia. reflexivity.
Qed.
(* the width test of 0x810f4: addiw a0, nch, -41 ; bltu a0, -39 is not taken when 2 <= nch <= 40 *)
Lemma ck_width_kill : forall (E : env) (k : nat) (v : Z), ew E k = Z_to_bv 64 v -> 2 <= v <= 40 ->
branch_taken BC_LTU (sv_denot E (SOff k (-41))) (sv_denot E (SLit 18446744073709551577)) = false.
Proof.
intros E k v Hk Hv. rewrite branch_ltu_U, U_SOff, U_SLit, Hk, Z_to_bv_unsigned.
unfold bv_wrap, zcanon, M64. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small v) by lia.
assert (Hm : (v + -41) mod 2 ^ 64 = 2 ^ 64 + v - 41) by (Z.div_mod_to_equations; lia).
rewrite Hm. rewrite (Z.mod_small 18446744073709551577) by lia.
apply Z.ltb_ge. lia.
Qed.
(* the parity test of 0x810fc: andi a0, nch, 1 ; bnez a0 is not taken when the width is even *)
Lemma ck_even_kill : forall (E : env) (k : nat) (v : Z), ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
Z.even v = true ->
branch_taken BC_NE (sv_denot E (SAlu ALU_AND (SOff k 0) (SLit 1))) (sv_denot E (SLit 0)) = false.
Proof.
intros E k v Hk Hv He. rewrite branch_ne_U, U_SLit, (U_and_lit E (SOff k 0) 1 ltac:(lia)).
rewrite (U_atom E k v Hk ltac:(lia)), (CheckFacts.land1_even v ltac:(lia) He).
rewrite (zcanon_id 0) by (unfold M64; lia). reflexivity.
Qed.
(* the slice test of 0x81120: addw s1, base, nch ; blt fabric, s1 *)
Lemma ck_br_lt_sum : forall (E : env) (ka kb kc : nat) (x y z : Z),
ew E ka = Z_to_bv 64 x -> ew E kb = Z_to_bv 64 y -> ew E kc = Z_to_bv 64 z ->
0 <= x < 2 ^ 63 -> 0 <= y -> 0 <= z -> y + z < 2 ^ 63 ->
branch_taken BC_LT (sv_denot E (SOff ka 0)) (sv_denot E (SAlu ALU_ADD (SOff kb 0) (SOff kc 0)))
= (x <? y + z).
Proof.
intros E ka kb kc x y z Ha Hb Hcc Hx Hy Hz Hyz. rewrite YO0c.branch_lt.
change (bv_unsigned (sv_denot E (SOff ka 0))) with (U E (SOff ka 0)).
change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SOff kb 0) (SOff kc 0))))
with (U E (SAlu ALU_ADD (SOff kb 0) (SOff kc 0))).
rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E kb y Hb ltac:(lia)), (U_atom E kc z Hcc ltac:(lia)).
rewrite (zcanon_id (y + z)) by (unfold M64; lia).
rewrite (U_atom E ka x Ha ltac:(lia)). rewrite !YO0b.s64_small by lia. reflexivity.
Qed.
Lemma ck_br_eq0 : forall (E : env) (k : nat) (v : Z), ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
branch_taken BC_EQ (sv_denot E (SOff k 0)) (sv_denot E (SLit 0)) = (v =? 0).
Proof.
intros E k v Hk Hv. rewrite branch_eq_U, (U_atom E k v Hk ltac:(lia)), U_SLit.
rewrite (zcanon_id 0) by (unfold M64; lia). reflexivity.
Qed.
Lemma ck_br_geu_lit : forall (E : env) (k : nat) (c v : Z), ew E k = Z_to_bv 64 v ->
0 <= v < 2 ^ 64 -> 0 <= c < 2 ^ 64 ->
branch_taken BC_GEU (sv_denot E (SLit c)) (sv_denot E (SOff k 0)) = negb (c <? v).
Proof.
intros E k c v Hk Hv Hc. rewrite branch_geu_U, U_SLit, (U_atom E k v Hk ltac:(lia)).
rewrite (zcanon_id c) by (unfold M64; lia). reflexivity.
Qed.
Lemma ck_br_eq_lit : forall (E : env) (k : nat) (c v : Z), ew E k = Z_to_bv 64 v ->
0 <= v < 2 ^ 64 -> 0 <= c < 2 ^ 64 ->
branch_taken BC_EQ (sv_denot E (SLit c)) (sv_denot E (SOff k 0)) = (c =? v).
Proof.
intros E k c v Hk Hv Hc. rewrite branch_eq_U, U_SLit, (U_atom E k v Hk ltac:(lia)).
rewrite (zcanon_id c) by (unfold M64; lia). reflexivity.
Qed.
(* the short circuit of 0x8117c: bge base_j, base_i + nch_i *)
Lemma ck_br_ge_sum : forall (E : env) (ka kb kc : nat) (x y z : Z),
ew E ka = Z_to_bv 64 x -> ew E kb = Z_to_bv 64 y -> ew E kc = Z_to_bv 64 z ->
0 <= x < 2 ^ 63 -> 0 <= y -> 0 <= z -> y + z < 2 ^ 63 ->
branch_taken BC_GE (sv_denot E (SOff ka 0)) (sv_denot E (SAlu ALU_ADD (SOff kb 0) (SOff kc 0)))
= negb (x <? y + z).
Proof.
intros E ka kb kc x y z Ha Hb Hcc Hx Hy Hz Hyz. rewrite YO0c.branch_ge.
change (bv_unsigned (sv_denot E (SOff ka 0))) with (U E (SOff ka 0)).
change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SOff kb 0) (SOff kc 0))))
with (U E (SAlu ALU_ADD (SOff kb 0) (SOff kc 0))).
rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E kb y Hb ltac:(lia)), (U_atom E kc z Hcc ltac:(lia)).
rewrite (zcanon_id (y + z)) by (unfold M64; lia).
rewrite (U_atom E ka x Ha ltac:(lia)). rewrite !YO0b.s64_small by lia. reflexivity.
Qed.
(* the inner count's test of 0x811c4: beqz s7, with s7 = n - j *)
Lemma ck_br_eq0_off : forall (E : env) (k : nat) (c v : Z), ew E k = Z_to_bv 64 v ->
0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
branch_taken BC_EQ (sv_denot E (SOff k c)) (sv_denot E (SLit 0)) = (v + c =? 0).
Proof.
intros E k c v Hk Hv Hvc. rewrite branch_eq_U, U_SOff, U_SLit, Hk.
rewrite unsigned_lit_small by lia.
rewrite (zcanon_id (v + c)) by (unfold M64; lia).
rewrite (zcanon_id 0) by (unfold M64; lia). reflexivity.
Qed.
Lemma ck_npos : forall z, 0 <= z <= 5 -> z <> 0 mod 2 ^ 64 -> 1 <= z <= 5.
Proof. intros z H1 H2. change (0 mod 2 ^ 64) with 0 in H2. lia. Qed.
(* The first NUL of row i's name field: B6 says the field holds one, so memchr's found arm applies. *)
Lemma ck_first_zero : forall (W : world SEGS) mem r bs i,
ck_bytes W mem r bs -> length bs = 288%nat -> 0 <= i <= 4 ->
In (Z_to_bv 8 0) (Boxreg.bx_name bs i) ->
exists kk, 0 <= kk < 32 /\ first_byte SEGS W mem (r + (56 * i + 24)) 32 0 kk.
Proof.
intros W mem r bs i HB HL Hi HIn.
assert (HNL : length (Boxreg.bx_name bs i) = 32%nat)
by (unfold Boxreg.bx_name; apply Boxreg.bsub_length; lia).
destruct (CheckFacts.find_byte_In0 _ HIn) as [j Hj].
destruct (StrFun.find_byte_Some 0 _ j Hj) as (Hjl & (b & Hnb & Hb0) & Hlt).
exists (Z.of_nat j).
assert (HNTH : forall m, 0 <= m < 32 ->
aview SEGS (w_H W) mem (r + (56 * i + 24) + m)
= Some (bv_unsigned (nth (Z.to_nat m) (Boxreg.bx_name bs i) (Z_to_bv 8 0)))).
{ intros m Hm. replace (r + (56 * i + 24) + m) with (r + (56 * i + 24 + m)) by lia.
  rewrite (HB (56 * i + 24 + m) ltac:(unfold REG_SIZE; lia)).
  f_equal. f_equal. unfold Boxreg.bx_name, Boxreg.bsub.
  rewrite ck_nth_firstn by lia. rewrite nth_skipn. f_equal. lia. }
split; [lia|]. split; [lia|]. split.
- intros m Hm. exists (bv_unsigned (nth (Z.to_nat m) (Boxreg.bx_name bs i) (Z_to_bv 8 0))).
  split; [apply HNTH; lia|].
  destruct (nth_error (Boxreg.bx_name bs i) (Z.to_nat m)) as [bb|] eqn:Hbb.
  + rewrite (nth_error_nth _ _ (Z_to_bv 8 0) Hbb). exact (Hlt (Z.to_nat m) bb ltac:(lia) Hbb).
  + apply nth_error_None in Hbb. lia.
- intros _. rewrite (HNTH (Z.of_nat j) ltac:(lia)). f_equal. rewrite Nat2Z.id.
  rewrite (nth_error_nth _ _ (Z_to_bv 8 0) Hnb). exact Hb0.
Qed.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_box) (PI := PI).
(* The registry block's bytes are the same after any step of the walk: they are a block of the state and
   the walk's footprint is empty. *)
Lemma ck_bytes_j : forall ly S W mem md memX mdX r bs sp0,
ajournal SEGS B CHECK_STK sp0 [] ly S W mem md [] ly S W memX mdX 0 ->
In (r, REG_SIZE) (ablocks B ly S) -> ck_bytes W mem r bs -> ck_bytes W memX r bs.
Proof.
intros ly S W mem md memX mdX r bs sp0 HJ Hin HBY i Hi.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HJblk & _).
rewrite (HJblk r REG_SIZE i Hin Hin ltac:(change (req_size REG_SIZE) with 288; unfold REG_SIZE in Hi; lia)
ltac:(apply inFP_nil)).
exact (HBY i Hi).
Qed.
Lemma ck_denot_off : forall (E : env) n v c, ew E n = Z_to_bv 64 v ->
sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof.
intros E n v c H. cbn [sv_denot]. rewrite H. apply bv_eq. rewrite !Z_to_bv_unsigned.
unfold bv_wrap. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma ck_src_ok_blk : forall (W : world SEGS) memX (regsT : bvmap 5 word) r bs lo n,
ck_bytes W memX r bs -> 0 <= lo -> 0 <= n -> lo + n <= 288 ->
(forall a, r <= a < r + 288 -> ~ (spZ regsT - ESTACK <= a < spZ regsT)) ->
src_ok SEGS W regsT memX (r + lo) n.
Proof.
intros W memX regsT r bs lo n HB Hlo Hn Hhi Hw a Ha.
split; [| apply Hw; lia].
pose proof (HB (a - r) ltac:(unfold REG_SIZE; lia)) as Hb.
replace (r + (a - r)) with a in Hb by lia. rewrite Hb. discriminate.
Qed.
(* memchr's first_byte index of a name field that holds a NUL (B6) is inside the field. *)
Lemma ck_kk_lt : forall (W : world SEGS) mem r bs i kk,
ck_bytes W mem r bs -> length bs = 288%nat -> 0 <= i <= 4 ->
In (Z_to_bv 8 0) (Boxreg.bx_name bs i) ->
first_byte SEGS W mem (r + (56 * i + 24)) 32 0 kk -> 0 <= kk < 32.
Proof.
intros W mem r bs i kk HB HL Hi HIn Hfb.
destruct (ck_first_zero W mem r bs i HB HL Hi HIn) as (j & Hj & Hfbj).
destruct Hfb as (Hk0 & Hlt & Hat). destruct Hfbj as (_ & _ & Hatj).
split; [lia|].
destruct (Z.lt_ge_cases kk 32) as [Hlt32 | Hge32]; [exact Hlt32|].
exfalso. destruct (Hlt j ltac:(lia)) as (b & Hb & Hbn). rewrite (Hatj ltac:(lia)) in Hb.
injection Hb as Hb. apply Hbn. symmetry. exact Hb.
Qed.
Hypothesis AMEMCHR : amemchr_realizesM SEGS B MCH_LO (MCH_LO + 32) (SIGMA BS___interceptor_trampoline_memchr).
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA BS___interceptor_trampoline_bcmp).
(* memchr through the trampoline, in the journal form of lib/Reusable/YCbq.v aj_memcmp_at / aj_bcmp_at: the contract
   (MemchrDef.v amemchr_realizes) takes ESTACK of present stack below the caller's sp (ecall_pre), and its post keeps
   every byte outside [sp - ESTACK, sp). *)
Lemma ck_memchr_at : forall lo hi pc, amemchr_realizesM SEGS B lo hi pc ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x c n (o : Z) raw,
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 c -> getr regsT 12 = w64 n ->
0 <= c < 256 -> 0 <= n < 2 ^ 32 -> 0 < x -> x + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
src_ok SEGS W regsT memT x n -> amem_range x n ->
range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF x n ->
(0 < n -> shadow_hull_vis (aview SEGS (w_H W) memT) x n) ->
consts_view SEGS lo hi W memT ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\
(exists kk, first_byte SEGS W memT x n c kk /\ getr regs2 10 = (if kk <? n then w64 (x + kk) else w64 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros lo hi pc AM W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x c n o raw
HJ Ha0 Ha1 Ha2 Hc Hn Hx Hxn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hsx Hmx Hrx Hhx Hcv.
pose proof (pa_segs_low) as Hsegs.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (ESTACK = 4096) as Hes by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
assert (HPRE : ecall_pre SEGS B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o); try eassumption. rewrite Hra. exact Hraw. }
eapply SRr_mono.
{ exact (AM lyc Sc W regsT memT mdc x c n HPRE Ha0 Ha1 Ha2 Hc Hn Hx Hxn Hsx Hmx Hrx Hhx Hcv). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write SEGS B LAWS Hsegs STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
(fun a => sp0 + o - ESTACK <= a < sp0 + o) Sc own HJ).
- intros a Ha Hna. apply (Hfr a Ha). exact Hna.
- exact Hpres2.
- exact Hsame.
- intros a Ha; left; left; zlia.
- exact HAR2.
- reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfr | exact Hpres2].
Qed.
Lemma ck_entry : forall ly S W (regs : bvmap 5 word) mem md ch (r fabric : Z) (bs : list byte),
afn_pre SEGS B CHECK_STK ly S W regs mem md ch ->
getr regs 10 = w64 r -> getr regs 11 = w64 fabric ->
In (r, REG_SIZE) (ablocks B ly S) -> ck_bytes W mem r bs ->
Boxreg.boxreg_B16 bs -> Boxreg.bx_fabric bs = fabric ->
st_ok_pi SEGS VAL (CE regs bs) ss_ck
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_checkP) mem (seg_rom SEGS)))
/\ sh_ok SEGS CBx ck_SH (CE regs bs) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md ch r fabric bs HPRE H10 H11 Hin HBY HB16 HFA.
pose proof HB16 as (HL & HB1 & HB2 & _).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : CHECK_STK = 8352) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md r REG_SIZE HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & _).
change (req_size REG_SIZE) with 288 in Hrceil, Hria.
pose proof (blk_off_imgP B ly S W mem md r REG_SIZE HAR Hin) as Himg.
change (req_size REG_SIZE) with 288 in Himg.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 1 ltac:(lia)) as HgotR. pose proof (pa_obj_img 12 ltac:(lia)) as HcellR.
pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_val_range (A_OBJ 1)) as Vg. pose proof (pa_val_range (A_OBJ 12)) as Vc.
rewrite restrict_mkst_fx.
set (E := CE regs bs).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs (ck_extra bs)) k)
by (intros k Hk; subst E; unfold CE; apply Eimg_low; exact Hk).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 r)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 fabric)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (Boxreg.bx_n bs))
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (ck_u32 bs 8))
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (ck_u32 bs 12))
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (ck_u32 bs 64))
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 (ck_u32 bs 68))
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 (ck_u32 bs 120))
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 6)).
assert (E39 : ew E 39 = Z_to_bv 64 (ck_u32 bs 124))
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 7)).
assert (E40 : ew E 40 = Z_to_bv 64 (ck_u32 bs 176))
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 8)).
assert (E41 : ew E 41 = Z_to_bv 64 (ck_u32 bs 180))
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 9)).
assert (E42 : ew E 42 = Z_to_bv 64 (ck_u32 bs 232))
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 10)).
assert (E43 : ew E 43 = Z_to_bv 64 (ck_u32 bs 236))
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 11)).
assert (Eg : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)))
by (subst E; unfold CE; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Ec : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
by (subst E; unfold CE; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall k v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some k) = v)
by (intros k v Hk Hv; cbn [base_val]; rewrite Hk; apply unsigned_lit_small; exact Hv).
split.
- unfold ss_ck, A_checkP. apply pa_entry_st_ok_full.
+ subst E. unfold CE. apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold stack_region, got_regionP, bcell_regionP, ck_reg_region.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite WS. lia.
* rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Eg) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
[cbn [sv_denot]; rewrite Ec, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
* rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Ec) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 CBx SB);
[cbn [sv_denot CBx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
* rewrite (VB 10%nat r E10) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
unfold ck_row_chunk. cbn [app Z.of_nat Nat.add Nat.mul].
repeat apply Forall_cons; try apply Forall_nil.
-- apply (chunk_ok_val SEGS E _ r 280 4 (SOff 33 0) (Boxreg.bx_n bs));
[cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| cbn; unfold Boxreg.boxreg_B1 in HB1; lia | zside |].
unfold Boxreg.bx_n. rewrite <- (ck_u32_rd4 bs 280 HL ltac:(lia) ltac:(lia)
ltac:(unfold Boxreg.boxreg_B1, Boxreg.bx_n in HB1; lia)).
exact (ck_val4u W mem r bs 280 HBY HL ltac:(lia) ltac:(lia)).
-- apply (chunk_ok_val SEGS E _ r 284 4 (SOff 11 0) fabric);
[cbn [sv_denot]; rewrite E11, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| cbn; unfold Boxreg.boxreg_B2 in HB2; rewrite HFA in HB2; lia | zside |].
rewrite <- HFA. unfold Boxreg.bx_fabric.
rewrite <- (ck_u32_rd4 bs 284 HL ltac:(lia) ltac:(lia)
ltac:(unfold Boxreg.boxreg_B2, Boxreg.bx_fabric in HB2; lia)).
exact (ck_val4u W mem r bs 284 HBY HL ltac:(lia) ltac:(lia)).
-- apply (chunk_ok_val SEGS E _ r 8 4 (SOff 34 0) (ck_u32 bs 8));
[cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| cbn; pose proof (ck_u32_range bs 8 HL ltac:(lia) ltac:(lia)); lia | zside |].
exact (ck_val4u W mem r bs 8 HBY HL ltac:(lia) ltac:(lia)).
-- apply (chunk_ok_val SEGS E _ r 12 4 (SOff 35 0) (ck_u32 bs 12));
[cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| cbn; pose proof (ck_u32_range bs 12 HL ltac:(lia) ltac:(lia)); lia | zside |].
exact (ck_val4u W mem r bs 12 HBY HL ltac:(lia) ltac:(lia)).
-- apply (chunk_ok_val SEGS E _ r 64 4 (SOff 36 0) (ck_u32 bs 64));
[cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| cbn; pose proof (ck_u32_range bs 64 HL ltac:(lia) ltac:(lia)); lia | zside |].
exact (ck_val4u W mem r bs 64 HBY HL ltac:(lia) ltac:(lia)).
-- apply (chunk_ok_val SEGS E _ r 68 4 (SOff 37 0) (ck_u32 bs 68));
[cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| cbn; pose proof (ck_u32_range bs 68 HL ltac:(lia) ltac:(lia)); lia | zside |].
exact (ck_val4u W mem r bs 68 HBY HL ltac:(lia) ltac:(lia)).
-- apply (chunk_ok_val SEGS E _ r 120 4 (SOff 38 0) (ck_u32 bs 120));
[cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| cbn; pose proof (ck_u32_range bs 120 HL ltac:(lia) ltac:(lia)); lia | zside |].
exact (ck_val4u W mem r bs 120 HBY HL ltac:(lia) ltac:(lia)).
-- apply (chunk_ok_val SEGS E _ r 124 4 (SOff 39 0) (ck_u32 bs 124));
[cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| cbn; pose proof (ck_u32_range bs 124 HL ltac:(lia) ltac:(lia)); lia | zside |].
exact (ck_val4u W mem r bs 124 HBY HL ltac:(lia) ltac:(lia)).
-- apply (chunk_ok_val SEGS E _ r 176 4 (SOff 40 0) (ck_u32 bs 176));
[cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| cbn; pose proof (ck_u32_range bs 176 HL ltac:(lia) ltac:(lia)); lia | zside |].
exact (ck_val4u W mem r bs 176 HBY HL ltac:(lia) ltac:(lia)).
-- apply (chunk_ok_val SEGS E _ r 180 4 (SOff 41 0) (ck_u32 bs 180));
[cbn [sv_denot]; rewrite E41, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| cbn; pose proof (ck_u32_range bs 180 HL ltac:(lia) ltac:(lia)); lia | zside |].
exact (ck_val4u W mem r bs 180 HBY HL ltac:(lia) ltac:(lia)).
-- apply (chunk_ok_val SEGS E _ r 232 4 (SOff 42 0) (ck_u32 bs 232));
[cbn [sv_denot]; rewrite E42, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| cbn; pose proof (ck_u32_range bs 232 HL ltac:(lia) ltac:(lia)); lia | zside |].
exact (ck_val4u W mem r bs 232 HBY HL ltac:(lia) ltac:(lia)).
-- apply (chunk_ok_val SEGS E _ r 236 4 (SOff 43 0) (ck_u32 bs 236));
[cbn [sv_denot]; rewrite E43, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| cbn; pose proof (ck_u32_range bs 236 HL ltac:(lia) ltac:(lia)); lia | zside |].
exact (ck_val4u W mem r bs 236 HBY HL ltac:(lia) ltac:(lia)).
+ apply pairwise_disjoint_of_extents.
unfold stack_region, got_regionP, bcell_regionP, ck_reg_region, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Eg) by lia. rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Ec) by lia.
rewrite (VB 10%nat r E10) by lia. cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil Hr4096 Hrceil HgotR HcellR HgcD Himg C1 C2 C3 C4 C5 WS Hstk0. clear.
unfold ASAN_CEIL. intros. repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [ck_facts f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
unfold Boxreg.boxreg_B1 in HB1. unfold Boxreg.boxreg_B2 in HB2. rewrite HFA in HB2.
rewrite Usp, E10, E11, E32, E33, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hal16 Hslo Hshi H47 Hceil C1 C2 C3 C4 C5 WS Hstk0 Hr16 Hr4096 Hrceil HB1 HB2. clear. unfold SB.
intros. repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, ck_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem E CBx 10 r 288 r 0 288).
+ eapply (range_addressable_of_block SEGS B LAWS ly S W mem md r REG_SIZE r 288 HAR Hin);
[lia | change (req_size REG_SIZE) with 288; lia].
+ unfold CBx. rewrite (U_atom E 32 SB E32) by (unfold SB; lia). reflexivity.
+ exact (U_atom E 10 r E10 ltac:(lia)).
+ lia.
+ lia.
+ intros x Hx. rewrite Z.min_l in Hx by lia. rewrite Z.max_r in Hx by lia.
revert Hx Hria Hr4096 Hrceil C1 C2 C3 C4 C5. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL.
clear. intros. lia.
Qed.
Ltac ck_norm HSx :=
lazymatch type of HSx with st_ok_pi ?a ?b ?c ?ssx ?d =>
let v := eval vm_compute in ssx in change ssx with v in HSx end.
(* an equation about an atom of the entry env, moved to the env the run left *)
Ltac ck_env :=
lazymatch goal with
| HSx : st_ok_pi _ _ ?Ef _ _ |- _ => Ef
| HSx : st_ok _ ?Ef _ _ |- _ => Ef
end.
Ltac ck_lift Hold Hnew :=
lazymatch type of Hold with ew _ ?k = ?v =>
let Ef := ck_env in
assert (Hnew : ew Ef k = v) by
(let HT := fresh "HT" in pose proof Hold as HT;
rewrite ?ew_havoc_old in HT by lia; rewrite ?ew_ewset_other in HT by lia;
rewrite ?ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; exact HT) end.
(* add a range fact for an atom to the symbolic state *)
Ltac ck_fact HSx kk f tac :=
lazymatch type of HSx with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let H2 := fresh "HSf" in
pose proof (st_ok_pi_add_fact Ex ssx msx kk f HSx ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; tac)) as H2;
clear HSx; rename H2 into HSx; ck_norm HSx end.
Ltac ck_run HSx HJx SHOKx Uspx :=
paj_run_tok RUN HSx HJx SHOKx Bspan;
[awr_ok_tac; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb]; rewrite ?ew_ewset_other by lia; exact Uspx |];
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* ---- the loop heads in canonical form -------------------------------------------------------------
   The two loops are walked as segment lemmas, one per (row i) and per (pair i, j), so the path count
   stays linear in the number of rows. Each lemma is stated at a loop head over a FIXED symbolic state:
   the registers the code keeps live are written with the entry's atoms (the row words 34 + 2 i and
   35 + 2 i, the shadow base 32, the row count 33, the registry base 10, the fabric 11, the image's
   ZERO 247), the registers that are dead at the head are given fresh atoms 512.. (a walk reaches a head
   with whatever atoms its calls left there, and `ck_reband` renames them), the frame holds the words
   the prologue and the latches wrote, and the facts are the walk's invariant: 0 <= base_m <= 38 and
   2 <= nch_m <= 40 for every row m the head has passed, and the row count's lower bound. *)
Definition CK_OH_CLOB : list (bv 5) := [1; 5; 6; 7; 8; 9; 10; 11; 12; 14; 15; 16; 17; 19; 21; 22; 23; 28; 29; 30; 31]%bv.
(* the thirteen saved words of the prologue, [sp0 - 104, sp0) *)
Definition ck_saved : list YP09.chunk :=
[YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0));
YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0));
YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].
(* the spill words: +0x08 and +0x18 the row count, +0x10 the fabric, +0x20 r, +0x28 i, +0x30 r + 56 (i + 1).
   The order is the order of the stores on the way to the head (a store moves its word to the front). *)
Definition ck_oh_chunks (i : nat) : list YP09.chunk :=
match i with
| O => [YP09.mkChunk (-144) (CVal 8 (SOff 11 0)); YP09.mkChunk (-152) (CVal 8 (SOff 33 0));
        YP09.mkChunk (-112) (CVal 8 (SOff 10 56)); YP09.mkChunk (-136) (CVal 8 (SOff 33 0));
        YP09.mkChunk (-128) (CVal 8 (SOff 10 0))] ++ ck_saved
| S _ => [YP09.mkChunk (-112) (CVal 8 (SOff 10 (56 * (Z.of_nat i + 1))));
          YP09.mkChunk (-120) (CVal 8 (SLit (Z.of_nat i)));
          YP09.mkChunk (-144) (CVal 8 (SOff 11 0)); YP09.mkChunk (-152) (CVal 8 (SOff 33 0));
          YP09.mkChunk (-136) (CVal 8 (SOff 33 0)); YP09.mkChunk (-128) (CVal 8 (SOff 10 0))] ++ ck_saved
end.
(* at an inner head row i's body has already written i + 1 to the spill at +0x28 *)
Definition ck_ih_chunks (i : nat) : list YP09.chunk :=
match i with
| O => [YP09.mkChunk (-120) (CVal 8 (SLit 1)); YP09.mkChunk (-144) (CVal 8 (SOff 11 0));
        YP09.mkChunk (-152) (CVal 8 (SOff 33 0)); YP09.mkChunk (-112) (CVal 8 (SOff 10 56));
        YP09.mkChunk (-136) (CVal 8 (SOff 33 0)); YP09.mkChunk (-128) (CVal 8 (SOff 10 0))] ++ ck_saved
| S _ => [YP09.mkChunk (-120) (CVal 8 (SLit (Z.of_nat i + 1)));
          YP09.mkChunk (-112) (CVal 8 (SOff 10 (56 * (Z.of_nat i + 1))));
          YP09.mkChunk (-144) (CVal 8 (SOff 11 0)); YP09.mkChunk (-152) (CVal 8 (SOff 33 0));
          YP09.mkChunk (-136) (CVal 8 (SOff 33 0)); YP09.mkChunk (-128) (CVal 8 (SOff 10 0))] ++ ck_saved
end.
Definition ck_stack_region (cs : list YP09.chunk) : YP09.region := YP09.mkRegion (Some 2%nat) (-160) 0 (-160) 0 cs.
Fixpoint ck_rows_facts (m : nat) : list (nat * afact) :=
match m with
| O => [(34%nat, mkAF 0 38 0); (35%nat, mkAF 2 40 0)]
| S m' => ck_rows_facts m' ++ [((34 + 2 * S m')%nat, mkAF 0 38 0); ((35 + 2 * S m')%nat, mkAF 2 40 0)]
end.
Definition ck_base_facts : list (nat * afact) :=
[(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, PTR 4); (11%nat, mkAF 1 40 0); (32%nat, mkAF SB SB 0)].
Definition ck_oh_facts (i : nat) : facts :=
mkFacts ((33%nat, mkAF (Z.of_nat i + 1) 5 0) :: ck_base_facts ++ ck_rows_facts i) [] [].
Definition ck_ih_facts (j : nat) : facts :=
mkFacts ((33%nat, mkAF (Z.of_nat j + 1) 5 0) :: ck_base_facts ++ ck_rows_facts j) [] [].
Definition ck_oh_regs (i : nat) : list sv :=
[SLit 0; SOff 512 0; SOff 2 (-160); SOff 3 0; SOff 4 0;
SOff 513 0; SOff 514 0; SOff 515 0; SOff 516 0; SOff 517 0;
SOff 518 0; SOff 519 0; SOff 520 0; SOff 11 0;
SOff 521 0; SOff 522 0; SOff 523 0; SOff 524 0;
SOff 247 0; SOff 525 0; SLit (Z.of_nat i); SOff 526 0; SOff 527 0; SOff 528 0;
SOff 32 0; SOff 33 (-1 - Z.of_nat i);
SOff 10 (56 * (Z.of_nat i + 1) + 12); SOff 10 (56 * (Z.of_nat i + 1) + 8);
SOff 529 0; SOff 530 0; SOff 531 0; SOff 532 0].
Definition ck_ih_regs (i j : nat) : list sv :=
[SLit 0; SOff 512 0; SOff 2 (-160); SOff 3 0; SOff 4 0;
SOff 513 0; SOff 514 0; SOff 515 0;
SOff (34 + 2 * i) 0; SAlu ALU_ADD (SOff (34 + 2 * i) 0) (SOff (35 + 2 * i) 0);
SOff 516 0; SOff 517 0; SOff 518 0; SOff 519 0; SOff 520 0; SOff 521 0; SOff 522 0; SOff 523 0;
SOff 247 0; SOff 10 (56 * Z.of_nat i); SOff 10 (56 * Z.of_nat j + 12); SOff 10 (56 * Z.of_nat j);
SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff 10 (56 * Z.of_nat j + 8)) (SLit 3));
SOff 33 (- Z.of_nat j); SOff 32 0; SOff 33 (-1 - Z.of_nat i);
SOff 10 (56 * (Z.of_nat i + 1) + 12); SOff 10 (56 * (Z.of_nat i + 1) + 8);
SOff 524 0; SOff 525 0; SOff 526 0; SOff 527 0].
(* 0x810c0 and 0x81160 as offsets from the function's first slot *)
Definition ss_oh (i : nat) : sstate :=
mkSS 4468 (ck_oh_regs i)
[ck_stack_region (ck_oh_chunks i); got_regionP; bcell_regionP 32; ck_reg_region] None (ck_oh_facts i).
Definition ss_ih (i j : nat) : sstate :=
mkSS 4628 (ck_ih_regs i j)
[ck_stack_region (ck_ih_chunks i); got_regionP; bcell_regionP 32; ck_reg_region] None (ck_ih_facts j).
(* the inner latch at 0x811b4, where the pair's four paths meet: the head's state again, at that pc *)
Definition ss_lat (i j : nat) : sstate :=
mkSS 4712 (ck_ih_regs i j)
[ck_stack_region (ck_ih_chunks i); got_regionP; bcell_regionP 32; ck_reg_region] None (ck_ih_facts j).
(* Give the registers of `clob` fresh atoms k, k + 1, ... : the state's registers, memory and facts must
   not name those atoms, and the machine state does not change. A walk uses it at a loop head, where the
   registers the code does not read again still hold the atoms of the last call. *)
Lemma ck_reband : forall (H : word -> bool) k E ss ms (clob : list (bv 5)),
st_ok_pi SEGS VAL E ss (restrict H ms) -> ss_resv ss = None ->
ss_atoms_p (pband k (k + length clob)) ss = true ->
regions_wf (ss_mem ss) = true -> no_cdata (ss_mem ss) = true ->
mem_atoms_p (pband k (k + length clob)) (ss_mem ss) = true ->
reg_nodup clob = true -> forallb (fun r : bv 5 => negb (bv_eqb r 0)) clob = true ->
st_ok_pi SEGS VAL (havoc E k (map (getr (ms_regs ms)) clob))
(mkSS (ss_pc ss) (sr_sets (ss_regs ss) (junk_upd k clob)) (ss_mem ss) None (ss_facts ss))
(restrict H ms).
Proof.
intros H k E ss ms clob HS Hrv Hat Hwf Hnc Hmat Hnd Hnz.
pose proof (st_ok_pi_restrict_mkst H E ss ms HS Hrv) as Hshape.
set (rg := ms_regs ms) in *. set (mm := ms_mem ms) in *. clearbody rg mm.
rewrite Hshape in HS |- *. rewrite restrict_mkst_fx in HS |- *.
exact (st_ok_pi_after_stretch_hi k E (abs_ss VAL ss) _ rg (mrestrict H mm) (ss_mem ss) (ss_pc ss) clob
HS Hrv Hat Hwf Hnc Hmat (submem_refl _) Hnd Hnz (fun r _ => eq_refl)
ltac:(apply Forall_forall; intros rr _; split;
[intros a Ha; reflexivity | intros a Ha Hw; exact Hw])).
Qed.
Ltac ck_reband_at HS k clob :=
lazymatch type of HS with
| st_ok_pi _ _ ?E ?ss (restrict ?H ?ms) =>
let H2 := fresh "HSb" in
pose proof (ck_reband H k E ss ms clob HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as H2;
clear HS; rename H2 into HS; ck_norm HS
end.
(* keep only the walk's invariant facts (and no branch conditions) *)
Ltac ck_setfacts HS fa :=
lazymatch type of HS with st_ok_pi _ _ ?E ?ss ?ms =>
let H2 := fresh "HSf" in
pose proof (st_ok_pi_facts_incl3 E ss ms (f_atoms fa) (f_conds fa) (f_alias fa) HS
ltac:(let v := eval vm_compute in (f_atoms fa) in change (f_atoms fa) with v;
intros x Hx; repeat (destruct Hx as [<- | Hx]; [cbn [ss_facts f_atoms];
repeat (first [left; reflexivity | right])|]); destruct Hx)
ltac:(let v := eval vm_compute in (f_conds fa) in change (f_conds fa) with v; intros x Hx; destruct Hx)
ltac:(let v := eval vm_compute in (f_alias fa) in change (f_alias fa) with v; intros x Hx; destruct Hx)) as H2;
clear HS; rename H2 into HS; ck_norm HS
end.
(* the state of a walk is the head's state *)
Ltac ck_fit HS ssx :=
let v := eval vm_compute in ssx in
lazymatch type of HS with st_ok_pi _ _ _ ?s _ =>
first [ constr_eq s v | idtac "FIT MISMATCH"; idtac "GOT" s; idtac "WANT" v; fail 1 "ck_fit" ];
change s with ssx in HS
end.
(* The statement's premises, as one proposition, so that a segment lemma carries them in one hypothesis. *)
Definition ck_ctx (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) (r fabric : Z) (bs : list byte)
(G : list (Z * Z)) : Prop :=
afn_pre SEGS B CHECK_STK ly S W regs mem md ch /\
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) /\
getr regs 10 = w64 r /\ getr regs 11 = w64 fabric /\
In (r, REG_SIZE) (ablocks B ly S) /\ ck_bytes W mem r bs /\
Boxreg.boxreg_B16 bs /\ Boxreg.bx_fabric bs = fabric /\
img_shadow_vis SEGS B /\ globs_marked SEGS B G /\
asn_rom_bytes SEGS B (VAL (A_OBJ 6)) (map (fun b : byte => bv_unsigned b) Boxreg.zero6) /\
In (VAL (A_OBJ 6), 6) G /\ IMG_LO + 64 <= VAL (A_OBJ 6) /\ VAL (A_OBJ 6) + 6 + 64 <= IMG_HI /\
asn_rom_bytes SEGS B MCH_LO MCH_CONSTS.
(* "from this head the function returns and its post holds": the walk's segment lemmas. *)
Definition ck_at (ssx : sstate) (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (r : Z) (bs : list byte) : Prop :=
forall (Ex : env) (msX : machine_state) (mdX : Model),
img_env VAL A_LIM Ex ->
st_ok_pi SEGS VAL Ex ssx (restrict (w_H W) msX) ->
env_agree 44 (Ereg regs (ck_extra bs)) Ex ->
ajournal SEGS B CHECK_STK (spZ regs) [] ly S W mem md [] ly S W (ms_mem msX) mdX 0 ->
SRr SEGS W (mkCfg msX mdX) (tcheck_post regs ly S W mem md r bs).
Definition ck_oh_prop (i : nat) : Prop :=
forall ly S W regs mem md ch r fabric bs G,
ck_ctx ly S W regs mem md ch r fabric bs G -> Z.of_nat i + 1 <= Boxreg.bx_n bs ->
ck_at (ss_oh i) ly S W regs mem md r bs.
Definition ck_ih_prop (i j : nat) : Prop :=
forall ly S W regs mem md ch r fabric bs G,
ck_ctx ly S W regs mem md ch r fabric bs G -> Z.of_nat j + 1 <= Boxreg.bx_n bs ->
ck_at (ss_ih i j) ly S W regs mem md r bs.
(* The return at 0x81274: ra holds the entry's ra again (the epilogue reloaded the saved words), every
   callee-saved register holds its entry atom, and the journal gives apost_base; the registry block's
   bytes are kept (FP = []). *)
Lemma ck_ret_at : forall ly S W (regs : bvmap 5 word) mem md ch r fabric bs G (E : env) ss ms mdX,
ck_ctx ly S W regs mem md ch r fabric bs G -> env_agree 44 (Ereg regs (ck_extra bs)) E ->
st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
plookup pl_tpi (ss_pc ss) = Some (PW RET_WORD_r) ->
sr_get (ss_regs ss) 1 = SOff 1 0 ->
forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) CALLEE_SAVED = true ->
ajournal SEGS B CHECK_STK (spZ regs) [] ly S W mem md [] ly S W (ms_mem ms) mdX 0 ->
SRr SEGS W (mkCfg ms mdX) (tcheck_post regs ly S W mem md r bs).
Proof.
intros ly S W regs mem md ch r fabric bs G E ss ms mdX HCTX HAG HS Hrv Hpl H1 Hcs HJ.
pose proof HCTX as (HPRE & _ & _ & _ & Hin & HBY & _).
pose proof HPRE as (HAR & Hra & _).
pose proof pa_segs_low as Hsegs.
assert (R1 : getr (ms_regs ms) 1 = getr regs 1).
{ pose proof (st_ok_pi_restrict_reg (w_H W) E ss ms 1 HS) as R. rewrite H1 in R. cbn [sv_denot] in R.
  rewrite R, Z.add_0_r, Z_to_bv_bv_unsigned. destruct HAG as [HA _]. rewrite HA by lia.
  exact (ew_Ereg_nat regs _ 1 1%bv eq_refl). }
assert (HAE : env_agree 32 (Ereg regs (ck_extra bs)) E)
by (destruct HAG as [HA HD]; split; [intros kk Hkk; apply HA; lia | exact HD]).
eapply (RET W E ss ms mdX _ HS Hrv Hpl).
intros mat'.
unfold tcheck_post, apost_base.
exists ly, S, (ms_regs ms), (ms_mem ms); eexists.
split; [cbn [ms_regs]; rewrite R1; rewrite Hra; reflexivity|].
split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|].
split; [eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs (ck_extra bs) HS); [exact HAE | exact Hcs]|].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [apply Permutation_refl|].
intros kk Hkk.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HJblk & _).
rewrite (HJblk r REG_SIZE kk Hin Hin ltac:(change (req_size REG_SIZE) with 288; unfold REG_SIZE in Hkk; lia)
ltac:(apply inFP_nil)).
exact (HBY kk Hkk).
Qed.
Ltac ck_ret :=
lazymatch goal with
| HC : ck_ctx ?ly ?S ?W ?regs ?mem ?md ?ch ?r ?fabric ?bs ?G, HAG : env_agree 44 _ _,
  HS : st_ok_pi _ _ ?Ef ?ssf (restrict _ ?msf), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
apply (ck_ret_at ly S W regs mem md ch r fabric bs G Ef ssf msf _ HC HAG HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HJ)
end.
(* ---- the two bcmp calls of the pair test (0x81198, 0x811ac), for the walk of rows i < j ----
   Port of lib/B/Prog/BoxBReacBoxregFind.v fnd_mac_eq / fnd_bcmp_call (image B, reac_boxreg_find) to check's
   journal (CHECK_STK, frame 160): the call goes through lib/Reusable/YCbq.v aj_bcmp_at with o = -160. Row i's MAC
   is the block's bytes (ck_bytes_j); ZERO's six bytes are read-only image bytes no runtime owns (asn_rom_bytes), kept
   by the journal's image clause and read through arodata_okP, as ck_memchr_body does for MCH_CONSTS; its shadow is
   BoxRo.ro_read_ok_glob over globs_marked G and img_shadow_vis. *)
Lemma ck_zero_at : forall STK sp0 ly S (W : world SEGS) mem md ly' S' mem' md' k,
ajournal SEGS B STK sp0 [] ly S W mem md [] ly' S' W mem' md' k ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
asn_rom_bytes SEGS B (VAL (A_OBJ 6)) (map (fun b : byte => bv_unsigned b) Boxreg.zero6) ->
forall t, 0 <= t < 6 -> aview SEGS (w_H W) mem' (VAL (A_OBJ 6) + t) = Some 0.
Proof.
intros STK sp0 ly S W mem md ly' S' mem' md' k HJ HRO HZ t Ht.
destruct (HZ t ltac:(cbn [length map Boxreg.zero6 repeat]; lia)) as (Hrom & Hown & Herr & Hval).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJimg & _).
rewrite (HJimg _ ltac:(destruct Hrom as (sg & Hsg & _ & Hb); exists sg; split; [exact Hsg | exact Hb])
  Hown Herr ltac:(apply fp_spares_closed; apply sink_closed_nil)).
rewrite (HRO _ ltac:(left; destruct Hrom as (sg & Hsg & Hw & Hb); exists sg; split; [exact Hsg | split; [exact Hw | exact Hb]])
  Hown Herr).
rewrite Hval.
assert (Ht6 : t = 0 \/ t = 1 \/ t = 2 \/ t = 3 \/ t = 4 \/ t = 5) by lia.
destruct Ht6 as [-> | [-> | [-> | [-> | [-> | ->]]]]]; reflexivity.
Qed.
(* row i's MAC against six bytes, byte by byte (BoxBReacBoxregFind.v fnd_mac_eq) *)
Lemma ck_mac_iff : forall bs M i, length bs = 288%nat -> length M = 6%nat -> 0 <= i < 5 ->
(Boxreg.bx_mac bs i = M <->
forall t, 0 <= t < 6 -> nth (Z.to_nat (56 * i + t)) bs (Z_to_bv 8 0) = nth (Z.to_nat t) M (Z_to_bv 8 0)).
Proof.
intros bs M i HL HLM Hi.
assert (Lm : length (Boxreg.bx_mac bs i) = 6%nat) by (unfold Boxreg.bx_mac; apply Boxreg.bsub_length; lia).
assert (Hn : forall t, 0 <= t < 6 ->
  nth (Z.to_nat t) (Boxreg.bx_mac bs i) (Z_to_bv 8 0) = nth (Z.to_nat (56 * i + t)) bs (Z_to_bv 8 0)).
{ intros t Ht. unfold Boxreg.bx_mac, Boxreg.bsub. rewrite nth_firstn.
  destruct (Nat.ltb_spec (Z.to_nat t) (Z.to_nat 6)); [|lia]. rewrite nth_skipn. f_equal. lia. }
split.
- intros <- t Ht. symmetry. exact (Hn t Ht).
- intros H. apply (nth_ext _ _ (Z_to_bv 8 0) (Z_to_bv 8 0)); [rewrite Lm, HLM; reflexivity|].
  intros t Ht. rewrite Lm in Ht. rewrite <- (Nat2Z.id t). rewrite (Hn (Z.of_nat t)) by lia. apply H. lia.
Qed.
(* the facts both calls need: the row count, the block's bounds, the stack window, the bytes now *)
Lemma ck_bcmp_pre : forall ly S W (regs : bvmap 5 word) mem md ch r fabric bs G memT mdT,
ck_ctx ly S W regs mem md ch r fabric bs G ->
ajournal SEGS B CHECK_STK (spZ regs) [] ly S W mem md [] ly S W memT mdT 0 ->
length bs = 288%nat /\ 0 <= Boxreg.bx_n bs <= 5 /\
r mod 16 = 0 /\ 4096 <= r /\ r + 288 <= alloc_ceiling /\ amem_range r 288 /\
(forall a, r <= a < r + 288 -> ~ (spZ regs + -160 - 2 * ESTACK <= a < spZ regs + -160)) /\
(forall a, VAL (A_OBJ 6) <= a < VAL (A_OBJ 6) + 6 -> ~ (spZ regs + -160 - 2 * ESTACK <= a < spZ regs + -160)) /\
amem_range (VAL (A_OBJ 6)) 6 /\ 0 <= VAL (A_OBJ 6) /\ VAL (A_OBJ 6) + 6 <= 2 ^ 63 /\ r + 288 <= 2 ^ 63 /\
ck_bytes W memT r bs /\ (forall t, 0 <= t < 6 -> aview SEGS (w_H W) memT (VAL (A_OBJ 6) + t) = Some 0).
Proof.
intros ly S W regs mem md ch r fabric bs G memT mdT HC HJ.
pose proof HC as (HPRE & HRO & _ & _ & Hin & HBY & HB16 & _ & _ & _ & HZ & _ & HZ1 & HZ2 & _).
destruct HB16 as (HL & HB1 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (WS : CHECK_STK = 8352) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W memT mdT r REG_SIZE HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & _).
change (req_size REG_SIZE) with 288 in *.
assert (HZlo : 0x10000 + 64 <= VAL (A_OBJ 6)) by exact HZ1.
assert (HZhi : VAL (A_OBJ 6) + 6 + 64 <= 0x5f6000) by exact HZ2.
split; [exact HL|]. split; [exact HB1|].
split; [exact Hr16|]. split; [lia|]. split; [lia|].
split; [eapply (amem_range_of_block SEGS B LAWS ly S W memT mdT r REG_SIZE r 288 HAR Hin);
        [lia | change (req_size REG_SIZE) with 288; lia]|].
split; [intros a Ha; unfold ASAN_CEIL, CHECK_STK in *; lia|].
split; [intros a Ha; unfold ASAN_CEIL, CHECK_STK in *; lia|].
split; [apply amem_range_high; [lia | left; lia | lia]|].
split; [lia|]. split; [lia|]. split; [lia|].
split; [exact (ck_bytes_j ly S W mem md memT mdT r bs (spZ regs) HJ Hin HBY)|].
exact (ck_zero_at _ _ _ _ _ _ _ _ _ _ _ _ HJ HRO HZ).
Qed.
Lemma ck_bcmp_zero : forall ly S W (regs : bvmap 5 word) mem md ch r fabric bs G (regsT : bvmap 5 word) memT mdT
(i : Z),
ck_ctx ly S W regs mem md ch r fabric bs G ->
ajournal SEGS B CHECK_STK (spZ regs) [] ly S W mem md [] ly S W memT mdT 0 ->
0 <= i < Boxreg.bx_n bs ->
getr regsT 10 = w64 (r + 56 * i) -> getr regsT 11 = w64 (VAL (A_OBJ 6)) -> getr regsT 12 = w64 6 ->
spZ regsT = spZ regs + -160 -> getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
YK0s.ret_ok (getr regsT 1) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA BS___interceptor_trampoline_bcmp)) memT (seg_rom SEGS)) mdT)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (getr regsT 1) mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B CHECK_STK (spZ regs) [] ly S W mem md [] ly S W mem2 md2 0 /\
aregs_preserved regsT regs2 /\
(bv_unsigned (getr regs2 10) = 0 <-> Boxreg.bx_mac bs i = Boxreg.zero6) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs + -160 - 2 * ESTACK <= a < spZ regs + -160) ->
aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a)).
Proof.
intros ly S W regs mem md ch r fabric bs G regsT memT mdT i HC HJ Hi H10 H11 H12 Hsp Hgp Htp Hra.
pose proof HC as (_ & _ & _ & _ & Hin & _ & _ & _ & HSV & HGM & _ & HZG & HZ1 & HZ2 & _).
destruct (ck_bcmp_pre ly S W regs mem md ch r fabric bs G memT mdT HC HJ)
  as (HL & HB1 & Hr16 & Hr4096 & Hrceil & Hrm & Hrw & Hzw & Hzm & Hz0 & Hz63 & Hr63 & HBT & HZT).
pose proof pa_segs_low as Hsegs.
pose proof HJ as (HAR & _).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (WS : CHECK_STK = 8352) by reflexivity.
eapply SRr_mono.
{ eapply (aj_bcmp_at SEGS B LAWS Hsegs _ ABCMP W regsT memT CHECK_STK (spZ regs) [] ly S W mem md [] ly S mdT 0
    (r + 56 * i) (VAL (A_OBJ 6)) 6 (-160) (getr regsT 1) HJ).
  - exact H10.
  - exact H11.
  - exact H12.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - exact Hsp.
  - reflexivity.
  - lia.
  - rewrite WS, Hes. lia.
  - exact Hgp.
  - exact Htp.
  - reflexivity.
  - exact Hra.
  - intros a Ha. split.
    + replace a with (r + (a - r)) by lia. rewrite (HBT (a - r) ltac:(unfold REG_SIZE; lia)). discriminate.
    + rewrite Hsp. pose proof (Hrw a ltac:(lia)). lia.
  - intros a Ha. split.
    + replace a with (VAL (A_OBJ 6) + (a - VAL (A_OBJ 6))) by lia. rewrite (HZT (a - VAL (A_OBJ 6))) by lia. discriminate.
    + rewrite Hsp. pose proof (Hzw a Ha). lia.
  - intros a Ha. apply Hrw. lia.
  - exact Hzw.
  - eapply (amem_range_of_block SEGS B LAWS ly S W memT mdT r REG_SIZE); [exact HAR | exact Hin | lia |
      change (req_size REG_SIZE) with 288; lia].
  - exact Hzm.
  - eapply (range_addressable_of_block SEGS B LAWS ly S W memT mdT r REG_SIZE); [exact HAR | exact Hin | lia |
      change (req_size REG_SIZE) with 288; lia].
  - intros _. eapply (shadow_hull_vis_of_block SEGS B LAWS ly S W memT mdT r REG_SIZE); [exact HAR | exact Hin | lia |
      change (req_size REG_SIZE) with 288; lia | lia].
  - exact (proj1 (ro_read_ok_glob SEGS B G ly S W memT mdT (VAL (A_OBJ 6)) 6 (VAL (A_OBJ 6)) 6
      HGM HZG HSV HAR ltac:(lia) ltac:(lia) ltac:(lia) HZ1 HZ2)).
  - intros _. exact (proj2 (ro_read_ok_glob SEGS B G ly S W memT mdT (VAL (A_OBJ 6)) 6 (VAL (A_OBJ 6)) 6
      HGM HZG HSV HAR ltac:(lia) ltac:(lia) ltac:(lia) HZ1 HZ2)). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP & Hv & Hcmp & Hfr & Hpres2).
split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP|].
split; [|exact Hfr].
rewrite Hv. rewrite (ck_mac_iff bs Boxreg.zero6 i HL eq_refl ltac:(lia)). split.
- intros H0 t Ht. assert (Hv0 : v = w64 0) by (apply bv_eq; rewrite H0; reflexivity).
  pose proof (proj1 Hcmp Hv0 t Ht) as Q.
  replace (r + 56 * i + t) with (r + (56 * i + t)) in Q by lia.
  rewrite (HBT (56 * i + t) ltac:(unfold REG_SIZE; lia)), (HZT t Ht) in Q. injection Q as Q.
  unfold Boxreg.zero6. rewrite nth_repeat. apply bv_eq. rewrite Q. reflexivity.
- intros Q. assert (Hv0 : v = w64 0).
  { apply Hcmp. intros t Ht. replace (r + 56 * i + t) with (r + (56 * i + t)) by lia.
    rewrite (HBT (56 * i + t) ltac:(unfold REG_SIZE; lia)), (HZT t Ht).
    rewrite (Q t Ht). unfold Boxreg.zero6. rewrite nth_repeat. reflexivity. }
  rewrite Hv0. reflexivity.
Qed.
Lemma ck_bcmp_rows : forall ly S W (regs : bvmap 5 word) mem md ch r fabric bs G (regsT : bvmap 5 word) memT mdT
(i j : Z),
ck_ctx ly S W regs mem md ch r fabric bs G ->
ajournal SEGS B CHECK_STK (spZ regs) [] ly S W mem md [] ly S W memT mdT 0 ->
0 <= i < Boxreg.bx_n bs -> 0 <= j < Boxreg.bx_n bs ->
getr regsT 10 = w64 (r + 56 * i) -> getr regsT 11 = w64 (r + 56 * j) -> getr regsT 12 = w64 6 ->
spZ regsT = spZ regs + -160 -> getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
YK0s.ret_ok (getr regsT 1) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA BS___interceptor_trampoline_bcmp)) memT (seg_rom SEGS)) mdT)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (getr regsT 1) mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B CHECK_STK (spZ regs) [] ly S W mem md [] ly S W mem2 md2 0 /\
aregs_preserved regsT regs2 /\
(bv_unsigned (getr regs2 10) = 0 <-> Boxreg.bx_mac bs i = Boxreg.bx_mac bs j) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs + -160 - 2 * ESTACK <= a < spZ regs + -160) ->
aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a)).
Proof.
intros ly S W regs mem md ch r fabric bs G regsT memT mdT i j HC HJ Hi Hj H10 H11 H12 Hsp Hgp Htp Hra.
pose proof HC as (_ & _ & _ & _ & Hin & _).
destruct (ck_bcmp_pre ly S W regs mem md ch r fabric bs G memT mdT HC HJ)
  as (HL & HB1 & Hr16 & Hr4096 & Hrceil & Hrm & Hrw & _ & _ & _ & _ & Hr63 & HBT & _).
pose proof pa_segs_low as Hsegs.
pose proof HJ as (HAR & _).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (WS : CHECK_STK = 8352) by reflexivity.
assert (Lj : length (Boxreg.bx_mac bs j) = 6%nat) by (unfold Boxreg.bx_mac; apply Boxreg.bsub_length; lia).
eapply SRr_mono.
{ eapply (aj_bcmp_at SEGS B LAWS Hsegs _ ABCMP W regsT memT CHECK_STK (spZ regs) [] ly S W mem md [] ly S mdT 0
    (r + 56 * i) (r + 56 * j) 6 (-160) (getr regsT 1) HJ).
  - exact H10.
  - exact H11.
  - exact H12.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - exact Hsp.
  - reflexivity.
  - lia.
  - rewrite WS, Hes. lia.
  - exact Hgp.
  - exact Htp.
  - reflexivity.
  - exact Hra.
  - intros a Ha. split.
    + replace a with (r + (a - r)) by lia. rewrite (HBT (a - r) ltac:(unfold REG_SIZE; lia)). discriminate.
    + rewrite Hsp. pose proof (Hrw a ltac:(lia)). lia.
  - intros a Ha. split.
    + replace a with (r + (a - r)) by lia. rewrite (HBT (a - r) ltac:(unfold REG_SIZE; lia)). discriminate.
    + rewrite Hsp. pose proof (Hrw a ltac:(lia)). lia.
  - intros a Ha. apply Hrw. lia.
  - intros a Ha. apply Hrw. lia.
  - eapply (amem_range_of_block SEGS B LAWS ly S W memT mdT r REG_SIZE); [exact HAR | exact Hin | lia |
      change (req_size REG_SIZE) with 288; lia].
  - eapply (amem_range_of_block SEGS B LAWS ly S W memT mdT r REG_SIZE); [exact HAR | exact Hin | lia |
      change (req_size REG_SIZE) with 288; lia].
  - eapply (range_addressable_of_block SEGS B LAWS ly S W memT mdT r REG_SIZE); [exact HAR | exact Hin | lia |
      change (req_size REG_SIZE) with 288; lia].
  - intros _. eapply (shadow_hull_vis_of_block SEGS B LAWS ly S W memT mdT r REG_SIZE); [exact HAR | exact Hin | lia |
      change (req_size REG_SIZE) with 288; lia | lia].
  - eapply (range_addressable_of_block SEGS B LAWS ly S W memT mdT r REG_SIZE); [exact HAR | exact Hin | lia |
      change (req_size REG_SIZE) with 288; lia].
  - intros _. eapply (shadow_hull_vis_of_block SEGS B LAWS ly S W memT mdT r REG_SIZE); [exact HAR | exact Hin | lia |
      change (req_size REG_SIZE) with 288; lia | lia]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP & Hv & Hcmp & Hfr & Hpres2).
split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP|].
split; [|exact Hfr].
rewrite Hv. rewrite (ck_mac_iff bs (Boxreg.bx_mac bs j) i HL Lj ltac:(lia)).
assert (Hmj : forall t, 0 <= t < 6 ->
  nth (Z.to_nat t) (Boxreg.bx_mac bs j) (Z_to_bv 8 0) = nth (Z.to_nat (56 * j + t)) bs (Z_to_bv 8 0)).
{ intros t Ht. symmetry. apply (proj1 (ck_mac_iff bs (Boxreg.bx_mac bs j) j HL Lj ltac:(lia)) eq_refl t Ht). }
split.
- intros H0 t Ht. assert (Hv0 : v = w64 0) by (apply bv_eq; rewrite H0; reflexivity).
  pose proof (proj1 Hcmp Hv0 t Ht) as Q.
  replace (r + 56 * i + t) with (r + (56 * i + t)) in Q by lia.
  replace (r + 56 * j + t) with (r + (56 * j + t)) in Q by lia.
  rewrite (HBT (56 * i + t) ltac:(unfold REG_SIZE; lia)), (HBT (56 * j + t) ltac:(unfold REG_SIZE; lia)) in Q.
  injection Q as Q. rewrite (Hmj t Ht). apply bv_eq. exact Q.
- intros Q. assert (Hv0 : v = w64 0).
  { apply Hcmp. intros t Ht.
    replace (r + 56 * i + t) with (r + (56 * i + t)) by lia.
    replace (r + 56 * j + t) with (r + (56 * j + t)) by lia.
    rewrite (HBT (56 * i + t) ltac:(unfold REG_SIZE; lia)), (HBT (56 * j + t) ltac:(unfold REG_SIZE; lia)).
    rewrite (Q t Ht), (Hmj t Ht). reflexivity. }
  rewrite Hv0. reflexivity.
Qed.
Lemma ck_agree_ewset : forall k0 n E0 E v, (k0 <= n)%nat -> env_agree k0 E0 E -> env_agree k0 E0 (ewset E n v).
Proof.
intros k0 n E0 E v Hn [HA HD]. split;
[intros m Hm; rewrite ew_ewset_other by lia; apply HA; lia | cbn [ed ewset]; exact HD].
Qed.
Ltac ck_agr H := first [ exact H
| apply env_agree_havoc_ge; [cbv; lia | ck_agr H]
| apply ck_agree_ewset; [cbv; lia | ck_agr H] ].
Ltac ck_ew_in H := repeat first [rewrite ew_havoc_old in H by lia | rewrite ew_ewset_other in H by lia].
(* the stack pointer equation at any env the walk made from the head's *)
Ltac ck_usp_by U := first [ exact U
| let U2 := fresh "U2" in pose proof U as U2;
  cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb] in U2 |- *;
  repeat first [rewrite ew_havoc_old by lia | rewrite ew_ewset_other by lia]; ck_ew_in U2; exact U2 ].
Ltac ck_head_intro :=
try unfold ck_oh_prop; try unfold ck_ih_prop; unfold ck_at;
intros ly S W regs mem md ch r fabric bs G HCTX HNB Ex msX mdX HEI HS HAG HJ;
pose proof HCTX as HCc;
destruct HCc as (HPRE & HROD & H10 & H11 & Hin & HBY & HB16 & HFA & HIMG & HGL & HZ & HZIN & HZLO & HZHI & HMCH);
pose proof HB16 as (HL & HB1 & HB2 & HB3 & HB4 & HB5 & HB6);
unfold Boxreg.boxreg_B1 in HB1; unfold Boxreg.boxreg_B2 in HB2;
pose proof (pa_wx) as Hwx; pose proof (pa_segs_low) as Hsegs;
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT);
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2);
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5);
destruct (al_blocks _ _ LAWS ly S W mem md r REG_SIZE HAR0 Hin) as (Hr16 & Hr4096 & Hrceil & Hria & HrNN);
change (req_size REG_SIZE) with 288 in Hrceil, Hria;
assert (HF : 1 <= fabric <= 40) by (rewrite <- HFA; exact HB2);
pose proof HAG as HAGd; destruct HAGd as [HA44 HD44];
assert (E1 : ew Ex 1 = getr regs 1) by (rewrite HA44 by lia; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl));
assert (E2 : ew Ex 2 = getr regs 2) by (rewrite HA44 by lia; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl));
assert (E3 : ew Ex 3 = getr regs 3) by (rewrite HA44 by lia; exact (ew_Ereg_nat regs _ 3 3%bv eq_refl));
assert (E4 : ew Ex 4 = getr regs 4) by (rewrite HA44 by lia; exact (ew_Ereg_nat regs _ 4 4%bv eq_refl));
assert (Usp : bv_unsigned (ew Ex 2) = spZ regs) by (rewrite E2; reflexivity);
assert (E10 : ew Ex 10 = Z_to_bv 64 r)
by (rewrite HA44 by lia; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10);
assert (E11 : ew Ex 11 = Z_to_bv 64 fabric)
by (rewrite HA44 by lia; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11);
assert (E32 : ew Ex 32 = Z_to_bv 64 SB) by (rewrite HA44 by lia; exact (ew_Ereg_extra regs _ 0));
assert (E33 : ew Ex 33 = Z_to_bv 64 (Boxreg.bx_n bs)) by (rewrite HA44 by lia; exact (ew_Ereg_extra regs _ 1));
assert (E34 : ew Ex 34 = Z_to_bv 64 (ck_u32 bs 8)) by (rewrite HA44 by lia; exact (ew_Ereg_extra regs _ 2));
assert (E35 : ew Ex 35 = Z_to_bv 64 (ck_u32 bs 12)) by (rewrite HA44 by lia; exact (ew_Ereg_extra regs _ 3));
assert (E36 : ew Ex 36 = Z_to_bv 64 (ck_u32 bs 64)) by (rewrite HA44 by lia; exact (ew_Ereg_extra regs _ 4));
assert (E37 : ew Ex 37 = Z_to_bv 64 (ck_u32 bs 68)) by (rewrite HA44 by lia; exact (ew_Ereg_extra regs _ 5));
assert (E38 : ew Ex 38 = Z_to_bv 64 (ck_u32 bs 120)) by (rewrite HA44 by lia; exact (ew_Ereg_extra regs _ 6));
assert (E39 : ew Ex 39 = Z_to_bv 64 (ck_u32 bs 124)) by (rewrite HA44 by lia; exact (ew_Ereg_extra regs _ 7));
assert (E40 : ew Ex 40 = Z_to_bv 64 (ck_u32 bs 176)) by (rewrite HA44 by lia; exact (ew_Ereg_extra regs _ 8));
assert (E41 : ew Ex 41 = Z_to_bv 64 (ck_u32 bs 180)) by (rewrite HA44 by lia; exact (ew_Ereg_extra regs _ 9));
assert (E42 : ew Ex 42 = Z_to_bv 64 (ck_u32 bs 232)) by (rewrite HA44 by lia; exact (ew_Ereg_extra regs _ 10));
assert (E43 : ew Ex 43 = Z_to_bv 64 (ck_u32 bs 236)) by (rewrite HA44 by lia; exact (ew_Ereg_extra regs _ 11));
assert (SHOK : sh_ok SEGS CBx ck_SH Ex (mrestrict (w_H W) (ms_mem msX)));
[ unfold sh_ok, ck_SH; constructor; [|constructor];
  apply (shent_ok_of_range SEGS (w_H W) (ms_mem msX) Ex CBx 10 r 288 r 0 288);
  [ eapply (range_addressable_of_block SEGS B LAWS ly S W (ms_mem msX) _ r REG_SIZE r 288 (proj1 HJ) Hin);
    [lia | change (req_size REG_SIZE) with 288; lia]
  | unfold CBx; rewrite (U_atom Ex 32 SB E32 ltac:(unfold SB; lia)); reflexivity
  | exact (U_atom Ex 10 r E10 ltac:(lia))
  | lia | lia
  | intros x Hx; rewrite Z.min_l in Hx by lia; rewrite Z.max_r in Hx by lia;
    revert Hx Hria Hr4096 Hrceil C1 C2 C3 C4 C5;
    unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL; clear; intros; lia ]
| ].
(* the return address a call left in the goal's pc *)
Ltac ck_ra := repeat match goal with Hq : getr _ 1%bv = Z_to_bv 64 (BASE + _) |- _ => rewrite Hq end.
(* move the walk's two standing equations (the atom map and the stack pointer) to the env a run left *)
Ltac ck_refresh_e Ec :=
lazymatch goal with
| HAG : env_agree 44 (Ereg ?regs (ck_extra ?bs)) _ |- _ =>
let H2 := fresh "HAGn" in
assert (H2 : env_agree 44 (Ereg regs (ck_extra bs)) Ec) by ck_agr HAG;
clear HAG; rename H2 into HAG
end;
lazymatch goal with
| Usp : bv_unsigned (ew _ 2) = spZ ?regs |- _ =>
let H3 := fresh "Uspn" in
assert (H3 : bv_unsigned (ew Ec 2) = spZ regs) by ck_usp_by Usp;
clear Usp; rename H3 into Usp
end.
Ltac ck_refresh :=
lazymatch goal with
| HSq : st_ok_pi _ _ ?Ec _ _ |- _ => ck_refresh_e Ec
| HSq : st_ok _ ?Ec _ _ |- _ => ck_refresh_e Ec
end.
(* the walk's env is the image env, through any band the calls and the re-bands made *)
Ltac ck_img := first [ assumption
| apply img_env_havoc_hi; [ck_img | cbv; lia]
| apply img_env_ewset_hi; [ck_img | cbv; lia] ].
Ltac ck_hei :=
lazymatch goal with HSq : st_ok_pi _ _ ?Ec _ _ |- _ =>
first [ lazymatch goal with Hq : img_env _ _ Ec |- _ => idtac end
| let H := fresh "HEI" in assert (H : img_env VAL A_LIM Ec) by ck_img ] end.
(* seat a reached state on a loop head's canonical state *)
Ltac ck_seat HS fa clob ssx :=
ck_setfacts HS fa; ck_reband_at HS 4000%nat clob; ck_reband_at HS 512%nat clob; ck_fit HS ssx;
ck_refresh; ck_hei.
Ltac ck_rn :=
lazymatch goal with
| HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _,
  Usp : bv_unsigned (ew _ 2) = spZ _ |- _ =>
paj_run_tok RUN HS HJ SHOK Bspan;
[awr_ok_tac; ck_usp_by Usp |];
repeat match goal with Hf : frame_of _ _ _ _ |- _ => clear Hf | Hg : mem_grows _ _ |- _ => clear Hg end
end; ck_refresh.
Ltac ck_rnto stop :=
lazymatch goal with
| HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _,
  Usp : bv_unsigned (ew _ 2) = spZ _ |- _ =>
paj_run_to_tok RUNTO HS HJ SHOK Bspan stop;
[awr_ok_tac; ck_usp_by Usp |];
repeat match goal with Hf : frame_of _ _ _ _ |- _ => clear Hf | Hg : mem_grows _ _ |- _ => clear Hg end
end; ck_refresh.
Ltac ck_brt :=
lazymatch goal with
| HS : st_ok_pi _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ => psrr_branch_tok RUN BR HS SHOK Bspan
end.
Ltac ck_drop_br := repeat lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => clear Hb end.
(* the equations of the atoms the walk reads, at the env of the current state *)
Ltac ck_nch_eq kn zi Gname :=
lazymatch goal with
| HC : ck_ctx _ _ _ ?regs _ _ _ _ _ ?bs _, HAG : env_agree 44 (Ereg _ (ck_extra _)) ?Ec |- _ =>
let j := eval vm_compute in (kn - 32)%nat in
let koff := eval vm_compute in (56 * zi + 12) in
let HA := fresh "HAq" in let HCq := fresh "HCq" in let HLq := fresh "HLq" in
pose proof HC as HCq; destruct HCq as (_ & _ & _ & _ & _ & _ & (HLq & _) & _);
assert (Gname : ew Ec kn = Z_to_bv 64 (Boxreg.bx_nch bs zi));
[ destruct HAG as [HA _]; rewrite HA by lia;
  rewrite <- (ck_u32_nch bs zi koff HLq ltac:(lia) ltac:(lia) ltac:(lia));
  exact (ew_Ereg_extra regs (ck_extra bs) j) | clear HLq ]
end.
Ltac ck_base_eq kb zi Gname :=
lazymatch goal with
| HC : ck_ctx _ _ _ ?regs _ _ _ _ _ ?bs _, HAG : env_agree 44 (Ereg _ (ck_extra _)) ?Ec |- _ =>
let j := eval vm_compute in (kb - 32)%nat in
let koff := eval vm_compute in (56 * zi + 8) in
let HA := fresh "HAq" in let HCq := fresh "HCq" in let HLq := fresh "HLq" in
pose proof HC as HCq; destruct HCq as (_ & _ & _ & _ & _ & _ & (HLq & _) & _);
assert (Gname : ew Ec kb = Z_to_bv 64 (Boxreg.bx_base bs zi));
[ destruct HAG as [HA _]; rewrite HA by lia;
  rewrite <- (ck_u32_base bs zi koff HLq ltac:(lia) ltac:(lia) ltac:(lia));
  exact (ew_Ereg_extra regs (ck_extra bs) j) | clear HLq ]
end.
Ltac ck_fab_eq Gname :=
lazymatch goal with
| HC : ck_ctx _ _ _ ?regs _ _ _ _ ?fabric _ _, HAG : env_agree 44 (Ereg _ (ck_extra _)) ?Ec |- _ =>
let HA := fresh "HAq" in let HCq := fresh "HCq" in let Hq := fresh "Hq" in
pose proof HC as HCq; destruct HCq as (_ & _ & _ & Hq & _);
assert (Gname : ew Ec 11 = Z_to_bv 64 fabric);
[ destruct HAG as [HA _]; rewrite HA by lia;
  rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact Hq | clear Hq ]
end.
Ltac ck_n_eq Gname :=
lazymatch goal with
| HC : ck_ctx _ _ _ ?regs _ _ _ _ _ ?bs _, HAG : env_agree 44 (Ereg _ (ck_extra _)) ?Ec |- _ =>
let HA := fresh "HAq" in
assert (Gname : ew Ec 33 = Z_to_bv 64 (Boxreg.bx_n bs))
by (destruct HAG as [HA _]; rewrite HA by lia; exact (ew_Ereg_extra regs (ck_extra bs) 1))
end.
Ltac ck_r_eq Gname :=
lazymatch goal with
| HC : ck_ctx _ _ _ ?regs _ _ _ ?r _ _ _, HAG : env_agree 44 (Ereg _ (ck_extra _)) ?Ec |- _ =>
let HA := fresh "HAq" in let HCq := fresh "HCq" in let Hq := fresh "Hq" in
pose proof HC as HCq; destruct HCq as (_ & _ & Hq & _);
assert (Gname : ew Ec 10 = Z_to_bv 64 r);
[ destruct HAG as [HA _]; rewrite HA by lia;
  rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact Hq | clear Hq ]
end.
Ltac ck_reg_eq k kr Gname :=
lazymatch goal with
| HC : ck_ctx _ _ _ ?regs _ _ _ _ _ _ _, HAG : env_agree 44 (Ereg _ (ck_extra _)) ?Ec |- _ =>
let HA := fresh "HAq" in
assert (Gname : ew Ec k = getr regs kr)
by (destruct HAG as [HA _]; rewrite HA by lia; apply (ew_Ereg_nat regs _ k kr); reflexivity)
end.
(* row zi's five model aborts (0x810ec, 0x810f8, 0x81100, 0x8111c, 0x81124), refuted by B3. *)
Ltac ck_row_aborts kbb kn zi :=
ck_rn;
lazymatch goal with
| HC : ck_ctx _ _ _ _ _ _ _ _ ?fabric _ _ |- _ =>
let GA := fresh "GA" in let GB := fresh "GB" in let GC := fresh "GC" in
let HB3q := fresh "HB3q" in let HFAq := fresh "HFAq" in let HCq := fresh "HCq" in
let Hnf := fresh "Hnf" in let Hev := fresh "Hev" in let Hsum := fresh "Hsum" in
pose proof HC as HCq; destruct HCq as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & HB3q & _) & HFAq & _);
ck_fab_eq GA; ck_nch_eq kn zi GB;
ck_brt;
[ exfalso; lazymatch goal with Hb : branch_taken _ _ _ = true |- _ =>
  lazymatch type of GB with ew ?Ec _ = _ =>
  rewrite (ck_br_lt Ec 11 kn fabric _ GA GB ltac:(lia) ltac:(lia)) in Hb end;
  apply Z.ltb_lt in Hb;
  destruct (HB3q zi ltac:(lia)) as (_ & _ & Hnf & _); rewrite HFAq in Hnf; lia end |];
clear GA GB; ck_drop_br;
ck_rn; ck_nch_eq kn zi GB;
ck_brt;
[ exfalso; lazymatch goal with Hb : branch_taken _ _ _ = true |- _ =>
  lazymatch type of GB with ew ?Ec _ = _ =>
  rewrite (ck_width_kill Ec kn _ GB ltac:(lia)) in Hb end; discriminate Hb end |];
clear GB; ck_drop_br;
ck_rn; ck_nch_eq kn zi GB;
ck_brt;
[ exfalso; lazymatch goal with Hb : branch_taken _ _ _ = true |- _ =>
  destruct (HB3q zi ltac:(lia)) as (Hev & _);
  lazymatch type of GB with ew ?Ec _ = _ =>
  rewrite (ck_even_kill Ec kn _ GB ltac:(lia) Hev) in Hb end; discriminate Hb end |];
clear GB; ck_drop_br;
ck_rn; ck_fab_eq GA; ck_nch_eq kn zi GB; ck_base_eq kbb zi GC;
ck_brt;
[ exfalso; lazymatch goal with Hb : branch_taken _ _ _ = true |- _ =>
  lazymatch type of GB with ew ?Ec _ = _ =>
  rewrite (ck_br_lt_sum Ec 11 kbb kn fabric _ _ GA GC GB
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in Hb end;
  apply Z.ltb_lt in Hb;
  destruct (HB3q zi ltac:(lia)) as (_ & _ & _ & _ & Hsum); rewrite HFAq in Hsum; lia end |];
clear GA GB GC; ck_drop_br; clear HB3q HFAq
end.
(* memchr (r + 56 i + 24, 0, 32) at 0x81134, in the M form; xoff = 56 i + 24. *)
Ltac ck_memchr_body HS xoff :=
lazymatch goal with
| HC : ck_ctx ?ly ?S ?W ?regs ?mem ?md ?ch ?r ?fabric ?bs ?G,
  HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  Usp : bv_unsigned (ew _ 2) = spZ _ |- _ =>
let Ra0 := fresh "Ra0" in let Ra1 := fresh "Ra1" in let Ra2 := fresh "Ra2" in
let Rra := fresh "Rra" in let Rsp := fresh "Rsp" in let Rgp := fresh "Rgp" in let Rtp := fresh "Rtp" in
let G10m := fresh "G10m" in let Hblkw := fresh "Hblkw" in let HBYm := fresh "HBYm" in
let Hcv := fresh "Hcv" in let Qsp := fresh "Qsp" in let E3q := fresh "E3q" in let E4q := fresh "E4q" in
let HCq := fresh "HCq" in let HPREq := fresh "HPREq" in
let HRODq := fresh "HRODq" in let HMCHq := fresh "HMCHq" in let HBYq := fresh "HBYq" in
let Hinq := fresh "Hinq" in let Hgpq := fresh "Hgpq" in let Htpq := fresh "Htpq" in
let Hes := fresh "Hes" in
assert (Hes : ESTACK = 4096) by reflexivity;
pose proof HC as HCq;
destruct HCq as (HPREq & HRODq & _ & _ & Hinq & HBYq & _ & _ & _ & _ & _ & _ & _ & _ & HMCHq);
pose proof HPREq as (_ & _ & _ & Hgpq & Htpq & _ & _ & _ & _);
ck_r_eq G10m; ck_reg_eq 3%nat (3%bv : bv 5) E3q; ck_reg_eq 4%nat (4%bv : bv 5) E4q;
pmkst HS;
prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (12%bv : bv 5) Ra2;
prreg HS (1%bv : bv 5) Rra; prreg HS (2%bv : bv 5) Rsp; prreg HS (3%bv : bv 5) Rgp; prreg HS (4%bv : bv 5) Rtp;
ck_ew_in G10m; ck_ew_in E3q; ck_ew_in E4q;
assert (Hblkw : forall a, r <= a < r + 288 -> ~ (spZ regs - CHECK_STK <= a < spZ regs))
by (unfold ASAN_CEIL, CHECK_STK in *; intros a Ha; lia);
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdQ) _ =>
assert (HBYm : ck_bytes W mm r bs);
[ apply (ck_bytes_j ly S W mem md _ _ r bs (spZ regs) HJ Hinq HBYq) | ];
assert (Hcv : consts_view SEGS MCH_LO (MCH_LO + 32) W mm);
[ intros a Ha; destruct (HMCHq (a - MCH_LO) ltac:(cbn [length MCH_CONSTS]; lia)) as (Hrom & Hown & Herr & _);
  replace (MCH_LO + (a - MCH_LO)) with a in Hrom, Hown, Herr by lia;
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJimg & _);
  rewrite (HJimg a ltac:(destruct Hrom as (sg & Hsg & _ & Hb); exists sg; split; [exact Hsg | exact Hb])
  Hown Herr ltac:(apply fp_spares_closed; apply sink_closed_nil));
  apply HRODq;
  [ left; destruct Hrom as (sg & Hsg & Hw & Hb); exists sg; split; [exact Hsg | split; [exact Hw | exact Hb]]
  | exact Hown | exact Herr ]
| ];
assert (Qsp : spZ rg = spZ regs + -160);
[ let Hu := fresh "Hu" in
  lazymatch type of Rsp with _ = Z_to_bv 64 (bv_unsigned (ew ?Ecu 2) + _) =>
  assert (Hu : bv_unsigned (ew Ecu 2) = spZ regs) by ck_usp_by Usp end;
  unfold spZ at 1; rewrite Rsp; rewrite unsigned_lit_small by (rewrite Hu; lia);
  rewrite Hu; reflexivity | ];
eapply SRr_bind;
[ eapply (ck_memchr_at MCH_LO (MCH_LO + 32) (SIGMA BS___interceptor_trampoline_memchr) AMEMCHR W rg mm
CHECK_STK (spZ regs) [] ly S W mem md [] ly S mdQ 0 (r + xoff) 0 32 (-160) _ HJ);
[ rewrite Ra0; exact (ck_denot_off _ 10 r xoff G10m)
| rewrite Ra1; reflexivity
| rewrite Ra2; reflexivity
| lia | lia | lia | lia
| exact Qsp | reflexivity | lia
| unfold CHECK_STK; lia
| rewrite Rgp; rewrite E3q; exact Hgpq
| rewrite Rtp; rewrite E4q; exact Htpq
| reflexivity
| rewrite Rra; apply ret_ok_codeptr_v; [lia | reflexivity]
| apply (ck_src_ok_blk W mm rg r bs xoff 32 HBYm ltac:(lia) ltac:(lia) ltac:(lia));
  intros a Ha; rewrite Qsp; pose proof (Hblkw a Ha); unfold CHECK_STK in *; lia
| eapply (amem_range_of_block SEGS B LAWS _ _ _ _ _ r REG_SIZE (r + xoff) 32 (proj1 HJ) Hinq);
  [lia | change (req_size REG_SIZE) with 288; lia]
| eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ r REG_SIZE (r + xoff) 32 (proj1 HJ) Hinq);
  [lia | change (req_size REG_SIZE) with 288; lia]
| intros _; eapply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ r REG_SIZE (r + xoff) 32 (proj1 HJ) Hinq);
  [lia | change (req_size REG_SIZE) with 288; lia | lia]
| exact Hcv ]
| ] end end.
Ltac ck_memchr_block xoff :=
lazymatch goal with
| HSq : st_ok_pi _ _ _ _ _ |- _ => ck_memchr_body HSq xoff
| HSq : st_ok _ _ _ _ |- _ => ck_memchr_body HSq xoff
end.
(* the four regions the walk carries are kept across a wrapper call *)
Ltac ck_keep_regions Hfr :=
lazymatch goal with |- Forall (region_kept _ ?Ec _ _) _ =>
lazymatch goal with
| HEIc : img_env _ _ Ec, HC : ck_ctx _ _ _ ?regs _ _ _ ?r _ _ _,
  Usp : bv_unsigned (ew Ec 2) = spZ _, HJq : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
let Eg2 := fresh "Eg2" in let Ec2 := fresh "Ec2" in let Er2 := fresh "Er2" in
let Gr := fresh "Gr" in let Hes := fresh "Hes" in let HJpres := fresh "HJpres" in
let HgotR := fresh "HgotR" in let HcellR := fresh "HcellR" in
assert (Hes : ESTACK = 4096) by reflexivity;
pose proof (pa_obj_img 1 ltac:(lia)) as HgotR; pose proof (pa_obj_img 12 ltac:(lia)) as HcellR;
pose proof HJq as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _);
ck_r_eq Gr;
assert (Eg2 : bv_unsigned (ew Ec 242%nat) = VAL (A_OBJ 1))
by (change 242%nat with (A_OBJ 1); apply HEIc; unfold A_OBJ, A_TEXT, A_LIM; lia);
assert (Ec2 : bv_unsigned (ew Ec 253%nat) = VAL (A_OBJ 12))
by (change 253%nat with (A_OBJ 12); apply HEIc; unfold A_OBJ, A_TEXT, A_LIM; lia);
assert (Er2 : bv_unsigned (ew Ec 10%nat) = r) by (rewrite Gr; apply unsigned_lit_small; lia);
pose proof (pa_val_range (A_OBJ 1)) as HV1; pose proof (pa_val_range (A_OBJ 12)) as HV12;
cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil;
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val];
[ rewrite Usp; intros a Ha; apply (mbyte_of_aview SEGS); apply Hfr;
  [unfold ASAN_CEIL in *; lia | unfold CHECK_STK in *; lia]
| rewrite Usp; intros a Ha _; apply (apresent_writable SEGS);
  apply HJpres; unfold CHECK_STK in *; lia
| rewrite Eg2; intros a Ha; apply (mbyte_of_aview SEGS); apply Hfr;
  [lia | unfold ASAN_CEIL, CHECK_STK in *; lia]
| intros a Ha; exfalso; lia
| rewrite Ec2; intros a Ha; apply (mbyte_of_aview SEGS); apply Hfr;
  [lia | unfold ASAN_CEIL, CHECK_STK in *; lia]
| intros a Ha; exfalso; lia
| rewrite Er2; intros a Ha; apply (mbyte_of_aview SEGS); apply Hfr;
  [lia | unfold ASAN_CEIL, CHECK_STK in *; lia]
| intros a Ha; exfalso; lia ] end end.
Ltac ck_sb_eq Gname :=
lazymatch goal with
| HC : ck_ctx _ _ _ ?regs _ _ _ _ _ ?bs _, HAG : env_agree 44 (Ereg _ (ck_extra _)) ?Ec |- _ =>
let HA := fresh "HAq" in
assert (Gname : ew Ec 32 = Z_to_bv 64 SB)
by (destruct HAG as [HA _]; rewrite HA by lia; exact (ew_Ereg_extra regs (ck_extra bs) 0))
end.
(* the registry block's shadow entry, at the current env and memory *)
Ltac ck_shok :=
lazymatch goal with
| HC : ck_ctx ?ly ?S ?W _ _ _ _ ?r _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?memc _ _,
  HS : st_ok_pi _ _ ?Ec _ _ |- _ =>
let Gr := fresh "Gr" in let Gs := fresh "Gs" in let SH := fresh "SHOK" in
let HCq := fresh "HCq" in let Hinq := fresh "Hinq" in
pose proof HC as HCq; destruct HCq as (_ & _ & _ & _ & Hinq & _);
ck_r_eq Gr; ck_sb_eq Gs;
assert (SH : sh_ok SEGS CBx ck_SH Ec (mrestrict (w_H W) memc));
[ unfold sh_ok, ck_SH; constructor; [|constructor];
  apply (shent_ok_of_range SEGS (w_H W) memc Ec CBx 10 r 288 r 0 288);
  [ eapply (range_addressable_of_block SEGS B LAWS ly S W memc _ r REG_SIZE r 288 (proj1 HJ) Hinq);
    [lia | change (req_size REG_SIZE) with 288; lia]
  | unfold CBx; rewrite (U_atom Ec 32 SB Gs ltac:(unfold SB; lia)); reflexivity
  | exact (U_atom Ec 10 r Gr ltac:(lia))
  | lia | lia
  | intros x Hx; rewrite Z.min_l in Hx by lia; rewrite Z.max_r in Hx by lia;
    try unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia ]
| clear Gr Gs Hinq ]
end.
(* the value a call returns in a0 (CLOB index 4), as an equation of its atom k *)
Ltac ck_a0 k v Hres Hname :=
lazymatch goal with HS : st_ok_pi _ _ (havoc ?Eb ?kb ?ws) _ _ |- _ =>
let j := eval vm_compute in (k - kb)%nat in
assert (Hname : ew (havoc Eb kb ws) k = Z_to_bv 64 v);
[ change k with (kb + j)%nat;
  rewrite (ew_havoc_new Eb kb ws j (Z_to_bv 64 0) ltac:(unfold CLOB; cbn [length map]; lia));
  cbn [map nth CLOB]; rewrite Hres; reflexivity | ]
end.
(* s6, the shadow address of row j's base word, after the inner latch: the latch adds 7 to
   SB + (r + 56 (j - 1) + 8) >> 3, which is SB + (r + 56 j + 8) >> 3, the next head's form. *)
Lemma ck_s6_U_step : forall (E : env) rr k0,
ew E 10 = Z_to_bv 64 rr -> ew E 32 = Z_to_bv 64 SB -> 0 <= rr -> 0 <= k0 -> rr + k0 + 56 < 2 ^ 47 ->
U E (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff 10 (k0 + 56)) (SLit 3)))
= U E (SAlu ALU_ADD (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff 10 k0) (SLit 3))) (SLit 7)).
Proof.
intros E rr k0 H10 H32 Hr Hk Hb.
rewrite !U_SAlu. cbn [zalu_raw].
rewrite !U_SOff, !U_SLit, H10, H32.
rewrite !unsigned_lit_small by (unfold SB; lia).
change (Z.land (zcanon 3) 63) with 3.
rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
unfold zcanon, M64, SB. Z.div_mod_to_equations. lia.
Qed.
Lemma ck_s6_fix : forall (H : word -> bool) E ss ms rr k0 kk,
st_ok_pi SEGS VAL E ss (restrict H ms) ->
sr_get (ss_regs ss) (22%bv : bv 5)
= SAlu ALU_ADD (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff 10 k0) (SLit 3))) (SLit 7) ->
kk = k0 + 56 ->
ew E 10 = Z_to_bv 64 rr -> ew E 32 = Z_to_bv 64 SB -> 0 <= rr -> 0 <= k0 -> rr + k0 + 56 < 2 ^ 47 ->
st_ok_pi SEGS VAL E (mkSS (ss_pc ss)
(sr_set (ss_regs ss) (22%bv : bv 5) (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff 10 kk) (SLit 3))))
(ss_mem ss) (ss_resv ss) (ss_facts ss)) (restrict H ms).
Proof.
intros H E ss ms rr k0 kk HS Hs6 Hkk H10 H32 Hr Hk Hb.
apply ast_ok_pi_set_reg_fp; [exact HS | reflexivity |].
change (getr (ms_regs (restrict H ms)) (22%bv : bv 5)) with (getr (ms_regs ms) (22%bv : bv 5)).
rewrite (st_ok_pi_restrict_reg H E ss ms (22%bv : bv 5) HS), Hs6. subst kk.
apply bv_eq. exact (ck_s6_U_step E rr k0 H10 H32 Hr Hk Hb).
Qed.
Ltac ck_fix_s6 :=
lazymatch goal with
| HS : st_ok_pi _ _ ?Ec ?ss (restrict ?Hh ?ms), HC : ck_ctx _ _ _ _ _ _ _ ?r _ _ _ |- _ =>
let e := eval vm_compute in (sr_get (ss_regs ss) (22%bv : bv 5)) in
lazymatch e with
| SAlu ALU_ADD (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff 10 ?k0) (SLit 3))) (SLit 7) =>
let kk := eval vm_compute in (k0 + 56) in
let Gr := fresh "Gr" in let Gs := fresh "Gs" in let H2 := fresh "HSs6" in
ck_r_eq Gr; ck_sb_eq Gs;
pose proof (ck_s6_fix Hh Ec ss ms r k0 kk HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
Gr Gs ltac:(lia) ltac:(lia) ltac:(lia)) as H2;
clear HS Gr Gs; rename H2 into HS; ck_norm HS
end end.
(* The two arms of the overlap test (0x8117c) meet at the bcmp call of 0x81198 in the same state, so the
   walk states the rest of the pair once: run the taken arm with the engine to `stop`, state the
   continuation at the state it reaches (with the head's facts, no branch conditions), and close both
   arms with it.  Without the join the inner loop's path count is 2 ^ (number of pairs). *)
Ltac ck_join cnd stop fa name :=
lazymatch goal with
| HC : ck_ctx ?ly ?S ?W ?regs ?mem ?md ?ch ?r ?fabric ?bs ?G,
  HS : st_ok_pi _ _ _ ?ss (restrict (w_H _) _), SHOK : sh_ok _ ?Bx ?SH _ _ |- SRr _ _ _ ?Q =>
let K := eval vm_compute in (run_K A_LIM Bx SH ss) in
lazymatch paj_tables RUN with (?tpi, ?tw) =>
let rr := eval vm_compute in (sym_run_toN_pi_tok tpi tw K Bx Bspan SH FUEL stop (add_cond ss cnd)) in
lazymatch rr with
| (?st', _) =>
let ssj := eval vm_compute in (sh_ss st') in
lazymatch ssj with
| mkSST ?pcj ?rgj _ ?mmj ?rvj _ =>
assert (name : forall (Ex2 : env) (msX : machine_state) (mdX : Model),
img_env VAL A_LIM Ex2 ->
st_ok_pi SEGS VAL Ex2 (mkSS pcj rgj mmj rvj fa) (restrict (w_H W) msX) ->
env_agree 44 (Ereg regs (ck_extra bs)) Ex2 ->
bv_unsigned (ew Ex2 2) = spZ regs ->
ajournal SEGS B CHECK_STK (spZ regs) [] ly S W mem md [] ly S W (ms_mem msX) mdX 0 ->
SRr SEGS W (mkCfg msX mdX) Q)
end end end end.
(* enter a continuation: drop the state of the arm that stated it, then take the continuation's own *)
Ltac ck_clear_state :=
repeat match goal with
| H : st_ok_pi _ _ _ _ _ |- _ => clear H
| H : st_ok _ _ _ _ |- _ => clear H
| H : sh_ok _ _ _ _ _ |- _ => clear H
| H : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => clear H
| H : bv_unsigned (ew _ 2) = spZ _ |- _ => clear H
| H : env_agree 44 _ _ |- _ => clear H
| H : img_env _ _ _ |- _ => clear H
end.
(* the bcmp call sites 0x81198 (row zi against ZERO) and 0x811ac (row zi against row zj) *)
Ltac ck_bcmp_zero_at HS zi ioff :=
lazymatch goal with
| HC : ck_ctx ?ly ?S ?W ?regs ?mem ?md ?ch ?r ?fabric ?bs ?G,
  HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  Usp : bv_unsigned (ew _ 2) = spZ _,
  HAG : env_agree 44 (Ereg _ (ck_extra _)) ?Ec, HEIq : img_env _ _ ?Ec |- _ =>
let Ra0 := fresh "Ra0" in let Ra1 := fresh "Ra1" in let Ra2 := fresh "Ra2" in
let Rra := fresh "Rra" in let Rsp := fresh "Rsp" in let Rgp := fresh "Rgp" in let Rtp := fresh "Rtp" in
let G10m := fresh "G10m" in let E3q := fresh "E3q" in let E4q := fresh "E4q" in
let HCq := fresh "HCq" in let HPREq := fresh "HPREq" in
let Hgpq := fresh "Hgpq" in let Htpq := fresh "Htpq" in let Qsp := fresh "Qsp" in
pose proof HC as HCq; destruct HCq as (HPREq & _);
pose proof HPREq as (_ & _ & _ & Hgpq & Htpq & _ & _ & _ & _);
ck_r_eq G10m; ck_reg_eq 3%nat (3%bv : bv 5) E3q; ck_reg_eq 4%nat (4%bv : bv 5) E4q;
pmkst HS;
prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (12%bv : bv 5) Ra2;
prreg HS (1%bv : bv 5) Rra; prreg HS (2%bv : bv 5) Rsp; prreg HS (3%bv : bv 5) Rgp; prreg HS (4%bv : bv 5) Rtp;
ck_ew_in G10m; ck_ew_in E3q; ck_ew_in E4q;
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdQ) _ =>
assert (Qsp : spZ rg = spZ regs + -160);
[ let Hu := fresh "Hu" in
  lazymatch type of Rsp with _ = Z_to_bv 64 (bv_unsigned (ew ?Ecu 2) + _) =>
  assert (Hu : bv_unsigned (ew Ecu 2) = spZ regs) by ck_usp_by Usp end;
  unfold spZ at 1; rewrite Rsp; rewrite unsigned_lit_small by (rewrite Hu; lia);
  rewrite Hu; reflexivity | ];
eapply SRr_bind;
[ eapply (ck_bcmp_zero ly S W regs mem md ch r fabric bs G rg mm mdQ zi HC HJ ltac:(lia));
  [ rewrite Ra0; exact (ck_denot_off _ 10 r ioff G10m)
  | rewrite Ra1; apply bv_eq;
    lazymatch goal with |- bv_unsigned (ew ?Ep 247) = _ =>
    let Hi := fresh "Hi" in assert (Hi : img_env VAL A_LIM Ep) by ck_img;
    rewrite (Hi 247%nat ltac:(cbv; lia)) end;
    unfold w64; rewrite unsigned_lit_small by apply pa_val_range; reflexivity
  | rewrite Ra2; reflexivity
  | exact Qsp
  | rewrite Rgp; rewrite E3q; exact Hgpq
  | rewrite Rtp; rewrite E4q; exact Htpq
  | rewrite Rra; apply ret_ok_codeptr_v; [lia | reflexivity] ]
| ] end end.
Ltac ck_bcmp_rows_at HS zi zj ioff joff :=
lazymatch goal with
| HC : ck_ctx ?ly ?S ?W ?regs ?mem ?md ?ch ?r ?fabric ?bs ?G,
  HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  Usp : bv_unsigned (ew _ 2) = spZ _,
  HAG : env_agree 44 (Ereg _ (ck_extra _)) ?Ec |- _ =>
let Ra0 := fresh "Ra0" in let Ra1 := fresh "Ra1" in let Ra2 := fresh "Ra2" in
let Rra := fresh "Rra" in let Rsp := fresh "Rsp" in let Rgp := fresh "Rgp" in let Rtp := fresh "Rtp" in
let G10m := fresh "G10m" in let E3q := fresh "E3q" in let E4q := fresh "E4q" in
let HCq := fresh "HCq" in let HPREq := fresh "HPREq" in
let Hgpq := fresh "Hgpq" in let Htpq := fresh "Htpq" in let Qsp := fresh "Qsp" in
pose proof HC as HCq; destruct HCq as (HPREq & _);
pose proof HPREq as (_ & _ & _ & Hgpq & Htpq & _ & _ & _ & _);
ck_r_eq G10m; ck_reg_eq 3%nat (3%bv : bv 5) E3q; ck_reg_eq 4%nat (4%bv : bv 5) E4q;
pmkst HS;
prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (12%bv : bv 5) Ra2;
prreg HS (1%bv : bv 5) Rra; prreg HS (2%bv : bv 5) Rsp; prreg HS (3%bv : bv 5) Rgp; prreg HS (4%bv : bv 5) Rtp;
ck_ew_in G10m; ck_ew_in E3q; ck_ew_in E4q;
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdQ) _ =>
assert (Qsp : spZ rg = spZ regs + -160);
[ let Hu := fresh "Hu" in
  lazymatch type of Rsp with _ = Z_to_bv 64 (bv_unsigned (ew ?Ecu 2) + _) =>
  assert (Hu : bv_unsigned (ew Ecu 2) = spZ regs) by ck_usp_by Usp end;
  unfold spZ at 1; rewrite Rsp; rewrite unsigned_lit_small by (rewrite Hu; lia);
  rewrite Hu; reflexivity | ];
eapply SRr_bind;
[ eapply (ck_bcmp_rows ly S W regs mem md ch r fabric bs G rg mm mdQ zi zj HC HJ ltac:(lia) ltac:(lia));
  [ rewrite Ra0; exact (ck_denot_off _ 10 r ioff G10m)
  | rewrite Ra1; exact (ck_denot_off _ 10 r joff G10m)
  | rewrite Ra2; reflexivity
  | exact Qsp
  | rewrite Rgp; rewrite E3q; exact Hgpq
  | rewrite Rtp; rewrite E4q; exact Htpq
  | rewrite Rra; apply ret_ok_codeptr_v; [lia | reflexivity] ]
| ] end end.
Ltac ck_bcmp_zero_block zi ioff :=
lazymatch goal with
| HSq : st_ok_pi _ _ _ _ _ |- _ => ck_bcmp_zero_at HSq zi ioff
| HSq : st_ok _ _ _ _ |- _ => ck_bcmp_zero_at HSq zi ioff
end.
Ltac ck_bcmp_rows_block zi zj ioff joff :=
lazymatch goal with
| HSq : st_ok_pi _ _ _ _ _ |- _ => ck_bcmp_rows_at HSq zi zj ioff joff
| HSq : st_ok _ _ _ _ |- _ => ck_bcmp_rows_at HSq zi zj ioff joff
end.
Ltac ck_use_join name fa :=
lazymatch goal with HS : st_ok_pi _ _ _ _ _ |- _ =>
ck_setfacts HS fa;
lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _, HJq : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
apply (name Ef _ _ ltac:(assumption) HSq ltac:(assumption) ltac:(assumption) HJq) end end.
(* row 4 is the last: n = 5, the inner loop is empty, and the function returns. *)
Lemma ck_oh_4 : ck_oh_prop 4.
Proof.
ck_head_intro.
change (Z.of_nat 4 + 1) with 5 in HNB.
assert (Hn5 : Boxreg.bx_n bs = 5) by lia.
destruct (Boxreg.B3_bounds bs 4 HB2 HB3 ltac:(lia)) as (Hbz & Hcz & Hsz).
ck_row_aborts 42%nat 43%nat 4.
ck_rn.
ck_memchr_block 248.
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (kk & Hfb & Ha02) & Hfr2 & Hpres2).
jafter_call_keep_hi HS 600%nat regs2 (mrestrict (w_H W) mem2) HP2 [0%nat; 1%nat; 2%nat; 3%nat] HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ ck_keep_regions Hfr2. }
assert (Hkk : 0 <= kk < 32).
{ eapply (ck_kk_lt W _ r bs 4 kk HBYm HL ltac:(lia) ltac:(apply HB6; lia)).
  replace (r + (56 * 4 + 24)) with (r + 248) by lia. exact Hfb. }
rewrite (proj2 (Z.ltb_lt kk 32) ltac:(lia)) in Ha02.
rewrite <- restrict_mkst_fx in HS2.
clear HS HJ SHOK. rename HS2 into HS. rename HJ2 into HJ.
ck_refresh. ck_hei.
ck_shok.
ck_a0 604%nat (r + 248 + kk) Ha02 Ha0v.
rewrite Rra.
ck_rn.
ck_lift Ha0v Ha0w.
ck_brt.
{ exfalso. rewrite (ck_br_eq0 _ 604 (r + 248 + kk) Ha0w ltac:(lia)) in Hc.
  apply Z.eqb_eq in Hc. lia. }
ck_drop_br.
ck_rn.
ck_brt.
2:{ exfalso. ck_n_eq Gn. lazymatch type of Gn with ew ?Ec _ = _ =>
    rewrite (ck_br_eq_lit Ec 33 5 (Boxreg.bx_n bs) Gn ltac:(lia) ltac:(lia)) in Hc end.
    apply Z.eqb_neq in Hc. lia. }
ck_drop_br.
ck_rn.
ck_ret.
Qed.
Lemma ck_ih_34 : ck_ih_prop 3 4.
Proof.
ck_head_intro.
change (Z.of_nat 4 + 1) with 5 in HNB.
assert (Hn5 : Boxreg.bx_n bs = 5) by lia.
destruct (Boxreg.B3_bounds bs 3 HB2 HB3 ltac:(lia)) as (Hb3 & Hc3 & Hs3).
destruct (Boxreg.B3_bounds bs 4 HB2 HB3 ltac:(lia)) as (Hb4 & Hc4 & Hs4).
ck_rn.
(* the pair (3, 4): the overlap test's two arms meet at the bcmp of 0x81198 *)
ck_join (mkAC BC_GE (SOff 42 0) (SAlu ALU_ADD (SOff 40 0) (SOff 41 0))) 4684 (ck_ih_facts 4) CONT.
{ ck_clear_state. intros Ex2 msX2 mdX2 HEI HS HAG Usp HJ. ck_shok.
  (* the pair's four paths meet again at the inner latch 0x811b4 *)
  assert (CONT2 : forall (Ex3 : env) (msX3 : machine_state) (mdX3 : Model),
  img_env VAL A_LIM Ex3 ->
  st_ok_pi SEGS VAL Ex3 (ss_lat 3 4) (restrict (w_H W) msX3) ->
  env_agree 44 (Ereg regs (ck_extra bs)) Ex3 ->
  bv_unsigned (ew Ex3 2) = spZ regs ->
  ajournal SEGS B CHECK_STK (spZ regs) [] ly S W mem md [] ly S W (ms_mem msX3) mdX3 0 ->
  SRr SEGS W (mkCfg msX3 mdX3) (tcheck_post regs ly S W mem md r bs)).
  { ck_clear_state. intros Ex3 msX3 mdX3 HEI HS HAG Usp HJ. ck_shok.
    (* n - 4 = 1 at the head, so the inner count is 0 and the latch leaves the inner loop *)
    ck_rn. ck_n_eq Gn.
    ck_brt.
    2:{ exfalso. lazymatch goal with Hb : branch_taken _ _ _ = false |- _ =>
        lazymatch type of Gn with ew ?Ec _ = _ =>
        rewrite (ck_br_eq0_off Ec 33 (-5) (Boxreg.bx_n bs) Gn ltac:(lia) ltac:(lia)) in Hb end;
        apply Z.eqb_neq in Hb; lia end. }
    clear Gn; ck_drop_br.
    (* the outer latch: i + 1 = 4 and n = 5, so the engine takes the back edge to row 4's head *)
    ck_rnto 4468.
    ck_seat HS (ck_oh_facts 4) CK_OH_CLOB (ss_oh 4).
    lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _, HJq : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    apply (ck_oh_4 ly S W regs mem md ch r fabric bs G HCTX ltac:(lia) Ef _ _ ltac:(assumption) HSq
    ltac:(assumption) HJq) end. }
  ck_rn.
  ck_bcmp_zero_block 3 168.
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hcmp & Hfr2).
  jafter_call_keep_hi HS 600%nat regs2 (mrestrict (w_H W) mem2) HP2 [0%nat; 1%nat; 2%nat; 3%nat] HS2.
  match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
  { ck_keep_regions Hfr2. }
  rewrite <- restrict_mkst_fx in HS2.
  clear HS HJ SHOK. rename HS2 into HS. rename HJ2 into HJ.
  ck_refresh. ck_hei. ck_shok.
  remember (bv_unsigned (getr regs2 10)) as vz eqn:Hvz.
  assert (Hv0 : getr regs2 10 = Z_to_bv 64 vz)
  by (rewrite Hvz; rewrite Z_to_bv_bv_unsigned; reflexivity).
  assert (Hvzr : 0 <= vz < 2 ^ 64)
  by (rewrite Hvz; pose proof (bv_unsigned_in_range 64 (getr regs2 10)) as Rq;
  unfold bv_modulus in Rq; change (2 ^ Z.of_N 64) with (2 ^ 64) in Rq; lia).
  ck_a0 604%nat vz Hv0 Ha0v.
  ck_ra.
  ck_rn.
  ck_lift Ha0v Ha0w.
  ck_brt.
  { (* row 3's MAC is zero6: the pair is settled, the walk goes to the latch *)
    ck_drop_br. clear Hcmp.
    ck_rnto 4712.
    ck_seat HS (ck_ih_facts 4) CLOB (ss_lat 3 4).
    lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _, HJq : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    apply (CONT2 Ef _ _ ltac:(assumption) HSq ltac:(assumption) ltac:(assumption) HJq) end. }
  (* row 3's MAC is not zero6, so B5 makes it differ from row 4's *)
  assert (Hnz : Boxreg.bx_mac bs 3 <> Boxreg.zero6).
  { intros Hq. lazymatch goal with Hb : branch_taken _ _ _ = false |- _ =>
    rewrite (ck_br_eq0 _ 604 vz Ha0w ltac:(lia)) in Hb;
    apply Z.eqb_neq in Hb; apply Hb; apply Hcmp; exact Hq end. }
  ck_drop_br. clear Hcmp Ha0v Ha0w Hv0 Hvzr Hvz.
  ck_rn.
  ck_bcmp_rows_block 3 4 168 224.
  cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hcmp3 & Hfr3).
  jafter_call_keep_hi HS 640%nat regs3 (mrestrict (w_H W) mem3) HP3 [0%nat; 1%nat; 2%nat; 3%nat] HS3.
  match type of HS3 with ?tq -> _ => assert (HRK : tq); [|specialize (HS3 HRK); clear HRK] end.
  { ck_keep_regions Hfr3. }
  rewrite <- restrict_mkst_fx in HS3.
  clear HS HJ SHOK. rename HS3 into HS. rename HJ3 into HJ.
  ck_refresh. ck_hei. ck_shok.
  remember (bv_unsigned (getr regs3 10)) as vw eqn:Hvw.
  assert (Hw0 : getr regs3 10 = Z_to_bv 64 vw)
  by (rewrite Hvw; rewrite Z_to_bv_bv_unsigned; reflexivity).
  assert (Hvwr : 0 <= vw < 2 ^ 64)
  by (rewrite Hvw; pose proof (bv_unsigned_in_range 64 (getr regs3 10)) as Rq;
  unfold bv_modulus in Rq; change (2 ^ Z.of_N 64) with (2 ^ 64) in Rq; lia).
  ck_a0 644%nat vw Hw0 Ha0u.
  ck_ra.
  ck_rn.
  ck_lift Ha0u Ha0t.
  ck_brt.
  { (* equal MACs: B5 refutes the abort at 0x811b0 *)
    exfalso. lazymatch goal with Hb : branch_taken _ _ _ = true |- _ =>
    rewrite (ck_br_eq0 _ 644 vw Ha0t ltac:(lia)) in Hb;
    apply Z.eqb_eq in Hb;
    destruct (HB5 3 4 ltac:(lia) ltac:(lia) ltac:(lia)) as [Hq | Hq];
    [exact (Hnz Hq) | exact (Hq (proj1 Hcmp3 Hb))] end. }
  ck_drop_br. clear Hcmp3.
  ck_rnto 4712.
  ck_seat HS (ck_ih_facts 4) CLOB (ss_lat 3 4).
  lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _, HJq : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  apply (CONT2 Ef _ _ ltac:(assumption) HSq ltac:(assumption) ltac:(assumption) HJq) end. }
(* the two arms of the overlap test of 0x8117c *)
ck_brt.
{ (* base_4 >= base_3 + nch_3: the slices are apart, the walk goes straight to the MAC test *)
  ck_rnto 4684. ck_use_join CONT (ck_ih_facts 4). }
(* base_4 < base_3 + nch_3: the second test of the pair, refuted by B4 *)
assert (Hlt1 : Boxreg.bx_base bs 4 < Boxreg.bx_base bs 3 + Boxreg.bx_nch bs 3).
{ lazymatch goal with Hb : branch_taken _ _ _ = false |- _ =>
  ck_base_eq 40%nat 3 GA; ck_nch_eq 41%nat 3 GB; ck_base_eq 42%nat 4 GC;
  lazymatch type of GA with ew ?Ec _ = _ =>
  rewrite (ck_br_ge_sum Ec 42 40 41 (Boxreg.bx_base bs 4) (Boxreg.bx_base bs 3) (Boxreg.bx_nch bs 3)
  GC GA GB ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in Hb end;
  apply negb_false_iff in Hb; apply Z.ltb_lt in Hb; exact Hb end. }
ck_drop_br.
ck_rn.
assert (Hlt2 : Boxreg.bx_base bs 3 < Boxreg.bx_base bs 4 + Boxreg.bx_nch bs 4 -> False).
{ intros Hq. destruct (HB4 3 4 ltac:(lia) ltac:(lia) ltac:(lia)).
  split; [exact Hq | exact Hlt1]. }
ck_brt.
{ exfalso. lazymatch goal with Hb : branch_taken _ _ _ = true |- _ =>
  ck_base_eq 40%nat 3 GA; ck_base_eq 42%nat 4 GC; ck_nch_eq 43%nat 4 GD;
  lazymatch type of GA with ew ?Ec _ = _ =>
  rewrite (ck_br_lt_sum Ec 40 42 43 (Boxreg.bx_base bs 3) (Boxreg.bx_base bs 4) (Boxreg.bx_nch bs 4)
  GA GC GD ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in Hb end;
  apply Z.ltb_lt in Hb; exact (Hlt2 Hb) end. }
ck_drop_br.
ck_rnto 4684.
ck_use_join CONT (ck_ih_facts 4).
Qed.



(* check from its entry to the head of row 0: the prologue, the row count and fabric tests, n = 0's return. *)
Lemma ck_from_oh0 : ck_oh_prop 0 -> tcheck_spec.
Proof.
intros HOH0. unfold tcheck_spec.
intros ly S W regs mem md ch r fabric bs G HPRE HROD H10 H11 Hin HBY HB16 HFA HIMG HGL HZ HZIN HZLO HZHI HMCH.
assert (HCTX : ck_ctx ly S W regs mem md ch r fabric bs G)
by exact (conj HPRE (conj HROD (conj H10 (conj H11 (conj Hin (conj HBY (conj HB16 (conj HFA
(conj HIMG (conj HGL (conj HZ (conj HZIN (conj HZLO (conj HZHI HMCH)))))))))))))).
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
destruct (ck_entry ly S W regs mem md ch r fabric bs HPRE H10 H11 Hin HBY HB16 HFA) as [HS SHOK].
pose proof (ajournal_init SEGS B CHECK_STK [] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (al_blocks _ _ LAWS ly S W mem md r REG_SIZE HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & _).
change (req_size REG_SIZE) with 288 in Hrceil, Hria.
remember (CE regs bs) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold CE; apply Eimg_env).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs (ck_extra bs)) k)
by (intros k Hk; subst E; unfold CE; apply Eimg_low; exact Hk).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 r)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 fabric)
by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 (SB))
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (Boxreg.bx_n bs))
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (ck_u32 bs 8))
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (ck_u32 bs 12))
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (ck_u32 bs 64))
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 (ck_u32 bs 68))
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 (ck_u32 bs 120))
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 6)).
assert (E39 : ew E 39 = Z_to_bv 64 (ck_u32 bs 124))
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 7)).
assert (E40 : ew E 40 = Z_to_bv 64 (ck_u32 bs 176))
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 8)).
assert (E41 : ew E 41 = Z_to_bv 64 (ck_u32 bs 180))
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 9)).
assert (E42 : ew E 42 = Z_to_bv 64 (ck_u32 bs 232))
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 10)).
assert (E43 : ew E 43 = Z_to_bv 64 (ck_u32 bs 236))
by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 11)).
assert (HAE : env_agree 32 (Ereg regs (ck_extra bs)) E)
by (split; [intros k Hk; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (HAG : env_agree 44 (Ereg regs (ck_extra bs)) E)
by (split; [intros k Hk; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
clear HE EL.
unfold cfg_at, A_checkP. change (w64 (BASE + AF_check)) with (Z_to_bv 64 (BASE + AF_check)).
paj_run_tok RUN HS HJ SHOK Bspan; [awr_ok_tac; exact Usp |].
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
psrr_branch_tok RUN BR HS SHOK Bspan.
(* n = 0: the epilogue and the return *)
{ ck_run HS HJ SHOK Usp.
lazymatch type of HS with st_ok_pi _ _ ?Ef _ (restrict _ ?msc) =>
assert (F1 : ew Ef 1 = getr regs 1) by (rewrite ?ew_ewset_other by lia; exact E1);
assert (HAEf : env_agree 32 (Ereg regs (ck_extra bs)) Ef)
by (eapply env_agree_trans; [exact HAE | split;
[intros kk Hkk; rewrite ?ew_ewset_other by lia; reflexivity | cbn [ed ewset]; reflexivity]]);
prreg HS (1%bv : bv 5) R1;
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
intros mat';
unfold tcheck_post, apost_base;
exists ly, S, (ms_regs msc), (ms_mem msc); eexists;
split; [cbn [ms_regs]; rewrite R1; first [rewrite F1 | rewrite E1]; rewrite Hra; reflexivity|];
split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|];
split; [eapply (aregs_preserved_of_st_ok SEGS _ Ef _ _ regs (ck_extra bs) HS);
[exact HAEf | vm_compute; reflexivity]|];
split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [apply Permutation_refl|];
intros kk Hkk;
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HJblk & _);
rewrite (HJblk r REG_SIZE kk Hin Hin ltac:(change (req_size REG_SIZE) with 288; unfold REG_SIZE in Hkk; lia)
ltac:(apply inFP_nil));
exact (HBY kk Hkk) end. }
(* n >= 1: the outer loop, row 0 first *)
pose proof HB16 as (HL & HB1 & HB2 & HB3 & HB4 & HB5 & HB6).
assert (HN : 0 <= Boxreg.bx_n bs <= 5) by exact HB1.
assert (HF : 1 <= fabric <= 40) by (rewrite <- HFA; exact HB2).
ck_lift E33 G33.
assert (Hn1 : 1 <= Boxreg.bx_n bs <= 5).
{ rewrite branch_eq_U in Hc. rewrite (U_atom _ 33 (Boxreg.bx_n bs) G33 ltac:(lia)) in Hc.
  rewrite U_SLit in Hc.
  apply Z.eqb_neq in Hc; unfold zcanon, M64 in Hc; exact (ck_npos _ HN Hc). }
ck_lift E34 G34. ck_lift E35 G35.
destruct (Boxreg.B3_bounds bs 0 HB2 HB3 ltac:(lia)) as (Hb0 & Hc0 & Hs0).
rewrite (ck_u32_base bs 0 8 HL ltac:(lia) ltac:(lia) ltac:(lia)) in G34.
rewrite (ck_u32_nch bs 0 12 HL ltac:(lia) ltac:(lia) ltac:(lia)) in G35.
ck_fact HS 34%nat (mkAF 0 38 0)
ltac:(rewrite G34, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
ck_fact HS 35%nat (mkAF 2 40 0)
ltac:(rewrite G35, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
clear Hc.
(* the outer loop's head 0x810c0 for row 0, seated as ss_oh 0 and closed by the hypothesis *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan 4468;
[awr_ok_tac; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb]; rewrite ?ew_ewset_other by lia; exact Usp |].
repeat match goal with Hf : frame_of _ _ _ _ |- _ => clear Hf | Hg : mem_grows _ _ |- _ => clear Hg end.
ck_norm HS.
ck_lift G33 G33p.
ck_fact HS 33%nat (mkAF 1 5 0)
ltac:(rewrite G33p, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
ck_seat HS (ck_oh_facts 0) CK_OH_CLOB (ss_oh 0).
lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _, HEIq : img_env _ _ ?Ef, HAGq : env_agree 44 _ ?Ef |- _ =>
apply (HOH0 ly S W regs mem md ch r fabric bs G HCTX ltac:(lia) Ef _ _ HEIq HSq HAGq HJ) end.
Qed.
(* row 0 with a next row possible: the walk of ck_oh_4 up to memchr's return, then the outer-loop test 0x81148
   (bgeu s4, a0: i + 1 >=u n) has both arms: n = 1 leaves through 0x81214 to the return; n >= 2 reaches the inner
   loop's head 0x81160 for the pair (0, 1), seated as ss_ih 0 1 and closed by the hypothesis. *)
Lemma ck_oh_0 : ck_ih_prop 0 1 -> ck_oh_prop 0.
Proof.
intros Hih.
ck_head_intro.
change (Z.of_nat 0 + 1) with 1 in HNB.
destruct (Boxreg.B3_bounds bs 0 HB2 HB3 ltac:(lia)) as (Hbz & Hcz & Hsz).
ck_row_aborts 34%nat 35%nat 0.
ck_rn.
ck_memchr_block 24.
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (kk & Hfb & Ha02) & Hfr2 & Hpres2).
jafter_call_keep_hi HS 600%nat regs2 (mrestrict (w_H W) mem2) HP2 [0%nat; 1%nat; 2%nat; 3%nat] HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ ck_keep_regions Hfr2. }
assert (Hkk : 0 <= kk < 32).
{ eapply (ck_kk_lt W _ r bs 0 kk HBYm HL ltac:(lia) ltac:(apply HB6; lia)).
  replace (r + (56 * 0 + 24)) with (r + 24) by lia. exact Hfb. }
rewrite (proj2 (Z.ltb_lt kk 32) ltac:(lia)) in Ha02.
rewrite <- restrict_mkst_fx in HS2.
clear HS HJ SHOK. rename HS2 into HS. rename HJ2 into HJ.
ck_refresh. ck_hei.
ck_shok.
ck_a0 604%nat (r + 24 + kk) Ha02 Ha0v.
rewrite Rra.
ck_rn.
ck_lift Ha0v Ha0w.
ck_brt.
{ exfalso. rewrite (ck_br_eq0 _ 604 (r + 24 + kk) Ha0w ltac:(lia)) in Hc.
  apply Z.eqb_eq in Hc. lia. }
ck_drop_br.
ck_rn.
ck_brt.
- (* taken: 1 >=u n, so n = 1; the function returns *)
  lazymatch type of Hc with branch_taken _ _ (sv_denot ?Ec _) = _ =>
    let Gq := fresh "Gq" in
    assert (Gq : ew Ec 33 = Z_to_bv 64 (Boxreg.bx_n bs))
      by (rewrite ?ew_havoc_old by lia; rewrite ?ew_ewset_other by lia;
          first [exact E33 | rewrite HA44 by lia; exact (ew_Ereg_extra regs (ck_extra bs) 1)]);
    rewrite (ck_br_geu_lit Ec 33 1 (Boxreg.bx_n bs) Gq ltac:(lia) ltac:(lia)) in Hc end.
  apply negb_true_iff in Hc. apply Z.ltb_ge in Hc.
  assert (HnI : Boxreg.bx_n bs = 1) by lia. clear Hc.
  ck_drop_br.
  ck_rn.
  ck_brt.
  2:{ exfalso. lazymatch type of Hc with branch_taken _ _ (sv_denot ?Ec _) = _ =>
    let Gq := fresh "Gq" in
    assert (Gq : ew Ec 33 = Z_to_bv 64 (Boxreg.bx_n bs))
      by (rewrite ?ew_havoc_old by lia; rewrite ?ew_ewset_other by lia;
          first [exact E33 | rewrite HA44 by lia; exact (ew_Ereg_extra regs (ck_extra bs) 1)]);
    rewrite (ck_br_eq_lit Ec 33 1 (Boxreg.bx_n bs) Gq ltac:(lia) ltac:(lia)) in Hc end.
      apply Z.eqb_neq in Hc. lia. }
  ck_drop_br.
  ck_rn.
  ck_ret.
- (* not taken: n >= 2; the inner loop's head for the pair (0, 1) *)
  lazymatch type of Hc with branch_taken _ _ (sv_denot ?Ec _) = _ =>
    let Gq := fresh "Gq" in
    assert (Gq : ew Ec 33 = Z_to_bv 64 (Boxreg.bx_n bs))
      by (rewrite ?ew_havoc_old by lia; rewrite ?ew_ewset_other by lia;
          first [exact E33 | rewrite HA44 by lia; exact (ew_Ereg_extra regs (ck_extra bs) 1)]);
    rewrite (ck_br_geu_lit Ec 33 1 (Boxreg.bx_n bs) Gq ltac:(lia) ltac:(lia)) in Hc end.
  apply negb_false_iff in Hc. apply Z.ltb_lt in Hc.
  assert (HNB2 : Z.of_nat 1 + 1 <= Boxreg.bx_n bs) by lia. clear Hc.
  destruct (Boxreg.B3_bounds bs 1 HB2 HB3 ltac:(lia)) as (Hbn & Hcn & Hsn).
  ck_drop_br.
  ck_rnto 4628.
  ck_base_eq 36%nat 1 Gb. ck_nch_eq 37%nat 1 Gc. ck_n_eq G33.
  ck_fact HS 36%nat (mkAF 0 38 0)
    ltac:(rewrite Gb, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
  ck_fact HS 37%nat (mkAF 2 40 0)
    ltac:(rewrite Gc, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
  ck_fact HS 33%nat (mkAF 2 5 0)
    ltac:(rewrite G33, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
  ck_seat HS (ck_ih_facts 1) CLOB (ss_ih 0 1).
  ck_refresh.
  lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _ |- _ =>
    assert (HEIf : img_env VAL A_LIM Ef)
      by (repeat first [ assumption | apply img_env_havoc_hi; [|cbv; lia] | apply img_env_ewset_hi; [|cbv; lia] ]) end.
  lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _ |- _ =>
    apply (Hih ly S W regs mem md ch r fabric bs G HCTX ltac:(lia) Ef _ _ ltac:(assumption) HSq ltac:(assumption) HJ) end.
Qed.
(* row 1 with a next row possible: the walk of ck_oh_4 up to memchr's return, then the outer-loop test 0x81148
   (bgeu s4, a0: i + 1 >=u n) has both arms: n = 2 leaves through 0x81214 to the return; n >= 3 reaches the inner
   loop's head 0x81160 for the pair (1, 2), seated as ss_ih 1 2 and closed by the hypothesis. *)
Lemma ck_oh_1 : ck_ih_prop 1 2 -> ck_oh_prop 1.
Proof.
intros Hih.
ck_head_intro.
change (Z.of_nat 1 + 1) with 2 in HNB.
destruct (Boxreg.B3_bounds bs 1 HB2 HB3 ltac:(lia)) as (Hbz & Hcz & Hsz).
ck_row_aborts 36%nat 37%nat 1.
ck_rn.
ck_memchr_block 80.
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (kk & Hfb & Ha02) & Hfr2 & Hpres2).
jafter_call_keep_hi HS 600%nat regs2 (mrestrict (w_H W) mem2) HP2 [0%nat; 1%nat; 2%nat; 3%nat] HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ ck_keep_regions Hfr2. }
assert (Hkk : 0 <= kk < 32).
{ eapply (ck_kk_lt W _ r bs 1 kk HBYm HL ltac:(lia) ltac:(apply HB6; lia)).
  replace (r + (56 * 1 + 24)) with (r + 80) by lia. exact Hfb. }
rewrite (proj2 (Z.ltb_lt kk 32) ltac:(lia)) in Ha02.
rewrite <- restrict_mkst_fx in HS2.
clear HS HJ SHOK. rename HS2 into HS. rename HJ2 into HJ.
ck_refresh. ck_hei.
ck_shok.
ck_a0 604%nat (r + 80 + kk) Ha02 Ha0v.
rewrite Rra.
ck_rn.
ck_lift Ha0v Ha0w.
ck_brt.
{ exfalso. rewrite (ck_br_eq0 _ 604 (r + 80 + kk) Ha0w ltac:(lia)) in Hc.
  apply Z.eqb_eq in Hc. lia. }
ck_drop_br.
ck_rn.
ck_brt.
- (* taken: 2 >=u n, so n = 2; the function returns *)
  lazymatch type of Hc with branch_taken _ _ (sv_denot ?Ec _) = _ =>
    let Gq := fresh "Gq" in
    assert (Gq : ew Ec 33 = Z_to_bv 64 (Boxreg.bx_n bs))
      by (rewrite ?ew_havoc_old by lia; rewrite ?ew_ewset_other by lia;
          first [exact E33 | rewrite HA44 by lia; exact (ew_Ereg_extra regs (ck_extra bs) 1)]);
    rewrite (ck_br_geu_lit Ec 33 2 (Boxreg.bx_n bs) Gq ltac:(lia) ltac:(lia)) in Hc end.
  apply negb_true_iff in Hc. apply Z.ltb_ge in Hc.
  assert (HnI : Boxreg.bx_n bs = 2) by lia. clear Hc.
  ck_drop_br.
  ck_rn.
  ck_brt.
  2:{ exfalso. lazymatch type of Hc with branch_taken _ _ (sv_denot ?Ec _) = _ =>
    let Gq := fresh "Gq" in
    assert (Gq : ew Ec 33 = Z_to_bv 64 (Boxreg.bx_n bs))
      by (rewrite ?ew_havoc_old by lia; rewrite ?ew_ewset_other by lia;
          first [exact E33 | rewrite HA44 by lia; exact (ew_Ereg_extra regs (ck_extra bs) 1)]);
    rewrite (ck_br_eq_lit Ec 33 2 (Boxreg.bx_n bs) Gq ltac:(lia) ltac:(lia)) in Hc end.
      apply Z.eqb_neq in Hc. lia. }
  ck_drop_br.
  ck_rn.
  ck_ret.
- (* not taken: n >= 3; the inner loop's head for the pair (1, 2) *)
  lazymatch type of Hc with branch_taken _ _ (sv_denot ?Ec _) = _ =>
    let Gq := fresh "Gq" in
    assert (Gq : ew Ec 33 = Z_to_bv 64 (Boxreg.bx_n bs))
      by (rewrite ?ew_havoc_old by lia; rewrite ?ew_ewset_other by lia;
          first [exact E33 | rewrite HA44 by lia; exact (ew_Ereg_extra regs (ck_extra bs) 1)]);
    rewrite (ck_br_geu_lit Ec 33 2 (Boxreg.bx_n bs) Gq ltac:(lia) ltac:(lia)) in Hc end.
  apply negb_false_iff in Hc. apply Z.ltb_lt in Hc.
  assert (HNB2 : Z.of_nat 2 + 1 <= Boxreg.bx_n bs) by lia. clear Hc.
  destruct (Boxreg.B3_bounds bs 2 HB2 HB3 ltac:(lia)) as (Hbn & Hcn & Hsn).
  ck_drop_br.
  ck_rnto 4628.
  ck_base_eq 38%nat 2 Gb. ck_nch_eq 39%nat 2 Gc. ck_n_eq G33.
  ck_fact HS 38%nat (mkAF 0 38 0)
    ltac:(rewrite Gb, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
  ck_fact HS 39%nat (mkAF 2 40 0)
    ltac:(rewrite Gc, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
  ck_fact HS 33%nat (mkAF 3 5 0)
    ltac:(rewrite G33, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
  ck_seat HS (ck_ih_facts 2) CLOB (ss_ih 1 2).
  ck_refresh.
  lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _ |- _ =>
    assert (HEIf : img_env VAL A_LIM Ef)
      by (repeat first [ assumption | apply img_env_havoc_hi; [|cbv; lia] | apply img_env_ewset_hi; [|cbv; lia] ]) end.
  lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _ |- _ =>
    apply (Hih ly S W regs mem md ch r fabric bs G HCTX ltac:(lia) Ef _ _ ltac:(assumption) HSq ltac:(assumption) HJ) end.
Qed.
(* row 2 with a next row possible: the walk of ck_oh_4 up to memchr's return, then the outer-loop test 0x81148
   (bgeu s4, a0: i + 1 >=u n) has both arms: n = 3 leaves through 0x81214 to the return; n >= 4 reaches the inner
   loop's head 0x81160 for the pair (2, 3), seated as ss_ih 2 3 and closed by the hypothesis. *)
Lemma ck_oh_2 : ck_ih_prop 2 3 -> ck_oh_prop 2.
Proof.
intros Hih.
ck_head_intro.
change (Z.of_nat 2 + 1) with 3 in HNB.
destruct (Boxreg.B3_bounds bs 2 HB2 HB3 ltac:(lia)) as (Hbz & Hcz & Hsz).
ck_row_aborts 38%nat 39%nat 2.
ck_rn.
ck_memchr_block 136.
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (kk & Hfb & Ha02) & Hfr2 & Hpres2).
jafter_call_keep_hi HS 600%nat regs2 (mrestrict (w_H W) mem2) HP2 [0%nat; 1%nat; 2%nat; 3%nat] HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ ck_keep_regions Hfr2. }
assert (Hkk : 0 <= kk < 32).
{ eapply (ck_kk_lt W _ r bs 2 kk HBYm HL ltac:(lia) ltac:(apply HB6; lia)).
  replace (r + (56 * 2 + 24)) with (r + 136) by lia. exact Hfb. }
rewrite (proj2 (Z.ltb_lt kk 32) ltac:(lia)) in Ha02.
rewrite <- restrict_mkst_fx in HS2.
clear HS HJ SHOK. rename HS2 into HS. rename HJ2 into HJ.
ck_refresh. ck_hei.
ck_shok.
ck_a0 604%nat (r + 136 + kk) Ha02 Ha0v.
rewrite Rra.
ck_rn.
ck_lift Ha0v Ha0w.
ck_brt.
{ exfalso. rewrite (ck_br_eq0 _ 604 (r + 136 + kk) Ha0w ltac:(lia)) in Hc.
  apply Z.eqb_eq in Hc. lia. }
ck_drop_br.
ck_rn.
ck_brt.
- (* taken: 3 >=u n, so n = 3; the function returns *)
  lazymatch type of Hc with branch_taken _ _ (sv_denot ?Ec _) = _ =>
    let Gq := fresh "Gq" in
    assert (Gq : ew Ec 33 = Z_to_bv 64 (Boxreg.bx_n bs))
      by (rewrite ?ew_havoc_old by lia; rewrite ?ew_ewset_other by lia;
          first [exact E33 | rewrite HA44 by lia; exact (ew_Ereg_extra regs (ck_extra bs) 1)]);
    rewrite (ck_br_geu_lit Ec 33 3 (Boxreg.bx_n bs) Gq ltac:(lia) ltac:(lia)) in Hc end.
  apply negb_true_iff in Hc. apply Z.ltb_ge in Hc.
  assert (HnI : Boxreg.bx_n bs = 3) by lia. clear Hc.
  ck_drop_br.
  ck_rn.
  ck_brt.
  2:{ exfalso. lazymatch type of Hc with branch_taken _ _ (sv_denot ?Ec _) = _ =>
    let Gq := fresh "Gq" in
    assert (Gq : ew Ec 33 = Z_to_bv 64 (Boxreg.bx_n bs))
      by (rewrite ?ew_havoc_old by lia; rewrite ?ew_ewset_other by lia;
          first [exact E33 | rewrite HA44 by lia; exact (ew_Ereg_extra regs (ck_extra bs) 1)]);
    rewrite (ck_br_eq_lit Ec 33 3 (Boxreg.bx_n bs) Gq ltac:(lia) ltac:(lia)) in Hc end.
      apply Z.eqb_neq in Hc. lia. }
  ck_drop_br.
  ck_rn.
  ck_ret.
- (* not taken: n >= 4; the inner loop's head for the pair (2, 3) *)
  lazymatch type of Hc with branch_taken _ _ (sv_denot ?Ec _) = _ =>
    let Gq := fresh "Gq" in
    assert (Gq : ew Ec 33 = Z_to_bv 64 (Boxreg.bx_n bs))
      by (rewrite ?ew_havoc_old by lia; rewrite ?ew_ewset_other by lia;
          first [exact E33 | rewrite HA44 by lia; exact (ew_Ereg_extra regs (ck_extra bs) 1)]);
    rewrite (ck_br_geu_lit Ec 33 3 (Boxreg.bx_n bs) Gq ltac:(lia) ltac:(lia)) in Hc end.
  apply negb_false_iff in Hc. apply Z.ltb_lt in Hc.
  assert (HNB2 : Z.of_nat 3 + 1 <= Boxreg.bx_n bs) by lia. clear Hc.
  destruct (Boxreg.B3_bounds bs 3 HB2 HB3 ltac:(lia)) as (Hbn & Hcn & Hsn).
  ck_drop_br.
  ck_rnto 4628.
  ck_base_eq 40%nat 3 Gb. ck_nch_eq 41%nat 3 Gc. ck_n_eq G33.
  ck_fact HS 40%nat (mkAF 0 38 0)
    ltac:(rewrite Gb, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
  ck_fact HS 41%nat (mkAF 2 40 0)
    ltac:(rewrite Gc, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
  ck_fact HS 33%nat (mkAF 4 5 0)
    ltac:(rewrite G33, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
  ck_seat HS (ck_ih_facts 3) CLOB (ss_ih 2 3).
  ck_refresh.
  lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _ |- _ =>
    assert (HEIf : img_env VAL A_LIM Ef)
      by (repeat first [ assumption | apply img_env_havoc_hi; [|cbv; lia] | apply img_env_ewset_hi; [|cbv; lia] ]) end.
  lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _ |- _ =>
    apply (Hih ly S W regs mem md ch r fabric bs G HCTX ltac:(lia) Ef _ _ ltac:(assumption) HSq ltac:(assumption) HJ) end.
Qed.
(* row 3 with a next row possible: the walk of ck_oh_4 up to memchr's return, then the outer-loop test 0x81148
   (bgeu s4, a0: i + 1 >=u n) has both arms: n = 4 leaves through 0x81214 to the return; n >= 5 reaches the inner
   loop's head 0x81160 for the pair (3, 4), seated as ss_ih 3 4 and closed by the hypothesis. *)
Lemma ck_oh_3 : ck_ih_prop 3 4 -> ck_oh_prop 3.
Proof.
intros Hih.
ck_head_intro.
change (Z.of_nat 3 + 1) with 4 in HNB.
destruct (Boxreg.B3_bounds bs 3 HB2 HB3 ltac:(lia)) as (Hbz & Hcz & Hsz).
ck_row_aborts 40%nat 41%nat 3.
ck_rn.
ck_memchr_block 192.
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (kk & Hfb & Ha02) & Hfr2 & Hpres2).
jafter_call_keep_hi HS 600%nat regs2 (mrestrict (w_H W) mem2) HP2 [0%nat; 1%nat; 2%nat; 3%nat] HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ ck_keep_regions Hfr2. }
assert (Hkk : 0 <= kk < 32).
{ eapply (ck_kk_lt W _ r bs 3 kk HBYm HL ltac:(lia) ltac:(apply HB6; lia)).
  replace (r + (56 * 3 + 24)) with (r + 192) by lia. exact Hfb. }
rewrite (proj2 (Z.ltb_lt kk 32) ltac:(lia)) in Ha02.
rewrite <- restrict_mkst_fx in HS2.
clear HS HJ SHOK. rename HS2 into HS. rename HJ2 into HJ.
ck_refresh. ck_hei.
ck_shok.
ck_a0 604%nat (r + 192 + kk) Ha02 Ha0v.
rewrite Rra.
ck_rn.
ck_lift Ha0v Ha0w.
ck_brt.
{ exfalso. rewrite (ck_br_eq0 _ 604 (r + 192 + kk) Ha0w ltac:(lia)) in Hc.
  apply Z.eqb_eq in Hc. lia. }
ck_drop_br.
ck_rn.
ck_brt.
- (* taken: 4 >=u n, so n = 4; the function returns *)
  lazymatch type of Hc with branch_taken _ _ (sv_denot ?Ec _) = _ =>
    let Gq := fresh "Gq" in
    assert (Gq : ew Ec 33 = Z_to_bv 64 (Boxreg.bx_n bs))
      by (rewrite ?ew_havoc_old by lia; rewrite ?ew_ewset_other by lia;
          first [exact E33 | rewrite HA44 by lia; exact (ew_Ereg_extra regs (ck_extra bs) 1)]);
    rewrite (ck_br_geu_lit Ec 33 4 (Boxreg.bx_n bs) Gq ltac:(lia) ltac:(lia)) in Hc end.
  apply negb_true_iff in Hc. apply Z.ltb_ge in Hc.
  assert (HnI : Boxreg.bx_n bs = 4) by lia. clear Hc.
  ck_drop_br.
  ck_rn.
  ck_brt.
  2:{ exfalso. lazymatch type of Hc with branch_taken _ _ (sv_denot ?Ec _) = _ =>
    let Gq := fresh "Gq" in
    assert (Gq : ew Ec 33 = Z_to_bv 64 (Boxreg.bx_n bs))
      by (rewrite ?ew_havoc_old by lia; rewrite ?ew_ewset_other by lia;
          first [exact E33 | rewrite HA44 by lia; exact (ew_Ereg_extra regs (ck_extra bs) 1)]);
    rewrite (ck_br_eq_lit Ec 33 4 (Boxreg.bx_n bs) Gq ltac:(lia) ltac:(lia)) in Hc end.
      apply Z.eqb_neq in Hc. lia. }
  ck_drop_br.
  ck_rn.
  ck_ret.
- (* not taken: n >= 5; the inner loop's head for the pair (3, 4) *)
  lazymatch type of Hc with branch_taken _ _ (sv_denot ?Ec _) = _ =>
    let Gq := fresh "Gq" in
    assert (Gq : ew Ec 33 = Z_to_bv 64 (Boxreg.bx_n bs))
      by (rewrite ?ew_havoc_old by lia; rewrite ?ew_ewset_other by lia;
          first [exact E33 | rewrite HA44 by lia; exact (ew_Ereg_extra regs (ck_extra bs) 1)]);
    rewrite (ck_br_geu_lit Ec 33 4 (Boxreg.bx_n bs) Gq ltac:(lia) ltac:(lia)) in Hc end.
  apply negb_false_iff in Hc. apply Z.ltb_lt in Hc.
  assert (HNB2 : Z.of_nat 4 + 1 <= Boxreg.bx_n bs) by lia. clear Hc.
  destruct (Boxreg.B3_bounds bs 4 HB2 HB3 ltac:(lia)) as (Hbn & Hcn & Hsn).
  ck_drop_br.
  ck_rnto 4628.
  ck_base_eq 42%nat 4 Gb. ck_nch_eq 43%nat 4 Gc. ck_n_eq G33.
  ck_fact HS 42%nat (mkAF 0 38 0)
    ltac:(rewrite Gb, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
  ck_fact HS 43%nat (mkAF 2 40 0)
    ltac:(rewrite Gc, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
  ck_fact HS 33%nat (mkAF 5 5 0)
    ltac:(rewrite G33, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
  ck_seat HS (ck_ih_facts 4) CLOB (ss_ih 3 4).
  ck_refresh.
  lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _ |- _ =>
    assert (HEIf : img_env VAL A_LIM Ef)
      by (repeat first [ assumption | apply img_env_havoc_hi; [|cbv; lia] | apply img_env_ewset_hi; [|cbv; lia] ]) end.
  lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _ |- _ =>
    apply (Hih ly S W regs mem md ch r fabric bs G HCTX ltac:(lia) Ef _ _ ltac:(assumption) HSq ltac:(assumption) HJ) end.
Qed.
Lemma ck_ih_2_4 : ck_ih_prop 2 4.
Proof.
ck_head_intro.
change (Z.of_nat 4 + 1) with 5 in HNB.
assert (Hn5 : Boxreg.bx_n bs = 5) by lia.
destruct (Boxreg.B3_bounds bs 2 HB2 HB3 ltac:(lia)) as (Hb2' & Hc2' & Hs2').
destruct (Boxreg.B3_bounds bs 4 HB2 HB3 ltac:(lia)) as (Hb4 & Hc4 & Hs4).
ck_rn.
(* the pair (2, 4): the overlap test's two arms meet at the bcmp of 0x81198 *)
ck_join (mkAC BC_GE (SOff 42 0) (SAlu ALU_ADD (SOff 38 0) (SOff 39 0))) 4684 (ck_ih_facts 4) CONT.
{ ck_clear_state. intros Ex2 msX2 mdX2 HEI HS HAG Usp HJ. ck_shok.
  (* the pair's four paths meet again at the inner latch 0x811b4 *)
  assert (CONT2 : forall (Ex3 : env) (msX3 : machine_state) (mdX3 : Model),
  img_env VAL A_LIM Ex3 ->
  st_ok_pi SEGS VAL Ex3 (ss_lat 2 4) (restrict (w_H W) msX3) ->
  env_agree 44 (Ereg regs (ck_extra bs)) Ex3 ->
  bv_unsigned (ew Ex3 2) = spZ regs ->
  ajournal SEGS B CHECK_STK (spZ regs) [] ly S W mem md [] ly S W (ms_mem msX3) mdX3 0 ->
  SRr SEGS W (mkCfg msX3 mdX3) (tcheck_post regs ly S W mem md r bs)).
  { ck_clear_state. intros Ex3 msX3 mdX3 HEI HS HAG Usp HJ. ck_shok.
    (* n - 4 = 1 at the head, so the inner count is 0 and the latch leaves the inner loop *)
    ck_rn. ck_n_eq Gn.
    ck_brt.
    2:{ exfalso. lazymatch goal with Hb : branch_taken _ _ _ = false |- _ =>
        lazymatch type of Gn with ew ?Ec _ = _ =>
        rewrite (ck_br_eq0_off Ec 33 (-5) (Boxreg.bx_n bs) Gn ltac:(lia) ltac:(lia)) in Hb end;
        apply Z.eqb_neq in Hb; lia end. }
    clear Gn; ck_drop_br.
    (* the outer latch: i + 1 = 3 and n = 5, so the engine takes the back edge to row 3's head *)
    ck_rnto 4468.
    ck_n_eq Gnx.
    ck_fact HS 33%nat (mkAF 4 5 0) ltac:(rewrite Gnx, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
    ck_seat HS (ck_oh_facts 3) CK_OH_CLOB (ss_oh 3).
    lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _, HJq : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    apply (ck_oh_3 ck_ih_34 ly S W regs mem md ch r fabric bs G HCTX ltac:(lia) Ef _ _ ltac:(assumption) HSq
    ltac:(assumption) HJq) end. }
  ck_rn.
  ck_bcmp_zero_block 2 112.
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hcmp & Hfr2).
  jafter_call_keep_hi HS 600%nat regs2 (mrestrict (w_H W) mem2) HP2 [0%nat; 1%nat; 2%nat; 3%nat] HS2.
  match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
  { ck_keep_regions Hfr2. }
  rewrite <- restrict_mkst_fx in HS2.
  clear HS HJ SHOK. rename HS2 into HS. rename HJ2 into HJ.
  ck_refresh. ck_hei. ck_shok.
  remember (bv_unsigned (getr regs2 10)) as vz eqn:Hvz.
  assert (Hv0 : getr regs2 10 = Z_to_bv 64 vz)
  by (rewrite Hvz; rewrite Z_to_bv_bv_unsigned; reflexivity).
  assert (Hvzr : 0 <= vz < 2 ^ 64)
  by (rewrite Hvz; pose proof (bv_unsigned_in_range 64 (getr regs2 10)) as Rq;
  unfold bv_modulus in Rq; change (2 ^ Z.of_N 64) with (2 ^ 64) in Rq; lia).
  ck_a0 604%nat vz Hv0 Ha0v.
  ck_ra.
  ck_rn.
  ck_lift Ha0v Ha0w.
  ck_brt.
  { (* row 2's MAC is zero6: the pair is settled, the walk goes to the latch *)
    ck_drop_br. clear Hcmp.
    ck_rnto 4712.
    ck_seat HS (ck_ih_facts 4) CLOB (ss_lat 2 4).
    lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _, HJq : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    apply (CONT2 Ef _ _ ltac:(assumption) HSq ltac:(assumption) ltac:(assumption) HJq) end. }
  (* row 2's MAC is not zero6, so B5 makes it differ from row 4's *)
  assert (Hnz : Boxreg.bx_mac bs 2 <> Boxreg.zero6).
  { intros Hq. lazymatch goal with Hb : branch_taken _ _ _ = false |- _ =>
    rewrite (ck_br_eq0 _ 604 vz Ha0w ltac:(lia)) in Hb;
    apply Z.eqb_neq in Hb; apply Hb; apply Hcmp; exact Hq end. }
  ck_drop_br. clear Hcmp Ha0v Ha0w Hv0 Hvzr Hvz.
  ck_rn.
  ck_bcmp_rows_block 2 4 112 224.
  cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hcmp3 & Hfr3).
  jafter_call_keep_hi HS 640%nat regs3 (mrestrict (w_H W) mem3) HP3 [0%nat; 1%nat; 2%nat; 3%nat] HS3.
  match type of HS3 with ?tq -> _ => assert (HRK : tq); [|specialize (HS3 HRK); clear HRK] end.
  { ck_keep_regions Hfr3. }
  rewrite <- restrict_mkst_fx in HS3.
  clear HS HJ SHOK. rename HS3 into HS. rename HJ3 into HJ.
  ck_refresh. ck_hei. ck_shok.
  remember (bv_unsigned (getr regs3 10)) as vw eqn:Hvw.
  assert (Hw0 : getr regs3 10 = Z_to_bv 64 vw)
  by (rewrite Hvw; rewrite Z_to_bv_bv_unsigned; reflexivity).
  assert (Hvwr : 0 <= vw < 2 ^ 64)
  by (rewrite Hvw; pose proof (bv_unsigned_in_range 64 (getr regs3 10)) as Rq;
  unfold bv_modulus in Rq; change (2 ^ Z.of_N 64) with (2 ^ 64) in Rq; lia).
  ck_a0 644%nat vw Hw0 Ha0u.
  ck_ra.
  ck_rn.
  ck_lift Ha0u Ha0t.
  ck_brt.
  { (* equal MACs: B5 refutes the abort at 0x811b0 *)
    exfalso. lazymatch goal with Hb : branch_taken _ _ _ = true |- _ =>
    rewrite (ck_br_eq0 _ 644 vw Ha0t ltac:(lia)) in Hb;
    apply Z.eqb_eq in Hb;
    destruct (HB5 2 4 ltac:(lia) ltac:(lia) ltac:(lia)) as [Hq | Hq];
    [exact (Hnz Hq) | exact (Hq (proj1 Hcmp3 Hb))] end. }
  ck_drop_br. clear Hcmp3.
  ck_rnto 4712.
  ck_seat HS (ck_ih_facts 4) CLOB (ss_lat 2 4).
  lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _, HJq : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  apply (CONT2 Ef _ _ ltac:(assumption) HSq ltac:(assumption) ltac:(assumption) HJq) end. }
(* the two arms of the overlap test of 0x8117c *)
ck_brt.
{ (* base_4 >= base_2 + nch_2: the slices are apart, the walk goes straight to the MAC test *)
  ck_rnto 4684. ck_use_join CONT (ck_ih_facts 4). }
(* base_4 < base_2 + nch_2: the second test of the pair, refuted by B4 *)
assert (Hlt1 : Boxreg.bx_base bs 4 < Boxreg.bx_base bs 2 + Boxreg.bx_nch bs 2).
{ lazymatch goal with Hb : branch_taken _ _ _ = false |- _ =>
  ck_base_eq 38%nat 2 GA; ck_nch_eq 39%nat 2 GB; ck_base_eq 42%nat 4 GC;
  lazymatch type of GA with ew ?Ec _ = _ =>
  rewrite (ck_br_ge_sum Ec 42 38 39 (Boxreg.bx_base bs 4) (Boxreg.bx_base bs 2) (Boxreg.bx_nch bs 2)
  GC GA GB ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in Hb end;
  apply negb_false_iff in Hb; apply Z.ltb_lt in Hb; exact Hb end. }
ck_drop_br.
ck_rn.
assert (Hlt2 : Boxreg.bx_base bs 2 < Boxreg.bx_base bs 4 + Boxreg.bx_nch bs 4 -> False).
{ intros Hq. destruct (HB4 2 4 ltac:(lia) ltac:(lia) ltac:(lia)).
  split; [exact Hq | exact Hlt1]. }
ck_brt.
{ exfalso. lazymatch goal with Hb : branch_taken _ _ _ = true |- _ =>
  ck_base_eq 38%nat 2 GA; ck_base_eq 42%nat 4 GC; ck_nch_eq 43%nat 4 GD;
  lazymatch type of GA with ew ?Ec _ = _ =>
  rewrite (ck_br_lt_sum Ec 38 42 43 (Boxreg.bx_base bs 2) (Boxreg.bx_base bs 4) (Boxreg.bx_nch bs 4)
  GA GC GD ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in Hb end;
  apply Z.ltb_lt in Hb; exact (Hlt2 Hb) end. }
ck_drop_br.
ck_rnto 4684.
ck_use_join CONT (ck_ih_facts 4).
Qed.
Lemma ck_ih_2_3 : ck_ih_prop 2 3.
Proof.
ck_head_intro.
change (Z.of_nat 3 + 1) with 4 in HNB.
destruct (Boxreg.B3_bounds bs 2 HB2 HB3 ltac:(lia)) as (Hb2' & Hc2' & Hs2').
destruct (Boxreg.B3_bounds bs 3 HB2 HB3 ltac:(lia)) as (Hb3 & Hc3 & Hs3).
ck_rn.
(* the pair (2, 3): the overlap test's two arms meet at the bcmp of 0x81198 *)
ck_join (mkAC BC_GE (SOff 40 0) (SAlu ALU_ADD (SOff 38 0) (SOff 39 0))) 4684 (ck_ih_facts 3) CONT.
{ ck_clear_state. intros Ex2 msX2 mdX2 HEI HS HAG Usp HJ. ck_shok.
  (* the pair's four paths meet again at the inner latch 0x811b4 *)
  assert (CONT2 : forall (Ex3 : env) (msX3 : machine_state) (mdX3 : Model),
  img_env VAL A_LIM Ex3 ->
  st_ok_pi SEGS VAL Ex3 (ss_lat 2 3) (restrict (w_H W) msX3) ->
  env_agree 44 (Ereg regs (ck_extra bs)) Ex3 ->
  bv_unsigned (ew Ex3 2) = spZ regs ->
  ajournal SEGS B CHECK_STK (spZ regs) [] ly S W mem md [] ly S W (ms_mem msX3) mdX3 0 ->
  SRr SEGS W (mkCfg msX3 mdX3) (tcheck_post regs ly S W mem md r bs)).
  { ck_clear_state. intros Ex3 msX3 mdX3 HEI HS HAG Usp HJ. ck_shok.
    (* the inner count's test of 0x811c4: n = 4 leaves the inner loop, n = 5 goes on to row 4 *)
    ck_rn. ck_n_eq Gn.
    ck_brt.
    { (* n = 4: the outer latch takes the walk to row 3's head *)
      clear Gn; ck_drop_br.
      ck_rnto 4468.
      ck_seat HS (ck_oh_facts 3) CK_OH_CLOB (ss_oh 3).
      lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _, HJq : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      apply (ck_oh_3 ck_ih_34 ly S W regs mem md ch r fabric bs G HCTX ltac:(lia) Ef _ _ ltac:(assumption) HSq
      ltac:(assumption) HJq) end. }
    (* n = 5: the inner loop goes on with the pair (2, 4) *)
    assert (Hn5 : Boxreg.bx_n bs = 5).
    { lazymatch goal with Hb : branch_taken _ _ _ = false |- _ =>
      lazymatch type of Gn with ew ?Ec _ = _ =>
      rewrite (ck_br_eq0_off Ec 33 (-4) (Boxreg.bx_n bs) Gn ltac:(lia) ltac:(lia)) in Hb end;
      apply Z.eqb_neq in Hb; lia end. }
    clear Gn; ck_drop_br.
    destruct (Boxreg.B3_bounds bs 4 HB2 HB3 ltac:(lia)) as (Hb4 & Hc4 & Hs4).
    ck_rnto 4628.
    ck_n_eq Gn5.
    ck_fact HS 33%nat (mkAF 5 5 0) ltac:(rewrite Gn5, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
    ck_base_eq 42%nat 4 Gb4.
    ck_fact HS 42%nat (mkAF 0 38 0) ltac:(rewrite Gb4, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
    ck_nch_eq 43%nat 4 Gc4.
    ck_fact HS 43%nat (mkAF 2 40 0) ltac:(rewrite Gc4, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
    ck_fix_s6.
    ck_seat HS (ck_ih_facts 4) CLOB (ss_ih 2 4).
    lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _, HJq : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    apply (ck_ih_2_4 ly S W regs mem md ch r fabric bs G HCTX ltac:(lia) Ef _ _ ltac:(assumption) HSq
    ltac:(assumption) HJq) end. }
  ck_rn.
  ck_bcmp_zero_block 2 112.
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hcmp & Hfr2).
  jafter_call_keep_hi HS 600%nat regs2 (mrestrict (w_H W) mem2) HP2 [0%nat; 1%nat; 2%nat; 3%nat] HS2.
  match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
  { ck_keep_regions Hfr2. }
  rewrite <- restrict_mkst_fx in HS2.
  clear HS HJ SHOK. rename HS2 into HS. rename HJ2 into HJ.
  ck_refresh. ck_hei. ck_shok.
  remember (bv_unsigned (getr regs2 10)) as vz eqn:Hvz.
  assert (Hv0 : getr regs2 10 = Z_to_bv 64 vz)
  by (rewrite Hvz; rewrite Z_to_bv_bv_unsigned; reflexivity).
  assert (Hvzr : 0 <= vz < 2 ^ 64)
  by (rewrite Hvz; pose proof (bv_unsigned_in_range 64 (getr regs2 10)) as Rq;
  unfold bv_modulus in Rq; change (2 ^ Z.of_N 64) with (2 ^ 64) in Rq; lia).
  ck_a0 604%nat vz Hv0 Ha0v.
  ck_ra.
  ck_rn.
  ck_lift Ha0v Ha0w.
  ck_brt.
  { (* row 2's MAC is zero6: the pair is settled, the walk goes to the latch *)
    ck_drop_br. clear Hcmp.
    ck_rnto 4712.
    ck_seat HS (ck_ih_facts 3) CLOB (ss_lat 2 3).
    lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _, HJq : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    apply (CONT2 Ef _ _ ltac:(assumption) HSq ltac:(assumption) ltac:(assumption) HJq) end. }
  (* row 2's MAC is not zero6, so B5 makes it differ from row 3's *)
  assert (Hnz : Boxreg.bx_mac bs 2 <> Boxreg.zero6).
  { intros Hq. lazymatch goal with Hb : branch_taken _ _ _ = false |- _ =>
    rewrite (ck_br_eq0 _ 604 vz Ha0w ltac:(lia)) in Hb;
    apply Z.eqb_neq in Hb; apply Hb; apply Hcmp; exact Hq end. }
  ck_drop_br. clear Hcmp Ha0v Ha0w Hv0 Hvzr Hvz.
  ck_rn.
  ck_bcmp_rows_block 2 3 112 168.
  cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hcmp3 & Hfr3).
  jafter_call_keep_hi HS 640%nat regs3 (mrestrict (w_H W) mem3) HP3 [0%nat; 1%nat; 2%nat; 3%nat] HS3.
  match type of HS3 with ?tq -> _ => assert (HRK : tq); [|specialize (HS3 HRK); clear HRK] end.
  { ck_keep_regions Hfr3. }
  rewrite <- restrict_mkst_fx in HS3.
  clear HS HJ SHOK. rename HS3 into HS. rename HJ3 into HJ.
  ck_refresh. ck_hei. ck_shok.
  remember (bv_unsigned (getr regs3 10)) as vw eqn:Hvw.
  assert (Hw0 : getr regs3 10 = Z_to_bv 64 vw)
  by (rewrite Hvw; rewrite Z_to_bv_bv_unsigned; reflexivity).
  assert (Hvwr : 0 <= vw < 2 ^ 64)
  by (rewrite Hvw; pose proof (bv_unsigned_in_range 64 (getr regs3 10)) as Rq;
  unfold bv_modulus in Rq; change (2 ^ Z.of_N 64) with (2 ^ 64) in Rq; lia).
  ck_a0 644%nat vw Hw0 Ha0u.
  ck_ra.
  ck_rn.
  ck_lift Ha0u Ha0t.
  ck_brt.
  { (* equal MACs: B5 refutes the abort at 0x811b0 *)
    exfalso. lazymatch goal with Hb : branch_taken _ _ _ = true |- _ =>
    rewrite (ck_br_eq0 _ 644 vw Ha0t ltac:(lia)) in Hb;
    apply Z.eqb_eq in Hb;
    destruct (HB5 2 3 ltac:(lia) ltac:(lia) ltac:(lia)) as [Hq | Hq];
    [exact (Hnz Hq) | exact (Hq (proj1 Hcmp3 Hb))] end. }
  ck_drop_br. clear Hcmp3.
  ck_rnto 4712.
  ck_seat HS (ck_ih_facts 3) CLOB (ss_lat 2 3).
  lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _, HJq : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  apply (CONT2 Ef _ _ ltac:(assumption) HSq ltac:(assumption) ltac:(assumption) HJq) end. }
(* the two arms of the overlap test of 0x8117c *)
ck_brt.
{ (* base_3 >= base_2 + nch_2: the slices are apart, the walk goes straight to the MAC test *)
  ck_rnto 4684. ck_use_join CONT (ck_ih_facts 3). }
(* base_3 < base_2 + nch_2: the second test of the pair, refuted by B4 *)
assert (Hlt1 : Boxreg.bx_base bs 3 < Boxreg.bx_base bs 2 + Boxreg.bx_nch bs 2).
{ lazymatch goal with Hb : branch_taken _ _ _ = false |- _ =>
  ck_base_eq 38%nat 2 GA; ck_nch_eq 39%nat 2 GB; ck_base_eq 40%nat 3 GC;
  lazymatch type of GA with ew ?Ec _ = _ =>
  rewrite (ck_br_ge_sum Ec 40 38 39 (Boxreg.bx_base bs 3) (Boxreg.bx_base bs 2) (Boxreg.bx_nch bs 2)
  GC GA GB ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in Hb end;
  apply negb_false_iff in Hb; apply Z.ltb_lt in Hb; exact Hb end. }
ck_drop_br.
ck_rn.
assert (Hlt2 : Boxreg.bx_base bs 2 < Boxreg.bx_base bs 3 + Boxreg.bx_nch bs 3 -> False).
{ intros Hq. destruct (HB4 2 3 ltac:(lia) ltac:(lia) ltac:(lia)).
  split; [exact Hq | exact Hlt1]. }
ck_brt.
{ exfalso. lazymatch goal with Hb : branch_taken _ _ _ = true |- _ =>
  ck_base_eq 38%nat 2 GA; ck_base_eq 40%nat 3 GC; ck_nch_eq 41%nat 3 GD;
  lazymatch type of GA with ew ?Ec _ = _ =>
  rewrite (ck_br_lt_sum Ec 38 40 41 (Boxreg.bx_base bs 2) (Boxreg.bx_base bs 3) (Boxreg.bx_nch bs 3)
  GA GC GD ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in Hb end;
  apply Z.ltb_lt in Hb; exact (Hlt2 Hb) end. }
ck_drop_br.
ck_rnto 4684.
ck_use_join CONT (ck_ih_facts 3).
Qed.
(* The pairs (1, j) of the inner loop, after ck_ih_34's walk: the overlap test of 0x8117c, the join at the bcmp of
   0x81198, the bcmp calls, B4 / B5, and the inner latch 0x811b4. At the latch's test 0x811c4 (beqz s7, s7 = n - (j + 1))
   the exit arm reaches row 2's outer head (closed by the hypothesis) and, for j < 4, the other arm reaches the pair
   (1, j + 1). *)
Lemma ck_ih_1_4 : ck_oh_prop 2 -> ck_ih_prop 1 4.
Proof.
intros Hoh.
ck_head_intro.
change (Z.of_nat 4 + 1) with 5 in HNB.
assert (Hn5 : Boxreg.bx_n bs = 5) by lia.
destruct (Boxreg.B3_bounds bs 1 HB2 HB3 ltac:(lia)) as (Hb1 & Hc1 & Hs1).
destruct (Boxreg.B3_bounds bs 4 HB2 HB3 ltac:(lia)) as (Hb4 & Hc4 & Hs4).
ck_rn.
(* the pair (1, 4): the overlap test's two arms meet at the bcmp of 0x81198 *)
ck_join (mkAC BC_GE (SOff 42 0) (SAlu ALU_ADD (SOff 36 0) (SOff 37 0))) 4684 (ck_ih_facts 4) CONT.
{ ck_clear_state. intros Ex2 msX2 mdX2 HEI HS HAG Usp HJ. ck_shok.
  (* the pair's four paths meet again at the inner latch 0x811b4 *)
  assert (CONT2 : forall (Ex3 : env) (msX3 : machine_state) (mdX3 : Model),
  img_env VAL A_LIM Ex3 ->
  st_ok_pi SEGS VAL Ex3 (ss_lat 1 4) (restrict (w_H W) msX3) ->
  env_agree 44 (Ereg regs (ck_extra bs)) Ex3 ->
  bv_unsigned (ew Ex3 2) = spZ regs ->
  ajournal SEGS B CHECK_STK (spZ regs) [] ly S W mem md [] ly S W (ms_mem msX3) mdX3 0 ->
  SRr SEGS W (mkCfg msX3 mdX3) (tcheck_post regs ly S W mem md r bs)).
  { ck_clear_state. intros Ex3 msX3 mdX3 HEI HS HAG Usp HJ. ck_shok.
    (* n - 4 = 1 at the head, so the inner count is 0 and the latch leaves the inner loop *)
    ck_rn. ck_n_eq Gn.
    ck_brt.
    2:{ exfalso. lazymatch goal with Hb : branch_taken _ _ _ = false |- _ =>
        lazymatch type of Gn with ew ?Ec _ = _ =>
        rewrite (ck_br_eq0_off Ec 33 (-5) (Boxreg.bx_n bs) Gn ltac:(lia) ltac:(lia)) in Hb end;
        apply Z.eqb_neq in Hb; lia end. }
    clear Gn; ck_drop_br.
    (* the outer latch: i + 1 = 2 and n >= 3, so the engine takes the back edge to row 2's head *)
    ck_rnto 4468.
    ck_n_eq Gnx.
    ck_fact HS 33%nat (mkAF 3 5 0)
      ltac:(rewrite Gnx, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
    ck_seat HS (ck_oh_facts 2) CK_OH_CLOB (ss_oh 2).
    lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _, HJq : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    apply (Hoh ly S W regs mem md ch r fabric bs G HCTX ltac:(lia) Ef _ _ ltac:(assumption) HSq
    ltac:(assumption) HJq) end. }
  ck_rn.
  ck_bcmp_zero_block 1 56.
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hcmp & Hfr2).
  jafter_call_keep_hi HS 600%nat regs2 (mrestrict (w_H W) mem2) HP2 [0%nat; 1%nat; 2%nat; 3%nat] HS2.
  match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
  { ck_keep_regions Hfr2. }
  rewrite <- restrict_mkst_fx in HS2.
  clear HS HJ SHOK. rename HS2 into HS. rename HJ2 into HJ.
  ck_refresh. ck_hei. ck_shok.
  remember (bv_unsigned (getr regs2 10)) as vz eqn:Hvz.
  assert (Hv0 : getr regs2 10 = Z_to_bv 64 vz)
  by (rewrite Hvz; rewrite Z_to_bv_bv_unsigned; reflexivity).
  assert (Hvzr : 0 <= vz < 2 ^ 64)
  by (rewrite Hvz; pose proof (bv_unsigned_in_range 64 (getr regs2 10)) as Rq;
  unfold bv_modulus in Rq; change (2 ^ Z.of_N 64) with (2 ^ 64) in Rq; lia).
  ck_a0 604%nat vz Hv0 Ha0v.
  ck_ra.
  ck_rn.
  ck_lift Ha0v Ha0w.
  ck_brt.
  { (* row 1's MAC is zero6: the pair is settled, the walk goes to the latch *)
    ck_drop_br. clear Hcmp.
    ck_rnto 4712.
    ck_seat HS (ck_ih_facts 4) CLOB (ss_lat 1 4).
    lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _, HJq : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    apply (CONT2 Ef _ _ ltac:(assumption) HSq ltac:(assumption) ltac:(assumption) HJq) end. }
  (* row 1's MAC is not zero6, so B5 makes it differ from row 4's *)
  assert (Hnz : Boxreg.bx_mac bs 1 <> Boxreg.zero6).
  { intros Hq. lazymatch goal with Hb : branch_taken _ _ _ = false |- _ =>
    rewrite (ck_br_eq0 _ 604 vz Ha0w ltac:(lia)) in Hb;
    apply Z.eqb_neq in Hb; apply Hb; apply Hcmp; exact Hq end. }
  ck_drop_br. clear Hcmp Ha0v Ha0w Hv0 Hvzr Hvz.
  ck_rn.
  ck_bcmp_rows_block 1 4 56 224.
  cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hcmp3 & Hfr3).
  jafter_call_keep_hi HS 640%nat regs3 (mrestrict (w_H W) mem3) HP3 [0%nat; 1%nat; 2%nat; 3%nat] HS3.
  match type of HS3 with ?tq -> _ => assert (HRK : tq); [|specialize (HS3 HRK); clear HRK] end.
  { ck_keep_regions Hfr3. }
  rewrite <- restrict_mkst_fx in HS3.
  clear HS HJ SHOK. rename HS3 into HS. rename HJ3 into HJ.
  ck_refresh. ck_hei. ck_shok.
  remember (bv_unsigned (getr regs3 10)) as vw eqn:Hvw.
  assert (Hw0 : getr regs3 10 = Z_to_bv 64 vw)
  by (rewrite Hvw; rewrite Z_to_bv_bv_unsigned; reflexivity).
  assert (Hvwr : 0 <= vw < 2 ^ 64)
  by (rewrite Hvw; pose proof (bv_unsigned_in_range 64 (getr regs3 10)) as Rq;
  unfold bv_modulus in Rq; change (2 ^ Z.of_N 64) with (2 ^ 64) in Rq; lia).
  ck_a0 644%nat vw Hw0 Ha0u.
  ck_ra.
  ck_rn.
  ck_lift Ha0u Ha0t.
  ck_brt.
  { (* equal MACs: B5 refutes the abort at 0x811b0 *)
    exfalso. lazymatch goal with Hb : branch_taken _ _ _ = true |- _ =>
    rewrite (ck_br_eq0 _ 644 vw Ha0t ltac:(lia)) in Hb;
    apply Z.eqb_eq in Hb;
    destruct (HB5 1 4 ltac:(lia) ltac:(lia) ltac:(lia)) as [Hq | Hq];
    [exact (Hnz Hq) | exact (Hq (proj1 Hcmp3 Hb))] end. }
  ck_drop_br. clear Hcmp3.
  ck_rnto 4712.
  ck_seat HS (ck_ih_facts 4) CLOB (ss_lat 1 4).
  lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _, HJq : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  apply (CONT2 Ef _ _ ltac:(assumption) HSq ltac:(assumption) ltac:(assumption) HJq) end. }
(* the two arms of the overlap test of 0x8117c *)
ck_brt.
{ (* base_4 >= base_1 + nch_1: the slices are apart, the walk goes straight to the MAC test *)
  ck_rnto 4684. ck_use_join CONT (ck_ih_facts 4). }
(* base_4 < base_1 + nch_1: the second test of the pair, refuted by B4 *)
assert (Hlt1 : Boxreg.bx_base bs 4 < Boxreg.bx_base bs 1 + Boxreg.bx_nch bs 1).
{ lazymatch goal with Hb : branch_taken _ _ _ = false |- _ =>
  ck_base_eq 36%nat 1 GA; ck_nch_eq 37%nat 1 GB; ck_base_eq 42%nat 4 GC;
  lazymatch type of GA with ew ?Ec _ = _ =>
  rewrite (ck_br_ge_sum Ec 42 36 37 (Boxreg.bx_base bs 4) (Boxreg.bx_base bs 1) (Boxreg.bx_nch bs 1)
  GC GA GB ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in Hb end;
  apply negb_false_iff in Hb; apply Z.ltb_lt in Hb; exact Hb end. }
ck_drop_br.
ck_rn.
assert (Hlt2 : Boxreg.bx_base bs 1 < Boxreg.bx_base bs 4 + Boxreg.bx_nch bs 4 -> False).
{ intros Hq. destruct (HB4 1 4 ltac:(lia) ltac:(lia) ltac:(lia)).
  split; [exact Hq | exact Hlt1]. }
ck_brt.
{ exfalso. lazymatch goal with Hb : branch_taken _ _ _ = true |- _ =>
  ck_base_eq 36%nat 1 GA; ck_base_eq 42%nat 4 GC; ck_nch_eq 43%nat 4 GD;
  lazymatch type of GA with ew ?Ec _ = _ =>
  rewrite (ck_br_lt_sum Ec 36 42 43 (Boxreg.bx_base bs 1) (Boxreg.bx_base bs 4) (Boxreg.bx_nch bs 4)
  GA GC GD ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in Hb end;
  apply Z.ltb_lt in Hb; exact (Hlt2 Hb) end. }
ck_drop_br.
ck_rnto 4684.
ck_use_join CONT (ck_ih_facts 4).
Qed.
Lemma ck_ih_1_3 : ck_oh_prop 2 -> ck_ih_prop 1 3.
Proof.
intros Hoh.
ck_head_intro.
change (Z.of_nat 3 + 1) with 4 in HNB.
destruct (Boxreg.B3_bounds bs 1 HB2 HB3 ltac:(lia)) as (Hb1 & Hc1 & Hs1).
destruct (Boxreg.B3_bounds bs 3 HB2 HB3 ltac:(lia)) as (Hb3 & Hc3 & Hs3).
ck_rn.
(* the pair (1, 3): the overlap test's two arms meet at the bcmp of 0x81198 *)
ck_join (mkAC BC_GE (SOff 40 0) (SAlu ALU_ADD (SOff 36 0) (SOff 37 0))) 4684 (ck_ih_facts 3) CONT.
{ ck_clear_state. intros Ex2 msX2 mdX2 HEI HS HAG Usp HJ. ck_shok.
  (* the pair's four paths meet again at the inner latch 0x811b4 *)
  assert (CONT2 : forall (Ex3 : env) (msX3 : machine_state) (mdX3 : Model),
  img_env VAL A_LIM Ex3 ->
  st_ok_pi SEGS VAL Ex3 (ss_lat 1 3) (restrict (w_H W) msX3) ->
  env_agree 44 (Ereg regs (ck_extra bs)) Ex3 ->
  bv_unsigned (ew Ex3 2) = spZ regs ->
  ajournal SEGS B CHECK_STK (spZ regs) [] ly S W mem md [] ly S W (ms_mem msX3) mdX3 0 ->
  SRr SEGS W (mkCfg msX3 mdX3) (tcheck_post regs ly S W mem md r bs)).
  { ck_clear_state. intros Ex3 msX3 mdX3 HEI HS HAG Usp HJ. ck_shok.
    (* the inner count n - 4 is 0 (n = 4: the latch leaves the inner loop) or not (n = 5: the pair (1, 4)) *)
    ck_rn. ck_n_eq Gn.
    ck_brt.
    - (* n = 4: the outer latch, i + 1 = 2 and n >= 3, takes the back edge to row 2's head *)
      clear Gn; ck_drop_br.
      ck_rnto 4468.
      ck_n_eq Gnx.
      ck_fact HS 33%nat (mkAF 3 5 0)
        ltac:(rewrite Gnx, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
      ck_seat HS (ck_oh_facts 2) CK_OH_CLOB (ss_oh 2).
      lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _, HJq : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      apply (Hoh ly S W regs mem md ch r fabric bs G HCTX ltac:(lia) Ef _ _ ltac:(assumption) HSq
      ltac:(assumption) HJq) end.
    - (* n = 5: the inner loop's head for the pair (1, 4) *)
      assert (HNB2 : Z.of_nat 4 + 1 <= Boxreg.bx_n bs).
      { lazymatch goal with Hb : branch_taken _ _ _ = false |- _ =>
        lazymatch type of Gn with ew ?Ec _ = _ =>
        rewrite (ck_br_eq0_off Ec 33 (-4) (Boxreg.bx_n bs) Gn ltac:(lia) ltac:(lia)) in Hb end;
        apply Z.eqb_neq in Hb; lia end. }
      clear Gn; ck_drop_br.
      destruct (Boxreg.B3_bounds bs 4 HB2 HB3 ltac:(lia)) as (Hbn & Hcn & Hsn).
      ck_rnto 4628.
      ck_base_eq 42%nat 4 Gb. ck_nch_eq 43%nat 4 Gc. ck_n_eq G33.
      ck_fact HS 42%nat (mkAF 0 38 0)
        ltac:(rewrite Gb, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
      ck_fact HS 43%nat (mkAF 2 40 0)
        ltac:(rewrite Gc, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
      ck_fact HS 33%nat (mkAF 5 5 0)
        ltac:(rewrite G33, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
      ck_fix_s6.
      ck_seat HS (ck_ih_facts 4) CLOB (ss_ih 1 4).
      lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _, HJq : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      apply (ck_ih_1_4 Hoh ly S W regs mem md ch r fabric bs G HCTX ltac:(lia) Ef _ _ ltac:(assumption) HSq
      ltac:(assumption) HJq) end. }
  ck_rn.
  ck_bcmp_zero_block 1 56.
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hcmp & Hfr2).
  jafter_call_keep_hi HS 600%nat regs2 (mrestrict (w_H W) mem2) HP2 [0%nat; 1%nat; 2%nat; 3%nat] HS2.
  match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
  { ck_keep_regions Hfr2. }
  rewrite <- restrict_mkst_fx in HS2.
  clear HS HJ SHOK. rename HS2 into HS. rename HJ2 into HJ.
  ck_refresh. ck_hei. ck_shok.
  remember (bv_unsigned (getr regs2 10)) as vz eqn:Hvz.
  assert (Hv0 : getr regs2 10 = Z_to_bv 64 vz)
  by (rewrite Hvz; rewrite Z_to_bv_bv_unsigned; reflexivity).
  assert (Hvzr : 0 <= vz < 2 ^ 64)
  by (rewrite Hvz; pose proof (bv_unsigned_in_range 64 (getr regs2 10)) as Rq;
  unfold bv_modulus in Rq; change (2 ^ Z.of_N 64) with (2 ^ 64) in Rq; lia).
  ck_a0 604%nat vz Hv0 Ha0v.
  ck_ra.
  ck_rn.
  ck_lift Ha0v Ha0w.
  ck_brt.
  { (* row 1's MAC is zero6: the pair is settled, the walk goes to the latch *)
    ck_drop_br. clear Hcmp.
    ck_rnto 4712.
    ck_seat HS (ck_ih_facts 3) CLOB (ss_lat 1 3).
    lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _, HJq : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    apply (CONT2 Ef _ _ ltac:(assumption) HSq ltac:(assumption) ltac:(assumption) HJq) end. }
  (* row 1's MAC is not zero6, so B5 makes it differ from row 3's *)
  assert (Hnz : Boxreg.bx_mac bs 1 <> Boxreg.zero6).
  { intros Hq. lazymatch goal with Hb : branch_taken _ _ _ = false |- _ =>
    rewrite (ck_br_eq0 _ 604 vz Ha0w ltac:(lia)) in Hb;
    apply Z.eqb_neq in Hb; apply Hb; apply Hcmp; exact Hq end. }
  ck_drop_br. clear Hcmp Ha0v Ha0w Hv0 Hvzr Hvz.
  ck_rn.
  ck_bcmp_rows_block 1 3 56 168.
  cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hcmp3 & Hfr3).
  jafter_call_keep_hi HS 640%nat regs3 (mrestrict (w_H W) mem3) HP3 [0%nat; 1%nat; 2%nat; 3%nat] HS3.
  match type of HS3 with ?tq -> _ => assert (HRK : tq); [|specialize (HS3 HRK); clear HRK] end.
  { ck_keep_regions Hfr3. }
  rewrite <- restrict_mkst_fx in HS3.
  clear HS HJ SHOK. rename HS3 into HS. rename HJ3 into HJ.
  ck_refresh. ck_hei. ck_shok.
  remember (bv_unsigned (getr regs3 10)) as vw eqn:Hvw.
  assert (Hw0 : getr regs3 10 = Z_to_bv 64 vw)
  by (rewrite Hvw; rewrite Z_to_bv_bv_unsigned; reflexivity).
  assert (Hvwr : 0 <= vw < 2 ^ 64)
  by (rewrite Hvw; pose proof (bv_unsigned_in_range 64 (getr regs3 10)) as Rq;
  unfold bv_modulus in Rq; change (2 ^ Z.of_N 64) with (2 ^ 64) in Rq; lia).
  ck_a0 644%nat vw Hw0 Ha0u.
  ck_ra.
  ck_rn.
  ck_lift Ha0u Ha0t.
  ck_brt.
  { (* equal MACs: B5 refutes the abort at 0x811b0 *)
    exfalso. lazymatch goal with Hb : branch_taken _ _ _ = true |- _ =>
    rewrite (ck_br_eq0 _ 644 vw Ha0t ltac:(lia)) in Hb;
    apply Z.eqb_eq in Hb;
    destruct (HB5 1 3 ltac:(lia) ltac:(lia) ltac:(lia)) as [Hq | Hq];
    [exact (Hnz Hq) | exact (Hq (proj1 Hcmp3 Hb))] end. }
  ck_drop_br. clear Hcmp3.
  ck_rnto 4712.
  ck_seat HS (ck_ih_facts 3) CLOB (ss_lat 1 3).
  lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _, HJq : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  apply (CONT2 Ef _ _ ltac:(assumption) HSq ltac:(assumption) ltac:(assumption) HJq) end. }
(* the two arms of the overlap test of 0x8117c *)
ck_brt.
{ (* base_3 >= base_1 + nch_1: the slices are apart, the walk goes straight to the MAC test *)
  ck_rnto 4684. ck_use_join CONT (ck_ih_facts 3). }
(* base_3 < base_1 + nch_1: the second test of the pair, refuted by B4 *)
assert (Hlt1 : Boxreg.bx_base bs 3 < Boxreg.bx_base bs 1 + Boxreg.bx_nch bs 1).
{ lazymatch goal with Hb : branch_taken _ _ _ = false |- _ =>
  ck_base_eq 36%nat 1 GA; ck_nch_eq 37%nat 1 GB; ck_base_eq 40%nat 3 GC;
  lazymatch type of GA with ew ?Ec _ = _ =>
  rewrite (ck_br_ge_sum Ec 40 36 37 (Boxreg.bx_base bs 3) (Boxreg.bx_base bs 1) (Boxreg.bx_nch bs 1)
  GC GA GB ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in Hb end;
  apply negb_false_iff in Hb; apply Z.ltb_lt in Hb; exact Hb end. }
ck_drop_br.
ck_rn.
assert (Hlt2 : Boxreg.bx_base bs 1 < Boxreg.bx_base bs 3 + Boxreg.bx_nch bs 3 -> False).
{ intros Hq. destruct (HB4 1 3 ltac:(lia) ltac:(lia) ltac:(lia)).
  split; [exact Hq | exact Hlt1]. }
ck_brt.
{ exfalso. lazymatch goal with Hb : branch_taken _ _ _ = true |- _ =>
  ck_base_eq 36%nat 1 GA; ck_base_eq 40%nat 3 GC; ck_nch_eq 41%nat 3 GD;
  lazymatch type of GA with ew ?Ec _ = _ =>
  rewrite (ck_br_lt_sum Ec 36 40 41 (Boxreg.bx_base bs 1) (Boxreg.bx_base bs 3) (Boxreg.bx_nch bs 3)
  GA GC GD ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in Hb end;
  apply Z.ltb_lt in Hb; exact (Hlt2 Hb) end. }
ck_drop_br.
ck_rnto 4684.
ck_use_join CONT (ck_ih_facts 3).
Qed.
Lemma ck_ih_1_2 : ck_oh_prop 2 -> ck_ih_prop 1 2.
Proof.
intros Hoh.
ck_head_intro.
change (Z.of_nat 2 + 1) with 3 in HNB.
destruct (Boxreg.B3_bounds bs 1 HB2 HB3 ltac:(lia)) as (Hb1 & Hc1 & Hs1).
destruct (Boxreg.B3_bounds bs 2 HB2 HB3 ltac:(lia)) as (Hb2' & Hc2' & Hs2').
ck_rn.
(* the pair (1, 2): the overlap test's two arms meet at the bcmp of 0x81198 *)
ck_join (mkAC BC_GE (SOff 38 0) (SAlu ALU_ADD (SOff 36 0) (SOff 37 0))) 4684 (ck_ih_facts 2) CONT.
{ ck_clear_state. intros Ex2 msX2 mdX2 HEI HS HAG Usp HJ. ck_shok.
  (* the pair's four paths meet again at the inner latch 0x811b4 *)
  assert (CONT2 : forall (Ex3 : env) (msX3 : machine_state) (mdX3 : Model),
  img_env VAL A_LIM Ex3 ->
  st_ok_pi SEGS VAL Ex3 (ss_lat 1 2) (restrict (w_H W) msX3) ->
  env_agree 44 (Ereg regs (ck_extra bs)) Ex3 ->
  bv_unsigned (ew Ex3 2) = spZ regs ->
  ajournal SEGS B CHECK_STK (spZ regs) [] ly S W mem md [] ly S W (ms_mem msX3) mdX3 0 ->
  SRr SEGS W (mkCfg msX3 mdX3) (tcheck_post regs ly S W mem md r bs)).
  { ck_clear_state. intros Ex3 msX3 mdX3 HEI HS HAG Usp HJ. ck_shok.
    (* the inner count n - 3 is 0 (n = 3: the latch leaves the inner loop) or not (n >= 4: the pair (1, 3)) *)
    ck_rn. ck_n_eq Gn.
    ck_brt.
    - (* n = 3: the outer latch, i + 1 = 2 and n >= 3, takes the back edge to row 2's head *)
      clear Gn; ck_drop_br.
      ck_rnto 4468.
      ck_n_eq Gnx.
      ck_fact HS 33%nat (mkAF 3 5 0)
        ltac:(rewrite Gnx, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
      ck_seat HS (ck_oh_facts 2) CK_OH_CLOB (ss_oh 2).
      lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _, HJq : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      apply (Hoh ly S W regs mem md ch r fabric bs G HCTX ltac:(lia) Ef _ _ ltac:(assumption) HSq
      ltac:(assumption) HJq) end.
    - (* n >= 4: the inner loop's head for the pair (1, 3) *)
      assert (HNB2 : Z.of_nat 3 + 1 <= Boxreg.bx_n bs).
      { lazymatch goal with Hb : branch_taken _ _ _ = false |- _ =>
        lazymatch type of Gn with ew ?Ec _ = _ =>
        rewrite (ck_br_eq0_off Ec 33 (-3) (Boxreg.bx_n bs) Gn ltac:(lia) ltac:(lia)) in Hb end;
        apply Z.eqb_neq in Hb; lia end. }
      clear Gn; ck_drop_br.
      destruct (Boxreg.B3_bounds bs 3 HB2 HB3 ltac:(lia)) as (Hbn & Hcn & Hsn).
      ck_rnto 4628.
      ck_base_eq 40%nat 3 Gb. ck_nch_eq 41%nat 3 Gc. ck_n_eq G33.
      ck_fact HS 40%nat (mkAF 0 38 0)
        ltac:(rewrite Gb, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
      ck_fact HS 41%nat (mkAF 2 40 0)
        ltac:(rewrite Gc, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
      ck_fact HS 33%nat (mkAF 4 5 0)
        ltac:(rewrite G33, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
      ck_fix_s6.
      ck_seat HS (ck_ih_facts 3) CLOB (ss_ih 1 3).
      lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _, HJq : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      apply (ck_ih_1_3 Hoh ly S W regs mem md ch r fabric bs G HCTX ltac:(lia) Ef _ _ ltac:(assumption) HSq
      ltac:(assumption) HJq) end. }
  ck_rn.
  ck_bcmp_zero_block 1 56.
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hcmp & Hfr2).
  jafter_call_keep_hi HS 600%nat regs2 (mrestrict (w_H W) mem2) HP2 [0%nat; 1%nat; 2%nat; 3%nat] HS2.
  match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
  { ck_keep_regions Hfr2. }
  rewrite <- restrict_mkst_fx in HS2.
  clear HS HJ SHOK. rename HS2 into HS. rename HJ2 into HJ.
  ck_refresh. ck_hei. ck_shok.
  remember (bv_unsigned (getr regs2 10)) as vz eqn:Hvz.
  assert (Hv0 : getr regs2 10 = Z_to_bv 64 vz)
  by (rewrite Hvz; rewrite Z_to_bv_bv_unsigned; reflexivity).
  assert (Hvzr : 0 <= vz < 2 ^ 64)
  by (rewrite Hvz; pose proof (bv_unsigned_in_range 64 (getr regs2 10)) as Rq;
  unfold bv_modulus in Rq; change (2 ^ Z.of_N 64) with (2 ^ 64) in Rq; lia).
  ck_a0 604%nat vz Hv0 Ha0v.
  ck_ra.
  ck_rn.
  ck_lift Ha0v Ha0w.
  ck_brt.
  { (* row 1's MAC is zero6: the pair is settled, the walk goes to the latch *)
    ck_drop_br. clear Hcmp.
    ck_rnto 4712.
    ck_seat HS (ck_ih_facts 2) CLOB (ss_lat 1 2).
    lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _, HJq : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    apply (CONT2 Ef _ _ ltac:(assumption) HSq ltac:(assumption) ltac:(assumption) HJq) end. }
  (* row 1's MAC is not zero6, so B5 makes it differ from row 2's *)
  assert (Hnz : Boxreg.bx_mac bs 1 <> Boxreg.zero6).
  { intros Hq. lazymatch goal with Hb : branch_taken _ _ _ = false |- _ =>
    rewrite (ck_br_eq0 _ 604 vz Ha0w ltac:(lia)) in Hb;
    apply Z.eqb_neq in Hb; apply Hb; apply Hcmp; exact Hq end. }
  ck_drop_br. clear Hcmp Ha0v Ha0w Hv0 Hvzr Hvz.
  ck_rn.
  ck_bcmp_rows_block 1 2 56 112.
  cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hcmp3 & Hfr3).
  jafter_call_keep_hi HS 640%nat regs3 (mrestrict (w_H W) mem3) HP3 [0%nat; 1%nat; 2%nat; 3%nat] HS3.
  match type of HS3 with ?tq -> _ => assert (HRK : tq); [|specialize (HS3 HRK); clear HRK] end.
  { ck_keep_regions Hfr3. }
  rewrite <- restrict_mkst_fx in HS3.
  clear HS HJ SHOK. rename HS3 into HS. rename HJ3 into HJ.
  ck_refresh. ck_hei. ck_shok.
  remember (bv_unsigned (getr regs3 10)) as vw eqn:Hvw.
  assert (Hw0 : getr regs3 10 = Z_to_bv 64 vw)
  by (rewrite Hvw; rewrite Z_to_bv_bv_unsigned; reflexivity).
  assert (Hvwr : 0 <= vw < 2 ^ 64)
  by (rewrite Hvw; pose proof (bv_unsigned_in_range 64 (getr regs3 10)) as Rq;
  unfold bv_modulus in Rq; change (2 ^ Z.of_N 64) with (2 ^ 64) in Rq; lia).
  ck_a0 644%nat vw Hw0 Ha0u.
  ck_ra.
  ck_rn.
  ck_lift Ha0u Ha0t.
  ck_brt.
  { (* equal MACs: B5 refutes the abort at 0x811b0 *)
    exfalso. lazymatch goal with Hb : branch_taken _ _ _ = true |- _ =>
    rewrite (ck_br_eq0 _ 644 vw Ha0t ltac:(lia)) in Hb;
    apply Z.eqb_eq in Hb;
    destruct (HB5 1 2 ltac:(lia) ltac:(lia) ltac:(lia)) as [Hq | Hq];
    [exact (Hnz Hq) | exact (Hq (proj1 Hcmp3 Hb))] end. }
  ck_drop_br. clear Hcmp3.
  ck_rnto 4712.
  ck_seat HS (ck_ih_facts 2) CLOB (ss_lat 1 2).
  lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _, HJq : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  apply (CONT2 Ef _ _ ltac:(assumption) HSq ltac:(assumption) ltac:(assumption) HJq) end. }
(* the two arms of the overlap test of 0x8117c *)
ck_brt.
{ (* base_2 >= base_1 + nch_1: the slices are apart, the walk goes straight to the MAC test *)
  ck_rnto 4684. ck_use_join CONT (ck_ih_facts 2). }
(* base_2 < base_1 + nch_1: the second test of the pair, refuted by B4 *)
assert (Hlt1 : Boxreg.bx_base bs 2 < Boxreg.bx_base bs 1 + Boxreg.bx_nch bs 1).
{ lazymatch goal with Hb : branch_taken _ _ _ = false |- _ =>
  ck_base_eq 36%nat 1 GA; ck_nch_eq 37%nat 1 GB; ck_base_eq 38%nat 2 GC;
  lazymatch type of GA with ew ?Ec _ = _ =>
  rewrite (ck_br_ge_sum Ec 38 36 37 (Boxreg.bx_base bs 2) (Boxreg.bx_base bs 1) (Boxreg.bx_nch bs 1)
  GC GA GB ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in Hb end;
  apply negb_false_iff in Hb; apply Z.ltb_lt in Hb; exact Hb end. }
ck_drop_br.
ck_rn.
assert (Hlt2 : Boxreg.bx_base bs 1 < Boxreg.bx_base bs 2 + Boxreg.bx_nch bs 2 -> False).
{ intros Hq. destruct (HB4 1 2 ltac:(lia) ltac:(lia) ltac:(lia)).
  split; [exact Hq | exact Hlt1]. }
ck_brt.
{ exfalso. lazymatch goal with Hb : branch_taken _ _ _ = true |- _ =>
  ck_base_eq 36%nat 1 GA; ck_base_eq 38%nat 2 GC; ck_nch_eq 39%nat 2 GD;
  lazymatch type of GA with ew ?Ec _ = _ =>
  rewrite (ck_br_lt_sum Ec 36 38 39 (Boxreg.bx_base bs 1) (Boxreg.bx_base bs 2) (Boxreg.bx_nch bs 2)
  GA GC GD ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in Hb end;
  apply Z.ltb_lt in Hb; exact (Hlt2 Hb) end. }
ck_drop_br.
ck_rnto 4684.
ck_use_join CONT (ck_ih_facts 2).
Qed.
(* The inner pairs (0, j) of row 0, j = 4 down to 1, each from ck_ih_34's segment (the pair test at 0x8117c, the bcmp
   calls 0x81198 / 0x811ac, the latch 0x811b4). For j < 4 the inner count's test 0x811c4 has both arms: n = j + 1
   goes to row 1's head through the outer latch (the hypothesis ck_oh_prop 1), n >= j + 2 to the pair (0, j + 1).
   rule 24: proves no function (kind: segment lemma). *)
(* ck_bcmp_zero_at / ck_bcmp_rows_at for row 0 (ioff = 0): the engine keeps a0 as the atom itself (SOff 10 0 reads back
   as ew E 10), so the register premise is closed from the atom's equation directly. Otherwise the same text. *)
Ltac ck_bcmp_zero_at0 HS zi ioff :=
lazymatch goal with
| HC : ck_ctx ?ly ?S ?W ?regs ?mem ?md ?ch ?r ?fabric ?bs ?G,
  HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  Usp : bv_unsigned (ew _ 2) = spZ _,
  HAG : env_agree 44 (Ereg _ (ck_extra _)) ?Ec, HEIq : img_env _ _ ?Ec |- _ =>
let Ra0 := fresh "Ra0" in let Ra1 := fresh "Ra1" in let Ra2 := fresh "Ra2" in
let Rra := fresh "Rra" in let Rsp := fresh "Rsp" in let Rgp := fresh "Rgp" in let Rtp := fresh "Rtp" in
let G10m := fresh "G10m" in let E3q := fresh "E3q" in let E4q := fresh "E4q" in
let HCq := fresh "HCq" in let HPREq := fresh "HPREq" in
let Hgpq := fresh "Hgpq" in let Htpq := fresh "Htpq" in let Qsp := fresh "Qsp" in
pose proof HC as HCq; destruct HCq as (HPREq & _);
pose proof HPREq as (_ & _ & _ & Hgpq & Htpq & _ & _ & _ & _);
ck_r_eq G10m; ck_reg_eq 3%nat (3%bv : bv 5) E3q; ck_reg_eq 4%nat (4%bv : bv 5) E4q;
pmkst HS;
prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (12%bv : bv 5) Ra2;
prreg HS (1%bv : bv 5) Rra; prreg HS (2%bv : bv 5) Rsp; prreg HS (3%bv : bv 5) Rgp; prreg HS (4%bv : bv 5) Rtp;
ck_ew_in G10m; ck_ew_in E3q; ck_ew_in E4q;
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdQ) _ =>
assert (Qsp : spZ rg = spZ regs + -160);
[ let Hu := fresh "Hu" in
  lazymatch type of Rsp with _ = Z_to_bv 64 (bv_unsigned (ew ?Ecu 2) + _) =>
  assert (Hu : bv_unsigned (ew Ecu 2) = spZ regs) by ck_usp_by Usp end;
  unfold spZ at 1; rewrite Rsp; rewrite unsigned_lit_small by (rewrite Hu; lia);
  rewrite Hu; reflexivity | ];
eapply SRr_bind;
[ eapply (ck_bcmp_zero ly S W regs mem md ch r fabric bs G rg mm mdQ zi HC HJ ltac:(lia));
  [ rewrite Ra0; first [ exact (ck_denot_off _ 10 r ioff G10m) | replace (r + 56 * zi) with r by lia; exact G10m ]
  | rewrite Ra1; apply bv_eq;
    lazymatch goal with |- bv_unsigned (ew ?Ep 247) = _ =>
    let Hi := fresh "Hi" in assert (Hi : img_env VAL A_LIM Ep) by ck_img;
    rewrite (Hi 247%nat ltac:(cbv; lia)) end;
    unfold w64; rewrite unsigned_lit_small by apply pa_val_range; reflexivity
  | rewrite Ra2; reflexivity
  | exact Qsp
  | rewrite Rgp; rewrite E3q; exact Hgpq
  | rewrite Rtp; rewrite E4q; exact Htpq
  | rewrite Rra; apply ret_ok_codeptr_v; [lia | reflexivity] ]
| ] end end.
Ltac ck_bcmp_rows_at0 HS zi zj ioff joff :=
lazymatch goal with
| HC : ck_ctx ?ly ?S ?W ?regs ?mem ?md ?ch ?r ?fabric ?bs ?G,
  HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  Usp : bv_unsigned (ew _ 2) = spZ _,
  HAG : env_agree 44 (Ereg _ (ck_extra _)) ?Ec |- _ =>
let Ra0 := fresh "Ra0" in let Ra1 := fresh "Ra1" in let Ra2 := fresh "Ra2" in
let Rra := fresh "Rra" in let Rsp := fresh "Rsp" in let Rgp := fresh "Rgp" in let Rtp := fresh "Rtp" in
let G10m := fresh "G10m" in let E3q := fresh "E3q" in let E4q := fresh "E4q" in
let HCq := fresh "HCq" in let HPREq := fresh "HPREq" in
let Hgpq := fresh "Hgpq" in let Htpq := fresh "Htpq" in let Qsp := fresh "Qsp" in
pose proof HC as HCq; destruct HCq as (HPREq & _);
pose proof HPREq as (_ & _ & _ & Hgpq & Htpq & _ & _ & _ & _);
ck_r_eq G10m; ck_reg_eq 3%nat (3%bv : bv 5) E3q; ck_reg_eq 4%nat (4%bv : bv 5) E4q;
pmkst HS;
prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (12%bv : bv 5) Ra2;
prreg HS (1%bv : bv 5) Rra; prreg HS (2%bv : bv 5) Rsp; prreg HS (3%bv : bv 5) Rgp; prreg HS (4%bv : bv 5) Rtp;
ck_ew_in G10m; ck_ew_in E3q; ck_ew_in E4q;
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdQ) _ =>
assert (Qsp : spZ rg = spZ regs + -160);
[ let Hu := fresh "Hu" in
  lazymatch type of Rsp with _ = Z_to_bv 64 (bv_unsigned (ew ?Ecu 2) + _) =>
  assert (Hu : bv_unsigned (ew Ecu 2) = spZ regs) by ck_usp_by Usp end;
  unfold spZ at 1; rewrite Rsp; rewrite unsigned_lit_small by (rewrite Hu; lia);
  rewrite Hu; reflexivity | ];
eapply SRr_bind;
[ eapply (ck_bcmp_rows ly S W regs mem md ch r fabric bs G rg mm mdQ zi zj HC HJ ltac:(lia) ltac:(lia));
  [ rewrite Ra0; first [ exact (ck_denot_off _ 10 r ioff G10m) | replace (r + 56 * zi) with r by lia; exact G10m ]
  | rewrite Ra1; first [ exact (ck_denot_off _ 10 r joff G10m) | replace (r + 56 * zj) with r by lia; exact G10m ]
  | rewrite Ra2; reflexivity
  | exact Qsp
  | rewrite Rgp; rewrite E3q; exact Hgpq
  | rewrite Rtp; rewrite E4q; exact Htpq
  | rewrite Rra; apply ret_ok_codeptr_v; [lia | reflexivity] ]
| ] end end.
Ltac ck_bcmp_zero_block0 zi ioff :=
lazymatch goal with
| HSq : st_ok_pi _ _ _ _ _ |- _ => ck_bcmp_zero_at0 HSq zi ioff
| HSq : st_ok _ _ _ _ |- _ => ck_bcmp_zero_at0 HSq zi ioff
end.
Ltac ck_bcmp_rows_block0 zi zj ioff joff :=
lazymatch goal with
| HSq : st_ok_pi _ _ _ _ _ |- _ => ck_bcmp_rows_at0 HSq zi zj ioff joff
| HSq : st_ok _ _ _ _ |- _ => ck_bcmp_rows_at0 HSq zi zj ioff joff
end.
(* the shadow pointer s6 after the inner latch (0x811c0 addi s6,s6,7) against its head form: with (r + k) a multiple
   of 8, sb + ((r + k) >> 3) + 7 = sb + ((r + k + 56) >> 3) *)
Lemma ck_s6_relatch : forall (E : env) sb r k k2, k2 = k + 56 -> ew E 32 = Z_to_bv 64 sb -> ew E 10 = Z_to_bv 64 r ->
0 <= sb -> sb + 2 ^ 61 < 2 ^ 64 -> 0 <= r -> 0 <= k -> r + k + 56 < 2 ^ 63 -> (r + k) mod 8 = 0 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff 10 k) (SLit 3))) (SLit 7)) =
sv_denot E (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff 10 k2) (SLit 3))).
Proof.
intros E sb r k k2 -> H32 H10 Hs0 Hs1 Hr Hk Hrk Hm.
assert (HU : U E (SAlu ALU_ADD (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff 10 k) (SLit 3))) (SLit 7)) =
  U E (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff 10 (k + 56)) (SLit 3)))).
{ rewrite !U_SAlu, !U_SOff, !U_SLit. cbn [zalu_raw]. rewrite H32, H10.
  rewrite !unsigned_lit_small by lia.
  change (zcanon 3) with 3. change (Z.land 3 63) with 3. change (zcanon 7) with 7.
  rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  unfold zcanon, M64. Z.div_mod_to_equations. lia. }
apply bv_eq. exact HU.
Qed.
Lemma ck_ih_0_4 : ck_oh_prop 1 -> ck_ih_prop 0 4.
Proof.
intros Hoh1.
ck_head_intro.
change (Z.of_nat 4 + 1) with 5 in HNB.
assert (Hn5 : Boxreg.bx_n bs = 5) by lia.
destruct (Boxreg.B3_bounds bs 0 HB2 HB3 ltac:(lia)) as (Hb0 & Hc0 & Hs0).
destruct (Boxreg.B3_bounds bs 4 HB2 HB3 ltac:(lia)) as (Hbj & Hcj & Hsj).
ck_rn.
(* the pair (0, 4): the overlap test's two arms meet at the bcmp of 0x81198 *)
ck_join (mkAC BC_GE (SOff 42 0) (SAlu ALU_ADD (SOff 34 0) (SOff 35 0))) 4684 (ck_ih_facts 4) CONT.
{ ck_clear_state. intros Ex2 msX2 mdX2 HEI HS HAG Usp HJ. ck_shok.
  (* the pair's four paths meet again at the inner latch 0x811b4 *)
  assert (CONT2 : forall (Ex3 : env) (msX3 : machine_state) (mdX3 : Model),
  img_env VAL A_LIM Ex3 ->
  st_ok_pi SEGS VAL Ex3 (ss_lat 0 4) (restrict (w_H W) msX3) ->
  env_agree 44 (Ereg regs (ck_extra bs)) Ex3 ->
  bv_unsigned (ew Ex3 2) = spZ regs ->
  ajournal SEGS B CHECK_STK (spZ regs) [] ly S W mem md [] ly S W (ms_mem msX3) mdX3 0 ->
  SRr SEGS W (mkCfg msX3 mdX3) (tcheck_post regs ly S W mem md r bs)).
  { ck_clear_state. intros Ex3 msX3 mdX3 HEI HS HAG Usp HJ. ck_shok.
    (* n - 5 = 0 at the latch: the inner loop is done; the outer latch takes the back edge to row 1 *)
    ck_rn. ck_n_eq Gn.
    ck_brt.
    2:{ exfalso. lazymatch goal with Hb : branch_taken _ _ _ = false |- _ =>
        lazymatch type of Gn with ew ?Ec _ = _ =>
        rewrite (ck_br_eq0_off Ec 33 (-5) (Boxreg.bx_n bs) Gn ltac:(lia) ltac:(lia)) in Hb end;
        apply Z.eqb_neq in Hb; lia end. }
    ck_drop_br.
    ck_fact HS 33%nat (mkAF 2 5 0)
      ltac:(rewrite Gn, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
    clear Gn.
    ck_rnto 4468.
    ck_seat HS (ck_oh_facts 1) CK_OH_CLOB (ss_oh 1).
    ck_refresh.
    lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _ |- _ =>
      assert (HEIf : img_env VAL A_LIM Ef)
        by (repeat first [ assumption | apply img_env_havoc_hi; [|cbv; lia] | apply img_env_ewset_hi; [|cbv; lia] ]) end.
    lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _, HJq : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    apply (Hoh1 ly S W regs mem md ch r fabric bs G HCTX ltac:(lia) Ef _ _ ltac:(assumption) HSq
    ltac:(assumption) HJq) end. }
  ck_rn.
  ck_bcmp_zero_block0 0 0.
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hcmp & Hfr2).
  jafter_call_keep_hi HS 600%nat regs2 (mrestrict (w_H W) mem2) HP2 [0%nat; 1%nat; 2%nat; 3%nat] HS2.
  match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
  { ck_keep_regions Hfr2. }
  rewrite <- restrict_mkst_fx in HS2.
  clear HS HJ SHOK. rename HS2 into HS. rename HJ2 into HJ.
  ck_refresh. ck_hei. ck_shok.
  remember (bv_unsigned (getr regs2 10)) as vz eqn:Hvz.
  assert (Hv0 : getr regs2 10 = Z_to_bv 64 vz)
  by (rewrite Hvz; rewrite Z_to_bv_bv_unsigned; reflexivity).
  assert (Hvzr : 0 <= vz < 2 ^ 64)
  by (rewrite Hvz; pose proof (bv_unsigned_in_range 64 (getr regs2 10)) as Rq;
  unfold bv_modulus in Rq; change (2 ^ Z.of_N 64) with (2 ^ 64) in Rq; lia).
  ck_a0 604%nat vz Hv0 Ha0v.
  ck_ra.
  ck_rn.
  ck_lift Ha0v Ha0w.
  ck_brt.
  { (* row 0's MAC is zero6: the pair is settled, the walk goes to the latch *)
    ck_drop_br. clear Hcmp.
    ck_rnto 4712.
    ck_seat HS (ck_ih_facts 4) CLOB (ss_lat 0 4).
    lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _, HJq : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    apply (CONT2 Ef _ _ ltac:(assumption) HSq ltac:(assumption) ltac:(assumption) HJq) end. }
  (* row 0's MAC is not zero6, so B5 makes it differ from row 4's *)
  assert (Hnz : Boxreg.bx_mac bs 0 <> Boxreg.zero6).
  { intros Hq. lazymatch goal with Hb : branch_taken _ _ _ = false |- _ =>
    rewrite (ck_br_eq0 _ 604 vz Ha0w ltac:(lia)) in Hb;
    apply Z.eqb_neq in Hb; apply Hb; apply Hcmp; exact Hq end. }
  ck_drop_br. clear Hcmp Ha0v Ha0w Hv0 Hvzr Hvz.
  ck_rn.
  ck_bcmp_rows_block0 0 4 0 224.
  cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hcmp3 & Hfr3).
  jafter_call_keep_hi HS 640%nat regs3 (mrestrict (w_H W) mem3) HP3 [0%nat; 1%nat; 2%nat; 3%nat] HS3.
  match type of HS3 with ?tq -> _ => assert (HRK : tq); [|specialize (HS3 HRK); clear HRK] end.
  { ck_keep_regions Hfr3. }
  rewrite <- restrict_mkst_fx in HS3.
  clear HS HJ SHOK. rename HS3 into HS. rename HJ3 into HJ.
  ck_refresh. ck_hei. ck_shok.
  remember (bv_unsigned (getr regs3 10)) as vw eqn:Hvw.
  assert (Hw0 : getr regs3 10 = Z_to_bv 64 vw)
  by (rewrite Hvw; rewrite Z_to_bv_bv_unsigned; reflexivity).
  assert (Hvwr : 0 <= vw < 2 ^ 64)
  by (rewrite Hvw; pose proof (bv_unsigned_in_range 64 (getr regs3 10)) as Rq;
  unfold bv_modulus in Rq; change (2 ^ Z.of_N 64) with (2 ^ 64) in Rq; lia).
  ck_a0 644%nat vw Hw0 Ha0u.
  ck_ra.
  ck_rn.
  ck_lift Ha0u Ha0t.
  ck_brt.
  { (* equal MACs: B5 refutes the abort at 0x811b0 *)
    exfalso. lazymatch goal with Hb : branch_taken _ _ _ = true |- _ =>
    rewrite (ck_br_eq0 _ 644 vw Ha0t ltac:(lia)) in Hb;
    apply Z.eqb_eq in Hb;
    destruct (HB5 0 4 ltac:(lia) ltac:(lia) ltac:(lia)) as [Hq | Hq];
    [exact (Hnz Hq) | exact (Hq (proj1 Hcmp3 Hb))] end. }
  ck_drop_br. clear Hcmp3.
  ck_rnto 4712.
  ck_seat HS (ck_ih_facts 4) CLOB (ss_lat 0 4).
  lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _, HJq : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  apply (CONT2 Ef _ _ ltac:(assumption) HSq ltac:(assumption) ltac:(assumption) HJq) end. }
(* the two arms of the overlap test of 0x8117c *)
ck_brt.
{ (* base_4 >= base_0 + nch_0: the slices are apart, the walk goes straight to the MAC test *)
  ck_rnto 4684. ck_use_join CONT (ck_ih_facts 4). }
(* base_4 < base_0 + nch_0: the second test of the pair, refuted by B4 *)
assert (Hlt1 : Boxreg.bx_base bs 4 < Boxreg.bx_base bs 0 + Boxreg.bx_nch bs 0).
{ lazymatch goal with Hb : branch_taken _ _ _ = false |- _ =>
  ck_base_eq 34%nat 0 GA; ck_nch_eq 35%nat 0 GB; ck_base_eq 42%nat 4 GC;
  lazymatch type of GA with ew ?Ec _ = _ =>
  rewrite (ck_br_ge_sum Ec 42 34 35 (Boxreg.bx_base bs 4) (Boxreg.bx_base bs 0) (Boxreg.bx_nch bs 0)
  GC GA GB ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in Hb end;
  apply negb_false_iff in Hb; apply Z.ltb_lt in Hb; exact Hb end. }
ck_drop_br.
ck_rn.
assert (Hlt2 : Boxreg.bx_base bs 0 < Boxreg.bx_base bs 4 + Boxreg.bx_nch bs 4 -> False).
{ intros Hq. destruct (HB4 0 4 ltac:(lia) ltac:(lia) ltac:(lia)).
  split; [exact Hq | exact Hlt1]. }
ck_brt.
{ exfalso. lazymatch goal with Hb : branch_taken _ _ _ = true |- _ =>
  ck_base_eq 34%nat 0 GA; ck_base_eq 42%nat 4 GC; ck_nch_eq 43%nat 4 GD;
  lazymatch type of GA with ew ?Ec _ = _ =>
  rewrite (ck_br_lt_sum Ec 34 42 43 (Boxreg.bx_base bs 0) (Boxreg.bx_base bs 4) (Boxreg.bx_nch bs 4)
  GA GC GD ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in Hb end;
  apply Z.ltb_lt in Hb; exact (Hlt2 Hb) end. }
ck_drop_br.
ck_rnto 4684.
ck_use_join CONT (ck_ih_facts 4).
Qed.
Lemma ck_ih_0_3 : ck_oh_prop 1 -> ck_ih_prop 0 3.
Proof.
intros Hoh1.
ck_head_intro.
change (Z.of_nat 3 + 1) with 4 in HNB.
destruct (Boxreg.B3_bounds bs 0 HB2 HB3 ltac:(lia)) as (Hb0 & Hc0 & Hs0).
destruct (Boxreg.B3_bounds bs 3 HB2 HB3 ltac:(lia)) as (Hbj & Hcj & Hsj).
ck_rn.
(* the pair (0, 3): the overlap test's two arms meet at the bcmp of 0x81198 *)
ck_join (mkAC BC_GE (SOff 40 0) (SAlu ALU_ADD (SOff 34 0) (SOff 35 0))) 4684 (ck_ih_facts 3) CONT.
{ ck_clear_state. intros Ex2 msX2 mdX2 HEI HS HAG Usp HJ. ck_shok.
  (* the pair's four paths meet again at the inner latch 0x811b4 *)
  assert (CONT2 : forall (Ex3 : env) (msX3 : machine_state) (mdX3 : Model),
  img_env VAL A_LIM Ex3 ->
  st_ok_pi SEGS VAL Ex3 (ss_lat 0 3) (restrict (w_H W) msX3) ->
  env_agree 44 (Ereg regs (ck_extra bs)) Ex3 ->
  bv_unsigned (ew Ex3 2) = spZ regs ->
  ajournal SEGS B CHECK_STK (spZ regs) [] ly S W mem md [] ly S W (ms_mem msX3) mdX3 0 ->
  SRr SEGS W (mkCfg msX3 mdX3) (tcheck_post regs ly S W mem md r bs)).
  { ck_clear_state. intros Ex3 msX3 mdX3 HEI HS HAG Usp HJ. ck_shok.
    (* the inner count's test 0x811c4 (beqz s7, s7 = n - 4) has both arms *)
    ck_rn. ck_n_eq Gn.
    ck_brt.
    { (* taken: n = 4; the outer latch takes the back edge to row 1 *)
      lazymatch goal with Hb : branch_taken _ _ _ = true |- _ =>
        lazymatch type of Gn with ew ?Ec _ = _ =>
        rewrite (ck_br_eq0_off Ec 33 (-4) (Boxreg.bx_n bs) Gn ltac:(lia) ltac:(lia)) in Hb end;
        apply Z.eqb_eq in Hb; assert (HnJ : Boxreg.bx_n bs = 4) by lia; clear Hb end.
      ck_drop_br.
      ck_fact HS 33%nat (mkAF 4 4 0)
        ltac:(rewrite Gn, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
      ck_fact HS 33%nat (mkAF 2 5 0)
        ltac:(rewrite Gn, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
      clear Gn.
      ck_rnto 4468.
      ck_seat HS (ck_oh_facts 1) CK_OH_CLOB (ss_oh 1).
      ck_refresh.
      lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _ |- _ =>
        assert (HEIf : img_env VAL A_LIM Ef)
          by (repeat first [ assumption | apply img_env_havoc_hi; [|cbv; lia] | apply img_env_ewset_hi; [|cbv; lia] ]) end.
      lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _, HJq : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      apply (Hoh1 ly S W regs mem md ch r fabric bs G HCTX ltac:(lia) Ef _ _ ltac:(assumption) HSq
      ltac:(assumption) HJq) end. }
    (* not taken: n >= 5; the inner loop's head for the pair (0, 4) *)
    lazymatch goal with Hb : branch_taken _ _ _ = false |- _ =>
      lazymatch type of Gn with ew ?Ec _ = _ =>
      rewrite (ck_br_eq0_off Ec 33 (-4) (Boxreg.bx_n bs) Gn ltac:(lia) ltac:(lia)) in Hb end;
      apply Z.eqb_neq in Hb; assert (HNB2 : Z.of_nat 4 + 1 <= Boxreg.bx_n bs) by lia; clear Hb end.
    destruct (Boxreg.B3_bounds bs 4 HB2 HB3 ltac:(lia)) as (Hbn & Hcn & Hsn).
    ck_drop_br.
    ck_fact HS 33%nat (mkAF 5 5 0)
      ltac:(rewrite Gn, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
    clear Gn.
    ck_rnto 4628.
    (* s6 came through the inner latch: put it in the head's form *)
    prreg HS (22%bv : bv 5) R22.
    ck_r_eq G10s. ck_sb_eq G32s.
    lazymatch type of HS with st_ok_pi _ _ ?Ec ?ssq ?msq =>
      let H2 := fresh "HSs" in
      pose proof (st_ok_pi_set_reg Ec ssq msq 22%bv (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff 10 232) (SLit 3))) HS
        ltac:(discriminate)
        ltac:(let Hq := fresh "Hq" in
              pose proof (ck_s6_relatch Ec SB r 176 232 eq_refl G32s G10s ltac:(unfold SB; lia) ltac:(unfold SB; lia)
                ltac:(lia) ltac:(lia) ltac:(unfold ASAN_CEIL in *; lia) ltac:(Z.div_mod_to_equations; lia)) as Hq;
              etransitivity; [exact R22 |]; cbn [sv_denot] in Hq |- *;
              rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Hq |- *; exact Hq)) as H2;
      clear HS; rename H2 into HS; ck_norm HS end.
    clear R22 G10s G32s.
    ck_base_eq 42%nat 4 Gb. ck_nch_eq 43%nat 4 Gc.
    ck_fact HS 42%nat (mkAF 0 38 0)
      ltac:(rewrite Gb, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
    ck_fact HS 43%nat (mkAF 2 40 0)
      ltac:(rewrite Gc, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
    clear Gb Gc.
    ck_seat HS (ck_ih_facts 4) CLOB (ss_ih 0 4).
    ck_refresh.
    lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _ |- _ =>
      assert (HEIf : img_env VAL A_LIM Ef)
        by (repeat first [ assumption | apply img_env_havoc_hi; [|cbv; lia] | apply img_env_ewset_hi; [|cbv; lia] ]) end.
    lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _, HJq : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    apply ((ck_ih_0_4 Hoh1) ly S W regs mem md ch r fabric bs G HCTX ltac:(lia) Ef _ _ ltac:(assumption) HSq
    ltac:(assumption) HJq) end. }
  ck_rn.
  ck_bcmp_zero_block0 0 0.
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hcmp & Hfr2).
  jafter_call_keep_hi HS 600%nat regs2 (mrestrict (w_H W) mem2) HP2 [0%nat; 1%nat; 2%nat; 3%nat] HS2.
  match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
  { ck_keep_regions Hfr2. }
  rewrite <- restrict_mkst_fx in HS2.
  clear HS HJ SHOK. rename HS2 into HS. rename HJ2 into HJ.
  ck_refresh. ck_hei. ck_shok.
  remember (bv_unsigned (getr regs2 10)) as vz eqn:Hvz.
  assert (Hv0 : getr regs2 10 = Z_to_bv 64 vz)
  by (rewrite Hvz; rewrite Z_to_bv_bv_unsigned; reflexivity).
  assert (Hvzr : 0 <= vz < 2 ^ 64)
  by (rewrite Hvz; pose proof (bv_unsigned_in_range 64 (getr regs2 10)) as Rq;
  unfold bv_modulus in Rq; change (2 ^ Z.of_N 64) with (2 ^ 64) in Rq; lia).
  ck_a0 604%nat vz Hv0 Ha0v.
  ck_ra.
  ck_rn.
  ck_lift Ha0v Ha0w.
  ck_brt.
  { (* row 0's MAC is zero6: the pair is settled, the walk goes to the latch *)
    ck_drop_br. clear Hcmp.
    ck_rnto 4712.
    ck_seat HS (ck_ih_facts 3) CLOB (ss_lat 0 3).
    lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _, HJq : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    apply (CONT2 Ef _ _ ltac:(assumption) HSq ltac:(assumption) ltac:(assumption) HJq) end. }
  (* row 0's MAC is not zero6, so B5 makes it differ from row 3's *)
  assert (Hnz : Boxreg.bx_mac bs 0 <> Boxreg.zero6).
  { intros Hq. lazymatch goal with Hb : branch_taken _ _ _ = false |- _ =>
    rewrite (ck_br_eq0 _ 604 vz Ha0w ltac:(lia)) in Hb;
    apply Z.eqb_neq in Hb; apply Hb; apply Hcmp; exact Hq end. }
  ck_drop_br. clear Hcmp Ha0v Ha0w Hv0 Hvzr Hvz.
  ck_rn.
  ck_bcmp_rows_block0 0 3 0 168.
  cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hcmp3 & Hfr3).
  jafter_call_keep_hi HS 640%nat regs3 (mrestrict (w_H W) mem3) HP3 [0%nat; 1%nat; 2%nat; 3%nat] HS3.
  match type of HS3 with ?tq -> _ => assert (HRK : tq); [|specialize (HS3 HRK); clear HRK] end.
  { ck_keep_regions Hfr3. }
  rewrite <- restrict_mkst_fx in HS3.
  clear HS HJ SHOK. rename HS3 into HS. rename HJ3 into HJ.
  ck_refresh. ck_hei. ck_shok.
  remember (bv_unsigned (getr regs3 10)) as vw eqn:Hvw.
  assert (Hw0 : getr regs3 10 = Z_to_bv 64 vw)
  by (rewrite Hvw; rewrite Z_to_bv_bv_unsigned; reflexivity).
  assert (Hvwr : 0 <= vw < 2 ^ 64)
  by (rewrite Hvw; pose proof (bv_unsigned_in_range 64 (getr regs3 10)) as Rq;
  unfold bv_modulus in Rq; change (2 ^ Z.of_N 64) with (2 ^ 64) in Rq; lia).
  ck_a0 644%nat vw Hw0 Ha0u.
  ck_ra.
  ck_rn.
  ck_lift Ha0u Ha0t.
  ck_brt.
  { (* equal MACs: B5 refutes the abort at 0x811b0 *)
    exfalso. lazymatch goal with Hb : branch_taken _ _ _ = true |- _ =>
    rewrite (ck_br_eq0 _ 644 vw Ha0t ltac:(lia)) in Hb;
    apply Z.eqb_eq in Hb;
    destruct (HB5 0 3 ltac:(lia) ltac:(lia) ltac:(lia)) as [Hq | Hq];
    [exact (Hnz Hq) | exact (Hq (proj1 Hcmp3 Hb))] end. }
  ck_drop_br. clear Hcmp3.
  ck_rnto 4712.
  ck_seat HS (ck_ih_facts 3) CLOB (ss_lat 0 3).
  lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _, HJq : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  apply (CONT2 Ef _ _ ltac:(assumption) HSq ltac:(assumption) ltac:(assumption) HJq) end. }
(* the two arms of the overlap test of 0x8117c *)
ck_brt.
{ (* base_3 >= base_0 + nch_0: the slices are apart, the walk goes straight to the MAC test *)
  ck_rnto 4684. ck_use_join CONT (ck_ih_facts 3). }
(* base_3 < base_0 + nch_0: the second test of the pair, refuted by B4 *)
assert (Hlt1 : Boxreg.bx_base bs 3 < Boxreg.bx_base bs 0 + Boxreg.bx_nch bs 0).
{ lazymatch goal with Hb : branch_taken _ _ _ = false |- _ =>
  ck_base_eq 34%nat 0 GA; ck_nch_eq 35%nat 0 GB; ck_base_eq 40%nat 3 GC;
  lazymatch type of GA with ew ?Ec _ = _ =>
  rewrite (ck_br_ge_sum Ec 40 34 35 (Boxreg.bx_base bs 3) (Boxreg.bx_base bs 0) (Boxreg.bx_nch bs 0)
  GC GA GB ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in Hb end;
  apply negb_false_iff in Hb; apply Z.ltb_lt in Hb; exact Hb end. }
ck_drop_br.
ck_rn.
assert (Hlt2 : Boxreg.bx_base bs 0 < Boxreg.bx_base bs 3 + Boxreg.bx_nch bs 3 -> False).
{ intros Hq. destruct (HB4 0 3 ltac:(lia) ltac:(lia) ltac:(lia)).
  split; [exact Hq | exact Hlt1]. }
ck_brt.
{ exfalso. lazymatch goal with Hb : branch_taken _ _ _ = true |- _ =>
  ck_base_eq 34%nat 0 GA; ck_base_eq 40%nat 3 GC; ck_nch_eq 41%nat 3 GD;
  lazymatch type of GA with ew ?Ec _ = _ =>
  rewrite (ck_br_lt_sum Ec 34 40 41 (Boxreg.bx_base bs 0) (Boxreg.bx_base bs 3) (Boxreg.bx_nch bs 3)
  GA GC GD ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in Hb end;
  apply Z.ltb_lt in Hb; exact (Hlt2 Hb) end. }
ck_drop_br.
ck_rnto 4684.
ck_use_join CONT (ck_ih_facts 3).
Qed.
Lemma ck_ih_0_2 : ck_oh_prop 1 -> ck_ih_prop 0 2.
Proof.
intros Hoh1.
ck_head_intro.
change (Z.of_nat 2 + 1) with 3 in HNB.
destruct (Boxreg.B3_bounds bs 0 HB2 HB3 ltac:(lia)) as (Hb0 & Hc0 & Hs0).
destruct (Boxreg.B3_bounds bs 2 HB2 HB3 ltac:(lia)) as (Hbj & Hcj & Hsj).
ck_rn.
(* the pair (0, 2): the overlap test's two arms meet at the bcmp of 0x81198 *)
ck_join (mkAC BC_GE (SOff 38 0) (SAlu ALU_ADD (SOff 34 0) (SOff 35 0))) 4684 (ck_ih_facts 2) CONT.
{ ck_clear_state. intros Ex2 msX2 mdX2 HEI HS HAG Usp HJ. ck_shok.
  (* the pair's four paths meet again at the inner latch 0x811b4 *)
  assert (CONT2 : forall (Ex3 : env) (msX3 : machine_state) (mdX3 : Model),
  img_env VAL A_LIM Ex3 ->
  st_ok_pi SEGS VAL Ex3 (ss_lat 0 2) (restrict (w_H W) msX3) ->
  env_agree 44 (Ereg regs (ck_extra bs)) Ex3 ->
  bv_unsigned (ew Ex3 2) = spZ regs ->
  ajournal SEGS B CHECK_STK (spZ regs) [] ly S W mem md [] ly S W (ms_mem msX3) mdX3 0 ->
  SRr SEGS W (mkCfg msX3 mdX3) (tcheck_post regs ly S W mem md r bs)).
  { ck_clear_state. intros Ex3 msX3 mdX3 HEI HS HAG Usp HJ. ck_shok.
    (* the inner count's test 0x811c4 (beqz s7, s7 = n - 3) has both arms *)
    ck_rn. ck_n_eq Gn.
    ck_brt.
    { (* taken: n = 3; the outer latch takes the back edge to row 1 *)
      lazymatch goal with Hb : branch_taken _ _ _ = true |- _ =>
        lazymatch type of Gn with ew ?Ec _ = _ =>
        rewrite (ck_br_eq0_off Ec 33 (-3) (Boxreg.bx_n bs) Gn ltac:(lia) ltac:(lia)) in Hb end;
        apply Z.eqb_eq in Hb; assert (HnJ : Boxreg.bx_n bs = 3) by lia; clear Hb end.
      ck_drop_br.
      ck_fact HS 33%nat (mkAF 3 3 0)
        ltac:(rewrite Gn, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
      ck_fact HS 33%nat (mkAF 2 5 0)
        ltac:(rewrite Gn, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
      clear Gn.
      ck_rnto 4468.
      ck_seat HS (ck_oh_facts 1) CK_OH_CLOB (ss_oh 1).
      ck_refresh.
      lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _ |- _ =>
        assert (HEIf : img_env VAL A_LIM Ef)
          by (repeat first [ assumption | apply img_env_havoc_hi; [|cbv; lia] | apply img_env_ewset_hi; [|cbv; lia] ]) end.
      lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _, HJq : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      apply (Hoh1 ly S W regs mem md ch r fabric bs G HCTX ltac:(lia) Ef _ _ ltac:(assumption) HSq
      ltac:(assumption) HJq) end. }
    (* not taken: n >= 4; the inner loop's head for the pair (0, 3) *)
    lazymatch goal with Hb : branch_taken _ _ _ = false |- _ =>
      lazymatch type of Gn with ew ?Ec _ = _ =>
      rewrite (ck_br_eq0_off Ec 33 (-3) (Boxreg.bx_n bs) Gn ltac:(lia) ltac:(lia)) in Hb end;
      apply Z.eqb_neq in Hb; assert (HNB2 : Z.of_nat 3 + 1 <= Boxreg.bx_n bs) by lia; clear Hb end.
    destruct (Boxreg.B3_bounds bs 3 HB2 HB3 ltac:(lia)) as (Hbn & Hcn & Hsn).
    ck_drop_br.
    ck_fact HS 33%nat (mkAF 4 5 0)
      ltac:(rewrite Gn, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
    clear Gn.
    ck_rnto 4628.
    (* s6 came through the inner latch: put it in the head's form *)
    prreg HS (22%bv : bv 5) R22.
    ck_r_eq G10s. ck_sb_eq G32s.
    lazymatch type of HS with st_ok_pi _ _ ?Ec ?ssq ?msq =>
      let H2 := fresh "HSs" in
      pose proof (st_ok_pi_set_reg Ec ssq msq 22%bv (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff 10 176) (SLit 3))) HS
        ltac:(discriminate)
        ltac:(let Hq := fresh "Hq" in
              pose proof (ck_s6_relatch Ec SB r 120 176 eq_refl G32s G10s ltac:(unfold SB; lia) ltac:(unfold SB; lia)
                ltac:(lia) ltac:(lia) ltac:(unfold ASAN_CEIL in *; lia) ltac:(Z.div_mod_to_equations; lia)) as Hq;
              etransitivity; [exact R22 |]; cbn [sv_denot] in Hq |- *;
              rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Hq |- *; exact Hq)) as H2;
      clear HS; rename H2 into HS; ck_norm HS end.
    clear R22 G10s G32s.
    ck_base_eq 40%nat 3 Gb. ck_nch_eq 41%nat 3 Gc.
    ck_fact HS 40%nat (mkAF 0 38 0)
      ltac:(rewrite Gb, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
    ck_fact HS 41%nat (mkAF 2 40 0)
      ltac:(rewrite Gc, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
    clear Gb Gc.
    ck_seat HS (ck_ih_facts 3) CLOB (ss_ih 0 3).
    ck_refresh.
    lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _ |- _ =>
      assert (HEIf : img_env VAL A_LIM Ef)
        by (repeat first [ assumption | apply img_env_havoc_hi; [|cbv; lia] | apply img_env_ewset_hi; [|cbv; lia] ]) end.
    lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _, HJq : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    apply ((ck_ih_0_3 Hoh1) ly S W regs mem md ch r fabric bs G HCTX ltac:(lia) Ef _ _ ltac:(assumption) HSq
    ltac:(assumption) HJq) end. }
  ck_rn.
  ck_bcmp_zero_block0 0 0.
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hcmp & Hfr2).
  jafter_call_keep_hi HS 600%nat regs2 (mrestrict (w_H W) mem2) HP2 [0%nat; 1%nat; 2%nat; 3%nat] HS2.
  match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
  { ck_keep_regions Hfr2. }
  rewrite <- restrict_mkst_fx in HS2.
  clear HS HJ SHOK. rename HS2 into HS. rename HJ2 into HJ.
  ck_refresh. ck_hei. ck_shok.
  remember (bv_unsigned (getr regs2 10)) as vz eqn:Hvz.
  assert (Hv0 : getr regs2 10 = Z_to_bv 64 vz)
  by (rewrite Hvz; rewrite Z_to_bv_bv_unsigned; reflexivity).
  assert (Hvzr : 0 <= vz < 2 ^ 64)
  by (rewrite Hvz; pose proof (bv_unsigned_in_range 64 (getr regs2 10)) as Rq;
  unfold bv_modulus in Rq; change (2 ^ Z.of_N 64) with (2 ^ 64) in Rq; lia).
  ck_a0 604%nat vz Hv0 Ha0v.
  ck_ra.
  ck_rn.
  ck_lift Ha0v Ha0w.
  ck_brt.
  { (* row 0's MAC is zero6: the pair is settled, the walk goes to the latch *)
    ck_drop_br. clear Hcmp.
    ck_rnto 4712.
    ck_seat HS (ck_ih_facts 2) CLOB (ss_lat 0 2).
    lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _, HJq : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    apply (CONT2 Ef _ _ ltac:(assumption) HSq ltac:(assumption) ltac:(assumption) HJq) end. }
  (* row 0's MAC is not zero6, so B5 makes it differ from row 2's *)
  assert (Hnz : Boxreg.bx_mac bs 0 <> Boxreg.zero6).
  { intros Hq. lazymatch goal with Hb : branch_taken _ _ _ = false |- _ =>
    rewrite (ck_br_eq0 _ 604 vz Ha0w ltac:(lia)) in Hb;
    apply Z.eqb_neq in Hb; apply Hb; apply Hcmp; exact Hq end. }
  ck_drop_br. clear Hcmp Ha0v Ha0w Hv0 Hvzr Hvz.
  ck_rn.
  ck_bcmp_rows_block0 0 2 0 112.
  cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hcmp3 & Hfr3).
  jafter_call_keep_hi HS 640%nat regs3 (mrestrict (w_H W) mem3) HP3 [0%nat; 1%nat; 2%nat; 3%nat] HS3.
  match type of HS3 with ?tq -> _ => assert (HRK : tq); [|specialize (HS3 HRK); clear HRK] end.
  { ck_keep_regions Hfr3. }
  rewrite <- restrict_mkst_fx in HS3.
  clear HS HJ SHOK. rename HS3 into HS. rename HJ3 into HJ.
  ck_refresh. ck_hei. ck_shok.
  remember (bv_unsigned (getr regs3 10)) as vw eqn:Hvw.
  assert (Hw0 : getr regs3 10 = Z_to_bv 64 vw)
  by (rewrite Hvw; rewrite Z_to_bv_bv_unsigned; reflexivity).
  assert (Hvwr : 0 <= vw < 2 ^ 64)
  by (rewrite Hvw; pose proof (bv_unsigned_in_range 64 (getr regs3 10)) as Rq;
  unfold bv_modulus in Rq; change (2 ^ Z.of_N 64) with (2 ^ 64) in Rq; lia).
  ck_a0 644%nat vw Hw0 Ha0u.
  ck_ra.
  ck_rn.
  ck_lift Ha0u Ha0t.
  ck_brt.
  { (* equal MACs: B5 refutes the abort at 0x811b0 *)
    exfalso. lazymatch goal with Hb : branch_taken _ _ _ = true |- _ =>
    rewrite (ck_br_eq0 _ 644 vw Ha0t ltac:(lia)) in Hb;
    apply Z.eqb_eq in Hb;
    destruct (HB5 0 2 ltac:(lia) ltac:(lia) ltac:(lia)) as [Hq | Hq];
    [exact (Hnz Hq) | exact (Hq (proj1 Hcmp3 Hb))] end. }
  ck_drop_br. clear Hcmp3.
  ck_rnto 4712.
  ck_seat HS (ck_ih_facts 2) CLOB (ss_lat 0 2).
  lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _, HJq : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  apply (CONT2 Ef _ _ ltac:(assumption) HSq ltac:(assumption) ltac:(assumption) HJq) end. }
(* the two arms of the overlap test of 0x8117c *)
ck_brt.
{ (* base_2 >= base_0 + nch_0: the slices are apart, the walk goes straight to the MAC test *)
  ck_rnto 4684. ck_use_join CONT (ck_ih_facts 2). }
(* base_2 < base_0 + nch_0: the second test of the pair, refuted by B4 *)
assert (Hlt1 : Boxreg.bx_base bs 2 < Boxreg.bx_base bs 0 + Boxreg.bx_nch bs 0).
{ lazymatch goal with Hb : branch_taken _ _ _ = false |- _ =>
  ck_base_eq 34%nat 0 GA; ck_nch_eq 35%nat 0 GB; ck_base_eq 38%nat 2 GC;
  lazymatch type of GA with ew ?Ec _ = _ =>
  rewrite (ck_br_ge_sum Ec 38 34 35 (Boxreg.bx_base bs 2) (Boxreg.bx_base bs 0) (Boxreg.bx_nch bs 0)
  GC GA GB ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in Hb end;
  apply negb_false_iff in Hb; apply Z.ltb_lt in Hb; exact Hb end. }
ck_drop_br.
ck_rn.
assert (Hlt2 : Boxreg.bx_base bs 0 < Boxreg.bx_base bs 2 + Boxreg.bx_nch bs 2 -> False).
{ intros Hq. destruct (HB4 0 2 ltac:(lia) ltac:(lia) ltac:(lia)).
  split; [exact Hq | exact Hlt1]. }
ck_brt.
{ exfalso. lazymatch goal with Hb : branch_taken _ _ _ = true |- _ =>
  ck_base_eq 34%nat 0 GA; ck_base_eq 38%nat 2 GC; ck_nch_eq 39%nat 2 GD;
  lazymatch type of GA with ew ?Ec _ = _ =>
  rewrite (ck_br_lt_sum Ec 34 38 39 (Boxreg.bx_base bs 0) (Boxreg.bx_base bs 2) (Boxreg.bx_nch bs 2)
  GA GC GD ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in Hb end;
  apply Z.ltb_lt in Hb; exact (Hlt2 Hb) end. }
ck_drop_br.
ck_rnto 4684.
ck_use_join CONT (ck_ih_facts 2).
Qed.
Lemma ck_ih_0_1 : ck_oh_prop 1 -> ck_ih_prop 0 1.
Proof.
intros Hoh1.
ck_head_intro.
change (Z.of_nat 1 + 1) with 2 in HNB.
destruct (Boxreg.B3_bounds bs 0 HB2 HB3 ltac:(lia)) as (Hb0 & Hc0 & Hs0).
destruct (Boxreg.B3_bounds bs 1 HB2 HB3 ltac:(lia)) as (Hbj & Hcj & Hsj).
ck_rn.
(* the pair (0, 1): the overlap test's two arms meet at the bcmp of 0x81198 *)
ck_join (mkAC BC_GE (SOff 36 0) (SAlu ALU_ADD (SOff 34 0) (SOff 35 0))) 4684 (ck_ih_facts 1) CONT.
{ ck_clear_state. intros Ex2 msX2 mdX2 HEI HS HAG Usp HJ. ck_shok.
  (* the pair's four paths meet again at the inner latch 0x811b4 *)
  assert (CONT2 : forall (Ex3 : env) (msX3 : machine_state) (mdX3 : Model),
  img_env VAL A_LIM Ex3 ->
  st_ok_pi SEGS VAL Ex3 (ss_lat 0 1) (restrict (w_H W) msX3) ->
  env_agree 44 (Ereg regs (ck_extra bs)) Ex3 ->
  bv_unsigned (ew Ex3 2) = spZ regs ->
  ajournal SEGS B CHECK_STK (spZ regs) [] ly S W mem md [] ly S W (ms_mem msX3) mdX3 0 ->
  SRr SEGS W (mkCfg msX3 mdX3) (tcheck_post regs ly S W mem md r bs)).
  { ck_clear_state. intros Ex3 msX3 mdX3 HEI HS HAG Usp HJ. ck_shok.
    (* the inner count's test 0x811c4 (beqz s7, s7 = n - 2) has both arms *)
    ck_rn. ck_n_eq Gn.
    ck_brt.
    { (* taken: n = 2; the outer latch takes the back edge to row 1 *)
      lazymatch goal with Hb : branch_taken _ _ _ = true |- _ =>
        lazymatch type of Gn with ew ?Ec _ = _ =>
        rewrite (ck_br_eq0_off Ec 33 (-2) (Boxreg.bx_n bs) Gn ltac:(lia) ltac:(lia)) in Hb end;
        apply Z.eqb_eq in Hb; assert (HnJ : Boxreg.bx_n bs = 2) by lia; clear Hb end.
      ck_drop_br.
      ck_fact HS 33%nat (mkAF 2 2 0)
        ltac:(rewrite Gn, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
      ck_fact HS 33%nat (mkAF 2 5 0)
        ltac:(rewrite Gn, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
      clear Gn.
      ck_rnto 4468.
      ck_seat HS (ck_oh_facts 1) CK_OH_CLOB (ss_oh 1).
      ck_refresh.
      lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _ |- _ =>
        assert (HEIf : img_env VAL A_LIM Ef)
          by (repeat first [ assumption | apply img_env_havoc_hi; [|cbv; lia] | apply img_env_ewset_hi; [|cbv; lia] ]) end.
      lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _, HJq : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      apply (Hoh1 ly S W regs mem md ch r fabric bs G HCTX ltac:(lia) Ef _ _ ltac:(assumption) HSq
      ltac:(assumption) HJq) end. }
    (* not taken: n >= 3; the inner loop's head for the pair (0, 2) *)
    lazymatch goal with Hb : branch_taken _ _ _ = false |- _ =>
      lazymatch type of Gn with ew ?Ec _ = _ =>
      rewrite (ck_br_eq0_off Ec 33 (-2) (Boxreg.bx_n bs) Gn ltac:(lia) ltac:(lia)) in Hb end;
      apply Z.eqb_neq in Hb; assert (HNB2 : Z.of_nat 2 + 1 <= Boxreg.bx_n bs) by lia; clear Hb end.
    destruct (Boxreg.B3_bounds bs 2 HB2 HB3 ltac:(lia)) as (Hbn & Hcn & Hsn).
    ck_drop_br.
    ck_fact HS 33%nat (mkAF 3 5 0)
      ltac:(rewrite Gn, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
    clear Gn.
    ck_rnto 4628.
    (* s6 came through the inner latch: put it in the head's form *)
    prreg HS (22%bv : bv 5) R22.
    ck_r_eq G10s. ck_sb_eq G32s.
    lazymatch type of HS with st_ok_pi _ _ ?Ec ?ssq ?msq =>
      let H2 := fresh "HSs" in
      pose proof (st_ok_pi_set_reg Ec ssq msq 22%bv (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff 10 120) (SLit 3))) HS
        ltac:(discriminate)
        ltac:(let Hq := fresh "Hq" in
              pose proof (ck_s6_relatch Ec SB r 64 120 eq_refl G32s G10s ltac:(unfold SB; lia) ltac:(unfold SB; lia)
                ltac:(lia) ltac:(lia) ltac:(unfold ASAN_CEIL in *; lia) ltac:(Z.div_mod_to_equations; lia)) as Hq;
              etransitivity; [exact R22 |]; cbn [sv_denot] in Hq |- *;
              rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Hq |- *; exact Hq)) as H2;
      clear HS; rename H2 into HS; ck_norm HS end.
    clear R22 G10s G32s.
    ck_base_eq 38%nat 2 Gb. ck_nch_eq 39%nat 2 Gc.
    ck_fact HS 38%nat (mkAF 0 38 0)
      ltac:(rewrite Gb, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
    ck_fact HS 39%nat (mkAF 2 40 0)
      ltac:(rewrite Gc, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia).
    clear Gb Gc.
    ck_seat HS (ck_ih_facts 2) CLOB (ss_ih 0 2).
    ck_refresh.
    lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _ |- _ =>
      assert (HEIf : img_env VAL A_LIM Ef)
        by (repeat first [ assumption | apply img_env_havoc_hi; [|cbv; lia] | apply img_env_ewset_hi; [|cbv; lia] ]) end.
    lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _, HJq : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    apply ((ck_ih_0_2 Hoh1) ly S W regs mem md ch r fabric bs G HCTX ltac:(lia) Ef _ _ ltac:(assumption) HSq
    ltac:(assumption) HJq) end. }
  ck_rn.
  ck_bcmp_zero_block0 0 0.
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hcmp & Hfr2).
  jafter_call_keep_hi HS 600%nat regs2 (mrestrict (w_H W) mem2) HP2 [0%nat; 1%nat; 2%nat; 3%nat] HS2.
  match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
  { ck_keep_regions Hfr2. }
  rewrite <- restrict_mkst_fx in HS2.
  clear HS HJ SHOK. rename HS2 into HS. rename HJ2 into HJ.
  ck_refresh. ck_hei. ck_shok.
  remember (bv_unsigned (getr regs2 10)) as vz eqn:Hvz.
  assert (Hv0 : getr regs2 10 = Z_to_bv 64 vz)
  by (rewrite Hvz; rewrite Z_to_bv_bv_unsigned; reflexivity).
  assert (Hvzr : 0 <= vz < 2 ^ 64)
  by (rewrite Hvz; pose proof (bv_unsigned_in_range 64 (getr regs2 10)) as Rq;
  unfold bv_modulus in Rq; change (2 ^ Z.of_N 64) with (2 ^ 64) in Rq; lia).
  ck_a0 604%nat vz Hv0 Ha0v.
  ck_ra.
  ck_rn.
  ck_lift Ha0v Ha0w.
  ck_brt.
  { (* row 0's MAC is zero6: the pair is settled, the walk goes to the latch *)
    ck_drop_br. clear Hcmp.
    ck_rnto 4712.
    ck_seat HS (ck_ih_facts 1) CLOB (ss_lat 0 1).
    lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _, HJq : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    apply (CONT2 Ef _ _ ltac:(assumption) HSq ltac:(assumption) ltac:(assumption) HJq) end. }
  (* row 0's MAC is not zero6, so B5 makes it differ from row 1's *)
  assert (Hnz : Boxreg.bx_mac bs 0 <> Boxreg.zero6).
  { intros Hq. lazymatch goal with Hb : branch_taken _ _ _ = false |- _ =>
    rewrite (ck_br_eq0 _ 604 vz Ha0w ltac:(lia)) in Hb;
    apply Z.eqb_neq in Hb; apply Hb; apply Hcmp; exact Hq end. }
  ck_drop_br. clear Hcmp Ha0v Ha0w Hv0 Hvzr Hvz.
  ck_rn.
  ck_bcmp_rows_block0 0 1 0 56.
  cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hcmp3 & Hfr3).
  jafter_call_keep_hi HS 640%nat regs3 (mrestrict (w_H W) mem3) HP3 [0%nat; 1%nat; 2%nat; 3%nat] HS3.
  match type of HS3 with ?tq -> _ => assert (HRK : tq); [|specialize (HS3 HRK); clear HRK] end.
  { ck_keep_regions Hfr3. }
  rewrite <- restrict_mkst_fx in HS3.
  clear HS HJ SHOK. rename HS3 into HS. rename HJ3 into HJ.
  ck_refresh. ck_hei. ck_shok.
  remember (bv_unsigned (getr regs3 10)) as vw eqn:Hvw.
  assert (Hw0 : getr regs3 10 = Z_to_bv 64 vw)
  by (rewrite Hvw; rewrite Z_to_bv_bv_unsigned; reflexivity).
  assert (Hvwr : 0 <= vw < 2 ^ 64)
  by (rewrite Hvw; pose proof (bv_unsigned_in_range 64 (getr regs3 10)) as Rq;
  unfold bv_modulus in Rq; change (2 ^ Z.of_N 64) with (2 ^ 64) in Rq; lia).
  ck_a0 644%nat vw Hw0 Ha0u.
  ck_ra.
  ck_rn.
  ck_lift Ha0u Ha0t.
  ck_brt.
  { (* equal MACs: B5 refutes the abort at 0x811b0 *)
    exfalso. lazymatch goal with Hb : branch_taken _ _ _ = true |- _ =>
    rewrite (ck_br_eq0 _ 644 vw Ha0t ltac:(lia)) in Hb;
    apply Z.eqb_eq in Hb;
    destruct (HB5 0 1 ltac:(lia) ltac:(lia) ltac:(lia)) as [Hq | Hq];
    [exact (Hnz Hq) | exact (Hq (proj1 Hcmp3 Hb))] end. }
  ck_drop_br. clear Hcmp3.
  ck_rnto 4712.
  ck_seat HS (ck_ih_facts 1) CLOB (ss_lat 0 1).
  lazymatch goal with HSq : st_ok_pi _ _ ?Ef _ _, HJq : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  apply (CONT2 Ef _ _ ltac:(assumption) HSq ltac:(assumption) ltac:(assumption) HJq) end. }
(* the two arms of the overlap test of 0x8117c *)
ck_brt.
{ (* base_1 >= base_0 + nch_0: the slices are apart, the walk goes straight to the MAC test *)
  ck_rnto 4684. ck_use_join CONT (ck_ih_facts 1). }
(* base_1 < base_0 + nch_0: the second test of the pair, refuted by B4 *)
assert (Hlt1 : Boxreg.bx_base bs 1 < Boxreg.bx_base bs 0 + Boxreg.bx_nch bs 0).
{ lazymatch goal with Hb : branch_taken _ _ _ = false |- _ =>
  ck_base_eq 34%nat 0 GA; ck_nch_eq 35%nat 0 GB; ck_base_eq 36%nat 1 GC;
  lazymatch type of GA with ew ?Ec _ = _ =>
  rewrite (ck_br_ge_sum Ec 36 34 35 (Boxreg.bx_base bs 1) (Boxreg.bx_base bs 0) (Boxreg.bx_nch bs 0)
  GC GA GB ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in Hb end;
  apply negb_false_iff in Hb; apply Z.ltb_lt in Hb; exact Hb end. }
ck_drop_br.
ck_rn.
assert (Hlt2 : Boxreg.bx_base bs 0 < Boxreg.bx_base bs 1 + Boxreg.bx_nch bs 1 -> False).
{ intros Hq. destruct (HB4 0 1 ltac:(lia) ltac:(lia) ltac:(lia)).
  split; [exact Hq | exact Hlt1]. }
ck_brt.
{ exfalso. lazymatch goal with Hb : branch_taken _ _ _ = true |- _ =>
  ck_base_eq 34%nat 0 GA; ck_base_eq 36%nat 1 GC; ck_nch_eq 37%nat 1 GD;
  lazymatch type of GA with ew ?Ec _ = _ =>
  rewrite (ck_br_lt_sum Ec 34 36 37 (Boxreg.bx_base bs 0) (Boxreg.bx_base bs 1) (Boxreg.bx_nch bs 1)
  GA GC GD ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in Hb end;
  apply Z.ltb_lt in Hb; exact (Hlt2 Hb) end. }
ck_drop_br.
ck_rnto 4684.
ck_use_join CONT (ck_ih_facts 1).
Qed.
(* check, the whole function: from the entry to row 0's head (ck_from_oh0), then the rows and the inner
   pairs, each a segment lemma between two loop heads; the chain closes from the last row back to row 0. *)
Theorem pb_check : tcheck_spec.
Proof.
exact (ck_from_oh0 (ck_oh_0 (ck_ih_0_1 (ck_oh_1 (ck_ih_1_2 (ck_oh_2 ck_ih_2_3)))))).
Qed.
End h.
End f.
End d.
