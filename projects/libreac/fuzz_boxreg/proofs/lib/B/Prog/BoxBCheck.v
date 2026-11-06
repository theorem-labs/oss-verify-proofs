(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8q.v:156-158;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbk.v:76-79; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203, 287-290,
   358-363, for libreac/fuzz_identity's ASan build (lib/A). The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8h.v:75-78, 95-98, 104-107. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_family_of.v, with its module paths, module names and numbers changed; 2292 of its 2375 lines of code are new or changed and 755 lines of the source are left out. *)
(* check (fuzz_boxreg.asan-ubsan 0x81034, 185 instructions): the contract of the ASan+UBSan build's code of the
   harness's static void check (const struct reac_boxreg *r, int fabric) (fuzz/fuzz_boxreg.c:115-159).
   The function takes a 144-byte frame on the machine stack (addi sp,sp,-0x90) and checks r for 4-byte alignment
   (UBSan). It loads n = r->n at r + 280 and r->fabric at r + 284, each after the ASan check of its shadow byte, and
   aborts unless 0 <= n <= 5 (bltu, unsigned) and r->fabric = fabric (a1, compared as 64 bits with the sign-extended
   word). Then, for i = 0 .. n - 1, it checks the pointer r + 56 i for overflow, loads nch_i at r + 56 i + 12 and
   base_i at r + 56 i + 8, each after its shadow check, and aborts unless nch_i is even, 2 <= nch_i <= 40,
   nch_i <= fabric, base_i >= 0 and base_i + nch_i <= fabric (the 32-bit sum checked for signed overflow); it calls
   memchr (r + 56 i + 24, 0, 32) through BB___interceptor_trampoline_memchr (0x41468, call at 0x81190) and aborts on
   NULL; then, for j = i + 1 .. n - 1, it checks the row index (j > 5 traps) and the pointer r + 56 j, loads base_j
   and nch_j (shadow checks; base_j + nch_j checked for signed overflow), aborts when the two slices meet, calls bcmp
   (r + 56 i, ZERO, 6) through BB___interceptor_trampoline_bcmp (0x41464, call at 0x81214) and, when that result is
   nonzero, bcmp (r + 56 i, r + 56 j, 6) (call at 0x81228), and aborts when the second result is 0. Every abort is
   __asan_handle_no_return then abort (0x812e0, 0x812e4). It returns void and writes nothing outside its own frame
   and the wrappers' windows below it.
   No abort is reached: the pre-condition carries Pau's check facts, the facts the plain contract
   (lib/Prog/check_c.v check_contract) takes: boxreg_B16 bs over the struct's bytes (B1: 0 <= n <= 5; B2:
   1 <= fabric <= 40; B3: each row's width is even, 2 .. 40 and at most the fabric, and its slice is inside the
   fabric; B4: no two rows meet; B5: a row's MAC is zero6 or differs from each later row's; B6: each row's name field
   holds a NUL) and bx_fabric bs = fabric. Each abort branch is refuted by one of them (n: B1; fabric: the equation;
   width, base and slice: B3; memchr NULL: B6; overlap: B4; MAC: B5 with the ZERO bytes), so the post states a return
   only, as the plain contract does. The plain walk's model lemmas (lib/Prog/CheckFacts.v memchr_name, memcmp_eq)
   give the same steps.
   Stack: the own 144-byte frame and 2 * ESTACK below it: abcmp_realizes asks for 2 * ESTACK of present stack below
   the caller's sp (CONVENTIONS section 4) and memchr's contract (lib/A/Rt/MemchrDef.v amemchr_realizesM, ecall_pre)
   asks for ESTACK, so the deeper is 2 * ESTACK; there is no program callee.
   Read footprint, each byte covered by a premise: the 288-byte registry struct at r, a heap block of the caller
   (In (r, REG_SIZEB) (ablocks ..) and its bytes bs; the code reads r + 280 .. r + 287 and r + 56 i + 8 ..
   r + 56 i + 15 for i < n; bcmp reads the MACs r + 56 i .. r + 56 i + 5; memchr reads the name r + 56 i + 24 ..
   r + 56 i + 24 + k and the rest of the NUL's aligned 8-byte word, inside the field); ZERO, the harness's
   static const uint8_t ZERO[6] (fuzz/fuzz_boxreg.c:56), the listing's object A_OBJ 4 (0x20cc0, auipc / addi at
   0x81204 / 0x81208), a registered global of the read-only image (asan_globals record (0x20cc0, 6)); the shadow
   bytes of the struct (the __asan_report_load4 branches 0x8129c, 0x812f8, 0x81308 .. 0x81314 are refuted by the
   block's shadow in AR); the GOT word of the shadow base (auipc / ld at 0x8107c) and the shadow cells are fixed by
   AR (AR_const_law, lib/Reusable/YG0d.v); the read-only image memchr's contract reads; the wrappers' own reads are
   inside their contracts.
   Image facts across calls: check's caller (LLVMFuzzerTestOneInput) calls check after other calls, and an ajournal
   keeps no shadow byte of the image (lib/Reusable/YCbq.v:358) and keeps an image byte only when it is neither an
   owned static nor an errno byte (:362). So ZERO and the read-only image are stated by facts that hold in every
   state, as in reac_boxreg_declare / reac_boxreg_set_name:
   - memchr's read-only view (lib/A/Rt/MemchrDef.v; absn_rom_kept of lib/B/Rt/SnprintfDefB.v): arodata_okP on the
     read-only segments; arodata_okP is carried by every journal (lib/A/Prog/BoxBase.v arodata_ok_journalP);
   - ZERO's bytes: absn_rom_bytes for zero6 (state-free: read-only image bytes that are no owned static and no errno
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
   arm (abort) is excluded by B6. The UBSan traps all go to the unimp word 0xc0001073 at 0x812dc: the alignment test
   andi r,3 (0x81070), the pointer-overflow tests bltu ~r,56 i (0x81114) and bltu ~r,56 j (0x811b4), the row-index
   test bltu 5,j (0x811b0) and the signed-overflow tests of base_i + nch_i (0x81178) and base_j + nch_j (0x811f4);
   they are refuted by the block law (r is a multiple of 16, at least 4096, and r + 288 is below the allocator's
   ceiling), by n <= 5 (B1) and by B3's bounds. The bcmp entry is the trampoline at 0x41464 (__wrap_bcmp is an alias
   of the same address), stated with abcmp_realizes, not amemcmp_realizes. No f* instruction occurs in the 185
   instructions and the only csr words are the two unimp traps (csrrw zero,cycle,zero at 0x812dc and 0x812e8, an
   illegal-instruction trap that writes no FP state, on refuted paths), so the fixed {fx} is sound. The old walk's
   runtime cells (asan_cells, REAL_MEMCHR, REAL_BCMP, REAL_MEMCMP, GOT_CF, CF + 254/255), its r mod 4 = 0 premise
   and its boxreg-measured CHECK_FRAME = 144 + BCMP_WRAP_K leave the statement: the cells are premises of the
   runtime hypotheses, the alignment follows from the block law.
   Image difference: the asan build (lib/A/Prog/Check.v) has a 160-byte frame, ZERO is its A_OBJ 6, and it has no
   UBSan checks; the result is the same.
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
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBList BoxBPa.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaJournal BoxBase BoxRo.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05.
(* REG_SIZEB, the size of struct reac_boxreg, is BoxBReacBoxregInit's. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBReacBoxregInit.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt Require Import SnprintfDefB.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg.
(* The walk's own Requires; Require cannot go inside the Sections, so they live here, as in lib/A/Prog/Check.v
   (a Theorem Labs lane for a Theorem Labs lane, 2026-10-29 06:35Z). lib/A/Rt/MemchrDef.v is the image-neutral memchr contract,
   the file that replaced the deleted lib/B/Rt/MemchrDef.v at c7e51887551. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require Import MemchrDef ConstsViewDef.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg boxb_listing}.
#[local] Notation SEGS := (@pa_segs _ boxb_listing PI).
#[local] Notation VAL := (@pa_val _ boxb_listing PI).
#[local] Notation BASE := (@pa_val _ boxb_listing PI A_TEXT).
(* The function's address in the image and the stack it needs: its own 144-byte frame and 2 * ESTACK below it for
   the bcmp wrapper (the memchr wrapper needs ESTACK, inside it). *)
Definition AB_checkP : Z := BASE + AF_check.
Definition CHECK_STKB : Z := 144 + 2 * ESTACK.
(* musl memchr's constant words (loads at 0x92504 / 0x9250c): the 32 image bytes of [0x10350, 0x10370) of
   fuzz_boxreg.asan-ubsan (same addresses and bytes as the asan build), read-only .rodata, not owned by the runtime,
   the range lib/A/Rt/MemchrDef.v amemchr_realizesM takes as lo .. hi. *)
Definition MCH_LOB : Z := 0x10350.
Definition MCH_CONSTSB : list Z :=
[128; 128; 128; 128; 128; 128; 128; 128; 219; 52; 182; 215; 130; 222; 27; 67;
 0; 0; 0; 0; 0; 0; 224; 63; 0; 1; 1; 1; 1; 1; 1; 1].
Section h.
Variable B : asyms.
Definition tbcheck_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md (r : Z) (bs : list byte)
  : world SEGS -> config -> Prop :=
apost_base SEGS B CHECK_STKB [] regs ly S W mem md 0
(fun ly' S' W' regs' mem' md' =>
ly' = ly /\ S' = S /\ W' = W /\ Permutation (ablocks B ly' S') (ablocks B ly S) /\
(forall i, 0 <= i < REG_SIZEB ->
  aview SEGS (w_H W') mem' (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0))))).
Definition tbcheck_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (r fabric : Z) (bs : list byte) (G : list (Z * Z)),
afn_pre SEGS B CHECK_STKB ly S W regs mem md ch ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
getr regs 10 = w64 r -> getr regs 11 = w64 fabric ->
(* the registry struct: a heap block holding bs, which passes Pau's checks for this fabric *)
In (r, REG_SIZEB) (ablocks B ly S) ->
(forall i, 0 <= i < REG_SIZEB ->
  aview SEGS (w_H W) mem (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) ->
Boxreg.boxreg_B16 bs -> Boxreg.bx_fabric bs = fabric ->
(* facts of the image and of the runtime's symbols, true in every state *)
img_shadow_vis SEGS B -> globs_marked SEGS B G ->
(* the image's ZERO (A_OBJ 4): six zero bytes of the read-only image, a registered global *)
absn_rom_bytes SEGS B (VAL (A_OBJ 4)) (map (fun b : byte => bv_unsigned b) Boxreg.zero6) -> In (VAL (A_OBJ 4), 6) G ->
IMG_LO + 64 <= VAL (A_OBJ 4) -> VAL (A_OBJ 4) + 6 + 64 <= IMG_HI ->
(* musl memchr's constants (consts_view SEGS MCH_LOB (MCH_LOB + 32) at the call follows, state-free) *)
absn_rom_bytes SEGS B MCH_LOB MCH_CONSTSB ->
SRr SEGS W (cfg_at SEGS AB_checkP regs mem md) (tbcheck_post regs ly S W mem md r bs).
(* the walk layer, loaded through the header's BoxBReacBoxregInit (B.Prog BoxBPaLib YC1g YC1h, A.Prog YC4b), imported
   below the frozen prefix *)
Import OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog.BoxBPaLib OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog.YC1g
  OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog.YC1h OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog.YC4b.
(* ---------------------------------------------------------------- the walk *)
#[local] Notation SIGMA := (@pa_sigma _ boxb_listing PI).
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA BB___interceptor_trampoline_bcmp).
(* The memchr wrapper's contract over musl memchr's constants [MCH_LOB, MCH_LOB + 32) (0x10350 .. 0x10370). *)
Hypothesis AMEMCHR : amemchr_realizesM SEGS B MCH_LOB (MCH_LOB + 32) (SIGMA BB___interceptor_trampoline_memchr).
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_boxb) (PI := PI).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
(* The symbolic state at the first slot: atom 32 is the shadow offset the code loads through the GOT word
   (object 1) from the shadow cell (object 12); atoms 33 and 34 are the 32-bit words n and fabric of the
   registry struct, atoms 35 + 2 i and 36 + 2 i the base and the width of its row i (i < 5), in the order
   of ck_offs. *)
Definition SBC : Z := 0x7fff8000.
Definition CBx : sv := SOff 32 0.
Definition BspanC : Z * Z := (SBC, SBC + 2 ^ 44 - 1).
Definition ckB (bs : list byte) (k : Z) : byte := nth (Z.to_nat k) bs (Z_to_bv 8 0).
(* the unsigned 32-bit word of the struct at offset k; Pau's rd4 is its signed form *)
Definition ckU (bs : list byte) (k : Z) : Z :=
bv_unsigned (ckB bs k) + 256 * bv_unsigned (ckB bs (k + 1)) +
65536 * bv_unsigned (ckB bs (k + 2)) + 16777216 * bv_unsigned (ckB bs (k + 3)).
Definition ck_extra (bs : list byte) : list word :=
[ Z_to_bv 64 SBC; Z_to_bv 64 (ckU bs 280); Z_to_bv 64 (ckU bs 284);
Z_to_bv 64 (ckU bs 8); Z_to_bv 64 (ckU bs 12); Z_to_bv 64 (ckU bs 64); Z_to_bv 64 (ckU bs 68);
Z_to_bv 64 (ckU bs 120); Z_to_bv 64 (ckU bs 124); Z_to_bv 64 (ckU bs 176); Z_to_bv 64 (ckU bs 180);
Z_to_bv 64 (ckU bs 232); Z_to_bv 64 (ckU bs 236) ].
Definition EC (regs : bvmap 5 word) (bs : list byte) : env := Eimg (Ereg regs (ck_extra bs)).
(* row i: base at 56 i + 8 (atom 35 + 2 i), width at 56 i + 12 (atom 36 + 2 i) *)
Definition ck_batom (i : Z) : nat := Z.to_nat (35 + 2 * i).
Definition ck_catom (i : Z) : nat := Z.to_nat (36 + 2 * i).
Definition ck_chunks : list YP09.chunk :=
[ YP09.mkChunk 8 (CVal 4 (SOff 35 0)); YP09.mkChunk 12 (CVal 4 (SOff 36 0));
YP09.mkChunk 64 (CVal 4 (SOff 37 0)); YP09.mkChunk 68 (CVal 4 (SOff 38 0));
YP09.mkChunk 120 (CVal 4 (SOff 39 0)); YP09.mkChunk 124 (CVal 4 (SOff 40 0));
YP09.mkChunk 176 (CVal 4 (SOff 41 0)); YP09.mkChunk 180 (CVal 4 (SOff 42 0));
YP09.mkChunk 232 (CVal 4 (SOff 43 0)); YP09.mkChunk 236 (CVal 4 (SOff 44 0));
YP09.mkChunk 280 (CVal 4 (SOff 33 0)); YP09.mkChunk 284 (CVal 4 (SOff 34 0)) ].
Definition ck_regions : smem :=
[ stack_region 144; got_regionP; bcell_regionP 32;
YP09.mkRegion (Some 10%nat) 0 288 0 0 ck_chunks ].
(* n is pinned to its value N (0 .. 5 by Pau's B1), so the engine decides every loop test; the other field
   atoms are only 32-bit words. *)
Definition ck_facts (N : Z) : facts :=
mkFacts ((2%nat, mkAF (2 ^ 46) (2 ^ 47) 4) :: (10%nat, mkAF 4096 140737479966720 4) :: (32%nat, mkAF SBC SBC 0) ::
(33%nat, mkAF N N 0) :: map (fun j : nat => ((34 + j)%nat, mkAF 0 4294967295 0)) (seq 0 11)) [] [].
Definition ss_ck (N : Z) : sstate := mkSS AF_check sr_atoms ck_regions None (ck_facts N).
Definition ck_SH : list shent := [mkSHE 10 0 288].
Lemma ckB_range : forall bs k, 0 <= bv_unsigned (ckB bs k) < 256.
Proof.
intros bs k. pose proof (bv_unsigned_in_range 8 (ckB bs k)) as R.
change (bv_modulus 8) with 256 in R. exact R.
Qed.
Lemma ckU_range : forall bs k, 0 <= ckU bs k < 2 ^ 32.
Proof.
intros bs k. unfold ckU.
pose proof (ckB_range bs k). pose proof (ckB_range bs (k + 1)).
pose proof (ckB_range bs (k + 2)). pose proof (ckB_range bs (k + 3)). lia.
Qed.
Lemma nth_skipn_b : forall (l : list byte) (n j : nat) d, nth j (skipn n l) d = nth (n + j) l d.
Proof.
intros l n. revert l. induction n as [|n IH]; intros l j d; [reflexivity|].
destruct l as [|x l]; cbn [skipn nth Nat.add]; [destruct j; reflexivity|]. apply IH.
Qed.
Lemma nth_firstn_b : forall (l : list byte) (n j : nat) d, (j < n)%nat -> nth j (firstn n l) d = nth j l d.
Proof.
intros l n. revert l. induction n as [|n IH]; intros l j d Hj; [lia|].
destruct l as [|x l]; cbn [firstn nth]; [destruct j; reflexivity|].
destruct j as [|j]; [reflexivity|]. apply IH. lia.
Qed.
Lemma bsub_nth_b : forall bs k n (j : nat), 0 <= k -> Z.of_nat j < n -> k + n <= Z.of_nat (length bs) ->
nth j (Boxreg.bsub bs k n) (Z_to_bv 8 0) = ckB bs (k + Z.of_nat j).
Proof.
intros bs k n j Hk Hj Hl. unfold Boxreg.bsub, ckB.
rewrite nth_firstn_b by lia. rewrite nth_skipn_b. f_equal. lia.
Qed.
(* Pau's signed field value is the signed form of the engine's word. *)
Lemma ckU_rd4 : forall bs k, 0 <= k -> k + 4 <= Z.of_nat (length bs) ->
Boxreg.rd4 bs k = bv_swrap 32 (ckU bs k).
Proof.
intros bs k Hk Hl. unfold Boxreg.rd4. f_equal.
assert (HL : length (Boxreg.bsub bs k 4) = 4%nat) by (apply Boxreg.bsub_length; lia).
assert (N0 : nth 0%nat (Boxreg.bsub bs k 4) (Z_to_bv 8 0) = ckB bs k)
  by (rewrite (bsub_nth_b bs k 4 0%nat Hk ltac:(cbn; lia) Hl); f_equal; lia).
assert (N1 : nth 1%nat (Boxreg.bsub bs k 4) (Z_to_bv 8 0) = ckB bs (k + 1))
  by (rewrite (bsub_nth_b bs k 4 1%nat Hk ltac:(cbn; lia) Hl); f_equal; lia).
assert (N2 : nth 2%nat (Boxreg.bsub bs k 4) (Z_to_bv 8 0) = ckB bs (k + 2))
  by (rewrite (bsub_nth_b bs k 4 2%nat Hk ltac:(cbn; lia) Hl); f_equal; lia).
assert (N3 : nth 3%nat (Boxreg.bsub bs k 4) (Z_to_bv 8 0) = ckB bs (k + 3))
  by (rewrite (bsub_nth_b bs k 4 3%nat Hk ltac:(cbn; lia) Hl); f_equal; lia).
destruct (Boxreg.bsub bs k 4) as [|x0 [|x1 [|x2 [|x3 [|x4 l]]]]]; cbn [length] in HL; try discriminate.
cbn [nth] in N0, N1, N2, N3.
rewrite OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib.Bytes.bytes_le_to_Z_le_val.
cbn [map OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib.Bytes.le_val].
rewrite N0, N1, N2, N3. unfold ckU. lia.
Qed.
Lemma ck_byte0 : forall a b c d, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= c < 256 -> 0 <= d < 256 ->
(a + 256 * b + 65536 * c + 16777216 * d) mod 256 = a.
Proof. intros a b c d Ha Hb Hc Hd. Z.div_mod_to_equations. lia. Qed.
Lemma ck_byte1 : forall a b c d, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= c < 256 -> 0 <= d < 256 ->
((a + 256 * b + 65536 * c + 16777216 * d) / 256) mod 256 = b.
Proof. intros a b c d Ha Hb Hc Hd. Z.div_mod_to_equations. lia. Qed.
Lemma ck_byte2 : forall a b c d, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= c < 256 -> 0 <= d < 256 ->
((a + 256 * b + 65536 * c + 16777216 * d) / 65536) mod 256 = c.
Proof. intros a b c d Ha Hb Hc Hd. Z.div_mod_to_equations. lia. Qed.
Lemma ck_byte3 : forall a b c d, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= c < 256 -> 0 <= d < 256 ->
((a + 256 * b + 65536 * c + 16777216 * d) / 16777216) mod 256 = d.
Proof. intros a b c d Ha Hb Hc Hd. Z.div_mod_to_equations. lia. Qed.
Lemma ck_le_byte : forall bs k t, 0 <= t < 4 ->
Z_to_bv 8 (YO0f.le_byte (ckU bs k) 4 (Z.to_nat t)) = ckB bs (k + t).
Proof.
intros bs k t Ht. apply bv_eq. rewrite Z_to_bv_unsigned.
unfold YO0f.le_byte, bv_wrap. change (bv_modulus 8) with 256.
pose proof (ckU_range bs k) as HR.
pose proof (ckB_range bs k) as R0. pose proof (ckB_range bs (k + 1)) as R1.
pose proof (ckB_range bs (k + 2)) as R2. pose proof (ckB_range bs (k + 3)) as R3.
change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32).
rewrite (Z.mod_small (ckU bs k) (2 ^ 32)) by lia.
unfold ckU in *.
assert (Ht0 : t = 0 \/ t = 1 \/ t = 2 \/ t = 3) by lia.
destruct Ht0 as [-> | [-> | [-> | ->]]].
- change (Z.to_nat 0) with 0%nat. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
  rewrite Z.mod_mod by lia. rewrite Z.add_0_r. apply ck_byte0; assumption.
- change (Z.to_nat 1) with 1%nat. change (8 * Z.of_nat 1) with 8.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
  rewrite Z.mod_mod by lia. apply ck_byte1; assumption.
- change (Z.to_nat 2) with 2%nat. change (8 * Z.of_nat 2) with 16.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 16) with 65536.
  rewrite Z.mod_mod by lia. apply ck_byte2; assumption.
- change (Z.to_nat 3) with 3%nat. change (8 * Z.of_nat 3) with 24.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 24) with 16777216.
  rewrite Z.mod_mod by lia. apply ck_byte3; assumption.
Qed.
(* a field of the struct, as the engine reads it: the 4 bytes of the block at r + k *)
Lemma ck_val4 : forall (W : world SEGS) mem r bs k,
0 <= k -> k + 4 <= REG_SIZEB ->
(forall i, 0 <= i < REG_SIZEB ->
  aview SEGS (w_H W) mem (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) ->
val_mem SEGS (mrestrict (w_H W) mem) (r + k) 4 (ckU bs k).
Proof.
intros W mem r bs k Hk Hk4 HV.
assert (HB : forall t, 0 <= t < 4 -> mbyte SEGS (mrestrict (w_H W) mem) (r + k + t) = Some (ckB bs (k + t))).
{ intros t Ht. pose proof (HV (k + t) ltac:(lia)) as H.
  unfold aview in H. replace (r + (k + t)) with (r + k + t) in H by lia.
  destruct (mbyte SEGS (mrestrict (w_H W) mem) (r + k + t)) as [b|] eqn:Hb; cbn [option_map] in H; [|discriminate].
  injection H as H. f_equal. apply bv_eq. exact H. }
intros j Hj.
assert (Hgen : forall t, 0 <= t < 4 ->
  mbyte SEGS (mrestrict (w_H W) mem) (r + k + t) = Some (Z_to_bv 8 (YO0f.le_byte (ckU bs k) 4 (Z.to_nat t)))).
{ intros t Ht. rewrite (HB t Ht). f_equal. symmetry. exact (ck_le_byte bs k t Ht). }
assert (Hj4 : (j = 0 \/ j = 1 \/ j = 2 \/ j = 3)%nat) by lia.
destruct Hj4 as [-> | [-> | [-> | ->]]];
[ exact (Hgen 0 ltac:(lia)) | exact (Hgen 1 ltac:(lia))
| exact (Hgen 2 ltac:(lia)) | exact (Hgen 3 ltac:(lia)) ].
Qed.
(* The entry state: the machine at the first slot of check, with the registry block's two header words and the
   base / width of each of the five rows as atoms. *)
Lemma ck_entry : forall ly S W (regs : bvmap 5 word) mem md ch (r N : Z) (bs : list byte),
afn_pre SEGS B CHECK_STKB ly S W regs mem md ch ->
getr regs 10 = w64 r -> In (r, REG_SIZEB) (ablocks B ly S) -> length bs = 288%nat ->
(forall i, 0 <= i < REG_SIZEB ->
  aview SEGS (w_H W) mem (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) ->
ckU bs 280 = N -> 0 <= N <= 5 ->
st_ok_pi SEGS VAL (EC regs bs) (ss_ck N) (restrict (w_H W) (mkst regs (Z_to_bv 64 AB_checkP) mem (seg_rom SEGS)))
/\ sh_ok SEGS CBx ck_SH (EC regs bs) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md ch r N bs HPRE H10 Hin HL HV HNv HNr.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : CHECK_STKB = 8336) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md r REG_SIZEB HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & _ & _).
change (req_size REG_SIZEB) with 288 in *.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
rewrite restrict_mkst_fx.
set (E := EC regs bs).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ck_extra bs)) n)
  by (intros n Hn; subst E; unfold EC; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 r)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (EX : forall j, (j < 13)%nat -> ew E (32 + j) = nth j (ck_extra bs) (Z_to_bv 64 0))
  by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (E32 : ew E 32 = Z_to_bv 64 SBC) by (exact (EX 0%nat ltac:(lia))).
assert (E33 : ew E 33 = Z_to_bv 64 (ckU bs 280)) by (exact (EX 1%nat ltac:(lia))).
assert (E34 : ew E 34 = Z_to_bv 64 (ckU bs 284)) by (exact (EX 2%nat ltac:(lia))).
assert (E35 : ew E 35 = Z_to_bv 64 (ckU bs 8)) by (exact (EX 3%nat ltac:(lia))).
assert (E36 : ew E 36 = Z_to_bv 64 (ckU bs 12)) by (exact (EX 4%nat ltac:(lia))).
assert (E37 : ew E 37 = Z_to_bv 64 (ckU bs 64)) by (exact (EX 5%nat ltac:(lia))).
assert (E38 : ew E 38 = Z_to_bv 64 (ckU bs 68)) by (exact (EX 6%nat ltac:(lia))).
assert (E39 : ew E 39 = Z_to_bv 64 (ckU bs 120)) by (exact (EX 7%nat ltac:(lia))).
assert (E40 : ew E 40 = Z_to_bv 64 (ckU bs 124)) by (exact (EX 8%nat ltac:(lia))).
assert (E41 : ew E 41 = Z_to_bv 64 (ckU bs 176)) by (exact (EX 9%nat ltac:(lia))).
assert (E42 : ew E 42 = Z_to_bv 64 (ckU bs 180)) by (exact (EX 10%nat ltac:(lia))).
assert (E43 : ew E 43 = Z_to_bv 64 (ckU bs 232)) by (exact (EX 11%nat ltac:(lia))).
assert (E44 : ew E 44 = Z_to_bv 64 (ckU bs 236)) by (exact (EX 12%nat ltac:(lia))).
assert (Egot : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)))
  by (subst E; unfold EC; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Ecell : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (subst E; unfold EC; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_ck, AB_checkP. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold ck_regions, stack_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite Ecell, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Ecell) by (pose proof (pa_val_range (A_OBJ 12)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 CBx SBC);
      [cbn [sv_denot CBx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SBC; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    * rewrite (VB 10%nat r E10) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      unfold ck_chunks.
      repeat apply Forall_cons; try apply Forall_nil;
      lazymatch goal with
      | |- YP09.chunk_ok _ _ _ _ {| YP09.c_off := ?off; YP09.c_val := CVal 4 (SOff ?a 0) |} =>
        apply (chunk_ok_val SEGS E _ r off 4 (SOff a 0) (ckU bs off));
        [ cbn [sv_denot];
          lazymatch goal with
          | H : ew E a = _ |- _ => rewrite H
          end;
          rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | pose proof (ckU_range bs off); change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia
        | zside
        | apply (ck_val4 W mem r bs off); [lia | unfold REG_SIZEB; lia | exact HV] ]
      end.
  + apply pairwise_disjoint_of_extents.
    unfold ck_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
    rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Ecell) by (pose proof (pa_val_range (A_OBJ 12)); lia).
    rewrite (VB 10%nat r E10) by lia.
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    pose proof (blk_off_imgP B ly S W mem md r REG_SIZEB HAR Hin) as Hbimg.
    change (req_size REG_SIZEB) with 288 in Hbimg.
    revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgcD HgotR Hr4096 Hrceil Hbimg. clear. intros.
    repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [ck_facts f_atoms atoms_ok map seq app Nat.add].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Usp; change (2 ^ 4) with 16;
            revert Hslo Hshi H47 Hceil C1 WS Hstk0 Hal16; clear; intros; repeat split; lia|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E10, unsigned_lit_small by lia;
            change (2 ^ 4) with 16; revert Hr16 Hr4096 Hrceil C1; clear; intros; repeat split; lia|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E32, unsigned_lit_small by (unfold SBC; lia);
            rewrite Z.pow_0_r, Z.mod_1_r; unfold SBC; lia|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E33, HNv, unsigned_lit_small by lia;
            rewrite Z.pow_0_r, Z.mod_1_r; lia|].
    repeat lazymatch goal with
    | |- afact_ok E ?n (mkAF 0 4294967295 0) /\ _ =>
      split;
      [ unfold afact_ok; cbn [af_lo af_hi af_al2];
        lazymatch goal with
        | H : ew E n = Z_to_bv 64 (ckU bs ?k) |- _ =>
          pose proof (ckU_range bs k) as HRk;
          rewrite H, unsigned_lit_small by lia;
          rewrite Z.pow_0_r, Z.mod_1_r; lia
        end |]
    end.
    exact I.
- unfold sh_ok, ck_SH. constructor; [|constructor].
  apply (shent_ok_of_block SEGS B LAWS ly S W mem md E CBx 10 r REG_SIZEB 0 288 HAR Hin).
  + unfold CBx. rewrite (U_atom E 32 SBC E32) by (unfold SBC; lia). reflexivity.
  + apply (U_atom E 10 r E10). lia.
  + lia.
  + change (req_size REG_SIZEB) with 288. lia.
Qed.
(* The value of a struct field as the engine computes it: a 4-byte signed load of the field's atom. *)
Lemma ck_U_sext : forall (E : env) bs a k, ew E a = Z_to_bv 64 (ckU bs k) ->
0 <= k -> k + 4 <= Z.of_nat (length bs) -> 0 <= Boxreg.rd4 bs k ->
U E (SExt true 32 (SOff a 0)) = Boxreg.rd4 bs k.
Proof.
intros E bs a k Ha Hk Hl Hpos. pose proof (ckU_range bs k) as HR.
rewrite U_SExt. rewrite (U_atom E a (ckU bs k) Ha ltac:(lia)).
change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small (ckU bs k) (2 ^ 32)) by lia.
rewrite <- (ckU_rd4 bs k Hk Hl).
pose proof (Boxreg.rd4_range bs k) as HRR.
apply zcanon_id. unfold M64. lia.
Qed.
(* The memchr wrapper at a call slot, in the journal form of lib/Reusable/YCbq.v's aj_memcmp_at (:2019), for the
   general contract of lib/B/Rt/MemchrDef.v (amemchr_realizesM): the wrapper writes only its own stack window,
   so the journal survives it. *)
Lemma aj_memchr_at : forall lo hi pc, amemchr_realizesM SEGS B lo hi pc ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x c n (o : Z) raw,
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 c -> getr regsT 12 = w64 n ->
0 <= c < 256 -> 0 <= n < 2 ^ 32 -> 0 < x -> x + n <= 2 ^ 63 ->
src_ok SEGS W regsT memT x n -> amem_range x n ->
range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF x n ->
(0 < n -> shadow_hull_vis (aview SEGS (w_H W) memT) x n) ->
consts_view SEGS lo hi W memT ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\
(exists kk, first_byte SEGS W memT x n c kk /\
   getr regs2 10 = (if kk <? n then w64 (x + kk) else w64 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - ESTACK <= a < sp0 + o) ->
 aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros lo hi pc AM W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x c n o raw
HJ Ha0 Ha1 Ha2 Hc Hn Hx0 Hxn Hsrc Hmr Hrad Hhull Hcv Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw.
pose proof (pa_segs_low) as Hsegs.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (HPRE : ecall_pre SEGS B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o);
  try eassumption. rewrite Hra. exact Hraw. }
eapply SRr_mono.
{ exact (AM lyc Sc W regsT memT mdc x c n HPRE Ha0 Ha1 Ha2 Hc Hn Hx0 Hxn Hsrc Hmr Hrad Hhull Hcv). }
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
(* A field value in the model's form, from the atom equation of the entry env. *)
Lemma ck_Ufield : forall (E : env) bs a k, ew E a = Z_to_bv 64 (ckU bs k) -> length bs = 288%nat ->
0 <= k -> k + 4 <= 288 -> 0 <= Boxreg.rd4 bs k -> U E (SExt true 32 (SOff a 0)) = Boxreg.rd4 bs k.
Proof. intros E bs a k Ha HL Hk Hk4 Hpos. apply (ck_U_sext E bs a k Ha Hk ltac:(rewrite HL; lia) Hpos). Qed.
Lemma ck_swrap_small : forall u v, 0 <= u < 2 ^ 32 -> 0 <= v < 2 ^ 31 -> bv_swrap 32 u = v -> u = v.
Proof.
intros u v Hu Hv H.
destruct (Z.lt_ge_cases u (2 ^ 31)) as [Hlt | Hge].
- rewrite (swrap32_id u ltac:(lia)) in H. exact H.
- rewrite (bv_swrap_hi 32 u ltac:(discriminate)
    ltac:(change (bv_half_modulus 32) with (2 ^ 31); lia)
    ltac:(change (bv_modulus 32) with (2 ^ 32); lia)) in H.
  change (bv_modulus 32) with (2 ^ 32) in H. lia.
Qed.
(* The registry block's bytes in any state of the walk: the journal keeps every byte of a live block outside the
   footprint, and check's footprint is empty. *)
Lemma ck_bytes_now : forall STK sp0 ly S (W : world SEGS) mem md mem' md' k r bs,
ajournal SEGS B STK sp0 [] ly S W mem md [] ly S W mem' md' k ->
In (r, REG_SIZEB) (ablocks B ly S) ->
(forall i, 0 <= i < REG_SIZEB ->
  aview SEGS (w_H W) mem (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) ->
forall i, 0 <= i < REG_SIZEB ->
  aview SEGS (w_H W) mem' (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0))).
Proof.
intros STK sp0 ly S W mem md mem' md' k r bs HJ Hin HV i Hi.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HBK & _).
rewrite (HBK r REG_SIZEB i Hin Hin ltac:(change (req_size REG_SIZEB) with 288; unfold REG_SIZEB in *; lia)
  (inFP_nil (r + i))).
apply HV. exact Hi.
Qed.
Lemma in_rom_img : forall a, in_rom SEGS a -> in_img SEGS a.
Proof. intros a (sg & Hin & _ & Hr). exists sg. split; [exact Hin | exact Hr]. Qed.
(* memchr's constants in any state of the walk: the journal keeps image bytes that are no owned static and no
   errno byte, and the spec's arodata_okP reads them as the image's bytes. *)
Lemma ck_consts : forall STK sp0 ly S (W : world SEGS) mem md ly' S' mem' md' k,
ajournal SEGS B STK sp0 [] ly S W mem md [] ly' S' W mem' md' k ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
absn_rom_bytes SEGS B MCH_LOB MCH_CONSTSB ->
consts_view SEGS MCH_LOB (MCH_LOB + 32) W mem'.
Proof.
intros STK sp0 ly S W mem md ly' S' mem' md' k HJ HRO HMC a Ha.
destruct (HMC (a - MCH_LOB) ltac:(cbn [length MCH_CONSTSB]; lia)) as (Hrom & Hno & Her & _).
replace (MCH_LOB + (a - MCH_LOB)) with a in Hrom, Hno, Her by lia.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HIMG & _).
rewrite (HIMG a (in_rom_img a Hrom) Hno Her (fp_spares_closed [] a sink_closed_nil)).
apply HRO; [left; exact Hrom | exact Hno | exact Her].
Qed.
(* Pau's B6 for row i: the first NUL that memchr finds in the 32-byte name field lies inside it. *)
Lemma ck_first_nul : forall (W : world SEGS) mem r bs i kk,
length bs = 288%nat -> 0 <= i -> 56 * i + 24 + 32 <= 288 ->
(forall t, 0 <= t < REG_SIZEB ->
  aview SEGS (w_H W) mem (r + t) = Some (bv_unsigned (nth (Z.to_nat t) bs (Z_to_bv 8 0)))) ->
In (Z_to_bv 8 0) (Boxreg.bx_name bs i) ->
first_byte SEGS W mem (r + 56 * i + 24) 32 0 kk -> kk < 32.
Proof.
intros W mem r bs i kk HL Hi Hi2 HV HIn (Hk & Hbef & _).
destruct (Z.lt_ge_cases kk 32) as [Hlt | Hge]; [exact Hlt | exfalso].
apply (In_nth _ _ (Z_to_bv 8 0)) in HIn as (t & Ht & Hnth).
unfold Boxreg.bx_name in Ht, Hnth.
rewrite Boxreg.bsub_length in Ht by (try rewrite HL; lia).
rewrite (bsub_nth_b bs (56 * i + 24) 32 t ltac:(lia) ltac:(lia) ltac:(rewrite HL; lia)) in Hnth.
destruct (Hbef (Z.of_nat t) ltac:(lia)) as (b & Hb & Hbne).
replace (r + 56 * i + 24 + Z.of_nat t) with (r + (56 * i + 24 + Z.of_nat t)) in Hb by lia.
rewrite (HV (56 * i + 24 + Z.of_nat t) ltac:(unfold REG_SIZEB; lia)) in Hb.
injection Hb as Hb. apply Hbne. rewrite <- Hb.
unfold ckB in Hnth. rewrite Hnth. reflexivity.
Qed.
(* the atom equation of the current env: see through the engine's token sets and the havocs of the calls *)
Ltac ckpeel := repeat (first [ rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia ]).
Ltac ckatom := ckpeel; assumption.
(* a register of the state as the engine's symbolic value, without the bitvector normal form *)
Ltac ckregraw HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
  cbn [ms_regs restrict mkst] in Hr
end.
Lemma ck_reg_of_U : forall (E : env) (w : word) (s : sv) (v : Z), w = sv_denot E s -> U E s = v -> w = w64 v.
Proof. intros E w s v -> <-. unfold w64, U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
(* the product of a register and a literal (the inner loop's bound n * 56) *)
Lemma ck_U_mul_lit : forall (E : env) a v c, ew E a = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 -> 0 <= c < 2 ^ 32 ->
U E (SMd M_MUL (SOff a 0) (SLit c)) = v * c.
Proof.
intros E a v c Ha Hv Hc. rewrite U_SMd. cbn [zmd_raw]. rewrite U_SLit, (U_atom E a v Ha ltac:(lia)).
rewrite (zcanon_id c) by (unfold M64; lia). apply zcanon_id. unfold M64. nia.
Qed.
Lemma ck_mod_neg : forall x, - 18446744073709551616 <= x < 0 ->
x mod 18446744073709551616 = x + 18446744073709551616.
Proof.
intros x Hx. rewrite <- (Z.mod_small (x + 18446744073709551616) 18446744073709551616) by lia.
rewrite <- Zplus_mod_idemp_r, Z_mod_same_full, Z.add_0_r. reflexivity.
Qed.
Lemma ck_ag_ewset : forall (E E' : env) n v, (32 <= n)%nat -> env_agree 32 E E' -> env_agree 32 E (ewset E' n v).
Proof.
intros E E' n v Hn (HA & HD). split; [|exact HD].
intros m Hm. rewrite ew_ewset_other by lia. apply HA. exact Hm.
Qed.
(* the walk's env is the entry env under the engine's token sets and the havocs of the calls *)
Ltac ckagree HAE := repeat first
[ exact HAE | apply env_agree_havoc_ge; [lia | ] | apply ck_ag_ewset; [lia | ] ].
(* a register that holds a small non-negative value, sign-extended from its low 32 bits *)
Lemma ck_U_sext_at : forall (E : env) a v, ew E a = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 ->
U E (SExt true 32 (SOff a 0)) = v.
Proof.
intros E a v Ha Hv. rewrite U_SExt, (U_atom E a v Ha ltac:(lia)).
change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small v (2 ^ 32)) by lia.
rewrite (swrap32_id v ltac:(lia)). apply zcanon_id. unfold M64. lia.
Qed.
(* sext.w rd, rs is addiw rd, rs, 0 *)
Lemma ck_U_aluw_at0 : forall (E : env) a v, ew E a = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 ->
U E (SAluw ALU_ADD (SOff a 0) (SLit 0)) = v.
Proof.
intros E a v Ha Hv. rewrite U_of_S, S_SAluw. cbn [zalu_raw].
rewrite (U_atom E a v Ha ltac:(lia)), U_SLit.
change (zcanon 0) with 0. rewrite Z.mod_0_l by lia. rewrite Z.add_0_r.
rewrite (Z.mod_small v (2 ^ 32)) by lia. rewrite (swrap32_id v ltac:(lia)).
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia.
Qed.
Lemma branch_lt_S : forall (E : env) a b,
branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (Sg E a <? Sg E b).
Proof. intros. reflexivity. Qed.
Lemma branch_ge_S : forall (E : env) a b,
branch_taken BC_GE (sv_denot E a) (sv_denot E b) = negb (Sg E a <? Sg E b).
Proof. intros. reflexivity. Qed.
(* the 32-bit add of a field and a literal, as the engine writes it (addiw) *)
Lemma ck_U_aluw_field : forall (E : env) bs a k c,
ew E a = Z_to_bv 64 (ckU bs k) -> length bs = 288%nat -> 0 <= k -> k + 4 <= 288 ->
0 <= Boxreg.rd4 bs k < 2 ^ 31 -> - 2 ^ 31 <= Boxreg.rd4 bs k + c < 2 ^ 31 -> - 2 ^ 31 <= c <= 0 ->
U E (SAluw ALU_ADD (SExt true 32 (SOff a 0)) (SLit c)) =
(Boxreg.rd4 bs k + c) mod 18446744073709551616.
Proof.
intros E bs a k c Ha HL Hk Hk4 Hv Hsum Hc.
rewrite U_of_S, S_SAluw. cbn [zalu_raw].
rewrite (ck_Ufield E bs a k Ha HL Hk Hk4 ltac:(lia)), U_SLit.
assert (HS32 : bv_swrap 32 (Boxreg.rd4 bs k mod 2 ^ 32 + zcanon c mod 2 ^ 32) = Boxreg.rd4 bs k + c).
{ transitivity (bv_swrap 32 (Boxreg.rd4 bs k + c)).
  - apply swrap32_congr. cbv [zcanon M64 two32]. Z.div_mod_to_equations. lia.
  - apply swrap32_id. lia. }
rewrite HS32. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616. reflexivity.
Qed.
(* an even field has a zero low bit (the andi of the width check) *)
Lemma ck_land1 : forall x, 0 <= x -> Z.even x = true -> Z.land x 1 = 0.
Proof.
intros x Hx He. change 1 with (Z.ones 1). rewrite Z.land_ones by lia.
change (2 ^ 1) with 2. rewrite Zeven_mod in He. apply Z.eqb_eq in He. exact He.
Qed.
(* the 64-bit and the 32-bit sums of two fields (the signed-overflow test of base + width) *)
Lemma ck_U_alu_add2 : forall (E : env) x y v1 v2, U E x = v1 -> U E y = v2 -> 0 <= v1 + v2 < 2 ^ 64 ->
U E (SAlu ALU_ADD x y) = v1 + v2.
Proof.
intros E x y v1 v2 H1 H2 Hr. rewrite U_SAlu. cbn [zalu_raw]. rewrite H1, H2.
apply zcanon_id. unfold M64. lia.
Qed.
Lemma ck_U_aluw_add2 : forall (E : env) x y v1 v2, U E x = v1 -> U E y = v2 ->
0 <= v1 < 2 ^ 31 -> 0 <= v2 < 2 ^ 31 -> v1 + v2 < 2 ^ 31 ->
U E (SAluw ALU_ADD x y) = v1 + v2.
Proof.
intros E x y v1 v2 H1 H2 R1 R2 R3. rewrite U_of_S, S_SAluw. cbn [zalu_raw]. rewrite H1, H2.
rewrite (Z.mod_small v1 (2 ^ 32)) by lia. rewrite (Z.mod_small v2 (2 ^ 32)) by lia.
rewrite (swrap32_id (v1 + v2)) by lia.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia.
Qed.
(* a branch hypothesis as a fact on Pau's model values *)
Ltac ck_norm bs HL :=
repeat match goal with
| Hc : branch_taken BC_EQ _ _ = _ |- _ => rewrite branch_eq_U in Hc
| Hc : branch_taken BC_NE _ _ = _ |- _ => rewrite branch_ne_U in Hc
| Hc : branch_taken BC_LTU _ _ = _ |- _ => rewrite branch_ltu_U in Hc
| Hc : branch_taken BC_GEU _ _ = _ |- _ => rewrite branch_geu_U in Hc
| Hc : branch_taken BC_LT _ _ = _ |- _ => rewrite branch_lt_S in Hc
| Hc : branch_taken BC_GE _ _ = _ |- _ => rewrite branch_ge_S in Hc
end;
repeat match goal with
| Hc : context [Sg ?Ew ?e] |- _ => rewrite (S_of_U Ew e) in Hc
end;
repeat match goal with
| Hc : context [U ?Ew (SLit ?c)] |- _ => rewrite (U_lit Ew c ltac:(lia)) in Hc
| Hc : context [U ?Ew (SAlu ALU_AND ?e (SLit ?m))] |- _ =>
  rewrite (U_and_lit Ew e m ltac:(lia)) in Hc
| Hc : context [U ?Ew (SMd M_MUL (SOff ?a 0) (SLit ?c))] |- _ =>
  match goal with
  | Hk : ew _ a = Z_to_bv 64 (ckU bs ?k) |- _ =>
    pose proof (ckU_range bs k);
    rewrite (ck_U_mul_lit Ew a (ckU bs k) c ltac:(ckatom) ltac:(lia) ltac:(lia)) in Hc
  end
| Hc : context [U ?Ew (SAlu ALU_XOR (SOff ?a 0) (SLit (-1)))] |- _ =>
  match goal with
  | Hk : ew _ a = Z_to_bv 64 ?v |- _ => rewrite (U_not Ew a v ltac:(ckatom) ltac:(lia)) in Hc
  end
| Hc : context [U ?Ew (SAluw ALU_ADD (SExt true 32 (SOff ?a 0)) (SLit ?c))] |- _ =>
  match goal with
  | Hk : ew _ a = Z_to_bv 64 (ckU bs ?k) |- _ =>
    rewrite (ck_U_aluw_field Ew bs a k c ltac:(ckatom) HL ltac:(lia) ltac:(lia)
               ltac:(lia) ltac:(lia) ltac:(lia)) in Hc
  end
| Hc : context [U ?Ew (SAluw ALU_ADD (SExt true 32 (SOff ?a1 0)) (SExt true 32 (SOff ?a2 0)))] |- _ =>
  match goal with
  | Hk1 : ew _ a1 = Z_to_bv 64 (ckU bs ?k1) |- _ =>
  match goal with
  | Hk2 : ew _ a2 = Z_to_bv 64 (ckU bs ?k2) |- _ =>
    rewrite (ck_U_aluw_add2 Ew _ _ _ _
               (ck_Ufield Ew bs a1 k1 ltac:(ckatom) HL ltac:(lia) ltac:(lia) ltac:(lia))
               (ck_Ufield Ew bs a2 k2 ltac:(ckatom) HL ltac:(lia) ltac:(lia) ltac:(lia))
               ltac:(lia) ltac:(lia) ltac:(lia)) in Hc
  end end
| Hc : context [U ?Ew (SAlu ALU_ADD (SExt true 32 (SOff ?a1 0)) (SExt true 32 (SOff ?a2 0)))] |- _ =>
  match goal with
  | Hk1 : ew _ a1 = Z_to_bv 64 (ckU bs ?k1) |- _ =>
  match goal with
  | Hk2 : ew _ a2 = Z_to_bv 64 (ckU bs ?k2) |- _ =>
    rewrite (ck_U_alu_add2 Ew _ _ _ _
               (ck_Ufield Ew bs a1 k1 ltac:(ckatom) HL ltac:(lia) ltac:(lia) ltac:(lia))
               (ck_Ufield Ew bs a2 k2 ltac:(ckatom) HL ltac:(lia) ltac:(lia) ltac:(lia))
               ltac:(lia)) in Hc
  end end
| Hc : context [U ?Ew (SExt true 32 (SOff ?a 0))] |- _ =>
  match goal with
  | Hk : ew _ a = Z_to_bv 64 (ckU bs ?k) |- _ =>
    rewrite (ck_Ufield Ew bs a k ltac:(ckatom) HL ltac:(lia) ltac:(lia) ltac:(lia)) in Hc
  end
| Hc : context [U ?Ew (SOff ?a 0)] |- _ =>
  match goal with
  | Hk : ew _ a = Z_to_bv 64 (ckU bs ?k) |- _ =>
    rewrite (U_atom Ew a (ckU bs k) ltac:(ckatom) ltac:(pose proof (ckU_range bs k); lia)) in Hc
  | Hk : ew _ a = Z_to_bv 64 ?v |- _ =>
    rewrite (U_atom Ew a v ltac:(ckatom) ltac:(lia)) in Hc
  end
end;
repeat match goal with
| Hc : context [Z.land ?x 1] |- _ =>
  let He := fresh "Hev" in assert (He : Z.even x = true) by assumption;
  rewrite (ck_land1 x ltac:(lia) He) in Hc; clear He
end;
repeat match goal with
| Hc : context [(?x) mod 18446744073709551616] |- _ =>
  first [ rewrite (Z.mod_small x 18446744073709551616) in Hc by lia
        | rewrite (ck_mod_neg x) in Hc by lia ]
end;
repeat match goal with
| Hc : context [bv_swrap 64 ?z] |- _ => rewrite (swrap64_id z ltac:(unfold half64; lia)) in Hc
end;
repeat match goal with
| Hc : negb _ = true |- _ => apply negb_true_iff in Hc
| Hc : negb _ = false |- _ => apply negb_false_iff in Hc
| Hc : (_ =? _) = true |- _ => apply Z.eqb_eq in Hc
| Hc : (_ =? _) = false |- _ => apply Z.eqb_neq in Hc
| Hc : (_ <? _) = true |- _ => apply Z.ltb_lt in Hc
| Hc : (_ <? _) = false |- _ => apply Z.ltb_ge in Hc
| Hc : (_ <=? _) = true |- _ => apply Z.leb_le in Hc
| Hc : (_ <=? _) = false |- _ => apply Z.leb_gt in Hc
end.
(* ---------------------------------------------------- the pair test of rows i < j: 0x811f8 .. 0x81230 *)
(* The overlap test and the two MAC compares of one inner iteration form a diamond (the slices do not meet on
   one of two sides; bcmp (mac_i, ZERO, 6) is or is not 0). The walk takes it as one segment, proved here from a
   fresh symbolic state, so the paths join again at 0x81230. *)
Definition PC_PAIR : Z := 0x124c.
Definition PC_PAIR_END : Z := 0x1284.
Definition ss_pair : sstate := mkSS PC_PAIR sr_atoms [] None (mkFacts [] [] []).
Definition EP (regs : bvmap 5 word) : env := Eimg (Ereg regs [Z_to_bv 64 SBC]).
Definition CK_KEPT : list (bv 5) := [0; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Lemma ck_notclob_in : forall rr : bv 5, reg_in rr CLOB = false -> In rr CK_KEPT.
Proof.
intros rr Hr. pose proof (all_regs_in rr) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [vm_compute in Hr; discriminate | cbv; tauto] |]).
destruct Hin.
Qed.
Lemma ck_frame_nil : forall (E : env) (H : word -> bool) (m m' : word -> option byte),
frame_of E [] (mrestrict H m) (mrestrict H m') -> forall a, aview SEGS H m' a = aview SEGS H m a.
Proof. intros E H m m' HF a. apply aview_eq_of. apply HF. intros (rr & [] & _). Qed.
Lemma ck_frame_nil' : forall (E : env) rs (H : word -> bool) (m m' : word -> option byte), rs = [] ->
frame_of E rs (mrestrict H m) (mrestrict H m') -> forall a, aview SEGS H m' a = aview SEGS H m a.
Proof. intros E rs H m m' -> HF a. exact (ck_frame_nil E H m m' HF a). Qed.
(* ZERO's six bytes in any state of the walk *)
Lemma ck_zero_now : forall STK sp0 ly S (W : world SEGS) mem md ly' S' mem' md' k,
ajournal SEGS B STK sp0 [] ly S W mem md [] ly' S' W mem' md' k ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
absn_rom_bytes SEGS B (VAL (A_OBJ 4)) (map (fun b : byte => bv_unsigned b) Boxreg.zero6) ->
forall t, 0 <= t < 6 -> aview SEGS (w_H W) mem' (VAL (A_OBJ 4) + t) = Some 0.
Proof.
intros STK sp0 ly S W mem md ly' S' mem' md' k HJ HRO HZ t Ht.
destruct (HZ t ltac:(cbn [length map Boxreg.zero6 repeat]; lia)) as (Hrom & Hno & Her & Hval).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HIMG & _).
rewrite (HIMG _ (in_rom_img _ Hrom) Hno Her (fp_spares_closed [] _ sink_closed_nil)).
rewrite (HRO _ (or_introl Hrom) Hno Her). rewrite Hval.
assert (Ht6 : (t = 0 \/ t = 1 \/ t = 2 \/ t = 3 \/ t = 4 \/ t = 5)) by lia.
destruct Ht6 as [-> | [-> | [-> | [-> | [-> | ->]]]]]; reflexivity.
Qed.
(* the MAC of row i as bytes *)
Lemma ck_mac_zero_bytes : forall bs i, length bs = 288%nat -> 0 <= i -> 56 * i + 6 <= 288 ->
Boxreg.bx_mac bs i = Boxreg.zero6 -> forall t, 0 <= t < 6 -> ckB bs (56 * i + t) = Z_to_bv 8 0.
Proof.
intros bs i HL Hi Hi6 Hz t Ht.
pose proof (bsub_nth_b bs (56 * i) 6 (Z.to_nat t) ltac:(lia) ltac:(lia) ltac:(rewrite HL; lia)) as N.
unfold Boxreg.bx_mac in Hz. rewrite Hz in N. rewrite Z2Nat.id in N by lia.
rewrite <- N. unfold Boxreg.zero6. apply nth_repeat.
Qed.
Lemma ck_mac_eq : forall bs i j, length bs = 288%nat -> 0 <= i -> 0 <= j -> 56 * i + 6 <= 288 -> 56 * j + 6 <= 288 ->
(forall t, 0 <= t < 6 -> ckB bs (56 * i + t) = ckB bs (56 * j + t)) -> Boxreg.bx_mac bs i = Boxreg.bx_mac bs j.
Proof.
intros bs i j HL Hi Hj Hi6 Hj6 Heq. unfold Boxreg.bx_mac.
apply (nth_ext _ _ (Z_to_bv 8 0) (Z_to_bv 8 0)).
- rewrite !Boxreg.bsub_length by (try rewrite HL; lia). reflexivity.
- intros t Ht. rewrite Boxreg.bsub_length in Ht by (try rewrite HL; lia).
  rewrite (bsub_nth_b bs (56 * i) 6 t ltac:(lia) ltac:(lia) ltac:(rewrite HL; lia)).
  rewrite (bsub_nth_b bs (56 * j) 6 t ltac:(lia) ltac:(lia) ltac:(rewrite HL; lia)).
  apply Heq. lia.
Qed.
(* beqz on the result atom of a call, as a fact on the returned word *)
Lemma ckp_br_eq0 : forall (E : env) n b (v : word), ew E n = v -> U E b = 0 ->
branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E b) = true -> v = w64 0.
Proof.
intros E n b v Hn Hb Hc. rewrite branch_eq_U, Hb in Hc. apply Z.eqb_eq in Hc.
unfold U in Hc. cbn [sv_denot] in Hc. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned in Hc.
apply bv_eq. rewrite Hc. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
Qed.
Lemma ckp_br_ne0 : forall (E : env) n b (v : word), ew E n = v -> U E b = 0 ->
branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E b) = false -> v <> w64 0.
Proof.
intros E n b v Hn Hb Hc Hv. rewrite branch_eq_U, Hb in Hc. apply Z.eqb_neq in Hc. apply Hc.
unfold U. cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned, Hv. unfold w64.
apply unsigned_lit_small. lia.
Qed.
(* the two MAC compares of the pair test cannot send it to the abort: bcmp (mac_i, ZERO, 6) is not 0 and
   bcmp (mac_i, mac_j, 6) is 0 would make row i's MAC non-zero and equal to row j's *)
Lemma ckp_abort : forall (H : word -> bool) (m1 m2 : word -> option byte) r z0 bs i j (v1 v2 : word),
length bs = 288%nat -> 0 <= i -> 0 <= j -> 56 * i + 56 <= 288 -> 56 * j + 56 <= 288 ->
(Boxreg.bx_mac bs i = Boxreg.zero6 \/ Boxreg.bx_mac bs i <> Boxreg.bx_mac bs j) ->
(forall t, 0 <= t < REG_SIZEB ->
  aview SEGS H m1 (r + t) = Some (bv_unsigned (nth (Z.to_nat t) bs (Z_to_bv 8 0)))) ->
(forall t, 0 <= t < 6 -> aview SEGS H m1 (z0 + t) = Some 0) ->
(forall t, 0 <= t < REG_SIZEB ->
  aview SEGS H m2 (r + t) = Some (bv_unsigned (nth (Z.to_nat t) bs (Z_to_bv 8 0)))) ->
(v1 = w64 0 <-> forall t, 0 <= t < 6 -> aview SEGS H m1 (r + 56 * i + t) = aview SEGS H m1 (z0 + t)) ->
(v2 = w64 0 <-> forall t, 0 <= t < 6 -> aview SEGS H m2 (r + 56 * i + t) = aview SEGS H m2 (r + 56 * j + t)) ->
v1 <> w64 0 -> v2 = w64 0 -> False.
Proof.
intros H m1 m2 r z0 bs i j v1 v2 HL Hi Hj Hi56 Hj56 Hmac HV1 HZ1 HV2 Heq1 Heq2 Hne Hz.
destruct Hmac as [Hm0 | Hmn].
- apply Hne. apply Heq1. intros t Ht.
  rewrite (HZ1 t Ht). replace (r + 56 * i + t) with (r + (56 * i + t)) by lia.
  rewrite (HV1 (56 * i + t) ltac:(unfold REG_SIZEB; lia)).
  pose proof (ck_mac_zero_bytes bs i HL Hi ltac:(lia) Hm0 t Ht) as Hb. unfold ckB in Hb.
  rewrite Hb. reflexivity.
- apply Hmn. apply (ck_mac_eq bs i j HL Hi Hj ltac:(lia) ltac:(lia)). intros t Ht.
  pose proof (proj1 Heq2 Hz t Ht) as Ht2.
  replace (r + 56 * i + t) with (r + (56 * i + t)) in Ht2 by lia.
  replace (r + 56 * j + t) with (r + (56 * j + t)) in Ht2 by lia.
  rewrite (HV2 (56 * i + t) ltac:(unfold REG_SIZEB; lia)), (HV2 (56 * j + t) ltac:(unfold REG_SIZEB; lia)) in Ht2.
  injection Ht2 as Ht2. unfold ckB. apply bv_eq. exact Ht2.
Qed.
(* The pair test of rows i < j as one segment: from the overlap test at 0x811f8 to the loop's increment at
   0x81230. The walk forks inside it (which side of row i's slice row j lies on; whether row i's MAC is zero),
   so the walk takes it in one step and its four paths join here. *)
Lemma ck_pair : forall (W : world SEGS) (regsT : bvmap 5 word) memT sp0 ly S mem md mdc kj
(r bi ni bj nj : Z) (bs : list byte) (i j : Z) (G : list (Z * Z))
(Q : world SEGS -> config -> Prop),
ajournal SEGS B CHECK_STKB sp0 [] ly S W mem md [] ly S W memT mdc kj ->
getr regsT 11 = w64 bj -> getr regsT 9 = w64 (bi + ni) -> getr regsT 10 = w64 (bj + nj) ->
getr regsT 27 = w64 bi -> getr regsT 18 = w64 (r + 56 * i) -> getr regsT 19 = w64 (r + 56 * j) ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> spZ regsT = sp0 + -144 ->
0 <= bi -> 2 <= ni <= 40 -> 0 <= bj -> 2 <= nj <= 40 -> bi + ni <= 40 -> bj + nj <= 40 ->
~ Boxreg.meets bi ni bj nj ->
(Boxreg.bx_mac bs i = Boxreg.zero6 \/ Boxreg.bx_mac bs i <> Boxreg.bx_mac bs j) ->
length bs = 288%nat -> 0 <= i -> 0 <= j -> 56 * i + 56 <= 288 -> 56 * j + 56 <= 288 ->
In (r, REG_SIZEB) (ablocks B ly S) ->
(forall t, 0 <= t < REG_SIZEB ->
  aview SEGS (w_H W) mem (r + t) = Some (bv_unsigned (nth (Z.to_nat t) bs (Z_to_bv 8 0)))) ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
absn_rom_bytes SEGS B (VAL (A_OBJ 4)) (map (fun b : byte => bv_unsigned b) Boxreg.zero6) ->
img_shadow_vis SEGS B -> globs_marked SEGS B G -> In (VAL (A_OBJ 4), 6) G ->
IMG_LO + 64 <= VAL (A_OBJ 4) -> VAL (A_OBJ 4) + 6 + 64 <= IMG_HI ->
(forall regs' mem' md',
   (forall rr : bv 5, In rr CK_KEPT -> getr regs' rr = getr regsT rr) ->
   ajournal SEGS B CHECK_STKB sp0 [] ly S W mem md [] ly S W mem' md' kj ->
   (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + -144 - 2 * ESTACK <= a < sp0 + -144) ->
      aview SEGS (w_H W) mem' a = aview SEGS (w_H W) memT a) ->
   (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem' a) ->
   SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + PC_PAIR_END)) mem' (seg_rom SEGS)) md') Q) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (BASE + PC_PAIR)) memT (seg_rom SEGS)) mdc) Q.
Proof.
intros W regsT memT sp0 ly S mem md mdc kj r bi ni bj nj bs i j G Q
HJ R11 R9 R10 R27 R18 R19 Rgp Rtp Hsp Hbi Hni Hbj Hnj Hei Hej Hmeet Hmac HL Hi Hj Hi56 Hj56 Hin HV HRO HZ
HSV HGM HZG HZ1 HZ2 HK.
pose proof (pa_segs_low) as Hsegs. pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & Hstatic & _ & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct (al_blocks _ _ LAWS ly S W memT mdc r REG_SIZEB HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & Hrp & _).
change (req_size REG_SIZEB) with 288 in Hrceil, Hria, Hrp.
pose proof (ck_bytes_now _ _ _ _ _ _ _ _ _ _ _ _ HJ Hin HV) as HVn.
pose proof (ck_zero_now _ _ _ _ _ _ _ _ _ _ _ _ HJ HRO HZ) as HZn.
pose proof (pa_val_range (A_OBJ 4)) as HZr. pose proof (pa_obj_img 4 ltac:(lia)) as HZi.
assert (Hes : ESTACK = 4096) by reflexivity. assert (WS : CHECK_STKB = 8336) by reflexivity.
set (E := EP regsT).
assert (HEI : img_env VAL A_LIM E) by (unfold E, EP; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regsT [Z_to_bv 64 SBC]) n)
  by (intros n Hn; unfold E, EP; apply Eimg_low; exact Hn).
assert (HAE : env_agree 32 (Ereg regsT [Z_to_bv 64 SBC]) E)
  by (split; [intros nn Hnn; rewrite EL by (unfold A_TEXT; lia); reflexivity | unfold E, EP; reflexivity]).
assert (E9 : ew E 9 = Z_to_bv 64 (bi + ni))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsT _ 9 9%bv eq_refl); exact R9).
assert (E10 : ew E 10 = Z_to_bv 64 (bj + nj))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsT _ 10 10%bv eq_refl); exact R10).
assert (E11 : ew E 11 = Z_to_bv 64 bj)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsT _ 11 11%bv eq_refl); exact R11).
assert (E27 : ew E 27 = Z_to_bv 64 bi)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsT _ 27 27%bv eq_refl); exact R27).
assert (E18 : ew E 18 = Z_to_bv 64 (r + 56 * i))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsT _ 18 18%bv eq_refl); exact R18).
assert (E19 : ew E 19 = Z_to_bv 64 (r + 56 * j))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsT _ 19 19%bv eq_refl); exact R19).
assert (E2 : ew E 2 = getr regsT 2)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsT _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regsT 3)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsT _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regsT 4)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsT _ 4 4%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regsT) by (rewrite E2; reflexivity).
assert (HS : st_ok_pi SEGS VAL E ss_pair
  (restrict (w_H W) (mkst regsT (Z_to_bv 64 (BASE + PC_PAIR)) memT (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_pair, PC_PAIR. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn. exact I.
  - split; [exact I | split; [exact I | exact I]]. }
assert (SHOK : sh_ok SEGS CBx [] E (mrestrict (w_H W) memT)) by apply Forall_nil.
assert (HKM : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + -144 - 2 * ESTACK <= a < sp0 + -144) ->
  aview SEGS (w_H W) memT a = aview SEGS (w_H W) memT a) by reflexivity.
assert (HPR : forall a, apresent (w_H W) memT a -> apresent (w_H W) memT a) by (intros; assumption).
(* the state at the end of the segment hands the walk back to the caller *)
let finish := idtac;
lazymatch goal with
| HSx : st_ok_pi _ _ ?Ex _ (restrict _ ?msx) |- _ =>
  pmkst HSx;
  first [ apply HK | idtac "PF-apply"; fail ];
  [ first [ let rr := fresh "rr" in let Hrr := fresh "Hrr" in intros rr Hrr;
            (* x0 reads as 0 in every register file; the engine writes it as the literal 0 after a call *)
            assert (Hrr' : rr = 0%bv \/ In rr (tl CK_KEPT))
              by (destruct Hrr as [Hr | Hr]; [left; symmetry; exact Hr | right; exact Hr]);
            clear Hrr; destruct Hrr' as [-> | Hrr'];
            [ first [ reflexivity | unfold getr; vm_compute; reflexivity ]
            | apply (regs_kept_of_st_ok_pi Ex _ _ regsT [Z_to_bv 64 SBC] (tl CK_KEPT) HSx ltac:(ckagree HAE)
                       ltac:(vm_compute; reflexivity) rr Hrr') ]
          | idtac "PF-regs"; fail ]
  | first [ assumption | idtac "PF-j"; fail ]
  | first [ exact HKM | idtac "PF-km"; fail ]
  | first [ exact HPR | idtac "PF-pr"; fail ] ]
end in
(* one bcmp call: the wrapper's contract in journal form, then the state at the return slot *)
let ck_bcmp := idtac;
lazymatch goal with
| HSx : st_ok _ _ _ (restrict _ ?msx), HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  let kk0 := run_K_hi HSx in
  let kH := eval vm_compute in (Nat.max kk0 1024) in
  pmkst HSx;
  let Ra0 := fresh "Ra0" in let Ra1 := fresh "Ra1" in let Ra2 := fresh "Ra2" in
  let Rra := fresh "Rra" in let Rsp := fresh "Rsp" in let Pgp := fresh "Pgp" in let Ptp := fresh "Ptp" in
  prreg HSx (10%bv : bv 5) Ra0; prreg HSx (11%bv : bv 5) Ra1; prreg HSx (12%bv : bv 5) Ra2;
  prreg HSx (1%bv : bv 5) Rra; prreg HSx (2%bv : bv 5) Rsp; prreg HSx (3%bv : bv 5) Pgp;
  prreg HSx (4%bv : bv 5) Ptp;
  repeat (rewrite ew_ewset_other in Ra0 by lia); repeat (rewrite ew_ewset_other in Ra1 by lia);
  repeat (rewrite ew_ewset_other in Ra2 by lia); repeat (rewrite ew_ewset_other in Rsp by lia);
  repeat (rewrite ew_ewset_other in Pgp by lia); repeat (rewrite ew_ewset_other in Ptp by lia);
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
  let Qsp := fresh "Qsp" in
  assert (Qsp : spZ rg = sp0 + -144)
    by (unfold spZ at 1; rewrite Rsp; ckpeel; rewrite Usp, Hsp; reflexivity);
  let HVc := fresh "HVc" in let HZc := fresh "HZc" in
  pose proof (ck_bytes_now _ _ _ _ _ _ _ _ _ _ _ _ HJx Hin HV) as HVc;
  pose proof (ck_zero_now _ _ _ _ _ _ _ _ _ _ _ _ HJx HRO HZ) as HZc;
  eapply SRr_bind;
  [ eapply (aj_bcmp_at SEGS B LAWS Hsegs (SIGMA BB___interceptor_trampoline_bcmp) ABCMP W rg mm
              CHECK_STKB sp0 [] ly S W mem md [] ly S _ _ _ _ 6 (-144) _ HJx);
    [ first [ rewrite Ra0; ckpeel; rewrite E18; repeat (rewrite unsigned_lit_small by lia); reflexivity
            | idtac "C-a0"; let t := type of Ra0 in idtac t; fail ]
    | first [ rewrite Ra1; ckpeel; rewrite E19; repeat (rewrite unsigned_lit_small by lia); reflexivity
            | rewrite Ra1; ckpeel; change 245%nat with (A_OBJ 4);
              rewrite (img_env_atomP E (A_OBJ 4) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia));
              repeat (rewrite unsigned_lit_small by lia); reflexivity
            | idtac "C-a1"; let t := type of Ra1 in idtac t; fail ]
    | first [ rewrite Ra2; reflexivity | idtac "C-a2"; fail ]
    | first [ lia | idtac "C-n"; fail ]
    | first [ lia | idtac "C-x0"; fail ]
    | first [ lia | idtac "C-x1"; fail ]
    | first [ lia | idtac "C-y0"; fail ]
    | first [ lia | idtac "C-y1"; fail ]
    | first [ exact Qsp | idtac "C-sp"; fail ]
    | first [ reflexivity | idtac "C-al"; fail ]
    | first [ lia | idtac "C-neg"; fail ]
    | first [ unfold CHECK_STKB; lia | idtac "C-bud"; fail ]
    | first [ rewrite Pgp; ckpeel; rewrite E3; exact Rgp | idtac "C-gp"; fail ]
    | first [ rewrite Ptp; ckpeel; rewrite E4; exact Rtp | idtac "C-tp"; fail ]
    | first [ exact Rra | idtac "C-ra"; fail ]
    | first [ apply ret_ok_codeptr_v; [lia | reflexivity] | idtac "C-rok"; fail ]
    | first [ unfold src_ok; let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; split;
              [ first [ replace a with (r + (a - r)) by lia;
                        rewrite (HVc (a - r) ltac:(unfold REG_SIZEB; lia)); discriminate
                      | replace a with (VAL (A_OBJ 4) + (a - VAL (A_OBJ 4))) by lia;
                        rewrite (HZc (a - VAL (A_OBJ 4)) ltac:(lia)); discriminate ]
              | rewrite Qsp; lia ]
            | idtac "C-srcx"; fail ]
    | first [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; split;
              [ first [ replace a with (r + (a - r)) by lia;
                        rewrite (HVc (a - r) ltac:(unfold REG_SIZEB; lia)); discriminate
                      | replace a with (VAL (A_OBJ 4) + (a - VAL (A_OBJ 4))) by lia;
                        rewrite (HZc (a - VAL (A_OBJ 4)) ltac:(lia)); discriminate ]
              | rewrite Qsp; lia ]
            | idtac "C-srcy"; fail ]
    | first [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; lia
            | idtac "C-wx"; fail ]
    | first [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; lia
            | idtac "C-wy"; fail ]
    | first [ eapply (amem_range_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR Hin);
              change (req_size REG_SIZEB) with 288; lia
            | apply amem_range_high; [lia | left; lia | lia] | idtac "C-mrx"; fail ]
    | first [ eapply (amem_range_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR Hin);
              change (req_size REG_SIZEB) with 288; lia
            | apply amem_range_high; [lia | left; lia | lia] | idtac "C-mry"; fail ]
    | first [ eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJx) Hin);
              change (req_size REG_SIZEB) with 288; lia
            | exact (proj1 (ro_read_ok_glob SEGS B G ly S W _ _ (VAL (A_OBJ 4)) 6 (VAL (A_OBJ 4)) 6
                              HGM HZG HSV (proj1 HJx) ltac:(lia) ltac:(lia) ltac:(lia) HZ1 HZ2))
            | idtac "C-radx"; fail ]
    | first [ intros _; eapply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJx) Hin);
              change (req_size REG_SIZEB) with 288; lia
            | intros _; exact (proj2 (ro_read_ok_glob SEGS B G ly S W _ _ (VAL (A_OBJ 4)) 6
                                        (VAL (A_OBJ 4)) 6 HGM HZG HSV (proj1 HJx) ltac:(lia) ltac:(lia) ltac:(lia)
                                        HZ1 HZ2))
            | idtac "C-hullx"; fail ]
    | first [ eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJx) Hin);
              change (req_size REG_SIZEB) with 288; lia
            | exact (proj1 (ro_read_ok_glob SEGS B G ly S W _ _ (VAL (A_OBJ 4)) 6 (VAL (A_OBJ 4)) 6
                              HGM HZG HSV (proj1 HJx) ltac:(lia) ltac:(lia) ltac:(lia) HZ1 HZ2))
            | idtac "C-rady"; fail ]
    | first [ intros _; eapply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJx) Hin);
              change (req_size REG_SIZEB) with 288; lia
            | intros _; exact (proj2 (ro_read_ok_glob SEGS B G ly S W _ _ (VAL (A_OBJ 4)) 6
                                        (VAL (A_OBJ 4)) 6 HGM HZG HSV (proj1 HJx) ltac:(lia) ltac:(lia) ltac:(lia)
                                        HZ1 HZ2))
            | idtac "C-hully"; fail ] ]
  | ];
  cbv beta;
  let W4 := fresh "W4" in let c4 := fresh "c4" in let regs4 := fresh "regs4" in let mem4 := fresh "mem4" in
  let md4 := fresh "md4" in let HJ4 := fresh "HJn" in let HP4 := fresh "HP4" in let v4 := fresh "v4" in
  let Hv4 := fresh "Hv4" in let Heq4 := fresh "Heqb" in let Hfr4 := fresh "Hfr4" in let Hpr4 := fresh "Hpr4" in
  intros W4 c4 _ (-> & regs4 & mem4 & md4 & v4 & -> & HJ4 & HP4 & Hv4 & Heq4 & Hfr4 & Hpr4);
  let HS4 := fresh "HSn" in
  jafter_call_keep_hi HSx kH regs4 (mrestrict (w_H W) mem4) HP4 (@nil nat) HS4;
  match type of HS4 with ?tq -> _ => let HRK := fresh "HRK" in assert (HRK : tq);
    [ apply Forall_nil | specialize (HS4 HRK); clear HRK ] end;
  clear HSx; rewrite <- restrict_mkst_fx in HS4;
  let HEIn := fresh "HEIn" in let SHn := fresh "SHn" in
  lazymatch type of HS4 with st_ok_pi _ _ ?En _ _ =>
    let EV := fresh "EV" in
    let k4 := eval vm_compute in (kH + 4)%nat in
    assert (EV : ew En k4 = v4)
      by (change k4 with (kH + 4)%nat; rewrite (ew_havoc_new _ kH _ 4 (Z_to_bv 64 0)) by (cbn; lia);
          cbn [map nth CLOB]; rewrite Hv4; reflexivity);
    assert (HEIn : img_env VAL A_LIM En) by (apply img_env_havoc_hi; [assumption | unfold A_LIM; lia]);
    assert (SHn : sh_ok SEGS CBx [] En (mrestrict (w_H W) mem4)) by apply Forall_nil
  end;
  let HKM2 := fresh "HKM" in
  assert (HKM2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + -144 - 2 * ESTACK <= a < sp0 + -144) ->
    aview SEGS (w_H W) mem4 a = aview SEGS (w_H W) memT a)
    by (intros a Ha Hw; rewrite (Hfr4 a Ha ltac:(lia)); apply HKM; assumption);
  clear HKM; rename HKM2 into HKM;
  let HPR2 := fresh "HPR" in
  assert (HPR2 : forall a, apresent (w_H W) memT a -> apresent (w_H W) mem4 a)
    by (intros a Ha; apply Hpr4; apply HPR; exact Ha);
  clear HPR; rename HPR2 into HPR;
  repeat match goal with
  | H : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => tryif constr_eq H HJ4 then fail else clear H
  end;
  repeat match goal with
  | H : sh_ok _ _ _ _ _ |- _ => tryif constr_eq H SHn then fail else clear H
  end
  end
end in
(* the run from one stop to the next; a run of this segment writes no memory *)
let step := idtac;
lazymatch goal with
| HSx : st_ok_pi _ _ _ _ _, HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHx : sh_ok _ _ _ _ _ |- _ =>
  paj_run_to_tok RUNTO HSx HJx SHx BspanC PC_PAIR_END; [awr_ok_tac; ckpeel; exact Usp |];
  lazymatch goal with
  | HFrx : frame_of ?Ex ?rs (mrestrict _ ?m0) (mrestrict _ ?m1) |- _ =>
    let HKM2 := fresh "HKM" in
    first [ assert (HKM2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + -144 - 2 * ESTACK <= a < sp0 + -144) ->
              aview SEGS (w_H W) m1 a = aview SEGS (w_H W) memT a)
              by (intros a Ha Hw; rewrite (ck_frame_nil' Ex rs (w_H W) m0 m1 eq_refl HFrx a); apply HKM; assumption)
          | idtac "ST-KM"; let t := type of HFrx in idtac t; let u := type of HKM in idtac u; fail ];
    clear HKM; rename HKM2 into HKM;
    let HPR2 := fresh "HPR" in
    first [ assert (HPR2 : forall a, apresent (w_H W) memT a -> apresent (w_H W) m1 a)
              by (intros a Ha; lazymatch goal with HG : mem_grows _ _ |- _ => apply (apresent_grows _ _ _ a HG) end;
                  apply HPR; exact Ha)
          | idtac "ST-PR"; fail ];
    clear HPR; rename HPR2 into HPR
  | _ => idtac "ST-NOFRAME"
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end
end in
(* a branch of this segment as a fact on Pau's values *)
let pnorm := idtac;
repeat match goal with
| Hc : branch_taken BC_EQ _ _ = _ |- _ => rewrite branch_eq_U in Hc
| Hc : branch_taken BC_LT _ _ = _ |- _ => rewrite branch_lt_S in Hc
| Hc : branch_taken BC_GE _ _ = _ |- _ => rewrite branch_ge_S in Hc
end;
repeat match goal with
| Hc : context [Sg ?Ew ?e] |- _ => rewrite (S_of_U Ew e) in Hc
end;
repeat match goal with
| Hc : context [U ?Ew (SAluw ALU_ADD (SOff 10 0) (SLit 0))] |- _ =>
  rewrite (ck_U_aluw_at0 Ew 10 (bj + nj) ltac:(ckatom) ltac:(lia)) in Hc
| Hc : context [U ?Ew (SOff ?a 0)] |- _ =>
  first [ rewrite (U_atom Ew a bj ltac:(ckatom) ltac:(lia)) in Hc
        | rewrite (U_atom Ew a bi ltac:(ckatom) ltac:(lia)) in Hc
        | rewrite (U_atom Ew a (bi + ni) ltac:(ckatom) ltac:(lia)) in Hc ]
end;
repeat match goal with
| Hc : context [bv_swrap 64 ?z] |- _ => rewrite (swrap64_id z ltac:(unfold half64; lia)) in Hc
end;
repeat match goal with
| Hc : negb _ = true |- _ => apply negb_true_iff in Hc
| Hc : negb _ = false |- _ => apply negb_false_iff in Hc
| Hc : (_ =? _) = true |- _ => apply Z.eqb_eq in Hc
| Hc : (_ =? _) = false |- _ => apply Z.eqb_neq in Hc
| Hc : (_ <? _) = true |- _ => apply Z.ltb_lt in Hc
| Hc : (_ <? _) = false |- _ => apply Z.ltb_ge in Hc
end in
(* a branch of this segment, at the state and sh_ok hypotheses of the current point *)
let br := idtac;
lazymatch goal with
| HSx : st_ok_pi _ _ _ _ _, SHx : sh_ok _ _ _ _ _ |- _ => psrr_branch_tok RUN BR HSx SHx BspanC
end in
(* the abort at 0x8122c: bcmp (mac_i, ZERO, 6) <> 0 and bcmp (mac_i, mac_j, 6) = 0 contradict Pau's MAC premise *)
let pabort := idtac;
repeat match goal with
| Hc : branch_taken BC_EQ (sv_denot ?Ex (SOff ?k 0)) (sv_denot ?Ex ?b) = true, EVx : ew _ ?k = ?v |- _ =>
  let Ek := fresh "Ek" in
  assert (Ek : ew Ex k = v) by (ckpeel; exact EVx);
  pose proof (ckp_br_eq0 Ex k b v Ek ltac:(first [ rewrite U_SLit; reflexivity | reflexivity ]) Hc) as Zv2;
  clear Hc Ek
| Hc : branch_taken BC_EQ (sv_denot ?Ex (SOff ?k 0)) (sv_denot ?Ex ?b) = false, EVx : ew _ ?k = ?v |- _ =>
  let Ek := fresh "Ek" in
  assert (Ek : ew Ex k = v) by (ckpeel; exact EVx);
  pose proof (ckp_br_ne0 Ex k b v Ek ltac:(first [ rewrite U_SLit; reflexivity | reflexivity ]) Hc) as Nv1;
  clear Hc Ek
end;
lazymatch type of Nv1 with ?v1 <> _ => lazymatch type of Zv2 with ?v2 = _ =>
lazymatch goal with H1 : v1 = _ <-> _, H2 : v2 = _ <-> _ |- _ =>
  refine (ckp_abort _ _ _ r _ bs i j v1 v2 HL Hi Hj Hi56 Hj56 Hmac _ _ _ H1 H2 Nv1 Zv2); assumption
end end end in
(* from the first call to 0x81230: bcmp (mac_i, ZERO, 6); if it is 0 the pair is done, else
   bcmp (mac_i, mac_j, 6), whose 0 (the abort) is refuted *)
let rest := idtac;
ck_bcmp; step;
br;
[ step; finish
| step; ck_bcmp; step;
  br;
  [ exfalso;
    first [ pabort | idtac "PAIR-ABORT"; fail ]
  | step; finish ] ] in
(* the overlap test at 0x811f8 (bge, then blt on the fall-through), then the two MAC compares; the paths join
   at 0x81230 *)
(br;
 [ step; rest
 | step;
   br;
   [ exfalso; apply Hmeet; unfold Boxreg.meets; pnorm; split; lia
   | step; rest ] ]).
Qed.

(* ==================================================================== the walk, split at its loop heads
   (a Theorem Labs lane, 2026-10-29). The walk of check B in check A's per-head form: one segment lemma per stretch
   between loop heads, each stated over a FIXED symbolic state at the head, so no run replays the rows before
   it. n is pinned (ck_facts N, as ck_entry gives it), so the engine decides every loop test; the heads are
   the outer loop's at 0x81108 (row i) and the inner loop's at 0x811b0 (pair i, j). The segments reuse the
   driver's call-site steps as tactics: ckb_memchr (memchr at 0x81190), ckb_pair (ck_pair at 0x811f8,
   re-entered at 0x81230) and ckb_ret (the return); their arguments are the names the driver's text reads. *)
Ltac ckb_ret W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs :=
lazymatch goal with
| HS2 : st_ok_pi _ _ _ _ (restrict _ ?msw), HJ2 : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  let R1 := fresh "R1" in
  first [ prreg HS2 (1%bv : bv 5) R1 | idtac "RS1"; fail ];
  repeat (rewrite ew_ewset_other in R1 by lia); repeat (rewrite ew_havoc_old in R1 by lia);
  first [ eapply (RET W _ _ _ _ _ HS2 eq_refl ltac:(vm_compute; reflexivity)) | idtac "RS2"; fail ];
  intros mat';
  unfold tbcheck_post, apost_base;
  eexists ly, S, _, _, _;
  first [ split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|] | idtac "RS3"; fail ];
  first [ split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ2|]
        | idtac "RS4"; fail ];
  first [ split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (ck_extra bs) HS2);
          [ ckagree HAE | vm_compute; reflexivity ]|] | idtac "RS5"; fail ];
  first [ split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [apply Permutation_refl|]
        | idtac "RS6"; fail ];
  let ii := fresh "ii" in let Hii := fresh "Hii" in let HBK := fresh "HBK" in
  intros ii Hii;
  pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HBK & _);
  first [ rewrite (HBK r REG_SIZEB ii Hin Hin
            ltac:(change (req_size REG_SIZEB) with 288; unfold REG_SIZEB in *; lia)
            (inFP_nil (r + ii))) | idtac "RS7"; fail ];
  first [ apply HV; exact Hii | idtac "RS8"; fail ]
end.
Ltac ckb_memchr W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs :=
lazymatch goal with
| HS2 : st_ok _ _ _ (restrict _ ?msw), HJ2 : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  let kk0 := run_K_hi HS2 in
  let kH := eval vm_compute in (Nat.max kk0 1024) in
  pmkst HS2;
  let Ra0 := fresh "Ra0" in let Ra1 := fresh "Ra1" in let Ra2 := fresh "Ra2" in
  let Rra := fresh "Rra" in let Rsp := fresh "Rsp" in let Rgp := fresh "Rgp" in let Rtp := fresh "Rtp" in
  prreg HS2 (10%bv : bv 5) Ra0; prreg HS2 (11%bv : bv 5) Ra1; prreg HS2 (12%bv : bv 5) Ra2;
  prreg HS2 (1%bv : bv 5) Rra; prreg HS2 (2%bv : bv 5) Rsp; prreg HS2 (3%bv : bv 5) Rgp; prreg HS2 (4%bv : bv 5) Rtp;
  repeat (rewrite ew_ewset_other in Ra0 by lia); repeat (rewrite ew_ewset_other in Ra1 by lia);
  repeat (rewrite ew_ewset_other in Ra2 by lia); repeat (rewrite ew_ewset_other in Rsp by lia);
  repeat (rewrite ew_ewset_other in Rgp by lia); repeat (rewrite ew_ewset_other in Rtp by lia);
  let c := lazymatch type of Ra0 with context [bv_unsigned (ew _ 10) + ?c] => c end in
  let I := eval vm_compute in ((c - 24) / 56) in
  idtac "AT-CALL" c I;
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
  let Ha0 := fresh "Ha0" in
  first [ assert (Ha0 : getr rg 10 = w64 (r + c))
            by (rewrite Ra0; ckpeel; rewrite E10, unsigned_lit_small by lia; reflexivity)
        | idtac "MC-a0"; let t := type of Ra0 in idtac t; fail ];
  let Qsp := fresh "Qsp" in
  first [ assert (Qsp : spZ rg = spZ regs + -144)
            by (unfold spZ at 1; rewrite Rsp; ckpeel; rewrite Usp, unsigned_lit_small by lia; reflexivity)
        | idtac "MC-sp"; fail ];
  let HVn := fresh "HVn" in
  pose proof (ck_bytes_now _ _ _ _ _ _ _ _ _ _ _ _ HJ2 Hin HV) as HVn;
  first [
  eapply SRr_bind;
  [ eapply (aj_memchr_at MCH_LOB (MCH_LOB + 32) _ AMEMCHR W rg mm CHECK_STKB (spZ regs) [] ly S W mem md [] ly S
              _ 0 (r + c) 0 32 (-144) _ HJ2);
    [ first [ exact Ha0 | idtac "G1"; fail ]
    | first [ rewrite Ra1; reflexivity | idtac "G2"; let t := type of Ra1 in idtac t; fail ]
    | first [ rewrite Ra2; reflexivity | idtac "G3"; let t := type of Ra2 in idtac t; fail ]
    | first [ lia | idtac "G4"; fail ] | first [ lia | idtac "G5"; fail ]
    | first [ lia | idtac "G6"; fail ] | first [ lia | idtac "G7"; fail ]
    | first [ intros a Ha; split;
      [ replace a with (r + (a - r)) by lia; rewrite (HVn (a - r) ltac:(unfold REG_SIZEB; lia)); discriminate
      | rewrite Qsp; lia ] | idtac "G8"; fail ]
    | first [ eapply (amem_range_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ2) Hin);
      change (req_size REG_SIZEB) with 288; lia | idtac "G9"; fail ]
    | first [ eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ2) Hin);
      change (req_size REG_SIZEB) with 288; lia | idtac "G10"; fail ]
    | first [ intros _; eapply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ2) Hin);
      change (req_size REG_SIZEB) with 288; lia | idtac "G11"; fail ]
    | first [ exact (ck_consts _ _ _ _ _ _ _ _ _ _ _ _ HJ2 HRO HMC) | idtac "G12"; fail ]
    | first [ exact Qsp | idtac "G13"; fail ]
    | first [ reflexivity | idtac "G14"; fail ]
    | first [ lia | idtac "G15"; fail ]
    | first [ unfold CHECK_STKB; lia | idtac "G16"; fail ]
    | first [ rewrite Rgp; ckpeel; rewrite E3; exact Hgp
            | idtac "G17"; let t := type of Rgp in idtac t; fail ]
    | first [ rewrite Rtp; ckpeel; rewrite E4; exact Htp | idtac "G18"; fail ]
    | first [ exact Rra | idtac "G19"; let t := type of Rra in idtac t; fail ]
    | first [ apply ret_ok_codeptr_v; [lia | reflexivity] | idtac "G20"; fail ] ]
  | ] | idtac "MC-call"; fail ];
  cbv beta;
  let W3 := fresh "W3" in let c3 := fresh "c3" in let regs3 := fresh "regs3" in let mem3 := fresh "mem3" in
  let md3 := fresh "md3" in let HJ3 := fresh "HJ3" in let HP3 := fresh "HP3" in let kk := fresh "kk" in
  let HFB := fresh "HFB" in let Ha0' := fresh "Ha0'" in let Hfr3 := fresh "Hfr3" in let Hpr3 := fresh "Hpr3" in
  intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & (kk & HFB & Ha0') & Hfr3 & Hpr3);
  let Hkk := fresh "Hkk" in
  first [ assert (Hkk : kk < 32)
            by (apply (ck_first_nul W mm r bs I kk HL ltac:(lia) ltac:(lia) HVn
                       (HB6 I ltac:(unfold Boxreg.bx_n; lia)));
                replace (r + 56 * I + 24) with (r + c) by lia; exact HFB)
        | idtac "MC-kk"; fail ];
  let Hkk0 := fresh "Hkk0" in
  assert (Hkk0 : 0 <= kk) by (destruct HFB as (Hkb & _); lia);
  replace (kk <? 32) with true in Ha0' by (symmetry; apply Z.ltb_lt; exact Hkk);
  let HS3 := fresh "HS3" in
  first [ jafter_call_keep_hi HS2 kH regs3 (mrestrict (w_H W) mem3) HP3 [0; 1; 2; 3]%nat HS3
        | idtac "MC-after"; fail ];
  match type of HS3 with ?tq -> _ => let HRK := fresh "HRK" in assert (HRK : tq);
    [ | specialize (HS3 HRK); clear HRK ] end;
  [ first [
    cbn [ms_mem restrict];
    let HJ3pres := fresh "HJ3pres" in
    pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ3pres & _);
    pose proof (pa_obj_img 1 ltac:(lia)); pose proof (pa_obj_img 12 ltac:(lia));
    pose proof (pa_val_range (A_OBJ 1)); pose proof (pa_val_range (A_OBJ 12));
    let EO1 := fresh "EO1" in let EO12 := fresh "EO12" in
    assert (EO1 : ew E 242 = Z_to_bv 64 (VAL (A_OBJ 1)))
      by (apply (img_env_atomP E (A_OBJ 1)); [exact HEI | unfold A_OBJ, A_TEXT, A_LIM; lia]);
    assert (EO12 : ew E 253 = Z_to_bv 64 (VAL (A_OBJ 12)))
      by (apply (img_env_atomP E (A_OBJ 12)); [exact HEI | unfold A_OBJ, A_TEXT, A_LIM; lia]);
    repeat apply Forall_cons; try apply Forall_nil;
    split;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val];
    ckpeel;
    rewrite ?Usp, ?EO1, ?EO12, ?E10; repeat (rewrite unsigned_lit_small by lia);
    let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    first [ apply (mbyte_of_aview SEGS); apply Hfr3; lia
          | try lia; intros _; apply (apresent_writable SEGS); apply HJ3pres; lia
          | match goal with |- ?G => idtac "KG" G end; let t := type of Ha in idtac "KHa" t; fail ]
    | idtac "MC-kept"; fail ]
  | ];
  clear HS2; rewrite <- restrict_mkst_fx in HS3;
  let EA0 := fresh "EA0" in
  let k4 := eval vm_compute in (kH + 4)%nat in
  lazymatch type of HS3 with st_ok_pi _ _ ?En _ _ =>
    first [ assert (EA0 : ew En k4 = Z_to_bv 64 (r + c + kk))
              by (change k4 with (kH + 4)%nat; rewrite (ew_havoc_new _ kH _ 4 (Z_to_bv 64 0)) by (cbn; lia);
                  cbn [map nth CLOB]; rewrite Ha0'; reflexivity)
          | idtac "MC-ea0"; fail ];
    let HEIn := fresh "HEIn" in
    assert (HEIn : img_env VAL A_LIM En) by (apply img_env_havoc_hi; [assumption | unfold A_LIM; lia]);
    let SH3 := fresh "SHOKn" in
    first [ assert (SH3 : sh_ok SEGS CBx ck_SH En (mrestrict (w_H W) mem3))
              by (unfold sh_ok, ck_SH; constructor; [|constructor];
                  apply (shent_ok_of_block SEGS B LAWS ly S W mem3 md3 En CBx 10 r REG_SIZEB 0 288
                           (proj1 HJ3) Hin);
                  [ unfold CBx; rewrite (U_atom En 32 SBC ltac:(ckatom) ltac:(unfold SBC; lia)); reflexivity
                  | apply (U_atom En 10 r ltac:(ckatom)); lia
                  | lia | change (req_size REG_SIZEB) with 288; lia ])
          | idtac "MC-shok"; fail ];
    repeat match goal with
    | H : sh_ok _ _ _ _ _ |- _ => tryif constr_eq H SH3 then fail else clear H
    end;
    repeat match goal with
    | H : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      tryif constr_eq H HJ3 then fail else clear H
    end
  end
  end
end.
Ltac ckb_pair W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs :=
lazymatch goal with
| HS' : st_ok_pi _ _ ?Ez ?ssz _, SHOK' : sh_ok _ ?Bx ?SH _ _ |- _ =>
        idtac "AT-PAIR";
        let kk0 := run_K_hi HS' in
        let kH := eval vm_compute in (Nat.max kk0 2048) in
        let Q9 := fresh "Q9" in let Q10 := fresh "Q10" in let Q11 := fresh "Q11" in
        let Q18 := fresh "Q18" in let Q19 := fresh "Q19" in let Q27 := fresh "Q27" in
        let Qg := fresh "Qg" in let Qt := fresh "Qt" in let Qs := fresh "Qs" in
        ckregraw HS' (9%bv : bv 5) Q9; ckregraw HS' (10%bv : bv 5) Q10; ckregraw HS' (11%bv : bv 5) Q11;
        ckregraw HS' (18%bv : bv 5) Q18; ckregraw HS' (19%bv : bv 5) Q19; ckregraw HS' (27%bv : bv 5) Q27;
        prreg HS' (3%bv : bv 5) Qg; prreg HS' (4%bv : bv 5) Qt; prreg HS' (2%bv : bv 5) Qs;
        repeat (rewrite ew_ewset_other in Qg by lia); repeat (rewrite ew_ewset_other in Qt by lia);
        repeat (rewrite ew_ewset_other in Qs by lia);
        let c18 := lazymatch type of Q18 with context [SOff 10 ?c] => c end in
        let c19 := lazymatch type of Q19 with context [SOff 10 ?c] => c end in
        let I := eval vm_compute in (c18 / 56) in
        let J := eval vm_compute in (c19 / 56) in
        let bI := eval vm_compute in (c18 + 8) in
        let nI := eval vm_compute in (c18 + 12) in
        let bJ := eval vm_compute in (c19 + 8) in
        let nJ := eval vm_compute in (c19 + 12) in
        let aI := eval vm_compute in (35 + 2 * Z.to_nat I)%nat in
        let dI := eval vm_compute in (36 + 2 * Z.to_nat I)%nat in
        let aJ := eval vm_compute in (35 + 2 * Z.to_nat J)%nat in
        let dJ := eval vm_compute in (36 + 2 * Z.to_nat J)%nat in
        idtac "PAIR" I J;
        pmkst HS';
        lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
        first [
        eapply (ck_pair W rg mm (spZ regs) ly S mem md _ _ r
                  (Boxreg.rd4 bs bI) (Boxreg.rd4 bs nI)
                  (Boxreg.rd4 bs bJ) (Boxreg.rd4 bs nJ) bs I J G _);
        [ first [ eassumption | idtac "K-J"; fail ]
        | first [ apply (ck_reg_of_U Ez _ _ _ Q11);
                  apply (ck_Ufield Ez bs aJ bJ ltac:(ckatom) HL ltac:(lia) ltac:(lia) ltac:(lia))
                | idtac "K-11"; fail ]
        | first [ apply (ck_reg_of_U Ez _ _ _ Q9);
                  apply (ck_U_aluw_add2 Ez _ _ _ _
                           (ck_Ufield Ez bs aI bI ltac:(ckatom) HL ltac:(lia) ltac:(lia) ltac:(lia))
                           (ck_Ufield Ez bs dI nI ltac:(ckatom) HL ltac:(lia) ltac:(lia) ltac:(lia)));
                  lia
                | idtac "K-9"; let t := type of Q9 in idtac t; fail ]
        | first [ apply (ck_reg_of_U Ez _ _ _ Q10);
                  apply (ck_U_alu_add2 Ez _ _ _ _
                           (ck_Ufield Ez bs aJ bJ ltac:(ckatom) HL ltac:(lia) ltac:(lia) ltac:(lia))
                           (ck_Ufield Ez bs dJ nJ ltac:(ckatom) HL ltac:(lia) ltac:(lia) ltac:(lia)));
                  lia
                | idtac "K-10"; let t := type of Q10 in idtac t; fail ]
        | first [ apply (ck_reg_of_U Ez _ _ _ Q27);
                  apply (ck_Ufield Ez bs aI bI ltac:(ckatom) HL ltac:(lia) ltac:(lia) ltac:(lia))
                | idtac "K-27"; fail ]
        | first [ apply (ck_reg_of_U Ez _ _ _ Q18);
                  rewrite (U_atom_off Ez 10 r c18 ltac:(ckatom) ltac:(lia) ltac:(lia)); f_equal; lia
                | idtac "K-18"; let t := type of Q18 in idtac t; fail ]
        | first [ apply (ck_reg_of_U Ez _ _ _ Q19);
                  rewrite (U_atom_off Ez 10 r c19 ltac:(ckatom) ltac:(lia) ltac:(lia)); f_equal; lia
                | idtac "K-19"; fail ]
        | first [ rewrite Qg; ckpeel; rewrite E3; exact Hgp | idtac "K-gp"; fail ]
        | first [ rewrite Qt; ckpeel; rewrite E4; exact Htp | idtac "K-tp"; fail ]
        | first [ unfold spZ at 1; rewrite Qs; ckpeel; rewrite Usp, unsigned_lit_small by lia; reflexivity
                | idtac "K-sp"; fail ]
        | first [ lia | idtac "K-bi"; fail ] | first [ lia | idtac "K-ni"; fail ]
        | first [ lia | idtac "K-bj"; fail ] | first [ lia | idtac "K-nj"; fail ]
        | first [ lia | idtac "K-ei"; fail ] | first [ lia | idtac "K-ej"; fail ]
        | first [ exact (HB4 I J ltac:(lia) ltac:(lia) ltac:(unfold Boxreg.bx_n; lia)) | idtac "K-B4"; fail ]
        | first [ exact (HB5 I J ltac:(lia) ltac:(lia) ltac:(unfold Boxreg.bx_n; lia)) | idtac "K-B5"; fail ]
        | first [ exact HL | idtac "K-L"; fail ]
        | first [ lia | idtac "K-i"; fail ] | first [ lia | idtac "K-j"; fail ]
        | first [ lia | idtac "K-i56"; fail ] | first [ lia | idtac "K-j56"; fail ]
        | first [ exact Hin | idtac "K-in"; fail ]
        | first [ exact HV | idtac "K-V"; fail ]
        | first [ exact HRO | idtac "K-RO"; fail ]
        | first [ exact HZ | idtac "K-Z"; fail ]
        | first [ exact HSV | idtac "K-SV"; fail ]
        | first [ exact HGM | idtac "K-GM"; fail ]
        | first [ exact HZG | idtac "K-ZG"; fail ]
        | first [ exact HZ1 | idtac "K-Z1"; fail ]
        | first [ exact HZ2 | idtac "K-Z2"; fail ]
        | ] | idtac "K-apply"; fail ];
        let regs5 := fresh "regs5" in let mem5 := fresh "mem5" in let md5 := fresh "md5" in
        let Hkept := fresh "Hkept" in let HJ5 := fresh "HJp" in let Hkm := fresh "Hkm" in
        let Hpr5 := fresh "Hpr5" in
        intros regs5 mem5 md5 Hkept HJ5 Hkm Hpr5; idtac "KC1";
        let HS5 := fresh "HSp" in
        first [ jafter_stretch_keep_hi HS' kH regs5 (mrestrict (w_H W) mem5) CLOB 4740 [0; 1; 2; 3]%nat HS5
              | idtac "KC-stretch"; fail ];
        idtac "KC2";
        match type of HS5 with ?tq -> _ => let H1 := fresh "H1" in assert (H1 : tq);
          [ first [ let rr := fresh "rr" in let Hrr := fresh "Hrr" in intros rr Hrr;
                    apply Hkept; apply ck_notclob_in; exact Hrr
                  | idtac "KC-regs"; match goal with |- ?G => idtac G end; fail ]
          | specialize (HS5 H1); clear H1 ] end;
        idtac "KC3";
        match type of HS5 with ?tq -> _ => let H2 := fresh "H2" in assert (H2 : tq);
          [ first [
            cbn [ms_mem restrict];
            let HJ5pres := fresh "HJ5pres" in
            pose proof HJ5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ5pres & _);
            pose proof (pa_obj_img 1 ltac:(lia)); pose proof (pa_obj_img 12 ltac:(lia));
            pose proof (pa_val_range (A_OBJ 1)); pose proof (pa_val_range (A_OBJ 12));
            let EO1 := fresh "EO1" in let EO12 := fresh "EO12" in
            assert (EO1 : ew E 242 = Z_to_bv 64 (VAL (A_OBJ 1)))
              by (apply (img_env_atomP E (A_OBJ 1)); [exact HEI | unfold A_OBJ, A_TEXT, A_LIM; lia]);
            assert (EO12 : ew E 253 = Z_to_bv 64 (VAL (A_OBJ 12)))
              by (apply (img_env_atomP E (A_OBJ 12)); [exact HEI | unfold A_OBJ, A_TEXT, A_LIM; lia]);
            repeat apply Forall_cons; try apply Forall_nil;
            split;
            cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val];
            ckpeel;
            rewrite ?Usp, ?EO1, ?EO12, ?E10; repeat (rewrite unsigned_lit_small by lia);
            let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
            first [ apply (mbyte_of_aview SEGS); apply Hkm; lia
                  | try lia; intros _; apply (apresent_writable SEGS); apply HJ5pres; lia
                  | match goal with |- ?G => idtac "KP" G end; fail ]
            | idtac "K-kept"; fail ]
          | specialize (HS5 H2); clear H2 ] end;
        idtac "KC4";
        clear HS'; rewrite <- restrict_mkst_fx in HS5;
        lazymatch type of HS5 with st_ok_pi _ _ ?En _ _ =>
          let HEIn := fresh "HEIn" in
          assert (HEIn : img_env VAL A_LIM En) by (apply img_env_havoc_hi; [assumption | unfold A_LIM; lia]);
          idtac "KC5";
          let SH5 := fresh "SHOKp" in
          first [ assert (SH5 : sh_ok SEGS CBx ck_SH En (mrestrict (w_H W) mem5))
                    by (unfold sh_ok, ck_SH; constructor; [|constructor];
                        apply (shent_ok_of_block SEGS B LAWS ly S W mem5 md5 En CBx 10 r REG_SIZEB 0 288
                                 (proj1 HJ5) Hin);
                        [ unfold CBx; rewrite (U_atom En 32 SBC ltac:(ckatom) ltac:(unfold SBC; lia)); reflexivity
                        | apply (U_atom En 10 r ltac:(ckatom)); lia
                        | lia | change (req_size REG_SIZEB) with 288; lia ])
                | idtac "K-shok"; fail ];
          repeat match goal with
          | H : sh_ok _ _ _ _ _ |- _ => tryif constr_eq H SH5 then fail else clear H
          end;
          repeat match goal with
          | H : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
            tryif constr_eq H HJ5 then fail else clear H
          end
        end
        end
end.
(* the walk to the next head: run to stop, take the calls, the pair and the branches on the way; at stop the
   goal is left at the head *)
Ltac ckb_go stop W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs :=
lazymatch goal with
| HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  paj_run_to_tok RUNTO HS HJ SHOK BspanC stop;
  [ awr_ok_tac; cbn [ew ewset Nat.eqb]; ckpeel; exact Usp | ];
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
  try (lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ =>
         tryif is_var mdx then idtac else (let mdv := fresh "mdv" in set (mdv := mdx) in *; clearbody mdv)
       end);
  lazymatch goal with
  | HS' : st_ok _ _ (setpc _ _) _ |- _ => ckb_memchr W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs; ckb_go stop W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs
  | HS' : st_ok_pi _ _ ?Ez ?ssz _, SHOK' : sh_ok _ ?Bx ?SH _ _ |- _ =>
    let pc := eval vm_compute in (ss_pc ssz) in
    tryif constr_eq pc stop then idtac "AT-HEAD" pc else
    (let K := eval vm_compute in (run_K A_LIM Bx SH ssz) in
     let why := lazymatch paj_tables RUN with
                | (?tpi, ?tw) => psym_why_tok tpi tw K Bx BspanC SH (start K Bx BspanC SH ssz) end in
     lazymatch why with
     | SR_jalr _ => idtac "AT-RET" pc; first [ ckb_ret W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs | idtac "RET-FAIL" pc; fail ]
     | SR_branch _ _ _ =>
       lazymatch pc with
       | 4684 => ckb_pair W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs; ckb_go stop W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs
       | _ =>
         idtac "AT-BR" pc why;
         psrr_branch_tok RUN BR HS' SHOK' BspanC;
         [ first [ solve [ exfalso; ck_norm bs HL; lia ] | ckb_go stop W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs | idtac "BR-T-FAIL" pc; fail ]
         | first [ solve [ exfalso; ck_norm bs HL; lia ] | ckb_go stop W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs | idtac "BR-F-FAIL" pc; fail ] ]
       end
     | _ => idtac "STUCK" pc why; fail
     end)
  end
end.
(* the statement's premises in one hypothesis, so a segment lemma carries them together *)
Definition ckb_ctx (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) (r fabric : Z) (bs : list byte)
(G : list (Z * Z)) : Prop :=
afn_pre SEGS B CHECK_STKB ly S W regs mem md ch /\
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) /\
getr regs 10 = w64 r /\ getr regs 11 = w64 fabric /\
In (r, REG_SIZEB) (ablocks B ly S) /\
(forall i, 0 <= i < REG_SIZEB ->
  aview SEGS (w_H W) mem (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) /\
Boxreg.boxreg_B16 bs /\ Boxreg.bx_fabric bs = fabric /\
img_shadow_vis SEGS B /\ globs_marked SEGS B G /\
absn_rom_bytes SEGS B (VAL (A_OBJ 4)) (map (fun b : byte => bv_unsigned b) Boxreg.zero6) /\ In (VAL (A_OBJ 4), 6) G /\
IMG_LO + 64 <= VAL (A_OBJ 4) /\ VAL (A_OBJ 4) + 6 + 64 <= IMG_HI /\
absn_rom_bytes SEGS B MCH_LOB MCH_CONSTSB.
(* modules the head machinery reads, already loaded through BoxBPaLib / YC1h / YC45 (no header change) *)
Import OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog.PaStep.
Import OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog.BoxBFrame.

(* ---- heads: a state at a loop head over a fixed symbolic state ---- *)
(* the walk's two standing facts at any env it made: the atom map below 45 and the stack pointer *)
Lemma ckb_agree_ewset : forall k0 n E0 E v, (k0 <= n)%nat -> env_agree k0 E0 E -> env_agree k0 E0 (ewset E n v).
Proof.
intros k0 n E0 E v Hn [HA HD]. split;
[intros m Hm; rewrite ew_ewset_other by lia; apply HA; lia | cbn [ed ewset]; exact HD].
Qed.
Ltac ckb_agr H := first [ exact H
| apply env_agree_havoc_ge; [cbv; lia | ckb_agr H]
| apply ckb_agree_ewset; [cbv; lia | ckb_agr H] ].
Ltac ckb_img := first [ assumption
| apply img_env_havoc_hi; [ckb_img | cbv; lia]
| apply img_env_ewset_hi; [ckb_img | cbv; lia] ].
Ltac ckb_ssnorm HSx :=
lazymatch type of HSx with st_ok_pi ?a ?b ?c ?ssx ?d =>
let v := eval vm_compute in ssx in change ssx with v in HSx end.
(* Give the registers of `clob` fresh atoms k, k + 1, ... (as in lib/A/Prog/Check.v ck_reband): a walk uses it
   at a loop head, where the registers the code does not read again still hold the atoms of the last call. *)
Lemma ckb_reband : forall (H : word -> bool) k E ss ms (clob : list (bv 5)),
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
Ltac ckb_reband_at HS k clob :=
lazymatch type of HS with
| st_ok_pi _ _ ?E ?ss (restrict ?H ?ms) =>
let H2 := fresh "HSb" in
pose proof (ckb_reband H k E ss ms clob HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as H2;
clear HS; rename H2 into HS; ckb_ssnorm HS
end.
(* keep only the walk's invariant facts (and no branch conditions) *)
Ltac ckb_setfacts HS fa :=
lazymatch type of HS with st_ok_pi _ _ ?E ?ss ?ms =>
let H2 := fresh "HSf" in
pose proof (st_ok_pi_facts_incl3 E ss ms (f_atoms fa) (f_conds fa) (f_alias fa) HS
ltac:(let v := eval vm_compute in (f_atoms fa) in change (f_atoms fa) with v;
intros x Hx; repeat (destruct Hx as [<- | Hx]; [cbn [ss_facts f_atoms];
repeat (first [left; reflexivity | right])|]); destruct Hx)
ltac:(let v := eval vm_compute in (f_conds fa) in change (f_conds fa) with v; intros x Hx; destruct Hx)
ltac:(let v := eval vm_compute in (f_alias fa) in change (f_alias fa) with v; intros x Hx; destruct Hx)) as H2;
clear HS; rename H2 into HS; ckb_ssnorm HS
end.
Ltac ckb_fit HS ssx :=
let v := eval vm_compute in ssx in
lazymatch type of HS with st_ok_pi _ _ _ ?s _ =>
first [ constr_eq s v | idtac "FIT MISMATCH"; idtac "GOT" s; idtac "WANT" v; fail 1 "ckb_fit" ];
change s with ssx in HS
end.

(* ---- the loop heads in canonical form (measured on the walk of n = 2: wt build-20261029T060206Z) ----
   Registers the code reads again keep the forms the walk gives them (s0 = r, a2 / s8 counters, s1 = b_i + n_i,
   s2 = r + 56 i, s4 = the shadow offset, s5 = 5, s6 = 56 (i + 1), s7 = ~r, s9 = 56 j, s10 = 56 n, s11 = b_i);
   the dead ones get fresh atoms 512 .. (ckb_reband); the frame holds the prologue's thirteen saved words and
   the spills, in the order of their last stores; the facts are the entry's (ck_facts N). *)
Definition CKB_OH_CLOB : list (bv 5) := [1; 5; 6; 7; 9; 10; 11; 13; 14; 15; 16; 17; 18; 19; 24; 25; 27; 28; 29; 30; 31]%bv.
Definition CKB_IH_CLOB : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 19; 28; 29; 30; 31]%bv.
Definition ckb_saved : list YP09.chunk :=
[YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0));
YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0));
YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].
(* spills: 0(sp) and 8(sp) n, 24(sp) the fabric, 32(sp) the inner loop's first row (i + 1), 16(sp) the row
   counter after a row (i + 1) *)
Definition ckb_oh_chunks (i : nat) : list YP09.chunk :=
match i with
| O => [YP09.mkChunk (-144) (CVal 8 (SOff 33 0)); YP09.mkChunk (-112) (CVal 8 (SLit 1));
        YP09.mkChunk (-136) (CVal 8 (SOff 33 0)); YP09.mkChunk (-120) (CVal 8 (SOff 11 0))] ++ ckb_saved
| S _ => [YP09.mkChunk (-112) (CVal 8 (SLit (Z.of_nat i + 1))); YP09.mkChunk (-128) (CVal 8 (SLit (Z.of_nat i)));
          YP09.mkChunk (-144) (CVal 8 (SOff 33 0)); YP09.mkChunk (-136) (CVal 8 (SOff 33 0));
          YP09.mkChunk (-120) (CVal 8 (SOff 11 0))] ++ ckb_saved
end.
Definition ckb_ih_chunks (i : nat) : list YP09.chunk :=
match i with
| O => [YP09.mkChunk (-128) (CVal 8 (SLit 1)); YP09.mkChunk (-144) (CVal 8 (SOff 33 0));
        YP09.mkChunk (-112) (CVal 8 (SLit 1)); YP09.mkChunk (-136) (CVal 8 (SOff 33 0));
        YP09.mkChunk (-120) (CVal 8 (SOff 11 0))] ++ ckb_saved
| S _ => [YP09.mkChunk (-128) (CVal 8 (SLit (Z.of_nat i + 1))); YP09.mkChunk (-112) (CVal 8 (SLit (Z.of_nat i + 1)));
          YP09.mkChunk (-144) (CVal 8 (SOff 33 0)); YP09.mkChunk (-136) (CVal 8 (SOff 33 0));
          YP09.mkChunk (-120) (CVal 8 (SOff 11 0))] ++ ckb_saved
end.
Definition ckb_regions (cs : list YP09.chunk) : smem :=
[YP09.mkRegion (Some 2%nat) (-144) 0 (-144) 0 cs; got_regionP; bcell_regionP 32;
YP09.mkRegion (Some 10%nat) 0 288 0 0 ck_chunks].
Definition ckb_oh_regs (i : nat) : list sv :=
[SLit 0; SOff 512 0; SOff 2 (-144); SOff 3 0; SOff 4 0;
SOff 513 0; SOff 514 0; SOff 515 0; SOff 10 0; SOff 516 0;
SOff 517 0; SOff 518 0; SLit (Z.of_nat i); SOff 519 0; SOff 520 0;
SOff 521 0; SOff 522 0; SOff 523 0; SOff 524 0; SOff 525 0;
SOff 32 0; SLit 5; SLit (56 * (Z.of_nat i + 1)); SAlu ALU_XOR (SOff 10 0) (SLit (-1));
SOff 526 0; SOff 527 0; SMd M_MUL (SOff 33 0) (SLit 56); SOff 528 0;
SOff 529 0; SOff 530 0; SOff 531 0; SOff 532 0].
Definition ckb_ih_regs (i j : nat) : list sv :=
[SLit 0; SOff 512 0; SOff 2 (-144); SOff 3 0; SOff 4 0;
SOff 513 0; SOff 514 0; SOff 515 0; SOff 10 0;
SAluw ALU_ADD (SExt true 32 (SOff (35 + 2 * i) 0)) (SExt true 32 (SOff (36 + 2 * i) 0));
SOff 516 0; SOff 517 0; SOff 518 0; SOff 519 0; SOff 520 0;
SOff 521 0; SOff 522 0; SOff 523 0; SOff 10 (56 * Z.of_nat i); SOff 524 0;
SOff 32 0; SLit 5; SLit (56 * (Z.of_nat i + 1)); SAlu ALU_XOR (SOff 10 0) (SLit (-1));
SLit (Z.of_nat j); SLit (56 * Z.of_nat j); SMd M_MUL (SOff 33 0) (SLit 56);
SExt true 32 (SOff (35 + 2 * i) 0);
SOff 525 0; SOff 526 0; SOff 527 0; SOff 528 0].
(* 0x81108 and 0x811b0 as offsets from the function's first slot (0x7ffac) *)
Definition ssb_oh (N : Z) (i : nat) : sstate :=
mkSS 4444 (ckb_oh_regs i) (ckb_regions (ckb_oh_chunks i)) None (ck_facts N).
Definition ssb_ih (N : Z) (i j : nat) : sstate :=
mkSS 4612 (ckb_ih_regs i j) (ckb_regions (ckb_ih_chunks i)) None (ck_facts N).
(* "from this head the function returns and its post holds" *)
Definition ckb_at (ssx : sstate) (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (r : Z) (bs : list byte) : Prop :=
forall (E : env) (msX : machine_state) (mdX : Model),
img_env VAL A_LIM E ->
st_ok_pi SEGS VAL E ssx (restrict (w_H W) msX) ->
env_agree 45 (Ereg regs (ck_extra bs)) E ->
ajournal SEGS B CHECK_STKB (spZ regs) [] ly S W mem md [] ly S W (ms_mem msX) mdX 0 ->
SRr SEGS W (mkCfg msX mdX) (tbcheck_post regs ly S W mem md r bs).
Definition ckb_oh_prop (N : Z) (i : nat) : Prop :=
forall ly S W regs mem md ch r fabric bs G,
ckb_ctx ly S W regs mem md ch r fabric bs G -> Boxreg.rd4 bs 280 = N ->
ckb_at (ssb_oh N i) ly S W regs mem md r bs.
Definition ckb_ih_prop (N : Z) (i j : nat) : Prop :=
forall ly S W regs mem md ch r fabric bs G,
ckb_ctx ly S W regs mem md ch r fabric bs G -> Boxreg.rd4 bs 280 = N ->
ckb_at (ssb_ih N i j) ly S W regs mem md r bs.
Definition ckb_entry_prop (N : Z) : Prop :=
forall ly S W regs mem md ch r fabric bs G,
ckb_ctx ly S W regs mem md ch r fabric bs G -> Boxreg.rd4 bs 280 = N ->
SRr SEGS W (cfg_at SEGS AB_checkP regs mem md) (tbcheck_post regs ly S W mem md r bs).
Ltac ckb_head_intro :=
try unfold ckb_oh_prop; try unfold ckb_ih_prop; unfold ckb_at;
intros ly S W regs mem md ch r fabric bs G HCTX HNv E msX mdX HEI HS HAG HJ;
pose proof HCTX as HCc;
destruct HCc as (HPRE & HRO & H10 & H11 & Hin & HV & HB16 & HFab & HSV & HGM & HZ & HZG & HZ1 & HZ2 & HMC);
pose proof (pa_wx) as Hwx; pose proof (pa_segs_low) as Hsegs;
pose proof HB16 as (HL & HB1 & HB2 & HB3 & HB4 & HB5 & HB6);
assert (HN : 0 <= Boxreg.rd4 bs 280 <= 5) by exact HB1;
assert (HFb : 1 <= Boxreg.rd4 bs 284 <= 40) by exact HB2;
assert (HFZ : Boxreg.rd4 bs 284 = fabric) by exact HFab;
assert (HNu : ckU bs 280 = Boxreg.rd4 bs 280)
  by (apply (ck_swrap_small (ckU bs 280) (Boxreg.rd4 bs 280) (ckU_range bs 280) ltac:(lia));
      symmetry; apply (ckU_rd4 bs 280); [lia | rewrite HL; lia]);
rewrite HNv in HNu;
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT);
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2);
destruct (al_blocks _ _ LAWS ly S W mem md r REG_SIZEB HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & _ & _);
change (req_size REG_SIZEB) with 288 in Hrceil, Hria;
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5);
assert (WS : CHECK_STKB = 8336) by reflexivity; assert (Hes : ESTACK = 4096) by reflexivity;
pose proof HAG as HAGd; destruct HAGd as [HA45 HD45];
assert (E1 : ew E 1 = getr regs 1) by (rewrite HA45 by lia; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl));
assert (E2 : ew E 2 = getr regs 2) by (rewrite HA45 by lia; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl));
assert (E3 : ew E 3 = getr regs 3) by (rewrite HA45 by lia; exact (ew_Ereg_nat regs _ 3 3%bv eq_refl));
assert (E4 : ew E 4 = getr regs 4) by (rewrite HA45 by lia; exact (ew_Ereg_nat regs _ 4 4%bv eq_refl));
assert (E10 : ew E 10 = Z_to_bv 64 r) by (rewrite HA45 by lia; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10);
assert (E11 : ew E 11 = Z_to_bv 64 fabric) by (rewrite HA45 by lia; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11);
assert (E32 : ew E 32 = Z_to_bv 64 SBC) by (rewrite HA45 by lia; exact (ew_Ereg_extra regs (ck_extra bs) 0));
assert (E33 : ew E 33 = Z_to_bv 64 (ckU bs 280)) by (rewrite HA45 by lia; exact (ew_Ereg_extra regs (ck_extra bs) 1));
assert (E34 : ew E 34 = Z_to_bv 64 (ckU bs 284)) by (rewrite HA45 by lia; exact (ew_Ereg_extra regs (ck_extra bs) 2));
assert (E35 : ew E 35 = Z_to_bv 64 (ckU bs 8)) by (rewrite HA45 by lia; exact (ew_Ereg_extra regs (ck_extra bs) 3));
assert (E36 : ew E 36 = Z_to_bv 64 (ckU bs 12)) by (rewrite HA45 by lia; exact (ew_Ereg_extra regs (ck_extra bs) 4));
assert (E37 : ew E 37 = Z_to_bv 64 (ckU bs 64)) by (rewrite HA45 by lia; exact (ew_Ereg_extra regs (ck_extra bs) 5));
assert (E38 : ew E 38 = Z_to_bv 64 (ckU bs 68)) by (rewrite HA45 by lia; exact (ew_Ereg_extra regs (ck_extra bs) 6));
assert (E39 : ew E 39 = Z_to_bv 64 (ckU bs 120)) by (rewrite HA45 by lia; exact (ew_Ereg_extra regs (ck_extra bs) 7));
assert (E40 : ew E 40 = Z_to_bv 64 (ckU bs 124)) by (rewrite HA45 by lia; exact (ew_Ereg_extra regs (ck_extra bs) 8));
assert (E41 : ew E 41 = Z_to_bv 64 (ckU bs 176)) by (rewrite HA45 by lia; exact (ew_Ereg_extra regs (ck_extra bs) 9));
assert (E42 : ew E 42 = Z_to_bv 64 (ckU bs 180)) by (rewrite HA45 by lia; exact (ew_Ereg_extra regs (ck_extra bs) 10));
assert (E43 : ew E 43 = Z_to_bv 64 (ckU bs 232)) by (rewrite HA45 by lia; exact (ew_Ereg_extra regs (ck_extra bs) 11));
assert (E44 : ew E 44 = Z_to_bv 64 (ckU bs 236)) by (rewrite HA45 by lia; exact (ew_Ereg_extra regs (ck_extra bs) 12));
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity);
assert (HAE : env_agree 32 (Ereg regs (ck_extra bs)) E)
  by (destruct HAG as [HA HD]; split; [intros kk Hkk; apply HA; lia | exact HD]);
assert (SHOK : sh_ok SEGS CBx ck_SH E (mrestrict (w_H W) (ms_mem msX)))
  by (unfold sh_ok, ck_SH; constructor; [|constructor];
      apply (shent_ok_of_block SEGS B LAWS ly S W (ms_mem msX) mdX E CBx 10 r REG_SIZEB 0 288 (proj1 HJ) Hin);
      [ unfold CBx; rewrite (U_atom E 32 SBC ltac:(ckatom) ltac:(unfold SBC; lia)); reflexivity
      | apply (U_atom E 10 r ltac:(ckatom)); lia
      | lia | change (req_size REG_SIZEB) with 288; lia ]);
assert (RB : forall i, 0 <= i < Boxreg.rd4 bs 280 ->
  0 <= Boxreg.rd4 bs (56 * i + 8) /\ 2 <= Boxreg.rd4 bs (56 * i + 12) <= 40 /\
  Z.even (Boxreg.rd4 bs (56 * i + 12)) = true /\
  Boxreg.rd4 bs (56 * i + 12) <= Boxreg.rd4 bs 284 /\
  Boxreg.rd4 bs (56 * i + 8) + Boxreg.rd4 bs (56 * i + 12) <= Boxreg.rd4 bs 284)
  by (intros i Hi; destruct (HB3 i Hi) as (Ha & Hb & Hc0 & Hd & He);
      unfold Boxreg.bx_nch, Boxreg.bx_base, Boxreg.bx_fabric in *;
      repeat split; first [exact Ha | lia]);
try (destruct (RB 0 ltac:(lia)) as (RB0b & RB0c & RB0e & RB0f & RB0s);
  change (56 * 0 + 8) with 8 in RB0b, RB0s; change (56 * 0 + 12) with 12 in RB0c, RB0e, RB0f, RB0s);
try (destruct (RB 1 ltac:(lia)) as (RB1b & RB1c & RB1e & RB1f & RB1s);
  change (56 * 1 + 8) with 64 in RB1b, RB1s; change (56 * 1 + 12) with 68 in RB1c, RB1e, RB1f, RB1s);
try (destruct (RB 2 ltac:(lia)) as (RB2b & RB2c & RB2e & RB2f & RB2s);
  change (56 * 2 + 8) with 120 in RB2b, RB2s; change (56 * 2 + 12) with 124 in RB2c, RB2e, RB2f, RB2s);
try (destruct (RB 3 ltac:(lia)) as (RB3b & RB3c & RB3e & RB3f & RB3s);
  change (56 * 3 + 8) with 176 in RB3b, RB3s; change (56 * 3 + 12) with 180 in RB3c, RB3e, RB3f, RB3s);
try (destruct (RB 4 ltac:(lia)) as (RB4b & RB4c & RB4e & RB4f & RB4s);
  change (56 * 4 + 8) with 232 in RB4b, RB4s; change (56 * 4 + 12) with 236 in RB4c, RB4e, RB4f, RB4s).
(* seat a reached state on a head's canonical state and enter that head's lemma *)
Ltac ckb_seat fa clob ssx NEXT :=
lazymatch goal with
| HS : st_ok_pi _ _ _ _ _ |- _ =>
  ckb_setfacts HS fa; ckb_reband_at HS 4000%nat clob; ckb_reband_at HS 512%nat clob; ckb_fit HS ssx
end;
lazymatch goal with
| HCTX : ckb_ctx ?ly ?S ?W ?regs ?mem ?md ?ch ?r ?fabric ?bs ?G, HNv : Boxreg.rd4 _ 280 = _,
  HAG : env_agree 45 _ _, HSq : st_ok_pi _ _ ?Ef _ _, HJq : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  apply (NEXT ly S W regs mem md ch r fabric bs G HCTX HNv Ef _ _ ltac:(ckb_img) HSq ltac:(ckb_agr HAG) HJq)
end.
(* row 0 of n = 1 *)
Lemma ckb_oh_1_0 : ckb_oh_prop 1 0.
Proof.
ckb_head_intro.
ckb_go 0 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
Qed.

(* row 1 of n = 2 *)
Lemma ckb_oh_2_1 : ckb_oh_prop 2 1.
Proof.
ckb_head_intro.
ckb_go 0 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
Qed.

(* pair (0, 1) of n = 2 *)
Lemma ckb_ih_2_0_1 : ckb_ih_prop 2 0 1.
Proof.
ckb_head_intro.
ckb_go 4684 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_pair W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_go 4444 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_seat (ck_facts 2) CKB_OH_CLOB (ssb_oh 2 1) ckb_oh_2_1.
Qed.

(* row 0 of n = 2 *)
Lemma ckb_oh_2_0 : ckb_oh_prop 2 0.
Proof.
ckb_head_intro.
ckb_go 4612 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_seat (ck_facts 2) CKB_IH_CLOB (ssb_ih 2 0 1) ckb_ih_2_0_1.
Qed.

(* row 2 of n = 3 *)
Lemma ckb_oh_3_2 : ckb_oh_prop 3 2.
Proof.
ckb_head_intro.
ckb_go 0 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
Qed.

(* pair (1, 2) of n = 3 *)
Lemma ckb_ih_3_1_2 : ckb_ih_prop 3 1 2.
Proof.
ckb_head_intro.
ckb_go 4684 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_pair W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_go 4444 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_seat (ck_facts 3) CKB_OH_CLOB (ssb_oh 3 2) ckb_oh_3_2.
Qed.

(* row 1 of n = 3 *)
Lemma ckb_oh_3_1 : ckb_oh_prop 3 1.
Proof.
ckb_head_intro.
ckb_go 4612 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_seat (ck_facts 3) CKB_IH_CLOB (ssb_ih 3 1 2) ckb_ih_3_1_2.
Qed.

(* pair (0, 2) of n = 3 *)
Lemma ckb_ih_3_0_2 : ckb_ih_prop 3 0 2.
Proof.
ckb_head_intro.
ckb_go 4684 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_pair W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_go 4444 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_seat (ck_facts 3) CKB_OH_CLOB (ssb_oh 3 1) ckb_oh_3_1.
Qed.

(* pair (0, 1) of n = 3 *)
Lemma ckb_ih_3_0_1 : ckb_ih_prop 3 0 1.
Proof.
ckb_head_intro.
ckb_go 4684 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_pair W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_go 4612 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_seat (ck_facts 3) CKB_IH_CLOB (ssb_ih 3 0 2) ckb_ih_3_0_2.
Qed.

(* row 0 of n = 3 *)
Lemma ckb_oh_3_0 : ckb_oh_prop 3 0.
Proof.
ckb_head_intro.
ckb_go 4612 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_seat (ck_facts 3) CKB_IH_CLOB (ssb_ih 3 0 1) ckb_ih_3_0_1.
Qed.

(* row 3 of n = 4 *)
Lemma ckb_oh_4_3 : ckb_oh_prop 4 3.
Proof.
ckb_head_intro.
ckb_go 0 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
Qed.

(* pair (2, 3) of n = 4 *)
Lemma ckb_ih_4_2_3 : ckb_ih_prop 4 2 3.
Proof.
ckb_head_intro.
ckb_go 4684 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_pair W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_go 4444 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_seat (ck_facts 4) CKB_OH_CLOB (ssb_oh 4 3) ckb_oh_4_3.
Qed.

(* row 2 of n = 4 *)
Lemma ckb_oh_4_2 : ckb_oh_prop 4 2.
Proof.
ckb_head_intro.
ckb_go 4612 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_seat (ck_facts 4) CKB_IH_CLOB (ssb_ih 4 2 3) ckb_ih_4_2_3.
Qed.

(* pair (1, 3) of n = 4 *)
Lemma ckb_ih_4_1_3 : ckb_ih_prop 4 1 3.
Proof.
ckb_head_intro.
ckb_go 4684 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_pair W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_go 4444 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_seat (ck_facts 4) CKB_OH_CLOB (ssb_oh 4 2) ckb_oh_4_2.
Qed.

(* pair (1, 2) of n = 4 *)
Lemma ckb_ih_4_1_2 : ckb_ih_prop 4 1 2.
Proof.
ckb_head_intro.
ckb_go 4684 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_pair W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_go 4612 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_seat (ck_facts 4) CKB_IH_CLOB (ssb_ih 4 1 3) ckb_ih_4_1_3.
Qed.

(* row 1 of n = 4 *)
Lemma ckb_oh_4_1 : ckb_oh_prop 4 1.
Proof.
ckb_head_intro.
ckb_go 4612 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_seat (ck_facts 4) CKB_IH_CLOB (ssb_ih 4 1 2) ckb_ih_4_1_2.
Qed.

(* pair (0, 3) of n = 4 *)
Lemma ckb_ih_4_0_3 : ckb_ih_prop 4 0 3.
Proof.
ckb_head_intro.
ckb_go 4684 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_pair W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_go 4444 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_seat (ck_facts 4) CKB_OH_CLOB (ssb_oh 4 1) ckb_oh_4_1.
Qed.

(* pair (0, 2) of n = 4 *)
Lemma ckb_ih_4_0_2 : ckb_ih_prop 4 0 2.
Proof.
ckb_head_intro.
ckb_go 4684 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_pair W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_go 4612 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_seat (ck_facts 4) CKB_IH_CLOB (ssb_ih 4 0 3) ckb_ih_4_0_3.
Qed.

(* pair (0, 1) of n = 4 *)
Lemma ckb_ih_4_0_1 : ckb_ih_prop 4 0 1.
Proof.
ckb_head_intro.
ckb_go 4684 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_pair W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_go 4612 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_seat (ck_facts 4) CKB_IH_CLOB (ssb_ih 4 0 2) ckb_ih_4_0_2.
Qed.

(* row 0 of n = 4 *)
Lemma ckb_oh_4_0 : ckb_oh_prop 4 0.
Proof.
ckb_head_intro.
ckb_go 4612 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_seat (ck_facts 4) CKB_IH_CLOB (ssb_ih 4 0 1) ckb_ih_4_0_1.
Qed.

(* row 4 of n = 5 *)
Lemma ckb_oh_5_4 : ckb_oh_prop 5 4.
Proof.
ckb_head_intro.
ckb_go 0 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
Qed.

(* pair (3, 4) of n = 5 *)
Lemma ckb_ih_5_3_4 : ckb_ih_prop 5 3 4.
Proof.
ckb_head_intro.
ckb_go 4684 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_pair W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_go 4444 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_seat (ck_facts 5) CKB_OH_CLOB (ssb_oh 5 4) ckb_oh_5_4.
Qed.

(* row 3 of n = 5 *)
Lemma ckb_oh_5_3 : ckb_oh_prop 5 3.
Proof.
ckb_head_intro.
ckb_go 4612 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_seat (ck_facts 5) CKB_IH_CLOB (ssb_ih 5 3 4) ckb_ih_5_3_4.
Qed.

(* pair (2, 4) of n = 5 *)
Lemma ckb_ih_5_2_4 : ckb_ih_prop 5 2 4.
Proof.
ckb_head_intro.
ckb_go 4684 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_pair W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_go 4444 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_seat (ck_facts 5) CKB_OH_CLOB (ssb_oh 5 3) ckb_oh_5_3.
Qed.

(* pair (2, 3) of n = 5 *)
Lemma ckb_ih_5_2_3 : ckb_ih_prop 5 2 3.
Proof.
ckb_head_intro.
ckb_go 4684 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_pair W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_go 4612 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_seat (ck_facts 5) CKB_IH_CLOB (ssb_ih 5 2 4) ckb_ih_5_2_4.
Qed.

(* row 2 of n = 5 *)
Lemma ckb_oh_5_2 : ckb_oh_prop 5 2.
Proof.
ckb_head_intro.
ckb_go 4612 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_seat (ck_facts 5) CKB_IH_CLOB (ssb_ih 5 2 3) ckb_ih_5_2_3.
Qed.

(* pair (1, 4) of n = 5 *)
Lemma ckb_ih_5_1_4 : ckb_ih_prop 5 1 4.
Proof.
ckb_head_intro.
ckb_go 4684 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_pair W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_go 4444 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_seat (ck_facts 5) CKB_OH_CLOB (ssb_oh 5 2) ckb_oh_5_2.
Qed.

(* pair (1, 3) of n = 5 *)
Lemma ckb_ih_5_1_3 : ckb_ih_prop 5 1 3.
Proof.
ckb_head_intro.
ckb_go 4684 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_pair W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_go 4612 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_seat (ck_facts 5) CKB_IH_CLOB (ssb_ih 5 1 4) ckb_ih_5_1_4.
Qed.

(* pair (1, 2) of n = 5 *)
Lemma ckb_ih_5_1_2 : ckb_ih_prop 5 1 2.
Proof.
ckb_head_intro.
ckb_go 4684 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_pair W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_go 4612 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_seat (ck_facts 5) CKB_IH_CLOB (ssb_ih 5 1 3) ckb_ih_5_1_3.
Qed.

(* row 1 of n = 5 *)
Lemma ckb_oh_5_1 : ckb_oh_prop 5 1.
Proof.
ckb_head_intro.
ckb_go 4612 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_seat (ck_facts 5) CKB_IH_CLOB (ssb_ih 5 1 2) ckb_ih_5_1_2.
Qed.

(* pair (0, 4) of n = 5 *)
Lemma ckb_ih_5_0_4 : ckb_ih_prop 5 0 4.
Proof.
ckb_head_intro.
ckb_go 4684 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_pair W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_go 4444 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_seat (ck_facts 5) CKB_OH_CLOB (ssb_oh 5 1) ckb_oh_5_1.
Qed.

(* pair (0, 3) of n = 5 *)
Lemma ckb_ih_5_0_3 : ckb_ih_prop 5 0 3.
Proof.
ckb_head_intro.
ckb_go 4684 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_pair W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_go 4612 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_seat (ck_facts 5) CKB_IH_CLOB (ssb_ih 5 0 4) ckb_ih_5_0_4.
Qed.

(* pair (0, 2) of n = 5 *)
Lemma ckb_ih_5_0_2 : ckb_ih_prop 5 0 2.
Proof.
ckb_head_intro.
ckb_go 4684 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_pair W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_go 4612 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_seat (ck_facts 5) CKB_IH_CLOB (ssb_ih 5 0 3) ckb_ih_5_0_3.
Qed.

(* pair (0, 1) of n = 5 *)
Lemma ckb_ih_5_0_1 : ckb_ih_prop 5 0 1.
Proof.
ckb_head_intro.
ckb_go 4684 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_pair W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_go 4612 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_seat (ck_facts 5) CKB_IH_CLOB (ssb_ih 5 0 2) ckb_ih_5_0_2.
Qed.

(* row 0 of n = 5 *)
Lemma ckb_oh_5_0 : ckb_oh_prop 5 0.
Proof.
ckb_head_intro.
ckb_go 4612 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_seat (ck_facts 5) CKB_IH_CLOB (ssb_ih 5 0 1) ckb_ih_5_0_1.
Qed.
(* n = 0: from the entry *)
Lemma ckb_entry_0 : ckb_entry_prop 0.
Proof.
unfold ckb_entry_prop.
intros ly S W regs mem md ch r fabric bs G HCTX HNv.
pose proof HCTX as HCc.
destruct HCc as (HPRE & HRO & H10 & H11 & Hin & HV & HB16 & HFab & HSV & HGM & HZ & HZG & HZ1 & HZ2 & HMC).
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
pose proof HB16 as (HL & HB1 & HB2 & HB3 & HB4 & HB5 & HB6).
(* Pau's facts in the engine's form: the struct's fields are rd4's of the byte list. *)
assert (HN : 0 <= Boxreg.rd4 bs 280 <= 5) by exact HB1.
assert (HFb : 1 <= Boxreg.rd4 bs 284 <= 40) by exact HB2.
assert (HFZ : Boxreg.rd4 bs 284 = fabric) by exact HFab.
assert (HNu : ckU bs 280 = Boxreg.rd4 bs 280)
  by (apply (ck_swrap_small (ckU bs 280) (Boxreg.rd4 bs 280) (ckU_range bs 280) ltac:(lia));
      symmetry; apply (ckU_rd4 bs 280); [lia | rewrite HL; lia]).
rewrite HNv in HNu.
destruct (ck_entry ly S W regs mem md ch r _ bs HPRE H10 Hin HL HV HNu ltac:(lia)) as [HS SHOK].
pose proof (ajournal_init SEGS B CHECK_STKB [] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct (al_blocks _ _ LAWS ly S W mem md r REG_SIZEB HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & _ & _).
change (req_size REG_SIZEB) with 288 in Hrceil, Hria.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : CHECK_STKB = 8336) by reflexivity. all: assert (Hes : ESTACK = 4096) by reflexivity.
remember (EC regs bs) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EC; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ck_extra bs)) n)
  by (intros n Hn; subst E; unfold EC; apply Eimg_low; exact Hn).
assert (EX : forall j, (j < 13)%nat -> ew E (32 + j) = nth j (ck_extra bs) (Z_to_bv 64 0))
  by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (E1 : ew E 1 = getr regs 1)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 r)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SBC) by (exact (EX 0%nat ltac:(lia))).
assert (E33 : ew E 33 = Z_to_bv 64 (ckU bs 280)) by (exact (EX 1%nat ltac:(lia))).
assert (E34 : ew E 34 = Z_to_bv 64 (ckU bs 284)) by (exact (EX 2%nat ltac:(lia))).
assert (E35 : ew E 35 = Z_to_bv 64 (ckU bs 8)) by (exact (EX 3%nat ltac:(lia))).
assert (E36 : ew E 36 = Z_to_bv 64 (ckU bs 12)) by (exact (EX 4%nat ltac:(lia))).
assert (E37 : ew E 37 = Z_to_bv 64 (ckU bs 64)) by (exact (EX 5%nat ltac:(lia))).
assert (E38 : ew E 38 = Z_to_bv 64 (ckU bs 68)) by (exact (EX 6%nat ltac:(lia))).
assert (E39 : ew E 39 = Z_to_bv 64 (ckU bs 120)) by (exact (EX 7%nat ltac:(lia))).
assert (E40 : ew E 40 = Z_to_bv 64 (ckU bs 124)) by (exact (EX 8%nat ltac:(lia))).
assert (E41 : ew E 41 = Z_to_bv 64 (ckU bs 176)) by (exact (EX 9%nat ltac:(lia))).
assert (E42 : ew E 42 = Z_to_bv 64 (ckU bs 180)) by (exact (EX 10%nat ltac:(lia))).
assert (E43 : ew E 43 = Z_to_bv 64 (ckU bs 232)) by (exact (EX 11%nat ltac:(lia))).
assert (E44 : ew E 44 = Z_to_bv 64 (ckU bs 236)) by (exact (EX 12%nat ltac:(lia))).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (E11 : ew E 11 = Z_to_bv 64 fabric)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (HAE : env_agree 32 (Ereg regs (ck_extra bs)) E)
  by (split; [intros nn Hnn; rewrite EL by (unfold A_TEXT; lia); reflexivity | subst E; reflexivity]).
assert (HAG : env_agree 45 (Ereg regs (ck_extra bs)) E)
  by (split; [intros nn Hnn; rewrite EL by (unfold A_TEXT; lia); reflexivity | subst E; reflexivity]).
clear HE.
unfold cfg_at, AB_checkP.
change (w64 (BASE + AF_check)) with (Z_to_bv 64 (BASE + AF_check)).
(* The row facts of Pau's B3 for each row the walk reads. *)
assert (RB : forall i, 0 <= i < Boxreg.rd4 bs 280 ->
  0 <= Boxreg.rd4 bs (56 * i + 8) /\ 2 <= Boxreg.rd4 bs (56 * i + 12) <= 40 /\
  Z.even (Boxreg.rd4 bs (56 * i + 12)) = true /\
  Boxreg.rd4 bs (56 * i + 12) <= Boxreg.rd4 bs 284 /\
  Boxreg.rd4 bs (56 * i + 8) + Boxreg.rd4 bs (56 * i + 12) <= Boxreg.rd4 bs 284)
  by (intros i Hi; destruct (HB3 i Hi) as (Ha & Hb & Hc0 & Hd & He);
      unfold Boxreg.bx_nch, Boxreg.bx_base, Boxreg.bx_fabric in *;
      repeat split; first [exact Ha | lia]).
try (destruct (RB 0 ltac:(lia)) as (RB0b & RB0c & RB0e & RB0f & RB0s);
          change (56 * 0 + 8) with 8 in RB0b, RB0s;
          change (56 * 0 + 12) with 12 in RB0c, RB0e, RB0f, RB0s).
try (destruct (RB 1 ltac:(lia)) as (RB1b & RB1c & RB1e & RB1f & RB1s);
          change (56 * 1 + 8) with 64 in RB1b, RB1s;
          change (56 * 1 + 12) with 68 in RB1c, RB1e, RB1f, RB1s).
try (destruct (RB 2 ltac:(lia)) as (RB2b & RB2c & RB2e & RB2f & RB2s);
          change (56 * 2 + 8) with 120 in RB2b, RB2s;
          change (56 * 2 + 12) with 124 in RB2c, RB2e, RB2f, RB2s).
try (destruct (RB 3 ltac:(lia)) as (RB3b & RB3c & RB3e & RB3f & RB3s);
          change (56 * 3 + 8) with 176 in RB3b, RB3s;
          change (56 * 3 + 12) with 180 in RB3c, RB3e, RB3f, RB3s).
try (destruct (RB 4 ltac:(lia)) as (RB4b & RB4c & RB4e & RB4f & RB4s);
          change (56 * 4 + 8) with 232 in RB4b, RB4s;
          change (56 * 4 + 12) with 236 in RB4c, RB4e, RB4f, RB4s).
ckb_go 0 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
Qed.

(* n = 1: from the entry *)
Lemma ckb_entry_1 : ckb_entry_prop 1.
Proof.
unfold ckb_entry_prop.
intros ly S W regs mem md ch r fabric bs G HCTX HNv.
pose proof HCTX as HCc.
destruct HCc as (HPRE & HRO & H10 & H11 & Hin & HV & HB16 & HFab & HSV & HGM & HZ & HZG & HZ1 & HZ2 & HMC).
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
pose proof HB16 as (HL & HB1 & HB2 & HB3 & HB4 & HB5 & HB6).
(* Pau's facts in the engine's form: the struct's fields are rd4's of the byte list. *)
assert (HN : 0 <= Boxreg.rd4 bs 280 <= 5) by exact HB1.
assert (HFb : 1 <= Boxreg.rd4 bs 284 <= 40) by exact HB2.
assert (HFZ : Boxreg.rd4 bs 284 = fabric) by exact HFab.
assert (HNu : ckU bs 280 = Boxreg.rd4 bs 280)
  by (apply (ck_swrap_small (ckU bs 280) (Boxreg.rd4 bs 280) (ckU_range bs 280) ltac:(lia));
      symmetry; apply (ckU_rd4 bs 280); [lia | rewrite HL; lia]).
rewrite HNv in HNu.
destruct (ck_entry ly S W regs mem md ch r _ bs HPRE H10 Hin HL HV HNu ltac:(lia)) as [HS SHOK].
pose proof (ajournal_init SEGS B CHECK_STKB [] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct (al_blocks _ _ LAWS ly S W mem md r REG_SIZEB HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & _ & _).
change (req_size REG_SIZEB) with 288 in Hrceil, Hria.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : CHECK_STKB = 8336) by reflexivity. all: assert (Hes : ESTACK = 4096) by reflexivity.
remember (EC regs bs) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EC; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ck_extra bs)) n)
  by (intros n Hn; subst E; unfold EC; apply Eimg_low; exact Hn).
assert (EX : forall j, (j < 13)%nat -> ew E (32 + j) = nth j (ck_extra bs) (Z_to_bv 64 0))
  by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (E1 : ew E 1 = getr regs 1)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 r)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SBC) by (exact (EX 0%nat ltac:(lia))).
assert (E33 : ew E 33 = Z_to_bv 64 (ckU bs 280)) by (exact (EX 1%nat ltac:(lia))).
assert (E34 : ew E 34 = Z_to_bv 64 (ckU bs 284)) by (exact (EX 2%nat ltac:(lia))).
assert (E35 : ew E 35 = Z_to_bv 64 (ckU bs 8)) by (exact (EX 3%nat ltac:(lia))).
assert (E36 : ew E 36 = Z_to_bv 64 (ckU bs 12)) by (exact (EX 4%nat ltac:(lia))).
assert (E37 : ew E 37 = Z_to_bv 64 (ckU bs 64)) by (exact (EX 5%nat ltac:(lia))).
assert (E38 : ew E 38 = Z_to_bv 64 (ckU bs 68)) by (exact (EX 6%nat ltac:(lia))).
assert (E39 : ew E 39 = Z_to_bv 64 (ckU bs 120)) by (exact (EX 7%nat ltac:(lia))).
assert (E40 : ew E 40 = Z_to_bv 64 (ckU bs 124)) by (exact (EX 8%nat ltac:(lia))).
assert (E41 : ew E 41 = Z_to_bv 64 (ckU bs 176)) by (exact (EX 9%nat ltac:(lia))).
assert (E42 : ew E 42 = Z_to_bv 64 (ckU bs 180)) by (exact (EX 10%nat ltac:(lia))).
assert (E43 : ew E 43 = Z_to_bv 64 (ckU bs 232)) by (exact (EX 11%nat ltac:(lia))).
assert (E44 : ew E 44 = Z_to_bv 64 (ckU bs 236)) by (exact (EX 12%nat ltac:(lia))).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (E11 : ew E 11 = Z_to_bv 64 fabric)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (HAE : env_agree 32 (Ereg regs (ck_extra bs)) E)
  by (split; [intros nn Hnn; rewrite EL by (unfold A_TEXT; lia); reflexivity | subst E; reflexivity]).
assert (HAG : env_agree 45 (Ereg regs (ck_extra bs)) E)
  by (split; [intros nn Hnn; rewrite EL by (unfold A_TEXT; lia); reflexivity | subst E; reflexivity]).
clear HE.
unfold cfg_at, AB_checkP.
change (w64 (BASE + AF_check)) with (Z_to_bv 64 (BASE + AF_check)).
(* The row facts of Pau's B3 for each row the walk reads. *)
assert (RB : forall i, 0 <= i < Boxreg.rd4 bs 280 ->
  0 <= Boxreg.rd4 bs (56 * i + 8) /\ 2 <= Boxreg.rd4 bs (56 * i + 12) <= 40 /\
  Z.even (Boxreg.rd4 bs (56 * i + 12)) = true /\
  Boxreg.rd4 bs (56 * i + 12) <= Boxreg.rd4 bs 284 /\
  Boxreg.rd4 bs (56 * i + 8) + Boxreg.rd4 bs (56 * i + 12) <= Boxreg.rd4 bs 284)
  by (intros i Hi; destruct (HB3 i Hi) as (Ha & Hb & Hc0 & Hd & He);
      unfold Boxreg.bx_nch, Boxreg.bx_base, Boxreg.bx_fabric in *;
      repeat split; first [exact Ha | lia]).
try (destruct (RB 0 ltac:(lia)) as (RB0b & RB0c & RB0e & RB0f & RB0s);
          change (56 * 0 + 8) with 8 in RB0b, RB0s;
          change (56 * 0 + 12) with 12 in RB0c, RB0e, RB0f, RB0s).
try (destruct (RB 1 ltac:(lia)) as (RB1b & RB1c & RB1e & RB1f & RB1s);
          change (56 * 1 + 8) with 64 in RB1b, RB1s;
          change (56 * 1 + 12) with 68 in RB1c, RB1e, RB1f, RB1s).
try (destruct (RB 2 ltac:(lia)) as (RB2b & RB2c & RB2e & RB2f & RB2s);
          change (56 * 2 + 8) with 120 in RB2b, RB2s;
          change (56 * 2 + 12) with 124 in RB2c, RB2e, RB2f, RB2s).
try (destruct (RB 3 ltac:(lia)) as (RB3b & RB3c & RB3e & RB3f & RB3s);
          change (56 * 3 + 8) with 176 in RB3b, RB3s;
          change (56 * 3 + 12) with 180 in RB3c, RB3e, RB3f, RB3s).
try (destruct (RB 4 ltac:(lia)) as (RB4b & RB4c & RB4e & RB4f & RB4s);
          change (56 * 4 + 8) with 232 in RB4b, RB4s;
          change (56 * 4 + 12) with 236 in RB4c, RB4e, RB4f, RB4s).
ckb_go 4444 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_seat (ck_facts 1) CKB_OH_CLOB (ssb_oh 1 0) ckb_oh_1_0.
Qed.

(* n = 2: from the entry *)
Lemma ckb_entry_2 : ckb_entry_prop 2.
Proof.
unfold ckb_entry_prop.
intros ly S W regs mem md ch r fabric bs G HCTX HNv.
pose proof HCTX as HCc.
destruct HCc as (HPRE & HRO & H10 & H11 & Hin & HV & HB16 & HFab & HSV & HGM & HZ & HZG & HZ1 & HZ2 & HMC).
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
pose proof HB16 as (HL & HB1 & HB2 & HB3 & HB4 & HB5 & HB6).
(* Pau's facts in the engine's form: the struct's fields are rd4's of the byte list. *)
assert (HN : 0 <= Boxreg.rd4 bs 280 <= 5) by exact HB1.
assert (HFb : 1 <= Boxreg.rd4 bs 284 <= 40) by exact HB2.
assert (HFZ : Boxreg.rd4 bs 284 = fabric) by exact HFab.
assert (HNu : ckU bs 280 = Boxreg.rd4 bs 280)
  by (apply (ck_swrap_small (ckU bs 280) (Boxreg.rd4 bs 280) (ckU_range bs 280) ltac:(lia));
      symmetry; apply (ckU_rd4 bs 280); [lia | rewrite HL; lia]).
rewrite HNv in HNu.
destruct (ck_entry ly S W regs mem md ch r _ bs HPRE H10 Hin HL HV HNu ltac:(lia)) as [HS SHOK].
pose proof (ajournal_init SEGS B CHECK_STKB [] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct (al_blocks _ _ LAWS ly S W mem md r REG_SIZEB HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & _ & _).
change (req_size REG_SIZEB) with 288 in Hrceil, Hria.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : CHECK_STKB = 8336) by reflexivity. all: assert (Hes : ESTACK = 4096) by reflexivity.
remember (EC regs bs) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EC; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ck_extra bs)) n)
  by (intros n Hn; subst E; unfold EC; apply Eimg_low; exact Hn).
assert (EX : forall j, (j < 13)%nat -> ew E (32 + j) = nth j (ck_extra bs) (Z_to_bv 64 0))
  by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (E1 : ew E 1 = getr regs 1)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 r)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SBC) by (exact (EX 0%nat ltac:(lia))).
assert (E33 : ew E 33 = Z_to_bv 64 (ckU bs 280)) by (exact (EX 1%nat ltac:(lia))).
assert (E34 : ew E 34 = Z_to_bv 64 (ckU bs 284)) by (exact (EX 2%nat ltac:(lia))).
assert (E35 : ew E 35 = Z_to_bv 64 (ckU bs 8)) by (exact (EX 3%nat ltac:(lia))).
assert (E36 : ew E 36 = Z_to_bv 64 (ckU bs 12)) by (exact (EX 4%nat ltac:(lia))).
assert (E37 : ew E 37 = Z_to_bv 64 (ckU bs 64)) by (exact (EX 5%nat ltac:(lia))).
assert (E38 : ew E 38 = Z_to_bv 64 (ckU bs 68)) by (exact (EX 6%nat ltac:(lia))).
assert (E39 : ew E 39 = Z_to_bv 64 (ckU bs 120)) by (exact (EX 7%nat ltac:(lia))).
assert (E40 : ew E 40 = Z_to_bv 64 (ckU bs 124)) by (exact (EX 8%nat ltac:(lia))).
assert (E41 : ew E 41 = Z_to_bv 64 (ckU bs 176)) by (exact (EX 9%nat ltac:(lia))).
assert (E42 : ew E 42 = Z_to_bv 64 (ckU bs 180)) by (exact (EX 10%nat ltac:(lia))).
assert (E43 : ew E 43 = Z_to_bv 64 (ckU bs 232)) by (exact (EX 11%nat ltac:(lia))).
assert (E44 : ew E 44 = Z_to_bv 64 (ckU bs 236)) by (exact (EX 12%nat ltac:(lia))).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (E11 : ew E 11 = Z_to_bv 64 fabric)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (HAE : env_agree 32 (Ereg regs (ck_extra bs)) E)
  by (split; [intros nn Hnn; rewrite EL by (unfold A_TEXT; lia); reflexivity | subst E; reflexivity]).
assert (HAG : env_agree 45 (Ereg regs (ck_extra bs)) E)
  by (split; [intros nn Hnn; rewrite EL by (unfold A_TEXT; lia); reflexivity | subst E; reflexivity]).
clear HE.
unfold cfg_at, AB_checkP.
change (w64 (BASE + AF_check)) with (Z_to_bv 64 (BASE + AF_check)).
(* The row facts of Pau's B3 for each row the walk reads. *)
assert (RB : forall i, 0 <= i < Boxreg.rd4 bs 280 ->
  0 <= Boxreg.rd4 bs (56 * i + 8) /\ 2 <= Boxreg.rd4 bs (56 * i + 12) <= 40 /\
  Z.even (Boxreg.rd4 bs (56 * i + 12)) = true /\
  Boxreg.rd4 bs (56 * i + 12) <= Boxreg.rd4 bs 284 /\
  Boxreg.rd4 bs (56 * i + 8) + Boxreg.rd4 bs (56 * i + 12) <= Boxreg.rd4 bs 284)
  by (intros i Hi; destruct (HB3 i Hi) as (Ha & Hb & Hc0 & Hd & He);
      unfold Boxreg.bx_nch, Boxreg.bx_base, Boxreg.bx_fabric in *;
      repeat split; first [exact Ha | lia]).
try (destruct (RB 0 ltac:(lia)) as (RB0b & RB0c & RB0e & RB0f & RB0s);
          change (56 * 0 + 8) with 8 in RB0b, RB0s;
          change (56 * 0 + 12) with 12 in RB0c, RB0e, RB0f, RB0s).
try (destruct (RB 1 ltac:(lia)) as (RB1b & RB1c & RB1e & RB1f & RB1s);
          change (56 * 1 + 8) with 64 in RB1b, RB1s;
          change (56 * 1 + 12) with 68 in RB1c, RB1e, RB1f, RB1s).
try (destruct (RB 2 ltac:(lia)) as (RB2b & RB2c & RB2e & RB2f & RB2s);
          change (56 * 2 + 8) with 120 in RB2b, RB2s;
          change (56 * 2 + 12) with 124 in RB2c, RB2e, RB2f, RB2s).
try (destruct (RB 3 ltac:(lia)) as (RB3b & RB3c & RB3e & RB3f & RB3s);
          change (56 * 3 + 8) with 176 in RB3b, RB3s;
          change (56 * 3 + 12) with 180 in RB3c, RB3e, RB3f, RB3s).
try (destruct (RB 4 ltac:(lia)) as (RB4b & RB4c & RB4e & RB4f & RB4s);
          change (56 * 4 + 8) with 232 in RB4b, RB4s;
          change (56 * 4 + 12) with 236 in RB4c, RB4e, RB4f, RB4s).
ckb_go 4444 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_seat (ck_facts 2) CKB_OH_CLOB (ssb_oh 2 0) ckb_oh_2_0.
Qed.

(* n = 3: from the entry *)
Lemma ckb_entry_3 : ckb_entry_prop 3.
Proof.
unfold ckb_entry_prop.
intros ly S W regs mem md ch r fabric bs G HCTX HNv.
pose proof HCTX as HCc.
destruct HCc as (HPRE & HRO & H10 & H11 & Hin & HV & HB16 & HFab & HSV & HGM & HZ & HZG & HZ1 & HZ2 & HMC).
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
pose proof HB16 as (HL & HB1 & HB2 & HB3 & HB4 & HB5 & HB6).
(* Pau's facts in the engine's form: the struct's fields are rd4's of the byte list. *)
assert (HN : 0 <= Boxreg.rd4 bs 280 <= 5) by exact HB1.
assert (HFb : 1 <= Boxreg.rd4 bs 284 <= 40) by exact HB2.
assert (HFZ : Boxreg.rd4 bs 284 = fabric) by exact HFab.
assert (HNu : ckU bs 280 = Boxreg.rd4 bs 280)
  by (apply (ck_swrap_small (ckU bs 280) (Boxreg.rd4 bs 280) (ckU_range bs 280) ltac:(lia));
      symmetry; apply (ckU_rd4 bs 280); [lia | rewrite HL; lia]).
rewrite HNv in HNu.
destruct (ck_entry ly S W regs mem md ch r _ bs HPRE H10 Hin HL HV HNu ltac:(lia)) as [HS SHOK].
pose proof (ajournal_init SEGS B CHECK_STKB [] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct (al_blocks _ _ LAWS ly S W mem md r REG_SIZEB HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & _ & _).
change (req_size REG_SIZEB) with 288 in Hrceil, Hria.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : CHECK_STKB = 8336) by reflexivity. all: assert (Hes : ESTACK = 4096) by reflexivity.
remember (EC regs bs) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EC; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ck_extra bs)) n)
  by (intros n Hn; subst E; unfold EC; apply Eimg_low; exact Hn).
assert (EX : forall j, (j < 13)%nat -> ew E (32 + j) = nth j (ck_extra bs) (Z_to_bv 64 0))
  by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (E1 : ew E 1 = getr regs 1)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 r)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SBC) by (exact (EX 0%nat ltac:(lia))).
assert (E33 : ew E 33 = Z_to_bv 64 (ckU bs 280)) by (exact (EX 1%nat ltac:(lia))).
assert (E34 : ew E 34 = Z_to_bv 64 (ckU bs 284)) by (exact (EX 2%nat ltac:(lia))).
assert (E35 : ew E 35 = Z_to_bv 64 (ckU bs 8)) by (exact (EX 3%nat ltac:(lia))).
assert (E36 : ew E 36 = Z_to_bv 64 (ckU bs 12)) by (exact (EX 4%nat ltac:(lia))).
assert (E37 : ew E 37 = Z_to_bv 64 (ckU bs 64)) by (exact (EX 5%nat ltac:(lia))).
assert (E38 : ew E 38 = Z_to_bv 64 (ckU bs 68)) by (exact (EX 6%nat ltac:(lia))).
assert (E39 : ew E 39 = Z_to_bv 64 (ckU bs 120)) by (exact (EX 7%nat ltac:(lia))).
assert (E40 : ew E 40 = Z_to_bv 64 (ckU bs 124)) by (exact (EX 8%nat ltac:(lia))).
assert (E41 : ew E 41 = Z_to_bv 64 (ckU bs 176)) by (exact (EX 9%nat ltac:(lia))).
assert (E42 : ew E 42 = Z_to_bv 64 (ckU bs 180)) by (exact (EX 10%nat ltac:(lia))).
assert (E43 : ew E 43 = Z_to_bv 64 (ckU bs 232)) by (exact (EX 11%nat ltac:(lia))).
assert (E44 : ew E 44 = Z_to_bv 64 (ckU bs 236)) by (exact (EX 12%nat ltac:(lia))).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (E11 : ew E 11 = Z_to_bv 64 fabric)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (HAE : env_agree 32 (Ereg regs (ck_extra bs)) E)
  by (split; [intros nn Hnn; rewrite EL by (unfold A_TEXT; lia); reflexivity | subst E; reflexivity]).
assert (HAG : env_agree 45 (Ereg regs (ck_extra bs)) E)
  by (split; [intros nn Hnn; rewrite EL by (unfold A_TEXT; lia); reflexivity | subst E; reflexivity]).
clear HE.
unfold cfg_at, AB_checkP.
change (w64 (BASE + AF_check)) with (Z_to_bv 64 (BASE + AF_check)).
(* The row facts of Pau's B3 for each row the walk reads. *)
assert (RB : forall i, 0 <= i < Boxreg.rd4 bs 280 ->
  0 <= Boxreg.rd4 bs (56 * i + 8) /\ 2 <= Boxreg.rd4 bs (56 * i + 12) <= 40 /\
  Z.even (Boxreg.rd4 bs (56 * i + 12)) = true /\
  Boxreg.rd4 bs (56 * i + 12) <= Boxreg.rd4 bs 284 /\
  Boxreg.rd4 bs (56 * i + 8) + Boxreg.rd4 bs (56 * i + 12) <= Boxreg.rd4 bs 284)
  by (intros i Hi; destruct (HB3 i Hi) as (Ha & Hb & Hc0 & Hd & He);
      unfold Boxreg.bx_nch, Boxreg.bx_base, Boxreg.bx_fabric in *;
      repeat split; first [exact Ha | lia]).
try (destruct (RB 0 ltac:(lia)) as (RB0b & RB0c & RB0e & RB0f & RB0s);
          change (56 * 0 + 8) with 8 in RB0b, RB0s;
          change (56 * 0 + 12) with 12 in RB0c, RB0e, RB0f, RB0s).
try (destruct (RB 1 ltac:(lia)) as (RB1b & RB1c & RB1e & RB1f & RB1s);
          change (56 * 1 + 8) with 64 in RB1b, RB1s;
          change (56 * 1 + 12) with 68 in RB1c, RB1e, RB1f, RB1s).
try (destruct (RB 2 ltac:(lia)) as (RB2b & RB2c & RB2e & RB2f & RB2s);
          change (56 * 2 + 8) with 120 in RB2b, RB2s;
          change (56 * 2 + 12) with 124 in RB2c, RB2e, RB2f, RB2s).
try (destruct (RB 3 ltac:(lia)) as (RB3b & RB3c & RB3e & RB3f & RB3s);
          change (56 * 3 + 8) with 176 in RB3b, RB3s;
          change (56 * 3 + 12) with 180 in RB3c, RB3e, RB3f, RB3s).
try (destruct (RB 4 ltac:(lia)) as (RB4b & RB4c & RB4e & RB4f & RB4s);
          change (56 * 4 + 8) with 232 in RB4b, RB4s;
          change (56 * 4 + 12) with 236 in RB4c, RB4e, RB4f, RB4s).
ckb_go 4444 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_seat (ck_facts 3) CKB_OH_CLOB (ssb_oh 3 0) ckb_oh_3_0.
Qed.

(* n = 4: from the entry *)
Lemma ckb_entry_4 : ckb_entry_prop 4.
Proof.
unfold ckb_entry_prop.
intros ly S W regs mem md ch r fabric bs G HCTX HNv.
pose proof HCTX as HCc.
destruct HCc as (HPRE & HRO & H10 & H11 & Hin & HV & HB16 & HFab & HSV & HGM & HZ & HZG & HZ1 & HZ2 & HMC).
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
pose proof HB16 as (HL & HB1 & HB2 & HB3 & HB4 & HB5 & HB6).
(* Pau's facts in the engine's form: the struct's fields are rd4's of the byte list. *)
assert (HN : 0 <= Boxreg.rd4 bs 280 <= 5) by exact HB1.
assert (HFb : 1 <= Boxreg.rd4 bs 284 <= 40) by exact HB2.
assert (HFZ : Boxreg.rd4 bs 284 = fabric) by exact HFab.
assert (HNu : ckU bs 280 = Boxreg.rd4 bs 280)
  by (apply (ck_swrap_small (ckU bs 280) (Boxreg.rd4 bs 280) (ckU_range bs 280) ltac:(lia));
      symmetry; apply (ckU_rd4 bs 280); [lia | rewrite HL; lia]).
rewrite HNv in HNu.
destruct (ck_entry ly S W regs mem md ch r _ bs HPRE H10 Hin HL HV HNu ltac:(lia)) as [HS SHOK].
pose proof (ajournal_init SEGS B CHECK_STKB [] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct (al_blocks _ _ LAWS ly S W mem md r REG_SIZEB HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & _ & _).
change (req_size REG_SIZEB) with 288 in Hrceil, Hria.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : CHECK_STKB = 8336) by reflexivity. all: assert (Hes : ESTACK = 4096) by reflexivity.
remember (EC regs bs) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EC; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ck_extra bs)) n)
  by (intros n Hn; subst E; unfold EC; apply Eimg_low; exact Hn).
assert (EX : forall j, (j < 13)%nat -> ew E (32 + j) = nth j (ck_extra bs) (Z_to_bv 64 0))
  by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (E1 : ew E 1 = getr regs 1)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 r)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SBC) by (exact (EX 0%nat ltac:(lia))).
assert (E33 : ew E 33 = Z_to_bv 64 (ckU bs 280)) by (exact (EX 1%nat ltac:(lia))).
assert (E34 : ew E 34 = Z_to_bv 64 (ckU bs 284)) by (exact (EX 2%nat ltac:(lia))).
assert (E35 : ew E 35 = Z_to_bv 64 (ckU bs 8)) by (exact (EX 3%nat ltac:(lia))).
assert (E36 : ew E 36 = Z_to_bv 64 (ckU bs 12)) by (exact (EX 4%nat ltac:(lia))).
assert (E37 : ew E 37 = Z_to_bv 64 (ckU bs 64)) by (exact (EX 5%nat ltac:(lia))).
assert (E38 : ew E 38 = Z_to_bv 64 (ckU bs 68)) by (exact (EX 6%nat ltac:(lia))).
assert (E39 : ew E 39 = Z_to_bv 64 (ckU bs 120)) by (exact (EX 7%nat ltac:(lia))).
assert (E40 : ew E 40 = Z_to_bv 64 (ckU bs 124)) by (exact (EX 8%nat ltac:(lia))).
assert (E41 : ew E 41 = Z_to_bv 64 (ckU bs 176)) by (exact (EX 9%nat ltac:(lia))).
assert (E42 : ew E 42 = Z_to_bv 64 (ckU bs 180)) by (exact (EX 10%nat ltac:(lia))).
assert (E43 : ew E 43 = Z_to_bv 64 (ckU bs 232)) by (exact (EX 11%nat ltac:(lia))).
assert (E44 : ew E 44 = Z_to_bv 64 (ckU bs 236)) by (exact (EX 12%nat ltac:(lia))).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (E11 : ew E 11 = Z_to_bv 64 fabric)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (HAE : env_agree 32 (Ereg regs (ck_extra bs)) E)
  by (split; [intros nn Hnn; rewrite EL by (unfold A_TEXT; lia); reflexivity | subst E; reflexivity]).
assert (HAG : env_agree 45 (Ereg regs (ck_extra bs)) E)
  by (split; [intros nn Hnn; rewrite EL by (unfold A_TEXT; lia); reflexivity | subst E; reflexivity]).
clear HE.
unfold cfg_at, AB_checkP.
change (w64 (BASE + AF_check)) with (Z_to_bv 64 (BASE + AF_check)).
(* The row facts of Pau's B3 for each row the walk reads. *)
assert (RB : forall i, 0 <= i < Boxreg.rd4 bs 280 ->
  0 <= Boxreg.rd4 bs (56 * i + 8) /\ 2 <= Boxreg.rd4 bs (56 * i + 12) <= 40 /\
  Z.even (Boxreg.rd4 bs (56 * i + 12)) = true /\
  Boxreg.rd4 bs (56 * i + 12) <= Boxreg.rd4 bs 284 /\
  Boxreg.rd4 bs (56 * i + 8) + Boxreg.rd4 bs (56 * i + 12) <= Boxreg.rd4 bs 284)
  by (intros i Hi; destruct (HB3 i Hi) as (Ha & Hb & Hc0 & Hd & He);
      unfold Boxreg.bx_nch, Boxreg.bx_base, Boxreg.bx_fabric in *;
      repeat split; first [exact Ha | lia]).
try (destruct (RB 0 ltac:(lia)) as (RB0b & RB0c & RB0e & RB0f & RB0s);
          change (56 * 0 + 8) with 8 in RB0b, RB0s;
          change (56 * 0 + 12) with 12 in RB0c, RB0e, RB0f, RB0s).
try (destruct (RB 1 ltac:(lia)) as (RB1b & RB1c & RB1e & RB1f & RB1s);
          change (56 * 1 + 8) with 64 in RB1b, RB1s;
          change (56 * 1 + 12) with 68 in RB1c, RB1e, RB1f, RB1s).
try (destruct (RB 2 ltac:(lia)) as (RB2b & RB2c & RB2e & RB2f & RB2s);
          change (56 * 2 + 8) with 120 in RB2b, RB2s;
          change (56 * 2 + 12) with 124 in RB2c, RB2e, RB2f, RB2s).
try (destruct (RB 3 ltac:(lia)) as (RB3b & RB3c & RB3e & RB3f & RB3s);
          change (56 * 3 + 8) with 176 in RB3b, RB3s;
          change (56 * 3 + 12) with 180 in RB3c, RB3e, RB3f, RB3s).
try (destruct (RB 4 ltac:(lia)) as (RB4b & RB4c & RB4e & RB4f & RB4s);
          change (56 * 4 + 8) with 232 in RB4b, RB4s;
          change (56 * 4 + 12) with 236 in RB4c, RB4e, RB4f, RB4s).
ckb_go 4444 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_seat (ck_facts 4) CKB_OH_CLOB (ssb_oh 4 0) ckb_oh_4_0.
Qed.

(* n = 5: from the entry *)
Lemma ckb_entry_5 : ckb_entry_prop 5.
Proof.
unfold ckb_entry_prop.
intros ly S W regs mem md ch r fabric bs G HCTX HNv.
pose proof HCTX as HCc.
destruct HCc as (HPRE & HRO & H10 & H11 & Hin & HV & HB16 & HFab & HSV & HGM & HZ & HZG & HZ1 & HZ2 & HMC).
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
pose proof HB16 as (HL & HB1 & HB2 & HB3 & HB4 & HB5 & HB6).
(* Pau's facts in the engine's form: the struct's fields are rd4's of the byte list. *)
assert (HN : 0 <= Boxreg.rd4 bs 280 <= 5) by exact HB1.
assert (HFb : 1 <= Boxreg.rd4 bs 284 <= 40) by exact HB2.
assert (HFZ : Boxreg.rd4 bs 284 = fabric) by exact HFab.
assert (HNu : ckU bs 280 = Boxreg.rd4 bs 280)
  by (apply (ck_swrap_small (ckU bs 280) (Boxreg.rd4 bs 280) (ckU_range bs 280) ltac:(lia));
      symmetry; apply (ckU_rd4 bs 280); [lia | rewrite HL; lia]).
rewrite HNv in HNu.
destruct (ck_entry ly S W regs mem md ch r _ bs HPRE H10 Hin HL HV HNu ltac:(lia)) as [HS SHOK].
pose proof (ajournal_init SEGS B CHECK_STKB [] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct (al_blocks _ _ LAWS ly S W mem md r REG_SIZEB HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & _ & _).
change (req_size REG_SIZEB) with 288 in Hrceil, Hria.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : CHECK_STKB = 8336) by reflexivity. all: assert (Hes : ESTACK = 4096) by reflexivity.
remember (EC regs bs) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EC; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ck_extra bs)) n)
  by (intros n Hn; subst E; unfold EC; apply Eimg_low; exact Hn).
assert (EX : forall j, (j < 13)%nat -> ew E (32 + j) = nth j (ck_extra bs) (Z_to_bv 64 0))
  by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (E1 : ew E 1 = getr regs 1)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 r)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SBC) by (exact (EX 0%nat ltac:(lia))).
assert (E33 : ew E 33 = Z_to_bv 64 (ckU bs 280)) by (exact (EX 1%nat ltac:(lia))).
assert (E34 : ew E 34 = Z_to_bv 64 (ckU bs 284)) by (exact (EX 2%nat ltac:(lia))).
assert (E35 : ew E 35 = Z_to_bv 64 (ckU bs 8)) by (exact (EX 3%nat ltac:(lia))).
assert (E36 : ew E 36 = Z_to_bv 64 (ckU bs 12)) by (exact (EX 4%nat ltac:(lia))).
assert (E37 : ew E 37 = Z_to_bv 64 (ckU bs 64)) by (exact (EX 5%nat ltac:(lia))).
assert (E38 : ew E 38 = Z_to_bv 64 (ckU bs 68)) by (exact (EX 6%nat ltac:(lia))).
assert (E39 : ew E 39 = Z_to_bv 64 (ckU bs 120)) by (exact (EX 7%nat ltac:(lia))).
assert (E40 : ew E 40 = Z_to_bv 64 (ckU bs 124)) by (exact (EX 8%nat ltac:(lia))).
assert (E41 : ew E 41 = Z_to_bv 64 (ckU bs 176)) by (exact (EX 9%nat ltac:(lia))).
assert (E42 : ew E 42 = Z_to_bv 64 (ckU bs 180)) by (exact (EX 10%nat ltac:(lia))).
assert (E43 : ew E 43 = Z_to_bv 64 (ckU bs 232)) by (exact (EX 11%nat ltac:(lia))).
assert (E44 : ew E 44 = Z_to_bv 64 (ckU bs 236)) by (exact (EX 12%nat ltac:(lia))).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (E11 : ew E 11 = Z_to_bv 64 fabric)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (HAE : env_agree 32 (Ereg regs (ck_extra bs)) E)
  by (split; [intros nn Hnn; rewrite EL by (unfold A_TEXT; lia); reflexivity | subst E; reflexivity]).
assert (HAG : env_agree 45 (Ereg regs (ck_extra bs)) E)
  by (split; [intros nn Hnn; rewrite EL by (unfold A_TEXT; lia); reflexivity | subst E; reflexivity]).
clear HE.
unfold cfg_at, AB_checkP.
change (w64 (BASE + AF_check)) with (Z_to_bv 64 (BASE + AF_check)).
(* The row facts of Pau's B3 for each row the walk reads. *)
assert (RB : forall i, 0 <= i < Boxreg.rd4 bs 280 ->
  0 <= Boxreg.rd4 bs (56 * i + 8) /\ 2 <= Boxreg.rd4 bs (56 * i + 12) <= 40 /\
  Z.even (Boxreg.rd4 bs (56 * i + 12)) = true /\
  Boxreg.rd4 bs (56 * i + 12) <= Boxreg.rd4 bs 284 /\
  Boxreg.rd4 bs (56 * i + 8) + Boxreg.rd4 bs (56 * i + 12) <= Boxreg.rd4 bs 284)
  by (intros i Hi; destruct (HB3 i Hi) as (Ha & Hb & Hc0 & Hd & He);
      unfold Boxreg.bx_nch, Boxreg.bx_base, Boxreg.bx_fabric in *;
      repeat split; first [exact Ha | lia]).
try (destruct (RB 0 ltac:(lia)) as (RB0b & RB0c & RB0e & RB0f & RB0s);
          change (56 * 0 + 8) with 8 in RB0b, RB0s;
          change (56 * 0 + 12) with 12 in RB0c, RB0e, RB0f, RB0s).
try (destruct (RB 1 ltac:(lia)) as (RB1b & RB1c & RB1e & RB1f & RB1s);
          change (56 * 1 + 8) with 64 in RB1b, RB1s;
          change (56 * 1 + 12) with 68 in RB1c, RB1e, RB1f, RB1s).
try (destruct (RB 2 ltac:(lia)) as (RB2b & RB2c & RB2e & RB2f & RB2s);
          change (56 * 2 + 8) with 120 in RB2b, RB2s;
          change (56 * 2 + 12) with 124 in RB2c, RB2e, RB2f, RB2s).
try (destruct (RB 3 ltac:(lia)) as (RB3b & RB3c & RB3e & RB3f & RB3s);
          change (56 * 3 + 8) with 176 in RB3b, RB3s;
          change (56 * 3 + 12) with 180 in RB3c, RB3e, RB3f, RB3s).
try (destruct (RB 4 ltac:(lia)) as (RB4b & RB4c & RB4e & RB4f & RB4s);
          change (56 * 4 + 8) with 232 in RB4b, RB4s;
          change (56 * 4 + 12) with 236 in RB4c, RB4e, RB4f, RB4s).
ckb_go 4444 W ly S regs mem md r bs G E E1 E3 E4 E10 Hra HAE Hin HV HRO HMC HL HB4 HB5 HB6 HZ HSV HGM HZG HZ1 HZ2 Hgp Htp HEI Usp Hsegs.
ckb_seat (ck_facts 5) CKB_OH_CLOB (ssb_oh 5 0) ckb_oh_5_0.
Qed.
Theorem pb_bcheck : tbcheck_spec.
Proof.
unfold tbcheck_spec.
intros ly S W regs mem md ch r fabric bs G HPRE HRO H10 H11 Hin HV HB16 HFab HSV HGM HZ HZG HZ1 HZ2 HMC.
assert (HCTX : ckb_ctx ly S W regs mem md ch r fabric bs G)
  by (unfold ckb_ctx; repeat (split; [assumption|]); assumption).
pose proof HB16 as (HL & HB1 & _).
assert (HN : 0 <= Boxreg.rd4 bs 280 <= 5) by exact HB1.
assert (HNcase : Boxreg.rd4 bs 280 = 0 \/ Boxreg.rd4 bs 280 = 1 \/ Boxreg.rd4 bs 280 = 2 \/
                 Boxreg.rd4 bs 280 = 3 \/ Boxreg.rd4 bs 280 = 4 \/ Boxreg.rd4 bs 280 = 5) by lia.
destruct HNcase as [HNv | [HNv | [HNv | [HNv | [HNv | HNv]]]]].
- exact (ckb_entry_0 ly S W regs mem md ch r fabric bs G HCTX HNv).
- exact (ckb_entry_1 ly S W regs mem md ch r fabric bs G HCTX HNv).
- exact (ckb_entry_2 ly S W regs mem md ch r fabric bs G HCTX HNv).
- exact (ckb_entry_3 ly S W regs mem md ch r fabric bs G HCTX HNv).
- exact (ckb_entry_4 ly S W regs mem md ch r fabric bs G HCTX HNv).
- exact (ckb_entry_5 ly S W regs mem md ch r fabric bs G HCTX HNv).
Qed.
End h.
End f.
End d.
