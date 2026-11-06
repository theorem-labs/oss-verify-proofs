(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8q.v:156-158;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbk.v:76-79; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203, 287-290,
   358-363, for libreac/fuzz_identity's asan-ubsan build (lib/B). The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8h.v:75-78, 95-98, 104-107. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_family_of.v, with its module paths and numbers changed; 2241 of its 2331 lines of code are new or changed and 757 lines of the source are left out. *)
(* reac_boxreg_declare (fuzz_boxreg.asan 0x817a0, 173 instructions): the contract of the ASan build's code.
   The function takes a 96-byte frame on the machine stack (addi sp,sp,-96; ra, s0..s9 saved there). It refuses
   (returns -1, writes nothing) unless k (a1, an int) is even and 2..40 (addiw a1,-41 / bltu -39, andi 1), the
   fabric word at r + 284 is at least k and the count n at r + 280 is at most 4 (each word read after its shadow
   byte is checked). With b0 (a3) >= 0 it refuses when fabric - k < b0, then scans rows 0 .. n-1 (base at
   r + 56i + 8, nch at r + 56i + 12, shadow-checked) and refuses on an overlap; with b0 < 0 it calls
   lowest_free_base (r, k) (0x818e8) and refuses on a negative result. Then, at row = r + 56 n, it calls
   __asan_memset (row, 0, 56) (0x81918), stores base (+8), nch (+12) and pinned = (b0 >= 0) (+20) after their
   shadow checks, calls snprintf (row + 24, 32, "%s", name) through __interceptor_trampoline_snprintf (0x81984)
   when name (a2) is not NULL, re-reads n and stores n + 1, and returns the old n. It writes nothing outside the
   288-byte registry struct at r (a heap block of the caller), its own frame and the wrappers' stack below it.
   Layout: the registry struct is 288 bytes: rows 0..280 (5 rows of 56 bytes: mac 0..5, base +8, nch +12,
   established +16, pinned +20, name +24..+55), n at +280, fabric at +284.
   Hazard (snprintf): the snprintf wrapper's contract is lib/A/Rt/SnprintfDef.v asnprintf_realizes (statement only,
   not yet proved); the proof takes it at pa_sigma BS___interceptor_trampoline_snprintf. Its measured stack need is
   8160 bytes, more than one ESTACK, so the stack below the call's sp is 2 * ESTACK and
   REAC_BOXREG_DECLARE_STK = own frame 96 + max (LOWEST_FREE_BASE_STK, 2 * ESTACK); __asan_memset needs only
   ESTACK. The snprintf post lets f10 and fcsr change (a Theorem Labs lane's A/Prog/vsnprintf_wrap_c.v 88-100, and a Theorem Labs lane's
   shared post 401616133a7 FMsnprintfShared.v:142-145), so since 82db7cf8c7c asnprintf_realizes returns at some fx'
   and this function's post is apost_baseF's: f registers equal except f10, fcsr the entry's or rounding mode 0.
   Format strings (.rodata): 0x20d40 "%s" (bytes 25 73 00) is the listing's A_OBJ 10, built by the auipc/addi
   pair at 0x81974 / 0x81978 (A_declare_fmtP). 0x20d60 (A_OBJ 11) is "" (one 00 byte), reac_boxreg_set_name's
   empty-string argument; this function never reads it (it skips snprintf when name is NULL). The wrapper's own
   .rodata reads (musl's vfprintf tables, e.g. the "-+   0X0x" prefix at 0x10b54) come under asn_rom_kept.
   How each premise of asnprintf_realizes holds at the call (0x81984), which comes after __asan_memset and, when
   b0 < 0, after lowest_free_base. An ajournal carries an image byte only when it is neither an owned static nor an
   errno byte (lib/Reusable/YCbq.v:362) and carries no byte below alloc_ceiling outside the blocks (:358), so the
   image's shadow and a heap chunk's tail are not carried; the premises are therefore stated so that each one either
   holds in every state or is carried:
   - asn_rom_kept (the contract's read-only view, lib/A/Rt/SnprintfDef.v): arodata_okP on the read-only segments;
     arodata_okP is carried by every journal (lib/A/Prog/BoxBase.v arodata_ok_journalP) and by memset's post.
   - "%s" bytes: asn_rom_bytes (state-free: read-only image bytes that are no owned static and no errno byte),
     read through asn_rom_kept at the call.
   - "%s" shadow: globs_marked G with In (A_declare_fmtP, 3) G (range_addressable) and img_shadow_vis with the
     64-byte margins (shadow_hull_vis), lib/A/Prog/BoxRo.v ro_read_ok_glob; both hold in every AR state.
   - "%s" 0 < f, amem_range, apart from the window and from the destination: from the margins, alloc_ceiling below
     the stack, and AR_client_img_law (a heap byte is no image byte).
   - name bytes s ++ [0]: inside the name's heap block, which every journal keeps (YCbq.v:360-361, callee FP = [])
     and the function's own writes miss (the registry block is apart from it; memset keeps all else).
   - name shadow and hull: AR_shadow_law for the name's block (every AR state); amem_range from AR_blocks_law.
   - the rest of the NUL's 8-byte word: inside the block, or past its requested size, which asn_blk_tail_vis makes
     readable in every AR state (the block starts on a 16-byte boundary, so the word ends by nm + round_up nn 8).
   - destination: the 32-byte name field r + 56 n + 24 of the registry block (n <= 4 from boxreg_inv).
   The __asan_report_load4 / store4 branches (0x819d4 .. 0x81a50) are refuted by the shadow of the registry block.
   Image difference: the asan-ubsan build (lib/B/Prog/BoxBReacBoxregDeclare.v) adds the UBSan checks (r null and
   alignment, fabric - k overflow, n < 6, pointer overflow, n + 1 overflow; their traps are unimp), calls
   range_taken (r, b0, k) instead of the inline row scan, and re-reads n after its callee.
   The memory model is Pau's plain one (lib/Prog/reac_boxreg_declare_c.v declare_refused, declare_placed,
   decl_row; lib/Prog/BoxregUpd.v new_row_bytes, the same bytes as decl_bytes), used as it is. The name premise
   follows lib/Prog/reac_boxreg_set_name_c.v name_ok: NULL with s = [], or a heap block holding s and its NUL. *)
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
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import LowestFreeBase ReacBoxregInit BoxRo.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require Import SnprintfDef.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK0j YP00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaStep BoxPaLib YC1g YC1h.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require lowest_free_base_c printf_facts_c.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Mem Bytes PropExec.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YO0f.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg BoxregUpd reac_boxreg_declare_c.
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
(* The function's address in the image, the address of its format string "%s" (A_OBJ 10, 0x20d40 in
   fuzz_boxreg.asan), and the stack it needs: its own 96-byte frame and below it the deeper of lowest_free_base's
   stack and the 2 * ESTACK of the snprintf wrapper (the memset wrapper needs ESTACK). *)
Definition A_reac_boxreg_declareP : Z := BASE + AF_reac_boxreg_declare.
Definition A_declare_fmtP : Z := VAL (A_OBJ 10).
Definition REAC_BOXREG_DECLARE_STK : Z := 96 + Z.max LOWEST_FREE_BASE_STK (2 * ESTACK).
Section h.
Variable B : asyms.
(* The registry block's bytes as Pau's byte list. *)
Definition tdecl_reg_bytes (W : world SEGS) (mem : word -> option byte) (r : Z) (bs : list byte) : Prop :=
forall i, 0 <= i < REG_SIZE ->
  aview SEGS (w_H W) mem (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0))).
(* The name argument (reac_boxreg_set_name_c.v name_ok, restated over the heap blocks): NULL with s = [], or
   the first byte of a heap block, apart from the registry block, that holds the characters s (none 0) and a NUL.
   The rest of the NUL's 8-byte word and the shadow are not stated here: AR and asn_blk_tail_vis give them in every
   state, so also at the snprintf call after lowest_free_base. *)
Definition tdecl_name_ok (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte) (r nm : Z)
  (s : list Z) : Prop :=
(nm = 0 /\ s = []) \/
(nm <> 0 /\ Forall (fun c => 0 < c < 256) s /\ Z.of_nat (length s) + 8 < 2 ^ 31 /\
 exists nn, In (nm, nn) (ablocks B ly S) /\ Z.of_nat (length s) + 1 <= nn /\
 (nm + nn <= r \/ r + REG_SIZE <= nm) /\
 (forall i, 0 <= i <= Z.of_nat (length s) ->
   aview SEGS (w_H W) mem (nm + i) = Some (nth (Z.to_nat i) (s ++ [0]) 0))).
Definition treac_boxreg_declare_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md (r k b0 : Z)
  (bs : list byte) (s : list Z) : world SEGS -> config -> Prop :=
apost_baseF SEGS B REAC_BOXREG_DECLARE_STK [(r, r + REG_SIZE)] regs ly S W mem md 0
(fun ly' S' W' regs' mem' md' =>
ly' = ly /\ S' = S /\ W' = W /\ Permutation (ablocks B ly' S') (ablocks B ly S) /\
((reac_boxreg_declare_c.declare_refused bs k b0 /\ getr regs' 10 = w64 (-1) /\ tdecl_reg_bytes W' mem' r bs) \/
 (exists b p, reac_boxreg_declare_c.declare_placed bs k b0 b p /\
   getr regs' 10 = w64 (Boxreg.bx_n bs) /\
   tdecl_reg_bytes W' mem' r (BoxregUpd.new_row_bytes bs (reac_boxreg_declare_c.decl_row b k p s))))).
Definition treac_boxreg_declare_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (r k nm b0 : Z) (bs : list byte) (s : list Z) (G : list (Z * Z)),
afn_pre SEGS B REAC_BOXREG_DECLARE_STK ly S W regs mem md ch ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
getr regs 10 = w64 r -> getr regs 11 = w64 k -> getr regs 12 = w64 nm -> getr regs 13 = w64 b0 ->
-2 ^ 31 <= k < 2 ^ 31 -> -2 ^ 31 <= b0 < 2 ^ 31 ->
In (r, REG_SIZE) (ablocks B ly S) -> tdecl_reg_bytes W mem r bs -> Boxreg.boxreg_inv bs ->
tdecl_name_ok ly S W mem r nm s ->
(* facts of the image and of the runtime's symbols, true in every state *)
asn_blk_tail_vis SEGS B -> img_shadow_vis SEGS B -> globs_marked SEGS B G ->
(* the format "%s": bytes of the read-only image, a registered global *)
asn_rom_bytes SEGS B A_declare_fmtP ASN_FMT -> In (A_declare_fmtP, 3) G ->
IMG_LO + 64 <= A_declare_fmtP -> A_declare_fmtP + 3 + 64 <= IMG_HI ->
(* R2 (a Theorem Labs lane 15:05Z): the format below the image's GOT canary slot, which the snprintf contract now asks (P2) *)
A_declare_fmtP + 3 <= 0x99b40 ->
(* the rounding mode at entry, which this function hands to the snprintf wrapper (SnprintfDef.v) *)
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
SRr SEGS W (cfg_at SEGS A_reac_boxreg_declareP regs mem md)
  (treac_boxreg_declare_post regs ly S W mem md r k b0 bs s).
(* ---------------------------------------------------------------------------------------------------------- *)
(* The walk of reac_boxreg_declare (fuzz_boxreg.asan 0x817a0).
   It is split at two points of the code, so that the paths the symbolic engine follows stay few:
   - dl_walk: the head of the inlined range_taken loop (0x81878, row i), for any i < n; by induction on n - i;
   - dp_walk: the placement (0x8190c, after s5 = r + 56 n), for either choice of base (b0 or lowest_free_base's z):
     __asan_memset of the row (aj_intrin_at), the three stores, and the snprintf of the name through one local lemma
     (dpl_snprintf_at) whose premises are asnprintf_realizes's at the call and whose continuation takes the FP state
     fx3 the wrapper returns at (a Theorem Labs lane's srr_fx_continue, relocated to lib/A/Rt/FMsnprintfSx.v); the rest, 0x81988
     to the return, runs at fx3 (no instruction there touches an f register or fcsr), so apost_baseF takes fx3;
   pb_reac_boxreg_declare walks from the entry to the refusals, through the call of lowest_free_base (aj_call with
   tlowest_free_base_spec at pa_sigma_lowest_free_base), to the loop head (row 0) and to the placement.
   At both split points the machine state is described at the machine level (dinv: the journal from the entry,
   the frame with the 11 saved registers, the unchanged registry block and the registers the rest reads), and
   each piece starts the symbolic engine afresh. Every __asan_report_* branch is refuted by the engine's shadow
   entries: the registry block (and a row of it) is addressable by the block law of AR (dshent_block). *)
(* a Theorem Labs lane's continuation lemma srr_fx_continue, relocated (lib/A/Rt/FMsnprintfSx.v, from
   a working branch ad235a56db0 proofs/omx-clap-core/fuzz_manifest/lib/A/FMsnprintfSx.v); cited
   qualified at the snprintf call. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require FMsnprintfSx.
(* amem8_of_block (lib/A/Rt/SnprintfAmem.v): the name's amem_range over |s| + 8 bytes (R2's P3) from its heap
   block; cited qualified at the snprintf call. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require SnprintfAmem.
#[local] Notation SIGMA := (@pa_sigma _ box_listing PI).
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA BS___asan_memset).
Hypothesis ASNPRINTF : asnprintf_realizes SEGS B (SIGMA BS___interceptor_trampoline_snprintf).
Hypothesis LFB : tlowest_free_base_spec B.
Let HBgot := pal_got_shadow B TL.
Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_box) (PI := PI).

(* The shadow base and the span of shadow addresses the engine may read. *)
Definition DSB : Z := 0x7fff8000.
Definition DBx : sv := SOff 32 0.
Definition Dspan : Z * Z := (DSB, DSB + 2 ^ 44 - 1).
Definition DSTK : Z := REAC_BOXREG_DECLARE_STK.
Lemma DSTK_val : DSTK = 8288.
Proof. reflexivity. Qed.

(* ---- branch conditions as integer facts ---- *)
Lemma dU_of_S : forall E v, U E v = Sg E v mod 2 ^ 64.
Proof.
intros E v. unfold U, Sg. rewrite unsigned_is_wrap_signed. unfold bv_wrap, bv_modulus. reflexivity.
Qed.
Lemma dS_atom : forall E n v c, ew E n = Z_to_bv 64 v -> - 2 ^ 63 <= v -> v + c < 2 ^ 63 -> - 2 ^ 63 <= v + c ->
Sg E (SOff n c) = v + c.
Proof.
intros E n v c H H1 H2 H3. rewrite S_SOff, H, Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). change (2 ^ 64 / 2) with (2 ^ 63).
rewrite <- Z.add_assoc, Zplus_mod_idemp_l, Z.add_assoc. rewrite Z.mod_small by lia. lia.
Qed.
Lemma dS_lit : forall E z, - 2 ^ 63 <= z < 2 ^ 63 -> Sg E (SLit z) = z.
Proof.
intros E z Hz. rewrite S_SLit. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). change (2 ^ 64 / 2) with (2 ^ 63). rewrite Z.mod_small by lia. lia.
Qed.
Lemma dbr_lt : forall E a b, branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (Sg E a <? Sg E b).
Proof. intros E a b. reflexivity. Qed.
Lemma dbr_ge : forall E a b, branch_taken BC_GE (sv_denot E a) (sv_denot E b) = negb (Sg E a <? Sg E b).
Proof. intros E a b. reflexivity. Qed.
Lemma dswrap32 : forall z, bv_swrap 32 z = (z + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31.
Proof. intros z. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. reflexivity. Qed.
Lemma dswrap32_small : forall z, - 2 ^ 31 <= z < 2 ^ 31 -> bv_swrap 32 z = z.
Proof. intros z Hz. rewrite dswrap32. rewrite Z.mod_small by lia. lia. Qed.
Lemma dmod32_of_64 : forall z, (z mod 2 ^ 64) mod 2 ^ 32 = z mod 2 ^ 32.
Proof.
intros z. change (2 ^ 64) with (2 ^ 32 * 2 ^ 32). rewrite Z.rem_mul_r by lia.
rewrite Z.mul_comm, Z_mod_plus_full. apply Z.mod_mod. lia.
Qed.
Lemma dmodsum : forall x y c M, 0 < M -> ((x mod M + y mod M) + c) mod M = (x + y + c) mod M.
Proof. intros x y c M HM. rewrite <- (Zplus_mod_idemp_l (x mod M + y mod M)), <- Zplus_mod, Zplus_mod_idemp_l. reflexivity. Qed.
Lemma dmoddif : forall x y c M, 0 < M -> ((x mod M - y mod M) + c) mod M = (x - y + c) mod M.
Proof. intros x y c M HM. rewrite <- (Zplus_mod_idemp_l (x mod M - y mod M)), <- Zminus_mod, Zplus_mod_idemp_l. reflexivity. Qed.
(* 0x817e4  bltu (k - 41)_32, -39 : taken (refuse) unless 2 <= k <= 40 *)
Lemma dc_kw : forall E k, ew E 11 = Z_to_bv 64 k -> - 2 ^ 31 <= k < 2 ^ 31 ->
branch_taken BC_LTU (sv_denot E (SAluw ALU_ADD (SOff 11 0) (SLit (-41)))) (sv_denot E (SLit 18446744073709551577)) =
negb ((2 <=? k) && (k <=? 40)).
Proof.
intros E k Hk Hr. rewrite branch_ltu_U, U_lit by lia. rewrite dU_of_S, S_SAluw. cbn [zalu_raw].
rewrite U_SOff, U_SLit, Hk, Z_to_bv_unsigned, Z.add_0_r. unfold zcanon, M64, bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_mod by lia. rewrite !dmod32_of_64.
assert (E1 : bv_swrap 32 (k mod 2 ^ 32 + -41 mod 2 ^ 32) = bv_swrap 32 (k - 41)).
{ rewrite !dswrap32, dmodsum by lia. replace (k + -41 + 2 ^ 31) with (k - 41 + 2 ^ 31) by lia. reflexivity. }
rewrite E1. rewrite dswrap32.
destruct (Z_lt_dec (k - 41) (- 2 ^ 31)) as [Hw | Hw].
- replace ((k - 41 + 2 ^ 31) mod 2 ^ 32) with (k - 41 + 2 ^ 31 + 2 ^ 32) by (apply Z.mod_unique with (-1); lia).
  rewrite Z.mod_small by lia. replace (2 <=? k) with false by (symmetry; apply Z.leb_gt; lia). cbn [andb negb].
  apply Z.ltb_lt. lia.
- rewrite (Z.mod_small (k - 41 + 2 ^ 31)) by lia. replace (k - 41 + 2 ^ 31 - 2 ^ 31) with (k - 41) by lia.
  destruct (Z.leb_spec 2 k); destruct (Z.leb_spec k 40); cbn [andb negb].
  + replace ((k - 41) mod 2 ^ 64) with (k - 41 + 2 ^ 64) by (apply Z.mod_unique with (-1); lia).
    apply Z.ltb_ge. lia.
  + rewrite Z.mod_small by lia. apply Z.ltb_lt. lia.
  + replace ((k - 41) mod 2 ^ 64) with (k - 41 + 2 ^ 64) by (apply Z.mod_unique with (-1); lia).
    apply Z.ltb_lt. lia.
  + lia.
Qed.
(* 0x817ec  bnez k & 1 *)
Lemma dc_kodd : forall E k, ew E 11 = Z_to_bv 64 k -> - 2 ^ 31 <= k < 2 ^ 31 ->
branch_taken BC_NE (sv_denot E (SAlu ALU_AND (SOff 11 0) (SLit 1))) (sv_denot E (SLit 0)) = Z.odd k.
Proof.
intros E k Hk Hr. rewrite branch_ne_U, U_and_lit, U_lit by lia. rewrite U_SOff, Hk, Z_to_bv_unsigned, Z.add_0_r.
unfold zcanon, M64, bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_mod by lia.
pose proof (Z.land_ones (k mod 2 ^ 64) 1 ltac:(lia)) as HL. change (Z.ones 1) with 1 in HL. change (2 ^ 1) with 2 in HL. rewrite HL.
assert (H2 : (k mod 2 ^ 64) mod 2 = k mod 2).
{ change (2 ^ 64) with (2 * 2 ^ 63). rewrite Z.rem_mul_r by lia. rewrite Z.mul_comm, Z_mod_plus_full. apply Z.mod_mod. lia. }
rewrite H2. rewrite Zmod_odd. destruct (Z.odd k); reflexivity.
Qed.
(* signed comparisons of small atoms / literals *)
Lemma dc_lt : forall E a b x y, Sg E a = x -> Sg E b = y -> branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (x <? y).
Proof. intros E a b x y Ha Hb. rewrite dbr_lt, Ha, Hb. reflexivity. Qed.
Lemma dc_ge : forall E a b x y, Sg E a = x -> Sg E b = y -> branch_taken BC_GE (sv_denot E a) (sv_denot E b) = negb (x <? y).
Proof. intros E a b x y Ha Hb. rewrite dbr_ge, Ha, Hb. reflexivity. Qed.
Lemma dS_aluw_sub : forall E a b x y, Sg E a = x -> Sg E b = y -> - 2 ^ 31 <= x - y < 2 ^ 31 ->
Sg E (SAluw ALU_SUB a b) = x - y.
Proof.
intros E a b x y Ha Hb Hr. rewrite S_SAluw. cbn [zalu_raw]. rewrite !dU_of_S, Ha, Hb. rewrite !dmod32_of_64.
rewrite dswrap32, dmoddif by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma dS_aluw_add : forall E a b x y, Sg E a = x -> Sg E b = y -> - 2 ^ 31 <= x + y < 2 ^ 31 ->
Sg E (SAluw ALU_ADD a b) = x + y.
Proof.
intros E a b x y Ha Hb Hr. rewrite S_SAluw. cbn [zalu_raw]. rewrite !dU_of_S, Ha, Hb. rewrite !dmod32_of_64.
rewrite dswrap32, dmodsum by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma dS_alu_add : forall E a b x y, Sg E a = x -> Sg E b = y -> - 2 ^ 63 <= x + y < 2 ^ 63 ->
Sg E (SAlu ALU_ADD a b) = x + y.
Proof.
intros E a b x y Ha Hb Hr. rewrite S_SAlu. cbn [zalu_raw]. rewrite !dU_of_S, Ha, Hb.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). change (2 ^ 64 / 2) with (2 ^ 63).
rewrite dmodsum by lia. rewrite Z.mod_small by lia. lia.
Qed.

(* ---- address-free model facts (Pau's plain model, lib/Prog) ---- *)

(* ---------- byte helpers ---------- *)

Lemma dm_Z_to_bv8_mod : forall x, Z_to_bv 8 (x mod 256) = Z_to_bv 8 x.
Proof.
  intros x. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  apply Z.mod_mod. lia.
Qed.

Lemma dm_nth_Z_to_le_bytes : forall n z j, (j < n)%nat ->
  nth j (Z_to_le_bytes n z) (Z_to_bv 8 0) = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat j)).
Proof.
  induction n as [|n IH]; intros z j Hj; [lia|].
  destruct j as [|j]; cbn [Z_to_le_bytes nth].
  - replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r. reflexivity.
  - rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.

Lemma dm_le4_nth : forall (w : bv 64) j, 0 <= j < 4 ->
  nth (Z.to_nat j) (Mem.le4 w) (Z_to_bv 8 0) = YP09.byte_of_word w j.
Proof.
  intros w j Hj. unfold Mem.le4, YP09.byte_of_word. rewrite dm_nth_Z_to_le_bytes by lia.
  rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma dm_byte_of_word_0 : forall j, bv_unsigned (YP09.byte_of_word (Z_to_bv 64 0) j) = 0.
Proof.
  intros j. unfold YP09.byte_of_word. rewrite !Z_to_bv_unsigned.
  change (bv_wrap 64 0) with 0. rewrite Z.shiftr_0_l. reflexivity.
Qed.

Lemma dm_le_bytes_roundtrip : forall l : list byte, Z_to_le_bytes (length l) (bytes_le_to_Z l) = l.
Proof.
  induction l as [|b l IH]; [reflexivity|].
  cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2 ^ Z.of_N 8) with 256 in Hb.
  pose proof (PropExec.bytes_le_to_Z_nonneg l) as Hl.
  rewrite Bytes.lor_shiftl8_add by lia.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
    Z.div_mod_to_equations. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace ((bv_unsigned b + 256 * bytes_le_to_Z l) / 256) with (bytes_le_to_Z l); [exact IH|].
    Z.div_mod_to_equations. lia.
Qed.

Lemma dm_swrap32_nonneg : forall z, 0 <= z < 2 ^ 32 -> 0 <= bv_swrap 32 z -> bv_swrap 32 z = z.
Proof.
  intros z Hz H. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in H |- *.
  change (2 ^ Z.of_N 32) with (2 ^ 32) in H |- *. change (2 ^ 32 / 2) with (2 ^ 31) in H |- *.
  Z.div_mod_to_equations. lia.
Qed.

(* ---------- M1: the bytes of a non-negative registry word ---------- *)

Lemma dm_rd4_byte : forall (bs : list byte) (o : Z) (j : nat), length bs = 288%nat -> 0 <= o -> o + 4 <= 288 ->
  0 <= Boxreg.rd4 bs o -> (j < 4)%nat ->
  nth (Z.to_nat (o + Z.of_nat j)) bs (Z_to_bv 8 0) = Z_to_bv 8 (YO0f.le_byte (Boxreg.rd4 bs o) 4 j).
Proof.
  intros bs o j HL Ho Ho4 Hr Hj.
  assert (Hlen : length (Boxreg.bsub bs o 4) = 4%nat) by (apply Boxreg.bsub_length; lia).
  pose proof (Boxreg.le4_range _ Hlen) as Hz.
  assert (E : Boxreg.rd4 bs o = bytes_le_to_Z (Boxreg.bsub bs o 4)).
  { unfold Boxreg.rd4 in Hr |- *. apply dm_swrap32_nonneg; assumption. }
  assert (N : nth (Z.to_nat (o + Z.of_nat j)) bs (Z_to_bv 8 0) = nth j (Boxreg.bsub bs o 4) (Z_to_bv 8 0)).
  { symmetry. apply nth_error_nth. rewrite BoxregUpd.nth_bsub by lia.
    destruct (Nat.ltb_spec j (Z.to_nat 4)) as [Hj4|Hj4]; [|lia].
    replace (Z.to_nat o + j)%nat with (Z.to_nat (o + Z.of_nat j)) by lia.
    apply nth_error_nth'. lia. }
  rewrite N. rewrite <- (dm_le_bytes_roundtrip (Boxreg.bsub bs o 4)) at 1. rewrite Hlen.
  rewrite dm_nth_Z_to_le_bytes by lia. rewrite E. unfold YO0f.le_byte.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite (Z.mod_small (bytes_le_to_Z (Boxreg.bsub bs o 4))) by lia.
  rewrite dm_Z_to_bv8_mod. reflexivity.
Qed.

Lemma dm_rd4_byte_u : forall (bs : list byte) (o : Z) (j : nat), length bs = 288%nat -> 0 <= o -> o + 4 <= 288 ->
  0 <= Boxreg.rd4 bs o -> (j < 4)%nat ->
  bv_unsigned (nth (Z.to_nat (o + Z.of_nat j)) bs (Z_to_bv 8 0)) = YO0f.le_byte (Boxreg.rd4 bs o) 4 j.
Proof.
  intros bs o j HL Ho Ho4 Hr Hj. rewrite dm_rd4_byte by assumption.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  unfold YO0f.le_byte. apply Z.mod_mod. lia.
Qed.

(* ---------- M2: the decisions ---------- *)

Lemma dm_refused_width : forall bs k b0, ~ (2 <= k <= 40) -> reac_boxreg_declare_c.declare_refused bs k b0.
Proof. intros bs k b0 H. left. intros (_ & Hk & _). exact (H Hk). Qed.

Lemma dm_refused_odd : forall bs k b0, Z.odd k = true -> reac_boxreg_declare_c.declare_refused bs k b0.
Proof.
  intros bs k b0 H. left. intros (He & _ & _). rewrite <- Z.negb_odd, H in He. discriminate.
Qed.

Lemma dm_refused_fabric : forall bs k b0, Boxreg.bx_fabric bs < k -> reac_boxreg_declare_c.declare_refused bs k b0.
Proof. intros bs k b0 H. left. intros (_ & _ & Hf). lia. Qed.

Lemma dm_refused_full : forall bs k b0, 4 < Boxreg.bx_n bs -> reac_boxreg_declare_c.declare_refused bs k b0.
Proof. intros bs k b0 H. right. left. lia. Qed.

Lemma dm_refused_room : forall bs k b0, 0 <= b0 -> Boxreg.bx_fabric bs - k < b0 ->
  reac_boxreg_declare_c.declare_refused bs k b0.
Proof. intros bs k b0 H0 H. right. right. left. split; [exact H0|]. intros (_ & Hr & _). lia. Qed.

Lemma dm_refused_overlap : forall bs k b0, 0 <= b0 ->
  (exists i, 0 <= i < Boxreg.bx_n bs /\ Boxreg.meets b0 k (Boxreg.bx_base bs i) (Boxreg.bx_nch bs i)) ->
  reac_boxreg_declare_c.declare_refused bs k b0.
Proof.
  intros bs k b0 H0 H. right. right. left. split; [exact H0|]. intros (_ & _ & Hm). exact (Hm H).
Qed.

Lemma dm_refused_nofree : forall bs k b0 z, b0 < 0 -> lowest_free_base_c.lowest_free bs k z -> z < 0 ->
  reac_boxreg_declare_c.declare_refused bs k b0.
Proof.
  intros bs k b0 z Hb Hl Hz. right. right. right. split; [exact Hb|].
  destruct Hl as [(-> & H) | (H & _)]; [|lia]. left. split; [reflexivity | exact H].
Qed.

Lemma dm_placed_pinned : forall bs k b0, 2 <= k <= 40 -> Z.even k = true -> k <= Boxreg.bx_fabric bs ->
  0 <= Boxreg.bx_n bs <= 4 -> 0 <= b0 -> b0 + k <= Boxreg.bx_fabric bs ->
  (forall i, 0 <= i < Boxreg.bx_n bs -> ~ Boxreg.meets b0 k (Boxreg.bx_base bs i) (Boxreg.bx_nch bs i)) ->
  reac_boxreg_declare_c.declare_placed bs k b0 b0 1.
Proof.
  intros bs k b0 Hk He Hf Hn Hb Hbk Hm.
  split; [split; [exact He | split; [exact Hk | exact Hf]]|]. split; [lia|].
  left. split; [exact Hb|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact Hb|]. split; [exact Hbk|]. intros (i & Hi & Hmi). exact (Hm i Hi Hmi).
Qed.

Lemma dm_placed_free : forall bs k b0 z, 2 <= k <= 40 -> Z.even k = true -> k <= Boxreg.bx_fabric bs ->
  0 <= Boxreg.bx_n bs <= 4 -> b0 < 0 -> lowest_free_base_c.lowest_free bs k z -> 0 <= z ->
  reac_boxreg_declare_c.declare_placed bs k b0 z 0.
Proof.
  intros bs k b0 z Hk He Hf Hn Hb Hl Hz.
  split; [split; [exact He | split; [exact Hk | exact Hf]]|]. split; [lia|].
  right. split; [exact Hb|]. split; [reflexivity|]. split; [exact Hz | exact Hl].
Qed.

Lemma dm_lowest_free_range : forall bs k z, 1 <= k -> lowest_free_base_c.lowest_free bs k z ->
  z = -1 \/ (0 <= z /\ z + k <= Boxreg.bx_fabric bs).
Proof. intros bs k z Hk [(-> & _) | (H0 & H1 & _)]; [left; reflexivity | right; lia]. Qed.

Lemma dm_boxreg_inv_facts : forall bs, Boxreg.boxreg_inv bs ->
  length bs = 288%nat /\ 0 <= Boxreg.bx_n bs <= 5 /\ 1 <= Boxreg.bx_fabric bs <= 40 /\
  (forall i, 0 <= i < Boxreg.bx_n bs -> 0 <= Boxreg.bx_base bs i <= 38 /\ 2 <= Boxreg.bx_nch bs i <= 40 /\
     Boxreg.bx_base bs i + Boxreg.bx_nch bs i <= 40).
Proof.
  intros bs ((HL & H1 & H2 & H3 & _) & _).
  split; [exact HL|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. exact (Boxreg.B3_bounds bs i H2 H3 Hi).
Qed.

(* ---------- M3: the final bytes of the placed case ---------- *)

Lemma dm_name_field_length : forall s, length (reac_boxreg_declare_c.name_field s) = 32%nat.
Proof.
  intros s. unfold reac_boxreg_declare_c.name_field, printf_facts_c.pf_bytes.
  rewrite length_app, length_map, repeat_length, length_firstn. lia.
Qed.

Lemma dm_decl_row_length : forall b k p s, length (reac_boxreg_declare_c.decl_row b k p s) = 56%nat.
Proof.
  intros b k p s. unfold reac_boxreg_declare_c.decl_row.
  rewrite !length_app, repeat_length, !Mem.length_le4, dm_name_field_length. reflexivity.
Qed.

Lemma dm_new_row_nth : forall (bs row : list byte) (i : Z), length bs = 288%nat -> 0 <= Boxreg.bx_n bs <= 4 ->
  length row = 56%nat -> 0 <= i < 288 ->
  nth (Z.to_nat i) (BoxregUpd.new_row_bytes bs row) (Z_to_bv 8 0) =
  if (280 <=? i) && (i <? 284) then nth (Z.to_nat (i - 280)) (Mem.le4 (Z_to_bv 64 (Boxreg.bx_n bs + 1))) (Z_to_bv 8 0)
  else if (56 * Boxreg.bx_n bs <=? i) && (i <? 56 * Boxreg.bx_n bs + 56)
  then nth (Z.to_nat (i - 56 * Boxreg.bx_n bs)) row (Z_to_bv 8 0)
  else nth (Z.to_nat i) bs (Z_to_bv 8 0).
Proof.
  intros bs row i HL Hn HR Hi. unfold BoxregUpd.new_row_bytes.
  assert (L1 : length (Mem.upd_bytes bs (Z.to_nat (56 * Boxreg.bx_n bs)) row) = 288%nat)
    by (rewrite Mem.upd_bytes_length; lia).
  apply nth_error_nth.
  rewrite Mem.upd_bytes_nth by (rewrite ?Mem.length_le4; lia).
  rewrite Mem.upd_bytes_nth by lia.
  rewrite Mem.length_le4.
  destruct (Nat.leb_spec 280 (Z.to_nat i)); destruct (Nat.ltb_spec (Z.to_nat i) (280 + 4));
    destruct (Z.leb_spec 280 i); destruct (Z.ltb_spec i 284); cbn [andb]; try (exfalso; lia).
  all: try (destruct (Nat.leb_spec (Z.to_nat (56 * Boxreg.bx_n bs)) (Z.to_nat i));
      destruct (Nat.ltb_spec (Z.to_nat i) (Z.to_nat (56 * Boxreg.bx_n bs) + length row));
      destruct (Z.leb_spec (56 * Boxreg.bx_n bs) i); destruct (Z.ltb_spec i (56 * Boxreg.bx_n bs + 56));
      cbn [andb]; try (exfalso; lia)).
  all: match goal with
       | |- nth_error ?l ?a = Some (nth ?c ?l ?d) =>
           replace a with c by lia; apply nth_error_nth'; rewrite ?Mem.length_le4; lia
       end.
Qed.

Lemma dm_nth_map_bv8 : forall (l : list Z) n,
  nth n (map (Z_to_bv 8) l) (Z_to_bv 8 0) = Z_to_bv 8 (nth n l 0).
Proof.
  induction l as [|x l IH]; intros [|n]; cbn [map nth]; try reflexivity. apply IH.
Qed.

Lemma dm_name_field_lo : forall s q, Forall (fun c => 0 < c < 256) s ->
  0 <= q < Z.of_nat (length (SnprintfDef.asn_out 32 s)) ->
  bv_unsigned (nth (Z.to_nat q) (reac_boxreg_declare_c.name_field s) (Z_to_bv 8 0)) =
  nth (Z.to_nat q) (SnprintfDef.asn_out 32 s) 0.
Proof.
  intros s q Hs Hq. unfold SnprintfDef.asn_out in *.
  unfold reac_boxreg_declare_c.name_field, printf_facts_c.pf_bytes.
  change (Z.to_nat (32 - 1)) with 31%nat in *.
  rewrite length_app in Hq. cbn [length] in Hq.
  assert (Hs' : Forall (fun c => 0 < c < 256) (firstn 31 s)).
  { rewrite <- (firstn_skipn 31 s) in Hs. apply Forall_app in Hs. exact (proj1 Hs). }
  rewrite Forall_forall in Hs'.
  destruct (Nat.ltb_spec (Z.to_nat q) (length (firstn 31 s))) as [Hlt|Hge].
  - rewrite app_nth1 by (rewrite ?length_map; lia). rewrite app_nth1 by (rewrite ?length_map; lia).
    rewrite dm_nth_map_bv8.
    assert (Hc : 0 < nth (Z.to_nat q) (firstn 31 s) 0 < 256) by (apply Hs'; apply nth_In; exact Hlt).
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. lia.
  - rewrite app_nth2 by (rewrite ?length_map; lia). rewrite app_nth2 by (rewrite ?length_map; lia).
    rewrite nth_repeat.
    replace (Z.to_nat q - length (firstn 31 s))%nat with 0%nat by lia. reflexivity.
Qed.

Lemma dm_name_field_hi : forall s q, Z.of_nat (length (SnprintfDef.asn_out 32 s)) <= q < 32 ->
  bv_unsigned (nth (Z.to_nat q) (reac_boxreg_declare_c.name_field s) (Z_to_bv 8 0)) = 0.
Proof.
  intros s q Hq. unfold SnprintfDef.asn_out in Hq.
  change (Z.to_nat (32 - 1)) with 31%nat in Hq.
  rewrite length_app in Hq. cbn [length] in Hq.
  unfold reac_boxreg_declare_c.name_field, printf_facts_c.pf_bytes.
  rewrite app_nth2 by (rewrite length_map; lia). rewrite nth_repeat. reflexivity.
Qed.

Lemma dm_asn_out_nil : SnprintfDef.asn_out 32 [] = [0].
Proof. reflexivity. Qed.

(* With s = [] (name NULL), the two name premises of dm_decl_bytes follow from 32 zero bytes. *)
Lemma dm_name_nil_premises : forall (rd : Z -> option Z) (a : Z),
  (forall j, 0 <= j < 32 -> rd (a + j) = Some 0) ->
  (forall j, 0 <= j < Z.of_nat (length (SnprintfDef.asn_out 32 [])) ->
     rd (a + j) = Some (nth (Z.to_nat j) (SnprintfDef.asn_out 32 []) 0)) /\
  (forall j, Z.of_nat (length (SnprintfDef.asn_out 32 [])) <= j < 32 -> rd (a + j) = Some 0).
Proof.
  intros rd a H.
  assert (L : length (SnprintfDef.asn_out 32 []) = 1%nat) by reflexivity. rewrite L.
  split; intros j Hj.
  - assert (j = 0) by lia. subst j. rewrite H by lia. reflexivity.
  - apply H. lia.
Qed.

Lemma dm_decl_bytes : forall (rd0 rd : Z -> option Z) (r b k p : Z) (bs : list byte) (s : list Z),
  length bs = 288%nat -> 0 <= Boxreg.bx_n bs <= 4 -> Forall (fun c => 0 < c < 256) s ->
  Z.of_nat (length s) + 8 < 2 ^ 31 ->
  (forall i, 0 <= i < 288 -> rd0 (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) ->
  (forall i, 0 <= i < 288 -> ~ (56 * Boxreg.bx_n bs <= i < 56 * Boxreg.bx_n bs + 56) -> ~ (280 <= i < 284) ->
     rd (r + i) = rd0 (r + i)) ->
  (forall j, 0 <= j < 8 -> rd (r + 56 * Boxreg.bx_n bs + j) = Some 0) ->
  (forall j, 0 <= j < 4 ->
     rd (r + 56 * Boxreg.bx_n bs + 8 + j) = Some (bv_unsigned (YP09.byte_of_word (Z_to_bv 64 b) j))) ->
  (forall j, 0 <= j < 4 ->
     rd (r + 56 * Boxreg.bx_n bs + 12 + j) = Some (bv_unsigned (YP09.byte_of_word (Z_to_bv 64 k) j))) ->
  (forall j, 0 <= j < 4 -> rd (r + 56 * Boxreg.bx_n bs + 16 + j) = Some 0) ->
  (forall j, 0 <= j < 4 ->
     rd (r + 56 * Boxreg.bx_n bs + 20 + j) = Some (bv_unsigned (YP09.byte_of_word (Z_to_bv 64 p) j))) ->
  (forall j, 0 <= j < Z.of_nat (length (SnprintfDef.asn_out 32 s)) ->
     rd (r + 56 * Boxreg.bx_n bs + 24 + j) = Some (nth (Z.to_nat j) (SnprintfDef.asn_out 32 s) 0)) ->
  (forall j, Z.of_nat (length (SnprintfDef.asn_out 32 s)) <= j < 32 ->
     rd (r + 56 * Boxreg.bx_n bs + 24 + j) = Some 0) ->
  (forall j, 0 <= j < 4 ->
     rd (r + 280 + j) = Some (bv_unsigned (YP09.byte_of_word (Z_to_bv 64 (Boxreg.bx_n bs + 1)) j))) ->
  forall i, 0 <= i < 288 ->
  rd (r + i) = Some (bv_unsigned (nth (Z.to_nat i)
                     (BoxregUpd.new_row_bytes bs (reac_boxreg_declare_c.decl_row b k p s)) (Z_to_bv 8 0))).
Proof.
  intros rd0 rd r b k p bs s HL Hn Hs Hsl H0 Hkeep Hmac Hb Hk Hest Hp Hnm1 Hnm2 Hcnt i Hi.
  pose proof (dm_decl_row_length b k p s) as HR.
  rewrite dm_new_row_nth by first [exact HL | exact Hn | exact HR | lia].
  set (n := Boxreg.bx_n bs) in *. clearbody n.
  destruct (Z.leb_spec 280 i); destruct (Z.ltb_spec i 284); cbn [andb]; try (exfalso; lia).
  (* the count word *)
  1: { rewrite dm_le4_nth by lia. replace (r + i) with (r + 280 + (i - 280)) by lia. apply Hcnt. lia. }
  all: destruct (Z.leb_spec (56 * n) i); destruct (Z.ltb_spec i (56 * n + 56)); cbn [andb];
    try (exfalso; lia).
  (* the kept bytes *)
  all: try (rewrite Hkeep by lia; apply H0; lia).
  (* the new row *)
  all: remember (i - 56 * n) as o eqn:Eo.
  all: replace (r + i) with (r + 56 * n + o) by lia.
  all: unfold reac_boxreg_declare_c.decl_row.
  all: destruct (Z.ltb_spec o 8);
    [ rewrite Hmac by lia; rewrite app_nth1 by (rewrite repeat_length; lia); rewrite nth_repeat; reflexivity
    | rewrite app_nth2 by (rewrite repeat_length; lia); rewrite repeat_length ].
  all: destruct (Z.ltb_spec o 12);
    [ replace (r + 56 * n + o) with (r + 56 * n + 8 + (o - 8)) by lia; rewrite Hb by lia;
      rewrite app_nth1 by (rewrite Mem.length_le4; lia);
      replace (Z.to_nat o - 8)%nat with (Z.to_nat (o - 8)) by lia; rewrite dm_le4_nth by lia; reflexivity
    | rewrite app_nth2 by (rewrite Mem.length_le4; lia); rewrite Mem.length_le4 ].
  all: destruct (Z.ltb_spec o 16);
    [ replace (r + 56 * n + o) with (r + 56 * n + 12 + (o - 12)) by lia; rewrite Hk by lia;
      rewrite app_nth1 by (rewrite Mem.length_le4; lia);
      replace (Z.to_nat o - 8 - 4)%nat with (Z.to_nat (o - 12)) by lia; rewrite dm_le4_nth by lia; reflexivity
    | rewrite app_nth2 by (rewrite Mem.length_le4; lia); rewrite Mem.length_le4 ].
  all: destruct (Z.ltb_spec o 20);
    [ replace (r + 56 * n + o) with (r + 56 * n + 16 + (o - 16)) by lia; rewrite Hest by lia;
      rewrite app_nth1 by (rewrite Mem.length_le4; lia);
      replace (Z.to_nat o - 8 - 4 - 4)%nat with (Z.to_nat (o - 16)) by lia; rewrite dm_le4_nth by lia;
      rewrite dm_byte_of_word_0; reflexivity
    | rewrite app_nth2 by (rewrite Mem.length_le4; lia); rewrite Mem.length_le4 ].
  all: destruct (Z.ltb_spec o 24);
    [ replace (r + 56 * n + o) with (r + 56 * n + 20 + (o - 20)) by lia; rewrite Hp by lia;
      rewrite app_nth1 by (rewrite Mem.length_le4; lia);
      replace (Z.to_nat o - 8 - 4 - 4 - 4)%nat with (Z.to_nat (o - 20)) by lia; rewrite dm_le4_nth by lia;
      reflexivity
    | rewrite app_nth2 by (rewrite Mem.length_le4; lia); rewrite Mem.length_le4 ].
  all: replace (Z.to_nat o - 8 - 4 - 4 - 4 - 4)%nat with (Z.to_nat (o - 24)) by lia.
  all: replace (r + 56 * n + o) with (r + 56 * n + 24 + (o - 24)) by lia.
  all: destruct (Z.ltb_spec (o - 24) (Z.of_nat (length (SnprintfDef.asn_out 32 s)))).
  all: first
    [ rewrite Hnm1 by lia; rewrite dm_name_field_lo by first [exact Hs | lia]; reflexivity
    | rewrite Hnm2 by lia; rewrite dm_name_field_hi by lia; reflexivity ].
Qed.

(* ---- reading the registry block ---- *)
Lemma dmbyte_of_view : forall (W : world SEGS) mem a (b : byte),
aview SEGS (w_H W) mem a = Some (bv_unsigned b) -> mbyte SEGS (mrestrict (w_H W) mem) a = Some b.
Proof.
intros W mem a b H. unfold aview in H. destruct (mbyte SEGS (mrestrict (w_H W) mem) a) as [b'|] eqn:Hm; [|discriminate H].
cbn in H. injection H as H. f_equal. apply bv_eq. exact H.
Qed.
Lemma dval4 : forall (W : world SEGS) mem r bs o, length bs = 288%nat -> tdecl_reg_bytes W mem r bs -> 0 <= o -> o + 4 <= 288 ->
0 <= Boxreg.rd4 bs o -> val_mem SEGS (mrestrict (w_H W) mem) (r + o) 4 (Boxreg.rd4 bs o).
Proof.
intros W mem r bs o HL HB Ho Ho4 Hr j Hj. apply dmbyte_of_view.
replace (r + o + Z.of_nat j) with (r + (o + Z.of_nat j)) by lia.
rewrite (HB (o + Z.of_nat j)) by (unfold REG_SIZE; lia). rewrite (dm_rd4_byte bs o j HL Ho Ho4 Hr Hj). reflexivity.
Qed.

(* ---- the shadow of a heap block, as the engine's shadow entries ---- *)
Lemma dshent_block : forall ly S (W : world SEGS) mem md Ex (n : nat) (q b sz lo hi : Z),
AR SEGS B ly S W mem md -> In (b, sz) (ablocks B ly S) ->
U Ex DBx = SHADOW_OFF -> U Ex (SOff n 0) = q ->
b <= q + lo -> lo <= hi -> q + hi <= b + req_size sz ->
shent_ok SEGS DBx Ex (mrestrict (w_H W) mem) (mkSHE n lo hi).
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

(* ---- the entry state ---- *)
(* atoms: 32 the shadow base, 33 fabric (r + 284), 34 n (r + 280) *)
Definition dm_RF : YP09.region :=
YP09.mkRegion (Some 10%nat) 280 288 0 0 [YP09.mkChunk 280 (CVal 4 (SOff 34 0)); YP09.mkChunk 284 (CVal 4 (SOff 33 0))].
Definition dm_regions : smem := [stack_region 96; got_regionP; bcell_regionP 32; dm_RF].
Definition dm_facts : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 140737479966720 4);
  (32%nat, mkAF DSB DSB 0); (33%nat, mkAF 1 40 0); (34%nat, mkAF 0 5 0)] [] [].
Definition ss_dm : sstate := mkSS AF_reac_boxreg_declare sr_atoms dm_regions None dm_facts.
Definition dm_SH : list shent := [mkSHE 10 0 288].
Definition dm_extra (bs : list byte) : list word := map (Z_to_bv 64) [DSB; Boxreg.bx_fabric bs; Boxreg.bx_n bs].
Definition dmE (regs : bvmap 5 word) (bs : list byte) : env := Eimg (Ereg regs (dm_extra bs)).

Lemma dinv_facts : forall bs, Boxreg.boxreg_inv bs ->
length bs = 288%nat /\ 0 <= Boxreg.bx_n bs <= 5 /\ 1 <= Boxreg.bx_fabric bs <= 40.
Proof.
intros bs ((HL & H1 & H2 & _) & _). unfold Boxreg.boxreg_B1, Boxreg.boxreg_B2 in *. tauto.
Qed.

Lemma dm_entry : forall ly S W (regs : bvmap 5 word) mem md ch r bs,
afn_pre SEGS B DSTK ly S W regs mem md ch -> getr regs 10 = w64 r ->
In (r, REG_SIZE) (ablocks B ly S) -> tdecl_reg_bytes W mem r bs -> Boxreg.boxreg_inv bs ->
st_ok_pi SEGS VAL (dmE regs bs) ss_dm
  (restrict (w_H W) (mkst regs (Z_to_bv 64 A_reac_boxreg_declareP) mem (seg_rom SEGS)))
/\ sh_ok SEGS DBx dm_SH (dmE regs bs) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md ch r bs HPRE H10 Hin HBY HINV.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof DSTK_val as WS.
destruct (dinv_facts bs HINV) as (HL & Hn5 & Hf40).
destruct (al_blocks _ _ LAWS ly S W mem md r REG_SIZE HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & _ & _).
change (req_size REG_SIZE) with 288 in *.
pose proof (blk_off_imgP B ly S W mem md r REG_SIZE HAR Hin) as Hrimg. change (req_size REG_SIZE) with 288 in Hrimg.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
pose proof pa_B_ok as HBASE.
pose proof (dval4 W mem r bs 280 HL HBY ltac:(lia) ltac:(lia) ltac:(unfold Boxreg.bx_n in Hn5; lia)) as Vn.
pose proof (dval4 W mem r bs 284 HL HBY ltac:(lia) ltac:(lia) ltac:(unfold Boxreg.bx_fabric in Hf40; lia)) as Vf.
change (Boxreg.rd4 bs 280) with (Boxreg.bx_n bs) in Vn. change (Boxreg.rd4 bs 284) with (Boxreg.bx_fabric bs) in Vf.
rewrite restrict_mkst_fx.
set (E := dmE regs bs).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (dm_extra bs)) n)
  by (intros n Hn; subst E; unfold dmE; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 r) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 DSB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (Boxreg.bx_fabric bs)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (Boxreg.bx_n bs)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (Egot : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; unfold dmE; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Ecell : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; unfold dmE; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
pose proof (pa_val_range (A_OBJ 1)) as Vg. pose proof (pa_val_range (A_OBJ 12)) as Vc.
split.
- unfold ss_dm, A_reac_boxreg_declareP. apply pa_entry_st_ok_full.
  + subst E. unfold dmE. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold dm_regions, stack_region, got_regionP, bcell_regionP, dm_RF.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite WS. lia.
    * rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Egot) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite Ecell, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Ecell) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 DBx DSB);
      [cbn [sv_denot DBx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold DSB; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    * rewrite (VB 10%nat r E10) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      -- apply (chunk_ok_val SEGS E _ r 280 4 (SOff 34 0) (Boxreg.bx_n bs));
         [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vn].
      -- apply (chunk_ok_val SEGS E _ r 284 4 (SOff 33 0) (Boxreg.bx_fabric bs));
         [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vf].
  + apply pairwise_disjoint_of_extents.
    unfold dm_regions, stack_region, got_regionP, bcell_regionP, dm_RF, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Egot) by lia. rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Ecell) by lia.
    rewrite (VB 10%nat r E10) by lia. cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgcD HgotR Hrimg Hr4096 Hrceil. clear. intros.
    repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [dm_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E10, E32, E33, E34, !unsigned_lit_small by (unfold DSB; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hslo Hshi H47 Hceil C1 WS Hstk0 Hal16 Hr16 Hr4096 Hrceil Hn5 Hf40. clear. unfold DSB. intros.
    repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, dm_SH. constructor; [|constructor].
  eapply (dshent_block ly S W mem md E 10 r r REG_SIZE 0 288 HAR Hin).
  + unfold DBx. rewrite (U_atom E 32 DSB E32) by (unfold DSB; lia). reflexivity.
  + exact (U_atom E 10 r E10 ltac:(lia)).
  + lia.
  + lia.
  + change (req_size REG_SIZE) with 288. lia.
Qed.

(* ---- the machine state at the two split points ---- *)
(* The 11 registers the prologue saves (ra, s0 .. s9) and their offsets from the lowered sp (sp - 96). *)
Definition dsave_reg : list Z := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25].
Definition dsave_off : list Z := [88; 80; 72; 64; 56; 48; 40; 32; 24; 16; 8].
Definition dframe_ok (regs0 : bvmap 5 word) (W : world SEGS) (mem : word -> option byte) : Prop :=
forall j, (j < 11)%nat ->
val_mem SEGS (mrestrict (w_H W) mem) (spZ regs0 - 96 + nth j dsave_off 0) 8
  (bv_unsigned (getr regs0 (Z_to_bv 5 (nth j dsave_reg 0)))).
(* The spec's premises, as one fact (they hold of the entry state throughout). *)
Definition dpre (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word) mem md ch (r k nm b0 : Z)
  (bs : list byte) (s : list Z) (G : list (Z * Z)) : Prop :=
afn_pre SEGS B DSTK ly S W regs mem md ch /\
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) /\
getr regs 10 = w64 r /\ getr regs 11 = w64 k /\ getr regs 12 = w64 nm /\ getr regs 13 = w64 b0 /\
-2 ^ 31 <= k < 2 ^ 31 /\ -2 ^ 31 <= b0 < 2 ^ 31 /\
In (r, REG_SIZE) (ablocks B ly S) /\ tdecl_reg_bytes W mem r bs /\ Boxreg.boxreg_inv bs /\
tdecl_name_ok ly S W mem r nm s /\
asn_blk_tail_vis SEGS B /\ img_shadow_vis SEGS B /\ globs_marked SEGS B G /\
asn_rom_bytes SEGS B A_declare_fmtP ASN_FMT /\ In (A_declare_fmtP, 3) G /\
IMG_LO + 64 <= A_declare_fmtP /\ A_declare_fmtP + 3 + 64 <= IMG_HI /\ A_declare_fmtP + 3 <= 0x99b40 /\
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0.
(* The state at 0x81878 (loop head) and 0x8190c (placement): the journal from the entry (no block freed, the same
   layout, state and world), the lowered sp, gp / tp / s10 / s11 as at the entry, the frame holding the saved
   registers, the registry block unchanged, and the registers both later pieces read: s0 = nm, s1 = r + 280,
   s8 = the shadow base, s7 = the shadow address of r + 280. *)
Definition dinv (regs0 : bvmap 5 word) ly S (W : world SEGS) mem0 md0 (r nm : Z) (bs : list byte)
  (regsc : bvmap 5 word) memc mdc : Prop :=
ajournal SEGS B DSTK (spZ regs0) [(r, r + REG_SIZE)] ly S W mem0 md0 [] ly S W memc mdc 0 /\
getr regsc 2 = w64 (spZ regs0 - 96) /\ getr regsc 3 = getr regs0 3 /\ getr regsc 4 = getr regs0 4 /\
getr regsc 26 = getr regs0 26 /\ getr regsc 27 = getr regs0 27 /\
dframe_ok regs0 W memc /\ tdecl_reg_bytes W memc r bs /\
getr regsc 8 = w64 nm /\ getr regsc 9 = w64 (r + 280) /\ getr regsc 24 = w64 DSB /\
getr regsc 23 = w64 ((r + 280) / 8 + DSB).
(* The post from a returned state at the FP state fy: fy's f registers but f10 are the entry's, and its fcsr is the
   entry's or has rounding mode 0 (apost_baseF's two FP facts). *)
Lemma dret_postF : forall (fy : YK11.FPState) ly S W (regs0 : bvmap 5 word) mem0 md0 r k b0 bs s
  (regsF : bvmap 5 word) memF mdF,
(forall q : bv 5, bv_unsigned q <> 10 -> Sem.reg_get (@fp_regs fy) q = Sem.reg_get (@fp_regs fx) q) ->
(@fp_csr fy = @fp_csr fx \/ Z.land (Z.shiftr (bv_unsigned (@fp_csr fy)) 5) 7 = 0) ->
ajournal SEGS B DSTK (spZ regs0) [(r, r + REG_SIZE)] ly S W mem0 md0 [] ly S W memF mdF 0 ->
aregs_preserved regs0 regsF ->
((reac_boxreg_declare_c.declare_refused bs k b0 /\ getr regsF 10 = w64 (-1) /\ tdecl_reg_bytes W memF r bs) \/
 (exists b p, reac_boxreg_declare_c.declare_placed bs k b0 b p /\
   getr regsF 10 = w64 (Boxreg.bx_n bs) /\
   tdecl_reg_bytes W memF r (BoxregUpd.new_row_bytes bs (reac_boxreg_declare_c.decl_row b k p s)))) ->
treac_boxreg_declare_post regs0 ly S W mem0 md0 r k b0 bs s W
  (mkCfg (@mkst fy regsF (getr regs0 1) memF (seg_rom SEGS)) mdF).
Proof.
intros fy ly S W regs0 mem0 md0 r k b0 bs s regsF memF mdF HFy HCy HJ HP HQ.
unfold treac_boxreg_declare_post, apost_baseF. exists fy, ly, S, regsF, memF, mdF.
split; [reflexivity|]. split; [exact HFy|]. split; [exact HCy|]. split; [exact HJ|]. split; [exact HP|].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [apply Permutation_refl | exact HQ].
Qed.
(* The post from a returned state at the entry's FP state (every path that does not reach the wrapper). *)
Lemma dret_post : forall ly S W (regs0 : bvmap 5 word) mem0 md0 r k b0 bs s (regsF : bvmap 5 word) memF mdF,
ajournal SEGS B DSTK (spZ regs0) [(r, r + REG_SIZE)] ly S W mem0 md0 [] ly S W memF mdF 0 ->
aregs_preserved regs0 regsF ->
((reac_boxreg_declare_c.declare_refused bs k b0 /\ getr regsF 10 = w64 (-1) /\ tdecl_reg_bytes W memF r bs) \/
 (exists b p, reac_boxreg_declare_c.declare_placed bs k b0 b p /\
   getr regsF 10 = w64 (Boxreg.bx_n bs) /\
   tdecl_reg_bytes W memF r (BoxregUpd.new_row_bytes bs (reac_boxreg_declare_c.decl_row b k p s)))) ->
treac_boxreg_declare_post regs0 ly S W mem0 md0 r k b0 bs s W
  (mkCfg (mkst regsF (getr regs0 1) memF (seg_rom SEGS)) mdF).
Proof.
intros ly S W regs0 mem0 md0 r k b0 bs s regsF memF mdF HJ HP HQ.
exact (dret_postF fx ly S W regs0 mem0 md0 r k b0 bs s regsF memF mdF (fun q _ => eq_refl) (or_introl eq_refl) HJ HP HQ).
Qed.

(* ---- the placement walk, 0x8190c (dp_walk) ---- *)
(* The state at 0x8190c: atoms 32 the shadow base, 33 r, 34 .. 44 the 11 saved words (dsave_reg's order: ra, s0,
   s1, s2 .. s9) of the frame at the lowered sp, 45 n (the word at r + 280). *)
Definition dpl_frame : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 96 0 0 (map (fun i => YP09.mkChunk (nth i dsave_off 0) (CVal 8 (SOff (34 + i)%nat 0))) (seq 0 11)).
Definition dpl_regs : list sv :=
sr_set (sr_set (sr_set sr_atoms 9%bv (SOff 33 280)) 23%bv (SAlu ALU_ADD (SAlu ALU_SRL (SOff 33 280) (SLit 3)) (SOff 32 0)))
  24%bv (SOff 32 0).
Definition dpl_RF : YP09.region := YP09.mkRegion (Some 33%nat) 280 284 280 284 [YP09.mkChunk 280 (CVal 4 (SOff 45 0))].
Definition dpl_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (21%nat, mkAF 4096 140737479966720 3);
  (33%nat, mkAF 4096 140737479966720 4); (32%nat, mkAF DSB DSB 0); (19%nat, mkAF 2 40 0); (22%nat, mkAF 0 38 0);
  (45%nat, mkAF 0 4 0)] [] [].
Definition ss_dpl : sstate := mkSS 6592 dpl_regs [dpl_frame; dpl_RF] None dpl_facts.
Definition dpl_SH : list shent := [mkSHE 21 0 56; mkSHE 33 0 288].
(* The row after __asan_memset: 24 zero bytes, the words +8, +12 and +20 stored next. *)
Definition dpl_RowA : YP09.region := YP09.mkRegion (Some 21%nat) 0 24 8 24 [YP09.mkChunk 0 (CZero 24)].
Definition dpl_extra (regs0 : bvmap 5 word) (r n : Z) : list word :=
[Z_to_bv 64 DSB; Z_to_bv 64 r] ++ map (fun j => getr regs0 (Z_to_bv 5 (nth j dsave_reg 0))) (seq 0 11) ++ [Z_to_bv 64 n].
Definition dplE (regsc regs0 : bvmap 5 word) (r n : Z) : env := Eimg (Ereg regsc (dpl_extra regs0 r n)).
(* The registry bytes the placement leaves as they are (all but the new row and n), and the name field. *)
Definition dpl_PR (r n a : Z) : Prop := r <= a < r + 288 /\ ~ (r + 56 * n <= a < r + 56 * n + 56) /\ ~ (r + 280 <= a < r + 284).
Lemma dpl_E_low : forall regsc regs0 r n (q : nat) (x : bv 5), Z.of_nat q = bv_unsigned x ->
ew (dplE regsc regs0 r n) q = getr regsc x.
Proof. intros regsc regs0 r n q x H. unfold dplE. apply ew_Eimg_Ereg_nat. exact H. Qed.
Lemma dpl_E_ext : forall regsc regs0 r n j, (j < 14)%nat ->
ew (dplE regsc regs0 r n) (32 + j) = nth j (dpl_extra regs0 r n) (Z_to_bv 64 0).
Proof. intros regsc regs0 r n j Hj. unfold dplE. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.
Lemma dpl_E_frame : forall regsc regs0 r n j, (j < 11)%nat ->
ew (dplE regsc regs0 r n) (34 + j) = getr regs0 (Z_to_bv 5 (nth j dsave_reg 0)).
Proof.
intros regsc regs0 r n j Hj. replace (34 + j)%nat with (32 + (2 + j))%nat by lia. rewrite dpl_E_ext by lia.
do 11 (destruct j as [|j]; [reflexivity|]). lia.
Qed.
Lemma dpl_bv_ne0 : forall (x : bv 5), bv_unsigned x <> 0 -> x <> 0%bv.
Proof. intros x H E. apply H. rewrite E. reflexivity. Qed.
Lemma dpl_den_U : forall E e z, 0 <= z < 2 ^ 64 -> U E e = z -> sv_denot E e = Z_to_bv 64 z.
Proof. intros E e z Hz H. apply bv_eq. rewrite unsigned_lit_small by lia. exact H. Qed.
Lemma dpl_frame_chunk : forall E m (regs0 : bvmap 5 word) (W : world SEGS) memc j,
(forall j, (j < 11)%nat -> ew E (34 + j) = getr regs0 (Z_to_bv 5 (nth j dsave_reg 0))) ->
dframe_ok regs0 W memc -> m = mrestrict (w_H W) memc -> (j < 11)%nat ->
YP09.chunk_ok SEGS E m (spZ regs0 - 96) (YP09.mkChunk (nth j dsave_off 0) (CVal 8 (SOff (34 + j) 0))).
Proof.
intros E m regs0 W memc j HE HF -> Hj.
apply (chunk_ok_val SEGS E _ (spZ regs0 - 96) (nth j dsave_off 0) 8 (SOff (34 + j) 0)
  (bv_unsigned (getr regs0 (Z_to_bv 5 (nth j dsave_reg 0))))).
- cbn [sv_denot]. rewrite (HE j Hj), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- pose proof (bv_unsigned_in_range 64 (getr regs0 (Z_to_bv 5 (nth j dsave_reg 0)))) as Hb.
  change (bv_modulus 64) with (2 ^ 64) in Hb. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
- change (Z.of_N 8) with 8. lia.
- change (N.to_nat 8) with 8%nat. exact (HF j Hj).
Qed.
Lemma dpl_entry : forall ly S W (regs0 : bvmap 5 word) mem0 md0 ch r k nm b0 bs s G (regsc : bvmap 5 word) memc mdc b p,
dpre ly S W regs0 mem0 md0 ch r k nm b0 bs s G ->
dinv regs0 ly S W mem0 md0 r nm bs regsc memc mdc ->
reac_boxreg_declare_c.declare_placed bs k b0 b p ->
getr regsc 21 = w64 (r + 56 * Boxreg.bx_n bs) -> getr regsc 22 = w64 b -> getr regsc 19 = w64 k ->
st_ok_pi SEGS VAL (dplE regsc regs0 r (Boxreg.bx_n bs)) ss_dpl
  (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + 6592)) memc (seg_rom SEGS))) /\
sh_ok SEGS DBx dpl_SH (dplE regsc regs0 r (Boxreg.bx_n bs)) (mrestrict (w_H W) memc).
Proof.
intros ly S W regs0 mem0 md0 ch r k nm b0 bs s G regsc memc mdc b p DP DI HPL H21 H22 H19.
destruct DP as (HPRE & _ & _ & _ & _ & _ & _ & _ & Hin & _ & HINV & _).
destruct DI as (HJ & Hsp & _ & _ & _ & _ & HFR & HBYc & _ & Hs1 & Hs8 & Hs7).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof DSTK_val as WS.
destruct (dm_boxreg_inv_facts bs HINV) as (HL & Hn5 & Hf40 & _).
pose proof HJ as (HARc & _).
destruct (al_blocks _ _ LAWS ly S W memc mdc r REG_SIZE HARc Hin) as (Hr16 & Hr4096 & Hrceil & Hria & Hpr & _).
change (req_size REG_SIZE) with 288 in *.
destruct HPL as ((Hev & Hk & Hkf) & Hn & HPB).
assert (Hb : 0 <= b <= 38).
{ destruct HPB as [(Hb0 & -> & _ & (_ & Hbk & _)) | (_ & _ & Hb0 & Hlf)]; [lia|].
  destruct (dm_lowest_free_range bs k b ltac:(lia) Hlf) as [-> | Hz]; lia. }
pose proof (dval4 W memc r bs 280 HL HBYc ltac:(lia) ltac:(lia) ltac:(unfold Boxreg.bx_n in Hn5; lia)) as Vn.
change (Boxreg.rd4 bs 280) with (Boxreg.bx_n bs) in Vn.
set (n := Boxreg.bx_n bs) in *.
rewrite restrict_mkst_fx.
set (E := dplE regsc regs0 r n).
assert (E2 : ew E 2 = getr regsc 2) by exact (dpl_E_low regsc regs0 r n 2 2%bv eq_refl).
assert (E19 : ew E 19 = Z_to_bv 64 k) by exact (eq_trans (dpl_E_low regsc regs0 r n 19 19%bv eq_refl) H19).
assert (E21 : ew E 21 = Z_to_bv 64 (r + 56 * n)) by exact (eq_trans (dpl_E_low regsc regs0 r n 21 21%bv eq_refl) H21).
assert (E22 : ew E 22 = Z_to_bv 64 b) by exact (eq_trans (dpl_E_low regsc regs0 r n 22 22%bv eq_refl) H22).
assert (E32 : ew E 32 = Z_to_bv 64 DSB) by exact (dpl_E_ext regsc regs0 r n 0 ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 r) by exact (dpl_E_ext regsc regs0 r n 1 ltac:(lia)).
assert (E45 : ew E 45 = Z_to_bv 64 n) by exact (dpl_E_ext regsc regs0 r n 13 ltac:(lia)).
assert (EF : forall j, (j < 11)%nat -> ew E (34 + j) = getr regs0 (Z_to_bv 5 (nth j dsave_reg 0)))
  by (intros j Hj; exact (dpl_E_frame regsc regs0 r n j Hj)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs0 - 96) by (rewrite E2, Hsp; apply unsigned_lit_small; lia).
assert (VB : forall q v, ew E q = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some q) = v).
{ intros q v Hq Hv. cbn [base_val]. rewrite Hq. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_dpl. apply pa_entry_st_ok_full.
  + unfold dpl_regs.
    apply regs_ok_pin; [| apply dpl_bv_ne0; cbv; lia |].
    2: { rewrite Hs8. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
    apply regs_ok_pin; [| apply dpl_bv_ne0; cbv; lia |].
    2: { rewrite Hs7. symmetry.
      assert (Hd : 0 <= (r + 280) / 8 < 2 ^ 61) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
      apply dpl_den_U; [unfold DSB; lia|].
      rewrite !U_SAlu, !U_SOff, U_SLit, E33, E32, !unsigned_lit_small by (unfold DSB; lia).
      cbn [zalu_raw]. unfold zcanon, M64.
      change (Z.land (3 mod 2 ^ 64) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
      rewrite Z.add_0_r. rewrite (Z.mod_small (r + 280)) by lia.
      rewrite (Z.mod_small ((r + 280) / 8)) by lia. rewrite (Z.mod_small DSB) by (unfold DSB; lia).
      apply Z.mod_small. unfold DSB. lia. }
    apply regs_ok_pin; [| apply dpl_bv_ne0; cbv; lia |].
    2: { rewrite Hs1. cbn [sv_denot]. rewrite E33, unsigned_lit_small by lia. reflexivity. }
    unfold E, dplE. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold dpl_frame, dpl_RF. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_map. apply Forall_forall. intros j Hj. apply in_seq in Hj.
      exact (dpl_frame_chunk E _ regs0 W memc j EF HFR eq_refl ltac:(lia)).
    * rewrite (VB 33%nat r E33) by lia. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); exact (proj1 (Hpr (r + o) ltac:(lia)))|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ r 280 4 (SOff 45 0) n);
      [cbn [sv_denot]; rewrite E45, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vn].
  + apply pairwise_disjoint_of_extents.
    unfold dpl_frame, dpl_RF, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 33%nat r E33) by lia. cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 Hr4096 Hrceil. clear. intros.
    repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [dpl_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E21, E33, E32, E19, E22, E45, !unsigned_lit_small by (unfold DSB; lia).
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hslo Hshi H47 Hceil C1 WS Hstk0 Hal16 Hr16 Hr4096 Hrceil Hn5 Hn Hk Hb. clear. unfold DSB. intros.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia | (Z.div_mod_to_equations; lia)].
- unfold sh_ok, dpl_SH. constructor; [|constructor; [|constructor]].
  + eapply (dshent_block ly S W memc mdc E 21 (r + 56 * n) r REG_SIZE 0 56 HARc Hin).
    * unfold DBx. rewrite (U_atom E 32 DSB E32) by (unfold DSB; lia). reflexivity.
    * exact (U_atom E 21 (r + 56 * n) E21 ltac:(lia)).
    * lia.
    * lia.
    * change (req_size REG_SIZE) with 288. lia.
  + eapply (dshent_block ly S W memc mdc E 33 r r REG_SIZE 0 288 HARc Hin).
    * unfold DBx. rewrite (U_atom E 32 DSB E32) by (unfold DSB; lia). reflexivity.
    * exact (U_atom E 33 r E33 ltac:(lia)).
    * lia.
    * lia.
    * change (req_size REG_SIZE) with 288. lia.
Qed.
(* The engine's state relation names the FP state only through the f registers and fcsr of the machine state: a state
   built by mkst at f1 that meets it at f1 meets it at f2 when built by mkst at f2. *)
Lemma dst_ok_pi_fx : forall (f1 f2 : YK11.FPState) E ss (H : word -> bool) regs pc mem rom,
@st_ok_pi SEGS VAL f1 E ss (restrict H (@mkst f1 regs pc mem rom)) ->
@st_ok_pi SEGS VAL f2 E ss (restrict H (@mkst f2 regs pc mem rom)).
Proof.
intros f1 f2 E ss H regs pc mem rom HS. hnf in HS |- *.
destruct HS as (_ & H2 & H3 & H4 & _ & H6 & H7 & H8 & H9).
split; [reflexivity|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [reflexivity|].
split; [exact H6|]. split; [exact H7|]. split; [exact H8 | exact H9].
Qed.
(* The snprintf wrapper's contract (asnprintf_realizes) at the call, composed with the journal: its premises at the
   call, the journal kept (the written bytes are in the footprint, the rest is its 2 * ESTACK window). The wrapper
   returns at SOME FP state fy (f registers but f10 kept, fcsr rounding mode 0); the caller's continuation takes fy
   last, with those two facts (FMsnprintfSx.srr_fx_continue). *)
Lemma dpl_snprintf_at : forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw d n f x
  (s : list Z) p m (Q : world SEGS -> config -> Prop),
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
getr regsT 10 = w64 d -> getr regsT 11 = w64 n -> getr regsT 12 = w64 f -> getr regsT 13 = w64 x ->
1 <= n < 2 ^ 31 ->
In (p, m) (ablocks B lyc Sc) -> p <= d -> d + n <= p + m -> (forall a, d <= a < d + n -> inFP FP a) ->
(forall a, d <= a < d + n -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
(forall i, 0 <= i < 3 -> aview SEGS (w_H W) memT (f + i) = Some (nth (Z.to_nat i) ASN_FMT 0)) ->
0 < f -> amem_range f 3 -> 0x10000 <= f -> f + 3 <= 0x99b40 ->
(forall a, f <= a < f + 3 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) -> (f + 3 <= d \/ d + n <= f) ->
range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF f 3 -> shadow_hull_vis (aview SEGS (w_H W) memT) f 3 ->
Forall (fun c => 0 < c < 256) s -> Z.of_nat (length s) + 8 < 2 ^ 31 -> 0 < x ->
(forall i, 0 <= i <= Z.of_nat (length s) -> aview SEGS (w_H W) memT (x + i) = Some (nth (Z.to_nat i) (s ++ [0]) 0)) ->
(forall a, x + Z.of_nat (length s) < a < asn_word_end x (Z.of_nat (length s)) -> aview SEGS (w_H W) memT a <> None) ->
amem_range x (Z.of_nat (length s) + 8) ->
(forall a, x <= a < asn_word_end x (Z.of_nat (length s)) -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
(asn_word_end x (Z.of_nat (length s)) <= d \/ d + n <= x) ->
range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF x (Z.of_nat (length s) + 1) ->
shadow_hull_vis (aview SEGS (w_H W) memT) x (Z.of_nat (length s) + 1) ->
asn_rom_kept SEGS B W memT ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
(forall regs2 mem2 md2,
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k ->
  aregs_preserved regsT regs2 ->
  (forall i, 0 <= i < Z.of_nat (length (asn_out n s)) ->
     aview SEGS (w_H W) mem2 (d + i) = Some (nth (Z.to_nat i) (asn_out n s) 0)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + Z.of_nat (length (asn_out n s))) ->
     ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) ->
  (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) ->
  forall fy : YK11.FPState,
  (forall q : bv 5, bv_unsigned q <> 10 -> Sem.reg_get (@fp_regs fy) q = Sem.reg_get (@fp_regs fx) q) ->
  Z.land (Z.shiftr (bv_unsigned (@fp_csr fy)) 5) 7 = 0 ->
  SRr SEGS W (mkCfg (@mkst fy regs2 raw mem2 (seg_rom SEGS)) md2) Q) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA BS___interceptor_trampoline_snprintf)) memT (seg_rom SEGS)) mdc) Q.
Proof.
intros W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw d n f x s p m Q
  HJ Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw H10 H11 H12 H13 Hn Hin Hpd Hdn Hfp Hdw
  HF1 HF2 HF3 HFP1 HFP2 HF4 HF5 HF6 HF7 HS1 HS2 HS3 HS4 HS5 HS6 HS7 HS8 HS9 HS10 HROM HFRM HK.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HPRE : ecall_pre SEGS B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o); try eassumption; [lia|].
  rewrite Hra. exact Hraw. }
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (Hlo2 : ly_stk_lo lyc + 2 * ESTACK <= spZ regsT) by (rewrite Eslo, Hsp'; lia).
assert (Hpres2E : forall a, spZ regsT - 2 * ESTACK <= a < spZ regsT -> apresent (w_H W) memT a)
  by (intros a Ha; apply Hpres; rewrite Hsp' in Ha; lia).
assert (HL : Z.of_nat (length (asn_out n s)) <= n).
{ unfold asn_out. rewrite length_app, length_firstn. cbn [length]. lia. }
pose proof (req_size_pos m ltac:(lia)) as Hm.
eapply (FMsnprintfSx.srr_fx_continue SEGS).
{ exact (ASNPRINTF lyc Sc W regsT memT mdc d n f x s p m HPRE Hlo2 Hpres2E H10 H11 H12 H13 Hn Hin Hpd Hdn
    ltac:(rewrite Hsp'; exact Hdw) HF1 HF2 HF3 HFP1 HFP2 ltac:(rewrite Hsp'; exact HF4) HF5 HF6 HF7
    HS1 HS2 HS3 HS4 HS5 HS6 ltac:(rewrite Hsp'; exact HS7) HS8 HS9 HS10 HROM HFRM). }
cbv beta. intros fy regs2 mem2 md2 HFy HCy (HAR2 & HP & Hsame & Hres & Hout & Hfr & Hpres2).
rewrite Hsp' in Hfr.
assert (Hcf : @cfg_at fy SEGS (raZ regsT) regs2 mem2 md2 = mkCfg (@mkst fy regs2 raw mem2 (seg_rom SEGS)) md2)
  by (unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
rewrite Hcf.
refine (HK regs2 mem2 md2 _ HP Hout Hfr Hpres2 fy HFy HCy).
eapply (ajournal_after_write SEGS B LAWS pa_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
  (fun a => (d <= a < d + Z.of_nat (length (asn_out n s))) \/ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) Sc own HJ).
- intros a Ha Hna. apply (Hfr a Ha); intros H'; apply Hna; [left | right]; exact H'.
- exact Hpres2.
- exact Hsame.
- intros a [Ha | Ha]; left.
  + right; left. split; [apply Hfp; lia|]. exists p, m. split; [exact Hin | lia].
  + left. lia.
- exact HAR2.
- reflexivity.
- reflexivity.
- lia.
- exact Hfrs.
- exact HQT.
Qed.
(* A run keeps the bytes outside its regions' windows. *)
Lemma dpl_frame_keep : forall (W : world SEGS) E rs (m1 m2 : word -> option byte) (P : Z -> Prop) (f : Z -> option Z),
frame_of E rs (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
(forall a, P a -> 0 <= a < 2 ^ 64 /\ ~ in_wrange E rs a) ->
(forall a, P a -> aview SEGS (w_H W) m1 a = f a) ->
forall a, P a -> aview SEGS (w_H W) m2 a = f a.
Proof.
intros W E rs m1 m2 P f HF HP HK a Ha. rewrite <- (HK a Ha). destruct (HP a Ha) as [Ha64 Hw].
unfold aview, mbyte. cbv beta. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. exact Hw.
Qed.
Lemma dpl_mbyte_zero : forall H (m : word -> option byte) a,
aview SEGS H m a = Some 0 -> mbyte SEGS (mrestrict H m) a = Some (Z_to_bv 8 0).
Proof.
intros H m a Ha. unfold aview in Ha. destruct (mbyte SEGS (mrestrict H m) a) as [bb|] eqn:Hb; [|discriminate].
cbn in Ha. injection Ha as Hb0. f_equal. apply bv_eq. rewrite Hb0. reflexivity.
Qed.
Lemma dpl_chunk_byte : forall E m n bb cs lo hi wlo whi od cv i,
region_ok SEGS E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = bb -> In (YP09.mkChunk od cv) cs -> 0 <= i < YP09.cv_len cv ->
exists c, YP09.cbyte SEGS E (bb + od) cv i = Some c /\ mbyte SEGS m (bb + od + i) = Some c.
Proof.
intros E m n bb cs lo hi wlo whi od cv i HR Hb Hin Hi.
unfold region_ok in HR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in HR.
destruct HR as (_ & _ & _ & HF). rewrite Hb in HF.
rewrite Forall_forall in HF. specialize (HF _ Hin).
unfold YP09.chunk_ok in HF. cbn [YP09.c_off YP09.c_val YP09.c_len] in HF.
exact (HF i Hi).
Qed.
Lemma dpl_view_of_mbyte : forall H (m : word -> option byte) a c,
mbyte SEGS (mrestrict H m) a = Some c -> aview SEGS H m a = Some (bv_unsigned c).
Proof. intros H m a c Hm. unfold aview. rewrite Hm. reflexivity. Qed.
Lemma dpl_cbyte_val : forall E a w v i, YP09.cbyte SEGS E a (CVal w v) i = Some (YP09.byte_of_word (sv_denot E v) i).
Proof. reflexivity. Qed.
Lemma dpl_br_eq0 : forall E q v, ew E q = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
branch_taken BC_EQ (sv_denot E (SOff q 0)) (sv_denot E (SLit 0)) = (v =? 0).
Proof. intros E q v H Hv. rewrite branch_eq_U, (U_atom E q v H Hv), U_lit by lia. reflexivity. Qed.
Lemma dpl_den_atom : forall E q v, ew E q = Z_to_bv 64 v -> sv_denot E (SOff q 0) = Z_to_bv 64 v.
Proof. intros E q v H. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
(* The pinned flag: slti a1, s2, 0; xori a1, a1, 1. *)
Definition dpl_pin : sv := SAlu ALU_XOR (SAlu ALU_SLT (SOff 18 0) (SLit 0)) (SLit 1).
Lemma dpl_den_pin : forall E b0, ew E 18 = Z_to_bv 64 b0 -> -2 ^ 31 <= b0 < 2 ^ 31 ->
sv_denot E dpl_pin = Z_to_bv 64 (if 0 <=? b0 then 1 else 0).
Proof.
intros E b0 H Hb. apply dpl_den_U; [destruct (0 <=? b0); lia|]. unfold dpl_pin.
rewrite !U_SAlu, U_SOff, !U_SLit, H. cbn [zalu_raw]. unfold zcanon, M64.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.add_0_r, Z.mod_mod by lia.
assert (Hs : bv_swrap 64 (b0 mod 2 ^ 64) = b0).
{ unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  change (2 ^ 64 / 2) with (2 ^ 63). Z.div_mod_to_equations; lia. }
rewrite Hs. replace (bv_swrap 64 (0 mod 2 ^ 64)) with 0 by reflexivity.
destruct (Z.ltb_spec b0 0); destruct (Z.leb_spec 0 b0); try lia; reflexivity.
Qed.
Lemma dpl_reg_atom : forall (fy : YK11.FPState) (H : word -> bool) E ss ms (x : bv 5) q (w : word),
@st_ok_pi SEGS VAL fy E ss (restrict H ms) -> sr_get (ss_regs ss) x = SOff q 0 -> ew E q = w -> getr (ms_regs ms) x = w.
Proof.
intros fy H E ss ms x q w HS Hx Hq. rewrite (st_ok_pi_restrict_reg H E ss ms x HS), Hx. cbn [sv_denot].
rewrite Hq, Z.add_0_r. apply Z_to_bv_bv_unsigned.
Qed.
Lemma dpl_reg_off : forall (fy : YK11.FPState) (H : word -> bool) E ss ms (x : bv 5) q c v,
@st_ok_pi SEGS VAL fy E ss (restrict H ms) -> sr_get (ss_regs ss) x = SOff q c -> bv_unsigned (ew E q) + c = v ->
getr (ms_regs ms) x = Z_to_bv 64 v.
Proof. intros fy H E ss ms x q c v HS Hx Hq. rewrite (st_ok_pi_restrict_reg H E ss ms x HS), Hx. cbn [sv_denot]. rewrite Hq. reflexivity. Qed.
Lemma dpl_aregs : forall (regs0 regsF : bvmap 5 word),
getr regsF (Z_to_bv 5 2) = getr regs0 (Z_to_bv 5 2) -> getr regsF (Z_to_bv 5 3) = getr regs0 (Z_to_bv 5 3) ->
getr regsF (Z_to_bv 5 4) = getr regs0 (Z_to_bv 5 4) ->
(forall j, (j < 11)%nat -> getr regsF (Z_to_bv 5 (nth j dsave_reg 0)) = getr regs0 (Z_to_bv 5 (nth j dsave_reg 0))) ->
getr regsF (Z_to_bv 5 26) = getr regs0 (Z_to_bv 5 26) -> getr regsF (Z_to_bv 5 27) = getr regs0 (Z_to_bv 5 27) ->
aregs_preserved regs0 regsF.
Proof.
intros regs0 regsF H2 H3 H4 HF H26 H27 q Hq. unfold acallee_saved in Hq.
destruct Hq as [-> | [-> | [-> | [-> | [-> | Hq]]]]]; try assumption.
- exact (HF 1%nat ltac:(lia)).
- exact (HF 2%nat ltac:(lia)).
- assert (q = 18 \/ q = 19 \/ q = 20 \/ q = 21 \/ q = 22 \/ q = 23 \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27) as Hc by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]];
  first [ assumption | exact (HF 3%nat ltac:(lia)) | exact (HF 4%nat ltac:(lia)) | exact (HF 5%nat ltac:(lia))
        | exact (HF 6%nat ltac:(lia)) | exact (HF 7%nat ltac:(lia)) | exact (HF 8%nat ltac:(lia))
        | exact (HF 9%nat ltac:(lia)) | exact (HF 10%nat ltac:(lia)) ].
Qed.
(* The row region and the word n at the return: base +8, nch +12, pinned +20 stored, the rest memset's zeros; n + 1. *)
Definition dpl_RowF : YP09.region := YP09.mkRegion (Some 21%nat) 0 24 8 24
  [YP09.mkChunk 20 (CVal 4 dpl_pin); YP09.mkChunk 12 (CVal 4 (SOff 19 0)); YP09.mkChunk 8 (CVal 4 (SOff 22 0));
   YP09.mkChunk 0 (CZero 8); YP09.mkChunk 16 (CZero 4)].
Definition dpl_RFF : YP09.region := YP09.mkRegion (Some 33%nat) 280 284 280 284 [YP09.mkChunk 280 (CVal 4 (SOff 45 1))].
(* The post from the returned state at the FP state fy (apost_baseF's two FP facts): the journal, the restored
   registers, a0 = n and the 288 bytes. *)
Lemma dpl_post : forall (fy : YK11.FPState) ly S W (regs0 : bvmap 5 word) mem0 md0 r k b0 bs s b p
  (regsF : bvmap 5 word) memF mdF memc E,
(forall q : bv 5, bv_unsigned q <> 10 -> Sem.reg_get (@fp_regs fy) q = Sem.reg_get (@fp_regs fx) q) ->
(@fp_csr fy = @fp_csr fx \/ Z.land (Z.shiftr (bv_unsigned (@fp_csr fy)) 5) 7 = 0) ->
ajournal SEGS B DSTK (spZ regs0) [(r, r + REG_SIZE)] ly S W mem0 md0 [] ly S W memF mdF 0 ->
aregs_preserved regs0 regsF ->
reac_boxreg_declare_c.declare_placed bs k b0 b p -> Boxreg.boxreg_inv bs ->
Forall (fun c => 0 < c < 256) s -> Z.of_nat (length s) + 8 < 2 ^ 31 ->
getr regsF 10 = w64 (Boxreg.bx_n bs) ->
tdecl_reg_bytes W memc r bs ->
(forall a, dpl_PR r (Boxreg.bx_n bs) a -> aview SEGS (w_H W) memF a = aview SEGS (w_H W) memc a) ->
region_ok SEGS E (mrestrict (w_H W) memF) dpl_RowF -> region_ok SEGS E (mrestrict (w_H W) memF) dpl_RFF ->
ew E 18 = Z_to_bv 64 b0 -> -2 ^ 31 <= b0 < 2 ^ 31 -> ew E 19 = Z_to_bv 64 k ->
ew E 21 = Z_to_bv 64 (r + 56 * Boxreg.bx_n bs) -> ew E 22 = Z_to_bv 64 b -> ew E 33 = Z_to_bv 64 r ->
ew E 45 = Z_to_bv 64 (Boxreg.bx_n bs) -> 0 <= r -> r + 288 < 2 ^ 64 ->
(forall j, 0 <= j < Z.of_nat (length (SnprintfDef.asn_out 32 s)) ->
   aview SEGS (w_H W) memF (r + 56 * Boxreg.bx_n bs + 24 + j) = Some (nth (Z.to_nat j) (SnprintfDef.asn_out 32 s) 0)) ->
(forall j, Z.of_nat (length (SnprintfDef.asn_out 32 s)) <= j < 32 ->
   aview SEGS (w_H W) memF (r + 56 * Boxreg.bx_n bs + 24 + j) = Some 0) ->
treac_boxreg_declare_post regs0 ly S W mem0 md0 r k b0 bs s W
  (mkCfg (@mkst fy regsF (getr regs0 1) memF (seg_rom SEGS)) mdF).
Proof.
intros fy ly S W regs0 mem0 md0 r k b0 bs s b p regsF memF mdF memc E HFy HCy HJF HP HPL HINV Hs Hsl R10 HBYc KEEPR
  HRA HRF E18 Hb0r E19 E21 E22 E33 E45 Hr0 Hr1 Hnm1 Hnm2.
destruct (dm_boxreg_inv_facts bs HINV) as (HL & Hn5 & Hf40 & _).
pose proof HPL as ((Hev & Hk & Hkf) & Hn & HPB).
assert (Hp : p = if 0 <=? b0 then 1 else 0).
{ destruct HPB as [(Hb0 & _ & -> & _) | (Hb0 & -> & _)].
  - destruct (Z.leb_spec 0 b0); [reflexivity | lia].
  - destruct (Z.leb_spec 0 b0); [lia | reflexivity]. }
set (n := Boxreg.bx_n bs) in *.
assert (U21 : bv_unsigned (ew E 21) = r + 56 * n) by (rewrite E21; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = r) by (rewrite E33; apply unsigned_lit_small; lia).
apply (dret_postF fy); [exact HFy | exact HCy | exact HJF | exact HP |].
right. exists b, p. split; [exact HPL|]. split; [exact R10|].
intros i Hi. unfold REG_SIZE in Hi.
refine (dm_decl_bytes (aview SEGS (w_H W) memc) (aview SEGS (w_H W) memF) r b k p bs s HL ltac:(lia) Hs Hsl
  _ _ _ _ _ _ _ Hnm1 Hnm2 _ i ltac:(lia)).
- intros i0 Hi0. exact (HBYc i0 ltac:(unfold REG_SIZE; lia)).
- intros i0 Hi0 H1 H2. apply KEEPR. unfold dpl_PR. lia.
- intros j Hj. change (Boxreg.bx_n bs) with n.
  destruct (dpl_chunk_byte E _ 21 (r + 56 * n) _ _ _ _ _ 0 (CZero 8) j HRA U21 ltac:(cbn [In]; auto 10) ltac:(cbn; lia))
    as (c & Hc & Hm).
  cbn [YP09.cbyte] in Hc. injection Hc as <-. rewrite Z.add_0_r in Hm. rewrite (dpl_view_of_mbyte _ _ _ _ Hm). reflexivity.
- intros j Hj. change (Boxreg.bx_n bs) with n.
  destruct (dpl_chunk_byte E _ 21 (r + 56 * n) _ _ _ _ _ 8 (CVal 4 (SOff 22 0)) j HRA U21 ltac:(cbn [In]; auto 10)
    ltac:(cbn; lia)) as (c & Hc & Hm).
  rewrite dpl_cbyte_val in Hc. rewrite <- Hc in Hm. rewrite (dpl_view_of_mbyte _ _ _ _ Hm), (dpl_den_atom E 22 b E22).
  reflexivity.
- intros j Hj. change (Boxreg.bx_n bs) with n.
  destruct (dpl_chunk_byte E _ 21 (r + 56 * n) _ _ _ _ _ 12 (CVal 4 (SOff 19 0)) j HRA U21 ltac:(cbn [In]; auto 10)
    ltac:(cbn; lia)) as (c & Hc & Hm).
  rewrite dpl_cbyte_val in Hc. rewrite <- Hc in Hm. rewrite (dpl_view_of_mbyte _ _ _ _ Hm), (dpl_den_atom E 19 k E19). reflexivity.
- intros j Hj. change (Boxreg.bx_n bs) with n.
  destruct (dpl_chunk_byte E _ 21 (r + 56 * n) _ _ _ _ _ 16 (CZero 4) j HRA U21 ltac:(cbn [In]; auto 10) ltac:(cbn; lia))
    as (c & Hc & Hm).
  cbn [YP09.cbyte] in Hc. injection Hc as <-. rewrite (dpl_view_of_mbyte _ _ _ _ Hm). reflexivity.
- intros j Hj. change (Boxreg.bx_n bs) with n.
  destruct (dpl_chunk_byte E _ 21 (r + 56 * n) _ _ _ _ _ 20 (CVal 4 dpl_pin) j HRA U21 ltac:(cbn [In]; auto 10)
    ltac:(cbn; lia)) as (c & Hc & Hm).
  rewrite dpl_cbyte_val in Hc. rewrite <- Hc in Hm. rewrite (dpl_view_of_mbyte _ _ _ _ Hm), (dpl_den_pin E b0 E18 Hb0r), <- Hp.
  reflexivity.
- intros j Hj.
  destruct (dpl_chunk_byte E _ 33 r _ _ _ _ _ 280 (CVal 4 (SOff 45 1)) j HRF U33 ltac:(cbn [In]; auto 10) ltac:(cbn; lia))
    as (c & Hc & Hm).
  rewrite dpl_cbyte_val in Hc. rewrite <- Hc in Hm. rewrite (dpl_view_of_mbyte _ _ _ _ Hm). cbn [sv_denot].
  rewrite E45, unsigned_lit_small by lia. reflexivity.
Qed.
(* The windows of a run's regions: the frame has none, dpl_RF is r + 280 .. r + 284, the row region 8 .. 24 of the row. *)
Ltac dpl_nowr U21 U33 :=
let a := fresh "a" in let Ha := fresh "Ha" in let rg := fresh "rg" in let Hrin := fresh "Hrin" in let Hr := fresh "Hr" in
intros a Ha; split; [try unfold dpl_PR in Ha; lia|];
intros (rg & Hrin & Hr);
lazymatch type of Hrin with In _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' in Hrin end;
cbn [In] in Hrin; repeat destruct Hrin as [<- | Hrin]; try destruct Hrin;
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val ew ewset havoc Nat.eqb Nat.ltb Nat.leb] in Hr;
rewrite ?U21, ?U33 in Hr; try unfold dpl_PR in Ha; lia.
(* The right to write the regions' windows: dpl_RF's in the footprint (a block base), the row region's inside the
   registry block. *)
Ltac dpl_awr r Hin U21 U33 :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn; lia|]
| eapply awr_ok_cons_block;
  [ reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb]; exact U33 | exact Hin | cbn [YP09.r_wlo]; lia
  | cbn [YP09.r_whi]; change (req_size REG_SIZE) with 288; lia
  | cbn [YP09.r_wlo YP09.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    exists (r, r + REG_SIZE); split; [left; reflexivity | cbn [fst snd]; unfold REG_SIZE; lia] | ]
| eapply awr_ok_cons_gen;
  [ reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb]; exact U21
  | cbn [YP09.r_wlo YP09.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; right; left; split;
    [ exists (r, r + REG_SIZE); split; [left; reflexivity | cbn [fst snd]; unfold REG_SIZE; lia]
    | exists r, REG_SIZE; split; [exact Hin | change (req_size REG_SIZE) with 288; lia] ]
  | ] ].
(* The return at 0x819d0: the restored registers from the frame atoms, a0 = n, then the post (dpl_post) at the FP
   state fy of the walk's state (RETx: paj_ret_at at fy; HFy HCy: apost_baseF's two FP facts of fy). *)
Ltac dpl_regeq E3 :=
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb]; rewrite E3; first [reflexivity | f_equal; apply bv_eq; reflexivity].
Ltac dpl_fin RETx fy HFy HCy W regs0 n Usp E3 E4 E18 E19 E21 E22 E26 E27 E33 E45 EF Hra Hsegs HJF HPL HINV Hs Hsl HBYc
  KEEPR Hb0r Hnm1 Hnm2 :=
lazymatch goal with HS : st_ok_pi _ _ ?Ef ?ssf (restrict _ ?msc) |- _ =>
let HRA := fresh "HRA" in let HRF := fresh "HRF" in let HPF := fresh "HPF" in
pose proof (st_ok_pi_region_nth Ef ssf (restrict (w_H W) msc) 0 dpl_RowF HS ltac:(vm_compute; reflexivity)) as HRA;
pose proof (st_ok_pi_region_nth Ef ssf (restrict (w_H W) msc) 2 dpl_RFF HS ltac:(vm_compute; reflexivity)) as HRF;
cbn [restrict ms_mem] in HRA, HRF;
assert (HPF : aregs_preserved regs0 (ms_regs msc));
[ apply dpl_aregs;
  [ rewrite (dpl_reg_off _ _ _ _ _ (Z_to_bv 5 2) 2 96 (spZ regs0) HS ltac:(vm_compute; reflexivity)
      ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb]; rewrite Usp; lia));
    unfold spZ; rewrite Z_to_bv_bv_unsigned; first [reflexivity | f_equal; apply bv_eq; reflexivity]
  | apply (dpl_reg_atom _ _ _ _ _ _ 3 _ HS); [vm_compute; reflexivity | dpl_regeq E3]
  | apply (dpl_reg_atom _ _ _ _ _ _ 4 _ HS); [vm_compute; reflexivity | dpl_regeq E4]
  | let j := fresh "j" in let Hj := fresh "Hj" in intros j Hj; apply (dpl_reg_atom _ _ _ _ _ _ (34 + j) _ HS);
    [ do 11 (destruct j as [|j]; [vm_compute; reflexivity|]); lia
    | repeat (rewrite YN3v.ew_havoc_old by lia); exact (EF j Hj) ]
  | apply (dpl_reg_atom _ _ _ _ _ _ 26 _ HS); [vm_compute; reflexivity | dpl_regeq E26]
  | apply (dpl_reg_atom _ _ _ _ _ _ 27 _ HS); [vm_compute; reflexivity | dpl_regeq E27] ]
| ];
let R1 := fresh "R1" in let R10 := fresh "R10" in
assert (R1 : getr (ms_regs msc) 1 = getr regs0 1)
  by (apply (dpl_reg_atom _ _ _ _ _ _ 34 _ HS);
      [ vm_compute; reflexivity
      | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb]; transitivity (getr regs0 (Z_to_bv 5 (nth 0 dsave_reg 0)));
        [exact (EF 0%nat ltac:(lia)) | first [reflexivity | f_equal; apply bv_eq; reflexivity]] ]);
assert (R10 : getr (ms_regs msc) 10 = w64 n)
  by (apply (dpl_reg_atom _ _ _ _ _ _ 45 _ HS); [vm_compute; reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb]; exact E45]);
eapply (RETx W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
let mat := fresh "mat" in intros mat; rewrite R1, Hra;
eapply (dpl_post fy _ _ W regs0 _ _ _ _ _ _ _ _ _ (ms_regs msc) (ms_mem msc) _ _ Ef HFy HCy
  ltac:(apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJF) HPF HPL HINV Hs Hsl R10 HBYc KEEPR HRA HRF);
[ cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb]; exact E18 | exact Hb0r | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb]; exact E19
| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb]; exact E21 | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb]; exact E22
| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb]; exact E33 | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb]; exact E45
| lia | lia | exact Hnm1 | exact Hnm2 ]
end.

(* The placement, 0x8190c (after s5 = r + 56 n): memset of the row, the stores of base, nch and pinned, the
   snprintf of the name when nm is not NULL, n + 1, and the return of n. *)
Lemma dp_walk : forall ly S W (regs0 : bvmap 5 word) mem0 md0 ch r k nm b0 bs s G (regsc : bvmap 5 word) memc mdc b p,
dpre ly S W regs0 mem0 md0 ch r k nm b0 bs s G ->
dinv regs0 ly S W mem0 md0 r nm bs regsc memc mdc ->
reac_boxreg_declare_c.declare_placed bs k b0 b p ->
getr regsc 21 = w64 (r + 56 * Boxreg.bx_n bs) -> getr regsc 22 = w64 b -> getr regsc 19 = w64 k ->
getr regsc 18 = w64 b0 ->
SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + 6592)) memc (seg_rom SEGS)) mdc)
  (treac_boxreg_declare_post regs0 ly S W mem0 md0 r k b0 bs s).
Proof.
intros ly S W regs0 mem0 md0 ch r k nm b0 bs s G regsc memc mdc b p DP DI HPL H21 H22 H19 H18.
destruct (dpl_entry ly S W regs0 mem0 md0 ch r k nm b0 bs s G regsc memc mdc b p DP DI HPL H21 H22 H19) as [HS SHOK].
pose proof DP as (HPRE & HRO & H10 & H11 & H12 & H13 & Hkr & Hb0r & Hin & HBY & HINV & HNM & HTV & HISV & HGM & HFMT
  & HFG & HFL & HFH & HFP2 & HFRM).
pose proof DI as (HJ & Hsp & Hgp' & Htp' & H26 & H27 & HFR & HBYc & Hs0 & Hs1 & Hs8 & Hs7).
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof DSTK_val as WS. assert (Hes : ESTACK = 4096) by reflexivity.
destruct (dm_boxreg_inv_facts bs HINV) as (HL & Hn5 & Hf40 & HROWS).
destruct (al_blocks _ _ LAWS ly S W mem0 md0 r REG_SIZE HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & _ & _).
change (req_size REG_SIZE) with 288 in *.
pose proof HPL as ((Hev & Hk & Hkf) & Hn & HPB).
assert (Hb : 0 <= b <= 38).
{ destruct HPB as [(Hb0 & -> & _ & (_ & Hbk & _)) | (_ & _ & Hb0 & Hlf)]; [lia|].
  destruct (dm_lowest_free_range bs k b ltac:(lia) Hlf) as [-> | Hz]; lia. }
set (n := Boxreg.bx_n bs) in *.
remember (dplE regsc regs0 r n) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold dplE; apply Eimg_env).
assert (E1 : ew E 1 = getr regsc 1) by (subst E; exact (dpl_E_low regsc regs0 r n 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regsc 2) by (subst E; exact (dpl_E_low regsc regs0 r n 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs0 3) by (subst E; rewrite (dpl_E_low regsc regs0 r n 3 3%bv eq_refl); exact Hgp').
assert (E4 : ew E 4 = getr regs0 4) by (subst E; rewrite (dpl_E_low regsc regs0 r n 4 4%bv eq_refl); exact Htp').
assert (E8 : ew E 8 = Z_to_bv 64 nm) by (subst E; rewrite (dpl_E_low regsc regs0 r n 8 8%bv eq_refl); exact Hs0).
assert (E18 : ew E 18 = Z_to_bv 64 b0) by (subst E; rewrite (dpl_E_low regsc regs0 r n 18 18%bv eq_refl); exact H18).
assert (E19 : ew E 19 = Z_to_bv 64 k) by (subst E; rewrite (dpl_E_low regsc regs0 r n 19 19%bv eq_refl); exact H19).
assert (E21 : ew E 21 = Z_to_bv 64 (r + 56 * n))
  by (subst E; rewrite (dpl_E_low regsc regs0 r n 21 21%bv eq_refl); exact H21).
assert (E22 : ew E 22 = Z_to_bv 64 b) by (subst E; rewrite (dpl_E_low regsc regs0 r n 22 22%bv eq_refl); exact H22).
assert (E26 : ew E 26 = getr regs0 26) by (subst E; rewrite (dpl_E_low regsc regs0 r n 26 26%bv eq_refl); exact H26).
assert (E27 : ew E 27 = getr regs0 27) by (subst E; rewrite (dpl_E_low regsc regs0 r n 27 27%bv eq_refl); exact H27).
assert (E32 : ew E 32 = Z_to_bv 64 DSB) by (subst E; exact (dpl_E_ext regsc regs0 r n 0 ltac:(lia))).
assert (E33 : ew E 33 = Z_to_bv 64 r) by (subst E; exact (dpl_E_ext regsc regs0 r n 1 ltac:(lia))).
assert (E45 : ew E 45 = Z_to_bv 64 n) by (subst E; exact (dpl_E_ext regsc regs0 r n 13 ltac:(lia))).
assert (EF : forall j, (j < 11)%nat -> ew E (34 + j) = getr regs0 (Z_to_bv 5 (nth j dsave_reg 0)))
  by (intros j Hj; subst E; exact (dpl_E_frame regsc regs0 r n j Hj)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs0 - 96) by (rewrite E2, Hsp; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = r + 56 * n) by (rewrite E21; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = r) by (rewrite E33; apply unsigned_lit_small; lia).
clear HEdef.
assert (KEEPR : forall a, dpl_PR r n a -> aview SEGS (w_H W) memc a = aview SEGS (w_H W) memc a) by reflexivity.
(* 1. 0x8190c .. 0x81918: the arguments of __asan_memset (row, 0, 56) *)
paj_run_tok RUN HS HJ SHOK Dspan; [dpl_awr r Hin U21 U33 |].
lazymatch goal with HFr : frame_of _ _ (mrestrict _ memc) (mrestrict _ ?m2) |- _ =>
  pose proof (dpl_frame_keep W E _ memc m2 (dpl_PR r n) (fun a => aview SEGS (w_H W) memc a) HFr
    ltac:(dpl_nowr U21 U33) KEEPR) as K2; clear KEEPR; rename K2 into KEEPR end.
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
pmkst HS.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
  assert (Qsp : spZ rg = spZ regs0 + -96) by (unfold spZ at 1; rewrite Rsp, Usp; lia) end.
(* 2. __asan_memset (row, 0, 56): the row reads 0; every other byte above its stack is kept. *)
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply SRr_bind;
[ eapply (aj_intrin_at SEGS B LAWS Hsegs OSet (SIGMA BS___asan_memset) AMEMSET W rg mm
    DSTK (spZ regs0) [(r, r + REG_SIZE)] ly S W mem0 md0 [] ly S _ 0 (r + 56 * n) 0 56 (-96) _ HJ);
  [ rewrite Ra0, E21; reflexivity
  | rewrite Ra1; reflexivity
  | rewrite Ra2; reflexivity
  | lia | lia | lia
  | exact Qsp
  | reflexivity
  | lia
  | rewrite WS, Hes; lia
  | rewrite Rgp, E3; exact Hgp
  | rewrite Rtp, E4; exact Htp
  | exact Rra
  | apply ret_ok_codeptr_v; [lia | reflexivity]
  | intros a Ha; split;
    [ right; left; split;
      [ exists (r, r + REG_SIZE); split; [left; reflexivity | cbn [fst snd]; unfold REG_SIZE; lia]
      | exists r, REG_SIZE; split; [exact Hin | change (req_size REG_SIZE) with 288; lia] ]
    | rewrite Hes; lia ]
  | eapply (amem_range_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hin); change (req_size REG_SIZE) with 288; lia
  | eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hin);
    change (req_size REG_SIZE) with 288; lia
  | intros _; eapply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hin);
    change (req_size REG_SIZE) with 288; lia
  | exact I ]
| ]
end.
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0 & Heff & Hfr & Hpres2).
assert (K2 : forall a, dpl_PR r n a -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a).
{ intros a Ha. rewrite <- (KEEPR a Ha). unfold dpl_PR in Ha. apply Hfr; [lia | lia | rewrite Hes; lia]. }
clear KEEPR. rename K2 into KEEPR.
assert (NAME0 : forall a, r + 56 * n + 24 <= a < r + 56 * n + 56 -> aview SEGS (w_H W) mem2 a = Some 0).
{ intros a Ha. replace a with (r + 56 * n + (a - (r + 56 * n))) by lia. rewrite (Heff (a - (r + 56 * n))) by lia.
  reflexivity. }
(* Back at the return slot: the frame and the word n are kept by the wrapper. *)
jafter_call_keep_hi HS 512%nat regs2 (mrestrict (w_H W) mem2) HP2 [0%nat; 1%nat] HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp; intros a Ha; [|lia].
    apply (mbyte_of_aview SEGS). apply Hfr; [lia | lia | rewrite Hes; lia].
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite U33; intros a Ha.
    + apply (mbyte_of_aview SEGS). apply Hfr; [lia | lia | rewrite Hes; lia].
    + intros _. apply (apresent_writable SEGS).
      destruct (al_blocks _ _ LAWS _ _ _ _ _ r REG_SIZE (proj1 HJ2) Hin) as (_ & _ & _ & _ & Hpr2 & _).
      change (req_size REG_SIZE) with 288 in Hpr2. exact (proj1 (Hpr2 a ltac:(lia))). }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
assert (HEI1 : img_env VAL A_LIM (havoc E 512 (map (getr regs2) CLOB)))
  by (apply img_env_havoc_hi; [exact HEI | cbv; lia]).
lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
(* The row after the memset: its first 24 bytes as a region (window 8 .. 24), 0. *)
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
assert (HRr : region_ok SEGS Ex (ms_mem (restrict Hh msx)) dpl_RowA);
[ cbn [restrict ms_mem mkst]; unfold dpl_RowA, region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ew havoc Nat.ltb Nat.leb];
  rewrite U21;
  destruct (al_blocks _ _ LAWS _ _ _ _ _ r REG_SIZE (proj1 HJ2) Hin) as (_ & _ & _ & _ & Hpr & _);
  change (req_size REG_SIZE) with 288 in Hpr;
  split; [lia|]; split; [lia|];
  split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (Hpr (r + 56 * n + o) ltac:(lia)))|];
  constructor; [|constructor];
  intros i Hi; cbn [YP09.c_off YP09.c_val YP09.c_len YP09.cv_len] in Hi |- *;
  exists (Z_to_bv 8 0); split; [reflexivity|];
  rewrite Z.add_0_r; apply dpl_mbyte_zero; rewrite (Heff i) by lia; reflexivity
| pose proof (st_ok_pi_add_region Ex ssx (restrict Hh msx) dpl_RowA HS eq_refl HRr
    ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
          cbn [all_disjoint]; unfold extent_disjoint, dpl_RowA;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val ew havoc Nat.ltb Nat.leb]; rewrite U21, U33, Usp;
          split; [lia | split; [lia | exact I]])) as HS2; clear HS HRr; rename HS2 into HS ]
end.
clear SHOK.
assert (SHOK : sh_ok SEGS DBx dpl_SH (havoc E 512 (map (getr regs2) CLOB)) (mrestrict (w_H W) mem2)).
{ unfold sh_ok, dpl_SH. constructor; [|constructor; [|constructor]].
  - eapply (dshent_block ly S W mem2 md2 _ 21 (r + 56 * n) r REG_SIZE 0 56 (proj1 HJ2) Hin).
    + unfold DBx. rewrite U_SOff. cbn [ew havoc Nat.ltb Nat.leb]. rewrite E32, unsigned_lit_small by (unfold DSB; lia).
      reflexivity.
    + rewrite U_SOff. cbn [ew havoc Nat.ltb Nat.leb]. rewrite U21, Z.add_0_r. apply zcanon_id. unfold M64. lia.
    + lia.
    + lia.
    + change (req_size REG_SIZE) with 288. lia.
  - eapply (dshent_block ly S W mem2 md2 _ 33 r r REG_SIZE 0 288 (proj1 HJ2) Hin).
    + unfold DBx. rewrite U_SOff. cbn [ew havoc Nat.ltb Nat.leb]. rewrite E32, unsigned_lit_small by (unfold DSB; lia).
      reflexivity.
    + rewrite U_SOff. cbn [ew havoc Nat.ltb Nat.leb]. rewrite U33, Z.add_0_r. apply zcanon_id. unfold M64. lia.
    + lia.
    + lia.
    + change (req_size REG_SIZE) with 288. lia. }
(* 3. 0x8191c .. 0x8196c: the stores of base (+8), nch (+12) and pinned (+20), each after its shadow check *)
paj_run_tok RUN HS HJ2 SHOK Dspan; [dpl_awr r Hin U21 U33 |].
lazymatch goal with HFr : frame_of _ _ (mrestrict _ mem2) (mrestrict _ ?m3) |- _ =>
  pose proof (dpl_frame_keep W _ _ mem2 m3 (dpl_PR r n) (fun a => aview SEGS (w_H W) memc a) HFr
    ltac:(dpl_nowr U21 U33) KEEPR) as K2; clear KEEPR; rename K2 into KEEPR;
  pose proof (dpl_frame_keep W _ _ mem2 m3 (fun a => r + 56 * n + 24 <= a < r + 56 * n + 56) (fun _ => Some 0) HFr
    ltac:(dpl_nowr U21 U33) NAME0) as K3; clear NAME0; rename K3 into NAME0 end.
cbv beta in KEEPR, NAME0.
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
assert (Hnmr : 0 <= nm < 2 ^ 64).
{ destruct HNM as [(-> & _) | (_ & _ & _ & nn & Hnin & _)]; [lia|].
  destruct (al_blocks _ _ LAWS ly S W mem0 md0 nm nn HAR Hnin) as (_ & Hn4096 & Hnceil & _ & _ & _ & Hnn).
  pose proof (req_size_pos nn ltac:(lia)). lia. }
(* 0x8196c  beqz s0 (nm) *)
psrr_branch_tok RUN BR HS SHOK Dspan.
{ lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
    rewrite (dpl_br_eq0 Ex 8 nm ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb]; exact E8) Hnmr) in Hc end.
  apply Z.eqb_eq in Hc.
  (* 4a. nm = NULL: the name stays memset's zeros; n + 1 at r + 280, the restores and the return of n *)
  paj_run_tok RUN HS HJ2 SHOK Dspan; [dpl_awr r Hin U21 U33 |].
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ ?m3) (mrestrict _ ?m4) |- _ =>
    pose proof (dpl_frame_keep W _ _ m3 m4 (dpl_PR r n) (fun a => aview SEGS (w_H W) memc a) HFr
      ltac:(dpl_nowr U21 U33) KEEPR) as K2; clear KEEPR; rename K2 into KEEPR;
    pose proof (dpl_frame_keep W _ _ m3 m4 (fun a => r + 56 * n + 24 <= a < r + 56 * n + 56) (fun _ => Some 0) HFr
      ltac:(dpl_nowr U21 U33) NAME0) as K3; clear NAME0; rename K3 into NAME0 end.
  cbv beta in KEEPR, NAME0.
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
  destruct HNM as [(_ & ->) | (Hnz & _)]; [|exfalso; exact (Hnz Hc)].
  assert (Hs : Forall (fun c => 0 < c < 256) (@nil Z)) by constructor.
  assert (Hsl : Z.of_nat (length (@nil Z)) < 2 ^ 31 - 1) by (cbn; lia).
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msc) =>
    destruct (dm_name_nil_premises (aview SEGS (w_H W) (ms_mem msc)) (r + 56 * n + 24)
      ltac:(intros j Hj; apply NAME0; lia)) as [Hnm1 Hnm2] end.
  assert (HFy0 : forall q : bv 5, bv_unsigned q <> 10 -> Sem.reg_get (@fp_regs fx) q = Sem.reg_get (@fp_regs fx) q)
    by (intros; reflexivity).
  assert (HCy0 : @fp_csr fx = @fp_csr fx \/ Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0) by (left; reflexivity).
  dpl_fin RET fx HFy0 HCy0 W regs0 n Usp E3 E4 E18 E19 E21 E22 E26 E27 E33 E45 EF Hra Hsegs HJ2 HPL HINV Hs Hsl HBYc
    KEEPR Hb0r Hnm1 Hnm2. }
lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
  rewrite (dpl_br_eq0 Ex 8 nm ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb]; exact E8) Hnmr) in Hc end.
apply Z.eqb_neq in Hc.
(* 4b. nm <> NULL: up to the call of snprintf (row + 24, 32, "%s", nm) *)
paj_run_tok RUN HS HJ2 SHOK Dspan; [dpl_awr r Hin U21 U33 |].
lazymatch goal with HFr : frame_of _ _ (mrestrict _ ?m3) (mrestrict _ ?m4) |- _ =>
  pose proof (dpl_frame_keep W _ _ m3 m4 (dpl_PR r n) (fun a => aview SEGS (w_H W) memc a) HFr
    ltac:(dpl_nowr U21 U33) KEEPR) as K2; clear KEEPR; rename K2 into KEEPR;
  pose proof (dpl_frame_keep W _ _ m3 m4 (fun a => r + 56 * n + 24 <= a < r + 56 * n + 56) (fun _ => Some 0) HFr
    ltac:(dpl_nowr U21 U33) NAME0) as K3; clear NAME0; rename K3 into NAME0 end.
cbv beta in KEEPR, NAME0.
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
destruct HNM as [(Hz & _) | (_ & HFs & Hsl & nn & Hnin & Hnn & Hdisj & Hby)]; [exfalso; exact (Hc Hz)|].
pmkst HS.
prreg HS (10%bv : bv 5) Sa0. prreg HS (11%bv : bv 5) Sa1. prreg HS (12%bv : bv 5) Sa2. prreg HS (13%bv : bv 5) Sa3.
prreg HS (1%bv : bv 5) Sra. prreg HS (2%bv : bv 5) Ssp. prreg HS (3%bv : bv 5) Sgp. prreg HS (4%bv : bv 5) Stp.
pose proof YM05.alloc_ceiling_val as Hacv.
pose proof (blk_off_imgP B ly S W mem0 md0 r REG_SIZE HAR Hin) as Hrimg. change (req_size REG_SIZE) with 288 in Hrimg.
unfold IMG_HI in HFH.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
  assert (Qsp2 : spZ rg = spZ regs0 + -96) by (unfold spZ at 1; rewrite Ssp, Usp; lia);
  pose proof HJ2 as (HAR3 & _ & _ & _ & _ & _ & _ & _ & HJF1 & HJF2 & HJF3 & _);
  (* the read-only image at the call: the entry's arodata_okP through the journal's image clause *)
  assert (ROMK : asn_rom_kept SEGS B W mm);
  [ intros a Hrom Hown Herr;
    assert (Himg : in_img SEGS a) by (destruct Hrom as (sg & Hsg & _ & Hr'); exists sg; split; [exact Hsg | exact Hr']);
    assert (Hspa : fp_spares [(r, r + REG_SIZE)] a)
      by (apply fp_spares_closed; exact (sink_closed_cons (r, r + REG_SIZE) [] ltac:(cbn; lia) sink_closed_nil));
    rewrite (HJF3 a Himg Hown Herr Hspa); apply HRO; [left; exact Hrom | exact Hown | exact Herr]
  | ];
  (* the format "%s": its bytes through ROMK, its shadow from globs_marked and img_shadow_vis *)
  assert (HF1 : forall i, 0 <= i < 3 -> aview SEGS (w_H W) mm (A_declare_fmtP + i) = Some (nth (Z.to_nat i) ASN_FMT 0));
  [ intros i Hi; destruct (HFMT i ltac:(change (Z.of_nat (length ASN_FMT)) with 3; lia)) as (Hrom & Hown & Herr & Hfb);
    rewrite (ROMK _ Hrom Hown Herr); exact Hfb
  | ];
  destruct (ro_read_ok_glob SEGS B G ly S W mm _ A_declare_fmtP 3 A_declare_fmtP 3 HGM HFG HISV HAR3
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold IMG_HI; lia)) as [HFRA HFHV];
  (* the name: a heap block apart from the registry, kept by the journal *)
  destruct (al_blocks _ _ LAWS ly S W mm _ nm nn HAR3 Hnin) as (Hnm16 & Hnm4096 & Hnmceil & Hnmia & Hnmpr & _ & Hnn0);
  assert (Hrq : req_size nn = nn) by (unfold req_size; destruct (Z.eqb_spec nn 0); lia);
  rewrite Hrq in Hnmceil, Hnmpr;
  assert (HWE : asn_word_end nm (Z.of_nat (length s)) <= nm + round_up nn 8)
    by (unfold asn_word_end, round_up; Z.div_mod_to_equations; lia);
  assert (HRU : nm + round_up nn 8 <= alloc_ceiling) by (unfold round_up; Z.div_mod_to_equations; lia);
  assert (HSB : forall i, 0 <= i <= Z.of_nat (length s) ->
    aview SEGS (w_H W) mm (nm + i) = Some (nth (Z.to_nat i) (s ++ [0]) 0));
  [ intros i Hi; rewrite (HJF2 nm nn i Hnin Hnin ltac:(rewrite Hrq; lia)); [exact (Hby i Hi)|];
    intros (rr & [<- | []] & Hrr); cbn [fst snd] in Hrr; unfold REG_SIZE in *; lia
  | ];
  assert (HST : forall a, nm + Z.of_nat (length s) < a < asn_word_end nm (Z.of_nat (length s)) ->
    aview SEGS (w_H W) mm a <> None);
  [ intros a Ha; destruct (Z_lt_ge_dec a (nm + nn)) as [Hlt | Hge];
    [ apply (aview_some_of_apresent SEGS); exact (proj1 (Hnmpr a ltac:(lia)))
    | exact (HTV ly S W mm _ nm nn a HAR3 Hnin ltac:(lia)) ]
  | ];
  eapply (dpl_snprintf_at W rg mm DSTK (spZ regs0) [(r, r + REG_SIZE)] ly S W mem0 md0 [] ly S _ 0 (-96) _
      (r + 56 * n + 24) 32 A_declare_fmtP nm s r REG_SIZE _ HJ2);
    [ exact Qsp2 | reflexivity | lia | rewrite WS; unfold ESTACK; lia
    | rewrite Sgp, E3; exact Hgp | rewrite Stp, E4; exact Htp | exact Sra | apply ret_ok_codeptr_v; [lia | reflexivity]
    | rewrite Sa0, U21; reflexivity
    | rewrite Sa1; reflexivity
    | rewrite Sa2; unfold A_declare_fmtP; exact (img_env_atomP E (A_OBJ 10) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))
    | rewrite Sa3, E8; reflexivity
    | lia
    | exact Hin | lia | unfold REG_SIZE; lia
    | intros a Ha; exists (r, r + REG_SIZE); split; [left; reflexivity | cbn [fst snd]; unfold REG_SIZE; lia]
    | intros a Ha; unfold ESTACK; lia
    | exact HF1
    | lia
    | apply amem_range_high; [lia | left; lia | lia]
    | lia
    | exact HFP2
    | intros a Ha; unfold ESTACK; lia
    | destruct Hrimg as [Hri | Hri]; [right | left]; lia
    | exact HFRA | exact HFHV
    | exact HFs | exact Hsl | lia
    | exact HSB | exact HST
    | eapply (SnprintfAmem.amem8_of_block SEGS B _ _ _ _ _ nm nn nm _ LAWS HAR3 Hnin); rewrite ?Hrq; lia
    | intros a Ha; unfold ESTACK; lia
    | destruct Hdisj as [Hd | Hd]; [left | right];
      [ assert (nm + round_up nn 8 <= r) by (unfold round_up; Z.div_mod_to_equations; lia); lia | unfold REG_SIZE in Hd; lia ]
    | eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR3 Hnin); rewrite ?Hrq; lia
    | eapply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR3 Hnin); rewrite ?Hrq; lia
    | exact ROMK
    | exact HFRM
    | ]
end.
(* The wrapper's continuation; its FP state fx3 comes last, after the facts the engine needs at the return slot. *)
intros regs3 mem3 md3 HJ3 HP3 Hout Hkeep3 Hpres3.
(* After snprintf: the name field holds asn_out 32 s, the rest of the row's name memset's zeros; all else kept. *)
assert (Hln : 1 <= Z.of_nat (length (SnprintfDef.asn_out 32 s)) <= 32)
  by (unfold SnprintfDef.asn_out; rewrite length_app, length_firstn; cbn [length]; lia).
assert (K2 : forall a, dpl_PR r n a -> aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) memc a).
{ intros a Ha. rewrite <- (KEEPR a Ha). unfold dpl_PR in Ha. apply Hkeep3; [lia | lia | unfold ESTACK; lia]. }
clear KEEPR. rename K2 into KEEPR.
assert (NAMEZ : forall a, r + 56 * n + 24 + Z.of_nat (length (SnprintfDef.asn_out 32 s)) <= a < r + 56 * n + 56 ->
  aview SEGS (w_H W) mem3 a = Some 0).
{ intros a Ha. rewrite Hkeep3 by (unfold ESTACK; lia). apply NAME0. lia. }
assert (NAMEO : forall a, r + 56 * n + 24 <= a < r + 56 * n + 24 + Z.of_nat (length (SnprintfDef.asn_out 32 s)) ->
  aview SEGS (w_H W) mem3 a = Some (nth (Z.to_nat (a - (r + 56 * n + 24))) (SnprintfDef.asn_out 32 s) 0)).
{ intros a Ha. replace a with (r + 56 * n + 24 + (a - (r + 56 * n + 24))) at 1 by lia. apply Hout. lia. }
clear NAME0.
(* Back at the return slot: the row region, the frame and the word n are kept by the wrapper. *)
jafter_call_keep_hi HS 600%nat regs3 (mrestrict (w_H W) mem3) HP3 [0%nat; 1%nat; 2%nat] HS3.
match type of HS3 with ?tq -> _ => assert (HRK : tq); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ r REG_SIZE (proj1 HJ3) Hin) as (_ & _ & _ & _ & Hpr3 & _).
  change (req_size REG_SIZE) with 288 in Hpr3.
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val ew havoc Nat.ltb Nat.leb]; rewrite U21;
      intros a Ha.
    + apply (mbyte_of_aview SEGS). apply Hkeep3; [lia | lia | unfold ESTACK; lia].
    + intros _. apply (apresent_writable SEGS). exact (proj1 (Hpr3 a ltac:(lia))).
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val ew havoc Nat.ltb Nat.leb]; rewrite Usp;
      intros a Ha; [|lia].
    apply (mbyte_of_aview SEGS). apply Hkeep3; [lia | lia | unfold ESTACK; lia].
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val ew havoc Nat.ltb Nat.leb]; rewrite U33;
      intros a Ha.
    + apply (mbyte_of_aview SEGS). apply Hkeep3; [lia | lia | unfold ESTACK; lia].
    + intros _. apply (apresent_writable SEGS). exact (proj1 (Hpr3 a ltac:(lia))). }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
assert (HEIs : img_env VAL A_LIM (havoc (havoc E 512 (map (getr regs2) CLOB)) 600 (map (getr regs3) CLOB)))
  by (apply img_env_havoc_hi; [exact HEI1 | cbv; lia]).
lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
clear SHOK.
assert (SHOK : sh_ok SEGS DBx dpl_SH (havoc (havoc E 512 (map (getr regs2) CLOB)) 600 (map (getr regs3) CLOB))
  (mrestrict (w_H W) mem3)).
{ unfold sh_ok, dpl_SH. constructor; [|constructor; [|constructor]].
  - eapply (dshent_block ly S W mem3 md3 _ 21 (r + 56 * n) r REG_SIZE 0 56 (proj1 HJ3) Hin).
    + unfold DBx. rewrite U_SOff. cbn [ew havoc Nat.ltb Nat.leb]. rewrite E32, unsigned_lit_small by (unfold DSB; lia).
      reflexivity.
    + rewrite U_SOff. cbn [ew havoc Nat.ltb Nat.leb]. rewrite U21, Z.add_0_r. apply zcanon_id. unfold M64. lia.
    + lia.
    + lia.
    + change (req_size REG_SIZE) with 288. lia.
  - eapply (dshent_block ly S W mem3 md3 _ 33 r r REG_SIZE 0 288 (proj1 HJ3) Hin).
    + unfold DBx. rewrite U_SOff. cbn [ew havoc Nat.ltb Nat.leb]. rewrite E32, unsigned_lit_small by (unfold DSB; lia).
      reflexivity.
    + rewrite U_SOff. cbn [ew havoc Nat.ltb Nat.leb]. rewrite U33, Z.add_0_r. apply zcanon_id. unfold M64. lia.
    + lia.
    + lia.
    + change (req_size REG_SIZE) with 288. lia. }
(* 5. 0x81988 .. 0x819d0: the shadow check of r + 280, n + 1 at r + 280, the restores and the return of n, at the FP
   state fx3 the wrapper returned at (no instruction there touches an f register or fcsr) *)
intros fx3 HFy3 HCy3r.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh (@mkst _ ?rgx ?pcx ?mmx ?romx)) =>
  pose proof (dst_ok_pi_fx fx fx3 Ex ssx Hh rgx pcx mmx romx HS) as HS4 end.
clear HS. rename HS4 into HS.
pose proof (paj_run (fx := fx3) B LAWS) as RUN3.
pose proof (paj_ret_at (fx := fx3) (PL := PL_box) (PI := PI)) as RET3.
assert (HCy3 : @fp_csr fx3 = @fp_csr fx \/ Z.land (Z.shiftr (bv_unsigned (@fp_csr fx3)) 5) 7 = 0) by (right; exact HCy3r).
paj_run_tok RUN3 HS HJ3 SHOK Dspan; [dpl_awr r Hin U21 U33 |].
lazymatch goal with HFr : frame_of _ _ (mrestrict _ ?m3) (mrestrict _ ?m4) |- _ =>
  pose proof (dpl_frame_keep W _ _ m3 m4 (dpl_PR r n) (fun a => aview SEGS (w_H W) memc a) HFr
    ltac:(dpl_nowr U21 U33) KEEPR) as K2; clear KEEPR; rename K2 into KEEPR;
  pose proof (dpl_frame_keep W _ _ m3 m4
    (fun a => r + 56 * n + 24 + Z.of_nat (length (SnprintfDef.asn_out 32 s)) <= a < r + 56 * n + 56) (fun _ => Some 0)
    HFr ltac:(dpl_nowr U21 U33) NAMEZ) as K3; clear NAMEZ; rename K3 into NAMEZ;
  pose proof (dpl_frame_keep W _ _ m3 m4
    (fun a => r + 56 * n + 24 <= a < r + 56 * n + 24 + Z.of_nat (length (SnprintfDef.asn_out 32 s)))
    (fun a => Some (nth (Z.to_nat (a - (r + 56 * n + 24))) (SnprintfDef.asn_out 32 s) 0))
    HFr ltac:(dpl_nowr U21 U33) NAMEO) as K4; clear NAMEO; rename K4 into NAMEO end.
cbv beta in KEEPR, NAMEZ, NAMEO.
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msc) =>
  assert (Hnm1 : forall j, 0 <= j < Z.of_nat (length (SnprintfDef.asn_out 32 s)) ->
    aview SEGS (w_H W) (ms_mem msc) (r + 56 * n + 24 + j) = Some (nth (Z.to_nat j) (SnprintfDef.asn_out 32 s) 0))
    by (intros j Hj; rewrite NAMEO by lia; replace (r + 56 * n + 24 + j - (r + 56 * n + 24)) with j by lia; reflexivity);
  assert (Hnm2 : forall j, Z.of_nat (length (SnprintfDef.asn_out 32 s)) <= j < 32 ->
    aview SEGS (w_H W) (ms_mem msc) (r + 56 * n + 24 + j) = Some 0)
    by (intros j Hj; apply NAMEZ; lia) end.
dpl_fin RET3 fx3 HFy3 HCy3 W regs0 n Usp E3 E4 E18 E19 E21 E22 E26 E27 E33 E45 EF Hra Hsegs HJ3 HPL HINV HFs Hsl HBYc
  KEEPR Hb0r Hnm1 Hnm2.
Qed.

(* ---- the loop head, 0x81878 (row i) ---- *)
(* atoms: 32 the shadow base, 33 row i's base (r + 56 i + 8), 34 row i's nch (r + 56 i + 12), 35 .. 45 the 11 saved
   words of the frame (dsave_reg order: ra, s0 .. s9). Registers: a0 = a3 = r + 56 i + 12 (atom 13), a4 = the shadow
   address of r + 56 i + 8, s8 = the shadow base. *)
Definition dl_frame : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 96 0 0 (map (fun j => YP09.mkChunk (nth j dsave_off 0) (CVal 8 (SOff (35 + j) 0))) (seq 0 11)).
Definition dl_regs : list sv :=
sr_set (sr_set (sr_set sr_atoms 10%bv (SOff 13 0)) 14%bv (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff 13 (-4)) (SLit 3))))
  24%bv (SOff 32 0).
Definition dl_row : YP09.region :=
YP09.mkRegion (Some 13%nat) (-12) 44 0 0 [YP09.mkChunk (-4) (CVal 4 (SOff 33 0)); YP09.mkChunk 0 (CVal 4 (SOff 34 0))].
Definition dl_facts : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (13%nat, mkAF 4108 140737479966720 2);
  (32%nat, mkAF DSB DSB 0); (33%nat, mkAF 0 38 0); (34%nat, mkAF 2 40 0); (12%nat, mkAF 2 40 0); (18%nat, mkAF 0 38 0);
  (19%nat, mkAF 2 40 0); (15%nat, mkAF 1 4 0)] [] [].
Definition ss_dl : sstate := mkSS 6444 dl_regs [dl_frame; dl_row] None dl_facts.
Definition dl_SH : list shent := [mkSHE 13 (-12) 44].
Definition dl_extra (regs0 : bvmap 5 word) (bs : list byte) (i : Z) : list word :=
map (Z_to_bv 64) [DSB; Boxreg.bx_base bs i; Boxreg.bx_nch bs i] ++
map (fun j => getr regs0 (Z_to_bv 5 (nth j dsave_reg 0))) (seq 0 11).
Definition dlE (regsc regs0 : bvmap 5 word) (bs : list byte) (i : Z) : env := Eimg (Ereg regsc (dl_extra regs0 bs i)).

Ltac dl_nz := let Hc := fresh "Hc" in intros Hc; apply (f_equal bv_unsigned) in Hc; vm_compute in Hc; discriminate Hc.

Lemma dl_ew : forall (regsc regs0 : bvmap 5 word) bs i,
(forall n, (n < A_TEXT)%nat -> ew (dlE regsc regs0 bs i) n = ew (Ereg regsc (dl_extra regs0 bs i)) n) /\
ew (dlE regsc regs0 bs i) 32 = Z_to_bv 64 DSB /\
ew (dlE regsc regs0 bs i) 33 = Z_to_bv 64 (Boxreg.bx_base bs i) /\
ew (dlE regsc regs0 bs i) 34 = Z_to_bv 64 (Boxreg.bx_nch bs i) /\
(forall j, (j < 11)%nat -> ew (dlE regsc regs0 bs i) (35 + j) = getr regs0 (Z_to_bv 5 (nth j dsave_reg 0))).
Proof.
intros regsc regs0 bs i. unfold dlE.
split; [intros n Hn; apply Eimg_low; exact Hn|].
split; [rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 0)|].
split; [rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 1)|].
split; [rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 2)|].
intros j Hj. rewrite Eimg_low by (unfold A_TEXT; lia).
replace (35 + j)%nat with (32 + (3 + j))%nat by lia. rewrite ew_Ereg_extra.
do 11 (destruct j as [|j]; [reflexivity|]). lia.
Qed.

Lemma dl_entry : forall ly S W (regs0 : bvmap 5 word) mem0 md0 ch r k nm b0 bs s G (regsc : bvmap 5 word) memc mdc i,
dpre ly S W regs0 mem0 md0 ch r k nm b0 bs s G ->
dinv regs0 ly S W mem0 md0 r nm bs regsc memc mdc ->
2 <= k <= 40 -> k <= Boxreg.bx_fabric bs -> Boxreg.bx_n bs <= 4 ->
0 <= b0 -> b0 + k <= Boxreg.bx_fabric bs -> 0 <= i < Boxreg.bx_n bs ->
getr regsc 10 = w64 (r + 56 * i + 12) -> getr regsc 13 = w64 (r + 56 * i + 12) ->
getr regsc 14 = w64 (DSB + (r + 56 * i + 8) / 8) -> getr regsc 15 = w64 (Boxreg.bx_n bs - i) ->
getr regsc 12 = w64 (b0 + k) -> getr regsc 18 = w64 b0 -> getr regsc 19 = w64 k ->
st_ok_pi SEGS VAL (dlE regsc regs0 bs i) ss_dl
  (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + 6444)) memc (seg_rom SEGS)))
/\ sh_ok SEGS DBx dl_SH (dlE regsc regs0 bs i) (mrestrict (w_H W) memc).
Proof.
intros ly S W regs0 mem0 md0 ch r k nm b0 bs s G regsc memc mdc i HPRE HINV Hk Hkf Hn4 Hb0 Hbk Hi
  R10 R13 R14 R15 R12 R18 R19.
destruct HPRE as (HFN & _ & _ & _ & _ & _ & _ & _ & Hin & _ & HBINV & _).
destruct HINV as (HJ & R2 & _ & _ & _ & _ & HFR & HBYc & _ & _ & R24 & _).
pose proof HFN as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof HJ as (HAR & _).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof DSTK_val as WS.
destruct (dm_boxreg_inv_facts bs HBINV) as (HL & Hn5 & Hf40 & Hrow).
destruct (Hrow i Hi) as (Hbase & Hnch & Hbn).
destruct (al_blocks _ _ LAWS ly S W memc mdc r REG_SIZE HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & _ & _).
change (req_size REG_SIZE) with 288 in *.
pose proof (dval4 W memc r bs (56 * i + 8) HL HBYc ltac:(lia) ltac:(lia) ltac:(unfold Boxreg.bx_base in Hbase; lia)) as Vb.
pose proof (dval4 W memc r bs (56 * i + 12) HL HBYc ltac:(lia) ltac:(lia) ltac:(unfold Boxreg.bx_nch in Hnch; lia)) as Vn.
change (Boxreg.rd4 bs (56 * i + 8)) with (Boxreg.bx_base bs i) in Vb.
change (Boxreg.rd4 bs (56 * i + 12)) with (Boxreg.bx_nch bs i) in Vn.
rewrite restrict_mkst_fx.
destruct (dl_ew regsc regs0 bs i) as (EL & E32 & E33 & E34 & EF).
set (E := dlE regsc regs0 bs i) in *.
assert (E2 : ew E 2 = Z_to_bv 64 (spZ regs0 - 96))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl); exact R2).
assert (E13 : ew E 13 = Z_to_bv 64 (r + 56 * i + 12))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 13 13%bv eq_refl); exact R13).
assert (E12 : ew E 12 = Z_to_bv 64 (b0 + k))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 12 12%bv eq_refl); exact R12).
assert (E15 : ew E 15 = Z_to_bv 64 (Boxreg.bx_n bs - i))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 15 15%bv eq_refl); exact R15).
assert (E18 : ew E 18 = Z_to_bv 64 b0)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 18 18%bv eq_refl); exact R18).
assert (E19 : ew E 19 = Z_to_bv 64 k)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 19 19%bv eq_refl); exact R19).
assert (Usp : bv_unsigned (ew E 2) = spZ regs0 - 96) by (rewrite E2; apply unsigned_lit_small; lia).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_dl. apply pa_entry_st_ok_full.
  + unfold dl_regs.
    apply YI04.regs_ok_pin;
      [apply YI04.regs_ok_pin;
        [apply YI04.regs_ok_pin; [subst E; unfold dlE; apply regs_ok_Eimg_Ereg | dl_nz |] | dl_nz |] | dl_nz |].
    * cbn [sv_denot]. rewrite E13, Z.add_0_r, Z_to_bv_bv_unsigned. exact R10.
    * rewrite R14. rewrite denot_lit_U. unfold w64. f_equal.
      rewrite U_SAlu, U_SOff, E32, U_SAlu, U_SOff, E13, U_SLit. cbn [zalu_raw].
      rewrite !unsigned_lit_small by (unfold DSB; lia).
      change (Z.land 3 63) with 3. rewrite Z.add_0_r.
      rewrite (zcanon_id DSB) by (unfold DSB, M64; lia). rewrite (zcanon_id 3) by (unfold M64; lia).
      rewrite (zcanon_id (r + 56 * i + 12 + -4)) by (unfold M64; lia).
      replace (Z.land 3 63) with 3 by reflexivity.
      rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
      replace (r + 56 * i + 12 + -4) with (r + 56 * i + 8) by lia.
      assert (0 <= (r + 56 * i + 8) / 8 <= r + 56 * i + 8) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
      rewrite (zcanon_id ((r + 56 * i + 8) / 8)) by (unfold M64; lia).
      symmetry. apply zcanon_id. unfold M64, DSB. lia.
    * fold (dlE regsc regs0 bs i). cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. exact R24.
  + vm_compute. reflexivity.
  + unfold dl_frame, dl_row.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (j & <- & Hj). apply in_seq in Hj.
      apply (chunk_ok_val SEGS E _ (spZ regs0 - 96) (nth j dsave_off 0) 8 (SOff (35 + j) 0)
        (bv_unsigned (getr regs0 (Z_to_bv 5 (nth j dsave_reg 0))))).
      -- cbn [sv_denot]. rewrite EF by lia. rewrite Z.add_0_r. reflexivity.
      -- pose proof (bv_unsigned_in_range 64 (getr regs0 (Z_to_bv 5 (nth j dsave_reg 0)))) as Hw.
         unfold bv_modulus in Hw. change (2 ^ Z.of_N 64) with (2 ^ 64) in Hw. zside.
      -- zside.
      -- exact (HFR j ltac:(lia)).
    * rewrite (VB 13%nat (r + 56 * i + 12) E13) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      -- apply (chunk_ok_val SEGS E _ (r + 56 * i + 12) (-4) 4 (SOff 33 0) (Boxreg.bx_base bs i));
         [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         replace (r + 56 * i + 12 + -4) with (r + (56 * i + 8)) by lia. exact Vb.
      -- apply (chunk_ok_val SEGS E _ (r + 56 * i + 12) 0 4 (SOff 34 0) (Boxreg.bx_nch bs i));
         [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         replace (r + 56 * i + 12 + 0) with (r + (56 * i + 12)) by lia. exact Vn.
  + apply pairwise_disjoint_of_extents.
    unfold dl_frame, dl_row, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 13%nat (r + 56 * i + 12) E13) by lia. cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 Hr4096 Hrceil Hi Hn4. clear. intros.
    repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [dl_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E13, E32, E33, E34, E12, E18, E19, E15, !unsigned_lit_small by (unfold DSB; lia).
    change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hslo Hshi H47 Hceil C1 WS Hstk0 Hal16 Hr16 Hr4096 Hrceil Hbase Hnch Hbn Hk Hkf Hb0 Hbk Hi Hn4 Hf40.
    clear. unfold DSB. intros.
    repeat match goal with |- _ /\ _ => split end; try lia; Z.div_mod_to_equations; lia.
- unfold sh_ok, dl_SH. constructor; [|constructor].
  eapply (dshent_block ly S W memc mdc E 13 (r + 56 * i + 12) r REG_SIZE (-12) 44 HAR Hin).
  + unfold DBx. rewrite (U_atom E 32 DSB E32) by (unfold DSB; lia). reflexivity.
  + exact (U_atom E 13 (r + 56 * i + 12) E13 ltac:(lia)).
  + lia.
  + lia.
  + change (req_size REG_SIZE) with 288. lia.
Qed.

(* ---- memory: the loop's regions have no window, so a run keeps every byte ---- *)
Lemma dl_nowin : forall E rs (m m' : word -> option byte),
forallb (fun rg => YP09.r_whi rg <=? YP09.r_wlo rg) rs = true -> frame_of E rs m m' -> forall x, m' x = m x.
Proof.
intros E rs m m' Hw HF x. apply HF. intros (rg & Hin & Hr).
rewrite forallb_forall in Hw. specialize (Hw rg Hin). apply Z.leb_le in Hw. lia.
Qed.
Lemma dl_mbyte_eq : forall (W : world SEGS) (m m' : word -> option byte), (forall x, m' x = m x) ->
forall a, mbyte SEGS (mrestrict (w_H W) m') a = mbyte SEGS (mrestrict (w_H W) m) a.
Proof. intros W m m' H a. unfold mbyte, mrestrict. rewrite !H. reflexivity. Qed.
Lemma dl_keep_frame : forall regs0 (W : world SEGS) (m m' : word -> option byte), (forall x, m' x = m x) ->
dframe_ok regs0 W m -> dframe_ok regs0 W m'.
Proof. intros regs0 W m m' H HF j Hj q Hq. rewrite (dl_mbyte_eq W m m' H). exact (HF j Hj q Hq). Qed.
Lemma dl_keep_bytes : forall (W : world SEGS) (m m' : word -> option byte) r bs, (forall x, m' x = m x) ->
tdecl_reg_bytes W m r bs -> tdecl_reg_bytes W m' r bs.
Proof. intros W m m' r bs H HB q Hq. unfold aview. rewrite (dl_mbyte_eq W m m' H). exact (HB q Hq). Qed.
Ltac dl_keep :=
repeat match goal with H : frame_of _ _ (mrestrict _ _) _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
lazymatch goal with
| HF : frame_of _ ?rs ?m1 ?m2, KEEP : forall x, ?m1 x = ?m0 x |- _ =>
  let K2 := fresh "KEEP" in
  assert (K2 : forall x, m2 x = m0 x)
    by (intros x; rewrite (dl_nowin _ rs m1 m2 ltac:(vm_compute; reflexivity) HF x); exact (KEEP x));
  clear HF KEEP
end.
(* A register of a symbolic state, with its symbolic value computed but not unfolded. *)
Ltac dl_reg HS R Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_pi_restrict_reg H E ss ms R HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) R) in change (sr_get (ss_regs ss) R) with e in Hr;
  cbn [ms_regs restrict] in Hr
end.

(* ---- the symbolic values the loop leaves in registers ---- *)
Lemma dl_U_atom : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
sv_denot E (SOff n c) = w64 (v + c).
Proof. intros E n v c H Hv Hc. cbn [sv_denot]. rewrite H, unsigned_lit_small by lia. reflexivity. Qed.
(* the back edge: a4 + 7 is the shadow address of row i + 1's base word *)
Lemma dl_a4_next : forall E r i, ew E 32 = Z_to_bv 64 DSB -> ew E 13 = Z_to_bv 64 (r + 56 * i + 12) ->
0 <= r -> 0 <= i -> r + 56 * i + 64 < 2 ^ 62 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff 13 (-4)) (SLit 3))) (SLit 7)) =
w64 (DSB + (r + 56 * (i + 1) + 8) / 8).
Proof.
intros E r i H32 H13 Hr Hi Hb.
assert (D : 0 <= (r + 56 * i + 8) / 8 <= r + 56 * i + 8) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
assert (U1 : U E (SOff 13 (-4)) = r + 56 * i + 8).
{ rewrite U_SOff, H13, unsigned_lit_small by lia. replace (r + 56 * i + 12 + -4) with (r + 56 * i + 8) by lia.
  apply zcanon_id. unfold M64. lia. }
assert (U2 : U E (SAlu ALU_SRL (SOff 13 (-4)) (SLit 3)) = (r + 56 * i + 8) / 8).
{ rewrite U_SAlu, U1, U_SLit. cbn [zalu_raw]. rewrite (zcanon_id 3) by (unfold M64; lia).
  replace (Z.land 3 63) with 3 by reflexivity. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  apply zcanon_id. unfold M64. lia. }
assert (U3 : U E (SOff 32 0) = DSB) by (apply U_atom; [exact H32 | unfold DSB; lia]).
assert (U4 : U E (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff 13 (-4)) (SLit 3))) = DSB + (r + 56 * i + 8) / 8).
{ rewrite U_SAlu, U3, U2. cbn [zalu_raw]. apply zcanon_id. unfold M64, DSB. lia. }
rewrite denot_lit_U. unfold w64. f_equal.
rewrite U_SAlu, U4, U_SLit. cbn [zalu_raw]. rewrite (zcanon_id 7) by (unfold M64; lia).
replace (r + 56 * (i + 1) + 8) with (r + 56 * i + 8 + 7 * 8) by lia. rewrite Z.div_add by lia.
rewrite Z.add_assoc. apply zcanon_id. unfold M64, DSB. lia.
Qed.
(* the exit: s5 = r + 56 n *)
Lemma dl_s5 : forall E r n, ew E 21 = Z_to_bv 64 r -> ew E 25 = Z_to_bv 64 n -> 0 <= r -> 0 <= n <= 5 ->
r + 280 < 2 ^ 62 ->
sv_denot E (SAlu ALU_ADD (SOff 21 0) (SMd M_MUL (SOff 25 0) (SLit 56))) = w64 (r + 56 * n).
Proof.
intros E r n H21 H25 Hr Hn Hb.
rewrite denot_lit_U. unfold w64. f_equal.
rewrite U_SAlu, U_SMd. rewrite (U_atom E 21 r H21) by lia. rewrite (U_atom E 25 n H25) by lia. rewrite U_SLit.
cbn [zalu_raw zmd_raw]. rewrite (zcanon_id 56) by (unfold M64; lia).
rewrite (zcanon_id (n * 56)) by (unfold M64; lia). replace (r + n * 56) with (r + 56 * n) by lia.
apply zcanon_id. unfold M64. lia.
Qed.
(* the callee-saved registers, one by one *)
Lemma dl_aregs : forall (regs0 regsF : bvmap 5 word),
(forall rr : bv 5, In rr CALLEE_SAVED -> getr regsF rr = getr regs0 rr) -> aregs_preserved regs0 regsF.
Proof.
intros regs0 regsF HC rr Hr. apply HC.
unfold acallee_saved in Hr. cbv [CALLEE_SAVED In].
assert (H : rr = 2 \/ rr = 3 \/ rr = 4 \/ rr = 8 \/ rr = 9 \/ rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/ rr = 22 \/
  rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
repeat (destruct H as [->|H]; [repeat (first [left; apply bv_eq; reflexivity | right])|]).
subst. repeat (first [left; apply bv_eq; reflexivity | right]).
Qed.

(* The head of the inlined range_taken loop, 0x81878, row i < n (by induction on n - i). *)
Lemma dl_walk : forall (d : nat) ly S W (regs0 : bvmap 5 word) mem0 md0 ch r k nm b0 bs s G
  (regsc : bvmap 5 word) memc mdc i,
dpre ly S W regs0 mem0 md0 ch r k nm b0 bs s G ->
dinv regs0 ly S W mem0 md0 r nm bs regsc memc mdc ->
d = Z.to_nat (Boxreg.bx_n bs - i) ->
2 <= k <= 40 -> Z.even k = true -> k <= Boxreg.bx_fabric bs -> Boxreg.bx_n bs <= 4 ->
0 <= b0 -> b0 + k <= Boxreg.bx_fabric bs -> 0 <= i < Boxreg.bx_n bs ->
(forall j, 0 <= j < i -> ~ Boxreg.meets b0 k (Boxreg.bx_base bs j) (Boxreg.bx_nch bs j)) ->
getr regsc 10 = w64 (r + 56 * i + 12) -> getr regsc 13 = w64 (r + 56 * i + 12) ->
getr regsc 14 = w64 (DSB + (r + 56 * i + 8) / 8) -> getr regsc 15 = w64 (Boxreg.bx_n bs - i) ->
getr regsc 12 = w64 (b0 + k) -> getr regsc 18 = w64 b0 -> getr regsc 19 = w64 k ->
getr regsc 20 = w64 (-1) -> getr regsc 21 = w64 r -> getr regsc 25 = w64 (Boxreg.bx_n bs) ->
SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + 6444)) memc (seg_rom SEGS)) mdc)
  (treac_boxreg_declare_post regs0 ly S W mem0 md0 r k b0 bs s).
Proof.
induction d as [|d IH]; intros ly S W regs0 mem0 md0 ch r k nm b0 bs s G regsc memc mdc i
  HPRE HINV Hd Hk Hke Hkf Hn4 Hb0 Hbk Hi Hprev R10 R13 R14 R15 R12 R18 R19 R20 R21 R25; [lia|].
destruct (dl_entry ly S W regs0 mem0 md0 ch r k nm b0 bs s G regsc memc mdc i HPRE HINV Hk Hkf Hn4 Hb0 Hbk Hi
  R10 R13 R14 R15 R12 R18 R19) as [HS SHOK].
pose proof HINV as (HJ & R2 & R3 & R4 & R26 & R27 & HFR & HBYc & R8 & R9 & R24 & R23).
pose proof HPRE as (HFN & _ & _ & _ & _ & _ & _ & _ & Hin & _ & HBINV & _).
pose proof HFN as (_ & Hra & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof DSTK_val as WS.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
destruct (dm_boxreg_inv_facts bs HBINV) as (HL & Hn5 & Hf40 & Hrow).
destruct (Hrow i Hi) as (Hbase & Hnch & Hbn).
destruct (al_blocks _ _ LAWS ly S W memc mdc r REG_SIZE (proj1 HJ) Hin) as (Hr16 & Hr4096 & Hrceil & _).
change (req_size REG_SIZE) with 288 in Hrceil.
destruct (dl_ew regsc regs0 bs i) as (EL & E32 & E33 & E34 & EF).
set (E := dlE regsc regs0 bs i) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, dlE; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsc (dl_extra regs0 bs i)) E)
  by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | unfold E, dlE; reflexivity]).
clearbody E.
assert (E2 : ew E 2 = Z_to_bv 64 (spZ regs0 - 96))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 2 2%bv eq_refl); exact R2).
assert (Usp : bv_unsigned (ew E 2) = spZ regs0 - 96) by (rewrite E2; apply unsigned_lit_small; lia).
assert (E12 : ew E 12 = Z_to_bv 64 (b0 + k))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 12 12%bv eq_refl); exact R12).
assert (E13 : ew E 13 = Z_to_bv 64 (r + 56 * i + 12))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 13 13%bv eq_refl); exact R13).
assert (E15 : ew E 15 = Z_to_bv 64 (Boxreg.bx_n bs - i))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 15 15%bv eq_refl); exact R15).
assert (E18 : ew E 18 = Z_to_bv 64 b0)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 18 18%bv eq_refl); exact R18).
assert (E20 : ew E 20 = Z_to_bv 64 (-1))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 20 20%bv eq_refl); exact R20).
assert (E21 : ew E 21 = Z_to_bv 64 r)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 21 21%bv eq_refl); exact R21).
assert (E25 : ew E 25 = Z_to_bv 64 (Boxreg.bx_n bs))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 25 25%bv eq_refl); exact R25).
(* signed values of the atoms the branches compare *)
assert (S18 : Sg E (SOff 18 0) = b0) by (rewrite (dS_atom E 18 b0 0 E18) by lia; lia).
assert (S33 : Sg E (SOff 33 0) = Boxreg.bx_base bs i) by (rewrite (dS_atom E 33 _ 0 E33) by lia; lia).
assert (S34 : Sg E (SOff 34 0) = Boxreg.bx_nch bs i) by (rewrite (dS_atom E 34 _ 0 E34) by lia; lia).
assert (S12 : Sg E (SOff 12 0) = b0 + k) by (rewrite (dS_atom E 12 _ 0 E12) by lia; lia).
assert (SA : Sg E (SAlu ALU_ADD (SOff 33 0) (SOff 34 0)) = Boxreg.bx_base bs i + Boxreg.bx_nch bs i)
  by (apply dS_alu_add; [exact S33 | exact S34 | lia]).
assert (KEEP : forall x, memc x = memc x) by reflexivity.
(* a register the loop does not change *)
let kept HSx := idtac;
  lazymatch goal with |- getr (ms_regs ?msx) ?R = getr regsc ?R =>
    let Hq := fresh "Hq" in dl_reg HSx R Hq; rewrite Hq; clear Hq; cbn [sv_denot];
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned, EL by (unfold A_TEXT; lia); apply ew_Ereg_nat; reflexivity
  end in
(* the machine state at the stop, and the memory kept since the loop head *)
let dinv_next HSx := idtac;
  lazymatch type of HSx with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
  lazymatch goal with KX : forall x, ms_mem msx x = memc x |- dinv _ _ _ _ _ _ _ _ _ _ _ _ =>
    unfold dinv;
    split; [exact HJ|];
    split; [transitivity (getr regsc 2); [kept HSx | exact R2]|];
    split; [transitivity (getr regsc 3); [kept HSx | exact R3]|];
    split; [transitivity (getr regsc 4); [kept HSx | exact R4]|];
    split; [transitivity (getr regsc 26); [kept HSx | exact R26]|];
    split; [transitivity (getr regsc 27); [kept HSx | exact R27]|];
    split; [exact (dl_keep_frame regs0 W memc (ms_mem msx) KX HFR)|];
    split; [exact (dl_keep_bytes W memc (ms_mem msx) r bs KX HBYc)|];
    split; [transitivity (getr regsc 8); [kept HSx | exact R8]|];
    split; [transitivity (getr regsc 9); [kept HSx | exact R9]|];
    split; [let Hq := fresh "Hq" in dl_reg HSx (24%bv : bv 5) Hq; rewrite Hq;
            rewrite (dl_U_atom E 32 DSB 0 E32) by (unfold DSB; lia); rewrite Z.add_0_r; reflexivity|];
    transitivity (getr regsc 23); [kept HSx | exact R23]
  end end in
(* 0x8190c (no row meets [b0, b0 + k); i + 1 = n is in the context): the placement, dp_walk with b = b0, pinned = 1 *)
let leafP Hnm := idtac;
  lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?msx) |- _ =>
    pmkst HSx;
    eapply (dp_walk ly S W regs0 mem0 md0 ch r k nm b0 bs s G (ms_regs msx) (ms_mem msx) _ b0 1 HPRE);
    [ dinv_next HSx
    | apply dm_placed_pinned; [exact Hk | exact Hke | exact Hkf | lia | exact Hb0 | exact Hbk |];
      intros j Hj; destruct (Z.eq_dec j i) as [->|Hne]; [exact Hnm | apply Hprev; lia]
    | let Hq := fresh "Hq" in dl_reg HSx (21%bv : bv 5) Hq; rewrite Hq; apply dl_s5; [exact E21 | exact E25 | lia..]
    | let Hq := fresh "Hq" in dl_reg HSx (22%bv : bv 5) Hq; rewrite Hq;
      rewrite (dl_U_atom E 18 b0 0 E18) by lia; rewrite Z.add_0_r; reflexivity
    | transitivity (getr regsc 19); [kept HSx | exact R19]
    | transitivity (getr regsc 18); [kept HSx | exact R18] ]
  end in
(* 0x81878 for row i + 1 (i + 1 < n is in the context): the induction hypothesis *)
let leafB Hnm := idtac;
  lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?msx) |- _ =>
    pmkst HSx;
    eapply (IH ly S W regs0 mem0 md0 ch r k nm b0 bs s G (ms_regs msx) (ms_mem msx) _ (i + 1) HPRE);
    [ dinv_next HSx
    | lia
    | exact Hk | exact Hke | exact Hkf | exact Hn4 | exact Hb0 | exact Hbk
    | lia
    | intros j Hj; destruct (Z.eq_dec j i) as [->|Hne]; [exact Hnm | apply Hprev; lia]
    | let Hq := fresh "Hq" in dl_reg HSx (10%bv : bv 5) Hq; rewrite Hq;
      rewrite (dl_U_atom E 13 _ 56 E13) by lia; unfold w64; f_equal; lia
    | let Hq := fresh "Hq" in dl_reg HSx (13%bv : bv 5) Hq; rewrite Hq;
      rewrite (dl_U_atom E 13 _ 56 E13) by lia; unfold w64; f_equal; lia
    | let Hq := fresh "Hq" in dl_reg HSx (14%bv : bv 5) Hq; rewrite Hq; apply dl_a4_next; [exact E32 | exact E13 | lia..]
    | let Hq := fresh "Hq" in dl_reg HSx (15%bv : bv 5) Hq; rewrite Hq;
      rewrite (dl_U_atom E 15 _ (-1) E15) by lia; unfold w64; f_equal; lia
    | transitivity (getr regsc 12); [kept HSx | exact R12]
    | transitivity (getr regsc 18); [kept HSx | exact R18]
    | transitivity (getr regsc 19); [kept HSx | exact R19]
    | transitivity (getr regsc 20); [kept HSx | exact R20]
    | transitivity (getr regsc 21); [kept HSx | exact R21]
    | transitivity (getr regsc 25); [kept HSx | exact R25] ]
  end in
(* 0x8199c .. 0x819d0 (row i meets [b0, b0 + k)): restore the frame, return -1 *)
let leafR Hm := idtac;
  lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?msx) |- _ =>
  lazymatch goal with KX : forall x, ms_mem msx x = memc x |- _ =>
    let RF1 := fresh "RF1" in let RF10 := fresh "RF10" in
    dl_reg HSx (1%bv : bv 5) RF1; dl_reg HSx (10%bv : bv 5) RF10;
    eapply (RET W _ _ _ _ _ HSx eq_refl ltac:(vm_compute; reflexivity));
    let mat' := fresh "mat" in intros mat';
    replace (v_jalr (getr (ms_regs msx) 1) 0) with (getr regs0 1);
    [| rewrite RF1; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
       let E35 := fresh "E35" in pose proof (EF 0%nat ltac:(lia)) as E35; cbn [Nat.add] in E35; rewrite E35;
       replace (Z_to_bv 5 (nth 0 dsave_reg 0)) with (1%bv : bv 5) by (apply bv_eq; reflexivity);
       symmetry; exact Hra ];
    apply dret_post;
    [ apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ
    | apply dl_aregs; intros rr Hrr; cbv [CALLEE_SAVED In] in Hrr;
      repeat (destruct Hrr as [<-|Hrr];
        [ lazymatch goal with |- getr _ ?R = _ => let Hq := fresh "Hq" in dl_reg HSx R Hq; rewrite Hq; clear Hq end;
          cbn [sv_denot];
          first
          [ rewrite Usp; replace (spZ regs0 - 96 + 96) with (spZ regs0) by lia; unfold spZ;
            apply Z_to_bv_bv_unsigned
          | rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
            lazymatch goal with |- ew E ?a = _ =>
              let j := eval vm_compute in (a - 35)%nat in
              replace a with (35 + j)%nat by reflexivity; rewrite (EF j) by lia; f_equal; apply bv_eq; reflexivity
            end
          | rewrite Z.add_0_r, Z_to_bv_bv_unsigned, EL by (unfold A_TEXT; lia);
            lazymatch goal with |- _ = getr regs0 ?R =>
              transitivity (getr regsc R); [apply ew_Ereg_nat; reflexivity |];
              first [exact R3 | exact R4 | exact R26 | exact R27]
            end ]
        |]);
      destruct Hrr
    | left; split; [apply dm_refused_overlap; [exact Hb0 | exists i; split; [exact Hi | exact Hm]]|];
      split;
      [ rewrite RF10; cbn [sv_denot]; rewrite E20, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | exact (dl_keep_bytes W memc (ms_mem msx) r bs KX HBYc) ] ]
  end end in
paj_run_tok RUN HS HJ SHOK Dspan; [awr_ok_tac |]; dl_keep;
(* 0x8189c  bge s2, base + nch *)
psrr_branch_tok RUN BR HS SHOK Dspan;
rewrite (dc_ge E _ _ b0 (Boxreg.bx_base bs i + Boxreg.bx_nch bs i) S18 SA) in Hc;
[ apply negb_true_iff, Z.ltb_ge in Hc; rename Hc into Hge;
  assert (Hnm : ~ Boxreg.meets b0 k (Boxreg.bx_base bs i) (Boxreg.bx_nch bs i)) by (unfold Boxreg.meets; lia);
  paj_run_tok RUN HS HJ SHOK Dspan; [awr_ok_tac |]; dl_keep;
  (* 0x818b4  beqz a5 - 1 *)
  psrr_branch_tok RUN BR HS SHOK Dspan;
  rewrite branch_eq_U, (U_atom_off E 15 _ (-1) E15), U_lit in Hc by lia;
  [ apply Z.eqb_eq in Hc;
    paj_run_to_tok RUNTO HS HJ SHOK Dspan 6592; [awr_ok_tac |]; dl_keep; leafP Hnm
  | apply Z.eqb_neq in Hc;
    paj_run_tok RUN HS HJ SHOK Dspan; [awr_ok_tac |]; dl_keep; leafB Hnm ]
| apply negb_false_iff, Z.ltb_lt in Hc; rename Hc into Hge;
  paj_run_tok RUN HS HJ SHOK Dspan; [awr_ok_tac |]; dl_keep;
  (* 0x818a0  blt base, b0 + k *)
  psrr_branch_tok RUN BR HS SHOK Dspan;
  rewrite (dc_lt E _ _ (Boxreg.bx_base bs i) (b0 + k) S33 S12) in Hc;
  [ apply Z.ltb_lt in Hc; rename Hc into Hlt;
    assert (Hm : Boxreg.meets b0 k (Boxreg.bx_base bs i) (Boxreg.bx_nch bs i)) by (unfold Boxreg.meets; lia);
    paj_run_tok RUN HS HJ SHOK Dspan; [awr_ok_tac |]; dl_keep; leafR Hm
  | apply Z.ltb_ge in Hc; rename Hc into Hlt;
    assert (Hnm : ~ Boxreg.meets b0 k (Boxreg.bx_base bs i) (Boxreg.bx_nch bs i)) by (unfold Boxreg.meets; lia);
    paj_run_tok RUN HS HJ SHOK Dspan; [awr_ok_tac |]; dl_keep;
    (* 0x818b4  beqz a5 - 1 *)
    psrr_branch_tok RUN BR HS SHOK Dspan;
    rewrite branch_eq_U, (U_atom_off E 15 _ (-1) E15), U_lit in Hc by lia;
    [ apply Z.eqb_eq in Hc;
      paj_run_to_tok RUNTO HS HJ SHOK Dspan 6592; [awr_ok_tac |]; dl_keep; leafP Hnm
    | apply Z.eqb_neq in Hc;
      paj_run_tok RUN HS HJ SHOK Dspan; [awr_ok_tac |]; dl_keep; leafB Hnm ] ] ].
Qed.


(* ---- memory facts the main walk carries ---- *)
(* The registry block's bytes are unchanged by a run whose windows miss it. *)
Lemma dkeepR_step : forall (W : world SEGS) E rs (m1 m2 m0 : word -> option byte) (r : Z),
0 <= r -> r + 288 <= 2 ^ 64 ->
frame_of E rs (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
(forall i, 0 <= i < 288 -> ~ in_wrange E rs (r + i)) ->
(forall i, 0 <= i < 288 -> aview SEGS (w_H W) m1 (r + i) = aview SEGS (w_H W) m0 (r + i)) ->
forall i, 0 <= i < 288 -> aview SEGS (w_H W) m2 (r + i) = aview SEGS (w_H W) m0 (r + i).
Proof.
intros W E rs m1 m2 m0 r Hr0 Hr1 HF HP HK i Hi. rewrite <- (HK i Hi).
unfold aview, mbyte. cbv beta. rewrite (HF (Z_to_bv 64 (r + i))); [reflexivity|].
rewrite unsigned_lit_small by lia. exact (HP i Hi).
Qed.
(* The frame's 11 saved words, from the stack region's chunks. *)
Lemma dframe_of_region : forall E (W : world SEGS) memc (regs0 : bvmap 5 word) wlo whi cs,
region_ok SEGS E (mrestrict (w_H W) memc) (YP09.mkRegion (Some 2%nat) (-96) 0 wlo whi cs) ->
bv_unsigned (ew E 2) = spZ regs0 ->
(forall j, (j < 11)%nat -> exists e, In (YP09.mkChunk (-96 + nth j dsave_off 0) (CVal 8 e)) cs /\
   sv_denot E e = getr regs0 (Z_to_bv 5 (nth j dsave_reg 0))) ->
dframe_ok regs0 W memc.
Proof.
intros E W memc regs0 wlo whi cs HR Hsp HC j Hj kk Hkk.
destruct (HC j Hj) as (e & Hin & He).
unfold region_ok in HR. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in HR.
destruct HR as (_ & _ & _ & HF). rewrite Hsp in HF.
pose proof (proj1 (Forall_forall _ _) HF _ Hin (Z.of_nat kk)) as Hc.
unfold c_len in Hc. cbn [YP09.c_val YP09.c_off cv_len Z.of_N] in Hc.
destruct (Hc ltac:(lia)) as (bb & Hcb & Hmb). cbn [cbyte] in Hcb. injection Hcb as <-.
replace (spZ regs0 - 96 + nth j dsave_off 0 + Z.of_nat kk) with (spZ regs0 + (-96 + nth j dsave_off 0) + Z.of_nat kk) by lia.
rewrite Hmb, He. f_equal. unfold YP09.byte_of_word.
rewrite le_byte_small; [reflexivity | | lia].
pose proof (bv_unsigned_in_range 64 (getr regs0 (Z_to_bv 5 (nth j dsave_reg 0)))) as Hb.
change (bv_modulus 64) with (2 ^ 64) in Hb. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). lia.
Qed.
(* No window of a run's regions holds a byte of the registry block (only the frame has one). *)
Ltac dnowr_r Usp :=
let i := fresh "i" in let Hi := fresh "Hi" in let rg := fresh "rg" in let Hrin := fresh "Hrin" in let Hr := fresh "Hr" in
intros i Hi (rg & Hrin & Hr);
lazymatch type of Hrin with In _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' in Hrin end;
cbn [In] in Hrin; repeat destruct Hrin as [<- | Hrin]; try destruct Hrin;
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val ew ewset havoc Nat.eqb Nat.ltb Nat.leb] in Hr; rewrite ?Usp in Hr; lia.

Lemma dS_atom0 : forall E n v, ew E n = Z_to_bv 64 v -> - 2 ^ 63 <= v < 2 ^ 63 -> Sg E (SOff n 0) = v.
Proof. intros E n v H Hv. rewrite (dS_atom E n v 0 H) by lia. lia. Qed.
Lemma dS_aluw_sub_atoms : forall E n1 n2 x y, ew E n1 = Z_to_bv 64 x -> ew E n2 = Z_to_bv 64 y ->
- 2 ^ 31 <= x < 2 ^ 31 -> - 2 ^ 31 <= y < 2 ^ 31 -> - 2 ^ 31 <= x - y < 2 ^ 31 ->
Sg E (SAluw ALU_SUB (SOff n1 0) (SOff n2 0)) = x - y.
Proof. intros E n1 n2 x y H1 H2 R1 R2 R3. apply dS_aluw_sub; [apply dS_atom0 | apply dS_atom0 |]; first [exact H1 | exact H2 | lia]. Qed.
Ltac dsa H n v Ev := rewrite (dS_atom0 _ n v) in H by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth map CLOB Nat.sub]; first [exact Ev | lia]).
Ltac dsl H z := rewrite (dS_lit _ z) in H by lia.
(* values of the symbolic registers at the split points *)
Lemma dV_srl : forall E n m c q v, ew E n = Z_to_bv 64 q -> ew E m = Z_to_bv 64 v ->
0 <= q < 2 ^ 64 -> 0 <= q + c < 2 ^ 64 -> 0 <= v -> v + (q + c) / 8 < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff m 0)) = w64 ((q + c) / 8 + v) /\
sv_denot E (SAlu ALU_ADD (SOff m 0) (SAlu ALU_SRL (SOff n c) (SLit 3))) = w64 (v + (q + c) / 8).
Proof.
intros E n m c q v Hn Hm Hq Hqc Hv Hs.
assert (D8 : 0 <= (q + c) / 8 <= q + c) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (HS : U E (SAlu ALU_SRL (SOff n c) (SLit 3)) = (q + c) / 8).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom_off E n q c Hn) by lia. rewrite U_SLit, (zcanon_id 3) by (unfold M64; lia).
  change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. apply zcanon_id. unfold M64. lia. }
split; unfold w64; rewrite denot_lit_U; f_equal; rewrite U_SAlu; cbn [zalu_raw]; rewrite HS, (U_atom E m v Hm) by lia;
apply zcanon_id; unfold M64; lia.
Qed.
Lemma dV_row : forall E n m q x, ew E n = Z_to_bv 64 q -> ew E m = Z_to_bv 64 x -> 0 <= q -> 0 <= x <= 5 -> q + 56 * x < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SOff n 0) (SMd M_MUL (SOff m 0) (SLit 56))) = w64 (q + 56 * x).
Proof.
intros E n m q x Hn Hm Hq Hx Hs. unfold w64. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite (U_atom E n q Hn), (U_atom E m x Hm) by lia.
rewrite U_SLit, (zcanon_id 56) by (unfold M64; lia). rewrite (zcanon_id (x * 56)) by (unfold M64; lia).
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma dV_aluw_add : forall E n1 n2 x y, ew E n1 = Z_to_bv 64 x -> ew E n2 = Z_to_bv 64 y ->
- 2 ^ 31 <= x < 2 ^ 31 -> - 2 ^ 31 <= y < 2 ^ 31 -> - 2 ^ 31 <= x + y < 2 ^ 31 ->
sv_denot E (SAluw ALU_ADD (SOff n1 0) (SOff n2 0)) = w64 (x + y).
Proof.
intros E n1 n2 x y H1 H2 R1 R2 R3. unfold w64. change (Z_to_bv 64 (x + y)) with (sv_denot E (SLit (x + y))).
apply S_inj. rewrite dS_lit by lia. apply dS_aluw_add; [apply dS_atom0 | apply dS_atom0 |]; first [exact H1 | exact H2 | lia].
Qed.
Lemma dsv_reg : forall E regs extra (n : nat) (rr : bv 5), env_agree 32 (Ereg regs extra) E -> (n < 32)%nat ->
Z.of_nat n = bv_unsigned rr -> sv_denot E (SOff n 0) = getr regs rr.
Proof.
intros E regs extra n rr [HA _] Hn Hr. cbn [sv_denot]. rewrite Z.add_0_r, (HA n Hn), Z_to_bv_bv_unsigned.
exact (ew_Ereg_nat regs extra n rr Hr).
Qed.
(* the frame's chunks after the prologue's 11 stores *)
Ltac dframe_tac HS Usp HAE :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ss (restrict _ ?msx) =>
let rg := eval vm_compute in (nth 0 (ss_mem ss) (stack_region 0)) in
let HR := fresh "HR" in
pose proof (st_ok_pi_region_nth Ex ss (restrict _ msx) 0 rg HS ltac:(vm_compute; reflexivity)) as HR;
cbn [restrict ms_mem] in HR;
eapply (dframe_of_region Ex _ _ _ _ _ _ HR); [cbn [ew ewset Nat.eqb]; exact Usp |];
let j := fresh "j" in let Hj := fresh "Hj" in intros j Hj;
do 11 (destruct j as [|j]; [eexists; split; [cbn [In]; repeat (first [left; reflexivity | right]) |
  apply (dsv_reg Ex _ _ _ _ HAE); [lia | reflexivity]] |]); lia
end.
Lemma dsv_atom : forall E n c v, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof.
intros E n c v H. cbn [sv_denot]. rewrite H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Ltac denv := cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth map CLOB Nat.sub].
Ltac prreg_raw HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?Ex ?ss (restrict ?H ?ms) =>
pose proof (st_ok_pi_restrict_reg H Ex ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
| st_ok ?segs ?Ex ?ss (restrict ?H ?ms) =>
pose proof (st_ok_restrict_reg segs H Ex ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
end.
(* paj_run_tok with the journal's arguments given explicitly (simple refine) *)
Ltac dpaj_run_tok RUN HS HJ SHOK Bspan :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
lazymatch type of HJ with
| ajournal _ _ ?STK ?sp0 ?FP ?ly ?S ?W0 ?mem ?md ?own ?lyc ?Sc _ _ ?mdc ?k =>
lazymatch goal with |- SRr _ _ _ ?Q =>
lazymatch paj_tables RUN with (?tpi, ?tw) =>
let K := eval vm_compute in (run_K A_LIM Bx SH ss) in
let rr := eval vm_compute in (sym_runN_pi_tok tpi tw K Bx Bspan SH FUEL ss) in
lazymatch rr with
| (?st', ?rs) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN_pi_tok tpi tw K Bx Bspan SH FUEL ss = (st', rs)) by (vm_compute; reflexivity);
let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI end in
simple refine (RUN W FUEL E K Bx Bspan SH ss st' rs ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q
  ltac:(unfold A_LIM; cbn; lia) HEI HS SHOK ltac:(vm_compute; reflexivity) Hrun HJ _ _ _);
[ clear Hrun; cbn [sh_obls]; srr_obls
| clear Hrun
| clear Hrun HS HJ SHOK; try match type of ms with machine_state => clear ms | _ => idtac end;
  paj_after_run_tok HS HJ SHOK ]
end end end end end end.
Ltac dpaj_run_to_tok RUNTO HS HJ SHOK Bspan stop :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
lazymatch type of HJ with
| ajournal _ _ ?STK ?sp0 ?FP ?ly ?S ?W0 ?mem ?md ?own ?lyc ?Sc _ _ ?mdc ?k =>
lazymatch goal with |- SRr _ _ _ ?Q =>
lazymatch paj_tables RUNTO with (?tpi, ?tw) =>
let K := eval vm_compute in (run_K A_LIM Bx SH ss) in
let rr := eval vm_compute in (sym_run_toN_pi_tok tpi tw K Bx Bspan SH FUEL stop ss) in
lazymatch rr with
| (?st', ?rs) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toN_pi_tok tpi tw K Bx Bspan SH FUEL stop ss = (st', rs)) by (vm_compute; reflexivity);
let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI end in
simple refine (RUNTO W FUEL stop E K Bx Bspan SH ss st' rs ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q
  ltac:(unfold A_LIM; cbn; lia) HEI HS SHOK ltac:(vm_compute; reflexivity) Hrun HJ _ _ _);
[ clear Hrun; cbn [sh_obls]; srr_obls
| clear Hrun
| clear Hrun HS HJ SHOK; try match type of ms with machine_state => clear ms | _ => idtac end;
  paj_after_run_tok HS HJ SHOK ]
end end end end end end.
Ltac dkeep_upd W E mem r Hrr Usp :=
lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), KEEPR : forall i, _ -> aview _ _ _ (r + i) = _ |- _ =>
let K2 := fresh "KEEPR" in
pose proof (dkeepR_step W _ _ _ _ mem r (proj1 Hrr) (proj2 Hrr) HFr ltac:(dnowr_r Usp) KEEPR) as K2; clear KEEPR HFr;
rename K2 into KEEPR end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac dleaf W regs bs E1 Hra HAE HBY Rpf :=
  let R1 := fresh "R1" in let R10 := fresh "R10" in
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    KEEPR : forall i, _ -> aview _ _ _ (_ + i) = _ |- _ =>
  prreg HS (1%bv : bv 5) R1; prreg HS (10%bv : bv 5) R10;
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
  let mat' := fresh "mat" in intros mat'; rewrite R1, E1, Hra;
  apply dret_post;
  [ apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ
  | eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (dm_extra bs) HS);
    [eapply env_agree_trans; [exact HAE | split; [let n := fresh in let Hn := fresh in intros n Hn; repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; reflexivity | reflexivity]]
    | vm_compute; reflexivity]
  | left; split; [exact Rpf|]; split; [rewrite R10; apply bv_eq; reflexivity|];
    let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; rewrite (KEEPR i Hi); apply HBY; exact Hi ] end.
Ltac drun W E mem r Hrr Usp :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  dpaj_run_tok RUN HS HJ SHOK Dspan; [awr_ok_tac; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb]; exact Usp |]; dkeep_upd W E mem r Hrr Usp end.
Theorem pb_reac_boxreg_declare : treac_boxreg_declare_spec.
Proof.
unfold treac_boxreg_declare_spec.
intros ly S W regs mem md ch r k nm b0 bs s G HPRE HRO H10 H11 H12 H13 Hkr Hb0r Hin HBY HINV HNM HTV HISV HGM HFMT HFG HFL HFH
  HFP2 HFRM.
assert (DP : dpre ly S W regs mem md ch r k nm b0 bs s G) by (unfold dpre; tauto).
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
destruct (dm_entry ly S W regs mem md ch r bs HPRE H10 Hin HBY HINV) as [HS SHOK].
pose proof (ajournal_init SEGS B DSTK [(r, r + REG_SIZE)] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof DSTK_val as WS. assert (WS2 : REAC_BOXREG_DECLARE_STK = 8288) by reflexivity.
destruct (dm_boxreg_inv_facts bs HINV) as (HL & Hn5 & Hf40 & HROWS).
destruct (al_blocks _ _ LAWS ly S W mem md r REG_SIZE HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & _ & _).
change (req_size REG_SIZE) with 288 in *.
remember (dmE regs bs) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold dmE; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (dm_extra bs)) n)
  by (intros n Hn; subst E; unfold dmE; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 r) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 k) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 nm) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = Z_to_bv 64 b0) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13).
assert (E32 : ew E 32 = Z_to_bv 64 DSB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (Boxreg.bx_fabric bs)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (Boxreg.bx_n bs)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (HAE : env_agree 32 (Ereg regs (dm_extra bs)) E)
  by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
clear HEdef EL.
set (fab := Boxreg.bx_fabric bs) in *. set (n := Boxreg.bx_n bs) in *.
assert (KEEPR : forall i, 0 <= i < 288 -> aview SEGS (w_H W) mem (r + i) = aview SEGS (w_H W) mem (r + i)) by reflexivity.
assert (Hrr : 0 <= r /\ r + 288 <= 2 ^ 64) by lia.
unfold cfg_at, A_reac_boxreg_declareP.
change (w64 (BASE + AF_reac_boxreg_declare)) with (Z_to_bv 64 (BASE + AF_reac_boxreg_declare)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite (proj1 HAE) by lia; exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite (proj1 HAE) by lia; exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E26 : ew E 26 = getr regs 26) by (rewrite (proj1 HAE) by lia; exact (ew_Ereg_nat regs _ 26 26%bv eq_refl)).
assert (E27 : ew E 27 = getr regs 27) by (rewrite (proj1 HAE) by lia; exact (ew_Ereg_nat regs _ 27 27%bv eq_refl)).
(* the prologue, the arguments and the width test 0x817e4 *)
drun W E mem r Hrr Usp.
psrr_branch_tok RUN BR HS SHOK Dspan.
{ (* k is not 2 .. 40 : refused *)
  rewrite (dc_kw E k E11 Hkr) in Hc. apply negb_true_iff, andb_false_iff in Hc.
  assert (Hk' : ~ (2 <= k <= 40)) by (destruct Hc as [Hc | Hc]; [apply Z.leb_gt in Hc | apply Z.leb_gt in Hc]; lia).
  drun W E mem r Hrr Usp. dleaf W regs bs E1 Hra HAE HBY (dm_refused_width bs k b0 Hk'). }
rewrite (dc_kw E k E11 Hkr) in Hc. apply negb_false_iff, andb_true_iff in Hc.
destruct Hc as [Hk1 Hk2]. apply Z.leb_le in Hk1. apply Z.leb_le in Hk2.
(* 0x817ec  bnez k & 1 *)
drun W E mem r Hrr Usp.
psrr_branch_tok RUN BR HS SHOK Dspan.
{ rewrite (dc_kodd E k E11 Hkr) in Hc. drun W E mem r Hrr Usp. dleaf W regs bs E1 Hra HAE HBY (dm_refused_odd bs k b0 Hc). }
rewrite (dc_kodd E k E11 Hkr) in Hc. assert (Hkev : Z.even k = true) by (rewrite <- Z.negb_odd, Hc; reflexivity). clear Hc.
(* 0x8181c  blt fabric, k *)
drun W E mem r Hrr Usp.
psrr_branch_tok RUN BR HS SHOK Dspan.
{ rewrite dbr_lt in Hc. dsa Hc 33%nat fab E33. dsa Hc 11%nat k E11.
  apply Z.ltb_lt in Hc. drun W E mem r Hrr Usp. dleaf W regs bs E1 Hra HAE HBY (dm_refused_fabric bs k b0 Hc). }
rewrite dbr_lt in Hc. dsa Hc 33%nat fab E33. dsa Hc 11%nat k E11.
apply Z.ltb_ge in Hc. rename Hc into Hfk.
(* 0x8183c  blt 4, n *)
drun W E mem r Hrr Usp.
psrr_branch_tok RUN BR HS SHOK Dspan.
{ rewrite dbr_lt in Hc. dsl Hc 4. dsa Hc 34%nat n E34.
  apply Z.ltb_lt in Hc. drun W E mem r Hrr Usp. dleaf W regs bs E1 Hra HAE HBY (dm_refused_full bs k b0 Hc). }
rewrite dbr_lt in Hc. dsl Hc 4. dsa Hc 34%nat n E34.
apply Z.ltb_ge in Hc. rename Hc into Hn4.
(* 0x81840  bltz b0 *)
drun W E mem r Hrr Usp.
psrr_branch_tok RUN BR HS SHOK Dspan.
{ rewrite dbr_lt in Hc. dsa Hc 13%nat b0 E13. dsl Hc 0.
  apply Z.ltb_lt in Hc. rename Hc into Hb0n.
  drun W E mem r Hrr Usp.
  (* the call of lowest_free_base, 0x818e8 *)
  prreg HS (1%bv : bv 5) Lra. prreg HS (3%bv : bv 5) Lgp. prreg HS (4%bv : bv 5) Ltp. prreg HS (8%bv : bv 5) Ls0.
  prreg HS (10%bv : bv 5) La0. prreg HS (11%bv : bv 5) La1. prreg_raw HS (2%bv : bv 5) Lsp.
  assert (Hnm0 : 0 <= nm < alloc_ceiling).
  { destruct HNM as [(-> & _) | (_ & _ & _ & nn & Hnin & Hnn & _)]; [lia|].
    destruct (al_blocks _ _ LAWS ly S W mem md nm nn HAR Hnin) as (_ & Hn4096 & Hnceil & _). unfold req_size in Hnceil.
    destruct (nn =? 0); lia. }
  lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msx) =>
  eapply SRr_bind;
  [ eapply (aj_call SEGS B LAWS pa_segs_low W Ex ssx msx DSTK (spZ regs) [(r, r + REG_SIZE)] ly S W mem md [] ly S _ 0
      LOWEST_FREE_BASE_STK [] 0 (-96) (ew Ex 2) (getr (ms_regs msx) 1) []
      (fun ly' S' W' regs' mem' md' => ly' = ly /\ S' = S /\ W' = W /\
         exists z, getr regs' 10 = w64 z /\ lowest_free_base_c.lowest_free bs k z)
      HS ltac:(vm_compute; reflexivity) HJ);
    [ exact Lsp
    | reflexivity
    | denv; exact Usp
    | reflexivity
    | lia
    | unfold LOWEST_FREE_BASE_STK, ESTACK; lia
    | unfold LOWEST_FREE_BASE_STK, ESTACK; rewrite WS; lia
    | rewrite Lgp; denv; rewrite E3; exact Hgp
    | rewrite Ltp; denv; rewrite E4; exact Htp
    | reflexivity
    | rewrite Lra; apply ret_ok_codeptr_v; [lia | reflexivity]
    | rewrite Lra, unsigned_lit_small by (pose proof pa_B_ok; lia); pose proof pa_base_lo; lia
    | left; split; [left; unfold s0Z; rewrite Ls0; denv; rewrite E12, unsigned_lit_small by lia; lia | reflexivity]
    | intros HPRE1; cbn [ss_pc setpc]; rewrite pa_sigma_lowest_free_base;
      destruct HINV as ((_ & HB1 & HB2 & HB3 & _) & _);
      exact (LFB ly S W (ms_regs msx) (ms_mem msx) _ [] r k bs HPRE1
               ltac:(rewrite La0; denv; exact E10) ltac:(rewrite La1; denv; exact E11) ltac:(lia) Hin HL
               ltac:(intros i Hi; rewrite (KEEPR i Hi); apply HBY; exact Hi) HB1 HB2 HB3)
    | intros aa Haa; exfalso; exact (inFP_nil aa Haa) ]
  | ] end.
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJ1 & HP2 & (-> & -> & -> & z & Hz & Hlf)).
  change (0 + 0) with 0 in HJ2.
  rewrite Lra.
  (* the registry block is kept by the call (its footprint is []) *)
  assert (KEEPR2 : forall i, 0 <= i < 288 -> aview SEGS (w_H W) mem2 (r + i) = aview SEGS (w_H W) mem (r + i)).
  { intros i Hi. pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
    lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
      rewrite (F2 r REG_SIZE i Hin Hin ltac:(change (req_size REG_SIZE) with 288; lia) ltac:(intros X; exact (inFP_nil _ X)));
      exact (KEEPR i Hi) end. }
  clear KEEPR. rename KEEPR2 into KEEPR.
  lazymatch type of HS with st_ok _ ?Ex _ (restrict _ ?msx) =>
    let HEIx := lazymatch goal with H : img_env _ _ Ex |- _ => H end in
    let HEIn := fresh "HEIc" in pose proof (img_env_havoc_hi Ex 1000 (map (getr regs2) CLOB) HEIx ltac:(cbv; lia)) as HEIn;
    assert (Lspz : spZ (ms_regs msx) = spZ regs - 96)
      by (change (spZ (ms_regs msx)) with (bv_unsigned (getr (ms_regs msx) 2)); rewrite Lsp, (dsv_atom _ 2 (-96) (spZ regs)) by (denv; rewrite <- Usp, Z_to_bv_bv_unsigned; reflexivity);
          rewrite unsigned_lit_small by lia; lia) end.
  jafter_call_keep_hi HS 1000%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 3]%nat HS2.
  match type of HS2 with ?Q -> _ => assert (HQ : Q); [| specialize (HS2 HQ); clear HQ] end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
    - eapply (region_kept_stack_sub SEGS B); [exact HJ1 | exact HJ2 | denv; exact Usp | lia | rewrite WS; lia | lia | lia | lia].
    - eapply (region_kept_block_sub SEGS B); [exact HJ1 | denv; rewrite E10; apply unsigned_lit_small; lia | exact Hin | exact Hin
        | lia | change (req_size REG_SIZE) with 288; lia | lia | intros aa _ X; exact (inFP_nil _ X)]. }
  rewrite <- restrict_mkst_fx in HS2. clear HS. rename HS2 into HS.
  lazymatch type of HS with st_ok_pi _ _ ?Ex2 _ _ =>
    assert (SHOK2 : sh_ok SEGS DBx dm_SH Ex2 (mrestrict (w_H W) mem2)) end.
  { unfold sh_ok, dm_SH. constructor; [|constructor].
    eapply (dshent_block ly S W mem2 md2 _ 10 r r REG_SIZE 0 288 (proj1 HJ2) Hin).
    - unfold DBx. rewrite (U_atom _ 32 DSB) by (first [denv; exact E32 | unfold DSB; lia]). reflexivity.
    - rewrite (U_atom _ 10 r) by (first [denv; exact E10 | lia]). reflexivity.
    - lia.
    - lia.
    - change (req_size REG_SIZE) with 288. lia. }
  clear SHOK. rename SHOK2 into SHOK.
  clear HJ. rename HJ2 into HJ.
  (* 0x818f0  bgez a0 *)
  drun W E mem r Hrr Usp.
  assert (Hzr : -1 <= z <= 40) by (destruct (dm_lowest_free_range bs k z ltac:(lia) Hlf) as [-> | (? & ?)]; lia).
  psrr_branch_tok RUN BR HS SHOK Dspan.
  + rewrite dbr_ge in Hc. dsa Hc 1004%nat z Hz. dsl Hc 0. apply negb_true_iff, Z.ltb_ge in Hc. rename Hc into Hz0.
    dpaj_run_to_tok RUNTO HS HJ SHOK Dspan 6592; [awr_ok_tac; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb]; exact Usp |].
    dkeep_upd W E mem r Hrr Usp.
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
      assert (HAE1 : env_agree 32 (Ereg regs (dm_extra bs)) Ex)
        by (eapply env_agree_trans; [exact HAE | split; [intros nn Hnn; repeat first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]; reflexivity | reflexivity]]) end.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
      assert (HFR : dframe_ok regs W (ms_mem msx)) by (dframe_tac HS Usp HAE1) end.
    prreg_raw HS (2%bv : bv 5) R2. prreg_raw HS (3%bv : bv 5) R3. prreg_raw HS (4%bv : bv 5) R4.
    prreg_raw HS (26%bv : bv 5) R26. prreg_raw HS (27%bv : bv 5) R27. prreg_raw HS (8%bv : bv 5) R8.
    prreg_raw HS (9%bv : bv 5) R9. prreg_raw HS (24%bv : bv 5) R24. prreg_raw HS (23%bv : bv 5) R23.
    prreg_raw HS (21%bv : bv 5) R21. prreg_raw HS (22%bv : bv 5) R22. prreg_raw HS (19%bv : bv 5) R19.
    prreg_raw HS (18%bv : bv 5) R18.
    rewrite (dsv_atom _ 2 (-96) (spZ regs)) in R2 by (denv; rewrite <- Usp, Z_to_bv_bv_unsigned; reflexivity).
    rewrite (dsv_reg _ regs _ 3 3%bv HAE1) in R3 by (first [lia | reflexivity]).
    rewrite (dsv_reg _ regs _ 4 4%bv HAE1) in R4 by (first [lia | reflexivity]).
    rewrite (dsv_reg _ regs _ 26 26%bv HAE1) in R26 by (first [lia | reflexivity]).
    rewrite (dsv_reg _ regs _ 27 27%bv HAE1) in R27 by (first [lia | reflexivity]).
    rewrite (dsv_atom _ 12 0 nm) in R8 by (denv; exact E12). rewrite Z.add_0_r in R8.
    rewrite (dsv_atom _ 10 280 r) in R9 by (denv; exact E10).
    rewrite (dsv_atom _ 32 0 DSB) in R24 by (denv; exact E32). rewrite Z.add_0_r in R24.
    assert (D8 : 0 <= (r + 280) / 8 <= r + 280) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    lazymatch type of R23 with _ = sv_denot ?Ex _ =>
      rewrite (proj1 (dV_srl Ex 10 32 280 r DSB ltac:(denv; exact E10) ltac:(denv; exact E32) ltac:(lia) ltac:(lia)
                       ltac:(unfold DSB; lia) ltac:(unfold DSB; lia))) in R23;
      rewrite (dV_row Ex 10 34 r n ltac:(denv; exact E10) ltac:(denv; exact E34) ltac:(lia) ltac:(lia) ltac:(lia)) in R21 end.
    rewrite (dsv_atom _ 1004 0 z) in R22 by (denv; exact Hz). rewrite Z.add_0_r in R22.
    rewrite (dsv_atom _ 11 0 k) in R19 by (denv; exact E11). rewrite Z.add_0_r in R19.
    rewrite (dsv_atom _ 13 0 b0) in R18 by (denv; exact E13). rewrite Z.add_0_r in R18.
    pmkst HS.
    eapply (dp_walk ly S W regs mem md ch r k nm b0 bs s G _ _ _ z 0 DP).
    - split; [exact HJ|]. split; [rewrite R2; unfold w64; f_equal; lia|]. split; [exact R3|]. split; [exact R4|].
      split; [exact R26|]. split; [exact R27|]. split; [exact HFR|].
      split; [intros i Hi; rewrite (KEEPR i Hi); apply HBY; exact Hi|].
      split; [exact R8|]. split; [exact R9|]. split; [exact R24 | exact R23].
    - apply (dm_placed_free bs k b0 z); first [exact Hkev | exact Hlf | lia].
    - exact R21.
    - exact R22.
    - exact R19.
    - exact R18.
  + rewrite dbr_ge in Hc. dsa Hc 1004%nat z Hz. dsl Hc 0. apply negb_false_iff, Z.ltb_lt in Hc.
    drun W E mem r Hrr Usp. dleaf W regs bs E1 Hra HAE HBY (dm_refused_nofree bs k b0 z Hb0n Hlf Hc). }
rewrite dbr_lt in Hc. dsa Hc 13%nat b0 E13. dsl Hc 0.
apply Z.ltb_ge in Hc. rename Hc into Hb0p.
(* 0x81854  blt (fabric - k)_32, b0 *)
drun W E mem r Hrr Usp.
psrr_branch_tok RUN BR HS SHOK Dspan.
{ rewrite dbr_lt in Hc. rewrite (dS_aluw_sub_atoms _ 33 11 fab k) in Hc by (cbn [ew ewset Nat.eqb]; first [exact E33 | exact E11 | lia]).
  dsa Hc 13%nat b0 E13.
  apply Z.ltb_lt in Hc. drun W E mem r Hrr Usp. dleaf W regs bs E1 Hra HAE HBY (dm_refused_room bs k b0 Hb0p Hc). }
rewrite dbr_lt in Hc. rewrite (dS_aluw_sub_atoms _ 33 11 fab k) in Hc by (cbn [ew ewset Nat.eqb]; first [exact E33 | exact E11 | lia]).
dsa Hc 13%nat b0 E13.
apply Z.ltb_ge in Hc. rename Hc into Hroom.
(* 0x81858  blez n *)
drun W E mem r Hrr Usp.
psrr_branch_tok RUN BR HS SHOK Dspan.
{ rewrite dbr_ge in Hc. dsl Hc 0. dsa Hc 34%nat n E34.
  apply negb_true_iff, Z.ltb_ge in Hc. assert (Hn0 : n = 0) by lia.
  dpaj_run_to_tok RUNTO HS HJ SHOK Dspan 6592; [awr_ok_tac; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb]; exact Usp |]. dkeep_upd W E mem r Hrr Usp.
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (HAE1 : env_agree 32 (Ereg regs (dm_extra bs)) Ex)
      by (eapply env_agree_trans; [exact HAE | split; [intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity]]) end.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
    assert (HFR : dframe_ok regs W (ms_mem msx)) by (dframe_tac HS Usp HAE1) end.
  prreg_raw HS (2%bv : bv 5) R2. prreg_raw HS (3%bv : bv 5) R3. prreg_raw HS (4%bv : bv 5) R4.
  prreg_raw HS (26%bv : bv 5) R26. prreg_raw HS (27%bv : bv 5) R27. prreg_raw HS (8%bv : bv 5) R8.
  prreg_raw HS (9%bv : bv 5) R9. prreg_raw HS (24%bv : bv 5) R24. prreg_raw HS (23%bv : bv 5) R23.
  prreg_raw HS (21%bv : bv 5) R21. prreg_raw HS (22%bv : bv 5) R22. prreg_raw HS (19%bv : bv 5) R19.
  prreg_raw HS (18%bv : bv 5) R18.
  rewrite (dsv_atom _ 2 (-96) (spZ regs)) in R2 by (denv; rewrite <- Usp, Z_to_bv_bv_unsigned; reflexivity).
  rewrite (dsv_reg _ regs _ 3 3%bv HAE1) in R3 by (first [lia | reflexivity]).
  rewrite (dsv_reg _ regs _ 4 4%bv HAE1) in R4 by (first [lia | reflexivity]).
  rewrite (dsv_reg _ regs _ 26 26%bv HAE1) in R26 by (first [lia | reflexivity]).
  rewrite (dsv_reg _ regs _ 27 27%bv HAE1) in R27 by (first [lia | reflexivity]).
  rewrite (dsv_atom _ 12 0 nm) in R8 by (denv; exact E12). rewrite Z.add_0_r in R8.
  rewrite (dsv_atom _ 10 280 r) in R9 by (denv; exact E10).
  rewrite (dsv_atom _ 32 0 DSB) in R24 by (denv; exact E32). rewrite Z.add_0_r in R24.
  assert (D8 : 0 <= (r + 280) / 8 <= r + 280) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  lazymatch type of R23 with _ = sv_denot ?Ex _ =>
    rewrite (proj1 (dV_srl Ex 10 32 280 r DSB ltac:(denv; exact E10) ltac:(denv; exact E32) ltac:(lia) ltac:(lia)
                     ltac:(unfold DSB; lia) ltac:(unfold DSB; lia))) in R23;
    rewrite (dV_row Ex 10 34 r n ltac:(denv; exact E10) ltac:(denv; exact E34) ltac:(lia) ltac:(lia) ltac:(lia)) in R21 end.
  rewrite (dsv_atom _ 13 0 b0) in R22 by (denv; exact E13). rewrite Z.add_0_r in R22.
  rewrite (dsv_atom _ 11 0 k) in R19 by (denv; exact E11). rewrite Z.add_0_r in R19.
  rewrite (dsv_atom _ 13 0 b0) in R18 by (denv; exact E13). rewrite Z.add_0_r in R18.
  pmkst HS.
  eapply (dp_walk ly S W regs mem md ch r k nm b0 bs s G _ _ _ b0 1 DP).
  - split; [exact HJ|]. split; [rewrite R2; unfold w64; f_equal; lia|]. split; [exact R3|]. split; [exact R4|].
    split; [exact R26|]. split; [exact R27|]. split; [exact HFR|].
    split; [intros i Hi; rewrite (KEEPR i Hi); apply HBY; exact Hi|].
    split; [exact R8|]. split; [exact R9|]. split; [exact R24 | exact R23].
  - apply dm_placed_pinned; first [exact Hkev | lia | intros i Hi; lia].
  - exact R21.
  - exact R22.
  - exact R19.
  - exact R18. }
rewrite dbr_ge in Hc. dsl Hc 0. dsa Hc 34%nat n E34.
apply negb_false_iff, Z.ltb_lt in Hc. rename Hc into Hnp.
dpaj_run_to_tok RUNTO HS HJ SHOK Dspan 6444; [awr_ok_tac; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb]; exact Usp |]. dkeep_upd W E mem r Hrr Usp.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
  assert (HAE1 : env_agree 32 (Ereg regs (dm_extra bs)) Ex)
    by (eapply env_agree_trans; [exact HAE | split; [intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity]]) end.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
  assert (HFR : dframe_ok regs W (ms_mem msx)) by (dframe_tac HS Usp HAE1) end.
prreg_raw HS (2%bv : bv 5) Q2. prreg_raw HS (3%bv : bv 5) Q3. prreg_raw HS (4%bv : bv 5) Q4.
prreg_raw HS (26%bv : bv 5) Q26. prreg_raw HS (27%bv : bv 5) Q27. prreg_raw HS (8%bv : bv 5) Q8.
prreg_raw HS (9%bv : bv 5) Q9. prreg_raw HS (24%bv : bv 5) Q24. prreg_raw HS (23%bv : bv 5) Q23.
prreg_raw HS (10%bv : bv 5) Q10. prreg_raw HS (13%bv : bv 5) Q13. prreg_raw HS (14%bv : bv 5) Q14.
prreg_raw HS (15%bv : bv 5) Q15. prreg_raw HS (12%bv : bv 5) Q12. prreg_raw HS (18%bv : bv 5) Q18.
prreg_raw HS (19%bv : bv 5) Q19. prreg_raw HS (20%bv : bv 5) Q20. prreg_raw HS (21%bv : bv 5) Q21.
prreg_raw HS (25%bv : bv 5) Q25.
rewrite (dsv_atom _ 2 (-96) (spZ regs)) in Q2 by (denv; rewrite <- Usp, Z_to_bv_bv_unsigned; reflexivity).
rewrite (dsv_reg _ regs _ 3 3%bv HAE1) in Q3 by (first [lia | reflexivity]).
rewrite (dsv_reg _ regs _ 4 4%bv HAE1) in Q4 by (first [lia | reflexivity]).
rewrite (dsv_reg _ regs _ 26 26%bv HAE1) in Q26 by (first [lia | reflexivity]).
rewrite (dsv_reg _ regs _ 27 27%bv HAE1) in Q27 by (first [lia | reflexivity]).
rewrite (dsv_atom _ 12 0 nm) in Q8 by (denv; exact E12). rewrite Z.add_0_r in Q8.
rewrite (dsv_atom _ 10 280 r) in Q9 by (denv; exact E10).
rewrite (dsv_atom _ 32 0 DSB) in Q24 by (denv; exact E32). rewrite Z.add_0_r in Q24.
assert (D8 : 0 <= (r + 280) / 8 <= r + 280) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (D8' : 0 <= (r + 8) / 8 <= r + 8) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
lazymatch type of Q23 with _ = sv_denot ?Ex _ =>
  rewrite (proj1 (dV_srl Ex 10 32 280 r DSB ltac:(denv; exact E10) ltac:(denv; exact E32) ltac:(lia) ltac:(lia)
                   ltac:(unfold DSB; lia) ltac:(unfold DSB; lia))) in Q23;
  rewrite (proj2 (dV_srl Ex 10 32 8 r DSB ltac:(denv; exact E10) ltac:(denv; exact E32) ltac:(lia) ltac:(lia)
                   ltac:(unfold DSB; lia) ltac:(unfold DSB; lia))) in Q14;
  rewrite (dV_aluw_add Ex 13 11 b0 k ltac:(denv; exact E13) ltac:(denv; exact E11) ltac:(lia) ltac:(lia) ltac:(lia)) in Q12 end.
rewrite (dsv_atom _ 10 12 r) in Q10 by (denv; exact E10).
rewrite (dsv_atom _ 10 12 r) in Q13 by (denv; exact E10).
rewrite (dsv_atom _ 34 0 n) in Q15 by (denv; exact E34). rewrite Z.add_0_r in Q15.
rewrite (dsv_atom _ 13 0 b0) in Q18 by (denv; exact E13). rewrite Z.add_0_r in Q18.
rewrite (dsv_atom _ 11 0 k) in Q19 by (denv; exact E11). rewrite Z.add_0_r in Q19.
cbn [sv_denot] in Q20.
rewrite (dsv_atom _ 10 0 r) in Q21 by (denv; exact E10). rewrite Z.add_0_r in Q21.
rewrite (dsv_atom _ 34 0 n) in Q25 by (denv; exact E34). rewrite Z.add_0_r in Q25.
pmkst HS.
eapply (dl_walk (Z.to_nat (n - 0)) ly S W regs mem md ch r k nm b0 bs s G _ _ _ 0 DP).
- split; [exact HJ|]. split; [rewrite Q2; unfold w64; f_equal; lia|]. split; [exact Q3|]. split; [exact Q4|].
  split; [exact Q26|]. split; [exact Q27|]. split; [exact HFR|].
  split; [intros i Hi; rewrite (KEEPR i Hi); apply HBY; exact Hi|].
  split; [exact Q8|]. split; [exact Q9|]. split; [exact Q24 | exact Q23].
- reflexivity.
- lia.
- exact Hkev.
- lia.
- lia.
- lia.
- lia.
- lia.
- intros j Hj. lia.
- rewrite Q10. f_equal. lia.
- rewrite Q13. f_equal. lia.
- rewrite Q14. replace (r + 56 * 0 + 8) with (r + 8) by lia. reflexivity.
- rewrite Q15. f_equal. lia.
- exact Q12.
- exact Q18.
- exact Q19.
- rewrite Q20. apply bv_eq. reflexivity.
- exact Q21.
- exact Q25.
Qed.

End h.
End f.
End d.
