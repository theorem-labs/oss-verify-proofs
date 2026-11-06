(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACh9.v:86-90
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203, 332-335, 358-363, 460-463 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:1593-1596, 1605-1615 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:2082-2086 [Apache-2.0 OR MIT], for libreac/fuzz_identity's ASan build
   (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8b.v:393-396. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_catalogue_defect.v, with its module paths and module names changed; 1658 of its 1740 lines of code are new or changed and 573 lines of the source are left out. *)
(* reac_boxreg_declare (fuzz_boxreg.asan-ubsan 0x81ad0, 167 instructions): the contract of the ASan+UBSan build's
   code. The function takes an 80-byte frame on the machine stack (addi sp,sp,-80; ra, s0..s8 saved there). It
   refuses (returns -1, writes nothing) unless k (a1, an int) is even and 2..40 (addiw a1,-41 / bltu -39, andi 1);
   it then checks r against NULL and 4-byte alignment for UBSan, refuses unless the fabric word at r + 284 is at
   least k and the count n at r + 280 is at most 4 (each word read after its shadow byte is checked). With b0 (a3)
   >= 0 it computes fabric - k with a UBSan overflow check, refuses when fabric - k < b0, then calls range_taken
   (r, b0, k) (0x81ba8) and refuses on a non-zero result; with b0 < 0 it calls lowest_free_base (r, k) (0x81bc0)
   and refuses on a negative result. Then it re-reads n (shadow-checked; UBSan index check n < 6), forms
   row = r + 56 n (UBSan pointer-overflow check), calls __asan_memset (row, 0, 56) (0x81c04), stores base (+8),
   nch (+12) and pinned = (b0 >= 0) (+20) after their shadow checks, calls snprintf (row + 24, 32, "%s", name)
   through __interceptor_trampoline_snprintf (0x81c70) when name (a2) is not NULL, re-reads n and stores n + 1
   (UBSan overflow check), and returns the old n. Every UBSan check branches to the trap at 0x81cc8 (unimp); the
   null / alignment and pointer-overflow branches are refuted by the allocator's block law (a block's address is
   a multiple of 16, at least 4096 and below the allocation ceiling), the others by n <= 4 and fabric, k in 1..40.
   It writes nothing outside the 288-byte registry struct at r (a heap block of the caller), its own frame and the
   wrappers' stack below it.
   Layout: the registry struct is 288 bytes: rows 0..280 (5 rows of 56 bytes: mac 0..5, base +8, nch +12,
   established +16, pinned +20, name +24..+55), n at +280, fabric at +284.
   Hazard (snprintf): the snprintf wrapper's contract is lib/B/Rt/SnprintfDefB.v absnprintf_realizes (statement
   only, not yet proved); the proof takes it at pa_sigma BB___interceptor_trampoline_snprintf. Its measured stack
   need is 8160 bytes, more than one ESTACK, so the stack below the call's sp is 2 * ESTACK and
   REAC_BOXREG_DECLARE_STKB = own frame 80 + max (LOWEST_FREE_BASE_STKB, RANGE_TAKEN_STKB, 2 * ESTACK);
   __asan_memset needs only ESTACK. The snprintf post lets f10 and fcsr change (a Theorem Labs lane's
   A/Prog/vsnprintf_wrap_c.v 88-100, and a Theorem Labs lane's shared post 401616133a7 FMsnprintfShared.v:142-145), so since
   82db7cf8c7c absnprintf_realizes returns at some fx' and this function's post is apost_baseF's: f registers equal
   except f10, fcsr the entry's or rounding mode 0.
   Format strings (.rodata): 0x20d40 "%s" (bytes 25 73 00) is the listing's A_OBJ 10, built by the auipc/addi
   pair at 0x81c60 / 0x81c64 (AB_declare_fmtP). 0x20d60 (A_OBJ 11) is "" (one 00 byte), reac_boxreg_set_name's
   empty-string argument; this function never reads it (it skips snprintf when name is NULL). The wrapper's own
   .rodata reads (musl's vfprintf tables, e.g. the "-+   0X0x" prefix at 0x10b54) come under absn_rom_kept.
   How each premise of absnprintf_realizes holds at the call (0x81c70), which comes after range_taken (0x81ba8,
   when b0 >= 0) or lowest_free_base (0x81bc0, when b0 < 0) and after __asan_memset. An ajournal carries an image
   byte only when it is neither an owned static nor an errno byte (lib/Reusable/YCbq.v:362) and carries no byte below
   alloc_ceiling outside the blocks (:358), so the image's shadow and a heap chunk's tail are not carried; the
   premises are therefore stated so that each one either holds in every state or is carried:
   - absn_rom_kept (the contract's read-only view, lib/B/Rt/SnprintfDefB.v): arodata_okP on the read-only segments;
     arodata_okP is carried by every journal (lib/A/Prog/BoxBase.v arodata_ok_journalP) and by memset's post.
   - "%s" bytes: absn_rom_bytes (state-free: read-only image bytes that are no owned static and no errno byte),
     read through absn_rom_kept at the call.
   - "%s" shadow: globs_marked G with In (AB_declare_fmtP, 3) G (range_addressable) and img_shadow_vis with the
     64-byte margins (shadow_hull_vis), lib/A/Prog/BoxRo.v ro_read_ok_glob; both hold in every AR state.
   - "%s" 0 < f, amem_range, apart from the window and from the destination: from the margins, alloc_ceiling below
     the stack, and AR_client_img_law (a heap byte is no image byte).
   - name bytes s ++ [0]: inside the name's heap block, which every journal keeps (YCbq.v:360-361, callee FP = [])
     and the function's own writes miss (the registry block is apart from it; memset keeps all else).
   - name shadow and hull: AR_shadow_law for the name's block (every AR state); amem_range from AR_blocks_law.
   - the rest of the NUL's 8-byte word: inside the block, or past its requested size, which absn_blk_tail_vis makes
     readable in every AR state (the block starts on a 16-byte boundary, so the word ends by nm + round_up nn 8).
   - destination: the 32-byte name field r + 56 n + 24 of the registry block (n <= 4 from boxreg_inv, re-read
     after the callee from the kept registry bytes).
   The __asan_report_load4 / store4 branches (0x81ccc .. 0x81d68) are refuted by the shadow of the registry block.
   Image difference: the asan build (lib/A/Prog/ReacBoxregDeclare.v) has no UBSan checks, scans the rows inline
   instead of calling range_taken, and computes the row from the n it read first.
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
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBList BoxBPa.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaJournal BoxBase BoxRo.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import
BoxBLowestFreeBase BoxBRangeTaken BoxBReacBoxregInit.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt Require Import SnprintfDefB.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg BoxregUpd reac_boxreg_declare_c.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBPaLib YC1g YC1h YC45 BoxBFrame.
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
#[local] Notation SIGMA := (@pa_sigma _ boxb_listing PI).
(* The function's address in the image, the address of its format string "%s" (A_OBJ 10, 0x20d40 in
   fuzz_boxreg.asan-ubsan), and the stack it needs: its own 80-byte frame and below it the deepest of
   lowest_free_base's stack, range_taken's stack and the 2 * ESTACK of the snprintf wrapper (the memset wrapper
   needs ESTACK). *)
Definition AB_reac_boxreg_declareP : Z := BASE + AF_reac_boxreg_declare.
Definition AB_declare_fmtP : Z := VAL (A_OBJ 10).
Definition REAC_BOXREG_DECLARE_STKB : Z :=
  80 + Z.max (Z.max LOWEST_FREE_BASE_STKB RANGE_TAKEN_STKB) (2 * ESTACK).
Section h.
Variable B : asyms.
(* The registry block's bytes as Pau's byte list. *)
Definition tbdecl_reg_bytes (W : world SEGS) (mem : word -> option byte) (r : Z) (bs : list byte) : Prop :=
forall i, 0 <= i < REG_SIZEB ->
  aview SEGS (w_H W) mem (r + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0))).
(* The name argument (reac_boxreg_set_name_c.v name_ok, restated over the heap blocks): NULL with s = [], or
   the first byte of a heap block, apart from the registry block, that holds the characters s (none 0) and a NUL.
   The rest of the NUL's 8-byte word and the shadow are not stated here: AR and absn_blk_tail_vis give them in every
   state, so also at the snprintf call after range_taken / lowest_free_base. *)
Definition tbdecl_name_ok (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte) (r nm : Z)
  (s : list Z) : Prop :=
(nm = 0 /\ s = []) \/
(nm <> 0 /\ Forall (fun c => 0 < c < 256) s /\ Z.of_nat (length s) + 8 < 2 ^ 31 /\
 exists nn, In (nm, nn) (ablocks B ly S) /\ Z.of_nat (length s) + 1 <= nn /\
 (nm + nn <= r \/ r + REG_SIZEB <= nm) /\
 (forall i, 0 <= i <= Z.of_nat (length s) ->
   aview SEGS (w_H W) mem (nm + i) = Some (nth (Z.to_nat i) (s ++ [0]) 0))).
Definition tbreac_boxreg_declare_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md (r k b0 : Z)
  (bs : list byte) (s : list Z) : world SEGS -> config -> Prop :=
apost_baseF SEGS B REAC_BOXREG_DECLARE_STKB [(r, r + REG_SIZEB)] regs ly S W mem md 0
(fun ly' S' W' regs' mem' md' =>
ly' = ly /\ S' = S /\ W' = W /\ Permutation (ablocks B ly' S') (ablocks B ly S) /\
((reac_boxreg_declare_c.declare_refused bs k b0 /\ getr regs' 10 = w64 (-1) /\ tbdecl_reg_bytes W' mem' r bs) \/
 (exists b p, reac_boxreg_declare_c.declare_placed bs k b0 b p /\
   getr regs' 10 = w64 (Boxreg.bx_n bs) /\
   tbdecl_reg_bytes W' mem' r (BoxregUpd.new_row_bytes bs (reac_boxreg_declare_c.decl_row b k p s))))).
Definition tbreac_boxreg_declare_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (r k nm b0 : Z) (bs : list byte) (s : list Z) (G : list (Z * Z)),
afn_pre SEGS B REAC_BOXREG_DECLARE_STKB ly S W regs mem md ch ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
getr regs 10 = w64 r -> getr regs 11 = w64 k -> getr regs 12 = w64 nm -> getr regs 13 = w64 b0 ->
-2 ^ 31 <= k < 2 ^ 31 -> -2 ^ 31 <= b0 < 2 ^ 31 ->
In (r, REG_SIZEB) (ablocks B ly S) -> tbdecl_reg_bytes W mem r bs -> Boxreg.boxreg_inv bs ->
tbdecl_name_ok ly S W mem r nm s ->
(* facts of the image and of the runtime's symbols, true in every state *)
absn_blk_tail_vis SEGS B -> img_shadow_vis SEGS B -> globs_marked SEGS B G ->
(* the format "%s": bytes of the read-only image, a registered global *)
absn_rom_bytes SEGS B AB_declare_fmtP ABSN_FMT -> In (AB_declare_fmtP, 3) G ->
IMG_LO + 64 <= AB_declare_fmtP -> AB_declare_fmtP + 3 + 64 <= IMG_HI ->
(* R2 (a Theorem Labs lane 15:05Z): the format below image B's GOT canary slot, which the snprintf contract now asks (P2) *)
AB_declare_fmtP + 3 <= 0x99f60 ->
(* the rounding mode at entry, which this function hands to the snprintf wrapper (SnprintfDefB.v) *)
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
SRr SEGS W (cfg_at SEGS AB_reac_boxreg_declareP regs mem md)
  (tbreac_boxreg_declare_post regs ly S W mem md r k b0 bs s).
(* The walk. Section hypotheses: the allocator laws, the image's GOT / shadow-cell objects (PALib), the memset and
   snprintf wrappers' contracts and the contracts of the two program callees. *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA BB___asan_memset).
Hypothesis ASNPRINTF : absnprintf_realizes SEGS B (SIGMA BB___interceptor_trampoline_snprintf).
Hypothesis TRT : tbrange_taken_spec B.
Hypothesis TLFB : tblowest_free_base_spec B.
(* a Theorem Labs lane's continuation lemma for the FP-existential snprintf post, relocated to boxreg as lib/A/Rt/FMsnprintfSx.v
   srr_fx_continue (ad235a56db0 proofs/omx-clap-core/fuzz_manifest/lib/A/FMsnprintfSx.v:53-77): the caller binds the
   FP state fx' the callee returns at and continues at @cfg_at fx'. Required, not imported: the walk names it fully. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require FMsnprintfSx.
(* R2: amem8_of_block (lib/A/Rt/SnprintfAmem.v), the snprintf contract's string bound amem_range x (|s| + 8) for a
   string inside a heap block. Required, not imported: the walk names it fully. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require SnprintfAmem.
(* st_ok reads the FP state only to compare it with the machine's f registers and fcsr: the same machine rebuilt at
   any FP state fy has the same symbolic state at fy (the walk's state at the snprintf call, which the engine leaves
   in st_ok form at the trampoline, carried to the FP state the wrapper returns at). *)
Lemma dsn_st_swap : forall (fy : YK11.FPState) E ss (H : word -> bool) (ms : machine_state),
  st_ok (fx := fx) SEGS E ss (restrict H ms) -> ss_resv ss = None ->
  st_ok (fx := fy) SEGS E ss (restrict H (@mkst fy (ms_regs ms) (ms_pc_val ms) (ms_mem ms) (ms_rom ms))).
Proof.
intros fy E ss H ms HS Hrv. destruct ss as [pc0 sr0 fr0 sm0 rv0 fs0]. cbn [ss_resv] in Hrv. subst rv0.
unfold st_ok in *.
destruct HS as (_ & H2 & _ & _ & _ & H6 & H7 & H8 & H9).
split; [reflexivity|]. split; [exact H2|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [exact H6|]. split; [exact H7|]. split; [exact H8 | exact H9].
Qed.
(* The shadow offset the code loads through the GOT word (object 1) from the shadow cell (object 12). *)
Definition SBD : Z := 0x7fff8000.
(* The frame slots of the saved registers: (register, offset from the frame base sp - 80). *)
Definition DECL_SAVES : list (nat * Z) :=
[(1%nat, 72); (8%nat, 64); (9%nat, 56); (18%nat, 48); (19%nat, 40); (20%nat, 32); (21%nat, 24); (22%nat, 16);
 (23%nat, 8); (24%nat, 0)].
(* The machine at 0x81bcc (offset 0x1c20), where both placement paths join (after range_taken's 0 or
   lowest_free_base's z >= 0): the registers the rest of the function reads, and the saved registers in the frame. *)
Definition dplace_at (regs regs2 : bvmap 5 word) (W : world SEGS) (mem2 : word -> option byte) (r k nm b0 b : Z)
  : Prop :=
spZ regs2 = spZ regs - 80 /\ getr regs2 3 = getr regs 3 /\ getr regs2 4 = getr regs 4 /\
getr regs2 25 = getr regs 25 /\ getr regs2 26 = getr regs 26 /\ getr regs2 27 = getr regs 27 /\
getr regs2 8 = w64 nm /\ getr regs2 9 = w64 (r + 280) /\ getr regs2 18 = w64 b0 /\ getr regs2 19 = w64 k /\
getr regs2 20 = w64 (-1) /\ getr regs2 21 = w64 r /\ getr regs2 22 = w64 b /\
getr regs2 23 = w64 (SBD + (r + 280) / 8) /\ getr regs2 24 = w64 SBD /\
(forall i o, In (i, o) DECL_SAVES ->
  val_mem SEGS (mrestrict (w_H W) mem2) (spZ regs - 80 + o) 8 (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat i))))).
(* The placement segment, from 0x81bcc to the return: the statement the walk's two placement paths use. *)
Definition dplace_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (r k nm b0 : Z) (bs : list byte) (s : list Z) (G : list (Z * Z))
  (regs2 : bvmap 5 word) mem2 md2 (b : Z),
afn_pre SEGS B REAC_BOXREG_DECLARE_STKB ly S W regs mem md ch ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
getr regs 10 = w64 r -> getr regs 11 = w64 k -> getr regs 12 = w64 nm -> getr regs 13 = w64 b0 ->
-2 ^ 31 <= k < 2 ^ 31 -> -2 ^ 31 <= b0 < 2 ^ 31 ->
In (r, REG_SIZEB) (ablocks B ly S) -> tbdecl_reg_bytes W mem r bs -> Boxreg.boxreg_inv bs ->
tbdecl_name_ok ly S W mem r nm s ->
absn_blk_tail_vis SEGS B -> img_shadow_vis SEGS B -> globs_marked SEGS B G ->
absn_rom_bytes SEGS B AB_declare_fmtP ABSN_FMT -> In (AB_declare_fmtP, 3) G ->
IMG_LO + 64 <= AB_declare_fmtP -> AB_declare_fmtP + 3 + 64 <= IMG_HI ->
AB_declare_fmtP + 3 <= 0x99f60 ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
ajournal SEGS B REAC_BOXREG_DECLARE_STKB (spZ regs) [(r, r + REG_SIZEB)] ly S W mem md [] ly S W mem2 md2 0 ->
tbdecl_reg_bytes W mem2 r bs ->
dplace_at regs regs2 W mem2 r k nm b0 b ->
reac_boxreg_declare_c.declare_placed bs k b0 b (if b0 <? 0 then 0 else 1) ->
SRr SEGS W (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 0x1c20)) mem2 (seg_rom SEGS)) md2)
  (tbreac_boxreg_declare_post regs ly S W mem md r k b0 bs s).
(* The snprintf call at 0x81c70 in the journal form of aj_intrin_at (lib/Reusable/YCbq.v): the machine at the
   wrapper's trampoline with the link raw, the destination d (32 bytes of a heap block of the call's state that the
   journal may write), the format f ("%s", a registered read-only global with its margins) and the string s at x (a
   heap block apart from the destination's block). The wrapper returns at SOME FP state fx' (its post,
   lib/B/Rt/SnprintfDefB.v): the f registers but f10 kept, rounding mode 0 in fcsr. *)
Definition dsnp_spec : Prop :=
forall W (regsT : bvmap 5 word) memT STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdc k (o : Z) raw (d f x : Z)
  (s : list Z) (p m xn : Z) (G : list (Z * Z)),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdc k ->
getr regsT 10 = w64 d -> getr regsT 11 = w64 32 -> getr regsT 12 = w64 f -> getr regsT 13 = w64 x ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
In (p, m) (ablocks B lyc Sc) -> p <= d -> d + 32 <= p + m ->
(forall a, d <= a < d + 32 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memT) ->
img_shadow_vis SEGS B -> globs_marked SEGS B G -> absn_rom_bytes SEGS B f ABSN_FMT -> In (f, 3) G ->
IMG_LO + 64 <= f -> f + 3 + 64 <= IMG_HI ->
f + 3 <= 0x99f60 ->
absn_blk_tail_vis SEGS B ->
Forall (fun c => 0 < c < 256) s -> Z.of_nat (length s) + 8 < 2 ^ 31 ->
In (x, xn) (ablocks B lyc Sc) -> Z.of_nat (length s) + 1 <= xn -> (x + xn <= p \/ p + m <= x) ->
(forall i, 0 <= i <= Z.of_nat (length s) -> aview SEGS (w_H W) memT (x + i) = Some (nth (Z.to_nat i) (s ++ [0]) 0)) ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA BB___interceptor_trampoline_snprintf)) memT (seg_rom SEGS)) mdc)
  (fun W2 c2 => W2 = W /\ exists (fx' : YK11.FPState) regs2 mem2 md2,
     c2 = @cfg_at fx' SEGS (bv_unsigned raw) regs2 mem2 md2 /\
     (forall j : bv 5, bv_unsigned j <> 10 -> Sem.reg_get (@fp_regs fx') j = Sem.reg_get (@fp_regs fx) j) /\
     Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0 /\
     ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
     aregs_preserved regsT regs2 /\ getr regs2 10 = w64 (Z.of_nat (length s)) /\
     (forall i, 0 <= i < Z.of_nat (length (absn_out 32 s)) ->
       aview SEGS (w_H W) mem2 (d + i) = Some (nth (Z.to_nat i) (absn_out 32 s) 0)) /\
     (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + Z.of_nat (length (absn_out 32 s))) ->
       ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
     (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
(* Helpers of decl_snprintf_at: the 8-byte word that holds the NUL ends by a multiple of 8 above it (a block's end
   below a 16-aligned next block or the allocation ceiling) and by the block's 8-byte rounded end; the call writes at
   most 32 bytes. *)
Lemma dsn_mod8_16 : forall a, a mod 16 = 0 -> a mod 8 = 0.
Proof.
intros a H. pose proof (Z.div_mod a 16 ltac:(lia)). pose proof (Z.div_mod a 8 ltac:(lia)).
pose proof (Z.mod_pos_bound a 8 ltac:(lia)). lia.
Qed.
Lemma dsn_mod8_4096 : forall a, a mod 4096 = 0 -> a mod 8 = 0.
Proof.
intros a H. pose proof (Z.div_mod a 4096 ltac:(lia)). pose proof (Z.div_mod a 8 ltac:(lia)).
pose proof (Z.mod_pos_bound a 8 ltac:(lia)). lia.
Qed.
Lemma dsn_word_end_le : forall x k e, e mod 8 = 0 -> x + k < e -> absn_word_end x k <= e.
Proof.
intros x k e He Hk. unfold absn_word_end.
pose proof (Z.div_mod (x + k) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (x + k) 8 ltac:(lia)).
pose proof (Z.div_mod e 8 ltac:(lia)). lia.
Qed.
Lemma dsn_word_end_tail : forall x k n, x mod 16 = 0 -> 0 <= k < n -> absn_word_end x k <= x + round_up n 8.
Proof.
intros x k n Hx Hk. pose proof (dsn_mod8_16 x Hx) as Hx8. unfold absn_word_end, round_up.
pose proof (Z.div_mod (x + k) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (x + k) 8 ltac:(lia)).
pose proof (Z.div_mod x 8 ltac:(lia)).
pose proof (Z.div_mod (n + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 8 - 1) 8 ltac:(lia)). lia.
Qed.
Lemma dsn_req_ge : forall n, n <= req_size n.
Proof. intros n. unfold req_size. destruct (Z.eqb_spec n 0); lia. Qed.
Lemma dsn_len_out : forall s, Z.of_nat (length (absn_out 32 s)) <= 32.
Proof.
intros s. unfold absn_out. rewrite length_app, length_firstn. cbn [length].
change (Z.to_nat (32 - 1)) with 31%nat. pose proof (Nat.le_min_l 31 (length s)). lia.
Qed.
(* The snprintf call: absnprintf_realizes at the trampoline, its premises from the journal (stack, presence), the
   allocator's block and shadow laws (destination, string, NUL word), the read-only view (format bytes,
   absn_rom_kept) and BoxRo (format shadow); its post in journal form as aj_intrin_at gives it, at the wrapper's fx'. *)
Lemma decl_snprintf_at : dsnp_spec.
Proof.
intros W regsT memT STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdc k o raw d f x s p m xn G
  HJ Ha0 Ha1 Ha2 Ha3 Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hpm Hpd Hdm Hwr Hro HV HG Hfmt HinG Hflo Hfhi Hfgot
  Htail Hs Hlen Hxn Hxlen Hxp Hstr HFRM.
pose proof (pa_segs_low) as Hsegs.
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _ & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (ESTACK = 4096) as Hes by reflexivity.
pose proof asan_consts as (C1 & _).
pose proof alloc_ceiling_value as [_ Cc].
pose proof (dsn_mod8_4096 _ Cc) as Hc8.
assert (Hfhi' : f + 67 <= 0x5f6000) by (unfold IMG_HI in Hfhi; lia).
destruct (al_blocks _ _ LAWS lyc Sc W memT mdc p m HAR Hpm) as (Hp16 & Hp4096 & Hpceil & _ & _ & _ & _).
destruct (al_blocks _ _ LAWS lyc Sc W memT mdc x xn HAR Hxn) as (Hx16 & Hx4096 & Hxceil & _ & Hxb & _ & _).
pose proof (dsn_req_ge m) as Rm. pose proof (dsn_req_ge xn) as Rxn.
assert (Hwlo : alloc_ceiling <= sp0 + o - 2 * ESTACK) by lia.
(* the stack: the call's 2 * ESTACK window lies in the journal's present stack *)
assert (HPRE : ecall_pre SEGS B lyc Sc W regsT memT mdc).
{ apply (ecall_pre_at SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdc k regsT o HJ Hsp' Hal Hneg);
  [lia | rewrite Hra; exact Hraw | exact Hgp | exact Htp]. }
assert (H2E : ly_stk_lo lyc + 2 * ESTACK <= spZ regsT) by (rewrite Eslo, Hsp'; lia).
assert (Hwin : forall a, spZ regsT - 2 * ESTACK <= a < spZ regsT -> apresent (w_H W) memT a).
{ intros a Ha. apply Hpres. rewrite Hsp' in Ha. lia. }
(* the destination: below the allocation ceiling, so below the window *)
assert (Hdwin : forall a, d <= a < d + 32 -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT)).
{ rewrite Hsp'. intros a Ha. lia. }
(* the format "%s": read-only image bytes, apart from the heap destination, below the window *)
assert (Hfb : forall i, 0 <= i < 3 -> aview SEGS (w_H W) memT (f + i) = Some (nth (Z.to_nat i) ABSN_FMT 0)).
{ intros i Hi. destruct (Hfmt i ltac:(change (Z.of_nat (length ABSN_FMT)) with 3; lia)) as (Hrom & Hno & Hne & Hv).
  rewrite <- Hv. apply Hro; [left; exact Hrom | exact Hno | exact Hne]. }
assert (Hf0 : 0 < f) by lia.
assert (Hfamr : amem_range f 3) by (unfold amem_range, kLowMemEnd; lia).
assert (Hf64k : 0x10000 <= f) by lia.
assert (Hfwin : forall a, f <= a < f + 3 -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT)).
{ rewrite Hsp'. intros a Ha. lia. }
assert (Hfd : f + 3 <= d \/ d + 32 <= f).
{ destruct (Z_le_gt_dec (f + 3) d) as [H|H]; [left; exact H|].
  destruct (Z_le_gt_dec (d + 32) f) as [H'|H']; [right; exact H'|]. exfalso.
  apply (blk_img SEGS B LAWS lyc Sc W memT mdc p m (Z.max f d) HAR Hpm); [lia|].
  destruct (Hfmt (Z.max f d - f) ltac:(change (Z.of_nat (length ABSN_FMT)) with 3; lia)) as ((sg & Hsg & _ & Hr) & _).
  exists sg. split; [exact Hsg | lia]. }
pose proof (ro_read_ok_glob SEGS B G lyc Sc W memT mdc f 3 f 3 HG HinG HV HAR ltac:(lia) ltac:(lia) ltac:(lia)
  Hflo Hfhi) as [Hfra Hfhull].
(* the string s at x: its heap block, the rest of the NUL's word inside the block or in its chunk tail *)
assert (Hx0 : 0 < x) by lia.
assert (Hnul : forall a, x + Z.of_nat (length s) < a < absn_word_end x (Z.of_nat (length s)) ->
  aview SEGS (w_H W) memT a <> None).
{ intros a Ha. destruct (Z_lt_le_dec a (x + xn)) as [Hin|Hout].
  - apply (aview_some_of_apresent SEGS). exact (proj1 (Hxb a ltac:(lia))).
  - apply (Htail lyc Sc W memT mdc x xn a HAR Hxn). split; [exact Hout|].
    pose proof (dsn_word_end_tail x (Z.of_nat (length s)) xn Hx16 ltac:(lia)). lia. }
assert (Hxamr : amem_range x (Z.of_nat (length s) + 8)).
{ apply (SnprintfAmem.amem8_of_block SEGS B lyc Sc W memT mdc x xn x (Z.of_nat (length s)) LAWS HAR Hxn); lia. }
assert (Hwe : absn_word_end x (Z.of_nat (length s)) <= alloc_ceiling) by (apply dsn_word_end_le; [exact Hc8 | lia]).
assert (Hxwin : forall a, x <= a < absn_word_end x (Z.of_nat (length s)) ->
  ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT)).
{ rewrite Hsp'. intros a Ha. lia. }
assert (Hxd : absn_word_end x (Z.of_nat (length s)) <= d \/ d + 32 <= x).
{ destruct Hxp as [Hb | Hb]; [left | right; lia].
  assert (absn_word_end x (Z.of_nat (length s)) <= p); [apply dsn_word_end_le; [exact (dsn_mod8_16 p Hp16) | lia] | lia]. }
pose proof (range_addressable_of_block SEGS B LAWS lyc Sc W memT mdc x xn x (Z.of_nat (length s) + 1) HAR Hxn
  ltac:(lia) ltac:(lia)) as Hxra.
pose proof (shadow_hull_vis_of_block SEGS B LAWS lyc Sc W memT mdc x xn x (Z.of_nat (length s) + 1) HAR Hxn
  ltac:(lia) ltac:(lia) ltac:(lia)) as Hxhull.
(* the read-only view the wrapper reads *)
assert (Hkept : absn_rom_kept SEGS B W memT).
{ intros a Ha Hno Hne. apply Hro; [left; exact Ha | exact Hno | exact Hne]. }
eapply SRr_mono.
{ exact (ASNPRINTF lyc Sc W regsT memT mdc d 32 f x s p m HPRE H2E Hwin Ha0 Ha1 Ha2 Ha3 ltac:(lia) Hpm Hpd Hdm
    Hdwin Hfb Hf0 Hfamr Hf64k Hfgot Hfwin Hfd Hfra Hfhull Hs Hlen Hx0 Hstr Hnul Hxamr Hxwin Hxd Hxra Hxhull Hkept HFRM). }
cbv beta. intros W2 c2 _ (-> & fx' & regs2 & mem2 & md2 & -> & Hf1 & Hf2 & HAR2 & HP & Hsame & Hres & Heff & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists fx', regs2, mem2, md2.
split; [unfold raZ; rewrite Hra; reflexivity|].
split; [exact Hf1|]. split; [exact Hf2|].
split.
{ eapply (ajournal_after_write SEGS B LAWS Hsegs STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdc k mem2 md2
    (fun a => (d <= a < d + 32) \/ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) Sc own HJ).
  - intros a Ha Hna. apply (Hfr a Ha); intros H'; apply Hna; [left; pose proof (dsn_len_out s); lia | right; exact H'].
  - exact Hpres2.
  - exact Hsame.
  - intros a [Ha | Ha]; left; [exact (Hwr a Ha) | left; lia].
  - exact HAR2.
  - reflexivity.
  - reflexivity.
  - lia.
  - exact Hfrs.
  - exact HQT. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Heff|]. split; [exact Hfr | exact Hpres2].
Qed.
(* The placement segment's walk, from 0x81bcc to the return (decl_place_of_snp below). Symbolic state at 0x81bcc
   (offset 0x1c20): atoms 0..31 are the ENTRY registers (so the return's callee-saved registers are atoms), atom 32
   is the shadow offset SBD, atom 33 the base b, atoms 34..49 the registers CLOB of the machine at 0x81bcc. The frame
   region holds the ten saved registers of DECL_SAVES; the region at r + 280 the count n (a literal: the walk runs
   once per n in 0..4); the shadow entry covers the 288-byte registry block. *)
Definition dp_extra (regs2 : bvmap 5 word) (b : Z) : list word := [Z_to_bv 64 SBD; Z_to_bv 64 b] ++ map (getr regs2) CLOB.
Definition dp_E (regs regs2 : bvmap 5 word) (b : Z) : env := Eimg (Ereg regs (dp_extra regs2 b)).
Definition dp_s7e : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 280) (SLit 3)) (SOff 32 0).
Definition dp_sr : list sv :=
[SLit 0; SOff 34 0; SOff 2 (-80); SOff 3 0; SOff 4 0; SOff 35 0; SOff 36 0; SOff 37 0;
 SOff 12 0; SOff 10 280; SOff 38 0; SOff 39 0; SOff 40 0; SOff 41 0; SOff 42 0; SOff 43 0;
 SOff 44 0; SOff 45 0; SOff 13 0; SOff 11 0; SLit (-1); SOff 10 0; SOff 33 0; dp_s7e; SOff 32 0;
 SOff 25 0; SOff 26 0; SOff 27 0; SOff 46 0; SOff 47 0; SOff 48 0; SOff 49 0].
Definition dp_frame : YP09.region := YP09.mkRegion (Some 2%nat) (-80) 0 (-80) 0
[YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0));
 YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0));
 YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0));
 YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
 YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].
Definition dp_nword (n : Z) : YP09.region :=
YP09.mkRegion (Some 10%nat) 280 284 280 284 [YP09.mkChunk 280 (CVal 4 (SLit n))].
Definition dp_facts : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 140737479966432 4); (32%nat, mkAF SBD SBD 0)] [] [].
Definition dp_ss (n : Z) : sstate := mkSS 7200 dp_sr [dp_frame; dp_nword n] None dp_facts.
Definition dp_SH : list shent := [mkSHE 10 0 288].
(* The row's base / nch / established / pinned words, added after __asan_memset (established is its zero). *)
Definition dp_row (n : Z) : YP09.region :=
YP09.mkRegion (Some 10%nat) (56 * n + 8) (56 * n + 24) (56 * n + 8) (56 * n + 24) [YP09.mkChunk (56 * n + 16) (CVal 4 (SLit 0))].
Lemma dp_s7 : forall E r, ew E 10 = Z_to_bv 64 r -> ew E 32 = Z_to_bv 64 SBD -> 0 <= r -> r + 288 <= 2 ^ 47 ->
sv_denot E dp_s7e = w64 (SBD + (r + 280) / 8).
Proof.
intros E r H10 H32 Hr0 Hr1. rewrite denot_lit_U. unfold w64. f_equal. unfold dp_s7e.
rewrite !U_SAlu. cbn [zalu_raw].
rewrite (U_atom_off E 10 r 280 H10) by lia. rewrite (U_atom E 32 SBD H32) by (unfold SBD; lia). rewrite U_SLit.
change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (0 <= (r + 280) / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
rewrite (zcanon_id ((r + 280) / 8)) by (unfold M64; lia).
rewrite zcanon_id by (unfold M64, SBD; lia). lia.
Qed.
Lemma dp_pin : forall E b0, ew E 13 = Z_to_bv 64 b0 -> -2 ^ 31 <= b0 < 2 ^ 31 ->
sv_denot E (SAlu ALU_XOR (SAlu ALU_SLT (SOff 13 0) (SLit 0)) (SLit 1)) = Z_to_bv 64 (if b0 <? 0 then 0 else 1).
Proof.
intros E b0 H13 Hb. rewrite denot_lit_U. f_equal. rewrite !U_SAlu. cbn [zalu_raw].
rewrite U_SOff, H13, Z.add_0_r, !U_SLit.
assert (X : bv_swrap 64 (zcanon (bv_unsigned (Z_to_bv 64 b0))) = b0).
{ rewrite Z_to_bv_unsigned. unfold zcanon, M64, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N].
  change (2 ^ 64) with 18446744073709551616. change (18446744073709551616 / 2) with 9223372036854775808.
  Z.div_mod_to_equations. lia. }
rewrite X. change (bv_swrap 64 (zcanon 0)) with 0.
destruct (b0 <? 0); reflexivity.
Qed.
Lemma dp_not_ltu : forall E r c, ew E 10 = Z_to_bv 64 r -> 0 <= r -> r + 288 <= 2 ^ 47 -> 0 <= c <= 2 ^ 32 ->
branch_taken BC_LTU (sv_denot E (SAlu ALU_XOR (SOff 10 0) (SLit (-1)))) (sv_denot E (SLit c)) = false.
Proof.
intros E r c H10 Hr0 Hr1 Hc. rewrite branch_ltu_U, (U_not E 10 r H10) by lia. rewrite U_lit by lia.
apply Z.ltb_ge. lia.
Qed.
Lemma dp_regs_ok : forall (regs regs2 : bvmap 5 word) W mem2 r k nm b0 b,
getr regs 10 = w64 r -> getr regs 11 = w64 k -> getr regs 12 = w64 nm -> getr regs 13 = w64 b0 ->
0 <= r -> r + 288 <= 2 ^ 47 ->
dplace_at regs regs2 W mem2 r k nm b0 b ->
regs_ok (dp_E regs regs2 b) dp_sr regs2.
Proof.
intros regs regs2 W mem2 r k nm b0 b H10 H11 H12 H13 Hr0 Hr1 HAT.
destruct HAT as (Asp & A3 & A4 & A25 & A26 & A27 & A8 & A9 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & _).
set (E := dp_E regs regs2 b).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (dp_extra regs2 b)) n)
  by (intros n Hn; unfold E, dp_E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 r) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 k) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 nm) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = Z_to_bv 64 b0) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13).
assert (E25 : ew E 25 = getr regs 25) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 25 25%bv eq_refl)).
assert (E26 : ew E 26 = getr regs 26) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 26 26%bv eq_refl)).
assert (E27 : ew E 27 = getr regs 27) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 27 27%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SBD) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 b) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = getr regs2 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = getr regs2 5) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = getr regs2 6) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = getr regs2 7) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (E38 : ew E 38 = getr regs2 10) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 6)).
assert (E39 : ew E 39 = getr regs2 11) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 7)).
assert (E40 : ew E 40 = getr regs2 12) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 8)).
assert (E41 : ew E 41 = getr regs2 13) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 9)).
assert (E42 : ew E 42 = getr regs2 14) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 10)).
assert (E43 : ew E 43 = getr regs2 15) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 11)).
assert (E44 : ew E 44 = getr regs2 16) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 12)).
assert (E45 : ew E 45 = getr regs2 17) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 13)).
assert (E46 : ew E 46 = getr regs2 28) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 14)).
assert (E47 : ew E 47 = getr regs2 29) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 15)).
assert (E48 : ew E 48 = getr regs2 30) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 16)).
assert (E49 : ew E 49 = getr regs2 31) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 17)).
apply regs_ok_by_cases. intros rr Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr];
[ match goal with |- _ = sv_denot ?E (sr_get ?sr ?r) =>
    let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
  first
  [ rewrite getr_zero; reflexivity
  | exact (eq_trans A23 (eq_sym (dp_s7 E r E10 E32 Hr0 Hr1)))
  | cbn [sv_denot]; exact A20
  | cbn [sv_denot];
    rewrite ?E2, ?E3, ?E4, ?E10, ?E11, ?E12, ?E13, ?E25, ?E26, ?E27, ?E32, ?E33, ?E34, ?E35, ?E36, ?E37, ?E38, ?E39,
      ?E40, ?E41, ?E42, ?E43, ?E44, ?E45, ?E46, ?E47, ?E48, ?E49;
    first
    [ rewrite Z.add_0_r, Z_to_bv_bv_unsigned; first [reflexivity | assumption]
    | rewrite Boxreg.addi_lit; exact A9
    | apply bv_eq; rewrite Z_to_bv_unsigned; unfold spZ in Asp;
      pose proof (bv_unsigned_in_range 64 (getr regs2 2)) as Hu; rewrite Asp in Hu |- *;
      unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64) in *; rewrite Z.mod_small; lia ] ]
| ]).
destruct Hr.
Qed.
Lemma dp_byte_val : forall v i, 0 <= v < 2 ^ 64 -> 0 <= i ->
bv_unsigned (byte_of_word (Z_to_bv 64 v) i) = (v / 2 ^ (8 * i)) mod 256.
Proof.
intros v i Hv Hi. unfold byte_of_word. rewrite Z_to_bv_unsigned, unsigned_lit_small by lia.
rewrite Z.shiftr_div_pow2 by lia. unfold bv_wrap, bv_modulus. cbn [Z.of_N]. reflexivity.
Qed.
Lemma dp_chunk_of_view : forall E H (m : word -> option byte) base off (w : N) e,
(forall i, 0 <= i < Z.of_N w -> aview SEGS H m (base + off + i) = Some (bv_unsigned (byte_of_word (sv_denot E e) i))) ->
YP09.chunk_ok SEGS E (mrestrict H m) base (YP09.mkChunk off (CVal w e)).
Proof.
intros E H m base off w e Hv i Hi. cbn [YP09.c_off YP09.c_val YP09.c_len cv_len] in Hi |- *.
exists (byte_of_word (sv_denot E e) i). split; [reflexivity|].
specialize (Hv i Hi). unfold aview in Hv.
destruct (mbyte SEGS (mrestrict H m) (base + off + i)) as [bb|]; [|discriminate].
injection Hv as Hv. f_equal. apply bv_eq. exact Hv.
Qed.
Lemma dp_nword_bytes : forall (bs : list byte) n, length bs = 288%nat -> Boxreg.bx_n bs = n -> 0 <= n <= 4 ->
forall i, 0 <= i < 4 -> bv_unsigned (nth (Z.to_nat (280 + i)) bs (Z_to_bv 8 0)) = (n / 2 ^ (8 * i)) mod 256.
Proof.
intros bs n HL Hn Hn4 i Hi.
assert (Hsk : forall j, nth (280 + j) bs (Z_to_bv 8 0) = nth j (skipn 280 bs) (Z_to_bv 8 0)).
{ intros j. rewrite <- (firstn_skipn 280 bs) at 1. rewrite app_nth2; rewrite length_firstn, HL; [f_equal; lia | lia]. }
replace (Z.to_nat (280 + i)) with (280 + Z.to_nat i)%nat by lia. rewrite Hsk.
unfold Boxreg.bx_n, Boxreg.rd4, Boxreg.bsub in Hn.
change (Z.to_nat 280) with 280%nat in Hn. change (Z.to_nat 4) with 4%nat in Hn.
pose proof (length_skipn 280 bs) as Hl8. rewrite HL in Hl8. change (288 - 280)%nat with 8%nat in Hl8.
destruct (skipn 280 bs) as [|x0 [|x1 [|x2 [|x3 l']]]]; cbn [length] in Hl8; try lia.
cbn [firstn] in Hn.
rewrite OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib.Bytes.bytes_le_to_Z_le_val in Hn.
cbn [map OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib.Bytes.le_val] in Hn.
pose proof (bv_unsigned_in_range 8 x0) as R0. pose proof (bv_unsigned_in_range 8 x1) as R1.
pose proof (bv_unsigned_in_range 8 x2) as R2. pose proof (bv_unsigned_in_range 8 x3) as R3.
change (bv_modulus 8) with 256 in R0, R1, R2, R3.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in Hn. cbn [Z.of_N] in Hn.
change (2 ^ 32) with 4294967296 in Hn. change (4294967296 / 2) with 2147483648 in Hn.
assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3) as [-> | [-> | [-> | ->]]] by lia.
all: lazymatch goal with |- context [Z.to_nat ?z] => let v := eval vm_compute in (Z.to_nat z) in change (Z.to_nat z) with v end.
all: cbn [nth].
all: lazymatch goal with |- context [2 ^ (8 * ?z)] => let v := eval vm_compute in (2 ^ (8 * z)) in change (2 ^ (8 * z)) with v end.
all: Z.div_mod_to_equations; lia.
Qed.
Lemma dp_entry : forall ly S W (regs : bvmap 5 word) mem md ch (r k nm b0 : Z) (bs : list byte)
  (regs2 : bvmap 5 word) mem2 md2 (b n : Z),
afn_pre SEGS B REAC_BOXREG_DECLARE_STKB ly S W regs mem md ch ->
getr regs 10 = w64 r -> getr regs 11 = w64 k -> getr regs 12 = w64 nm -> getr regs 13 = w64 b0 ->
In (r, REG_SIZEB) (ablocks B ly S) ->
ajournal SEGS B REAC_BOXREG_DECLARE_STKB (spZ regs) [(r, r + REG_SIZEB)] ly S W mem md [] ly S W mem2 md2 0 ->
tbdecl_reg_bytes W mem2 r bs -> length bs = 288%nat -> Boxreg.bx_n bs = n -> 0 <= n <= 4 ->
dplace_at regs regs2 W mem2 r k nm b0 b ->
st_ok_pi SEGS VAL (dp_E regs regs2 b) (dp_ss n)
  (restrict (w_H W) (mkst regs2 (Z_to_bv 64 (BASE + 7200)) mem2 (seg_rom SEGS)))
/\ sh_ok SEGS CBR dp_SH (dp_E regs regs2 b) (mrestrict (w_H W) mem2).
Proof.
intros ly S W regs mem md ch r k nm b0 bs regs2 mem2 md2 b n HPRE H10 H11 H12 H13 Hin HJ HB HL Hn Hn4 HAT.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOXREG_DECLARE_STKB = 8272) by reflexivity.
pose proof HJ as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
destruct (al_blocks _ _ LAWS ly S W mem2 md2 r REG_SIZEB HAR2 Hin) as (Hr16 & Hr4096 & Hrceil & Hria & Hbp & _).
change (req_size REG_SIZEB) with 288 in *.
assert (Hrsp : r + 288 <= spZ regs - 8272) by lia.
pose proof HAT as (Asp & A3 & A4 & A25 & A26 & A27 & A8 & A9 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & Asv).
rewrite restrict_mkst_fx.
set (E := dp_E regs regs2 b).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (dp_extra regs2 b)) n)
  by (intros n0 Hn0; unfold E, dp_E; apply Eimg_low; exact Hn0).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 r) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SBD) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (EF : forall i, (i < 32)%nat -> ew E i = getr regs (Z_to_bv 5 (Z.of_nat i)))
  by (intros i Hi; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_lt; exact Hi).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (Ur : bv_unsigned (ew E 10) = r) by (rewrite E10; apply unsigned_lit_small; lia).
assert (FCH : forall i o, In (i, o) DECL_SAVES ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W) mem2) (spZ regs) (YP09.mkChunk (o - 80) (CVal 8 (SOff i 0)))).
{ intros i o Hio.
  assert (Hi : (i < 32)%nat).
  { pose proof Hio as Hio'. cbv [DECL_SAVES In] in Hio'.
    repeat (destruct Hio' as [Hio' | Hio']; [injection Hio' as <- <-; lia |]). destruct Hio'. }
  apply (chunk_ok_val SEGS E _ (spZ regs) (o - 80) 8 (SOff i 0) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat i))))).
  - cbn [sv_denot]. rewrite (EF i Hi), Z.add_0_r. reflexivity.
  - pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 (Z.of_nat i)))) as Hu.
    change (bv_modulus 64) with (2 ^ 64) in Hu. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  - cbn. lia.
  - replace (spZ regs + (o - 80)) with (spZ regs - 80 + o) by lia. exact (Asv i o Hio). }
split.
- unfold dp_ss. apply pa_entry_st_ok_full.
  + exact (dp_regs_ok regs regs2 W mem2 r k nm b0 b H10 H11 H12 H13 ltac:(lia) ltac:(lia) HAT).
  + vm_compute. reflexivity.
  + unfold dp_frame, dp_nword.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite Usp. split; [lia|]. split; [lia|]. split.
      { intros o Ho. apply (apresent_writable SEGS). apply HJpres. lia. }
      repeat apply Forall_cons; try apply Forall_nil.
      -- exact (FCH 24%nat 0 ltac:(cbv; tauto)).
      -- exact (FCH 23%nat 8 ltac:(cbv; tauto)).
      -- exact (FCH 22%nat 16 ltac:(cbv; tauto)).
      -- exact (FCH 21%nat 24 ltac:(cbv; tauto)).
      -- exact (FCH 20%nat 32 ltac:(cbv; tauto)).
      -- exact (FCH 19%nat 40 ltac:(cbv; tauto)).
      -- exact (FCH 18%nat 48 ltac:(cbv; tauto)).
      -- exact (FCH 9%nat 56 ltac:(cbv; tauto)).
      -- exact (FCH 8%nat 64 ltac:(cbv; tauto)).
      -- exact (FCH 1%nat 72 ltac:(cbv; tauto)).
    * rewrite Ur. split; [lia|]. split; [lia|]. split.
      { intros o Ho. apply (apresent_writable SEGS). apply (proj1 (Hbp (r + o) ltac:(lia))). }
      apply Forall_cons; [|apply Forall_nil].
      apply dp_chunk_of_view. intros i Hi. change (Z.of_N 4) with 4 in Hi.
      cbn [sv_denot]. rewrite dp_byte_val by lia.
      replace (r + 280 + i) with (r + (280 + i)) by lia. rewrite (HB (280 + i)) by (unfold REG_SIZEB; lia).
      f_equal. exact (dp_nword_bytes bs n HL Hn Hn4 i Hi).
  + apply pairwise_disjoint_of_extents.
    unfold dp_frame, dp_nword, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, Ur.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hrsp Hr4096. clear. intros. repeat split; lia.
  + split; [|split; exact I].
    cbn [dp_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, Ur, E32, !unsigned_lit_small by (unfold SBD; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 Hal16 Hr16 Hr4096 Hrceil.
    clear. unfold SBD. intros. repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, dp_SH. apply Forall_cons; [|apply Forall_nil].
  apply (rbi_shent B LAWS ly S W mem2 md2 E r r REG_SIZEB 0 288 10 HAR2 Hin).
  + unfold CBR. rewrite (U_atom E 32 SBD E32) by (unfold SBD; lia). reflexivity.
  + apply (U_atom E 10 r E10). lia.
  + lia. + lia. + change (req_size REG_SIZEB) with 288. lia.
Qed.
(* Pau's byte lists, byte by byte. *)
Lemma dp_upd_lo : forall (cs bs : list byte) (k i : nat) d, (k + length bs <= length cs)%nat -> (i < k)%nat ->
nth i (OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib.Mem.upd_bytes cs k bs) d = nth i cs d.
Proof.
intros cs bs k i d Hk Hi. unfold OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib.Mem.upd_bytes.
rewrite app_nth1 by (rewrite length_firstn; lia).
rewrite <- (firstn_skipn k cs) at 2. rewrite app_nth1 by (rewrite length_firstn; lia). reflexivity.
Qed.
Lemma dp_upd_in : forall (cs bs : list byte) (k i : nat) d, (k + length bs <= length cs)%nat -> (k <= i < k + length bs)%nat ->
nth i (OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib.Mem.upd_bytes cs k bs) d = nth (i - k) bs d.
Proof.
intros cs bs k i d Hk Hi. unfold OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib.Mem.upd_bytes.
rewrite app_nth2 by (rewrite length_firstn; lia). rewrite length_firstn.
replace (Nat.min k (length cs)) with k by lia. rewrite app_nth1 by lia. reflexivity.
Qed.
Lemma dp_upd_hi : forall (cs bs : list byte) (k i : nat) d, (k + length bs <= length cs)%nat -> (k + length bs <= i)%nat ->
nth i (OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib.Mem.upd_bytes cs k bs) d = nth i cs d.
Proof.
intros cs bs k i d Hk Hi. unfold OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib.Mem.upd_bytes.
rewrite app_nth2 by (rewrite length_firstn; lia). rewrite length_firstn.
replace (Nat.min k (length cs)) with k by lia. rewrite app_nth2 by lia.
rewrite <- (firstn_skipn (k + length bs) cs) at 2. rewrite app_nth2 by (rewrite length_firstn; lia).
rewrite length_firstn. replace (Nat.min (k + length bs) (length cs)) with (k + length bs)%nat by lia.
f_equal. lia.
Qed.
Lemma dp_le4_nth : forall (w : word) j, 0 <= j < 4 ->
nth (Z.to_nat j) (OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib.Mem.le4 w) (Z_to_bv 8 0) = byte_of_word w j.
Proof.
intros w j Hj. unfold OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib.Mem.le4, byte_of_word.
assert (j = 0 \/ j = 1 \/ j = 2 \/ j = 3) as [-> | [-> | [-> | ->]]] by lia;
cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add Z_to_le_bytes nth];
rewrite ?Z.shiftr_shiftr by lia; reflexivity.
Qed.
Lemma dp_le4_length : forall w : word, length (OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib.Mem.le4 w) = 4%nat.
Proof. exact OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib.Mem.length_le4. Qed.
Lemma dp_name_length : forall s, length (reac_boxreg_declare_c.name_field s) = 32%nat.
Proof.
intros s. unfold reac_boxreg_declare_c.name_field, printf_facts_c.pf_bytes.
rewrite length_app, length_map, length_firstn, repeat_length. lia.
Qed.
Lemma dp_row_length : forall b k p s, length (reac_boxreg_declare_c.decl_row b k p s) = 56%nat.
Proof.
intros b k p s. unfold reac_boxreg_declare_c.decl_row.
rewrite !length_app, repeat_length, !dp_le4_length, dp_name_length. reflexivity.
Qed.
Lemma dp_name_nth : forall s j, Forall (fun c => 0 < c < 256) s -> 0 <= j < 32 ->
bv_unsigned (nth (Z.to_nat j) (reac_boxreg_declare_c.name_field s) (Z_to_bv 8 0)) = nth (Z.to_nat j) (absn_out 32 s) 0.
Proof.
intros s j HF Hj. unfold reac_boxreg_declare_c.name_field, absn_out, printf_facts_c.pf_bytes.
change (Z.to_nat (32 - 1)) with 31%nat.
pose proof (length_firstn 31 s) as Hm.
destruct (Nat.ltb_spec (Z.to_nat j) (length (firstn 31 s))) as [Hlt | Hge].
- rewrite app_nth1 by (rewrite length_map; lia). rewrite app_nth1 by lia.
  rewrite map_nth. rewrite Z_to_bv_unsigned.
  assert (Hin : In (nth (Z.to_nat j) (firstn 31 s) 0) (firstn 31 s)) by (apply nth_In; exact Hlt).
  rewrite <- (firstn_skipn 31 s) in HF. apply Forall_app in HF as [HF _].
  rewrite Forall_forall in HF. specialize (HF _ Hin).
  unfold bv_wrap, bv_modulus. cbn [Z.of_N]. apply Z.mod_small. change (2 ^ 8) with 256. lia.
- rewrite app_nth2 by (rewrite length_map; lia). rewrite nth_repeat. rewrite app_nth2 by lia.
  destruct (Z.to_nat j - length (firstn 31 s))%nat as [|q]; [reflexivity | destruct q; reflexivity].
Qed.
Lemma dp_row_lo : forall b k p s j, 0 <= j < 8 ->
nth (Z.to_nat j) (reac_boxreg_declare_c.decl_row b k p s) (Z_to_bv 8 0) = Z_to_bv 8 0.
Proof.
intros b k p s j Hj. unfold reac_boxreg_declare_c.decl_row.
rewrite app_nth1 by (rewrite repeat_length; lia). apply nth_repeat.
Qed.
Lemma dp_row_word : forall b k p s o v j, (o = 8 /\ v = b \/ o = 12 /\ v = k \/ o = 16 /\ v = 0 \/ o = 20 /\ v = p) ->
0 <= j < 4 ->
nth (Z.to_nat (o + j)) (reac_boxreg_declare_c.decl_row b k p s) (Z_to_bv 8 0) = byte_of_word (Z_to_bv 64 v) j.
Proof.
intros b k p s o v j Ho Hj. unfold reac_boxreg_declare_c.decl_row.
rewrite app_nth2 by (rewrite repeat_length; destruct Ho as [[-> _] | [[-> _] | [[-> _] | [-> _]]]]; lia).
rewrite repeat_length.
destruct Ho as [[-> ->] | [[-> ->] | [[-> ->] | [-> ->]]]].
- rewrite app_nth1 by (rewrite dp_le4_length; lia).
  replace (Z.to_nat (8 + j) - 8)%nat with (Z.to_nat j) by lia. apply dp_le4_nth; exact Hj.
- rewrite app_nth2 by (rewrite dp_le4_length; lia). rewrite dp_le4_length.
  rewrite app_nth1 by (rewrite dp_le4_length; lia).
  replace (Z.to_nat (12 + j) - 8 - 4)%nat with (Z.to_nat j) by lia. apply dp_le4_nth; exact Hj.
- rewrite app_nth2 by (rewrite dp_le4_length; lia). rewrite dp_le4_length.
  rewrite app_nth2 by (rewrite dp_le4_length; lia). rewrite dp_le4_length.
  rewrite app_nth1 by (rewrite dp_le4_length; lia).
  replace (Z.to_nat (16 + j) - 8 - 4 - 4)%nat with (Z.to_nat j) by lia. apply dp_le4_nth; exact Hj.
- rewrite app_nth2 by (rewrite dp_le4_length; lia). rewrite dp_le4_length.
  rewrite app_nth2 by (rewrite dp_le4_length; lia). rewrite dp_le4_length.
  rewrite app_nth2 by (rewrite dp_le4_length; lia). rewrite dp_le4_length.
  rewrite app_nth1 by (rewrite dp_le4_length; lia).
  replace (Z.to_nat (20 + j) - 8 - 4 - 4 - 4)%nat with (Z.to_nat j) by lia. apply dp_le4_nth; exact Hj.
Qed.
Lemma dp_row_name : forall b k p s j, 0 <= j < 32 ->
nth (Z.to_nat (24 + j)) (reac_boxreg_declare_c.decl_row b k p s) (Z_to_bv 8 0) =
nth (Z.to_nat j) (reac_boxreg_declare_c.name_field s) (Z_to_bv 8 0).
Proof.
intros b k p s j Hj. unfold reac_boxreg_declare_c.decl_row.
rewrite app_nth2 by (rewrite repeat_length; lia). rewrite repeat_length.
do 4 (rewrite app_nth2 by (rewrite dp_le4_length; lia); rewrite dp_le4_length).
f_equal. lia.
Qed.
(* The registry block's bytes after the segment: Pau's new_row_bytes of the declared row. *)
Lemma dp_final : forall (W : world SEGS) (mem2 memT mem3 memF : word -> option byte) (r n b k p : Z) (bs : list byte)
  (s : list Z),
length bs = 288%nat -> Boxreg.bx_n bs = n -> 0 <= n <= 4 -> Forall (fun c => 0 < c < 256) s ->
tbdecl_reg_bytes W mem2 r bs ->
(forall i, 0 <= i < 288 -> ~ (56 * n <= i < 56 * n + 56) -> ~ (280 <= i < 284) ->
  aview SEGS (w_H W) memT (r + i) = aview SEGS (w_H W) mem2 (r + i)) ->
(forall i, 0 <= i < 56 -> aview SEGS (w_H W) mem3 (r + 56 * n + i) = Some (0 mod 256)) ->
(forall i, 0 <= i < 288 -> ~ (56 * n <= i < 56 * n + 56) ->
  aview SEGS (w_H W) mem3 (r + i) = aview SEGS (w_H W) memT (r + i)) ->
(forall i, 0 <= i < 288 -> ~ (56 * n + 8 <= i < 56 * n + 56) -> ~ (280 <= i < 284) ->
  aview SEGS (w_H W) memF (r + i) = aview SEGS (w_H W) mem3 (r + i)) ->
(forall o v j, (o = 8 /\ v = b \/ o = 12 /\ v = k \/ o = 16 /\ v = 0 \/ o = 20 /\ v = p) -> 0 <= j < 4 ->
  aview SEGS (w_H W) memF (r + 56 * n + o + j) = Some (bv_unsigned (byte_of_word (Z_to_bv 64 v) j))) ->
(forall j, 0 <= j < 32 -> aview SEGS (w_H W) memF (r + 56 * n + 24 + j) = Some (nth (Z.to_nat j) (absn_out 32 s) 0)) ->
(forall j, 0 <= j < 4 -> aview SEGS (w_H W) memF (r + 280 + j) = Some (bv_unsigned (byte_of_word (Z_to_bv 64 (n + 1)) j))) ->
tbdecl_reg_bytes W memF r (BoxregUpd.new_row_bytes bs (reac_boxreg_declare_c.decl_row b k p s)).
Proof.
intros W mem2 memT mem3 memF r n b k p bs s HL Hn Hn4 HF HB KA Heff Hfr KB Hrow Hnm Hnw i Hi.
unfold REG_SIZEB in Hi. unfold BoxregUpd.new_row_bytes. rewrite Hn.
assert (HRL : length (reac_boxreg_declare_c.decl_row b k p s) = 56%nat) by apply dp_row_length.
assert (HL1 : length (OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib.Mem.upd_bytes bs (Z.to_nat (56 * n))
  (reac_boxreg_declare_c.decl_row b k p s)) = 288%nat)
  by (rewrite OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib.Mem.upd_bytes_length; [exact HL | lia]).
destruct (Z_lt_le_dec i 280) as [Hi280 | Hi280].
- rewrite dp_upd_lo by (rewrite ?dp_le4_length, ?HL1; lia).
  destruct (Z_lt_le_dec i (56 * n)) as [Hlo | Hlo].
  + rewrite dp_upd_lo by (rewrite ?HRL, ?HL; lia).
    rewrite KB, Hfr, KA by lia. exact (HB i ltac:(unfold REG_SIZEB; lia)).
  + destruct (Z_lt_le_dec i (56 * n + 56)) as [Hrw | Hrw].
    * rewrite dp_upd_in by (rewrite ?HRL, ?HL; lia).
      replace (Z.to_nat i - Z.to_nat (56 * n))%nat with (Z.to_nat (i - 56 * n)) by lia.
      destruct (Z_lt_le_dec (i - 56 * n) 8) as [H8 | H8].
      { rewrite dp_row_lo by lia. rewrite KB by lia.
        replace (r + i) with (r + 56 * n + (i - 56 * n)) by lia. rewrite Heff by lia. reflexivity. }
      destruct (Z_lt_le_dec (i - 56 * n) 24) as [H24 | H24].
      { assert (Hc : exists o v, (o = 8 /\ v = b \/ o = 12 /\ v = k \/ o = 16 /\ v = 0 \/ o = 20 /\ v = p) /\
                       o <= i - 56 * n < o + 4).
        { destruct (Z_lt_le_dec (i - 56 * n) 12); [exists 8, b; split; [left; auto | lia]|].
          destruct (Z_lt_le_dec (i - 56 * n) 16); [exists 12, k; split; [right; left; auto | lia]|].
          destruct (Z_lt_le_dec (i - 56 * n) 20); [exists 16, 0; split; [right; right; left; auto | lia]|].
          exists 20, p; split; [right; right; right; auto | lia]. }
        destruct Hc as (o & v & Hov & Hor).
        replace (i - 56 * n) with (o + (i - 56 * n - o)) by lia.
        rewrite (dp_row_word b k p s o v (i - 56 * n - o) Hov) by lia.
        replace (r + i) with (r + 56 * n + o + (i - 56 * n - o)) by lia. apply Hrow; [exact Hov | lia]. }
      replace (i - 56 * n) with (24 + (i - 56 * n - 24)) by lia.
      rewrite dp_row_name by lia. rewrite dp_name_nth by (first [exact HF | lia]).
      replace (r + i) with (r + 56 * n + 24 + (i - 56 * n - 24)) by lia. apply Hnm. lia.
    * rewrite dp_upd_hi by (rewrite ?HRL, ?HL; lia).
      rewrite KB, Hfr, KA by lia. exact (HB i ltac:(unfold REG_SIZEB; lia)).
- destruct (Z_lt_le_dec i 284) as [Hi284 | Hi284].
  + rewrite dp_upd_in by (rewrite ?dp_le4_length, ?HL1; lia).
    replace (Z.to_nat i - 280)%nat with (Z.to_nat (i - 280)) by lia.
    rewrite dp_le4_nth by lia. replace (r + i) with (r + 280 + (i - 280)) by lia. apply Hnw. lia.
  + rewrite dp_upd_hi by (rewrite ?dp_le4_length, ?HL1; lia).
    rewrite dp_upd_hi by (rewrite ?HRL, ?HL; lia).
    rewrite KB, Hfr, KA by lia. exact (HB i ltac:(unfold REG_SIZEB; lia)).
Qed.
(* The final region of the row and of the count, byte by byte. *)
Lemma dp_rowfacts : forall Ex (H : word -> bool) memF c n r b k b0, n = c ->
region_ok SEGS Ex (mrestrict H memF) (YP09.mkRegion (Some 10%nat) (56 * c + 8) (56 * c + 24) (56 * c + 8) (56 * c + 24)
  [YP09.mkChunk (56 * c + 20) (CVal 4 (SAlu ALU_XOR (SAlu ALU_SLT (SOff 13 0) (SLit 0)) (SLit 1)));
   YP09.mkChunk (56 * c + 12) (CVal 4 (SOff 11 0)); YP09.mkChunk (56 * c + 8) (CVal 4 (SOff 33 0));
   YP09.mkChunk (56 * c + 16) (CVal 4 (SLit 0))]) ->
bv_unsigned (ew Ex 10) = r -> ew Ex 11 = Z_to_bv 64 k -> ew Ex 13 = Z_to_bv 64 b0 -> ew Ex 33 = Z_to_bv 64 b ->
-2 ^ 31 <= b0 < 2 ^ 31 ->
forall o v j, (o = 8 /\ v = b \/ o = 12 /\ v = k \/ o = 16 /\ v = 0 \/ o = 20 /\ v = (if b0 <? 0 then 0 else 1)) ->
0 <= j < 4 -> aview SEGS H memF (r + 56 * n + o + j) = Some (bv_unsigned (byte_of_word (Z_to_bv 64 v) j)).
Proof.
intros Ex H memF c n r b k b0 -> HR Hr H11 H13 H33 Hb0 o v j Ho Hj. unfold aview.
destruct Ho as [[-> ->] | [[-> ->] | [[-> ->] | [-> ->]]]].
- replace (r + 56 * c + 8 + j) with (r + (56 * c + 8) + j) by lia.
  rewrite (rbi_chunk_byte SEGS Ex _ 10 r _ _ _ _ _ (56 * c + 8) 4 (SOff 33 0) j HR Hr)
    by first [right; right; left; reflexivity | cbn; lia].
  cbn [option_map sv_denot]. rewrite H33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- replace (r + 56 * c + 12 + j) with (r + (56 * c + 12) + j) by lia.
  rewrite (rbi_chunk_byte SEGS Ex _ 10 r _ _ _ _ _ (56 * c + 12) 4 (SOff 11 0) j HR Hr)
    by first [right; left; reflexivity | cbn; lia].
  cbn [option_map sv_denot]. rewrite H11, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- replace (r + 56 * c + 16 + j) with (r + (56 * c + 16) + j) by lia.
  rewrite (rbi_chunk_byte SEGS Ex _ 10 r _ _ _ _ _ (56 * c + 16) 4 (SLit 0) j HR Hr)
    by first [right; right; right; left; reflexivity | cbn; lia].
  reflexivity.
- replace (r + 56 * c + 20 + j) with (r + (56 * c + 20) + j) by lia.
  rewrite (rbi_chunk_byte SEGS Ex _ 10 r _ _ _ _ _ (56 * c + 20) 4 _ j HR Hr) by first [left; reflexivity | cbn; lia].
  cbn [option_map]. rewrite (dp_pin Ex b0 H13 Hb0). reflexivity.
Qed.
Lemma dp_nwfacts : forall Ex (H : word -> bool) memF c n r, n = c ->
region_ok SEGS Ex (mrestrict H memF) (YP09.mkRegion (Some 10%nat) 280 284 280 284 [YP09.mkChunk 280 (CVal 4 (SLit (c + 1)))]) ->
bv_unsigned (ew Ex 10) = r ->
forall j, 0 <= j < 4 -> aview SEGS H memF (r + 280 + j) = Some (bv_unsigned (byte_of_word (Z_to_bv 64 (n + 1)) j)).
Proof.
intros Ex H memF c n r -> HR Hr j Hj. unfold aview.
rewrite (rbi_chunk_byte SEGS Ex _ 10 r _ _ _ _ _ 280 4 (SLit (c + 1)) j HR Hr) by first [left; reflexivity | cbn; lia].
reflexivity.
Qed.
(* The read-only view is carried by a journal whose footprint holds no sink token (BoxBase.v arodata_ok_journalP
   without its ro_below_ofl premise). *)
Lemma dp_aro : forall STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k,
~ YI16.sink_open_fp FP ->
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W0) mem0) ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W') mem').
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k Hc HJ HR a Hro Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a); [exact (HR a Hro Ho He) | | exact Ho | exact He | exact (fp_spares_closed FP a Hc)].
destruct Hro as [(sg & Hs & _ & Hr) | Hgot]; [exists sg; split; [exact Hs | exact Hr] | exact (pa_relro_img a Hgot)].
Qed.
Lemma dp_nm_range : forall ly S W mem md r nm s, AR SEGS B ly S W mem md -> tbdecl_name_ok ly S W mem r nm s ->
0 <= nm < 2 ^ 64.
Proof.
intros ly S W mem md r nm s HAR [[-> _] | (_ & _ & _ & nn & Hnn & _)]; [lia|].
destruct (al_blocks _ _ LAWS ly S W mem md nm nn HAR Hnn) as (_ & H4 & Hc & _ & _ & _ & Hm).
pose proof (asan_consts) as (C1 & _). pose proof (req_size_pos nn ltac:(lia)) as [Q1 _]. lia.
Qed.
Lemma dp_agree_ewset : forall k E E' n v, (k <= n)%nat -> env_agree k E E' -> env_agree k E (ewset E' n v).
Proof. intros k E E' n v Hk [A D]. split; [intros i Hi; rewrite ew_ewset_other by lia; apply A; lia | exact D]. Qed.
Lemma dp_out_length : forall s, Z.of_nat (length (absn_out 32 s)) <= 32.
Proof. intros s. unfold absn_out. rewrite length_app, length_firstn. cbn [length]. lia. Qed.
Let dp_RUN := paj_run B LAWS.
Let dp_BR := paj_branch (PI := PI).
Let dp_RET := paj_ret_at (PL := PL_boxb) (PI := PI).
(* The write windows of every run of the segment: the frame, the row's base..pinned words, the count. *)
Definition dp_win (sp0 r n a : Z) : Prop :=
(sp0 - 80 <= a < sp0) \/ (r + 56 * n + 8 <= a < r + 56 * n + 24) \/ (r + 280 <= a < r + 284).
(* Markers the walk's tactics match (a goal pattern cannot name the proof's own variables): the count's case n = c,
   and the arm of beqz s0 (0: name NULL, 1: snprintf called). *)
Definition dp_case (n c : Z) : Prop := n = c.
Definition dp_arm (i : Z) : Prop := True.
Local Ltac dp_awr r Hin Ur Usp :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0 fp b0 bc ly own) end;
  repeat first
  [ apply awr_ok_nil
  | eapply awr_ok_cons_stack; [reflexivity | exact Usp | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |]
  | eapply (awr_ok_cons_block _ _ _ _ _ _ _ _ _ _ 10%nat r REG_SIZEB);
    [ reflexivity | exact Ur | exact Hin | cbn [YP09.r_wlo]; lia
    | change (req_size REG_SIZEB) with 288; cbn [YP09.r_whi]; lia
    | cbn [YP09.r_wlo YP09.r_whi]; intros ?a ?Ha; exists (r, r + REG_SIZEB);
      split; [left; reflexivity | cbn [fst snd]; unfold REG_SIZEB; lia]
    | ] ].
Local Ltac dp_keep Ur Usp :=
  lazymatch goal with
  | KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ dp_win ?sp0 ?r ?n a -> aview ?segs ?H ?m1 a = aview ?segs ?H ?m0 a,
    HFr : frame_of ?Ex ?rs (mrestrict ?H ?m1) (mrestrict ?H ?m2) |- _ =>
    let K2 := fresh "KEEP" in
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ dp_win sp0 r n a -> aview segs H m2 a = aview segs H m0 a);
    [ let a := fresh "a" in let Ha := fresh "Ha" in let HZ := fresh "HZ" in
      intros a Ha HZ; transitivity (aview segs H m1 a); [| exact (KEEP a Ha HZ)];
      apply (kept_of_frame Ex rs H m1 m2 (dp_win sp0 r n) HFr); [| exact Ha | exact HZ];
      let bb := fresh "bb" in let wlo := fresh "wlo" in let whi := fresh "whi" in let aa := fresh "aa" in
      let Hwin := fresh "Hwin" in let Har := fresh "Har" in
      intros bb wlo whi aa Hwin Har; vm_compute in Hwin;
      repeat (destruct Hwin as [Hwin | Hwin];
              [injection Hwin as <- <- <-; cbn [base_val] in Har; rewrite ?Ur, ?Usp in Har; unfold dp_win; lia |]);
      destruct Hwin
    | clear KEEP HFr; rename K2 into KEEP ]
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Lemma decl_place_of_snp : dsnp_spec -> dplace_spec.
Proof.
intros SNP. unfold dplace_spec.
intros ly S W regs mem md ch r k nm b0 bs s G regs2 mem2 md2 b HPRE HRO H10 H11 H12 H13 Hk Hb0 Hin HB0 Hinv Hname
  Htail Hvis Hglob Hfmt HfG Hflo Hfhi Hfgot HFRM HJ HB HAT Hpl.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOXREG_DECLARE_STKB = 8272) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md r REG_SIZEB HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & _ & _).
change (req_size REG_SIZEB) with 288 in Hrceil, Hria.
assert (Hrsp : r + 288 <= spZ regs - 8272) by lia.
assert (HL : length bs = 288%nat) by (destruct Hinv as ((HL & _) & _); exact HL).
assert (Hn4 : 0 <= Boxreg.bx_n bs <= 4)
  by (destruct Hinv as ((_ & HB1 & _) & _); destruct Hpl as (_ & Hn5 & _); unfold Boxreg.boxreg_B1 in HB1; lia).
assert (Hnmr : 0 <= nm < 2 ^ 64) by exact (dp_nm_range ly S W mem md r nm s HAR Hname).
assert (Hfp : ~ YI16.sink_open_fp [(r, r + REG_SIZEB)]) by (apply sink_closed_cons; [cbn; lia | exact sink_closed_nil]).
pose proof (dp_out_length s) as HoutL.
remember (Boxreg.bx_n bs) as n eqn:Hneq.
remember (dp_E regs regs2 b) as E eqn:HE.
assert (HSS : forall c, n = c ->
  st_ok_pi SEGS VAL E (dp_ss c) (restrict (w_H W) (mkst regs2 (Z_to_bv 64 (BASE + 7200)) mem2 (seg_rom SEGS)))
  /\ sh_ok SEGS CBR dp_SH E (mrestrict (w_H W) mem2))
  by (intros c Hc0; subst c E; exact (dp_entry ly S W regs mem md ch r k nm b0 bs regs2 mem2 md2 b n HPRE H10 H11 H12 H13
        Hin HJ HB HL (eq_sym Hneq) Hn4 HAT)).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n0, (n0 < A_TEXT)%nat -> ew E n0 = ew (Ereg regs (dp_extra regs2 b)) n0)
  by (intros n0 Hn0; subst E; apply Eimg_low; exact Hn0).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 r) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 k) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 nm) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = Z_to_bv 64 b0) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13).
assert (E32 : ew E 32 = Z_to_bv 64 SBD) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 b) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (HAE : env_agree 32 (Ereg regs (dp_extra regs2 b)) E)
  by (split; [intros n0 Hn0; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (Ur : bv_unsigned (ew E 10) = r) by (rewrite E10; apply unsigned_lit_small; lia).
clear HE EL.
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ dp_win (spZ regs) r n a ->
  aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem2 a) by reflexivity.
assert (Hcase : n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4) by lia.
destruct Hcase as [Hnc | [Hnc | [Hnc | [Hnc | Hnc]]]];
[ destruct (HSS 0 Hnc) as [HS SHOK]; assert (Hcc : dp_case n 0) by exact Hnc
| destruct (HSS 1 Hnc) as [HS SHOK]; assert (Hcc : dp_case n 1) by exact Hnc
| destruct (HSS 2 Hnc) as [HS SHOK]; assert (Hcc : dp_case n 2) by exact Hnc
| destruct (HSS 3 Hnc) as [HS SHOK]; assert (Hcc : dp_case n 3) by exact Hnc
| destruct (HSS 4 Hnc) as [HS SHOK]; assert (Hcc : dp_case n 4) by exact Hnc ]; clear HSS.
(* From 0x81bcc to the UBSan pointer-overflow test bltu ~r, 56 n (0x81bf0): the shadow check of r + 280, the count n
   (the region's literal; bgeu n, 6 is decided by the engine), 56 n. The test stops the engine unless n = 0; then
   on to the call of __asan_memset (row = r + 56 n, 0, 56) at 0x81c04. *)
all: paj_run_tok dp_RUN HS HJ SHOK BspanR; [dp_awr r Hin Ur Usp |].
all: dp_keep Ur Usp.
all: lazymatch type of HS with
  | st_ok_pi _ _ _ _ _ =>
    psrr_branch_tok dp_RUN dp_BR HS SHOK BspanR;
    [ exfalso; rewrite (dp_not_ltu E r _ E10) in Hc by lia; discriminate
    | clear Hc; paj_run_tok dp_RUN HS HJ SHOK BspanR; [dp_awr r Hin Ur Usp |]; dp_keep Ur Usp ]
  | _ => idtac end.
all: pmkst HS.
all: prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (12%bv : bv 5) Ra2; prreg HS (1%bv : bv 5) Rra;
  prreg HS (2%bv : bv 5) Rsp; prreg HS (3%bv : bv 5) Rgp; prreg HS (4%bv : bv 5) Rtp.
(* __asan_memset: zeros at [row, row + 56), every other byte above its stack kept. *)
all: lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
  assert (Qsp : spZ rg = spZ regs + -80) by (unfold spZ at 1; rewrite Rsp, Usp, unsigned_lit_small by lia; reflexivity);
  eapply SRr_bind;
  [ eapply (aj_intrin_at SEGS B LAWS Hsegs OSet (SIGMA BB___asan_memset) AMEMSET W rg mm
      REAC_BOXREG_DECLARE_STKB (spZ regs) [(r, r + REG_SIZEB)] ly S W mem md [] ly S _ 0 (r + 56 * n) 0 56 (-80) _ HJ);
    [ rewrite Ra0, E10; rewrite ?Boxreg.addi_lit; unfold w64; f_equal; unfold dp_case in Hcc; lia
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
        [ exists (r, r + REG_SIZEB); split; [left; reflexivity | cbn [fst snd]; unfold REG_SIZEB; lia]
        | exists r, REG_SIZEB; split; [exact Hin | change (req_size REG_SIZEB) with 288; lia] ]
      | rewrite Hes; lia ]
    | eapply (amem_range_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hin); change (req_size REG_SIZEB) with 288; lia
    | eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hin);
      change (req_size REG_SIZEB) with 288; lia
    | intros _; eapply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ (proj1 HJ) Hin);
      change (req_size REG_SIZEB) with 288; lia
    | exact I ]
  | ]
end.
all: cbv beta; intros W2 c2 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Ha03 & Heff & Hfr & Hpres3).
all: pose proof HJ3 as (HAR3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres3 & _).
all: destruct (al_blocks _ _ LAWS ly S W mem3 md3 r REG_SIZEB HAR3 Hin) as (_ & _ & _ & _ & Hbp3 & _).
all: change (req_size REG_SIZEB) with 288 in Hbp3.
all: clear Ra0 Ra1 Ra2 Rra Rgp Rtp Rsp Qsp.
(* Back at 0x81c08: the frame and the count are kept. *)
all: jafter_call_keep_hi HS 512%nat regs3 (mrestrict (w_H W) mem3) HP3 [0; 1]%nat HS2.
all: match type of HS2 with ?tq -> _ => assert (HRK : tq);
  [ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil;
    (split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?Usp, ?Ur; intros a Ha;
     [ apply (mbyte_of_aview SEGS); apply Hfr; [lia | lia | rewrite Hes; lia]
     | intros _; apply (apresent_writable SEGS); first [apply HJpres3; lia | apply (proj1 (Hbp3 a ltac:(lia)))] ])
  | specialize (HS2 HRK); clear HRK ] end.
all: clear HS; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS.
all: remember (havoc E 512 (map (getr regs3) CLOB)) as E' eqn:HE' in HS.
all: assert (HEI' : img_env VAL A_LIM E') by (rewrite HE'; apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia]).
all: assert (OLD : forall k0, (k0 < 512)%nat -> ew E' k0 = ew E k0)
  by (intros k0 Hk0; rewrite HE'; apply YN3v.ew_havoc_old; exact Hk0).
all: assert (HAE' : env_agree 32 (Ereg regs (dp_extra regs2 b)) E')
  by (rewrite HE'; apply env_agree_havoc_ge; [lia | exact HAE]).
all: clear HE'.
all: assert (F1 : ew E' 1 = getr regs 1) by (rewrite OLD by lia; exact E1).
all: assert (F3 : ew E' 3 = getr regs 3) by (rewrite OLD by lia; exact E3).
all: assert (F4 : ew E' 4 = getr regs 4) by (rewrite OLD by lia; exact E4).
all: assert (F10 : ew E' 10 = Z_to_bv 64 r) by (rewrite OLD by lia; exact E10).
all: assert (F11 : ew E' 11 = Z_to_bv 64 k) by (rewrite OLD by lia; exact E11).
all: assert (F12 : ew E' 12 = Z_to_bv 64 nm) by (rewrite OLD by lia; exact E12).
all: assert (F13 : ew E' 13 = Z_to_bv 64 b0) by (rewrite OLD by lia; exact E13).
all: assert (F32 : ew E' 32 = Z_to_bv 64 SBD) by (rewrite OLD by lia; exact E32).
all: assert (F33 : ew E' 33 = Z_to_bv 64 b) by (rewrite OLD by lia; exact E33).
all: assert (Usp' : bv_unsigned (ew E' 2) = spZ regs) by (rewrite OLD by lia; exact Usp).
all: assert (Ur' : bv_unsigned (ew E' 10) = r) by (rewrite OLD by lia; exact Ur).
all: clear OLD.
all: lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
all: clear SHOK.
(* The row's base..pinned words as a writable region (established is the wrapper's zero). *)
all: lazymatch goal with Hcc : dp_case _ ?c |- _ =>
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict ?Hh ?msx) =>
  assert (HR : region_ok SEGS E' (ms_mem (restrict Hh msx)) (dp_row c));
  [ cbn [restrict ms_mem mkst]; unfold dp_row, region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
    rewrite Ur'; split; [lia|]; split; [lia|]; split;
    [ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (Hbp3 (r + o) ltac:(lia)))
    | apply Forall_cons; [|apply Forall_nil]; apply dp_chunk_of_view; intros i Hi; change (Z.of_N 4) with 4 in Hi;
      cbn [sv_denot]; rewrite dp_byte_val by lia; rewrite Zdiv_0_l;
      replace (r + (56 * c + 16) + i) with (r + 56 * n + (16 + i)) by lia; rewrite Heff by lia; reflexivity ]
  | pose proof (st_ok_pi_add_region E' ssx (restrict Hh msx) (dp_row c) HS ltac:(vm_compute; reflexivity) HR
      ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
              let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
            cbn [all_disjoint]; unfold extent_disjoint, dp_row;
            cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
            rewrite Ur', Usp'; repeat match goal with |- _ /\ _ => split end; first [exact I | lia])) as HS2;
    clear HS HR; rename HS2 into HS ]
  end end.
all: lazymatch type of HS with st_ok_pi _ _ _ ?ss _ => let v := eval vm_compute in ss in change ss with v in HS end.
all: assert (SHOK : sh_ok SEGS CBR dp_SH E' (mrestrict (w_H W) mem3)) by
  (unfold sh_ok, dp_SH; apply Forall_cons; [|apply Forall_nil];
   apply (rbi_shent B LAWS ly S W mem3 md3 E' r r REG_SIZEB 0 288 10 HAR3 Hin);
   [ unfold CBR; rewrite (U_atom E' 32 SBD F32) by (unfold SBD; lia); reflexivity
   | apply (U_atom E' 10 r F10); lia | lia | lia | change (req_size REG_SIZEB) with 288; lia ]).
all: assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ dp_win (spZ regs) r n a ->
  aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem3 a) by reflexivity.
(* The three shadow-checked stores (base, nch, pinned), up to beqz s0 at 0x81c58. *)
all: paj_run_tok dp_RUN HS HJ3 SHOK BspanR; [dp_awr r Hin Ur' Usp' |].
all: dp_keep Ur' Usp'.
all: psrr_branch_tok dp_RUN dp_BR HS SHOK BspanR.
(* beqz s0: arm 0 (name NULL, s = []) skips snprintf, arm 1 calls it. *)
all: rewrite branch_eq_U, (U_atom E' 12 nm F12 Hnmr), U_lit in Hc by lia.
all: lazymatch goal with
| Hc : (_ =? _) = true |- _ => apply Z.eqb_eq in Hc; assert (Harm : dp_arm 0) by exact I
| Hc : (_ =? _) = false |- _ => apply Z.eqb_neq in Hc; assert (Harm : dp_arm 1) by exact I
end.
(* Arm 0: the reload of n (bltu (n + 1)_32, n is decided), the store of n + 1, the epilogue, up to ret. *)
all: lazymatch goal with Harm : dp_arm 0 |- _ =>
  assert (Hs0 : s = []) by (destruct Hname as [[_ Hs0] | [Hne _]]; [exact Hs0 | contradiction]);
  assert (Hsf : Forall (fun c => 0 < c < 256) s) by (rewrite Hs0; constructor);
  paj_run_tok dp_RUN HS HJ3 SHOK BspanR; [dp_awr r Hin Ur' Usp' |]
| _ => idtac end.
all: lazymatch goal with Harm : dp_arm 0 |- _ => dp_keep Ur' Usp' | _ => idtac end.
all: lazymatch goal with Harm : dp_arm 0, HS : st_ok_pi _ _ _ _ (restrict _ ?msF) |- _ =>
  assert (KB' : forall i, 0 <= i < 288 -> ~ (56 * n + 8 <= i < 56 * n + 56) -> ~ (280 <= i < 284) ->
     aview SEGS (w_H W) (ms_mem msF) (r + i) = aview SEGS (w_H W) mem3 (r + i))
    by (intros i Hi H1 H2; apply KB; [lia | unfold dp_win; lia]);
  assert (Hnm' : forall j, 0 <= j < 32 ->
     aview SEGS (w_H W) (ms_mem msF) (r + 56 * n + 24 + j) = Some (nth (Z.to_nat j) (absn_out 32 s) 0))
    by (intros j Hj; rewrite KB by (first [lia | unfold dp_win; lia]);
        replace (r + 56 * n + 24 + j) with (r + 56 * n + (24 + j)) by lia; rewrite Heff by lia;
        rewrite Hs0; unfold absn_out; destruct (Z.to_nat j) as [|[|q]]; reflexivity);
  (* the path skips the wrapper: it returns at the entry's FP state *)
  assert (Hfr6 : forall j : bv 5, bv_unsigned j <> 10 -> Sem.reg_get (@fp_regs fx) j = Sem.reg_get (@fp_regs fx) j)
    by (intros; reflexivity);
  assert (Hcsr6 : @fp_csr fx = @fp_csr fx \/ Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0)
    by (left; reflexivity)
| _ => idtac end.
(* Arm 1: the arguments (row + 24, 32, "%s", name) and the call of the snprintf trampoline at 0x81c70; the walk
   continues at the FP state fx6 the wrapper returns at (FMsnprintfSx.srr_fx_continue). *)
all: lazymatch goal with Harm : dp_arm 1 |- _ =>
  destruct Hname as [[Hz _] | (Hne & Hsf & Hsl & nn & Hnn & Hnnl & Hap & Hsb)]; [contradiction|];
  paj_run_tok dp_RUN HS HJ3 SHOK BspanR; [dp_awr r Hin Ur' Usp' |]
| _ => idtac end.
all: lazymatch goal with Harm : dp_arm 1 |- _ => dp_keep Ur' Usp' | _ => idtac end.
all: lazymatch goal with Harm : dp_arm 1 |- _ =>
  pmkst HS; prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (12%bv : bv 5) Ra2;
  prreg HS (13%bv : bv 5) Ra3; prreg HS (1%bv : bv 5) Rra; prreg HS (2%bv : bv 5) Rsp;
  prreg HS (3%bv : bv 5) Rgp; prreg HS (4%bv : bv 5) Rtp
| _ => idtac end.
all: lazymatch goal with Harm : dp_arm 1 |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
  assert (Qsp : spZ rg = spZ regs + -80) by (unfold spZ at 1; rewrite Rsp, Usp', unsigned_lit_small by lia; reflexivity);
  eapply (FMsnprintfSx.srr_fx_continue (fx := fx) SEGS);
  [ eapply (SNP W rg mm REAC_BOXREG_DECLARE_STKB (spZ regs) [(r, r + REG_SIZEB)] ly S W mem md [] ly S _ 0 (-80) _
      (r + 56 * n + 24) AB_declare_fmtP nm s r REG_SIZEB nn G HJ3);
    [ rewrite Ra0, F10, Boxreg.addi_lit; unfold w64; f_equal; unfold dp_case in Hcc; lia
    | rewrite Ra1; reflexivity
    | rewrite Ra2, (img_env_atomP E' 251 HEI') by (unfold A_TEXT, A_LIM; lia); reflexivity
    | rewrite Ra3, F12; reflexivity
    | exact Qsp
    | reflexivity
    | lia
    | rewrite WS, Hes; lia
    | rewrite Rgp, F3; exact Hgp
    | rewrite Rtp, F4; exact Htp
    | exact Rra
    | apply ret_ok_codeptr_v; [lia | reflexivity]
    | exact Hin
    | lia
    | unfold REG_SIZEB, dp_case in *; lia
    | intros a Ha; right; left; split;
      [ exists (r, r + REG_SIZEB); split; [left; reflexivity | cbn [fst snd]; unfold REG_SIZEB, dp_case in *; lia]
      | exists r, REG_SIZEB; split; [exact Hin | change (req_size REG_SIZEB) with 288; unfold dp_case in Hcc; lia] ]
    | exact (dp_aro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hfp HJ3 HRO)
    | exact Hvis | exact Hglob | exact Hfmt | exact HfG | exact Hflo | exact Hfhi | exact Hfgot | exact Htail
    | exact Hsf | exact Hsl | exact Hnn | exact Hnnl | exact Hap
    | intros i Hi; pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Fb & _);
      pose proof (req_size_pos nn ltac:(lia)) as [_ Hrq];
      rewrite (Fb nm nn i Hnn Hnn ltac:(lia)); [exact (Hsb i Hi)|];
      intros (rr & Hrr & Har); destruct Hrr as [<- | []]; cbn [fst snd] in Har; unfold REG_SIZEB in *; lia
    | exact HFRM ]
  | ]
| _ => idtac end.
all: lazymatch goal with Harm : dp_arm 1 |- _ =>
  intros fx6 regs6 mem6 md6 Hfr6 Hrm6 HR6; cbv beta in HR6;
  destruct HR6 as (HJ6 & HP6 & Ha06 & Hout & Hkeep6 & Hpres6);
  assert (Hcsr6 : @fp_csr fx6 = @fp_csr fx \/ Z.land (Z.shiftr (bv_unsigned (@fp_csr fx6)) 5) 7 = 0)
    by (right; exact Hrm6); clear Hrm6;
  unfold cfg_at, w64; rewrite Z_to_bv_bv_unsigned;
  pose proof HJ6 as (HAR6 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres6 & _);
  destruct (al_blocks _ _ LAWS ly S W mem6 md6 r REG_SIZEB HAR6 Hin) as (_ & _ & _ & _ & Hbp6 & _);
  change (req_size REG_SIZEB) with 288 in Hbp6;
  clear Ra0 Ra1 Ra2 Ra3 Rra Rgp Rtp Rsp Qsp
| _ => idtac end.
(* Back at 0x81c74, at fx6 (no instruction from 0x81c74 to the return reads or writes an f register or fcsr): the
   row's words, the frame and the count are kept (the call writes the name field and its stack below the frame). *)
all: lazymatch goal with Harm : dp_arm 1 |- _ =>
  pose proof (dsn_st_swap fx6 _ _ _ _ HS eq_refl) as HSx; clear HS; rename HSx into HS;
  jafter_call_keep_hi HS 544%nat regs6 (mrestrict (w_H W) mem6) HP6 [0; 1; 2]%nat HS2;
  match type of HS2 with ?tq -> _ => assert (HRK : tq);
  [ cbn [ms_mem restrict mkst]; repeat apply Forall_cons; try apply Forall_nil;
    (split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?Usp', ?Ur'; intros a Ha;
     [ apply (mbyte_of_aview SEGS); apply Hkeep6; [lia | unfold dp_case in Hcc; lia | rewrite Hes; lia]
     | intros _; apply (apresent_writable SEGS);
       first [apply HJpres6; lia | apply (proj1 (Hbp6 a ltac:(unfold dp_case in Hcc; lia)))] ])
  | specialize (HS2 HRK); clear HRK ] end;
  clear HS; rewrite <- (restrict_mkst_fx (fx := fx6)) in HS2; rename HS2 into HS
| _ => idtac end.
all: lazymatch goal with Harm : dp_arm 1, HS : st_ok_pi _ _ (havoc ?Ey 544 ?wsy) _ _ |- _ =>
  remember (havoc Ey 544 wsy) as E'' eqn:HE'' in HS;
  assert (HEI'' : img_env VAL A_LIM E'') by (rewrite HE''; apply img_env_havoc_hi; [exact HEI' | unfold A_LIM; lia]);
  assert (OLD : forall k0, (k0 < 544)%nat -> ew E'' k0 = ew E' k0)
    by (intros k0 Hk0; rewrite HE''; apply YN3v.ew_havoc_old; exact Hk0);
  assert (HAE'' : env_agree 32 (Ereg regs (dp_extra regs2 b)) E'')
    by (rewrite HE''; apply env_agree_havoc_ge; [lia | exact HAE']);
  clear HE'';
  assert (G1 : ew E'' 1 = getr regs 1) by (rewrite OLD by lia; exact F1);
  assert (G10 : ew E'' 10 = Z_to_bv 64 r) by (rewrite OLD by lia; exact F10);
  assert (G11 : ew E'' 11 = Z_to_bv 64 k) by (rewrite OLD by lia; exact F11);
  assert (G13 : ew E'' 13 = Z_to_bv 64 b0) by (rewrite OLD by lia; exact F13);
  assert (G32 : ew E'' 32 = Z_to_bv 64 SBD) by (rewrite OLD by lia; exact F32);
  assert (G33 : ew E'' 33 = Z_to_bv 64 b) by (rewrite OLD by lia; exact F33);
  assert (Usp'' : bv_unsigned (ew E'' 2) = spZ regs) by (rewrite OLD by lia; exact Usp');
  assert (Ur'' : bv_unsigned (ew E'' 10) = r) by (rewrite OLD by lia; exact Ur');
  clear OLD F1 F3 F4 F10 F11 F12 F13 F32 F33 Usp' Ur' HAE' SHOK;
  rename G1 into F1, G10 into F10, G11 into F11, G13 into F13, G32 into F32, G33 into F33, Usp'' into Usp',
    Ur'' into Ur', HAE'' into HAE';
  lazymatch type of HS with st_ok_pi _ _ _ ?ss5 _ => let v := eval vm_compute in ss5 in change ss5 with v in HS end;
  assert (SHOK : sh_ok SEGS CBR dp_SH E'' (mrestrict (w_H W) mem6)) by
    (unfold sh_ok, dp_SH; apply Forall_cons; [|apply Forall_nil];
     apply (rbi_shent B LAWS ly S W mem6 md6 E'' r r REG_SIZEB 0 288 10 HAR6 Hin);
     [ unfold CBR; rewrite (U_atom E'' 32 SBD F32) by (unfold SBD; lia); reflexivity
     | apply (U_atom E'' 10 r F10); lia | lia | lia | change (req_size REG_SIZEB) with 288; lia ]);
  assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ dp_win (spZ regs) r n a ->
    aview SEGS (w_H W) mem6 a = aview SEGS (w_H W) mem6 a) by reflexivity
| _ => idtac end.
(* The reload of n, the store of n + 1, the epilogue, up to ret (at fx6). *)
all: lazymatch goal with Harm : dp_arm 1 |- _ =>
  paj_run_tok (paj_run (fx := fx6) B LAWS) HS HJ6 SHOK BspanR; [dp_awr r Hin Ur' Usp' |]
| _ => idtac end.
all: lazymatch goal with Harm : dp_arm 1 |- _ => dp_keep Ur' Usp' | _ => idtac end.
all: lazymatch goal with Harm : dp_arm 1, HS : st_ok_pi _ _ _ _ (restrict _ ?msF) |- _ =>
  assert (KB' : forall i, 0 <= i < 288 -> ~ (56 * n + 8 <= i < 56 * n + 56) -> ~ (280 <= i < 284) ->
     aview SEGS (w_H W) (ms_mem msF) (r + i) = aview SEGS (w_H W) mem3 (r + i))
    by (intros i Hi H1 H2; rewrite KC by (first [lia | unfold dp_win; lia]);
        rewrite Hkeep6 by (first [lia | rewrite Hes; lia]); apply KB; [lia | unfold dp_win; lia]);
  assert (Hnm' : forall j, 0 <= j < 32 ->
     aview SEGS (w_H W) (ms_mem msF) (r + 56 * n + 24 + j) = Some (nth (Z.to_nat j) (absn_out 32 s) 0))
    by (intros j Hj; rewrite KC by (first [lia | unfold dp_win; lia]);
        destruct (Z_lt_le_dec j (Z.of_nat (length (absn_out 32 s)))) as [Hjl | Hjl];
        [ apply Hout; lia
        | rewrite Hkeep6 by (first [lia | rewrite Hes; lia]); rewrite KB by (first [lia | unfold dp_win; lia]);
          replace (r + 56 * n + 24 + j) with (r + 56 * n + (24 + j)) by lia; rewrite Heff by lia;
          rewrite nth_overflow by lia; reflexivity ])
| _ => idtac end.
(* The return at the FP state fy of the arm (fx on arm 0, fx6 on arm 1): the post's journal, the callee-saved
   registers (atoms of the entry registers), a0 = n and the registry bytes (dp_final). *)
all: lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msF), Hcc : dp_case _ ?c,
    HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?msF) _ _, HFP : @fp_csr ?fy = _ \/ _ |- _ =>
  lazymatch type of KA with forall a, _ -> _ -> aview _ _ ?mT a = _ =>
  prreg HS (1%bv : bv 5) R1; prreg HS (10%bv : bv 5) R10;
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as HRrow;
  pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as HRnw;
  cbn [restrict ms_mem] in HRrow, HRnw;
  pose proof (dp_rowfacts Ex (w_H W) (ms_mem msF) c n r b k b0 Hcc HRrow Ur' F11 F13 F33 Hb0) as Hrow;
  pose proof (dp_nwfacts Ex (w_H W) (ms_mem msF) c n r Hcc HRnw Ur') as Hnw;
  assert (KA' : forall i, 0 <= i < 288 -> ~ (56 * n <= i < 56 * n + 56) -> ~ (280 <= i < 284) ->
     aview SEGS (w_H W) mT (r + i) = aview SEGS (w_H W) mem2 (r + i))
    by (intros i Hi H1 H2; apply KA; [lia | unfold dp_win; lia]);
  assert (Hfr' : forall i, 0 <= i < 288 -> ~ (56 * n <= i < 56 * n + 56) ->
     aview SEGS (w_H W) mem3 (r + i) = aview SEGS (w_H W) mT (r + i))
    by (intros i Hi H1; apply Hfr; [lia | lia | rewrite Hes; lia]);
  eapply (paj_ret_at (fx := fy) (PL := PL_boxb) (PI := PI) W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
  intros mat';
  unfold tbreac_boxreg_declare_post, apost_baseF;
  exists fy, ly, S, (ms_regs msF), (ms_mem msF); eexists;
  split; [cbn [ms_regs]; rewrite R1, F1, Hra; reflexivity|];
  split; [exact Hfr6|]; split; [exact HFP|];
  split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJx|];
  split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (dp_extra regs2 b) HS);
          [repeat first [exact HAE' | apply dp_agree_ewset; [cbv; lia|]] | vm_compute; reflexivity]|];
  split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [apply Permutation_refl|];
  right; exists b, (if b0 <? 0 then 0 else 1); split; [exact Hpl|]; split;
  [ rewrite R10; unfold w64; f_equal; unfold dp_case in Hcc; lia
  | exact (dp_final W mem2 mT mem3 (ms_mem msF) r n b k (if b0 <? 0 then 0 else 1) bs s HL (eq_sym Hneq) Hn4 Hsf HB
             KA' Heff Hfr' KB' Hrow Hnm' Hnw) ]
  end end.
Qed.
(* The entry part of the walk: from the entry to the refusals and to the two callee calls, joining at 0x81bcc. *)
Definition dm_b (bs : list byte) (i : Z) : Z := bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)).
Definition dm_w4 (bs : list byte) (o : Z) : Z :=
dm_b bs o + 256 * dm_b bs (o + 1) + 65536 * dm_b bs (o + 2) + 16777216 * dm_b bs (o + 3).
Lemma dm_b_range : forall bs i, 0 <= dm_b bs i < 256.
Proof. intros bs i. unfold dm_b. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) bs (Z_to_bv 8 0))) as R. exact R. Qed.
Lemma dm_w4_range : forall bs o, 0 <= dm_w4 bs o < 2 ^ 32.
Proof.
intros bs o. unfold dm_w4. pose proof (dm_b_range bs o). pose proof (dm_b_range bs (o + 1)).
pose proof (dm_b_range bs (o + 2)). pose proof (dm_b_range bs (o + 3)). lia.
Qed.
Lemma dm_le_byte : forall bs o (k : nat), (k < 4)%nat -> YO0f.le_byte (dm_w4 bs o) 4 k = dm_b bs (o + Z.of_nat k).
Proof.
intros bs o k Hk. unfold YO0f.le_byte. rewrite (Z.mod_small (dm_w4 bs o)) by (pose proof (dm_w4_range bs o); change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32); lia).
rewrite Z.shiftr_div_pow2 by lia. unfold dm_w4.
pose proof (dm_b_range bs o). pose proof (dm_b_range bs (o + 1)).
pose proof (dm_b_range bs (o + 2)). pose proof (dm_b_range bs (o + 3)).
destruct k as [|[|[|[|k]]]]; try lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ];
rewrite ?Z.add_0_r; change (2 ^ (8 * 0)) with 1; change (2 ^ (8 * 1)) with 256; change (2 ^ (8 * 2)) with 65536;
change (2 ^ (8 * 3)) with 16777216; Z.div_mod_to_equations; lia.
Qed.
Lemma dm_val_mem4 : forall W mem r bs o, tbdecl_reg_bytes W mem r bs -> 0 <= o -> o + 4 <= 288 ->
val_mem SEGS (mrestrict (w_H W) mem) (r + o) 4 (dm_w4 bs o).
Proof.
intros W mem r bs o HB Ho Ho4 k Hk. rewrite (dm_le_byte bs o k Hk).
specialize (HB (o + Z.of_nat k) ltac:(unfold REG_SIZEB; lia)).
destruct (aview_byte SEGS (w_H W) mem (r + (o + Z.of_nat k)) _ HB) as (b & Hb & Hv & _).
replace (r + o + Z.of_nat k) with (r + (o + Z.of_nat k)) by lia. rewrite Hb. f_equal.
unfold dm_b. rewrite Hv. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma dm_bsub4 : forall (bs : list byte) o, length bs = 288%nat -> 0 <= o -> o + 4 <= 288 ->
bytes_le_to_Z (Boxreg.bsub bs o 4) = dm_w4 bs o.
Proof.
intros bs o HL Ho Ho4.
assert (E : Boxreg.bsub bs o 4 = [nth (Z.to_nat o) bs (Z_to_bv 8 0); nth (Z.to_nat (o + 1)) bs (Z_to_bv 8 0);
  nth (Z.to_nat (o + 2)) bs (Z_to_bv 8 0); nth (Z.to_nat (o + 3)) bs (Z_to_bv 8 0)]).
{ apply BoxregUpd.list_ext_nth. intros i. rewrite BoxregUpd.nth_bsub by lia.
  destruct i as [|[|[|[|i]]]]; cbn [Nat.ltb Nat.leb Z.to_nat Pos.to_nat Pos.iter_op Nat.add nth_error];
  [..| destruct i; reflexivity];
  (rewrite nth_error_nth' with (d := Z_to_bv 8 0) by lia; f_equal; f_equal; lia). }
rewrite E, OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib.Bytes.bytes_le_to_Z_le_val.
cbn [map OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib.Bytes.le_val]. unfold dm_w4, dm_b. lia.
Qed.
Lemma dm_rd4 : forall (bs : list byte) o, length bs = 288%nat -> 0 <= o -> o + 4 <= 288 ->
Boxreg.rd4 bs o = bv_swrap 32 (dm_w4 bs o).
Proof. intros bs o HL Ho Ho4. unfold Boxreg.rd4. rewrite dm_bsub4 by assumption. reflexivity. Qed.
Lemma dm_w4_small : forall bs o v, length bs = 288%nat -> 0 <= o -> o + 4 <= 288 -> Boxreg.rd4 bs o = v -> 0 <= v ->
dm_w4 bs o = v.
Proof.
intros bs o v HL Ho Ho4 Hr Hv. rewrite dm_rd4 in Hr by assumption. pose proof (dm_w4_range bs o) as R.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in Hr. cbn [Z.of_N] in Hr.
change (2 ^ 32 / 2) with (2 ^ 31) in Hr. Z.div_mod_to_equations. lia.
Qed.
(* The symbolic state at the entry: the frame, the GOT word and the shadow cell, and the registry block's words n
   (r + 280, atom 34) and fabric (r + 284, atom 33); atom 32 is the shadow offset. *)
Definition dm_RR : YP09.region :=
YP09.mkRegion (Some 10%nat) 280 288 280 280 [YP09.mkChunk 280 (CVal 4 (SOff 34 0)); YP09.mkChunk 284 (CVal 4 (SOff 33 0))].
Definition dm_regions : smem := [stack_region 80; got_regionP; bcell_regionP 32; dm_RR].
Definition dm_facts : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 140737479966432 4); (32%nat, mkAF SBR SBR 0);
         (33%nat, mkAF 0 4294967295 0); (34%nat, mkAF 0 4294967295 0)] [] [].
Definition ss_dm : sstate := mkSS AF_reac_boxreg_declare sr_atoms dm_regions None dm_facts.
Definition dm_SH : list shent := [mkSHE 10 0 288].
Definition dm_extra (bs : list byte) : list word := map (Z_to_bv 64) [SBR; dm_w4 bs 284; dm_w4 bs 280].
Definition EM (regs : bvmap 5 word) (bs : list byte) : env := Eimg (Ereg regs (dm_extra bs)).
Lemma dm_entry : forall ly S W (regs : bvmap 5 word) mem md ch r bs,
afn_pre SEGS B REAC_BOXREG_DECLARE_STKB ly S W regs mem md ch ->
getr regs 10 = w64 r -> In (r, REG_SIZEB) (ablocks B ly S) -> tbdecl_reg_bytes W mem r bs ->
st_ok_pi SEGS VAL (EM regs bs) ss_dm (restrict (w_H W) (mkst regs (Z_to_bv 64 AB_reac_boxreg_declareP) mem (seg_rom SEGS)))
/\ sh_ok SEGS CBR dm_SH (EM regs bs) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md ch r bs HPRE H10 Hin HRB.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOXREG_DECLARE_STKB = 8272) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md r REG_SIZEB HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & _ & _).
change (req_size REG_SIZEB) with 288 in *.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
pose proof (dm_w4_range bs 284) as R284. pose proof (dm_w4_range bs 280) as R280.
rewrite restrict_mkst_fx.
set (E := EM regs bs).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (dm_extra bs)) n)
  by (intros n Hn; subst E; unfold EM; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 r) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SBR) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (dm_w4 bs 284)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (dm_w4 bs 280)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (Egot : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; unfold EM; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Ecell : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; unfold EM; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_dm, AB_reac_boxreg_declareP. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold dm_regions, dm_RR, stack_region, got_regionP, bcell_regionP.
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
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 CBR SBR);
      [cbn [sv_denot CBR]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SBR; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    * rewrite (VB 10%nat r E10) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      -- apply (chunk_ok_val SEGS E _ r 280 4 (SOff 34 0) (dm_w4 bs 280));
         [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         exact (dm_val_mem4 W mem r bs 280 HRB ltac:(lia) ltac:(lia)).
      -- apply (chunk_ok_val SEGS E _ r 284 4 (SOff 33 0) (dm_w4 bs 284));
         [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         exact (dm_val_mem4 W mem r bs 284 HRB ltac:(lia) ltac:(lia)).
  + apply pairwise_disjoint_of_extents.
    unfold dm_regions, dm_RR, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) Egot) by (pose proof (pa_val_range (A_OBJ 1)); lia).
    rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) Ecell) by (pose proof (pa_val_range (A_OBJ 12)); lia).
    rewrite (VB 10%nat r E10) by lia.
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    pose proof (blk_off_imgP B ly S W mem md r REG_SIZEB HAR Hin) as Himg. change (req_size REG_SIZEB) with 288 in Himg.
    revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgcD HgotR Hr4096 Hrceil Himg. clear.
    intros. repeat split; lia.
  + split; [|split; exact I].
    cbn [dm_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E10, E32, E33, E34, !unsigned_lit_small by (unfold SBR; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 Hal16 Hr16 Hr4096 Hrceil R284 R280.
    clear. unfold SBR. intros. repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, dm_SH. apply Forall_cons; [|apply Forall_nil].
  eapply (rbi_shent B LAWS ly S W mem md E r r REG_SIZEB 0 288 10%nat HAR Hin);
  [ unfold CBR; rewrite (U_atom E 32 SBR E32) by (unfold SBR; lia); reflexivity
  | rewrite (U_atom E 10 r E10) by lia; reflexivity | lia | lia | change (req_size REG_SIZEB) with 288; lia ].
Qed.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_boxb) (PI := PI).
Let RUNTO := paj_run_to B LAWS.
(* The branch conditions of the entry part, as Z tests. *)
Lemma dm_sx : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 -> sv_denot E (SExt true 32 (SOff n 0)) = Z_to_bv 64 v.
Proof.
intros E n v H Hv. rewrite denot_lit_U, U_SExt, (U_atom E n v H) by lia. cbv iota.
change (2 ^ Z.of_N 32) with 4294967296. rewrite (Z.mod_small v) by lia.
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
unfold zcanon, M64. f_equal. Z.div_mod_to_equations. lia.
Qed.
Lemma dm_blt : forall a b, -2 ^ 63 <= a < 2 ^ 63 -> -2 ^ 63 <= b < 2 ^ 63 ->
branch_taken BC_LT (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. cbn [branch_taken]. exact (Boxreg.lts_lit a b Ha Hb). Qed.
Lemma dm_den_atom : forall E n v, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v H. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma dm_c1 : forall E k, ew E 11 = Z_to_bv 64 k -> -2 ^ 31 <= k < 2 ^ 31 ->
branch_taken BC_LTU (sv_denot E (SAluw ALU_ADD (SOff 11 0) (SLit (-41)))) (sv_denot E (SLit 18446744073709551577))
= negb ((2 <=? k) && (k <=? 40)).
Proof.
intros E k H11 Hk. rewrite branch_ltu_U, U_SLit, U_of_S, S_SAluw. cbn [zalu_raw].
rewrite U_SOff, H11, Z.add_0_r, U_SLit, Z_to_bv_unsigned.
unfold zcanon, M64, bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648.
change (bv_modulus 32) with 4294967296. change (bv_modulus 64) with 18446744073709551616.
change (2 ^ 64) with 18446744073709551616. change (2 ^ 32) with 4294967296.
destruct (Z.leb_spec 2 k), (Z.leb_spec k 40); cbn [andb negb];
[apply Z.ltb_ge | apply Z.ltb_lt | apply Z.ltb_lt | apply Z.ltb_lt]; Z.div_mod_to_equations; lia.
Qed.
Lemma dm_c2 : forall E k, ew E 11 = Z_to_bv 64 k -> 2 <= k <= 40 ->
branch_taken BC_NE (sv_denot E (SAlu ALU_AND (SOff 11 0) (SLit 1))) (sv_denot E (SLit 0)) = negb (k mod 2 =? 0).
Proof.
intros E k H11 Hk. rewrite branch_ne_U, U_and_lit, (U_atom E 11 k H11), U_lit by lia.
change 1 with (Z.ones 1). rewrite Z.land_ones by lia. reflexivity.
Qed.
Lemma dm_lt_sx_atom : forall E n m v w, ew E n = Z_to_bv 64 v -> ew E m = Z_to_bv 64 w -> 0 <= v < 2 ^ 31 ->
-2 ^ 31 <= w < 2 ^ 31 -> branch_taken BC_LT (sv_denot E (SExt true 32 (SOff n 0))) (sv_denot E (SOff m 0)) = (v <? w).
Proof. intros E n m v w Hn Hm Hv Hw. rewrite (dm_sx E n v Hn Hv), (dm_den_atom E m w Hm). apply dm_blt; lia. Qed.
Lemma dm_lt_lit_sx : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 -> 0 <= c < 2 ^ 31 ->
branch_taken BC_LT (sv_denot E (SLit c)) (sv_denot E (SExt true 32 (SOff n 0))) = (c <? v).
Proof. intros E n v c Hn Hv Hc. rewrite (dm_sx E n v Hn Hv). cbn [sv_denot]. apply dm_blt; lia. Qed.
Lemma dm_lt_atom_0 : forall E n v, ew E n = Z_to_bv 64 v -> -2 ^ 63 <= v < 2 ^ 63 ->
branch_taken BC_LT (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = (v <? 0).
Proof. intros E n v Hn Hv. rewrite (dm_den_atom E n v Hn). cbn [sv_denot]. apply dm_blt; lia. Qed.
Lemma dm_c6 : forall E f k, ew E 33 = Z_to_bv 64 f -> ew E 11 = Z_to_bv 64 k -> 0 <= f <= 40 -> 0 <= k <= 40 ->
branch_taken BC_NE (sv_denot E (SAluw ALU_SUB (SExt true 32 (SOff 33 0)) (SOff 11 0)))
  (sv_denot E (SAlu ALU_SUB (SExt true 32 (SOff 33 0)) (SOff 11 0))) = false.
Proof.
intros E f k H33 H11 Hf Hk.
assert (UX : U E (SExt true 32 (SOff 33 0)) = f) by (unfold U; rewrite (dm_sx E 33 f H33) by lia; apply unsigned_lit_small; lia).
assert (UK : U E (SOff 11 0) = k) by (apply (U_atom E 11 k H11); lia).
rewrite branch_ne_U, U_of_S, S_SAluw, U_SAlu. cbn [zalu_raw]. rewrite UX, UK.
unfold zcanon, M64, bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648.
change (bv_modulus 32) with 4294967296. change (bv_modulus 64) with 18446744073709551616.
change (2 ^ 64) with 18446744073709551616. change (2 ^ 32) with 4294967296.
apply negb_false_iff, Z.eqb_eq. Z.div_mod_to_equations. lia.
Qed.
Lemma dm_c7 : forall E f k b0, ew E 33 = Z_to_bv 64 f -> ew E 11 = Z_to_bv 64 k -> ew E 13 = Z_to_bv 64 b0 ->
0 <= f <= 40 -> 0 <= k <= 40 -> -2 ^ 31 <= b0 < 2 ^ 31 ->
branch_taken BC_LT (sv_denot E (SAluw ALU_ADD (SAlu ALU_SUB (SExt true 32 (SOff 33 0)) (SOff 11 0)) (SLit 0)))
  (sv_denot E (SOff 13 0)) = (f - k <? b0).
Proof.
intros E f k b0 H33 H11 H13 Hf Hk Hb.
assert (UX : U E (SExt true 32 (SOff 33 0)) = f) by (unfold U; rewrite (dm_sx E 33 f H33) by lia; apply unsigned_lit_small; lia).
assert (UK : U E (SOff 11 0) = k) by (apply (U_atom E 11 k H11); lia).
assert (D : sv_denot E (SAluw ALU_ADD (SAlu ALU_SUB (SExt true 32 (SOff 33 0)) (SOff 11 0)) (SLit 0)) = Z_to_bv 64 (f - k)).
{ rewrite denot_lit_U. apply bv_eq. rewrite !Z_to_bv_unsigned.
  rewrite U_of_S, S_SAluw, U_SAlu, U_SLit. cbn [zalu_raw]. rewrite UX, UK.
  unfold zcanon, M64, bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648.
  change (bv_modulus 32) with 4294967296. change (bv_modulus 64) with 18446744073709551616.
  change (2 ^ 64) with 18446744073709551616. change (2 ^ 32) with 4294967296.
  Z.div_mod_to_equations. lia. }
rewrite D, (dm_den_atom E 13 b0 H13). apply dm_blt; lia.
Qed.
Lemma dm_agree_ewset : forall E0 E n v, (32 <= n)%nat -> env_agree 32 E0 E -> env_agree 32 E0 (ewset E n v).
Proof. intros E0 E n v Hn [HA HD]. split; [intros i Hi; rewrite ew_ewset_other by lia; apply HA; exact Hi | exact HD]. Qed.
(* The memory outside the frame [sp - 80, sp) after a run step whose only write window is the frame. *)
Ltac dm_keep Usp :=
  lazymatch goal with
  | HFr : frame_of ?Ex ?rs (mrestrict (w_H ?Wv) ?m1) (mrestrict _ ?m2),
    KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (?lo <= a < ?hi) -> aview _ _ ?m1 a = aview _ _ ?m0 a |- _ =>
    let K2 := fresh "KEEP" in
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H Wv) m2 a = aview SEGS (w_H Wv) m0 a);
    [ let a := fresh "a" in let Ha := fresh "Ha" in let Hw := fresh "Hw" in
      intros a Ha Hw; transitivity (aview SEGS (w_H Wv) m1 a); [ | exact (KEEP a Ha Hw)];
      apply (kept_of_frame (segs := SEGS) Ex rs (w_H Wv) m1 m2 (fun x => lo <= x < hi) HFr); [| exact Ha | exact Hw];
      let bb := fresh "bb" in let wlo := fresh "wlo" in let whi := fresh "whi" in let aa := fresh "aa" in
      let Hin := fresh "Hin" in let Hr := fresh "Hr" in
      intros bb wlo whi aa Hin Hr;
      lazymatch type of Hin with In _ (windows ?rr) => let rs' := eval vm_compute in (windows rr) in change (windows rr) with rs' in Hin end;
      cbn [In] in Hin; repeat destruct Hin as [Hin | Hin]; try contradiction; injection Hin as <- <- <-;
      cbn [base_val ew ewset havoc Nat.eqb Nat.ltb Nat.leb] in Hr; rewrite ?ew_ewset_other in Hr by lia; rewrite ?Usp in Hr; lia
    | clear KEEP HFr; rename K2 into KEEP ]
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac dm_side := first [ lia | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb Nat.sub nth map CLOB]; rewrite ?ew_ewset_other by lia; assumption ].
Ltac dm_run Usp :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  paj_run_tok RUN HS HJ SHOK BspanR;
  [ awr_ok_tac; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb]; rewrite ?ew_ewset_other by lia; exact Usp | dm_keep Usp ] end.
Ltac dm_run_to Usp stop :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  paj_run_to_tok RUNTO HS HJ SHOK BspanR stop;
  [ awr_ok_tac; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb]; rewrite ?ew_ewset_other by lia; exact Usp | dm_keep Usp ] end.
(* The frame region after the prologue: the ten saved registers. *)
Definition DM_FRAME : YP09.region :=
YP09.mkRegion (Some 2%nat) (-80) 0 (-80) 0
 [YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
  YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0));
  YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
  YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].
Lemma dm_bv5 : forall n, (n < 32)%nat -> Z.of_nat n = bv_unsigned (Z_to_bv 5 (Z.of_nat n)).
Proof.
intros n Hn. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma dm_frame_vals : forall Ex m (regs : bvmap 5 word),
region_ok SEGS Ex m DM_FRAME -> bv_unsigned (ew Ex 2) = spZ regs ->
(forall (n : nat) (rr : bv 5), Z.of_nat n = bv_unsigned rr -> (n < 32)%nat -> ew Ex n = getr regs rr) ->
forall i o, In (i, o) DECL_SAVES -> val_mem SEGS m (spZ regs - 80 + o) 8 (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat i)))).
Proof.
intros Ex m regs HR Hsp HE i o Hio.
assert (G : forall (n : nat) (od : Z), In (YP09.mkChunk od (CVal 8 (SOff n 0))) (YP09.r_chunks DM_FRAME) -> (n < 32)%nat ->
  val_mem SEGS m (spZ regs + od) 8 (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat n))))).
{ intros n od Hin Hn.
  refine (field_of_region (segs := SEGS) Ex m 2%nat (spZ regs) _ (-80) 0 (-80) 0 od 8 (SOff n 0) _ HR Hsp Hin _ _ _).
  - cbn [sv_denot]. rewrite (HE n (Z_to_bv 5 (Z.of_nat n)) (dm_bv5 n Hn) Hn), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 (Z.of_nat n)))) as R. change (bv_modulus 64) with (2 ^ 64) in R.
    change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  - lia. }
cbn [DECL_SAVES In] in Hio. repeat destruct Hio as [Hio | Hio]; try contradiction; injection Hio as <- <-;
match goal with |- val_mem _ _ (spZ regs - 80 + ?o) _ _ => replace (spZ regs - 80 + o) with (spZ regs + (o - 80)) by lia end;
(apply G; [cbn [DM_FRAME YP09.r_chunks In Z.sub Z.add Z.opp Pos.sub_mask]; repeat (first [left; reflexivity | right]) | lia]).
Qed.
Lemma dm_den_s7 : forall Ex r, ew Ex 10 = Z_to_bv 64 r -> ew Ex 32 = Z_to_bv 64 SBR -> 0 <= r -> r + 288 <= 2 ^ 47 ->
sv_denot Ex (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 280) (SLit 3)) (SOff 32 0)) = w64 (SBD + (r + 280) / 8).
Proof.
intros Ex r H10 H32 Hr0 Hr1. rewrite denot_lit_U. unfold w64. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_srl3, U_SOff, H10, unsigned_lit_small, (U_atom Ex 32 SBR H32) by (unfold SBR; lia).
rewrite (zcanon_id (r + 280)) by (unfold M64; lia).
unfold SBD, SBR. rewrite Z.add_comm. apply zcanon_id. unfold M64. split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
pose proof (Z.div_le_upper_bound (r + 280) 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma dm_eq_atom_0 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = (v =? 0).
Proof. intros E n v Hn Hv. rewrite branch_eq_U, (U_atom E n v Hn Hv), U_lit by lia. reflexivity. Qed.
Lemma dm_place_at : forall Ex (regs regs2 : bvmap 5 word) (W : world SEGS) mem2 r k nm b0 b,
(forall (n : nat) (rr : bv 5), Z.of_nat n = bv_unsigned rr -> (n < 32)%nat -> ew Ex n = getr regs rr) ->
ew Ex 32 = Z_to_bv 64 SBR -> 4096 <= r -> r + 288 <= 2 ^ 47 -> 4096 <= spZ regs <= 2 ^ 47 ->
getr regs 10 = w64 r -> getr regs 11 = w64 k -> getr regs 12 = w64 nm -> getr regs 13 = w64 b0 ->
getr regs2 2 = sv_denot Ex (SOff 2 (-80)) ->
getr regs2 3 = sv_denot Ex (SOff 3 0) -> getr regs2 4 = sv_denot Ex (SOff 4 0) ->
getr regs2 25 = sv_denot Ex (SOff 25 0) -> getr regs2 26 = sv_denot Ex (SOff 26 0) -> getr regs2 27 = sv_denot Ex (SOff 27 0) ->
getr regs2 8 = sv_denot Ex (SOff 12 0) -> getr regs2 9 = sv_denot Ex (SOff 10 280) ->
getr regs2 18 = sv_denot Ex (SOff 13 0) -> getr regs2 19 = sv_denot Ex (SOff 11 0) ->
getr regs2 20 = sv_denot Ex (SLit 18446744073709551615) -> getr regs2 21 = sv_denot Ex (SOff 10 0) ->
getr regs2 22 = w64 b ->
getr regs2 23 = sv_denot Ex (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 280) (SLit 3)) (SOff 32 0)) ->
getr regs2 24 = sv_denot Ex (SOff 32 0) ->
region_ok SEGS Ex (mrestrict (w_H W) mem2) DM_FRAME ->
dplace_at regs regs2 W mem2 r k nm b0 b.
Proof.
intros Ex regs regs2 W mem2 r k nm b0 b HE H32 Hr0 Hr1 Hsp H10 H11 H12 H13 R2 R3 R4 R25 R26 R27 R8 R9 R18 R19 R20 R21 R22 R23 R24 HR.
assert (A : forall (n : nat) (rr : bv 5), Z.of_nat n = bv_unsigned rr -> (n < 32)%nat ->
  forall c, sv_denot Ex (SOff n c) = Z_to_bv 64 (bv_unsigned (getr regs rr) + c)).
{ intros n rr Hrr Hn c. cbn [sv_denot]. rewrite (HE n rr Hrr Hn). reflexivity. }
assert (A0 : forall (n : nat) (rr : bv 5), Z.of_nat n = bv_unsigned rr -> (n < 32)%nat -> sv_denot Ex (SOff n 0) = getr regs rr).
{ intros n rr Hrr Hn. rewrite (A n rr Hrr Hn 0), Z.add_0_r. apply Z_to_bv_bv_unsigned. }
assert (E10 : ew Ex 10 = Z_to_bv 64 r) by (rewrite (HE 10%nat 10%bv eq_refl ltac:(lia)); exact H10).
unfold dplace_at.
split. { unfold spZ at 1. rewrite R2, (A 2%nat 2%bv eq_refl ltac:(lia)). fold (spZ regs). rewrite unsigned_lit_small by lia. lia. }
split. { rewrite R3. exact (A0 3%nat 3%bv eq_refl ltac:(lia)). }
split. { rewrite R4. exact (A0 4%nat 4%bv eq_refl ltac:(lia)). }
split. { rewrite R25. exact (A0 25%nat 25%bv eq_refl ltac:(lia)). }
split. { rewrite R26. exact (A0 26%nat 26%bv eq_refl ltac:(lia)). }
split. { rewrite R27. exact (A0 27%nat 27%bv eq_refl ltac:(lia)). }
split. { rewrite R8, (A0 12%nat 12%bv eq_refl ltac:(lia)). exact H12. }
split. { rewrite R9, (A 10%nat 10%bv eq_refl ltac:(lia)), H10. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
split. { rewrite R18, (A0 13%nat 13%bv eq_refl ltac:(lia)). exact H13. }
split. { rewrite R19, (A0 11%nat 11%bv eq_refl ltac:(lia)). exact H11. }
split. { rewrite R20. cbn [sv_denot]. apply bv_eq. reflexivity. }
split. { rewrite R21, (A0 10%nat 10%bv eq_refl ltac:(lia)). exact H10. }
split. { exact R22. }
split. { rewrite R23. apply (dm_den_s7 Ex r E10 H32); lia. }
split. { rewrite R24. cbn [sv_denot]. rewrite H32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
apply (dm_frame_vals Ex _ regs HR); [rewrite (HE 2%nat 2%bv eq_refl ltac:(lia)); reflexivity | exact HE].
Qed.
Ltac dm_rawreg HS r H :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?Hh ?ms) =>
    pose proof (st_ok_pi_restrict_reg Hh E ss ms r HS) as H;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in H;
    cbn [ms_regs restrict mkst] in H
  | st_ok ?segs ?E ?ss (restrict ?Hh ?ms) =>
    pose proof (st_ok_restrict_reg segs Hh E ss ms r HS) as H;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in H;
    cbn [ms_regs restrict mkst] in H
  end.
Ltac dm_agree HAE := repeat first [exact HAE | apply dm_agree_ewset; [cbv; lia|] | apply env_agree_havoc_ge; [lia|]].
(* A refusal: the run to the return through 0x81c94 (a0 = s4 = -1), and the post's left arm, at the entry's FP
   state (the path never reaches the snprintf wrapper). *)
Ltac dm_leaf Usp HAE E1 Hra Hsegs KEEP REGK REF :=
  dm_run Usp;
  lazymatch goal with HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    let R10 := fresh "R10" in let R1 := fresh "R1" in
    prreg HS (10%bv : bv 5) R10; prreg HS (1%bv : bv 5) R1;
    eapply (RET _ _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
    let mat' := fresh "mat" in intros mat';
    unfold tbreac_boxreg_declare_post, apost_baseF;
    exists fx; eexists; eexists; exists (ms_regs msc), (ms_mem msc); eexists;
    split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|];
    split; [intros ? ?; reflexivity|]; split; [left; reflexivity|];
    split; [apply (ajournal_materialize SEGS B LAWS Hsegs); rewrite ?wvb_collapse in HJ; exact HJ|];
    split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ _ (dm_extra _) HS); [dm_agree HAE | vm_compute; reflexivity]|];
    split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [apply Permutation_refl|];
    left; split;
    [ unfold reac_boxreg_declare_c.declare_refused, reac_boxreg_declare_c.box_width_ok, reac_boxreg_declare_c.range_ok; REF
    | split; [rewrite R10; apply bv_eq; reflexivity|];
      let i := fresh "i" in let Hi := fresh "Hi" in
      intros i Hi; unfold REG_SIZEB in Hi; rewrite (KEEP (_ + i)) by lia; apply REGK; unfold REG_SIZEB; exact Hi ]
  end.
Lemma decl_main : dplace_spec -> tbreac_boxreg_declare_spec.
Proof.
intros DPL. unfold tbreac_boxreg_declare_spec.
intros ly S W regs mem md ch r k nm b0 bs s G HPRE HRO H10 H11 H12 H13 Hk Hb0 Hin HRB HINV HNM HTV HISV HGM HFB HFG HFL HFH
  HFGOT HFRM.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
destruct (dm_entry ly S W regs mem md ch r bs HPRE H10 Hin HRB) as [HS SHOK].
pose proof (ajournal_init SEGS B REAC_BOXREG_DECLARE_STKB [(r, r + REG_SIZEB)] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOXREG_DECLARE_STKB = 8272) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md r REG_SIZEB HAR Hin) as (Hr16 & Hr4096 & Hrceil & Hria & _ & _).
change (req_size REG_SIZEB) with 288 in *. assert (Hsz : REG_SIZEB = 288) by reflexivity.
assert (Hnmr : 0 <= nm < alloc_ceiling).
{ destruct HNM as [(Hn0 & _) | (_ & _ & _ & nn & Hnn & Hnl & _)]; [lia|].
  destruct (al_blocks _ _ LAWS ly S W mem md nm nn HAR Hnn) as (_ & Hn4 & Hnc & _).
  assert (Hrq : 1 <= req_size nn) by (unfold req_size; destruct (Z.eqb_spec nn 0); lia). lia. }
pose proof (pa_base_lo (PL := PL_boxb) (PI := PI)) as HBlo. pose proof (@pa_B_ok _ _ PI) as HBok.
remember (EM regs bs) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (dm_extra bs)) n)
  by (intros n Hn; subst E; unfold EM; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 r) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 k) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 nm) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = Z_to_bv 64 b0) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13).
assert (E32 : ew E 32 = Z_to_bv 64 SBR) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (dm_w4 bs 284)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (dm_w4 bs 280)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (HAE : env_agree 32 (Ereg regs (dm_extra bs)) E)
  by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (HEreg : forall (n : nat) (rr : bv 5), Z.of_nat n = bv_unsigned rr -> (n < 32)%nat -> ew E n = getr regs rr)
  by (intros n rr Hrr Hn; rewrite (proj1 HAE n Hn); exact (ew_Ereg_nat regs _ n rr Hrr)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
clear HE EL.
unfold cfg_at, AB_reac_boxreg_declareP.
change (w64 (BASE + AF_reac_boxreg_declare)) with (Z_to_bv 64 (BASE + AF_reac_boxreg_declare)).
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 80 <= a < spZ regs) -> aview SEGS (w_H W) mem a = aview SEGS (w_H W) mem a)
  by reflexivity.
pose proof HINV as HINV0.
destruct HINV as [[HL [HB1 [HB2 [HB3 [HB4 [HB5 HB6]]]]]] HB7].
assert (EF : dm_w4 bs 284 = Boxreg.bx_fabric bs) by (unfold Boxreg.boxreg_B2 in HB2; apply dm_w4_small; [exact HL | lia | lia | reflexivity | lia]).
assert (EN : dm_w4 bs 280 = Boxreg.bx_n bs) by (unfold Boxreg.boxreg_B1 in HB1; apply dm_w4_small; [exact HL | lia | lia | reflexivity | lia]).
rewrite EF in E33. rewrite EN in E34. unfold Boxreg.boxreg_B1 in HB1. unfold Boxreg.boxreg_B2 in HB2.
dm_run Usp.
psrr_branch_tok RUN BR HS SHOK BspanR.
{ rewrite (dm_c1 _ k) in Hc by dm_side.
  dm_leaf Usp HAE E1 Hra Hsegs KEEP HRB ltac:(left; intros (_ & HK & _); apply negb_true_iff, andb_false_iff in Hc;
    destruct Hc as [Hc | Hc]; apply Z.leb_gt in Hc; lia). }
rewrite (dm_c1 _ k) in Hc by dm_side. apply negb_false_iff, andb_true_iff in Hc. destruct Hc as [Hk2 Hk40].
apply Z.leb_le in Hk2, Hk40.
dm_run Usp.
psrr_branch_tok RUN BR HS SHOK BspanR.
{ rewrite (dm_c2 _ k) in Hc by dm_side.
  dm_leaf Usp HAE E1 Hra Hsegs KEEP HRB ltac:(left; intros (Hev & _ & _); apply Z.even_spec in Hev; destruct Hev as [m Hm];
    apply negb_true_iff, Z.eqb_neq in Hc; apply Hc; rewrite Hm, Z.mul_comm, Z.mod_mul by lia; reflexivity). }
rewrite (dm_c2 _ k) in Hc by dm_side. apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hkev.
dm_run Usp.
psrr_branch_tok RUN BR HS SHOK BspanR.
{ rewrite (dm_lt_sx_atom _ 33 11 (Boxreg.bx_fabric bs) k) in Hc by dm_side.
  dm_leaf Usp HAE E1 Hra Hsegs KEEP HRB ltac:(left; intros (_ & _ & Hkf); apply Z.ltb_lt in Hc; lia). }
rewrite (dm_lt_sx_atom _ 33 11 (Boxreg.bx_fabric bs) k) in Hc by dm_side. apply Z.ltb_ge in Hc. rename Hc into Hfk.
dm_run Usp.
psrr_branch_tok RUN BR HS SHOK BspanR.
{ rewrite (dm_lt_lit_sx _ 34 (Boxreg.bx_n bs) 4) in Hc by dm_side.
  dm_leaf Usp HAE E1 Hra Hsegs KEEP HRB ltac:(right; left; apply Z.ltb_lt in Hc; lia). }
rewrite (dm_lt_lit_sx _ 34 (Boxreg.bx_n bs) 4) in Hc by dm_side. apply Z.ltb_ge in Hc. rename Hc into Hn4.
assert (Hkevn : Z.even k = true) by (apply Z.even_spec; exists (k / 2); pose proof (Z.div_mod k 2 ltac:(lia)); lia).
dm_run Usp.
psrr_branch_tok RUN BR HS SHOK BspanR.
2:{ rewrite (dm_lt_atom_0 _ 13 b0) in Hc by dm_side. apply Z.ltb_ge in Hc. rename Hc into Hb0p.
    dm_run Usp.
    psrr_branch_tok RUN BR HS SHOK BspanR.
    { exfalso. rewrite (dm_c6 _ (Boxreg.bx_fabric bs) k) in Hc by dm_side. discriminate Hc. }
    clear Hc. dm_run Usp.
    psrr_branch_tok RUN BR HS SHOK BspanR.
    { rewrite (dm_c7 _ (Boxreg.bx_fabric bs) k b0) in Hc by dm_side.
      dm_leaf Usp HAE E1 Hra Hsegs KEEP HRB ltac:(right; right; left; split; [lia | intros (_ & Hr & _); apply Z.ltb_lt in Hc; lia]). }
    rewrite (dm_c7 _ (Boxreg.bx_fabric bs) k b0) in Hc by dm_side. apply Z.ltb_ge in Hc. rename Hc into Hfkb.
    dm_run Usp.
    (* the call of range_taken (0x81ba8) *)
    lazymatch goal with HS : st_ok _ _ _ (restrict _ ?msc) |- _ => rename msc into mcall end.
    dm_rawreg HS (2%bv : bv 5) Tsp.
    prreg HS (1%bv : bv 5) Tra. prreg HS (3%bv : bv 5) Tgp. prreg HS (4%bv : bv 5) Ttp. prreg HS (8%bv : bv 5) Ts0.
    prreg HS (10%bv : bv 5) Ta0. prreg HS (11%bv : bv 5) Ta1. prreg HS (12%bv : bv 5) Ta2.
    assert (Qsp : spZ (ms_regs mcall) = spZ regs - 80)
      by (unfold spZ at 1; rewrite Tsp; cbn [sv_denot ew ewset Nat.eqb]; rewrite Usp, unsigned_lit_small by lia; lia).
    assert (KREG : tbdecl_reg_bytes W (ms_mem mcall) r bs)
      by (intros i Hi; unfold REG_SIZEB in Hi; rewrite (KEEP (r + i)) by lia; apply HRB; unfold REG_SIZEB; exact Hi).
    eapply SRr_bind.
    { lazymatch goal with HS : st_ok _ ?Ex _ _ |- _ =>
      eapply (aj_call SEGS B LAWS Hsegs W Ex _ mcall REAC_BOXREG_DECLARE_STKB (spZ regs) [(r, r + REG_SIZEB)] ly S W mem md [] ly S _ 0
        RANGE_TAKEN_STKB [] 0 (-80) (ew Ex 2) (getr (ms_regs mcall) 1) []
        (fun ly2 S2 W2 regs2 mem2 md2 => ly2 = ly /\ S2 = S /\ W2 = W /\
          ((lowest_free_base_c.slice_meets bs b0 k /\ getr regs2 10 = w64 1) \/
           (~ lowest_free_base_c.slice_meets bs b0 k /\ getr regs2 10 = w64 0))) HS eq_refl HJ) end.
      - exact Tsp.
      - reflexivity.
      - cbn [ew ewset Nat.eqb]. exact Usp.
      - reflexivity.
      - lia.
      - unfold RANGE_TAKEN_STKB, ESTACK. lia.
      - unfold RANGE_TAKEN_STKB, ESTACK. rewrite WS. lia.
      - rewrite Tgp, E3. exact Hgp.
      - rewrite Ttp, E4. exact Htp.
      - reflexivity.
      - rewrite Tra. apply ret_ok_codeptr_v; [lia | reflexivity].
      - rewrite Tra, unsigned_lit_small by lia. lia.
      - apply achain_low. unfold s0Z. rewrite Ts0, E12, unsigned_lit_small by lia. lia.
      - intros HPRE2. cbn [ss_pc setpc]. rewrite pa_sigma_range_taken.
        eapply SRr_mono.
        { apply (TRT ly S W (ms_regs mcall) (ms_mem mcall) _ [] r b0 k bs HPRE2).
          + rewrite Ta0, E10. reflexivity.
          + rewrite Ta1, E13. reflexivity.
          + rewrite Ta2, E11. reflexivity.
          + exact Hin.
          + exact HL.
          + exact KREG.
          + exact HB1.
          + lia.
          + intros i Hi. destruct (HB3 i Hi) as (_ & ? & ? & ? & ?). lia.
          + lia.
          + lia.
          + lia. }
        cbv beta. intros W2 c2 _ Hpost. exact Hpost.
      - intros a X. exfalso. exact (inFP_nil _ X). }

    cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJ1 & HP2 & (-> & -> & -> & HRT)).
    pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & K1a & K1b & _).
    pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
    jafter_call_keep_hi HS 512%nat regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2.
    match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
    { cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
      split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; cbn [ew ewset Nat.eqb]; rewrite Usp;
      intros a Ha.
      - apply (mbyte_of_aview SEGS). apply K1a; [lia | unfold RANGE_TAKEN_STKB, LOWEST_FREE_BASE_STKB, RANGE_TAKEN_STKB, ESTACK; lia].
      - intros _. apply (apresent_writable SEGS). apply HJpres. lia. }
    assert (KREG2 : tbdecl_reg_bytes W mem2 r bs).
    { intros i Hi. unfold REG_SIZEB in Hi.
      rewrite (K1b r REG_SIZEB i Hin Hin ltac:(change (req_size REG_SIZEB) with 288; lia) ltac:(intros X; exact (inFP_nil _ X))).
      apply KREG. unfold REG_SIZEB. exact Hi. }
    lazymatch type of HS with st_ok _ ?Ex _ _ =>
      assert (HEIc : img_env VAL A_LIM (havoc Ex 512 (map (getr regs2) CLOB))) by (apply img_env_havoc_hi; [assumption | unfold A_LIM; lia]) end.
    clear HS SHOK KEEP. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
    lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => assert (SHOK : sh_ok SEGS CBR [] Ex (mrestrict (w_H W) mem2)) by constructor end.
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 80 <= a < spZ regs) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem2 a)
      by reflexivity.
    clear HJ HJ1 K1a K1b. rename HJ2 into HJ. change (0 + 0) with 0 in HJ.
    rewrite Tra.
    destruct HRT as [(HM & HR10) | (HNMt & HR10)].
    + dm_run Usp.
      psrr_branch_tok RUN BR HS SHOK BspanR.
      { exfalso. rewrite (dm_eq_atom_0 _ 516 1) in Hc by dm_side. discriminate Hc. }
      clear Hc.
      dm_leaf Usp HAE E1 Hra Hsegs KEEP KREG2 ltac:(right; right; left; split; [lia | intros (_ & _ & Hn); exact (Hn HM)]).
    + dm_run Usp.
      psrr_branch_tok RUN BR HS SHOK BspanR.
      2:{ exfalso. rewrite (dm_eq_atom_0 _ 516 0) in Hc by dm_side. discriminate Hc. }
      clear Hc.
      dm_run_to Usp 7200.

      lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msc) |- _ =>
        pmkst HS;
        dm_rawreg HS (2%bv : bv 5) P2; dm_rawreg HS (3%bv : bv 5) P3; dm_rawreg HS (4%bv : bv 5) P4;
        dm_rawreg HS (25%bv : bv 5) P25; dm_rawreg HS (26%bv : bv 5) P26; dm_rawreg HS (27%bv : bv 5) P27;
        dm_rawreg HS (8%bv : bv 5) P8; dm_rawreg HS (9%bv : bv 5) P9; dm_rawreg HS (18%bv : bv 5) P18;
        dm_rawreg HS (19%bv : bv 5) P19; dm_rawreg HS (20%bv : bv 5) P20; dm_rawreg HS (21%bv : bv 5) P21;
        dm_rawreg HS (22%bv : bv 5) P22; dm_rawreg HS (23%bv : bv 5) P23; dm_rawreg HS (24%bv : bv 5) P24;
        assert (HFR : region_ok SEGS Ex (mrestrict (w_H W) (ms_mem msc)) DM_FRAME)
          by (exact (st_ok_pi_region_nth Ex ssx (restrict (w_H W) msc) 0 DM_FRAME HS eq_refl));
        assert (HEx : forall (n : nat) (rr : bv 5), Z.of_nat n = bv_unsigned rr -> (n < 32)%nat -> ew Ex n = getr regs rr)
          by (intros n rr Hrr Hn; repeat (first [rewrite ew_havoc_old by lia | rewrite ew_ewset_other by lia]);
              exact (HEreg n rr Hrr Hn));
        apply (DPL ly S W regs mem md ch r k nm b0 bs s G (ms_regs msc) (ms_mem msc) _ b0 HPRE HRO H10 H11 H12 H13 Hk Hb0 Hin HRB
                 HINV0 HNM HTV HISV HGM HFB HFG HFL HFH HFGOT HFRM);
        [ rewrite ?wvb_collapse in HJ; first [exact HJ | apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ]
        | intros i Hi; unfold REG_SIZEB in Hi; rewrite (KEEP (r + i)) by lia; apply KREG2; unfold REG_SIZEB; exact Hi
        | apply (dm_place_at Ex regs (ms_regs msc) W (ms_mem msc) r k nm b0 b0 HEx ltac:(dm_side) ltac:(lia) ltac:(lia) ltac:(lia)
                  H10 H11 H12 H13 P2 P3 P4 P25 P26 P27 P8 P9 P18 P19 P20 P21 ltac:(rewrite P22; cbn [sv_denot]; rewrite (HEx 13%nat 13%bv eq_refl ltac:(lia)), H13, Z.add_0_r; unfold w64; apply Z_to_bv_bv_unsigned) P23 P24 HFR)
        | unfold reac_boxreg_declare_c.declare_placed, reac_boxreg_declare_c.box_width_ok, reac_boxreg_declare_c.range_ok; rewrite (proj2 (Z.ltb_ge b0 0) Hb0p); split; [repeat split; first [exact Hkevn | lia] |]; split; [lia|]; left; repeat split; first [lia | reflexivity | exact HNMt] ]
      end.
  }
rewrite (dm_lt_atom_0 _ 13 b0) in Hc by dm_side. apply Z.ltb_lt in Hc. rename Hc into Hb0n.
dm_run Usp.
(* the call of lowest_free_base (0x81bc0) *)
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?msc) |- _ => rename msc into mcall end.
dm_rawreg HS (2%bv : bv 5) Tsp.
prreg HS (1%bv : bv 5) Tra. prreg HS (3%bv : bv 5) Tgp. prreg HS (4%bv : bv 5) Ttp. prreg HS (8%bv : bv 5) Ts0.
prreg HS (10%bv : bv 5) Ta0. prreg HS (11%bv : bv 5) Ta1.
assert (Qsp : spZ (ms_regs mcall) = spZ regs - 80)
  by (unfold spZ at 1; rewrite Tsp; cbn [sv_denot ew ewset Nat.eqb]; rewrite Usp, unsigned_lit_small by lia; lia).
assert (KREG : tbdecl_reg_bytes W (ms_mem mcall) r bs)
  by (intros i Hi; unfold REG_SIZEB in Hi; rewrite (KEEP (r + i)) by lia; apply HRB; unfold REG_SIZEB; exact Hi).
eapply SRr_bind.
{ lazymatch goal with HS : st_ok _ ?Ex _ _ |- _ =>
  eapply (aj_call SEGS B LAWS Hsegs W Ex _ mcall REAC_BOXREG_DECLARE_STKB (spZ regs) [(r, r + REG_SIZEB)] ly S W mem md [] ly S _ 0
    LOWEST_FREE_BASE_STKB [] 0 (-80) (ew Ex 2) (getr (ms_regs mcall) 1) []
    (fun ly2 S2 W2 regs2 mem2 md2 => ly2 = ly /\ S2 = S /\ W2 = W /\
      exists z, getr regs2 10 = w64 z /\ lowest_free_base_c.lowest_free bs k z) HS eq_refl HJ) end.
  - exact Tsp.
  - reflexivity.
  - cbn [ew ewset Nat.eqb]. exact Usp.
  - reflexivity.
  - lia.
  - unfold LOWEST_FREE_BASE_STKB, RANGE_TAKEN_STKB, ESTACK. lia.
  - unfold LOWEST_FREE_BASE_STKB, RANGE_TAKEN_STKB, ESTACK. rewrite WS. lia.
  - rewrite Tgp, E3. exact Hgp.
  - rewrite Ttp, E4. exact Htp.
  - reflexivity.
  - rewrite Tra. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite Tra, unsigned_lit_small by lia. lia.
  - apply achain_low. unfold s0Z. rewrite Ts0, E12, unsigned_lit_small by lia. lia.
  - intros HPRE2. cbn [ss_pc setpc]. rewrite pa_sigma_lowest_free_base.
    eapply SRr_mono.
    { apply (TLFB ly S W (ms_regs mcall) (ms_mem mcall) _ [] r k bs HPRE2).
      + rewrite Ta0, E10. reflexivity.
      + rewrite Ta1, E11. reflexivity.
      + lia.
      + exact Hin.
      + exact HL.
      + exact KREG.
      + exact HB1.
      + exact HB2.
      + exact HB3. }
    cbv beta. intros W2 c2 _ Hpost. exact Hpost.
  - intros a X. exfalso. exact (inFP_nil _ X). }

cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJ1 & HP2 & (-> & -> & -> & HRT)).
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & K1a & K1b & _).
pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
jafter_call_keep_hi HS 512%nat regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; cbn [ew ewset Nat.eqb]; rewrite Usp;
  intros a Ha.
  - apply (mbyte_of_aview SEGS). apply K1a; [lia | unfold RANGE_TAKEN_STKB, LOWEST_FREE_BASE_STKB, RANGE_TAKEN_STKB, ESTACK; lia].
  - intros _. apply (apresent_writable SEGS). apply HJpres. lia. }
assert (KREG2 : tbdecl_reg_bytes W mem2 r bs).
{ intros i Hi. unfold REG_SIZEB in Hi.
  rewrite (K1b r REG_SIZEB i Hin Hin ltac:(change (req_size REG_SIZEB) with 288; lia) ltac:(intros X; exact (inFP_nil _ X))).
  apply KREG. unfold REG_SIZEB. exact Hi. }
lazymatch type of HS with st_ok _ ?Ex _ _ =>
  assert (HEIc : img_env VAL A_LIM (havoc Ex 512 (map (getr regs2) CLOB))) by (apply img_env_havoc_hi; [assumption | unfold A_LIM; lia]) end.
clear HS SHOK KEEP. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => assert (SHOK : sh_ok SEGS CBR [] Ex (mrestrict (w_H W) mem2)) by constructor end.
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 80 <= a < spZ regs) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem2 a)
  by reflexivity.
clear HJ HJ1 K1a K1b. rename HJ2 into HJ. change (0 + 0) with 0 in HJ.
rewrite Tra.
destruct HRT as (z & HR10 & Hlf).
assert (Hzr : -1 <= z <= 40 /\ (z < 0 -> z = -1)).
{ destruct Hlf as [(-> & _) | (Hz0 & Hzk & _)]; lia. }
dm_run Usp.
psrr_branch_tok RUN BR HS SHOK BspanR.
{ rewrite (dm_lt_atom_0 _ 516 z) in Hc by dm_side. apply Z.ltb_lt in Hc.
  dm_leaf Usp HAE E1 Hra Hsegs KEEP KREG2 ltac:(right; right; right; split; [lia | replace (-1) with z by lia; exact Hlf]). }
rewrite (dm_lt_atom_0 _ 516 z) in Hc by dm_side. apply Z.ltb_ge in Hc. rename Hc into Hz0.
dm_run_to Usp 7200.

lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msc) |- _ =>
  pmkst HS;
  dm_rawreg HS (2%bv : bv 5) P2; dm_rawreg HS (3%bv : bv 5) P3; dm_rawreg HS (4%bv : bv 5) P4;
  dm_rawreg HS (25%bv : bv 5) P25; dm_rawreg HS (26%bv : bv 5) P26; dm_rawreg HS (27%bv : bv 5) P27;
  dm_rawreg HS (8%bv : bv 5) P8; dm_rawreg HS (9%bv : bv 5) P9; dm_rawreg HS (18%bv : bv 5) P18;
  dm_rawreg HS (19%bv : bv 5) P19; dm_rawreg HS (20%bv : bv 5) P20; dm_rawreg HS (21%bv : bv 5) P21;
  dm_rawreg HS (22%bv : bv 5) P22; dm_rawreg HS (23%bv : bv 5) P23; dm_rawreg HS (24%bv : bv 5) P24;
  assert (HFR : region_ok SEGS Ex (mrestrict (w_H W) (ms_mem msc)) DM_FRAME)
    by (exact (st_ok_pi_region_nth Ex ssx (restrict (w_H W) msc) 0 DM_FRAME HS eq_refl));
  assert (HEx : forall (n : nat) (rr : bv 5), Z.of_nat n = bv_unsigned rr -> (n < 32)%nat -> ew Ex n = getr regs rr)
    by (intros n rr Hrr Hn; repeat (first [rewrite ew_havoc_old by lia | rewrite ew_ewset_other by lia]);
        exact (HEreg n rr Hrr Hn));
  apply (DPL ly S W regs mem md ch r k nm b0 bs s G (ms_regs msc) (ms_mem msc) _ z HPRE HRO H10 H11 H12 H13 Hk Hb0 Hin HRB
           HINV0 HNM HTV HISV HGM HFB HFG HFL HFH HFGOT HFRM);
  [ rewrite ?wvb_collapse in HJ; first [exact HJ | apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ]
  | intros i Hi; unfold REG_SIZEB in Hi; rewrite (KEEP (r + i)) by lia; apply KREG2; unfold REG_SIZEB; exact Hi
  | apply (dm_place_at Ex regs (ms_regs msc) W (ms_mem msc) r k nm b0 z HEx ltac:(dm_side) ltac:(lia) ltac:(lia) ltac:(lia)
            H10 H11 H12 H13 P2 P3 P4 P25 P26 P27 P8 P9 P18 P19 P20 P21 ltac:(rewrite P22; cbn [sv_denot]; rewrite Z.add_0_r; replace (ew Ex 516) with (Z_to_bv 64 z) by (symmetry; dm_side); unfold w64; apply Z_to_bv_bv_unsigned) P23 P24 HFR)
  | unfold reac_boxreg_declare_c.declare_placed, reac_boxreg_declare_c.box_width_ok, reac_boxreg_declare_c.range_ok; rewrite (proj2 (Z.ltb_lt b0 0) Hb0n); split; [repeat split; first [exact Hkevn | lia] |]; split; [lia|]; right; repeat split; first [lia | reflexivity | exact Hlf] ]
end.
Qed.
(* The walk: the entry part (decl_main) with the placement segment (decl_place_of_snp) and the snprintf call
   (decl_snprintf_at). *)
Theorem pbb_reac_boxreg_declare : tbreac_boxreg_declare_spec.
Proof. exact (decl_main (decl_place_of_snp decl_snprintf_at)). Qed.
End h.
End f.
End d.
