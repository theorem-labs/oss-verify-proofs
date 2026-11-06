(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the part of proofs/cgif/cgif_file_fuzzer/lib/YC20.v that carries no cgif name, as fuzz_grant's lib/A/Prog/GrantBase.v (origin/cold/pg-prog 4a980cd5011) and fuzz_identity's lib/A/Prog/IdentBase.v (origin/cold/port-libreac-identity ea5560a967b) carry it, with only the unit's module prefix changed, for libreac/fuzz_boxreg: the read-only range, the frame object and the shape of a call's post-condition. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_boxreg/lib/A/Prog/BoxBase.v at origin/ossv/recipes ee71d1fd3fc
   for reac-pw/fuzz_role (image A and image B): module paths changed; its lines 17-45 (in_roP, arodata_okP,
   ro_below_ofl, ro_spares, arodata_ok_journalP) are taken as they stand; its lines 46-107 (afobj, apost_base,
   apost_baseF, fxr, apost_baseF_continue) are left out and replaced by the role definitions below (rl_fxk in place of
   fxr, for role's float registers; rl_wcell in place of afobj, for a cell that lies on the stack or in a side-stack
   frame); the role constants, the string predicate rl_cstr and the read-only cell predicate rl_ro_cells are new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgBase.v at 0de5d668c87e for reac-pw/fuzz_rate
   (image A and image B): module paths changed; in_roP .. arodata_ok_journalP taken as they stand; the prefix rl_
   becomes rt_ (rl_fxk, rl_cstr, rl_ro_cells, rl_wcell, rl_fresh_awr(_n), rl_x, rl_xv, rl_loc, rl_at, rl_cut, rl_fsh,
   rl_inw); the role constants are replaced by rate's (rt_len, rt_bl and the texts the checks compare, from the shared
   Pod model); role's quantity record rl_env becomes rt_renv with rate's three blocks and seven header values, and
   rl_x gains their constructors; rt_i32tab (a table of 4-byte values read by instrumented loads) and rt_rom_kept
   (the read-only image as every call keeps it: the released fuzz_boxreg lib/A/Rt/SnprintfDef.v asn_rom_kept) with
   its two sources are new. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_disco/lib/A/Prog/DiscoRo.v and
   proofs/libreac/fuzz_boxreg/lib/A/Prog/BoxRo.v at origin/ossv/recipes 09c6822d886 (img_shadow_vis, globs_marked,
   ro_unowned, ro_usable_glob, ro_hull, ro_read_ok_glob) become rt_img_shadow_vis, rt_globs_marked, rt_ro_unowned,
   rt_glob_usable, rt_img_hull and rt_glob_read_ok, with the image's range as parameters in place of IMG_LO / IMG_TOP;
   rt_img_unowned, rt_aview_mbyte, rt_cstr_at, rt_i32tab_at, rt_u64tab_at, rt_img_bytes, rt_img_val, rt_ro_mbyte,
   rt_val_of_ro, rt_bytes_of_ro, rt_rom_pinned, rt_rom_view_of and rt_glob_of_b are new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgBase.v, with its module names changed; 337 of its 373 lines of code are new or changed and 301 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgDcsvDefs.v at 693242f63d54 and the statement
   text of proofs/reac-pw/fuzz_rate/lib/A/Rt/SnprintfRateDef.v at the same commit, for image B
   (fuzz_rate.asan-ubsan): the image is images.AsanUbsan; the entry, the code table (264 words), the callee entries,
   the return addresses, the loop head, the tail, the .got and runtime cells and the frame descriptor are image B's;
   the cut state names image B's cells of the real frame (buflen R+24, buf R+32, F R+8 / R+16 / R+112, tmp R+48,
   cell R+72, "," R+40, "" R+64) and registers (the frame's shadow address in s2, the format in s9, ~tmp in a3); the
   image facts are lib/AU/RtPgSiteB.v's rate_B_img_facts; the snprintf wrapper's contract text is
   SnprintfRateDef.v's rate_snprintf_sd_realizes, unchanged, stated here at image B's string addresses (equal to
   image A's) with image B's trampoline as its entry. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address below is measured on its
   unstripped twin sha256 a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, whose loaded bytes are
   the same): the definitions the walk of reac_rate_drivable_csv (0x842d8, 1056 bytes, 264 instructions) is split
   over. Statement text only: proves no function (kind: segment lemma, its parts).

   THE CODE, in the three parts the walk is split into:

   PART 1, the prologue 0x842d8 .. 0x84474 (to the loop head 0x84478):
     0x842d8 `addi sp,sp,-224`; 0x842dc `sd zero,0(sp)` (the stack probe); 0x842e0 .. 0x84310 the 13 saves of ra
     and s0 .. s11 at [S - 104, S) for S the entry sp; 0x84314 `addi s0,sp,224` (s0 = S); 0x84318
     `andi sp,sp,-32`, so the realigned base is R = 32 * ((S - 224) / 32); 0x8431c `mv s1,sp`;
     0x84320 / 0x84324 buflen and buf into the cells R+24 and R+32; 0x84328 .. 0x8433c the two .got cells
     0x9c1c8 and 0x9c170 give the use-after-return cell 0xa4f40 (its 4-byte value is 1) and the shadow-offset
     cell 0xa4f38 (its 8-byte value is the runtime's shadow offset K); 0x84340 / 0x84344 K and the mask into the
     cells R+88 and R+80; 0x84348 `beqz a2` is NOT taken (the flag is 1), so 0x8434c `li a0,128` and 0x84350
     `jal __asan_stack_malloc_1` (0x3cfd4) take a side-stack frame F of class 1 (128 bytes), ra = 0x84354;
     0x84354 `j 0x8435c`; 0x8435c `mv a4,a0`, 0x84360 F into the cell R+16, and 0x84364 `bnez a0,0x84384` is
     taken (F >= 4096), so the real-stack arm 0x84368 .. 0x84380 (the probe loop) is DEAD; 0x84384 .. 0x84474
     fill the cells R+112 (F), R+72 (cell = F + 96), R+48 (tmp = F + 32), R+40 (","), R+64 (""), R+8 (F) and
     R+56 (48000), write the frame header F+0 (the magic 0x41b58ab3), F+8 (the descriptor 0x16f96) and F+16
     (0x842d8, the function's own address), set tmp[0] = 0 at F+32, and write the frame's 16 shadow bytes at
     (F >> 3) + K: 0xf1 0xf1 0xf1 0xf1 (the header and its redzone), 0x00 x 4 (tmp[32] at F+32, in scope),
     0xf2 x 4 (the middle redzone), 0xf8 0xf8 (cell[16] at F+96, out of scope), 0xf3 0xf3 (the right redzone);
     s5 = 0 (len), s11 = 3, s6 = 44100, s8 = 96000, s7 = s10 = 0x216a0 (the table `ordered`), s9 = 0x216c0
     (the format), s2 = (F >> 3) + K, and 0x84420 `not a3,t4` a3 = ~tmp (the operand of the two
     pointer-overflow tests of the loop).

   PART 2, the loop body, three passes i = 0, 1, 2 from the head 0x84478:
     0x84478 .. 0x84488 the instrumented check of the 4-byte load at s10 = 0x216a0 + 4 i (its shadow byte at
     (s10 >> 3) + K, the `bnez` and the slow block 0x84568 .. 0x84570); 0x8448c `lw a4,0(s7)` reads ordered[i];
     0x84490 .. 0x844b8 the compare chain against 44100 / 96000 / 48000 gives a0 = 1 / 4 / 2; 0x844bc / 0x844c0
     `ld a1,80(s1)` and `and a0,a0,a1` test the bit of the mask; 0x844c4 `beqz a0` skips the pass.
     On a set bit: 0x844c8 `mv s4,a3` (s4 = ~tmp); 0x844cc / 0x844d0 put the two shadow bytes of cell to 0 (cell
     in scope); 0x844d4 / 0x844d8 / 0x844dc choose a3 = "" (0x21700) while len = 0 and "," (0x216e0) after;
     0x844e0 .. 0x844ec call the snprintf wrapper (a0 = cell, a1 = 16, a2 = "%s%d" 0x216c0, a3 = the separator,
     a4 = ordered[i]) through the trampoline 0x4222c, ra = 0x844f0; 0x844f0 `bltz a0` and 0x84504 `bltu 31,s3`
     are NOT taken (the answer is 5 or 6 bytes and len + it is at most 17); 0x84500 `mv a3,s4`;
     THE TRAP BRANCH 0x84508 `bltu a3,s5` (to the `unimp` 0x846e8: tmp + len would wrap) is NOT taken;
     0x8450c .. 0x84518 call __asan_memcpy(tmp + len, cell, n) (0x518b8) with ra = 0x8451c; 0x8451c `ld a0,48(s1)`;
     THE TRAP BRANCH 0x84520 `bltu s4,s3` (tmp + len + n would wrap) is NOT taken; 0x84524 `mv a3,s4`;
     0x8452c `sb zero,0(a0)` writes the NUL at tmp + len + n (no instrumented check: the compiler elided it);
     0x84548 / 0x8454c put the two shadow bytes of cell back to 0xf8; 0x84550 len := len + n.
     Both paths: 0x84554 / 0x84558 / 0x8455c decrement s11 and advance s10 and s7 by 4; 0x84560 `bnez s11` goes
     back to the head, 0x84564 `j 0x8457c` leaves the loop.

   PART 3, the tail 0x8457c .. 0x846e4 (the return):
     0x8457c `ld a0,24(s1)` (a0 = buflen); 0x84580 `beqz a0,0x845e4` skips the copy when buflen = 0; else
     0x84584 .. 0x84590 copy = min(len, buflen - 1) (unsigned `bltu`), 0x84594 `ld s4,32(s1)` (buf), 0x84598 ..
     0x845a4 call __asan_memcpy(buf, tmp, copy) with ra = 0x845a8; 0x845a8 `add a0,s4,s3` (buf + copy);
     THE TRAP BRANCHES 0x845ac `bltu a0,s4` (buf + copy wraps), 0x845c0 `beqz a1` after `snez` / `seqz` / `xor`
     (exactly one of buf, buf + copy is 0) and 0x845c8 `beqz a1` (buf is 0) are NOT taken; 0x845cc .. 0x845dc the
     instrumented check of the 1-byte store at buf + copy (its slow block 0x846ec / 0x846f0), 0x845e0
     `sb zero,0(a0)` the NUL; 0x845e4 .. 0x845f4 put tmp's four shadow bytes to 0xf8 (out of scope); 0x845f8 ..
     0x84604 write the retirement word 0x45e0360e at F+0 (F from the cell R+8); 0x84608 / 0x8460c `ld a0,16(s1)`,
     `beqz a0` is NOT taken (F >= 4096), so the F = 0 arm 0x84664 .. 0x846a0 is DEAD; 0x84614 .. 0x84654 put all
     16 shadow bytes of the frame to 0xf5 (released); 0x84658 / 0x8465c read the flag pointer at F + 120 and write
     0 to the flag byte: the inline release of the frame (no __asan_stack_free_1 call); 0x846a4 a0 = len;
     0x846a8 .. 0x846e0 the 13 restores; 0x846e4 `ret`.

   WHY NO ERROR PATH IS REACHED: the two instrumented checks are the only ones. The first reads the shadow byte
   of the 4-byte table entry, which the contract's rt_i32tab premise marks usable; the second reads the shadow
   byte of buf + copy, which the contract's range_addressable premise marks usable, with copy < buflen. Both are
   stepped through the kernel's token engine (lib/Reusable/YCbn.v), which decides the `bnez` and its slow block
   from those premises, so neither call of an __asan_report_ entry at 0x84578 or 0x846f4 is ever stepped.
   WHY NO TRAP IS REACHED: the five branches to the `unimp` 0x846e8 compare values the cut state bounds: tmp, cell
   and the frame lie in the side stack below 2^47, len + n <= 17 (RateCsv.csv_prefix_length), 0 < buf and
   buf + buflen <= 2^63 (the contract's premise). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YK0o YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Model Layout RateCfg RateCsv.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB RtPgSiteB RtPgStepsB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* image B's loaded segments; an abbreviation, so every statement names the image module's own term *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* ======================================== the image ======================================== *)
Definition B_DCSV : Z := 0x842d8.         (* reac_rate_drivable_csv *)
Definition DC_NW : nat := 264%nat.        (* its 264 4-byte instruction words *)
Definition dc_tbl : ctable := build_table rsegs B_DCSV DC_NW TEmpty.
Lemma dc_tbl_ok : table_ok rsegs dc_tbl.
Proof. apply build_table_ok0. unfold B_DCSV. lia. Qed.

Definition B_SM1 : Z := 0x3cfd4.          (* __asan_stack_malloc_1 *)
Definition B_MEMCPY : Z := 0x518b8.       (* __asan_memcpy (RtPgStepsB.RTSB_MEMCPY) *)
Definition DC_RA_SM1 : Z := 0x84354.      (* the frame call's return address *)
Definition DC_RA_SNP : Z := 0x844f0.      (* the snprintf call's *)
Definition DC_RA_CPY1 : Z := 0x8451c.     (* the loop's __asan_memcpy *)
Definition DC_RA_CPY2 : Z := 0x845a8.     (* the tail's __asan_memcpy *)
Definition DC_LOOP : Z := 0x84478.        (* the loop head *)
Definition DC_TAIL : Z := 0x8457c.        (* the first pc after the loop *)
Definition DC_TRAP : Z := 0x846e8.        (* the `unimp` the five trap branches go to *)
Definition DC_CID : Z := 1.               (* the side-stack frame's class *)
Definition B_ORD : Z := 0x216a0.          (* reac_rate_drivable_csv.ordered, 3 x 4 bytes *)
Definition B_GOT_SHADOW : Z := 0x9c170.
Definition B_SHADOW_CELL : Z := 0xa4f38.
Definition B_GOT_UAR : Z := 0x9c1c8.
Definition B_UAR_CELL : Z := 0xa4f40.
Definition DC_FRAME_MAGIC : Z := 0x41b58ab3.
Definition DC_FRAME_DESCR : Z := 0x16f96.
Definition DC_RETIRE : Z := 0x45e0360e.
Definition DC_FSZ : Z := 128.             (* fs_frame_bytes 1 *)
Lemma dc_fsz : fs_frame_bytes DC_CID = DC_FSZ.
Proof. reflexivity. Qed.

(* The frame's 16 shadow bytes after the prologue (cell out of scope). *)
Definition dc_shA : list Z :=
  [0xf1; 0xf1; 0xf1; 0xf1; 0; 0; 0; 0; 0xf2; 0xf2; 0xf2; 0xf2; 0xf8; 0xf8; 0xf3; 0xf3].

(* The 13 registers the prologue saves at S - 8 - 8 j, in the order it saves them. *)
Definition dc_saved : list (bv 5) := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

(* ======================= the snprintf wrapper's contract (SnprintfRateDef.v's text) =======================
   The one call the program makes, reac_rate_drivable_csv's `jal 0x4222c` at 0x844ec (reac_rate_cfg.c:60,
   snprintf(cell, sizeof cell, "%s%d", sep, ordered[i])): a0 = the cell (the cell R+72 holds), a1 = 16, a2 = the
   format "%s%d" (.str.5 0x216c0, a 5-byte registered global whose bytes are 25 73 25 64 00, in s9), a3 = the
   separator ("" = .str.7 0x21700 while no rate has been written, "," = .str.6 0x216e0 after), a4 = ordered[i]
   (one of 44100, 48000, 96000 from reac_rate_drivable_csv.ordered 0x216a0, loaded by `lw`, so sign-extended).
   The entry is __interceptor_trampoline_snprintf 0x4222c. The text below is lib/A/Rt/SnprintfRateDef.v's, word for
   word: image B's string addresses and bytes are image A's; only the entry differs, and it is the parameter pc. *)
Definition SNP_TRAMP : Z := 0x4222c.  (* __interceptor_trampoline_snprintf *)
Definition SNP_FMT : Z := 0x216c0.    (* .str.5: "%s%d" *)
Definition SNP_COMMA : Z := 0x216e0.  (* .str.6: "," *)
Definition SNP_EMPTY : Z := 0x21700.  (* .str.7: "" *)
Definition SNP_SIZE : Z := 16.        (* sizeof cell *)

Definition SNP_FMT_BYTES : list Z := [37; 115; 37; 100].
Definition SNP_STK : Z := 2 * ESTACK.
(* what the call prints: the separator, then "%d" of the rate (RateCsv.csv_dec, the printf model's pf_dec) *)
Definition snp_text (sep : list Z) (v : Z) : list Z := sep ++ RateCsv.csv_dec v.
(* what it leaves at the destination: the first SNP_SIZE - 1 bytes of the text and a NUL *)
Definition snp_dest_bytes (T : list Z) : list Z := firstn (Z.to_nat (SNP_SIZE - 1)) T ++ [0].

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.

(* lib/A/RtPgBase.v rt_cstr: a NUL-terminated string s at a, in the image, with its len + 1 bytes marked usable and
   their shadow bytes readable *)
Definition snp_cstr (H : word -> bool) (mem : word -> option byte) (a : Z) (s : list Z) : Prop :=
(forall i, 0 <= i < Z.of_nat (length s) -> aview segs H mem (a + i) = Some (nth (Z.to_nat i) s 0)) /\
aview segs H mem (a + Z.of_nat (length s)) = Some 0 /\
Forall (fun b => 0 < b < 256) s /\
0 < a /\ a + Z.of_nat (length s) + 1 <= 2 ^ 63 /\
(forall i, 0 <= i <= Z.of_nat (length s) -> in_img segs (a + i)) /\
amem_range a (Z.of_nat (length s) + 1) /\
range_addressable (aview segs H mem) SHADOW_OFF a (Z.of_nat (length s) + 1) /\
shadow_hull_vis (aview segs H mem) a (Z.of_nat (length s) + 1).

(* lib/A/RtPgBase.v rt_rom_kept: a byte of a read-only segment that is neither an owned static nor an errno byte
   reads as the image's byte *)
Definition snp_rom_kept (W : world segs) (mem : word -> option byte) : Prop :=
forall a, in_rom segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
aview segs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)).

Definition rate_snprintf_sd_realizes (pc : Z) : Prop :=
forall ly S W regs mem md (d x v : Z) (sep : list Z),
ecall_pre segs B ly S W regs mem md ->
ly_stk_lo ly + SNP_STK <= spZ regs ->
(forall a, spZ regs - SNP_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 d -> getr regs 11 = w64 SNP_SIZE -> getr regs 12 = w64 SNP_FMT -> getr regs 13 = w64 x ->
(* the separator: "" or "," *)
(x = SNP_EMPTY /\ sep = [] \/ x = SNP_COMMA /\ sep = [44]) ->
(* the rate: a 32-bit int, sign-extended in a4 *)
-2 ^ 31 <= v < 2 ^ 31 -> bv_unsigned (getr regs 14) mod 2 ^ 32 = v mod 2 ^ 32 ->
(* the format and the separator as the caller holds them *)
snp_cstr (w_H W) mem SNP_FMT SNP_FMT_BYTES -> snp_cstr (w_H W) mem x sep ->
snp_rom_kept W mem ->
(* the destination: the 16 bytes of the cell, outside the window and outside the image *)
0 < d -> d + SNP_SIZE + 8 <= 2 ^ 63 ->
dest_ok segs B ly S W regs mem d SNP_SIZE -> amem_range d (SNP_SIZE + 8) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF d SNP_SIZE ->
shadow_hull_vis (aview segs (w_H W) mem) d SNP_SIZE ->
(d + SNP_SIZE <= spZ regs - SNP_STK \/ spZ regs <= d) ->
(d + SNP_SIZE <= YImgTop.IMG_LO \/ YImgTop.IMG_TOP <= d) ->
(* rounding mode 0 at entry *)
YK0o.frm_zero (@fp_csr fx) ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists (fx' : YK11.FPState) regs' mem' md',
c' = @cfg_at fx' segs (raZ regs) regs' mem' md' /\
(forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@fp_regs fx') k = Sem.reg_get (@fp_regs fx) k) /\
YK0o.frm_zero (@fp_csr fx') /\
AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (Z.of_nat (length (snp_text sep v))) /\
(forall i, 0 <= i < Z.of_nat (length (snp_dest_bytes (snp_text sep v))) ->
 aview segs (w_H W) mem' (d + i) = Some (nth (Z.to_nat i) (snp_dest_bytes (snp_text sep v)) 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + Z.of_nat (length (snp_dest_bytes (snp_text sep v)))) ->
 ~ (spZ regs - SNP_STK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
End s.

(* ================================== the value model ==================================
   The separator the code picks (reac_rate_cfg.c:60 `len ? "," : ""`) and the text one pass appends: the model's
   own csv_step, written as the two pieces the walk sees (the snprintf answer is sep ++ "%d" of the rate). *)
Definition dc_sep (L : list Z) : list Z := match L with [] => [] | _ :: _ => [44] end.
Definition dc_T (mask : Z) (i : nat) : list Z :=
  snp_text (dc_sep (RateCsv.csv_prefix mask i)) (nth i RateCfg.closed_list 0).

Lemma dc_step_set : forall mask i, Z.testbit mask (Z.of_nat i) = true ->
  RateCsv.csv_prefix mask (S i) = RateCsv.csv_prefix mask i ++ dc_T mask i.
Proof.
  intros mask i Hb. rewrite RateCsv.csv_prefix_S, Hb. unfold dc_T, snp_text, dc_sep.
  destruct (RateCsv.csv_prefix mask i); rewrite app_assoc; reflexivity.
Qed.

Lemma dc_step_clear : forall mask i, Z.testbit mask (Z.of_nat i) = false ->
  RateCsv.csv_prefix mask (S i) = RateCsv.csv_prefix mask i.
Proof. intros mask i Hb. rewrite RateCsv.csv_prefix_S, Hb. reflexivity. Qed.

(* The three rates: ordered[i] = closed_list[i], and "%d" of each is 5 digits. *)
Lemma dc_rate_vals : nth 0 RateCfg.closed_list 0 = 44100 /\ nth 1 RateCfg.closed_list 0 = 48000 /\
  nth 2 RateCfg.closed_list 0 = 96000.
Proof. repeat split; reflexivity. Qed.

Lemma dc_T_len : forall mask i, (i < 3)%nat -> 5 <= Z.of_nat (length (dc_T mask i)) <= 6.
Proof.
  intros mask i Hi. unfold dc_T, snp_text, dc_sep. rewrite length_app.
  assert (Hd : length (RateCsv.csv_dec (nth i RateCfg.closed_list 0)) = 5%nat).
  { destruct i as [|[|[|i]]]; [| | |lia]; reflexivity. }
  rewrite Hd. destruct (RateCsv.csv_prefix mask i); cbn [length]; lia.
Qed.

Lemma dc_len_le : forall mask i, 0 <= mask -> (i <= 3)%nat ->
  0 <= Z.of_nat (length (RateCsv.csv_prefix mask i)) <= 17.
Proof.
  intros mask i Hm Hi. pose proof (RateCsv.csv_prefix_length mask i Hi Hm) as H. lia.
Qed.

(* Every byte of a pass's text is a digit or a comma: no NUL, each below 256. *)
Lemma dc_T_chars : forall mask i, (i < 3)%nat -> Forall (fun c => 44 <= c <= 57) (dc_T mask i).
Proof.
  intros mask i Hi. unfold dc_T, snp_text. apply Forall_app. split.
  - unfold dc_sep. destruct (RateCsv.csv_prefix mask i); [apply Forall_nil|].
    apply Forall_cons; [lia | apply Forall_nil].
  - destruct i as [|[|[|i]]]; [| | |lia];
    [ change (RateCsv.csv_dec (nth 0 RateCfg.closed_list 0)) with [52; 52; 49; 48; 48]
    | change (RateCsv.csv_dec (nth 1 RateCfg.closed_list 0)) with [52; 56; 48; 48; 48]
    | change (RateCsv.csv_dec (nth 2 RateCfg.closed_list 0)) with [57; 54; 48; 48; 48] ];
    repeat (apply Forall_cons; [lia|]); apply Forall_nil.
Qed.

(* The snprintf answer is written whole: |T| <= 6 < 15, so firstn 15 T = T. *)
Lemma dc_dest_bytes : forall mask i, (i < 3)%nat ->
  snp_dest_bytes (dc_T mask i) = dc_T mask i ++ [0].
Proof.
  intros mask i Hi. unfold snp_dest_bytes, SNP_SIZE.
  pose proof (dc_T_len mask i Hi) as Hl. change (Z.to_nat (16 - 1)) with 15%nat.
  rewrite firstn_all2 by lia. reflexivity.
Qed.

Lemma dc_list3 : forall mask, RateCsv.csv_list mask = RateCsv.csv_prefix mask 3.
Proof. reflexivity. Qed.

(* The separator of a pass is "" exactly while nothing has been written. *)
Lemma dc_sep_empty : forall L, L = [] -> dc_sep L = [].
Proof. intros L ->. reflexivity. Qed.
Lemma dc_sep_comma : forall L, L <> [] -> dc_sep L = [44].
Proof. intros [|x L] H; [exfalso; exact (H eq_refl) | reflexivity]. Qed.

(* The float states this walk runs at. The snprintf wrapper returns at a state that keeps every float register
   but f10 and has a zero rounding mode, and the walk goes on from there, so each cut state carries
   `rt_fxk [10] fx fq` and the parts chain them. *)
Lemma dc_fxk_refl : forall ks fq, YK0o.frm_zero (@fp_csr fq) -> rt_fxk ks fq fq.
Proof. intros ks fq H. split; [intros; reflexivity | exact H]. Qed.

Lemma dc_fxk_trans : forall ks f1 f2 f3, rt_fxk ks f1 f2 -> rt_fxk ks f2 f3 -> rt_fxk ks f1 f3.
Proof.
  intros ks f1 f2 f3 [A1 _] [A2 B2]. split; [intros k Hk; rewrite (A2 k Hk); exact (A1 k Hk) | exact B2].
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

(* ============================ the context of one call ============================ *)
Record dcx := DCx {
dx_STK : Z; dx_sp0 : Z; dx_FP : list (Z * Z);
dx_ly : alayout; dx_S : astate; dx_W0 : world rsegs; dx_mem0 : word -> option byte; dx_md0 : Model;
dx_own : list (Z * Z); dx_k : Z;
dx_lyc : alayout; dx_Sc : astate; dx_W : world rsegs; dx_memc : word -> option byte; dx_mdc : Model;
dx_regs : bvmap 5 word; dx_mask : Z; dx_buf : Z; dx_n : Z }.

(* the entry sp and the realigned base of the real frame *)
Definition dx_S0 (c : dcx) : Z := spZ (dx_regs c).
Definition dx_R (c : dcx) : Z := 32 * ((dx_S0 c - 224) / 32).

(* The premises of RtPgCSpec.rt_drivable_csv_specX at image B's constants, as one predicate. *)
Definition dc_pre (c : dcx) : Prop :=
rt_cpre rsegs B (dx_STK c) (dx_sp0 c) (dx_FP c) (dx_ly c) (dx_S c) (dx_W0 c) (dx_mem0 c) (dx_md0 c)
  (dx_own c) (dx_k c) T_dcsv_STK (dx_regs c) (dx_lyc c) (dx_Sc c) (dx_W c) (dx_memc c) (dx_mdc c) /\
getr (dx_regs c) 10 = w64 (dx_mask c) /\ 0 <= dx_mask c < 2 ^ 64 /\
getr (dx_regs c) 11 = w64 (dx_buf c) /\ getr (dx_regs c) 12 = w64 (dx_n c) /\ 0 <= dx_n c <= 23 /\
(0 < dx_n c ->
 0 < dx_buf c /\ dx_buf c + dx_n c <= 2 ^ 63 /\
 (exists m, In (dx_buf c, m) (ablocks B (dx_lyc c) (dx_Sc c)) /\ ~ In (dx_buf c, m) (ablocks B (dx_ly c) (dx_S c)) /\
  dx_n c <= m) /\
 range_addressable (aview rsegs (w_H (dx_W c)) (dx_memc c)) SHADOW_OFF (dx_buf c) (dx_n c) /\
 shadow_hull_vis (aview rsegs (w_H (dx_W c)) (dx_memc c)) (dx_buf c) (dx_n c) /\ amem_range (dx_buf c) (dx_n c) /\
 (dx_buf c + dx_n c <= dx_S0 c - T_dcsv_STK \/ dx_S0 c <= dx_buf c)) /\
count_cid DC_CID (frames (dx_Sc c)) < fs_frames DC_CID /\
rt_cstr rsegs (w_H (dx_W c)) (dx_memc c) SNP_FMT STR_FMT_SD /\
rt_cstr rsegs (w_H (dx_W c)) (dx_memc c) SNP_COMMA STR_COMMA /\
rt_cstr rsegs (w_H (dx_W c)) (dx_memc c) SNP_EMPTY STR_EMPTY /\
rt_i32tab rsegs (w_H (dx_W c)) (dx_memc c) B_ORD RateCfg.closed_list /\
rt_rom_kept rsegs B (dx_W c) (dx_memc c) /\
YK0o.frm_zero (@fp_csr fx).

(* ============================ the state at a cut ============================
   dc_core holds at the loop head and at the tail: the journal from the function's entry with the frame (1, pos)
   on its own list, the state facts the post needs, the registers the tail reads, the cells of the real frame,
   the 13 saves, the frame's flag pointer, tmp's bytes, the frame's shadow, and the image facts the premises
   carry, at this state. *)
Definition dc_core (c : dcx) (i : nat) (pos : Z) (fq : YK11.FPState)
(S1 : astate) (W1 : world rsegs) (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
let R := dx_R c in let S0 := dx_S0 c in
let F := frame_addr (dx_lyc c) DC_CID pos in
let shF := shadow_addr F in
let len := Z.of_nat (length (RateCsv.csv_prefix (dx_mask c) i)) in
(i <= 3)%nat /\
rt_fxk [10] fx fq /\
(* the journal and the state *)
ajournal rsegs B (dx_STK c) (dx_sp0 c) (dx_FP c) (dx_ly c) (dx_S c) (dx_W0 c) (dx_mem0 c) (dx_md0 c)
  ((DC_CID, pos) :: dx_own c) (dx_lyc c) S1 W1 mem1 md1 (dx_k c) /\
frames S1 = (DC_CID, pos) :: frames (dx_Sc c) /\ ~ In (DC_CID, pos) (frames (dx_Sc c)) /\
(* the call state with only the side stack's own field changed: the frame's allocation and its release are both
   a set_fs (YG01.v stack_malloc_post, stack_free_state), and nothing else here touches the state. This is what
   carries the post's meter clause mo_le MT Sc S2 0 through the release (YC5d.v ameter_fs_laws). *)
(exists f, S1 = set_fs f (dx_Sc c)) /\
(* the frame's position, as the model gives it (YG01.v stack_malloc_post). With it, lib/Reusable/YF0v.v
   own_free_frame and own_free_frame_shadow say that every byte of the frame and of its 16 shadow bytes is
   `aowned B lyc Sc`, which is what the kept conjunct and the post's E need for the bytes this walk writes
   inside the frame. *)
0 <= pos < fs_frames DC_CID /\
ablocks B (dx_lyc c) S1 = ablocks B (dx_lyc c) (dx_Sc c) /\
st_nev S1 = st_nev (dx_Sc c) /\ st_secs S1 = st_secs (dx_Sc c) /\ st_chunks S1 = st_chunks (dx_Sc c) /\
same_io (dx_mdc c) md1 /\ wle (dx_W c) W1 /\
(* the geometry *)
R mod 32 = 0 /\ S0 - 240 <= R <= S0 - 224 /\
(* the registers the tail reads: sp, gp, tp, s0 = S, s1 = R, s2 = the frame's shadow address, s5 = len *)
getr regs1 2 = w64 R /\ getr regs1 3 = w64 (as_gp B) /\ getr regs1 4 = w64 (as_tp B) /\
getr regs1 8 = w64 S0 /\ getr regs1 9 = w64 R /\ getr regs1 18 = w64 shF /\ getr regs1 21 = w64 len /\
(* the cells of the real frame *)
val_mem rsegs (mrestrict (w_H W1) mem1) (R + 8) 8 F /\
val_mem rsegs (mrestrict (w_H W1) mem1) (R + 16) 8 F /\
val_mem rsegs (mrestrict (w_H W1) mem1) (R + 24) 8 (dx_n c) /\
val_mem rsegs (mrestrict (w_H W1) mem1) (R + 32) 8 (dx_buf c) /\
val_mem rsegs (mrestrict (w_H W1) mem1) (R + 40) 8 SNP_COMMA /\
val_mem rsegs (mrestrict (w_H W1) mem1) (R + 48) 8 (F + 32) /\
val_mem rsegs (mrestrict (w_H W1) mem1) (R + 56) 8 48000 /\
val_mem rsegs (mrestrict (w_H W1) mem1) (R + 64) 8 SNP_EMPTY /\
val_mem rsegs (mrestrict (w_H W1) mem1) (R + 72) 8 (F + 96) /\
val_mem rsegs (mrestrict (w_H W1) mem1) (R + 80) 8 (dx_mask c) /\
val_mem rsegs (mrestrict (w_H W1) mem1) (R + 88) 8 SHADOW_OFF /\
val_mem rsegs (mrestrict (w_H W1) mem1) (R + 112) 8 F /\
(* the 13 saved registers *)
(forall j, (j < 13)%nat -> val_mem rsegs (mrestrict (w_H W1) mem1) (S0 - 8 - 8 * Z.of_nat j) 8
   (bv_unsigned (getr (dx_regs c) (nth j dc_saved 0%bv)))) /\
(* the frame: its flag pointer, tmp's bytes, its 16 shadow bytes, its presence *)
rdword (aview rsegs (w_H W1) mem1) (F + DC_FSZ - 8) = Some (flag_addr (dx_lyc c) DC_CID pos) /\
garr8 rsegs (mrestrict (w_H W1) mem1) (F + 32) (RateCsv.csv_prefix (dx_mask c) i ++ [0]) /\
rt_fsh rsegs (w_H W1) mem1 F dc_shA /\
(forall a, F <= a < F + DC_FSZ -> apresent (w_H W1) mem1 a) /\
(forall a, shF <= a < shF + DC_FSZ / 8 -> apresent (w_H W1) mem1 a) /\
(* the image facts the premises carry, at this state *)
rt_cstr rsegs (w_H W1) mem1 SNP_FMT STR_FMT_SD /\
rt_cstr rsegs (w_H W1) mem1 SNP_COMMA STR_COMMA /\
rt_cstr rsegs (w_H W1) mem1 SNP_EMPTY STR_EMPTY /\
rt_i32tab rsegs (w_H W1) mem1 B_ORD RateCfg.closed_list /\
rt_rom_kept rsegs B W1 mem1 /\
(0 < dx_n c -> range_addressable (aview rsegs (w_H W1) mem1) SHADOW_OFF (dx_buf c) (dx_n c) /\
   shadow_hull_vis (aview rsegs (w_H W1) mem1) (dx_buf c) (dx_n c) /\
   (forall a, dx_buf c <= a < dx_buf c + dx_n c -> apresent (w_H W1) mem1 a)) /\
(* every byte outside the function's stack window and the bytes the runtime owned at the call is as at the call *)
(forall a, 0 <= a < 2 ^ 64 -> ~ (dx_S0 c - T_dcsv_STK <= a < dx_S0 c) -> ~ aowned B (dx_lyc c) (dx_Sc c) a ->
   aview rsegs (w_H W1) mem1 a = aview rsegs (w_H (dx_W c)) (dx_memc c) a).

(* At the loop head the loop registers hold their pass values too: s6 = 44100, s7 = s10 = ordered + 4 i,
   s8 = 96000, s9 = the format, s11 = 3 - i, and a3 = ~tmp (the 64-bit complement of F + 32), which the pass
   saves in s4 and reads in its two trap tests. *)
Definition dc_loop (c : dcx) (i : nat) (pos : Z) (fq : YK11.FPState)
(S1 : astate) (W1 : world rsegs) (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
dc_core c i pos fq S1 W1 regs1 mem1 md1 /\ (i < 3)%nat /\
getr regs1 13 = w64 (2 ^ 64 - 1 - (frame_addr (dx_lyc c) DC_CID pos + 32)) /\
getr regs1 22 = w64 44100 /\ getr regs1 24 = w64 96000 /\ getr regs1 25 = w64 SNP_FMT /\
getr regs1 23 = w64 (B_ORD + 4 * Z.of_nat i) /\ getr regs1 26 = w64 (B_ORD + 4 * Z.of_nat i) /\
getr regs1 27 = w64 (3 - Z.of_nat i).

(* The config at a cut. *)
Definition dc_loop_cfg (c : dcx) (i : nat) : world rsegs -> config -> Prop :=
fun W1 cfg => exists (fq : YK11.FPState) pos S1 regs1 mem1 md1,
cfg = mkCfg (@mkst fq regs1 (w64 DC_LOOP) mem1 (seg_rom rsegs)) md1 /\
dc_loop c i pos fq S1 W1 regs1 mem1 md1.

Definition dc_tail_cfg (c : dcx) : world rsegs -> config -> Prop :=
fun W1 cfg => exists (fq : YK11.FPState) pos S1 regs1 mem1 md1,
cfg = mkCfg (@mkst fq regs1 (w64 DC_TAIL) mem1 (seg_rom rsegs)) md1 /\
dc_core c 3 pos fq S1 W1 regs1 mem1 md1.

Definition dc_next (c : dcx) (i : nat) : world rsegs -> config -> Prop :=
match i with 2%nat => dc_tail_cfg c | _ => dc_loop_cfg c (S i) end.

(* The post of the whole call: RtPgCSpec.rt_cpost_o at image B's constants. *)
Definition dc_post (c : dcx) : world rsegs -> config -> Prop :=
rt_cpost_o rsegs B MT (dx_STK c) (dx_sp0 c) (dx_FP c) (dx_ly c) (dx_S c) (dx_W0 c) (dx_mem0 c) (dx_md0 c)
  (dx_own c) (dx_k c) T_dcsv_STK (dx_regs c) (dx_lyc c) (dx_Sc c) (dx_W c) (dx_memc c) (dx_mdc c)
  (rt_fxk [10] fx)
  (fun x => aowned B (dx_lyc c) (dx_Sc c) x \/ (0 < dx_n c /\ dx_buf c <= x < dx_buf c + dx_n c))
  (fun W2 regs2 mem2 =>
     getr regs2 10 = w64 (Z.of_nat (length (RateCsv.csv_list (dx_mask c)))) /\
     (0 < dx_n c -> garr8 rsegs (mrestrict (w_H W2) mem2) (dx_buf c)
        (RateCsv.csv_cut (RateCsv.csv_list (dx_mask c)) (dx_n c) ++ [0]))).

(* ============================ the three parts ============================ *)
Definition dc_pro_stmt : Prop :=
forall c : dcx, dc_pre c ->
SRr rsegs (dx_W c) (cfg_at rsegs B_DCSV (dx_regs c) (dx_memc c) (dx_mdc c)) (dc_loop_cfg c 0).

Definition dc_body_stmt : Prop :=
forall (c : dcx) (i : nat) (fq : YK11.FPState) pos S1 W1 regs1 mem1 md1,
dc_pre c -> dc_loop c i pos fq S1 W1 regs1 mem1 md1 ->
SRr rsegs W1 (@cfg_at fq rsegs DC_LOOP regs1 mem1 md1) (dc_next c i).

Definition dc_epi_stmt : Prop :=
forall (c : dcx) (fq : YK11.FPState) pos S1 W1 regs1 mem1 md1,
dc_pre c -> dc_core c 3 pos fq S1 W1 regs1 mem1 md1 ->
SRr rsegs W1 (@cfg_at fq rsegs DC_TAIL regs1 mem1 md1) (dc_post c).

(* ============================ the runtime this walk calls ============================
   The facts about the memory-checking runtime and the image's symbol record that the three parts use, at image
   B's values. Each is a law of the kit, of image B's core or of a sibling lane's; none is proved here (kind:
   statement text). The snprintf wrapper's is rate_snprintf_sd_realizes above at the trampoline SNP_TRAMP =
   0x4222c. *)
Definition dc_rt : Prop :=
AR_laws rsegs B /\
model_laws (as_universe B) /\
stack_malloc_progressP B /\
frame_flag_lawP rsegs B /\
astack_free_law rsegs B /\
api_env rsegs B /\
ameter_laws MT /\
ameter_fs_laws MT /\
(* image B's read-only facts in the released split (lib/AU/RtPgSiteB.v rate_B_img_facts, RtPgCSpec.rt_img_facts at
   image B's record RtPgImgB.rate_himg_B: the read ranges of the record's strings and tables hold no owned static and
   no errno byte, the registered globals are marked, the image's shadow is readable). The four facts the contract
   gives at the call are rebuilt at a later state by dc_img_carry below. *)
rate_B_img_facts rsegs B /\
(* no hypothesis is asked for the stack-protector word the musl printf core reads: the snprintf wrapper's contract
   asks nothing of its caller about it (rate_snprintf_sd_realizes above). *)
(forall fq : YK11.FPState, @astack_malloc_realizes fq rc rsegs B DC_CID) /\
(forall fq : YK11.FPState, @aintrin_realizes fq rc rsegs B OCpy B_MEMCPY) /\
(forall fq : YK11.FPState, @rate_snprintf_sd_realizes fq rc rsegs B SNP_TRAMP) /\
pc_asan_memcpy (as_code B) = B_MEMCPY /\
pc_stack_malloc (as_code B) DC_CID = B_SM1 /\
as_got_shadow B = B_GOT_SHADOW /\ as_shadow_cell B = B_SHADOW_CELL /\
as_got_uar B = B_GOT_UAR /\ as_uar_cell B = B_UAR_CELL.
End b.

(* ============================ the image facts at a later state ============================
   The contract gives the format, the two separators and the table `ordered` at the call (rt_cstr / rt_i32tab at
   memc). The class-1 frame law lets the frame call change any byte the runtime owns, so those facts cannot be
   carried across it as they stand; but their BYTES are no owned static (rate_B_img_facts), hence owned in no AR
   state (RtPgBase.rt_img_unowned), and they lie in the image, below every stack window. So the cut state's kept
   conjunct keeps them, and rate_B_cstr_at / rate_B_i32tab_at rebuild the four facts at any later AR state. *)
Section img. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis LAWS : AR_laws rsegs B.
Hypothesis IMGF : rate_B_img_facts rsegs B.

Lemma dc_in_strs : In (SNP_FMT, STR_FMT_SD) rate_B_strs /\ In (SNP_COMMA, STR_COMMA) rate_B_strs /\
  In (SNP_EMPTY, STR_EMPTY) rate_B_strs /\ In (B_ORD, RateCfg.closed_list) rate_B_i32.
Proof.
  unfold rate_B_strs, rate_B_i32.
  repeat split; cbn [In]; repeat (first [left; reflexivity | right]).
Qed.

(* The four facts at an AR state whose image bytes that are no owned static read as at a REFERENCE state where the
   four facts hold (any H0 / mem0: the call, or an earlier cut). This is the form a part uses inside a pass, where
   its reference is the cut state it started from and its own runs keep every image byte. *)
Lemma dc_img_carry_from : forall (H0 : word -> bool) mem0 ly1 S1 (W1 : world rsegs) mem1 md1,
rt_cstr rsegs H0 mem0 SNP_FMT STR_FMT_SD -> rt_cstr rsegs H0 mem0 SNP_COMMA STR_COMMA ->
rt_cstr rsegs H0 mem0 SNP_EMPTY STR_EMPTY -> rt_i32tab rsegs H0 mem0 B_ORD RateCfg.closed_list ->
AR rsegs B ly1 S1 W1 mem1 md1 ->
(forall a, in_img rsegs a -> ~ Exists (in_zr a) (as_owned_static B) ->
   aview rsegs (w_H W1) mem1 a = aview rsegs H0 mem0 a) ->
rt_cstr rsegs (w_H W1) mem1 SNP_FMT STR_FMT_SD /\
rt_cstr rsegs (w_H W1) mem1 SNP_COMMA STR_COMMA /\
rt_cstr rsegs (w_H W1) mem1 SNP_EMPTY STR_EMPTY /\
rt_i32tab rsegs (w_H W1) mem1 B_ORD RateCfg.closed_list.
Proof using IMGF.
intros H0 mem0 ly1 S1 W1 mem1 md1 Hfmt Hcom Hemp Hord HAR1 KI.
destruct dc_in_strs as (I1 & I2 & I3 & I4).
split; [|split; [|split]].
- apply (rate_B_cstr_at rsegs B SNP_FMT STR_FMT_SD ly1 S1 W1 mem1 md1 H0 mem0 IMGF I1 HAR1 Hfmt).
  intros i Hi. apply KI.
  + destruct Hfmt as (_ & _ & _ & _ & _ & Himg & _). exact (Himg i Hi).
  + exact (proj1 (rate_B_str_unowned rsegs B SNP_FMT STR_FMT_SD IMGF I1 (SNP_FMT + i) ltac:(lia))).
- apply (rate_B_cstr_at rsegs B SNP_COMMA STR_COMMA ly1 S1 W1 mem1 md1 H0 mem0 IMGF I2 HAR1 Hcom).
  intros i Hi. apply KI.
  + destruct Hcom as (_ & _ & _ & _ & _ & Himg & _). exact (Himg i Hi).
  + exact (proj1 (rate_B_str_unowned rsegs B SNP_COMMA STR_COMMA IMGF I2 (SNP_COMMA + i) ltac:(lia))).
- apply (rate_B_cstr_at rsegs B SNP_EMPTY STR_EMPTY ly1 S1 W1 mem1 md1 H0 mem0 IMGF I3 HAR1 Hemp).
  intros i Hi. apply KI.
  + destruct Hemp as (_ & _ & _ & _ & _ & Himg & _). exact (Himg i Hi).
  + exact (proj1 (rate_B_str_unowned rsegs B SNP_EMPTY STR_EMPTY IMGF I3 (SNP_EMPTY + i) ltac:(lia))).
- apply (rate_B_i32tab_at rsegs B B_ORD RateCfg.closed_list ly1 S1 W1 mem1 md1 H0 mem0 IMGF I4 HAR1 Hord).
  intros i Hi. apply KI.
  + destruct Hord as (Himg & _). exact (Himg i Hi).
  + exact (proj1 (rate_B_i32_unowned rsegs B B_ORD RateCfg.closed_list IMGF I4 (B_ORD + i) ltac:(lia))).
Qed.

Lemma dc_img_carry : forall (c : dcx) ly1 S1 (W1 : world rsegs) mem1 md1,
dc_pre B c -> AR rsegs B ly1 S1 W1 mem1 md1 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (dx_S0 c - T_dcsv_STK <= a < dx_S0 c) -> ~ aowned B (dx_lyc c) (dx_Sc c) a ->
   aview rsegs (w_H W1) mem1 a = aview rsegs (w_H (dx_W c)) (dx_memc c) a) ->
rt_cstr rsegs (w_H W1) mem1 SNP_FMT STR_FMT_SD /\
rt_cstr rsegs (w_H W1) mem1 SNP_COMMA STR_COMMA /\
rt_cstr rsegs (w_H W1) mem1 SNP_EMPTY STR_EMPTY /\
rt_i32tab rsegs (w_H W1) mem1 B_ORD RateCfg.closed_list.
Proof using LAWS IMGF.
intros c ly1 S1 W1 mem1 md1 Hpre HAR1 KE.
destruct Hpre as (HCP & _ & _ & _ & _ & _ & _ & _ & Hfmt & Hcom & Hemp & Hord & _ & _).
destruct HCP as (HJ & _ & _ & _ & _ & _ & Hwlo & Hwhi & _).
pose proof (proj1 HJ) as HARc.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hal & Hstk0 & Hceil & Hslo & _) & _).
pose proof asan_consts as (C1 & _ & _ & _ & C5).
destruct dc_in_strs as (I1 & I2 & I3 & I4).
(* an image byte that is no owned static is as at the call *)
assert (KI : forall a, in_img rsegs a -> ~ Exists (in_zr a) (as_owned_static B) ->
   aview rsegs (w_H W1) mem1 a = aview rsegs (w_H (dx_W c)) (dx_memc c) a).
{ intros a Hi Ho. pose proof (rtsb_segs_low a Hi) as Hlow. rewrite C5 in Hlow.
  apply KE.
  - lia.
  - unfold dx_S0, T_dcsv_STK, ESTACK in *. lia.
  - exact (rt_img_unowned rsegs B LAWS _ _ _ _ _ a HARc Hi Ho). }
apply (dc_img_carry_from (w_H (dx_W c)) (dx_memc c) ly1 S1 W1 mem1 md1 Hfmt Hcom Hemp Hord HAR1 KI).
Qed.
End img.

Print Assumptions dc_img_carry.
