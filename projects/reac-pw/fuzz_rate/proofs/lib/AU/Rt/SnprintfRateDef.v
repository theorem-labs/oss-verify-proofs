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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgBase.v, with its module names changed; 45 of its 67 lines of code are new or changed and 315 lines of the source are left out. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; symbols from the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1): the contract of the snprintf wrapper at the one
   call the program makes, reac_rate_drivable_csv's `jal 0x4222c` at 0x844ec (reac_rate_cfg.c:60,
   snprintf(cell, sizeof cell, "%s%d", sep, ordered[i])). Statement only: rule 24, proves no function (the proof is
   lib/AU/Rt/SnprintfRate.v rate_snprintf_sd).

   The call, read off the code (0x844d4 .. 0x844ec): a0 = the cell (`ld a0,0x48(s1)`), a1 = 16, a2 = the format "%s%d"
   (s9; .str.5 0x216c0, a 32-byte registered global whose bytes are 25 73 25 64 00), a3 = the separator ("" = .str.7 0x21700 while
   no rate has been written, "," = .str.6 0x216e0 after), a4 = ordered[i] (one of 44100, 48000, 96000 from
   reac_rate_drivable_csv.ordered 0x216a0, loaded by `lw a4,0(s7)` at 0x8448c, so sign-extended). The path:
   __interceptor_trampoline_snprintf 0x4222c (`j 0x45ae0`) -> ___interceptor_snprintf 0x45ae0 ->
   ___interceptor_vsnprintf 0x456f0 (printf_common 0x44b74 checks the format and the %s argument, REAL(vsnprintf) =
   musl vsnprintf 0x94bc4 -> __wrap_vfprintf 0x42220 -> ___interceptor_vfprintf 0x4563c -> vfprintf 0x91a98 ->
   printf_core 0x91c48 -> sn_write 0x94c90, then the check of the written range) -> return.

   The form is the kit's wrapper contracts' (YG0d.v abcmp_realizes; the released fuzz_boxreg lib/A/Rt/SnprintfDef.v
   asnprintf_realizes and fuzz_disco lib/Rt/SnShared.v sh_asnprintf_realizes): from ecall_pre and SNP_STK bytes of
   present stack below sp, an SRr to raZ regs with the same world, some float state fx' that keeps every float
   register but f10 and has a zero rounding mode, AR kept with the same ly S W, the callee-saved registers kept, the
   model's lazy backing kept, a0 = |T| for T = sep ++ RateCsv.csv_dec v, the bytes firstn 15 T ++ [0] at d, every
   other byte outside the SNP_STK window unchanged, presence kept.
   - snp_cstr is lib/A/RtPgBase.v rt_cstr's text, snp_rom_kept is RtPgBase.v rt_rom_kept's text (both: fuzz_boxreg
     SnprintfDef.v), so a caller's rt_cstr / rt_rom_kept facts are these by conversion.
   - SNP_STK = 2 * ESTACK: the walk uses 8160 bytes below sp (the wrapper frames 0x60 + 0x870 + 0x130 + 0x30 and the
     musl printf core's 5552; fuzz_disco lib/A/FMsnprintfFm.v fm_K_min_gxa).
   - The destination premises are over the 16 bytes of the cell; the call writes |T| + 1 <= 16 of them when
     |T| <= 15 (the separator has at most one byte and a rate at most 11 characters, so always here).
   - The read-only image (snp_rom_kept) gives the constants the musl printf core reads and the rest of the 8-byte word
     after each string's NUL (printf_common and the strnlen interceptor read the string's word); the stack-protector
     cells and the runtime's cells come from AR and the image (lib/AU/YD1o.v got_canary_of_arodata, canary_readable). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/Rt/SnprintfRateDef.v at 71994ff034c7, derived by derive_y.py: addresses moved from reac-pw/fuzz_rate's asan image (image A) to its asan-ubsan image (image B), the image module Asan -> AsanUbsan; the call site moved by hand to image B's (reac_rate_drivable_csv differs in image B: its `jal` to the trampoline is at 0x844ec, the argument set-up from 0x844d4) and the comment above restated for image B. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YK0o YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require RateCsv.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- image B's values at the call (measured on the pinned image and its unstripped twin) ---- *)
Definition SNP_TRAMP : Z := 0x4222c.  (* __interceptor_trampoline_snprintf: `j 0x45ae0` *)
Definition SNP_FMT : Z := 0x216c0.    (* .str.5: "%s%d" *)
Definition SNP_COMMA : Z := 0x216e0.  (* .str.6: "," *)
Definition SNP_EMPTY : Z := 0x21700.  (* .str.7: "" *)
Definition SNP_SIZE : Z := 16.        (* sizeof cell *)

(* ---- the call's text ---- *)
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
