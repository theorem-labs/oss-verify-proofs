From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog Require Import pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Prog Require Import fuzz_catalogue_row_c reac_box_pin_parse_c SlotInv.
Import ListNotations.
Open Scope Z_scope.

(** LLVMFuzzerTestOneInput of fuzz_pin.c:71-104 (508 bytes, 127 instructions at 0x12cbc in the UBSan image; frame
    80 bytes; U/FrameAPI.ENTRY). The plain contract (lib/Prog/LLVMFuzzerTestOneInput_c.v) with the UBSan numbers: the
    frame's obligation U/Prog/SlotInv.slot_goal (from U/FrameAPI.frame_ubsan), split at the cuts of U/Prog/SlotInv.v
    into S_E01, S_M01, S_X01 below, plus the n >= 2^26 run (0x12cdc `srli a2,a1,26`; 0x12ce0 `bnez a2,0x12e2c`), as one
    evt like ctrl's slot_early. The whole function promises lib_contract_g's lib_post, as in the plain build.

    UBSan checks, all on one trap site 0x12eac `unimp` (0x12eb0 is the abort call, 0x12eb4 a second `unimp`):
      0x12cf4: n >= 1 and data + 1 <= 1 (data = 0 or data + 1 wraps);   0x12d18: rest + (n - 1) wraps;
      0x12d28: rest <> 0 and rest + (n - 1) = 0, or rest = 0 and rest + (n - 1) <> 0 (pointer-overflow);
      0x12d70: phi + k wraps (`not s4,s0`; `bltu s4,s2`);   0x12d90: phi + tok wraps (in the scan);
      0x12e7c / 0x12e94: phi + tok + 1 wraps or is 2^64 - 1;   0x12ea0: want not 8-aligned (before `ld s2,8(s1)`).
    The first three are S_E01's (GV: the input block is a user block below alloc_ceiling, data >= 4096 by blocks_low,
    or n = 0); the rest are pin_mid_contract's, which its premises exclude (phi + k + 1 <= 2^64 from rw_cells; want
    is FUZZ_CATALOGUE + 0x128 i, 8-aligned: pin_spec.row_addr_mod8, 0x1c848 mod 8 = 0).
    Callee contracts (the released forms relocated to pin's UBSan image): S_E01: U/Prog/memchr_c.v (MEMCHR = 0x1ab44, called at 0x12d3c) and the
    frame's malloc_contract (ms_malloc = 0x13d04) through ctrl's U b1_malloc_call; pin_mid_contract: U/Prog/memcpy_c.v
    (0x1ac40), U/Prog/strlen_c.v (0x1b334) and the U fuzz_catalogue_row_contract, reac_box_pin_parse_contract,
    check_known/row/label_contract; S_X01: the frame's free_contract (ms_free = 0x13bc4) through ctrl's U
    b8_free_call. Statement text only: no function is proved here. *)

(** ** The middle segment as an evt: [0x12d50, 0x12e24)
    From malloc's return (0x12d50 `beqz a0,0x12eb0`, the abort call, not taken: phi <> 0) to the join before free.
    Registers at 0x12d50: a0 = phi, s2 = k = length s, s1 = src, s3 = fl (k and src swap registers against the plain
    build). In order: phi into s0, memcpy(phi, src, k) when k <> 0 (0x12d68), the phi + k check, phi[k] = 0
    (0x12d78), len = strlen(phi) (0x12d80); when len <> 0 the scan (0x12d90 .. 0x12da4) and, when fl & 7 = 0,
    want = fuzz_catalogue_row(phi, tok) (0x12e68) and want_label (0x12e74 .. 0x12ea8); the cells sp + 16 (model) and
    sp + 8 (label) set to 0 (0x12dbc, 0x12dc0); rc = reac_box_pin_parse(fl bit 0 ? 0 : phi, fl bit 1 ? 0 : sp + 16,
    fl bit 2 ? 0 : sp + 8) (0x12df8); check_known(rc, want) (0x12e04); when rc = 0, check_row(model, want) (0x12e14)
    and check_label(label, want_label) (0x12e20). It ends at 0x12e24 with s0 = phi, s6-s11, sp, gp, tp unchanged
    (s4 = ~phi and s5 = the scan's byte are the harness's own), and no byte changed outside the callees' stack below
    sp (reac_box_pin_parse's 224 bytes are the most), the two cells [sp + 8, sp + 24), and the block
    [phi, phi + k + 1). Premises as in the plain build, with the cells at [sp + 8, sp + 24). *)
Definition PIN_MID : Z := 0x12d50.
Definition PIN_JOIN : Z := 0x12e24.
Definition MID_STACK : Z := 224.
Definition MID_OUT : Z := 24.

Definition pin_mid_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (s junk slack : list byte) (fl src phi lo : Z) (can : word),
    a0 = Z_to_bv 64 phi -> phi <> 0 ->
    s2 = Z_to_bv 64 (Z.of_nat (length s)) -> s1 = Z_to_bv 64 src -> s3 = Z_to_bv 64 fl ->
    0 <= fl < 256 -> ~ In NUL s ->
    bytes_at rsegs m src s ->
    rw_cells rsegs m phi [CB (S (length s)) junk] ->
    (forall a, phi <= a < phi + Z.of_nat (length s) + 1 -> seg_rom rsegs (wa a) = None) ->
    bytes_at rsegs m (phi + Z.of_nat (length s) + 1) slack ->
    (- (phi + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack) ->
    (src + Z.of_nat (length s) <= phi \/ phi + Z.of_nat (length s) <= src) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + MID_STACK <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
    wr_at rsegs m (bv_unsigned sp + 8) (MID_OUT - 8) ->
    (forall a, lo <= a < bv_unsigned sp + MID_OUT -> seg_rom rsegs (wa a) = None) ->
    (phi + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= lo \/ bv_unsigned sp + MID_OUT <= phi) ->
    (forall a, FUZZ_CATALOGUE <= a < FUZZ_CATALOGUE + CAT_BYTES -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) ->
    bytes_at rsegs m PARSE_SSP_GOT (le8 (Z_to_bv 64 PARSE_SSP_GUARD)) ->
    bytes_at rsegs m PARSE_SSP_GUARD (le8 can) ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (ra' t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' (Z_to_bv 64 phi) s1' a0' a1' a2' a3' a4' a5' a6' a7'
                       s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 PIN_JOIN) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - MID_STACK, bv_unsigned sp + MID_OUT); (phi, phi + Z.of_nat (length s) + 1)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PIN_MID) fc None m (seg_rom rsegs)).

(** ** The segment statements (ctrl's Slot.v Section Stmts form; the cuts of U/Prog/SlotInv.v)
    S_E01, ENTRY -> K12d50: the prologue (saves at [S - 56, S)); n < 2^26 by GV; fl and src with the three UBSan
      checks on data (0x12cf4, 0x12d18, 0x12d28); memchr(src, 0, n - 1) when n >= 2 (0x12d3c); k; malloc(k + 1) at
      0x12d4c with ra = 0x12d50, through ctrl's U b1_malloc_call.
    S_M01, K12d50 -> K12e24: pin_mid_contract on the normalized memory, as in the plain build, with sp = S - 80 and
      the writes in [S - 304, S - 56) and the block.
    S_X01, K12e24 -> RET: `mv a0,s0` and free(phi) at 0x12e28 with ra = 0x12e2c through ctrl's U b8_free_call;
      `mv a0,zero`, the restores, `addi sp,sp,80`, ret: Post. *)
Section Stmts.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.

Definition S_E01 : Prop :=
  Hcut B APIf ra (Inv_K12d50 B APIf ra empty) -> Hcut B APIf ra (Inv_ENTRY B APIf ra empty).
Definition S_M01 : Prop :=
  Hcut B APIf ra (Inv_K12e24 B APIf ra empty) -> Hcut B APIf ra (Inv_K12d50 B APIf ra empty).
Definition S_X01 : Prop := Hcut B APIf ra (Inv_K12e24 B APIf ra empty).

Definition seg_lemmas : Prop := S_E01 /\ S_M01 /\ S_X01.

End Stmts.
