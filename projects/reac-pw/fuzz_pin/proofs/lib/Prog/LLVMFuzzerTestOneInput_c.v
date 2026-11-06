From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog Require Import pin_spec fuzz_catalogue_row_c reac_box_pin_parse_c
  SlotInv.
Import ListNotations.
Open Scope Z_scope.

(** LLVMFuzzerTestOneInput of fuzz_pin.c:71-104 (416 bytes, 104 instructions at 0x12cac in the plain image; frame
    64 bytes; FrameAPI.ENTRY). It allocates (fuzz_str: malloc(k + 1), free), so its contract is in the form libreac/
    fuzz_ctrl's released slot consumes: the frame's obligation SlotInv.slot_goal
    (lib_contract_g for ENTRY, from FrameAPI.frame_plain), split at the cuts of SlotInv.v into the segment statements
    S_E01, S_M01, S_X01 below (ctrl's continuation form: the H of each exit cut -> the H of the entry cut), plus the
    n >= 2^26 run (0x12cc8 `srli a2,a1,26`; 0x12ccc `bnez a2,0x12dec`: `mv a0,zero` and the epilogue, no call), which
    the slot proves as one evt like ctrl's slot_early. What the whole function promises is lib_contract_g's: from
    lib_pre at ENTRY (a0 = data, a1 = n, the input block or `empty` for n = 0; sp 16-aligned with 65536 writable
    bytes below it, above alloc_ceiling and below 2^63; ra even), it returns to ra with a0 = 0, every callee-saved
    register as at entry, the allocator back to its entry blocks (RES_END), the input bytes unchanged, and no byte
    changed outside [sp - 65536, sp) and the allocator's own state (lib_post).

    The middle segment's body is stated as an evt, pin_mid_contract, so that its walk (the checks' premises, all of
    pin_spec's agreement) can be proved apart from the slot; S_M01's proof lifts it inside FR as ctrl's segments lift
    theirs (Tac_b1's run over the stack window and the live harness block). The callee contracts the walks take as
    premises (the released forms relocated to pin's image, or written here):
      S_E01: memchr_contract (Prog/memchr_c.v, MEMCHR = 0x1aa28; memchr(data + 1, 0, n - 1) at 0x12cf4), and malloc
             through the frame's malloc_contract (ms_malloc = 0x13be8) as ctrl's b1_malloc_call, request k + 1 <= 2^26 - 1
             (SlotInv.resb_room);
      pin_mid_contract: memcpy_contract (Prog/memcpy_c.v, 0x1ab24), strlen_contract (Prog/strlen_c.v, 0x1b218),
             fuzz_catalogue_row_contract, reac_box_pin_parse_contract, check_known_contract, check_row_contract,
             check_label_contract (written here), and pin_spec.harness_known / harness_row_label / harness_agrees;
      S_X01: free through the frame's free_contract (ms_free = 0x13aa8) as ctrl's b8_free_call.
    Statement text only: no function is proved here. *)

(** ** The middle segment as an evt: [0x12d1c, 0x12de4)
    From malloc's return (0x12d1c `beqz a0,0x12e48`, the abort call, not taken: phi <> 0) to the join before free.
    Registers at 0x12d1c: a0 = phi (the block), s1 = k = length s (the bytes fuzz_str copies), s2 = src (their
    address), s3 = fl (the flags byte). In order: memcpy(phi, src, k) when k <> 0 (0x12d34), phi[k] = 0 (0x12d3c),
    len = strlen(phi) (0x12d44) = k; when len <> 0, the scan `tok` (0x12d54 .. 0x12d64) and, when fl & 7 = 0,
    want = fuzz_catalogue_row(phi, tok) (0x12e18) and want_label (0x12e28 .. 0x12e44); the cells sp + 8 (model) and sp
    (label) set to 0 (0x12d7c, 0x12d80); rc = reac_box_pin_parse(fl bit 0 ? 0 : phi, fl bit 1 ? 0 : sp + 8, fl bit 2 ?
    0 : sp) (0x12db8); check_known(rc, want) (0x12dc4); when rc = 0, check_row(model, want) (0x12dd4) and
    check_label(label, want_label) (0x12de0). It ends at 0x12de4 with s0 = phi, every s register from s5 up, sp, gp, tp
    unchanged, and no byte changed outside the callees' stack below sp (reac_box_pin_parse's 176 bytes are the most),
    the two cells [sp, sp + 16), and the block [phi, phi + k + 1).
    Premises: the k bytes s at src (no NUL: pin_spec.pin_str_no_nul); the block's k + 1 bytes writable (rw_cells, as
    ctrl's f02_evt asks), outside the image (malloc_ret's fresh_block), with the bytes after it to the next 8-byte
    boundary readable (slack: the frame's block_slack_present); src and the block apart for memcpy; the stack region
    [lo, sp) as reac_box_pin_parse_contract needs it and the two cells writable; [lo, sp + 16) outside the image and
    the block (and its slack) outside [lo, sp + 16); the table, the SSP cells and mem_inv as reac_box_pin_parse
    needs them. The slot discharges each from FR at the cut (see S_M01). *)
Definition PIN_MID : Z := 0x12d1c.
Definition PIN_JOIN : Z := 0x12de4.
Definition MID_STACK : Z := 176.
Definition MID_OUT : Z := 16.

Definition pin_mid_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (s junk slack : list byte) (fl src phi lo : Z) (can : word),
    a0 = Z_to_bv 64 phi -> phi <> 0 ->
    s1 = Z_to_bv 64 (Z.of_nat (length s)) -> s2 = Z_to_bv 64 src -> s3 = Z_to_bv 64 fl ->
    0 <= fl < 256 -> ~ In NUL s ->
    bytes_at rsegs m src s ->
    rw_cells rsegs m phi [CB (S (length s)) junk] ->
    (forall a, phi <= a < phi + Z.of_nat (length s) + 1 -> seg_rom rsegs (wa a) = None) ->
    bytes_at rsegs m (phi + Z.of_nat (length s) + 1) slack ->
    (- (phi + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack) ->
    (src + Z.of_nat (length s) <= phi \/ phi + Z.of_nat (length s) <= src) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + MID_STACK <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
    wr_at rsegs m (bv_unsigned sp) MID_OUT ->
    (forall a, lo <= a < bv_unsigned sp + MID_OUT -> seg_rom rsegs (wa a) = None) ->
    (phi + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= lo \/ bv_unsigned sp + MID_OUT <= phi) ->
    (forall a, FUZZ_CATALOGUE <= a < FUZZ_CATALOGUE + CAT_BYTES -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) ->
    bytes_at rsegs m PARSE_SSP_GOT (le8 (Z_to_bv 64 PARSE_SSP_GUARD)) ->
    bytes_at rsegs m PARSE_SSP_GUARD (le8 can) ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (ra' t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' (Z_to_bv 64 phi) s1' a0' a1' a2' a3' a4' a5' a6' a7'
                       s2' s3' s4' s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 PIN_JOIN) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - MID_STACK, bv_unsigned sp + MID_OUT); (phi, phi + Z.of_nat (length s) + 1)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PIN_MID) fc None m (seg_rom rsegs)).

(** ** The segment statements (ctrl's Slot.v Section Stmts form)
    S_E01, ENTRY -> K12d1c: the prologue (saves at [S - 48, S)); n < 2^26 by GV, so 0x12ccc falls through; fl and
      src (0x12cd8 .. 0x12ce0); memchr(src, 0, n - 1) when n >= 2 (0x12cf4; its buffer is the input block's tail,
      unchanged since ENTRY by FR and GV's blk_data); k (0x12d10 or n - 1 or 0); malloc(k + 1) at 0x12d18 with
      ra = 0x12d1c, through ctrl's b1_malloc_call (FR with hb = [], k + 1 <= 2^26 - 1 since n < 2^26), whose
      continuation gives FR with hb = [(phi, k + 1)], phi <> 0, and the callee-saved registers (so KS).
    S_M01, K12d1c -> K12de4: pin_mid_contract on the normalized memory, with s := pin_str (g_in g) (length k, so
      g_k g = length s), fl := g_fl g, src := g_src g, lo := S - 65536 (FR's stk), sp = S - 64; the block's bytes
      from the frame's blocks_writable, its slack from block_slack_present, its absence from the image from the
      allocator relation (ax_blocks_img); the table [0x1c730, 0x1d3e8) from relro (frame_RELRO covers [0x1c720, 0x1d478)); the SSP cells
      from the allocator relation's statics; then the writes lie in [S - 240, S - 48) and the block, so FR and the
      block list carry over and KS holds (s5-s11 kept), s0 = phi.
    S_X01, K12de4 -> RET: `mv a0,s0` and free(phi) at 0x12de8 with ra = 0x12dec, through ctrl's b8_free_call (the
      block (phi, k + 1) is a user block by the Permutation of CUTST), which leaves hb = []; `mv a0,zero`, the restores
      from the saved bytes, `addi sp,sp,64`, ret to ra: Post (lib_post; RES_END by resb_end; KS gives s5-s11). *)
Section Stmts.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.

Definition S_E01 : Prop :=
  Hcut B APIf ra (Inv_K12d1c B APIf ra empty) -> Hcut B APIf ra (Inv_ENTRY B APIf ra empty).
Definition S_M01 : Prop :=
  Hcut B APIf ra (Inv_K12de4 B APIf ra empty) -> Hcut B APIf ra (Inv_K12d1c B APIf ra empty).
Definition S_X01 : Prop := Hcut B APIf ra (Inv_K12de4 B APIf ra empty).

Definition seg_lemmas : Prop := S_E01 /\ S_M01 /\ S_X01.

End Stmts.
