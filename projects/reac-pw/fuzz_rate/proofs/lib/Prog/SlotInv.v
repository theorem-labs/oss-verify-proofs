(* Cut invariants of reac-pw/fuzz_rate LLVMFuzzerTestOneInput (plain, [0x12fc0, 0x145a8)): the rate quantities of the
   ghost and one Inv_<cut> per cut between ENTRY and RET, each a CUTST of Prog/SlotFR.v (FR over the live harness
   blocks hb, at some FP state with rounding mode 0). Statement text: no function is proved here.
   The form is reac-pw/fuzz_role's Prog/SlotInv.v (itself fuzz_pin's and
   libreac/fuzz_ctrl's released Prog/SlotInv.v, origin/ossv/recipes 25e3d17bdb50), with rate's three live blocks
   (fuzz_rate.c:231-284):
   - pp = malloc(19744) (0x13154 `jal malloc`, a0 = s3 = 5 << 12 - 0x2e0); pod = fuzz_dup(pp->buf, pp->len) =
     malloc(len ? len : 1) (0x141e0, a0 = len + (len = 0) from 0x141d8-0x141dc); buf = malloc(buflen ? buflen : 1)
     (0x14510, a0 = s5 = buflen + (buflen = 0) from 0x14504-0x14508); free(buf) (0x14550), free(pod) (0x14558),
     free(pp) (0x14560, pp reloaded by 0x1455c `ld a0,0x80(sp)`). The new block is at the head of hb: [(pp, 19744)],
     [(pod, len); (pp, 19744)], [(buf, bl); (pod, len); (pp, 19744)]. len >= 8 (pod_build's first two 4-byte puts
     always succeed), so pod's request is len. buf's block length is the REQUEST bl = buflen + (buflen = 0) in [1, 23]
     (g_bl): malloc_ret records the request, so buflen in its place would make the block list false for buflen = 0.
   - The header (fuzz.h:37-56: fuzz_u8 reads one byte, or gives 0 and reads nothing when no byte is left; fuzz_u32 is
     four fuzz_u8 little-endian): flags = byte 0, mask = byte 1, buflen = byte 2 mod 24 (0x13098-0x130ac: `mulhu` by
     the constant at .rodata 0x104e0, checked for all 256 bytes), other = bytes 3..6; g_u8 g i is byte i of the input
     or 0. pod_build reads the input after these 7 bytes (g_rest, at g_src, g_k bytes).
   - Cuts: ENTRY (0x12fc0); K13158, malloc(pp)'s return address (`bnez a0` there); K141e4, malloc(pod)'s return
     address (`beqz a0` there); K14504, after check_code(refuse_code(MALFORMED), MALFORMED) returned (fuzz_rate.c:270,
     0x14500 `jal check_code`), before buf's request (0x14504 `seqz s5,s10`); K1454c, after check_csv returned, before
     free(buf)'s argument move (0x1454c `mv a0,s4`); RET = Post. The size >= 2^26 return (0x12ff8 `srli a2,a1,26`,
     0x13000 `j 0x14564`) passes no cut: the slot runs it from ENTRY as one evt (GV bounds g_n below 2^26 at the
     cuts). K14504 and K1454c follow the FP-changing parse, pod_nearest and snprintf: CUTST takes any FP state with
     rounding mode 0.
   - Each cut names exactly the registers and frame cells that the code after it reads before writing them (backward
     liveness; the segment statements are in Prog/LLVMFuzzerTestOneInput_c.v):
     K13158: a0 = pp (nonzero, 16-aligned: malloc_ret), s5 = the input cursor (data + min 7 n: 0x13004 `mv s5,a0`,
       then 0x13140 `addi s5,s5,7` or the `addi s5,s5,k` of each path with 1 <= n < 7), s0 = the bytes left (n - 7
       or 0; 0x1313c), s6 = flags (0x1300c), s9 = mask (0x13060), s10 = buflen (0x130ac), s7 = byte 3 (0x130d0),
       the cell sp + 0x30 = byte 4 << 8 (0x13100), s11 = byte 5 (0x1311c), s4 = byte 6 << 8 (0x13144), each 0 when
       its byte is absent, s3 = 19744 (memset's size at 0x13178), s1 = 0x5000 (0x13164 `addiw s1,s1,-0x2ec` makes
       &n_ent's offset 0x4d14);
     K141e4: a0 = pod (nonzero, 16-aligned), s4 = len (8 or 16 from 0x13208 / 0x13278 when pod_build adds no
       property, else `ld s4,0(a6)` at 0x140f0 / 0x14190 / 0x141c8), s1 = pp, s6 = flags, s9 = mask, s10 = buflen,
       s7 = byte 3, s2 = byte 4 << 8, s11 = byte 5 (reloaded at 0x140f4-0x14110), the cells
       sp + 0x28 = byte 6 << 8 (0x13188), sp + 0x70 = pp + 0x4d14 (&n_ent; corrupt at 4 from it, 0x14228-0x1422c),
       sp + 0x80 = pp (0x13180, the only store; read by free(pp)'s 0x1455c), sp + 0xb0 = pp + 0x4000 (&len; is_props
       and params_struct at 0x14238-0x1425c), and the pp block's 19744 bytes = Pod.Layout.pp_bytes of the record
       pod_build made of the input after the header (FR does not carry the bytes of a harness block, and malloc keeps
       the other blocks' bytes);
     K14504: s3 = pod (0x141e8; no write to s3 in [0x141ec, 0x14558)), s9 = mask, s10 = buflen, the cell
       sp + 0x80 = pp (nothing after K14504 reads the pp or pod block's bytes);
     K1454c: s4 = buf (0x14518), s3 = pod, the cell sp + 0x80 = pp. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require Import SlotFR.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Model Layout.
Import ListNotations.
Open Scope Z_scope.

(* struct pod_props: 19744 bytes; len at 0x4000, n_ent at 0x4d14 (corrupt at 0x4d18). *)
Definition POD_PROPS : Z := 19744.
Definition POD_LEN_OFF : Z := 0x4000.
Definition POD_NENT_OFF : Z := 0x4d14.

(* The rate quantities of the input: byte i of the input or 0 (fuzz_u8), the seven header values, the bytes after
   the header (pod_build's input), the cursor after the header, the bytes left, the record pod_build makes, its
   buffer length (pp->len) and buf's malloc request. *)
Definition g_u8 (g : ghost) (i : nat) : Z :=
  match nth_error (g_in g) i with Some b => bv_unsigned b | None => 0 end.
Definition g_fl (g : ghost) : Z := g_u8 g 0.
Definition g_mask (g : ghost) : Z := g_u8 g 1.
Definition g_buflen (g : ghost) : Z := g_u8 g 2 mod 24.
Definition g_b3 (g : ghost) : Z := g_u8 g 3.
Definition g_b4 (g : ghost) : Z := g_u8 g 4.
Definition g_b5 (g : ghost) : Z := g_u8 g 5.
Definition g_b6 (g : ghost) : Z := g_u8 g 6.
Definition g_rest (g : ghost) : list byte := skipn 7 (g_in g).
Definition g_src (g : ghost) : Z := g_p g + Z.min 7 (g_n g).
Definition g_k (g : ghost) : Z := g_n g - Z.min 7 (g_n g).
Definition g_rec (g : ghost) : pod_rec := fst (pod_build (g_rest g)).
Definition g_len (g : ghost) : Z := Z.of_nat (length (buf (g_rec g))).
Definition g_bl (g : ghost) : Z := g_buflen g + (if g_buflen g =? 0 then 1 else 0).

(* The live harness blocks after malloc(pp), malloc(pod) and malloc(buf) (new block at the head). *)
Definition hb_pp (pp : Z) : list (Z * Z) := [(pp, POD_PROPS)].
Definition hb_pod (g : ghost) (pod pp : Z) : list (Z * Z) := [(pod, g_len g); (pp, POD_PROPS)].
Definition hb_buf (g : ghost) (cb pod pp : Z) : list (Z * Z) := [(cb, g_bl g); (pod, g_len g); (pp, POD_PROPS)].

Section Slot.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.

(* K13158, malloc(pp)'s return (0x13154 `jal malloc` with a0 = 19744): the header values. *)
Definition Inv_K13158 (g : ghost) (c : config) : Prop :=
  exists pp, CUTST B APIf ra empty g 0x13158 (hb_pp pp) (fun regs m =>
    rg regs 10 pp /\ pp <> 0 /\ pp mod 16 = 0 /\
    rg regs 21 (g_src g) /\ rg regs 8 (g_k g) /\
    rg regs 22 (g_fl g) /\ rg regs 25 (g_mask g) /\ rg regs 26 (g_buflen g) /\ rg regs 23 (g_b3 g) /\
    bytes_at rsegs m (fsp g + 0x30) (le8 (Z_to_bv 64 (g_b4 g * 256))) /\
    rg regs 27 (g_b5 g) /\ rg regs 20 (g_b6 g * 256) /\
    rg regs 19 POD_PROPS /\ rg regs 9 0x5000) c.

(* K141e4, malloc(pod)'s return (0x141e0 `jal malloc` with a0 = len): the header values and the record in pp. *)
Definition Inv_K141e4 (g : ghost) (c : config) : Prop :=
  exists pp pod, CUTST B APIf ra empty g 0x141e4 (hb_pod g pod pp) (fun regs m =>
    rg regs 10 pod /\ pod <> 0 /\ pod mod 16 = 0 /\
    rg regs 20 (g_len g) /\ rg regs 9 pp /\
    rg regs 22 (g_fl g) /\ rg regs 25 (g_mask g) /\ rg regs 26 (g_buflen g) /\ rg regs 23 (g_b3 g) /\
    rg regs 18 (g_b4 g * 256) /\ rg regs 27 (g_b5 g) /\
    bytes_at rsegs m (fsp g + 0x28) (le8 (Z_to_bv 64 (g_b6 g * 256))) /\
    bytes_at rsegs m (fsp g + 0x70) (le8 (Z_to_bv 64 (pp + POD_NENT_OFF))) /\
    bytes_at rsegs m (fsp g + 0x80) (le8 (Z_to_bv 64 pp)) /\
    bytes_at rsegs m (fsp g + 0xb0) (le8 (Z_to_bv 64 (pp + POD_LEN_OFF))) /\
    bytes_at rsegs m pp (pp_bytes (g_rec g))) c.

(* K14504, after check_code(refuse_code(MALFORMED), MALFORMED) (0x14500 `jal check_code`), before buf's request. *)
Definition Inv_K14504 (g : ghost) (c : config) : Prop :=
  exists pp pod, CUTST B APIf ra empty g 0x14504 (hb_pod g pod pp) (fun regs m =>
    rg regs 19 pod /\ rg regs 25 (g_mask g) /\ rg regs 26 (g_buflen g) /\
    bytes_at rsegs m (fsp g + 0x80) (le8 (Z_to_bv 64 pp))) c.

(* K1454c, after check_csv, before free(buf) (0x1454c `mv a0,s4`; 0x14550 `jal free`). *)
Definition Inv_K1454c (g : ghost) (c : config) : Prop :=
  exists pp pod cb, CUTST B APIf ra empty g 0x1454c (hb_buf g cb pod pp) (fun regs m =>
    rg regs 20 cb /\ rg regs 19 pod /\
    bytes_at rsegs m (fsp g + 0x80) (le8 (Z_to_bv 64 pp))) c.

End Slot.
