(* Cut invariants of reac-pw/fuzz_rate LLVMFuzzerTestOneInput (UBSan, [0x12fe0, 0x146c0)): the rate quantities of the
   ghost and one Inv_<cut> per cut between ENTRY and RET, each a CUTST of U/Prog/SlotFR.v. Statement text: no function
   is proved here. The plain file (lib/Prog/SlotInv.v) with the UBSan numbers; the form is reac-pw/fuzz_role's
   U/Prog/SlotInv.v:
   - pp = malloc(19744) at 0x1310c (a0 = s3 = 5 << 12 - 0x2e0); pod = malloc(len ? len : 1) at 0x14208 (a0 = len +
     (len = 0), 0x14200-0x14204); buf = malloc(buflen ? buflen : 1) at 0x14624 (a0 = s5 = buflen + (buflen = 0),
     0x14614-0x1461c); free(buf) at 0x14664, free(pod) at 0x1466c, free(pp) at 0x14674 (pp reloaded by 0x14670
     `ld a0,0xd8(sp)`). hb = [(pp, 19744)], then [(pod, len); (pp, 19744)], then [(buf, bl); (pod, len); (pp, 19744)]
     with bl = buflen + (buflen = 0), the malloc request.
   - The header as in the plain file (fuzz.h:37-56); the reads of bytes 3..6 lie out of line at 0x143d0-0x1446c
     (0x130e4 `j 0x143d0`, back by 0x143f4 / 0x14420 / 0x14448 / 0x1446c); buflen = byte 2 mod 24 (0x130c4-0x130d8).
   - Cuts: ENTRY (0x12fe0); K13110, malloc(pp)'s return address (`bnez a0` there); K1420c, malloc(pod)'s return
     address (`beqz a0` there); K14614, after check_code(refuse_code(MALFORMED), MALFORMED) returned (0x14610
     `jal check_code`), before buf's request (0x14614 `ld s0,0x30(sp)`); K14660, after check_csv returned, before
     free(buf)'s argument move (0x14660 `mv a0,s4`); RET = Post. The size >= 2^26 return (0x13018 `srli a2,a1,26`,
     0x13020 `j 0x14678`) passes no cut.
   - The registers and frame cells each cut names (those the code after it reads before writing them):
     K13110: a0 = pp (nonzero, 16-aligned), s7 = the input cursor (data + min 7 n: 0x13024 `mv s7,a0` for n = 0,
       the `mv s7,a2` at 0x130fc for 1 <= n <= 6, 0x14460 for n >= 7), s1 = the bytes left (n - 7 or 0; 0x1445c),
       s2 = flags (0x1303c), s5 = mask (0x13058), the cell sp + 0x30 = buflen (0x130dc), s4 = byte 3 (0x143dc), the
       cells sp + 0x28 = byte 4 << 8 (0x14414), sp + 0x20 = byte 5 (0x1443c), sp + 0x18 = byte 6 << 8 (0x14468), each
       0 when its byte is absent, s3 = 19744 (memset's size at 0x13120), s0 = 0x5000;
     K1420c: a0 = pod (nonzero, 16-aligned), s4 = len (8 or 16 from 0x131d4 / 0x1326c when pod_build adds no
       property, else `ld s4,0(s11)` at 0x140d8 / 0x141f4), s8 = pp (0x13118; memcpy's source at 0x1421c),
       s11 = pp + 0x4000 (&len; is_props at 0x1425c), s2 = flags (reloaded from sp + 0x38 at
       0x140dc / 0x141ec), the cells sp + 8 = byte 3 (0x131b8), sp + 0x10 = mask (0x13190), sp + 0x18 = byte 6 << 8,
       sp + 0x20 = byte 5, sp + 0x28 = byte 4 << 8, sp + 0x30 = buflen, sp + 0x38 = flags (0x13294), sp + 0x98 =
       pp + 0x4d14 (&n_ent, 0x1328c; corrupt at 4 from it, 0x14248-0x1424c), sp + 0xd8 = pp (0x13298, the only store;
       read by free(pp)'s 0x14670), and the pp block's 19744 bytes = Pod.Layout.pp_bytes of the record;
     K14614: s3 = pod (0x14210), s10 = mask (0x14518 `ld s10,0x10(sp)`), the cells sp + 0x30 = buflen and
       sp + 0xd8 = pp;
     K14660: s4 = buf (0x1462c), s3 = pod, the cell sp + 0xd8 = pp. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import SlotFR.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Model Layout.
Import ListNotations.
Open Scope Z_scope.

(* struct pod_props: 19744 bytes; len at 0x4000, n_ent at 0x4d14 (corrupt at 0x4d18). *)
Definition POD_PROPS : Z := 19744.
Definition POD_LEN_OFF : Z := 0x4000.
Definition POD_NENT_OFF : Z := 0x4d14.

(* The rate quantities of the input, as in the plain file. *)
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

Definition hb_pp (pp : Z) : list (Z * Z) := [(pp, POD_PROPS)].
Definition hb_pod (g : ghost) (pod pp : Z) : list (Z * Z) := [(pod, g_len g); (pp, POD_PROPS)].
Definition hb_buf (g : ghost) (cb pod pp : Z) : list (Z * Z) := [(cb, g_bl g); (pod, g_len g); (pp, POD_PROPS)].

Section Slot.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.

(* K13110, malloc(pp)'s return (0x1310c `jal malloc` with a0 = 19744): the header values. *)
Definition Inv_K13110 (g : ghost) (c : config) : Prop :=
  exists pp, CUTST B APIf ra empty g 0x13110 (hb_pp pp) (fun regs m =>
    rg regs 10 pp /\ pp <> 0 /\ pp mod 16 = 0 /\
    rg regs 23 (g_src g) /\ rg regs 9 (g_k g) /\
    rg regs 18 (g_fl g) /\ rg regs 21 (g_mask g) /\
    bytes_at rsegs m (fsp g + 0x30) (le8 (Z_to_bv 64 (g_buflen g))) /\
    rg regs 20 (g_b3 g) /\
    bytes_at rsegs m (fsp g + 0x28) (le8 (Z_to_bv 64 (g_b4 g * 256))) /\
    bytes_at rsegs m (fsp g + 0x20) (le8 (Z_to_bv 64 (g_b5 g))) /\
    bytes_at rsegs m (fsp g + 0x18) (le8 (Z_to_bv 64 (g_b6 g * 256))) /\
    rg regs 19 POD_PROPS /\ rg regs 8 0x5000) c.

(* K1420c, malloc(pod)'s return (0x14208 `jal malloc` with a0 = len): the header values and the record in pp. *)
Definition Inv_K1420c (g : ghost) (c : config) : Prop :=
  exists pp pod, CUTST B APIf ra empty g 0x1420c (hb_pod g pod pp) (fun regs m =>
    rg regs 10 pod /\ pod <> 0 /\ pod mod 16 = 0 /\
    rg regs 20 (g_len g) /\ rg regs 24 pp /\ rg regs 27 (pp + POD_LEN_OFF) /\ rg regs 18 (g_fl g) /\
    bytes_at rsegs m (fsp g + 0x8) (le8 (Z_to_bv 64 (g_b3 g))) /\
    bytes_at rsegs m (fsp g + 0x10) (le8 (Z_to_bv 64 (g_mask g))) /\
    bytes_at rsegs m (fsp g + 0x18) (le8 (Z_to_bv 64 (g_b6 g * 256))) /\
    bytes_at rsegs m (fsp g + 0x20) (le8 (Z_to_bv 64 (g_b5 g))) /\
    bytes_at rsegs m (fsp g + 0x28) (le8 (Z_to_bv 64 (g_b4 g * 256))) /\
    bytes_at rsegs m (fsp g + 0x30) (le8 (Z_to_bv 64 (g_buflen g))) /\
    bytes_at rsegs m (fsp g + 0x38) (le8 (Z_to_bv 64 (g_fl g))) /\
    bytes_at rsegs m (fsp g + 0x98) (le8 (Z_to_bv 64 (pp + POD_NENT_OFF))) /\
    bytes_at rsegs m (fsp g + 0xd8) (le8 (Z_to_bv 64 pp)) /\
    bytes_at rsegs m pp (pp_bytes (g_rec g))) c.

(* K14614, after check_code(refuse_code(MALFORMED), MALFORMED) (0x14610 `jal check_code`), before buf's request. *)
Definition Inv_K14614 (g : ghost) (c : config) : Prop :=
  exists pp pod, CUTST B APIf ra empty g 0x14614 (hb_pod g pod pp) (fun regs m =>
    rg regs 19 pod /\ rg regs 26 (g_mask g) /\
    bytes_at rsegs m (fsp g + 0x30) (le8 (Z_to_bv 64 (g_buflen g))) /\
    bytes_at rsegs m (fsp g + 0xd8) (le8 (Z_to_bv 64 pp))) c.

(* K14660, after check_csv, before free(buf) (0x14660 `mv a0,s4`; 0x14664 `jal free`). *)
Definition Inv_K14660 (g : ghost) (c : config) : Prop :=
  exists pp pod cb, CUTST B APIf ra empty g 0x14660 (hb_buf g cb pod pp) (fun regs m =>
    rg regs 20 cb /\ rg regs 19 pod /\
    bytes_at rsegs m (fsp g + 0xd8) (le8 (Z_to_bv 64 pp))) c.

End Slot.
