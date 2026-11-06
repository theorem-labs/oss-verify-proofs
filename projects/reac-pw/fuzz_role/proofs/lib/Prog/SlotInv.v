(* Cut invariants of reac-pw/fuzz_role LLVMFuzzerTestOneInput (plain, [0x12ea0, 0x141c0)): the role quantities of the
   ghost and one Inv_<cut> per cut between ENTRY and RET, each a CUTST of Prog/SlotFR.v (FR over the live harness
   blocks hb, at some FP state with rounding mode 0). Statement text: no function is proved here.
   The form is reac-pw/fuzz_pin's Prog/SlotInv.v (libreac/fuzz_ctrl's released Prog/SlotInv.v, origin/ossv/recipes
   25e3d17bdb50), with role's two live blocks:
   - pp = malloc(19744) (0x12f10 `jal malloc`, a0 = s1 = 5 << 12 - 0x2e0), the struct pod_props that pod_build fills;
     pod = malloc(len ? len : 1) (0x13f48, a0 = len + (len = 0) from 0x13f40-0x13f44, len = pp->len); free(pod)
     (0x1415c) then free(pp) (0x14164). The new block is at the head of hb: [(pp, 19744)], then
     [(pod, len); (pp, 19744)]; len >= 8 (pod_build's first two 4-byte puts always succeed), so the request
     len + (len = 0) is len.
   - Cuts: ENTRY (0x12ea0); K12f14, malloc(pp)'s return address (`bnez a0` there); K13f4c, malloc(pod)'s return
     address (`beqz a0` there); K14158, just after check_code returned, before free(pod)'s argument move
     (0x14158 `mv a0,s1`); RET = Post. The size >= 2^26 return (0x12ed8 `srli a2,a1,26`, 0x12ee0 `j 0x14168`) passes
     no cut: the slot runs it from ENTRY as one evt (GV bounds g_n below 2^26 at the cuts).
   - Each cut names exactly the registers and frame cells that the code after it reads before writing them (the
     segment statements are in Prog/LLVMFuzzerTestOneInput_c.v):
     K12f14: a0 = pp (nonzero, 16-aligned: malloc_ret), s3 = the input cursor (data + 1, or data when the input is
       empty; 0x12ee4 `mv s3,a0`, 0x12ef0 `addi s3,s3,1`), s2 = the bytes left (n - 1 or 0; 0x12ef4 / 0x12efc),
       s5 = the flags byte (0x12eec `lbu s5,0(s3)`, 0 when empty), s1 = 19744 (memset's size at 0x12f34),
       s0 = 0x5000 (0x12f20 `addiw s0,s0,-0x2ec` makes &n_ent's offset 0x4d14);
     K13f4c: a0 = pod (nonzero, 16-aligned), s2 = len (0x13f34 `ld s2,0(a6)`), s11 = pp (0x12f1c), s4 = pp + 0x4d14
       (&n_ent; corrupt at 4(s4), 0x13f88), s5 = flags, the frame cells sp + 0x50 = pp (reloaded at 0x13fd4,
       0x1408c, 0x140b0, 0x140c0) and sp + 0x80 = pp + 0x4000 (&len; is_props at 8, params_struct at 0x10,
       0x13f94), and the pp block's 19744 bytes = Pod.Layout.pp_bytes of the record pod_build made of the input after
       the flags byte (FR does not carry the bytes of a harness block, and malloc keeps the other blocks' bytes);
     K14158: s1 = pod (0x13f50), s11 = pp (restored from sp + 0x50 on every path that wrote s11). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog Require Import SlotFR.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Model Layout.
Import ListNotations.
Open Scope Z_scope.

(* struct pod_props: 19744 bytes; len at 0x4000, n_ent at 0x4d14 (corrupt at 0x4d18). *)
Definition POD_PROPS : Z := 19744.
Definition POD_LEN_OFF : Z := 0x4000.
Definition POD_NENT_OFF : Z := 0x4d14.

(* The role quantities of the input (fuzz.h's cursor: fuzz_u8 reads one byte, or 0 and nothing when none is left):
   the flags byte, the bytes after it (pod_build's input), the cursor after the flags byte, the bytes left, the record
   pod_build makes and its buffer length (pp->len). *)
Definition g_fl (g : ghost) : Z := match g_in g with [] => 0 | b :: _ => bv_unsigned b end.
Definition g_rest (g : ghost) : list byte := tl (g_in g).
Definition g_src (g : ghost) : Z := g_p g + Z.min 1 (g_n g).
Definition g_k (g : ghost) : Z := g_n g - Z.min 1 (g_n g).
Definition g_rec (g : ghost) : pod_rec := fst (pod_build (g_rest g)).
Definition g_len (g : ghost) : Z := Z.of_nat (length (buf (g_rec g))).

(* The live harness blocks after malloc(pp), and after malloc(pod) (new block at the head). *)
Definition hb_pp (pp : Z) : list (Z * Z) := [(pp, POD_PROPS)].
Definition hb_pod (g : ghost) (pod pp : Z) : list (Z * Z) := [(pod, g_len g); (pp, POD_PROPS)].

Section Slot.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.

(* K12f14, malloc(pp)'s return (0x12f10 `jal malloc` with a0 = 19744). *)
Definition Inv_K12f14 (g : ghost) (c : config) : Prop :=
  exists pp, CUTST B APIf ra empty g 0x12f14 (hb_pp pp) (fun regs m =>
    rg regs 10 pp /\ pp <> 0 /\ pp mod 16 = 0 /\
    rg regs 19 (g_src g) /\ rg regs 18 (g_k g) /\ rg regs 21 (g_fl g) /\
    rg regs 9 POD_PROPS /\ rg regs 8 0x5000) c.

(* K13f4c, malloc(pod)'s return (0x13f48 `jal malloc` with a0 = len): the record in the pp block. *)
Definition Inv_K13f4c (g : ghost) (c : config) : Prop :=
  exists pp pod, CUTST B APIf ra empty g 0x13f4c (hb_pod g pod pp) (fun regs m =>
    rg regs 10 pod /\ pod <> 0 /\ pod mod 16 = 0 /\
    rg regs 18 (g_len g) /\ rg regs 27 pp /\ rg regs 20 (pp + POD_NENT_OFF) /\ rg regs 21 (g_fl g) /\
    bytes_at rsegs m (fsp g + 0x50) (le8 (Z_to_bv 64 pp)) /\
    bytes_at rsegs m (fsp g + 0x80) (le8 (Z_to_bv 64 (pp + POD_LEN_OFF))) /\
    bytes_at rsegs m pp (pp_bytes (g_rec g))) c.

(* K14158, after check_code, before free(pod) (0x14158 `mv a0,s1`; 0x1415c `jal free`). *)
Definition Inv_K14158 (g : ghost) (c : config) : Prop :=
  exists pp pod, CUTST B APIf ra empty g 0x14158 (hb_pod g pod pp) (fun regs m =>
    rg regs 9 pod /\ rg regs 27 pp) c.

End Slot.
