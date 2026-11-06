(* Cut invariants of reac-pw/fuzz_role LLVMFuzzerTestOneInput (UBSan, [0x12ec0, 0x14224)): the role quantities of the
   ghost and one Inv_<cut> per cut between ENTRY and RET, each a CUTST of U/Prog/SlotFR.v. Statement text: no function
   is proved here. The plain file (lib/Prog/SlotInv.v) with the UBSan numbers:
   - pp = malloc(19744) at 0x12f44 (a0 = s1 = 5 << 12 - 0x2e0); pod = malloc(len ? len : 1) at 0x13f30 (a0 = len +
     (len = 0), 0x13f28-0x13f2c); free(pod) at 0x141b8, free(pp) at 0x141c0. hb = [(pp, 19744)], then
     [(pod, len); (pp, 19744)].
   - Cuts: ENTRY (0x12ec0); K12f48, malloc(pp)'s return address (`bnez a0` there); K13f34, malloc(pod)'s return
     address (0x13f34 `ld s3,0x10(sp)`, then the `beqz a0` at 0x13f38); K141b4, just after check_code returned, before
     free(pod)'s argument move (0x141b4 `mv a0,s1`); RET = Post. The size >= 2^26 return (0x12ef8, 0x12f00
     `j 0x141c4`) passes no cut.
   - The registers and frame cells each cut names (those the code after it reads before writing them):
     K12f48: a0 = pp (nonzero, 16-aligned), s6 = the input cursor (data + 1, or data when the input is empty;
       0x12f04 `mv s6,a0`, 0x12f28 `mv s6,a0` with a0 = s6 + 1), s2 = the bytes left (0x12f24 / 0x12f30), the frame
       cell sp + 0x10 = the flags byte as 8 bytes (0x12f20 `sd a2,0x10(sp)` after `lbu`, or 0x12f34
       `sd zero,0x10(sp)`), s1 = 19744 (memset's size, 0x12f58), s0 = 0x5000;
     K13f34: a0 = pod (nonzero, 16-aligned), s2 = len (0x13f1c `ld s2,0(s7)`), s8 = pp (0x12f50; memcpy's source at
       0x13f48, free(pp) at 0x141bc, reloaded from sp + 0x68 where it was overwritten), s7 = pp + 0x4000 (&len;
       is_props and params_struct at 0x13f84 / 0x13f8c), the frame cells sp + 0x10 = flags (0x13f34, 0x140b4,
       0x14100), sp + 0x68 = pp (0x13fc0, 0x140b0, 0x140fc) and sp + 0x70 = pp + 0x4d14 (&n_ent; corrupt at 4 from
       it, 0x13f70-0x13f74; n_ent, 0x13f9c), and the pp block's 19744 bytes = Pod.Layout.pp_bytes of the record;
     K141b4: s1 = pod (0x13f3c), s8 = pp. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog Require Import SlotFR.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Model Layout.
Import ListNotations.
Open Scope Z_scope.

(* struct pod_props: 19744 bytes; len at 0x4000, n_ent at 0x4d14 (corrupt at 0x4d18). *)
Definition POD_PROPS : Z := 19744.
Definition POD_LEN_OFF : Z := 0x4000.
Definition POD_NENT_OFF : Z := 0x4d14.

(* The role quantities of the input, as in the plain file. *)
Definition g_fl (g : ghost) : Z := match g_in g with [] => 0 | b :: _ => bv_unsigned b end.
Definition g_rest (g : ghost) : list byte := tl (g_in g).
Definition g_src (g : ghost) : Z := g_p g + Z.min 1 (g_n g).
Definition g_k (g : ghost) : Z := g_n g - Z.min 1 (g_n g).
Definition g_rec (g : ghost) : pod_rec := fst (pod_build (g_rest g)).
Definition g_len (g : ghost) : Z := Z.of_nat (length (buf (g_rec g))).

Definition hb_pp (pp : Z) : list (Z * Z) := [(pp, POD_PROPS)].
Definition hb_pod (g : ghost) (pod pp : Z) : list (Z * Z) := [(pod, g_len g); (pp, POD_PROPS)].

Section Slot.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.

(* K12f48, malloc(pp)'s return (0x12f44 `jal malloc` with a0 = 19744). *)
Definition Inv_K12f48 (g : ghost) (c : config) : Prop :=
  exists pp, CUTST B APIf ra empty g 0x12f48 (hb_pp pp) (fun regs m =>
    rg regs 10 pp /\ pp <> 0 /\ pp mod 16 = 0 /\
    rg regs 22 (g_src g) /\ rg regs 18 (g_k g) /\
    bytes_at rsegs m (fsp g + 0x10) (le8 (Z_to_bv 64 (g_fl g))) /\
    rg regs 9 POD_PROPS /\ rg regs 8 0x5000) c.

(* K13f34, malloc(pod)'s return (0x13f30 `jal malloc` with a0 = len): the record in the pp block. *)
Definition Inv_K13f34 (g : ghost) (c : config) : Prop :=
  exists pp pod, CUTST B APIf ra empty g 0x13f34 (hb_pod g pod pp) (fun regs m =>
    rg regs 10 pod /\ pod <> 0 /\ pod mod 16 = 0 /\
    rg regs 18 (g_len g) /\ rg regs 24 pp /\ rg regs 23 (pp + POD_LEN_OFF) /\
    bytes_at rsegs m (fsp g + 0x10) (le8 (Z_to_bv 64 (g_fl g))) /\
    bytes_at rsegs m (fsp g + 0x68) (le8 (Z_to_bv 64 pp)) /\
    bytes_at rsegs m (fsp g + 0x70) (le8 (Z_to_bv 64 (pp + POD_NENT_OFF))) /\
    bytes_at rsegs m pp (pp_bytes (g_rec g))) c.

(* K141b4, after check_code, before free(pod) (0x141b4 `mv a0,s1`; 0x141b8 `jal free`). *)
Definition Inv_K141b4 (g : ghost) (c : config) : Prop :=
  exists pp pod, CUTST B APIf ra empty g 0x141b4 (hb_pod g pod pp) (fun regs m =>
    rg regs 9 pod /\ rg regs 24 pp) c.

End Slot.
