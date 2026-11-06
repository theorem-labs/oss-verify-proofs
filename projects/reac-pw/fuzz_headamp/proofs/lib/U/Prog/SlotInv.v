(* Cut invariants of reac-pw/fuzz_headamp LLVMFuzzerTestOneInput (UBSan, [0x12fa8, 0x148ac); fuzz_headamp.c:311-360):
   the headamp quantities of the ghost and one Inv_<cut> per cut between ENTRY and RET, each a CUTST of
   U/Prog/SlotFR.v. Statement text: no function is proved here. The plain file (lib/Prog/SlotInv.v) with the UBSan
   numbers; addresses: the UBSan ELF, unstripped sha256 1d123858383d3510..., pinned sha256 0516fd55d25d...
   - The input: as in the plain file. The code: 0x12ffc `mv s6,a0`; n = 0: s2 = s3 = 0, the cell sp + 0x10 := 1
     (0x13038-0x13044); n >= 1: sp + 0x10 := (data[0] & 1) = 0 = 1 - null (0x13014-0x13020 `lbu`, `andi 1`,
     `seqz`, `sd`), and n = 1: s2 = s3 = 0, s6 = data + 1; n >= 2: s2 = n - 2, s6 = data + 2, s3 = data[1] mod 10
     (0x1305c-0x1307c). The two traps 0x13010 / 0x13058 (data + 1, data + 2 wrap) are dead (S_E01).
   - The four blocks: pp = malloc(19744) at 0x1308c; pod = malloc(len ? len : 1) at 0x140e0 (a0 = len + (len = 0),
     0x140d8-0x140dc); out = malloc(3 (cap + 1)) at 0x14114 (a0 = s4, 0x14104-0x1410c); first = malloc(m ? m : 1),
     m = 3 max(rc, 0), at 0x147dc (0x147c0-0x147d8); free(first) 0x14830, free(out) 0x14838, free(pod) 0x14840,
     free(pp) 0x14848. hb: [] -> [pp] -> [pod; pp] -> [out; pod; pp] -> [first; out; pod; pp], LIFO.
   - Cuts: ENTRY (0x12fa8); K13090, malloc(pp)'s return (`bnez a0` there); K140e4, malloc(pod)'s return (`beqz a0`
     there); K14118, malloc(out)'s return (`beqz a0` there); K147e0, malloc(first)'s return (`beqz a0` there);
     K1482c, just after check_plain returned (0x1482c `mv a0,s7`, then free(first)); RET = Post. The size >= 2^26
     return (0x12ff0 `srli a2,a1,26`, 0x12ff8 `j 0x1484c`) passes no cut.
   - The registers and frame cells each cut names (those the code after it reads before writing them; a liveness listing of the UBSan ELF, with its artifacts sp + 0x8/1 at K13090 (0x1312c `sd s3,8(sp)` writes it first) and
     sp + 0x134..0x13c/4 (memset(x) at 0x141a4) left out), plus the spine's facts:
     K13090: a0 = pp (nonzero, 16-aligned); s6 = the cursor (data + min(n, 2)); s2 = the bytes left; s3 = cap
       (stored at 0x1312c `sd s3,8(sp)`); the cell sp + 0x10 = 1 - null as 8 bytes; s1 = 19744 (memset's size,
       0x130a0); s0 = 0x5000 (0x131f8 `addiw a0,s0,-0x2ec`);
     K140e4: a0 = pod (nonzero, 16-aligned); s3 = len (0x13fb8 / 0x140cc `ld s3,0(s7)`); s7 = pp + 0x4000 (&len;
       is_props / params_struct at 0x141b4 / 0x141bc); s8 = pp (memcpy's source, 0x140f8); the cells sp + 0x8 =
       cap (0x140ec `lbu s2,8(sp)`), sp + 0x10 = 1 - null (0x1413c), sp + 0x68 = pp + 0x4d14 (&n_ent; corrupt at
       0x1418c-0x14190, n_ent at 0x14254-0x14268), sp + 0x70 = pp (0x14244; free(pp)'s argument, 0x14844),
       sp + 0x78 = pp + 0x4000 (0x14764); the pp block = pp_bytes of the record;
     K14118: a0 = out (nonzero, 16-aligned); s0 = 3 cap (0x14168 `add a0,s3,s0`); s1 = pod; s2 = cap; s4 = 3 cap + 3
       (0x14124, 0x14804); s7 = pp + 0x4000; the cells sp + 0x10, sp + 0x68, sp + 0x70, sp + 0x78; the pp block
       and the pod block = buf r, pod nonzero and 16-aligned;
     K147e0: a0 = first (nonzero, 16-aligned), first's size nf = first_req rc; s1 = pod; s2 = cap; s3 = out;
       s4 = 3 cap + 3; s5 = (null ? 0 : pod) (0x14140-0x14144); s6 = rc; s8 = 3 max(rc, 0); the cell
       sp + 0x70 = pp; the pod block = buf r, out = the first parse's cells as bytes then 0xa5, pod and out nonzero
       and 16-aligned, errno a readable and writable cell; any FP state with rounding mode 0;
     K1482c: s7 = first, s3 = out, s1 = pod and the cell sp + 0x70 = pp (0x14844 `ld a0,0x70(sp)`). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import Mem Frame Cells Step.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import SlotFR.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Model Layout Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import reac_headamp_prop_parse_result_c.
Import ListNotations.
Open Scope Z_scope.

(* struct pod_props: 19744 bytes; len at 0x4000, n_ent at 0x4d14 (corrupt at 0x4d18). *)
Definition POD_PROPS : Z := 19744.
Definition POD_LEN_OFF : Z := 0x4000.
Definition POD_NENT_OFF : Z := 0x4d14.

(* The record, its length, the parse's answer, out's size and bytes, first's request: as in the plain file. *)
Definition head_rec (inp : list byte) : pod_rec := fst (pod_build inp).
Definition head_len (inp : list byte) : Z := Z.of_nat (length (buf (head_rec inp))).
Definition head_ans (nl cap : Z) (inp : list byte) : answer :=
  parse_props (parse_arg (nl =? 1) (buf (head_rec inp))) cap.
Definition OUT_LEN (cap : Z) : Z := 3 * (cap + 1).
Definition out_after (cap : Z) (o : answer) : list byte :=
  ha_cells_bytes (ans_cells o) ++
  repeat GUARD_BYTE (Z.to_nat (OUT_LEN cap) - length (ha_cells_bytes (ans_cells o))).
Definition first_req (rc : Z) : Z := if 0 <? rc then 3 * rc else 1.

(* The headamp quantities of the input, as in the plain file. *)
Definition g_b0 (g : ghost) : Z := fst (Cursor.fuzz_u8 (g_in g)).
Definition g_null (g : ghost) : Z := Z.land (g_b0 g) 1.
Definition g_cap (g : ghost) : Z := fst (Cursor.fuzz_u8 (snd (Cursor.fuzz_u8 (g_in g)))) mod 10.
Definition g_rest (g : ghost) : list byte := snd (Cursor.fuzz_u8 (snd (Cursor.fuzz_u8 (g_in g)))).
Definition g_src (g : ghost) : Z := g_p g + Z.min 2 (g_n g).
Definition g_k (g : ghost) : Z := g_n g - Z.min 2 (g_n g).
Definition g_rec (g : ghost) : pod_rec := head_rec (g_rest g).
Definition g_len (g : ghost) : Z := head_len (g_rest g).
Definition g_ans (g : ghost) : answer := head_ans (g_null g) (g_cap g) (g_rest g).

Definition hb_pp (pp : Z) : list (Z * Z) := [(pp, POD_PROPS)].
Definition hb_pod (g : ghost) (pod pp : Z) : list (Z * Z) := [(pod, g_len g); (pp, POD_PROPS)].
Definition hb_out (g : ghost) (out pod pp : Z) : list (Z * Z) := (out, OUT_LEN (g_cap g)) :: hb_pod g pod pp.
Definition hb_first (g : ghost) (first nf out pod pp : Z) : list (Z * Z) := (first, nf) :: hb_out g out pod pp.

Section Slot.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.

(* K13090, malloc(pp)'s return (0x1308c `jal malloc` with a0 = 19744). *)
Definition Inv_K13090 (g : ghost) (c : config) : Prop :=
  exists pp, CUTST B APIf ra empty g 0x13090 (hb_pp pp) (fun regs m =>
    rg regs 10 pp /\ pp <> 0 /\ pp mod 16 = 0 /\
    rg regs 22 (g_src g) /\ rg regs 18 (g_k g) /\ rg regs 19 (g_cap g) /\
    bytes_at rsegs m (fsp g + 0x10) (le8 (Z_to_bv 64 (1 - g_null g))) /\
    rg regs 9 POD_PROPS /\ rg regs 8 0x5000) c.

(* K140e4, malloc(pod)'s return (0x140e0 `jal malloc` with a0 = len): the record in the pp block. *)
Definition Inv_K140e4 (g : ghost) (c : config) : Prop :=
  exists pp pod, CUTST B APIf ra empty g 0x140e4 (hb_pod g pod pp) (fun regs m =>
    rg regs 10 pod /\ pod <> 0 /\ pod mod 16 = 0 /\
    rg regs 19 (g_len g) /\ rg regs 23 (pp + POD_LEN_OFF) /\ rg regs 24 pp /\
    bytes_at rsegs m (fsp g + 0x8) (le8 (Z_to_bv 64 (g_cap g))) /\
    bytes_at rsegs m (fsp g + 0x10) (le8 (Z_to_bv 64 (1 - g_null g))) /\
    bytes_at rsegs m (fsp g + 0x68) (le8 (Z_to_bv 64 (pp + POD_NENT_OFF))) /\
    bytes_at rsegs m (fsp g + 0x70) (le8 (Z_to_bv 64 pp)) /\
    bytes_at rsegs m (fsp g + 0x78) (le8 (Z_to_bv 64 (pp + POD_LEN_OFF))) /\
    bytes_at rsegs m pp (pp_bytes (g_rec g))) c.

(* K14118, malloc(out)'s return (0x14114 `jal malloc` with a0 = 3 cap + 3). *)
Definition Inv_K14118 (g : ghost) (c : config) : Prop :=
  exists pp pod out, CUTST B APIf ra empty g 0x14118 (hb_out g out pod pp) (fun regs m =>
    rg regs 10 out /\ out <> 0 /\ out mod 16 = 0 /\
    rg regs 8 (3 * g_cap g) /\ rg regs 9 pod /\ pod <> 0 /\ pod mod 16 = 0 /\ rg regs 18 (g_cap g) /\
    rg regs 20 (OUT_LEN (g_cap g)) /\ rg regs 23 (pp + POD_LEN_OFF) /\
    bytes_at rsegs m (fsp g + 0x10) (le8 (Z_to_bv 64 (1 - g_null g))) /\
    bytes_at rsegs m (fsp g + 0x68) (le8 (Z_to_bv 64 (pp + POD_NENT_OFF))) /\
    bytes_at rsegs m (fsp g + 0x70) (le8 (Z_to_bv 64 pp)) /\
    bytes_at rsegs m (fsp g + 0x78) (le8 (Z_to_bv 64 (pp + POD_LEN_OFF))) /\
    bytes_at rsegs m pp (pp_bytes (g_rec g)) /\
    bytes_at rsegs m pod (buf (g_rec g))) c.

(* K147e0, malloc(first)'s return (0x147dc `jal malloc` with a0 = first_req rc). *)
Definition Inv_K147e0 (g : ghost) (c : config) : Prop :=
  exists pp pod out first nf, CUTST B APIf ra empty g 0x147e0 (hb_first g first nf out pod pp) (fun regs m =>
    rg regs 10 first /\ first <> 0 /\ first mod 16 = 0 /\ nf = first_req (ans_rc (g_ans g)) /\
    rg regs 9 pod /\ pod <> 0 /\ pod mod 16 = 0 /\ rg regs 18 (g_cap g) /\
    rg regs 19 out /\ out <> 0 /\ out mod 16 = 0 /\ rg regs 20 (OUT_LEN (g_cap g)) /\
    rg regs 21 (if g_null g =? 1 then 0 else pod) /\ rg regs 22 (ans_rc (g_ans g)) /\
    rg regs 24 (3 * Z.max (ans_rc (g_ans g)) 0) /\
    bytes_at rsegs m (fsp g + 0x70) (le8 (Z_to_bv 64 pp)) /\
    bytes_at rsegs m pod (buf (g_rec g)) /\
    bytes_at rsegs m out (out_after (g_cap g) (g_ans g)) /\
    (exists ev, rw_cells rsegs m (errno_addr B) [C4 ev])) c.

(* K1482c, after check_plain, before free(first) (0x1482c `mv a0,s7`; 0x14830 `jal free`). *)
Definition Inv_K1482c (g : ghost) (c : config) : Prop :=
  exists pp pod out first nf, CUTST B APIf ra empty g 0x1482c (hb_first g first nf out pod pp) (fun regs m =>
    rg regs 23 first /\ rg regs 19 out /\ rg regs 9 pod /\
    bytes_at rsegs m (fsp g + 0x70) (le8 (Z_to_bv 64 pp))) c.

End Slot.
