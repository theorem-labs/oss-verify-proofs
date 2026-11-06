(* Cut invariants of reac-pw/fuzz_headamp LLVMFuzzerTestOneInput (plain, [0x12f88, 0x14680); fuzz_headamp.c:311-360):
   the headamp quantities of the ghost and one Inv_<cut> per cut between ENTRY and RET, each a CUTST of Prog/SlotFR.v
   (FR over the live harness blocks hb, at some FP state with rounding mode 0). Statement text: no function is proved
   here. The form is reac-pw/fuzz_role's Prog/SlotInv.v, with headamp's
   four live blocks. Addresses: the plain ELF, unstripped sha256 fe40c856bfc73f2b..., pinned sha256 61497eebc35c...
   - The input: null = fuzz_u8 & 1 (fuzz_headamp.c:316), cap = fuzz_u8 % 10 (:317), fuzz.h's fuzz_u8 (fuzz.h:37-43:
     0 and no advance when no byte is left; Pod/Cursor.v fuzz_u8); pod_build (:322) reads the bytes after those two.
     The code: 0x12fd8 `mv s3,a0`; n = 0: s7 = s2 = s6 = 0 (0x13000-0x13008); n = 1: s7 = data[0] & 1, s2 = s6 = 0,
     s3 = data + 1 (0x12fe0-0x12ff8); n >= 2: s7 = data[0] & 1 (0x12fe8), s2 = n - 2, s3 = data + 2, s6 = data[1] -
     10 (data[1] * 0xcd >> 11) = data[1] mod 10 (0x13010-0x13030).
   - The four blocks, freed in the reverse order (LIFO): pp = malloc(19744) (0x13040, a0 = s1 = 5 << 12 - 0x2e0);
     pod = malloc(len ? len : 1) (0x14048, a0 = len + (len = 0), 0x14040-0x14044; len = pp->len in [8, 5440], so the
     request is len); out = malloc(3 (cap + 1)) (0x1407c, a0 = s4 = 3cap + 3, 0x1406c-0x14074;
     sizeof(struct reac_headamp_setting) = 3); first = malloc(m ? m : 1) with m = 3 max(rc, 0) (0x14164, a0 = s8 +
     (s8 = 0), 0x14148-0x14160); free(first) 0x141b8, free(out) 0x141c0, free(pod) 0x141c8, free(pp) 0x141d0. The
     new block is at the head of hb: [] -> [pp] -> [pod; pp] -> [out; pod; pp] -> [first; out; pod; pp], and each
     free takes the head.
   - Cuts: ENTRY (0x12f88, SlotFR.Inv_ENTRY); K13044, malloc(pp)'s return (`bnez a0` there); K1404c, malloc(pod)'s
     return (`beqz a0` there); K14080, malloc(out)'s return (`beqz a0` there); K14168, malloc(first)'s return (`beqz
     a0` there); K141b4, just after check_plain returned (0x141b4 `mv a0,s7`, then free(first)); RET = SlotFR.Post.
     The size >= 2^26 return (0x12fcc `srli a2,a1,26`, 0x12fd4 `j 0x141d4`) passes no cut: the slot runs it from
     ENTRY as one evt (Prog/LLVMFuzzerTestOneInput_c.v headamp_early_contract; GV bounds g_n below 2^26 at the cuts).
   - Each cut names exactly the registers and frame cells the code after it reads before writing them (checked on
     the disassembly of the plain ELF; a liveness listing of it, with its callee-store artifacts sp + 0x40/4 and
     sp + 0x10c..0x114/4 left out: memset(x) at 0x140fc and the `sd` at 0x14574 write them first), plus what the next
     segment's spine needs to cross the cut:
     K13044: a0 = pp (nonzero, 16-aligned: malloc_ret); s3 = the cursor (data + min(n, 2)); s2 = the bytes left
       (n - min(n, 2)); s7 = null (0 or 1); s6 = cap (0..9); s1 = 19744 (memset's size, 0x13064); s0 = 0x5000
       (0x13050 `addiw s0,s0,-0x2ec` makes &n_ent's offset 0x4d14);
     K1404c: a0 = pod (nonzero, 16-aligned); s4 = len (0x14034 `ld s4,0(s2)`); s5 = pp (memcpy's source, 0x14060);
       s6 = cap (0x14054 `andi s2,s6,0xff`); s7 = null; s8 = pp + 0x4d14 (&n_ent; corrupt at 4(s8), 0x140e8; n_ent
       at 0(s8), 0x14234); the cells sp + 0x50 = pp + 0x4000 (&len; is_props at 8, params_struct at 0x10, read at
       0x14220-0x1422c) and sp + 0x58 = pp (0x13188 `sd s5,0x58(sp)`; free(pp)'s argument, 0x141cc); and the pp
       block's 19744 bytes = Pod.Layout.pp_bytes of the record pod_build made of the bytes after the first two
       (FR does not carry a harness block's bytes; malloc keeps the other blocks' bytes);
     K14080: a0 = out (nonzero, 16-aligned); s0 = 3 cap (&out[cap] = out + s0, 0x140c4); s1 = pod; s2 = cap;
       s4 = 3 cap + 3 (memset's size, 0x1408c and 0x1418c); s7 = null (0x140a4, 0x14104); s8 = pp + 0x4d14; the
       cells sp + 0x50, sp + 0x58; the pp block (expect_of reads it) and the pod block = Pod.Model.buf of the record
       (memcpy(pod, pp, len) at 0x14068), pod nonzero and 16-aligned (the parse's premise);
     K14168: a0 = first (nonzero, 16-aligned) with first's size nf = 1 or 3 rc (first_req rc); s1 = pod (free(pod),
       0x141c4); s2 = cap; s3 = out; s4 = 3 cap + 3; s5 = (null ? 0 : pod) (the plain parse's a0, 0x14194);
       s6 = rc = the first parse's answer, ans_rc (parse_props (parse_arg null (buf r)) cap) (memcpy's guard
       0x14170, check_plain's a1); s8 = 3 max(rc, 0) (memcpy's size, 0x1417c); the cell sp + 0x58 = pp; and what
       the spine needs past the cut: the pod block = buf r (the second parse reads it), out's 3 cap + 3 bytes = the
       first parse's cells as bytes (Spec/HeadBytes.v ha_cells_bytes) then 0xa5 to the end (memcpy(first, out, 3rc)
       copies the cells, check_plain compares them), pod and out nonzero and 16-aligned, and errno a readable and
       writable 4-byte cell (the second parse calls strtol, which may write errno). The FP registers and fflags
       are those the first parse and the inlined pod_nearest's soft-float calls left: CUTST takes any FP state
       with rounding mode 0;
     K141b4: s7 = first, s3 = out, s1 = pod (free's arguments, 0x141b4, 0x141bc, 0x141c4) and the cell
       sp + 0x58 = pp (0x141cc `ld a0,0x58(sp)`). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import Mem Frame Cells Step.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import SlotFR.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Model Layout Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import reac_headamp_prop_parse_result_c.
Import ListNotations.
Open Scope Z_scope.

(* struct pod_props: 19744 bytes; len at 0x4000, n_ent at 0x4d14 (corrupt at 0x4d18) (Pod/Layout.v PP_SIZE, OFF_LEN,
   OFF_N_ENT). *)
Definition POD_PROPS : Z := 19744.
Definition POD_LEN_OFF : Z := 0x4000.
Definition POD_NENT_OFF : Z := 0x4d14.

(* The record pod_build makes of its input, its buffer length (pp->len), and the parse's answer on it for the null
   flag nl (0 or 1) and cap (fuzz_headamp.c:333: reac_headamp_prop_parse_result(null ? NULL : pod, out, cap, &res)). *)
Definition head_rec (inp : list byte) : pod_rec := fst (pod_build inp).
Definition head_len (inp : list byte) : Z := Z.of_nat (length (buf (head_rec inp))).
Definition head_ans (nl cap : Z) (inp : list byte) : answer :=
  parse_props (parse_arg (nl =? 1) (buf (head_rec inp))) cap.

(* out's size, 3 (cap + 1) (fuzz_headamp.c:326), and its bytes after memset(out, 0xa5, ..) and a parse that answered
   o: the cells as bytes, then 0xa5 to the end (the parse writes out[0, 3n) only). *)
Definition OUT_LEN (cap : Z) : Z := 3 * (cap + 1).
Definition out_after (cap : Z) (o : answer) : list byte :=
  ha_cells_bytes (ans_cells o) ++
  repeat GUARD_BYTE (Z.to_nat (OUT_LEN cap) - length (ha_cells_bytes (ans_cells o))).

(* first's request: fuzz_dup(out, 3 max(rc, 0)) asks malloc(m ? m : 1) (fuzz.h:73), so 1 for rc <= 0, else 3 rc. *)
Definition first_req (rc : Z) : Z := if 0 <? rc then 3 * rc else 1.

(* The headamp quantities of the input. *)
Definition g_b0 (g : ghost) : Z := fst (Cursor.fuzz_u8 (g_in g)).
Definition g_null (g : ghost) : Z := Z.land (g_b0 g) 1.
Definition g_cap (g : ghost) : Z := fst (Cursor.fuzz_u8 (snd (Cursor.fuzz_u8 (g_in g)))) mod 10.
Definition g_rest (g : ghost) : list byte := snd (Cursor.fuzz_u8 (snd (Cursor.fuzz_u8 (g_in g)))).
Definition g_src (g : ghost) : Z := g_p g + Z.min 2 (g_n g).
Definition g_k (g : ghost) : Z := g_n g - Z.min 2 (g_n g).
Definition g_rec (g : ghost) : pod_rec := head_rec (g_rest g).
Definition g_len (g : ghost) : Z := head_len (g_rest g).
Definition g_ans (g : ghost) : answer := head_ans (g_null g) (g_cap g) (g_rest g).

(* The live harness blocks at the cuts (the newest at the head); first's size nf is an argument, fixed by the cut. *)
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

(* K13044, malloc(pp)'s return (0x13040 `jal malloc` with a0 = 19744). *)
Definition Inv_K13044 (g : ghost) (c : config) : Prop :=
  exists pp, CUTST B APIf ra empty g 0x13044 (hb_pp pp) (fun regs m =>
    rg regs 10 pp /\ pp <> 0 /\ pp mod 16 = 0 /\
    rg regs 19 (g_src g) /\ rg regs 18 (g_k g) /\ rg regs 23 (g_null g) /\ rg regs 22 (g_cap g) /\
    rg regs 9 POD_PROPS /\ rg regs 8 0x5000) c.

(* K1404c, malloc(pod)'s return (0x14048 `jal malloc` with a0 = len): the record in the pp block. *)
Definition Inv_K1404c (g : ghost) (c : config) : Prop :=
  exists pp pod, CUTST B APIf ra empty g 0x1404c (hb_pod g pod pp) (fun regs m =>
    rg regs 10 pod /\ pod <> 0 /\ pod mod 16 = 0 /\
    rg regs 20 (g_len g) /\ rg regs 21 pp /\ rg regs 22 (g_cap g) /\ rg regs 23 (g_null g) /\
    rg regs 24 (pp + POD_NENT_OFF) /\
    bytes_at rsegs m (fsp g + 0x50) (le8 (Z_to_bv 64 (pp + POD_LEN_OFF))) /\
    bytes_at rsegs m (fsp g + 0x58) (le8 (Z_to_bv 64 pp)) /\
    bytes_at rsegs m pp (pp_bytes (g_rec g))) c.

(* K14080, malloc(out)'s return (0x1407c `jal malloc` with a0 = 3 cap + 3): the record in pp, its buffer in pod. *)
Definition Inv_K14080 (g : ghost) (c : config) : Prop :=
  exists pp pod out, CUTST B APIf ra empty g 0x14080 (hb_out g out pod pp) (fun regs m =>
    rg regs 10 out /\ out <> 0 /\ out mod 16 = 0 /\
    rg regs 8 (3 * g_cap g) /\ rg regs 9 pod /\ pod <> 0 /\ pod mod 16 = 0 /\ rg regs 18 (g_cap g) /\
    rg regs 20 (OUT_LEN (g_cap g)) /\ rg regs 23 (g_null g) /\ rg regs 24 (pp + POD_NENT_OFF) /\
    bytes_at rsegs m (fsp g + 0x50) (le8 (Z_to_bv 64 (pp + POD_LEN_OFF))) /\
    bytes_at rsegs m (fsp g + 0x58) (le8 (Z_to_bv 64 pp)) /\
    bytes_at rsegs m pp (pp_bytes (g_rec g)) /\
    bytes_at rsegs m pod (buf (g_rec g))) c.

(* K14168, malloc(first)'s return (0x14164 `jal malloc` with a0 = first_req rc), after the first parse and every
   check that compares with it: rc, the cells in out, the pod bytes for the second parse, errno a cell. *)
Definition Inv_K14168 (g : ghost) (c : config) : Prop :=
  exists pp pod out first nf, CUTST B APIf ra empty g 0x14168 (hb_first g first nf out pod pp) (fun regs m =>
    rg regs 10 first /\ first <> 0 /\ first mod 16 = 0 /\ nf = first_req (ans_rc (g_ans g)) /\
    rg regs 9 pod /\ pod <> 0 /\ pod mod 16 = 0 /\ rg regs 18 (g_cap g) /\
    rg regs 19 out /\ out <> 0 /\ out mod 16 = 0 /\ rg regs 20 (OUT_LEN (g_cap g)) /\
    rg regs 21 (if g_null g =? 1 then 0 else pod) /\ rg regs 22 (ans_rc (g_ans g)) /\
    rg regs 24 (3 * Z.max (ans_rc (g_ans g)) 0) /\
    bytes_at rsegs m (fsp g + 0x58) (le8 (Z_to_bv 64 pp)) /\
    bytes_at rsegs m pod (buf (g_rec g)) /\
    bytes_at rsegs m out (out_after (g_cap g) (g_ans g)) /\
    (exists ev, rw_cells rsegs m (errno_addr B) [C4 ev])) c.

(* K141b4, after check_plain, before free(first) (0x141b4 `mv a0,s7`; 0x141b8 `jal free`). *)
Definition Inv_K141b4 (g : ghost) (c : config) : Prop :=
  exists pp pod out first nf, CUTST B APIf ra empty g 0x141b4 (hb_first g first nf out pod pp) (fun regs m =>
    rg regs 23 first /\ rg regs 19 out /\ rg regs 9 pod /\
    bytes_at rsegs m (fsp g + 0x58) (le8 (Z_to_bv 64 pp))) c.

End Slot.
