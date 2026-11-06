(* fuzz_socket (netlink.h:72-87) on image A (fuzz_link.asan 0x821cc, 196 bytes; listing
   (internal path) (internal record, sha256 c29851f5d96a)): the fake socket(). It hands out
   NL_FD = 7, or fails once with the errno the input chose. The three arguments are dead. The plain contract is
   lib/Prog/fuzz_socket_c.v; this file states the SAME link_spec result in link_amem.v's `aleaf` form.

   The image-A code, in order:
     +0x00..+0x10  push a 32-byte frame; save ra, s0..s2
     +0x14..+0x24  s0 := LA_G_NL (+0x18/+0x1c auipc/addi); s1 := lw (g_nl + 0x4020c) = socket_errno. g_nl's fields
                   are read and written at constant offsets from that address; the instrumentation leaves an
                   access at a constant offset into a global unchecked, so none of them has a shadow check.
     +0x28  beqz s1 -> +0x64
     errno arm (socket_errno <> 0):
     +0x2c..+0x34  s2 := the shadow base, loaded through the .got cell 0xa19d0 (LA_GOT_SHADOW -> LA_SHADOW_CELL)
     +0x38  jal ___errno_location (0x90a7c): a0 := tp - 164
     +0x3c..+0x48, +0xb4..+0xbc  the instrumented check of the 4-byte store to a0: shadow byte s of a0; s = 0
                   passes; else (a0 & 7) + 3 < s passes; else errpath_store4 (0x5a77c)
     +0x4c  sw s1, 0(a0)              errno := socket_errno
     +0x58  sw zero, 0x20c(g + 0x40000)   socket_errno := 0;  +0x5c a0 := -1;  j +0x9c
     ok arm (socket_errno = 0):
     +0x64  lw a0, 0x214 = open;  +0x68 beqz -> +0x7c;  +0x78 sw 1, 0x220   misuse := 1 when open <> 0
     +0x84  lw a1, 0x218 = opened;  +0x90 sw 1, 0x214 (open := 1);  +0x94 sw opened + 1, 0x218;  +0x98 a0 := 7
     +0x9c..+0xb0  restore, pop, ret.
   0x40000 + 0x20c = 262668 = NK_SOCKET_ERRNO, + 0x214 = NK_OPEN, + 0x218 = NK_OPENED, + 0x220 = NK_MISUSE
   (link_spec.v:711-716).

   Which instruction needs which premise:
   - the journal, gp/tp, ret_ok (apre): the frame stores +0x04..+0x10 (inside [sp - K, sp)); +0xb0 ret.
   - K = 32: the 32-byte frame; ___errno_location (0x90a7c, 3 instructions: lib/A/AD20.v lists it as `(0x90a7c, 3%nat)`)
     pushes nothing. No realignment. link-a/form/FORM.md (internal record, sha256 13aeff774164) section 5: 32.
   - `exists bs, anlk_at m LA_G_NL bs`: the loads +0x24, +0x64, +0x84 and the stores +0x58, +0x78, +0x90, +0x94
     (bytes readable and writable).
   - `nlk_wf bs`: carried for the Post's `nlk_wf bs'` (the stores keep open and misuse in 0..1, socket_errno 0).
   - `nk_opened bs + 1 < 2 ^ 31`: +0x8c `addi a1, a1, 1` then the 4-byte store +0x94; it keeps the Post's `nk_opened bs' = nk_opened bs + 1`
     exact and nlk_wf's bound true (link-a/plan/CONTRACTS.md (internal record, sha256 5cd783c633c3) section 5, UTwinsA).
   - errno (slice convention C1, link-a/contracts/kernel.md (internal record, sha256 977f60b79b94)): `as_errno B = as_tp B - 164`:
     ___errno_location answers tp - 164 and apre gives tp = as_tp B, so the store +0x4c goes to as_errno B, the address the
     journal and `akept` except; `awrange m (as_errno B) 4`: +0x4c's store; `range_addressable (ard m) SHADOW_OFF (as_errno B) 4`:
     the check +0x3c..+0x48 passes (YG0v.v saddr_ok: s = 0, or (a & 7) + 3 < s); `apart_frame regs K (as_errno B) 4` and
     `apart_gnl LA_G_NL (as_errno B) 4`: the frame stores and the g_nl stores do not touch errno, and the store to errno
     does not touch g_nl (the plain separations, link-a/plan/CONTRACTS.md (internal record, sha256 5cd783c633c3) section 5).
   - the write set [LA_G_NL + NK_SOCKET_ERRNO, LA_G_NL + NK_MISUSE + 4) and apre's `ajw` on it: the stores +0x58,
     +0x78, +0x90, +0x94. Image bytes: `ajw` holds of them only through `inG G` (LA_G holds all of g_nl).
   - registers: +0x5c a0 := -1, +0x98 a0 := 7 (the Post's result).
   EV = 0 (no allocator event), SIDE = [] (no frame_alloc).

   What does NOT carry over from the plain text:
   - errno in the write set. The plain Wr has (errno_at regs, errno_at regs + 4). On image A the write set is also
     the premise `ajw`, which no byte of errno meets (errno is an image byte outside LA_G, outside the window, in no
     block and no frame); the journal (Reusable/YCbq.v:359) and `akept` (link_amem.v) already except
     [as_errno B, as_errno B + 4) in their image clauses, so the store needs no write-set entry.
   - `frame_apart_gnl regs 32` (link-a/form/FORM.md (internal record, sha256 13aeff774164) section 1a): the window is on
     the real stack above alloc_ceiling (`astk_ok`, YCbq.v:330-332) and g_nl is an image byte.
   - `errno_at regs` (tp - 164) is restated as `as_errno B` with the premise tying the two.

   Satisfiability witness (a run; lib/A/Prog/kernel_witness.v `fuzz_socket_apre_sat` closes the function-specific part):
   nl_talk's first call, 0x88a38 area, in the run of link-a/form/WITNESS.md (internal record, sha256 b8aaf8151f7f) section
   1, before the socket opens: g_nl as kernel() and interfaces() left it (open = 0, opened = 0, closed = 0, misuse = 0,
   socket_errno = 0 or an nl_errno_tab value); errno at TFIB_ERRNO = 0x631b6c in musl's static TLS (.bss, writable, shadow 0
   like every byte of the image outside the instrumented globals' redzones); sp = nl_talk's realigned sp on the real stack.
   The journal part is LLVMFuzzerTestOneInput's, as link-a/form/WITNESS.md (internal record, sha256 b8aaf8151f7f) section 1.
   Proves no function (kind: statement text). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YI16 YM05 YG0v YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem.
Import ListNotations.
Local Open Scope Z_scope.

Definition FUZZ_SOCKET_A : Z := 0x821cc.
Lemma FUZZ_SOCKET_A_is_entry : FUZZ_SOCKET_A = LA_fuzz_socket. Proof. reflexivity. Qed.

(* the stack bound on image A: the 32-byte frame; ___errno_location pushes nothing *)
Definition FUZZ_SOCKET_AK : Z := 32.

(* the write set: g_nl's socket_errno .. misuse words (as the plain contract's, without errno: see the header) *)
Definition fuzz_socket_awr (regs : bvmap 5 word) (m : word -> option byte) : list (Z * Z) :=
  [(LA_G_NL + NK_SOCKET_ERRNO, LA_G_NL + NK_MISUSE + 4)].

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Variable segs : list Segment.
Variables rlo rhi : Z.
Variable B : asyms.

Definition fuzz_socket_apre (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  exists bs, anlk_at segs m LA_G_NL bs /\ nlk_wf bs /\ nk_opened bs + 1 < 2 ^ 31
    /\ as_errno B = as_tp B - 164
    /\ awrange segs m (as_errno B) 4
    /\ range_addressable (ard segs m) SHADOW_OFF (as_errno B) 4
    /\ apart_frame regs FUZZ_SOCKET_AK (as_errno B) 4 /\ apart_gnl LA_G_NL (as_errno B) 4.

Definition fuzz_socket_apost (regs : bvmap 5 word) (m : word -> option byte)
    (regs' : bvmap 5 word) (m' : word -> option byte) : Prop :=
  forall bs, anlk_at segs m LA_G_NL bs -> exists bs', anlk_at segs m' LA_G_NL bs'
    /\ nlk_wf bs'
    /\ nk_send_errno bs' = nk_send_errno bs /\ nk_end_errno bs' = nk_end_errno bs
    /\ nk_closed bs' = nk_closed bs
    /\ (nk_socket_errno bs <> 0 ->
          getr regs' 10 = w64 (-1) /\ nk_socket_errno bs' = 0
          /\ au32_at segs m' (as_errno B) (nk_socket_errno bs)
          /\ nk_open bs' = nk_open bs /\ nk_opened bs' = nk_opened bs
          /\ nk_misuse bs' = nk_misuse bs)
    /\ (nk_socket_errno bs = 0 ->
          getr regs' 10 = w64 NL_FD /\ nk_socket_errno bs' = 0
          /\ nk_open bs' = 1 /\ nk_opened bs' = nk_opened bs + 1
          /\ nk_misuse bs' = (if nk_open bs =? 0 then nk_misuse bs else 1)).

Definition fuzz_socket_acontract : Prop :=
  aleaf SK segs rlo rhi B FUZZ_SOCKET_A FUZZ_SOCKET_AK 0 [] fuzz_socket_apre fuzz_socket_awr fuzz_socket_apost.

End c.
