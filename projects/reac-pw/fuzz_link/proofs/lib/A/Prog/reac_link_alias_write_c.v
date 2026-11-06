(* reac_link_alias_write (reac_link_alias.c:121-149) on image A (fuzz_link.asan 0x88f54, 1252 bytes; listing
   (internal path) (internal record, sha256 0b8d5e317aa8)): the library sets one
   netdev's interface alias over rtnetlink; an empty alias removes it. a0 = name, a1 = alias. The plain contract is
   lib/Prog/reac_link_alias_write_c.v; this file states the SAME link_spec result (`write_lib`) in the read-set
   form `aleaf_rd` of link_amem.v (link-a/form/FORM.md (internal record, sha256 13aeff774164) section 11).

   The image-A code, in order:
     +0x00..+0x2c  push a 96-byte frame (+0x04 probes it); save ra, s0..s8
     +0x30  s0 := the entry sp;  +0x34 `andi sp, sp, -0x20` (sp down by 0 or 16);  +0x38 s1 := sp
     +0x3c  s4 := alias;  +0x40..+0x54 the side-stack switch (.got+0xb8) and the shadow base (.got+0x60, into s7);
     +0x58  s6 := name
     +0x5c  `beqz a2` -> the real-stack arm +0x70..+0x94 (a 416-byte frame carved below sp)
     +0x60..+0x64  frame_alloc_3(0x1a0 = 416) (0x3dc18): the class-3 side frame (512 bytes), into s3 and s8
     +0x98..+0xc4  the frame's magic, descriptor 0x123b0 and pc stored at s8 + 0, 8, 16
     +0xa8..+0x1a0  its shadow: 0xf1 x 4 (left redzone [s8, s8 + 32)), 0xf8 x 37 (the 292-byte request at s8 + 32,
                   out of scope), 0xf3 x 11 (right redzone [s8 + 328, s8 + 416))
     +0x1a4  s5 := -22;  +0x1a8 `beqz name` -> +0x3a4
     +0x1ac..+0x1b8  the instrumented check of the 1-byte load of name[0] (errpath_load1 0x5a31c at +0x4e0)
     +0x1bc  `beqz alias` -> +0x3a4;  +0x1c0 `lbu name[0]`; +0x1c4 `beqz` -> +0x3a4
     +0x1c8..+0x1cc  wrapper_strlen(alias) (0x43044);  +0x1d0..+0x1d8 a length above 255: s5 := -36, -> +0x3a4
     +0x1e4..+0x1e8  fuzz_if_nametoindex(name) (0x826cc); +0x1ec `beqz` -> +0x3a0 (s5 := -19)
     +0x1f4..+0x28c  s6 := s8 + 32 (the request); its shadow := 0 x 36 and 4 (292 bytes usable, in scope)
     +0x290..+0x29c  checked_memset(req + 12, 0, 280) (0x53214)
     +0x2a0..+0x2c4  rta_type 20 (IFLA_IFALIAS) at +0x22, type 16 (RTM_NEWLINK) with flags 5 (NLM_F_REQUEST |
                   NLM_F_ACK) at +4, seq 1 at +8, ifi_index at +0x14, rta_len = len + 4 at +0x20
     +0x2c8..+0x2d4  checked_memcpy(req + 36, alias, len) (0x52d78)
     +0x2d8..+0x2e4  nlmsg_len := 32 + ((len + 7) & 0x1fc) stored at req + 0
     +0x2e8..+0x2fc  nl_talk(req, nlmsg_len, 0, 0, 0, 0) (0x88974): no kind, no alias buffer;  +0x300 s5 := a0
     +0x304..+0x398  the request's shadow := 0xf8 (out of scope)
     +0x3a4..+0x3ac  the retired magic 0x45e0360e stored at s8
     +0x3b0  `beqz s3` -> +0x3cc (real-stack arm: the frame's 52 shadow bytes := 0)
     +0x3b4..+0x3bc  meta_fill_f5(shadow, 64) (0x55f7c: the 512-byte frame's shadow := 0xf5);
     +0x3c0..+0x3c4  `ld a0, 0x1f8(s3); sb zero, 0(a0)`: the frame's flag := 0 (the inline release)
     +0x49c..+0x4d0  a0 := s5; restore s0..s8, ra; pop; ret.

   The real-stack arm is not taken under the premises (link-a/form/FORM.md (internal record, sha256 13aeff774164) section
   4.2): AR's const law holds the switch cell at 1 and `aside_room Sc [(3, 1); ...]` gives frame_alloc_3 a frame.

   Which instruction needs which premise:
   - the journal, gp/tp, ret_ok, the window (apre): the frame stores +0x04..+0x2c in [sp - 96, sp); +0x4d0 ret.
   - K = 96 + 16 + NL_TALK_AK = 8560: the frame, the realignment slack of +0x34, nl_talk's 8448 (nl_talk_c.v), the
     deepest callee window. The others: fuzz_if_nametoindex 8272, wrapper_strlen ESTACK (link's
     lib/A/Rt/RtString.v:74-84 astrlen_realizes, `PRE (ESTACK)`), checked_memset, checked_memcpy, frame_alloc_3,
     meta_fill_f5 ESTACK. The plain K (16928) does not carry over.
   - SIDE = [(3, 1); (9, 1)]: the own class-3 frame, then nl_talk's class-9 frame while it is live. EV = 0.
   - `astr_arg m name nm`; for `nm = Some s`: `achk m name (|s| + 1)`, `|s| + 1 < 2 ^ 32` and the TAIL (every byte
     after the NUL up to the end of its 8-byte granule visible): the check +0x1ac..+0x1b8 and fuzz_if_nametoindex's
     strcmp wrapper (fuzz_if_nametoindex_apre's `astrcmp_arg_ni`, in fuzz_if_nametoindex_c.v,
     with link's strcmp contract's `atail_vis`); `apart_frame regs K name`, `apart_gnl` (the
     plain separations). The tail is a visibility premise at entry, not in the read set: the account of
     reac_link_alias_read_c.v ("THE TAIL BYTES ...") holds word for word here (the library walks' integration build,
     2026-10-30, reac_link_alias_writeArmsD.v: without it the call +0x1e8 cannot meet `astrcmp_arg_ni`).
   - `astr_arg m alias al`; for `al = Some s`: `achk m alias (|s| + 1)`, `|s| + 1 < 2 ^ 32` and the bytes after the NUL
     up to the next multiple of 8 (the plain `slack`, LinkHelpers' STRLEN'S SLACK): the strlen wrapper (+0x1cc; the
     released form reads [alias, alias + |s| + 1) checked and the tail of its last granule, RtString.v
     astrlen_realizes `RD`, `atail_vis`) and checked_memcpy's source [alias, alias + |s|) (YG0d.v:332-333);
     `apart_frame regs K alias`, `apart_gnl`: the frame stores and the callees' g_nl stores keep it.
   - the interface table: `anlk_at`, `aiftab_at m LA_G_NL kbs tab`, g_nl's shadow usable and visible, per string the
     plain separations and, for the p `au64_at` fixes in [0, 2 ^ 64), `0 < p`, `|n2| + 1 < 2 ^ 32`, `achk m p (|n2| + 1)`
     and the same tail clause: fuzz_if_nametoindex's Pre (as reac_link_alias_read_c.v); the positive clause is stated for
     0 <= p < 2 ^ 64 only (link-a/plan/CONTRACTS.md (internal record, sha256 5cd783c633c3) 6a: `au64_at` fixes p modulo 2 ^ 64).
   - `anlk_at`, `nlk_wf`, `nk_open = 0`, the two count bounds, errno (`aerrno_ok`, nl_talk_c.v): nl_talk's Pre (its
     request is in this function's live class-3 frame, so its read set is `akb`; its two buffers are NULL).
   - the READ SET (`reac_link_alias_write_ard`): the name and the alias through their NULs (when not NULL) and
     every table string through its NUL. frame_alloc_3 (+0x64) and the stores +0x98..+0x1a0 into the frame it hands
     out and its shadow come BEFORE the reads of name (+0x1c0, +0x1e8), alias (+0x1cc, +0x2d4) and the table
     (+0x1e8); `akb` excludes a free side frame or free heap holding them, and makes akept keep the table strings for
     the Post's `aiftab_at m' kbs' tab`.
   - the write set: g_nl's [LA_G_NL, LA_G_NL + NK_N_SENT + 4) (nl_talk's callees).

   What does NOT carry over from the plain text:
   - errno in the write set (as nl_talk_c.v); `errno_at regs` is `as_errno B` with `as_errno B = as_tp B - 164`.
   - `frame_apart_gnl regs 16928` (link-a/form/FORM.md (internal record, sha256 13aeff774164) section 1a). The plain K.
   Every plain Post conjunct carries over unchanged in content, over the A views.

   Satisfiability witness (a run; lib/A/Prog/alib_witness.v `reac_link_alias_write_apre_sat` closes the
   function-specific part at a memory holding these values): LLVMFuzzerTestOneInput's call at 0x83868 (op_write) in
   the run of link-a/form/WITNESS.md (internal record, sha256 b8aaf8151f7f) section 1. Registers: ra = 0x8386c; a0 = the
   name op_write takes from its names table (the lemma: g_names[2] = "nl2"); a1 = the alias text_of returned, here a
   .rodata `texts` entry (the lemma: texts[7] = "vlan" at 0x211c0, its NUL at 0x211c4, then 0x211c5..0x211c7 in .rodata:
   strlen's slack); sp = LLVMFuzzerTestOneInput's sp; gp, tp the image's. Memory (g_nl and its interfaces() table,
   errno, shadow), journal and G as in reac_link_alias_read_c.v's witness, and for the alias: "vlan" is an instrumented
   .rodata global of size 5, so shadow(0x211c0) = 0x05 (AF0m.v:867), which `saddr_ok`
   accepts for its 5 bytes; `aside_room Sc [(3, 1); (9, 1)]` is 0 + 1 <= 2048 and 0 + 1 <= 32; the read set (name,
   alias, table strings, through their NULs) is `akb` by the image clause (Tfib_owned_static meets none of those
   bytes; its row (0x211c5, 0x1b), "vlan"'s redzone, holds the slack, which is not in the read set: the Pre asks
   only that those .rodata bytes be readable). The text_of arm that copies input bytes into a fresh malloc(s1 + 1)
   block is not used here; it meets `slack` too: the bytes past the block's requested size are not client bytes
   (YG0n.v:230-232), but the alias-write walk's `awc_blk_tail_vis` (proved in
   reac_link_alias_writeArmsC.v:100-120, Qed) makes [p + req_size, p + round_up(req_size, 16)) visible at every AR
   state (a second comparer, 2026-10-30; this was the first comparer's open remark 5).

   Proves no function (kind: statement text). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YI16 YM05 YG0v YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem nl_talk_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition REAC_LINK_ALIAS_WRITE_A : Z := 0x88f54.
Lemma REAC_LINK_ALIAS_WRITE_A_is_entry : REAC_LINK_ALIAS_WRITE_A = LA_reac_link_alias_write.
Proof. reflexivity. Qed.

(* the stack bound on image A: the 96-byte frame, the realignment slack of +0x34, nl_talk's window *)
Definition REAC_LINK_ALIAS_WRITE_AFRAME : Z := 96.
Definition REAC_LINK_ALIAS_WRITE_ASLACK : Z := 16.
Definition REAC_LINK_ALIAS_WRITE_AK : Z :=
  REAC_LINK_ALIAS_WRITE_AFRAME + REAC_LINK_ALIAS_WRITE_ASLACK + NL_TALK_AK.
Lemma REAC_LINK_ALIAS_WRITE_AK_val : REAC_LINK_ALIAS_WRITE_AK = 8560. Proof. reflexivity. Qed.

(* the side-stack room: the own class-3 frame and nl_talk's class-9 frame *)
Definition REAC_LINK_ALIAS_WRITE_ASIDE : list (Z * Z) := [(3, 1); (9, 1)].

(* the write set: g_nl up to n_sent *)
Definition reac_link_alias_write_awr (regs : bvmap 5 word) (m : word -> option byte) : list (Z * Z) :=
  [(LA_G_NL, LA_G_NL + NK_N_SENT + 4)].

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Variable segs : list Segment.
Variables rlo rhi : Z.
Variable B : asyms.

(* the read set: the name and the alias through their NULs, and every interface-table string through its NUL *)
Definition reac_link_alias_write_ard (regs : bvmap 5 word) (m : word -> option byte) (a : Z) : Prop :=
  (aarg regs 0 <> 0 /\ exists s, acstr_at segs m (aarg regs 0) s /\
     aarg regs 0 <= a <= aarg regs 0 + Z.of_nat (length s))
  \/ (aarg regs 1 <> 0 /\ exists s, acstr_at segs m (aarg regs 1) s /\
     aarg regs 1 <= a <= aarg regs 1 + Z.of_nat (length s))
  \/ (exists bs tab i n2 ix p, anlk_at segs m LA_G_NL bs /\ aiftab_at segs m LA_G_NL bs tab /\
        nth_error tab i = Some (n2, ix) /\ au64_at segs m (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p /\
        acstr_at segs m p n2 /\ p <= a <= p + Z.of_nat (length n2)).

Definition reac_link_alias_write_apre (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  exists kbs tab nm al,
    anlk_at segs m LA_G_NL kbs /\ nlk_wf kbs /\ nk_open kbs = 0
    /\ nk_opened kbs + 1 < 2 ^ 31 /\ nk_closed kbs + 1 < 2 ^ 31 /\ aiftab_at segs m LA_G_NL kbs tab
    /\ range_addressable (ard segs m) SHADOW_OFF LA_G_NL NK_SIZE /\ shadow_hull_vis (ard segs m) LA_G_NL NK_SIZE
    /\ aerrno_ok segs B REAC_LINK_ALIAS_WRITE_AK regs m
    /\ astr_arg segs m (aarg regs 0) nm /\ astr_arg segs m (aarg regs 1) al
    /\ (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
          au64_at segs m (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
          apart_frame regs REAC_LINK_ALIAS_WRITE_AK p (Z.of_nat (length n2) + 1)
          /\ apart_gnl LA_G_NL p (Z.of_nat (length n2) + 1)
          /\ apart (as_errno B) 4 p (Z.of_nat (length n2) + 1)
          /\ (0 <= p < 2 ^ 64 -> 0 < p /\
                Z.of_nat (length n2) + 1 < 2 ^ 32 /\ achk segs m p (Z.of_nat (length n2) + 1)
                /\ (forall a, p + Z.of_nat (length n2) < a
                              < p + Z.of_nat (length n2) - (p + Z.of_nat (length n2)) mod 8 + 8 ->
                      ard segs m a <> None)))
    /\ (forall s, nm = Some s ->
          apart_frame regs REAC_LINK_ALIAS_WRITE_AK (aarg regs 0) (Z.of_nat (length s) + 1)
          /\ apart_gnl LA_G_NL (aarg regs 0) (Z.of_nat (length s) + 1)
          /\ Z.of_nat (length s) + 1 < 2 ^ 32 /\ achk segs m (aarg regs 0) (Z.of_nat (length s) + 1)
          /\ (forall a, aarg regs 0 + Z.of_nat (length s) < a
                        < aarg regs 0 + Z.of_nat (length s) - (aarg regs 0 + Z.of_nat (length s)) mod 8 + 8 ->
                ard segs m a <> None))
    /\ (forall s, al = Some s ->
          apart_frame regs REAC_LINK_ALIAS_WRITE_AK (aarg regs 1) (Z.of_nat (length s) + 1)
          /\ apart_gnl LA_G_NL (aarg regs 1) (Z.of_nat (length s) + 1)
          /\ Z.of_nat (length s) + 1 < 2 ^ 32 /\ achk segs m (aarg regs 1) (Z.of_nat (length s) + 1))
    /\ (forall s, al = Some s -> exists slack,
          abytes segs m (aarg regs 1 + Z.of_nat (length s) + 1) slack
          /\ (- (aarg regs 1 + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack)).

Definition reac_link_alias_write_apost (regs : bvmap 5 word) (m : word -> option byte)
    (regs' : bvmap 5 word) (m' : word -> option byte) : Prop :=
  forall kbs tab nm al,
    anlk_at segs m LA_G_NL kbs -> aiftab_at segs m LA_G_NL kbs tab ->
    astr_arg segs m (aarg regs 0) nm -> astr_arg segs m (aarg regs 1) al ->
    let WR := write_lib tab nm al (nk_sent kbs) (nk_kstate kbs) in
    getr regs' 10 = w64 (w_rc WR)
    /\ (exists kbs', anlk_at segs m' LA_G_NL kbs' /\ nlk_wf kbs'
          /\ nk_chunks kbs' = nk_chunks kbs /\ nk_end_errno kbs' = nk_end_errno kbs
          /\ nk_n_if kbs' = nk_n_if kbs /\ aiftab_at segs m' LA_G_NL kbs' tab
          /\ nk_next kbs' = Z.of_nat (k_next (w_state WR))
          /\ nk_socket_errno kbs' = k_sock (w_state WR)
          /\ nk_send_errno kbs' = k_send (w_state WR)
          /\ nk_sent kbs' = w_reqs WR /\ nk_n_sent kbs' = Z.of_nat (length (w_reqs WR))
          /\ nk_open kbs' = 0 /\ nk_misuse kbs' = nk_misuse kbs
          /\ nk_opened kbs' - nk_closed kbs' = nk_opened kbs - nk_closed kbs
          /\ nk_opened kbs <= nk_opened kbs' <= nk_opened kbs + 1
          /\ ((nm = None \/ al = None \/ nm = Some []
               \/ (forall s, al = Some s -> ALIAS_MAX <= Z.of_nat (length s))
               \/ (forall s, nm = Some s -> index_of tab s = 0)) ->
                nk_opened kbs' = nk_opened kbs)).

Definition reac_link_alias_write_acontract : Prop :=
  aleaf_rd SK segs rlo rhi B REAC_LINK_ALIAS_WRITE_A REAC_LINK_ALIAS_WRITE_AK 0 REAC_LINK_ALIAS_WRITE_ASIDE
    reac_link_alias_write_apre reac_link_alias_write_ard reac_link_alias_write_awr reac_link_alias_write_apost.

End c.
