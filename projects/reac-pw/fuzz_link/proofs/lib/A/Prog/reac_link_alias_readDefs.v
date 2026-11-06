(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img at fuzz_command's ASan image end 0x606000; ajournal no longer keeps footprint (FP) bytes in the image or at or above alloc_ceiling (fp_spares FP a also requires ~ inFP FP a, and the clause for bytes at or above alloc_ceiling outside [sp0 - STK, sp0) requires ~ inFP FP a), awr_byte (and awr_ok) take the start state's side-stack frames as a new parameter and also admit footprint writes to the program's statics as_prog_static in the image, to the caller's stack above sp0 and to those caller frames (awr_prog_or_caller), acall_kept_of_journal, region_kept_stack_sub, awr_byte_present and aj_intrin_at take the matching premises, ajournal_sub_wide composes a callee whose footprint lies in what the caller may write, awr_byte_present_prog and aj_intrin_at_prog take prog_rw for stores to the statics, AR_errno_present gives the errno cell's value from errno_rom, and astack_rd/astack_pres (stack bytes readable/present from sp to the stack top) give a frame chain for any s0 but an aligned sp + 8 (chain_pre_any, achain_any) and carry across an ajournal (astack_rd_journal, astack_pres_journal). *)
(* Modified by Theorem Labs, 2026-10: the malloc/free journal lemmas (aj_free_at, aj_free_at_io, aj_free_null_at, aj_free_null_at_io, aj_malloc_at, aj_malloc_at_io, aj_malloc_at04, aj_malloc_at04_io, aj_malloc, aj_free) no longer take In (call_trace0 ...) (as_universe B); the model laws get the trace length (call_trace_len) and the contracts the event bound. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/Reusable/YCbq.v, with its module paths and module names changed; 1154 of its 1305 lines of code are new or changed and 3194 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LinkWalkSide.v, with its module names changed; 327 of its 364 lines of code are new or changed and 1268 lines of the source are left out. *)
(* reac_link_alias_read (fuzz_link.asan 0x8867c, 760 bytes; listing
   (internal path) (internal record, sha256 7c23ed8f465f)): the symbolic states of
   its image-A walk, the entry lemma, and the small byte lemmas the walk needs.

   The walk runs in six segments (the engine's own answer, measured):
     +0x000 .. +0x078  tok    -> PTS_call LS___asan_stack_malloc_1 at +0x07c
     +0x07c .. +0x114  plain  -> the branch `beqz s5` at +0x118   (the frame header and its shadow)
     +0x118 .. +0x174  tok    -> PTS_call LS_fuzz_if_nametoindex at +0x178 (the two guarded NUL stores and the
                                 name's first byte: three instrumented checks, all discharged by the shadow
                                 entries of the three pointers)
     +0x178 .. +0x1a0  plain  -> PRS_call LS___asan_memset at +0x1a4
     +0x1a4 .. +0x1dc  plain  -> PRS_call LS_nl_talk at +0x1e0
     +0x1e0 .. +0x2c4  plain  -> the `ret`
   The atoms: 0..31 are the entry registers (10 = name, 11 = kind, 12 = kind_n, 13 = alias, 14 = alias_n),
   32 = the shadow base, 40.. = the junk of the first call (44 = its a0 = the frame F), 60 = the realigned sp,
   61 = the frame's flag, 62 = SB + F / 8 (the frame's shadow, through the alias YP0i.v shadow_decl_ok),
   70 = the name's first byte.

   Proves no function (kind: segment lemma of reac_link_alias_read's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem LinkWalk link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkPi LinkWalkSide PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import reac_link_alias_read_c nl_talk_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ==========================================================================
   The symbolic data (closed: every definition below computes)
   ========================================================================== *)

Definition AR_SB : Z := 0x7fff8000.
Lemma AR_SB_eq : AR_SB = SHADOW_OFF. Proof. reflexivity. Qed.
Definition ARBx : sv := SOff 32 0.
Definition ARspan : Z * Z := (AR_SB, AR_SB + 2 ^ 44 - 1).
Definition ARP (al : Z) : afact := mkAF 4096 140737479966720 al.
Definition AR_extra : list word := [Z_to_bv 64 AR_SB].

(* the entry state: the 128-byte machine frame, the shadow-base GOT word and its cell, the side-stack switch
   GOT word and its cell *)
Definition ar_stack : YP09.region := YP09.mkRegion (Some 2%nat) (-128) 0 (-128) 0 [].
Definition ar_got : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 1)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff (A_OBJ 64) 0))].
Definition ar_cell : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 64)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))].
Definition ar_ugot : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 0)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff (A_OBJ 65) 0))].
Definition ar_ucell : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 65)) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 1))].
Definition ar_regions : smem := [ar_stack; ar_got; ar_cell; ar_ugot; ar_ucell].
Definition ar_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF AR_SB AR_SB 0)] [] [].
Definition ar_ss : sstate := mkSS AF_reac_link_alias_read sr_atoms ar_regions None ar_facts.

(* The byte lemmas the entry needs are in lib/A/Prog/LinkWalkPi.v
   (val_mem_of_rd32, rdword_of_val_mem) and the kit's YCbq (val_mem_of_rdword). *)

(* ==========================================================================
   THE CUTS between the files of the walk, in the style of libreac/fuzz_pcap's PcapSourceOpenPh.v and of the
   sibling lane's lib/A/Prog/reac_link_alias_writeDefs.v.
     MID  +0x118 `beqz s5`   the class-1 frame is taken, its header and its sixteen shadow bytes are written
     SEND +0x180 `addi s8,s10,0x20`  the name is a known interface: s7 holds its index, which is not 0
     EXIT +0x1fc `lui a1,0x45e03`    the body is done and a0 holds the return code
   ========================================================================== *)

Definition AR_CID : Z := 1.                     (* addi a0,zero,0x60; jal frame_alloc_1   +0x74, +0x78 *)
Definition AR_SZ : Z := 96.                     (* 0x60: the bytes the frame request asks for *)
Definition AR_FB : Z := 128.                    (* fs_frame_bytes 1 *)
Definition AR_SHN : Z := 16.                    (* AR_FB / 8: the frame's shadow bytes *)
Definition AR_FRAME : Z := 128.                 (* addi sp,sp,-0x80  +0x00 *)
Definition AR_FLAGPTR : Z := 120.               (* ld a1,0x78(s2)  +0x250: the frame's flag address *)
Definition AR_REQ : Z := 32.                    (* addi s8,s10,0x20  +0x180: the request inside the frame *)
Definition AR_MAGIC : Z := 0x41b58ab3.          (* lui a0,0x41b59; addiw a0,a0,-0x54d  +0xb0, +0xc0 *)
Definition AR_RETIRED : Z := 0x45e0360e.        (* lui a1,0x45e03; addiw a1,a1,0x60e  +0x1fc, +0x200 *)
Lemma AR_FB_val : fs_frame_bytes AR_CID = AR_FB. Proof. reflexivity. Qed.
Lemma AR_SHN_val : AR_FB / 8 = AR_SHN. Proof. reflexivity. Qed.

Definition AR_CUT_MID : Z := AF_reac_link_alias_read + 0x118.
Definition AR_CUT_SEND : Z := AF_reac_link_alias_read + 0x180.
Definition AR_CUT_EXIT : Z := AF_reac_link_alias_read + 0x1fc.
Lemma AR_CUTS_pin : 0x821cc + AR_CUT_MID = 0x88794 /\ 0x821cc + AR_CUT_SEND = 0x887fc
  /\ 0x821cc + AR_CUT_EXIT = 0x88878.
Proof. repeat split; reflexivity. Qed.

Section z. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section zb.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.

(* the variables of the contract, at one call *)
Record arcx := mkARCX {
  ar_G : list (Z * Z); ar_XO : Z; ar_OUT : list (Z * Z);
  ar_STK : Z; ar_sp0 : Z; ar_FP : list (Z * Z);
  ar_ly : alayout; ar_S : astate; ar_W0 : world SEGS; ar_mem0 : word -> option byte; ar_md0 : Model;
  ar_own : list (Z * Z);
  ar_lyc : alayout; ar_Sc : astate; ar_W : world SEGS; ar_memc : word -> option byte; ar_mdc : Model;
  ar_k : Z; ar_regs : bvmap 5 word }.

Definition ar_m0 (cx : arcx) : word -> option byte := rdW (ar_W cx) (ar_memc cx).
Definition ar_wr (cx : arcx) : list (Z * Z) := reac_link_alias_read_awr (ar_regs cx) (ar_m0 cx).
Definition ar_E (cx : arcx) : Z -> Prop := fun a => inFP (ar_wr cx) a.
Definition ar_sp (cx : arcx) : Z := spZ (ar_regs cx).
Definition ar_name (cx : arcx) : Z := aarg (ar_regs cx) 0.
Definition ar_kind (cx : arcx) : Z := aarg (ar_regs cx) 1.
Definition ar_kn (cx : arcx) : Z := aarg (ar_regs cx) 2.
Definition ar_alias (cx : arcx) : Z := aarg (ar_regs cx) 3.
Definition ar_an (cx : arcx) : Z := aarg (ar_regs cx) 4.
(* the realigned stack pointer s1 (+0x3c, +0x40), which every call of the body runs on *)
Definition ar_sp1 (cx : arcx) : Z := 32 * ((ar_sp cx - AR_FRAME) / 32).
(* the class-1 side frame, its flag byte and the base of its sixteen shadow bytes *)
Definition ar_F (cx : arcx) (fpos : Z) : Z := frame_addr (ar_lyc cx) AR_CID fpos.
Definition ar_FL (cx : arcx) (fpos : Z) : Z := flag_addr (ar_lyc cx) AR_CID fpos.
Definition ar_SH (cx : arcx) (fpos : Z) : Z := SHADOW_OFF + ar_F cx fpos / 8.

(* ---- the contract at the context ---- *)
Definition ar_pre (cx : arcx) : Prop :=
  apre SK SEGS PCAP_RLO PCAP_RHI B REAC_LINK_ALIAS_READ_AK 0 REAC_LINK_ALIAS_READ_ASIDE
    (ar_wr cx) (ar_G cx) (ar_XO cx) (ar_OUT cx) (ar_STK cx) (ar_sp0 cx) (ar_FP cx)
    (ar_ly cx) (ar_S cx) (ar_W0 cx) (ar_mem0 cx) (ar_md0 cx) (ar_own cx)
    (ar_lyc cx) (ar_Sc cx) (ar_W cx) (ar_memc cx) (ar_mdc cx) (ar_k cx) (ar_regs cx) /\
  (forall a, reac_link_alias_read_ard SEGS (ar_regs cx) (ar_m0 cx) a ->
     akb SEGS B (ar_lyc cx) (ar_Sc cx) (ar_sp cx - REAC_LINK_ALIAS_READ_AK) (ar_sp cx) a) /\
  reac_link_alias_read_apre SEGS B (ar_regs cx) (ar_m0 cx).

Definition ar_post (cx : arcx) : world SEGS -> config -> Prop :=
  apost SK SEGS B REAC_LINK_ALIAS_READ_AK 0 (ar_E cx)
    (ar_G cx) (ar_XO cx) (ar_OUT cx) (ar_STK cx) (ar_sp0 cx) (ar_FP cx)
    (ar_ly cx) (ar_S cx) (ar_W0 cx) (ar_mem0 cx) (ar_md0 cx) (ar_own cx)
    (ar_lyc cx) (ar_Sc cx) (ar_W cx) (ar_memc cx) (ar_mdc cx) (ar_k cx) (ar_regs cx)
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       S2 = set_fs (st_fs S2) (ar_Sc cx) /\
       Permutation (ablocks B ly2 S2) (ablocks B (ar_lyc cx) (ar_Sc cx)) /\
       reac_link_alias_read_apost SEGS (ar_regs cx) (ar_m0 cx) regs2 (rdW W2 mem2)).

(* ---- what every cut after frame_alloc_1 holds ---- *)
Definition ar_base (cx : arcx) (fpos : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
    (ms3 : machine_state) (md3 : Model) : Prop :=
  let regs := ar_regs cx in
  let R := ms_regs ms3 in
  let m3 := ms_mem ms3 in
  let rd := aview SEGS (w_H W3) m3 in
  let F := ar_F cx fpos in
  let SH := ar_SH cx fpos in
  (* the shape the engine certifies *)
  ms_resv ms3 = None /\ ms_svc_pending ms3 = None /\ ms_rom ms3 = seg_rom SEGS /\
  ms_fregs ms3 = fp_regs /\ ms_fcsr ms3 = fp_csr /\
  (* the caller's journal, with this call's frame on top of the frames its owner took *)
  ajournal_gx SEGS B (ar_G cx) (ar_XO cx) (ar_OUT cx) (ar_STK cx) (ar_sp0 cx) (ar_FP cx)
    (ar_ly cx) (ar_S cx) (ar_W0 cx) (ar_mem0 cx) (ar_md0 cx) ((AR_CID, fpos) :: ar_own cx)
    ly3 S3 W3 m3 md3 (ar_k cx) /\
  frames S3 = (AR_CID, fpos) :: frames (ar_Sc cx) /\ ~ In (AR_CID, fpos) (frames (ar_Sc cx)) /\
  (exists fs, S3 = set_fs fs (ar_Sc cx)) /\
  Permutation (ablocks B ly3 S3) (ablocks B (ar_lyc cx) (ar_Sc cx)) /\
  (* the frame-witness state apost_side and akept_drop_side (LinkWalkSide.v) ask for *)
  (exists S1 W1 mem1 md1, AR SEGS B (ar_lyc cx) S1 W1 mem1 md1 /\
     frames S1 = (AR_CID, fpos) :: frames (ar_Sc cx) /\
     ablocks B (ar_lyc cx) S1 = ablocks B (ar_lyc cx) (ar_Sc cx)) /\
  (forall c q, frame_addr ly3 c q = frame_addr (ar_lyc cx) c q) /\
  (* the registers the rest of the body and the epilogue read; s8 is NOT here: +0x180 overwrites it *)
  getr R 2 = w64 (ar_sp1 cx) /\ getr R 9 = w64 (ar_sp1 cx) /\ getr R 8 = w64 (ar_sp cx) /\
  getr R 18 = w64 F /\ getr R 26 = w64 F /\ getr R 25 = w64 SH /\
  getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 27 = getr regs 27 /\
  (* the twelve words the prologue saved: ra at sp - 8, then s0, s1, s2 .. s10 *)
  rdword rd (ar_sp cx - 8) = Some (raZ regs) /\
  (forall j, 0 <= j < 11 -> rdword rd (ar_sp cx - 16 - 8 * j) =
     Some (bv_unsigned (getr regs (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j))))) /\
  (* the frame's flag address at its last word, and the frame and its shadow present *)
  rdword rd (F + AR_FLAGPTR) = Some (ar_FL cx fpos) /\
  (forall a, F <= a < F + AR_FB -> apresent (w_H W3) m3 a) /\
  (forall a, SH <= a < SH + AR_SHN -> apresent (w_H W3) m3 a) /\
  (* what the body has written so far: the contract's write set together with the side frame it took
     (the Eacc recipe; apost_side drops aside_rng again with akept_drop_side) *)
  akept SEGS B (ar_lyc cx) (ar_Sc cx) (ar_W cx) (ar_memc cx) W3 m3
    (ar_sp cx - REAC_LINK_ALIAS_READ_AK) (ar_sp cx)
    (fun a => ar_E cx a \/ aside_rng (ar_lyc cx) AR_CID fpos a) /\
  (* the descriptors, the file system and the read-only image *)
  m_fds md3 = m_fds (ar_mdc cx) /\ m_fs md3 = m_fs (ar_mdc cx) /\
  arodata_okP SEGS PCAP_RLO PCAP_RHI B rd.

(* the bytes of the fake kernel, which only nl_talk's callees write, are still the caller's *)
Definition ar_gnl_kept (cx : arcx) (W3 : world SEGS) (m3 : word -> option byte) : Prop :=
  forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE ->
    aview SEGS (w_H W3) m3 a = aview SEGS (w_H (ar_W cx)) (ar_memc cx) a.

(* the two buffers' bytes, which the head does not write: the arms store into them at +0x130 and +0x14c, and
   need their other bytes to re-state `abuf` (akept's exception set holds the buffers, so it says nothing of them) *)
Definition ar_bufs_kept (cx : arcx) (W3 : world SEGS) (m3 : word -> option byte) : Prop :=
  (ar_kind cx <> 0 -> forall a, ar_kind cx <= a < ar_kind cx + ar_kn cx ->
     aview SEGS (w_H W3) m3 a = aview SEGS (w_H (ar_W cx)) (ar_memc cx) a) /\
  (ar_alias cx <> 0 -> forall a, ar_alias cx <= a < ar_alias cx + ar_an cx ->
     aview SEGS (w_H W3) m3 a = aview SEGS (w_H (ar_W cx)) (ar_memc cx) a).

(* THE STRCMP TAIL (fuzz_if_nametoindex_c.v:122-123, astrcmp_arg_ni): the wrapper reads the
   whole last granule of a string, so every byte past the NUL up to the end of that granule must be visible.
   lib/A/Prog/reac_link_alias_read_c.v's apre gives exactly that at the call's memory, for the name and for
   every interface-table string; `ar_tail_str` names those strings and `ar_tails` is the fact the walk carries
   from the entry to the fuzz_if_nametoindex call. The head moves it across frame_alloc_1 with
   LinkWalkMkVis.v tail_vis_transport (by the class of the string's NUL, which is in the read set); the arms move
   it across their own runs, which only grow the memory (`ar_vis_grows` / `ar_vis_pres`). *)
Definition ar_tail_rng (p : Z) (s : list byte) (a : Z) : Prop :=
  p + Z.of_nat (length s) < a < p + Z.of_nat (length s) - (p + Z.of_nat (length s)) mod 8 + 8.

Definition ar_tail_str (cx : arcx) (p : Z) (s : list byte) : Prop :=
  (p = ar_name cx /\ astr_arg SEGS (ar_m0 cx) (ar_name cx) (Some s))
  \/ (exists bs tab i ix,
        anlk_at SEGS (ar_m0 cx) LA_G_NL bs /\ aiftab_at SEGS (ar_m0 cx) LA_G_NL bs tab /\
        nth_error tab i = Some (s, ix) /\
        au64_at SEGS (ar_m0 cx) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p /\ 0 <= p < 2 ^ 64 /\
        acstr_at SEGS (ar_m0 cx) p s).

Definition ar_tails (cx : arcx) (W3 : world SEGS) (m3 : word -> option byte) : Prop :=
  forall p s, ar_tail_str cx p s -> forall a, ar_tail_rng p s a -> ard SEGS (rdW W3 m3) a <> None.

(* Visibility is monotone: a byte a memory shows is either one the memory holds, which a later memory still
   holds, or an image ROM byte, which no memory changes. This is how the tail clause moves across a step of
   the walk; the values of those bytes are NOT kept (a guarded NUL store may land in a tail granule). *)
Lemma ar_vis_grows : forall (W : world SEGS) (m m' : word -> option byte) a,
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  ard SEGS (rdW W m) a <> None -> ard SEGS (rdW W m') a <> None.
Proof.
  intros W m m' a HG Hv. unfold ard, YP09.mbyte in *.
  destruct (mrestrict (w_H W) m (Z_to_bv 64 a)) as [b|] eqn:E.
  - assert (Hn : mrestrict (w_H W) m' (Z_to_bv 64 a) <> None)
      by (apply HG; rewrite E; discriminate).
    destruct (mrestrict (w_H W) m' (Z_to_bv 64 a)); [cbn; discriminate | exfalso; exact (Hn eq_refl)].
  - destruct (mrestrict (w_H W) m' (Z_to_bv 64 a)) as [b'|] eqn:E'; [cbn; discriminate | exact Hv].
Qed.

(* the same from the presence form the arms carry across a stretch *)
Lemma ar_vis_pres : forall (W : world SEGS) (m m' : word -> option byte) a,
  (forall x, apresent (w_H W) m x -> apresent (w_H W) m' x) ->
  ard SEGS (rdW W m) a <> None -> ard SEGS (rdW W m') a <> None.
Proof.
  intros W m m' a HP Hv. unfold ard, YP09.mbyte, mrestrict in *.
  destruct (w_H W (Z_to_bv 64 a)) eqn:EH; [exact Hv|].
  destruct (m (Z_to_bv 64 a)) as [b|] eqn:E.
  - destruct (HP a (conj EH (ex_intro _ b E))) as (_ & bb & Hbb). rewrite Hbb. cbn. discriminate.
  - destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:E'; [cbn; discriminate | exact Hv].
Qed.

(* the two guarded NUL stores of +0x130 and +0x14c, as the rest of the walk reads them back *)
Definition ar_bufs_nul (cx : arcx) (W3 : world SEGS) (m3 : word -> option byte) : Prop :=
  (ar_kind cx <> 0 -> 1 <= ar_kn cx ->
     acstr_at SEGS (rdW W3 m3) (ar_kind cx) [] /\ abuf SEGS (rdW W3 m3) (ar_kind cx) (ar_kn cx)) /\
  (ar_alias cx <> 0 -> 1 <= ar_an cx ->
     acstr_at SEGS (rdW W3 m3) (ar_alias cx) [] /\ abuf SEGS (rdW W3 m3) (ar_alias cx) (ar_an cx)).

(* ---- the post's result, as a cut states it: the return code and the kernel's bytes at the cut ---- *)
Definition ar_pf (cx : arcx) (rcv : Z) (W' : world SEGS) (m : word -> option byte) : Prop :=
  forall kbs tab nm,
    anlk_at SEGS (ar_m0 cx) LA_G_NL kbs -> aiftab_at SEGS (ar_m0 cx) LA_G_NL kbs tab ->
    astr_arg SEGS (ar_m0 cx) (ar_name cx) nm ->
    let R := read_lib tab nm (ar_kn cx) (ar_an cx) (nk_sent kbs) (nk_kstate kbs) in
    rcv = r_rc R
    /\ (exists kbs', anlk_at SEGS (rdW W' m) LA_G_NL kbs' /\ nlk_wf kbs'
          /\ nk_chunks kbs' = nk_chunks kbs /\ nk_end_errno kbs' = nk_end_errno kbs
          /\ nk_n_if kbs' = nk_n_if kbs /\ aiftab_at SEGS (rdW W' m) LA_G_NL kbs' tab
          /\ nk_next kbs' = Z.of_nat (k_next (r_state R))
          /\ nk_socket_errno kbs' = k_sock (r_state R)
          /\ nk_send_errno kbs' = k_send (r_state R)
          /\ nk_sent kbs' = r_reqs R /\ nk_n_sent kbs' = Z.of_nat (length (r_reqs R))
          /\ nk_open kbs' = 0 /\ nk_misuse kbs' = nk_misuse kbs
          /\ nk_opened kbs' - nk_closed kbs' = nk_opened kbs - nk_closed kbs
          /\ nk_opened kbs <= nk_opened kbs' <= nk_opened kbs + 1
          /\ ((nm = None \/ nm = Some [] \/ (forall s, nm = Some s -> index_of tab s = 0)) ->
                nk_opened kbs' = nk_opened kbs))
    /\ (ar_kind cx <> 0 -> 1 <= ar_kn cx -> acstr_at SEGS (rdW W' m) (ar_kind cx) (r_kind R))
    /\ (ar_alias cx <> 0 -> 1 <= ar_an cx -> acstr_at SEGS (rdW W' m) (ar_alias cx) (r_alias R))
    /\ (ar_kind cx <> 0 -> 1 <= ar_kn cx -> abuf SEGS (rdW W' m) (ar_kind cx) (ar_kn cx))
    /\ (ar_alias cx <> 0 -> 1 <= ar_an cx -> abuf SEGS (rdW W' m) (ar_alias cx) (ar_an cx)).

(* ---- the three cuts ---- *)
(* +0x118 `beqz s5`: the frame is taken and poisoned; s3 = alias, s4 = alias_n, s5 = kind, s6 = kind_n,
   s7 = name, s8 = the shadow base. Nothing of the caller's memory has moved yet. *)
Definition ar_gi_mid (cx : arcx) (fpos : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
    (ms3 : machine_state) (md3 : Model) : Prop :=
  ms_pc_val ms3 = w64 (BASE + AR_CUT_MID) /\
  getr (ms_regs ms3) 19 = w64 (ar_alias cx) /\
  getr (ms_regs ms3) 20 = w64 (ar_an cx) /\
  getr (ms_regs ms3) 21 = w64 (ar_kind cx) /\
  getr (ms_regs ms3) 22 = w64 (ar_kn cx) /\
  getr (ms_regs ms3) 23 = w64 (ar_name cx) /\
  getr (ms_regs ms3) 24 = w64 SHADOW_OFF /\
  ar_gnl_kept cx W3 (ms_mem ms3) /\
  (forall a, reac_link_alias_read_ard SEGS (ar_regs cx) (ar_m0 cx) a ->
     aview SEGS (w_H W3) (ms_mem ms3) a = aview SEGS (w_H (ar_W cx)) (ar_memc cx) a) /\
  ar_tails cx W3 (ms_mem ms3) /\
  ar_bufs_kept cx W3 (ms_mem ms3) /\
  ar_base cx fpos ly3 S3 W3 ms3 md3.

(* +0x180 `addi s8,s10,0x20`: the name is a C string that the table knows; s7 holds its index. The two NUL
   stores are done, so `ar_bufs_nul` holds. *)
Definition ar_gi_send (cx : arcx) (fpos : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
    (ms3 : machine_state) (md3 : Model) : Prop :=
  exists sn tab kbs,
  ms_pc_val ms3 = w64 (BASE + AR_CUT_SEND) /\
  anlk_at SEGS (ar_m0 cx) LA_G_NL kbs /\ aiftab_at SEGS (ar_m0 cx) LA_G_NL kbs tab /\
  acstr_at SEGS (ar_m0 cx) (ar_name cx) sn /\ ar_name cx <> 0 /\ sn <> [] /\
  index_of tab sn <> 0 /\
  getr (ms_regs ms3) 23 = w64 (index_of tab sn) /\
  getr (ms_regs ms3) 19 = w64 (ar_alias cx) /\
  getr (ms_regs ms3) 20 = w64 (ar_an cx) /\
  getr (ms_regs ms3) 21 = w64 (ar_kind cx) /\
  getr (ms_regs ms3) 22 = w64 (ar_kn cx) /\
  getr (ms_regs ms3) 24 = w64 SHADOW_OFF /\
  ar_gnl_kept cx W3 (ms_mem ms3) /\
  ar_bufs_nul cx W3 (ms_mem ms3) /\
  ar_base cx fpos ly3 S3 W3 ms3 md3.

(* +0x1fc `lui a1,0x45e03`: the body is done, a0 is the return code, the kernel's bytes are as the post says. *)
Definition ar_gi_exit (cx : arcx) (fpos : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
    (ms3 : machine_state) (md3 : Model) : Prop :=
  exists rcv,
  ms_pc_val ms3 = w64 (BASE + AR_CUT_EXIT) /\
  getr (ms_regs ms3) 10 = w64 rcv /\
  ar_base cx fpos ly3 S3 W3 ms3 md3 /\
  ar_pf cx rcv W3 (ms_mem ms3).

(* `ar_from GI`: from every state GI describes, the run reaches the post. *)
Definition ar_from (GI : arcx -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop) : Prop :=
  forall (cx : arcx) (fpos : Z) ly3 S3 W3 (ms3 : machine_state) md3,
  ar_pre cx -> GI cx fpos ly3 S3 W3 ms3 md3 -> SRr SEGS W3 (mkCfg ms3 md3) (ar_post cx).

Definition ar_exit_obl : Prop := ar_from ar_gi_exit.
Definition ar_send_obl : Prop := ar_from ar_gi_send.
Definition ar_mid_obl : Prop := ar_from ar_gi_mid.

End zb.
End z.

(* ==========================================================================
   The entry
   ========================================================================== *)

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis HV : LinkVals.
Hypothesis TL : PALib B.

Let HBgot := pal_got_shadow B TL.
Let HBcell := pal_cell B TL.
Let HBguar := pal_got_uar B TL.
Let HBuar := pal_uar_cell B TL.

Lemma ar_obj_val : forall i, (i < link_nobj)%nat -> pa_val (A_OBJ i) = link_obj i.
Proof. intros i Hi. exact (lv_obj HV i Hi). Qed.

Lemma ar_entry : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word),
  ajournal_gx pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REAC_LINK_ALIAS_READ_AK -> spZ regs <= sp0 ->
  st_ok_pi pa_segs pa_val (Eimg (Ereg regs AR_extra)) ar_ss
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (pa_val A_TEXT + AF_reac_link_alias_read)) memc (seg_rom pa_segs))).
Proof.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJX Hal16 Hwlo Hwhi.
destruct HJX as (HSTK & HXO & (memS & HJ & Hag) & Hout).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (HK : REAC_LINK_ALIAS_READ_AK = 8592) by reflexivity.
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell. rewrite HBguar, HBuar in Kguar. rewrite HBuar in Kuar.
pose proof (ar_obj_val 0%nat ltac:(unfold link_nobj; lia)) as V0.
pose proof (ar_obj_val 1%nat ltac:(unfold link_nobj; lia)) as V1.
pose proof (ar_obj_val 64%nat ltac:(unfold link_nobj; lia)) as V64.
pose proof (ar_obj_val 65%nat ltac:(unfold link_nobj; lia)) as V65.
cbv [link_obj] in V0, V1, V64, V65.
set (E := Eimg (Ereg regs AR_extra)).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs AR_extra) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 AR_SB)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs AR_extra 0)).
assert (EIMG : forall i, (i < 66)%nat -> ew E (A_OBJ i) = Z_to_bv 64 (pa_val (A_OBJ i)))
  by (intros i Hi; subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VBI : forall i, (i < 66)%nat -> base_val E (Some (A_OBJ i)) = pa_val (A_OBJ i)).
{ intros i Hi. cbn [base_val]. rewrite (EIMG i Hi). apply unsigned_lit_small.
  pose proof (pa_val_range (A_OBJ i)). lia. }
rewrite restrict_mkst_fx. unfold ar_ss. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold ar_regions, ar_stack, ar_got, ar_cell, ar_ugot, ar_ucell.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. fold E. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable pa_segs). cbn [ms_mem restrict mkst]. apply Hpres. lia.
  + fold E. rewrite (VBI 1%nat ltac:(lia)).
    split; [rewrite V1; lia|]. split; [rewrite V1; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val pa_segs E _ (pa_val (A_OBJ 1)) 0 8 (SOff (A_OBJ 64) 0) (pa_val (A_OBJ 64)));
      [ cbn [sv_denot]; rewrite (EIMG 64%nat ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (pa_val_range (A_OBJ 64)); zside | zside |].
    rewrite Z.add_0_r. cbn [ms_mem restrict mkst].
    exact (val_mem_of_rdword pa_segs (w_H W) memc _ _ Kgot).
  + fold E. rewrite (VBI 64%nat ltac:(lia)).
    split; [rewrite V64; lia|]. split; [rewrite V64; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val pa_segs E _ (pa_val (A_OBJ 64)) 0 8 (SOff 32 0) AR_SB);
      [ cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold AR_SB; zside | zside |].
    rewrite Z.add_0_r. cbn [ms_mem restrict mkst].
    exact (val_mem_of_rdword pa_segs (w_H W) memc _ _ Kcell).
  + fold E. rewrite (VBI 0%nat ltac:(lia)).
    split; [rewrite V0; lia|]. split; [rewrite V0; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val pa_segs E _ (pa_val (A_OBJ 0)) 0 8 (SOff (A_OBJ 65) 0) (pa_val (A_OBJ 65)));
      [ cbn [sv_denot]; rewrite (EIMG 65%nat ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (pa_val_range (A_OBJ 65)); zside | zside |].
    rewrite Z.add_0_r. cbn [ms_mem restrict mkst].
    exact (val_mem_of_rdword pa_segs (w_H W) memc _ _ Kguar).
  + fold E. rewrite (VBI 65%nat ltac:(lia)).
    split; [rewrite V65; lia|]. split; [rewrite V65; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val pa_segs E _ (pa_val (A_OBJ 65)) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
    rewrite Z.add_0_r. cbn [ms_mem restrict mkst].
    exact (val_mem_of_rd32 pa_segs (w_H W) memc _ _ Kuar).
- apply pairwise_disjoint_of_extents.
  unfold ar_regions, ar_stack, ar_got, ar_cell, ar_ugot, ar_ucell, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  fold E. rewrite !VBI by lia. cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  rewrite V0, V1, V64, V65.
  revert Hslo Hshi H47 Hceil C1a C1b C3 HK Hstk0 Hwlo Hwhi. clear. intros. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [ar_facts f_atoms atoms_ok]. split; [|split; [|exact I]].
  + unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E. rewrite Usp. change (2 ^ 4) with 16.
    revert Hal16 Hslo Hshi H47 Hceil C1a C1b C3 HK Hstk0 Hwlo Hwhi HSTK HXO. clear. intros.
    repeat split; lia.
  + unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E.
    rewrite E32, unsigned_lit_small by (unfold AR_SB; lia).
    rewrite Z.pow_0_r, Z.mod_1_r. repeat split; lia.
Qed.

End b.
End a.
Arguments ar_entry {fx rc} SK {PI}.
About ar_entry.
Print Assumptions ar_entry.
