(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img at fuzz_command's ASan image end 0x606000; ajournal no longer keeps footprint (FP) bytes in the image or at or above alloc_ceiling (fp_spares FP a also requires ~ inFP FP a, and the clause for bytes at or above alloc_ceiling outside [sp0 - STK, sp0) requires ~ inFP FP a), awr_byte (and awr_ok) take the start state's side-stack frames as a new parameter and also admit footprint writes to the program's statics as_prog_static in the image, to the caller's stack above sp0 and to those caller frames (awr_prog_or_caller), acall_kept_of_journal, region_kept_stack_sub, awr_byte_present and aj_intrin_at take the matching premises, ajournal_sub_wide composes a callee whose footprint lies in what the caller may write, awr_byte_present_prog and aj_intrin_at_prog take prog_rw for stores to the statics, AR_errno_present gives the errno cell's value from errno_rom, and astack_rd/astack_pres (stack bytes readable/present from sp to the stack top) give a frame chain for any s0 but an aligned sp + 8 (chain_pre_any, achain_any) and carry across an ajournal (astack_rd_journal, astack_pres_journal). *)
(* Modified by Theorem Labs, 2026-10: the malloc/free journal lemmas (aj_free_at, aj_free_at_io, aj_free_null_at, aj_free_null_at_io, aj_malloc_at, aj_malloc_at_io, aj_malloc_at04, aj_malloc_at04_io, aj_malloc, aj_free) no longer take In (call_trace0 ...) (as_universe B); the model laws get the trace length (call_trace_len) and the contracts the event bound. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/Reusable/YCbq.v, with its module paths and module names changed; 1154 of its 1305 lines of code are new or changed and 3194 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LinkWalkSide.v, with its module paths and module names changed; 181 of its 214 lines of code are new or changed and 1272 lines of the source are left out. *)
(* reac_code_emit (reac_code.h:103-108) on image A (fuzz_link.asan 0x89be4, 464 bytes; listing
   (internal path) (internal record, sha256 102ac6881148)): the data the phases of its
   walk share. The contract is lib/A/Prog/reac_code_emit_c.v (`aleaf_fx`, K = 9360, EV = 0, SIDE = [(0, 1)]); the phases
   are lib/A/Prog/reac_code_emit{Entry,Head,Mid,Exit}.v and the top is lib/A/Prog/reac_code_emit.v.

   THE SHAPE OF THE CODE (offsets from 0x89be4, read from the listing).
   - +0x00..+0x2c  a 128-byte machine frame (`addi sp, sp, -0x80`; `sd zero, 0(sp)` probes its lowest word); ra at
     sp0 - 0x28, s0..s7 at sp0 - 0x30 .. sp0 - 0x68; s0 := sp0 - 0x20;
   - +0x30..+0x3c  `andi sp, sp, -0x20` (the realigned stack pointer em_sp1, in s1); s2 := a3 (the format),
     s4 := a0 (the stream);
   - +0x40..+0x54  s5 := the shadow base (.got+0x60 -> the cell), a0 := the side-stack switch (.got+0xb8 -> the cell,
     1 in every state AR allows);
   - +0x58..+0x64  the four vararg registers a4..a7 at s0 .. s0 + 0x18 (sp0 - 0x20 .. sp0 - 0x8: the va_list);
   - +0x68..+0x74  `beqz a0` (not taken), frame_alloc_0(0x40): the class-0 side frame F (64 bytes), in s3 and s6;
     with `aside_room Sc [(0, 1)]` its address is at least 4096, so `bnez s3` at +0x84 skips the real-stack arm
     +0x88..+0xa0;
   - +0xa4..+0x100 F into the realigned frame's slot s1 + 0x10; the frame's header (magic, description 0x16fc9, the
     function's address) at F, F + 8, F + 16; s5 := the frame's shadow SH; SH[4] := 0xf8, SH[5..7] := 0xf3,
     SH[0..3] := 0xf1; s7 := -8;
   - +0x104..+0x11c the three literals; wrapper_fprintf (f, "%s: %s ", "reac-pw", "E_NOT_MARKED") (F1, 0x89d00);
   - +0x120..+0x138 SH[4] := 0; ap := s0, spilled to F + 0x20 and read back; wrapper_vfprintf (f, fmt, ap)
     (V1, 0x89d1c);
   - +0x13c..+0x17c SH[4] := 0xf8; the retired magic at F; `beqz s3` (not taken); SH[0..7] := 0xf5; the inline
     release of the class-0 frame: `ld a0, 0x38(s3)` (the flag-address word frame_alloc left at F + 56),
     `sb zero, 0(a0)`;
   - +0x1a0..+0x1cc sp := s0 - 0x60, the saved registers back, `addi sp, sp, 0x80`, `ret`.

   THE PHASES. Each phase lemma has the shape `em_from fx GI_next -> em_from fx GI_self` (nl_talk_defs.v's nt_from,
   pcap's PcapSourceNextDefs.v nx_from), where `em_from fx GI` says: from any machine state at the FP state fx that GI
   describes, with the class-0 frame taken at slot fp, the run reaches the contract's post `em_post fxe cx` at the
   ENTRY FP state fxe, for every fxe with `BoxBase.fxr fxe fx`. A phase that calls a printf-family wrapper takes the
   next phase at every fx' (`forall fx', em_from fx' GI_next`), because the wrapper returns at some fx' with
   `BoxBase.fxr fx fx'` (LinkWalkMkPrintf.v aj_gx_printf_mf_at), and `fxr_trans` gives `fxr fxe fx'`.
     reac_code_emitEntry.v  em_entry : (forall fx', em_from fx' em_f1_inv) -> em_start fx  (+0x00 .. F1, +0x120)
     reac_code_emitMid.v    em_mid   : (forall fx', em_from fx' em_v1_inv) -> em_from fx em_f1_inv  (.. V1, +0x13c)
     reac_code_emitExit.v   em_exit  : em_from fx em_v1_inv                           (.. release, ret, the Post)
   The entry phase keeps one symbolic state from the entry through frame_alloc_0 (a runtime call at the same FP
   state) to the call of wrapper_fprintf; each printf-family call ends a phase, because the run after it is at
   another FP state.

   Proves no function (kind: segment lemma). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require printf_facts_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFileSink AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit LinkWalk LinkWalkSide.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import model_decide_c reac_code_emit_c LinkWalkMkFmt.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require BoxBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ==========================================================================
   1. The cuts of the walk, as listing offsets
   ========================================================================== *)

Definition EM_entry : Z := AF_reac_code_emit.          (* 0x89be4 the first slot                          *)
Definition EM_fa : Z := AF_reac_code_emit + 0x70.      (* 0x89c54 jal frame_alloc_0                       *)
Definition EM_fa_ra : Z := AF_reac_code_emit + 0x74.   (* 0x89c58 frame_alloc_0 returned                  *)
Definition EM_f1 : Z := AF_reac_code_emit + 0x11c.     (* 0x89d00 jal wrapper_fprintf (F1)                *)
Definition EM_f1_ra : Z := AF_reac_code_emit + 0x120.  (* 0x89d04 wrapper_fprintf returned                *)
Definition EM_v1 : Z := AF_reac_code_emit + 0x138.     (* 0x89d1c jal wrapper_vfprintf (V1)               *)
Definition EM_v1_ra : Z := AF_reac_code_emit + 0x13c.  (* 0x89d20 wrapper_vfprintf returned               *)
Definition EM_ret : Z := AF_reac_code_emit + 0x1cc.    (* 0x89db0 the `ret`                               *)

Lemma EM_addrs :
  map (fun o => link_text + o) [EM_entry; EM_fa; EM_fa_ra; EM_f1; EM_f1_ra; EM_v1; EM_v1_ra; EM_ret] =
    [0x89be4; 0x89c54; 0x89c58; 0x89d00; 0x89d04; 0x89d1c; 0x89d20; 0x89db0].
Proof. reflexivity. Qed.

(* The three calls, each at the slot before its return cut. *)
Lemma EM_calls_listed :
  map (fun o => nth_error link_listing (Z.to_nat (o / 4))) [EM_fa; EM_f1; EM_v1] =
  [Some (PCall LS___asan_stack_malloc_0 (1%bv : bv 5));
   Some (PCall LS___interceptor_trampoline_fprintf (1%bv : bv 5));
   Some (PCall LS___interceptor_trampoline_vfprintf (1%bv : bv 5))].
Proof. vm_compute. reflexivity. Qed.

(* ==========================================================================
   2. The geometry of the frame
   ========================================================================== *)

(* The realigned stack pointer the body runs on (`andi sp, sp, -0x20` at +0x30 after the 128-byte push). *)
Definition em_sp1 (sp0 : Z) : Z := 32 * ((sp0 - REAC_CODE_EMIT_AFRAME) / 32).

Lemma em_sp1_range : forall sp0, 0 <= sp0 - REAC_CODE_EMIT_AFRAME -> sp0 mod 16 = 0 ->
  sp0 - REAC_CODE_EMIT_AFRAME - 16 <= em_sp1 sp0 <= sp0 - REAC_CODE_EMIT_AFRAME /\
  em_sp1 sp0 mod 32 = 0 /\ em_sp1 sp0 mod 16 = 0.
Proof.
  intros sp0 H0 H16. unfold em_sp1, REAC_CODE_EMIT_AFRAME in *.
  pose proof (Z.div_mod (sp0 - 128) 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (sp0 - 128) 32 ltac:(lia)) as M.
  assert (Hm : (sp0 - 128) mod 32 = 0 \/ (sp0 - 128) mod 32 = 16) by lia.
  split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|].
  replace (32 * ((sp0 - 128) / 32)) with ((2 * ((sp0 - 128) / 32)) * 16) by lia. apply Z_mod_mult.
Qed.

(* The machine frame's slots, as offsets from the entry stack pointer sp0. *)
Definition EM_RA : Z := -0x28.         (* sd ra, 0x58(sp)   +0x08; ld ra, 0x58(sp)   +0x1a4 *)
Definition EM_S0 : Z := -0x30.         (* sd s0 .. s7 at 0x50(sp) .. 0x18(sp), +0x0c .. +0x28 *)
Definition EM_VA : Z := -0x20.         (* s0 = sp0 - 0x20: sd a4 .. a7, 0(s0) .. 0x18(s0) +0x58 .. +0x64 *)
Definition EM_FSLOT : Z := 0x10.       (* sd s6, 0x10(s1)   +0xa4: F into the realigned frame *)

(* The side frame's own numbers (class 0: a 64-byte slot, 8 shadow bytes). *)
Definition EM_CID : Z := 0.
Definition EM_FSZ : Z := 64.           (* addi a0, zero, 0x40  +0x6c *)
Definition EM_AP : Z := 0x20.          (* sd a0, 0x20(s6); ld a2, 0x20(s6)  +0x128, +0x12c *)
Definition EM_MAGIC : Z := 0x41b58ab3.     (* lui a0, 0x41b59; addiw a0, a0, -0x54d  +0xa8, +0xc0 *)
Definition EM_RETIRED : Z := 0x45e0360e.   (* lui a0, 0x45e03; addiw a0, a0, 0x60e   +0x140, +0x144 *)

Lemma EM_sizes : fs_frame_bytes EM_CID = EM_FSZ /\ REAC_CODE_EMIT_AK = 9360 /\
  REAC_CODE_EMIT_AK = REAC_CODE_EMIT_AFRAME + REAC_CODE_EMIT_ASLACK + AEMIT_RT_STK.
Proof. repeat split; reflexivity. Qed.

(* ==========================================================================
   3. The call's context and its premises
   ========================================================================== *)

Section a. Context {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.

Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Variable B : asyms.

(* Everything the contract's premises fix, in one record (nl_talk_defs.v ntcx, pcap's ncx): the journal at the
   call, the registers, and the witnesses of reac_code_emit_apre (the format, its pieces, the arguments, the text,
   the FILE's pending count). *)
Record emcx := mkEMCX {
  e_G : list (Z * Z); e_XO : Z; e_OUT : list (Z * Z);
  e_STK : Z; e_sp0 : Z; e_FP : list (Z * Z);
  e_ly : alayout; e_S : astate; e_W0 : world SEGS; e_mem0 : word -> option byte; e_md0 : Model;
  e_own : list (Z * Z);
  e_lyc : alayout; e_Sc : astate; e_W : world SEGS; e_memc : word -> option byte; e_mdc : Model;
  e_k : Z;
  e_regs : bvmap 5 word;
  e_fmt : list Z;                          (* the caller's format, without its NUL               *)
  e_ps : list printf_facts_c.pf_piece;     (* its pieces                                        *)
  e_args : list printf_facts_c.pf_arg;     (* the vararg registers a4.. as the format reads them  *)
  e_T : list Z;                            (* the text                                          *)
  e_kf : Z                                 (* the FILE's pending bytes at the call              *)
}.

(* the arguments, by name *)
Definition e_f (cx : emcx) : Z := aarg (e_regs cx) 0.
Definition e_fp (cx : emcx) : Z := aarg (e_regs cx) 3.
Definition e_vregs (cx : emcx) : list word :=
  [getr (e_regs cx) 14; getr (e_regs cx) 15; getr (e_regs cx) 16; getr (e_regs cx) 17].
(* the memory the walk sees at the call, the entry and the realigned stack pointer, the frame's addresses *)
Definition e_m (cx : emcx) : word -> option byte := rdW (e_W cx) (e_memc cx).
Definition e_spe (cx : emcx) : Z := spZ (e_regs cx).
Definition e_sp1 (cx : emcx) : Z := em_sp1 (e_spe cx).
Definition eF (cx : emcx) (fp : Z) : Z := frame_addr (e_lyc cx) EM_CID fp.
Definition eSH (cx : emcx) (fp : Z) : Z := shadow_of_addr SHADOW_OFF (eF cx fp).
Definition eFL (cx : emcx) (fp : Z) : Z := flag_addr (e_lyc cx) EM_CID fp.

(* The write set and the read set of the contract, at this call. *)
Definition e_Wr (cx : emcx) : list (Z * Z) := reac_code_emit_awr (e_regs cx) (e_m cx).
Definition e_E (cx : emcx) : Z -> Prop := fun a => inFP (e_Wr cx) a.
Definition e_Rd (cx : emcx) : Z -> Prop := reac_code_emit_ard SEGS (e_regs cx) (e_m cx).

(* What every phase may assume of the call: the premises of reac_code_emit_acontract at segs := SEGS,
   rlo := PCAP_RLO, rhi := PCAP_RHI, with reac_code_emit_apre's witnesses fixed by the context. *)
Definition em_base (cx : emcx) : Prop :=
  apre SK SEGS PCAP_RLO PCAP_RHI B REAC_CODE_EMIT_AK 0 [(EM_CID, 1)] (e_Wr cx)
    (e_G cx) (e_XO cx) (e_OUT cx) (e_STK cx) (e_sp0 cx) (e_FP cx) (e_ly cx) (e_S cx) (e_W0 cx) (e_mem0 cx)
    (e_md0 cx) (e_own cx) (e_lyc cx) (e_Sc cx) (e_W cx) (e_memc cx) (e_mdc cx) (e_k cx) (e_regs cx) /\
  (forall a, e_Rd cx a -> akb SEGS B (e_lyc cx) (e_Sc cx) (e_spe cx - REAC_CODE_EMIT_AK) (e_spe cx) a) /\
  e_f cx <> 0 /\ e_fp cx <> 0 /\
  In (e_f cx, AMF_BLOCK) (ablocks B (e_lyc cx) (e_Sc cx)) /\
  amemfile_k SEGS (e_m cx) (e_f cx) (e_kf cx) /\
  amf_blk_ok SEGS (e_regs cx) REAC_CODE_EMIT_AK (e_m cx) (e_f cx) /\
  e_kf cx + EMIT_HEAD + Z.of_nat (length (e_T cx)) <= AMF_BUFSIZ /\
  aemit_fmt SEGS (e_regs cx) REAC_CODE_EMIT_AK (e_m cx) (e_f cx) (e_fp cx) (e_fmt cx) (e_ps cx) (e_args cx) (e_T cx) /\
  acstr_at SEGS (e_m cx) LA_FMT_SS S_FMT_SS /\
  astr_rt_ok SEGS (e_regs cx) REAC_CODE_EMIT_AK (e_m cx) LA_FMT_SS S_FMT_SS /\
  acstr_at SEGS (e_m cx) LA_S_REACPW S_REACPW /\
  astr_rt_ok SEGS (e_regs cx) REAC_CODE_EMIT_AK (e_m cx) LA_S_REACPW S_REACPW /\
  acstr_at SEGS (e_m cx) LA_S_E_NOT_MARKED S_E_NOT_MARKED /\
  astr_rt_ok SEGS (e_regs cx) REAC_CODE_EMIT_AK (e_m cx) LA_S_E_NOT_MARKED S_E_NOT_MARKED.

(* The post of the whole call at the entry's FP state fxe, in the shape reac_code_emit_acontract asks. *)
Definition em_post (fxe : YK11.FPState) (cx : emcx) : world SEGS -> config -> Prop :=
  apostF (fx := fxe) SK SEGS B REAC_CODE_EMIT_AK 0 (e_E cx)
    (e_G cx) (e_XO cx) (e_OUT cx) (e_STK cx) (e_sp0 cx) (e_FP cx) (e_ly cx) (e_S cx) (e_W0 cx) (e_mem0 cx)
    (e_md0 cx) (e_own cx) (e_lyc cx) (e_Sc cx) (e_W cx) (e_memc cx) (e_mdc cx) (e_k cx) (e_regs cx)
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       S2 = set_fs (st_fs S2) (e_Sc cx) /\ Permutation (ablocks B ly2 S2) (ablocks B (e_lyc cx) (e_Sc cx)) /\
       reac_code_emit_apost SEGS (e_regs cx) (e_m cx) regs2 (rdW W2 mem2)).

(* ==========================================================================
   4. A phase
   ========================================================================== *)

(* An invariant at a cut: the FP state the machine runs at, the context, the frame's slot fp, the journal's index,
   and the state. *)
Definition em_inv : Type :=
  YK11.FPState -> emcx -> Z -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop.

(* `em_from fx GI`: from any machine state at fx that GI describes, with the class-0 frame taken at slot fp and the
   caller's journal extended by it, the run reaches the post at every entry FP state fxe with fxr fxe fx. *)
Definition em_from (fx : YK11.FPState) (GI : em_inv) : Prop :=
  forall (fxe : YK11.FPState) (cx : emcx) (fp k2 : Z) ly3 S3 W3 (ms3 : machine_state) md3,
  @BoxBase.fxr fxe fx -> YK0o.frm_zero (@YK11.fp_csr fxe) ->
  em_base cx ->
  ajournal_gx SEGS B (e_G cx) (e_XO cx) (e_OUT cx) (e_STK cx) (e_sp0 cx) (e_FP cx) (e_ly cx) (e_S cx)
    (e_W0 cx) (e_mem0 cx) (e_md0 cx) ((EM_CID, fp) :: e_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  GI fx cx fp k2 ly3 S3 W3 ms3 md3 ->
  SRr SEGS W3 (mkCfg ms3 md3) (em_post fxe cx).

(* The whole call at the entry's FP state fx: from the function's first slot under em_base to the post. *)
Definition em_start (fx : YK11.FPState) : Prop :=
  forall cx : emcx, YK0o.frm_zero (@YK11.fp_csr fx) -> em_base cx ->
  SRr SEGS (e_W cx) (@cfg_at fx SEGS (BASE + EM_entry) (e_regs cx) (e_memc cx) (e_mdc cx)) (em_post fx cx).

(* ==========================================================================
   5. The state at a cut
   ========================================================================== *)

(* The fixed fields of a machine state at a cut, at the FP state fx. *)
Definition em_shape (fx : YK11.FPState) (pc : Z) (ms3 : machine_state) : Prop :=
  ms_pc_val ms3 = w64 (BASE + pc) /\ ms_resv ms3 = None /\ ms_svc_pending ms3 = None /\
  ms_rom ms3 = seg_rom SEGS /\ ms_fregs ms3 = @YK11.fp_regs fx /\ ms_fcsr ms3 = @YK11.fp_csr fx.

(* The journal's bookkeeping at every cut while the class-0 frame at slot fp is live (nl_talk_defs.v nt_jbk): no
   allocator event, the caller's blocks up to a permutation, the side stack as the only part of the allocator state
   that moved, the layout's frame addresses unchanged, a witness state at the CALL's layout for apost_side, and no
   descriptor or file-system change. *)
Definition em_jbk (cx : emcx) (fp k2 : Z) (ly3 : alayout) (S3 : astate) (md3 : Model) : Prop :=
  k2 = e_k cx /\
  Permutation (ablocks B ly3 S3) (ablocks B (e_lyc cx) (e_Sc cx)) /\
  S3 = set_fs (st_fs S3) (e_Sc cx) /\
  frames S3 = (EM_CID, fp) :: frames (e_Sc cx) /\
  ~ In (EM_CID, fp) (frames (e_Sc cx)) /\
  (forall c p, frame_addr ly3 c p = frame_addr (e_lyc cx) c p) /\
  (forall c p, flag_addr ly3 c p = flag_addr (e_lyc cx) c p) /\
  (exists S1 W1 mem1 md1, AR SEGS B (e_lyc cx) S1 W1 mem1 md1 /\
     frames S1 = (EM_CID, fp) :: frames (e_Sc cx) /\
     ablocks B (e_lyc cx) S1 = ablocks B (e_lyc cx) (e_Sc cx)) /\
  m_fds md3 = m_fds (e_mdc cx) /\ m_fs md3 = m_fs (e_mdc cx).

(* What the call keeps of the caller's memory at a cut: ONE akept clause whose exception set is the bytes E (inside
   the contract's write set, the FILE block) and the class-0 frame's range, its shadow and its flag byte
   (LinkWalkSide.v aside_rng; the side-frame recipe, consumed by apost_side), and the read-only view. *)
Definition em_kept (cx : emcx) (E : Z -> Prop) (fp : Z) (W3 : world SEGS) (mem3 : word -> option byte) : Prop :=
  akept SEGS B (e_lyc cx) (e_Sc cx) (e_W cx) (e_memc cx) W3 mem3
    (e_spe cx - REAC_CODE_EMIT_AK) (e_spe cx)
    (fun a => E a \/ aside_rng (e_lyc cx) EM_CID fp a) /\
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W3) mem3) /\
  (forall a, E a -> e_E cx a).

(* A machine word at an address, as the walk reads a slot back. *)
Definition em_at (W3 : world SEGS) (ms3 : machine_state) (a v : Z) : Prop :=
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) a = Some v.

(* The saved registers of the machine frame, which the epilogue reads back (+0x08..+0x28, +0x1a4..+0x1c4): ra at
   sp0 - 0x28, then s0, s1, s2, ..., s7 at sp0 - 0x30, sp0 - 0x38, ..., sp0 - 0x68. *)
Definition em_saved (cx : emcx) (W3 : world SEGS) (ms3 : machine_state) : Prop :=
  em_at W3 ms3 (e_spe cx + EM_RA) (raZ (e_regs cx)) /\
  forall j, 0 <= j < 8 ->
    em_at W3 ms3 (e_spe cx + EM_S0 - 8 * j)
      (bv_unsigned (getr (e_regs cx) (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j)))).

(* The va_list's four slots (+0x58..+0x64): a4..a7 at sp0 - 0x20 .. sp0 - 0x8. *)
Definition em_va (cx : emcx) (W3 : world SEGS) (ms3 : machine_state) : Prop :=
  forall j, 0 <= j < 4 ->
    em_at W3 ms3 (e_spe cx + EM_VA + 8 * j) (bv_unsigned (getr (e_regs cx) (Z_to_bv 5 (14 + j)))).

(* The flag-address word frame_alloc_0 left at F + 56, which the inline release reads (+0x174). *)
Definition em_flagw (cx : emcx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) : Prop :=
  em_at W3 ms3 (eF cx fp + fs_frame_bytes EM_CID - 8) (eFL cx fp).

(* The registers every cut after the prologue keeps: s0 = sp0 - 0x20, s1 = sp = the realigned stack pointer,
   s2 = the format, s4 = the stream, gp, tp, and s8..s11 as at the entry (no instruction writes them). *)
Definition em_regs (cx : emcx) (ms3 : machine_state) : Prop :=
  getr (ms_regs ms3) 2 = w64 (e_sp1 cx) /\
  getr (ms_regs ms3) 8 = w64 (e_spe cx + EM_VA) /\
  getr (ms_regs ms3) 9 = w64 (e_sp1 cx) /\
  getr (ms_regs ms3) 18 = getr (e_regs cx) 13 /\
  getr (ms_regs ms3) 20 = getr (e_regs cx) 10 /\
  getr (ms_regs ms3) 3 = getr (e_regs cx) 3 /\
  getr (ms_regs ms3) 4 = getr (e_regs cx) 4 /\
  getr (ms_regs ms3) 24 = getr (e_regs cx) 24 /\ getr (ms_regs ms3) 25 = getr (e_regs cx) 25 /\
  getr (ms_regs ms3) 26 = getr (e_regs cx) 26 /\ getr (ms_regs ms3) 27 = getr (e_regs cx) 27.

(* ... and from +0xb8 on, with the frame taken: s3 = s6 = F, s5 = the frame's shadow SH, s7 = -8. *)
Definition em_fregs (cx : emcx) (fp : Z) (ms3 : machine_state) : Prop :=
  getr (ms_regs ms3) 19 = w64 (eF cx fp) /\
  getr (ms_regs ms3) 22 = w64 (eF cx fp) /\
  getr (ms_regs ms3) 21 = w64 (eSH cx fp) /\
  getr (ms_regs ms3) 23 = w64 (-8).

(* The FILE at a cut, with kk bytes pending (LinkMfDefs.v amf_k: amemfile_at and the window). *)
Definition em_file (cx : emcx) (kk : Z) (W3 : world SEGS) (ms3 : machine_state) : Prop :=
  amf_k SEGS link_amf (rdW W3 (ms_mem ms3)) (e_f cx) kk.

(* ==========================================================================
   6. The phase boundaries
   ========================================================================== *)

(* EM_f1_ra (+0x120): wrapper_fprintf returned; the FILE holds the 22 bytes of the head line more. The entry phase
   proves this; the middle phase consumes it. *)
Definition em_f1_inv : em_inv := fun fx cx fp k2 ly3 S3 W3 ms3 md3 =>
  em_shape fx EM_f1_ra ms3 /\ em_regs cx ms3 /\ em_fregs cx fp ms3 /\ em_saved cx W3 ms3 /\ em_va cx W3 ms3 /\
  em_flagw cx fp W3 ms3 /\
  4096 <= eF cx fp /\ eF cx fp + fs_frame_bytes EM_CID <= alloc_ceiling /\
  em_jbk cx fp k2 ly3 S3 md3 /\ em_kept cx (e_E cx) fp W3 (ms_mem ms3) /\
  em_file cx (e_kf cx + EMIT_HEAD) W3 ms3.

(* EM_v1_ra (+0x13c): wrapper_vfprintf returned; the FILE holds the caller's text T more. The middle phase proves
   this; the exit phase consumes it. *)
Definition em_v1_inv : em_inv := fun fx cx fp k2 ly3 S3 W3 ms3 md3 =>
  em_shape fx EM_v1_ra ms3 /\ em_regs cx ms3 /\ em_fregs cx fp ms3 /\ em_saved cx W3 ms3 /\
  em_flagw cx fp W3 ms3 /\
  4096 <= eF cx fp /\ eF cx fp + fs_frame_bytes EM_CID <= alloc_ceiling /\
  em_jbk cx fp k2 ly3 S3 md3 /\ em_kept cx (e_E cx) fp W3 (ms_mem ms3) /\
  em_file cx (e_kf cx + EMIT_HEAD + Z.of_nat (length (e_T cx))) W3 ms3.

(* The write set is the FILE block. *)
Lemma e_E_file : forall cx a, e_f cx <> 0 -> (e_E cx a <-> e_f cx <= a < e_f cx + AMF_BLOCK).
Proof.
  intros cx a Hf. unfold e_E, e_Wr, reac_code_emit_awr, aivl. fold (e_f cx).
  rewrite inFP_cons. destruct (e_f cx =? 0) eqn:E0; [apply Z.eqb_eq in E0; contradiction|].
  split; [intros [H | H]; [exact H | destruct H as (r & Hr & _); destruct Hr] | intros H; left; exact H].
Qed.

End b.
End a.

(* SK is an explicit argument of every statement above (Context (SK : YI16.sink_head), no braces): the only global
   sink_head instance of this closure is the plain build's (lib/Reusable/YI5b.v), so it must never be inferred. *)
