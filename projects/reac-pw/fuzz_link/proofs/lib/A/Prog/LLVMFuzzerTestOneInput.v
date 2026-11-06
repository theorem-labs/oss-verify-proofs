(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B's walk of pcap_source_open in the asan-ubsan instance of fuzz_pcap
   (libreac v1.9.0; pin fuzz_pcap.asan-ubsan, sha256 9e66f771f22a...; function at 0x811e0 =
   BASE + AF_pcap_source_open, AF = 0xa58), proving lib/A's image-generic contract tpcap_source_open_specX
   (lib/A/Prog/PcapSourceOpenDefs.v) at SEGS = pa_segs, rlo / rhi = pa_relro_lo / pa_relro_hi,
   apath / alen / afile = VAL (A_OBJ 3) / VAL (A_OBJ 4) / VAL (A_OBJ 2) (0x20d00 "<fuzz-input>", g_file_len
   0x5d3e40, g_file 0x5d3e60), with FM_RA and roimg as parameters. At ossv/recipes 25e3d17bdb50 (2026-10-29), there was no released proof of this function at
   this image (rule 24 lookup, a Theorem Labs lane, 22:35Z): the v1.8 ubsan proof (lib/U/Prog/pcap_source_open.v at
   origin/ossv/recipes c8557374ad2e) serves only as the template for the UBSan guards.

   The code. Up to the fopen call it is lib/A's ASan code byte for byte at
   other pcs (asan 0x8145c.. = asan-ubsan 0x811e0..): the prologue saves ra, s0 .. s9 (0x811e0..0x81210) and
   realigns s1 = sp = (sp - 96) & -32 (0x81218); the use-after-return flag is read through the GOT (0x81228
   auipc / 0x8122c ld, listing object 0 = 0x99750) from the runtime cell at 0x81234 (object 16 = 0xa17c0): the
   walk takes it as 1 (the kit's AR_const_law through al_const, with uar_cell_regionP (A_OBJ 16) holding SLit 1;
   the pin's file holds 0 and the runtime sets 1 at init), so 0x81240 `beqz a2` is not taken;
   __asan_stack_malloc_1(0x60) at 0x81248 returns the class-1 frame F (aj_stack_malloc_atS, YC85.v:292), whose
   two caller premises are discharged at op_to_call's frame request: count_cid 1 (frames Sc) < fs_frames 1 from
   op_pre's length (frames Sc) <= 7 through count_cid_le_length and 8 <= fs_frames 1, and the apath premise by
   op_SMP (stack_malloc_progressP from lib/Reusable/YG05.v:70, as cgif_file_fuzzer lib/A/ACed.v:129-130), so
   F >= 4096, 0x8125c `bnez s2` is taken and the machine-frame arm 0x81260..0x81278 is dead; then *(s1) = F
   (0x8127c), the header (0x41b58ab3, objects 10 and 11; 0x812a4..0x812ac), the twelve shadow bytes
   (0x812b8..0x812e4: 0xf1 x4, 0xf8 x3, 0xf3 x5), the mode literal "rb" (object 12, 0x812e8 / 0x812ec; HMODE)
   and the call of libreac_fuzz_fopen (0x812f4) through cl_callS (YC85.v:383) with FOPEN as the callee.

   The cut. This file walks the head: entry -> op_to_call (a Qed checkpoint at the call, op_at_call) ->
   head_to_fopen, which makes the call and establishes PcapSourceOpenPhF.v's op_fopen_ret at the return
   0x812f8. From there PcapSourceOpenPhM.v (op_from_fopen) walks to the two cuts of PcapSourceOpenPh.v and
   PcapSourceOpenB.v (op_from_null / op_from_read) to the return; pb_pcap_source_openX composes the three.
   The three UBSan guards are therefore decided outside this file, at these pcs and against these template lines:
   in PcapSourceOpenPhM.v 0x812f8 `beqz s3` (ps = 0, not taken: ps >= 4096 from op_pre's frame bounds; template
   :114 / :334, premise :93 / :290) and 0x81300 / 0x81304 `andi a0,s3,7; bnez a0` (ps mod 8 <> 0, not taken:
   op_pre's ps mod 8 = 0; template :115 / :335); in PcapSourceOpenB.v 0x81390 / 0x81394 `addi a0,zero,-3;
   bgeu s4,a0` (F + 32 >=u 2^64 - 3, not taken: F + 128 <= alloc_ceiling < 2^47; template :408-412, premise
   :291 and :295-299); all three
   go to the `unimp` at 0x8153c, and every ASan report path 0x81540..0x815b4 is dead because ps's 24 bytes are
   addressable and ps mod 8 = 0. In the head, op_at_call carries what those walks need: ps unwritten and still
   range_addressable, and op_fopen_ret's FILE-block footprint fact for the fclose of the tail.

   The callee hypotheses, used at this image as Section hypotheses: FOPEN : tlibreac_fuzz_fopen_specX
   (lib/A/Prog/PcapFuzzFopenDefs.v), AFREAD : afread_spec (lib/A/Stdio/PFreadISpec.v:138), AFCLOSE :
   afclose_source_spec (lib/A/Stdio/PFclose.v:209), ASM1 : astack_malloc_realizes (lib/Reusable/YG0d.v:285),
   ASF : astack_free_law (lib/Reusable/YG0d.v:301) and FFL : frame_flag_lawP (lib/Reusable/YCbq.v:797), the meter laws MLAW / MLAWF /
   FM, ASIL : asource_img_laws, and the kit's LAWS / TL / TLF / ML. Four instance obligations beyond the kit:
   ROK (roimg reads only image bytes outside the runtime's statics, errno and the open-file list head; applied at
   the fopen call to carry roimg from the entry memory across the prologue and the frame setup), HPATH (the path
   literal's shadow, as a law of every AR state: the frame request's kept clauses do not keep a global's shadow,
   YG0n.v:241 makes it aowned; discharged by the instance through AR_zshadow_law, YG0d.v:435-438), HGX (g_file_len
   and g_file are image bytes outside the runtime's statics and errno; the gx_ok shape of
   lib/A/Prog/PcapEntryDefs.v:366, 395, discharged by the harness), and RO : ro_below_ofl (as
   lib/A/Prog/PcapHarnessTail.v:37). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/B/Prog/PcapSourceOpen.v, with its module paths, module names and numbers changed; 501 of its 581 lines of code are new or changed and 1471 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/reac_link_alias_writeHead.v, with its module paths and module names changed; 24 of its 67 lines of code are new or changed and 538 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/reac_link_alias_read.v, with its module paths and module names changed; 257 of its 294 lines of code are new or changed and 30 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput (fuzz_link.c:764-790) on image A (fuzz_link.asan, the PUBLISHED pin, sha256 059dae63e07c...;
   listing (internal path) (internal record, sha256 e84d6f0c6974),
   0x827d4, 5468 bytes): the TOP of the walk. It assembles the phases of lib/A/Prog/LLVMFuzzerTestOneInputDefs.v
   into the image-A entry contract of lib/A/Prog/LinkEntry.v at the instance of LinkEntryA.v:

     LLVMFuzzerTestOneInput_aproof : tfib_lib_contract_xf_all_A link_asink_head B MT XM_LIB XN_LIB

   (`tfib_lib_contract_xf_all_A SK B MT XM_LIB XN_LIB` is
    `forall fx, tfib_lib_contract_xf (fx := fx) SK tfibsegs PCAP_RLO PCAP_RHI A_LLVMF RA_LLVMF A_EMPTY
     LLVMF_STK G_HARNESS B MT XM_LIB XN_LIB link_amf LA_NUL`, LinkEntryA.v:75-78.)

   THE PHASES (lib/A/Prog/LLVMFuzzerTestOneInputDefs.v fixes their cuts and their invariants; each is
   `lf_from POST GI_next -> lf_from POST GI_self`, and the entry phase proves `lf_start POST`):
     LLVMFuzzerTestOneInputEntry.v  lf_entry : lf_from POST (lf_gl_inv 0) -> lf_start POST
     LLVMFuzzerTestOneInputGl.v     lf_gl    : lf_from POST (lf_ol_inv 0) -> forall j, 0 <= j < 64 ->   (PROVED)
                                               lf_from POST (lf_gl_inv j)
     LLVMFuzzerTestOneInputOl.v     lf_ol    : lf_from POST (lf_ca_inv) -> forall j, 0 <= j < 4 ->   (PROVED)
                                               lf_from POST (lf_ol_inv j)
     LLVMFuzzerTestOneInputBlk.v    lf_blk   : lf_from POST (lf_lh_inv 0) -> lf_from POST (lf_ca_inv)
     LLVMFuzzerTestOneInputHead.v   lf_head  : forall i, 0 <= i <= 47 ->       (PROVED)
                                               (forall op, 0 <= op <= 5 -> lf_from POST (lf_arm_inv op i)) ->
                                               lf_from POST lf_exit_inv -> lf_from POST (lf_lh_inv i)
     LLVMFuzzerTestOneInputOp<k>.v  lf_op<k> : forall i, 0 <= i <= 47 ->
                                               lf_from POST (lf_tail_inv i) -> lf_from POST (lf_arm_inv k i)
     LLVMFuzzerTestOneInputTail.v   lf_tail  : forall i, 0 <= i <= 47 ->       (PROVED)
                                               (i < 47 -> lf_from POST (lf_lh_inv (i + 1))) ->
                                               lf_from POST lf_exit_inv -> lf_from POST (lf_tail_inv i)
     LLVMFuzzerTestOneInputExit.v   lf_exit  : lf_from (lf_post) lf_exit_inv
   so the only cycle is the operation loop, which `lf_loop_at` below closes by induction on the operations
   left (48 - i), as boxreg's Prog/BoxLxLoop.v does.

   The image instance is lib/A/Prog/LinkImgInst.v `PI_link`, with `pi_link_vals : LinkVals` and
   `pi_link_segs : pa_segs = tfibsegs` (the HSEGS of the walk kit).

   Released proofs (rule 24): none of LLVMFuzzerTestOneInput on image A (lookups
   lookups/slot-lookups.md (internal record, sha256 ac58b3adf586); the rule-24 slot check at 16:18Z confirmed it,
   disposition none: written new).
   Proves function LLVMFuzzerTestOneInput (image A, the asan build). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YI00 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 YO09 YGwildCount.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile AMemFileSink LinkWildRoom AF0m AB1v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide BoxBase.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs LinkImgInst.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs LinkSnpDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputTail LLVMFuzzerTestOneInputHead.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputGl LLVMFuzzerTestOneInputOl.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import text_of_c model_decide_c check_verdict_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKpre LLVMFuzzerTestOneInputFree.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputOp4.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import mark_quietly_c check_mark_c check_requests_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputMq LLVMFuzzerTestOneInputMqCall LLVMFuzzerTestOneInputOp5.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputBlk.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK1d PcapImgEnd.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AD1y.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelroA link_aro YC4b LinkWalkPi LinkWalkZsh.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputEntry.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import reac_served_unmark_all_c model_read_c model_write_c
  LinkWalkBcmp kernel_c check_socket_c check_marks_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputOp3.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require RtString.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import index_of_c reac_link_alias_write_c check_refused_c
  check_write_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputOp1.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputOp2.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import text_buf_c reac_link_alias_read_c check_bounds_c check_read_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputOp0.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import SetShadowDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputExit LLVMFuzzerTestOneInputLeave.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require ZTraceSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.

Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).

Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variable MS : amemfile_syms.
Variable la_nul : Z.
Variable LF_CTX : list (list Z).
Variables LF_MO_SET LF_MO_OP LF_MO_END : Z.
(* the calloc wrapper's own return address inside the allocator (the instance: DEC_A_calloc_ra0) *)
Variable LF_CALLOC_RA0 : Z.

#[local] Notation FROM POST GI :=
  (lf_from SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END POST GI).
#[local] Notation START POST :=
  (lf_start SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END POST).
#[local] Notation POSTL := (lf_post SK B MT XN_LIB MS la_nul).
#[local] Notation GL j := (lf_gl_inv B MT MS la_nul j).
#[local] Notation OL j := (lf_ol_inv B MT MS la_nul j).
#[local] Notation CA := (lf_ca_inv B MT MS la_nul).
#[local] Notation LH i := (lf_lh_inv B MT MS la_nul LF_MO_SET LF_MO_OP i).
#[local] Notation ARM op i := (lf_arm_inv B MT MS la_nul LF_MO_SET LF_MO_OP op i).
#[local] Notation TAIL i := (lf_tail_inv B MT MS la_nul LF_MO_SET LF_MO_OP i).
#[local] Notation EXIT := (lf_exit_inv B MT MS la_nul LF_MO_SET LF_MO_OP).

(* ==========================================================================
   The phases, as their files prove them
   ========================================================================== *)

(* The image facts the proved phases take (each discharged at link's instance: pi_link_segs, pi_link_vals,
   AD2l.PcapB_syms, AR_laws_ok). *)
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : pa_segs = tfibsegs.
Hypothesis LV : LinkVals (PI := PI).
(* The loop head is PROVED (lib/A/Prog/LLVMFuzzerTestOneInputHead.v `lf_head`). *)
(* snprintf at every FP state the g_names loop reaches; lib/A/Rt/LinkSnp.v `link_snprintf` discharges it. *)
Hypothesis SNP : forall fy : YK11.FPState,
  @asnprintf_link_realizes fy rc pa_segs B PCAP_RLO PCAP_RHI LA_W_SNPRINTF.
(* The g_names loop is PROVED (lib/A/Prog/LLVMFuzzerTestOneInputGl.v `lf_gl`). *)
Let LF_GL : forall POST, FROM POST (OL 0) -> forall j, 0 <= j < 64 -> FROM POST (GL j) :=
  lf_gl SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB LV HSEGS SNP.
(* The odd-table loop is PROVED (lib/A/Prog/LLVMFuzzerTestOneInputOl.v `lf_ol`). *)
Let LF_OL : forall POST, FROM POST CA -> forall j, 0 <= j < 4 -> FROM POST (OL j) :=
  lf_ol SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS.
Let LF_HEAD : forall POST i, 0 <= i <= 47 ->
  (forall op, 0 <= op <= 5 -> FROM POST (ARM op i)) -> FROM POST EXIT -> FROM POST (LH i) :=
  lf_head SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS LV.
(* The six arms, one lemma per operation (op = b mod 6: read, write, mark, unmark, decide, refused). *)
(* op_decide is PROVED (lib/A/Prog/LLVMFuzzerTestOneInputOp4.v `lf_op4`), over these
   callee contracts and allocator rules, each discharged at link's instance: *)
Hypothesis MT_OK : forall S m, mo_ok MT S m.
Hypothesis MT_LE : forall S S' m, mo_le MT S S' m.
Hypothesis TXO_RO : forall i, (i < 11)%nat ->
  text_of_ro pa_segs PCAP_RLO PCAP_RHI B (fst (nth i KP_TEXTS (0, [])))
    (Z.of_nat (length (snd (nth i KP_TEXTS (0, [])))) + 1).
Hypothesis TXO_TR : text_of_traces B.
Hypothesis TXO_C : forall fy : YK11.FPState, text_of_acontract (fx := fy) SK pa_segs PCAP_RLO PCAP_RHI B MT LF_CTX.
Hypothesis RSD_C : forall fy : YK11.FPState, reac_served_decide_acontract (fx := fy) SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis MDC_C : forall fy : YK11.FPState, model_decide_acontract (fx := fy) SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis CV_C : forall fy : YK11.FPState, check_verdict_acontract (fx := fy) SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis AFREE4W : forall fy : YK11.FPState, afree04_rule_w (fx := fy) SK pa_segs B MT.
Hypothesis AFREENULL4W : forall fy : YK11.FPState, afree_null04_rule_w (fx := fy) SK pa_segs B MT.
Hypothesis LF_TRACE_FREE : lf_trace_free B.
(* The entry is PROVED (lib/A/Prog/LLVMFuzzerTestOneInputEntry.v `lf_entry`): the
   machine frame, frame_alloc_4 (ASM4, lib/A/Rt/StackSideInst.v link_stack_malloc_4), the 112 shadow bytes, the
   early-return test, the spill slots and checked_memset of g_nl (CMS, lib/A/AE2r.v asan_memset_realizes). *)
Hypothesis TL : PALib B.
Hypothesis ASM4 : astack_malloc_realizes pa_segs B 4.
Hypothesis CMS : forall ly S (W : world pa_segs) regs mem md d x n,
  ecall_pre pa_segs B ly S W regs mem md ->
  getr regs 10 = w64 d -> getr regs 11 = w64 x -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d ->
  d + n <= 2 ^ 63 ->
  dest_ok pa_segs B ly S W regs mem d n ->
  range_addressable (aview pa_segs (w_H W) mem) SHADOW_OFF d n ->
  (0 < n -> shadow_hull_vis (aview pa_segs (w_H W) mem) d n) ->
  amem_range d n ->
  SRr pa_segs W (cfg_at pa_segs 0x53214 regs mem md)
  (fun W' c' => W' = W /\ exists regs' mem' md',
    c' = cfg_at pa_segs (raZ regs) regs' mem' md' /\
    AR pa_segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
    getr regs' 10 = w64 d /\
    (forall i, 0 <= i < n -> aview pa_segs (w_H W) mem' (d + i) = Some (x mod 256)) /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (spZ regs - ESTACK <= a < spZ regs) ->
       aview pa_segs (w_H W) mem' a = aview pa_segs (w_H W) mem a) /\
    (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Let LF_ENTRY : forall POST, FROM POST (GL 0) -> START POST :=
  lf_entry SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LV LAWS TL TB HSEGS ASM4 CMS.
(* The two callocs and the loop's set-up are PROVED (lib/A/Prog/LLVMFuzzerTestOneInputBlk.v `lf_blk`),
   over the calloc rule with its depot clause (acalloc04_rule_d) and the two sites' traces. *)
Hypothesis ACALLOC4W : forall fy : YK11.FPState,
  acalloc04_rule_w (fx := fy) SK pa_segs B MT (pa_sigma LS___interceptor_trampoline_calloc) LF_CALLOC_RA0 8856 2192.
Hypothesis LF_TRACE_CALLOC : lf_trace_calloc B LF_CALLOC_RA0.
Let LF_BLK : forall POST, FROM POST (LH 0) -> FROM POST CA :=
  lf_blk SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LF_CALLOC_RA0 LAWS TB HSEGS LV MT_LE
    MT_OK ACALLOC4W LF_TRACE_CALLOC.
(* op_refused is PROVED (lib/A/Prog/LLVMFuzzerTestOneInputOp5.v `lf_op5`), over mark_quietly's two
   arms (mark_quietly_aproof_open / _again), check_mark's and check_requests' contracts. *)
Hypothesis MQO : forall fx0 : YK11.FPState,
  @mark_quietly_acontract_open fx0 rc SK pa_segs PCAP_RLO PCAP_RHI B MT (mo_malloc MT AMF_BLOCK) LF_CTX
    (fun _ => True) (mq_ledpost B).
Hypothesis MQA : forall fx0 : YK11.FPState,
  @mark_quietly_acontract_again fx0 rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis CM : forall fx0 : YK11.FPState, @check_mark_acontract fx0 rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis CR : forall fx0 : YK11.FPState, @check_requests_acontract fx0 rc SK pa_segs PCAP_RLO PCAP_RHI B.
(* op_unmark is PROVED (lib/A/Prog/LLVMFuzzerTestOneInputOp3.v `lf_op3`), over these callee
   contracts, each discharged at link's instance by its lane's proof. *)
Hypothesis KERNEL : forall fy : YK11.FPState, @kernel_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis MODEL_READ : forall fy : YK11.FPState, @model_read_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis MODEL_WRITE : forall fy : YK11.FPState, @model_write_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis ABCMP : forall fy : YK11.FPState, @abcmp_realizes fy rc pa_segs B (pa_sigma LS___interceptor_trampoline_bcmp).
Hypothesis UNMARK_ALL : forall fy : YK11.FPState,
  @reac_served_unmark_all_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis CS : forall fy : YK11.FPState, @check_socket_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis CMK : forall fy : YK11.FPState, @check_marks_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
Let LF_OP3 : forall POST i, 0 <= i <= 47 -> FROM POST (TAIL i) -> FROM POST (ARM 3 i) :=
  lf_op3 SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LV LAWS TB HSEGS MT_LE KERNEL MODEL_READ
    MODEL_WRITE ABCMP UNMARK_ALL CS CMK CR.
Let LF_OP5 : forall POST i, 0 <= i <= 47 -> FROM POST (TAIL i) -> FROM POST (ARM 5 i) :=
  lf_op5 SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS LV TB HSEGS MT_LE MT_OK
    MQO MQA CM CR.
(* op_write is PROVED (lib/A/Prog/LLVMFuzzerTestOneInputOp1.v `lf_op1`), over the contracts it
   shares with the other arms and these, each discharged at link's instance by its lane's proof. *)
Hypothesis ALIAS_WRITE : forall fy : YK11.FPState,
  @reac_link_alias_write_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis ASTRLEN : forall fy : YK11.FPState,
  @RtString.astrlen_realizes fy rc pa_segs B (pa_sigma LS___interceptor_trampoline_strlen).
Hypothesis INDEX_OF : forall fy : YK11.FPState, @index_of_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis CREF : forall fy : YK11.FPState, @check_refused_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis CWRITE : forall fy : YK11.FPState, @check_write_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
Let LF_OP1 : forall POST i, 0 <= i <= 47 -> FROM POST (TAIL i) -> FROM POST (ARM 1 i) :=
  lf_op1 SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LV LAWS TB HSEGS MT_OK MT_LE TXO_TR TXO_C
    KERNEL MODEL_WRITE ALIAS_WRITE CS ASTRLEN INDEX_OF CREF CWRITE CR AFREE4W AFREENULL4W LF_TRACE_FREE.
(* op_mark is PROVED (lib/A/Prog/LLVMFuzzerTestOneInputOp2.v `lf_op2`: the selector, kernel,
   model_begin, model_read / model_decide / model_write or bcmp, the inlined remember with its strcmp loop and
   snprintf, mark_quietly and the four checks); its one new hypothesis is the strcmp wrapper's realization. *)
Hypothesis STRCMP : forall fy : YK11.FPState,
  @RtString.astrcmp_realizes fy rc pa_segs B (pa_sigma LS___interceptor_trampoline_strcmp).
Let LF_OP2 : forall POST i, 0 <= i <= 47 -> FROM POST (TAIL i) -> FROM POST (ARM 2 i) :=
  lf_op2 SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LV LAWS TB HSEGS MT_LE MT_OK KERNEL
    MODEL_READ MDC_C MODEL_WRITE ABCMP STRCMP SNP MQO MQA CS CM CMK CR.
(* op_read is PROVED (lib/A/Prog/LLVMFuzzerTestOneInputOp0.v `lf_op0`, the op_read loop and its RS / RC / RF arms: the
   selector, the two size bytes, kernel, model_begin, two text_buf, two checked_memset, model_read,
   reac_link_alias_read, the checks, check_bounds x2, check_read, check_requests, two frees and the tail), over these
   new hypotheses, each discharged at link's instance. *)
Hypothesis TXB_C : forall fy : YK11.FPState,
  text_buf_acontract (fx := fy) SK pa_segs PCAP_RLO PCAP_RHI B MT LF_CTX.
Hypothesis TXB_TR : text_buf_traces B LF_CTX.
Hypothesis AMSET : forall fy : YK11.FPState, aintrin_realizes (fx := fy) pa_segs B OSet 0x53214.
Hypothesis ALIAS_READ : forall fy : YK11.FPState,
  @reac_link_alias_read_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis CBND : forall fy : YK11.FPState, @check_bounds_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis CREAD : forall fy : YK11.FPState, @check_read_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
Let LF_OP0 : forall POST i, 0 <= i <= 47 -> FROM POST (TAIL i) -> FROM POST (ARM 0 i) :=
  lf_op0 SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LV LAWS TB HSEGS MT_LE MT_OK KERNEL TXB_C
    TXB_TR AMSET MODEL_READ ALIAS_READ CS CREF INDEX_OF CBND CREAD CR AFREE4W AFREENULL4W LF_TRACE_FREE.
Let LF_OP4 : forall POST i, 0 <= i <= 47 -> FROM POST (TAIL i) -> FROM POST (ARM 4 i) :=
  lf_op4 SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS LV TB HSEGS MT_OK MT_LE
    TXO_RO TXO_TR TXO_C RSD_C MDC_C CV_C AFREE4W AFREENULL4W LF_TRACE_FREE.

Lemma LF_ARM : forall POST op i, 0 <= op <= 5 -> 0 <= i <= 47 ->
  FROM POST (TAIL i) -> FROM POST (ARM op i).
Proof.
  intros POST op i Hop Hi HT.
  assert (op = 0 \/ op = 1 \/ op = 2 \/ op = 3 \/ op = 4 \/ op = 5) as Hc by lia.
  destruct Hc as [->|[->|[->|[->|[->| ->]]]]].
  - exact (LF_OP0 POST i Hi HT).
  - exact (LF_OP1 POST i Hi HT).
  - exact (LF_OP2 POST i Hi HT).
  - exact (LF_OP3 POST i Hi HT).
  - exact (LF_OP4 POST i Hi HT).
  - exact (LF_OP5 POST i Hi HT).
Qed.
(* The loop tail is PROVED (lib/A/Prog/LLVMFuzzerTestOneInputTail.v `lf_tail`); its only
   Section hypothesis is the allocator's laws at the image. *)
Let LF_TAIL : forall POST i, 0 <= i <= 47 ->
  (i < 47 -> FROM POST (LH (i + 1))) -> FROM POST EXIT -> FROM POST (TAIL i) :=
  lf_tail SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS.
(* The exit is PROVED (lib/A/Prog/LLVMFuzzerTestOneInputExit.v `lf_frees` and ...Leave.v `lf_leave`, composed
   as `lf_exit`): the two frees, the retired magic, meta_fill_f5, the inline flag release, the
   restores and the return, to tfib_lib_post_x at LL 0 (m_fs md) []. ASS is meta_fill_f5's realization
   (lib/A/Rt/SetShadow.v link_set_shadow_f5). *)
Hypothesis ASS : forall fy : YK11.FPState,
  aset_shadow_realizes (fx := fy) pa_segs B (pa_sigma LS___asan_set_shadow_f5) 0xf5.
Let LF_EXIT : FROM POSTL EXIT :=
  lf_exit SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS LV MT_LE ASS MT_OK
    AFREE4W LF_TRACE_FREE.

(* ==========================================================================
   The operation loop: 48 turns, by induction on the turns left
   ========================================================================== *)

Lemma lf_loop_n : forall n i, 0 <= i <= 47 -> 48 - i <= Z.of_nat n -> FROM POSTL (LH i).
Proof.
  induction n as [|n IH]; intros i Hi Hn; [cbn in Hn; lia|].
  apply (LF_HEAD POSTL i Hi); [|exact LF_EXIT].
  intros op Hop. apply (LF_ARM POSTL op i Hop Hi).
  apply (LF_TAIL POSTL i Hi); [|exact LF_EXIT].
  intros Hlt. apply (IH (i + 1)); [lia|]. rewrite Nat2Z.inj_succ in Hn. lia.
Qed.

Lemma lf_loop_at : forall i, 0 <= i <= 47 -> FROM POSTL (LH i).
Proof.
  intros i Hi. apply (lf_loop_n (Z.to_nat (48 - i)) i Hi). rewrite Z2Nat.id by lia. lia.
Qed.

(* The whole call: from the function's first slot under lf_base to the contract's post. *)
Lemma lf_whole : START POSTL.
Proof.
  apply LF_ENTRY. apply LF_GL; [|lia]. apply LF_OL; [|lia]. apply LF_BLK. apply lf_loop_at. lia.
Qed.

End b.
End a.

(* ==========================================================================
   The bridge: from the walk at link's image instance to the entry contract
   ========================================================================== *)

Section top.
Context {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variable LF_CTX : list (list Z).
Variables LF_MO_SET LF_MO_OP LF_MO_END : Z.

#[local] Notation PIl := (@PI_link rc).
#[local] Notation SEGSl := (@pa_segs rc link_listing PIl).

(* (1) The walk, at link's image instance and at the memory FILE's record and long_alias's NUL of
   LinkEntryA.v: this is `lf_whole` above with its eight phase hypotheses discharged by the phase files
   (LLVMFuzzerTestOneInputEntry.v, ...Gl.v, ...Ol.v, ...Blk.v, ...Head.v, ...Op0.v .. ...Op5.v, ...Exit.v). *)
Hypothesis LF_WHOLE : forall fx : YK11.FPState,
  @lf_start fx rc SK PIl B MT XM_LIB XN_LIB link_amf LA_NUL LF_CTX LF_MO_SET LF_MO_OP LF_MO_END
    (@lf_post rc SK PIl B MT XN_LIB link_amf LA_NUL).

(* (2) B is link's: its owned statics are AF0m's, which is what `G_HARNESS_gx_ok` asks (LinkEntryA.v). *)
Hypothesis HOWN : as_owned_static B = Tfib_owned_static.

(* (3) The allocator-trace contexts of the call's allocating sites (the CTX of text_of / text_buf /
   mark_quietly and of the allocator rules), at the driver's return address: the start-up universe's. *)
Hypothesis HCTX : forall (cx : @lcx rc PIl) (regsT : bvmap 5 word),
  raZ (c_regs cx) = RA_LLVMF ->
  In (raZ regsT - @pa_val rc link_listing PIl A_TEXT) LF_ALLOC_SITES ->
  In (raZ regsT :: spine (lf_chain cx)) LF_CTX.

(* (4) The meter: the charges of the set-up, of one operation and of the exit fit in the budget the frame
   grants. At the closing's instance (MT := the trivial meter, XM_LIB = XN_LIB = fun _ => 0) all three are 0. *)
Hypothesis HMO : 0 <= LF_MO_SET /\ 0 <= LF_MO_OP /\ 0 <= LF_MO_END.
Hypothesis HBUD : forall n, LF_MO_SET + 48 * LF_MO_OP + LF_MO_END <= XM_LIB n.
Hypothesis HXMN : forall n, XM_LIB n <= XN_LIB n.
Hypothesis MTL : ameter_laws MT.
Hypothesis MFSL : ameter_fs_laws MT.

(* The context of the call, as the entry contract hands it over. *)
Definition top_cx (ly : alayout) (S : astate) (W : world SEGSl) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (p : Z) (pl : list byte) (T : list (Z * Z)) : @lcx rc PIl :=
  mkLCX (PI := PIl) ly S W regs mem md p pl T (Ereg regs []).

(* lf_base from the contract's pre at the lib/A instance. *)
Lemma lf_base_of_pre : forall (fx : YK11.FPState) ly S (W : world SEGSl) regs mem md p n pl T,
  @tfib_lib_pre_x rc SK SEGSl PCAP_RLO PCAP_RHI RA_LLVMF A_EMPTY LLVMF_STK B MT XM_LIB link_amf LA_NUL
    regs ly S W mem md p n pl T ->
  n = Z.of_nat (length pl) ->
  YK0o.frm_zero (@fp_csr fx) ->
  @lf_base fx rc SK PIl B MT XM_LIB XN_LIB link_amf LA_NUL LF_CTX LF_MO_SET LF_MO_OP LF_MO_END
    (top_cx ly S W regs mem md p pl T).
Proof.
  intros fx ly S W regs mem md p n pl T HPRE Hn Hfz.
  unfold lf_base, top_cx, c_n. cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_pl c_T c_E0].
  rewrite <- Hn.
  split; [exact HPRE|].
  split; [exact Hfz|].
  split; [exact (G_HARNESS_gx_ok B HOWN)|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [intros n0 r Hn0; exact (ew_Ereg_nat regs [] n0 r Hn0)|].
  split; [exact (f_equal (@bv_unsigned 64) (ew_Ereg_nat regs [] 2%nat (2%bv : bv 5) eq_refl))|].
  split.
  { intros regsT Hs.
    refine (HCTX (top_cx ly S W regs mem md p pl T) regsT _ Hs).
    destruct HPRE as (_ & Hra & _). cbn [c_regs top_cx]. exact Hra. }
  destruct HMO as (M1 & M2 & M3).
  split; [exact M1|]. split; [exact M2|]. split; [exact M3|].
  split; [exact (HBUD _)|]. split; [exact (HXMN _)|]. split; [exact MTL | exact MFSL].
Qed.

(* Row of the frame: the ASan build's entry contract of link, at the lib/A instance. *)
Theorem LLVMFuzzerTestOneInput_aproof : tfib_lib_contract_xf_all_A SK B MT XM_LIB XN_LIB.
Proof.
  unfold tfib_lib_contract_xf_all_A, tfib_lib_contract_xf_all, tfib_lib_contract_xf.
  intros fx ly S W regs mem md p n pl T K HAI HPRE Hfz HK.
  assert (Hn : n = Z.of_nat (length pl)) by (destruct HPRE as (_ & _ & _ & _ & _ & Hnpl & _); exact Hnpl).
  pose proof (lf_base_of_pre fx ly S W regs mem md p n pl T HPRE Hn Hfz) as HB.
  pose proof (LF_WHOLE fx (top_cx ly S W regs mem md p pl T) HB) as HRUN.
  cbn [LIBK ZTraceSpec.checksum_shape].
  refine (HRUN HAI _ _).
  intros W' c' Hwle HAI' HPOST.
  apply (HK (LL 0 (m_fs md) []) W' c' Hwle HAI').
  unfold lf_post, top_cx, c_n in HPOST.
  cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_pl c_T] in HPOST.
  rewrite <- Hn in HPOST.
  destruct HPOST as (fy & ly' & S' & regs' & mem' & md' & k & T' & Ec & Hz & HPOST).
  exists fy, ly', S', regs', mem', md', k, T'.
  split; [exact Ec|]. split; [exact Hz | exact HPOST].
Qed.

About LLVMFuzzerTestOneInput_aproof.
Print Assumptions LLVMFuzzerTestOneInput_aproof.

End top.
