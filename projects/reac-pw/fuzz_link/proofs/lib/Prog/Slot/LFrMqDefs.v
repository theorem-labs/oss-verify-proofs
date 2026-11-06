(* The slot LLVMFuzzerTestOneInput (fuzz_link.c:764-790), plain image: the mark_quietly step at the SR level
   (S-FR item 6), its definitions and the statement of lfr_mark (proved in lib/Prog/Slot/LFrMq.v).

   mark_quietly (0x15d88; lib/Prog/mark_quietly_c.v) is called at 0x13dac (op_mark, ra 0x13db0) and at 0x13c70
   (op_refused, ra 0x13c74). The step goes from a CUT at 0x15d88 to a CUT at ra; on the way it opens the slot's
   memory FILE (the first mark of the run: the kept set T is [] and g_sink = 0) or keeps it (T = [(f, MF_BLOCK)],
   g_sink = f). The new kept set is [(f, MF_BLOCK)]; the FILE joins the slot's heap blocks hb when this driver
   call opened it (lmq_hb).
   - lmq_sink: what the FILE the call finds is, and where it lies (for the arm's premises at that sink);
   - lmq_arm: the premises of mark_quietly_contract the arm gives (over the arm's cut state: its registers R and
     its memory, the evt-level view normalize_cj of the config's);
   - lmq_post: the contract's Post over the two views, with the frame's carry (LFrCall.lfr_call_core) and the
     FILE's placement;
   - lmq_hb: the slot's heap blocks after the call. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Contract Img0 FrameAPI MemFile MemFileRI.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import AllocSlots AllocRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Regs6ss MState.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import LLVMFuzzerTestOneInput_c link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import memfile_c reac_served_mark_c mark_quietly_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require StdioModel.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LFr.
Import ListNotations.
Local Open Scope Z_scope.

(* the slot's heap blocks after the call: the FILE joins them when this driver call opened it *)
Definition lmq_hb (T : list (Z * Z)) (f : Z) (hb : list (Z * Z)) : list (Z * Z) :=
  match T with
  | [] => (f, MF_BLOCK) :: hb
  | _ => hb
  end.

(* The premises of mark_quietly_contract the arm gives, at the sink the call finds: over the arm's cut state
   (registers R, memory m = the view normalize_cj of the config's). a0 = getr R 10 (the marks block or NULL),
   a1 = getr R 11 (the name or NULL). *)
Definition lmq_arm (g : lghost) (hb : list (Z * Z)) (R : bvmap 5 word) (m : word -> option byte)
    (sink : Z) (tab : list (list byte * Z)) (kbs : list byte) (nm : option (list byte)) : Prop :=
  nlk_at m kbs /\ nlk_wf kbs /\ nk_open kbs = 0 /\ iftab_at m kbs tab /\
  nk_opened kbs + 2 < 2 ^ 31 /\ nk_closed kbs + 2 < 2 ^ 31 /\
  policy_ro m /\ str_arg m (bv_unsigned (getr R 11)) nm /\
  mark_errno_ok m R MARK_QUIETLY_K sink /\
  mark_table_ok m R MARK_QUIETLY_K sink tab /\
  (bv_unsigned (getr R 10) <> 0 ->
     exists q n, In (q, n) hb /\ q <= bv_unsigned (getr R 10) /\ bv_unsigned (getr R 10) + MK_SIZE <= q + n) /\
  (forall s, nm = Some s -> kept_str (bv_unsigned (getr R 11)) (name_span (bv_unsigned (getr R 11)) s)) /\
  (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
     u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> 0 <= p < 2 ^ 64 ->
     kept_str p (Z.of_nat (length n2) + 1)) /\
  mark_name_ok m R MARK_QUIETLY_K sink nm /\
  mark_block_ok m R MARK_QUIETLY_K sink /\
  guard_words m.

Section MQD.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.

(* The FILE the call finds (LFR's mf_gi T and lkept): none (T = [], g_sink = 0), or the kept block
   T = [(sink, MF_BLOCK)], in the heap below the slot's stack window, outside the image (and so wholly below or
   above its address range, mf_place_ok), apart from every other block of hb and of the entry blocks, and an
   entry block only when it is the entry's kept FILE (then lg_T g = [(sink, MF_BLOCK)]). *)
Definition lmq_sink (g : lghost) (hb T : list (Z * Z)) (sink : Z) : Prop :=
  (T = [] /\ sink = 0) \/
  (T = [(sink, MF_BLOCK)] /\ 4096 <= sink /\ sink + MF_BLOCK <= lg_S g - SLOT_STACK /\
   mf_place_ok sink /\ (forall i, 0 <= i < MF_BLOCK -> ~ in_img B (sink + i)) /\
   (forall a k, In (a, k) hb -> (a, k) <> (sink, MF_BLOCK) -> sink + MF_BLOCK <= a \/ a + k <= sink) /\
   (forall a k, In (a, k) (blocks (lg_L g) (lg_A g)) -> (a, k) <> (sink, MF_BLOCK) ->
      sink + MF_BLOCK <= a \/ a + k <= sink) /\
   (In (sink, MF_BLOCK) (blocks (lg_L g) (lg_A g)) -> lg_T g = [(sink, MF_BLOCK)])).

(* mark_quietly's Post over the views m (the call's) and m' (the return's): the callee-saved registers, the
   rounding mode, the frame's carry of the regions an allocator-facing call keeps minus what this call writes
   (mq_writes: g_nl up to the request ring, g_sink, g_say, g_said, the open-file list head, the marks block,
   the FILE block), what every step gives (lpost_mem), the three heads and the FILE with at most one line
   pending, the FILE kept (sink <> 0) or fresh (sink = 0), and the answer: the refusal (a0 = 0) or the
   library's mark (a0 <> 0), word for word at tab / kbs / nm. *)
Definition lmq_post (g : lghost) (hb T : list (Z * Z)) (R : bvmap 5 word) (m : word -> option byte)
    (sink : Z) (tab : list (list byte * Z)) (kbs : list byte) (nm : option (list byte))
    (regs' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte) (sink' : Z) : Prop :=
  regs_preserved R regs' /\ frm0 fc' /\
  lcarry (fun x => lkeep B g hb x /\ ~ mq_writes (bv_unsigned (getr R 10)) sink' x) m m' /\
  lpost_mem g m' /\
  u64_at m' A_G_SINK sink' /\ u64_at m' A_G_SAY sink' /\ u64_at m' StdioModel.A_OFL_HEAD sink' /\
  sink' <> 0 /\
  (exists k', k' <= MARK_LINE_MAX /\ memfile_k m' sink' k') /\
  (sink <> 0 -> sink' = sink) /\
  (sink = 0 -> lfresh B g hb sink' MF_BLOCK) /\
  (bv_unsigned (getr R 10) = 0 -> getr regs' 10 = Z_to_bv 64 (- E_INVAL) /\ nlk_at m' kbs) /\
  (bv_unsigned (getr R 10) <> 0 -> forall gbs,
     marks_at m (bv_unsigned (getr R 10)) gbs ->
     let M := mark_lib tab nm (mk_names gbs) (nk_sent kbs) (nk_kstate kbs) in
     getr regs' 10 = Z_to_bv 64 (m_rc M)
     /\ (exists gbs', marks_at m' (bv_unsigned (getr R 10)) gbs'
           /\ marks_wf gbs' /\ mk_names gbs' = m_marks M
           /\ mk_n gbs' = Z.of_nat (length (m_marks M)))
     /\ (exists kbs', nlk_at m' kbs' /\ nlk_wf kbs'
           /\ nk_chunks kbs' = nk_chunks kbs /\ nk_end_errno kbs' = nk_end_errno kbs
           /\ nk_n_if kbs' = nk_n_if kbs /\ iftab_at m' kbs' tab
           /\ nk_next kbs' = Z.of_nat (k_next (m_state M))
           /\ nk_sent kbs' = m_reqs M
           /\ nk_n_sent kbs' = Z.of_nat (length (m_reqs M))
           /\ nk_open kbs' = 0 /\ nk_misuse kbs' = nk_misuse kbs
           /\ nk_opened kbs' - nk_closed kbs' = nk_opened kbs - nk_closed kbs
           /\ nk_opened kbs <= nk_opened kbs' <= nk_opened kbs + 2)).

(* THE STEP (proved in LFrMq.v as lfr_mark): from a CUT at mark_quietly's entry to a CUT at ra with the FILE f
   kept and, when this call opened it, among the slot's heap blocks. *)
Definition lfr_mark_stmt : Prop :=
  forall g hb T ra (P : machine_state -> Prop) (P' : Z -> machine_state -> Prop) c,
  lroom_hb hb -> 0 <= ra < 2 ^ 64 -> ra mod 2 = 0 ->
  CUT B API g MARK_QUIETLY hb T P c ->
  (forall ms, P ms -> getr (ms_regs ms) 1 = Z_to_bv 64 ra /\
     getr (ms_regs ms) 2 = Z_to_bv 64 (lg_S g - SLOT_FRAME) /\ getr (ms_regs ms) 4 = Z_to_bv 64 A_TP) ->
  (forall ms sink, P ms -> lmq_sink g hb T sink ->
     exists tab kbs nm, lmq_arm g hb (ms_regs ms) (ms_mem ms) sink tab kbs nm) ->
  (forall R F fc m sink tab kbs nm regs' F' fc' m' sink',
     P (MS R F (Z_to_bv 64 MARK_QUIETLY) fc None m (seg_rom rsegs)) -> lmq_sink g hb T sink ->
     lmq_arm g hb R m sink tab kbs nm ->
     lmq_post g hb T R m sink tab kbs nm regs' fc' m' sink' ->
     P' sink' (MS regs' F' (Z_to_bv 64 ra) fc' None m' (seg_rom rsegs))) ->
  SR (ms_segs B) c (fun c' => exists f, CUT B API g ra (lmq_hb T f hb) [(f, MF_BLOCK)] (P' f) c').

End MQD.
