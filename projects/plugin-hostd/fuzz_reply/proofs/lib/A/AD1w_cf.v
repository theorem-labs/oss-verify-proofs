(* The interface between fuzz_reply's program contract and the cf driver: what the driver loop supplies at each of
   target_run's calls of LLVMFuzzerTestOneInput, and what it may assume back.  Stated over ARcf (Reusable/YG0ncf.v) at
   Hp = [] and the YCbqG journal forms, in the shape of the one cf library contract that exists,
   preset_lib_contract_x (a working branch's fuzz_preset/lib/A/PresetCfnA.v:647), with three
   fuzz_reply changes, and with the per-call invariant of fuzz_state's driver port (a working branch
   e16cb210877, A/AD1w.v lib_inv_stable / lib_inv_init, A/ACfn.v tfib_lib_contract_xI) widened from (W, mem) to
   (ly, S, W, mem), because fuzz_reply's invariant names the blocks that survive a call.
   The three changes against preset's form:
   - the post's `Permutation (ablocks ...)` is REPLACED by W8's fr_surv (ACfn_cf.v): fuzz_reply's entry keeps g_src's
     table and g_out's buffer across calls and may move g_out's buffer.  A driver that keeps the Permutation proves
     something false for this image;
   - the journal is ajournal_x over the program globals G_fr_c B as its PST (the globals the call writes) and the
     footprint sink_token :: fr_FP (ACfn_cf.v; the driver's footprint lemmas are stated over a tail after
     sink_token, and W8's post, whose footprint is fr_FP alone, reaches it by footprint weakening);
   - the per-call invariant is W8's fr_gi (W_LLVMFuzzerTestOneInput_cut.v): the program's globals between calls.
   The driver's room is the Section variable LIBROOM (preset: LIB_ROOM abudget_cf CF_LIB, Reusable/YGcfNames.v:535),
   fixed with the cf driver lane.
   READABLE STACK (STKR): the pre's LAST conjunct, `forall a, spZ regs <= a < ly_top ly -> aview .. a <> None`, in the
   exact text W8's fr_lib_pre_cf / fr_lib_pre_cf_x carry last (cut.v:177, cut_x.v:100), so the bridge passes it
   through.  The driver supplies it at each call: RelocA-2's AStkPres.v (tfib_handoff_stk_pres) gives presence over
   [usp - stack_max_size, ly_top) at start-up, forwarded by memory monotonicity; CfDriver threads it and projects to
   [spZ regs, ly_top) at the call. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0ncf YGcfNames YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00cf YG01cf YGcfRoomKeep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_cut W_LLVMFuzzerTestOneInput_G ACfn_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyGuard.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0dcf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section d.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape} {ci : CfImg} {cp : CfParams}.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
(* the cf driver's room at each call (preset: LIB_ROOM abudget_cf CF_LIB); fixed with the cf driver lane *)
Variable LIBROOM : astate -> Prop.
(* NP: the cf allocator's NON-primary room between calls (preset: iface_room_np, PresetCfnA.v section 3b); in the pre
   at each call AND back in the post, so W8's contract owes it at the return.  Without it in the post the driver
   cannot free what it allocated: after the last call it frees q (AD1r.v:845 / :860) and the buffer, afree_realizes_cf
   needs acall_pre_cf, and acall_pre_cf's ROOM_cf (YGcfRoomPre.v:37) follows from no ARcf fact (CfDriver's finding,
   approved by a Theorem Labs lane 2026-10-29).  Instantiated by the cf driver lane; its laws below are the driver's named
   hypotheses, preset's texts verbatim at our types.  The step law serves only the driver's own allocator calls
   BEFORE the first call (at most 2 live blocks there); after the last call the tail law gives ROOM_cf_k S 2 once and
   the two frees are paid by the room-keeping free lemma, so the entry's surviving blocks never meet the step law.
   OPEN, not covered here: NP must also survive the entry's own malloc_cf / free_cf (W8 owes NP S' at the return);
   that law is the cf instance's (room_live_cf, a Theorem Labs lane) and joins this list when it is stated. *)
Variable NP : astate -> Prop.
Definition NP_LIVE : nat := 3.
Definition iface_room_np_init : Prop := NP YG00.init_state.
Definition iface_room_np_step : Prop :=
  (forall U S n tr trc p S', Wf_cf U S -> qtight S -> NP S -> (length (blocks S) <= NP_LIVE)%nat ->
     apath (YG00cf.malloc_cf n tr S) trc (p, S') -> NP S') /\
  (forall U S p tr trc S', Wf_cf U S -> qtight S -> NP S -> (length (blocks S) <= NP_LIVE)%nat ->
     apath (YG00cf.free_cf p tr S) trc (tt, S') -> NP S').
Definition iface_room_np_tail : Prop := forall S, NP S -> ROOM_cf_k S 2.
Local Notation segs := tfibsegs.
Local Notation rd W mem := (mrestrict (w_H W) mem).
Local Notation ARx := (ARcf (cp := cp) tfibsegs B).
Local Notation GF := (G_fr_c B).

(* ---- the per-call invariant (fpgen A/AD1w.v:23-30, widened to the layout and the allocator state) ---- *)
Definition fr_LI (ci0 : Z) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) : Prop :=
  0 <= ci0 <= 4 /\ fr_gi B GF ly S W mem.
(* the live blocks the driver holds at a call: each at a positive address, ending inside the address space.  The
   driver has it from AR (AR_blocks_law, Reusable/YG0d.v:435: 4096 <= p, p + req_size n <= alloc_ceiling).
   fr_lib_inv_stable needs it: fr_gi does not bound the table / g_out addresses it names, and fr_FP drops the
   table's range when g_src reads 0 (counterexample without it: lib/A/AD1w_cf_inv.v fr_lib_inv_stable_v0_false) *)
Definition fr_blk_ok (ly : alayout) (S : astate) : Prop :=
  forall p n, In (p, n) (ablocks B ly S) -> 0 < p /\ p + n <= 2 ^ 64.
(* it survives what the driver does between calls: every byte of the globals and of the surviving blocks is kept,
   and every block stays live (fpgen's lib_inv_stable, whose footprint is the harness statics) *)
Definition fr_lib_inv_stable : Prop :=
  forall ci0 regs ly S (W : world segs) mem ly' S' (W' : world segs) mem',
  fr_LI ci0 ly S W mem ->
  fr_blk_ok ly S ->
  (forall a, inG GF a \/ inFP (fr_FP regs ly S W mem) a ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a /\
     (apresent (w_H W) mem a -> apresent (w_H W') mem' a) /\
     (writable_at segs (rd W mem) a -> writable_at segs (rd W' mem') a)) ->
  (forall b, In b (ablocks B ly S) -> In b (ablocks B ly' S')) ->
  fr_LI ci0 ly' S' W' mem'.
(* it holds at the first call, from the start-up state: every global object byte reads its start-up value
   (AF0m's .bss zero facts; g_wake is .data {-1, -1}, W_rep.v:42) and is writable, and no harness block is live
   (fpgen's lib_inv_init, whose premise is the statics holding their image values); errno is AF0m's (ts_errno:
   as_errno B = TFIB_ERRNO), whose four bytes are image bytes, readable and writable in every memory.  No presence:
   start-up never stores to a global, so its bytes read through seg_rom and are absent, and fr_gi asks writability
   (W8's ruling G4, a working branch ec4dd616ed1 W_LLVMFuzzerTestOneInput_cut.v:148) *)
Definition fr_lib_inv_init : Prop :=
  as_errno B = TFIB_ERRNO_A ->
  forall (ly : alayout) (S : astate) (W : world segs) mem (init : Z -> Z),
  (forall a, inG G_fr_obj a -> aview segs (w_H W) mem a = Some (init a) /\ writable_at segs (rd W mem) a) ->
  (forall a, inG G_fr_obj a ->
     Some (init a) = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)) \/
     (seg_rom segs (Z_to_bv 64 a) = None /\ init a = 0)) ->
  fr_LI 0 ly S W mem.

(* ---- the call's pre and post as the driver sees them ---- *)
Definition fr_lib_pre_drv (regs : bvmap 5 word) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (mem : word -> option byte) (md : Model) (p n : Z) (pl : list byte) (M : Z) (ci0 : Z) : Prop :=
  afn_pre_x segs B ARx LLVMF_STK ly S Hp W regs mem md [] /\
  raZ regs = RA_LLVMF /\
  getr regs 10 = w64 p /\ getr regs 11 = w64 n /\
  ((n = 0 /\ p = A_EMPTY) \/ (0 < n < 2 ^ 26 /\ In (p, n) (ablocks B ly S))) /\
  n = Z.of_nat (length pl) /\ garr8 segs (rd W mem) p (map (fun b : byte => bv_unsigned b) pl) /\
  frames S = [] /\ Hp = [] /\
  fr_live_pre S /\ LIBROOM S /\ NP S /\
  0 <= ci0 < 4 /\ fr_LI ci0 ly S W mem /\
  rom_view segs W mem /\
  arodata_okS segs B RLO RHI (aview segs (w_H W) mem) /\
  asink_none segs tfib_K (rd W mem) md /\
  fd_lookup (m_fds md) (alloc_fd (m_fds md)) = None /\
  Fs.fs_sorted (m_fs md) = true /\
  ameta_inv segs tfib_K ly (rd W mem) M /\
  mo_ok MT S (XM_LIB n) /\
  (* STKR *)
  (forall a, spZ regs <= a < ly_top ly -> aview segs (w_H W) mem a <> None) /\
  (* HFP (W8Entry-2's clause, a Theorem Labs lane 22:44Z): the input block and the harness blocks are distinct and the
     harness blocks alive; the driver has it from fr_heap (AD1r_heap_cf.v H_call) *)
  (List.NoDup ((if n =? 0 then [] else [(p, n)]) ++ fr_hblks W mem) /\ incl (fr_hblks W mem) (ablocks B ly S)) /\
  (* XCNT (W8's cut.v text, ACfn_cf.v fr_xcnt_ok): the relay and g_out as the globals hold them, and few other live
     blocks; the driver has it from fr_heap (AD1r_heap_cf.v H_xcnt) *)
  fr_xcnt_ok B ly S W mem (if n =? 0 then [] else [(p, n)]) /\
  (* CAPOUT (W8's cut.v text, ACfn_cf.v fr_capout_ok): 0 <= g_capout <= CAPOUT_MAX; the driver has it from
     fr_heap (AD1r_heap_cf.v H_capout) *)
  fr_capout_ok W mem /\
  (* field round 3 (Part A), last: the call memory's read-only bytes (part 3c: over aro_addr_cf, the RELRO range and
     the cf_ro_reads ranges), the conjunct W1 adds to top_x's ARX (W_LLVMFuzzerTestOneInput_top_x.v); the driver
     carries it from main's hand-off (A/AD1vcf.v relro_ok) *)
  YG0dcf.arodata_ok_cf segs B mem.
Definition fr_lib_post_drv (regs : bvmap 5 word) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (mem : word -> option byte) (md : Model) (p n : Z) (M : Z) (ci0 : Z) (l : lleaf)
  (ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model)
  (k : Z) : Prop :=
  ajournal_x (SK := AE2k.tfib_sink_head) segs B GF ARx LLVMF_STK (spZ regs) (sink_token :: fr_FP regs ly S W mem)
    ly S Hp W mem md [] ly' S' [] W' mem' md' k /\
  fr_live_post S S' k /\ NP S' /\
  aregs_preserved regs regs' /\ getr regs' 10 = w64 0 /\
  fr_surv B ly S W mem ly' S' W' mem' /\
  fr_LI (ci0 + 1) ly' S' W' mem' /\ rom_view segs W' mem' /\
  (forall fd, fd_lookup (m_fds md') fd = fd_lookup (m_fds md) fd) /\
  m_fs md' = ll_fs l /\ ll_ret l = 0 /\ ll_out l = [] /\ Fs.fs_sorted (ll_fs l) = true /\
  asink_none segs tfib_K (rd W' mem') md' /\
  ameta_inv segs tfib_K ly' (rd W' mem') M /\
  mo_le MT S S' (XN_LIB n) /\
  (forall i, 0 <= i < n -> aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i)) /\
  (* HFP at the return (W8's cut.v:207 text): what the driver's fr_heap steps by (AD1r_heap_cf.v H_step) *)
  (List.NoDup (fr_hblks W' mem') /\ incl (fr_hblks W' mem') (ablocks B ly' S')) /\
  (* XCNT at the return, at the call's (p, n): fr_heap's at the next call (AD1r_heap_cf.v H_step) *)
  fr_xcnt_ok B ly' S' W' mem' (if n =? 0 then [] else [(p, n)]) /\
  (* CAPOUT at the return: fr_heap's at the next call (AD1r_heap_cf.v H_step) *)
  fr_capout_ok W' mem' /\
  (* field round 3 (Part A), last: the RELRO bytes at the return, from the post journal's ARX (lib/A/W_LLVMFuzzerTestOneInput_top_x.v, W1) *)
  YG0dcf.arodata_ok_cf segs B mem'.
(* the program slot as the cf driver consumes it, at call ci0 of target_run's (fpgen ACfn.v tfib_lib_contract_xI) *)
Definition fr_lib_contract_drv : Prop :=
  forall ly S Hp (W : world segs) (regs : bvmap 5 word) mem md p n pl M (K : lleaf -> TSet) (ci0 : Z),
  AI segs (w_H W) (w_A W) md ->
  fr_lib_pre_drv regs ly S Hp W mem md p n pl M ci0 ->
  (forall (l : lleaf) (W' : world segs) (c' : config),
     wle W W' -> AI segs (w_H W') (w_A W') (cfg_model c') ->
     (exists ly' S' regs' mem' md' k,
        c' = cfg_at segs RA_LLVMF regs' mem' md' /\
        fr_lib_post_drv regs ly S Hp W mem md p n M ci0 l ly' S' W' regs' mem' md' k) ->
     srealizes segs c' (K l)) ->
  srealizes segs (cfg_at segs A_LLVMF regs mem md) (LIBK pl (m_fs md) K).
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the call's post and the slot at a world relation R (the library run can free,
   so at the cf instance R := wle' segs RZ_cf).  At R := wle they are fr_lib_post_drv / fr_lib_contract_drv (the two
   _wle lemmas below, by reflexivity). *)
Section dR.
Variable R : world segs -> world segs -> Prop.
Definition fr_lib_post_drvR (regs : bvmap 5 word) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (mem : word -> option byte) (md : Model) (p n : Z) (M : Z) (ci0 : Z) (l : lleaf)
  (ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model)
  (k : Z) : Prop :=
  ajournal_xR (SK := AE2k.tfib_sink_head) segs B GF ARx R LLVMF_STK (spZ regs) (sink_token :: fr_FP regs ly S W mem)
    ly S Hp W mem md [] ly' S' [] W' mem' md' k /\
  fr_live_post S S' k /\ NP S' /\
  aregs_preserved regs regs' /\ getr regs' 10 = w64 0 /\
  fr_surv B ly S W mem ly' S' W' mem' /\
  fr_LI (ci0 + 1) ly' S' W' mem' /\ rom_view segs W' mem' /\
  (forall fd, fd_lookup (m_fds md') fd = fd_lookup (m_fds md) fd) /\
  m_fs md' = ll_fs l /\ ll_ret l = 0 /\ ll_out l = [] /\ Fs.fs_sorted (ll_fs l) = true /\
  asink_none segs tfib_K (rd W' mem') md' /\
  ameta_inv segs tfib_K ly' (rd W' mem') M /\
  mo_le MT S S' (XN_LIB n) /\
  (forall i, 0 <= i < n -> aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i)) /\
  (List.NoDup (fr_hblks W' mem') /\ incl (fr_hblks W' mem') (ablocks B ly' S')) /\
  fr_xcnt_ok B ly' S' W' mem' (if n =? 0 then [] else [(p, n)]) /\
  fr_capout_ok W' mem' /\
  YG0dcf.arodata_ok_cf segs B mem'.
Definition fr_lib_contract_drvR : Prop :=
  forall ly S Hp (W : world segs) (regs : bvmap 5 word) mem md p n pl M (K : lleaf -> TSet) (ci0 : Z),
  AI segs (w_H W) (w_A W) md ->
  fr_lib_pre_drv regs ly S Hp W mem md p n pl M ci0 ->
  (forall (l : lleaf) (W' : world segs) (c' : config),
     R W W' -> AI segs (w_H W') (w_A W') (cfg_model c') ->
     (exists ly' S' regs' mem' md' k,
        c' = cfg_at segs RA_LLVMF regs' mem' md' /\
        fr_lib_post_drvR regs ly S Hp W mem md p n M ci0 l ly' S' W' regs' mem' md' k) ->
     srealizes segs c' (K l)) ->
  srealizes segs (cfg_at segs A_LLVMF regs mem md) (LIBK pl (m_fs md) K).
End dR.
Lemma fr_lib_post_drv_wle : fr_lib_post_drv = fr_lib_post_drvR (@wle segs). Proof. reflexivity. Qed.
Lemma fr_lib_contract_drv_wle : fr_lib_contract_drv = fr_lib_contract_drvR (@wle segs). Proof. reflexivity. Qed.
End d.

(* the slot at every FP state, as the composition takes it (preset_lib_contract_x_all / tfib_lib_contract_xI_all) *)
Definition fr_lib_contract_drv_all {rc : YM05.RunCeil} {LS : lib_shape} {ci : CfImg} {cp : CfParams}
  (B : asyms) (MT : ameter_ops) (XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z) (LIBROOM NP : astate -> Prop) : Prop :=
  forall fx : YK11.FPState,
    fr_lib_contract_drv (fx := fx) (rc := rc) (LS := LS) (cp := cp) B MT XM_LIB XN_LIB RLO RHI LIBROOM NP.
(* the slot at R, at every FP state (route R; at R := wle it is fr_lib_contract_drv_all) *)
Definition fr_lib_contract_drv_allR {rc : YM05.RunCeil} {LS : lib_shape} {ci : CfImg} {cp : CfParams}
  (B : asyms) (MT : ameter_ops) (XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z) (LIBROOM NP : astate -> Prop)
  (R : world tfibsegs -> world tfibsegs -> Prop) : Prop :=
  forall fx : YK11.FPState,
    fr_lib_contract_drvR (fx := fx) (rc := rc) (LS := LS) (cp := cp) B MT XM_LIB XN_LIB RLO RHI LIBROOM NP R.
