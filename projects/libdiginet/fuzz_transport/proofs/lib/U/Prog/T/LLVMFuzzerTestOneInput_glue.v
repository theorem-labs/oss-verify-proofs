(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths changed; 522 of its 775 lines of code are new or changed and 274 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/Prog/T/TSRGlue.v, with its module paths changed; 922 of its 1003 lines of code are new or changed and 694 lines of the source are left out. *)
(* The SR glue of the ubsan walk of LLVMFuzzerTestOneInput: the pieces of U/Prog/T/LLVMFuzzerTestOneInput_lh.v
   (entry, dispatch, the nine ops, latch, exit; each an evt walk over the normalized memory), bound by
   U/Prog/T/TSRGlue.v's run step (X_run: g_run / g_run_cf) and the SR contracts of receive and build_and_receive
   (X_recv / X_bar, at every FP state: each call returns at an fx' of its own). One proof for the SR form (X = SR,
   ROOM = room_slots) and the cut-free form (X = SRcf, ROOM = room_cf), as the build_and_receive walk
   (U/Prog/T/build_and_receive.v bar_gen).
   The loop: lg_loop, by induction on the fuel OPS_MAX - ops, carries the model's loop invariant
   `forall A, lh_heap_ok A -> exists Bw', LLVMFuzzerTestOneInput_loop_m f timg_ubsan B A D c k = Some (Bw', tt)`
   (TModel/TOpsA.v loop_m_step_at); a receiving op fixes A k to the heap frame its malloc returned.
   The end: lib_post with G = frame_G (the world) from TSRGlue's sr_fr (lg_lib_post), sink_none kept by the image
   clause (SINK: the sink words lie in the image, apart from the allocator, errno and the world). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Reusable Require YK14 YO10.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Contract Img0 SlotAgree AgreeLift FrameAPI
  AllocRoom.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem Frame MState Regs6ss RegisterBridge Exec Step Cells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldMem TImg TCb TOps TOpsA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require RoAdapt.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract GI receive_c
  build_and_receive_c TSRGlue LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_fr.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require build_and_receive.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------- registers *)

(* The register file X_run's continuation hands back, as the explicit file of the end state. *)
Lemma lg_mkR_of : forall (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25
    v26 v27 v28 v29 v30 v31 : word) regs,
  Regs6ss.xregs_eqv (Frame.mkR v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24
                       v25 v26 v27 v28 v29 v30 v31) regs ->
  Regs6ss.mkR_of regs = Frame.mkR v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23
                          v24 v25 v26 v27 v28 v29 v30 v31.
Proof.
  intros v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29
    v30 v31 regs H.
  unfold Regs6ss.mkR_of.
  repeat match goal with |- context [reg_get regs ?r] => rewrite <- (H r eq_refl) end.
  reflexivity.
Qed.

(* After a call that keeps the callee-saved registers of regs1 (explicit as the file mkR v1 .. v31), the file regs2
   with its caller-saved registers as they are. *)
Lemma lg_mkR_cs : forall (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25
    v26 v27 v28 v29 v30 v31 : word) regs1 regs2,
  Regs6ss.xregs_eqv (Frame.mkR v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24
                       v25 v26 v27 v28 v29 v30 v31) regs1 ->
  regs_preserved regs1 regs2 ->
  Regs6ss.mkR_of regs2 =
    Frame.mkR (reg_get regs2 1) v2 v3 v4 (reg_get regs2 5) (reg_get regs2 6) (reg_get regs2 7) v8 v9
      (reg_get regs2 10) (reg_get regs2 11) (reg_get regs2 12) (reg_get regs2 13) (reg_get regs2 14)
      (reg_get regs2 15) (reg_get regs2 16) (reg_get regs2 17) v18 v19 v20 v21 v22 v23 v24 v25 v26 v27
      (reg_get regs2 28) (reg_get regs2 29) (reg_get regs2 30) (reg_get regs2 31).
Proof.
  intros v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29
    v30 v31 regs1 regs2 HX HP.
  unfold Regs6ss.mkR_of. f_equal.
  all: lazymatch goal with
       | |- reg_get ?R2 ?r = reg_get ?R2 ?r => reflexivity
       | |- reg_get ?R2 ?r = _ =>
           transitivity (reg_get regs1 r);
           [ let z := eval cbv in (bv_unsigned r) in exact (HP z ltac:(unfold callee_saved; lia))
           | rewrite <- (HX r eq_refl); reflexivity ]
       end.
Qed.

(* ---------------------------------------------------------------- memory *)

Lemma lg_blk_bytes : forall (B : malloc_syms) m A bs, ms_segs B = rsegs -> 0 <= A ->
  A + Z.of_nat (length bs) <= 2 ^ 64 -> blk_data B m A bs -> Mem.bytes_at rsegs m A bs.
Proof. exact build_and_receive.bar_blk_bytes. Qed.

Lemma lg_bytes_blk : forall (B : malloc_syms) m A bs, ms_segs B = rsegs -> Mem.bytes_at rsegs m A bs -> blk_data B m A bs.
Proof. exact build_and_receive.bar_bytes_blk. Qed.

(* The relro block lies inside frame_RELRO's first block [0x21ee8, 0x22050): G_img_c gives relro_img. *)
Lemma lg_relro_of_G : forall (B : malloc_syms) mem, ms_segs B = rsegs -> G_img_c B frame_RELRO mem -> relro_img mem.
Proof.
  intros B mem HS H i Hi. specialize (H (RELRO_BASE + i)).
  change (mbyte rsegs mem (RELRO_BASE + i) = seg_rom rsegs (Mem.wa (RELRO_BASE + i))).
  rewrite <- HS. apply H. exists 0x21ee8, (0x22050 - 0x21ee8). split.
  - unfold frame_RELRO. left. reflexivity.
  - unfold RELRO_BASE, RELRO_LEN in *. lia.
Qed.

Section S.
Context {SH : sink_head} {SK : sink_syms}.

Definition lg_sink_addr (a : Z) : Prop :=
  (sk_ofl_head <= a < sk_ofl_head + 8) \/ a = sk_threaded \/ (sk_ofl_lock <= a < sk_ofl_lock + 4).

Lemma lg_sink_none_kept : forall (B : malloc_syms) mem mem' md,
  (forall a, lg_sink_addr a -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a) ->
  sink_none B mem md -> sink_none B mem' md.
Proof.
  intros B mem mem' md Hfr ((Ht & Hl) & Hhead & Hn).
  split; [split|split; [|exact Hn]].
  - eapply val_mem_frame; [|exact Ht]. intros x Hx. apply Hfr. right. left. cbn in Hx. lia.
  - eapply val_mem_frame; [|exact Hl]. intros x Hx. apply Hfr. right. right. cbn in Hx. lia.
  - apply (val_mem_word_mem (ms_segs B)). apply (val_mem_word_mem (ms_segs B)) in Hhead.
    eapply val_mem_frame; [|exact Hhead]. intros x Hx. apply Hfr. left. cbn in Hx. lia.
Qed.

End S.

Lemma lg_callee_cases : forall x, callee_saved x ->
  x = 2 \/ x = 3 \/ x = 4 \/ x = 8 \/ x = 9 \/ x = 18 \/ x = 19 \/ x = 20 \/ x = 21 \/
  x = 22 \/ x = 23 \/ x = 24 \/ x = 25 \/ x = 26 \/ x = 27.
Proof. intros x Hx. unfold callee_saved in Hx. lia. Qed.

Lemma lg_fds_vm : forall vm md, m_fds (with_vmmaps vm md) = m_fds md.
Proof. intros vm md. destruct md as [f [mp lz mt] io fs pr li ti]. reflexivity. Qed.

(* lia over the frame constants *)
Ltac lgl := try (unfold build_and_receive_FRAME in *); try (unfold receive_FRAME in *);
  try (unfold ALLOC_STACK in *); try (unfold LH_K in *); try (unfold LH_FRAME in *); lia.

(* ---------------------------------------------------------------- the generic run *)

Section Gen.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis HGG : ms_got_guard B = H_GUARD_GOT.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis WORLD : forall a, h_world a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis RELRO : forall a, RELRO_BASE <= a < RELRO_BASE + RELRO_LEN ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis CTX_LOW : ms_ctx B + CTX_SIZE <= alloc_ceiling.
Hypothesis SINK : forall a, lg_sink_addr a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4) /\ ~ h_world a.

(* SR rsegs or SRcf B; ROOM the matching budget *)
Variable X : config -> (config -> Prop) -> Prop.
Variable ROOM : Model -> sbound -> Z -> Prop.
Hypothesis X_bind : forall c (R Q : config -> Prop), X c R -> (forall c', R c' -> X c' Q) -> X c Q.
Hypothesis X_ret : forall c (Q : config -> Prop), Q c -> X c Q.
Hypothesis X_run : forall stk S L0 A0 mem0 md0 (fx' : FPState) regs pc mem md L A
    (Q : machine_state -> Prop) (P : config -> Prop),
  sr_fr B API stk S L0 A0 mem0 md0 L A mem md -> alloc_ceiling + stk <= S -> S <= 2 ^ 64 ->
  Exec.evt rsegs Q (MState.MS (Regs6ss.mkR_of regs) (@fp_regs fx') pc (@fp_csr fx') None
                      (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R F pc' fc m' W, ms = MState.MS R F pc' fc None m' (seg_rom rsegs) /\
     Frame.munch W (normalize rsegs mem) m' /\ Frame.wmono rsegs (normalize rsegs mem) m' /\
     (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x ->
        (S - stk <= x < S) \/ h_world x \/ exists y k, sr_mine L0 A0 L A y k /\ y <= x < y + k)) ->
  (forall R F pc' fc m0', Q (MState.MS R F pc' fc None m0' (seg_rom rsegs)) ->
     forall regs' m', Regs6ss.xregs_eqv R regs' -> mem_rel rsegs m' m0' ->
     sr_fr B API stk S L0 A0 mem0 md0 L A m' md ->
     X (mkCfg (@mkst (mkFP F fc) regs' pc' m' (seg_rom rsegs)) md) P) ->
  X (mkCfg (@mkst fx' regs pc mem (seg_rom rsegs)) md) P.
Hypothesis X_recv : forall (fx' : FPState) L A regs mem md b (Bw : list byte) (p : Z) (bytes : list byte)
    (by_poll pf : Z),
  h_pre B API receive_FRAME L A regs mem md b Bw -> frm_zero (@fp_csr fx') ->
  receive_args B L A regs mem Bw p bytes by_poll pf -> ROOM md b (Z.max 1 (Z.of_nat (length bytes))) ->
  X (mkCfg (@mkst fx' regs (Z_to_bv 64 receive_ENTRY) mem (seg_rom rsegs)) md)
    (receive_ret B API L A regs mem md b Bw bytes by_poll pf).
Hypothesis X_bar : forall (fx' : FPState) L A regs mem md b (Bw : list byte) (dstp srcp bodyp : Z)
    (dst src body : list byte) (send ack retry cmd : Z),
  h_pre B API build_and_receive_FRAME L A regs mem md b Bw -> frm_zero (@fp_csr fx') ->
  bar_args B L A regs mem Bw dstp srcp bodyp dst src body send ack retry cmd ->
  ROOM md b (Z.max 1 (bar_len dst src send ack retry cmd body)) ->
  X (mkCfg (@mkst fx' regs (Z_to_bv 64 build_and_receive_ENTRY) mem (seg_rom rsegs)) md)
    (bar_ret B API L A regs mem md b Bw dst src body send ack retry cmd).

(* the pieces *)
Hypothesis ENTRY : llvm_entry_stmt.
Hypothesis DISP : llvm_disp_stmt.
Hypothesis LATCH : llvm_latch_stmt.
Hypothesis EXIT : llvm_exit_stmt.
Hypothesis OP0 : llvm_op_recv_stmt 0.
Hypothesis OP8 : llvm_op_recv_stmt 8.
Hypothesis OP1 : llvm_op_bar_stmt 1 LH_RET_BAR1.
Hypothesis OP2 : llvm_op_bar_stmt 2 LH_RET_BAR2.
Hypothesis OP3 : llvm_op_stmt 3.
Hypothesis OP4 : llvm_op_stmt 4.
Hypothesis OP5 : llvm_op_stmt 5.
Hypothesis OP6 : llvm_op_stmt 6.
Hypothesis OP7 : llvm_op_stmt 7.

(* the walk's entry *)
Variables (j : nat) (ra empty stk : Z) (L0 : layout) (A0 : astate) (regs0 : bvmap 5 word)
  (mem0 : word -> option byte) (md0 : Model) (data : Z) (D : list byte) (b0 : sbound) (Bw0 : list byte).
Hypothesis HKS : LLVM_K <= stk.
Hypothesis HRA : YK0s.ret_ok (Z_to_bv 64 ra).
Hypothesis PRE : llvm_walk_pre B API j ra empty stk L0 A0 regs0 mem0 md0 data (Z.of_nat (length D)) D b0 Bw0.
Hypothesis ROOMB : forall L A mem md k, aa_MR API L A mem md -> 1 <= k <= 65536 -> ROOM md b0 k.

Local Abbreviation SS := (spZ regs0).
Local Abbreviation LO := (spZ regs0 - stk).
Local Abbreviation SP := (spZ regs0 - LH_FRAME).
Local Abbreviation WFP := [(spZ regs0 - stk, spZ regs0 - LH_FRAME + LH_FRAME); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)].

Definition INV (f : nat) (c : fuzz_in) (Bw : list byte) (k : nat) : Prop :=
  forall A, lh_heap_ok A -> exists Bw', LLVMFuzzerTestOneInput_loop_m f timg_ubsan Bw A D c k = Some (Bw', tt).

(* An SR configuration of the walk: the run relation from the entry, the budget, frm_zero, and the program point P
   of the machine state on the normalized memory (the segment starts there: m0 = that memory). *)
Definition lg_st (pc : Z) (P : (word -> option byte) -> bvmap 5 word -> bv 32 -> machine_state -> Prop)
    (c : config) : Prop :=
  exists (fx' : FPState) regs mem md L A,
    c = mkCfg (@mkst fx' regs (Z_to_bv 64 pc) mem (seg_rom rsegs)) md /\
    frm_zero (@fp_csr fx') /\
    sr_fr B API stk SS L0 A0 mem0 md0 L A mem md /\ res_ok_slots A b0 /\
    P (normalize rsegs mem) (@fp_regs fx') (@fp_csr fx')
      (MState.MS (Regs6ss.mkR_of regs) (@fp_regs fx') (Z_to_bv 64 pc) (@fp_csr fx') None (normalize rsegs mem)
         (seg_rom rsegs)).

Definition lg_head (ops : Z) (c : fuzz_in) (Bw : list byte) :=
  fun m0 F fc ms => llvm_head data D regs0 m0 SP LO ops c Bw F fc ms.
Definition lg_out :=
  fun m0 F fc ms => llvm_out regs0 m0 SP LO F fc ms.

(* the end of a run that reaches the next head or the exit *)
Definition lg_next (m0 : word -> option byte) (ops : Z) (F : bvmap 5 word) (fc : bv 32) (ms : machine_state)
    : Prop :=
  (exists c2 B2 k2, llvm_head data D regs0 m0 SP LO (ops + 1) c2 B2 F fc ms /\
     INV (Z.to_nat (OPS_MAX - (ops + 1))) c2 B2 k2) \/
  llvm_out regs0 m0 SP LO F fc ms.

(* the end of a run that reaches receive's entry, as llvm_op_recv_stmt states it *)
Definition lg_recv (m0 : word -> option byte) (ops : Z) (c : fuzz_in) (Bw : list byte) (F : bvmap 5 word)
    (fc : bv 32) (ms' : machine_state) : Prop :=
  exists (s0 s2 s3 s4 s5 s6 s7 : word) (p : Z) (bytes : list byte) (by_poll pf : Z) (c2 : fuzz_in),
    llvm_at_recv data D regs0 m0 SP LO ops Bw LH_RET_RECV s0 s2 s3 s4 s5 s6 s7 p bytes by_poll pf F fc ms' /\
    (forall I A k, LLVMFuzzerTestOneInput_op_m I Bw A D c k =
       match receive_m I Bw (A k) bytes by_poll pf with
       | Some (B1, _) => Some (B1, (c2, S k))
       | None => None
       end) /\
    (forall m0' B' F' fc' ms'' (Q' : machine_state -> Prop), g_fail_next B' <= 1 ->
       llvm_ret data D regs0 m0' SP LO ops B' LH_RET_RECV s0 s2 s3 s4 s5 s6 s7 F' fc' ms'' ->
       (forall ms3, llvm_latch data D regs0 m0' SP LO ops c2 B' F' fc' ms3 -> Exec.evt rsegs Q' ms3) ->
       Exec.evt rsegs Q' ms'').

(* the end of a run that reaches build_and_receive's entry, as llvm_op_bar_stmt states it *)
Definition lg_bar (rret : Z) (m0 : word -> option byte) (ops : Z) (c : fuzz_in) (Bw : list byte)
    (F : bvmap 5 word) (fc : bv 32) (ms' : machine_state) : Prop :=
  exists (s0 s2 s3 s4 s5 s6 s7 : word) (dstp srcp bodyp : Z) (dst src body : list byte)
         (send ack retry cmd : Z) (c2 : fuzz_in),
    llvm_at_bar data D regs0 m0 SP LO ops Bw rret s0 s2 s3 s4 s5 s6 s7 dstp srcp bodyp dst src body
      send ack retry cmd F fc ms' /\
    (forall I A k, LLVMFuzzerTestOneInput_op_m I Bw A D c k =
       match build_and_receive_m I Bw (A k) dst src send ack retry cmd body with
       | Some (B1, _) => Some (B1, (c2, S k))
       | None => None
       end) /\
    (forall m0' B' F' fc' ms'' (Q' : machine_state -> Prop), g_fail_next B' <= 1 ->
       llvm_ret data D regs0 m0' SP LO ops B' rret s0 s2 s3 s4 s5 s6 s7 F' fc' ms'' ->
       (forall ms3, llvm_latch data D regs0 m0' SP LO ops c2 B' F' fc' ms3 -> Exec.evt rsegs Q' ms3) ->
       Exec.evt rsegs Q' ms'').

Definition lg_step (m0 : word -> option byte) (ops : Z) (c : fuzz_in) (Bw : list byte) (F : bvmap 5 word)
    (fc : bv 32) (ms : machine_state) : Prop :=
  lg_next m0 ops F fc ms \/ lg_recv m0 ops c Bw F fc ms \/ lg_bar LH_RET_BAR1 m0 ops c Bw F fc ms \/
  lg_bar LH_RET_BAR2 m0 ops c Bw F fc ms.

(* ---- facts of the entry ---- *)

Lemma lg_nums : alloc_ceiling + stk <= SS /\ SS < 2 ^ 63 /\ SS mod 16 = 0 /\ 10176 <= stk /\
  SR_RES_TOP < alloc_ceiling /\ W_BASE_UBSAN + W_LEN <= SR_RES_TOP /\ alloc_ceiling < 2 ^ 63.
Proof.
  pose proof PRE as ((_ & _ & _ & _ & _ & Hal & Hceil & H63 & _) & _).
  pose proof YM05.alloc_ceiling_value as Hac.
  unfold LLVM_K, LLVM_FRAME, build_and_receive_FRAME, receive_FRAME, ALLOC_STACK in HKS.
  unfold SR_RES_TOP, W_BASE_UBSAN, W_LEN. repeat split; lia.
Qed.

Lemma lg_block : D <> [] -> exists q, In (q, Z.of_nat (length D)) (user_blocks A0) /\ ptr_addr L0 q = data.
Proof.
  intros HD. pose proof PRE as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpl & _) & _).
  destruct Hpl as [[Hn _] | [_ H]]; [|exact H].
  exfalso. destruct D; [exact (HD eq_refl) | cbn in Hn; lia].
Qed.

Lemma lg_data_range : D <> [] ->
  4096 <= data /\ data + Z.of_nat (length D) <= alloc_ceiling /\ off_world data (Z.of_nat (length D)).
Proof.
  intros HD. pose proof PRE as ((HM0 & _) & _).
  destruct (lg_block HD) as (q & Hq & Hqp).
  assert (HL : 0 < Z.of_nat (length D)) by (destruct D; [exact (False_ind _ (HD eq_refl)) | cbn; lia]).
  destruct (mr_blocks B (aa_MR API) (aa_laws API) L0 A0 mem0 md0 q _ 0 HM0 Hq ltac:(lia)) as (_ & H1 & H2 & _).
  rewrite Hqp in H1, H2. split; [lia|]. split; [lia|].
  apply (wmem_off_heap B data _ SEGS HL). intros i Hi.
  pose proof (ax_blocks_img AX L0 A0 mem0 md0 q _ i HM0 Hq Hi) as Hn. rewrite Hqp in Hn. exact Hn.
Qed.

(* The input bytes stay in every state the run relation reaches (they are an entry block). *)
Lemma lg_data_bytes : forall L A mem md, sr_fr B API stk SS L0 A0 mem0 md0 L A mem md -> D <> [] ->
  Mem.bytes_at rsegs mem data D.
Proof.
  intros L A mem md FR HD.
  pose proof FR as (_ & _ & _ & _ & _ & _ & _ & _ & Hbyt & _).
  pose proof PRE as (_ & _ & HBD & _).
  destruct (lg_block HD) as (q & Hq & Hqp).
  assert (Hb : In (data, Z.of_nat (length D)) (blocks L0 A0)) by (apply blocks_In; exists q; auto).
  destruct (lg_data_range HD) as (R1 & R2 & _). pose proof lg_nums as (_ & _ & _ & _ & _ & _ & N7).
  apply (lg_blk_bytes B); [exact SEGS | lia | lia |].
  intros i Hi. rewrite (Hbyt data _ i Hb Hi). exact (HBD i Hi).
Qed.

(* ---- the loop's memory on the normalized memory of an SR state ---- *)

Lemma lg_frame_off_img : forall i, 0 <= i < 240 -> ~ in_img B (SP + i).
Proof.
  intros i Hi Himg. pose proof (sr_in_img_top B _ SEGS Himg) as T.
  pose proof lg_nums as (N1 & _ & _ & N4 & N5 & _). unfold LH_FRAME in T. lia.
Qed.

Lemma lg_frame_norm : forall mem cs, ro_agree rsegs mem -> (Cells.cells_size cs <= 240)%nat ->
  Step.rw_cells rsegs mem SP cs -> Step.rw_cells rsegs (normalize rsegs mem) SP cs.
Proof.
  intros mem cs Hro Hsz H. apply (sr_rw_cells_norm B); [exact SEGS | exact Hro | | exact H].
  intros i Hi. apply lg_frame_off_img. lia.
Qed.

Lemma lg_mem_of_sr : forall L A mem md Bw j10 jio j60,
  sr_fr B API stk SS L0 A0 mem0 md0 L A mem md -> D <> [] ->
  relro_img mem -> wmem rsegs mem Bw -> g_fail_next Bw <= 1 ->
  length j10 = 16%nat -> length jio = 32%nat -> length j60 = 40%nat ->
  Step.rw_cells rsegs mem SP (llvm_frame regs0 SP j10 jio j60) ->
  llvm_mem data D regs0 (normalize rsegs mem) SP LO Bw (normalize rsegs mem) j10 jio j60.
Proof.
  intros L A mem md Bw j10 jio j60 FR HD HR HW HG H1 H2 H3 HF.
  pose proof FR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hstw & _ & _ & Hro & _).
  pose proof lg_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
  destruct (lg_data_range HD) as (R1 & R2 & R3).
  unfold llvm_mem.
  split; [lia|]. split; [lia|]. split; [exact R3|].
  split; [exact (bytes_at_normalize rsegs mem data D Hro (lg_data_bytes L A mem md FR HD))|].
  split; [unfold LH_FRAME; Z.div_mod_to_equations; lia|].
  split; [apply (norm_stk B); [exact SEGS | exact Hro | lia | unfold LH_FRAME; lia
                              | intros a Ha; apply Hstw; unfold LH_FRAME in *; lia]|].
  split; [unfold LH_K, LH_FRAME; lia|]. split; [unfold LH_FRAME; lia|]. split; [lia|].
  split; [apply mem_inv_normalize|].
  split; [exact (sr_relro_norm mem Hro HR)|].
  split; [exact (sr_wmem_norm mem Bw Hro HW)|].
  split; [exact HG|].
  split; [apply Frame.munch_refl|]. split; [apply Frame.wmono_refl|].
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  apply lg_frame_norm; [exact Hro | rewrite (llvm_frame_size regs0 SP j10 jio j60 H1 H2 H3); lia | exact HF].
Qed.

(* An evt end memory m0' and the SR memory mem' related by mem_rel: the loop's memory on normalize mem'. *)
Lemma lg_mem_back : forall m0 Bw m j10 jio j60 L A mem' md, D <> [] ->
  llvm_mem data D regs0 m0 SP LO Bw m j10 jio j60 ->
  mem_rel rsegs mem' m -> sr_fr B API stk SS L0 A0 mem0 md0 L A mem' md ->
  llvm_mem data D regs0 (normalize rsegs mem') SP LO Bw (normalize rsegs mem') j10 jio j60.
Proof.
  intros m0 Bw m j10 jio j60 L A mem' md HDn HM REL FR.
  pose proof HM as (HD0 & HDL & HOW & HD & HSP & HSTK & HLO & HSP2 & HWL & HMI & HRO & HWM & HFN & HMU & HWMO &
                    HJ1 & HJ2 & HJ3 & HRW).
  apply (lg_mem_of_sr L A mem' md); [exact FR | exact HDn | exact (sr_relro_back mem' m REL HRO)
    | exact (sr_wmem_back mem' m Bw REL HWM) | exact HFN | exact HJ1 | exact HJ2 | exact HJ3
    | exact (sr_rw_cells_rel mem' m _ _ REL HRW)].
Qed.

(* ---- footprints of the runs ---- *)

Lemma lg_fpx : forall L A x, 0 <= x < 2 ^ 64 -> ~ Frame.outside WFP x ->
  (SS - stk <= x < SS) \/ h_world x \/ exists y k, sr_mine L0 A0 L A y k /\ y <= x < y + k.
Proof.
  intros L A x Hx NO. cbn [Frame.outside] in NO. unfold h_world. unfold LH_FRAME in *.
  destruct (Z_le_dec (SS - stk) x) as [A1|A1]; [destruct (Z_lt_dec x SS) as [A2|A2]|].
  - left. lia.
  - destruct (Z_le_dec W_BASE_UBSAN x); [destruct (Z_lt_dec x (W_BASE_UBSAN + W_LEN))|].
    + right; left. lia.
    + exfalso. apply NO. split; [lia | split; [lia | exact I]].
    + exfalso. apply NO. split; [lia | split; [lia | exact I]].
  - destruct (Z_le_dec W_BASE_UBSAN x); [destruct (Z_lt_dec x (W_BASE_UBSAN + W_LEN))|].
    + right; left. lia.
    + exfalso. apply NO. split; [lia | split; [lia | exact I]].
    + exfalso. apply NO. split; [lia | split; [lia | exact I]].
Qed.

Lemma lg_fp_mem : forall m0 Bw m j10 jio j60, llvm_mem data D regs0 m0 SP LO Bw m j10 jio j60 ->
  Frame.munch WFP m0 m /\ Frame.wmono rsegs m0 m.
Proof.
  intros m0 Bw m j10 jio j60 (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMU & HWMO & _).
  split; [exact HMU | exact HWMO].
Qed.

Lemma lg_fp_step : forall m0 ops c Bw F fc ms, lg_step m0 ops c Bw F fc ms ->
  exists R F' pc' fc' m', ms = MState.MS R F' pc' fc' None m' (seg_rom rsegs) /\
    Frame.munch WFP m0 m' /\ Frame.wmono rsegs m0 m'.
Proof.
  intros m0 ops c Bw F fc ms [[(c2 & B2 & k2 & H & _) | H] | [H | [H | H]]].
  - destruct H as (ra' & t0 & t1 & t2 & s0 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s3 & s6 & t3 & t4 & t5 & t6 &
                   m & j10 & jio & j60 & -> & _ & _ & _ & HM).
    do 5 eexists. split; [reflexivity|]. exact (lg_fp_mem _ _ _ _ _ _ HM).
  - destruct H as (ra' & t0 & t1 & t2 & s0 & s1 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & s5 & s6 &
                   s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & m & jlow & -> & _ & _ & _ & _ & HMU & HWMO & _).
    do 5 eexists. split; [reflexivity|]. split; [exact HMU | exact HWMO].
  - destruct H as (s0 & s2 & s3 & s4 & s5 & s6 & s7 & p & bytes & bp & pf & c2 & H & _).
    destruct H as (t0 & t1 & t2 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m & j10 & jio & j60 & -> & _ & _ & _ & _ &
                   _ & _ & _ & HM).
    do 5 eexists. split; [reflexivity|]. exact (lg_fp_mem _ _ _ _ _ _ HM).
  - destruct H as (s0 & s2 & s3 & s4 & s5 & s6 & s7 & dp & sp' & bp & dst & src & body & sd & ak & rt & cm & c2 & H & _).
    destruct H as (t0 & t1 & t2 & a2 & a3 & t3 & t4 & t5 & t6 & m & j10 & jio & j60 & -> & _ & _ & _ & _ & _ & _ &
                   _ & _ & _ & _ & _ & HM).
    do 5 eexists. split; [reflexivity|]. exact (lg_fp_mem _ _ _ _ _ _ HM).
  - destruct H as (s0 & s2 & s3 & s4 & s5 & s6 & s7 & dp & sp' & bp & dst & src & body & sd & ak & rt & cm & c2 & H & _).
    destruct H as (t0 & t1 & t2 & a2 & a3 & t3 & t4 & t5 & t6 & m & j10 & jio & j60 & -> & _ & _ & _ & _ & _ & _ &
                   _ & _ & _ & _ & _ & HM).
    do 5 eexists. split; [reflexivity|]. exact (lg_fp_mem _ _ _ _ _ _ HM).
Qed.

(* X_run's footprint premise, for a run that ends in lg_step (or lg_next, its first disjunct). *)
Lemma lg_fp_run : forall mem L A ops c Bw F fc ms, lg_step (normalize rsegs mem) ops c Bw F fc ms ->
  exists R F' pc' fc' m' W, ms = MState.MS R F' pc' fc' None m' (seg_rom rsegs) /\
    Frame.munch W (normalize rsegs mem) m' /\ Frame.wmono rsegs (normalize rsegs mem) m' /\
    (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x ->
       (SS - stk <= x < SS) \/ h_world x \/ exists y k, sr_mine L0 A0 L A y k /\ y <= x < y + k).
Proof.
  intros mem L A ops c Bw F fc ms H.
  destruct (lg_fp_step _ _ _ _ _ _ _ H) as (R & F' & pc' & fc' & m' & -> & MU & WMO).
  exists R, F', pc', fc', m', WFP. split; [reflexivity|]. split; [exact MU|]. split; [exact WMO|].
  exact (lg_fpx L A).
Qed.

(* ---- continuing after a run that reached the next head or the exit ---- *)

Lemma lg_head_cont : forall ops c2 B2 R F0 fc0 F pc fc m0' m0 regs' mem' md L A,
  llvm_head data D regs0 m0 SP LO ops c2 B2 F0 fc0 (MState.MS R F pc fc None m0' (seg_rom rsegs)) ->
  Regs6ss.xregs_eqv R regs' -> mem_rel rsegs mem' m0' ->
  sr_fr B API stk SS L0 A0 mem0 md0 L A mem' md -> res_ok_slots A b0 -> frm_zero fc0 ->
  lg_st LH_HEAD (lg_head ops c2 B2) (mkCfg (@mkst (mkFP F fc) regs' pc mem' (seg_rom rsegs)) md).
Proof.
  intros ops c2 B2 R F0 fc0 F pc fc m0' m0 regs' mem' md L A H HX REL FR RES FZ.
  destruct H as (ra' & t0 & t1 & t2 & s0 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s3 & s6 & t3 & t4 & t5 & t6 &
                 m & j10 & jio & j60 & EQ & HOPS & HN & HC & HM).
  injection EQ as ER EF EP EC EM. subst R F pc fc m0'.
  assert (HDn : D <> []) by (intros E; rewrite E in HC; unfold llvm_cursor in HC; cbn [length] in HC; lia).
  exists (mkFP F0 fc0), regs', mem', md, L, A.
  split; [reflexivity|]. split; [exact FZ|]. split; [exact FR|]. split; [exact RES|].
  unfold lg_head, llvm_head. cbn [fp_regs fp_csr].
  rewrite (lg_mkR_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs' HX).
  do 23 eexists. split; [reflexivity|].
  split; [exact HOPS|]. split; [exact HN|]. split; [exact HC|].
  exact (lg_mem_back m0 B2 m j10 jio j60 L A mem' md HDn HM REL FR).
Qed.

Lemma lg_out_cont : forall R F0 fc0 F pc fc m0' m0 regs' mem' md L A,
  llvm_out regs0 m0 SP LO F0 fc0 (MState.MS R F pc fc None m0' (seg_rom rsegs)) ->
  Regs6ss.xregs_eqv R regs' -> mem_rel rsegs mem' m0' ->
  sr_fr B API stk SS L0 A0 mem0 md0 L A mem' md -> res_ok_slots A b0 -> frm_zero fc0 ->
  lg_st LH_OUT lg_out (mkCfg (@mkst (mkFP F fc) regs' pc mem' (seg_rom rsegs)) md).
Proof.
  intros R F0 fc0 F pc fc m0' m0 regs' mem' md L A H HX REL FR RES FZ.
  destruct H as (ra' & t0 & t1 & t2 & s0 & s1 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & s5 & s6 &
                 s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & m & jlow & EQ & HSP & HLO & HSP2 & HMI & HMU &
                 HWMO & HJ & HRW).
  injection EQ as ER EF EP EC EM. subst R F pc fc m0'.
  exists (mkFP F0 fc0), regs', mem', md, L, A.
  split; [reflexivity|]. split; [exact FZ|]. split; [exact FR|]. split; [exact RES|].
  pose proof FR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hro & _).
  unfold lg_out, llvm_out. cbn [fp_regs fp_csr].
  rewrite (lg_mkR_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs' HX).
  do 30 eexists. split; [reflexivity|].
  split; [exact HSP|]. split; [exact HLO|]. split; [exact HSP2|].
  split; [apply mem_inv_normalize|]. split; [apply Frame.munch_refl|]. split; [apply Frame.wmono_refl|].
  split; [exact HJ|].
  apply lg_frame_norm; [exact Hro | cbn [Cells.cells_size Cells.csize llvm_saved]; lia |].
  exact (sr_rw_cells_rel mem' m _ _ REL HRW).
Qed.

Lemma lg_next_cont : forall ops R F0 fc0 F pc fc m0' m0 regs' mem' md L A (P : config -> Prop),
  lg_next m0 ops F0 fc0 (MState.MS R F pc fc None m0' (seg_rom rsegs)) ->
  Regs6ss.xregs_eqv R regs' -> mem_rel rsegs mem' m0' ->
  sr_fr B API stk SS L0 A0 mem0 md0 L A mem' md -> res_ok_slots A b0 -> frm_zero fc0 ->
  (forall cfg' c2 B2 k2, lg_st LH_HEAD (lg_head (ops + 1) c2 B2) cfg' ->
     INV (Z.to_nat (OPS_MAX - (ops + 1))) c2 B2 k2 -> X cfg' P) ->
  (forall cfg', lg_st LH_OUT lg_out cfg' -> X cfg' P) ->
  X (mkCfg (@mkst (mkFP F fc) regs' pc mem' (seg_rom rsegs)) md) P.
Proof.
  intros ops R F0 fc0 F pc fc m0' m0 regs' mem' md L A P HQ HX REL FR RES FZ KH KO.
  destruct HQ as [(c2 & B2 & k2 & H & HI) | H].
  - exact (KH _ c2 B2 k2 (lg_head_cont _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H HX REL FR RES FZ) HI).
  - exact (KO _ (lg_out_cont _ _ _ _ _ _ _ _ _ _ _ _ _ H HX REL FR RES FZ)).
Qed.

(* ---- the model's step ---- *)

Lemma lg_op_noA : forall I Bw A A' c k, 3 <= snd (fuzz_u8_m D c) mod 9 <= 7 ->
  LLVMFuzzerTestOneInput_op_m I Bw A D c k = LLVMFuzzerTestOneInput_op_m I Bw A' D c k.
Proof.
  intros I Bw A A' c k H. unfold LLVMFuzzerTestOneInput_op_m.
  destruct (fuzz_u8_m D c) as [c1 opb]. cbn [snd] in H.
  destruct (Z.eqb_spec (opb mod 9) 0); [lia|].
  destruct (Z.eqb_spec (opb mod 9) 1); [lia|].
  destruct (Z.eqb_spec (opb mod 9) 2); [lia|].
  destruct (Z.eqb_spec (opb mod 9) 3); [reflexivity|].
  destruct (Z.eqb_spec (opb mod 9) 4); [reflexivity|].
  destruct (Z.eqb_spec (opb mod 9) 5); [reflexivity|].
  destruct (Z.eqb_spec (opb mod 9) 6); [reflexivity|].
  destruct (Z.eqb_spec (opb mod 9) 7); [reflexivity|]. lia.
Qed.

Lemma lg_heap_4096 : lh_heap_ok (fun _ => 4096).
Proof. intros i _. lia. Qed.

Lemma lg_heap_upd : forall A k a, lh_heap_ok A -> 0 < a /\ a + 65536 <= 2 ^ 64 -> lh_heap_ok (aupd A k a).
Proof. intros A k a HA Ha i Hi. unfold aupd. destruct (Nat.eqb i k); [exact Ha | exact (HA i Hi)]. Qed.

Lemma lg_op_some : forall f c Bw k, INV (S f) c Bw k -> fi_n c <> 0 ->
  exists B1 c2 k1, LLVMFuzzerTestOneInput_op_m timg_ubsan Bw (fun _ => 4096) D c k = Some (B1, (c2, k1)).
Proof.
  intros f c Bw k HI HN. destruct (HI _ lg_heap_4096) as (B' & HL).
  cbn [LLVMFuzzerTestOneInput_loop_m] in HL.
  destruct (Z.eqb_spec (fi_n c) 0) as [E|_]; [contradiction|].
  destruct (LLVMFuzzerTestOneInput_op_m timg_ubsan Bw (fun _ => 4096) D c k) as [[B1 [c2 k1]]|]; [|discriminate HL].
  exists B1, c2, k1. reflexivity.
Qed.

Lemma lg_inv_nonrecv : forall f c Bw k B1 c2 k1, INV (S f) c Bw k -> fi_n c <> 0 ->
  3 <= snd (fuzz_u8_m D c) mod 9 <= 7 ->
  LLVMFuzzerTestOneInput_op_m timg_ubsan Bw (fun _ => 4096) D c k = Some (B1, (c2, k1)) ->
  INV f c2 B1 k1.
Proof.
  intros f c Bw k B1 c2 k1 HI HN Hop HOP. unfold INV.
  apply (loop_m_step_at lh_heap_ok f timg_ubsan Bw D c k 4096 B1 c2 k1); [| exact HI | exact HN |].
  - intros A HA. apply lg_heap_upd; [exact HA | lia].
  - intros A _. rewrite (lg_op_noA timg_ubsan Bw (aupd A k 4096) (fun _ => 4096) c k Hop). exact HOP.
Qed.

(* A receiving op: the model's premise of the callee (for every heap frame a), and the step with the frame a the
   callee's malloc returned. *)
Lemma lg_model_call : forall f c Bw k (call : timg -> list byte -> Z -> option (list byte * unit)) c2,
  INV (S f) c Bw k -> fi_n c <> 0 ->
  (forall I A k, LLVMFuzzerTestOneInput_op_m I Bw A D c k =
     match call I Bw (A k) with Some (B1, _) => Some (B1, (c2, S k)) | None => None end) ->
  forall a, 0 < a /\ a + 65536 <= 2 ^ 64 -> call timg_ubsan Bw a <> None.
Proof.
  intros f c Bw k call c2 HI HN LINK a Ha HNone.
  destruct (HI _ (lg_heap_upd (fun _ => 4096) k a lg_heap_4096 Ha)) as (B' & HL).
  cbn [LLVMFuzzerTestOneInput_loop_m] in HL.
  destruct (Z.eqb_spec (fi_n c) 0) as [E|_]; [contradiction|].
  rewrite (LINK timg_ubsan (aupd (fun _ => 4096) k a) k), aupd_at, HNone in HL. discriminate HL.
Qed.

Lemma lg_inv_call : forall f c Bw k (call : timg -> list byte -> Z -> option (list byte * unit)) c2 a Bw',
  INV (S f) c Bw k -> fi_n c <> 0 ->
  (forall I A k, LLVMFuzzerTestOneInput_op_m I Bw A D c k =
     match call I Bw (A k) with Some (B1, _) => Some (B1, (c2, S k)) | None => None end) ->
  0 < a /\ a + 65536 <= 2 ^ 64 -> call timg_ubsan Bw a = Some (Bw', tt) ->
  INV f c2 Bw' (S k).
Proof.
  intros f c Bw k call c2 a Bw' HI HN LINK Ha RM. unfold INV.
  apply (loop_m_step_at lh_heap_ok f timg_ubsan Bw D c k a Bw' c2 (S k)); [| exact HI | exact HN |].
  - intros A HA. exact (lg_heap_upd A k a HA Ha).
  - intros A _. rewrite (LINK timg_ubsan (aupd A k a) k), aupd_at, RM. reflexivity.
Qed.

(* ---- the SR calls ---- *)

Lemma lg_ret_ok_recv : YK0s.ret_ok (Z_to_bv 64 LH_RET_RECV).
Proof. reflexivity. Qed.
Lemma lg_ret_ok_bar1 : YK0s.ret_ok (Z_to_bv 64 LH_RET_BAR1).
Proof. reflexivity. Qed.
Lemma lg_ret_ok_bar2 : YK0s.ret_ok (Z_to_bv 64 LH_RET_BAR2).
Proof. reflexivity. Qed.

(* The return run of a call: the op's return continuation, then the latch. *)
Lemma lg_ret_run : forall f ops c2 Bw' k2 (fx2 : FPState) regs2 rret mem2 md2 L2 A2 (P : config -> Prop)
    (s0 s2 s3 s4 s5 s6 s7 : word) j10 jio j60,
  Z.to_nat (OPS_MAX - ops) = S f -> 0 <= ops < OPS_MAX -> D <> [] ->
  INV f c2 Bw' k2 ->
  sr_fr B API stk SS L0 A0 mem0 md0 L2 A2 mem2 md2 -> res_ok_slots A2 b0 -> frm_zero (@fp_csr fx2) ->
  relro_img mem2 -> wmem rsegs mem2 Bw' -> g_fail_next Bw' <= 1 ->
  length j10 = 16%nat -> length jio = 32%nat -> length j60 = 40%nat ->
  Step.rw_cells rsegs mem2 SP (llvm_frame regs0 SP j10 jio j60) ->
  Regs6ss.mkR_of regs2 =
    Frame.mkR (reg_get regs2 1) (Z_to_bv 64 SP) (reg_get regs0 3) (reg_get regs0 4) (reg_get regs2 5)
      (reg_get regs2 6) (reg_get regs2 7) s0 (Z_to_bv 64 1)
      (reg_get regs2 10) (reg_get regs2 11) (reg_get regs2 12) (reg_get regs2 13) (reg_get regs2 14)
      (reg_get regs2 15) (reg_get regs2 16) (reg_get regs2 17) s2 s3 s4 s5 s6 s7
      (Z_to_bv 64 (W_BASE_UBSAN + OFF_M)) (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_fail_next))
      (Z_to_bv 64 (W_BASE_UBSAN + OFF_g_s)) (Z_to_bv 64 ops)
      (reg_get regs2 28) (reg_get regs2 29) (reg_get regs2 30) (reg_get regs2 31) ->
  (forall m0' B' F' fc' ms'' (Q' : machine_state -> Prop), g_fail_next B' <= 1 ->
     llvm_ret data D regs0 m0' SP LO ops B' rret s0 s2 s3 s4 s5 s6 s7 F' fc' ms'' ->
     (forall ms3, llvm_latch data D regs0 m0' SP LO ops c2 B' F' fc' ms3 -> Exec.evt rsegs Q' ms3) ->
     Exec.evt rsegs Q' ms'') ->
  (forall cfg' c3 B3 k3, lg_st LH_HEAD (lg_head (ops + 1) c3 B3) cfg' ->
     INV (Z.to_nat (OPS_MAX - (ops + 1))) c3 B3 k3 -> X cfg' P) ->
  (forall cfg', lg_st LH_OUT lg_out cfg' -> X cfg' P) ->
  X (mkCfg (@mkst fx2 regs2 (Z_to_bv 64 rret) mem2 (seg_rom rsegs)) md2) P.
Proof.
  intros f ops c2 Bw' k2 fx2 regs2 rret mem2 md2 L2 A2 P s0 s2 s3 s4 s5 s6 s7 j10 jio j60
    HF HOPS HDn HI FR2 RES2 FZ2 RLR2 WM2 GF2 HJ1 HJ2 HJ3 HRW2 EMK RET KH KO.
  pose proof lg_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
  apply (X_run stk SS L0 A0 mem0 md0 fx2 regs2 (Z_to_bv 64 rret) mem2 md2 L2 A2
    (lg_next (normalize rsegs mem2) ops (@fp_regs fx2) (@fp_csr fx2)) P FR2); [lia | lia | | |].
  - rewrite EMK.
    apply (RET (normalize rsegs mem2) Bw' (@fp_regs fx2) (@fp_csr fx2) _ _ GF2).
    + unfold llvm_ret. do 20 eexists. split; [reflexivity|]. split; [exact HOPS|].
      exact (lg_mem_of_sr L2 A2 mem2 md2 Bw' j10 jio j60 FR2 HDn RLR2 WM2 GF2 HJ1 HJ2 HJ3 HRW2).
    + intros ms3 HL3. apply (LATCH data D regs0 _ SP LO ops c2 Bw' _ _ ms3 _ HL3).
      * intros HN2 HO2 ms4 HH4. apply Exec.evt_done. left. exists c2, Bw', k2. split; [exact HH4|].
        replace (Z.to_nat (OPS_MAX - (ops + 1))) with f by lia. exact HI.
      * intros _ ms4 HO4. apply Exec.evt_done. right. exact HO4.
  - intros ms HQ. exact (lg_fp_run mem2 L2 A2 ops c2 Bw' _ _ ms (or_introl HQ)).
  - intros R3 F3 pc3 fc3 m03 HQ3 regs3 mem3 HX3 REL3 FR3.
    exact (lg_next_cont ops R3 (@fp_regs fx2) (@fp_csr fx2) F3 pc3 fc3 m03 (normalize rsegs mem2) regs3 mem3 md2
      L2 A2 P HQ3 HX3 REL3 FR3 RES2 FZ2 KH KO).
Qed.

Lemma lg_recv_call : forall f ops c Bw k L A md F0 fc0 F pc fc R m0' regs' mem' m0 (P : config -> Prop),
  Z.to_nat (OPS_MAX - ops) = S f -> INV (S f) c Bw k -> fi_n c <> 0 -> D <> [] ->
  lg_recv m0 ops c Bw F0 fc0 (MState.MS R F pc fc None m0' (seg_rom rsegs)) ->
  Regs6ss.xregs_eqv R regs' -> mem_rel rsegs mem' m0' ->
  sr_fr B API stk SS L0 A0 mem0 md0 L A mem' md -> res_ok_slots A b0 -> frm_zero fc0 ->
  (forall cfg' c2 B2 k2, lg_st LH_HEAD (lg_head (ops + 1) c2 B2) cfg' ->
     INV (Z.to_nat (OPS_MAX - (ops + 1))) c2 B2 k2 -> X cfg' P) ->
  (forall cfg', lg_st LH_OUT lg_out cfg' -> X cfg' P) ->
  X (mkCfg (@mkst (mkFP F fc) regs' pc mem' (seg_rom rsegs)) md) P.
Proof.
  intros f ops c Bw k L A md F0 fc0 F pc fc R m0' regs' mem' m0 P HF HI HN HDn HQ HX REL FR RES FZ KH KO.
  destruct HQ as (s0 & s2 & s3 & s4 & s5 & s6 & s7 & pp & bytes & bp & pf & c2 & HAT & LINK & RET).
  destruct HAT as (t0 & t1 & t2 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m & j10 & jio & j60 & EQ & HOPS & HP1 & HP2
    & HBY & HLEN & HBP & HPF & HM).
  injection EQ as ER EF EP EC EM. subst R F pc fc m0'.
  pose proof HM as (HD0 & HDL & HOW & HD & HSP & HSTK & HLO & HSP2 & HWL & HMI & HRO & HWM & HFN & HMU & HWMO &
                    HJ1 & HJ2 & HJ3 & HRW).
  pose proof FR as (HM1 & HW1 & HB1 & HID1 & Hmd1 & Hhigh1 & Himg1 & Hub1 & Hbyt1 & Hstw1 & Herr1 & Hgd1 & Hro1 &
                    Hle1 & Hlen1).
  pose proof lg_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
  pose proof PRE as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & Htp0 & _) & _).
  pose proof YM05.alloc_ceiling_value as ACV.
  assert (G1 : getr regs' 1 = Z_to_bv 64 LH_RET_RECV) by (rewrite (sr_getr_eqv _ _ _ HX); reflexivity).
  assert (G2 : getr regs' 2 = Z_to_bv 64 SP) by (rewrite (sr_getr_eqv _ _ _ HX); reflexivity).
  assert (G4 : getr regs' 4 = getr regs0 4) by (rewrite (sr_getr_eqv _ _ _ HX); reflexivity).
  assert (G10 : getr regs' 10 = Z_to_bv 64 pp) by (rewrite (sr_getr_eqv _ _ _ HX); reflexivity).
  assert (G11 : getr regs' 11 = Z_to_bv 64 (Z.of_nat (length bytes))) by (rewrite (sr_getr_eqv _ _ _ HX); reflexivity).
  assert (G12 : getr regs' 12 = Z_to_bv 64 bp) by (rewrite (sr_getr_eqv _ _ _ HX); reflexivity).
  assert (G13 : getr regs' 13 = Z_to_bv 64 pf) by (rewrite (sr_getr_eqv _ _ _ HX); reflexivity).
  assert (SP1 : spZ regs' = SP) by (unfold spZ at 1; rewrite G2; apply MState.unsigned_lit; unfold LH_FRAME; lia).
  unfold receive_FRAME, ALLOC_STACK, LH_K, LH_FRAME in *.
  assert (HPRE : h_pre B API receive_FRAME L A regs' mem' md b0 Bw).
  { split.
    { eapply (g_pre B API); [exact FR | rewrite G1; exact lg_ret_ok_recv
        | rewrite SP1, Zminus_mod, N3; reflexivity | rewrite SP1; lgl
        | rewrite SP1; lgl | lgl | lgl | rewrite SP1; lgl | rewrite G4; exact Htp0]. }
    destruct (mr_model B _ (aa_laws API) _ _ _ _ HM1) as (Hh & Hl & _).
    split; [exact HID1|]. split; [exact Hh|]. split; [exact Hl|]. split; [rewrite SEGS; exact Hro1|].
    split; [exact RES|].
    split; [unfold w_off_stack, receive_FRAME, ALLOC_STACK; rewrite G2, MState.unsigned_lit by lia; lia|].
    split; [exact (sr_wmem_back mem' m Bw REL HWM)|]. split; [exact HFN|].
    exact (sr_relro_back mem' m REL HRO). }
  assert (MODEL : forall a, h_addr_ok a -> receive_m timg_ubsan Bw a bytes bp pf <> None).
  { intros a Ha. exact (lg_model_call f c Bw k (fun I B1 a1 => receive_m I B1 a1 bytes bp pf) c2 HI HN LINK a Ha). }
  assert (HARGS : receive_args B L A regs' mem' Bw pp bytes bp pf).
  { split; [exact G10|]. split; [exact G11|]. split; [exact G12|]. split; [exact HBP|].
    split; [rewrite G13, MState.unsigned_lit by lia; apply Z.mod_small; lia|]. split; [exact HPF|]. split; [exact HLEN|].
    split; [apply (lg_bytes_blk B); [exact SEGS | exact (RoAdapt.bytes_at_back rsegs mem' m _ _ REL HBY)]|].
    split; [|exact MODEL].
    destruct (Nat.eq_dec (length bytes) 0) as [E0|E0]; [left; rewrite E0; reflexivity|].
    right. destruct (lg_data_range HDn) as (R1 & R2 & R3). split.
    - unfold off_world in *. destruct R3 as [R3|R3]; [left | right]; lia.
    - left. destruct (lg_block HDn) as (q & Hq & Hqp). destruct (Hub1 q _ Hq) as [Hq1 Hq2].
      exists q, (Z.of_nat (length D)). split; [exact Hq1|]. rewrite Hq2, Hqp. lia. }
  eapply X_bind.
  { change (Z_to_bv 64 LH_RECV) with (Z_to_bv 64 receive_ENTRY).
    exact (X_recv (mkFP F0 fc0) L A regs' mem' md b0 Bw pp bytes bp pf HPRE FZ HARGS
      (ROOMB L A mem' md (Z.max 1 (Z.of_nat (length bytes))) HM1 ltac:(lia))). }
  intros c2' (a & Bw' & HAOK & ACEIL & OFFI & RM & POSTH).
  destruct POSTH as (fx2 & L2 & A2 & regs2 & mem2 & md2 & -> & FZ2 & CPK2 & INIT2 & HALT2 & LAZY2 & BLK2 & UB2 &
    REG2 & RES2 & ROA2 & GK2 & WM2 & GF2 & RLR2).
  rewrite SEGS in ROA2.
  pose proof CPK2 as (_ & _ & _ & _ & _ & Hrp2 & _ & _ & KEEP2 & _).
  assert (ELOW : forall x, (h_world x \/ a <= x < a + Z.max 1 (Z.of_nat (length bytes)) \/
                   ms_ctx B <= x < ms_ctx B + CTX_SIZE) -> x < alloc_ceiling).
  { intros x [Hw | [Hh | Hc]].
    - destruct (WORLD x Hw) as (Hi & _). pose proof (sr_in_img_top B x SEGS Hi). lia.
    - lia.
    - lia. }
  assert (FR2 : sr_fr B API stk SS L0 A0 mem0 md0 L2 A2 mem2 md2).
  { eapply (sr_fr_call B API); try exact SEGS; try exact AX; try exact WORLD; try exact HGG; try exact ERRNO_LOW;
      try exact RELRO;
      [exact FR | lia | lia | exact CPK2 | rewrite SP1; lgl | rewrite SP1; lgl | | | | | | exact INIT2 | exact ROA2
      | exact GK2 | exact REG2].
    - intros x [Hw | [Hh | Hc]]; [right; right; left; exact Hw | | right; right; right; exact Hc].
      right; left. split; [lia|]. replace x with (a + (x - a)) by lia. apply OFFI. lia.
    - intros x Hx. right. intros HE. pose proof (ELOW x HE). lia.
    - intros x HE Hx. exfalso. pose proof (ELOW x HE). lia.
    - intros q kk Hin. apply UB2. exact (proj1 (Hub1 q kk Hin)).
    - intros a0 kk i Hin Hi. pose proof (sr_fr_blocks B API _ _ _ _ _ _ _ _ _ _ FR a0 kk Hin) as Hin'.
      apply blocks_In in Hin' as (p0 & <- & Hp). exact (KEEP2 p0 kk i Hp (UB2 p0 kk Hp) Hi). }
  assert (GA : forall x, SP <= x < SS -> mbyte (ms_segs B) mem2 x = mbyte (ms_segs B) mem' x /\
                 (writable_at (ms_segs B) mem' x <-> writable_at (ms_segs B) mem2 x)).
  { intros x Hx. eapply (g_above B API) with (stk := stk) (S := SS); try exact ERRNO_LOW; try exact SEGS;
      [exact HM1 | exact CPK2 | | | | | exact ELOW | ].
    all: try (rewrite SP1); lgl. }
  assert (HRW2 : Step.rw_cells rsegs mem2 SP (llvm_frame regs0 SP j10 jio j60)).
  { apply (sr_rw_cells_frame mem'); [exact (sr_rw_cells_rel mem' m _ _ REL HRW)|].
    intros x Hx. rewrite (llvm_frame_size regs0 SP j10 jio j60 HJ1 HJ2 HJ3) in Hx. rewrite <- SEGS.
    destruct (GA x ltac:(lgl)) as [E1 E2]. split; [exact E1 | exact E2]. }
  rewrite G1, SEGS.
  apply (lg_ret_run f ops c2 Bw' (S k) fx2 regs2 LH_RET_RECV mem2 md2 L2 A2 P s0 s2 s3 s4 s5 s6 s7
    j10 jio j60 HF HOPS HDn); [ | exact FR2 | exact RES2 | exact FZ2 | exact RLR2 | exact WM2 | exact GF2
    | exact HJ1 | exact HJ2 | exact HJ3 | exact HRW2 | | exact RET | exact KH | exact KO].
  - exact (lg_inv_call f c Bw k (fun I B1 a1 => receive_m I B1 a1 bytes bp pf) c2 a Bw' HI HN LINK HAOK RM).
  - exact (lg_mkR_cs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs' regs2 HX Hrp2).
Qed.

Lemma lg_bar_call : forall f ops c Bw k rret L A md F0 fc0 F pc fc R m0' regs' mem' m0 (P : config -> Prop),
  rret = LH_RET_BAR1 \/ rret = LH_RET_BAR2 ->
  Z.to_nat (OPS_MAX - ops) = S f -> INV (S f) c Bw k -> fi_n c <> 0 -> D <> [] ->
  lg_bar rret m0 ops c Bw F0 fc0 (MState.MS R F pc fc None m0' (seg_rom rsegs)) ->
  Regs6ss.xregs_eqv R regs' -> mem_rel rsegs mem' m0' ->
  sr_fr B API stk SS L0 A0 mem0 md0 L A mem' md -> res_ok_slots A b0 -> frm_zero fc0 ->
  (forall cfg' c2 B2 k2, lg_st LH_HEAD (lg_head (ops + 1) c2 B2) cfg' ->
     INV (Z.to_nat (OPS_MAX - (ops + 1))) c2 B2 k2 -> X cfg' P) ->
  (forall cfg', lg_st LH_OUT lg_out cfg' -> X cfg' P) ->
  X (mkCfg (@mkst (mkFP F fc) regs' pc mem' (seg_rom rsegs)) md) P.
Proof.
  intros f ops c Bw k rret L A md F0 fc0 F pc fc R m0' regs' mem' m0 P HRR HF HI HN HDn HQ HX REL FR RES FZ KH KO.
  destruct HQ as (s0 & s2 & s3 & s4 & s5 & s6 & s7 & dstp & srcp & bodyp & dst & src & body & send & ack & retry & cmd &
    c2 & HAT & LINK & RET).
  destruct HAT as (t0 & t1 & t2 & a2 & a3 & t3 & t4 & t5 & t6 & m & j10 & jio & j60 & EQ & HOPS & HMD & HMS
    & HSD & HSD2 & HAK & HAK2 & HRT & HCM & HBY & HBODY & HM).
  injection EQ as ER EF EP EC EM. subst R F pc fc m0'.
  pose proof HM as (HD0 & HDL & HOW & HD & HSP & HSTK & HLO & HSP2 & HWL & HMI & HRO & HWM & HFN & HMU & HWMO &
                    HJ1 & HJ2 & HJ3 & HRW).
  pose proof FR as (HM1 & HW1 & HB1 & HID1 & Hmd1 & Hhigh1 & Himg1 & Hub1 & Hbyt1 & Hstw1 & Herr1 & Hgd1 & Hro1 &
                    Hle1 & Hlen1).
  pose proof lg_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
  pose proof PRE as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & Htp0 & _) & _).
  pose proof YM05.alloc_ceiling_value as ACV.
  assert (G1 : getr regs' 1 = Z_to_bv 64 rret) by (rewrite (sr_getr_eqv _ _ _ HX); reflexivity).
  assert (G2 : getr regs' 2 = Z_to_bv 64 SP) by (rewrite (sr_getr_eqv _ _ _ HX); reflexivity).
  assert (G4 : getr regs' 4 = getr regs0 4) by (rewrite (sr_getr_eqv _ _ _ HX); reflexivity).
  assert (G10 : getr regs' 10 = Z_to_bv 64 dstp) by (rewrite (sr_getr_eqv _ _ _ HX); reflexivity).
  assert (G11 : getr regs' 11 = Z_to_bv 64 srcp) by (rewrite (sr_getr_eqv _ _ _ HX); reflexivity).
  assert (G12 : getr regs' 12 = a2) by (rewrite (sr_getr_eqv _ _ _ HX); reflexivity).
  assert (G13 : getr regs' 13 = a3) by (rewrite (sr_getr_eqv _ _ _ HX); reflexivity).
  assert (G14 : getr regs' 14 = Z_to_bv 64 retry) by (rewrite (sr_getr_eqv _ _ _ HX); reflexivity).
  assert (G15 : getr regs' 15 = Z_to_bv 64 cmd) by (rewrite (sr_getr_eqv _ _ _ HX); reflexivity).
  assert (G16 : getr regs' 16 = Z_to_bv 64 bodyp) by (rewrite (sr_getr_eqv _ _ _ HX); reflexivity).
  assert (G17 : getr regs' 17 = Z_to_bv 64 (Z.of_nat (length body))) by (rewrite (sr_getr_eqv _ _ _ HX); reflexivity).
  assert (SP1 : spZ regs' = SP) by (unfold spZ at 1; rewrite G2; apply MState.unsigned_lit; unfold LH_FRAME; lia).
  assert (MODEL : forall a, h_addr_ok a -> build_and_receive_m timg_ubsan Bw a dst src send ack retry cmd body <> None).
  { intros a Ha.
    exact (lg_model_call f c Bw k (fun I B1 a1 => build_and_receive_m I B1 a1 dst src send ack retry cmd body) c2
      HI HN LINK a Ha). }
  assert (LB : Z.of_nat (length body) <= 1484).
  { pose proof (MODEL 4096 ltac:(unfold h_addr_ok; lia)) as M4. unfold build_and_receive_m in M4.
    destruct (Z.ltb_spec SPEC_MAX_BODY (Z.of_nat (length body))) as [H|H]; [exfalso; apply M4; reflexivity|].
    unfold SPEC_MAX_BODY in H. lia. }
  destruct HMD as (LD & HMD0 & HMD1 & HMDb & HMDr). destruct HMS as (LS & HMS0 & HMS1 & HMSb & HMSr).
  assert (BLEN : bar_len dst src send ack retry cmd body = Z.max 30 (Z.of_nat (length body)) + 30)
    by (unfold bar_len; apply build_and_receive.bar_frame_len; [exact LD | exact LS]).
  unfold build_and_receive_FRAME, receive_FRAME, ALLOC_STACK, LH_K, LH_FRAME in *.
  assert (HPRE : h_pre B API build_and_receive_FRAME L A regs' mem' md b0 Bw).
  { split.
    { eapply (g_pre B API); [exact FR | rewrite G1; destruct HRR as [-> | ->]; [exact lg_ret_ok_bar1 | exact lg_ret_ok_bar2]
        | rewrite SP1, Zminus_mod, N3; reflexivity | rewrite SP1; lgl
        | rewrite SP1; lgl | lgl | lgl | rewrite SP1; lgl
        | rewrite G4; exact Htp0]. }
    destruct (mr_model B _ (aa_laws API) _ _ _ _ HM1) as (Hh & Hl & _).
    split; [exact HID1|]. split; [exact Hh|]. split; [exact Hl|]. split; [rewrite SEGS; exact Hro1|].
    split; [exact RES|].
    split; [unfold w_off_stack, build_and_receive_FRAME, receive_FRAME, ALLOC_STACK; rewrite G2, MState.unsigned_lit by lia;
            lia|].
    split; [exact (sr_wmem_back mem' m Bw REL HWM)|]. split; [exact HFN|].
    exact (sr_relro_back mem' m REL HRO). }
  assert (HARGS : bar_args B L A regs' mem' Bw dstp srcp bodyp dst src body send ack retry cmd).
  { split; [exact G10|].
    split; [split; [exact LD|]; split; [apply (lg_bytes_blk B); [exact SEGS |
            exact (RoAdapt.bytes_at_back rsegs mem' m _ _ REL HMDb)] | exact HMDr]|].
    split; [exact G11|].
    split; [split; [exact LS|]; split; [apply (lg_bytes_blk B); [exact SEGS |
            exact (RoAdapt.bytes_at_back rsegs mem' m _ _ REL HMSb)] | exact HMSr]|].
    split; [rewrite G12; exact HSD|]. split; [exact HSD2|].
    split; [rewrite G13; exact HAK|]. split; [exact HAK2|].
    split; [exact G14|]. split; [exact HRT|]. split; [exact G15|]. split; [exact HCM|].
    split; [exact G16|]. split; [exact G17|].
    split; [apply (lg_bytes_blk B); [exact SEGS | exact (RoAdapt.bytes_at_back rsegs mem' m _ _ REL HBY)]|].
    split; [|exact MODEL].
    destruct (Nat.eq_dec (length body) 0) as [E0|E0]; [left; rewrite E0; reflexivity|].
    right. destruct HBODY as [(B1 & B2) | (B1 & B2)].
    - destruct (lg_data_range HDn) as (R1 & R2 & R3). split.
      + unfold off_world in *. destruct R3 as [R3|R3]; [left | right]; lia.
      + left. destruct (lg_block HDn) as (q & Hq & Hqp). destruct (Hub1 q _ Hq) as [Hq1 Hq2].
        exists q, (Z.of_nat (length D)). split; [exact Hq1|]. rewrite Hq2, Hqp. lia.
    - split.
      + unfold off_world. right. lia.
      + right. rewrite SP1. lia. }
  eapply X_bind.
  { change (Z_to_bv 64 LH_BAR) with (Z_to_bv 64 build_and_receive_ENTRY).
    exact (X_bar (mkFP F0 fc0) L A regs' mem' md b0 Bw dstp srcp bodyp dst src body send ack retry cmd HPRE FZ HARGS
      (ROOMB L A mem' md (Z.max 1 (bar_len dst src send ack retry cmd body)) HM1 ltac:(rewrite BLEN; lia))). }
  intros c2' (a & Bw' & HAOK & ACEIL & OFFI & RM & POSTH).
  destruct POSTH as (fx2 & L2 & A2 & regs2 & mem2 & md2 & -> & FZ2 & CPK2 & INIT2 & HALT2 & LAZY2 & BLK2 & UB2 &
    REG2 & RES2 & ROA2 & GK2 & WM2 & GF2 & RLR2).
  rewrite SEGS in ROA2.
  pose proof CPK2 as (_ & _ & _ & _ & _ & Hrp2 & _ & _ & KEEP2 & _).
  rewrite BLEN in ACEIL, OFFI.
  assert (ELOW : forall x, (h_world x \/ a <= x < a + Z.max 1 (bar_len dst src send ack retry cmd body) \/
                   ms_ctx B <= x < ms_ctx B + CTX_SIZE) -> x < alloc_ceiling).
  { intros x [Hw | [Hh | Hc]].
    - destruct (WORLD x Hw) as (Hi & _). pose proof (sr_in_img_top B x SEGS Hi). lia.
    - rewrite BLEN in Hh. lia.
    - lia. }
  assert (FR2 : sr_fr B API stk SS L0 A0 mem0 md0 L2 A2 mem2 md2).
  { eapply (sr_fr_call B API); try exact SEGS; try exact AX; try exact WORLD; try exact HGG; try exact ERRNO_LOW;
      try exact RELRO;
      [exact FR | lia | lia | exact CPK2 | rewrite SP1; lgl | rewrite SP1; lgl | | | | | | exact INIT2 | exact ROA2
      | exact GK2 | exact REG2].
    - intros x [Hw | [Hh | Hc]]; [right; right; left; exact Hw | | right; right; right; exact Hc].
      right; left. rewrite BLEN in Hh. split; [lia|]. replace x with (a + (x - a)) by lia. apply OFFI. lia.
    - intros x Hx. right. intros HE. pose proof (ELOW x HE). lia.
    - intros x HE Hx. exfalso. pose proof (ELOW x HE). lia.
    - intros q kk Hin. apply UB2. exact (proj1 (Hub1 q kk Hin)).
    - intros a0 kk i Hin Hi. pose proof (sr_fr_blocks B API _ _ _ _ _ _ _ _ _ _ FR a0 kk Hin) as Hin'.
      apply blocks_In in Hin' as (p0 & <- & Hp). exact (KEEP2 p0 kk i Hp (UB2 p0 kk Hp) Hi). }
  assert (GA : forall x, SP <= x < SS -> mbyte (ms_segs B) mem2 x = mbyte (ms_segs B) mem' x /\
                 (writable_at (ms_segs B) mem' x <-> writable_at (ms_segs B) mem2 x)).
  { intros x Hx. eapply (g_above B API) with (stk := stk) (S := SS); try exact ERRNO_LOW; try exact SEGS;
      [exact HM1 | exact CPK2 | | | | | exact ELOW | ].
    all: try (rewrite SP1); lgl. }
  assert (HRW2 : Step.rw_cells rsegs mem2 SP (llvm_frame regs0 SP j10 jio j60)).
  { apply (sr_rw_cells_frame mem'); [exact (sr_rw_cells_rel mem' m _ _ REL HRW)|].
    intros x Hx. rewrite (llvm_frame_size regs0 SP j10 jio j60 HJ1 HJ2 HJ3) in Hx. rewrite <- SEGS.
    destruct (GA x ltac:(lgl)) as [E1 E2]. split; [exact E1 | exact E2]. }
  rewrite G1, SEGS.
  apply (lg_ret_run f ops c2 Bw' (S k) fx2 regs2 rret mem2 md2 L2 A2 P s0 s2 s3 s4 s5 s6 s7
    j10 jio j60 HF HOPS HDn); [ | exact FR2 | exact RES2 | exact FZ2 | exact RLR2 | exact WM2 | exact GF2
    | exact HJ1 | exact HJ2 | exact HJ3 | exact HRW2 | | exact RET | exact KH | exact KO].
  - exact (lg_inv_call f c Bw k (fun I B1 a1 => build_and_receive_m I B1 a1 dst src send ack retry cmd body) c2 a Bw'
      HI HN LINK HAOK RM).
  - exact (lg_mkR_cs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs' regs2 HX Hrp2).
Qed.

(* ---- one pass of the loop ---- *)

Lemma lg_head_step : forall f ops c Bw k cfg (P : config -> Prop),
  Z.to_nat (OPS_MAX - ops) = S f ->
  lg_st LH_HEAD (lg_head ops c Bw) cfg -> INV (S f) c Bw k ->
  (forall cfg' c2 B2 k2, lg_st LH_HEAD (lg_head (ops + 1) c2 B2) cfg' ->
     INV (Z.to_nat (OPS_MAX - (ops + 1))) c2 B2 k2 -> X cfg' P) ->
  (forall cfg', lg_st LH_OUT lg_out cfg' -> X cfg' P) ->
  X cfg P.
Proof.
  intros f ops c Bw k cfg P HF (fx' & regs & mem & md & L & A & -> & FZ & FR & RES & HH) HI KH KO.
  pose proof lg_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7). unfold lg_head in HH.
  pose proof HH as (ra' & t0 & t1 & t2 & s0 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s3 & s6 & t3 & t4 & t5 & t6 &
                    m & j10 & jio & j60 & _ & HOPS & HN & HC & _).
  assert (HDn : D <> []) by (intros E; rewrite E in HC; unfold llvm_cursor in HC; cbn [length] in HC; lia).
  apply (X_run stk SS L0 A0 mem0 md0 fx' regs (Z_to_bv 64 LH_HEAD) mem md L A
    (lg_step (normalize rsegs mem) ops c Bw (@fp_regs fx') (@fp_csr fx')) P FR); [lia | lia | | |].
  - apply (DISP data D regs0 _ SP LO ops c Bw _ _ _ _ HH). intros ms1 HC1.
    pose proof (Z.mod_pos_bound (snd (fuzz_u8_m D c)) 9 ltac:(lia)) as Hop9.
    destruct (lg_op_some f c Bw k HI HN) as (B1 & c2 & k1 & HOP).
    assert (NREC : forall i, 3 <= i <= 7 -> snd (fuzz_u8_m D c) mod 9 = i ->
              llvm_op_stmt i -> Exec.evt rsegs (lg_step (normalize rsegs mem) ops c Bw (@fp_regs fx') (@fp_csr fx')) ms1).
    { intros i Hi Ei OPi. rewrite Ei in HC1.
      eapply Exec.evt_cut; [exact (OPi data D regs0 _ SP LO ops c _ Bw _ _ _ (fun _ => 4096) k B1 c2 k1 HC1 HOP)|].
      intros ms2 HL2. apply (LATCH data D regs0 _ SP LO ops c2 B1 _ _ ms2 _ HL2).
      - intros HN2 HO2 ms3 HH3. apply Exec.evt_done. left. left. exists c2, B1, k1. split; [exact HH3|].
        replace (Z.to_nat (OPS_MAX - (ops + 1))) with f by lia.
        exact (lg_inv_nonrecv f c Bw k B1 c2 k1 HI HN ltac:(lia) HOP).
      - intros _ ms3 HO3. apply Exec.evt_done. left. right. exact HO3. }
    assert (Hcase : snd (fuzz_u8_m D c) mod 9 = 0 \/ snd (fuzz_u8_m D c) mod 9 = 1 \/
                    snd (fuzz_u8_m D c) mod 9 = 2 \/ snd (fuzz_u8_m D c) mod 9 = 3 \/
                    snd (fuzz_u8_m D c) mod 9 = 4 \/ snd (fuzz_u8_m D c) mod 9 = 5 \/
                    snd (fuzz_u8_m D c) mod 9 = 6 \/ snd (fuzz_u8_m D c) mod 9 = 7 \/
                    snd (fuzz_u8_m D c) mod 9 = 8) by lia.
    destruct Hcase as [E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]].
    + rewrite E in HC1. eapply Exec.evt_mono; [exact (OP0 data D regs0 _ SP LO ops c _ Bw _ _ _ HC1)|].
      intros ms2 H2. right. left. exact H2.
    + rewrite E in HC1. eapply Exec.evt_mono; [exact (OP1 data D regs0 _ SP LO ops c _ Bw _ _ _ HC1)|].
      intros ms2 H2. right. right. left. exact H2.
    + rewrite E in HC1. eapply Exec.evt_mono; [exact (OP2 data D regs0 _ SP LO ops c _ Bw _ _ _ HC1)|].
      intros ms2 H2. right. right. right. exact H2.
    + exact (NREC 3 ltac:(lia) E OP3).
    + exact (NREC 4 ltac:(lia) E OP4).
    + exact (NREC 5 ltac:(lia) E OP5).
    + exact (NREC 6 ltac:(lia) E OP6).
    + exact (NREC 7 ltac:(lia) E OP7).
    + rewrite E in HC1. eapply Exec.evt_mono; [exact (OP8 data D regs0 _ SP LO ops c _ Bw _ _ _ HC1)|].
      intros ms2 H2. right. left. exact H2.
  - intros ms HQ. exact (lg_fp_run mem L A ops c Bw _ _ ms HQ).
  - intros R F pc fc m0' HQ regs' mem' HX REL FR'.
    destruct HQ as [HQ | [HQ | [HQ | HQ]]].
    + exact (lg_next_cont ops R _ _ F pc fc m0' _ regs' mem' md L A P HQ HX REL FR' RES FZ KH KO).
    + exact (lg_recv_call f ops c Bw k L A md _ _ F pc fc R m0' regs' mem' _ P HF HI HN HDn HQ HX REL FR' RES FZ KH KO).
    + exact (lg_bar_call f ops c Bw k LH_RET_BAR1 L A md _ _ F pc fc R m0' regs' mem' _ P (or_introl eq_refl)
        HF HI HN HDn HQ HX REL FR' RES FZ KH KO).
    + exact (lg_bar_call f ops c Bw k LH_RET_BAR2 L A md _ _ F pc fc R m0' regs' mem' _ P (or_intror eq_refl)
        HF HI HN HDn HQ HX REL FR' RES FZ KH KO).
Qed.

Lemma lg_loop : forall f ops c Bw k cfg (P : config -> Prop),
  Z.to_nat (OPS_MAX - ops) = f -> lg_st LH_HEAD (lg_head ops c Bw) cfg -> INV f c Bw k ->
  (forall cfg', lg_st LH_OUT lg_out cfg' -> X cfg' P) -> X cfg P.
Proof.
  induction f as [|f IH]; intros ops c Bw k cfg P HF HH HI KO.
  - exfalso. destruct HH as (fx' & regs & mem & md & L & A & _ & _ & _ & _ & HH). unfold lg_head in HH.
    destruct HH as (ra' & t0 & t1 & t2 & s0 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s3 & s6 & t3 & t4 & t5 & t6 &
                    m & j10 & jio & j60 & _ & HOPS & _). unfold OPS_MAX in *. lia.
  - apply (lg_head_step f ops c Bw k cfg P HF HH HI); [|exact KO].
    intros cfg' c2 B2 k2 HH2 HI2. apply (IH (ops + 1) c2 B2 k2 cfg' P); [lia | exact HH2 | | exact KO].
    replace f with (Z.to_nat (OPS_MAX - (ops + 1))) by lia. exact HI2.
Qed.

(* ---- the end ---- *)

Lemma lg_post : forall L A regs mem md,
  sr_fr B API stk SS L0 A0 mem0 md0 L A mem md -> getr regs 10 = Z_to_bv 64 0 -> regs_preserved regs0 regs ->
  lib_post B API llvm_G stk L0 A0 regs0 mem0 md0 data L A regs mem md /\ sink_none B mem md /\
  (forall i, 0 <= i < Z.of_nat (length D) -> mbyte (ms_segs B) mem (data + i) = mbyte (ms_segs B) mem0 (data + i)) /\
  ro_agree rsegs mem.
Proof.
  intros L A regs mem md (HM & HW & HB & HID & (vm & Hmd) & Hhigh & Himg & Hub & Hbyt & Hstw & Herr & Hgd & MI & Hle &
    Hlen) Ha0 Hrp.
  pose proof PRE as ((HM0 & HW0 & HB0 & HID0 & Hra & Hal & Hceil & H63 & Hstw0 & Htp & Herr0 & Hp & Hn & Hpl & Hrod) &
    _ & _ & Hsn & _).
  pose proof YM05.alloc_ceiling_value as ACV.
  split.
  { split; [exact HM|]. split; [exact HW|]. split; [exact HB|]. split; [exact HID|].
    split; [exact Ha0|]. split; [exact Hrp|]. split; [exists vm; exact Hmd|].
    split.
    { intros q k Hq. destruct (Hub q k Hq) as [Hq1 Hq2]. exists q. split; [exact Hq1 | exact Hq2]. }
    split.
    { intros a Ha Hns. apply Hhigh;
        [exact Ha | intros Hs; apply Hns; left; exact Hs | intros Hs; apply Hns; right; exact Hs | intros Hc; lia]. }
    split.
    { intros a T1 T2 T3 T4 T5. apply Himg; [exact T1 | exact T2 | exact T3 | exact T4 |].
      intros Hw. apply T5. apply (proj2 (frame_G_world a)). exact Hw. }
    split.
    { intros q k i Hq _ Hi. assert (Hb : In (ptr_addr L0 q, k) (blocks L0 A0)) by (apply blocks_In; exists q; auto).
      exact (Hbyt _ k i Hb Hi). }
    intros a [Hs|Hs]; [exact (Hstw a Hs) | exact (Herr a Hs)]. }
  split.
  { assert (Hs1 : sink_none B mem md0).
    { apply (lg_sink_none_kept B mem0 mem md0); [|exact Hsn].
      intros a Ha. destruct (SINK a Ha) as (T1 & T2 & T3 & T4 & T5). exact (proj1 (Himg a T1 T2 T3 T4 T5)). }
    rewrite Hmd. destruct Hs1 as (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
    rewrite lg_fds_vm. exact H3. }
  split; [|exact MI].
  intros i Hi. destruct Hpl as [[E _] | [_ (q & Hq & Hqp)]]; [lia|].
  assert (Hb : In (data, Z.of_nat (length D)) (blocks L0 A0)) by (apply blocks_In; exists q; auto).
  exact (Hbyt data _ i Hb Hi).
Qed.

Lemma lg_exit : forall cfg, lg_st LH_OUT lg_out cfg ->
  X cfg (llvm_walk_post B API j ra stk L0 A0 regs0 mem0 md0 data (Z.of_nat (length D)) b0).
Proof.
  intros cfg (fx' & regs & mem & md & L & A & -> & FZ & FR & RES & HO).
  pose proof lg_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
  unfold lg_out in HO.
  eapply (X_run stk SS L0 A0 mem0 md0 fx' regs (Z_to_bv 64 LH_OUT) mem md L A _ _ FR);
    [lia | lia | exact (EXIT regs0 _ SP LO _ _ _ HO) | |].
  - intros ms (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m & -> & MU & WMO).
    do 5 eexists. exists WFP. split; [reflexivity|]. split; [exact MU|]. split; [exact WMO|]. exact (lg_fpx L A).
  - intros R F pc fc m0' HQ regs' mem' HX REL FR'.
    destruct HQ as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m & EQ & MU & WMO).
    injection EQ as ER EF EP EC EM. subst R F pc fc m0'.
    apply X_ret.
    pose proof PRE as ((_ & _ & _ & _ & Hra0 & _) & _).
    assert (G10 : getr regs' 10 = Z_to_bv 64 0) by (rewrite (sr_getr_eqv _ _ _ HX); reflexivity).
    assert (RP : regs_preserved regs0 regs').
    { intros r Hr. rewrite (sr_getr_eqv _ _ _ HX).
      destruct (lg_callee_cases r Hr) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
        try reflexivity.
      transitivity (Z_to_bv 64 (spZ regs0)).
      - transitivity (Z_to_bv 64 (spZ regs0 - LH_FRAME + LH_FRAME)); [reflexivity | f_equal; lia].
      - unfold spZ. apply MState.Z_to_bv_bv_unsigned. }
    destruct (lg_post L A regs' mem' md FR' G10 RP) as (Hpost & Hsn & Hpay & Hro').
    exists (mkFP (@fp_regs fx') (@fp_csr fx')), L, A, regs', mem', md.
    split.
    { rewrite SEGS. f_equal. f_equal. transitivity (MState.ret_pc (getr regs0 1)); [reflexivity|].
      rewrite Hra0. exact (sr_ret_pc _ HRA). }
    split; [exact FZ|]. split; [exact Hpost|]. split; [exact Hsn|].
    split; [exact RES|]. split; [exact Hpay|]. split; [exact Hro' | exact I].
Qed.

(* ---- the whole walk ---- *)

Theorem lg_gen : X (mkCfg (mkst regs0 (Z_to_bv 64 LLVM_ENTRY) mem0 (seg_rom rsegs)) md0)
  (llvm_walk_post B API j ra stk L0 A0 regs0 mem0 md0 data (Z.of_nat (length D)) b0).
Proof using All.
  pose proof PRE as ((HM0 & HW0 & HB0 & HID0 & Hra0 & Hal0 & Hceil0 & H630 & Hstw0 & Htp0 & Herr0 & Hp0 & Hn0 &
    Hpl0 & Hrod0) & _ & HBD & Hsn0 & Hsp47 & Hres0 & Hro0 & HG0 & HGI0 & Hfz0 & HWM0 & HMO).
  pose proof lg_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
  assert (FR0 : sr_fr B API stk SS L0 A0 mem0 md0 L0 A0 mem0 md0).
  { apply (sr_fr_refl B API); [exact HM0 | exact HW0 | exact HB0 | exact HID0 | exact Hstw0 | exact Herr0 | exact Hro0]. }
  eapply (X_bind _ (fun cfg => lg_st LH_OUT lg_out cfg \/
                     exists c1 B1, lg_st LH_HEAD (lg_head 0 c1 B1) cfg /\ INV (Z.to_nat OPS_MAX) c1 B1 O)).
  2:{ intros cfg [HO | (c1 & B1 & HH & HI)]; [exact (lg_exit cfg HO)|].
      apply (lg_loop (Z.to_nat OPS_MAX) 0 c1 B1 O cfg _); [f_equal; lia | exact HH | exact HI | exact lg_exit]. }
  eapply (X_run stk SS L0 A0 mem0 md0 fx regs0 (Z_to_bv 64 LLVM_ENTRY) mem0 md0 L0 A0 _ _ FR0); [lia | lia | | |].
  - change (Z_to_bv 64 LLVM_ENTRY) with (Z_to_bv 64 LH_ENTRY).
    apply (ENTRY data D regs0 (@fp_regs fx) (@fp_csr fx) (normalize rsegs mem0) LO Bw0);
      try change (bv_unsigned (reg_get regs0 2)) with SS.
    + exact Hp0.
    + exact Hn0.
    + exact Hal0.
    + apply (norm_stk B); [exact SEGS | exact Hro0 | lia | lia | intros a Ha; apply Hstw0; lia].
    + unfold LH_FRAME, LH_K. lia.
    + exact H630.
    + lia.
    + destruct (Nat.eq_dec (length D) 0) as [E0|E0]; [left; apply length_zero_iff_nil; exact E0|].
      assert (HDn : D <> []) by (intros E; rewrite E in E0; exact (E0 eq_refl)).
      right. destruct (lg_data_range HDn) as (R1 & R2 & R3). split; [lia|]. split; [lia|]. split; [exact R3|].
      exact (bytes_at_normalize rsegs mem0 data D Hro0 (lg_data_bytes L0 A0 mem0 md0 FR0 HDn)).
    + apply mem_inv_normalize.
    + exact (sr_relro_norm mem0 Hro0 (lg_relro_of_G B mem0 SEGS HG0)).
    + exact (sr_wmem_norm mem0 Bw0 Hro0 HWM0).
    + exact HMO.
  - intros ms [HO | (c1 & B1 & HH & _)].
    + destruct HO as (ra' & t0 & t1 & t2 & s0 & s1 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & s5 & s6 &
                      s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & m & jlow & -> & _ & _ & _ & _ & MU & WMO & _).
      do 5 eexists. exists WFP. split; [reflexivity|]. split; [exact MU|]. split; [exact WMO|].
      exact (lg_fpx L0 A0).
    + destruct HH as (ra' & t0 & t1 & t2 & s0 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s3 & s6 & t3 & t4 & t5 & t6 &
                      m & j10 & jio & j60 & -> & _ & _ & _ & HM).
      destruct (lg_fp_mem _ _ _ _ _ _ HM) as [MU WMO].
      do 5 eexists. exists WFP. split; [reflexivity|]. split; [exact MU|]. split; [exact WMO|].
      exact (lg_fpx L0 A0).
  - intros R F pc fc m0' HQ regs' mem' HX REL FR'. apply X_ret.
    destruct HQ as [HO | (c1 & B1 & HH & HI)].
    + left. exact (lg_out_cont R _ _ F pc fc m0' _ regs' mem' md0 L0 A0 HO HX REL FR' Hres0 Hfz0).
    + right. exists c1, B1.
      split; [exact (lg_head_cont 0 c1 B1 R _ _ F pc fc m0' _ regs' mem' md0 L0 A0 HH HX REL FR' Hres0 Hfz0) | exact HI].
Qed.

End Gen.

(* ---------------------------------------------------------------- the two forms *)

Section Inst.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis SINK : forall a, lg_sink_addr a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4) /\ ~ h_world a.
Hypothesis ENTRY : llvm_entry_stmt.
Hypothesis DISP : llvm_disp_stmt.
Hypothesis LATCH : llvm_latch_stmt.
Hypothesis EXIT : llvm_exit_stmt.
Hypothesis OP0 : llvm_op_recv_stmt 0.
Hypothesis OP8 : llvm_op_recv_stmt 8.
Hypothesis OP1 : llvm_op_bar_stmt 1 LH_RET_BAR1.
Hypothesis OP2 : llvm_op_bar_stmt 2 LH_RET_BAR2.
Hypothesis OP3 : llvm_op_stmt 3.
Hypothesis OP4 : llvm_op_stmt 4.
Hypothesis OP5 : llvm_op_stmt 5.
Hypothesis OP6 : llvm_op_stmt 6.
Hypothesis OP7 : llvm_op_stmt 7.

Theorem llvm_walk_sr :
  (forall fx' : FPState, @receive_contract fx' rc B API) ->
  (forall fx' : FPState, @build_and_receive_contract fx' rc B API) ->
  LLVMFuzzerTestOneInput_walk_contract (fx:=fx) (rc:=rc) (SH:=SH) (SK:=SK) B API.
Proof.
  intros RECV BAR HB j Hj ra empty stk Hk Hra L A regs mem md p n pl b Bw PRE ROOM.
  pose proof HB as (SEGS & _ & _ & HGG & _ & AX & ERRNO_LOW & CTX_LOW & WORLD & RELRO).
  pose proof PRE as (_ & Hn & _). subst n.
  rewrite SEGS.
  refine (lg_gen B API SEGS AX HGG ERRNO_LOW WORLD RELRO CTX_LOW SINK (SR rsegs) (fun _ b n => room_slots b n)
    _ _ _ _ _ ENTRY DISP LATCH EXIT OP0 OP8 OP1 OP2 OP3 OP4 OP5 OP6 OP7 j ra empty stk L A regs mem md p pl b Bw
    Hk Hra PRE _).
  - intros c R Q H1 H2. exact (SR_bind rsegs c R Q H1 H2).
  - intros c Q HQ. exact (SR_ret rsegs c Q HQ).
  - intros. eapply (g_run B API); try exact SEGS; try exact AX; try exact HGG; try exact ERRNO_LOW;
      try exact WORLD; try exact RELRO; eassumption.
  - intros fx' L0 A0 regs0 mem0 md0 b0 Bw0 p0 bytes bp pf HP HF HA HR. rewrite <- SEGS.
    exact (RECV fx' HB L0 A0 regs0 mem0 md0 b0 Bw0 p0 bytes bp pf HP HF HA HR).
  - intros fx' L0 A0 regs0 mem0 md0 b0 Bw0 dp sp' bp dst src body sd ak rt cm HP HF HA HR. rewrite <- SEGS.
    exact (BAR fx' HB L0 A0 regs0 mem0 md0 b0 Bw0 dp sp' bp dst src body sd ak rt cm HP HF HA HR).
  - intros L0 A0 mem0 md0 k HM Hk'. destruct ROOM as (R1 & R2 & R3).
    apply room_slots_small; [lia | rewrite R3; unfold CAPMAX; lia | lia | lia].
Qed.

Theorem llvm_walk_cf :
  (forall fx' : FPState, @receive_contract_cf fx' rc B API) ->
  (forall fx' : FPState, @build_and_receive_contract_cf fx' rc B API) ->
  LLVMFuzzerTestOneInput_walk_contract_cf (fx:=fx) (rc:=rc) (SH:=SH) (SK:=SK) B API.
Proof.
  intros RECV BAR HB LIM j Hj ra empty stk Hk Hra L A regs mem md p n pl b Bw PRE ROOM.
  pose proof HB as (SEGS & _ & _ & HGG & _ & AX & ERRNO_LOW & CTX_LOW & WORLD & RELRO).
  pose proof PRE as (_ & Hn & _). subst n.
  rewrite SEGS.
  refine (lg_gen B API SEGS AX HGG ERRNO_LOW WORLD RELRO CTX_LOW SINK (SRcf B) room_cf
    _ _ _ _ _ ENTRY DISP LATCH EXIT OP0 OP8 OP1 OP2 OP3 OP4 OP5 OP6 OP7 j ra empty stk L A regs mem md p pl b Bw
    Hk Hra PRE _).
  - intros c R Q H1 H2. exact (SRcf_bind B c R Q H1 H2).
  - intros c Q HQ T HK. exact (HK c HQ).
  - intros. eapply (g_run_cf B API); try exact SEGS; try exact AX; try exact HGG; try exact ERRNO_LOW;
      try exact WORLD; try exact RELRO; eassumption.
  - intros fx' L0 A0 regs0 mem0 md0 b0 Bw0 p0 bytes bp pf HP HF HA HR. rewrite <- SEGS.
    exact (RECV fx' HB L0 A0 regs0 mem0 md0 b0 Bw0 p0 bytes bp pf HP HF HA HR).
  - intros fx' L0 A0 regs0 mem0 md0 b0 Bw0 dp sp' bp dst src body sd ak rt cm HP HF HA HR. rewrite <- SEGS.
    exact (BAR fx' HB L0 A0 regs0 mem0 md0 b0 Bw0 dp sp' bp dst src body sd ak rt cm HP HF HA HR).
  - intros L0 A0 mem0 md0 k HM Hk'. destruct ROOM as (R1 & R2 & R3 & R4).
    apply room_cf_of_limit; [exact (LIM L0 A0 mem0 md0 HM) | | lia | lia].
    apply room_slots_small; [lia | unfold CAPMAX, CAP_AG in *; lia | lia | lia].
Qed.

End Inst.
