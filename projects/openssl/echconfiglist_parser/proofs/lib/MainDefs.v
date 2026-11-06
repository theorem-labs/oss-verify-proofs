(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.openssl.echconfiglist_parser.images Require Import Plain.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import Amb
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes AgentLib Frame StreamSim FileSim
  SymRun Hoare Spec SReach LibDiagKn RefLayout RefStartupDefs RefStartupFacts RefStartup RefStdioDefs RefExitBase HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Mem Cells Step Frame MState.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres.   (* [comment removed for export] *)
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prog.
(* [comment removed for export] *)
Import OSSVerify.Proofs.openssl.echconfiglist_parser.lib.PropExec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Abbreviation RSEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition hdr_b (data : list byte) (i : nat) : Z := bv_unsigned (nth i data (Z_to_bv 8 0)).
Definition hdr_cfg (data : list byte) : Z := (hdr_b data 0 + 256 * hdr_b data 1) mod 32768.   (* [comment removed for export] *)
Definition hdr_counting (data : list byte) : bool := (32768 <=? hdr_b data 0 + 256 * hdr_b data 1)%Z.
Definition hdr_calls (data : list byte) : nat :=
  match Z.to_nat (hdr_cfg data) with O => 1%nat | _ => S (Z.to_nat (hdr_b data 2 mod 4)) end.
Definition hdr_payload_len (data : list byte) : Z := Z.of_nat (length data) - 6 - hdr_cfg data.

Lemma hdr_calls_range : forall data, (1 <= hdr_calls data <= 4)%nat.
Proof.
  intros data. unfold hdr_calls. destruct (Z.to_nat (hdr_cfg data)); [lia|].
  pose proof (Z.mod_pos_bound (hdr_b data 2) 4 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ro_none (mem : word -> option byte) : Prop :=
  forall i, 0x10000 <= i < 0x27e000 -> mem (Z_to_bv 64 i) = None.

(* [comment removed for export] *)
Definition relro_none (mem : word -> option byte) : Prop :=
  forall i, 0x27e000 <= i < 0x2db160 -> (i < 0x2db120 \/ 0x2db128 <= i) -> mem (Z_to_bv 64 i) = None.

(* [comment removed for export] *)
Definition lib_none (mem : word -> option byte) : Prop :=
  forall i, rin_ivs LIBX0 i -> mem (Z_to_bv 64 i) = None.

(* [comment removed for export] *)
Definition prist_rng (i : Z) : Prop :=
  (0x27e000 <= i < 0x2db160 /\ (i < 0x2db120 \/ 0x2db128 <= i)) \/ rin_ivs LIBX0 i.
Definition prist_none (mem : word -> option byte) : Prop :=
  forall i, prist_rng i -> mem (Z_to_bv 64 i) = None.
Lemma prist_relro : forall mem, prist_none mem -> relro_none mem.
Proof. intros mem H i Hi Hj. apply H. left. split; assumption. Qed.
Lemma prist_lib : forall mem, prist_none mem -> lib_none mem.
Proof. intros mem H i Hi. apply H. right. exact Hi. Qed.
(* [comment removed for export] *)
Ltac prist_lit H := unfold prist_rng, LIBX0 in H; cbn [rin_ivs fst snd] in H.
Lemma prist_rng_bounds : forall i, prist_rng i -> 0x27e000 <= i < 0x311000.
Proof. intros i Hi. prist_lit Hi. lia. Qed.

(* [comment removed for export] *)
Definition tid_cell (mem : word -> option byte) (tid : Z) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 0x2ef3d0) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) /\ 0 < tid < 2 ^ 22.

(* [comment removed for export] *)
Definition errno_cell (mem : word -> option byte) : Prop :=
  exists e4, rdn RSEGS mem (Z_to_bv 64 0x2ef3d4) 4 = Some e4 /\ length e4 = 4%nat.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition TR_STACK : Z := 65536.

Section TargetRun.
  Context {HCEIL : HeapCeil}.   (* [comment removed for export] *)
  Variable HS : hsr.

  (* [comment removed for export] *)
  Record TRpre (sp : word) (A cap : Z) (data : list byte) (s : PState) (LB : list RMalloc_iface_stmt.block)
                (model : Model) (regs : bvmap 5 word) (mem : word -> option byte) : Prop := TRPRE {
    (* [comment removed for export] *)
    tr_ra  : getr regs 1 = Z_to_bv 64 0xdda4c;
    tr_sp  : getr regs 2 = sp;
    tr_tp  : getr regs 4 = Z_to_bv 64 0x2ef478;
    tr_a0  : getr regs 10 = Z_to_bv 64 (A + 2);                                  (* [comment removed for export] *)
    tr_a1  : getr regs 11 = Z_to_bv 64 (hdr_cfg data);                           (* [comment removed for export] *)
    tr_a2  : getr regs 12 = Z_to_bv 64 (A + 2 + hdr_cfg data + 4);                (* [comment removed for export] *)
    tr_a3  : getr regs 13 = Z_to_bv 64 (hdr_payload_len data);                   (* [comment removed for export] *)
    (* [comment removed for export] *)
    tr_len6  : 6 + hdr_cfg data <= Z.of_nat (length data);
    tr_lenhi : Z.of_nat (length data) < MAX_INPUT;
    (* [comment removed for export] *)
    tr_sp16  : bv_unsigned sp mod 16 = 0;
    tr_splo  : hceil + TR_STACK + 4096 <= bv_unsigned sp;
    tr_sphi  : bv_unsigned sp + 128 <= 0x800000000000;
    tr_stk   : stk_ok RSEGS mem sp TR_STACK;
    tr_stkcj : stk rsegs mem (bv_unsigned sp - TR_STACK) (bv_unsigned sp);
    (* [comment removed for export] *)
    tr_rheap : hs_RHEAP HS s LB mem;
    tr_krel  : hs_KREL HS s model;
    tr_blk   : In (A, cap) (map (fun b => (blk_addr b, blk_size b)) LB);
    tr_lb1   : lb_bytes LB <= 2 ^ 27 /\ Z.of_nat (length LB) <= 2;
    tr_aux   : exists B, hs_rauxv_ok HS mem B /\ bv_unsigned sp + 128 <= B < 2 ^ 64;
    (* [comment removed for export] *)
    tr_cap   : Z.of_nat (length data) <= cap;
    tr_data  : rdn RSEGS mem (Z_to_bv 64 A) (length data) = Some data;
    (* [comment removed for export] *)
    tr_ro    : ro_none mem;
    tr_inv   : mem_inv rsegs mem;
    tr_cells : cells_ok mem diag_cells;        (* [comment removed for export] *)
    tr_pf1   : cells_ok mem pf1_cells;         (* [comment removed for export] *)
    tr_relro : relro_none mem;                 (* [comment removed for export] *)
    tr_lib   : lib_none mem;                   (* [comment removed for export] *)
    tr_tid   : exists tid, tid_cell mem tid;
    tr_errno : errno_cell mem;
    tr_canary : exists can, canary_ok mem can;  (* [comment removed for export] *)
    (* [comment removed for export] *)
    tr_h     : m_halted model = None;
    tr_lazy  : m_vm_lazy model = [];
    tr_fd1   : fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1));
    tr_fd2   : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) }.

  (* [comment removed for export] *)
  Record stdout_after (mem : word -> option byte) (k : nat) : Prop := SOA {
    so_flags : rdn RSEGS mem (Z_to_bv 64 0x2dc7a0) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5));
    so_rpos  : rdn RSEGS mem (Z_to_bv 64 0x2dc7a8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
    so_rend  : rdn RSEGS mem (Z_to_bv 64 0x2dc7b0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
    so_wend  : rdn RSEGS mem (Z_to_bv 64 0x2dc7c0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x310360));
    so_wpos  : rdn RSEGS mem (Z_to_bv 64 0x2dc7c8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (0x30ff60 + 2 * Z.of_nat k)));
    so_wbase : rdn RSEGS mem (Z_to_bv 64 0x2dc7d8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x30ff60));
    so_write : rdn RSEGS mem (Z_to_bv 64 0x2dc7e8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x272e44));
    so_buf   : rdn RSEGS mem (Z_to_bv 64 0x2dc7f8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x30ff60));
    so_bsz   : rdn RSEGS mem (Z_to_bv 64 0x2dc800) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1024));
    so_fd    : rdn RSEGS mem (Z_to_bv 64 0x2dc818) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1));
    so_lock  : rdn RSEGS mem (Z_to_bv 64 0x2dc82c) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
    so_bytes : rdn RSEGS mem (Z_to_bv 64 0x30ff60) (2 * k) = Some (zero_lines k) }.

  (* [comment removed for export] *)
  Definition exit_skip (a : Z) : bool :=
    (((0x2dc7a0 <=? a) && (a <? 0x2dc888)) || (a =? 0x30f4d0) || (a =? 0x30f4d8) || (a =? 0x30f4e0)
     || (a =? 0x2ec900) || (a =? 0x2ec904) || (a =? 0x2ecb38) || (a =? 0x2ecb3c))%Z.
  Definition exit_cells : list (Z * nat * Z) :=
    filter (fun c => match c with (a, _, _) => negb (exit_skip a) end) diag_cells.

  (* [comment removed for export] *)
  Definition atexit_reg_cells : list (Z * nat * Z) :=
    [(0x30f4d8, 8%nat, 0x30f4e0); (0x30f4d0, 4%nat, 1); (0x30f4e0, 8%nat, 0); (0x30f4e8, 8%nat, 0x26f030);
     (0x30f5e8, 8%nat, 0xddd28); (0x2ec904, 1%nat, 0)]%Z.

  (* [comment removed for export] *)
  Record TRpost (sp : word) (A cap : Z) (data : list byte) (LB : list RMalloc_iface_stmt.block) (model : Model)
                 (regs : bvmap 5 word) (mem : word -> option byte)
                 (regs' : bvmap 5 word) (mem' : word -> option byte) (model' : Model) : Prop := TRPOST {
    tq_sp   : getr regs' 2 = sp;
    tq_tp   : getr regs' 4 = Z_to_bv 64 0x2ef478;
    tq_a0   : getr regs' 10 = Z_to_bv 64 0;                                      (* [comment removed for export] *)
    tq_cs   : forall r : reg, In r ([8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv : list reg) -> getr regs' r = getr regs r;
    (* [comment removed for export] *)
    tq_above : forall a : word, bv_unsigned sp <= bv_unsigned a -> mem' a = mem a;
    tq_stk   : stk_ok RSEGS mem' sp TR_STACK;
    tq_stkcj : stk rsegs mem' (bv_unsigned sp - TR_STACK) (bv_unsigned sp);
    (* [comment removed for export] *)
    tq_heap  : exists s' LB', hs_RHEAP HS s' LB' mem' /\ hs_KREL HS s' model'
                 /\ (forall b, In b LB -> In b LB');
    tq_mpres : hs_MPRES HS model model';
    tq_aux   : exists B, hs_rauxv_ok HS mem' B /\ bv_unsigned sp + 128 <= B;
    (* [comment removed for export] *)
    tq_ro    : ro_none mem';
    tq_inv   : mem_inv rsegs mem';
    tq_cells : cells_ok mem' (exit_cells ++ atexit_reg_cells);   (* [comment removed for export] *)
    tq_dgc   : mem' (Z_to_bv 64 0x2ecb3c) = None;                 (* [comment removed for export] *)
    tq_relro : relro_none mem';
    tq_out   : stdout_after mem' (Nat.pred (hdr_calls data));
    tq_canary : exists can, canary_ok mem' can;
    tq_tid   : exists tid, tid_cell mem' tid;
    tq_errno : errno_cell mem';
    (* [comment removed for export] *)
    tq_h     : m_halted model' = None;
    tq_lazy  : m_vm_lazy model' = [];
    tq_fs    : m_fs model' = m_fs model;
    tq_fd1   : fd_lookup (m_fds model') (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1));
    tq_fd2   : fd_lookup (m_fds model') (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) }.

  (* [comment removed for export] *)
  Definition target_run_stmt : Prop :=
    forall (sp : word) (A cap : Z) (data : list byte) (s : PState) (LB : list RMalloc_iface_stmt.block)
           (model : Model) (regs : bvmap 5 word) (mem : word -> option byte) (K : TSet),
      TRpre sp A cap data s LB model regs mem ->
      K [] ->
      (forall regs' mem' model', TRpost sp A cap data LB model regs mem regs' mem' model' ->
         realizes RSEGS (mkCfg (mkst regs' (Z_to_bv 64 0xdda4c) mem' (seg_rom RSEGS)) model') K) ->
      realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0xddbc0) mem (seg_rom RSEGS)) model)
               (t_emit (W 1 [Z_to_bv 8 48; Z_to_bv 8 10]) K).
End TargetRun.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record heap_extra (HS : hsr) : Prop := HEX {
  (* [comment removed for export] *)
  hx_sr    : forall Q c, hs_SR HS Q c -> sreach RSEGS Q c;
  (* [comment removed for export] *)
  hx_mpres : forall mo mo', hs_MPRES HS mo mo' -> m_fs mo' = m_fs mo /\ m_fds mo' = m_fds mo;
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  hx_live : 2 ^ 28 <= hs_LIVE_MAX HS /\ 2850 <= hs_LIVE_CNT_MAX HS /\ 16 <= hs_LIVE_BIG_MAX HS;
  (* [comment removed for export] *)
  hx_krel_vm : forall s mo mo', hs_KREL HS s mo ->
      m_halted mo' = m_halted mo -> m_vm_lazy mo' = m_vm_lazy mo ->
      m_vm_materialized mo' = m_vm_materialized mo -> m_vmmaps mo' = m_vmmaps mo -> hs_KREL HS s mo';
  (* [comment removed for export] *)
  hx_statics : forall s LB m, hs_RHEAP HS s LB m ->
      rdn RSEGS m (Z_to_bv 64 0x30f70b) 1 = Some [Z_to_bv 8 0]
      /\ rdn RSEGS m (Z_to_bv 64 0x2db120) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x30f4b8))
      /\ exists can, canary_ok m can }.

(* [comment removed for export] *)
Lemma big1_le1 : forall n, 0 <= big1 n <= 1.
Proof. intros n. unfold big1. destruct (BIGB <? n); lia. Qed.

Lemma hx_krel_fds : forall HS, heap_extra HS -> forall s mo f, hs_KREL HS s mo -> hs_KREL HS s (with_fds f mo).
Proof. intros HS HX s mo f K. eapply (hx_krel_vm HS HX); [exact K | | | |]; destruct mo; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition model0 (tid brk mbase sp0 : word) (lim : Z) (inp : ProcInput) : Model :=
  with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp0 lim inp).

Section MainStmt.
  Context {HCEIL : HeapCeil}.
  Definition main_realizes_stmt (HS : hsr) : Prop :=
    forall (sp0 tid brk mbase : word) (rnd : EntryDraw) (lim : Z) (inp : ProcInput) (regs : bvmap 5 word)
           (mem : word -> option byte) (ps0 : PState) (B : Z),
      valid_sp sp0 -> entry_stack_fits sp0 (in_argv inp) (in_envp inp) ->
      valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
      0 < bv_unsigned tid < 2 ^ 22 ->
      hceil + 8388608 <= bv_unsigned sp0 ->                      (* [comment removed for export] *)
      @main_entry (amb_of inp) sp0 (in_argv inp) (in_envp inp) rnd tid regs mem ->
      hs_RHEAP HS ps0 [] mem -> hs_KREL HS ps0 (model0 tid brk mbase sp0 lim inp) ->
      hs_rauxv_ok HS mem B -> bv_unsigned sp0 <= B < 2 ^ 64 ->
      target_run_stmt HS ->
      realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0xdd8b8) mem (seg_rom RSEGS)) (model0 tid brk mbase sp0 lim inp))
               (spec (in_argv inp) (in_fs inp)).
End MainStmt.
