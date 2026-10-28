(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes AgentLib Frame SReach HeapCeil Spec SymRun RefPrintfLib
  LazyRestrict LazySR.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Mem Cells Step Frame MState SysStep Exec.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsCXXHeap AsDriverLaws AsStack0 AsAuxv
  ECH_Xpres ECH_Iface AsPrintfFirst.
Import OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.PropExec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

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
Lemma hdr_cfg_range : forall data, 0 <= hdr_cfg data < 32768.
Proof. intros data. unfold hdr_cfg. apply Z.mod_pos_bound. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition aro_none (mem : word -> option byte) : Prop := forall i, 0x10000 <= i < 0x195000 -> mem (Z_to_bv 64 i) = None.
Definition arelro_none (mem : word -> option byte) : Prop := forall i, 0x571000 <= i < 0x5ea000 -> mem (Z_to_bv 64 i) = None.

(* [comment removed for export] *)
Definition aglb_none (mem : word -> option byte) : Prop :=
  (forall i, 0x5edd90 <= i < 0x5ede88 -> mem (Z_to_bv 64 i) = None)
  /\ (forall i, 0x5edf70 <= i < 0x6a7220 /\ ~ (0x5edf88 <= i < 0x5edf90) -> mem (Z_to_bv 64 i) = None).
  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition atid_cell (mem : word -> option byte) (tid : Z) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 0xbe1be8) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) /\ 0 < tid < 2 ^ 22.
(* [comment removed for export] *)
Definition acanary (mem : word -> option byte) (can : Z) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 0xc01cd0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 can)) /\ 0 <= can < 2 ^ 64.

(* [comment removed for export] *)
Definition adrv_cells : list (Z * nat * Z) :=
  [(0x5edca8, 4%nat, 0x5);        (* [comment removed for export] *)
   (0x5edcb0, 8%nat, 0x0);        (* [comment removed for export] *)
   (0x5edcb8, 8%nat, 0x0);        (* [comment removed for export] *)
   (0x5edcc8, 8%nat, 0x0);        (* [comment removed for export] *)
   (0x5edcd0, 8%nat, 0x0);        (* [comment removed for export] *)
   (0x5edce0, 8%nat, 0x0);        (* [comment removed for export] *)
   (0x5edcf0, 8%nat, 0x56407c);   (* [comment removed for export] *)
   (0x5edd00, 8%nat, 0xc02398);   (* [comment removed for export] *)
   (0x5edd08, 8%nat, 0x0);        (* [comment removed for export] *)
   (0x5edd20, 4%nat, 0x2);        (* [comment removed for export] *)
   (0x5edd30, 4%nat, 0x0);        (* [comment removed for export] *)
   (0x5edd34, 4%nat, 0xffffffff); (* [comment removed for export] *)
   (0x5edd38, 4%nat, 0xffffffff); (* [comment removed for export] *)
   (0xc01f00, 4%nat, 0);          (* [comment removed for export] *)
   (0xc01f23, 1%nat, 0);          (* [comment removed for export] *)
   (0xc01ce0, 1%nat, 0);          (* [comment removed for export] *)
   (0xc01ce4, 4%nat, 0);          (* [comment removed for export] *)
   (0xc01cf0, 8%nat, 0xc01cf8);   (* [comment removed for export] *)
   (0xc01cf8, 8%nat, 0);          (* [comment removed for export] *)
   (0xc01d00, 8%nat, 0x55e508);   (* [comment removed for export] *)
   (0xc01e00, 8%nat, 0x1de71c);   (* [comment removed for export] *)
   (0x6a7290, 1%nat, 0);          (* [comment removed for export] *)
   (0x5ea840, 8%nat, 0x5ea840);   (* [comment removed for export] *)
   (0xc02388, 8%nat, 0)           (* [comment removed for export] *)]%Z.
(* [comment removed for export] *)
Definition aatexit_pre_cells : list (Z * nat * Z) :=
  [(0xc01ce8, 4%nat, 1);          (* [comment removed for export] *)
   (0xbdcf50, 1%nat, 0);          (* [comment removed for export] *)
   (0xbdcf54, 1%nat, 0)]%Z.       (* [comment removed for export] *)
(* [comment removed for export] *)
Definition aatexit_reg_cells : list (Z * nat * Z) :=
  [(0xc01ce8, 4%nat, 2);          (* [comment removed for export] *)
   (0xc01d08, 8%nat, 0x55e508);   (* [comment removed for export] *)
   (0xc01e08, 8%nat, 0x1ef154);   (* [comment removed for export] *)
   (0xbdcf54, 1%nat, 0)]%Z.       (* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition astdout0 : list (Z * nat * Z) :=
  [(0x5ede88, 4%nat, 0x5); (0x5ede90, 8%nat, 0x0); (0x5ede98, 8%nat, 0x0); (0x5edea8, 8%nat, 0x0); (0x5edeb0, 8%nat, 0x0);
   (0x5edec0, 8%nat, 0x0); (0x5eded0, 8%nat, 0x5655d4); (0x5edee0, 8%nat, 0xc027a8); (0x5edee8, 8%nat, 0x400);
   (0x5edf00, 4%nat, 0x1); (0x5edf10, 4%nat, 0x0); (0x5edf14, 4%nat, 0xffffffff); (0x5edf18, 4%nat, 0xa)]%Z.

(* [comment removed for export] *)
Record astdout_after (mem : word -> option byte) (k : nat) : Prop := ASOA {
  so_flags : rdn RSEGS mem (Z_to_bv 64 0x5ede88) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5));
  so_rpos  : rdn RSEGS mem (Z_to_bv 64 0x5ede90) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  so_rend  : rdn RSEGS mem (Z_to_bv 64 0x5ede98) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  so_wend  : rdn RSEGS mem (Z_to_bv 64 0x5edea8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xc02ba8));
  so_wpos  : rdn RSEGS mem (Z_to_bv 64 0x5edeb0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (0xc027a8 + 2 * Z.of_nat k)));
  so_wbase : rdn RSEGS mem (Z_to_bv 64 0x5edec0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xc027a8));
  so_write : rdn RSEGS mem (Z_to_bv 64 0x5eded0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x56407c));
  so_buf   : rdn RSEGS mem (Z_to_bv 64 0x5edee0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xc027a8));
  so_bsz   : rdn RSEGS mem (Z_to_bv 64 0x5edee8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1024));
  so_fd    : rdn RSEGS mem (Z_to_bv 64 0x5edf00) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1));
  so_mode  : rdn RSEGS mem (Z_to_bv 64 0x5edf10) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
  so_lock  : rdn RSEGS mem (Z_to_bv 64 0x5edf14) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
  so_lbf   : rdn RSEGS mem (Z_to_bv 64 0x5edf18) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
  so_bytes : rdn RSEGS mem (Z_to_bv 64 0xc027a8) (2 * k) = Some (zero_lines k) }.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ATR_STACK : Z := 65536.

Section TargetRun.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Variable L : alib.

  (* [comment removed for export] *)
  Definition adrv_traces : Prop :=
       trace_ok (as_TR H) APC0_MALLOC [0x1eed74]      (* [comment removed for export] *)
    /\ trace_ok (as_TR H) APC0_MALLOC [0x1eedc8]      (* [comment removed for export] *)
    /\ trace_ok (as_TR H) APC0_FREE [0x1eedec]        (* [comment removed for export] *)
    /\ trace_ok (as_TR H) APC0_FREE [0x1eef20]        (* [comment removed for export] *)
    /\ trace_ok (as_TR H) APC0_MALLOC [0x1ef05c]      (* [comment removed for export] *)
    /\ trace_ok (as_TR H) APC0_FREE [0x1ef0f4]        (* [comment removed for export] *)
    /\ pf_ok (as_TR H) (al_PF L) P_FUZZ_RA []         (* [comment removed for export] *)
    /\ al_tr_ok L H.

  (* [comment removed for export] *)
  Definition atr_cost (data : list byte) : Z :=
    let N := hdr_payload_len data in as_Cm H N + as_Cf H N + Z.of_nat (hdr_calls data) * fuzz_cost H L N.

  (* [comment removed for export] *)
  Record atr_statics (sp : word) (mem : word -> option byte) : Prop := ATRS {
    ats_inv   : mem_inv asegs mem;
    ats_ac    : ACONST mem;
    ats_relro : arelro_none mem;
    ats_glb   : aglb_none mem;                 (* [comment removed for export] *)
    ats_cells : cells_ok mem adrv_cells;
    ats_tid   : exists tid, atid_cell mem tid;
    ats_errno : exists e, rw_cells asegs mem AERRNO [C4 e];
    ats_can   : exists can, acanary mem can;
    ats_rfs   : as_RFS H [] mem;
    ats_sh0   : exists shi, stack0 mem (bv_unsigned sp - ATR_STACK) shi /\ bv_unsigned sp <= shi }.

  (* [comment removed for export] *)
  Record ATRpre (sp : word) (A cap : Z) (data : list byte) (p : bptr) (s : as_St H) (LB : list block)
                (msF : machine_state) (mo : Model) (regs : bvmap 5 word) (mem : word -> option byte) : Prop := ATRPRE {
    (* [comment removed for export] *)
    atr_vis  : as_VIS H s msF = mkst regs (Z_to_bv 64 0x1eeff8) mem (seg_rom asegs);
    atr_krel : as_AKREL H s (mkCfg msF mo);
    (* [comment removed for export] *)
    atr_ra  : getr regs 1 = Z_to_bv 64 0x1eee98;
    atr_sp  : getr regs 2 = sp;
    atr_tp  : getr regs 4 = Z_to_bv 64 ATP;
    atr_a0  : getr regs 10 = Z_to_bv 64 (A + 2);                                  (* [comment removed for export] *)
    atr_a1  : getr regs 11 = Z_to_bv 64 (hdr_cfg data);                           (* [comment removed for export] *)
    atr_a2  : getr regs 12 = Z_to_bv 64 (A + 2 + hdr_cfg data + 4);                (* [comment removed for export] *)
    atr_a3  : getr regs 13 = Z_to_bv 64 (hdr_payload_len data);                   (* [comment removed for export] *)
    (* [comment removed for export] *)
    atr_len6  : 6 + hdr_cfg data <= Z.of_nat (length data);
    atr_lenhi : Z.of_nat (length data) < MAX_INPUT;
    (* [comment removed for export] *)
    atr_sp16  : bv_unsigned sp mod 16 = 0;
    atr_splo  : aceil + ATR_STACK + 4096 <= bv_unsigned sp;
    atr_sphi  : bv_unsigned sp + 128 <= 0x800000000000;
    atr_stk   : stk_ok RSEGS mem sp ATR_STACK;
    atr_stkcj : stk asegs mem (bv_unsigned sp - ATR_STACK) (bv_unsigned sp);
    (* [comment removed for export] *)
    atr_rheap : as_RHEAP H s LB mem;
    atr_blk   : In (p, A, cap) LB;
    atr_lb1   : lb_bytes LB <= 2 ^ 27 /\ Z.of_nat (length LB) <= 2;
    atr_al    : atr_cost data <= as_AL H s;
    atr_aux   : exists B, as_rauxv_ok H mem B /\ bv_unsigned sp + 128 <= B < 2 ^ 64 /\ aauxv_ok mem B;   (* [comment removed for export] *)
    (* [comment removed for export] *)
    atr_cap   : Z.of_nat (length data) <= cap;
    atr_data  : rdn RSEGS mem (Z_to_bv 64 A) (length data) = Some data;
    atr_addr  : addressable mem A cap;
    atr_cb    : exists junk, rw_cells asegs mem A [CB (Z.to_nat cap) junk];   (* [comment removed for export] *)
    (* [comment removed for export] *)
    atr_st    : atr_statics sp mem;
    atr_out   : cells_ok mem astdout0;        (* [comment removed for export] *)
    atr_reg   : cells_ok mem aatexit_pre_cells;   (* [comment removed for export] *)
    atr_lib   : forall i, rin_ivs (al_LIBX0 L) i -> mem (Z_to_bv 64 i) = None;   (* [comment removed for export] *)
    (* [comment removed for export] *)
    atr_tr    : adrv_traces;
    atr_live  : ADRV_LIVE <= as_LIVE_MAX H /\ ADRV_CNT <= as_LIVE_CNT_MAX H;
    (* [comment removed for export] *)
    atr_fd1   : fd_lookup (m_fds mo) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1));
    atr_fd2   : fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2));
    (* [comment removed for export] *)
    atr_musl0 : amusl0 mem }.

  (* [comment removed for export] *)
  Record ATRpost (sp : word) (A cap : Z) (data : list byte) (p : bptr) (s : as_St H) (LB : list block) (mo : Model)
                 (regs : bvmap 5 word) (mem : word -> option byte)
                 (regs' : bvmap 5 word) (mem' : word -> option byte) (msF' : machine_state) (mo' : Model) (s' : as_St H) : Prop := ATRPOST {
    atq_vis  : as_VIS H s' msF' = mkst regs' (Z_to_bv 64 0x1eee98) mem' (seg_rom asegs);
    atq_krel : as_AKREL H s' (mkCfg msF' mo');
    atq_mpres : as_MPRES H mo mo';
    atq_sp   : getr regs' 2 = sp;
    atq_tp   : getr regs' 4 = Z_to_bv 64 ATP;
    atq_a0   : getr regs' 10 = Z_to_bv 64 0;                                      (* [comment removed for export] *)
    atq_cs   : forall r : reg, In r ([8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv : list reg) -> getr regs' r = getr regs r;
    (* [comment removed for export] *)
    atq_above : forall a : word, bv_unsigned sp <= bv_unsigned a -> mem' a = mem a;
    atq_stk   : stk_ok RSEGS mem' sp ATR_STACK;
    atq_stkcj : stk asegs mem' (bv_unsigned sp - ATR_STACK) (bv_unsigned sp);
    (* [comment removed for export] *)
    atq_heap  : exists LB', as_RHEAP H s' LB' mem' /\ (forall b, In b LB -> In b LB');   (* [comment removed for export] *)
    atq_al    : as_AL H s' >= as_AL H s - atr_cost data;
    atq_aux   : exists B, as_rauxv_ok H mem' B /\ bv_unsigned sp + 128 <= B < 2 ^ 64 /\ aauxv_ok mem' B;
    (* [comment removed for export] *)
    atq_data  : rdn RSEGS mem' (Z_to_bv 64 A) (length data) = Some data;
    atq_addr  : addressable mem' A cap;
    atq_cb    : exists junk, rw_cells asegs mem' A [CB (Z.to_nat cap) junk];
    (* [comment removed for export] *)
    atq_st    : atr_statics sp mem';
    atq_out   : astdout_after mem' (Nat.pred (hdr_calls data));
    atq_reg   : cells_ok mem' aatexit_reg_cells;                  (* [comment removed for export] *)
    atq_dgc   : mem' (Z_to_bv 64 ACLEANUP) = None;                 (* [comment removed for export] *)
    (* [comment removed for export] *)
    atq_fs    : m_fs mo' = m_fs mo;
    atq_fd1   : fd_lookup (m_fds mo') (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1));
    atq_fd2   : fd_lookup (m_fds mo') (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) }.

  (* [comment removed for export] *)
  Definition as_target_run_stmt : Prop :=
    forall (sp : word) (A cap : Z) (data : list byte) (p : bptr) (s : as_St H) (LB : list block)
           (msF : machine_state) (mo : Model) (regs : bvmap 5 word) (mem : word -> option byte) (K : TSet),
      ATRpre sp A cap data p s LB msF mo regs mem ->
      K [] ->
      (forall regs' mem' msF' mo' s', ATRpost sp A cap data p s LB mo regs mem regs' mem' msF' mo' s' ->
         realizes asegs (mkCfg msF' mo') K) ->
      realizes asegs (mkCfg msF mo) (t_emit (W 1 [Z_to_bv 8 48; Z_to_bv 8 10]) K).
End TargetRun.
