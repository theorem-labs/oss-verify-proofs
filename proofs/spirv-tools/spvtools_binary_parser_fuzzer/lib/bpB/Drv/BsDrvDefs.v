(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BCatExec BCatSim BSeqExec BStoreOk BShapeAlg BNodes BAgentLib BFrame BReach BeapCeil BSpec BSymRun BRefPrintfLib BazyRestrict BazySR.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMem BCells BStep BLFrame BMState BSysStep BExec.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsDriverLaws BsStack0 BXXRep DvB_FuzzStmt BsPrintfFirst BsExitDefs.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require LbB_DStat.
Import BPropExec.
Import ListNotations.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Definition hdr_b (data : list byte) (i : nat) : Z := bv_unsigned (nth i data (Z_to_bv 8 0)).
Definition hdr_cfg (data : list byte) : Z := (hdr_b data 0 + 256 * hdr_b data 1) mod 32768.
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

Definition aro_none (mem : word -> option byte) : Prop := forall i, 0x10000 <= i < 0x91000 -> mem (Z_to_bv 64 i) = None.
Definition arelro_none (mem : word -> option byte) : Prop := forall i, 0x17e000 <= i < 0x186000 -> mem (Z_to_bv 64 i) = None.

Definition aglb_none (mem : word -> option byte) : Prop :=
  (forall i, 0x189a08 <= i < 0x189b00 -> mem (Z_to_bv 64 i) = None)
  /\ (forall i, 0x189be8 <= i < 0x18d980 -> mem (Z_to_bv 64 i) = None).

Definition atid_cell (mem : word -> option byte) (tid : Z) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 0x6c57b0) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) /\ 0 < tid < 2 ^ 22.

Definition acanary (mem : word -> option byte) (can : Z) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 0x6e5898) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 can)) /\ 0 <= can < 2 ^ 64.

Definition aios_cells : list (Z * nat * Z) :=
  [(0x6c3938, 8%nat, 0x182c10); (0x6c3978, 8%nat, 0x189b00); (0x6c3980, 8%nat, 0x6c43b0); (0x6c3988, 8%nat, 0x6c3904); (0x6c3998, 8%nat, 0x182c10); (0x6c39d8, 8%nat, 0x189920); (0x6c39e0, 8%nat, 0x6c43b0); (0x6c39e8, 8%nat, 0x6c390c); (0x6c39f8, 8%nat, 0x182d40); (0x6c3a38, 8%nat, 0x189b00); (0x6c3a40, 8%nat, 0x6c4540); (0x6c3a48, 8%nat, 0x6c391c); (0x6c3a58, 8%nat, 0x182d40); (0x6c3a98, 8%nat, 0x189920); (0x6c3aa0, 8%nat, 0x6c4540); (0x6c3aa8, 8%nat, 0x6c3924); (0x6c3b88, 8%nat, 0x1827b0); (0x6c3b99, 1%nat, 0x10); (0x6c3bb0, 4%nat, 0x0); (0x6c3bb8, 8%nat, 0x6c3938); (0x6c3c18, 8%nat, 0x0); (0x6c3c28, 8%nat, 0x1828d0); (0x6c3c39, 1%nat, 0x10); (0x6c3c50, 4%nat, 0x0); (0x6c3c58, 8%nat, 0x6c39f8); (0x6c3cb8, 8%nat, 0x0); (0x6c3e08, 8%nat, 0x1827b0); (0x6c3e19, 1%nat, 0x10); (0x6c3e30, 4%nat, 0x0); (0x6c3e38, 8%nat, 0x6c3998); (0x6c3e98, 8%nat, 0x0); (0x6c3ea8, 8%nat, 0x1828d0); (0x6c3eb9, 1%nat, 0x10); (0x6c3ed0, 4%nat, 0x0); (0x6c3ed8, 8%nat, 0x6c3a58); (0x6c3f38, 8%nat, 0x0); (0x6c43b0, 8%nat, 0x183288); (0x6c4540, 8%nat, 0x182fd8); (0x6c4550, 8%nat, 0x6a768)]%Z.

Definition adrv_cells : list (Z * nat * Z) :=
  [(0x189920, 4%nat, 0x5);
   (0x189928, 8%nat, 0x0);
   (0x189930, 8%nat, 0x0);
   (0x189940, 8%nat, 0x0);
   (0x189948, 8%nat, 0x0);
   (0x189958, 8%nat, 0x0);
   (0x189968, 8%nat, 0x16cdd0);
   (0x189978, 8%nat, 0x6e6070);
   (0x189980, 8%nat, 0x0);
   (0x189998, 4%nat, 0x2);
   (0x1899a8, 4%nat, 0x0);
   (0x1899ac, 4%nat, 0xffffffff);
   (0x1899b0, 4%nat, 0xffffffff);
   (0x6e5ac8, 4%nat, 0);
   (0x6e5aeb, 1%nat, 0);
   (0x6e58ac, 4%nat, 0);
   (0x6e58b0, 4%nat, 3);
   (0x6e58b8, 8%nat, 0x6e58c0);
   (0x6e58c0, 8%nat, 0);
   (0x6e58c8, 8%nat, 0x165424);
   (0x6e59c8, 8%nat, 0xd7e54);
   (0x18d9d0, 1%nat, 0);
   (0x186f40, 8%nat, 0x186f40);
   (0x6e6060, 8%nat, 0);

   (0x6e58d0, 8%nat, 0x126ca0); (0x6e58d8, 8%nat, 0xae38c); (0x6e59d0, 8%nat, 0x6c38f8); (0x6e59d8, 8%nat, 0);
   (0x6c5828, 8%nat, 0x6e5b20);

   (0x6e58a8, 1%nat, 0); (0x6c3690, 1%nat, 0); (0x6c3694, 1%nat, 0)]%Z
  ++ aios_cells.

Definition ATR_SLOT_CELL : Z := 0x6e58b0.
Definition ATR_INIT_CELL : Z := 0x6c3690.
Definition ATR_AEF_CELL : Z := 0x6c3694.
Definition adrv_cells_base : list (Z * nat * Z) :=
  Eval vm_compute in List.filter (fun c : Z * nat * Z => match c with (a, _, _) =>
                        negb ((a =? ATR_SLOT_CELL) || (a =? ATR_INIT_CELL) || (a =? ATR_AEF_CELL))%bool end) adrv_cells.
Definition atr_new_cells (b : Z) : list (Z * nat * Z) :=
  [(0x6e58b0, 4%nat, 4); (0x6e58e0, 8%nat, 0x165424); (0x6e59e0, 8%nat, 0xe881c); (0x6c3690, 1%nat, 1); (0x6c3694, 1%nat, b)]%Z.
Definition adrv_cellsT_of (b : Z) : list (Z * nat * Z) := adrv_cells_base ++ atr_new_cells b.
Definition adrv_cells_T : list (Z * nat * Z) := Eval vm_compute in adrv_cellsT_of 0.
Lemma adrv_cells_T_eq : adrv_cells_T = adrv_cellsT_of 0. Proof. vm_compute. reflexivity. Qed.

Definition astdout0 : list (Z * nat * Z) :=
  [(0x189b00, 4%nat, 0x5); (0x189b08, 8%nat, 0x0); (0x189b10, 8%nat, 0x0); (0x189b20, 8%nat, 0x0); (0x189b28, 8%nat, 0x0);
   (0x189b38, 8%nat, 0x0); (0x189b48, 8%nat, 0x16dfd4); (0x189b58, 8%nat, 0x6e6480); (0x189b60, 8%nat, 0x400);
   (0x189b78, 4%nat, 0x1); (0x189b88, 4%nat, 0x0); (0x189b8c, 4%nat, 0xffffffff); (0x189b90, 4%nat, 0xa)]%Z.

Record astdout_after (mem : word -> option byte) (k : nat) : Prop := ASOA {
  so_flags : rdn RSEGS mem (Z_to_bv 64 0x189b00) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5));
  so_rpos  : rdn RSEGS mem (Z_to_bv 64 0x189b08) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  so_rend  : rdn RSEGS mem (Z_to_bv 64 0x189b10) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  so_wend  : rdn RSEGS mem (Z_to_bv 64 0x189b20) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x6e6880));
  so_wpos  : rdn RSEGS mem (Z_to_bv 64 0x189b28) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (0x6e6480 + 2 * Z.of_nat k)));
  so_wbase : rdn RSEGS mem (Z_to_bv 64 0x189b38) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x6e6480));
  so_write : rdn RSEGS mem (Z_to_bv 64 0x189b48) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x16cdd0));
  so_buf   : rdn RSEGS mem (Z_to_bv 64 0x189b58) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x6e6480));
  so_bsz   : rdn RSEGS mem (Z_to_bv 64 0x189b60) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1024));
  so_fd    : rdn RSEGS mem (Z_to_bv 64 0x189b78) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1));
  so_mode  : rdn RSEGS mem (Z_to_bv 64 0x189b88) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
  so_lock  : rdn RSEGS mem (Z_to_bv 64 0x189b8c) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
  so_lbf   : rdn RSEGS mem (Z_to_bv 64 0x189b90) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
  so_bytes : rdn RSEGS mem (Z_to_bv 64 0x6e6480) (2 * k) = Some (zero_lines k) }.

Definition ATR_STACK : Z := 69632.

Definition adstat_win (x : Z) : Prop := (0x6c40d8 <= x < 0x6c47bb) \/ (0x6c5828 <= x < 0x6c5830).

Definition adstat_runs_in2 (rs : list (Z * list Z)) : bool :=
  forallb (fun r => ((0x6c40d8 <=? fst r) && (fst r + Z.of_nat (length (snd r)) <=? 0x6c47bb))
                    || ((0x6c5828 <=? fst r) && (fst r + Z.of_nat (length (snd r)) <=? 0x6c5830)))%bool rs.

Lemma adstat_runs_ok : adstat_runs_in2 LbB_DStat.D_DIAG_A = true.
Proof. vm_compute. reflexivity. Qed.

Lemma adstat_runs_win : forall x, LbB_DStat.in_drun LbB_DStat.D_DIAG_A x -> adstat_win x.
Proof.
  intros x Hx. unfold LbB_DStat.in_drun in Hx.
  destruct (LbB_DStat.dlookup LbB_DStat.D_DIAG_A x) as [b|] eqn:E; [|congruence].
  destruct (LbB_DStat.dlookup_range _ _ _ E) as (a & bs & HIn & HR).
  pose proof adstat_runs_ok as K. unfold adstat_runs_in2 in K. rewrite forallb_forall in K.
  specialize (K (a, bs) HIn). cbn [fst snd] in K. unfold adstat_win.
  destruct (Z.leb_spec 0x6c40d8 a), (Z.leb_spec (a + Z.of_nat (length bs)) 0x6c47bb),
           (Z.leb_spec 0x6c5828 a), (Z.leb_spec (a + Z.of_nat (length bs)) 0x6c5830); cbn in K; try discriminate; lia.
Qed.

Lemma adstat_eq : forall m m', LbB_DStat.dstat m -> (forall x, adstat_win x -> m' (wa x) = m (wa x)) -> LbB_DStat.dstat m'.
Proof.
  intros m m' D HE. unfold LbB_DStat.dstat in *. eapply LbB_DStat.dstat_rs_pteq; [exact D|].
  intros x _ HI. apply HE. apply adstat_runs_win. exact HI.
Qed.

Section TargetRun.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Variable P : fuzz_params.

  Definition adrv_traces : Prop :=
       trace_ok (as_TR H) APC0_MALLOC [0xe8448]
    /\ trace_ok (as_TR H) APC0_MALLOC [0xe849c]
    /\ trace_ok (as_TR H) APC0_FREE [0xe84c0]
    /\ trace_ok (as_TR H) APC0_FREE [0xe85f0]
    /\ trace_ok (as_TR H) APC0_MALLOC [0xe8728]
    /\ trace_ok (as_TR H) APC0_FREE [0xe87bc]
    /\ pf_ok (as_TR H) (fz_pf P) 0xe8790 []
    /\ fz_tr_ok P H.

  Definition atr_cost (data : list byte) : Z :=
    let N := hdr_payload_len data in as_Cm H N + as_Cf H N + Z.of_nat (hdr_calls data) * fz_cost P N.

  Record atr_statics (cs : list (Z * nat * Z)) (sp : word) (mem : word -> option byte) : Prop := ATRS {
    ats_inv   : mem_inv asegs mem;
    ats_ac    : ACONST mem;
    ats_relro : arelro_none mem;
    ats_glb   : aglb_none mem;
    ats_cells : cells_ok mem cs;
    ats_tid   : exists tid, atid_cell mem tid;
    ats_errno : exists e, rw_cells asegs mem AERRNO [C4 e];
    ats_can   : exists can, acanary mem can;
    ats_rfs   : as_RFS H [] mem;
    ats_sh0   : exists shi, stack0 mem (bv_unsigned sp - ATR_STACK) shi /\ 0x800000000000 <= shi;
    ats_dstat : LbB_DStat.dstat mem }.

  Record ATRpre (sp : word) (A cap : Z) (data : list byte) (p : bptr) (s : as_St H) (LB : list block)
                (msF : machine_state) (mo : Model) (regs : bvmap 5 word) (mem : word -> option byte) : Prop := ATRPRE {

    atr_vis  : as_VIS H s msF = mkst regs (Z_to_bv 64 0xe86c4) mem (seg_rom asegs);
    atr_krel : as_AKREL H s (mkCfg msF mo);

    atr_ra  : getr regs 1 = Z_to_bv 64 0xe8568;
    atr_sp  : getr regs 2 = sp;
    atr_tp  : getr regs 4 = Z_to_bv 64 ATP;
    atr_a0  : getr regs 10 = Z_to_bv 64 (A + 2);
    atr_a1  : getr regs 11 = Z_to_bv 64 (hdr_cfg data);
    atr_a2  : getr regs 12 = Z_to_bv 64 (A + 2 + hdr_cfg data + 4);
    atr_a3  : getr regs 13 = Z_to_bv 64 (hdr_payload_len data);

    atr_len6  : 6 + hdr_cfg data <= Z.of_nat (length data);
    atr_lenhi : Z.of_nat (length data) < MAX_INPUT;

    atr_sp16  : bv_unsigned sp mod 16 = 0;
    atr_splo  : aceil + ATR_STACK + 4096 <= bv_unsigned sp;
    atr_sphi  : bv_unsigned sp + 128 <= 0x800000000000;
    atr_stk   : stk_ok RSEGS mem sp ATR_STACK;
    atr_stkcj : stk asegs mem (bv_unsigned sp - ATR_STACK) (bv_unsigned sp);

    atr_rheap : as_RHEAP H s LB mem;
    atr_blk   : In (p, A, cap) LB;
    atr_lb1   : lb_bytes LB <= 2 ^ 27 /\ Z.of_nat (length LB) <= 2;
    atr_al    : atr_cost data <= as_AL H s;
    atr_aux   : exists B, as_rauxv_ok H mem B /\ bv_unsigned sp + 128 <= B < 2 ^ 64;

    atr_cap   : Z.of_nat (length data) <= cap;
    atr_data  : rdn RSEGS mem (Z_to_bv 64 A) (length data) = Some data;
    atr_addr  : addressable mem A cap;
    atr_cb    : exists junk, rw_cells asegs mem A [CB (Z.to_nat cap) junk];

    atr_st    : atr_statics adrv_cells sp mem;
    atr_out   : cells_ok mem astdout0;
    atr_latch : exists ib : byte, rdn RSEGS mem (Z_to_bv 64 0x6c3690) 1 = Some [ib];

    atr_tr    : adrv_traces;
    atr_live  : ADRV_LIVE <= as_LIVE_MAX H /\ ADRV_CNT <= as_LIVE_CNT_MAX H;

    atr_fd1   : fd_lookup (m_fds mo) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1));
    atr_fd2   : fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) }.

  Record ATRpost (fx' : DFP) (sp : word) (A cap : Z) (data : list byte) (p : bptr) (s : as_St H) (LB : list block) (mo : Model)
                 (regs : bvmap 5 word) (mem : word -> option byte)
                 (regs' : bvmap 5 word) (mem' : word -> option byte) (msF' : machine_state) (mo' : Model) (s' : as_St H) : Prop := ATRPOST {
    atq_vis  : as_VIS H s' msF' = @mkst fx' regs' (Z_to_bv 64 0xe8568) mem' (seg_rom asegs);
    atq_krel : as_AKREL H s' (mkCfg msF' mo');
    atq_mpres : as_MPRES H mo mo';
    atq_sp   : getr regs' 2 = sp;
    atq_tp   : getr regs' 4 = Z_to_bv 64 ATP;
    atq_a0   : getr regs' 10 = Z_to_bv 64 0;
    atq_cs   : forall r : reg, In r ([8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv : list reg) -> getr regs' r = getr regs r;

    atq_above : forall a : word, bv_unsigned sp <= bv_unsigned a -> mem' a = mem a;
    atq_stk   : stk_ok RSEGS mem' sp ATR_STACK;
    atq_stkcj : stk asegs mem' (bv_unsigned sp - ATR_STACK) (bv_unsigned sp);

    atq_heap  : exists LB', as_RHEAP H s' LB' mem' /\ Permutation LB' LB;
    atq_al    : as_AL H s' >= as_AL H s - atr_cost data;
    atq_aux   : exists B, as_rauxv_ok H mem' B /\ bv_unsigned sp + 128 <= B < 2 ^ 64;

    atq_data  : rdn RSEGS mem' (Z_to_bv 64 A) (length data) = Some data;
    atq_addr  : addressable mem' A cap;
    atq_cb    : exists junk, rw_cells asegs mem' A [CB (Z.to_nat cap) junk];

    atq_st    : atr_statics adrv_cells_T sp mem';
    atq_out   : astdout_after mem' (Nat.pred (hdr_calls data));

    atq_fs    : m_fs mo' = m_fs mo;
    atq_fd1   : fd_lookup (m_fds mo') (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1));
    atq_fd2   : fd_lookup (m_fds mo') (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) }.

  Definition as_target_run_stmt : Prop :=
    forall (sp : word) (A cap : Z) (data : list byte) (p : bptr) (s : as_St H) (LB : list block)
           (msF : machine_state) (mo : Model) (regs : bvmap 5 word) (mem : word -> option byte) (K : TSet),
      ATRpre sp A cap data p s LB msF mo regs mem ->
      K [] ->
      (forall (fx' : DFP) regs' mem' msF' mo' s', ATRpost fx' sp A cap data p s LB mo regs mem regs' mem' msF' mo' s' ->
         realizes asegs (mkCfg msF' mo') K) ->
      realizes asegs (mkCfg msF mo) (t_emit (W 1 [Z_to_bv 8 48; Z_to_bv 8 10]) K).
End TargetRun.
