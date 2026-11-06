(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HPropExec HCatExec HCatSim HSeqExec HStoreOk HShapeAlg HNodes HAgentLib HFrame SReach HeapCeil HSpec HSymRun HRefPrintfLib LazyRestrict LazySR.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HMem HCells HStep HLFrame HMState HSysStep HExec.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsCXXHeap AsDriverLaws AsStack0 CXXRep DvA_FuzzStmt AsPrintfFirst AsExitDefs.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require LbA_DStat.
Import HPropExec.
Import ListNotations.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Abbreviation RSEGS := Asan.M.loaded_segments.

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
Definition arelro_none (mem : word -> option byte) : Prop := forall i, 0x17c000 <= i < 0x185000 -> mem (Z_to_bv 64 i) = None.

Definition aglb_none (mem : word -> option byte) : Prop :=
  (forall i, 0x188048 <= i < 0x188140 -> mem (Z_to_bv 64 i) = None)
  /\ (forall i, 0x188228 <= i < 0x18c040 -> mem (Z_to_bv 64 i) = None).

Definition atid_cell (mem : word -> option byte) (tid : Z) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 0x6c3e70) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) /\ 0 < tid < 2 ^ 22.

Definition acanary (mem : word -> option byte) (can : Z) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 0x6e3f58) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 can)) /\ 0 <= can < 2 ^ 64.

Definition aios_cells : list (Z * nat * Z) :=
  [(0x6c1ff8, 8%nat, 0x181250); (0x6c2038, 8%nat, 0x188140); (0x6c2040, 8%nat, 0x6c2a70); (0x6c2048, 8%nat, 0x6c1fc4); (0x6c2058, 8%nat, 0x181250); (0x6c2098, 8%nat, 0x187f60); (0x6c20a0, 8%nat, 0x6c2a70); (0x6c20a8, 8%nat, 0x6c1fcc); (0x6c20b8, 8%nat, 0x181380); (0x6c20f8, 8%nat, 0x188140); (0x6c2100, 8%nat, 0x6c2c00); (0x6c2108, 8%nat, 0x6c1fdc); (0x6c2118, 8%nat, 0x181380); (0x6c2158, 8%nat, 0x187f60); (0x6c2160, 8%nat, 0x6c2c00); (0x6c2168, 8%nat, 0x6c1fe4); (0x6c2248, 8%nat, 0x180df0); (0x6c2259, 1%nat, 0x10); (0x6c2270, 4%nat, 0x0); (0x6c2278, 8%nat, 0x6c1ff8); (0x6c22d8, 8%nat, 0x0); (0x6c22e8, 8%nat, 0x180f10); (0x6c22f9, 1%nat, 0x10); (0x6c2310, 4%nat, 0x0); (0x6c2318, 8%nat, 0x6c20b8); (0x6c2378, 8%nat, 0x0); (0x6c24c8, 8%nat, 0x180df0); (0x6c24d9, 1%nat, 0x10); (0x6c24f0, 4%nat, 0x0); (0x6c24f8, 8%nat, 0x6c2058); (0x6c2558, 8%nat, 0x0); (0x6c2568, 8%nat, 0x180f10); (0x6c2579, 1%nat, 0x10); (0x6c2590, 4%nat, 0x0); (0x6c2598, 8%nat, 0x6c2118); (0x6c25f8, 8%nat, 0x0); (0x6c2a70, 8%nat, 0x1818c8); (0x6c2c00, 8%nat, 0x181618); (0x6c2c10, 8%nat, 0x6acc0)]%Z.

Definition adrv_cells : list (Z * nat * Z) :=
  [(0x187f60, 4%nat, 0x5);
   (0x187f68, 8%nat, 0x0);
   (0x187f70, 8%nat, 0x0);
   (0x187f80, 8%nat, 0x0);
   (0x187f88, 8%nat, 0x0);
   (0x187f98, 8%nat, 0x0);
   (0x187fa8, 8%nat, 0x16b42c);
   (0x187fb8, 8%nat, 0x6e4730);
   (0x187fc0, 8%nat, 0x0);
   (0x187fd8, 4%nat, 0x2);
   (0x187fe8, 4%nat, 0x0);
   (0x187fec, 4%nat, 0xffffffff);
   (0x187ff0, 4%nat, 0xffffffff);
   (0x6e4188, 4%nat, 0);
   (0x6e41ab, 1%nat, 0);
   (0x6e3f6c, 4%nat, 0);
   (0x6e3f70, 4%nat, 3);
   (0x6e3f78, 8%nat, 0x6e3f80);
   (0x6e3f80, 8%nat, 0);
   (0x6e3f88, 8%nat, 0x163a80);
   (0x6e4088, 8%nat, 0xd820c);
   (0x18c090, 1%nat, 0);
   (0x185580, 8%nat, 0x185580);
   (0x6e4720, 8%nat, 0);

   (0x6e3f90, 8%nat, 0x1252fc); (0x6e3f98, 8%nat, 0xae744); (0x6e4090, 8%nat, 0x6c1fb8); (0x6e4098, 8%nat, 0);
   (0x6c3ee8, 8%nat, 0x6e41e0);

   (0x6e3f68, 1%nat, 0); (0x6c1d50, 1%nat, 0); (0x6c1d54, 1%nat, 0)]%Z
  ++ aios_cells.

Definition ATR_SLOT_CELL : Z := 0x6e3f70.
Definition ATR_INIT_CELL : Z := 0x6c1d50.
Definition ATR_AEF_CELL : Z := 0x6c1d54.
Definition adrv_cells_base : list (Z * nat * Z) :=
  Eval vm_compute in List.filter (fun c : Z * nat * Z => match c with (a, _, _) =>
                        negb ((a =? ATR_SLOT_CELL) || (a =? ATR_INIT_CELL) || (a =? ATR_AEF_CELL))%bool end) adrv_cells.
Definition atr_new_cells (b : Z) : list (Z * nat * Z) :=
  [(0x6e3f70, 4%nat, 4); (0x6e3fa0, 8%nat, 0x163a80); (0x6e40a0, 8%nat, 0xe8bd4); (0x6c1d50, 1%nat, 1); (0x6c1d54, 1%nat, b)]%Z.
Definition adrv_cellsT_of (b : Z) : list (Z * nat * Z) := adrv_cells_base ++ atr_new_cells b.
Definition adrv_cells_T : list (Z * nat * Z) := Eval vm_compute in adrv_cellsT_of 0.
Lemma adrv_cells_T_eq : adrv_cells_T = adrv_cellsT_of 0. Proof. vm_compute. reflexivity. Qed.

Definition astdout0 : list (Z * nat * Z) :=
  [(0x188140, 4%nat, 0x5); (0x188148, 8%nat, 0x0); (0x188150, 8%nat, 0x0); (0x188160, 8%nat, 0x0); (0x188168, 8%nat, 0x0);
   (0x188178, 8%nat, 0x0); (0x188188, 8%nat, 0x16c630); (0x188198, 8%nat, 0x6e4b40); (0x1881a0, 8%nat, 0x400);
   (0x1881b8, 4%nat, 0x1); (0x1881c8, 4%nat, 0x0); (0x1881cc, 4%nat, 0xffffffff); (0x1881d0, 4%nat, 0xa)]%Z.

Record astdout_after (mem : word -> option byte) (k : nat) : Prop := ASOA {
  so_flags : rdn RSEGS mem (Z_to_bv 64 0x188140) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5));
  so_rpos  : rdn RSEGS mem (Z_to_bv 64 0x188148) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  so_rend  : rdn RSEGS mem (Z_to_bv 64 0x188150) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  so_wend  : rdn RSEGS mem (Z_to_bv 64 0x188160) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x6e4f40));
  so_wpos  : rdn RSEGS mem (Z_to_bv 64 0x188168) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (0x6e4b40 + 2 * Z.of_nat k)));
  so_wbase : rdn RSEGS mem (Z_to_bv 64 0x188178) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x6e4b40));
  so_write : rdn RSEGS mem (Z_to_bv 64 0x188188) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x16b42c));
  so_buf   : rdn RSEGS mem (Z_to_bv 64 0x188198) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x6e4b40));
  so_bsz   : rdn RSEGS mem (Z_to_bv 64 0x1881a0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1024));
  so_fd    : rdn RSEGS mem (Z_to_bv 64 0x1881b8) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1));
  so_mode  : rdn RSEGS mem (Z_to_bv 64 0x1881c8) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
  so_lock  : rdn RSEGS mem (Z_to_bv 64 0x1881cc) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
  so_lbf   : rdn RSEGS mem (Z_to_bv 64 0x1881d0) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
  so_bytes : rdn RSEGS mem (Z_to_bv 64 0x6e4b40) (2 * k) = Some (zero_lines k) }.

Definition ATR_STACK : Z := 69632.

Definition adstat_win (x : Z) : Prop := (0x6c2798 <= x < 0x6c2e7b) \/ (0x6c3ee8 <= x < 0x6c3ef0).

Definition adstat_runs_in2 (rs : list (Z * list Z)) : bool :=
  forallb (fun r => ((0x6c2798 <=? fst r) && (fst r + Z.of_nat (length (snd r)) <=? 0x6c2e7b))
                    || ((0x6c3ee8 <=? fst r) && (fst r + Z.of_nat (length (snd r)) <=? 0x6c3ef0)))%bool rs.

Lemma adstat_runs_ok : adstat_runs_in2 LbA_DStat.D_DIAG_A = true.
Proof. vm_compute. reflexivity. Qed.

Lemma adstat_runs_win : forall x, LbA_DStat.in_drun LbA_DStat.D_DIAG_A x -> adstat_win x.
Proof.
  intros x Hx. unfold LbA_DStat.in_drun in Hx.
  destruct (LbA_DStat.dlookup LbA_DStat.D_DIAG_A x) as [b|] eqn:E; [|congruence].
  destruct (LbA_DStat.dlookup_range _ _ _ E) as (a & bs & HIn & HR).
  pose proof adstat_runs_ok as K. unfold adstat_runs_in2 in K. rewrite forallb_forall in K.
  specialize (K (a, bs) HIn). cbn [fst snd] in K. unfold adstat_win.
  destruct (Z.leb_spec 0x6c2798 a), (Z.leb_spec (a + Z.of_nat (length bs)) 0x6c2e7b),
           (Z.leb_spec 0x6c3ee8 a), (Z.leb_spec (a + Z.of_nat (length bs)) 0x6c3ef0); cbn in K; try discriminate; lia.
Qed.

Lemma adstat_eq : forall m m', LbA_DStat.dstat m -> (forall x, adstat_win x -> m' (wa x) = m (wa x)) -> LbA_DStat.dstat m'.
Proof.
  intros m m' D HE. unfold LbA_DStat.dstat in *. eapply LbA_DStat.dstat_rs_pteq; [exact D|].
  intros x _ HI. apply HE. apply adstat_runs_win. exact HI.
Qed.

Section TargetRun.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Variable P : fuzz_params.

  Definition adrv_traces : Prop :=
       trace_ok (as_TR H) APC0_MALLOC [0xe8800]
    /\ trace_ok (as_TR H) APC0_MALLOC [0xe8854]
    /\ trace_ok (as_TR H) APC0_FREE [0xe8878]
    /\ trace_ok (as_TR H) APC0_FREE [0xe89a8]
    /\ trace_ok (as_TR H) APC0_MALLOC [0xe8ae0]
    /\ trace_ok (as_TR H) APC0_FREE [0xe8b74]
    /\ pf_ok (as_TR H) (fz_pf P) 0xe8b48 []
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
    ats_dstat : LbA_DStat.dstat mem }.

  Record ATRpre (sp : word) (A cap : Z) (data : list byte) (p : bptr) (s : as_St H) (LB : list block)
                (msF : machine_state) (mo : Model) (regs : bvmap 5 word) (mem : word -> option byte) : Prop := ATRPRE {

    atr_vis  : as_VIS H s msF = mkst regs (Z_to_bv 64 0xe8a7c) mem (seg_rom asegs);
    atr_krel : as_AKREL H s (mkCfg msF mo);

    atr_ra  : getr regs 1 = Z_to_bv 64 0xe8920;
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
    atr_latch : exists ib : byte, rdn RSEGS mem (Z_to_bv 64 0x6c1d50) 1 = Some [ib];

    atr_tr    : adrv_traces;
    atr_live  : ADRV_LIVE <= as_LIVE_MAX H /\ ADRV_CNT <= as_LIVE_CNT_MAX H;

    atr_fd1   : fd_lookup (m_fds mo) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1));
    atr_fd2   : fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) }.

  Record ATRpost (fx' : DFP) (sp : word) (A cap : Z) (data : list byte) (p : bptr) (s : as_St H) (LB : list block) (mo : Model)
                 (regs : bvmap 5 word) (mem : word -> option byte)
                 (regs' : bvmap 5 word) (mem' : word -> option byte) (msF' : machine_state) (mo' : Model) (s' : as_St H) : Prop := ATRPOST {
    atq_vis  : as_VIS H s' msF' = @mkst fx' regs' (Z_to_bv 64 0xe8920) mem' (seg_rom asegs);
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
