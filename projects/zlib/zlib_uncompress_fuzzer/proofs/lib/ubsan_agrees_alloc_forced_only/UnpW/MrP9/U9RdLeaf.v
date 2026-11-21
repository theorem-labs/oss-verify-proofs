(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx. (* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import base decidable list.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require PropExec StdModel ShapeAlg ShapeLaws ModelAmb Spec. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW Require U9ReadBase U9ReadStage U9World U9StdioDefs U9TargetPre.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Walk Arr SysStep ITree Nodes.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KInv. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KLink. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec Require Import KEv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MM15. Import MM15. Import MM15.ProgDeps. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MM13. Import MM13. Import MM13.MallocBlocks. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MM12. Import MM12. Import MM12.Malloc_iface. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MM02. Import MM02. Import MM02.Malloc_ifaceP.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainU9 Require Import PImg RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Mr Require Import MrRulesU9.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.MrP9 Require Import U9HeapPre U9HBase U9HConv U9TrTail U9SoOk U9RdLib U9RdInv U9RdRules U9RdLoop U9RdEnd U9LfBase U9LfOom U9LfRefused.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Module OSp := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec.
Module OW := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U9World.
Module ORB := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U9ReadBase.

Section LEAF.
Context {RCa1 : RunCtx}.  (* a worker (A1) tool *)
Context {rc : runConstT}.
Variable sp0 : word.
Hypothesis Hvsp : valid_sp sp0.
Hypothesis HATOP : ATOP = bv_unsigned sp0 - 8388608.
Variables (path : list byte) (stdin0 : ModelAmb.AmbIn) (fs0 : Fs) (tid : word) (content : list byte).
Hypothesis Htid : 0 < bv_unsigned tid < 2 ^ 22.

Let SP : Z := bv_unsigned sp0.
Abbreviation GRD := (G_rd path stdin0 fs0 tid).

Lemma SPr : 0x7fff80000000 <= SP <= 0x800000000000.
Proof. destruct Hvsp as (A & B & _). unfold sp_window_lo, sp_window_hi in *. unfold SP. lia. Qed.

(* [comment removed for export] *)
Lemma lf_stack : forall M, rd_base SP tid M -> ORB.stack_writable M sp0.
Proof.
  intros M BASE d m Hd Hm.
  pose proof SPr as SPR. destruct Hvsp as (_ & _ & SPal).
  exact (stack_writable_of_base SP SPR tid content M BASE d m Hd Hm).   (* a worker port727: window, no ATOP *)
Qed.

Lemma lf_img : forall M, rd_base SP tid M -> Forall (fun iv => OW.img_clear M (fst iv) (snd iv)) lf_ivs.
Proof.
  intros M BASE. pose proof (rb_img _ _ _ BASE) as IMG. pose proof (rb_mi _ _ _ BASE) as MI.
  unfold lf_ivs. repeat (apply Forall_cons; [|try apply Forall_nil]); cbn [fst snd]; intros i Hi.
  1:{ destruct (Z_lt_le_dec i 0x22000) as [A|A]; [apply mem_inv_none; [exact MI | lia]|].
      apply (IMG 0x22000 0x22ed0 i); [cbn; tauto | lia]. }
  all: lazymatch goal with H : ?lo <= ?j < ?hi |- _ => apply (IMG lo hi j); [cbn; tauto | exact H] end.
Qed.

Lemma lf_tid : forall M, rd_base SP tid M -> OW.cell M 0x741a8 4 (bv_unsigned tid).
Proof. intros M BASE. unfold OW.cell. rewrite Z_to_bv_bv_unsigned. exact (rb_tid _ _ _ BASE). Qed.

Lemma lf_got : forall s LB M, RHEAP s LB M -> OW.cell M 0x22ed0 8 0x944b8.
Proof. intros s LB M HH. exact (proj1 (ssp_of_RHEAP s LB M HH)). Qed.

Lemma lf_guard : forall s LB M, RHEAP s LB M -> OW.cell M 0x944b8 8 (bv_unsigned CAN).
Proof. intros s LB M HH. unfold OW.cell. rewrite Z_to_bv_bv_unsigned. exact (proj2 (ssp_of_RHEAP s LB M HH)). Qed.

Lemma lf_need_locks : forall s LB M, RHEAP s LB M -> OW.cell M 0x944db 1 0.
Proof.
  intros s LB M HH.
  destruct HH as (st & LB0 & _ & _ & (_ & _ & (_ & G & _) & _) & _). unfold RNEED_LOCKS in G.
  destruct G as [[_ B] _]. cbn [cells_bytes cbytes] in B.
  pose proof (bytes_at_rdn (run_segments psegs rc_inp rc_sp rc_mb) M _ _ 0%nat 1%nat B ltac:(cbn; lia)) as X. rewrite Z.add_0_r in X. exact X.
Qed.

(* [comment removed for export] *)
Lemma lf_model : forall X off s mo, OWN X (GRD off) s mo ->
  m_halted mo = None /\ m_vm_lazy mo = [] /\ fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) /\ m_fs mo = fs0.
Proof.
  intros X off s mo HOWN. pose proof HOWN as [(L & _ & HKL & _) [_ HG]].
  split; [exact (kl_halt _ _ _ HKL)|].
  split; [exact (ns_nolazy _ _ _ _ _ _ _ (nodes_sound (run_segments psegs rc_inp rc_sp rc_mb)) mo (kl_minv _ _ _ HKL))|].
  unfold G_rd in HG. rewrite HG. split; reflexivity.
Qed.

(* a worker port727 (): the far-end reader, from KL's minv (the leaf tails' stderr write needs it). *)
Lemma lf_rdr : forall X off s mo, OWN X (GRD off) s mo -> m_channel_reader mo = true.
Proof. intros X off s mo [(L & _ & HKL & _) _]. exact (minv_reader _ (kl_minv _ _ _ HKL)). Qed.

(* [comment removed for export] *)
Theorem leaf_oom : oom_cont SP path stdin0 fs0 tid content (OSp.t_die OSp.msg_oom fs0).
Proof.
  intros pb buf cap M s mo x8 x18 x24 x25 x26 x27 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 RI HCAP HL.
  pose proof (ri_base _ _ _ _ _ _ _ _ _ _ _ RI) as BASE. pose proof (ri_heap _ _ _ _ _ _ _ _ _ _ _ RI) as HH.
  destruct (lf_model _ _ _ _ (ri_own _ _ _ _ _ _ _ _ _ _ _ RI)) as (Hh & Hl & FD2 & FS).
  rewrite <- FS.
  lazymatch goal with |- realizes _ (mkCfg (MS ?RR _ _ _ _ _ _) _) _ =>
    exact (ref_oom_tail sp0 [] mo Hvsp Hh Hl FD2 (lf_rdr _ _ _ _ (ri_own _ _ _ _ _ _ _ _ _ _ _ RI)) (bv_unsigned tid) RR M eq_refl eq_refl eq_refl (lf_stack M BASE) (lf_img M BASE)
             (lf_tid M BASE) Htid (bv_unsigned CAN) (lf_got _ _ _ HH) (lf_guard _ _ _ HH) (lf_need_locks _ _ _ HH) 0x14b60 (or_introl eq_refl)) end.
Qed.

Theorem leaf_refused : ref_cont SP path stdin0 fs0 tid content (OSp.t_die OSp.msg_refused fs0).
Proof.
  intros pb buf M s mo x8 x18 x24 x25 x26 x27 y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 RI HL.
  pose proof (ri_base _ _ _ _ _ _ _ _ _ _ _ RI) as BASE. pose proof (ri_heap _ _ _ _ _ _ _ _ _ _ _ RI) as HH.
  destruct (lf_model _ _ _ _ (ri_own _ _ _ _ _ _ _ _ _ _ _ RI)) as (Hh & Hl & FD2 & FS).
  rewrite <- FS.
  lazymatch goal with |- realizes _ (mkCfg (MS ?RR _ _ _ _ _ _) _) _ =>
    exact (ref_refused_tail sp0 [] mo Hvsp Hh Hl FD2 (lf_rdr _ _ _ _ (ri_own _ _ _ _ _ _ _ _ _ _ _ RI)) (bv_unsigned tid) RR M eq_refl eq_refl eq_refl (lf_stack M BASE) (lf_img M BASE)
             (lf_tid M BASE) Htid (bv_unsigned CAN) (lf_got _ _ _ HH) (lf_guard _ _ _ HH) (lf_need_locks _ _ _ HH)) end.
Qed.

(* [comment removed for export] *)
Theorem leaf_oom1 :
  forall (M' : word -> option byte) (s' : PState) (mo' : Model)
         (y1 y5 y6 y7 x8 x9 y11 y12 y13 y14 y15 y16 y17 x18 x19 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31 : word),
    rd_base SP tid M' -> RHEAP s' [] M' -> OWN [] (GRD 0) s' mo' ->
    realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (MS (mkR y1 (Z_to_bv 64 (SP - 128)) (Z_to_bv 64 0x10800) (Z_to_bv 64 RATP) y5 y6 y7 x8 x9
                                   (Z_to_bv 64 0) y11 y12 y13 y14 y15 y16 y17 x18 x19 (Z_to_bv 64 3) (Z_to_bv 64 65536)
                                   x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)
                              bvmap_empty (Z_to_bv 64 0x14ba0) fc0 None M' (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo') (OSp.t_die OSp.msg_oom fs0).
Proof.
  intros M s mo y1 y5 y6 y7 x8 x9 y11 y12 y13 y14 y15 y16 y17 x18 x19 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31 BASE HH HOWN.
  destruct (lf_model _ _ _ _ HOWN) as (Hh & Hl & FD2 & FS).
  rewrite <- FS.
  lazymatch goal with |- realizes _ (mkCfg (MS ?RR _ _ _ _ _ _) _) _ =>
    exact (ref_oom_tail sp0 [] mo Hvsp Hh Hl FD2 (lf_rdr _ _ _ _ HOWN) (bv_unsigned tid) RR M eq_refl eq_refl eq_refl (lf_stack M BASE) (lf_img M BASE)
             (lf_tid M BASE) Htid (bv_unsigned CAN) (lf_got _ _ _ HH) (lf_guard _ _ _ HH) (lf_need_locks _ _ _ HH) 0x14ba0 (or_intror eq_refl)) end.
Qed.
End LEAF.
