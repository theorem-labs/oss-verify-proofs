(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Bytes Arr SysStep ITree Nodes NodesCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim Monad StdioBase Stdio Driver.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import TrzStdio TrzLeaf.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages LazyModel ITreeA NodesA ImplRzA MonadA TrzNodesA CompatE2.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BM_kit BI_shadow B_iface BI_iface BI_lowshadow BX_file BX_trz BX_unreg BX_fini1 BX_fini2 BX_Exit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BX_atexit B_iface5x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition so_get (so : stdout_st) : stdout_st := so.
Definition so_set (so : stdout_st) (_ : stdout_st) : stdout_st := so.

Section Adapt.
Variable APS : Type.
Variable AHK : APS -> list ablock -> list fblock -> mem -> Model -> Prop.
Variable SO : APS -> stdout_st.
Variables (aS : APS -> word -> Prop) (aN : APS -> nat) (aEB : APS -> Z).
Notation C := ACONSTS.

(* [comment removed for export] *)
Definition AHK_icp_exit_stmt : Prop :=
  forall s LB LF m mo, AHK s LB LF m mo ->
       (exists t, exit_statics m t)
    /\ (exists guard cdt thr sec tm1, stdio_state m (SO s) guard cdt thr sec tm1)
    /\ low_shadow_ok m
    /\ pages_budgeted (aS s) 0x7fffc000 0x7fffd000 /\ pages_budgeted (aS s) 0x8000d065 0x8000dfd8
    /\ lazy_disjoint mo alloc_ceiling (2^47) /\ lazy_disjoint mo 0x10000 0x603000.

Hypothesis Hkip : AHK_kip_stmt C APS AHK aS aN aEB.
Hypothesis Hmi : AHK_mem_inv_stmt bsegs APS AHK.
Hypothesis Hexit : AHK_icp_exit_stmt.

#[local] Notation wz := (fun z : Z => Z_to_bv 64 z).
#[local] Notation usp sp := (bv_unsigned sp).

Lemma leaf_exit_model_none : forall code (so : stdout_st) mo r mo',
  zlength (so_buf so) <= STDOUT_BUFSIZ ->
  leaf (Driver.exit_model (io_S so_get so_set) code so) mo r mo' -> False.
Proof. aceil.
  intros code so mo r mo' Hb L. unfold Driver.exit_model in L.
  change (io_exit (io_S so_get so_set)) with (stdout_exit_flush so_get so_set) in L.
  apply leaf_mbind_inv in L as (a & mo1 & L1 & L).
  apply (leaf_stdout_exit_flush_ok so_get so_set (fun _ _ => eq_refl) (fun _ _ _ => eq_refl)) in L1 as [-> ->]; [| exact Hb | intros x; reflexivity].
  cbn [fst snd] in L. apply leaf_msys in L as (rsp & evs & Hst & _). exact Hst.
Qed.

Lemma aexit_rz :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : APS) (LB : list ablock) (LF : list fblock)
         (code lo : Z),
  AHK s LB LF m mo -> atx_ok_on bsegs m -> 0 <= code < 2^32 -> zlength (so_buf (SO s)) <= STDOUT_BUFSIZ ->
  stk bsegs m lo (usp sp) -> alloc_ceiling <= lo -> lo <= usp sp - AEXIT_STACK -> usp sp < 2^47 -> tp = wz (c_tp C) -> frm0 fc -> a0 = wz code ->
  realizes_cfg acfg bsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz (c_exit C)) fc None m (seg_rom bsegs)) mo)
            (ShapeAlg.t_emit (Wz 1 (fst (exit_flush_pure (SO s)))) (t_exit (bv_and (wz code) (wz 255)) (m_fs mo))).
Proof. aceil.
  intros until lo. intros HA (reg & p3 & p4 & FJ & AJ & ATC & _ & FLG) CODE HB ST LOC LO SPTS HTP FRM HA0.
  cbv beta. unfold AEXIT_STACK in LO.
  destruct (Hkip _ _ _ _ _ HA) as (Hh & Hminv & HLI & POL & MAG).
  pose proof (Hmi _ _ _ _ _ HA) as MI.
  destruct (Hexit _ _ _ _ _ HA) as ((t & ES) & (guard & cdt & thr & sec & tm1 & SS) & LS & PBA & PBB & LDS & LDI).
  pose proof (bv_unsigned_in_range 64 sp) as SR. unfold bv_modulus in SR. cbn in SR.
  aceil.
  set (P := acc_ok (m_vm_lazy mo) (aS s)).
  assert (IM : implMA bsegs P (Driver.exit_model (io_S so_get so_set) code) (SO s) (fun _ _ _ => False)
                 (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x92900) fc None m (seg_rom bsegs))).
  { eapply (exit_spec so_get so_set) with (lo := lo) (t := t) (guard := guard) (cdt := cdt) (thr := thr) (sec := sec) (tm1 := tm1)
                                            (reg := reg) (p3 := p3) (p4 := p4) (FJ := FJ) (AJ := AJ).
    - intros x so; reflexivity.
    - intros x so so'; reflexivity.
    - intros x; reflexivity.
    - intros a k H1 H2. apply POL. unfold adrv_acc. cbn [fst snd]. rewrite unsigned_lit by lia. left. aceil. lia.
    - intros a k H1 H2. apply POL. unfold adrv_acc. cbn [fst snd c_img_lo c_img_hi ACONSTS]. rewrite unsigned_lit by lia. right; left. lia.
    - intros a k H1 H2. right. eapply pages_budgeted_acc_inS; [exact PBA | lia | lia | lia | lia].
    - intros a k H1 H2. right. eapply pages_budgeted_acc_inS; [exact PBB | lia | lia | lia | lia].
    - intros a. right. split; [| intros k Hk; cbn in Hk; lia]. unfold acc_nowrap. cbn [fst snd].
      pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 a)) as X. unfold bv_modulus in X. cbn in X. lia.
    - exact ST.
    - exact LOC.   (* [comment removed for export] *)
    - unfold AEXIT_DEPTH. lia.
    - exact SPTS.
    - exact MI.
    - exact ES.
    - exact SS.
    - exact ATC.
    - exact FLG.
    - apply (low_shadow_stk _ _ _ LS); lia.
    - apply (low_shadow_stk _ _ _ LS); lia.
    - apply (low_shadow_stk _ _ _ LS); lia.
    - rewrite HTP. reflexivity.
    - exact HA0.
    - exact CODE. }
  unfold implMA in IM.
  eapply (implA_trzA_srealizes bsegs (aS s) (aN s) (aEB s) P
            (Driver.exit_model (io_S so_get so_set) code (SO s)) _ _ mo mo (fun _ _ => t_nil) _ IM).
  - (* [comment removed for export] *)
    unfold Driver.exit_model. change (io_exit (io_S so_get so_set)) with (stdout_exit_flush so_get so_set).
    apply (trzA_stdout_exit_flush_k so_get so_set (fun _ _ => eq_refl) (fun _ _ _ => eq_refl)
             (fun _ => msys (NExit code) dec_exit) (SO s) mo (fun _ _ => t_nil) _ (conj Hminv Hh) HB).
    + apply trzA_exit. exact Hminv.
    + apply t_emit_has_nil.
    + intros x; reflexivity.
  - apply mequiv_refl.
  - split; [split; [exact HLI | split; [exact Hminv | exact Hh]] | intros x Hx; exact Hx].
  - intros r ms' mot' moa' _ L _ _. exfalso. exact (leaf_exit_model_none code (SO s) mo r mot' HB L).
Qed.

Lemma aexit_ok : aexit_atx_stmt bsegs C APS AHK SO.
Proof. aceil.
  unfold aexit_atx_stmt. intros. eapply aexit_rz; eassumption.
Qed.

(* [comment removed for export] *)
Lemma alibc_head_ok : AHK_libc_head_stmt bsegs APS AHK.
Proof.
  intros s LB LF m mo HA.
  destruct (Hexit _ _ _ _ _ HA) as (_ & (guard & cdt & thr & sec & tm1 & SS) & _).
  destruct SS as (STAT & _). destruct STAT as (LIBC & _). exists cdt, thr, sec, tm1. exact LIBC.
Qed.
End Adapt.
End RC__1.
