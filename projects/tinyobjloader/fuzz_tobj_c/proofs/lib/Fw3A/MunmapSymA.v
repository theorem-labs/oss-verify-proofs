(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (triple1_munmap_symA and etriple_munmap_symA written as plain text with munmap's exact cut, maps_subtract equals map_remove, added to their premise and passed to the munmap step lemmas; the frame obligation's new cases closed by RomBase's tactics; RomBase imported). *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "eval"; "reg_sv"; "SLit"; "rm"; "sobj"; "valuation"; "obj_range"; "ranges_disjoint"; "ss_next"; "ss_objs"; "ss_pc"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "Z_to_bv"; "bv"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_X"; "ax_base"; "shadow_addr"; "@Stdlib.ZArith.BinInt.Z"; "add"; "lt"; "le"; "modulo"; "pow"; "@Corelib.Init.Datatypes"; "pair"; "list"; "bool"; "prod"; "true"; "Some"; "fst"; "option"; "snd"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "vm_maps"; "Model"; "event"; "TASK_SIZE"; "map_has"; "map_remove"; "page_size"; "region_free"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "unmap_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MmapFixedA"; "tp_forget"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "stableA"; "ok_frameA"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_gpr"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "smatch_pendingA"; "A_after"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "munmap_model"; "mmap_n"; "mmap_nZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep RomBase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundL SymSoundM SymSoundR SymComplete SymCall SymExit Glue3 SymHeap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA LedgerA SysCallA MmapA MmapFixedA MmapFixedA2 MmapNodesA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import SysSpecStart SysStartA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Open Scope Z_scope.

Section N.
Variable segs : list Segment.
Local Notation wstep := (wstep segs).

Lemma munmap_len_sym : ltac2:(tb__ "0|6|
S9S1eS11Q40M0A1M1A1S14S1eS2aA1M2S39S29S3S12S40Vsegs;R8R7R6S1dG2S3bR5S3cR4R3A2A4A5S0S3S5S13R7A1ZbA2R3A3S0G1S4RaR4A2S10G0R3A2A3S0S12S1bR4Z1000A2Z0M3A3S1S19G3R5A2S19R5S1cZ2Z3eA2A2A2S1S2S0G1S3aR9U1A2M4S10G0G3A2A3A1S1S0S12S45G4A1R6A3S1S0G1S44G4A1S10G0R6A2M5A3S0S12SfG0G5A2R6A3A2A2A2F_;F_;F_;F_;F_;Fnlit;Fen;Fmd;Fms;Ftr;FA;Ftp;Frho;").
Proof using .
  intros rho tp A tr ms md en nlit Hsp H11 Een Hmod Hn.
  destruct (pending_argsA segs rho tp A tr ms md Hsp) as (_ & G1 & _). rewrite H11, Een in G1.
  assert (Un : bv_unsigned (Z_to_bv 64 nlit) = nlit) by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; change (bv_modulus 64) with (2 ^ 64); lia).
  assert (Hlenv : bv_unsigned (ms_gpr ms 1) = nlit) by (rewrite G1; exact Un).
  assert (HnZ : mmap_nZ (ms_gpr ms 1) = nlit).
  { unfold mmap_nZ, page_round_up_Z, page_size. rewrite Hlenv.
    pose proof Hmod as Hmod'. apply Z.mod_divide in Hmod'; [|lia]. destruct Hmod' as [q Hq]. rewrite Hq.
    replace (q * 4096 + 4096 - 1) with (4095 + q * 4096) by lia. rewrite Z.div_add by lia. change (4095 / 4096) with 0. lia. }
  split; [intros E; rewrite E in Hlenv; rewrite Z_to_bv_unsigned in Hlenv; change (bv_wrap 64 0) with 0 in Hlenv; lia|].
  split; [exact HnZ|]. split; [unfold mmap_n; rewrite HnZ; reflexivity | exact Un].
Qed.

(* LPS 08b1429 (in 727298f3): the exact munmap arm cuts with [maps_subtract]; Fw3A/MmapNodesA.v's
   Section MunmapA takes [Hrm] (the cut removes exactly the entry, the model's
   [maps_subtract_exact]).  This triple and [etriple_munmap_symA] below are written out as plain
   text (decoded from this file's [tbs__] table) with that one conjunct added to the J-premise,
   right after the [map_has] one, as MmapNodesA.v's [triple1_munmapA] has it. *)
Theorem triple1_munmap_symA :
  forall (ok : world -> Prop) (J Jo : jpredA) (A : axst) (rho : valuation)
         (tp : list word) (ea en : sv) (nlit : Z),
    ok_frameA segs ok J ->
    ok_pframeA segs ok J ->
    stableA segs (ss_next (ax_S A)) J ->
    instr_at segs (ss_pc (ax_S A)) = Some Ecall ->
    reg_sv (ax_S A) 17 = SLit 215 ->
    reg_sv (ax_S A) 10 = ea ->
    reg_sv (ax_S A) 11 = en ->
    eval rho en = Z_to_bv 64 nlit ->
    nlit mod 4096 = 0 ->
    0 < nlit < 2 ^ 62 ->
    (forall tr ms md,
        smatch_pendingA segs rho tp A (tr, mkCfg ms md) ->
        J rho tp tr md ->
        (let a := ms_gpr ms 0 in
           bv_unsigned a mod page_size = 0
           /\ bv_unsigned a + nlit <= TASK_SIZE
           /\ map_has (vm_maps (m_vmmaps md)) a (Z_to_bv 64 nlit) = true
           /\ maps_subtract (vm_maps (m_vmmaps md)) (bv_unsigned a)
                (bv_unsigned a + bv_unsigned (Z_to_bv 64 nlit))
              = map_remove (vm_maps (m_vmmaps md)) a
           /\ (forall s, In (a, s) (vm_maps (m_vmmaps md)) -> s = Z_to_bv 64 nlit)
           /\ region_free (map_remove (vm_maps (m_vmmaps md)) a) a (Z_to_bv 64 nlit) = true
           /\ (forall o, In o (ss_objs (ax_S A)) ->
                 ranges_disjoint (obj_range rho o)
                   (bv_unsigned a, bv_unsigned a + nlit))
           /\ (forall (rr : sv * sv) (y : Z),
                 In rr (ax_X A) ->
                 bv_unsigned (eval rho (fst rr)) <= y
                   < bv_unsigned (eval rho (fst rr)) + bv_unsigned (eval rho (snd rr)) ->
                 ~ (bv_unsigned a
                      <= bv_unsigned (shadow_addr (bv_unsigned (eval rho (ax_base A))) y)
                      < bv_unsigned a + nlit))
           /\ Jo (set_rm rho (unmap_range (rm rho) a (Z_to_bv 64 nlit)))
                (tp_forget (bv_unsigned a) (bv_unsigned a + nlit) tp) tr
                (munmap_model md a (Z_to_bv 64 nlit)))) ->
    triple1 segs ok (SPA segs J A rho tp)
      (fun w => SPA segs Jo (A_after A (SLit 0))
                  (set_rm rho (unmap_range (rm rho) (eval rho ea) (Z_to_bv 64 nlit)))
                  (tp_forget (bv_unsigned (eval rho ea))
                     (bv_unsigned (eval rho ea) + nlit) tp) w).
Proof using .
  intros ok J Jo A rho tp ea en nlit Hokf Hokp Hst Hi H17 H10 H11 Een Hmod Hn HJ.
  apply triple1_ecall_detA; [exact Hokf | exact Hst | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pendingA_pending segs _ _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segs _ _ _ _ _ _ Hsp) as Hh.
  destruct (munmap_len_sym rho tp A tr ms md en nlit Hsp H11 Een Hmod Hn) as (Hlen & HnZ & HnE & Un).
  destruct (pending_argsA segs rho tp A tr ms md Hsp) as (G0 & _). rewrite H10 in G0.
  destruct (HJ tr ms md Hsp Hk) as (Hal & Hwrap & Hhas & Hrm & Huniq & Hfree & Hdisj & Hxs & HJo).
  assert (H215 : bv_unsigned (Z_to_bv 64 215) = 215%Z) by reflexivity.
  assert (Hwrap' : bv_unsigned (ms_gpr ms 0) + mmap_nZ (ms_gpr ms 1) <= TASK_SIZE) by (rewrite HnZ; exact Hwrap).
  unfold TASK_SIZE in Hwrap.
  rewrite <- HnE in Hhas.
  rewrite <- HnE in Hrm.
  split.
  - eapply Hokp; try exact Hk; try exact Hp; try (solve [RomBase.rob_auto | eapply RomBase.sys_rob_exit; eassumption]). apply (munmap_only_okA segs ms md _ H215 Hal Hlen Hwrap' Hhas Hrm).
  - intros w' Hw. rewrite (wstep_munmap_invA segs ms md _ Hh H215 Hal Hlen Hwrap' Hhas Hrm tr w' Hp Hw). rewrite HnE. rewrite <- G0.
    split.
    + unfold munmap_model, with_mmap_destroyed. unfold A_after.
      replace (bv_unsigned (ms_gpr ms 0) + nlit) with (bv_unsigned (ms_gpr ms 0) + bv_unsigned (Z_to_bv 64 nlit)) by (rewrite Un; reflexivity).
      eapply (smatchA_after_munmap segs rho _ tp A tr ms md tr (munmap_vm (m_vmmaps md) (ms_gpr ms 0) (Z_to_bv 64 nlit))
                (ms_gpr ms 0) (Z_to_bv 64 nlit) (Z_to_bv 64 0) (SLit 0) (ss_next (ax_S A)) Hsp);
        try reflexivity.
      all: try exact Huniq; try exact Hfree; try exact Hal; try exact Hend; try exact Hea; try exact (map_contains_In _ _ _ Hcont); try (rewrite <- HnE; exact (map_contains_In _ _ _ Hcont));
           try (rewrite Un; unfold page_size; exact Hmod); try (rewrite Un; exact Hdisj); try (rewrite Un; exact Hxs);
           try (rewrite Un; exact Hseg); try (rewrite Un; exact Htl); try apply agree_below_refl; try apply Pos.le_refl;
           try (rewrite eval_set_rm; symmetry; exact G0); try (cbn [eval]; unfold enomem_ret; apply Z_to_bv_bv_unsigned); try (rewrite Un; lia).
    + cbn [w_tr w_cfg fst snd cfg_model]. exact HJo.
Qed.

Theorem etriple_munmap_symA :
  forall (J Jo : jpredA) (A : axst) (rho : valuation)
         (tp : list word) (ea en : sv) (nlit : Z),
    stableA segs (ss_next (ax_S A)) J ->
    instr_at segs (ss_pc (ax_S A)) = Some Ecall ->
    reg_sv (ax_S A) 17 = SLit 215 ->
    reg_sv (ax_S A) 10 = ea ->
    reg_sv (ax_S A) 11 = en ->
    eval rho en = Z_to_bv 64 nlit ->
    nlit mod 4096 = 0 ->
    0 < nlit < 2 ^ 62 ->
    (forall tr ms md,
        smatch_pendingA segs rho tp A (tr, mkCfg ms md) ->
        J rho tp tr md ->
        (let a := ms_gpr ms 0 in
           bv_unsigned a mod page_size = 0
           /\ bv_unsigned a + nlit <= TASK_SIZE
           /\ map_has (vm_maps (m_vmmaps md)) a (Z_to_bv 64 nlit) = true
           /\ maps_subtract (vm_maps (m_vmmaps md)) (bv_unsigned a)
                (bv_unsigned a + bv_unsigned (Z_to_bv 64 nlit))
              = map_remove (vm_maps (m_vmmaps md)) a
           /\ (forall s, In (a, s) (vm_maps (m_vmmaps md)) -> s = Z_to_bv 64 nlit)
           /\ region_free (map_remove (vm_maps (m_vmmaps md)) a) a (Z_to_bv 64 nlit) = true
           /\ (forall o, In o (ss_objs (ax_S A)) ->
                 ranges_disjoint (obj_range rho o)
                   (bv_unsigned a, bv_unsigned a + nlit))
           /\ (forall (rr : sv * sv) (y : Z),
                 In rr (ax_X A) ->
                 bv_unsigned (eval rho (fst rr)) <= y
                   < bv_unsigned (eval rho (fst rr)) + bv_unsigned (eval rho (snd rr)) ->
                 ~ (bv_unsigned a
                      <= bv_unsigned (shadow_addr (bv_unsigned (eval rho (ax_base A))) y)
                      < bv_unsigned a + nlit))
           /\ Jo (set_rm rho (unmap_range (rm rho) a (Z_to_bv 64 nlit)))
                (tp_forget (bv_unsigned a) (bv_unsigned a + nlit) tp) tr
                (munmap_model md a (Z_to_bv 64 nlit)))) ->
    etriple segs (SPA segs J A rho tp)
      (fun w => SPA segs Jo (A_after A (SLit 0))
                  (set_rm rho (unmap_range (rm rho) (eval rho ea) (Z_to_bv 64 nlit)))
                  (tp_forget (bv_unsigned (eval rho ea))
                     (bv_unsigned (eval rho ea) + nlit) tp) w).
Proof using .
  intros J Jo A rho tp ea en nlit Hst Hi H17 H10 H11 Een Hmod Hn HJ.
  apply etriple_ecall_detA; [exact Hst | exact Hi |].
  intros tr ms md Hsp Hk.
  pose proof (smatch_pendingA_pending segs _ _ _ _ _ _ Hsp) as Hp. rewrite H17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segs _ _ _ _ _ _ Hsp) as Hh.
  destruct (munmap_len_sym rho tp A tr ms md en nlit Hsp H11 Een Hmod Hn) as (Hlen & HnZ & HnE & Un).
  destruct (pending_argsA segs rho tp A tr ms md Hsp) as (G0 & _). rewrite H10 in G0.
  destruct (HJ tr ms md Hsp Hk) as (Hal & Hwrap & Hhas & Hrm & Huniq & Hfree & Hdisj & Hxs & HJo).
  assert (H215 : bv_unsigned (Z_to_bv 64 215) = 215%Z) by reflexivity.
  assert (Hwrap' : bv_unsigned (ms_gpr ms 0) + mmap_nZ (ms_gpr ms 1) <= TASK_SIZE) by (rewrite HnZ; exact Hwrap).
  unfold TASK_SIZE in Hwrap.
  rewrite <- HnE in Hhas.
  rewrite <- HnE in Hrm.
  eexists. split; [exact (wstep_munmap_introA segs ms md _ Hh H215 Hal Hlen Hwrap' Hhas Hrm tr Hp)|].
  rewrite HnE. rewrite <- G0. split.
  - unfold munmap_model, with_mmap_destroyed. unfold A_after.
    replace (bv_unsigned (ms_gpr ms 0) + nlit) with (bv_unsigned (ms_gpr ms 0) + bv_unsigned (Z_to_bv 64 nlit)) by (rewrite Un; reflexivity).
    eapply (smatchA_after_munmap segs rho _ tp A tr ms md tr (munmap_vm (m_vmmaps md) (ms_gpr ms 0) (Z_to_bv 64 nlit))
              (ms_gpr ms 0) (Z_to_bv 64 nlit) (Z_to_bv 64 0) (SLit 0) (ss_next (ax_S A)) Hsp);
      try reflexivity.
    all: try exact Huniq; try exact Hfree; try exact Hal; try exact Hend; try exact Hea; try exact (map_contains_In _ _ _ Hcont); try (rewrite <- HnE; exact (map_contains_In _ _ _ Hcont));
         try (rewrite Un; unfold page_size; exact Hmod); try (rewrite Un; exact Hdisj); try (rewrite Un; exact Hxs);
         try (rewrite Un; exact Hseg); try (rewrite Un; exact Htl); try apply agree_below_refl; try apply Pos.le_refl;
         try (rewrite eval_set_rm; symmetry; exact G0); try (cbn [eval]; unfold enomem_ret; apply Z_to_bv_bv_unsigned); try (rewrite Un; lia).
  - cbn [w_tr w_cfg fst snd cfg_model]. exact HJo.
Qed.

End N.
