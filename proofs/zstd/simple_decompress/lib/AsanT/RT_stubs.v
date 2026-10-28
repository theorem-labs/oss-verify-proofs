(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import ITree Nodes Decode SysStep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import MM_syscalls.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import SysStepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Import Exc.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Definition rt_mmap_entry := 0x66700%Z.
Definition rt_munmap_entry := 0x6670c%Z.
Definition rt_mprotect_entry := 0x66718%Z.
Definition rt_close_entry := 0x66754%Z.

(* [comment removed for export] *)
Definition eff_mem (m : word -> option byte) (e : resp) : word -> option byte :=
  apply_writes (apply_copies m (apply_zeros (apply_unmaps m (eff_unmaps e)) (eff_zeros e)) (eff_copies e)) (eff_writes e).

Lemma nret_MSsvc_gen : forall R F pc x8 fc rv m ro e,
  nret (MSsvc R F pc x8 fc rv m ro) e = MS (bvmap_set 10 (eff_ret e) R) F (pc + Z_to_bv 64 4) fc rv (eff_mem m e) ro.
Proof. intros. destruct e. reflexivity. Qed.

Lemma eff_mem_efferr : forall m ci e, eff_mem m (efferr_ci ci e) = m.
Proof. reflexivity. Qed.
Lemma eff_mem_eff0 : forall m ci r, eff_mem m (eff0_ci ci r) = m.
Proof. reflexivity. Qed.
Lemma eff_mem_zeros : forall m r z ci, eff_mem m (mkEffectU r [] [z] [] [] ci) = apply_zeros m [z].
Proof. reflexivity. Qed.
Lemma eff_mem_unmaps : forall m r u ci, eff_mem m (mkEffectU r [] [] [u] [] ci) = apply_unmaps m [u].
Proof. reflexivity. Qed.
Lemma eff_mem_rstrip : forall m e, eff_mem m (rstrip e) = eff_mem m e.
Proof. intros m [r ws zs us cs ci]. reflexivity. Qed.
Lemma eff_ret_rstrip : forall e, eff_ret (rstrip e) = eff_ret e.
Proof. intros [r ws zs us cs ci]. reflexivity. Qed.
Lemma fstepA_rstrip : forall n e R R', fstepA n (rstrip e) R R' <-> fstepA n e R R'.
Proof. intros n e R R'. destruct n; cbn; rewrite ?eff_ret_rstrip; tauto. Qed.

(* [comment removed for export] *)
Lemma rt_mmap_grant : forall addr len flags avoid rsp a R R',
  fstepA (NMmap addr len (PROT_READ + PROT_WRITE) flags) rsp R R' ->
  dec_mmap ATOP len avoid rsp = Some (MmOk a) -> (0 <= len)%Z ->     (* [comment removed for export] *)
  rng R' a (mmap_len len).
Proof.
  intros addr len flags avoid rsp a R R' HF Hdec LEN.
  destruct (dec_mmap_Some _ _ _ _ _ Hdec) as [ci [-> Hok]].
  pose proof (mmap_addr_ok_true _ _ _ _ Hok) as ((HA & H0 & HC) & _).
  pose proof (mmap_len_ge len) as ML. pose proof atop_range as AR.
  assert (E : bv_unsigned (eff_ret (mkEffectU (Z_to_bv 64 a) [] [(wa a, Z_to_bv 64 (mmap_len len))] [] [] ci)) = a).
  { cbn [eff_ret]. apply unsigned_lit. clear -H0 HC ML LEN. lia. }
  pose proof (fstepA_mmap_grant addr len flags _ R R' HF) as G. rewrite E in G.
  rewrite (unsigned_lit len) in G by (clear -H0 HC ML LEN; lia). apply G. exact HA.
Qed.

Section STUBS.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).

Definition rt_regs (a0 a1 a2 a3 a4 a5 a7 : word) : bvmap 5 word :=
  mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.

Local Ltac stub_tail HF Hdec rsp :=
  rewrite nret_MSsvc_gen; rewrite ?mkR_set_a0; simp_regs;
  (lazymatch goal with
   | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4) _ _ _ _) =>
       let p' := eval vm_compute in (p + 4)%Z in
       replace (Z_to_bv 64 p + Z_to_bv 64 4 : word) with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity)
   end).

(* [comment removed for export] *)
Lemma rt_mmap_stub : forall RNG {X} (dec : resp -> option X) (addr len prot flags : Z) (x17 : word),
  implA bsegs RNG (enode (NMmap addr len prot flags) dec)
    (epostF (fun a RNG' ms' => exists rsp,
        fstepA (NMmap addr len prot flags) rsp RNG RNG' /\ dec rsp = Some a /\
        ms' = MS (rt_regs (eff_ret rsp) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) (Z_to_bv 64 222))
                 F (ret_pc ra) fc None (eff_mem m rsp) (seg_rom bsegs)))
    (MS (rt_regs (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) x17)
        F (Z_to_bv 64 0x66700) fc None m (seg_rom bsegs)).
Proof.
  intros RNG X dec addr len prot flags x17. unfold rt_regs. apply implF_enode.
  step. step_ecall. split. { at_nodeA_solve. }
  intros rsp RNG' a HF Hdec. stub_tail HF Hdec rsp.
  step.
  apply evtF_done. exists rsp. split; [exact HF|]. split; [exact Hdec|]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rt_mmap_stubP : forall (fst : node -> resp -> footprint -> footprint -> Prop) RNG {X} (dec : resp -> option X)
    (addr len prot flags : Z) (x17 : word),
  @implF node bsegs (at_nodeA bsegs) fst _ RNG (enode (NMmap addr len prot flags) dec)
    (epostF (fun a RNG' ms' => exists rsp,
        fst (NMmap addr len prot flags) rsp RNG RNG' /\ dec rsp = Some a /\
        ms' = MS (rt_regs (eff_ret rsp) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) (Z_to_bv 64 222))
                 F (ret_pc ra) fc None (eff_mem m rsp) (seg_rom bsegs)))
    (MS (rt_regs (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) x17)
        F (Z_to_bv 64 0x66700) fc None m (seg_rom bsegs)).
Proof.
  intros fst RNG X dec addr len prot flags x17. unfold rt_regs. apply implF_enode.
  step. step_ecall. split. { at_nodeA_solve. }
  intros rsp RNG' a HF Hdec. stub_tail HF Hdec rsp.
  step.
  apply evtF_done. exists rsp. split; [exact HF|]. split; [exact Hdec|]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rt_munmap_stub : forall RNG {X} (dec : resp -> option X) (addr len : Z) (x12 x13 x14 x15 x17 : word),
  implA bsegs RNG (enode (NMunmap addr len) dec)
    (epostF (fun a RNG' ms' => exists rsp,
        fstepA (NMunmap addr len) rsp RNG RNG' /\ dec rsp = Some a /\
        ms' = MS (rt_regs (eff_ret rsp) (Z_to_bv 64 len) x12 x13 x14 x15 (Z_to_bv 64 215))
                 F (ret_pc ra) fc None (eff_mem m rsp) (seg_rom bsegs)))
    (MS (rt_regs (Z_to_bv 64 addr) (Z_to_bv 64 len) x12 x13 x14 x15 x17)
        F (Z_to_bv 64 0x6670c) fc None m (seg_rom bsegs)).
Proof.
  intros RNG X dec addr len x12 x13 x14 x15 x17. unfold rt_regs. apply implF_enode.
  step. step_ecall. split. { at_nodeA_solve. }
  intros rsp RNG' a HF Hdec. stub_tail HF Hdec rsp.
  step.
  apply evtF_done. exists rsp. split; [exact HF|]. split; [exact Hdec|]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rt_mprotect_stub : forall RNG {X} (dec : resp -> option X) (addr len prot : Z) (x13 x14 x15 x17 : word),
  implA bsegs RNG (enode (NMprotect addr len prot) dec)
    (epostF (fun a RNG' ms' => exists rsp,
        fstepA (NMprotect addr len prot) rsp RNG RNG' /\ dec rsp = Some a /\
        ms' = MS (rt_regs (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (eff_ret rsp)))) (Z_to_bv 64 len) (Z_to_bv 64 prot) x13 x14 x15 (Z_to_bv 64 226))
                 F (ret_pc ra) fc None (eff_mem m rsp) (seg_rom bsegs)))
    (MS (rt_regs (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) x13 x14 x15 x17)
        F (Z_to_bv 64 0x66718) fc None m (seg_rom bsegs)).
Proof.
  intros RNG X dec addr len prot x13 x14 x15 x17. unfold rt_regs. apply implF_enode.
  step. step_ecall. split. { at_nodeA_solve. }
  intros rsp RNG' a HF Hdec. stub_tail HF Hdec rsp.
  step. rewrite Z.add_0_r. step.
  apply evtF_done. exists rsp. split; [exact HF|]. split; [exact Hdec|]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rt_close_stub : forall RNG {X} (dec : resp -> option X) (fd : Z) (x11 x12 x13 x14 x15 x17 : word),
  (3 <= fd < 2^32)%Z ->
  implA bsegs RNG (enode (NClose fd) dec)
    (epostF (fun a RNG' ms' => exists rsp,
        RNG' = RNG /\ dec rsp = Some a /\
        ms' = MS (rt_regs (eff_ret rsp) x11 x12 x13 x14 x15 (Z_to_bv 64 57))
                 F (ret_pc ra) fc None (eff_mem m rsp) (seg_rom bsegs)))
    (MS (rt_regs (Z_to_bv 64 fd) x11 x12 x13 x14 x15 x17)
        F (Z_to_bv 64 0x66754) fc None m (seg_rom bsegs)).
Proof.
  intros RNG X dec fd x11 x12 x13 x14 x15 x17 FD. unfold rt_regs. apply implF_enode.
  step. step_ecall. split. { at_nodeA_solve. }
  intros rsp RNG' a HF Hdec. stub_tail HF Hdec rsp.
  step.
  apply evtF_done. exists rsp. split; [exact HF|]. split; [exact Hdec|]. reflexivity.
Qed.

End STUBS.
End CANSEC1.
