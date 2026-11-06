(* The slot LLVMFuzzerTestOneInput, plain image: segment C of the op_write arm (fuzz_link.c:735-751),
   from free's return 0x14060 (LC1Defs.c1_14060) to the next loop head 0x13a1c or to L_EXIT 0x1413c
   (LC1Defs.c1_next). The code (link/ct/dis/plain/LLVMFuzzerTestOneInput.s):
     0x14060  addi  s5, zero, 0x2e      s5 = 46
     0x14064  ld    s6, 0x30(sp)        s6 = A_JT (frame cell FO_JT)
     0x14068  bltu  s5, s11, 0x1413c    taken iff 46 < i, i.e. i = 47: L_EXIT
     0x1406c  ld    s2, 0x48(sp)        s2 = N (the cursor cell FO_N)
     0x14070  addiw s11, s11, 1         s11 = i + 1
     0x14074  bnez  s2, 0x13a1c         N <> 0: the loop head of operation i + 1
     0x14078  j     0x1413c             N = 0: L_EXIT
   No store and no call: the footprint is LC1Call.seg_fp_refl. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC1Defs LC1Call.
Local Open Scope Z_scope.

Theorem c1_seg_C : forall (E : lenv) (i : Z) (gp : word) (ms : machine_state),
  lenv_ok E -> c1_14060 E i gp ms ->
  evt rsegs (eqv_cl (fun ms' => c1_next E i gp ms' /\ seg_fp (e_S E) (c1_hp E) (ms_mem ms) (ms_mem ms'))) ms.
Proof.
  intros E i gp ms HE H.
  remember (ms_mem ms) as m0 eqn:Em0.
  destruct H as (ra & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & s5 & s6 &
                 t3 & t4 & t5 & t6 & F & fc & m & P & N & kbs & mbs & gbs &
                 -> & FC & Hi & HN & LM & CUR & MI & TM & ST).
  cbv [ms_mem MS] in Em0. subst m0.
  pose proof LM as LM'.
  destruct LM' as (FRx & SAV & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LA & _ & _ & _ & _ & _ & _ & _ &
                   CU & WE & GM).
  destruct FRx as (j0 & j1 & j2 & nc & FR).
  destruct CU as (_ & k & Hk & EP & EN).
  destruct HE as (HS1 & HS2 & _ & _ & _ & _ & _ & _ & HPL & _).
  unfold lh_cells in FR. unfold FO_P in CUR.
  unfold wz, C1_FREE_RA.
  step. step. step.
  destruct (Z.eq_dec i 47) as [->|I47].
  - if_true.
    apply evt_eqv_done. split; [right | apply seg_fp_refl].
    destruct (rw_cells_forget _ _ _ _ FR) as [jf FRf].
    unfold ex_ms. do 30 eexists. split; [reflexivity|].
    refine (conj FC (conj _ (conj SAV (conj WE (conj GM (conj LA (conj MI (conj TM ST)))))))).
    exact FRf.
  - assert (Ui : bv_unsigned (Z_to_bv 64 i) = i) by (apply unsigned_lit; lia).
    assert (C3 : bv_ltu (Z_to_bv 64 46) (Z_to_bv 64 i) = false).
    { unfold_cond. fold_lit_ux. rewrite Ui. apply Z.ltb_ge. lia. }
    rewrite C3; cbv iota.
    clear FR. move CUR at bottom.
    step. step.
    assert (SW : bv_swrap 32 (i + 1) = i + 1)
      by (apply bv_swrap_small; change (bv_half_modulus 32) with (2 ^ 31); lia).
    rewrite Ui, SW.
    step.
    assert (UN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
    destruct (Z.eq_dec N 0) as [N0|N0].
    + rewrite N0. if_false. step.
      apply evt_eqv_done. split; [right | apply seg_fp_refl].
      destruct LM as ((j0' & j1' & j2' & nc' & FR') & _).
      destruct (rw_cells_forget _ _ _ _ FR') as [jf FRf].
      unfold ex_ms. do 30 eexists. split; [reflexivity|].
      refine (conj FC (conj _ (conj SAV (conj WE (conj GM (conj LA (conj MI (conj TM ST)))))))).
      exact FRf.
    + assert (C6 : negb (bv_eqb (wz N) (Z_to_bv 64 0)) = true).
      { unfold wz. unfold_cond. fold_lit_ux. rewrite UN. apply Bool.negb_true_iff, Z.eqb_neq. lia. }
      rewrite C6; cbv iota.
      apply evt_eqv_done. split; [left; split; [lia|] | apply seg_fp_refl].
      unfold lh_ms. do 26 eexists. split; [reflexivity|].
      refine (conj FC (conj _ (conj _ (conj LM (conj MI (conj TM ST)))))); lia.
Qed.
