From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import StrFun Verbs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import VerbsMem VerbsFacts strcspn_c strncmp_c verb_is_c.
Import ListNotations.
Open Scope Z_scope.

Lemma nz_not_in : forall l, Forall (fun b => bv_unsigned b <> 0) l -> ~ In (Z_to_bv 8 0) l.
Proof. intros l H HI. rewrite Forall_forall in H. apply (H _ HI). reflexivity. Qed.

Theorem verb_is_holds : strcspn_contract -> strncmp_contract -> verb_is_contract.
Proof.
  intros SC SN. unfold verb_is_contract, VERB_IS, VERB_IS_K, DS_STR, DT_STR.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    can tb fb fs HT HF LT LF HDS HDT HSSP OG OGD HMI ST LO OT OF ODS ODT.
  destruct HT as [HTb HTz]. destruct HF as [HFb [HFz HFs]]. destruct HSSP as [HG HGD].
  cbn [map] in HDS, HDT.
  unfold off_lo, SSP_GOT, SSP_GUARD in *.
  unfold strcspn_contract, STRCSPN, CSPN_SSP_GOT, CSPN_SSP_GUARD in SC.
  unfold strncmp_contract, STRNCMP in SN.
  pose proof (upto_length is_sep tb) as LTT. pose proof (upto_length (fun b => bv_unsigned b =? 32) fb) as LVF.
  fold (tfirst tb) in LTT. fold (vfirst fb) in LVF.
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (proj1 ST) as LO0.
  carve_frame 32%nat ST.
  do 11 zstep.
  assert (SPU : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  assert (UDS : bv_unsigned (Z_to_bv 64 66380) = 66380) by (apply unsigned_lit; lia).
  assert (UDT : bv_unsigned (Z_to_bv 64 67148) = 67148) by (apply unsigned_lit; lia).
  eapply evt_cut.
  { eapply SC with (lo := lo) (can := can) (str := fb) (slack := fs) (set := [Z_to_bv 8 32]);
      rewrite ?SPU, ?UDS; cbn [length app].
    all: first [ exact HFb | exact HDS | exact HG | exact HGD | exact HMI | exact ST | apply nz_not_in; assumption
               | apply nz_not_in; repeat constructor; vm_compute; discriminate | intros _; exact HFs | lia ]. }
  post_call rsegs m1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m2 end.
  rewrite SPU in POST. rename POST into ST.
  do 5 zstep.
  eapply evt_cut.
  { eapply SC with (lo := lo) (can := can) (str := tb) (slack := []) (set := map (Z_to_bv 8) [32; 9]);
      rewrite ?SPU, ?UDT; cbn [length app map].
    all: first [ exact HTb | exact HDT | exact HG | exact HGD | assumption | apply nz_not_in; assumption
               | apply nz_not_in; repeat constructor; vm_compute; discriminate
               | intros HL1; cbn in HL1; lia | lia ]. }
  post_call rsegs m2.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m3 end.
  rewrite SPU in POST. rename POST into ST.
  rewrite cspn_tfirst, cspn_vfirst.
  zstep.
  assert (BE : bv_eqb (Z_to_bv 64 (Z.of_nat (length (tfirst tb)))) (Z_to_bv 64 (Z.of_nat (length (vfirst fb))))
               = Nat.eqb (length (tfirst tb)) (length (vfirst fb))).
  { unfold bv_eqb. rewrite !unsigned_lit by lia.
    destruct (Nat.eqb_spec (length (tfirst tb)) (length (vfirst fb))); [apply Z.eqb_eq | apply Z.eqb_neq]; lia. }
  rewrite BE. clear BE.
  destruct (Nat.eqb_spec (length (tfirst tb)) (length (vfirst fb))) as [EQ|NE]; cbn [negb].
  - do 4 zstep.
    destruct (strncmp_verb tb fb fs HTz HFz EQ) as (v & HV & VR & VE).
    eapply evt_cut.
    { eapply SN with (ls := tb ++ [Z_to_bv 8 0]) (rs := fb ++ Z_to_bv 8 0 :: fs) (v := v);
        [exact HTb | exact HFb | rewrite unsigned_lit by lia; exact HV | assumption]. }
    post_call rsegs m3.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m4 end.
    do 7 zstep. release_frame FR ST (bv_unsigned sp). zstep. finish.
    rewrite <- VE. destruct (Z.eqb_spec v 0) as [->|NZ]; [reflexivity|].
    destruct (v mod 18446744073709551616 <? 1) eqn:LT1; [apply Z.ltb_lt in LT1; exfalso; lia | reflexivity].
  - do 6 zstep. release_frame FR ST (bv_unsigned sp). zstep. finish.
    rewrite (verb_is_m_len_ne tb fb NE). reflexivity.
Qed.
