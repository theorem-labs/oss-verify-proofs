From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import ManifestModel ManifestMem expected_c check_as_written_c.
Import ListNotations.
Open Scope Z_scope.

Theorem check_as_written_holds : expected_contract -> check_as_written_contract.
Proof.
  intros EXP. unfold check_as_written_contract, CHECK_AS_WRITTEN, CHECK_AS_WRITTEN_K.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    tb ts ub us HT HU HA0 HA1 HLT HLU HN HP HMI ST LO OT OU OP.
  subst a2. set (N := names (zbytes tb) (zbytes ub)) in *.
  unfold EXPECTED_K in *. unfold PREFIX_LC_STR in *.
  destruct HT as [HTb [HTz HTs]]. destruct HU as [HUb [HUz HUs]].
  unfold off_stack in OT, OU, OP.
  unfold prefix_lc in HP. cbn [map app] in HP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (proj1 ST) as LO0.
  carve_frame 16%nat ST.
  do 5 zstep.
  assert (SPU : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16)
    by (apply unsigned_lit; lia).
  eapply evt_cut.
  { eapply EXP with (lo := lo) (tb := tb) (ts := ts) (ub := ub) (us := us);
      unfold off_stack, PREFIX_LC_STR, EXPECTED_K; try rewrite SPU;
      first [ split; [assumption | split; assumption] | exact HP | assumption | lia ]. }
  intros ms' PO. unfold kret in PO. rewrite SPU in PO. fold N in PO.
  destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
                  E & MU2 & WM2 & MI2 & ST2 & R).
  subst ms' a0'.
  replace (ret_pc (Z_to_bv 64 78408)) with (Z_to_bv 64 78408) by (apply bv_eq; vm_compute; reflexivity).
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp + -16) [C8 s0; C8 ra]).
  { eapply rw_cells_transport; [exact FR | exact MU2 | exact WM2 | cbn; unfold EXPECTED_K; lia]. }
  clear FR. rename FR2 into FR.
  assert (MUF : munch [(bv_unsigned sp - 256, bv_unsigned sp)] m m2).
  { eapply munch_trans; [eapply munch_weaken; [|exact MU] | eapply munch_weaken; [|exact MU2]];
      intros x Hx; cbn in *; unfold EXPECTED_K in *; lia. }
  pose proof (wmono_trans rsegs _ _ _ WM WM2) as WMF.
  clear MU MU2 WM WM2 ST.
  zstep.
  destruct (bv_eqb (Z_to_bv 64 N) (Z_to_bv 64 0)) eqn:EQ0.
  - cbn [negb]. zstep. rewrite EQ0. cbn [negb]. zstep. rewrite EQ0.
    do 3 zstep. release_frame FR ST2 (bv_unsigned sp). zstep. finish; try exact I.
  - cbn [negb]. zstep. rewrite EQ0. zstep. rewrite EQ0.
    do 3 zstep. release_frame FR ST2 (bv_unsigned sp). zstep. finish; try exact I.
Qed.
