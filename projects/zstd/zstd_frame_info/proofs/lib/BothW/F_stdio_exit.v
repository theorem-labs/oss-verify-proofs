(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim Monad Stdio Prog.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import F_syscalls StdioFiles Stdio_kit.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import F_stdio_write F_stdout_write F_fwritex_stdout.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg MonadF AExit.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import ITreeA StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma bv_eqb_refl : forall {n} (x : bv n), bv_eqb x x = true.
Proof. intros n x. unfold bv_eqb. apply Z.eqb_refl. Qed.

End CANSEC1.
Ltac if_refl :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if bv_eqb ?x ?x then _ else _) _ _ _ _) => rewrite (bv_eqb_refl x); cbv iota
  end.

Ltac if_lit :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
  end.

(* [comment removed for export] *)
Ltac raise_high :=
  repeat match goal with H : rw_cells bsegs _ ?A _ |- _ =>
    lazymatch A with Zpos _ => idtac | _ => fail end;
    lazymatch eval vm_compute in (0x5e6000 <=? A)%Z with true => idtac | false => fail end;
    move H at bottom;
    lazymatch type of H with ?T => change T with (sf_hide T) in H end
  end; sf_unhide.
Ltac hstep := raise_high; step.

Section CANSEC2. Context {rc : runConstT}.
Section StdioExit.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Hypothesis get_set : forall s so, get_so (set_so so s) = so.
  Hypothesis set_set : forall s so so', set_so so' (set_so so s) = set_so so' s.
  Hypothesis set_get : forall s, set_so (get_so s) s = s.

  #[using="get_set set_set set_get"] Theorem stdio_exit_proof : stdio_exit_spec_stmt2 get_so set_so.
  Proof.
    unfold stdio_exit_spec_stmt2. intros until tm1. intros ST LIBC OFL SIN SINF SOUT SERR SOF SEF GOT GUARD MI -> LO GLO RSTK RIMG RG0 SP47.
    unfold GLOBALS_TOP, got_ssp, ssp_guard, RSTDIN, stdin_cells in *.
    destruct SOF as (flags & mode & tail & bufbytes & FC & FL72 & BUF & BUFP & BUFL & INACT).
    destruct SEF as (eflags & emode & ee & ewend & etail & EFC).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    remember (get_so s) as so eqn:ESO.
    pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp); (RSTDOUT, 0x9d7c0); (RSTDOUT_BUF, 0x5f4ae0)]%Z m) as MU.
    pose proof (wmono_refl bsegs m) as WM.
    assert (FL64 : Z.land (bv_unsigned flags) 64 = 0).
    { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
      destruct (Z.eq_dec i 6) as [->|NE].
      - pose proof (f_equal (fun z => Z.testbit z 6) FL72) as T. cbn beta in T. rewrite Z.land_spec, Z.bits_0 in T.
        change (Z.testbit 64 6) with true in T |- *. change (Z.testbit 72 6) with true in T. exact T.
      - change 64 with (2^6). Local Ltac2 Set LiaHints.tbl := fun () => "01h0?11076238981.11712428134302.11612712493573.11713106294589.96 15685060272.10116464978571.11717316435632.11717429498245.11617776320431.10017826350070.98 18039553618.10118039553618.99 19006120615.99 19190715397.11719251685870.96 19251685870.99 20433961190.90 2172651747.2   22961942245.0  24161039186.10124161039186.99 24812739566.96 24812739566.99 25076088621.11725271559662.96 25271559662.99 25435258127.10125566553219.99 2597719022.96  2597719022.99  26323796050.10126323796050.99 26494647592.10126494647592.96 26494647592.99 26506338798.96 26506338798.99 26631534418.10126631534418.99 26918735101.96 2713962757.117 27810329426.10127810329426.99 31399144472.94 31401241662.11432008302853.11732027975233.0  32600174396.96 33510054780.92 33611007621.11734140524150.98 3523399062.5   3834455829.95  3836733332.115 38847153746.10138847153746.99 39937472148.93 40201484047.10440201484047.12440201484047.99 41072247790.96 41072247790.99 42589983314.10142589983314.99 42831019478.10142831019478.99 43000880110.96 43000880110.99 43035628988.3  43061776187.88 43104399792.99 43802119662.96 43802119662.99 43987951405.98 45221239098.96 45221239098.99 45464076536.11748615158610.10148615158610.99 4866047897.99  5180980284.99  52712884706.11653675608710.96 53767577774.10353767577774.12353767577775.98 54164510851.10254164510851.12254164510851.96 54958665221.11656170415931.4  57622410744.11758146277394.91 59038122478.96 59038122478.99 59178106163.10159308587280.3  59310859210.1  59310859210.2  59591862534.96 59624177333.0  60247965245.96 60679622738.10160679622738.99 61874979822.96 61874979822.99 62583080755.99 63135048575.0  63235321900.10163235321900.12163235321901.95 63779719325.10163792152522.89 63967133241.88 66716304261.11667081926311.96 67442352978.10167442352978.99 68094715463.93 954855045.116  00000<00=00I00V00^00c00h01401<01A01M01Y01^01j02602B02G02M02N02Z02f03203>03J03V03b03g03l04804D04P04\04a04f04k05705C05O05[05`05l06806D06I06N06Z06[06c06h07407907E07M07U07a07m08508:08?08D08P08\08h09409>09H09T09`09d09l0:40:@0:L0:T0:^0:h0;40;@0;L0;Q0;Y0;Z0;_0;g0;o0<70<<0<A0<F0<R0<S0<`0<h0=40=@0=E0=M0=R0=W0=\0=]0=b0=n0>:0>F0>R0>W0>X0>`0>h0?00?50?;0?<0?H0?M0?Y0?e0?j0@6S2LO3GLO3LTBFS2LO3GLO3LTBS4BUFL3LTB2CFS3LTB2HBS3LTBS3LTBS2LO3GLO3LTBS2LO3LTBS3LTBS2LO3GLO3LTBS2LO3GLO3LTBS3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS3LTBS4SP47SS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS3LTBS3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS3LTBS3LTBS3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS3LTBS3LTBS2LO3GLO3LTBSS3LTB2HBS3LTBS2LO3GLO3LTBS3LTBS2LO3GLO3RSPS2LO3LTBS2LO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3LTBS3LTBS3LTBS3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS4SP473LTBS4SP473LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LOS2LO3LTBS3LTB2HBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3LTBS4SP473LTBS4SP473LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS3LTBS3LTB2HBFS3LTBS2LO3LTBS2LO3LTBS2LO3LTBS3LTBS3LTBS3LTBS2LO3GLO3LTBSS3LTB2CF2Hq1HS2LO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS3LTBS3CF'2HqS3CF'S3CF'S3LTBSS3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS3LTBSS2LO3LTBS2LO3LTBS2LO3LTBS3LTBS2NE1eSS2LO3GLO3LTBS3LTBS2LO3GLO3LTBS2LO3GLO3LTBS3LTBS2LO3GLO3LTB".
rewrite Z.pow2_bits_eqb by lia.
        destruct (Z.eqb_spec 6 i); [lia|]. apply Bool.andb_false_r. }
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; clear - RSP LO GLO; lia).
    assert (LTB : length (to_bytes (so_buf so)) = length (so_buf so)) by (unfold to_bytes; apply length_map).
    unfold file_cells in FC, EFC.
    unfold stdout_exit_flush. apply (implAM_rdso get_so). rewrite <- ESO.
    eapply implAM_evt. 2:{ intros ms' H; exact H. } cbv beta.
    carve_frame 16%nat ST.
    do 4 hstep.
    (* [comment removed for export] *)
    carve_frame 16%nat ST.
    hstep. hstep. fix_lit_store. do 5 hstep.
    do 3 hstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true.
    hstep.
    do 5 hstep.
    release_frame FR0 ST (bv_unsigned sp + -16).
    (* [comment removed for export] *)
    hstep. hstep. if_false.
    (* [comment removed for export] *)
    hstep. hstep. hstep. if_false.
    hstep. hstep. if_lit.
    hstep. hstep. hstep. if_lit.
    hstep. hstep. hstep. if_lit.
    (* [comment removed for export] *)
    hstep. hstep. hstep. if_false.
    hstep. hstep. if_lit.
    hstep. hstep.
    destruct (0 <? zlength (so_buf so)) eqn:CF.
    - (* [comment removed for export] *)
      pose proof (proj1 (Z.ltb_lt _ _) CF) as CF'.
      assert (ACT : so_active so = true).
      { destruct (so_active so) eqn:E; [reflexivity|]. exfalso. rewrite (INACT eq_refl) in CF'. unfold zlength in CF'. cbn in CF'. clear - CF'. lia. }
      rewrite ACT in FC |- *.
      hstep. if_cases Hq; zify_cond Hq. 1:{ exfalso. unfold zlength in *. clear - Hq CF'. lia. }
      do 4 hstep. hstep.
      rewrite (ret_pc_even _) by (destruct (so_first so); cbn; lia).
      replace (Z_to_bv 64 (if so_first so then 584256 else 581692) : word) with (Z_to_bv 64 (wfn_of (get_so s)) : word)
        by (rewrite <- ESO; reflexivity).
      apply evtF_done.
      eapply implAM_post_evt'.
      { eapply (stdout_writefn_spec get_so set_so get_set set_set) with (lo := lo) (S := 0) (s := []) (flags := flags) (mode := mode) (tail := tail) (canary := guard);
          [ rewrite <- ESO; exact ACT
          | unfold stdout_cells, wfn_of, lbf_of, file_cells; rewrite <- ESO; exact FC
          | exact FL64
          | rewrite <- ESO; eapply CB_prefix_bytes_at; [exact BUF| rewrite LTB; exact BUFP]
          | rewrite <- ESO; exact BUFL
          | apply bytes_at_nil; clear; lia
          | reflexivity | reflexivity | reflexivity
          | rewrite ESP; exact ST | rewrite ESP; unfold STDOUT_WRITE_DEPTH; clear - LO; lia | exact GLO
          | split; [exact GOT | exact GUARD] | exact MI
          | clear; lia | unfold zlength; cbn; clear; lia
          | left; reflexivity
          | rewrite ESP; eapply rng_sub'; [exact RSTK | clear - LO RSP; lia] | apply (rng0_use _ _ RG0); clear; lia | exact RIMG
          | rewrite ESP; clear - SP47; lia | unfold zlength; cbn; clear; lia ]. }   (* [comment removed for export] *)
      cbv beta. intros [] st2 ms2 PO2.
      destruct PO2 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2 & ->).
      rewrite ESP in MU2, ST2. unfold STDOUT_WRITE_DEPTH in MU2. rewrite <- ESO in FC2 |- *.
      rewrite (ret_pc_even 583372) by (cbn; lia).
      transport_after_call bsegs m1 m2 MU2 WM2.
      unfold stdout_cells, file_cells in FC2.
      (* [comment removed for export] *)
      hstep. hstep. hstep. if_lit.
      (* [comment removed for export] *)
      hstep. hstep. hstep. if_lit.
      hstep. hstep. if_lit.
      hstep. hstep. hstep. if_refl.
      hstep. hstep. hstep. if_lit.
      (* [comment removed for export] *)
      hstep. hstep. hstep. hstep.
      release_frame FR ST2 (bv_unsigned sp).
      apply evtF_done. unfold stdio_exit_post.
      do 15 eexists. exists (so_after so). eexists.
      split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI2|]. split; [exact ST2|].
      split; [reflexivity|].
      split.
      { unfold stdout_file. exists flags, mode, tail, bufbytes.
        unfold stdout_cells, wfn_of, lbf_of in FC2 |- *. cbn [so_active so_buf so_first so_lbf_nl so_after] in FC2 |- *.
        split; [exact FC2|]. split; [exact FL72|]. split; [exact BUF|]. split; [reflexivity|].
        split; [unfold zlength; cbn; clear; lia|]. intros X; discriminate X. }
      split; [reflexivity|].
      split; [exists eflags, emode, ee, ewend, etail; exact EFC|].
      destruct SSP2 as [GOT2 GUARD2]. split; [exact GOT2 | exact GUARD2].
    - (* [comment removed for export] *)
      pose proof (proj1 (Z.ltb_ge _ _) CF) as CF'.
      assert (E0 : so_buf so = []).
      { destruct (so_buf so); [reflexivity|]. exfalso. unfold zlength in CF'. cbn [length] in CF'. clear - CF'. lia. }
      rewrite E0 in *. unfold zlength. cbn [length Z.of_nat]. rewrite Z.add_0_r.
      unfold zlength in FC. cbn [length Z.of_nat] in FC. rewrite Z.add_0_r in FC.
      hstep. if_refl.
      hstep. hstep. hstep. if_lit.
      (* [comment removed for export] *)
      hstep. hstep. hstep. if_lit.
      hstep. hstep. if_lit.
      hstep. hstep. hstep. if_refl.
      hstep. hstep. hstep. if_lit.
      hstep. hstep. hstep. hstep.
      release_frame FR ST (bv_unsigned sp).
      apply evtF_done. apply implAM_ret. apply evtF_done. unfold stdio_exit_post.
      do 15 eexists. exists so. eexists.
      split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
      split; [rewrite ESO, set_get; reflexivity|].
      split.
      { unfold stdout_file. exists flags, mode, tail, bufbytes. rewrite E0. unfold zlength. cbn [length Z.of_nat]. rewrite Z.add_0_r.
        split; [exact FC|]. split; [exact FL72|]. split; [exact BUF|]. split; [reflexivity|].
        split; [clear; lia|]. intros _; reflexivity. }
      split; [exact E0|].
      split; [exists eflags, emode, ee, ewend, etail; exact EFC|].
      split; [exact GOT | exact GUARD].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End StdioExit.

(* [comment removed for export] *)
#[using="Type"] Theorem stdio_exit_proof_ps : stdio_exit_spec_stmt2 ps_so set_so_ps.
Proof.
  apply stdio_exit_proof.
  - intros s so. reflexivity.
  - intros s so so'. reflexivity.
  - intros [mm b f so]. reflexivity.
Qed.
End CANSEC2.
