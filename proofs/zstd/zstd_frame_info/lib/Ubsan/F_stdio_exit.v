(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac ITree Nodes Decode SysStep.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import MonadX.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim Monad Stdio Prog.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import F_syscalls StdioFiles Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Common Require Import F_fmt_fp_lib.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import F_stdio_write F_stdout_write F_fwritex_stdout.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import UImg.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma bv_eqb_refl : forall {n} (x : bv n), bv_eqb x x = true.
Proof. intros n x. unfold bv_eqb. apply Z.eqb_refl. Qed.

Ltac if_refl :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if bv_eqb ?x ?x then _ else _) _ _ _ _) => rewrite (bv_eqb_refl x); cbv iota
  end.

Ltac if_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
  end.

(* [comment removed for export] *)
Lemma impl_post_evt' : forall {R} (t : itree node R) (Q Q' : R -> machine_state -> Prop) ms,
  impl usegs (at_node usegs) t Q ms -> (forall r ms', Q r ms' -> evt usegs (Q' r) ms') ->
  impl usegs (at_node usegs) t Q' ms.
Proof.
  induction t as [r|n k IH]; intros Q Q' ms H HQ; cbn in *.
  - eapply evt_cut; [exact H|]. intros ms' H'. apply HQ. exact H'.
  - eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; eauto.
Qed.
Lemma implM_post_evt' : forall {St A} (c : M St A) s Q Q' ms,
  implM usegs c s Q ms -> (forall a s' ms', Q a s' ms' -> evt usegs (Q' a s') ms') ->
  implM usegs c s Q' ms.
Proof.
  intros St A c s Q Q' ms H HQ. unfold implM in *. eapply impl_post_evt'; [exact H|].
  intros [|[a s']] ms' H'; cbn in *; [apply evt_done; exact I| apply HQ; exact H'].
Qed.

Section StdioExit.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Hypothesis get_set : forall s so, get_so (set_so so s) = so.
  Hypothesis set_set : forall s so so', set_so so' (set_so so s) = set_so so' s.
  Hypothesis set_get : forall s, set_so (get_so s) s = s.

  #[using="get_set set_set set_get"] Theorem stdio_exit_proof : stdio_exit_spec_stmt get_so set_so.
  Proof.
    unfold stdio_exit_spec_stmt. intros until tm1. intros ST LIBC OFL SIN SOUT SERR SOF SEF GOT GUARD MI -> LO GLO SP47.
    unfold GLOBALS_TOP, got_ssp, ssp_guard in *.
    destruct SOF as (flags & mode & tail & bufbytes & FC & FL72 & BUF & BUFP & BUFL & INACT).
    destruct SEF as (eflags & emode & ee & ewend & etail & EFC).
    change usegs with usegs in *.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    remember (get_so s) as so eqn:ESO.
    pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp); (RSTDOUT, 0x1ded0); (RSTDOUT_BUF, 0x4eb00)]%Z m) as MU.
    pose proof (wmono_refl usegs m) as WM.
    assert (FL64 : Z.land (bv_unsigned flags) 64 = 0).
    { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
      destruct (Z.eq_dec i 6) as [->|NE].
      - pose proof (f_equal (fun z => Z.testbit z 6) FL72) as T. cbn beta in T. rewrite Z.land_spec, Z.bits_0 in T.
        change (Z.testbit 64 6) with true in T |- *. change (Z.testbit 72 6) with true in T. exact T.
      - change 64 with (2^6). Local Ltac2 Set LiaHints.tbl := fun () => "01_0?12428134302.11015685060272.95 18589389294.90 18589389294.93 19006120615.93 20433961190.84 2172651747.2   22856607214.90 22856607214.93 22961942245.0  25076088621.11125435258127.95 25566553219.93 26494647592.90 26494647592.93 26494647592.95 27132802181.11131399144472.88 31401241662.10831523060718.90 31523060718.93 32027975233.0  32600174396.90 33510054780.86 34029742981.11034171235310.90 34171235310.93 3439967214.90  3439967214.93  3523399062.5   38214534392.1113830406688.89  3834310178.109 38761854802.93 38761854802.95 39941652000.87 39949608786.93 39949608786.95 40201484047.11840201484047.93 40201484047.98 42831019478.93 42831019478.95 43035628988.3  43061776187.82 43104399792.93 43607580549.11143863873618.93 43863873618.95 43892577675.11144395637586.93 44395637586.95 45075744594.93 45075744594.95 45221239098.90 45221239098.93 47935039314.93 47935039314.95 4866047897.93  49270498929.90 49952102226.93 49952102226.95 5180980284.93  52136437230.90 52136437230.93 52712884706.11053480771973.11053607217270.92 54164510851.11654164510851.90 54164510851.96 56033189458.93 56033189458.95 56337473341.90 56582466030.90 56582466030.93 57228544494.90 57228544494.93 57622410744.11158135773316.85 59178106163.95 59308587280.3  59310859210.1  59310859210.2  59576971633.90 59624177333.0  59959501701.11160128159214.90 60128159214.93 60262524490.90 60729825738.90 61581656914.93 61581656914.95 6253858422.92  62583080755.93 63135048575.0  63779719325.95 63792152522.83 63967133241.82 64955098885.11165080049157.11066070781104.11166557938821.11066747928658.93 66747928658.95 67081926311.90 67943285742.90 67943285742.93 68037941509.11068094715463.87 7835420037.111 00000100900E00Q00V00[00a00m01901:01F01K01P01U01Z01_01`01e01j02602B02C02K02P02\02h03403@03L03X03d03l04404@04L04T04`04l05105605;05E05O05S05[05c05o06;06G06L06X06d07007<07F07P07\07h07m08208>08J08R08^08j08k09709<09A09F09K09W09c0:00:<0:H0:T0:`0:m0;50;:0;B0;G0;L0;Q0;R0;^0;j0<60<;0<@0<L0<X0<]0<b0<c0<h0<n0<o0=;0=G0=L0=X0=d0>00>50>A0>M0>Y0>^0>jFS3LTB2HBS2LO3GLO3LTBS2LO3GLO3LTBS3LTBS3LTBS4SP47S2LO3GLO3LTBS2LO3GLO3LTBSS2LO3GLO3LTBS3LTBS3LTBS3LTBS3LTBS3LTBFS3LTBS3LTBS2LO3GLO3LTBS2LO3GLO3LTBSS3LTB2HBS3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3RSPS2LO3GLO3LTBS2LO3LTBS2LO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS3LTBS3LTBS3LTBS4SP473LTBS4SP473LTBS2LOS2LO3LTBS3LTB2HBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS4SP473LTBS4SP473LTBS2LO3GLO3LTBS2LO3GLO3LTBS3LTBS3LTBS2LO3GLO3LTBS2LO3GLO3LTBS3LTB2HBS2LO3GLO3LTBS2LO3GLO3LTBFS2LO3GLO3LTBS3LTBS3LTBS3LTBS3LTBS2LO3GLO3LTBS2LO3GLO3LTBS4BUFL3LTB2CFS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS3LTB2CF2Hq1HS2LO3LTBS3LTBS3CF'2HqS3CF'S3CF'S3LTBSS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS3LTBS3LTBS2LO3GLO3LTBS2LO3GLO3LTBS3LTBS3LTBSS3LTBS2NE1eSS2LO3GLO3LTBS2LO3GLO3LTBS3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS3LTBS2LO3GLO3LTBS2LO3GLO3LTBS2LO3GLO3LTBS3LTBS2LO3GLO3LTB".
rewrite Z.pow2_bits_eqb by lia.
        destruct (Z.eqb_spec 6 i); [lia|]. apply Bool.andb_false_r. }
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; clear - RSP LO GLO; lia).
    assert (LTB : length (to_bytes (so_buf so)) = length (so_buf so)) by (unfold to_bytes; apply length_map).
    unfold file_cells in FC, EFC.
    unfold implM, stdout_exit_flush. apply (implM_rdso usegs get_so). rewrite <- ESO.
    eapply (implM_evt usegs). 2:{ intros ms' H; exact H. } cbv beta.
    carve_frame 16%nat ST.
    do 4 step.
    (* [comment removed for export] *)
    carve_frame 16%nat ST.
    step. step. fix_lit_store. do 5 step.
    do 3 step. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true.
    step.
    do 5 step.
    release_frame FR0 ST (bv_unsigned sp + -16).
    (* [comment removed for export] *)
    step. step. if_false.
    step. step. step. if_true.
    (* [comment removed for export] *)
    step. step. step. if_false.
    step. step. if_lit.
    step. step.
    destruct (0 <? zlength (so_buf so)) eqn:CF.
    - (* [comment removed for export] *)
      pose proof (proj1 (Z.ltb_lt _ _) CF) as CF'.
      assert (ACT : so_active so = true).
      { destruct (so_active so) eqn:E; [reflexivity|]. exfalso. rewrite (INACT eq_refl) in CF'. unfold zlength in CF'. cbn in CF'. clear - CF'. lia. }
      rewrite ACT in FC |- *.
      step. if_cases Hq; zify_cond Hq. 1:{ exfalso. unfold zlength in *. clear - Hq CF'. lia. }
      do 4 step. step.
      rewrite (ret_pc_even _) by (destruct (so_first so); cbn; lia).
      replace (Z_to_bv 64 (if so_first so then 92124 else 91716) : word) with (Z_to_bv 64 (wfn_of (get_so s)) : word)
        by (rewrite <- ESO; reflexivity).
      apply evt_done.
      eapply implM_post_evt'.
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
          | rewrite ESP; clear - SP47; lia | unfold zlength; cbn; clear; lia
          | left; reflexivity ]. }
      cbv beta. intros [] st2 ms2 PO2.
      destruct PO2 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2 & ->).
      rewrite ESP in MU2, ST2. unfold STDOUT_WRITE_DEPTH in MU2. rewrite <- ESO in FC2 |- *.
      rewrite (ret_pc_even 91364) by (cbn; lia).
      transport_after_call usegs m1 m2 MU2 WM2.
      unfold stdout_cells, file_cells in FC2.
      (* [comment removed for export] *)
      step. step. step. if_lit.
      (* [comment removed for export] *)
      step. step. step. if_lit.
      step. step. if_lit.
      step. step. step. if_refl.
      step. step. step. if_lit.
      (* [comment removed for export] *)
      step. step. step. step.
      release_frame FR ST2 (bv_unsigned sp).
      apply evt_done. unfold stdio_exit_post.
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
      destruct SSP2 as [GOT2 GUARD2]. change usegs with usegs in GOT2, GUARD2. split; [exact GOT2 | exact GUARD2].
    - (* [comment removed for export] *)
      pose proof (proj1 (Z.ltb_ge _ _) CF) as CF'.
      assert (E0 : so_buf so = []).
      { destruct (so_buf so); [reflexivity|]. exfalso. unfold zlength in CF'. cbn [length] in CF'. clear - CF'. lia. }
      rewrite E0 in *. unfold zlength. cbn [length Z.of_nat]. rewrite Z.add_0_r.
      unfold zlength in FC. cbn [length Z.of_nat] in FC. rewrite Z.add_0_r in FC.
      step. if_refl.
      step. step. step. if_lit.
      (* [comment removed for export] *)
      step. step. step. if_lit.
      step. step. if_lit.
      step. step. step. if_refl.
      step. step. step. if_lit.
      step. step. step. step.
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. apply evt_done. unfold stdio_exit_post.
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
Theorem stdio_exit_proof_ps : stdio_exit_spec_stmt ps_so set_so_ps.
Proof.
  apply stdio_exit_proof.
  - intros s so. reflexivity.
  - intros s so so'. reflexivity.
  - intros [mm b f so]. reflexivity.
Qed.
