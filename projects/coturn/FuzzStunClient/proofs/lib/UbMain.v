(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, the top applies the three bridges to the statement's run (VdsoBridge, RunSegTail, RomStable), main_entry takes the launch input, entry point, uid and hwcap, and the launch conjunct and channel reader come from the premises. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.coturn.FuzzStunClient.images Require Import Ubsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Amb.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame Spec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import ShapeLaws.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import UbStartup UbMainEntry UbUsage UbOpenFail UbOpenFailBranch
  UbPilotOOM_defs UbPilotOOM UbReadBase UbReadStage UbWorld UbTargetPre UbRead0 SymPlanSoundA
  UbLeafWorld UbLeafDir UbHeader UbLeafBigFile UbTargetTop BaseUbsan.
(* The three bridges to the statement's run (LPS 122da3c): (A) Common/VdsoBridge, (B1)
   Common/RunSegTail, (B2) Common/Cfg/RomStable.  Required, not imported, and used qualified. *)
From LinuxProcessSemantics.LinuxProcessSem Require VdsoCommute VdsoCommuteSys.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require VdsoBridge RunSegTail.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.Cfg Require RomStable.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFast.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastK.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastS.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastM.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SumWalkFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.in_list ::= in_list_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.peel ::= peel_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StoreOk.store_ok_peel ::= store_ok_peel_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.SumWalkTac.rdn_peel1 ::= rdn_peel1_fast.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Definition rsegs := Ubsan.M.loaded_segments.
Definition rpc := Ubsan.M.init_pc.
Definition rph := Ubsan.M.phdrs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ref_list_byte_eqb_eq : forall p q, list_byte_eqb p q = true <-> p = q.
Proof.
  induction p as [|a p IH]; destruct q as [|b q]; cbn; try (split; congruence).
  rewrite Bool.andb_true_iff, IH. unfold bv_eqb. rewrite Z.eqb_eq.
  split.
  - intros [H1 ->]. f_equal. apply bv_eq. exact H1.
  - intros H. injection H. intros -> ->. auto.
Qed.

(* [comment removed for export] *)
Lemma teq_pilot : forall A O K : TSet,
  t_eq (t_alt2 A (t_alt2 (t_alt2 O (t_alt2 O (t_alt2 O K))) (t_alt2 O K))) (t_alt2 A (t_alt2 O K)).
Proof. intros A O K tr. unfold t_alt2. tauto. Qed.

Lemma teq_absorb3 : forall A O B : TSet,
  t_eq (t_alt2 A (t_alt2 O (t_alt2 O B))) (t_alt2 A (t_alt2 O B)).
Proof. intros A O B tr. unfold t_alt2. tauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma in_rng_lit : forall (i base : Z) (len : Z),
  (0 <= base < 2 ^ 64)%Z -> (0 <= i < 2 ^ 64)%Z ->
  in_rng (Z_to_bv 64 i) (Z_to_bv 64 base) len <-> (base <= i < base + len)%Z.
Proof.
  intros i base len Hb Hi. unfold in_rng. rewrite !u64_lit by lia. tauto.
Qed.

Lemma read0_outside : forall (sp0 gm : word) (L i : Z),
  (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
  (0x58000 <= bv_unsigned gm)%Z -> (bv_unsigned gm + 69632 <= 2 ^ 47)%Z ->
  (0 <= L)%Z -> (0 <= i < 2 ^ 64)%Z ->
  ~ (bv_unsigned sp0 - 8388608 <= i < bv_unsigned sp0 - 128)%Z ->
  ~ (bv_unsigned gm + 32 <= i < bv_unsigned gm + 32 + L)%Z ->
  ~ (RSTAGE <= i < RSTAGE + 65536)%Z ->
  outside (Z_to_bv 64 i) (read_regions0 sp0 gm L).
Proof.
  intros sp0 gm L i Hsp Hg1 Hg2 HL Hi N1 N2 N3. unfold read_regions0. cbn [outside].
  rewrite !in_rng_lit by (unfold RSTAGE; lia). repeat split; lia.
Qed.

Lemma world0_after_read0 : forall (sp0 p1 gm : word) (content : list byte)
    (R0 : bvmap 5 word) (M0 : word -> option byte) (R : bvmap 5 word) (M : word -> option byte)
    (area brkv mas tid : Z),
  (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
  (area + 4096 <= bv_unsigned sp0 - 8388608)%Z -> (bv_unsigned gm + 69632 <= bv_unsigned sp0 - 8388608)%Z ->
  read_post0 sp0 p1 gm content R0 M0 R M ->
  (Z.of_nat (length content) < 65536)%Z ->
  world0 area (bv_unsigned gm) brkv mas tid M0 ->
  world0 area (bv_unsigned gm) brkv mas tid M.
Proof.
  intros sp0 p1 gm content R0 M0 R M area brkv mas tid Hsp Hat Hgt RQ HL W.
  pose proof (w_area_rng _ _ _ _ _ _ W) as Har. pose proof (w_gm_rng _ _ _ _ _ _ W) as Hgr.
  pose proof (w_area_img _ _ _ _ _ _ W) as Hai.
  pose proof (w_disj _ _ _ _ _ _ W) as Hdj. pose proof (w_grp_def _ _ _ _ _ _ W) as Hdef.
  pose proof (rq_frame _ _ _ _ _ _ _ _ RQ) as Hfr. pose proof (rq_grows _ _ _ _ _ _ _ _ RQ) as Hgw.
  eapply world0_frame; [exact W | |].
  - intros i Hi. apply Hfr. unfold world0_fp, READ_STAGE in Hi.
    apply read0_outside; unfold RSTAGE; lia.
  - intros i Hi. apply Hgw. apply Hdef. exact Hi.
Qed.

Lemma main_frame_after_read0 : forall (sp0 p1 gm : word) (content : list byte)
    (R0 : bvmap 5 word) (M0 : word -> option byte) (R : bvmap 5 word) (M : word -> option byte)
    (area brkv mas tid : Z),
  (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
  (bv_unsigned gm + 69632 <= bv_unsigned sp0 - 8388608)%Z ->
  read_post0 sp0 p1 gm content R0 M0 R M ->
  (Z.of_nat (length content) < 65536)%Z ->
  world0 area (bv_unsigned gm) brkv mas tid M0 ->
  main_frame (bv_unsigned sp0) M0 -> main_frame (bv_unsigned sp0) M.
Proof.
  intros sp0 p1 gm content R0 M0 R M area brkv mas tid Hsp Hgt RQ HL W MF.
  pose proof (w_gm_rng _ _ _ _ _ _ W) as Hgr.
  pose proof (rq_frame _ _ _ _ _ _ _ _ RQ) as Hfr.
  eapply main_frame_frame; [lia | lia | | exact MF].
  intros i Hi. apply Hfr. apply read0_outside; unfold RSTAGE; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition K13a8c (data : list byte) (fs0 : Fs) : TSet :=
  if (Z.of_nat (length data) <? 65536)%Z then t_body data fs0
  else t_alt2 (t_die msg_oom fs0) (t_body data fs0).

Lemma teq_opened : forall path data fs0,
  t_eq (t_alt2 (t_die (msg_cannot_open path) fs0)
               (t_alt2 (t_alt2 (t_die msg_oom fs0)
                  (t_alt2 (t_die msg_oom fs0) (t_alt2 (t_die msg_oom fs0) (K13a8c data fs0))))
                  (t_alt2 (t_die msg_oom fs0) (K13a8c data fs0))))
       (t_alt2 (t_die (msg_cannot_open path) fs0) (t_opened data fs0)).
Proof.
  intros path data fs0. eapply t_eq_trans; [apply teq_pilot|]. unfold t_opened, K13a8c.
  destruct (Z.of_nat (length data) <? 65536)%Z; [apply t_eq_refl | apply teq_absorb3].
Qed.

Section FileExists.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : InputStream.
  Variable fdata : list byte.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  (* MECHANICAL TWIN of RefMain.v's Section FileExists; UbPilotOOM's section header declares exactly
     the variables RefPilotOOM's does.  [main_entry] takes 12 arguments at UbStartup, [p1] is
     [cat_argv_ptr (ed_top rdraw) av ev (in_execfn inp) 1] so it takes [a0s path envv rdraw inp]
     and not [sp0], and [header_phase] and [ref_big_file] each take an
     [a_channel_reader = true] premise. *)
  Variable inp : ProcInput.
  Variable entry : word.
  Variables uid hw : word.
  Hypothesis ME : main_entry inp mbase entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0.
  Hypothesis Hbrk : valid_brk RSEGS brk.
  Hypothesis Hfile : fs_lookup fs0 path = Some fdata.
  Hypothesis Hpne : path <> [].
  Hypothesis Hpnd : path <> dot_path.
  Hypothesis Hplen : (length path <= 4095)%nat.
  Hypothesis Hrdr0 : a_channel_reader = true.

  Lemma target_vm_of_small : forall (VM : VmMaps) (p1 mb gm sec cn : word) (area : Z) R M,
    area = (bv_unsigned mb + 4096)%Z -> read_pre sp0 p1 mb gm sec cn R M ->
    vm_pre VM sp0 mb gm -> vm_small sp0 mbase VM gm ->
    target_vm (bv_unsigned sp0) (bv_unsigned gm) area VM.
  Proof.
    intros VM p1 mb gm sec cn area R M Harea RP
           (Pr & Psp & Pl & Ph & Pf & Pn & Plive & (p & Pin & Pne & Plo & Phi) & Pseps) (Vr & Vl & Vn & Vin & Vf & Vs).
    pose proof (rp_b _ _ _ _ _ _ _ _ RP) as Hb. pose proof (rp_gm _ _ _ _ _ _ _ _ RP) as Hg.
    constructor.
    - (* both ledgers are the launch's [init_reserved]; [vm_pre] states it at [vm_init_sp VM] *)
      rewrite Psp. exact Pr.
    - rewrite Z_to_bv_bv_unsigned. exact Vin.
    - exists (fst p), (snd p). destruct p as [lo sz]. cbn [fst snd] in *. split; [exact Pin|]. lia.
    - exact Vn.
    - exact Vf.
    - exact Vs.
    - rewrite Vl. unfold LIM, target_alloc_limit. lia.
    - rewrite Psp. symmetry. apply Z_to_bv_bv_unsigned.
    - unfold alloc_top, stack_max_size. rewrite Psp. lia.
    - unfold alloc_top, stack_max_size. rewrite Psp. lia.
  Qed.

  Lemma after_malloc_main :
    after_malloc sp0 a0s path envv rdraw tid mbase fs0 stdin0 inp (K13a8c fdata fs0).
  Proof.
    unfold after_malloc. intros R M VM mb gm sec cn area brkv mas Harea RP W MF VP VS.
    pose proof Hvsp as Hvsp'. destruct Hvsp' as (SPlo & SPhi & SPal).
    unfold sp_window_lo, sp_window_hi in SPlo, SPhi.
    pose proof (rp_b _ _ _ _ _ _ _ _ RP) as Hb. pose proof (rp_gm _ _ _ _ _ _ _ _ RP) as Hg.
    unfold K13a8c. destruct (Z.ltb_spec0 (Z.of_nat (length fdata)) 65536) as [Hlt|Hge].
    - (* [comment removed for export] *)
      eapply read_k0; try eassumption.
      intros R' M' RQ.
      pose proof (target_vm_of_small VM (p1 a0s path envv rdraw inp) mb gm sec cn area R M Harea RP VP VS) as TV.
      apply (header_phase sp0 (p1 a0s path envv rdraw inp) gm tid area brkv mas fdata VM stdin0 fs0 R M R' M' Hvsp Hrdr0 RQ).
      + eapply world0_after_read0; [ | | | exact RQ | exact Hlt | exact W]; lia.
      + eapply main_frame_after_read0; [ | | exact RQ | exact Hlt | exact W | exact MF]; lia.
      + exact Hlt.
      + exact TV.
      + intros R'' M'' TP.
        exact (target_phase_top (bv_unsigned sp0) (bv_unsigned gm) area brkv mas (bv_unsigned tid)
                 fdata R'' M'' VM (model_post VM stdin0 fs0 tid) TP TV
                 (SPSA.std_model_mk VM stdin0 fs0 (Some tid) None Hrdr0)).
    - (* [comment removed for export] *)
      apply (ref_big_file sp0 (p1 a0s path envv rdraw inp) mb gm sec cn R M area brkv mas VM path fdata stdin0 fs0 tid
               Hfile ltac:(lia) Harea RP W MF VP Hrdr0).
  Qed.

  Theorem ref_file_exists :
    realizes RSEGS (mkCfg (mkst regs0 (0x13ac0 : word) mem0 (seg_rom RSEGS))
                          (with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp0 LIM (mkProcInputC [a0s; path] envv fs0 stdin0))))
             (t_alt2 (t_die (msg_cannot_open path) fs0) (t_opened fdata fs0)).
  Proof.
    eapply rz_conseq; [ | apply teq_opened ].
    replace (0x13ac0 : word) with (Z_to_bv 64 0x13ac0) by (apply bv_eq; reflexivity).
    (* Section lemmas by [eapply] + [eassumption], never a positional list: a section's
       discharged set is neither its header nor a text-level closure. *)
    eapply oom_pilot; try eassumption.
    - eapply open_err_branch_cannot_open; eassumption.
    - eapply brk_ok_sem; try eassumption.
      apply after_malloc_main.
    - eapply mmap_ok_sem; try eassumption.
      apply after_malloc_main.
  Qed.
End FileExists.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem ub_realizes_spec : ub_spec_stmt.
Proof.
  unfold ub_spec_stmt. intros sp brk mbase rdraw inp VE VI.
  (* The assembly, as in RefMain.
     (B2) rewrites the start configuration while the index is still the binary's, then (B1),
     generic in the configuration, moves the index.  Bridge (A), the vDSO draw, is applied
     below, right after [ref_startup], over the image's own segments, where its premise
     [vdso_text_seg segs = None] holds; it is false over [run_segments]. *)
  assert (Hnone : vdso_image UBM.loaded_segments = None)
    by (apply RomStable.vdso_image_none_of_no_text; reflexivity).
  apply (RunSegTail.realizes_run_segments UBM.loaded_segments inp sp mbase _ _ Hnone).
  apply (RomStable.realizes_run_init UBM.loaded_segments inp sp brk mbase
           UBM.init_pc UBM.phdrs rdraw target_alloc_limit _ Hnone).
  pose proof (valid_input_va_size _ VI) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in VE.
  (* LPS 727298f3: [valid_entry]'s Sv48 form ends with the launch conjunct, and
     [valid_input] ([c0dd863a:theories/LinuxProcessSem/Run.v:4647-4659]) carries sixteen clauses, with
     [valid_launch] THIRTEENTH and the channel reader FOURTEENTH. *)
  destruct VE as (Hsp & Hbrk & Hmb & Hfit & Hlau).
  destruct VI as (Hva & Hve & Hfs & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hvl & Hcr & _ & _).
  change UBM.loaded_segments with rsegs in *. change UBM.init_pc with rpc. change UBM.phdrs with rph.
  change target_alloc_limit with LIM.
  apply ref_startup; try assumption.
  intros tid regs mem Htid ME.
  (* Bridge (A): see RefMain.ref_realizes_spec_lim. *)
  rewrite VdsoCommute.with_tid_with_vdso.
  lazymatch goal with |- realizes ?s (mkCfg ?ms (with_vdso ?v ?m)) ?T =>
    change (realizes s (VdsoCommuteSys.cfg_with_vdso v (mkCfg ms m)) T) end.
  apply (VdsoBridge.realizes_with_vdso_no_text Ubsan.M.loaded_segments ltac:(reflexivity)).
  (* [comment removed for export] *)
  rewrite (init_model_of _ _ _ _ _ inp).
  (* the launch's channel reader, as the Amb the consumers read it from (Amb.v:59) *)
  assert (Hrdr0 : @a_channel_reader (amb_of inp) = true) by exact Hcr.
  set (AMB := amb_of inp) in *. clearbody AMB.
  set (argv := in_argv inp) in *. set (envp := in_envp inp) in *.
  set (fs0 := in_fs inp) in *. set (stdin0 := in_stdin inp) in *.
  clearbody argv envp fs0 stdin0.
  (* Section lemmas by [eapply] and [eassumption], never a positional list (see RefLeafDir). *)
  destruct argv as [|a0s [|path [|x l]]].
  - eapply ref_usage_w; try eassumption; cbn; lia.
  - eapply ref_usage_w; try eassumption; cbn; lia.
  - cbn [spec].
    destruct (Nat.leb_spec0 4096 (length path)) as [Hlong|Hshort].
    + eapply ref_open_fail_toolong_w; eassumption.
    + destruct (list_byte_eqb path []) eqn:Hemp.
      * apply ref_list_byte_eqb_eq in Hemp.
        eapply ref_open_fail_empty_w; eassumption.
      * assert (Hne : path <> []) by (intros E; apply ref_list_byte_eqb_eq in E; rewrite E in Hemp; discriminate).
        destruct (list_byte_eqb path dot_path) eqn:Hdot.
        -- apply ref_list_byte_eqb_eq in Hdot. rewrite Hdot in *.
           eapply (ref_dir_path cannot_open_branch); eassumption.
        -- assert (Hnd : path <> dot_path)
             by (intros E; apply ref_list_byte_eqb_eq in E; rewrite E in Hdot; discriminate).
           destruct (fs_lookup fs0 path) as [data|] eqn:Hlk.
           ++ eapply ref_file_exists with (fdata := data); try eassumption; lia.
           ++ eapply ref_open_fail_absent_w; try eassumption; lia.
  - eapply ref_usage_w; try eassumption; cbn; lia.
Qed.
