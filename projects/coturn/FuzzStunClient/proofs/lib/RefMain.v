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
From OSSVerify.coturn.FuzzStunClient.images Require Import Plain.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Amb.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame Spec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import ShapeLaws.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import RefStartup RefMainEntry RefUsage RefOpenFail RefOpenFailBranch
  RefPilotOOM_defs RefPilotOOM RefReadBase RefReadStage RefWorld RefTargetPre RefRead0 SymPlanSoundA
  RefLeafWorld RefLeafDir RefHeader RefLeafBigFile RefTargetTop BaseUbsan RefLim.
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

Definition rsegs := Plain.M.loaded_segments.
Definition rpc := Plain.M.init_pc.
Definition rph := Plain.M.phdrs.

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
Definition K139ac (data : list byte) (fs0 : Fs) : TSet :=
  if (Z.of_nat (length data) <? 65536)%Z then t_body data fs0
  else t_alt2 (t_die msg_oom fs0) (t_body data fs0).

Lemma teq_opened : forall path data fs0,
  t_eq (t_alt2 (t_die (msg_cannot_open path) fs0)
               (t_alt2 (t_alt2 (t_die msg_oom fs0)
                  (t_alt2 (t_die msg_oom fs0) (t_alt2 (t_die msg_oom fs0) (K139ac data fs0))))
                  (t_alt2 (t_die msg_oom fs0) (K139ac data fs0))))
       (t_alt2 (t_die (msg_cannot_open path) fs0) (t_opened data fs0)).
Proof.
  intros path data fs0. eapply t_eq_trans; [apply teq_pilot|]. unfold t_opened, K139ac.
  destruct (Z.of_nat (length data) <? 65536)%Z; [apply t_eq_refl | apply teq_absorb3].
Qed.

Section FileExists.
  Context {AMB : Amb}.
  Context {AL : AllocLim}.
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
  (* [main_entry] takes the launch's own input, the mmap base and the entry point, and its
     uid/hwcap (RefStartup.v:65).  Same shape as RefPilotOOM.v:100-113, whose section this one feeds. *)
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
    - exact Vl.
    - rewrite Psp. symmetry. apply Z_to_bv_bv_unsigned.
    - unfold alloc_top, stack_max_size. rewrite Psp. lia.
    - unfold alloc_top, stack_max_size. rewrite Psp. lia.
  Qed.

  (* [p1] is [cat_argv_ptr (ed_top rdraw) av ev (in_execfn inp) 1] (RefMainEntry.v:135), so it
     takes [a0s path envv rdraw inp] and not [sp0], the form RefOpenFail.v:183 uses.
     [header_phase] (RefHeader.v:851) and [ref_big_file] (RefLeafBigFile.v:38) each take an
     [a_channel_reader = true] premise. *)
  Lemma after_malloc_main :
    after_malloc sp0 a0s path envv rdraw tid mbase fs0 stdin0 inp (K139ac fdata fs0).
  Proof.
    unfold after_malloc. intros R M VM mb gm sec cn area brkv mas Harea RP W MF VP VS.
    pose proof Hvsp as Hvsp'. destruct Hvsp' as (SPlo & SPhi & SPal).
    unfold sp_window_lo, sp_window_hi in SPlo, SPhi.
    pose proof (rp_b _ _ _ _ _ _ _ _ RP) as Hb. pose proof (rp_gm _ _ _ _ _ _ _ _ RP) as Hg.
    unfold K139ac. destruct (Z.ltb_spec0 (Z.of_nat (length fdata)) 65536) as [Hlt|Hge].
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
    realizes RSEGS (mkCfg (mkst regs0 (0x139e0 : word) mem0 (seg_rom RSEGS))
                          (with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp0 LIM (mkProcInputC [a0s; path] envv fs0 stdin0))))
             (t_alt2 (t_die (msg_cannot_open path) fs0) (t_opened fdata fs0)).
  Proof.
    eapply rz_conseq; [ | apply teq_opened ].
    replace (0x139e0 : word) with (Z_to_bv 64 0x139e0) by (apply bv_eq; reflexivity).
    (* Section lemmas are applied by [eapply] + [eassumption], never by a positional list: a
       section's discharged set is neither its header nor a text-level closure. *)
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

Section Entry.
  Context {AL : AllocLim}.

(* [comment removed for export] *)
Theorem ref_realizes_spec_lim : forall sp brk mbase rdraw inp,
  valid_entry (mkImage SRCM.loaded_segments SRCM.init_pc SRCM.phdrs) (mkEntry sp brk mbase rdraw) inp -> valid_input inp ->
  realizes SRCM.loaded_segments
    (init_config SRCM.loaded_segments SRCM.init_pc SRCM.phdrs sp brk mbase rdraw LIM inp)
    (spec (in_argv inp) (in_fs inp)).
Proof.
  intros sp brk mbase rdraw inp VE VI.
  pose proof (valid_input_va_size _ VI) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in VE.
  (* LPS 727298f3: [valid_entry]'s Sv48 form ends with the launch conjunct, and
     [valid_input] ([c0dd863a:theories/LinuxProcessSem/Run.v:4647-4659]) carries sixteen clauses, with
     [valid_launch] THIRTEENTH and the channel reader FOURTEENTH. *)
  destruct VE as (Hsp & Hbrk & Hmb & Hfit & Hlau).
  destruct VI as (Hva & Hve & Hfs & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hvl & Hcr & _ & _).
  change SRCM.loaded_segments with rsegs in *. change SRCM.init_pc with rpc. change SRCM.phdrs with rph.
  apply ref_startup; try assumption.
  intros tid regs mem Htid ME.
  (* Bridge (A).  [ref_startup]'s hand-off model carries the launch's vDSO draw
     ([with_vdso], as [Run.init_config] does); every consumer below is stated without it.  Over
     the image's own segments there is no vDSO text, so [VdsoBridge.realizes_with_vdso_no_text]
     discharges the draw at every pc.  ([with_tid] and [with_vdso] commute definitionally:
     VdsoCommute.with_tid_with_vdso.) *)
  rewrite VdsoCommute.with_tid_with_vdso.
  lazymatch goal with |- realizes ?s (mkCfg ?ms (with_vdso ?v ?m)) ?T =>
    change (realizes s (VdsoCommuteSys.cfg_with_vdso v (mkCfg ms m)) T) end.
  apply (VdsoBridge.realizes_with_vdso_no_text Plain.M.loaded_segments ltac:(reflexivity)).
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
End Entry.

(* [comment removed for export] *)
(* THE ASSEMBLY.
   [ref_realizes_spec_lim] proves the walk over the BINARY's own segment list and its own start
   state; [ref_spec_stmt] (BaseUbsan.v:21-26) asks for the RUN's, which differ in two places:
     the start CONFIGURATION  -> (B2) Common/Cfg/RomStable.realizes_run_init
     the segment INDEX        -> (B1) Common/RunSegTail.realizes_run_segments
   Bridge (A), the vDSO draw, is applied inside [ref_realizes_spec_lim], right after
   [ref_startup], over the image's own segments: its premise [vdso_text_seg segs = None] holds
   there and is FALSE over [run_segments], so it cannot be applied here.
   (B2) rewrites the configuration while the index is still the binary's, then (B1), which is
   generic in the configuration, moves the index.  Both ask [vdso_image segs = None], which
   [RomStable.vdso_image_none_of_no_text] derives from the closed [vdso_text_seg] computation. *)
Theorem ref_realizes_spec : ref_spec_stmt.
Proof.
  intros sp brk mb rnd inp VE VI.
  assert (Hnone : vdso_image SRCM.loaded_segments = None)
    by (apply RomStable.vdso_image_none_of_no_text; reflexivity).
  apply (RunSegTail.realizes_run_segments SRCM.loaded_segments inp sp mb _ _ Hnone).
  apply (RomStable.realizes_run_init SRCM.loaded_segments inp sp brk mb
           SRCM.init_pc SRCM.phdrs rnd source_alloc_limit _ Hnone).
  exact (@ref_realizes_spec_lim SrcLim sp brk mb rnd inp VE VI).
Qed.

(* [comment removed for export] *)
(* The source half of the two sanitizer tops (AsanTop, BothTop), in the form
   [Asan/AsanTopGlue.ref_spec_stmt_san] asks: over the RUN's segments, as [ref_spec_stmt], at
   the sanitizer budget.  Same assembly as [ref_realizes_spec]: (B2), then (B1), over
   [ref_realizes_spec_lim], which applies (A). *)
Theorem ref_realizes_spec_san : forall sp brk mb rnd inp,
  valid_entry (mkImage SRCM.loaded_segments SRCM.init_pc SRCM.phdrs) (mkEntry sp brk mb rnd) inp -> valid_input inp ->
  realizes (run_segments SRCM.loaded_segments inp sp mb)
    (init_config (run_segments SRCM.loaded_segments inp sp mb) SRCM.init_pc SRCM.phdrs sp brk mb rnd SanitizerBudgets.lim_source inp)
    (spec (in_argv inp) (in_fs inp)).
Proof.
  intros sp brk mb rnd inp VE VI.
  assert (Hnone : vdso_image SRCM.loaded_segments = None)
    by (apply RomStable.vdso_image_none_of_no_text; reflexivity).
  apply (RunSegTail.realizes_run_segments SRCM.loaded_segments inp sp mb _ _ Hnone).
  apply (RomStable.realizes_run_init SRCM.loaded_segments inp sp brk mb
           SRCM.init_pc SRCM.phdrs rnd SanitizerBudgets.lim_source _ Hnone).
  exact (@ref_realizes_spec_lim SanLim sp brk mb rnd inp VE VI).
Qed.
