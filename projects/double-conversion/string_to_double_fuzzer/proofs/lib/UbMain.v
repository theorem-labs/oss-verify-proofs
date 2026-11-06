(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ModelAmb.
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgU.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import UbStartupDefs.   (* [comment removed for export] *)
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Frame
  Spec ShapeLaws UbStartup UbMainEntry
  UbPilotOOM_defs UbPilotOOM UbReadBase UbReadStage UbWorld UbTargetPre UbTargetPreK UbRead0
  UbSymPlanSoundA UbTargetCover.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import UbLeafWorld UbLeafHeader UbLeafBigFile UbLeafDir.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)


Definition rsegs := ImgU.M.loaded_segments.
Definition rpc := ImgU.M.init_pc.
Definition rph := ImgU.M.phdrs.

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
  (0xe6000 <= bv_unsigned gm)%Z -> (bv_unsigned gm + 69632 <= bv_unsigned sp0 - 8388608)%Z ->
  (0 <= L)%Z -> (0 <= i < 2 ^ 64)%Z ->
  ~ (bv_unsigned sp0 - 8388608 <= i < bv_unsigned sp0 - 128)%Z ->
  ~ (STAGE <= i < STAGE + 65536)%Z ->
  ~ (bv_unsigned gm + 32 <= i < bv_unsigned gm + 32 + L)%Z ->
  outside (Z_to_bv 64 i) (read_regions0 sp0 gm L).
Proof.
  intros sp0 gm L i Hsp Hg1 Hg2 HL Hi N1 NS N2. unfold read_regions0. cbn [outside]. unfold STAGE in *.
  rewrite !in_rng_lit by lia. repeat split; lia.
Qed.

Lemma world0_after_read0 : forall (sp0 p1 gm : word) (content : list byte)
    (R0 : bvmap 5 word) (M0 : word -> option byte) (R : bvmap 5 word) (M : word -> option byte)
    (area brkv mas tid sec : Z),
  (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
  read_post0 sp0 p1 gm content R0 M0 R M ->
  (Z.of_nat (length content) < 65536)%Z ->
  world0 (bv_unsigned sp0) area (bv_unsigned gm) brkv mas tid sec M0 ->
  world0 (bv_unsigned sp0) area (bv_unsigned gm) brkv mas tid sec M.
Proof.
  intros sp0 p1 gm content R0 M0 R M area brkv mas tid sec Hsp RQ HL W.
  pose proof (w_area_rng _ _ _ _ _ _ _ _ W) as Har. pose proof (w_gm_rng _ _ _ _ _ _ _ _ W) as Hgr.
  pose proof (w_disj _ _ _ _ _ _ _ _ W) as Hdj. pose proof (w_grp_def _ _ _ _ _ _ _ _ W) as Hdef.
  pose proof (w_area_img _ _ _ _ _ _ _ _ W) as Hai.
  pose proof (rq_frame _ _ _ _ _ _ _ _ RQ) as Hfr. pose proof (rq_grows _ _ _ _ _ _ _ _ RQ) as Hgw.
  eapply world0_frame; [exact W | |].
  - intros i Hi. apply Hfr. unfold world0_fp in Hi.
    apply read0_outside; unfold STAGE; lia.
  - intros i Hi. apply Hgw. apply Hdef. exact Hi.
Qed.

Lemma main_frame_after_read0 : forall (sp0 p1 gm : word) (content : list byte)
    (R0 : bvmap 5 word) (M0 : word -> option byte) (R : bvmap 5 word) (M : word -> option byte)
    (area brkv mas tid sec : Z),
  (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z ->
  read_post0 sp0 p1 gm content R0 M0 R M ->
  (Z.of_nat (length content) < 65536)%Z ->
  world0 (bv_unsigned sp0) area (bv_unsigned gm) brkv mas tid sec M0 ->
  main_frame (bv_unsigned sp0) M0 -> main_frame (bv_unsigned sp0) M.
Proof.
  intros sp0 p1 gm content R0 M0 R M area brkv mas tid sec Hsp RQ HL W MF.
  pose proof (w_gm_rng _ _ _ _ _ _ _ _ W) as Hgr.
  pose proof (rq_frame _ _ _ _ _ _ _ _ RQ) as Hfr.
  eapply main_frame_frame; [lia | lia | | exact MF].
  intros i Hi. apply Hfr. apply read0_outside; unfold STAGE; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition K32608 (data : list byte) (fs0 : Fs) : TSet :=
  if (Z.of_nat (length data) <? 65536)%Z then t_body data fs0
  else t_alt2 (t_die msg_oom fs0) (t_body data fs0).

Lemma teq_opened : forall path data fs0,
  t_eq (t_alt2 (t_die (msg_cannot_open path) fs0)
               (t_alt2 (t_alt2 (t_die msg_oom fs0)
                  (t_alt2 (t_die msg_oom fs0) (t_alt2 (t_die msg_oom fs0) (K32608 data fs0))))
                  (t_alt2 (t_die msg_oom fs0) (K32608 data fs0))))
       (t_alt2 (t_die (msg_cannot_open path) fs0) (t_opened data fs0)).
Proof.
  intros path data fs0. eapply t_eq_trans; [apply teq_pilot|]. unfold t_opened, K32608.
  destruct (Z.of_nat (length data) <? 65536)%Z; [apply t_eq_refl | apply teq_absorb3].
Qed.

(* [comment removed for export] *)
Definition target_phase_stmt : Prop :=
  forall (sp0 gm area brkv mas tid sec : Z) (content : list byte)
         (R : bvmap 5 word) (M : word -> option byte) (VM : VmMaps) (model : Model),
    target_pre sp0 gm area brkv mas tid sec content R M -> target_vm sp0 gm area VM -> SPSA.std_model VM model ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x32904) M (seg_rom RSEGS)) model) (t_target content (m_fs model)).

Definition target_phase_k_stmt : Prop :=
  forall k : Z, (1 <= k <= 10)%Z ->
  forall (sp0 B area brkv mas tid sec : Z) (content : list byte)
         (R : bvmap 5 word) (M : word -> option byte) (VM : VmMaps) (model : Model),
    target_pre_k k sp0 B area brkv mas tid sec content R M -> target_vm_k k sp0 B area VM -> SPSA.std_model VM model ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x32904) M (seg_rom RSEGS)) model) (t_target content (m_fs model)).

(* [comment removed for export] *)
Definition usage_stmt : Prop :=
  forall (sp0 : word) (av envv : list (list byte)) (uid hw : word) (rdraw : EntryDraw) (tid : word)
         (regs0 : bvmap 5 word) (mem0 : word -> option byte) (brk mbase : word) (fs0 : Fs) (stdin0 : AmbIn) (lim : Z),
    valid_argv av -> valid_envp envv -> valid_sp sp0 -> entry_stack_fits sp0 av envv -> (0 < bv_unsigned tid < 2 ^ 22)%Z ->
    main_entry sp0 av envv uid hw rdraw tid regs0 mem0 -> length av <> 2%nat ->
    realizes RSEGS (mkCfg (mkst regs0 (0x32634 : word) mem0 (seg_rom RSEGS))
                          (with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp0 lim (mkProcInputA av envv fs0 stdin0))))
             (t_die (msg_usage (hd [] av)) fs0).

(* [comment removed for export] *)
Definition open_fail_stmt : Prop :=
  forall (sp0 : word) (a0s path : list byte) (envv : list (list byte)) (uid hw : word) (rdraw : EntryDraw) (tid : word)
         (regs0 : bvmap 5 word) (mem0 : word -> option byte) (brk mbase : word) (fs0 : Fs) (stdin0 : AmbIn) (lim : Z),
    valid_argv [a0s; path] -> valid_envp envv -> valid_sp sp0 -> entry_stack_fits sp0 [a0s; path] envv ->
    (0 < bv_unsigned tid < 2 ^ 22)%Z ->
    main_entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0 ->
    ((4096 <= length path)%nat
     \/ path = []
     \/ ((length path <= 4095)%nat /\ path <> [] /\ path_has_slash path = false /\ path_is_dirref path = false
         /\ fs_lookup fs0 path = None)) ->
    realizes RSEGS (mkCfg (mkst regs0 (0x32634 : word) mem0 (seg_rom RSEGS))
                          (with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp0 lim (mkProcInputA [a0s; path] envv fs0 stdin0))))
             (t_die (msg_cannot_open path) fs0).

(* [comment removed for export] *)
Definition open_err_stmt : Prop :=
  forall (sp0 : word) (a0s path : list byte) (envv : list (list byte)) (uid hw : word) (rdraw : EntryDraw) (tid : word)
         (regs0 : bvmap 5 word) (mem0 : word -> option byte) (brk mbase : word) (fs0 : Fs) (stdin0 : AmbIn),
    valid_argv [a0s; path] -> valid_envp envv -> valid_sp sp0 -> entry_stack_fits sp0 [a0s; path] envv ->
    main_entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0 ->
    open_err_branch sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 (t_die (msg_cannot_open path) fs0).

Section FileExists.
  Hypothesis TPH : target_phase_stmt.
  Hypothesis TPKH : target_phase_k_stmt.
  Hypothesis OEH : open_err_stmt.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable uid : word.   (* [comment removed for export] *)
  Variable hw : word.    (* [comment removed for export] *)
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : AmbIn.
  Variable fdata : list byte.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Hfits : entry_stack_fits sp0 [a0s; path] envv.   (* [comment removed for export] *)
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0.
  Hypothesis Hbrk : valid_brk RSEGS brk.
  Hypothesis Hfile : fs_lookup fs0 path = Some fdata.
  Hypothesis Hpne : path <> [].
  Hypothesis Hpnd : path <> dot_path.
  Hypothesis Hplen : (length path <= 4095)%nat.

  (* [comment removed for export] *)
  Lemma Hpns : path_has_slash path = false.
  Proof. destruct Hva as (_ & _ & _ & _ & H5). cbn [tl] in H5. apply Forall_inv in H5. exact (proj1 H5). Qed.
  Lemma Hpndr : path_is_dirref path = false.
  Proof.
    destruct Hva as (_ & _ & _ & _ & H5). cbn [tl] in H5. apply Forall_inv in H5 as [_ Hdd].
    unfold path_is_dirref. rewrite Hdd, Bool.orb_false_r. change Uapi.dot_path with dot_path.
    destruct (path_eqb path dot_path) eqn:E; [|reflexivity]. apply path_eqb_eq in E. contradiction.
  Qed.

  (* [comment removed for export] *)
  Lemma live_bytes_bound : forall (l : list (word * word)) n b,
    (length l <= n)%nat -> Forall (fun p => (0 < bv_unsigned (snd p) <= b)%Z /\ (bv_unsigned (fst p) + bv_unsigned (snd p) <= 2 ^ 64)%Z) l ->
    (0 <= b)%Z -> (live_bytes l <= Z.of_nat n * b)%Z.
  Proof.
    intros l. induction l as [|[a sz] l IH]; intros n b Hlen HF Hb; cbn [live_bytes length] in *.
    - lia.
    - apply Forall_cons_iff in HF as [[H1 _] HF]. cbn [snd] in H1.
      destruct n as [|n]; [lia|]. specialize (IH n b ltac:(lia) HF Hb). lia.
  Qed.

  Lemma target_vm_of_small : forall (VM : VmMaps) (mb gm : word) (area : Z),
    area = (bv_unsigned mb + 4096)%Z -> vm_pre VM sp0 mb gm -> vm_small VM gm ->
    target_vm (bv_unsigned sp0) (bv_unsigned gm) area VM.
  Proof.
    intros VM mb gm area Harea (Pr & Pisp & Pl & Ph & Pf & Pn & Plive & (p & Pin & Pne & Plo & Phi) & Pseps) (Vr & Vl & Vn & Vin & Vf & Vs).
    constructor.
    - exact Vr.
    - (* [comment removed for export] *) rewrite Z_to_bv_bv_unsigned. exact Pisp.
    - (* [comment removed for export] *) eapply Forall_impl; [|exact Pf]. intros q (_ & _ & Hq). exact Hq.
    - rewrite Z_to_bv_bv_unsigned. exact Vin.
    - exists (fst p), (snd p). destruct p as [lo sz]. cbn [fst snd] in *. split; [exact Pin|]. lia.
    - exact Vn.
    - exact Vf.
    - exact Vs.
    - exact Vl.
  Qed.

  Lemma after_malloc_main :
    after_malloc sp0 a0s path envv rdraw tid fs0 stdin0 (K32608 fdata fs0).
  Proof.
    unfold after_malloc. intros R M VM mb gm area brkv mas Harea RP W MF VP VS.
    pose proof Hvsp as Hvsp'. destruct Hvsp' as (SPlo & SPhi & SPal).
    unfold sp_window_lo, sp_window_hi in SPlo, SPhi.
    unfold K32608. destruct (Z.ltb_spec0 (Z.of_nat (length fdata)) 65536) as [Hlt|Hge].
    - (* [comment removed for export] *)
      apply (read_k0 sp0 (p1 sp0 a0s path envv) mb gm (canary_w rdraw) (secret_w rdraw) path fdata VM stdin0 fs0 tid Hfile R M _ RP Hlt).
      intros R' M' RQ.
      pose proof VS as VS'. destruct VS' as (VSr & VSl & VSn & VSin & VSsm & VSsep).
      apply (header_phase sp0 (p1 sp0 a0s path envv) gm tid area brkv mas (bv_unsigned (secret_w rdraw)) fdata VM stdin0 fs0 R M R' M' Hvsp RQ).
      + eapply world0_after_read0; [ | exact RQ | exact Hlt | exact W]. lia.
      + eapply main_frame_after_read0; [ | exact RQ | exact Hlt | exact W | exact MF]. lia.
      + exact Hlt.
      + exact VSin.
      + intros R'' M'' TP.
        pose proof (TPH (bv_unsigned sp0) (bv_unsigned gm) area brkv mas (bv_unsigned tid) (bv_unsigned (secret_w rdraw))
                      fdata R'' M'' VM (model_post VM stdin0 fs0 tid) TP
                      (target_vm_of_small VM mb gm area Harea VP VS)
                      (SPSA.std_model_mk VM stdin0 fs0 (Some tid) None)) as X.
        exact X.
    - (* [comment removed for export] *)
      apply (ref_big_file TPKH sp0 (p1 sp0 a0s path envv) mb gm (canary_w rdraw) (secret_w rdraw) R M area brkv mas VM path fdata stdin0 fs0 tid
               Hfile ltac:(lia) Harea RP W MF VP VS).
  Qed.

  Theorem ref_file_exists :
    realizes RSEGS (mkCfg (mkst regs0 (0x32634 : word) mem0 (seg_rom RSEGS))
                          (with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp0 LIM (mkProcInputA [a0s; path] envv fs0 stdin0))))
             (t_alt2 (t_die (msg_cannot_open path) fs0) (t_opened fdata fs0)).
  Proof.
    eapply rz_conseq; [ | apply teq_opened ].
    replace (0x32634 : word) with (Z_to_bv 64 0x32634) by (apply bv_eq; reflexivity).
    apply (oom_pilot sp0 a0s path envv uid hw rdraw tid regs0 mem0 brk mbase fs0 stdin0 fdata
             Hva Hve Hvsp Htid ME Hbrk Hfile Hpne Hpns Hpndr Hplen).
    - apply (OEH sp0 a0s path envv uid hw rdraw tid regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Hfits ME).
    - apply (brk_ok_sem sp0 a0s path envv uid hw rdraw tid regs0 mem0 brk mbase fs0 stdin0 fdata
               Hva Hve Hvsp Htid ME Hbrk Hfile Hpne Hpns Hpndr Hplen).
      apply after_malloc_main.
    - apply (mmap_ok_sem sp0 a0s path envv uid hw rdraw tid regs0 mem0 brk mbase fs0 stdin0 fdata
               Hva Hve Hvsp Htid ME Hbrk Hfile Hpne Hpns Hpndr Hplen).
      apply after_malloc_main.
  Qed.
End FileExists.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem ref_realizes_spec :
  target_phase_stmt -> target_phase_k_stmt -> usage_stmt -> open_fail_stmt -> open_err_stmt ->
  forall sp brk mbase (rdraw : EntryDraw) (inp : ProcInput),
    valid_sp sp -> valid_brk rsegs brk -> entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
    realizes rsegs
      (init_config rsegs rpc rph sp brk mbase rdraw target_alloc_limit inp)
      (spec (in_argv inp) (in_fs inp)).
Proof.
  intros TPH TPKH USH OFH OEH sp brk mbase rdraw inp Hsp Hbrk Hfits Hva Hve Hfs.
  change (init_config rsegs rpc rph sp brk mbase rdraw target_alloc_limit inp)
    with (init_config rsegs rpc rph sp brk mbase rdraw target_alloc_limit
            (mkProcInputA (in_argv inp) (in_envp inp) (in_fs inp) (amb_of inp))).
  set (stdin0 := amb_of inp).
  generalize (in_argv inp) (in_envp inp) (in_fs inp) Hfits Hva Hve Hfs; clear Hfits Hva Hve Hfs; intros argv envp fs0 Hfits Hva Hve Hfs.
  cbn [in_argv in_fs mkProcInputA].
  change target_alloc_limit with LIM.
  apply ref_startup; try assumption.
  intros tid regs mem Htid ME. rewrite in_argv_A, in_envp_A, in_uid_A, in_hwcap_A in ME. cbn [in_argv in_envp mkProcInputA] in ME.
  set (uid := ia_uid stdin0) in ME. set (hw := ia_hwcap stdin0) in ME.
  destruct argv as [|a0s [|path [|x l]]].
  - apply (USH sp [] envp uid hw rdraw tid regs mem brk mbase fs0 stdin0 LIM Hva Hve Hsp Hfits Htid ME). cbn; lia.
  - apply (USH sp [a0s] envp uid hw rdraw tid regs mem brk mbase fs0 stdin0 LIM Hva Hve Hsp Hfits Htid ME). cbn; lia.
  - cbn [spec].
    destruct (Nat.leb_spec0 4096 (length path)) as [Hlong|Hshort].
    + apply (OFH sp a0s path envp uid hw rdraw tid regs mem brk mbase fs0 stdin0 LIM Hva Hve Hsp Hfits Htid ME). left. exact Hlong.
    + destruct (list_byte_eqb path []) eqn:Hemp.
      * apply ref_list_byte_eqb_eq in Hemp.
        apply (OFH sp a0s path envp uid hw rdraw tid regs mem brk mbase fs0 stdin0 LIM Hva Hve Hsp Hfits Htid ME). right. left. exact Hemp.
      * assert (Hne : path <> []) by (intros E; apply ref_list_byte_eqb_eq in E; rewrite E in Hemp; discriminate).
        destruct (list_byte_eqb path dot_path) eqn:Hdot.
        -- apply ref_list_byte_eqb_eq in Hdot. rewrite Hdot in *.
           apply (ref_dir_path (fun sp0 a0s envv uid hw rdraw tid regs0 mem0 brk mbase fs0 stdin0 =>
                                  OEH sp0 a0s dot_path envv uid hw rdraw tid regs0 mem0 brk mbase fs0 stdin0)
                    sp a0s envp uid hw rdraw tid regs mem brk mbase fs0 stdin0 Hva Hve Hsp Hfits Htid ME Hbrk).
        -- assert (Hnd : path <> dot_path)
             by (intros E; apply ref_list_byte_eqb_eq in E; rewrite E in Hdot; discriminate).
           destruct (fs_lookup fs0 path) as [data|] eqn:Hlk.
           ++ apply (ref_file_exists TPH TPKH OEH sp a0s path envp uid hw rdraw tid regs mem brk mbase fs0 stdin0 data
                       Hva Hve Hsp Hfits Htid ME Hbrk Hlk Hne Hnd ltac:(lia)).
           ++ apply (OFH sp a0s path envp uid hw rdraw tid regs mem brk mbase fs0 stdin0 LIM Hva Hve Hsp Hfits Htid ME).
              right. right. repeat split.
              ** lia.
              ** exact Hne.
              ** exact (Hpns a0s path Hva).
              ** exact (Hpndr a0s path Hva Hnd).
              ** exact Hlk.
  - apply (USH sp (a0s :: path :: x :: l) envp uid hw rdraw tid regs mem brk mbase fs0 stdin0 LIM Hva Hve Hsp Hfits Htid ME). cbn; lia.
Qed.
