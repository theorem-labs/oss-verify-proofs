(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, the section reads the launch (valid_launch, entry_launch_ok_va), the first grow's ledger is init_reserved with the launch's vDSO pair, whose freedom from the heap grow (brk_region_free_model1) follows brk_grow_admissible_init_vdso and vdso_region_free_below of projects/coturn/FuzzStunClient/proofs/lib/Common/RefNodes.v, stage C walks the auxv to AT_NULL for either CONFIG_RSEQ value, and the brk ceiling is alloc_ceiling. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.skcms.iccprofile_info.images Require Plain.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require ArgvEnv.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Amb PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg ShapeLaws Nodes MmapSim AllocSim FileSim AgentLib SpecConsts SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame Spec LibWritev RefNodes RefMemcpyLib SymXfer RefMemcpyBase RefMemcpy RefStartup RefMainEntry Hoare MemSplit.
Unset Nia Cache.  (* [comment removed for export] *)

Module RefPilotOOM_defs.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec2Sound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRun OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDrive OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveX OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMemcpyLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefMainEntry.
Unset Lia Cache.

Import ListNotations. Import SX2. Import SX2S.

Abbreviation RSEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
Section WithFP1. Context {FP : PropExec.FPState}.
Definition kn_exec : list kentry := kn_main.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition STOPS : list Z := [0x1dbe0; 0x1dfe4; 0x1e0dc; 0x1e120; 0x12f28; 0x18348; 0x16a60; 0x18fe8]%Z.

Definition FUEL : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].

Definition run (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).

(* [comment removed for export] *)
Definition ssA0 : sym_state := SS 0x12a88 sr_main [] kn_exec 38.
Definition rA := Eval vm_compute in run scr0 ssA0.
Definition srA : list expr := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA : list kentry := Eval vm_compute in kn_after rA kn_exec.
Definition logA : list sentry := Eval vm_compute in s_log (fst (fst rA)).

(* [comment removed for export] *)
Definition srB0 : list expr := sr_upd srA (ridx 10) (ELit 3).
(* LPS 727298f3: [get_random_secret] scans the auxv types to AT_RANDOM in this stage and on to
   AT_NULL in stage C, so the stages start from RefMainEntry.kn_auxt and, at C, the CONFIG_RSEQ
   tail [kn_auxtail] (C is defined at the CONFIG_RSEQ value; [oom_seg2] walks both). *)
Definition ssB0 : sym_state := SS 0x1e508 srB0 [] (kn_auxt ++ knA) 38.
Definition rB := Eval vm_compute in run scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB (kn_auxt ++ knA).

(* [comment removed for export] *)
Definition mc_store : sentry := SE (SA (EVar 0) (-384)) 8 (EVar 7).
Definition knB2 : list kentry := Eval vm_compute in fst (fst (carry [mc_store] knB [])).
(* [comment removed for export] *)
Definition srC0 : list expr := Eval vm_compute in sr_after_call_j srB (map ridx callee_kept) 38.

(* [comment removed for export] *)
Definition ssC0 : sym_state := SS 0x174d8 srC0 [] (kn_auxtail true ++ knB2) 70.
Definition rC := Eval vm_compute in run scr0 ssC0.
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in kn_after rC knB2.

(* [comment removed for export] *)
Definition b_expr : expr := EVar 70.
Definition knD0 : list kentry := KAlign b_expr 4096 :: KRange b_expr 0x52000 0x80052000 :: knC.
Definition srD0 : list expr := sr_upd srC (ridx 10) b_expr.
Definition ssD0 : sym_state := SS 0x175a4 srD0 [] knD0 71.
Definition rD := Eval vm_compute in run scr0 ssD0.
Definition srD : list expr := Eval vm_compute in s_regs (fst (fst rD)).
Definition knD : list kentry := Eval vm_compute in kn_after rD knD0.
(* [comment removed for export] *)
Definition ugly_b : expr :=
  EAlu ALU_ADD b_expr (EAlu ALU_AND (ELit 4095) (EMd M_MUL (ELit (-1)) b_expr)).
Definition srD2 : list expr := Eval vm_compute in map (esub ugly_b b_expr) srD.
Definition knD2 : list kentry := Eval vm_compute in map (ksub ugly_b b_expr) knD.

(* [comment removed for export] *)
Lemma itinerary_ok :
  (s_pc (fst (fst rA)), snd (fst rA)) = (0x1e504%Z, [])
  /\ (s_pc (fst (fst rB)), snd (fst rB)) = (0x1dbe0%Z, [])
  /\ (s_pc (fst (fst rC)), snd (fst rC)) = (0x175a0%Z, [])
  /\ (s_pc (fst (fst rD)), snd (fst rD)) = (0x175c4%Z, []).
Proof. vm_compute. repeat split; reflexivity. Qed.
End WithFP1.

End RefPilotOOM_defs.
From Stdlib Require Zify.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require PerfWalkBz.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.skcms.iccprofile_info.images Require Import Plain.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import Amb
  PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg ShapeLaws Nodes
  MmapSim AllocSim FileSim AgentLib SpecConsts
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame
  Spec LibWritev RefNodes RefMemcpyLib RefMemcpyBase RefMemcpy
  RefStartup RefMainEntry Hoare MemSplit RefLim.
Import RefPilotOOM_defs.
From Stdlib Require Import Zify.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PerfWalkBz.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Ltac SymDriveX.run_block_with HR HK fuel stops scr NX keep ::= run_block_with_bz HR HK fuel stops scr NX keep.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX false.
Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX true.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section WithFP1. Context {FP : PropExec.FPState}.
Section Pilot.
  Context {AMB : Amb}.
  Context {AL : AllocLim}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable rndb : EntryDraw.   (* [comment removed for export] *)
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
  Local Notation INP := (mkProcInputC [a0s; path] envv fs0 stdin0) (only parsing).
  Hypothesis ME : main_entry sp0 INP mbase rndb tid regs0 mem0.
  Hypothesis Hvl : valid_launch INP.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rndb) INP.
  Hypothesis Hbrk : valid_brk RSEGS brk.
  Hypothesis Hfile : fs_lookup fs0 path = Some fdata.
  Hypothesis Hpne : path <> [].
  Hypothesis Hpnd : path <> dot_path.
  Hypothesis Hplen : (length path <= 4095)%nat.
  Hypothesis Hpdd : path <> dotdot_path.             (* [comment removed for export] *)
  Hypothesis Hpsl : path_has_slash path = false.     (* [comment removed for export] *)

  Definition ENV (vals : list word) : env := Env (vals_ev vals) (blobs_ev (blobs0 a0s path)).

  (* [comment removed for export] *)
  Definition fds0 : list (word * FdEntry) :=
    [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
     (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))].
  (* [comment removed for export] *)
  Definition model0 : Model :=
    with_tid tid (with_vdso a_vdso (init_model (segments_reserved RSEGS) brk mbase sp0 LIM (mkProcInputC [a0s; path] envv fs0 stdin0))).
  (* [comment removed for export] *)
  Definition fds1g (fd3 : FdEntry) : list (word * FdEntry) := fd_insert fds0 (Z_to_bv 64 3) fd3.
  Definition model1g (fd3 : FdEntry) : Model :=
    mkModelC (fds1g fd3) (mkVmMapsFull (init_reserved (segments_reserved RSEGS) mbase sp0 a_kernel) [] [] brk brk LIM mbase sp0) stdin0 fs0 None (Some tid) None.
  Definition fds1 : list (word * FdEntry) := fds1g (FdFile path (Z_to_bv 64 0)).
  Definition model1 : Model := model1g (FdFile path (Z_to_bv 64 0)).

  (* [comment removed for export] *)
  Definition above_sp0 (M : word -> option byte) : Prop :=
    forall a : word, (bv_unsigned sp0 <= bv_unsigned a)%Z -> M a = mem0 a.

  Lemma model0_eq : model0 = mkModelC fds0 (mkVmMapsFull (init_reserved (segments_reserved RSEGS) mbase sp0 a_kernel) [] [] brk brk LIM mbase sp0)
                                     stdin0 fs0 None (Some tid) None.
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma m1_vmmaps : forall fd3, m_vmmaps (model1g fd3) = mkVmMapsFull (init_reserved (segments_reserved RSEGS) mbase sp0 a_kernel) [] [] brk brk LIM mbase sp0.
  Proof. intros. reflexivity. Qed.
  Lemma m1_fs : forall fd3, m_fs (model1g fd3) = fs0.
  Proof. intros. reflexivity. Qed.
  Lemma m1_fds : forall fd3, m_fds (model1g fd3) = fds1g fd3.
  Proof. intros. reflexivity. Qed.
  Lemma m0_fds : m_fds model0 = fds0.
  Proof. reflexivity. Qed.
  Lemma m0_fs : m_fs model0 = fs0.
  Proof. reflexivity. Qed.

  Lemma fds1_2 : forall fd3, fd_lookup (fds1g fd3) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
  Proof. intros. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma above_sp0_block : forall vals log M,
    vals_ev vals 0 = sp0 -> log_below_b 0 0x52000 log = true -> above_sp0 M ->
    above_sp0 (mem_denot (ENV vals) M log).
  Proof.
    intros vals log M P0 Hb HA a Ha. pose proof (proj1 Hvsp) as SPlo. unfold sp_window_lo in SPlo.
    rewrite (mem_denot_above (ENV vals) M log 0%nat 0x52000 a Hb); [apply HA; exact Ha | | |];
      cbn [ev ENV]; rewrite ?P0; lia.
  Qed.

  Lemma alloc_fd_fds0 : alloc_fd fds0 = Z_to_bv 64 3.
  Proof. exact (alloc_fd_init _ _ _). Qed.
  Lemma fd_lookup_fds0_3 : fd_lookup fds0 (Z_to_bv 64 3) = None.
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Ltac refresh_above vals P0 HA :=
    lazymatch type of HA with above_sp0 ?Mo =>
      lazymatch goal with EQ : ?Mn = mem_denot _ Mo ?log |- _ =>
        let HA' := fresh "HA" in
        pose proof (above_sp0_block vals log Mo P0 ltac:(vm_compute; reflexivity) HA) as HA';
        rewrite <- EQ in HA'; clear HA EQ; rename HA' into HA
      end
    end.
  (* [comment removed for export] *)
  Ltac name_state R M :=
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rn _ ?Mn _) _) _ => rename Rn into R; rename Mn into M end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma rtop : reserved_top (segments_reserved RSEGS) = 0x52000%Z.
  Proof. vm_compute. reflexivity. Qed.

  Lemma brk_lo : (0x52000 <= bv_unsigned brk)%Z.
  Proof. pose proof (proj1 Hbrk) as H. rewrite rtop in H. exact H. Qed.
  Lemma brk_hi : (bv_unsigned brk <= 0x80052000)%Z.
  Proof. pose proof (proj1 (proj2 Hbrk)) as H. rewrite rtop, brk_aslr_max_val in H. cbn in H. lia. Qed.
  Lemma brk_al : (bv_unsigned brk mod 4096 = 0)%Z.
  Proof. exact (proj2 (proj2 Hbrk)). Qed.

  (* [comment removed for export] *)
  Lemma ugly_b_sem : forall vals, vals_ev vals 70 = brk ->
    edenot (ENV vals) ugly_b = edenot (ENV vals) b_expr.
  Proof.
    intros vals P70. cbn [edenot ugly_b b_expr ev ENV]. rewrite P70.
    rewrite alu_add, alu_and, m_mul. unfold v_add, v_and, v_mul.
    pose proof brk_al as Hal. pose proof (u64_range brk) as Hb.
    set (y := bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (-1)) * bv_unsigned brk))).
    assert (Hy : (y mod 4096 = 0)%Z).
    { subst y. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
      rewrite Z.mod_mod_divide by (exists (2 ^ 52)%Z; reflexivity).
      destruct (proj1 (Z.mod_divide (bv_unsigned brk) 4096 ltac:(lia)) Hal) as [q Hq]. rewrite Hq.
      rewrite Z.mul_assoc. apply Z_mod_mult. }
    assert (Hand : Z.land (bv_unsigned (Z_to_bv 64 4095)) y = 0%Z).
    { change (bv_unsigned (Z_to_bv 64 4095)) with (Z.ones 12). rewrite Z.land_comm, Z.land_ones by lia.
      change (2 ^ 12)%Z with 4096%Z. exact Hy. }
    rewrite Hand. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned.
  Qed.

  (* [comment removed for export] *)
  Lemma path_nonul : ~ In (Z_to_bv 8 0) path.
  Proof.
    destruct Hva as (_ & _ & _ & Hn & _). inversion Hn as [|x l Hx Hl]; subst. inversion Hl; subst. assumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* LPS 727298f3: the first grow's ledger is [init_reserved], the image's reservations followed by
     the vdso/vvar pair ([State.vdso_reserved]) at [page_round_down_Z (min mbase (sp0 - stack_max_size))].
     The image part keeps the [reserved_top] argument; the pair lies in [[top - vdso_len, top)]
     ([State.vdso_reserved_above]), [vdso_len <= 20 pages] ([State.vdso_len_bounds]) and
     [top >= mmap_base_min] by the launch's own base ([Run.entry_launch_ok_va_base]), so the heap
     grow ends far below it.  After coturn's Common/RefNodes.v [brk_grow_admissible_init_vdso] and
     [vdso_region_free_below]. *)
  Lemma brk_region_free_model1 :
    region_free (init_reserved (segments_reserved RSEGS) mbase sp0 a_kernel ++ [])
                brk (Z_to_bv 64 (8192 + page_size)) = true.
  Proof.
    pose proof brk_lo as Blo. pose proof brk_hi as Bhi. pose proof (proj1 Hvsp) as SPlo.
    assert (Hmb : (mmap_base_min <= bv_unsigned mbase)%Z)
      by exact (proj1 (entry_launch_ok_va_base Sv48 (mkEntry sp0 brk mbase rndb) INP Hlau)).
    assert (Hx1 : (mmap_base_min <= Z.min (bv_unsigned mbase) (bv_unsigned sp0 - stack_max_size))%Z)
      by (unfold sp_window_lo, stack_max_size, mmap_base_min in *; lia).
    pose proof (Z.le_min_l (bv_unsigned mbase) (bv_unsigned sp0 - stack_max_size)) as Hx2.
    pose proof (u64_range mbase) as Hmr.
    assert (Htp : (page_round_down_Z (Z.min (bv_unsigned mbase) (bv_unsigned sp0 - stack_max_size))
                   < two_pow_64)%Z).
    { unfold page_round_down_Z, page_size, two_pow_64.
      pose proof (Z.mul_div_le (Z.min (bv_unsigned mbase) (bv_unsigned sp0 - stack_max_size)) 4096
                    ltac:(lia)). lia. }
    assert (Hge : (mmap_base_min
                   <= page_round_down_Z (Z.min (bv_unsigned mbase) (bv_unsigned sp0 - stack_max_size)))%Z).
    { unfold page_round_down_Z, page_size.
      pose proof (Z.div_le_mono _ _ 4096 ltac:(lia) Hx1) as Hd.
      change (mmap_base_min / 4096)%Z with 0x154555557%Z in Hd. unfold mmap_base_min. lia. }
    pose proof (vdso_len_bounds a_kernel) as Hvdl.
    rewrite app_nil_r. unfold init_reserved. rewrite region_free_app. apply andb_true_intro. split.
    - apply region_free_above_top. rewrite rtop. exact Blo.
    - apply region_free_below. apply Forall_forall. intros [a n] Hin. cbn [fst].
      destruct (vdso_reserved_above a_kernel _ a n Htp Hin) as [Ha _].
      rewrite u64_lit by (unfold page_size; lia). unfold page_size, mmap_base_min in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma brk_grow_ok_model1 : forall fd3,
    Mmap.brk_grow_ok (model1g fd3) (Z_to_bv 64 (bv_unsigned brk + 8192)) (Z_to_bv 64 (bv_unsigned brk + 8192)) = true.
  Proof.
    intros fd3. pose proof brk_lo. pose proof brk_hi. pose proof brk_al. pose proof LIM_ge.
    pose proof (proj1 Hvsp) as SPlo. unfold sp_window_lo in SPlo.
    apply (brk_grow_ok_aligned_intro (model1g fd3) 8192); rewrite ?m1_vmmaps; cbn [vm_brk vm_reserved vm_maps vm_init_sp vm_limit].
    (* LPS #38 (in 727298f3): the ceiling is [alloc_ceiling], with [init_sp_ok] before the
       [region_free] (RefNodes.brk_grow_admissible_init).  One bullet per premise, so the
       one that fails is named. *)
    - exact brk_al.
    - reflexivity.
    - lia.
    - lia.
    - pose proof OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan.AsanCeil.alloc_ceiling_val. lia.
    - exact (proj1 Hvsp).
    - exact brk_region_free_model1.
    - rewrite vm_backing_used_simple by reflexivity. rewrite m1_vmmaps.
      unfold vm_backed_bytes, vm_backed_maps. cbn. try unfold LIM in *.
      rewrite ?target_alloc_limit_val in *. lia.
  Qed.

  (* [comment removed for export] *)
  Definition brk_ok_branch_g (fd3 : FdEntry) (KB : TSet) : Prop :=
    forall vals R M,
      length vals = 71%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 70 = brk ->
      vals_ev vals 1 = p0 INP rndb -> vals_ev vals 2 = p1 INP rndb ->
      vals_ev vals 5 = tid ->
      regs_ok (ENV vals) srD2 R -> know_ok RSEGS (ENV vals) M knD2 -> above_sp0 M ->
      realizes RSEGS
        (mkCfg (mkst (regupd R 10 (Z_to_bv 64 (bv_unsigned brk + 8192))) (Z_to_bv 64 0x175c8)
                     (zfill brk (Z_to_bv 64 8192) M) (seg_rom RSEGS))
               (mkModelC (fds1g fd3) (mkVmMapsFull (init_reserved (segments_reserved RSEGS) mbase sp0 a_kernel) [(brk, Z_to_bv 64 8192)] [] brk
                                            (Z_to_bv 64 (bv_unsigned brk + 8192)) LIM mbase sp0)
                        stdin0 fs0 None (Some tid) None)) KB.
  Definition brk_ok_branch : TSet -> Prop := brk_ok_branch_g (FdFile path (Z_to_bv 64 0)).

  Lemma oom_seg2 : forall fd3 KBb vals R M,
    brk_ok_branch_g fd3 KBb ->
    length vals = 38%nat -> vals_ev vals 0 = sp0 ->
    vals_ev vals 1 = p0 INP rndb -> vals_ev vals 2 = p1 INP rndb -> vals_ev vals 5 = tid ->
    regs_ok (ENV vals) srB0 R -> know_ok RSEGS (ENV vals) M knA -> above_sp0 M ->
    (* the launch's auxv words (RefMainEntry.know_aux_above), in any memory that keeps the stack above sp0 *)
    (forall M', above_sp0 M' -> know_ok RSEGS (ENV vals) M' (kn_aux (kb_rseq (in_kernel INP)))) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x1e508) M (seg_rom RSEGS)) (model1g fd3)) KBb.
  Proof.
    intros fd3 KBb vals R M HKBb HL P0 P1 P2 P5t HR HK HA HX.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    (* [comment removed for export] *)
    pose proof (HX M HA) as HX0. unfold kn_aux, know_ok in HX0. apply Forall_app in HX0 as [HXt _].
    pose proof (proj2 (SymDriveX.know_ok_app RSEGS _ _ _ _) (conj HXt HK)) as HK'. clear HK HXt. rename HK' into HK.
    run_block_keep scr0 38%nat.
    refresh_above vals P0 HA. clear R M. name_state R M.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose proof (know_nth RSEGS _ _ knB ltac:(let i := kidx knB (is_krange (EVar 4)) in exact i) _ HK eq_refl)
      as Krnd; cbn [kentry_ok edenot ev ENV] in Krnd.
    pose proof (know_nth RSEGS _ _ knB ltac:(let i := kidx knB (is_kdisj (EVar 0) (EVar 4)) in exact i) _ HK eq_refl)
      as Kdj; cbn [kentry_ok] in Kdj; unfold estart in Kdj; cbn [a_base a_off edenot ev ENV] in Kdj; rewrite P0 in Kdj.
    krdv HK 4%nat 8%Z 8%nat Hrd8.
    { apply flat_intro; cbn [edenot ev ENV]; lia. }
    pose proof (kwr_store_ok RSEGS (ENV vals) _ knB ltac:(let i := kidx knB (is_kwr_cov (EVar 0) (-384) 8) in exact i)
                  _ _ _ (-384) 8 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hwr8.
    set (dst := adenot (ENV vals) (SA (EVar 0) (-384))) in *.
    set (src := adenot (ENV vals) (SA (EVar 4) 8)) in *.
    assert (Hudst : bv_unsigned dst = (bv_unsigned sp0 - 384)%Z).
    { subst dst. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite P0, u_small by lia. lia. }
    assert (Husrc : bv_unsigned src = (bv_unsigned (vals_ev vals 4) + 8)%Z).
    { subst src. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite u_small by lia. lia. }
    assert (MC : mcH M dst src 8 (word_to_le_bytes 8 (vals_ev vals 7))).
    { constructor.
      - lia.
      - reflexivity.
      - exact Hrd8.
      - exact Hwr8.
      - lia.
      - lia.
      - lia. }
    assert (RT : Hoare.ret_ok (Z_to_bv 64 0x174d8)) by (apply bv_eq; vm_compute; reflexivity).
    assert (G1 : getr R 1 = Z_to_bv 64 0x174d8) by (regv HR (1:reg); reflexivity).
    assert (G10 : getr R 10 = dst) by (regv HR (10:reg); subst dst; apply edenot_add_lit).
    assert (G11 : getr R 11 = src) by (regv HR (11:reg); subst src; apply edenot_add_lit).
    assert (G12 : getr R 12 = Z_to_bv 64 8) by (regv HR (12:reg); reflexivity).
    destruct (ref_memcpy M dst src 8 _ (seg_rom RSEGS) MC R (Z_to_bv 64 0x174d8) RT G1 G10 G11 G12)
      as (R2 & Hms & Hkeep). clear RT G1 G10 G11 G12.
    replace (Z_to_bv 64 121824) with (0x1dbe0 : word) by (apply bv_eq; vm_compute; reflexivity).
    eapply rz_msteps; [reflexivity | reflexivity | exact Hms |]. clear Hms.
    (* [comment removed for export] *)
    assert (HA' : above_sp0 (wbytes M dst (word_to_le_bytes 8 (vals_ev vals 7)))).
    { intros a Ha. rewrite wbytes_outside; [apply HA; exact Ha | rewrite length_N_to_le_bytes; lia | rewrite length_N_to_le_bytes; right; lia]. }
    clear HA. rename HA' into HA.
    (* [comment removed for export] *)
    lazymatch type of HR with regs_ok _ ?sr _ =>
      pose proof (regs_after_keeps vals _ sr _ R2 callee_kept ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep
                    callee_kept_no0) as HR2 end.
    rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
    (* [comment removed for export] *)
    lazymatch type of HK with know_ok _ ?E ?M0 ?kn =>
      let c := eval vm_compute in (carry [mc_store] kn []) in
      lazymatch c with (?kn', ?scs, ?hs) =>
        pose proof (know_after_store RSEGS E M0 kn (SA (EVar 0) (-384)) 8 (EVar 7) (word_to_le_bytes 8 (vals_ev vals 7))
                      kn' scs hs ltac:(vm_compute; reflexivity) eq_refl HK ltac:(lia)
                      ltac:(apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia) eq_refl) as HK2
      end end.
    clear HK. subst dst.
    lazymatch type of HK2 with know_ok _ _ ?Mc ?kn =>
      pose proof (env_app_know RSEGS vals (junk_vals R2) _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK end.
    clear HK2.
    pose proof (HX _ HA) as HXa.
    lazymatch type of HXa with know_ok _ _ ?Mc ?kn =>
      pose proof (env_app_know RSEGS vals (junk_vals R2) _ Mc kn
                    ltac:(rewrite HL; destruct (kb_rseq (in_kernel INP)); vm_compute; reflexivity) HXa) as HXc end.
    clear HXa.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 70%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (P0' : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (P1' : vals_ev vals1 1 = p0 INP rndb) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P1).
    assert (P2' : vals_ev vals1 2 = p1 INP rndb) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
    assert (P5' : vals_ev vals1 5 = tid) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P5t).
    clearbody vals1. clear HL P0 P1 P2 P5t. rename HL1 into HL. rename P0' into P0. rename P1' into P1. rename P2' into P2. rename P5' into P5t.
    change (Env (vals_ev vals1) (blobs_ev (blobs0 a0s path))) with (ENV vals1) in HR, HK, HXc.
    (* [comment removed for export] *)
    (* Stage C runs to AT_NULL, whose place is CONFIG_RSEQ's: both values are walked.  The
       walks differ only in the scan's end pointer, left in a2 until stage D overwrites it;
       [knC] is among the facts of both. *)
    revert HXc. destruct (kb_rseq (in_kernel INP)); intros HXc;
      unfold kn_aux, know_ok in HXc; apply Forall_app in HXc as [_ HXt];
      pose proof (proj2 (SymDriveX.know_ok_app RSEGS _ _ _ _) (conj HXt HK)) as HK'; clear HK HXt; rename HK' into HK.
    * run_block_keep scr0 70%nat.
      refresh_above vals1 P0 HA. clear Hrd8 Hwr8 Hudst Husrc MC Krnd Kdj. clear R2 M. try clear R. name_state R M.
      lazymatch type of HK with know_ok _ ?E0 ?M0 ?kn0 =>
        assert (HKc : know_ok RSEGS E0 M0 knC)
          by (apply (SymXfer.know_ok_sub RSEGS E0 M0 kn0 knC); [vm_compute; reflexivity | exact HK]) end.
      clear HK. rename HKc into HK.
      (* [comment removed for export] *)
      eapply (rz_brk_query RSEGS _ _ _ (model1g fd3) ECALLW).
      - vm_compute. reflexivity.
      - apply is_ecall_ECALLW.
      - reflexivity.
      - reflexivity.
      - regv HR (17 : reg). reflexivity.
      - regv HR (10 : reg). reflexivity.
      - rewrite v_addi_pc4 by lia. change (0x175a0 + 4)%Z with 0x175a4%Z.
        rewrite m1_vmmaps; cbn [vm_brk].
        (* [comment removed for export] *)
        lazymatch type of HR with regs_ok _ ?sr ?Rc =>
          pose proof (env_app_regs vals1 [brk] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals1 [brk] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HR HK.
        set (vals2 := vals1 ++ [brk]) in *.
        assert (HL2 : length vals2 = 71%nat) by (subst vals2; rewrite length_app, HL; reflexivity).
        assert (P0' : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
        assert (P70 : vals_ev vals2 70 = brk).
        { subst vals2. rewrite <- HL. rewrite <- (Nat.add_0_r (length vals1)). rewrite vals_ev_app_r. reflexivity. }
        assert (P1' : vals_ev vals2 1 = p0 INP rndb) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P1).
        assert (P2' : vals_ev vals2 2 = p1 INP rndb) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
        assert (P5' : vals_ev vals2 5 = tid) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P5t).
        clearbody vals2. clear HL P0 P1 P2 P5t. rename HL2 into HL. rename P0' into P0. rename P1' into P1. rename P2' into P2. rename P5' into P5t.
        change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path))) with (ENV vals2) in HR2, HK2.
        pose proof (regs_set_a0 (ENV vals2) _ _ brk b_expr HR2 ltac:(cbn [edenot b_expr ev ENV]; exact P70)) as HR.
        clear HR2.
        (* [comment removed for export] *)
        lazymatch type of HK2 with know_ok _ _ ?Mc _ =>
          assert (HK : know_ok RSEGS (ENV vals2) Mc knD0) end.
        { unfold knD0. apply know_ok_cons; [|apply know_ok_cons; [|exact HK2]].
          - apply kalign_intro; [lia|]. cbn [edenot b_expr ev ENV]. rewrite P70. exact brk_al.
          - apply krange_intro. cbn [edenot b_expr ev ENV]. rewrite P70. pose proof brk_lo. pose proof brk_hi. lia. }
        clear HK2.
        (* [comment removed for export] *)
        run_block_keep scr0 71%nat.
        refresh_above vals2 P0 HA. clear R M. name_state R M.
        (* [comment removed for export] *)
        pose proof (regs_ok_esub (ENV vals2) ugly_b b_expr _ _ (ugly_b_sem vals2 P70) HR) as HR2.
        pose proof (know_ok_ksub RSEGS (ENV vals2) _ ugly_b b_expr _ (ugly_b_sem vals2 P70) HK) as HK2.
        clear HR HK. rename HR2 into HR. rename HK2 into HK.
        lazymatch type of HR with regs_ok _ ?sr _ => let sr' := eval vm_compute in sr in change sr with sr' in HR end.
        lazymatch type of HK with know_ok _ _ _ ?kn => let kn' := eval vm_compute in kn in change kn with kn' in HK end.
        (* [comment removed for export] *)
        eapply (rz_brk_grow RSEGS _ _ _ (model1g fd3) ECALLW 8192).
        + vm_compute. reflexivity.
        + apply is_ecall_ECALLW.
        + reflexivity.
        + reflexivity.
        + regv HR (17 : reg). reflexivity.
        + rewrite m1_vmmaps; cbn [vm_brk]. exact brk_al.
        + reflexivity.
        + lia.
        + rewrite m1_vmmaps; cbn [vm_brk]. pose proof brk_lo. lia.
        + rewrite m1_vmmaps; cbn [vm_brk]. pose proof brk_hi. lia.
        + rewrite m1_vmmaps; cbn [vm_brk vm_start_brk]. lia.
        + rewrite m1_vmmaps; cbn [vm_brk]. regv HR (10 : reg). rewrite edenot_add_lit.
          unfold adenot, v_addi. cbn [a_base a_off edenot b_expr ev ENV]. rewrite P70. reflexivity.
        + rewrite m1_vmmaps; cbn [vm_brk]. apply brk_grow_ok_model1.
        + rewrite v_addi_pc4 by lia. change (0x175c4 + 4)%Z with 0x175c8%Z.
          rewrite m1_vmmaps; cbn [vm_brk vm_reserved vm_maps vm_noaccess vm_start_brk vm_limit vm_mmap_base vm_init_sp].
          eapply (HKBb vals2); try eassumption.
    * run_block_keep scr0 70%nat.
      refresh_above vals1 P0 HA. clear Hrd8 Hwr8 Hudst Husrc MC Krnd Kdj. clear R2 M. try clear R. name_state R M.
      lazymatch type of HK with know_ok _ ?E0 ?M0 ?kn0 =>
        assert (HKc : know_ok RSEGS E0 M0 knC)
          by (apply (SymXfer.know_ok_sub RSEGS E0 M0 kn0 knC); [vm_compute; reflexivity | exact HK]) end.
      clear HK. rename HKc into HK.
      (* [comment removed for export] *)
      eapply (rz_brk_query RSEGS _ _ _ (model1g fd3) ECALLW).
      - vm_compute. reflexivity.
      - apply is_ecall_ECALLW.
      - reflexivity.
      - reflexivity.
      - regv HR (17 : reg). reflexivity.
      - regv HR (10 : reg). reflexivity.
      - rewrite v_addi_pc4 by lia. change (0x175a0 + 4)%Z with 0x175a4%Z.
        rewrite m1_vmmaps; cbn [vm_brk].
        (* [comment removed for export] *)
        lazymatch type of HR with regs_ok _ ?sr ?Rc =>
          pose proof (env_app_regs vals1 [brk] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
        lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
          pose proof (env_app_know RSEGS vals1 [brk] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
        clear HR HK.
        set (vals2 := vals1 ++ [brk]) in *.
        assert (HL2 : length vals2 = 71%nat) by (subst vals2; rewrite length_app, HL; reflexivity).
        assert (P0' : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
        assert (P70 : vals_ev vals2 70 = brk).
        { subst vals2. rewrite <- HL. rewrite <- (Nat.add_0_r (length vals1)). rewrite vals_ev_app_r. reflexivity. }
        assert (P1' : vals_ev vals2 1 = p0 INP rndb) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P1).
        assert (P2' : vals_ev vals2 2 = p1 INP rndb) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P2).
        assert (P5' : vals_ev vals2 5 = tid) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P5t).
        clearbody vals2. clear HL P0 P1 P2 P5t. rename HL2 into HL. rename P0' into P0. rename P1' into P1. rename P2' into P2. rename P5' into P5t.
        change (Env (vals_ev vals2) (blobs_ev (blobs0 a0s path))) with (ENV vals2) in HR2, HK2.
        pose proof (regs_set_a0 (ENV vals2) _ _ brk b_expr HR2 ltac:(cbn [edenot b_expr ev ENV]; exact P70)) as HR.
        clear HR2.
        (* [comment removed for export] *)
        lazymatch type of HK2 with know_ok _ _ ?Mc _ =>
          assert (HK : know_ok RSEGS (ENV vals2) Mc knD0) end.
        { unfold knD0. apply know_ok_cons; [|apply know_ok_cons; [|exact HK2]].
          - apply kalign_intro; [lia|]. cbn [edenot b_expr ev ENV]. rewrite P70. exact brk_al.
          - apply krange_intro. cbn [edenot b_expr ev ENV]. rewrite P70. pose proof brk_lo. pose proof brk_hi. lia. }
        clear HK2.
        (* [comment removed for export] *)
        run_block_keep scr0 71%nat.
        refresh_above vals2 P0 HA. clear R M. name_state R M.
        (* [comment removed for export] *)
        pose proof (regs_ok_esub (ENV vals2) ugly_b b_expr _ _ (ugly_b_sem vals2 P70) HR) as HR2.
        pose proof (know_ok_ksub RSEGS (ENV vals2) _ ugly_b b_expr _ (ugly_b_sem vals2 P70) HK) as HK2.
        clear HR HK. rename HR2 into HR. rename HK2 into HK.
        lazymatch type of HR with regs_ok _ ?sr _ => let sr' := eval vm_compute in sr in change sr with sr' in HR end.
        lazymatch type of HK with know_ok _ _ _ ?kn => let kn' := eval vm_compute in kn in change kn with kn' in HK end.
        (* [comment removed for export] *)
        eapply (rz_brk_grow RSEGS _ _ _ (model1g fd3) ECALLW 8192).
        + vm_compute. reflexivity.
        + apply is_ecall_ECALLW.
        + reflexivity.
        + reflexivity.
        + regv HR (17 : reg). reflexivity.
        + rewrite m1_vmmaps; cbn [vm_brk]. exact brk_al.
        + reflexivity.
        + lia.
        + rewrite m1_vmmaps; cbn [vm_brk]. pose proof brk_lo. lia.
        + rewrite m1_vmmaps; cbn [vm_brk]. pose proof brk_hi. lia.
        + rewrite m1_vmmaps; cbn [vm_brk vm_start_brk]. lia.
        + rewrite m1_vmmaps; cbn [vm_brk]. regv HR (10 : reg). rewrite edenot_add_lit.
          unfold adenot, v_addi. cbn [a_base a_off edenot b_expr ev ENV]. rewrite P70. reflexivity.
        + rewrite m1_vmmaps; cbn [vm_brk]. apply brk_grow_ok_model1.
        + rewrite v_addi_pc4 by lia. change (0x175c4 + 4)%Z with 0x175c8%Z.
          rewrite m1_vmmaps; cbn [vm_brk vm_reserved vm_maps vm_noaccess vm_start_brk vm_limit vm_mmap_base vm_init_sp].
          eapply (HKBb vals2); try eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition open_err_branch (KA : TSet) : Prop :=
    forall e vals R M,
      In e openat_errnos ->
      length vals = 39%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 38 = errno_ret e ->
      vals_ev vals 1 = p0 INP rndb -> vals_ev vals 2 = p1 INP rndb ->
      vals_ev vals 5 = tid ->
      regs_ok (ENV vals) (sr_upd srA (ridx 10) (EVar 38)) R -> know_ok RSEGS (ENV vals) M knA ->
      (forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x) ->
      realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x1e508) M (seg_rom RSEGS)) model0) KA.

  Lemma oom_seg1 : forall KA KBb,
    open_err_branch KA -> brk_ok_branch KBb ->
    realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x12a88) mem0 (seg_rom RSEGS)) model0) (t_alt2 KA KBb).
  Proof.
    intros KA KBb HKA HKBb.
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
    unfold sp_window_lo, sp_window_hi in *.
    pose proof (main_regs_ok sp0 a0s path INP mbase brk tid rndb regs0 mem0 eq_refl Hva Hve Hvsp Hvl Hlau Htid ME) as HR.
    pose proof (main_know_ok sp0 a0s path INP mbase brk tid rndb regs0 mem0 eq_refl Hva Hve Hvsp Hvl Hlau Htid ME) as HK.
    pose proof (know_aux_above sp0 a0s path INP mbase brk tid rndb regs0 mem0 eq_refl Hva Hve Hvsp Hvl Hlau Htid ME) as AUX.
    change (E0 sp0 a0s path INP tid rndb regs0) with (ENV (vals0 sp0 INP tid rndb regs0)) in HR, HK, AUX.
    set (vals := vals0 sp0 INP tid rndb regs0) in *.
    assert (HL : length vals = 38%nat) by (subst vals; unfold vals0; rewrite length_app, length_skipn, junk_vals_length; reflexivity).
    assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
    assert (P1 : vals_ev vals 1 = p0 INP rndb) by reflexivity.
    assert (P2 : vals_ev vals 2 = p1 INP rndb) by reflexivity.
    assert (P5t : vals_ev vals 5 = tid) by reflexivity.
    destruct (main_str sp0 a0s path INP mbase brk tid rndb regs0 mem0 eq_refl Hva Hve Hvsp Hvl Hlau Htid ME 1%nat ltac:(lia)) as (Sr & Slo & Shi & Slen).
    cbn [nth] in Sr, Slo, Shi, Slen.
    clearbody vals.
    (* [comment removed for export] *)
    run_block_keep scr0 38%nat.
    (* [comment removed for export] *)
    assert (Sr' : rdn RSEGS M (p1 INP rndb) (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite EQM. unfold p1. rewrite (rdn_mem_denot_above RSEGS (ENV vals) mem0 _ 0%nat 0x52000);
        [exact Sr | vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia
        | pose proof (u64_range (cat_argv_ptr (ed_top rndb) [a0s; path] envv a_execfn 1)); lia]. }
    (* [comment removed for export] *)
    eapply (rz_openat_file RSEGS _ _ _ model0 ECALLW); try apply is_ecall_ECALLW.
    - vm_compute. reflexivity.
    - reflexivity.
    - reflexivity.
    - regv HR (17 : reg). reflexivity.
    - regv HR (10 : reg). apply bv_eq. reflexivity.
    - regv HR (12 : reg). vm_compute. reflexivity.
    - (* [comment removed for export] *) rewrite m0_fds. rewrite alloc_fd_fds0. apply fd_lookup_fds0_3.
    - (* [comment removed for export] *) split; [exact Hplen|]. split; [apply path_nonul|].
      split; [regv HR (11 : reg); cbn [edenot ev ENV]; rewrite P2; unfold p1; pose proof (OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ArgvEnv.cat_argv_ptr_task INP mbase sp0 brk rndb 1 Hlau ltac:(change (in_argv INP) with [a0s; path]; cbn; lia)) as T; change (in_argv INP) with [a0s; path] in T |- *; cbn [nth] in T; unfold TASK_SIZE; lia|]. 
      regv HR (11 : reg). cbn [edenot ev ENV]. rewrite P2. exact Sr'.
    - exact Hpne.
    - exact Hpnd.
    - exact Hpdd.
    - exact Hpsl.
    - rewrite m0_fs. exact Hfile.
    - (* [comment removed for export] *)
      intros e He. rewrite v_addi_pc4 by lia. change (0x1e504 + 4)%Z with 0x1e508%Z.
      lazymatch type of HR with regs_ok _ ?sr ?Rc =>
        pose proof (env_app_regs vals [errno_ret e] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
      lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
        pose proof (env_app_know RSEGS vals [errno_ret e] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
      change (Env (vals_ev (vals ++ [errno_ret e])) (blobs_ev (blobs0 a0s path))) with (ENV (vals ++ [errno_ret e])) in HR2, HK2.
      eapply (HKA e (vals ++ [errno_ret e])); try eassumption.
      + rewrite length_app, HL. reflexivity.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P0.
      + rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P1.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P2.
      + rewrite vals_ev_app_l by (rewrite HL; lia). exact P5t.
      + apply regs_set_a0; [exact HR2|]. cbn [edenot ev ENV].
        rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
      + intros x Hx. rewrite EQM. apply (mem_denot_above (ENV vals) mem0 _ 0%nat 0x52000);
          [vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia].
    - (* [comment removed for export] *)
      rewrite v_addi_pc4 by lia. change (0x1e504 + 4)%Z with 0x1e508%Z.
      rewrite m0_fds. rewrite alloc_fd_fds0.
      change (with_fds (fd_insert fds0 (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 0))) model0)
        with (model1g (FdFile path (Z_to_bv 64 0))).
      pose proof (regs_set_a0 (ENV vals) _ _ (Z_to_bv 64 3) (ELit 3) HR eq_refl) as HR2.
      assert (HA : above_sp0 M).
      { intros x Hx. rewrite EQM. apply (mem_denot_above (ENV vals) mem0 _ 0%nat 0x52000);
          [vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia]. }
      eapply (oom_seg2 (FdFile path (Z_to_bv 64 0)) KBb vals); try eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Theorem oom_pilot : forall KA KBb,
    open_err_branch KA -> brk_ok_branch KBb ->
    realizes RSEGS
      (mkCfg (mkst regs0 (Z_to_bv 64 0x12a88) mem0 (seg_rom RSEGS))
             (with_tid tid (with_vdso a_vdso (init_model (segments_reserved RSEGS) brk mbase sp0 LIM (mkProcInputC [a0s; path] envv fs0 stdin0)))))
      (t_alt2 KA KBb).
  Proof. intros. apply oom_seg1; assumption. Qed.

End Pilot.
End WithFP1.

