(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.AS Require Import
  PropExec ShapeAlg SpinAlg AsanAcct AsanAcctImages AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound BothPlanImages AsanInit BothStartup StartupHS2Both BothBoot
  AsanNodesWJoin StartupPlanBoth StartupHSBoth StartupPlan2Both BothCertDefs BothStartupCert BothStartupCertB BothStartupCertC BothStartupCertD BothStartupCert2   (* [comment removed for export] *)
  RegsEqv0 SrzEqv MainExport MainFactsBoth.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Step Frame.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import AcctCore TopLevelGen.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require Import TopLevel.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition AMAIN : Z := 0x7faec.           (* [comment removed for export] *)
Definition ARA : Z := 0xa1544.             (* [comment removed for export] *)
Definition AGP : Z := 0x10800.             (* [comment removed for export] *)
Definition ATP : Z := 0x5ed290.            (* [comment removed for export] *)
Definition AIMG_LO : Z := 0x10000.         (* [comment removed for export] *)
Definition AIMG_HI : Z := 0x60f000.
Definition ACEIL : Z := 0x7fff7f800000.    (* [comment removed for export] *)
Definition KHIGH : Z := 0x10007fff8000.    (* [comment removed for export] *)
Definition ASHOFF : Z := 0x7fff8000.       (* [comment removed for export] *)
Definition ABAND_LO : Z := 0x7fff7000.     (* [comment removed for export] *)
Definition ABAND_LEN : Z := 0x100000001000.
Definition V_VMBRK : nat := 452.           (* [comment removed for export] *)

Lemma asegs_ASEGS : ASEGS = bsegs.
Proof. reflexivity. Qed.
Lemma aph_APH : APH = b_phdrs.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record amodel (V : nat -> Z) (sp : word) (fs : Fs.Fs) (mo : Model) : Prop := AMODEL {
  am_halted   : m_halted mo = None;
  am_fds      : m_fds mo = [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
                            (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))];
  am_fs       : m_fs mo = fs;
  am_reserved : vm_reserved (m_vmmaps mo) = segments_reserved bsegs;
  am_limit    : vm_limit (m_vmmaps mo) = target_alloc_limit;
  am_brk      : vm_brk (m_vmmaps mo) = Z_to_bv 64 (V V_VMBRK);
  am_start_brk : bv_unsigned (vm_start_brk (m_vmmaps mo)) <= V V_VMBRK;
  (* [comment removed for export] *)
  am_top      : vm_init_sp (m_vmmaps mo) = sp;
  am_usp      : 0x7fff80000000 <= bv_unsigned sp /\ bv_unsigned sp <= 0x800000000000 /\ bv_unsigned sp mod 16 = 0;
  (* [comment removed for export] *)
  am_maps     : ledger_den V asan_ledger (vm_maps (m_vmmaps mo));
  am_kinds    : Forall (lentry_kind_ok V mo) asan_ledger;
  am_sep      : ivs_sep (vm_maps (m_vmmaps mo));
  am_bounds   : Forall (fun iv => 0 < bv_unsigned (snd iv) /\ bv_unsigned (fst iv) mod 4096 = 0 /\ bv_unsigned (snd iv) mod 4096 = 0
                                  /\ 0 < bv_unsigned (fst iv)
                                  /\ (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= AIMG_LO \/ AIMG_HI <= bv_unsigned (fst iv))
                                  /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= bv_unsigned sp - 8388608)
                       (vm_maps (m_vmmaps mo));
  am_lazy_bounds : Forall (fun iv => (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= AIMG_LO \/ AIMG_HI <= bv_unsigned (fst iv))
                                     /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= bv_unsigned sp - 8388608)
                          (m_vm_lazy mo);
  am_noaccess_wf : Forall (fun iv => bv_unsigned (fst iv) + bv_unsigned (snd iv) <= 2 ^ 64) (vm_noaccess (m_vmmaps mo));
  am_noaccess_sub : forall z, MainExport.in_ivs z (vm_noaccess (m_vmmaps mo)) -> MainExport.in_ivs z (vm_maps (m_vmmaps mo));
  (* [comment removed for export] *)
  am_noaccess_pos : Forall (fun iv => 0 < bv_unsigned (snd iv)) (vm_noaccess (m_vmmaps mo));
  am_totsz    : ivs_sum (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) <= asan_totsz;
  (* [comment removed for export] *)
  am_nonlazy  : nonlazy_bytes mo <= asan_eager;
  am_abytes   : ivz_bytes (allow_of ASHOFF V asan_vis) <= asan_abytes;
  am_budget   : nonlazy_bytes mo + ivz_bytes (allow_of ASHOFF V asan_vis) <= target_alloc_limit;
  am_allow_wf : ivz_wf (allow_of ASHOFF V asan_vis);
  am_mat_nodup : List.NoDup (m_vm_materialized mo);
  am_mat      : forall p, In p (m_vm_materialized mo) ->
                  bv_unsigned p mod 4096 = 0 /\ page_in_ranges p (m_vm_lazy mo) = true /\ aallowed (allow_of ASHOFF V asan_vis) p
}.

(* [comment removed for export] *)
Record amodelL (lim : Z) (V : nat -> Z) (sp : word) (fs : Fs.Fs) (mo : Model) : Prop := AMODELL {
  amL_halted   : m_halted mo = None;
  amL_fds      : m_fds mo = [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
                            (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))];
  amL_fs       : m_fs mo = fs;
  amL_reserved : vm_reserved (m_vmmaps mo) = segments_reserved bsegs;
  amL_limit    : vm_limit (m_vmmaps mo) = lim;          (* [comment removed for export] *)
  amL_brk      : vm_brk (m_vmmaps mo) = Z_to_bv 64 (V V_VMBRK);
  amL_start_brk : bv_unsigned (vm_start_brk (m_vmmaps mo)) <= V V_VMBRK;
  (* [comment removed for export] *)
  amL_top      : vm_init_sp (m_vmmaps mo) = sp;
  amL_usp      : 0x7fff80000000 <= bv_unsigned sp /\ bv_unsigned sp <= 0x800000000000 /\ bv_unsigned sp mod 16 = 0;
  (* [comment removed for export] *)
  amL_maps     : ledger_den V asan_ledger (vm_maps (m_vmmaps mo));
  amL_kinds    : Forall (lentry_kind_ok V mo) asan_ledger;
  amL_sep      : ivs_sep (vm_maps (m_vmmaps mo));
  amL_bounds   : Forall (fun iv => 0 < bv_unsigned (snd iv) /\ bv_unsigned (fst iv) mod 4096 = 0 /\ bv_unsigned (snd iv) mod 4096 = 0
                                  /\ 0 < bv_unsigned (fst iv)
                                  /\ (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= AIMG_LO \/ AIMG_HI <= bv_unsigned (fst iv))
                                  /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= bv_unsigned sp - 8388608)
                       (vm_maps (m_vmmaps mo));
  amL_lazy_bounds : Forall (fun iv => (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= AIMG_LO \/ AIMG_HI <= bv_unsigned (fst iv))
                                     /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= bv_unsigned sp - 8388608)
                          (m_vm_lazy mo);
  amL_noaccess_wf : Forall (fun iv => bv_unsigned (fst iv) + bv_unsigned (snd iv) <= 2 ^ 64) (vm_noaccess (m_vmmaps mo));
  amL_noaccess_sub : forall z, MainExport.in_ivs z (vm_noaccess (m_vmmaps mo)) -> MainExport.in_ivs z (vm_maps (m_vmmaps mo));
  (* [comment removed for export] *)
  amL_noaccess_pos : Forall (fun iv => 0 < bv_unsigned (snd iv)) (vm_noaccess (m_vmmaps mo));
  amL_totsz    : ivs_sum (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) <= asan_totsz;
  (* [comment removed for export] *)
  amL_nonlazy  : nonlazy_bytes mo <= asan_eager;
  amL_abytes   : ivz_bytes (allow_of ASHOFF V asan_vis) <= asan_abytes;
  amL_budget   : nonlazy_bytes mo + ivz_bytes (allow_of ASHOFF V asan_vis) <= lim;
  amL_allow_wf : ivz_wf (allow_of ASHOFF V asan_vis);
  amL_mat_nodup : List.NoDup (m_vm_materialized mo);
  amL_mat      : forall p, In p (m_vm_materialized mo) ->
                  bv_unsigned p mod 4096 = 0 /\ page_in_ranges p (m_vm_lazy mo) = true /\ aallowed (allow_of ASHOFF V asan_vis) p
}.

Lemma amodelL_amodel : forall V sp fs mo, amodelL target_alloc_limit V sp fs mo -> amodel V sp fs mo.
Proof. intros V sp fs mo H. destruct H. constructor; assumption. Qed.
Lemma amodel_amodelL : forall V sp fs mo, amodel V sp fs mo -> amodelL target_alloc_limit V sp fs mo.
Proof. intros V sp fs mo H. destruct H. constructor; assumption. Qed.

(* [comment removed for export] *)
Definition Wblk (en : ExecEntry) (inp : ProcInput) : Z :=
  (Z.of_nat (length (build_stack_bytes b_phdrs (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en))) - 16
   - (8 * Z.of_nat (length (in_argv inp)) + 8 * Z.of_nat (length (in_envp inp)) + 184)) / 8.

(* [comment removed for export] *)
Definition hidden_arg (en : ExecEntry) (inp : ProcInput) (a : Z) : Prop :=
  let usp := bv_unsigned (en_sp en) in
  let argc := Z.of_nat (length (in_argv inp)) in
  let envc := Z.of_nat (length (in_envp inp)) in
  (usp + 8 * argc + 16 <= a < usp + 8 * argc + 8 * envc + 24)
  \/ (usp + 8 * argc + 8 * envc + 184 <= a < usp + 8 * argc + 8 * envc + 184 + 8 * Wblk en inp).

(* [comment removed for export] *)
Definition ashadow (a : Z) : Prop := (0x7fff7000 <= a < 0x8fff7000) \/ (0x2008fff7000 <= a < 0x10007fff8000).
Definition ASHADOWS : list (Z * Z) := [(0x7fff7000, 0x8fff7000); (0x2008fff7000, 0x10007fff8000)].
Definition ashadow_vis (V : nat -> Z) (a : Z) : Prop :=
  exists bn, In bn asan_vis_app /\ ASHOFF + zv V (fst bn) / 8 <= a < ASHOFF + (zv V (fst bn) + zv V (snd bn)) / 8.
(* [comment removed for export] *)
Definition ashadow0 (V : nat -> Z) (m : word -> option byte) : Prop :=
  forall a, ashadow a -> ~ ashadow_vis V a -> m (wa a) = Some (Z_to_bv 8 0).

(* [comment removed for export] *)
Definition asan_mem_facts_w (w : bool) : list mfact := if w then asan_mem_facts_w1 else asan_mem_facts_w2.
Definition asan_pure_facts_w (w : bool) : list pfact := if w then asan_pure_facts_w1 else asan_pure_facts_w2.

Definition amain_at (en : ExecEntry) (inp : ProcInput) (ms : machine_state) (mo : Model) : Prop :=
  let usp := bv_unsigned (en_sp en) in
  let argc := Z.of_nat (length (in_argv inp)) in
  let envc := Z.of_nat (length (in_envp inp)) in
  exists (w : bool) (V : nat -> Z) (m : word -> option byte),
    ms = MS (mkR (Z_to_bv 64 ARA) (Z_to_bv 64 (usp - 48)) (Z_to_bv 64 AGP) (Z_to_bv 64 ATP)
                 (Z_to_bv 64 (V 664%nat)) (Z_to_bv 64 (V 665%nat)) (Z_to_bv 64 (V 666%nat))
                 (Z_to_bv 64 (usp + 8)) (Z_to_bv 64 argc) (Z_to_bv 64 argc) (Z_to_bv 64 (usp + 8))
                 (Z_to_bv 64 (usp + 8 * argc + 16)) (Z_to_bv 64 0x6000000000000000)
                 (Z_to_bv 64 (V 667%nat)) (Z_to_bv 64 (V 668%nat)) (Z_to_bv 64 (V 669%nat)) (Z_to_bv 64 (V 670%nat))
                 (Z_to_bv 64 AMAIN) (Z_to_bv 64 (usp + 8 * argc + 16))
                 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                 (Z_to_bv 64 (V 671%nat)) (Z_to_bv 64 (V 672%nat)) (Z_to_bv 64 (V 673%nat)) (Z_to_bv 64 (V 674%nat)))
            bvmap_empty (Z_to_bv 64 AMAIN) (Z_to_bv 32 0) None m (seg_rom bsegs)
    /\ (forall n, 0 <= V n < 2 ^ 64)
    (* [comment removed for export] *)
    /\ (V 0%nat = usp / 32768 /\ V 6%nat = usp mod 4096 / 16 /\ V 10%nat = usp mod 32768 / 4096
        /\ 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat = usp
        /\ V 1%nat = argc /\ V 2%nat = envc
        /\ V 3%nat = Z.of_nat (length (nth 0 (in_argv inp) [])) /\ V 7%nat = Z.of_nat (length (nth 1 (in_argv inp) []))
        /\ V 4%nat = Wblk en inp /\ V 5%nat = bv_unsigned (en_brk en) / 4096 /\ V 8%nat = bv_unsigned (in_uid inp)
        /\ V 9%nat = bv_unsigned (in_hwcap inp))
    /\ Forall (mfact_ok bsegs V m) (asan_mem_facts ++ asan_mem_facts_w w)
    /\ Forall (pfact_ok V) (asan_pure_facts ++ asan_pure_facts_w w)
    /\ mem_inv bsegs m
    /\ stk bsegs m (usp - 8388608) usp
    /\ (forall a, hidden_arg en inp a ->
          m (wa a) = wrap_mem b_phdrs (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) (wa a))
    /\ ashadow0 V m
    /\ amodel V (en_sp en) (in_fs inp) mo.

(* [comment removed for export] *)
Definition amain_atL (lim : Z) (en : ExecEntry) (inp : ProcInput) (ms : machine_state) (mo : Model) : Prop :=
  let usp := bv_unsigned (en_sp en) in
  let argc := Z.of_nat (length (in_argv inp)) in
  let envc := Z.of_nat (length (in_envp inp)) in
  exists (w : bool) (V : nat -> Z) (m : word -> option byte),
    ms = MS (mkR (Z_to_bv 64 ARA) (Z_to_bv 64 (usp - 48)) (Z_to_bv 64 AGP) (Z_to_bv 64 ATP)
                 (Z_to_bv 64 (V 664%nat)) (Z_to_bv 64 (V 665%nat)) (Z_to_bv 64 (V 666%nat))
                 (Z_to_bv 64 (usp + 8)) (Z_to_bv 64 argc) (Z_to_bv 64 argc) (Z_to_bv 64 (usp + 8))
                 (Z_to_bv 64 (usp + 8 * argc + 16)) (Z_to_bv 64 0x6000000000000000)
                 (Z_to_bv 64 (V 667%nat)) (Z_to_bv 64 (V 668%nat)) (Z_to_bv 64 (V 669%nat)) (Z_to_bv 64 (V 670%nat))
                 (Z_to_bv 64 AMAIN) (Z_to_bv 64 (usp + 8 * argc + 16))
                 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                 (Z_to_bv 64 (V 671%nat)) (Z_to_bv 64 (V 672%nat)) (Z_to_bv 64 (V 673%nat)) (Z_to_bv 64 (V 674%nat)))
            bvmap_empty (Z_to_bv 64 AMAIN) (Z_to_bv 32 0) None m (seg_rom bsegs)
    /\ (forall n, 0 <= V n < 2 ^ 64)
    (* [comment removed for export] *)
    /\ (V 0%nat = usp / 32768 /\ V 6%nat = usp mod 4096 / 16 /\ V 10%nat = usp mod 32768 / 4096
        /\ 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat = usp
        /\ V 1%nat = argc /\ V 2%nat = envc
        /\ V 3%nat = Z.of_nat (length (nth 0 (in_argv inp) [])) /\ V 7%nat = Z.of_nat (length (nth 1 (in_argv inp) []))
        /\ V 4%nat = Wblk en inp /\ V 5%nat = bv_unsigned (en_brk en) / 4096 /\ V 8%nat = bv_unsigned (in_uid inp)
        /\ V 9%nat = bv_unsigned (in_hwcap inp))
    /\ Forall (mfact_ok bsegs V m) (asan_mem_facts ++ asan_mem_facts_w w)
    /\ Forall (pfact_ok V) (asan_pure_facts ++ asan_pure_facts_w w)
    /\ mem_inv bsegs m
    /\ stk bsegs m (usp - 8388608) usp
    /\ (forall a, hidden_arg en inp a ->
          m (wa a) = wrap_mem b_phdrs (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) (wa a))
    /\ ashadow0 V m
    /\ amodelL lim V (en_sp en) (in_fs inp) mo.

Lemma amain_atL_amain_at : forall en inp ms mo, amain_atL target_alloc_limit en inp ms mo -> amain_at en inp ms mo.
Proof.
  intros en inp ms mo (w & V & m & H). exists w, V, m.
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
  repeat (split; [assumption|]). apply amodelL_amodel. exact H10.
Qed.
Lemma amain_at_amain_atL : forall en inp ms mo, amain_at en inp ms mo -> amain_atL target_alloc_limit en inp ms mo.
Proof.
  intros en inp ms mo (w & V & m & H). exists w, V, m.
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
  repeat (split; [assumption|]). apply amodel_amodelL. exact H10.
Qed.

(* [comment removed for export] *)
Lemma ashadow0_range : forall V m lo n,
  ashadow0 V m -> 0 < n ->
  (forall a, lo <= a < lo + n -> ashadow a /\ ~ ashadow_vis V a) ->
  (forall i, 0 <= i < n -> m (wa (lo + i)) = Some (Z_to_bv 8 0))
  /\ wr_at bsegs m lo n /\ rw_cells bsegs m lo [CB (Z.to_nat n) (zeros n)].
Proof.
  intros V m lo n H0 Hn HR.
  assert (Z0 : forall i, 0 <= i < n -> m (wa (lo + i)) = Some (Z_to_bv 8 0)).
  { intros i Hi. destruct (HR (lo + i) ltac:(lia)) as (S1 & S2). exact (H0 _ S1 S2). }
  split; [exact Z0|].
  destruct (HR lo ltac:(lia)) as (Slo & _). destruct (HR (lo + n - 1) ltac:(lia)) as (Shi & _). unfold ashadow in Slo, Shi.
  apply overlay_zero_rw; [lia| unfold MainExport.two64; lia| lia| exact Z0].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sub_of (bn : zexp * zexp) (b' : zexp) (n' : Z) : bool :=
  match snd bn with
  | ZLit nn =>
      (zexp_eqb (fst bn) b' && (0 <=? nn) && (nn <=? n'))
      || match fst bn with
         | ZAdd b0 (ZLit k) => zexp_eqb b0 b' && (0 <=? k) && (0 <=? nn) && (k + nn <=? n')
         | _ => false
         end
  | _ => false
  end.

Lemma sub_of_sound : forall V bn b' n', sub_of bn b' n' = true ->
  zv V b' <= zv V (fst bn) /\ zv V (fst bn) + zv V (snd bn) <= zv V b' + n'.
Proof.
  intros V [b n] b' n' H. unfold sub_of in H. cbn [fst snd] in *. destruct n as [nn| | | | |]; try discriminate.
  apply orb_prop in H as [H|H].
  - apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply zexp_eqb_eq in H1. subst b'.
    apply Z.leb_le in H2. apply Z.leb_le in H3. cbn [zv]. lia.
  - destruct b as [| |b0 k| | |]; try discriminate. destruct k as [k| | | | |]; try discriminate.
    apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply zexp_eqb_eq in H1. subst b'. apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.leb_le in H4. cbn [zv]. lia.
Qed.

(* [comment removed for export] *)
Definition band_fact (blo blen : Z) (PF : list pfact) (bn : zexp * zexp) : bool :=
  existsb (fun f => match f with
                    | PDisj b' n' (ZLit c) d => (c =? blo) && (d =? blen) && sub_of bn b' n'
                    | _ => false
                    end) PF.

Lemma band_fact_sound : forall V blo blen PF bn a, Forall (pfact_ok V) PF -> band_fact blo blen PF bn = true ->
  blo <= a < blo + blen -> ~ (zv V (fst bn) <= a < zv V (fst bn) + zv V (snd bn)).
Proof.
  intros V blo blen PF bn a HPF H Ha Hin. unfold band_fact in H. apply existsb_exists in H as (f & Hf & Hm).
  destruct f as [| |b' n' c d|]; try discriminate. destruct c as [c| | | | |]; try discriminate.
  apply andb_prop in Hm as [Hm H3]. apply andb_prop in Hm as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst c d.
  pose proof (sub_of_sound V bn b' n' H3) as [S1 S2].
  pose proof (proj1 (Forall_forall _ _) HPF _ Hf) as D. cbn [pfact_ok zv] in D. lia.
Qed.

(* [comment removed for export] *)
Definition shad_clear (VR : vranges) (PF : list pfact) (bn : zexp * zexp) : bool :=
  range_clear ASHADOWS VR bn || band_fact ABAND_LO ABAND_LEN PF bn.

Lemma shad_clear_sound : forall V VR PF bn a, vr_sound V VR -> Forall (pfact_ok V) PF -> shad_clear VR PF bn = true ->
  (exists s, In s ASHADOWS /\ fst s <= a < snd s) -> ~ (zv V (fst bn) <= a < zv V (fst bn) + zv V (snd bn)).
Proof.
  intros V VR PF bn a HV HPF H HS. unfold shad_clear in H. apply orb_prop in H as [H|H].
  - exact (range_clear_sound V VR ASHADOWS bn a HV H HS).
  - apply (band_fact_sound V ABAND_LO ABAND_LEN PF bn a HPF H).
    destruct HS as (s & Hs & Ha). unfold ABAND_LO, ABAND_LEN. cbn in Hs. destruct Hs as [<-|[<-|[]]]; cbn in Ha; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Bridge.
  Variable sp brk0 mbase : word.
  Variable rdraw : EntryDraw.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variables uid gid : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nof sigm : word.
  Variable hw : word.
  Variable abt : bool.
  Variable urnd : InputStream.   (* [comment removed for export] *)
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk ASEGS brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.

  Definition en0 : ExecEntry := mkEntry sp brk0 mbase rdraw.
  Definition inp0 : ProcInput := AsanInit.inp argv envp fs stdin uid gid hw groups net nof sigm abt urnd.

  #[local] Abbreviation SINV := (SINV0 APH sp rdraw brk0 argv envp uid hw).
  #[local] Abbreviation argH := (argH0 APH sp rdraw argv envp uid hw).
  #[local] Abbreviation E0a := (AsanInit.E0 APH sp rdraw brk0 argv envp uid hw).
  (* [comment removed for export] *)
  Section Lim.
  Variable LIM : Z.

  Let AH := argH0_high APH sp rdraw argv envp uid hw Hsp Hva.

  (* [comment removed for export] *)
  Lemma sinv_usp : forall E M, SINV E M -> uE E e_sp0 = bv_unsigned sp.
Proof.
    intros E M [HE _].
    transitivity (uE E0a e_sp0); [| exact (AsanInit.u_e_sp0 APH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit)].
    unfold e_sp0, uE. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit. cbn [edenot].
    rewrite !HE by (unfold NX0, V_S1, V_S2, V_SP; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Theorem amain_bridge_w : forall (w : bool) (hs : acs),
    s_regs (a_ss hs) = s_regs (a_ss HS_asan2_1) -> pc hs = AMAIN -> a_fd hs = FdStd -> a_brk hs = EVar V_VMBRK ->
    forallb (mjustify (kn hs) (var_ranges (kn hs)) AIMG_LO AIMG_HI) (asan_mem_facts ++ asan_mem_facts_w w) = true ->
    forallb (pjustify (kn hs) (var_ranges (kn hs))) (asan_pure_facts ++ asan_pure_facts_w w) = true ->
    vis_match (var_ranges (kn hs)) (a_vis hs) asan_vis_app = true /\ vis_match (var_ranges (kn hs)) (a_ghost hs) asan_ghost = true ->
    ledger_xmatch (var_ranges (kn hs)) (a_maps hs) asan_ledger = true ->
    a_totsz hs = asan_totsz /\ a_ylo hs = asan_ylo /\ a_eager hs = asan_eager /\ a_abytes hs = asan_abytes ->
    forall E R FULL mo,
    cs_ok ASEGS BOTH LIM SINV argH fs E hs R FULL mo ->
    exists ms, cfg_eqv (cfg_of ASEGS R (pc hs) FULL mo) (mkCfg ms mo) /\ amain_atL LIM en0 inp0 ms mo.
Proof.
    intros w hs Hregs Hpc Hfd Hbrk0 MJ PJ VJ LJ CONSTS E R FULL mo HC. rewrite Hpc.
    set (V := uev E).
    pose proof (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC) as HSINV. pose proof HSINV as [Hev Hhid].
    pose proof (sinv_usp E FULL HSINV) as USP.
    pose proof (AsanInit.uE0 APH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) as (U0 & U6 & U1 & U2 & U3 & U4 & U5).
    pose proof (AsanInit.uE0_sp APH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) as U10.
    pose proof (AsanInit.uE0_L1 APH sp rdraw brk0 argv envp uid hw Hva) as U7.
    pose proof (AsanInit.uE0_uid APH sp rdraw brk0 argv envp uid hw) as U8.
    pose proof (AsanInit.uE0_hw APH sp rdraw brk0 argv envp uid hw) as U9.
    unfold APS.uE in U0, U6, U1, U2, U3, U4, U5, U7, U8, U9, U10. cbn [edenot] in U0, U6, U1, U2, U3, U4, U5, U7, U8, U9, U10.
    assert (PIN : forall n z, (n < 11)%nat -> bv_unsigned (ev E0a n) = z -> V n = z).
    { intros n z Hn Hz. unfold V, uev. rewrite (Hev n) by (unfold NX0; lia). exact Hz. }
    pose proof (PIN 0%nat _ ltac:(lia) U0) as P0. pose proof (PIN 6%nat _ ltac:(lia) U6) as P6.
    pose proof (PIN 1%nat _ ltac:(lia) U1) as P1. pose proof (PIN 2%nat _ ltac:(lia) U2) as P2.
    pose proof (PIN 3%nat _ ltac:(lia) U3) as P3. pose proof (PIN 4%nat _ ltac:(lia) U4) as P4.
    pose proof (PIN 5%nat _ ltac:(lia) U5) as P5. pose proof (PIN 7%nat _ ltac:(lia) U7) as P7.
    pose proof (PIN 8%nat _ ltac:(lia) U8) as P8. pose proof (PIN 9%nat _ ltac:(lia) U9) as P9.
    pose proof (PIN 10%nat _ ltac:(lia) U10) as P10.
    clear U0 U6 U1 U2 U3 U4 U5 U7 U8 U9 U10.
    assert (Hal : bv_unsigned sp mod 16 = 0) by (pose proof Hsp as (_ & _ & H); exact H).
    pose proof (AsanInit.usp_lo sp Hsp) as LO.
    pose proof (AsanInit.usp_hi APH sp rdraw argv envp uid hw Hva Hve Hfit) as HI.
    assert (PSP : 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat = bv_unsigned sp).
    { rewrite P0, P6, P10. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    assert (VR : forall n, 0 <= V n < 2 ^ 64) by (intros n; apply uev_range).
    pose proof (co_top _ _ _ _ _ _ _ _ _ _ _ HC) as TOP. rewrite USP in TOP.
    assert (ATOP : atop mo = bv_unsigned sp - 8388608) by (unfold atop; rewrite TOP; reflexivity).
    eexists. split; cycle 1.
    {
      exists w, V, FULL. split; [reflexivity|].
      split; [exact VR|].
      split; [repeat split; assumption|].
      assert (HIDrom : forall a, APS.hid BOTH argH E hs mo a = true -> seg_rom bsegs a = None).
      { intros a Ha. apply (APS.seg_rom_off_hull ASEGS BOTH asan_in_hull).
        unfold APS.hid in Ha. apply orb_prop in Ha as [Ha|Ha].
        - pose proof (AH E a Ha) as Hc. unfold APS.in_hull. cbn [img_lo img_hi BOTH]. unfold CEIL in Hc.
          apply andb_false_iff. right. apply Z.ltb_ge. lia.
        - apply negb_true_iff in Ha. unfold APS.vis in Ha. apply orb_false_iff in Ha as [Ha _]. apply orb_false_iff in Ha as [Ha _]. exact Ha. }
      assert (HULLvis : forall a, AIMG_LO <= bv_unsigned a < AIMG_HI -> APS.hid BOTH argH E hs mo a = false).
      { intros a Ha. apply (APS.hid_hull BOTH asan_hull_ok argH AH). unfold APS.in_hull. cbn [img_lo img_hi BOTH]. unfold AIMG_LO, AIMG_HI in Ha.
        apply andb_true_intro. split; [apply Z.leb_le| apply Z.ltb_lt]; lia. }
      pose proof (export_sound bsegs E (APS.hid BOTH argH E hs mo) FULL (kn hs) AIMG_LO AIMG_HI
                    (co_know _ _ _ _ _ _ _ _ _ _ _ HC) HIDrom HULLvis _ _ MJ PJ) as [HMF HPF].
      pose proof (proj1 (Forall_app _ _ _) HMF) as [HMFc _].
      pose proof (proj1 (Forall_app _ _ _) HPF) as [HPFc _].
      split; [exact HMF|]. split; [exact HPF|].
      split.
      { intros a b Hab. rewrite a_ro_addr.
        destruct (Z.leb_spec0 0x10000 (bv_unsigned a)); [|reflexivity].
        destruct (Z.ltb_spec0 (bv_unsigned a) 0xb1000); [|reflexivity].
        exfalso. pose proof (mimg_cover bsegs V FULL asan_mem_facts 0x10000 0xb1000 HMFc ltac:(vm_compute; reflexivity) (bv_unsigned a) ltac:(lia)) as X.
        unfold wa in X. rewrite Z_to_bv_bv_unsigned in X. congruence. }
      split.
      { pose proof (mwr_find bsegs V FULL asan_mem_facts
                      (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-8388608))) 8388608
                      HMFc ltac:(vm_compute; reflexivity)) as W.
        cbn [zv] in W. fold V in W.
        replace (32768 * V 0%nat + (16 * V 6%nat + 4096 * V 10%nat) + -8388608) with (bv_unsigned sp - 8388608) in W by lia.
        cbn [en0 en_sp].
        apply wr_at_stk; [replace (bv_unsigned sp - (bv_unsigned sp - 8388608)) with 8388608 by lia; exact W|].
        intros a Ha. apply ref_find_segment_none; [lia|]. lia. }
      split.
      { intros a Ha. cbn [en0 inp0 AsanInit.inp mkProcInput en_sp en_draw in_argv in_envp in_uid in_hwcap]. apply Hhid.
        pose proof (AsanInit.usp_fit APH sp rdraw argv envp uid hw Hfit) as F.
        pose proof (AsanInit.W_range APH sp rdraw argv envp uid hw Hva Hve) as (W1 & W2 & W3).
        pose proof (AsanInit.len_av APH sp rdraw argv envp uid hw Hva) as LA. pose proof (AsanInit.len_ev APH sp rdraw argv envp uid hw Hve) as LE.
        unfold hidden_arg, Wblk in Ha. cbn [en0 inp0 AsanInit.inp mkProcInput en_sp en_draw in_argv in_envp in_uid in_hwcap] in Ha.
        try rewrite <- aph_APH in Ha.
        unfold argH0. rewrite wa_unsigned by lia.
        apply orb_true_intro. destruct Ha as [Ha|Ha]; [left|right]; apply andb_true_intro; split;
          first [apply Z.leb_le; lia | apply Z.ltb_lt; lia]. }
      pose proof (var_ranges_sound ASEGS E _ (kn hs) (co_know _ _ _ _ _ _ _ _ _ _ _ HC)) as HVR.
      destruct VJ as [VJa VJg].
      pose proof (vis_match_sound E _ _ _ HVR VJa) as HVISa. pose proof (vis_match_sound E _ _ _ HVR VJg) as HVISg.
      pose proof (Forall2_app HVISa HVISg) as HVIS. change (asan_vis_app ++ asan_ghost) with asan_vis in HVIS.
      pose proof (ledger_den_sound E _ HVR _ _ _ LJ (co_maps _ _ _ _ _ _ _ _ _ _ _ HC)) as HLD.
      pose proof (ledger_kinds_sound E _ HVR _ _ mo LJ (co_none _ _ _ _ _ _ _ _ _ _ _ HC) (co_kinds _ _ _ _ _ _ _ _ _ _ _ HC)) as HKD.
      fold V in HLD, HKD.
      split.
      { pose proof (pvranges_sound V asan_pure_facts VR HPFc) as HVRp.
        assert (CLRv : forallb (shad_clear (pvranges asan_pure_facts) asan_pure_facts) asan_vis_app = true) by (vm_compute; reflexivity).
        assert (CLRg : forallb (shad_clear (pvranges asan_pure_facts) asan_pure_facts) asan_ghost = true) by (vm_compute; reflexivity).
        assert (Elow : In (LMap (ZLit 0x7fff7000) 0x10000000 KRWLAZY) asan_ledger) by (cbn; tauto).
        assert (Ehigh : In (LMap (ZLit 0x2008fff7000) 0xdfff0001000 KRWLAZY) asan_ledger) by (cbn; tauto).
        intros a Hsh Hnv.
        assert (Ha : 0 <= a < 2 ^ 64) by (unfold ashadow in Hsh; lia).
        assert (Ua : bv_unsigned (wa a) = a) by (apply wa_unsigned; exact Ha).
        assert (KL : ~ MainExport.in_ivs a (vm_noaccess (m_vmmaps mo)) /\ page_in_ranges (page_base (wa a)) (m_vm_lazy mo) = true
                     /\ APS.in_ivs a (vm_maps (m_vmmaps mo)) = true).
        { destruct Hsh as [Hsh|Hsh].
          - pose proof (proj1 (Forall_forall _ _) HKD _ Elow) as K. cbn [lentry_kind_ok zv] in K.
            destruct (K (wa a) ltac:(rewrite Ua; lia)) as [K1 K2]. rewrite Ua in K1. split; [exact K1|]. split; [exact K2|].
            apply (proj2 (in_ivs_APS _ _)). exists (wa 0x7fff7000, wa 0x10000000). split; [exact (ledger_den_In V _ _ _ _ _ HLD Elow)|].
            cbn [fst snd]. rewrite !wa_unsigned by lia. lia.
          - pose proof (proj1 (Forall_forall _ _) HKD _ Ehigh) as K. cbn [lentry_kind_ok zv] in K.
            destruct (K (wa a) ltac:(rewrite Ua; lia)) as [K1 K2]. rewrite Ua in K1. split; [exact K1|]. split; [exact K2|].
            apply (proj2 (in_ivs_APS _ _)). exists (wa 0x2008fff7000, wa 0xdfff0001000). split; [exact (ledger_den_In V _ _ _ _ _ HLD Ehigh)|].
            cbn [fst snd]. rewrite !wa_unsigned by lia. lia. }
        destruct KL as (Kna & Klz & Kmap).
        assert (HSS : exists s, In s ASHADOWS /\ fst s <= a < snd s).
        { destruct Hsh as [Hsh|Hsh]; [exists (0x7fff7000, 0x8fff7000) | exists (0x2008fff7000, 0x10007fff8000)]; cbn; split; auto; lia. }
        apply (co_zero _ _ _ _ _ _ _ _ _ _ _ HC (wa a)); rewrite ?Ua.
        -
          unfold APS.hid. apply orb_true_intro. right. apply negb_true_iff. unfold APS.vis. rewrite Ua.
          rewrite Klz. cbn [negb].
          replace (APS.in_hull BOTH a) with false.
          2:{ symmetry. unfold APS.in_hull. cbn [img_lo img_hi BOTH]. apply andb_false_iff. right. apply Z.ltb_ge. unfold ashadow in Hsh. lia. }
          replace (atop mo <=? a) with false by (symmetry; apply Z.leb_gt; rewrite ATOP; unfold ashadow in Hsh; lia).
          cbn [orb]. replace (APS.in_allow BOTH E hs a) with false; [destruct (APS.in_ivs _ _ && _)%bool; reflexivity|].
          symmetry. unfold APS.in_allow. apply orb_false_intro.
          +
            unfold APS.in_vis. apply Bool.not_true_iff_false. intros X. apply existsb_exists in X as (p & Hp & Xp).
            apply andb_prop in Xp as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
            destruct (Forall2_In_l _ _ _ _ HVISa Hp) as (bn & Hbn & E1 & E2 & E3). unfold APS.uE in X1, X2. rewrite ?E1, ?E2 in X1; rewrite ?E1, ?E2 in X2. fold V in X1, X2.
            apply (shad_clear_sound V _ asan_pure_facts bn a HVRp HPFc (proj1 (forallb_forall _ _) CLRv bn Hbn) HSS). lia.
          +
            unfold APS.in_sh. apply Bool.not_true_iff_false. intros X. apply existsb_exists in X as (p & Hp & Xp).
            apply andb_prop in Xp as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2. unfold APS.sh_lo, APS.sh_hi, APS.uE in X1, X2.
            destruct (Forall2_In_l _ _ _ _ HVISa Hp) as (bn & Hbn & E1 & E2 & E3). rewrite ?E1, ?E2 in X1; rewrite ?E1, ?E2 in X2. fold V in X1, X2.
            apply Hnv. exists bn. split; [exact Hbn|]. change (shadow_off BOTH) with ASHOFF in X1, X2. lia.
        - exact Kmap.
        - apply Bool.not_true_iff_false. intros X. apply Kna. apply (proj1 (in_ivs_APS _ _)). exact X.
        - exact Klz.
        -
          unfold APS.in_ghost. apply Bool.not_true_iff_false. intros X. apply existsb_exists in X as (p & Hp & Xp).
          apply andb_prop in Xp as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2. unfold APS.uE in X1, X2.
          destruct (Forall2_In_l _ _ _ _ HVISg Hp) as (bn & Hbn & E1 & E2 & E3). rewrite ?E1, ?E2 in X1; rewrite ?E1, ?E2 in X2. fold V in X1, X2.
          apply (shad_clear_sound V _ asan_pure_facts bn a HVRp HPFc (proj1 (forallb_forall _ _) CLRg bn Hbn) HSS). lia. }
      pose proof (allowA_allow_of BOTH E _ _ HVIS) as HAL. change (shadow_off BOTH) with ASHOFF in HAL. change (flat_map (allow1 BOTH E) (a_vis hs ++ a_ghost hs)) with (allowA BOTH E hs) in HAL.
      fold V in HAL.
      pose proof CONSTS as (Ct & Cy & Ce & Ca).
      assert (USPW : vm_init_sp (m_vmmaps mo) = sp) by (apply bv_eq; exact TOP).
      destruct HC. cbn [inp0 AsanInit.inp mkProcInput in_fs en0 en_sp]. rewrite Hfd in co_fds0. rewrite Hbrk0 in co_brk0.
      constructor.
      + exact co_halt0.
      + exact co_fds0.
      + exact co_fs0.
      + exact co_res0.
      + exact co_limit0.
      + rewrite co_brk0. cbn [edenot]. symmetry. apply Z_to_bv_bv_unsigned.
      + rewrite co_brk0 in co_sbrk0. cbn [edenot] in co_sbrk0. exact co_sbrk0.
      + exact USPW.
      + split; [exact LO|]. split; [lia| exact Hal].
      + exact HLD.
      + exact HKD.
      + apply seps_ivs_sep. exact co_seps0.
      + eapply Forall_impl; [|exact co_bounds0]. cbv beta. intros iv (B1 & B2 & B3 & B4 & B5 & B6).
        unfold hull_clear in B5. cbn [img_lo img_hi BOTH] in B5. rewrite ATOP in B6. unfold AIMG_LO, AIMG_HI. repeat split; assumption.
      + eapply Forall_impl; [|exact co_lazyb0]. cbv beta. intros iv (B5 & B6).
        unfold hull_clear in B5. cbn [img_lo img_hi BOTH] in B5. rewrite ATOP in B6. unfold AIMG_LO, AIMG_HI. split; assumption.
      + destruct co_wf0 as (_ & Wn & _). apply Forall_forall. intros iv Hiv. exact (Wn iv Hiv).
      + intros z Hz. apply (proj1 (in_ivs_APS _ _)). apply co_nasub0. apply (proj2 (in_ivs_APS _ _)). exact Hz.
      + exact co_napos0.
      + rewrite <- Ct. exact co_totsz0.
      + rewrite <- Ce. exact co_eager0.
      + rewrite <- Ca, <- HAL. exact co_abytes0.
      + rewrite <- HAL. pose proof (minv_budget _ _ co_minv0) as B. rewrite co_limit0 in B. exact B.
      + rewrite <- HAL. exact (APS.A_wf_allowA BOTH HS_asan2 XN0 XE0 XB0 NX0 E hs).
      + exact (minv_nodup _ _ co_minv0).
      + intros p Hp. split; [exact (minv_aligned _ _ co_minv0 p Hp)|]. split; [exact (minv_lazy _ _ co_minv0 p Hp)|].
        rewrite <- HAL. apply page_allowedb_aallowed. exact (minv_allowed _ _ co_minv0 p Hp). }
    -
      unfold cfg_of. split; [|reflexivity]. cbn [cfg_ms].
      split; [| split; [apply regs_eqv_refl| repeat split; reflexivity]].
      cbn [ms_regs AS.PropExec.mkst MS].
      intros r Hr. destruct (OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib.RegsEquiv.reg_of_nat r) as (n & -> & Hn).
      pose proof (is_x0_of_nat n Hn Hr) as Hn1.
      rewrite (regs_ok_nth E _ R (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) n Hn1). rewrite reg_get_mkR by exact Hn1. rewrite Hregs.
      destruct n as [|n]; [cbv in Hr; discriminate|].
      cbn [en0 inp0 AsanInit.inp mkProcInput en_sp in_argv in_envp].
      do 31 (destruct n as [|n];
        [ cbn [nth HS_asan2_1 a_ss s_regs];
          first [ reflexivity
                | symmetry; apply Z_to_bv_bv_unsigned
                | erewrite <- (zexp_of_sound E) by reflexivity; cbn [zv]; fold V; unfold AMAIN, ARA, AGP, ATP; f_equal; lia ]
        |]). lia.
  Qed.

  (* [comment removed for export] *)
  Theorem amain_bridgeL_1 : forall E R FULL mo,
    cs_ok ASEGS BOTH LIM SINV argH fs E HS_asan2_1 R FULL mo ->
    exists ms, cfg_eqv (cfg_of ASEGS R (pc HS_asan2_1) FULL mo) (mkCfg ms mo) /\ amain_atL LIM en0 inp0 ms mo.
Proof.
    exact (amain_bridge_w true HS_asan2_1 eq_refl eq_refl eq_refl eq_refl asan_mem_facts_justified_w1 asan_pure_facts_justified_w1
             asan_vis_justified_w1 asan_ledger_justified_w1 asan_consts_w1).
  Qed.
  Theorem amain_bridgeL_2 : forall E R FULL mo,
    cs_ok ASEGS BOTH LIM SINV argH fs E HS_asan2_2 R FULL mo ->
    exists ms, cfg_eqv (cfg_of ASEGS R (pc HS_asan2_2) FULL mo) (mkCfg ms mo) /\ amain_atL LIM en0 inp0 ms mo.
Proof.
    exact (amain_bridge_w false HS_asan2_2 eq_refl eq_refl eq_refl eq_refl asan_mem_facts_justified_w2 asan_pure_facts_justified_w2
             asan_vis_justified_w2 asan_ledger_justified_w2 asan_consts_w2).
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis HLIM : source_alloc_limit <= LIM.
  #[local] Notation CERT_A_T := (check ASEGS IT0 BOTH NX0 LIM (XNS ASEGS BOTH NX0 LIM) XE0 XB0 HS_asanA KC0 BFUEL FUEL None both_init startup_plan = COk startup_shape).
  #[local] Notation CERT_B_T := (check ASEGS ITB BOTH NXB LIM (XNS ASEGS BOTH NXB LIM) XE0 XB0 HS_asanB KC0 BFUEL FUEL None HS_asanA_10 startup_plan_segA = COk startup_shapeB).
  #[local] Notation CERT_C_T := (check ASEGS ITC BOTH NXC LIM (XNS ASEGS BOTH NXC LIM) XE0 XB0 HS_asanC KC0 BFUEL FUEL None HS_asanB_11 startup_plan_segB = COk startup_shapeC).
  #[local] Notation CERT_D_T := (check ASEGS ITD BOTH NXD LIM (XNS ASEGS BOTH NXD LIM) XE0 XB0 HS_asanD KC0 BFUEL FUEL None HS_asanC_12 startup_plan_segC = COk startup_shapeD).
  #[local] Notation CERT_2_T := (check ASEGS IT2 BOTH NXS2 LIM (XNS ASEGS BOTH NXS2 LIM) XE0 XB0 HS_asan2 KC0 BFUEL FUEL None HS_asanD_0 startup2_plan = COk startup2_shape).
  (* [comment removed for export] *)
  Variable TL : TSet.
  Hypothesis TL_nil : TL [].
  Hypothesis MAINL : forall ms mo, amain_atL LIM en0 inp0 ms mo -> srealizes bsegs (mkCfg ms mo) TL.

  Theorem asan_main_bootL : CERT_A_T -> CERT_B_T -> CERT_C_T -> CERT_D_T -> CERT_2_T ->
    srealizes bsegs (init_config bsegs AsanUbsan.M.init_pc b_phdrs sp brk0 mbase rdraw LIM inp0) TL.
Proof.
    intros CERT_A CERT_B CERT_C CERT_D CERT_2.
    change bsegs with ASEGS. change b_phdrs with APH.
    refine (asan_boot sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nof sigm abt urnd Hsp Hbrk Hva Hve Hfit Huid Hhw
             LIM HLIM (fun _ _ => TL) _ _ _ CERT_A CERT_B CERT_C CERT_D CERT_2).
    - intros; reflexivity.
    - intros; exact TL_nil.
    - intros h ch Hh E R FULL mo HC. destruct h as [|[|[|h]]]; cbn in Hh; try discriminate Hh; injection Hh as <-.
      + destruct (amain_bridgeL_1 E R FULL mo HC) as (ms & Heqv & Hat).
        apply (srealizes_eqv ASEGS (mkCfg ms mo) TL (MAINL ms mo Hat)). apply cfg_eqv_sym. exact Heqv.
      + destruct (amain_bridgeL_2 E R FULL mo HC) as (ms & Heqv & Hat).
        apply (srealizes_eqv ASEGS (mkCfg ms mo) TL (MAINL ms mo Hat)). apply cfg_eqv_sym. exact Heqv.
  Qed.
  End Lim.

  (* [comment removed for export] *)
  Theorem amain_bridge_1 : forall E R FULL mo,
    cs_ok ASEGS BOTH AsanInit.LIMIT SINV argH fs E HS_asan2_1 R FULL mo ->
    exists ms, cfg_eqv (cfg_of ASEGS R (pc HS_asan2_1) FULL mo) (mkCfg ms mo) /\ amain_at en0 inp0 ms mo.
Proof.
    intros E R FULL mo HC. destruct (amain_bridgeL_1 AsanInit.LIMIT E R FULL mo HC) as (ms & He & Ha).
    exists ms. split; [exact He | exact (amain_atL_amain_at _ _ _ _ Ha)].
  Qed.
  Theorem amain_bridge_2 : forall E R FULL mo,
    cs_ok ASEGS BOTH AsanInit.LIMIT SINV argH fs E HS_asan2_2 R FULL mo ->
    exists ms, cfg_eqv (cfg_of ASEGS R (pc HS_asan2_2) FULL mo) (mkCfg ms mo) /\ amain_at en0 inp0 ms mo.
Proof.
    intros E R FULL mo HC. destruct (amain_bridgeL_2 AsanInit.LIMIT E R FULL mo HC) as (ms & He & Ha).
    exists ms. split; [exact He | exact (amain_atL_amain_at _ _ _ _ Ha)].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Variable T : TSet.
  Hypothesis T_nil : T [].
  Hypothesis MAINA : forall ms mo, amain_at en0 inp0 ms mo -> srealizes bsegs (mkCfg ms mo) T.

  Theorem asan_main_boot :
    srealizes bsegs (init_config bsegs AsanUbsan.M.init_pc b_phdrs sp brk0 mbase rdraw target_alloc_limit inp0) T.
Proof.
    exact (asan_main_bootL AsanInit.LIMIT AsanInit.LIMIT_ge T T_nil (fun ms mo H => MAINA ms mo (amain_atL_amain_at _ _ _ _ H))
             startup_cert startup_certB startup_certC startup_certD startup2_cert).
  Qed.
End Bridge.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem asan_side_ok : forall T : tfam,
  (forall en inp, valid_entry (mkImage bsegs b_init_pc b_phdrs) en inp -> valid_input_either inp ->
      T inp en [] /\ forall ms mo, amain_at en inp ms mo -> srealizes bsegs (mkCfg ms mo) (T inp en)) ->
  side_ok bsegs b_init_pc b_phdrs target_alloc_limit T.
Proof.
  intros T HT. apply side_ok_of_srealizes. intros [sp brk0 mbase rdraw] inp Hv Hi.
  destruct (HT _ _ Hv Hi) as [Tnil MAINA].
  rewrite (valid_entry_either _ _ _ _ _ _ _ _ Hi) in Hv.
  destruct Hv as (Hsp & Hbrk & Hmb & Hfit).
  pose proof Hi as (Hva & Hve & Hfs & Hrel & [Huid Hgid] & Hnof & Hsigm & Hhw & Hvasz & Hur).
  destruct inp as [argv envp ifs stdin uid gid groups net nof sigm hw abt vasz urnd tmp].
  cbn in Hfit, Hva, Hve, Hfs, Huid, Hgid, Hhw, Hvasz. subst vasz.
  exact (asan_main_boot sp brk0 mbase rdraw argv envp (fs_seed_tmp ifs tmp) stdin uid gid groups net nof sigm hw abt urnd Hsp Hbrk Hva Hve Hfit Huid Hhw _ Tnil MAINA).
Qed.
