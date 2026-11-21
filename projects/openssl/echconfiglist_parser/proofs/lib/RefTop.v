(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (main_entry a record over the run's input with the launch facts; rauxv_ok re-proved over Lib/AuxvTable's whole vector, hvdso as AT_SYSINFO_EHDR; heap_extra_HS and the walk over RSEGS ++ rt_tail; the ref_realizes_spec theorems over run_segments; the library closed at the run instance HeapSRVC.HRv, with heap_extra_HRv, the clean vDSO window of the entry memory and the pair in the initial ledger, the launch facts from VdsoLaunch); and launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.openssl.echconfiglist_parser.images Require Import Plain.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import Amb
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Frame StepTac StartupTac ArgvEnv RefLayout
  Spec SReach RefStartupDefs RefStartup RefStartupFacts RefMainEntry LibDiagKn LibDiagKnMain LibTail
  SymExec2 SymExec2Sound SymRun SymDrive SymDriveX HeapCeil HeapSecret
  MainDefs MainArith MainMem MainLoop MainTop TargetRun.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Mem Cells CellsX Arr Step Frame MState SysStep.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import AuxvTable.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prog AllocTop MmNodes KLink KLink3.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Agent Require Import Malloc_iface.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import ECH_Iface.   (* [comment removed for export] *)
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMallocTree RMalloc_iface RMalloc_ifaceP RMalloc_iface_stmt HeapSR_iface
  MallocSR MallocSR_init MallocSR_hyps MallocSR_closed.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require RomBase RomStable RunTail.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require MainSegs.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require MemSplit VdsoClean.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require MmVdso.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require HeapSRRun HeapSRVC ECH_LibTop VdsoLaunch.
Import ListNotations.
Import SymExec2.SX2. Import SymExec2Sound.SX2S.
Import OSSVerify.Proofs.openssl.echconfiglist_parser.lib.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Abbreviation RSEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bytes_le_val_eq : forall bs, bytes_le_val bs = bytes_le_to_Z bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [bytes_le_val bytes_le_to_Z]. rewrite <- IH.
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2 ^ Z.of_N 8) with 256 in Hb.
  pose proof (bytes_le_val_range bs) as Hv.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
  rewrite Z.lor_comm. replace (bytes_le_val bs * 256) with (256 * bytes_le_val bs) by lia.
  rewrite lor_disjoint_add by lia. lia.
Qed.

Lemma le8_bytes_le_val : forall bs, length bs = 8%nat -> word_to_le_bytes 8 (Z_to_bv 64 (bytes_le_val bs)) = bs.
Proof. intros bs Hl. rewrite bytes_le_val_eq. apply word_to_le_bytes_of_lez; [exact Hl | lia]. Qed.

Section Top.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* The heap's reach is a reach over the run's list: [MallocSR]'s reach over the binary's
     segments lifted by [RunTail.sreach_lift_rt] (the binary carries no vDSO image); the free
     that stays on the binary's segments is [MallocSR]'s own ([hsr_bin HS] is [HS]). *)
  Lemma heap_extra_HS {RT : RunTail.RunTail} : heap_extra HS.
  Proof.
    split.
    - intros Q c HQ Hr. exact (RunTail.sreach_lift_rt RSEGS MainSegs.vdso_image_RSEGS Q c (hx_sr_proof Q c HQ) Hr).
    - destruct heap_sr_hyps_closed as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F & _). exact F.
    - apply hx_mpres_proof.
    - cbn [hs_LIVE_MAX hs_LIVE_CNT_MAX hs_LIVE_BIG_MAX HS]. unfold HBYTES, HCNT, HBIG. lia.
    - cbn [hs_KREL HS]. intros s mo mo' K Hh Hl Hm Hv Hk Hr. apply (KM_vm s mo mo' K).
      + destruct K as (L & _ & KL & _). destruct (kb_minv _ _ _ KL) as [A1 [A2 A3]].
        split; [rewrite Hl; exact A1 | split; [rewrite Hm; exact A2 | rewrite Hr; exact A3]].
      + rewrite Hh. exact (proj1 (KM_halted_lazy s mo K)).
      + exact Hk.
      + exact Hv.
    - intros s LB m RH. pose proof (hx_statics_proof s LB m RH) as (H1 & H2 & H3). rewrite !rdn_same in *.
      split; [exact H1|]. split; [exact H2|]. exists hcanary. split; [exact H3 | hsb; lia].
    - cbn [hs_KREL HS]. exact KM_reader.
  Qed.

  (* The run instance [HeapSRVC.HRv] the library is closed at.  Its reach is [HeapSRRun.sr_run]
     over the run's tail, which is [hx_reach]'s own form; the free that stays on the binary's
     segments is [HeapSRVC.free_bin_vc] ([HeapSRVC.HRbin] is [hsr_bin HRv]); its kernel relation
     moves by [HeapSRVC.krel_vm_vc]; every other field reads [HS]'s part ([heap_extra_HS]). *)
  Lemma heap_extra_HRv {RT : RunTail.RunTail} (vlo vmid vhi : Z) :
    @Ref.ECH_LibTop.vdso_run_facts HCEIL (@RunTail.rt_tail RT) vlo vmid vhi ->
    heap_extra (@Ref.HeapSRVC.HRv HCEIL HSEC (@RunTail.rt_tail RT) vlo vmid vhi).
  Proof.
    intros VRF. pose proof (@heap_extra_HS RT) as HXS. destruct VRF.
    split.
    - intros Q c HQ _. exact HQ.
    - change (Ref.HeapSR_iface.free_sr_stmt (@Ref.HeapSRVC.HRbin HCEIL HSEC (@RunTail.rt_tail RT) vlo vmid vhi)).
      eapply Ref.HeapSRVC.free_bin_vc; eassumption.
    - exact (hx_mpres HS HXS).
    - exact (hx_live HS HXS).
    - intros s mo mo' K Hh Hl Hm Hv Hk Hr. eapply Ref.HeapSRVC.krel_vm_vc; eassumption.
    - intros s LB m RH. destruct RH as (RH & _ & _). exact (hx_statics HS HXS s LB m RH).
    - intros s mo K. destruct K as (K & _). exact (hx_krel_rdr HS HXS s mo K).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section AtMain.
    Context {AMB : Amb}.
    Variable sp0 : word.
    Variables a0s path : list byte.
    Variable envv : list (list byte).
    Variable rdraw : EntryDraw.
    Variable tid : word.
    Variable regs0 : bvmap 5 word.
    Variable mem0 : word -> option byte.
    Hypothesis Hva : valid_argv [a0s; path].
    Hypothesis Hve : valid_envp envv.
    Hypothesis Hvsp : valid_sp sp0.
    Hypothesis Htid : 0 < bv_unsigned tid < 2 ^ 22.
    (* [main_entry] is a record over the run's whole input ([RefStartup.v:68]); the input is
       the one [MainTop]'s Section TwoArgs builds from the same four components, and the entry
       is the image's literal, as [RefStartup.ref_startup] spells it.  The three Variables sit
       before [ME], its first user. *)
    Variables (mbase : word) (fs0 : Fs) (stdin0 : InputStream).
    Let inp : ProcInput := mkProcInputC [a0s; path] envv fs0 stdin0.
    Let entryw : word := (0xdd764 : word).
    Hypothesis ME : main_entry inp mbase entryw sp0 rdraw tid regs0 mem0.
    (* The launch facts the stack-image layer states its reads under ([RefLayout.v]), over the
       entry's [brk]; the caller has both from [RefStartup.ref_startup]'s own premises. *)
    Variable brk : word.
    Hypothesis Hvl : valid_launch inp.
    Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp.
    (* [comment removed for export] *)
    Hypothesis HCE : hceil = bv_unsigned sp0 - stack_max_size.
    Hypothesis HSE : hsecret = secret_of_draw rdraw /\ hcanary = bv_unsigned (canary_w rdraw).
    (* LPS 727298f3: [hvdso] is the launch's vDSO text base (AT_SYSINFO_EHDR, [Run.launch_auxv]) plus
       the clock_gettime entry's offset 1460, as [ref_realizes_spec_lim] builds the heap-ceiling record *)
    Hypothesis HVD : hvdso = bv_unsigned (vdso_text_base (in_kernel inp) sp0 mbase) + 1460.

    Let SPlo : 0x7fff80000000 <= bv_unsigned sp0 := proj1 Hvsp.
    Let SPhi : bv_unsigned sp0 <= 0x800000000000 := proj1 (proj2 Hvsp).

    (* The stack-image layer's premises, discharged by type ([RefMainEntry.v]). *)
    Ltac layout_sideT :=
      first [ eassumption | exact Hva | exact Hve | exact (proj2 (proj2 Hvsp))
            | (unfold sp_window_lo; pose proof SPlo; lia) | (unfold sp_window_hi; pose proof SPhi; lia) ].

    (* [comment removed for export] *)
    Lemma D_main_threads : forall segs, rdn segs (D_main inp sp0 rdraw tid) (Z_to_bv 64 0x30f708) 1 = Some [Z_to_bv 8 1].
    Proof.
      intros segs. pose proof (u64_range tid). pose proof (RefStartupFacts.len_av inp Hva). pose proof SPlo. pose proof SPhi.
      unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
      pose proof (rdn_wbytes_hit segs [Z_to_bv 8 1]) as Hh. cbn [length] in Hh. apply Hh. unorm; lia.
    Qed.
    Lemma D_main_tls_size : forall segs, rdn segs (D_main inp sp0 rdraw tid) (Z_to_bv 64 0x30f720) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xe0)).
    Proof.
      intros segs. pose proof (u64_range tid). pose proof (RefStartupFacts.len_av inp Hva). pose proof SPlo. pose proof SPhi.
      unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel. apply rdn_wbytes_hit8. unorm; lia.
    Qed.
    Lemma D_main_tls_align : forall segs, rdn segs (D_main inp sp0 rdraw tid) (Z_to_bv 64 0x30f728) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 8)).
    Proof.
      intros segs. pose proof (u64_range tid). pose proof (RefStartupFacts.len_av inp Hva). pose proof SPlo. pose proof SPhi.
      unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel. apply rdn_wbytes_hit8. unorm; lia.
    Qed.

    (* [comment removed for export] *)
    Lemma rw_cells_of_rdn : forall m (A : Z) cs,
      cells_wf cs ->
      rdn RSEGS m (Z_to_bv 64 A) (length (cells_bytes cs)) = Some (cells_bytes cs) ->
      store_ok RSEGS m (Z_to_bv 64 A) (cells_size cs) = true ->
      0 <= A -> A + Z.of_nat (cells_size cs) <= 2 ^ 64 ->
      rw_cells rsegs m A cs.
    Proof.
      intros m A cs Hwf HD HS HA HAn. pose proof (cells_bytes_length cs Hwf) as HL.
      split; [split; [exact Hwf | apply rdn_bytes_at; [exact HD | lia | rewrite HL; lia]]|].
      split; [lia|]. split; [lia|]. intros i Hi. rewrite wa_eq.
      replace (Z_to_bv 64 (A + i)) with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 A) + i)) by (rewrite u_small by lia; reflexivity).
      apply (store_ok_all RSEGS m (cells_size cs) (Z_to_bv 64 A)); [rewrite u_small by lia; lia | exact HS | rewrite !u_small by lia; lia].
    Qed.

    (* [comment removed for export] *)
    Lemma rw_cell1 : forall m (A : Z) c,
      cell_wf c ->
      rdn RSEGS m (Z_to_bv 64 A) (csize c) = Some (cbytes c) ->
      store_ok RSEGS m (Z_to_bv 64 A) (csize c) = true -> 0 <= A -> A + Z.of_nat (csize c) <= 2 ^ 64 ->
      rw_cells rsegs m A [c].
    Proof.
      intros m A c Hwf HD HS HA HAn. apply rw_cells_of_rdn; cbn [cells_wf cells_bytes cells_size]; rewrite ?app_nil_r, ?Nat.add_0_r;
        [split; [exact Hwf | exact I] | rewrite (cbytes_length c Hwf); exact HD | exact HS | exact HA | exact HAn].
    Qed.
    Ltac rw_split :=
      lazymatch goal with |- rw_cells _ ?m ?A (?c :: ?rest) =>
        lazymatch rest with
        | [] => idtac
        | _ => apply (proj2 (rw_cells_app rsegs m A [c] rest)); cbn [cells_size csize Nat.add]; split; [| rw_split]
        end end.
    Ltac rw_one RD := apply rw_cell1; [cbn; first [reflexivity | exact I] | cbn [csize cbytes]; RD | cbn [csize]; apply store_ok_wseg; vm_compute; reflexivity | lia | cbn; lia].

    Lemma bytes_at_u64s : forall m (A : Z) ws,
      0 <= A -> A + 8 * Z.of_nat (length ws) < 2 ^ 64 ->
      (forall j, (j < length ws)%nat -> rdn RSEGS m (Z_to_bv 64 (A + 8 * Z.of_nat j)) 8 = Some (word_to_le_bytes 8 (nth j ws (Z_to_bv 64 0)))) ->
      rdn RSEGS m (Z_to_bv 64 A) (8 * length ws) = Some (u64s ws).
    Proof.
      intros m A ws. revert A. induction ws as [|w ws IH]; intros A HA HAn HW; [reflexivity|].
      cbn [length] in *. replace (8 * S (length ws))%nat with (8 + 8 * length ws)%nat by lia. cbn [u64s].
      apply rdn_app_Z; [| | lia | lia].
      - pose proof (HW 0%nat ltac:(lia)) as H0. rewrite Z.mul_0_r, Z.add_0_r in H0. exact H0.
      - change (Z.of_nat 8) with 8. apply IH; [lia | lia |]. intros j Hj.
        replace (A + 8 + 8 * Z.of_nat j) with (A + 8 * Z.of_nat (S j)) by lia. apply (HW (S j)). lia.
    Qed.


    (* [RefMainEntry]'s Section MainEntryProofs exports are [Proof using All]; both argv/envp
       ties are [eq_refl] on this input. *)
    Let E := E0 inp sp0 a0s path envv rdraw tid regs0.
    Let HK : know_ok RSEGS E mem0 kn_main :=
      main_know_ok inp mbase entryw sp0 brk a0s path envv rdraw tid regs0 mem0
        Hva Hve Hvsp Htid eq_refl eq_refl Hvl Hlau ME.

    Lemma kn_main_entry : forall e, In e kn_main -> kentry_ok RSEGS E mem0 e.
    Proof. intros e He. exact (proj1 (Forall_forall _ _) HK e He). Qed.

    Lemma none_high : forall i, 0x30f778 <= i < 0x311000 -> mem0 (Z_to_bv 64 i) = None.
    Proof.
      intros i Hi. pose proof (kn_main_entry (KImg 0x30f778 0x311000) ltac:(unfold kn_main, kn_stack, kn_auxv, kn_image; in_solve)) as K.
      cbn [kentry_ok] in K. destruct K as (_ & _ & K). apply K. exact Hi.
    Qed.

    (* [comment removed for export] *)
    Lemma rdn_D : forall (a : Z) n, 0 <= a -> a + Z.of_nat n <= 0x311000 ->
      rdn RSEGS mem0 (Z_to_bv 64 a) n = rdn RSEGS (D_main inp sp0 rdraw tid) (Z_to_bv 64 a) n.
    Proof.
      intros a n Ha Hn. pose proof SPlo. apply (main_entry_rdn_data _ _ _ _ _ _ _ _ ME). rewrite u_small by lia. rewrite stack_max_size_val. lia.
    Qed.
    (* the record binders inferred from [ME] ([RefStartupFacts.v]). *)
    Ltac rd_miss a n := rewrite (main_entry_rdn_image _ _ _ _ SPlo _ _ _ _ ME RSEGS a n) by (vm_compute; reflexivity); vm_refl_bv.

    (* Word [j] of the auxv for EVERY word of the vector, [j < 2 * auxv_count rseq]:
       [RefMainEntry.auxv_word_at] with its bound widened to the launch's own, since
       [Ref/RMallocTree.rauxv_ok] claims the whole vector, the AT_RSEQ pairs and AT_NULL too. *)
    Lemma auxv_word_atR : forall j, (j < 2 * auxv_count (kb_rseq (in_kernel inp)))%nat ->
      rdn RSEGS mem0 (Z_to_bv 64 (bv_unsigned (auxvp inp sp0) + 8 * Z.of_nat j)) 8
      = Some (word_to_le_bytes 8 (nth j (auxv_words (launch_auxv inp sp0 mbase) RPH entryw
                                            (in_uid inp) (in_gid inp) (in_hwcap inp)
                                            (rnd inp sp0 a0s path envv)
                                            (at_execfn_ptr (ed_top rdraw) (in_execfn inp)))
                                      (Z_to_bv 64 0))).
    Proof.
      intros j Hj. pose proof SPlo as HLO. pose proof SPhi as HHI.
      assert (Hac : (auxv_count (kb_rseq (in_kernel inp)) <= 29)%nat)
        by (unfold auxv_count; destruct (kb_rseq (in_kernel inp)); lia).
      destruct (auxvp_u inp mbase entryw sp0 brk a0s path envv rdraw tid regs0 mem0
                  Hva Hve Hvsp Htid eq_refl eq_refl Hvl Hlau ME) as [Hu Hb].
      rewrite (main_entry_rdn_above _ _ _ _ _ _ _ _ ME) by (rewrite u_small by lia; lia).
      pose proof (rdn_wmem_stack RSEGS inp mbase RPH entryw sp0 rdraw) as Hw; unfold wmem in Hw; rewrite Hw by (rewrite u_small by lia; lia).
      replace (Z_to_bv 64 (bv_unsigned (auxvp inp sp0) + 8 * Z.of_nat j))
        with ((sp0 + nat_to_word (auxv_off (in_argv inp) (in_envp inp) + 8 * j))%bv)
        by (change (in_argv inp) with [a0s; path]; change (in_envp inp) with envv; rewrite w_add_nat; f_equal; lia).
      assert (Hr : rdn RSEGS (stack_to_mem sp0 (entry_stack_image inp mbase RPH entryw sp0 rdraw))
                     ((sp0 + nat_to_word (auxv_off (in_argv inp) (in_envp inp) + 8 * j))%bv) 8
                   = Some (word_le8 (nth j (auxv_words (launch_auxv inp sp0 mbase) RPH entryw
                                              (in_uid inp) (in_gid inp) (in_hwcap inp)
                                              (at_random_ptr sp0 (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))
                                              (at_execfn_ptr (ed_top rdraw) (in_execfn inp)))
                                       (Z_to_bv 64 0))))
        by (eapply (read_auxv_word RSEGS Sv48 inp mbase RPH entryw sp0 brk rdraw); first [ layout_sideT | exact Hj ]).
      rewrite Hr. rewrite n_to_le_8_spec. reflexivity.
    Qed.

    Lemma main_entry_heap :
      hs_RHEAP HS (ps_init (reservedZ rsegs)) [] mem0 /\ hs_rauxv_ok HS mem0 (bv_unsigned sp0).
    Proof.
      pose proof SPlo as Hlo. pose proof SPhi as Hhi. hcb. hsb. destruct HSE as [HS1 HS2].
      destruct (auxvp_u inp mbase entryw sp0 brk a0s path envv rdraw tid regs0 mem0
                  Hva Hve Hvsp Htid eq_refl eq_refl Hvl Hlau ME) as [AU1 AU2].
      destruct (rnd_u inp mbase entryw sp0 brk a0s path envv rdraw tid regs0 mem0
                  Hva Hve Hvsp Htid eq_refl eq_refl Hvl Hlau ME) as (RN1 & RN2 & RN3).
      assert (EAUX : auxv_w inp sp0 = auxvp inp sp0) by reflexivity.
      (* [comment removed for export] *)
      assert (LC : rw_cells rsegs mem0 0x30f708 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0)]).
      { rw_split.
        - rw_one ltac:(rewrite rdn_D by lia; apply D_main_threads).
        - rw_one ltac:(rd_miss 0x30f709 1%nat).
        - rw_one ltac:(rd_miss 0x30f70a 1%nat).
        - rw_one ltac:(rd_miss 0x30f70b 1%nat).
        - rw_one ltac:(rd_miss 0x30f70c 4%nat). }
      assert (LC2 : rw_cells rsegs mem0 0x30f710 [C8 (auxv_w inp sp0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 224); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 0);
                                           C8 (Z_to_bv 64 4096); CB 48 (repeat (Z_to_bv 8 0) 48)]).
      { rw_split.
        - rw_one ltac:(rewrite rdn_D by lia;
                       apply (D_main_auxvp inp mbase entryw sp0 brk a0s path envv rdraw tid regs0 mem0
                                Hva Hve Hvsp Htid eq_refl eq_refl Hvl Hlau ME)).
        - rw_one ltac:(rd_miss 0x30f718 8%nat).
        - rw_one ltac:(rewrite rdn_D by lia; apply D_main_tls_size).
        - rw_one ltac:(rewrite rdn_D by lia; apply D_main_tls_align).
        - rw_one ltac:(rd_miss 0x30f730 8%nat).
        - (* [RefStartupFacts.D_main_pagesize]; its premises by type *)
          rw_one ltac:(rewrite rdn_D by lia; eapply D_main_pagesize; first [exact Hva | exact Hlo | exact Hhi]).
        - rw_one ltac:(rd_miss 0x30f740 48%nat). }
      assert (GOT : rw_cells rsegs mem0 0x2db120 [C8 (Z_to_bv 64 0x30f4b8)]) by (rw_one ltac:(rd_miss 0x2db120 8%nat)).
      assert (CAN : rw_cells rsegs mem0 0x30f4b8 [C8 (Z_to_bv 64 hcanary)]).
      { rw_one ltac:(rewrite rdn_D by lia; rewrite HS2, Z_to_bv_bv_unsigned;
                      change (le8 (canary_w rdraw)) with (word_to_le_bytes 8 (canary_w rdraw)); rewrite <- (canary_bytes_w rdraw);
                      eapply D_main_guard; first [exact Hva | exact Hlo | exact Hhi]). }
      assert (MI : mem_inv rsegs mem0) by (apply ro_none_mem_inv; exact (main_entry_ro_none _ _ _ sp0 rdraw tid regs0 mem0 Hvsp ME)).
      destruct (RHEAP_init_proof mem0 (auxv_w inp sp0) (Z_to_bv 8 1) (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 64 0)
                  (Z_to_bv 64 0) (Z_to_bv 64 224) (Z_to_bv 64 8) (Z_to_bv 64 0) (repeat (Z_to_bv 8 0) 48) eq_refl
                  ltac:(intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply none_high; lia)
                  LC LC2 GOT CAN ltac:(intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply none_high; lia) MI) as [RH AUXC].
      split; [exact RH|].
      (* [Ref/RMallocTree.rauxv_ok] claims the whole vector the launch writes, keyed by
         [Lib/AuxvTable]'s generator: the value record is the model's own
         ([AuxvTable.auxv_vals_of], equal to the model's words by [AuxvTable.auxv_list_eq]), AT_RANDOM
         and AT_EXECFN are the launch's pointers, and the rseq shape is the run's [kb_rseq]. *)
      cbn [hs_rauxv_ok HS]. unfold rauxv_ok.
      set (rndw := rnd inp sp0 a0s path envv) in *. set (auxw := auxvp inp sp0) in *.
      exists (bv_unsigned auxw),
             (auxv_vals_of (launch_auxv inp sp0 mbase) RPH entryw (in_uid inp) (in_gid inp) (in_hwcap inp)),
             (bv_unsigned rndw), (bv_unsigned (at_execfn_ptr (ed_top rdraw) (in_execfn inp))),
             (kb_rseq (in_kernel inp)).
      pose proof (u64_range auxw). pose proof (u64_range rndw).
      pose proof (u64_range (at_execfn_ptr (ed_top rdraw) (in_execfn inp))).
      pose proof (auxv_vec_bytes_range (kb_rseq (in_kernel inp))) as Hvb.
      assert (Hac : (auxv_count (kb_rseq (in_kernel inp)) <= 29)%nat)
        by (unfold auxv_count; destruct (kb_rseq (in_kernel inp)); lia).
      (* the vector [Ref/RMallocTree.rauxv_ok] claims ([HeapSR_iface] has a list of the same name) *)
      assert (EL : RMallocTree.rauxv_list (auxv_vals_of (launch_auxv inp sp0 mbase) RPH entryw (in_uid inp) (in_gid inp) (in_hwcap inp))
                     (bv_unsigned rndw) (bv_unsigned (at_execfn_ptr (ed_top rdraw) (in_execfn inp))) (kb_rseq (in_kernel inp))
                   = auxv_words (launch_auxv inp sp0 mbase) RPH entryw (in_uid inp) (in_gid inp) (in_hwcap inp)
                       rndw (at_execfn_ptr (ed_top rdraw) (in_execfn inp)))
        by exact (auxv_list_eq (launch_auxv inp sp0 mbase) RPH entryw (in_uid inp) (in_gid inp) (in_hwcap inp)
                    rndw (at_execfn_ptr (ed_top rdraw) (in_execfn inp))).
      assert (LEN : length (auxv_words (launch_auxv inp sp0 mbase) RPH entryw (in_uid inp) (in_gid inp) (in_hwcap inp)
                              rndw (at_execfn_ptr (ed_top rdraw) (in_execfn inp)))
                    = (2 * auxv_count (kb_rseq (in_kernel inp)))%nat)
        by (rewrite <- EL; unfold RMallocTree.rauxv_list; rewrite length_map; apply length_auxv_words_Z).
      repeat match goal with |- _ /\ _ => split end; try (rewrite HCE, stack_max_size_val; lia); try lia.
      - unfold wz. rewrite Z_to_bv_bv_unsigned. rewrite EAUX in AUXC. exact AUXC.
      - rewrite EL. apply rdn_bytes_at; [| lia | rewrite u64s_length, LEN; lia].
        rewrite u64s_length. apply bytes_at_u64s; [lia | rewrite LEN; lia |].
        intros j Hj. rewrite LEN in Hj. subst auxw rndw. exact (auxv_word_atR j Hj).
      - (* [comment removed for export] *)
        apply rdn_bytes_at; [| lia | replace (length (le8 (wz hsecret))) with 8%nat by reflexivity; lia].
        replace (length (le8 (wz hsecret))) with 8%nat by reflexivity.
        rewrite (main_entry_rdn_above _ _ _ _ _ _ _ _ ME) by (rewrite u_small by lia; lia).
        pose proof (rdn_wmem_stack RSEGS inp mbase RPH entryw sp0 rdraw) as Hw. unfold wmem in Hw. rewrite Hw by (rewrite u_small by lia; lia).
        (* [RefLayout.rnd_facts]; its premises by type *)
        pose proof (rnd_facts RSEGS Sv48 inp mbase RPH entryw sp0 brk rdraw) as RF.
        repeat match type of RF with ?P -> _ =>
          let H := fresh in assert (H : P) by layout_sideT; specialize (RF H) end.
        destruct RF as (_ & _ & _ & _ & RB).
        subst rndw. unfold rnd. rewrite (RB 8%nat 8%nat ltac:(lia)).
        f_equal. unfold le8, wz. rewrite HS1. unfold secret_of_draw, secret_bytes_of_draw.
        symmetry. apply le8_bytes_le_val. rewrite length_firstn, length_skipn, length_at_random_bytes. reflexivity.
      - apply auxv_vals_ok_of; vm_compute; reflexivity.
      - (* AT_SYSINFO_EHDR is the vDSO text base ([AuxvTable.auxv_vals_of], [Run.launch_auxv]) *)
        rewrite HVD. reflexivity.
    Qed.
  End AtMain.
End Top.

(* A walk over the binary's own segments, from a state whose read-only backing is the binary's,
   is a walk over the run's segment list from the same state with the run's backing:
   [RomStable.realizes_wrom] then [RomStable.realizes_run_segments], as [RomStable.run_init]. *)
Lemma realizes_lift_run : forall inp (sp mbase pc : word) regs mem mo T,
  realizes RSEGS (mkCfg (mkst regs pc mem (seg_rom RSEGS)) mo) T ->
  realizes (run_segments RSEGS inp sp mbase)
    (mkCfg (mkst regs pc mem (seg_rom (run_segments RSEGS inp sp mbase))) mo) T.
Proof.
  intros inp sp mbase pc regs mem mo T H.
  apply (RomStable.realizes_run_segments RSEGS inp sp mbase); [reflexivity |].
  exact (RomStable.realizes_wrom RSEGS eq_refl _ T H (seg_rom (run_segments RSEGS inp sp mbase))
           (RomStable.rom_ext_run_segments RSEGS inp sp mbase)).
Qed.

(* The entry memory holds no byte of a window at or above 0x311000 and below the stack's
   reservation: below [sp0 - stack_max_size] it is [D_main] ([RefStartup.main_entry_mem_data]),
   whose writes all lie below 0x311000 ([RefStartupDefs.D_main]). *)
Lemma main_entry_vclean {AMB : Amb} : forall inp (mbase entry sp0 : word) rdraw tid regs
    (mem0 : word -> option byte) (vlo vhi : Z),
  main_entry inp mbase entry sp0 rdraw tid regs mem0 ->
  0x311000 <= vlo -> vhi <= bv_unsigned sp0 - stack_max_size ->
  VdsoClean.vclean vlo vhi mem0.
Proof.
  intros inp mbase entry sp0 rdraw tid regs mem0 vlo vhi ME Hlo Hhi x Hx.
  rewrite (main_entry_mem_data _ _ _ _ _ _ _ _ ME x) by lia.
  unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc.
  repeat (rewrite MemSplit.wbytes_outside
            by (rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia)).
  reflexivity.
Qed.

(* The launch's model keeps the vDSO pair in its reserved ledger, the vvar entry holding
   [[vd_lo, vd_mid)] and the text entry [[vd_mid, vd_top)]: [State.vm_reserved_init_model] and
   [State.vdso_top_init_model], as [MallocSR_init.KM_init] reads them. *)
Lemma pair_inv_model0 : forall tid brk (mbase sp : word) rnd lim inp,
  valid_sp sp -> valid_mmap_base mbase ->
  Ref.HeapSRRun.pair_inv (Ref.VdsoLaunch.vd_lo (in_kernel inp) sp mbase)
    (Ref.VdsoLaunch.vd_mid (in_kernel inp) sp mbase) (Ref.VdsoLaunch.vd_top sp mbase)
    (model0 tid brk mbase sp rnd lim inp).
Proof.
  intros tid brk mbase sp rnd lim inp Hsp Hmb.
  assert (ET : vdso_top (m_vmmaps (init_model (segments_reserved RSEGS) brk mbase sp lim inp))
               = Ref.VdsoLaunch.vd_top sp mbase).
  { rewrite vdso_top_init_model. unfold Ref.VdsoLaunch.vd_top. symmetry. apply page_round_down_Z_min_r. }
  assert (ER : vm_reserved (m_vmmaps (init_model (segments_reserved RSEGS) brk mbase sp lim inp))
               = segments_reserved RSEGS ++ vdso_reserved (in_kernel inp) (Ref.VdsoLaunch.vd_top sp mbase)).
  { rewrite vm_reserved_init_model, ET. reflexivity. }
  assert (W1 : MmVdso.win_in (Ref.VdsoLaunch.vd_lo (in_kernel inp) sp mbase) (Ref.VdsoLaunch.vd_mid (in_kernel inp) sp mbase)
                 (vdso_reserved (in_kernel inp) (Ref.VdsoLaunch.vd_top sp mbase)))
    by (eapply Ref.VdsoLaunch.pair_win_lo; eassumption).
  assert (W2 : MmVdso.win_in (Ref.VdsoLaunch.vd_mid (in_kernel inp) sp mbase) (Ref.VdsoLaunch.vd_top sp mbase)
                 (vdso_reserved (in_kernel inp) (Ref.VdsoLaunch.vd_top sp mbase)))
    by (eapply Ref.VdsoLaunch.pair_win_hi; eassumption).
  assert (I : incl (vdso_reserved (in_kernel inp) (Ref.VdsoLaunch.vd_top sp mbase))
                   (segments_reserved RSEGS ++ vdso_reserved (in_kernel inp) (Ref.VdsoLaunch.vd_top sp mbase)))
    by (intros e He; apply in_or_app; right; exact He).
  unfold Ref.HeapSRRun.pair_inv, MmVdso.mm_vinv.
  change (m_kernel (model0 tid brk mbase sp rnd lim inp)) with (in_kernel inp).
  change (m_vmmaps (model0 tid brk mbase sp rnd lim inp))
    with (m_vmmaps (init_model (segments_reserved RSEGS) brk mbase sp lim inp)).
  rewrite ET, ER.
  exact (conj (conj W1 I) (conj W2 I)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithLib.
  (* [comment removed for export] *)
  Hypothesis FZ_p : OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref.ECH_LibTop.fuzz_vc_type.

(* The run against [run_segments] from [Run.init_config] over it, as [RefStartup.ref_startup]
   states it.  The auxv's AT_SYSINFO_EHDR is the text base of the vDSO pair the launch maps
   ([VdsoLaunch.vdso_text_base_pair]).  The launch facts are premises the caller PROVES from
   [Run.valid_input] ([valid_input_channel_reader], [valid_input_launch]) and [Run.valid_entry]
   ([valid_entry_sv48]). *)
Theorem ref_realizes_spec_lim :
  forall (sp brk mbase : word) (rnd : EntryDraw) (lim : Z) (inp : ProcInput),
    valid_sp sp -> valid_brk RSEGS brk -> 2 ^ 31 <= lim ->   (* [comment removed for export] *)
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
    valid_mmap_base mbase ->   (* from [Run.valid_entry]; [KM_init] reads it *)
    in_channel_reader inp = true ->
    valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
    realizes (run_segments RSEGS inp sp mbase)
      (init_config (run_segments RSEGS inp sp mbase) Plain.M.init_pc RPH sp brk mbase rnd lim inp)
      (spec (in_argv inp) (in_fs inp)).
Proof.
  intros sp brk mbase rnd lim inp Hsp Hbrk Hlim Hfit Hva Hve Hfs Hmb Hrd Hvl Hlau.
  (* [hvdso]: the vDSO's clock_gettime entry, AT_SYSINFO_EHDR ([Run.launch_auxv]) plus its
     offset 1460 in the image ([Lib/VdsoImg.rvdso_cgt_off_measured]) *)
  pose (HCEIL := mkHeapCeil (bv_unsigned sp - stack_max_size) (alloc_top_range sp Hsp)
                   (bv_unsigned (vdso_text_base (in_kernel inp) sp mbase) + 1460)).
  pose (HSEC := heap_secret_of_draw rnd (canary_w rnd)).
  apply (ref_startup sp brk mbase rnd lim inp); try assumption.
  intros tid regs mem Htid ME.
  replace (with_tid tid (model_init inp brk mbase sp rnd lim)) with (model0 tid brk mbase sp rnd lim inp)
    by (unfold model_init, model0; rewrite RomStable.segments_reserved_run_segments; reflexivity).
  (* The run's list is the binary's segments and the launch's vDSO/vvar pair
     ([Run.run_segments]): the tail [RunTail.run_tail_of] names, the one main's walk is over. *)
  pose (RT := RunTail.run_tail_of (in_kernel inp) sp mbase).
  change (run_segments RSEGS inp sp mbase) with (RSEGS ++ @RunTail.rt_tail RT).
  (* The library is closed at the run instance [HeapSRVC.HRv] over that tail, with the pair's
     base, text base and top as [Run.vdso_segments] (Run.v:290-306) places them; [VdsoLaunch]
     proves the launch facts its laws and time() take, and the launch's model keeps the pair in
     its reserved ledger ([pair_inv_model0]). *)
  assert (VRF0 : @Ref.ECH_LibTop.vdso_run_facts HCEIL (vdso_segments (in_kernel inp) sp mbase)
                   (Ref.VdsoLaunch.vd_lo (in_kernel inp) sp mbase) (Ref.VdsoLaunch.vd_mid (in_kernel inp) sp mbase)
                   (Ref.VdsoLaunch.vd_top sp mbase))
    by (eapply Ref.VdsoLaunch.vdso_launch_facts; first [eassumption | reflexivity]).
  pose proof (pair_inv_model0 tid brk mbase sp rnd lim inp Hsp Hmb) as PI0.
  set (vlo := Ref.VdsoLaunch.vd_lo (in_kernel inp) sp mbase) in *.
  set (vmid := Ref.VdsoLaunch.vd_mid (in_kernel inp) sp mbase) in *.
  set (vhi := Ref.VdsoLaunch.vd_top sp mbase) in *.
  assert (VRF : @Ref.ECH_LibTop.vdso_run_facts HCEIL (@RunTail.rt_tail RT) vlo vmid vhi) by exact VRF0.
  clear VRF0.
  pose proof (proj1 (Ref.ECH_LibTop.heap_vc_of_facts HCEIL HSEC (@RunTail.rt_tail RT) vlo vmid vhi VRF)) as HH.
  pose proof (@heap_extra_HRv HCEIL HSEC RT vlo vmid vhi VRF) as HX.
  assert (HCE0 : @hceil HCEIL = bv_unsigned sp - stack_max_size) by reflexivity.
  assert (HVD0 : @hvdso HCEIL = bv_unsigned (vdso_text_base (in_kernel inp) sp mbase) + 1460) by reflexivity.
  assert (HTS : bv_unsigned sp <= TASK_SIZE)
    by (pose proof (proj1 (proj2 Hsp)) as L; unfold sp_window_hi in L; unfold TASK_SIZE; lia).
  clearbody HCEIL RT vlo vmid vhi.
  lazymatch goal with |- realizes _ (mkCfg (mkst _ ?pc _ _) _) _ => replace pc with (Z_to_bv 64 0xdd8b8) by (apply bv_eq; reflexivity) end.
  (* This unit's [Amb] carries no /tmp field: the input is canonicalised with its /tmp folded
     into the image ([Amb.init_model_canon]); [main_entry] and the launch facts read neither,
     so they hold of the canonical input by conversion. *)
  pose proof (main_entry_canon _ _ _ _ _ _ _ _ ME) as ME'. pose proof (valid_launch_canon _ Hvl) as Hvl'.
  pose proof (entry_launch_canon _ _ _ _ _ _ Hlau) as Hlau'. clear ME Hvl Hlau.
  change (in_channel_reader inp) with (@a_channel_reader (amb_of inp)) in Hrd.
  assert (EM : model0 tid brk mbase sp rnd lim inp
               = model0 tid brk mbase sp rnd lim (@mkProcInputC (amb_of inp) (in_argv inp) (in_envp inp) (in_fs inp) (in_stdin inp)))
    by (unfold model0; rewrite <- init_model_canon; reflexivity).
  rewrite EM in PI0 |- *. clear EM.
  change (in_kernel inp) with (@a_kernel (amb_of inp)) in HVD0.
  set (AMB := amb_of inp) in *. set (argv := in_argv inp) in *. set (envp := in_envp inp) in *.
  set (fs0 := in_fs inp) in *. set (stdin0 := in_stdin inp) in *.
  clearbody AMB argv envp fs0 stdin0. clear inp.
  rename ME' into ME, Hvl' into Hvl, Hlau' into Hlau.
  (* [comment removed for export] *)
  destruct argv as [|a0s [|path [|x l]]].
  - apply (RunTail.realizes_lift_rt RSEGS MainSegs.vdso_image_RSEGS).
    apply (ref_usage sp [] envp rnd tid regs mem brk mbase lim fs0 stdin0 Hva Hve Hsp Htid ME Hvl Hlau ltac:(cbn; lia) Hfit Hrd).
  - apply (RunTail.realizes_lift_rt RSEGS MainSegs.vdso_image_RSEGS).
    apply (ref_usage sp [a0s] envp rnd tid regs mem brk mbase lim fs0 stdin0 Hva Hve Hsp Htid ME Hvl Hlau ltac:(cbn; lia) Hfit Hrd).
  - destruct (@main_entry_heap HCEIL HSEC AMB sp a0s path envp rnd tid regs mem Hva Hve Hsp Htid mbase fs0 stdin0 ME brk Hvl Hlau
                HCE0 (conj eq_refl eq_refl) HVD0) as [RH AUX].
    (* the run instance's heap relation adds the clean window and every block's distance from
       it (none yet); the entry memory holds no byte of the window *)
    pose proof (@Ref.ECH_LibTop.vr_w HCEIL _ _ _ _ VRF) as (W1 & W2 & W3 & W4).
    assert (Whi : vhi <= bv_unsigned sp - stack_max_size) by lia.
    pose proof (main_entry_vclean _ _ _ _ _ _ _ _ vlo vhi ME W1 Whi) as VC.
    apply (@main_realizes HCEIL RT (@Ref.HeapSRVC.HRv HCEIL HSEC (@RunTail.rt_tail RT) vlo vmid vhi) HH HX
             sp tid brk mbase rnd lim (@mkProcInputC AMB [a0s; path] envp fs0 stdin0) regs mem
             (ps_init (reservedZ rsegs)) (bv_unsigned sp) Hsp Hfit Hva Hve Hfs Htid).
    + rewrite HCE0, stack_max_size_val. lia.
    + exact ME.
    + exact Hvl.
    + exact Hlau.
    + exact (conj RH (conj VC (@Forall_nil _ _))).
    + (* [model0] carries the launch's vDSO draw ([MainDefs.model0]); the kernel relation does
         not read it, so it is [KM_init]'s model moved by [KM_vm]; the pair is [pair_inv_model0]'s *)
      assert (KM0 : KM (ps_init (reservedZ rsegs))
                      (model0 tid brk mbase sp rnd lim (@mkProcInputC AMB [a0s; path] envp fs0 stdin0))).
      { unfold model0.
        apply (KM_vm _ (with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp lim
                                        (@mkProcInputC AMB [a0s; path] envp fs0 stdin0)))).
        all: first [ apply KM_init; [exact Hbrk | exact Hsp | unfold BUDCAP; exact Hlim | exact (eq_sym HCE0) | exact Hmb | exact Hrd]
                   | (split; [reflexivity | split; [reflexivity | exact Hrd]])
                   | reflexivity ]. }
      exact (conj KM0 PI0).
    + (* the auxv bound is the launch's sp, below [TASK_SIZE] *)
      exact (conj AUX HTS).
    + pose proof (proj1 Hsp) as L. unfold sp_window_lo in L. pose proof (u64_range sp). lia.
    + apply (@target_run_sound HCEIL RT (@Ref.HeapSRVC.HRv HCEIL HSEC (@RunTail.rt_tail RT) vlo vmid vhi) HH HX).
      exact (FZ_p HCEIL HSEC (@RunTail.rt_tail RT) vlo vmid vhi VRF).
  - apply (RunTail.realizes_lift_rt RSEGS MainSegs.vdso_image_RSEGS).
    apply (ref_usage sp (a0s :: path :: x :: l) envp rnd tid regs mem brk mbase lim fs0 stdin0 Hva Hve Hsp Htid ME Hvl Hlau ltac:(cbn; lia) Hfit Hrd).
Qed.

Theorem ref_realizes_spec :
  forall (sp brk mbase : word) (rnd : EntryDraw) (inp : ProcInput),
    valid_sp sp -> valid_brk RSEGS brk ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
    valid_mmap_base mbase ->
    in_channel_reader inp = true ->
    valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
    realizes (run_segments RSEGS inp sp mbase)
      (init_config (run_segments RSEGS inp sp mbase) Plain.M.init_pc RPH sp brk mbase rnd source_alloc_limit inp)
      (spec (in_argv inp) (in_fs inp)).
Proof.
  intros sp brk mbase rnd inp Hsp Hbrk Hfit Hva Hve Hfs Hmb Hrd Hvl Hlau.
  apply ref_realizes_spec_lim; try assumption. unfold source_alloc_limit. lia.
Qed.

(* [comment removed for export] *)
Theorem ref_realizes_spec_san :
  forall (sp brk mbase : word) (rnd : EntryDraw) (inp : ProcInput),
    valid_sp sp -> valid_brk RSEGS brk ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
    valid_mmap_base mbase ->
    in_channel_reader inp = true ->
    valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
    realizes (run_segments RSEGS inp sp mbase)
      (init_config (run_segments RSEGS inp sp mbase) Plain.M.init_pc RPH sp brk mbase rnd sanitizer_source_limit inp)
      (spec (in_argv inp) (in_fs inp)).
Proof.
  intros sp brk mbase rnd inp Hsp Hbrk Hfit Hva Hve Hfs Hmb Hrd Hvl Hlau.
  apply ref_realizes_spec_lim; try assumption. unfold sanitizer_source_limit. lia.
Qed.
End WithLib.
