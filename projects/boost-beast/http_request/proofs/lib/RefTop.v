(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.boost_beast.http_request.images Require Import Plain.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import Amb
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Frame StepTac StartupTac ArgvEnv RefLayout
  Spec SReach RefStartupDefs RefStartup RefStartupFacts RefMainEntry LibDiagKn LibDiagKnMain LibTail
  SymExec2 SymExec2Sound SymRun SymDrive SymDriveX HeapCeil HeapSecret
  MainDefs MainArith MainMem MainLoop MainTop TargetRun.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Mem Cells CellsX Arr Step Frame MState SysStep.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prog AllocTop MmNodes KLink KLink3.
From OSSVerify.Proofs.boost_beast.http_request.lib.Agent Require Import Malloc_iface.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ref Require Import RSegs RMallocTree RMalloc_iface RMalloc_ifaceP RMalloc_iface_stmt HeapSR_iface
  MallocSR MallocSR_init MallocSR_hyps MallocSR_closed XRep XFuzz_stmt XFuzz_stmt2.
Import ListNotations.
Import SymExec2.SX2. Import SymExec2Sound.SX2S.
Import OSSVerify.Proofs.boost_beast.http_request.lib.PropExec.
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
  Lemma heap_extra_HS : heap_extra HS.
  Proof.
    split.
    - apply hx_sr_proof.
    - apply hx_mpres_proof.
    - cbn [hs_LIVE_MAX hs_LIVE_CNT_MAX HS]. unfold HBYTES, HCNT. lia.
    - cbn [hs_KREL HS]. intros s mo mo' K Hh Hl Hm Hv. apply (KM_vm s mo mo' K).
      + destruct K as (L & _ & KL & _). destruct (kb_minv _ _ _ KL) as [A1 A2]. split; [rewrite Hl; exact A1 | rewrite Hm; exact A2].
      + rewrite Hh. exact (proj1 (KM_halted_lazy s mo K)).
      + exact Hv.
    - intros s LB m RH. pose proof (hx_statics_proof s LB m RH) as (H1 & H2 & H3). rewrite !rdn_same in *.
      split; [exact H1|]. split; [exact H2|]. exists hcanary. split; [exact H3 | hsb; lia].
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
    Hypothesis ME : main_entry sp0 [a0s; path] envv rdraw tid regs0 mem0.
    (* [comment removed for export] *)
    Hypothesis HCE : hceil = bv_unsigned sp0 - stack_max_size.
    Hypothesis HSE : hsecret = secret_of_draw rdraw /\ hcanary = bv_unsigned (canary_w rdraw).

    Let av : list (list byte) := [a0s; path].
    Let SPlo : 0x7fff80000000 <= bv_unsigned sp0 := proj1 Hvsp.
    Let SPhi : bv_unsigned sp0 <= 0x800000000000 := proj1 (proj2 Hvsp).

    (* [comment removed for export] *)
    Lemma D_main_threads : forall segs, rdn segs (D_main sp0 av envv a_hwcap rdraw tid) (Z_to_bv 64 0xb28e0) 1 = Some [Z_to_bv 8 1].
    Proof.
      intros segs. pose proof (u64_range tid). pose proof (len_av av Hva). pose proof SPlo. pose proof SPhi.
      unfold D_main, D_cx, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
      pose proof (rdn_wbytes_hit segs [Z_to_bv 8 1]) as Hh. cbn [length] in Hh. apply Hh. unorm; lia.
    Qed.
    Lemma D_main_tls_size : forall segs, rdn segs (D_main sp0 av envv a_hwcap rdraw tid) (Z_to_bv 64 0xb28f8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xe8)).
    Proof.
      intros segs. pose proof (u64_range tid). pose proof (len_av av Hva). pose proof SPlo. pose proof SPhi.
      unfold D_main, D_cx, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel. apply rdn_wbytes_hit8. unorm; lia.
    Qed.
    (* [comment removed for export] *)
    Lemma D_main_tls_head : forall segs, rdn segs (D_main sp0 av envv a_hwcap rdraw tid) (Z_to_bv 64 0xb28f0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xb2660)).
    Proof.
      intros segs. pose proof (u64_range tid). pose proof (len_av av Hva). pose proof SPlo. pose proof SPhi.
      unfold D_main, D_cx, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel. apply rdn_wbytes_hit8. unorm; lia.
    Qed.
    Lemma D_main_tls_cnt : forall segs, rdn segs (D_main sp0 av envv a_hwcap rdraw tid) (Z_to_bv 64 0xb2908) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1)).
    Proof.
      intros segs. pose proof (u64_range tid). pose proof (len_av av Hva). pose proof SPlo. pose proof SPhi.
      unfold D_main, D_cx, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel. apply rdn_wbytes_hit8. unorm; lia.
    Qed.
    Lemma D_main_tls_align : forall segs, rdn segs (D_main sp0 av envv a_hwcap rdraw tid) (Z_to_bv 64 0xb2900) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 8)).
    Proof.
      intros segs. pose proof (u64_range tid). pose proof (len_av av Hva). pose proof SPlo. pose proof SPhi.
      unfold D_main, D_cx, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel. apply rdn_wbytes_hit8. unorm; lia.
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

    Let E := E0 sp0 a0s path envv rdraw tid regs0.
    Let HK : know_ok RSEGS E mem0 kn_main := main_know_ok sp0 a0s path envv rdraw tid regs0 mem0 Hva Hve Hvsp Htid ME.

    Lemma kn_main_entry : forall e, In e kn_main -> kentry_ok RSEGS E mem0 e.
    Proof. intros e He. exact (proj1 (Forall_forall _ _) HK e He). Qed.

    Lemma none_high : forall i, 0xb2950 <= i < 0xb4000 -> mem0 (Z_to_bv 64 i) = None.
    Proof.
      intros i Hi. pose proof (kn_main_entry (KImg 0xb2950 0xb4000) ltac:(unfold kn_main, kn_stack, kn_auxv, kn_image; in_solve)) as K.
      cbn [kentry_ok] in K. destruct K as (_ & _ & K). apply K. exact Hi.
    Qed.

    (* [comment removed for export] *)
    Lemma rdn_D : forall (a : Z) n, 0 <= a -> a + Z.of_nat n <= 0xb4000 ->
      rdn RSEGS mem0 (Z_to_bv 64 a) n = rdn RSEGS (D_main sp0 av envv a_hwcap rdraw tid) (Z_to_bv 64 a) n.
    Proof.
      intros a n Ha Hn. pose proof SPlo. apply (main_entry_rdn_data sp0 av envv rdraw tid regs0 mem0 ME). rewrite u_small by lia. rewrite stack_max_size_val. lia.
    Qed.
    Ltac rd_miss a n := rewrite (main_entry_rdn_image sp0 av envv rdraw tid SPlo regs0 mem0 ME RSEGS a n) by (vm_compute; reflexivity); vm_refl_bv.

    Lemma main_entry_heap :
      hs_RHEAP HS (ps_init (reservedZ rsegs)) [] mem0 /\ hs_rauxv_ok HS mem0 (bv_unsigned sp0).
    Proof.
      pose proof SPlo as Hlo. pose proof SPhi as Hhi. hcb. hsb. destruct HSE as [HS1 HS2].
      destruct (auxvp_u sp0 a0s path envv rdraw Hva Hve Hvsp) as [AU1 AU2].
      destruct (rnd_u sp0 a0s path envv rdraw Hva Hve Hvsp) as (RN1 & RN2 & RN3).
      assert (EAUX : auxv_w sp0 av envv = auxvp sp0 a0s path envv) by reflexivity.
      (* [comment removed for export] *)
      assert (LC : rw_cells rsegs mem0 0xb28e0 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0)]).
      { rw_split.
        - rw_one ltac:(rewrite rdn_D by lia; apply D_main_threads).
        - rw_one ltac:(rd_miss 0xb28e1 1%nat).
        - rw_one ltac:(rd_miss 0xb28e2 1%nat).
        - rw_one ltac:(rd_miss 0xb28e3 1%nat).
        - rw_one ltac:(rd_miss 0xb28e4 4%nat). }
      assert (LC2 : rw_cells rsegs mem0 0xb28e8 [C8 (auxv_w sp0 av envv); C8 (Z_to_bv 64 0xb2660); C8 (Z_to_bv 64 232); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 1);
                                           C8 (Z_to_bv 64 4096); CB 48 (repeat (Z_to_bv 8 0) 48)]).
      { rw_split.
        - rw_one ltac:(rewrite rdn_D by lia; apply (D_main_auxvp sp0 a0s path envv rdraw tid Hvsp)).
        - rw_one ltac:(rewrite rdn_D by lia; apply D_main_tls_head).
        - rw_one ltac:(rewrite rdn_D by lia; apply D_main_tls_size).
        - rw_one ltac:(rewrite rdn_D by lia; apply D_main_tls_align).
        - rw_one ltac:(rewrite rdn_D by lia; apply D_main_tls_cnt).
        - rw_one ltac:(rewrite rdn_D by lia; apply (D_main_pagesize sp0 av envv rdraw tid Hva)).
        - rw_one ltac:(rd_miss 0xb2918 48%nat). }
      assert (GOT : rw_cells rsegs mem0 0x7f808 [C8 (Z_to_bv 64 0xb2690)]) by (rw_one ltac:(rd_miss 0x7f808 8%nat)).
      assert (CAN : rw_cells rsegs mem0 0xb2690 [C8 (Z_to_bv 64 hcanary)]).
      { rw_one ltac:(rewrite rdn_D by lia; rewrite HS2, Z_to_bv_bv_unsigned;
                      change (le8 (canary_w rdraw)) with (word_to_le_bytes 8 (canary_w rdraw)); rewrite <- (canary_bytes_w rdraw);
                      apply (D_main_guard sp0 av envv rdraw tid)). }
      assert (MI : mem_inv rsegs mem0) by (apply ro_none_mem_inv; exact (main_entry_ro_none sp0 _ _ rdraw tid regs0 mem0 Hvsp ME)).
      destruct (RHEAP_init_proof mem0 (auxv_w sp0 av envv) (Z_to_bv 8 1) (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 64 0)
                  (Z_to_bv 64 0xb2660) (Z_to_bv 64 232) (Z_to_bv 64 8) (Z_to_bv 64 1) (repeat (Z_to_bv 8 0) 48) eq_refl
                  ltac:(intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply none_high; lia)
                  LC LC2 GOT CAN ltac:(intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply none_high; lia) MI) as [RH AUXC].
      split; [exact RH|].
      (* [comment removed for export] *)
      cbn [hs_rauxv_ok HS]. unfold rauxv_ok.
      set (rndw := rnd sp0 a0s path envv) in *. set (auxw := auxvp sp0 a0s path envv) in *.
      exists (bv_unsigned auxw), (bv_unsigned (Z_to_bv 64 (Z.of_N (ph_addr RPH)))), (bv_unsigned (Z_to_bv 64 (Z.of_N (ph_ent RPH)))),
             (bv_unsigned (Z_to_bv 64 (Z.of_N (ph_num RPH)))), (bv_unsigned a_hwcap), 4096, (bv_unsigned (a_uid)), (bv_unsigned (a_uid)), 0, (bv_unsigned rndw).
      pose proof (u64_range auxw). pose proof (u64_range rndw). pose proof (u64_range a_uid). pose proof (u64_range a_hwcap).
      pose proof (u64_range (Z_to_bv 64 (Z.of_N (ph_addr RPH)))). pose proof (u64_range (Z_to_bv 64 (Z.of_N (ph_ent RPH)))). pose proof (u64_range (Z_to_bv 64 (Z.of_N (ph_num RPH)))).
      lazymatch goal with |- context [u64s ?l] => assert (LEN : length l = 20%nat) by reflexivity end.
      repeat match goal with |- _ /\ _ => split end; try (rewrite HCE, stack_max_size_val; lia); try lia.
      - unfold wz. rewrite Z_to_bv_bv_unsigned. rewrite EAUX in AUXC. exact AUXC.
      - apply rdn_bytes_at; [| lia | rewrite u64s_length, LEN; lia].
        rewrite u64s_length. apply bytes_at_u64s; [lia | rewrite LEN; lia |].
        intros j Hj. rewrite LEN in Hj. subst auxw. rewrite (auxv_word_at sp0 a0s path envv rdraw tid regs0 mem0 Hva Hve Hvsp ME j Hj).
        f_equal. f_equal. rewrite auxv_words_eq. unfold rauxv_list, wz. subst rndw. cbn [map].
        rewrite !Z_to_bv_bv_unsigned.
        destruct j as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|j]]]]]]]]]]]]]]]]]]]]; try reflexivity; cbn [length] in Hj; lia.
      - (* [comment removed for export] *)
        apply rdn_bytes_at; [| lia | replace (length (le8 (wz hsecret))) with 8%nat by reflexivity; lia].
        replace (length (le8 (wz hsecret))) with 8%nat by reflexivity.
        rewrite (main_entry_rdn_above sp0 av envv rdraw tid regs0 mem0 ME) by (rewrite u_small by lia; lia).
        pose proof (rdn_wmem_stack RSEGS RPH sp0 av envv a_uid a_hwcap rdraw) as Hw. unfold wmem in Hw. rewrite Hw by (rewrite u_small by lia; lia).
        destruct (rnd_facts RSEGS RPH sp0 rdraw av envv a_uid a_hwcap Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) (proj2 (proj2 Hvsp)))
          as (_ & _ & _ & _ & RB).
        subst rndw. unfold rnd. rewrite (RB 8%nat 8%nat ltac:(lia)).
        f_equal. unfold le8, wz. rewrite HS1. unfold secret_of_draw, secret_bytes_of_draw.
        symmetry. apply le8_bytes_le_val. rewrite length_firstn, length_skipn, length_at_random_bytes. reflexivity.
    Qed.
  End AtMain.
End Top.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition XFUZZ : Prop := forall (HC : HeapCeil) (H : hsr), @heap_sr_hyps HC H ->
  (forall s LB m, hs_RHEAP H s LB m -> CanaryReads m) -> @fuzz_stmt2 HC H.

Theorem ref_realizes_spec_lim : XFUZZ ->
  forall (sp brk mbase : word) (rnd : EntryDraw) (lim : Z) (inp : ProcInput),
    valid_sp sp -> valid_brk RSEGS brk -> 2 ^ 34 <= lim ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
    realizes RSEGS (init_config RSEGS Plain.M.init_pc RPH sp brk mbase rnd lim inp) (spec (in_argv inp) (in_fs inp)).
Proof.
  intros XF sp brk mbase rnd lim inp Hsp Hbrk Hlim Hfit Hva Hve Hfs.
  (* [comment removed for export] *)
  pose (HCEIL := mkHeapCeil (bv_unsigned sp - stack_max_size) (alloc_top_range sp Hsp)).
  pose (HSEC := heap_secret_of_draw rnd (canary_w rnd)).
  pose proof (@heap_sr_hyps_closed HCEIL HSEC) as HH. pose proof (@heap_extra_HS HCEIL HSEC) as HX.
  apply (ref_startup sp brk mbase rnd lim inp); try assumption.
  intros tid regs mem Htid ME.
  lazymatch goal with |- realizes _ (mkCfg (mkst _ ?pc _ _) _) _ => replace pc with (Z_to_bv 64 0x2ac68) by (apply bv_eq; reflexivity) end.
  destruct inp as [argv envp fs0 stdin0 uid gid groups net nf sm hw abt vasz urnd tmp0].
  unfold in_fs in *. cbn [in_argv in_envp in_image_fs in_tmp in_stdin] in *.
  pose (AMB := amb_of (mkProcInput_full argv envp fs0 stdin0 uid gid groups net nf sm hw abt vasz urnd tmp0)).
  change (amb_of _) with AMB in ME.
  change (mkProcInput_full argv envp fs0 stdin0 uid gid groups net nf sm hw abt vasz urnd tmp0) with (@mkProcInputC AMB argv envp fs0 stdin0).
  change (fs_seed_tmp fs0 tmp0) with (@fsC AMB fs0) in Hfs |- *.
  (* [comment removed for export] *)
  destruct argv as [|a0s [|path [|x l]]].
  - apply (ref_usage sp [] envp rnd tid regs mem brk mbase lim fs0 stdin0 Hva Hve Hsp Htid ME ltac:(cbn; lia) Hfit).
  - apply (ref_usage sp [a0s] envp rnd tid regs mem brk mbase lim fs0 stdin0 Hva Hve Hsp Htid ME ltac:(cbn; lia) Hfit).
  - destruct (@main_entry_heap HCEIL HSEC AMB sp a0s path envp rnd tid regs mem Hva Hve Hsp Htid ME eq_refl (conj eq_refl eq_refl)) as [RH AUX].
    apply (@main_realizes HCEIL HS HH HX sp tid brk mbase rnd lim (mkProcInput_full [a0s; path] envp fs0 stdin0 uid gid groups net nf sm hw abt vasz urnd tmp0) regs mem
             (ps_init (reservedZ rsegs)) (bv_unsigned sp) Hsp Hfit Hva Hve Hfs Htid).
    + cbn [hceil HCEIL]. rewrite stack_max_size_val. lia.
    + exact ME.
    + exact RH.
    + unfold model0. apply KM_init; [exact Hbrk | exact Hsp | exact Hlim | reflexivity].
    + exact AUX.
    + pose proof (proj1 Hsp) as L. unfold sp_window_lo in L. pose proof (u64_range sp). lia.
    + apply (target_run_sound HS HH HX). apply (XF HCEIL HS HH).
      intros s1 LB1 m1 RH1. destruct (hx_statics HS HX s1 LB1 m1 RH1) as (_ & GOT1 & [can1 CAN1]).
      split; [exact GOT1 | exists can1; exact (proj1 CAN1)].
  - apply (ref_usage sp (a0s :: path :: x :: l) envp rnd tid regs mem brk mbase lim fs0 stdin0 Hva Hve Hsp Htid ME ltac:(cbn; lia) Hfit).
Qed.

Theorem ref_realizes_spec : XFUZZ ->
  forall (sp brk mbase : word) (rnd : EntryDraw) (inp : ProcInput),
    valid_sp sp -> valid_brk RSEGS brk ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
    realizes RSEGS (init_config RSEGS Plain.M.init_pc RPH sp brk mbase rnd source_alloc_limit inp) (spec (in_argv inp) (in_fs inp)).
Proof.
  intros XF sp brk mbase rnd inp Hsp Hbrk Hfit Hva Hve Hfs.
  apply (ref_realizes_spec_lim XF); try assumption. unfold source_alloc_limit. lia.
Qed.
