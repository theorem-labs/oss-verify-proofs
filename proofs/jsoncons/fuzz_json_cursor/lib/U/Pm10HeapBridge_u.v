(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import Mem Cells Step Arr.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.Pm10 Require Import RMallocRep_u RMallocTree_u RMalloc_iface_u RF_aligned_u RF_aligned_spec_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.Bridge Require Import PmHeapInst10_u PmHeapClosed10_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import RunEnv
  PropExec CatExec SeqExec StoreOk MemSplit AgentLib StartupTac RefLayout ArgvEnv LibTail ZStores
  SymExec2 SymExec2Sound SymDriveX DrvKit
  SymDrive. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10StartupDefs_u Pm10Startup_u Pm10StartupFacts_u Pm10MainEntry_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import HeapIface LibIface LibIfaceFp. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10DrvLib_u Pm10DrvLibL_u Pm10DrvG_u Pm10DrvMain_u.
Import ListNotations.
Import SX2. Import SX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FPX_1.
Variable scfg : SpuriousCfg.
Hypothesis Halloc : sc_alloc scfg = false.
Hypothesis Hfs : sc_fs scfg = true.
#[local] Existing Instance PropExec.fx0.

Lemma drv_layout_L0 : forall sp, valid_sp sp -> drv_layout (L0 (bv_unsigned sp)) sp.
Proof.
  intros sp Hsp. constructor; try reflexivity.
  - intros a Ha. cbn [hl_alloc_static L0] in Ha. unfold RMLOCK, RCTX in Ha. lia.
  - intros a Ha. cbn [hl_alloc_ro L0] in Ha. unfold IMG_LO, RLIBC, RMLOCK, RCTX, RGOT_SSP, RSSP_GUARD in Ha. lia.
  - cbn [hl_stack L0]. unfold RALIGNED_STACK, RMALLOC_STACK. lia.
  - cbn [hl_k_per_malloc L0]. unfold KPM. lia.
  - cbn [hl_b_overhead L0]. vm_compute. discriminate.
Qed.

Lemma bytes_at_of_rdn : forall segs m (a : Z) (bs : list byte),
  rdn segs m (Z_to_bv 64 a) (length bs) = Some bs -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  bytes_at segs m a bs.
Proof.
  intros segs m a bs Hr Ha Hb. split; [exact Ha|]. split; [exact Hb|].
  revert a Hr Ha Hb. induction bs as [|b bs IH]; intros a Hr Ha Hb i Hi; [cbn in Hi; lia|].
  cbn [length] in Hr. rewrite rdn_unfold in Hr. fold (wa a) in Hr.
  destruct (mrd segs m (wa a)) as [b0|] eqn:E0; [|discriminate].
  destruct (rdn segs m (wa a + 1)%bv (length bs)) as [r|] eqn:E1; [|discriminate].
  injection Hr as <- <-.
  destruct i as [|i].
  - cbn. rewrite Z.add_0_r. exact E0.
  - cbn [nth_error]. replace (a + Z.of_nat (S i)) with ((a + 1) + Z.of_nat i) by lia.
    cbn [length] in Hb.
    apply (IH (a + 1)); [| lia | lia | cbn in Hi; lia].
    rewrite wa_succ in E1. exact E1.
Qed.

Lemma wr_at_of_store_ok : forall segs m (a : Z) (n : nat),
  store_ok segs m (Z_to_bv 64 a) n = true -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> wr_at segs m a (Z.of_nat n).
Proof.
  intros segs m a n Hs Ha Hb. split; [exact Ha|]. split; [exact Hb|]. intros i Hi.
  pose proof (store_ok_wview segs m (Z_to_bv 64 a) n (Z.to_nat i) Hs ltac:(lia)) as W.
  rewrite u_small in W by lia. rewrite Z2Nat.id in W by lia. exact W.
Qed.

Lemma bytes_at_app2 : forall segs m a bs1 bs2,
  bytes_at segs m a bs1 -> bytes_at segs m (a + Z.of_nat (length bs1)) bs2 -> bytes_at segs m a (bs1 ++ bs2).
Proof. intros. apply bytes_at_app. split; assumption. Qed.

Section MainEntry.
  Context {RE : RunEnv}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0.
  Let RND : bv 128 := ed_random rdraw.

  Let Hlo : 0x7fff80000000 <= bv_unsigned sp0 := proj1 Hvsp.
  Let Hhi : bv_unsigned sp0 <= 0x800000000000 := proj1 (proj2 Hvsp).

  Lemma rdn_main_data : forall (a : Z) (n : nat), 0 <= a -> a + Z.of_nat n <= 0xf8000 ->
    rdn RSEGS mem0 (Z_to_bv 64 a) n = rdn RSEGS (D_main sp0 [a0s; path] envv hw RND tid) (Z_to_bv 64 a) n.
  Proof.
    intros a n Ha Hn. apply (main_entry_rdn_data sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0 ME).
    rewrite u_small by lia. unfold stack_max_size. lia.
  Qed.

  Lemma rdn_main_img : forall (a : Z) (n : nat), D_main_missb a n = true -> a + Z.of_nat n <= 0xf8000 ->
    rdn RSEGS mem0 (Z_to_bv 64 a) n = rdn RSEGS (fun _ => None) (Z_to_bv 64 a) n.
  Proof.
    intros a n Hb Hn.
    assert (Ha : 0 <= a).
    { unfold D_main_missb in Hb. apply andb_true_iff in Hb as [Hb _]. apply andb_true_iff in Hb as [_ Hb]. apply Z.leb_le in Hb. exact Hb. }
    rewrite rdn_main_data by lia. apply (D_main_miss sp0 [a0s; path] envv hw rdraw tid). exact Hb.
  Qed.

  Lemma mem_main_none : forall (lo hi : Z) (x : word), D_main_missb lo (Z.to_nat (hi - lo)) = true -> lo <= hi <= 0xf8000 ->
    lo <= bv_unsigned x < hi -> mem0 x = None.
  Proof.
    intros lo hi x Hb Hhi' Hx.
    assert (Hlo0 : 0 <= lo).
    { unfold D_main_missb in Hb. apply andb_true_iff in Hb as [Hb _]. apply andb_true_iff in Hb as [_ Hb]. apply Z.leb_le in Hb. exact Hb. }
    rewrite <- (Z_to_bv_bv_unsigned 64 x).
    rewrite (main_entry_mem_data sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0 ME) by (rewrite u_small by lia; unfold stack_max_size; lia).
    apply (D_main_none sp0 [a0s; path] envv hw RND tid (bv_unsigned x) Hva Hlo Hhi).
    apply (missb_sub lo (Z.to_nat (hi - lo))); [exact Hb | lia | rewrite Z2Nat.id by lia; lia].
  Qed.

  Lemma store_ok_data : forall (a : Z) (n : nat), 0xc4000 <= a -> a + Z.of_nat n <= 0xf8000 ->
    store_ok RSEGS mem0 (Z_to_bv 64 a) n = true.
  Proof.
    intros a n Ha Hn.
    eapply (store_ok_window RSEGS mem0 (Z_to_bv 64 0xc4000) (Z_to_bv 64 a) 0x34000 n 0xc4000 0xf8000);
      [reflexivity | reflexivity | lia | apply wseg_data | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
  Qed.
  Lemma store_ok_relro : forall (a : Z) (n : nat), 0xbd000 <= a -> a + Z.of_nat n <= 0xc4000 ->
    store_ok RSEGS mem0 (Z_to_bv 64 a) n = true.
  Proof.
    intros a n Ha Hn.
    eapply (store_ok_window RSEGS mem0 (Z_to_bv 64 0xbd000) (Z_to_bv 64 a) 28672 n 0xbd000 0xc4000);
      [reflexivity | reflexivity | lia | vm_compute; reflexivity | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
  Qed.

  Lemma rw_cells_of_rdn : forall (A : Z) cs,
    cells_wf cs ->
    rdn RSEGS mem0 (Z_to_bv 64 A) (length (cells_bytes cs)) = Some (cells_bytes cs) ->
    store_ok RSEGS mem0 (Z_to_bv 64 A) (cells_size cs) = true ->
    0 <= A -> A + Z.of_nat (cells_size cs) <= 2 ^ 64 ->
    rw_cells rsegs mem0 A cs.
  Proof.
    intros A cs Hwf Hr Hs HA HB. pose proof (cells_bytes_length cs Hwf) as HL.
    split; [split; [exact Hwf|]|].
    - apply bytes_at_of_rdn; [exact Hr | exact HA | rewrite HL; exact HB].
    - apply wr_at_of_store_ok; [exact Hs | exact HA | exact HB].
  Qed.

  Lemma bytes_eq_of_unsigned : forall (l1 l2 : list byte), map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
  Proof.
    intros l1. induction l1 as [|b1 l1 IH]; intros [|b2 l2] H; cbn in H; try discriminate; [reflexivity|].
    injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
  Qed.

  Ltac img_read a n :=
    rewrite (rdn_main_img a n) by (first [vm_compute; reflexivity | lia]);
    lazymatch goal with |- ?l = Some _ => let v := eval vm_compute in l in change l with v end;
    f_equal; apply bytes_eq_of_unsigned; vm_compute; reflexivity.

  Lemma main_init_statics0 : init_statics0 (bv_unsigned sp0) mem0.
  Proof.
    pose proof (u64_range tid) as Ht.
    destruct (auxvp_u sp0 a0s path envv uid hw rdraw Hva Hve Hvsp) as [AV1 AV2].
    destruct (rnd_u sp0 a0s path envv uid hw rdraw Hva Hve Hvsp) as (RN1 & RN2 & RN3 & RN4).
    pose proof (u64_range (auxvp sp0 a0s path envv)) as AVR. pose proof (u64_range (rnd sp0 a0s path envv)) as RNR.
    pose proof (u64_range uid) as UR. pose proof (u64_range hw) as HWR. pose proof (u64_range (canary_w RND)) as CR.
    unfold init_statics0.
    split; [|split; [|split; [|split; [|split; [|split]]]]].
    -
      intros a Ha. apply (mem_main_none 0xf6c08 0xf73f8 a); [vm_compute; reflexivity | lia | exact Ha].
    -
      apply rw_cells_of_rdn; [cbn; tauto | | apply store_ok_data; cbn; lia | lia | cbn; lia].
      cbn [length cells_bytes cbytes app]. img_read 0xf6a93 1%nat.
    -
      apply rw_cells_of_rdn; [cbn; tauto | | apply store_ok_data; cbn; lia | lia | cbn; lia].
      cbn [length cells_bytes cbytes le8 word_to_le_bytes Z_to_le_bytes app].
      rewrite rdn_main_data by (cbn; lia). apply (D_main_pagesize sp0 [a0s; path] envv hw rdraw tid Hva).
    -
      apply rw_cells_of_rdn; [cbn; tauto | | apply store_ok_relro; cbn; lia | lia | cbn; lia].
      cbn [length cells_bytes cbytes le8 word_to_le_bytes Z_to_le_bytes app]. img_read 0xc3a48 8%nat.
    -
      exists (bv_unsigned (canary_w RND)). split; [lia|].
      apply rw_cells_of_rdn; [cbn; tauto | | apply store_ok_data; cbn; lia | lia | cbn; lia].
      cbn [length cells_bytes cbytes le8 word_to_le_bytes Z_to_le_bytes app]. rewrite Z_to_bv_bv_unsigned.
      exact (main_entry_guard sp0 [a0s; path] envv uid hw rdraw tid (proj1 Hvsp) regs0 mem0 ME RSEGS).
    -
      set (sec := firstn 8 (skipn 8 (at_random_bytes RND))).
      assert (Lsec : length sec = 8%nat) by (subst sec; rewrite length_firstn, length_skipn, length_at_random_bytes; reflexivity).
      exists (bv_unsigned (auxvp sp0 a0s path envv)), (Z.of_N (ph_addr RPH)), (Z.of_N (ph_ent RPH)), (Z.of_N (ph_num RPH)), (bv_unsigned hw),
             4096, (bv_unsigned uid), (bv_unsigned uid), 0, (bv_unsigned (rnd sp0 a0s path envv)), (bytes_le_to_Z sec).
      pose proof (bytes_le_to_Z_bound sec) as SB. rewrite Lsec in SB.
      split; [|split; [|split]].
      + apply rw_cells_of_rdn; [cbn; tauto | | unfold RAUXV_CELL; apply store_ok_data; cbn; lia | unfold RAUXV_CELL; lia | unfold RAUXV_CELL; cbn; lia].
        unfold RAUXV_CELL. cbn [length cells_bytes cbytes le8 word_to_le_bytes Z_to_le_bytes app].
        rewrite rdn_main_data by (cbn; lia). unfold wz. rewrite Z_to_bv_bv_unsigned. apply (D_main_auxvp sp0 a0s path envv hw rdraw tid Hvsp).
      +
        cbn [map u64s app].
        repeat (apply bytes_at_app2; [|cbn [length le8 word_to_le_bytes Z_to_le_bytes Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add]]);
          [.. | apply bytes_at_nil; lia];
          (apply bytes_at_of_rdn; [| lia | cbn [length le8 word_to_le_bytes Z_to_le_bytes]; lia]);
          cbn [length le8 word_to_le_bytes Z_to_le_bytes]; unfold wz;
          lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) 8 = _ =>
            first [ replace a with (bv_unsigned (auxvp sp0 a0s path envv) + 8 * Z.of_nat 0) by lia;
                    rewrite (main_auxv sp0 a0s path envv uid hw rdraw tid regs0 mem0 Hva Hve Hvsp ME 0%nat) by lia
                  | let rec go j := (replace a with (bv_unsigned (auxvp sp0 a0s path envv) + 8 * Z.of_nat j) by lia;
                                     rewrite (main_auxv sp0 a0s path envv uid hw rdraw tid regs0 mem0 Hva Hve Hvsp ME j) by lia)
                                    || go (S j) in go 1%nat ]
          end;
          cbn [nth]; rewrite ?Z_to_bv_bv_unsigned; try reflexivity.
        all: vm_compute; reflexivity.
      +
        apply bytes_at_of_rdn; [| lia | unfold le8; rewrite length_word_to_le_bytes; lia]. unfold le8. rewrite length_word_to_le_bytes.
        rewrite (main_entry_rdn_above sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0 ME); [ | rewrite u_small by lia; lia | rewrite u_small by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].
        pose proof (rdn_wmem_stack RSEGS RPH sp0 [a0s; path] envv uid hw rdraw) as Hw. unfold wmem in Hw.
        rewrite Hw; [ | rewrite u_small by lia; lia | rewrite u_small by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].
        replace (bv_unsigned (rnd sp0 a0s path envv) + 8) with (bv_unsigned (rnd sp0 a0s path envv) + Z.of_nat 8) by lia.
        rewrite (RN4 8%nat 8%nat ltac:(lia)). fold sec. rewrite (word_to_le_bytes_of_lez 8 sec Lsec ltac:(lia)). reflexivity.
      + pose proof (proj1 Hvsp).
        change (Z.of_N (ph_addr RPH)) with 0x10040%Z. change (Z.of_N (ph_ent RPH)) with 56%Z. change (Z.of_N (ph_num RPH)) with 10%Z. lia.
    -
      intros a b Hab. destruct (ro_addr rsegs a) eqn:E; [|reflexivity]. exfalso.
      apply ref_ro_addr_true in E. unfold IMG_LO in E.
      rewrite (mem_main_none 0x10000 0xbd000 a) in Hab; [discriminate | vm_compute; reflexivity | lia | lia].
  Qed.

  Theorem main_hi_heap0 : forall brk mbase (lim : Z),
    valid_brk RSEGS brk -> valid_mmap_base mbase ->
    hi_heap (HI0 (bv_unsigned sp0)) [] (K0, B0) mem0 (mkVmMapsFull (segments_reserved RSEGS) [] [] brk brk lim mbase sp0).
  Proof.
    intros brk mbase lim Hbrk Hmb.
    apply (HI0_init (bv_unsigned sp0) mem0 lim); [apply main_init_statics0|].
    exists brk, mbase, sp0. split; [reflexivity|]. split; [exact Hbrk|]. split; [exact Hmb|]. split; [exact Hvsp|]. reflexivity.
  Qed.
End MainEntry.

Section WithLib.
  Variable LayF : word -> lib_layout.
  Variable LStF : word -> lib_statics.
  Hypothesis DLLF : forall sp, valid_sp sp -> drv_lib_layout (LayF sp) (L0 (bv_unsigned sp)).
  Hypothesis LIokF : forall sp, valid_sp sp -> lib_iface_ok_fp (LayF sp) scfg (HI0 (bv_unsigned sp)) (LStF sp).
  Hypothesis LXokF : forall sp, valid_sp sp -> lib_exit_ok (LStF sp).
  Hypothesis Hbudget : forall sp n, valid_sp sp -> 0 <= n < 67108864 ->
    cred (L0 (bv_unsigned sp)) (KPM + 4 * fst (ll_credit (LayF sp) n)) (n + BOV + 4 * snd (ll_credit (LayF sp) n)) 0
         (debit (L0 (bv_unsigned sp)) (K0, B0) 65536).

  Theorem src0_realizes_spec_heap_lim : forall lim, src_realizes_stmt2_lim scfg lim.
  Proof.
    intro lim0.
    apply (src0_realizes_spec_lim scfg (fun sp => L0 (bv_unsigned sp)) (fun sp => HI0 (bv_unsigned sp)) LayF LStF (K0, B0)).
    - intros sp Hsp. apply HI0_ok_closed. exact Halloc.
    - exact drv_layout_L0.
    - exact DLLF.
    - exact LIokF.
    - exact LXokF.
    - intros lim sp a0s path envp uid hw rdraw tid regs mem brk mbase Hsp Hbrk Hmb Hva Hve Htid ME.
      exact (main_hi_heap0 sp a0s path envp uid hw rdraw tid regs mem Hva Hve Hsp Htid ME brk mbase lim Hbrk Hmb).
    - exact Hfs.
    - exact Hbudget.
  Qed.

  Theorem src0_realizes_spec_heap : src_realizes_stmt2 scfg.
  Proof. exact (src0_realizes_spec_heap_lim source_alloc_limit). Qed.
End WithLib.
End FPX_1.
