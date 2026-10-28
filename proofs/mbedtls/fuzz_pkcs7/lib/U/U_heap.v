(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr AEvt HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_layout.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad MSafe Prog KInv KStep KStepC
     MallocTree MallocBlocks MallocHINV Malloc_iface ImplAevt RunParams RunConsts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_F_syscalls HP_RMallocRep HP_RMallocTree HP_RMalloc_iface HP_RMalloc_ifaceP HP_RF_malloc_spec HP_RF_free_spec HP_F_memset HP_allzerop HP_calloc.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import VirginDefs InitMem.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_heap () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.Heap.RunParams.RunParams"; "RocqVerifyHarness.AgentSubmission.Heap.RunConsts.rc_secret"; "RocqVerifyHarness.AgentSubmission.Heap.RunConsts.rc_canary"; "RocqVerifyHarness.AgentSubmission.U.U_layout.run_ceil"; "RocqVerifyHarness.AgentSubmission.Heap.RunConsts.rc_secret_range"; "RocqVerifyHarness.AgentSubmission.Heap.RunConsts.rc_canary_range"; "PHeap.run_ceil_cok"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Lists.ListDef.map"; "RocqVerifyHarness.AgentSubmission.Heap.MallocBlocks.block"; "PHeap.bview"; "h_blocks"; "RocqVerifyHarness.AgentSubmission.U.HP_RMalloc_iface.RHEAP"; "PHeap.HRP"; "h_rc"; "h_s"; "RocqVerifyHarness.AgentSubmission.Heap.KStep.OWN"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.bptr"; "RocqVerifyHarness.AgentSubmission.Heap.MallocBlocks.blk_id"; "PHeap.GT"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rauxv_ok"; "h_top"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.U.HP_F_memset.rsegs"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RERRNO"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.U.HP_calloc.RMALLOC_REPLACED"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Datatypes.fst"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.snd"; "Corelib.Init.Logic.or"; "PHeap.PHEAP"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "Corelib.Lists.ListDef.Forall"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "RocqVerifyHarness.AgentSubmission.U.U_layout.U_layout"; "PHeap.data_iv_ok"; "Stdlib.Lists.List.In"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_waddr"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.call_post"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_pres"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.PState"; "mkHST"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.block_range"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aptr"; "stdpp.base.lookup"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.cptr"; "stdpp.gmap.gmap"; "stdpp.decidable.prod_eq_dec"; "Corelib.Numbers.BinNums.N"; "stdpp.numbers.N.eq_dec"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.N_countable"; "stdpp.countable.Z_countable"; "stdpp.gmap.gmap_lookup"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_slots"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.ps_m"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.Heap.VirginDefs.undersized"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.get_meta_rec"; "Corelib.Lists.ListDef.repeat"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Heap.MallocTree.mem"; "hst"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.U.HP_RMalloc_iface.RMALLOC_STACK"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RATP"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevt"; "PHeap.pmalloc_post"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.U.HP_RMalloc_iface.RMALLOC_SYM"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_malloc"; "Stdlib.Lists.List.NoDup"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc_iface.lb_remove"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.lb_remove"; "Stdlib.Sorting.Permutation.Permutation"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_free"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_calloc"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "PHeap.U_heap_init_hyps"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.ps_init"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.reservedZ"; "RocqVerifyHarness.AgentSubmission.Heap.RunConsts.rconsts"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.rdn"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Corelib.Init.Datatypes.nat"; "Stdlib.Lists.List.nth_error"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u64s"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.wz"; "LinuxProcessSemantics.LinuxProcessSem.State.VmMaps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "RocqVerifyHarness.AgentSubmission.Heap.KInv.KL"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HI"; "PHeap.PHEAP_mok"; "PHeap.PHEAP_blocks"; "PHeap.PHEAP_heap_frame"; "PHeap.PHEAP_mo_other"; "PHeap.PHEAP_malloc"; "PHeap.PHEAP_calloc"; "PHeap.PHEAP_free"; "PHeap.PHEAP_free_null"].


(* [comment removed for export] *)

(* [comment removed for export] *)
Record hst := mkHST { h_rc : rconsts; h_s : PState; h_blocks : list block; h_top : Z }.

Section PHeap.
Variable sp0 : word.
Local Notation PL := (U_layout sp0).
Local Notation ACEIL := (@alloc_ceiling (U_layout sp0)).

(* [comment removed for export] *)

#[using="Type"] Lemma U_static_eq : forall a, hl_static PL a <-> (ralloc_static a \/ RMALLOC_REPLACED <= a < RMALLOC_REPLACED + 4).
Proof. intros a. cbn [hl_static U_layout]. unfold U_static, ralloc_static, RLIBC, RCTX, RERRNO, RATP, RSSP_GUARD, RGOT_SSP, RMALLOC_REPLACED. lia. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma run_ceil_cok : ceil_ok (run_ceil sp0).
Proof. unfold ceil_ok, ALLOC_CEIL_LO, ALLOC_CEIL_HI. pose proof (run_ceil_lo sp0). pose proof (run_ceil_hi sp0). lia. Qed.

Definition HRP (rc : rconsts) : run_params := ltac2:(CDefT.buildp (gd_tbl_P_heap ()) "(0.(1.O1.)(2.O1.)(3.Vsp0,)(4.O1.)(5.O1.)$6.)")
(* [comment removed for export] *).

(* [comment removed for export] *)
#[using="Type"] Lemma rceil_HRP rc : @rceil (HRP rc) = ACEIL.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Local Ltac ceilnum :=
  pose proof (run_ceil_lo sp0); pose proof (run_ceil_hi sp0);
  change ACEIL with (run_ceil sp0) in *;
  repeat match goal with
         | |- context [@rceil ?R] => change (@rceil R) with (run_ceil sp0) in *
         | H : context [@rceil ?R] |- _ => change (@rceil R) with (run_ceil sp0) in *
         end.

(* [comment removed for export] *)

Definition bview (b : block) : blk := (blk_addr b, blk_size b).
Definition GT : PState -> Model -> Prop := fun _ _ => True.
#[using="Type"] Lemma frame_ok_GT : frame_ok GT. Proof. intros ? ? ? ? _ _ _ _. exact I. Qed.

Definition PHEAP (h : hst) (LB : list blk) (m : mem) (mo : Model) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_heap ()) "(7.(8.(9.$:.)O3.(;.$<.$:.$=.(>.O4.)))(7.(?.(10.(11.O4.))(12.O4.)(>.O4.)O2.)(7.(13.(;.$<.$14.$15.(>.O4.))$16.(12.O4.)O1.)(7.(17.(10.(11.O4.))O2.(18.O4.))(7.(19.(1:.&40.)Lerrv,(1:.&40.)(1;.$1<.O2.$1=.(1>.$1?.(20.R1.)(21.$1?.))))(1;.$1<.O2.$22.(1>.$1?.(20.(23.&40.=))(21.$1?.))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
#[using="Type"] Lemma tmm_msys {A} n (dec : resp -> option A) (s : PState) : is_mm n -> tmm (msys n dec s).
Proof. intros Hn. unfold msys. apply tmm_enode. exact Hn. Qed.

#[using="Type"] Lemma tmm_mbind {A B} (m : Monad.M PState A) (f : A -> Monad.M PState B) s :
  tmm (m s) -> (forall a s', tmm (f a s')) -> tmm (mbind m f s).
Proof. intros Hm Hf. unfold mbind. apply tmm_ebind; [exact Hm|]. intros [a s']. apply Hf. Qed.

#[using="Type"] Lemma tmm_ev_step e s : tmm (ev_step e s).
Proof.
  destruct e as [req|addr len prot flags|addr len|addr len prot|p c h|w]; unfold ev_step.
  - destruct (req =? 0).
    + apply tmm_mbind; [apply tmm_msys; exact I|]. intros a s'. apply tmm_mbind; [exact I|]. intros; exact I.
    + apply tmm_mbind; [exact I|]. intros a s'. apply tmm_mbind; [apply tmm_msys; exact I|]. intros [] s''; [apply tmm_mbind; [exact I| intros; exact I]| exact I].
  - destruct (negb _); [|destruct (prot =? 0)]; (apply tmm_mbind; [apply tmm_msys; exact I| intros; exact I]).
  - apply tmm_mbind; [apply tmm_msys; exact I| intros; exact I].
  - apply tmm_mbind; [apply tmm_msys; exact I| intros; exact I].
  - exact I.
  - exact I.
Qed.

#[using="Type"] Lemma tmm_membed {R} (t : stree ev Z R) : forall s, tmm (membed t s).
Proof.
  induction t as [r|e k IH]; intros s; cbn -[mbind mret ev_step tmm]; [exact I|].
  apply tmm_mbind; [apply tmm_ev_step|]. intros z s'. apply IH.
Qed.

#[using="Type"] Lemma tmm_raw_malloc n s : tmm (raw_malloc n s).
Proof.
  unfold raw_malloc. apply tmm_mbind; [exact I|]. intros s0 s1.
  apply tmm_mbind; [apply tmm_membed|]. intros [st' p] s2. apply tmm_mbind; [exact I|]. intros; exact I.
Qed.

#[using="Type"] Lemma tmm_raw_free p s : tmm (raw_free p s).
Proof.
  unfold raw_free. apply tmm_mbind; [exact I|]. intros s0 s1.
  apply tmm_mbind; [apply tmm_membed|]. intros; exact I.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma in_block_bview LB a : HeapIface.in_block (map bview LB) a <-> Malloc_iface.in_block LB a.
Proof.
  unfold HeapIface.in_block, Malloc_iface.in_block, bview. split.
  - (intros dd_H; ddestruct dd_H as ([A n] & Hin & Hr)). apply in_map_iff in Hin as (b & E & Hb). injection E as <- <-. exists b. cbn in Hr. auto.
  - (intros dd_H; ddestruct dd_H as (b & Hb & Hr)). exists (blk_addr b, blk_size b). split; [apply in_map_iff; exists b; auto| cbn; exact Hr].
Qed.

#[using="Type"] Lemma mo_frame_of_vm_only mo mo' : vm_only mo mo' -> mo_frame mo mo'.
Proof. (intros dd_H; ddestruct dd_H as (A & B & C & D & E & F & _)). unfold mo_frame. repeat split; assumption. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma PHEAP_mok h LB m mo : PHEAP h LB m mo -> MOK mo.
Proof.
  (intros dd_H; ddestruct dd_H as (_ & _ & [(L & _ & HK & _) _] & _)). split; [exact (kl_halt _ _ _ HK)| exact (kl_minv _ _ _ HK)].
Qed.

#[using="Type"] Lemma heap_pres_of_r LB SP m m' :
  rheap_pres LB SP m m' -> heap_pres usegs PL (map bview LB) SP m m'.
Proof.
  intros HP a Ha Hc. apply HP; [exact Ha|].
  destruct Hc as [H|[H|H]]; [left; exact H| right; left| right; right; apply in_block_bview; exact H].
  rewrite U_static_eq in H. change (hl_data_lo PL) with 0x48000 in H. change (hl_data_hi PL) with 0x7e000 in H. tauto.
Qed.

#[using="Type"] Lemma block_range_r rc A n : @rblock_range (HRP rc) A n <-> block_range PL A n.
Proof.
  unfold rblock_range, block_range. rewrite rceil_HRP.
  change (hl_img_lo PL) with 0x10000. change (hl_img_hi PL) with 0x7e000. tauto.
Qed.

#[using="Type"] Lemma PHEAP_blocks h LB m mo : PHEAP h LB m mo ->
  Forall (fun b => block_range PL (fst b) (snd b)) LB /\ blocks_apart LB.
Proof.
  (intros dd_H; ddestruct dd_H as (-> & RH & _ & _)). set (hRP := HRP (h_rc h)) in *. split.
  - apply Forall_forall. intros [A n] Hin. apply in_map_iff in Hin as (b & E & Hb). unfold bview in E. injection E as <- <-.
    cbn [fst snd]. apply (block_range_r (h_rc h)). exact (RHEAP_block_range_proof _ _ _ b RH Hb).
  - pose proof (RHEAP_blocks_nodup_proof _ _ _ RH) as ND.
    pose proof (fun b1 b2 => RHEAP_blocks_disjoint_proof _ _ _ b1 b2 RH) as DJ.
    set (LBf := h_blocks h) in *. clearbody LBf. clear RH.
    induction LBf as [|b LBf IH]; cbn; [exact I|].
    cbn in ND. inversion ND as [|x l Hni ND']; subst. split.
    + intros B k Hin. apply in_map_iff in Hin as (b' & E & Hb'). unfold bview in E. injection E as <- <-.
      apply (DJ b b' (or_introl eq_refl) (or_intror Hb')). intros E. apply Hni. rewrite E. apply in_map. exact Hb'.
    + apply IH; [exact ND'|]. intros b1 b2 H1 H2. apply DJ; right; assumption.
Qed.

(* [comment removed for export] *)
Fixpoint units (a : Z) (n : nat) : list ivl :=
  match n with O => [] | S n' => (a, a + 1) :: units (a + 1) n' end.





(* [comment removed for export] *)
Definition data_iv_ok (iv : Z * Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_heap ()) "(7.(24.+48000.(25.$26.$26.O1.))(7.(24.(27.$26.$26.O1.)+7>000.)(7.(28.(24.(27.$26.$26.O1.)+4;<=8.)(24.+4;<>0.(25.$26.$26.O1.)))(7.(28.(24.(27.$26.$26.O1.)+5=024.)(24.+5=028.(25.$26.$26.O1.)))(7.(28.(24.(27.$26.$26.O1.)+7=330.)(24.+7=338.(25.$26.$26.O1.)))(28.(24.(27.$26.$26.O1.)+7=350.)(24.+7=76<.(25.$26.$26.O1.))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
#[using="Type"] Lemma PHEAP_frame h LB m m' W mo : ltac2:(CDefT.buildp (gd_tbl_P_heap ()) "P,(29.O6.O5.O4.O1.)P,(2:.O2.O4.O3.)P,(2;.$1<.O4.O3.)P,(2<.(2=.$26.$26.)Liv,(2=.$26.$26.)(28.(7.(24.(2>.(2?.Vsp0,))(25.$26.$26.R1.))(24.(27.$26.$26.R1.)(18.O6.)))(28.(30.R1.)(19.$:.Lb,$:.(7.(31.$:.R1.O5.)(7.(24.(25.$26.$26.R1.)(25.$26.$26.R2.))(24.(27.$26.$26.R2.)(32.(25.$26.$26.R1.)(27.$26.$26.R1.))))))))O2.)(29.O6.O5.O3.O1.)")
(* [comment removed for export] *).
Proof.
  intros HP MU WM FW. pose proof (PHEAP_blocks _ _ _ _ HP) as [BR _]. ddestruct HP as (ELB & RH & OW & AUX & [errv ERR] & MRP).
  set (hRP := HRP (h_rc h)) in *.
  dpose AUX as (av & x3 & x4 & x5 & hw & x6 & x11 & x12 & x23 & rnd & _ & _ & _ & AB & _).
  assert (CASES : forall lo hi, In (lo, hi) W -> (ACEIL <= lo /\ hi <= h_top h) \/ data_iv_ok (lo, hi) \/ (exists A n, In (A, n) LB /\ block_range PL A n /\ A <= lo /\ hi <= A + n)).
  { intros lo hi Hin. pose proof (proj1 (Forall_forall _ _) FW _ Hin) as [C|[C|([A n] & Hb & C1 & C2)]]; [left; exact C| right; left; exact C| right; right].
    dexists A, n. split; [exact Hb|]. split; [exact (proj1 (Forall_forall _ _) BR _ Hb)| cbn in C1, C2; lia]. }
  unfold data_iv_ok, block_range in CASES. change (hl_img_lo PL) with 0x10000 in CASES. change (hl_img_hi PL) with 0x7e000 in CASES. cbn [fst snd] in CASES.
  split; [exact ELB|]. split; [|split; [exact OW| split; [|split]]].
  - eapply RHEAP_frame_proof; [exact RH| exact MU| exact WM|].
    apply Forall_forall. intros [lo hi] Hin. destruct (CASES lo hi Hin) as [[C1 C2]|[C|(A & n & Hb & _ & C1 & C2)]].
    + left. exact C1.
    + right; left. cbn [fst snd]. unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP. lia.
    + right; right. rewrite ELB in Hb. apply in_map_iff in Hb as (b' & E & Hb'). exists b'. split; [exact Hb'|]. unfold bview in E. injection E as <- <-. cbn. lia.
  - eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|].
    apply Forall_forall. intros [lo hi] Hin. cbn [fst snd]. destruct (CASES lo hi Hin) as [[C1 C2]|[C|(A & n & Hb & (B1 & B2 & B3 & B4 & B5) & C1 & C2)]].
    + unfold RAUXV_CELL in *. ceilnum. lia.
    + unfold RAUXV_CELL in *. ceilnum. lia.
    + unfold RAUXV_CELL in *. ceilnum. lia.
  - exists errv. eapply rw_cells_transport; [exact ERR| exact MU| exact WM|].
    apply (MallocTree.Forall_disjoint_from (fun iv => In iv W)); [apply Forall_forall; intros iv Hiv; exact Hiv|].
    intros lo hi Hin. cbn [cells_size csize Nat.add]. destruct (CASES lo hi Hin) as [[C1 C2]|[C|(A & n & Hb & (B1 & B2 & B3 & B4 & B5) & C1 & C2)]].
    + unfold RERRNO, RATP in *. ceilnum. lia.
    + unfold RERRNO, RATP in *. lia.
    + unfold RERRNO, RATP in *. ceilnum. lia.
  - eapply rw_cells_transport; [exact MRP| exact MU| exact WM|].
    apply (MallocTree.Forall_disjoint_from (fun iv => In iv W)); [apply Forall_forall; intros iv Hiv; exact Hiv|].
    intros lo hi Hin. cbn [cells_size csize Nat.add]. destruct (CASES lo hi Hin) as [[C1 C2]|[C|(A & n & Hb & (B1 & B2 & B3 & B4 & B5) & C1 & C2)]].
    + unfold RMALLOC_REPLACED in *. ceilnum. lia.
    + unfold RMALLOC_REPLACED in *. lia.
    + unfold RMALLOC_REPLACED in *. ceilnum. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma PHEAP_heap_frame h LB m m' mo (SP : Z) : ltac2:(CDefT.buildp (gd_tbl_P_heap ()) "P,(29.O6.O5.O4.O2.)P,(24.(2>.(2?.Vsp0,))O1.)P,Pa,$26.P,(7.(24.=R1.)(33.R1.(34.+2.+40.)))P,(35.(36.(2?.Vsp0,)O5.O1.(18.O6.)R2.))(8.(37.(1:.&8.))A1.O3.(38.R3.)A1.O4.(38.R3.))P,(2;.$1<.O4.O3.)(29.O6.O5.O3.O2.)")
(* [comment removed for export] *).
Proof.
  intros HP HSP AG WM.
  set (W0 := (0x48000, 0x4bcd8) :: (0x4bce0, 0x5d024) :: (0x5d028, 0x7d330) :: (0x7d338, 0x7d350) :: (0x7d76c, 0x7e000)
            :: map (fun b : blk => (fst b, fst b + snd b)) LB).
  set (W := if Z.leb SP (h_top h) then (SP, h_top h) :: W0 else W0).
  assert (OUT : forall x, outside W x -> (SP <= x < h_top h -> False) /\ outside W0 x).
  { intros x Hx. subst W. destruct (Z.leb_spec SP (h_top h)); [| split; [lia| exact Hx]].
    change (outside ((SP, h_top h) :: W0) x) with (~ (SP <= x < h_top h) /\ outside W0 x) in Hx. destruct Hx as [Hx1 Hx2]. split; [lia| exact Hx2]. }
  apply (PHEAP_frame h LB m m' W mo HP); [| exact WM|].
  - intros x Hx. pose proof (bv_unsigned_in_range 64 x) as XR. change (bv_modulus 64) with (2^64) in XR.
    rewrite <- (wa_unsigned_id x). apply AG; [lia|]. intros C. destruct (OUT _ Hx) as [H1 Hx0]. subst W0. cbn [outside] in Hx0. ddestruct Hx0 as (H2 & H3 & H4 & H5 & H6 & H7).
    destruct C as [C|[C|(b & Hb & C)]]; [lia| |].
    + cbn [hl_data_lo hl_data_hi hl_static U_layout] in C. unfold U_static in C. lia.
    + clear - H7 Hb C. induction LB as [|b0 LB IH]; [destruct Hb|]. cbn [map outside] in H7. destruct H7 as [H7 H8].
      destruct Hb as [<-|Hb]; [cbn in H7; lia| exact (IH Hb H8)].
  - assert (FW0 : Forall (fun iv => (ACEIL <= fst iv /\ snd iv <= h_top h) \/ data_iv_ok iv \/ (exists b, In b LB /\ fst b <= fst iv /\ snd iv <= fst b + snd b)) W0).
    { subst W0. do 5 (constructor; [right; left; unfold data_iv_ok; cbn; lia|]).
      apply Forall_forall. intros iv Hin. apply in_map_iff in Hin as (b & <- & Hb). right; right. exists b. cbn. split; [exact Hb| lia]. }
    subst W. destruct (Z.leb_spec SP (h_top h)); [| exact FW0]. constructor; [left; cbn [fst snd]; lia| exact FW0].
Qed.

#[using="Type"] Lemma errno_addr_RATP tp : tp = Z_to_bv 64 RATP -> errno_addr tp = RERRNO.
Proof. intros ->. unfold errno_addr, RERRNO, RATP. rewrite unsigned_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma malloc_replaced_pres {hRP : run_params} LBf SP m m' :
  rheap_pres LBf SP m m' -> rw_cells rsegs m RMALLOC_REPLACED [C4 (Z_to_bv 64 0)] -> rw_cells rsegs m' RMALLOC_REPLACED [C4 (Z_to_bv 64 0)].
Proof.
  intros HP H. eapply rheap_pres_rw_cells; [exact HP| exact H|]. right; left.
  cbn [cells_size csize Nat.add]. unfold RMALLOC_REPLACED, RLIBC, RCTX, RERRNO, RATP, RSSP_GUARD, RGOT_SSP. lia.
Qed.

(* [comment removed for export] *)
Definition pmalloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (mo : Model) (h : hst) (LB : list blk) (n lo : Z) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_heap ()) "(39.$3:.O18.O17.O16.O15.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.Lr,(1:.&40.)Lm',P,(1:.&40.)(37.(1:.&8.))Lmo',$3;.(7.(3<.$3:.R2.)(7.(3=.$3:.R2.O1.(3>.&40.O17.))(7.(3?.O5.R1.)(7.(40.$3:.(2?.Vsp0,)O3.(3>.&40.O17.)O6.R2.)(19.$41.Ls',$41.(28.(7.(8.(1:.&40.)R4.(23.&40.=))(29.(42.(11.O4.)R1.(>.O4.)(18.O4.))O3.R3.R2.))(19.$26.LA,$26.(19.(9.(1:.&8.))Ljunk,(9.(1:.&8.))(19.$14.Lp,$14.(7.(8.(1:.&40.)R7.(23.&40.R3.))(7.(43.(2?.Vsp0,)R3.O2.)(7.(29.(42.(11.O4.)R4.(1>.(2=.(2=.$14.$26.)$26.)(44.(2=.$14.$26.)$26.(44.$14.$26.R1.R3.)O2.)(>.O4.))(18.O4.))(1>.(2=.$26.$26.)(44.$26.$26.R3.O2.)O3.)R6.R5.)(7.(1;.$3:.R6.R3.(1>.$1?.(45.(46.O2.)R2.)(21.$1?.)))Pg,$47.Pi,$26.P,(8.(37.(2=.$47.$26.))(48.$49.(2=.$47.$26.)(4:.$47.(4;.$4<.$4=.$26.$4>.)(4?.$4<.$4=.$50.$26.$4>.$51.)(2=.$47.$26.))(52.$47.(4;.$4<.$4=.$26.$4>.)(4?.$4<.$4=.$50.$26.$4>.$51.)(2=.$47.$26.))(25.$49.$26.R3.)(53.(54.R6.)))(55.(2=.$47.$26.)(44.$47.$26.R2.R1.)))P,(56.(57.(54.R7.)R3.))(8.(9.(1:.&8.))R6.(58.(1:.&8.)(23.&8.=)(46.O2.)))))))))))))))))")
(* [comment removed for export] *).

#[using="Type"] Lemma PHEAP_malloc_gen : ltac2:(CDefT.buildp (gd_tbl_P_heap ()) "Pra,(1:.&40.)Psp,(1:.&40.)Pgp,(1:.&40.)Ptp,(1:.&40.)Pt0,(1:.&40.)Pt1,(1:.&40.)Pt2,(1:.&40.)Ps0,(1:.&40.)Ps1,(1:.&40.)Pa0,(1:.&40.)Pa1,(1:.&40.)Pa2,(1:.&40.)Pa3,(1:.&40.)Pa4,(1:.&40.)Pa5,(1:.&40.)Pa6,(1:.&40.)Pa7,(1:.&40.)Ps2,(1:.&40.)Ps3,(1:.&40.)Ps4,(1:.&40.)Ps5,(1:.&40.)Ps6,(1:.&40.)Ps7,(1:.&40.)Ps8,(1:.&40.)Ps9,(1:.&40.)Ps10,(1:.&40.)Ps11,(1:.&40.)Pt3,(1:.&40.)Pt4,(1:.&40.)Pt5,(1:.&40.)Pt6,(1:.&40.)PF,(59.&5.(1:.&40.))Pfc,(1:.&20.)Pm,$5:.Pmo,$3;.Ph,$5;.PLB,(9.$:.)Pn,$26.Plo,$26.P,(29.R4.R3.R6.R5.)P,(3=.$3:.R7.R2.(3>.&40.R27.))P,(24.(2>.(2?.Vsp0,))R3.)P,(24.R4.(5<.(3>.&40.R29.)$5=.))P,(3<.$3:.R:.)P,(8.(1:.&40.)R29.(23.&40.$5>.))P,(24.(3>.&40.R2<.)(18.R:.))P,(8.(1:.&40.)R25.(23.&40.R9.))P,(7.(24.=R:.)(33.R:.(34.+2.+20.)))(5?.$3:.(60.R30.R2?.R2>.R2=.R29.R28.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R11.R10.R?.R>.R=.R<.R;.R:.)(61.(62.(63.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.)R11.(23.&40.$64.)R10.(65.(1:.&40.))R?.(66.$3:.))R>.))")
(* [comment removed for export] *).
Proof.
  intros until lo. (intros dd_H; ddestruct dd_H as (ELB & RH & OW & AUX & [errv ERR] & MRP); intros ST CLO LO MI TP SPB A0 N). set (hRP := HRP (h_rc h)) in *.
  assert (ERR' : rw_cells rsegs m (errno_addr tp) [C4 errv]) by (rewrite (errno_addr_RATP tp TP); exact ERR).
  pose proof (rmalloc_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                (h_s h) (h_blocks h) n lo (h_top h) errv RH AUX SPB ST CLO LO ERR' MI TP A0 N) as IM.
  pose proof (raw_malloc_spec_c (map blk_id (h_blocks h)) GT n frame_ok_GT ltac:(lia)) as MSP.
  pose proof OW as [(L & _ & HK & _) _].
  pose proof (implM_mspec_aevt rsegs (raw_malloc n) (h_s h) _ _ _ _ mo (tmm_raw_malloc n (h_s h)) IM MSP OW
                (kl_minv _ _ _ HK) (kl_halt _ _ _ HK)) as AE.
  eapply aevt_mono; [exact AE|]. clear AE IM MSP.
  (intros [ms' mo'] dd_H; ddestruct dd_H as (a & s' & HP & HQ & MI' & HH' & VO)). cbn [cfg_ms cfg_model] in *.
  ddestruct HP as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m' & errv' & -> & MI2 & ST2 & ERR2 & AUX2 & PRES & _ & _ & CASE).
  unfold pmalloc_post, call_post. deexists 17. split; [reflexivity|].
  split; [exact MI2|]. split; [exact ST2|]. split; [apply mo_frame_of_vm_only; exact VO|].
  split; [rewrite ELB; apply heap_pres_of_r; exact PRES|].
  rewrite (errno_addr_RATP tp TP) in ERR2.
  exists s'. destruct a as [p|].
  - ddestruct CASE as (A & junk & -> & BR & RH' & UCH & _ & ZJ). destruct HQ as [OW' _].
    right. dexists A, junk, p. split; [reflexivity|]. split; [apply (block_range_r (h_rc h)); exact BR|]. split; [| split; [exact UCH| exact ZJ]].
    split; [rewrite ELB; reflexivity|]. split; [exact RH'|]. split; [exact OW'|]. split; [exact AUX2|]. split; [exists errv'; exact ERR2| exact (malloc_replaced_pres _ _ _ _ PRES MRP)].
  - destruct CASE as [-> RH'].
    left. split; [reflexivity|].
    split; [exact ELB|]. split; [exact RH'|]. split; [exact HQ|]. split; [exact AUX2|]. split; [exists errv'; exact ERR2| exact (malloc_replaced_pres _ _ _ _ PRES MRP)].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma PHEAP_malloc : ltac2:(CDefT.buildp (gd_tbl_P_heap ()) "Pra,(1:.&40.)Psp,(1:.&40.)Pgp,(1:.&40.)Ptp,(1:.&40.)Pt0,(1:.&40.)Pt1,(1:.&40.)Pt2,(1:.&40.)Ps0,(1:.&40.)Ps1,(1:.&40.)Pa0,(1:.&40.)Pa1,(1:.&40.)Pa2,(1:.&40.)Pa3,(1:.&40.)Pa4,(1:.&40.)Pa5,(1:.&40.)Pa6,(1:.&40.)Pa7,(1:.&40.)Ps2,(1:.&40.)Ps3,(1:.&40.)Ps4,(1:.&40.)Ps5,(1:.&40.)Ps6,(1:.&40.)Ps7,(1:.&40.)Ps8,(1:.&40.)Ps9,(1:.&40.)Ps10,(1:.&40.)Ps11,(1:.&40.)Pt3,(1:.&40.)Pt4,(1:.&40.)Pt5,(1:.&40.)Pt6,(1:.&40.)PF,(59.&5.(1:.&40.))Pfc,(1:.&20.)Pm,$5:.Pmo,$3;.Ph,$5;.PLB,(9.$:.)Pn,$26.Plo,$26.P,(29.R4.R3.R6.R5.)P,(3=.$3:.R7.R2.(3>.&40.R27.))P,(24.(2>.(2?.Vsp0,))R3.)P,(24.R4.(5<.(3>.&40.R29.)(67.(2?.Vsp0,))))P,(3<.$3:.R:.)P,(8.(1:.&40.)R29.(23.&40.(68.(2?.Vsp0,))))P,(24.(3>.&40.R2<.)(18.R:.))P,(8.(1:.&40.)R25.(23.&40.R9.))P,(7.(24.=R:.)(33.R:.(34.+2.+20.)))(5?.$3:.(39.$3:.R30.R2?.R2>.R2=.R29.R28.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R11.R10.Lr,(1:.&40.)Lm',P,(1:.&40.)(37.(1:.&8.))Lmo',$3;.(7.(3<.$3:.R2.)(7.(3=.$3:.R2.R=.(3>.&40.R32.))(7.(3?.R11.R1.)(7.(40.$3:.(2?.Vsp0,)R?.(3>.&40.R32.)R12.R2.)(19.$5;.Lh',$5;.(7.(8.$26.(18.R1.)(18.R11.))(28.(7.(8.(1:.&40.)R4.(23.&40.=))(29.R1.R10.R3.R2.))(19.$26.LA,$26.(19.(9.(1:.&8.))Ljunk,(9.(1:.&8.))(7.(8.(1:.&40.)R6.(23.&40.R2.))(7.(43.(2?.Vsp0,)R2.R11.)(7.(29.R3.(1>.(2=.$26.$26.)(44.$26.$26.R2.R11.)R12.)R5.R4.)(1;.$3:.R5.R2.(1>.$1?.(45.(46.R11.)R1.)(21.$1?.))))))))))))))))(61.(62.(63.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.)R11.(23.&40.(69.(2?.Vsp0,)))R10.(65.(1:.&40.))R?.(66.$3:.))R>.))")
(* [comment removed for export] *).
Proof.
  intros until lo. intros HP ST CLO LO MI TP SPB A0 N.
  change (hl_stack PL) with 8224 in *. change (hl_tp PL) with RATP in *. change (hl_malloc PL) with RMALLOC_SYM in *.
  eapply aevt_mono; [eapply (PHEAP_malloc_gen ra sp gp tp); try eassumption; unfold RMALLOC_STACK; lia|].
  intros [ms' mo'] HQ. unfold pmalloc_post, call_post in HQ |- *.
  ddestruct HQ as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m' & mo'' & E & MI2 & ST2 & MF & PRES & s' & CASE).
  deexists 17. split; [exact E|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact MF|]. split; [exact PRES|].
  destruct CASE as [[-> HP']|(A & junk & p & -> & BR & HP' & UCH & _)].
  - exists (mkHST (h_rc h) s' (h_blocks h) (h_top h)). split; [reflexivity|]. left. split; [reflexivity| exact HP'].
  - exists (mkHST (h_rc h) s' ((p, A, n) :: h_blocks h) (h_top h)). split; [reflexivity|]. right. dexists A, junk. split; [reflexivity|]. split; [exact BR|]. split; [exact HP'| exact UCH].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma bptr_eqb_eq p q : bptr_eqb p q = true <-> p = q.
Proof.
  unfold bptr_eqb. rewrite andb_true_iff, KStep.aptr_eqb_eq, Z.eqb_eq. destruct p, q; cbn. split; [intros [-> ->]; reflexivity| intros E; injection E; auto].
Qed.

#[using="Type"] Lemma lb_remove_cons p b L : Malloc_iface.lb_remove p (b :: L) = if bptr_eqb (blk_id b) p then Malloc_iface.lb_remove p L else b :: Malloc_iface.lb_remove p L.
Proof.
  unfold Malloc_iface.lb_remove. rewrite filter_cons.
  destruct (bptr_eqb (blk_id b) p); cbn [negb].
  - destruct (decide (Is_true false)) as [[]|?]; reflexivity.
  - destruct (decide (Is_true true)) as [?|n]; [reflexivity| destruct (n I)].
Qed.

#[using="Type"] Lemma lb_remove_notin p LBf : ~ In p (map blk_id LBf) -> Malloc_iface.lb_remove p LBf = LBf.
Proof.
  induction LBf as [|b LBf IH]; intros Hn; [reflexivity|]. cbn [map In] in Hn. rewrite lb_remove_cons.
  destruct (bptr_eqb (blk_id b) p) eqn:E.
  - exfalso. apply Hn. left. apply bptr_eqb_eq in E. exact E.
  - f_equal. apply IH. tauto.
Qed.

#[using="Type"] Lemma lb_remove_first : ltac2:(CDefT.buildp (gd_tbl_P_heap ()) "PLBf,(9.$<.)PA,$26.Pn,$26.P,(6:.$14.(;.$<.$14.$15.R3.))P,(31.(2=.$26.$26.)(44.$26.$26.R3.R2.)(;.$<.$:.$=.R4.))(19.$<.Lb,$<.(19.$26.Ln',$26.(7.(31.$<.R2.R7.)(7.(8.$<.R2.(44.(2=.$14.$26.)$26.(44.$14.$26.(15.R2.)R6.)R1.))(7.(8.(9.$:.)(;.$<.$:.$=.(6;.(15.R2.)R7.))(6<.R6.(;.$<.$:.$=.R7.)))(6=.$14.(1>.$14.(15.R2.)(;.$<.$14.$15.(6;.(15.R2.)R7.)))(;.$<.$14.$15.R7.)))))))")
(* [comment removed for export] *).
Proof.
  induction LBf as [|b0 LBf IH]; intros A n ND Hin; [destruct Hin|].
  cbn [map] in ND. inversion ND as [|x l Hni ND']; subst.
  destruct (Z.eq_dec (blk_addr b0) A) as [EA|NA].
  - dexists b0, (blk_size b0). split; [left; reflexivity|]. split; [destruct b0 as [[p A'] n']; cbn in *; subst; reflexivity|].
    rewrite lb_remove_cons. rewrite (proj2 (bptr_eqb_eq _ _) eq_refl). rewrite lb_remove_notin by exact Hni.
    cbn [map HeapIface.lb_remove]. unfold bview at 2. cbn [fst]. rewrite EA, Z.eqb_refl.
    split; [reflexivity| apply Permutation_refl].
  - cbn [map In] in Hin. destruct Hin as [E|Hin]; [exfalso; apply NA; unfold bview in E; injection E; auto|].
    ddestruct (IH A n ND' Hin) as (b & n' & Hb & Eb & EM & PERM).
    assert (NE : bptr_eqb (blk_id b0) (blk_id b) = false).
    { destruct (bptr_eqb (blk_id b0) (blk_id b)) eqn:E; [|reflexivity]. exfalso. apply bptr_eqb_eq in E. apply Hni. rewrite E. apply in_map. exact Hb. }
    exists b, n'. split; [right; exact Hb|]. split; [exact Eb|].
    rewrite lb_remove_cons, NE. cbn [map HeapIface.lb_remove]. unfold bview at 3. cbn [fst].
    replace (blk_addr b0 =? A) with false by (symmetry; apply Z.eqb_neq; exact NA).
    split; [f_equal; exact EM|].
    eapply Permutation_trans; [apply perm_swap|]. apply perm_skip. exact PERM.
Qed.

#[using="Type"] Lemma PHEAP_free : ltac2:(CDefT.buildp (gd_tbl_P_heap ()) "Pra,(1:.&40.)Psp,(1:.&40.)Pgp,(1:.&40.)Ptp,(1:.&40.)Pt0,(1:.&40.)Pt1,(1:.&40.)Pt2,(1:.&40.)Ps0,(1:.&40.)Ps1,(1:.&40.)Pa0,(1:.&40.)Pa1,(1:.&40.)Pa2,(1:.&40.)Pa3,(1:.&40.)Pa4,(1:.&40.)Pa5,(1:.&40.)Pa6,(1:.&40.)Pa7,(1:.&40.)Ps2,(1:.&40.)Ps3,(1:.&40.)Ps4,(1:.&40.)Ps5,(1:.&40.)Ps6,(1:.&40.)Ps7,(1:.&40.)Ps8,(1:.&40.)Ps9,(1:.&40.)Ps10,(1:.&40.)Ps11,(1:.&40.)Pt3,(1:.&40.)Pt4,(1:.&40.)Pt5,(1:.&40.)Pt6,(1:.&40.)PF,(59.&5.(1:.&40.))Pfc,(1:.&20.)Pm,$5:.Pmo,$3;.Ph,$5;.PLB,(9.$:.)PA,$26.Pn,$26.Plo,$26.P,(29.R5.R4.R7.R6.)P,(31.(2=.$26.$26.)(44.$26.$26.R4.R3.)R5.)P,(3=.$3:.R9.R3.(3>.&40.R29.))P,(24.(2>.(2?.Vsp0,))R4.)P,(24.R5.(5<.(3>.&40.R2;.)(67.(2?.Vsp0,))))P,(3<.$3:.R<.)P,(8.(1:.&40.)R2;.(23.&40.(68.(2?.Vsp0,))))P,(24.(3>.&40.R2>.)(18.R<.))P,(8.(1:.&40.)R27.(23.&40.R;.))(5?.$3:.(39.$3:.R31.R30.R2?.R2>.R2:.R29.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R12.R11.L,(1:.&40.)Lm',P,(1:.&40.)(37.(1:.&8.))Lmo',$3;.(7.(3<.$3:.R2.)(7.(3=.$3:.R2.R=.(3>.&40.R33.))(7.(3?.R12.R1.)(7.(40.$3:.(2?.Vsp0,)(6<.R?.R10.)(3>.&40.R33.)R13.R2.)(19.$5;.Lh',$5;.(7.(8.$26.(18.R1.)(18.R12.))(29.R1.(6<.R10.R11.)R3.R2.))))))))(61.(62.(63.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.)R12.(23.&40.(6>.(2?.Vsp0,)))R11.(65.(1:.&40.))R10.(66.$3:.))R?.))")
(* [comment removed for export] *).
Proof.
  intros until lo. (intros dd_H; ddestruct dd_H as (ELB & RH & OW & AUX & [errv ERR] & MRP); intros HIN ST CLO LO MI TP SPB A0). set (hRP := HRP (h_rc h)) in *.
  change (hl_stack PL) with 8224 in *. change (hl_tp PL) with RATP in *. change (hl_free PL) with RFREE_SYM in *.
  assert (ERR' : rw_cells rsegs m (errno_addr tp) [C4 errv]) by (rewrite (errno_addr_RATP tp TP); exact ERR).
  rewrite ELB in HIN.
  destruct (lb_remove_first (h_blocks h) A n (RHEAP_blocks_nodup_proof _ _ _ RH) HIN) as (b & n' & Hb & Eb & EM & PERM).
  set (p := blk_id b) in *. set (X' := map blk_id (Malloc_iface.lb_remove p (h_blocks h))) in *.
  assert (OW' : OWN (p :: X') GT (h_s h) mo) by (eapply OWN_perm; [apply Permutation_sym; exact PERM| exact OW]).
  pose proof (rfree_spec_proof ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                (h_s h) (h_blocks h) p A n' lo (h_top h) errv RH ltac:(rewrite <- Eb; exact Hb) AUX SPB ST CLO ltac:(unfold RFREE_STACK; lia) ERR' MI TP A0) as IM.
  pose proof (raw_free_spec_c X' GT p frame_ok_GT) as MSP.
  pose proof OW as [(L & _ & HK & _) _].
  pose proof (implM_mspec_aevt rsegs (raw_free p) (h_s h) _ _ _ _ mo (tmm_raw_free p (h_s h)) IM MSP OW'
                (kl_minv _ _ _ HK) (kl_halt _ _ _ HK)) as AE.
  eapply aevt_mono; [exact AE|]. clear AE IM MSP.
  (intros [ms' mo'] dd_H; ddestruct dd_H as (a & s' & HP & HQ & MI' & HH' & VO)). cbn [cfg_ms cfg_model] in *.
  ddestruct HP as (u0 & u1 & u2 & v & v0 & v1 & v2 & v3 & v4 & v5 & v6 & u3 & u4 & u5 & u6 & m' & -> & MI2 & ST2 & ERR2 & AUX2 & PRES & _ & _ & RH').
  unfold call_post. deexists 17. split; [reflexivity|].
  split; [exact MI2|]. split; [exact ST2|]. split; [apply mo_frame_of_vm_only; exact VO|].
  split; [rewrite ELB, <- EM; apply heap_pres_of_r; exact PRES|].
  rewrite (errno_addr_RATP tp TP) in ERR2.
  exists (mkHST (h_rc h) s' (Malloc_iface.lb_remove p (h_blocks h)) (h_top h)). split; [reflexivity|].
  split; [rewrite ELB; symmetry; exact EM|]. split; [exact RH'|]. split; [exact HQ|]. split; [exact AUX2|]. split; [exists errv; exact ERR2| exact (malloc_replaced_pres _ _ _ _ PRES MRP)].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma PHEAP_free_null : ltac2:(CDefT.buildp (gd_tbl_P_heap ()) "Pra,(1:.&40.)Psp,(1:.&40.)Pgp,(1:.&40.)Ptp,(1:.&40.)Pt0,(1:.&40.)Pt1,(1:.&40.)Pt2,(1:.&40.)Ps0,(1:.&40.)Ps1,(1:.&40.)Pa0,(1:.&40.)Pa1,(1:.&40.)Pa2,(1:.&40.)Pa3,(1:.&40.)Pa4,(1:.&40.)Pa5,(1:.&40.)Pa6,(1:.&40.)Pa7,(1:.&40.)Ps2,(1:.&40.)Ps3,(1:.&40.)Ps4,(1:.&40.)Ps5,(1:.&40.)Ps6,(1:.&40.)Ps7,(1:.&40.)Ps8,(1:.&40.)Ps9,(1:.&40.)Ps10,(1:.&40.)Ps11,(1:.&40.)Pt3,(1:.&40.)Pt4,(1:.&40.)Pt5,(1:.&40.)Pt6,(1:.&40.)PF,(59.&5.(1:.&40.))Pfc,(1:.&20.)Pm,$5:.P,(8.(1:.&40.)R19.(23.&40.=))(6?.$3:.Lms',$70.(8.$70.R1.(62.(63.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.)R5.(71.R24.)R4.(65.(1:.&40.))R3.(66.$3:.)))(62.(63.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.)R4.(23.&40.(6>.(2?.Vsp0,)))R3.(65.(1:.&40.))R2.(66.$3:.)))")
(* [comment removed for export] *).
Proof. intros. apply (@rfree_null_spec (HRP rc0)). assumption. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma heap_pres_stackw LB SP lo' m m1 : ltac2:(CDefT.buildp (gd_tbl_P_heap ()) "P,(2:.(1>.(2=.$26.$26.)(44.$26.$26.O3.O4.)(21.(2=.$26.$26.)))O2.O1.)P,(2;.$1<.O2.O1.)P,(24.(2>.(2?.Vsp0,))O3.)P,(2<.(2=.$26.$26.)Lb,(2=.$26.$26.)(43.(2?.Vsp0,)(25.$26.$26.R1.)(27.$26.$26.R1.))O5.)(40.$3:.(2?.Vsp0,)O5.O4.O2.O1.)")
(* [comment removed for export] *).
Proof.
  intros MU WM CLO BR a Ha Hc. split; [| intros Hw; apply WM; exact Hw].
  apply MU. rewrite wa_unsigned by lia. cbn. destruct Hc as [C|[C|([A n] & Hb & C)]].
  - lia.
  - change (hl_data_lo PL) with 0x48000 in C. change (hl_data_hi PL) with 0x7e000 in C. ceilnum. lia.
  - pose proof (proj1 (Forall_forall _ _) BR _ Hb) as (B1 & B2 & B3 & B4 & B5). cbn [fst snd] in *. lia.
Qed.

#[using="Type"] Lemma heap_pres_blockw LB SP A n m m1 : ltac2:(CDefT.buildp (gd_tbl_P_heap ()) "P,(2:.(1>.(2=.$26.$26.)(44.$26.$26.O4.(32.O4.O3.))(21.(2=.$26.$26.)))O2.O1.)P,(2;.$1<.O2.O1.)P,(43.(2?.Vsp0,)O4.O3.)P,(24.(2>.(2?.Vsp0,))O5.)P,PB,$26.Pk,$26.P,(31.(2=.$26.$26.)(44.$26.$26.R2.R1.)O6.)(28.(24.(32.O4.O3.)R3.)(24.(32.R3.R2.)O4.))(40.$3:.(2?.Vsp0,)O6.O5.O2.O1.)")
(* [comment removed for export] *).
Proof.
  (intros MU WM dd_H; ddestruct dd_H as (B1 & B2 & B3 & B4 & B5); intros CLO AP a Ha Hc). split; [| intros Hw; apply WM; exact Hw].
  apply MU. rewrite wa_unsigned by lia. cbn. change (hl_img_lo PL) with 0x10000 in B5. change (hl_img_hi PL) with 0x7e000 in B5. ceilnum.
  destruct Hc as [C|[C|([B k] & Hb & C)]].
  - lia.
  - change (hl_data_lo PL) with 0x48000 in C. change (hl_data_hi PL) with 0x7e000 in C. lia.
  - pose proof (AP B k Hb). cbn in C. lia.
Qed.

#[using="Type"] Lemma heap_pres_mono_sp LB SP1 SP2 m m1 : heap_pres usegs PL LB SP1 m m1 -> SP1 <= SP2 -> heap_pres usegs PL LB SP2 m m1.
Proof. intros HP LE a Ha Hc. apply HP; [exact Ha|]. destruct Hc as [C|C]; [left; lia| right; exact C]. Qed.

#[using="Type"] Lemma heap_pres_trans' LB SP m m1 m2 : heap_pres usegs PL LB SP m m1 -> heap_pres usegs PL LB SP m1 m2 -> heap_pres usegs PL LB SP m m2.
Proof. intros H1 H2. eapply heap_pres_trans_sub; [exact H1| exact H2| intros b Hb; exact Hb]. Qed.

#[using="Type"] Lemma calloc_args_norm cnt sz : ltac2:(CDefT.buildp (gd_tbl_P_heap ()) "P,(24.=O2.)P,(24.=O1.)P,(33.(72.O2.O1.)(34.+2.+20.))(19.$26.Lcnt',$26.(19.$26.Lsz',$26.(7.(8.(1:.&40.)(23.&40.O2.)(23.&40.R2.))(7.(8.(1:.&40.)(23.&40.O1.)(23.&40.R1.))(7.(7.(24.=R2.)(33.R2.(34.+2.+40.)))(7.(7.(24.=R1.)(33.R1.(34.+2.+40.)))(8.$26.(72.R2.R1.)(72.O2.O1.))))))))")
(* [comment removed for export] *).
Proof.
  intros C S P. destruct (Z.lt_ge_cases cnt (2^64)) as [LC|GC].
  - destruct (Z.lt_ge_cases sz (2^64)) as [LS|GS]; [dexists cnt, sz; repeat split; lia|].
    assert (cnt = 0) by nia. subst cnt. dexists 0, (sz mod 2^64). rewrite <- (Z_to_bv_mod64 sz).
    pose proof (Z.mod_pos_bound sz (2^64) ltac:(lia)). repeat split; lia.
  - assert (sz = 0) by nia. subst sz. dexists (cnt mod 2^64), 0. rewrite <- (Z_to_bv_mod64 cnt).
    pose proof (Z.mod_pos_bound cnt (2^64) ltac:(lia)). repeat split; lia.
Qed.

#[using="Type"] Lemma PHEAP_calloc : ltac2:(CDefT.buildp (gd_tbl_P_heap ()) "Pra,(1:.&40.)Psp,(1:.&40.)Pgp,(1:.&40.)Ptp,(1:.&40.)Pt0,(1:.&40.)Pt1,(1:.&40.)Pt2,(1:.&40.)Ps0,(1:.&40.)Ps1,(1:.&40.)Pa0,(1:.&40.)Pa1,(1:.&40.)Pa2,(1:.&40.)Pa3,(1:.&40.)Pa4,(1:.&40.)Pa5,(1:.&40.)Pa6,(1:.&40.)Pa7,(1:.&40.)Ps2,(1:.&40.)Ps3,(1:.&40.)Ps4,(1:.&40.)Ps5,(1:.&40.)Ps6,(1:.&40.)Ps7,(1:.&40.)Ps8,(1:.&40.)Ps9,(1:.&40.)Ps10,(1:.&40.)Ps11,(1:.&40.)Pt3,(1:.&40.)Pt4,(1:.&40.)Pt5,(1:.&40.)Pt6,(1:.&40.)PF,(59.&5.(1:.&40.))Pfc,(1:.&20.)Pm,$5:.Pmo,$3;.Ph,$5;.PLB,(9.$:.)Pcnt,$26.Psz,$26.Plo,$26.P,(29.R5.R4.R7.R6.)P,(3=.$3:.R8.R2.(3>.&40.R28.))P,(24.(2>.(2?.Vsp0,))R3.)P,(24.R4.(5<.(3>.&40.R2:.)(67.(2?.Vsp0,))))P,(3<.$3:.R;.)P,(8.(1:.&40.)R2:.(23.&40.(68.(2?.Vsp0,))))P,(24.(3>.&40.R2=.)(18.R;.))P,(8.(1:.&40.)R26.(23.&40.R:.))P,(8.(1:.&40.)R26.(23.&40.R:.))P,(24.=R<.)P,(24.=R<.)P,(33.(72.R>.R=.)(34.+2.+20.))(5?.$3:.(39.$3:.R34.R33.R32.R31.R2=.R2<.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R15.R14.Lr,(1:.&40.)Lm',P,(1:.&40.)(37.(1:.&8.))Lmo',$3;.(7.(3<.$3:.R2.)(7.(3=.$3:.R2.R10.(3>.&40.R36.))(7.(3?.R15.R1.)(7.(40.$3:.(2?.Vsp0,)R13.(3>.&40.R36.)R16.R2.)(19.$5;.Lh',$5;.(7.(8.$26.(18.R1.)(18.R15.))(28.(7.(8.(1:.&40.)R4.(23.&40.=))(29.R1.R14.R3.R2.))(19.$26.LA,$26.(7.(8.(1:.&40.)R5.(23.&40.R1.))(7.(43.(2?.Vsp0,)R1.(72.R14.R13.))(7.(29.R2.(1>.(2=.$26.$26.)(44.$26.$26.R1.(72.R14.R13.))R15.)R4.R3.)(1;.$3:.R4.R1.(1>.$1?.(45.(46.(72.R14.R13.))(58.(1:.&8.)(23.&8.=)(46.(72.R14.R13.))))(21.$1?.)))))))))))))))(61.(62.(63.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.)R15.(23.&40.(73.(2?.Vsp0,)))R14.(65.(1:.&40.))R13.(66.$3:.))R12.))")
(* [comment removed for export] *).
Proof.
  intros until lo. intros HP ST CLO LO MI TP SPB A0 A1 C0 S0 PR. set (hRP := HRP (h_rc h)) in *.
  change (hl_stack PL) with 8224 in *. change (hl_tp PL) with RATP in *. change (hl_calloc PL) with 0x3f960 in *.
  pose proof (PHEAP_mok _ _ _ _ HP) as MK. pose proof (PHEAP_blocks _ _ _ _ HP) as [BRs _].
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof CLO as CLON. pose proof (run_ceil_lo sp0) as RCLO. change ACEIL with (run_ceil sp0) in CLON.
  ddestruct (calloc_args_norm cnt sz C0 S0 PR) as (cnt' & sz' & E0 & E1 & C' & S' & EP).
  rewrite E0 in A0. rewrite E1 in A1. rewrite <- EP. assert (PR' : cnt' * sz' < 2^32) by lia.
  clear E0 E1 C0 S0 EP PR cnt sz. rename cnt' into cnt. rename sz' into sz. rename PR' into PR.
  (* [comment removed for export] *)
  apply (aevtM_cut_evt usegs mo _ _ _ MK (@rcalloc_pre hRP ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo cnt sz
           ST CLO ltac:(lia) MI A0 A1 C' S' PR)).
  (intros ms1 dd_H; ddestruct dd_H as (a2' & m1 & -> & MU1 & WM1 & MI1 & ST1 & [j0 FR1])).
  assert (HP1 : PHEAP h LB m1 mo).
  { eapply PHEAP_frame; [exact HP| exact MU1| exact WM1|]. constructor; [left; cbn; lia| constructor]. }
  assert (PRES1 : heap_pres usegs PL LB (bv_unsigned sp) m m1) by (eapply heap_pres_stackw; [exact MU1| exact WM1| lia| exact BRs]).
  assert (SPE : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  (* [comment removed for export] *)
  eapply aevtM_cut.
  { eapply (PHEAP_malloc_gen (Z_to_bv 64 0x3f9b0) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp); try eassumption; rewrite ?SPE; [exact ST1| unfold RMALLOC_STACK; lia| lia| reflexivity| lia]. }
  cbv beta. intros ms2 mo2 PO. unfold pmalloc_post, call_post in PO.
  ddestruct PO as (u0 & u1 & u2 & r & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & mo2' & E & MI2 & ST2 & MF2 & PRES2 & s' & CASE).
  injection E as -> ->.
  replace (ret_pc (Z_to_bv 64 0x3f9b0)) with (Z_to_bv 64 0x3f9b0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  rewrite SPE in ST2, PRES2.
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp + -32) [CB 8 j0; C8 s1; C8 s0; C8 ra]).
  { eapply heap_pres_rw_cells; [exact PRES2| exact FR1|]. intros a Ha. left. lia. }
  assert (PRES12 : heap_pres usegs PL LB (bv_unsigned sp) m m2).
  { eapply heap_pres_trans'; [exact PRES1|]. eapply heap_pres_mono_sp; [exact PRES2| lia]. }
  destruct CASE as [[-> HP2]|(A & junk & p & -> & BR & HP2 & UCH & ZJ)].
  - (* [comment removed for export] *)
    pose proof (PHEAP_mok _ _ _ _ HP2) as MK2.
    apply (aevtM_cut_evt usegs mo2' _ _ _ MK2 (@rcalloc_null hRP sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ ra s0 s1 F fc m2 lo j0
             ST2 CLO ltac:(lia) FR2 MI2)).
    intros ms3 [-> ST3]. apply aevtM_done. unfold call_post. deexists 17. split; [reflexivity|].
    split; [exact MI2|]. split; [exact ST3|]. split; [exact MF2|]. split; [exact PRES12|].
    exists (mkHST (h_rc h) s' (h_blocks h) (h_top h)). split; [reflexivity|]. left. split; [reflexivity| exact HP2].
  - (* [comment removed for export] *)
    pose proof (PHEAP_mok _ _ _ _ HP2) as MK2. dpose HP2 as (_ & RH2 & _ & _ & _ & MRP2).
    dpose BR as (B1 & B2 & B3 & B4 & B5). change (hl_img_lo PL) with 0x10000 in B5. change (hl_img_hi PL) with 0x7e000 in B5.
    pose proof B4 as B4N. change ACEIL with (run_ceil sp0) in B4N.
    apply (aevtM_cut_evt usegs mo2' _ _ _ MK2 (rcalloc_chk sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m2 A ltac:(lia) MRP2)).
    intros ms3 ->.
    ddestruct (@rallzerop_heap hRP (Z_to_bv 64 0x3fa90) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp u0 u1 u2 (Z_to_bv 64 A) (Z_to_bv 64 (cnt * sz)) (Z_to_bv 64 A) v1 v2 v3 v4 v5 v6 v7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F fc m2
                s' ((p, A, cnt * sz) :: h_blocks h) p A (cnt * sz) RH2 (or_introl eq_refl) MI2 eq_refl) as (g & i & z & SL & HZ & ZR & EV).
    unfold rallzerop_entry in EV.
    apply (aevtM_cut_evt usegs mo2' _ _ _ MK2 EV). (intros ms4 dd_H; ddestruct dd_H as (w1 & w2 & w3 & w4 & w5 & w6 & ->)).
    replace (ret_pc (Z_to_bv 64 0x3fa90)) with (Z_to_bv 64 0x3fa90) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    destruct (Z.eq_dec z 0) as [->|NZ].
    + (* [comment removed for export] *)
      pose proof UCH as [_ W2]. cbn [cells_size csize Nat.add] in W2. rewrite Nat.add_0_r, Z2Nat.id in W2 by lia.
      unfold wz. st1. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia; [exfalso; apply K; reflexivity|]. st1.
      apply (aevtM_cut_evt usegs mo2' _ _ _ MK2 (@rcalloc_clear hRP sp gp tp _ _ _ _ _ _ _ _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ _ ra s0 s1 F fc m2 lo A (cnt * sz) j0
               ST2 CLO ltac:(lia) MI2 FR2 W2 B1 B4 B5 ltac:(lia))).
      intros ms5 PO. unfold rcc_post in PO.
      ddestruct PO as (x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m3 & -> & MU3 & WM3 & MI3 & ST3 & ZB & W3).
      assert (HP3 : PHEAP (mkHST (h_rc h) s' ((p, A, cnt * sz) :: h_blocks h) (h_top h)) ((A, cnt * sz) :: LB) m3 mo2').
      { eapply PHEAP_frame; [exact HP2| exact MU3| exact WM3|]. constructor; [| constructor]. right; right. exists (A, cnt * sz). split; [left; reflexivity| cbn; lia]. }
      apply aevtM_done. unfold call_post. deexists 17. split; [reflexivity|].
      split; [exact MI3|]. split; [exact ST3|]. split; [exact MF2|].
      split. { eapply heap_pres_trans'; [exact PRES12|]. eapply heap_pres_blockw; [exact MU3| exact WM3| exact BR| lia|].
               pose proof (PHEAP_blocks _ _ _ _ HP2) as [_ [AP _]]. exact AP. }
      exists (mkHST (h_rc h) s' ((p, A, cnt * sz) :: h_blocks h) (h_top h)). split; [reflexivity|]. right. exists A.
      split; [reflexivity|]. split; [exact BR|]. split; [exact HP3|].
      apply F_malloc_free.rw_cells_of_bytes; cbn; [rewrite repeat_length; split; reflexivity| rewrite app_nil_r; exact ZB| rewrite Nat.add_0_r, Z2Nat.id by lia; exact W3].
    + (* [comment removed for export] *)
      pose proof (ZJ g i SL (proj1 HZ NZ)) as ->.
      apply (aevtM_cut_evt usegs mo2' _ _ _ MK2 (@rcalloc_ret_same hRP sp gp tp _ _ _ _ _ _ _ _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ ra s0 s1 F fc m2 lo A z j0
               ST2 CLO ltac:(lia) FR2 MI2 NZ ltac:(lia) ltac:(lia))).
      intros ms5 [-> ST5]. apply aevtM_done. unfold call_post. deexists 17. split; [reflexivity|].
      split; [exact MI2|]. split; [exact ST5|]. split; [exact MF2|]. split; [exact PRES12|].
      exists (mkHST (h_rc h) s' ((p, A, cnt * sz) :: h_blocks h) (h_top h)). split; [reflexivity|]. right. exists A.
      split; [reflexivity|]. split; [exact BR|]. split; [exact HP2| exact UCH].
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma U_heap_statics h LB m mo : ltac2:(CDefT.buildp (gd_tbl_P_heap ()) "P,(29.O4.O3.O2.O1.)(7.(1;.$3:.O2.+7=353.(1>.$1?.(74.(23.&8.=))(21.$1?.)))(7.(1;.$3:.O2.+7=330.(1>.$1?.(75.(23.&40.(2.(11.O4.))))(21.$1?.)))(7.(1;.$3:.O2.+4;<=8.(1>.$1?.(75.(23.&40.+7=330.))(21.$1?.)))(7.(1;.$3:.O2.+7=380.(1>.$1?.(75.(23.&40.+1000.))(21.$1?.)))(7.(1;.$3:.O2.+7=3<0.(1>.$1?.(20.(23.&40.=))(21.$1?.)))(19.(1:.&40.)Le,(1:.&40.)(1;.$3:.O2.+5=024.(1>.$1?.(20.R1.)(21.$1?.)))))))))")
(* [comment removed for export] *).           (* [comment removed for export] *)
Proof.
  (intros dd_H; ddestruct dd_H as (_ & (st & LB0 & _ & _ & MR & _) & _ & _ & ERR & _)).
  dpose MR as (_ & _ & (L1 & L2 & L3 & L4 & L5) & _).
  unfold RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD, RERRNO, wz, b8 in *.
  split; [exact L2|]. split; [exact L5|]. split; [exact L4|]. split; [exact L3|]. split; [exact L1| exact ERR].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac rimg_chunk NONE m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  assert (H : rw_cells rsegs m A cs);
  [ apply (rw_cells_recast rsegs m A [CB (length bs) bs] cs);
    [ apply (rw_cells_image0 rsegs m A bs);
      [ intros a Ha; apply NONE; cbn [length] in Ha; lia | vm_compute; reflexivity | lia | cbn [length]; lia ]
    | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
  | ].

(* [comment removed for export] *)
Record U_heap_init_hyps (rc : rconsts) (m : mem) (mo : Model) (top : Z) : Prop := mkPHI {
  (* [comment removed for export] *)
  phi_bss : forall a : word, 0x7d3c0 <= bv_unsigned a < 0x7d76c -> m a = None;
  (* [comment removed for export] *)
  phi_need_locks : rw_cells usegs m 0x7d353 [C1 (Z_to_bv 8 0)];
  (* [comment removed for export] *)
  phi_page_size : rw_cells usegs m 0x7d380 [C8 (Z_to_bv 64 4096)];
  (* [comment removed for export] *)
  phi_auxv : @rauxv_ok (HRP rc) m top;
  (* [comment removed for export] *)
  phi_got : rw_cells usegs m 0x4bcd8 [C8 (Z_to_bv 64 0x7d330)];
  phi_guard : rw_cells usegs m 0x7d330 [C8 (Z_to_bv 64 (rc_canary rc))];
  (* [comment removed for export] *)
  phi_errno : exists e, rw_cells usegs m 0x5d024 [C4 e];
  phi_minv : mem_inv usegs m;
  (* [comment removed for export] *)
  phi_lazy : m_vm_lazy mo = [];
  phi_halt : m_halted mo = None;
  phi_maps : vm_maps (m_vmmaps mo) = [];
  phi_resv : vm_reserved (m_vmmaps mo) = segments_reserved usegs;
  phi_brk : vm_brk (m_vmmaps mo) = vm_start_brk (m_vmmaps mo);
  phi_valid : valid_brk usegs (vm_start_brk (m_vmmaps mo));
  (* [comment removed for export] *)
  phi_isp : vm_init_sp (m_vmmaps mo) = sp0;
  phi_vsp : valid_sp sp0
}.

#[using="Type"] Lemma reserved_top_ge l e : In e l -> ehi e <= reserved_top l.
Proof.
  induction l as [|[a sz] l IH]; intros Hin; [destruct Hin|]. cbn [reserved_top]. destruct Hin as [<-|Hin]; [unfold ehi; cbn; lia|].
  specialize (IH Hin). lia.
Qed.

#[using="Type"] Lemma U_heap_init_s rc m mo top : ltac2:(CDefT.buildp (gd_tbl_P_heap ()) "P,(76.O4.O3.O2.O1.)(19.$5;.Lh,$5;.(7.(29.R1.(21.$:.)O3.O2.)(7.(8.$26.(18.R1.)O1.)(7.(8.$41.(12.R1.)(77.(1.O4.)(2.O4.)(3.Vsp0,)(78.$1<.)))(7.(8.(9.$<.)(>.R1.)(21.$<.))(8.$79.(11.R1.)O4.))))))")
(* [comment removed for export] *).
Proof.
  intros [NONE NL PS AUXV GOT GUARD ERR MI LZ HALT MAPS RESV BRK VB ISP VSP]. set (hRP := HRP rc) in *.
  pose proof (rc_secret_range rc) as SR. pose proof (rc_canary_range rc) as GR. pose proof run_ceil_cok as CO.
  set (st0 := minit (rc_secret rc) (rc_canary rc) (run_ceil sp0) ref_reserved).
  rimg_chunk NONE m 0x7d3c8%Z (ctx_head_cells st0) CXH.
  rimg_chunk NONE m (0x7d3c8 + 80)%Z [CB 384 (u64s (repeat (wz 0) 48))] CXA.
  rimg_chunk NONE m (0x7d3c8 + 464)%Z [CB 384 (u64s (repeat (wz 0) 48))] CXU.
  rimg_chunk NONE m (0x7d3c8 + 848)%Z [CB 32 (MallocRep.zeros 32)] CXS.
  rimg_chunk NONE m (0x7d3c8 + 880)%Z [CB 32 (MallocRep.zeros 32)] CXB.
  rimg_chunk NONE m (0x7d3c8 + 912)%Z (ctx_tail_cells st0) CXT.
  rimg_chunk NONE m 0x7d3c0%Z [C4 (wz 0)] ML.
  rimg_chunk NONE m 0x7d768%Z [C4 (Z_to_bv 64 0)] MRP.
  exists (mkHST rc (ps_init (rc_secret rc) (rc_canary rc) (run_ceil sp0) (reservedZ rsegs)) [] top). split; [| split; [reflexivity| split; [reflexivity| split; reflexivity]]].
  split; [reflexivity|]. split; [| split; [| split; [exact AUXV| split; [exact ERR| exact MRP]]]].
  - (* [comment removed for export] *)
    dexists st0, []. split; [apply Permutation_refl|]. split; [unfold ps_init; cbn [ps_m]; rewrite reservedZ_ref; reflexivity|].
    split.
    2:{ unfold ps_init; cbn [ps_brk]. apply HINV_from_init; assumption. }
    split; [|split; [|split; [|split; [|split]]]].
    + (* [comment removed for export] *) split.
      { (* [comment removed for export] *) split; [reflexivity|]. split; [apply s_ceil_minit; exact CO|]. split; reflexivity. }
      split; [intros rid r H; rewrite lookup_empty in H; discriminate|].
      split; [intros ? ? ? ? H; rewrite lookup_empty in H; discriminate|].
      split; [intros ? ? H; cbn in H; rewrite lookup_empty in H; discriminate|].
      intros ? ? H; cbn in H; rewrite lookup_empty in H; discriminate.
    + unfold rmrep_ctx, RCTX. split; [exact CXH|]. split; [|split; [|split; [|split]]].
      * replace (actives st0) with (repeat (wz 0) 48) by reflexivity. eapply u64arr_of_rw_cells'; [exact CXA| reflexivity| reflexivity].
      * replace (usages st0) with (repeat (wz 0) 48) by reflexivity. eapply u64arr_of_rw_cells'; [exact CXU| reflexivity| reflexivity].
      * replace (unmap_seqs st0) with (MallocRep.zeros 32) by reflexivity. apply (u8arr_of_rw_cells rsegs m _ 32). exact CXS.
      * replace (bouncess st0) with (MallocRep.zeros 32) by reflexivity. apply (u8arr_of_rw_cells rsegs m _ 32). exact CXB.
      * exact CXT.
    + unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD. split; [exact ML|]. split; [|split; [|split]].
      * change (b8 0) with (Z_to_bv 8 0). exact NL.
      * change (wz 4096) with (Z_to_bv 64 4096). exact PS.
      * change (wz 512816) with (Z_to_bv 64 0x7d330). exact GOT.
      * exact GUARD.
    + intros a ar H. cbn in H. rewrite lookup_empty in H. discriminate.
    + intros b gh H. cbn in H. rewrite lookup_empty in H. discriminate.
    + intros rid r H. cbn in H. rewrite lookup_empty in H. discriminate.
  - (* [comment removed for export] *)
    split; [| split; [apply List.NoDup_nil| exact I]].
    exists (led_init (run_ceil sp0) (reservedZ rsegs)). split; [unfold ps_init; cbn [ps_m]; apply creach_init; assumption|]. split; [| intros c []].
    dpose VB as (Vlo & Vhi & Val). pose proof (run_ceil_lo sp0) as RCL.
    assert (RT : reserved_top (segments_reserved usegs) = 0x7e000) by (vm_compute; reflexivity).
    constructor; rewrite ?MAPS, ?RESV, ?BRK.
    + exact LZ.
    + exact HALT.
    + split; [intros e []| apply pwdisj_nil].
    + (* [comment removed for export] *) cbn [ld_ceil led_init]. unfold alloc_top. rewrite ISP. change stack_max_size with 8388608. apply run_ceil_eq. exact VSP.
    + (* [comment removed for export] *) cbn [ld_ceil led_init]. exact CO.
    + cbn [ld_resv led_init]. rewrite reservedZ_ref. vm_compute. reflexivity.
    + intros e Hin. pose proof (reserved_top_ge _ _ Hin). lia.
    + cbn [ld_ceil led_init]. unfold PGSZ, page_size, brk_aslr_max in *. lia.
    + intros b l [].
    + intros b l k [].
    + apply List.NoDup_nil.
    + intros b l H. discriminate.
    + cbn [ld_brk led_init ld_brkreg]. split; [reflexivity| reflexivity].
Qed.


(* [comment removed for export] *)
#[using="Type"] Lemma bytes_at_of_rdn_h : ltac2:(CDefT.buildp (gd_tbl_P_heap ()) "Pm,P,(1:.&40.)(37.(1:.&8.))Pbs,(9.(1:.&8.))Pa,$26.P,(8.(37.(9.(1:.&8.)))(7:.$3:.R3.(23.&40.R1.)(7;.(1:.&8.)R2.))(55.(9.(1:.&8.))R2.))P,(24.=R2.)P,(24.(32.R3.(7<.(7;.(1:.&8.)R4.)))(34.+2.+40.))(7=.$3:.R6.R4.R5.)")
(* [comment removed for export] *).
Proof.
  intros m bs. induction bs as [|b bs IH]; intros a H Ha Hl.
  - apply bytes_at_nil. cbn in Hl. lia.
  - cbn [length] in H, Hl. rewrite rdn_unfold in H.
    destruct (mrd usegs m (Z_to_bv 64 a)) as [b'|] eqn:E; [|discriminate].
    destruct (rdn usegs m (Z_to_bv 64 a + 1) (length bs)) as [r|] eqn:E2; [|discriminate].
    injection H as Hb Hr. subst b' r.
    change (b :: bs) with ([b] ++ bs). apply (proj2 (bytes_at_app usegs m a [b] bs)). split.
    + split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. destruct i; [|lia]. cbn. rewrite Z.add_0_r. unfold wa. exact E.
    + change (Z.of_nat (length [b])) with 1. apply IH; try lia.
      replace (Z_to_bv 64 (a + 1)) with (Z_to_bv 64 a + 1 : word)%bv; [exact E2|].
      apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. change (bv_unsigned (1 : word)) with 1.
      rewrite !bv_wrap64_mod. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

#[using="Type"] Lemma auxv_bytes_of_rdn : ltac2:(CDefT.buildp (gd_tbl_P_heap ()) "Pm,P,(1:.&40.)(37.(1:.&8.))Pl,(9.$26.)Pa,$26.P,Pi,$7>.Pv,$26.P,(8.(37.$26.)(7?.$26.R4.R2.)(55.$26.R1.))(8.(37.(9.(1:.&8.)))(7:.$3:.R6.(23.&40.(32.R4.(72.+8.(7<.R3.))))#8.)(55.(9.(1:.&8.))(80.#8.(23.&40.R2.))))P,(24.=R2.)P,(24.(32.R3.(72.+8.(7<.(7;.$26.R4.))))(34.+2.+40.))(7=.$3:.R6.R4.(81.(;.$26.(1:.&40.)$82.R5.)))")
(* [comment removed for export] *).
Proof.
  intros m l. induction l as [|v l IH]; intros a RD Ha Hl.
  - cbn. apply bytes_at_nil. lia.
  - cbn [map u64s].
    apply (proj2 (bytes_at_app usegs m a (le8 (wz v)) (u64s (map wz l)))). rewrite length_le8. split.
    + specialize (RD 0%nat v eq_refl). rewrite Z.mul_0_r, Z.add_0_r in RD.
      apply bytes_at_of_rdn_h; [exact RD| lia| rewrite length_le8; cbn [length] in Hl; lia].
    + apply IH; [| lia| cbn [length] in Hl; lia]. intros i w Hi. replace (a + 8 + 8 * Z.of_nat i) with (a + 8 * Z.of_nat (S i)) by lia. apply RD. exact Hi.
Qed.

#[using="Type"] Lemma rauxv_ok_intro (rc : rconsts) : ltac2:(CDefT.buildp (gd_tbl_P_heap ()) "Pm,P,(1:.&40.)(37.(1:.&8.))Ptop,$26.Pav,$26.Prnd,$26.Px3,$26.Px4,$26.Px5,$26.Phw,$26.Px6,$26.Px11,$26.Px12,$26.Px23,$26.P,(8.(37.(9.(1:.&8.)))(7:.$3:.R<.(23.&40.+7=358.)#8.)(55.(9.(1:.&8.))(80.#8.(23.&40.R:.))))P,Pi,$7>.Pv,$26.P,(8.(37.$26.)(7?.$26.(1>.$26.+3.(1>.$26.R;.(1>.$26.+4.(1>.$26.R:.(1>.$26.+5.(1>.$26.R9.(1>.$26.+10.(1>.$26.R8.(1>.$26.+6.(1>.$26.R7.(1>.$26.+;.(1>.$26.R6.(1>.$26.+<.(1>.$26.R5.(1>.$26.+17.(1>.$26.R4.(1>.$26.+19.(1>.$26.R<.(1>.$26.=(1>.$26.=(21.$26.)))))))))))))))))))))R2.)(55.$26.R1.))(8.(37.(9.(1:.&8.)))(7:.$3:.R10.(23.&40.(32.R>.(72.+8.(7<.R3.))))#8.)(55.(9.(1:.&8.))(80.#8.(23.&40.R2.))))P,(8.(37.(9.(1:.&8.)))(7:.$3:.R>.(23.&40.(32.R;.+8.))#8.)(55.(9.(1:.&8.))(80.#8.(23.&40.(1.O1.)))))P,(24.(2>.(2?.Vsp0,))R>.)P,(24.R?.R>.)P,(24.(32.R?.+:0.)(34.+2.+40.))P,(24.R11.(32.R?.+8.))P,(24.(32.R10.+10.)(34.+2.+40.))P,(7.(24.=R10.)(33.R10.(34.+2.+40.)))P,(7.(24.=R10.)(33.R10.(34.+2.+40.)))P,(7.(24.=R10.)(33.R10.(34.+2.+40.)))P,(7.(24.=R10.)(33.R10.(34.+2.+40.)))P,(7.(24.=R10.)(33.R10.(34.+2.+40.)))P,(7.(24.=R10.)(33.R10.(34.+2.+40.)))P,(7.(24.=R10.)(33.R10.(34.+2.+40.)))P,(7.(24.=R10.)(33.R10.(34.+2.+40.)))P,(24.=R19.)(17.(10.O1.)R1=.R1<.)")
(* [comment removed for export] *).
Proof.
  intros until x23. intros RC RV RZ T0 T1 T2 T3 T4 R3 R4 R5 Rhw R6 R11 R12 R23 Rr. set (hRP := HRP rc) in *.
  pose proof T0 as T0N. pose proof (run_ceil_lo sp0) as RCL. change ACEIL with (run_ceil sp0) in T0N.
  dexists av, x3, x4, x5, hw, x6, x11, x12, x23, rnd.
  split. { (* [comment removed for export] *) split.
    - split; [cbn; split; exact I|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. unfold RAUXV_CELL, wz. apply bytes_at_of_rdn_h; [rewrite length_le8; exact RC| lia| rewrite length_le8; lia].
    - cbn [cells_size csize Nat.add]. unfold RAUXV_CELL. split; [lia|]. split; [lia|]. intros i Hi. unfold wview.
      destruct (m (wa (512856 + i))); [discriminate|].
      assert (E : exists k, (k < 8)%nat /\ i = Z.of_nat k) by (exists (Z.to_nat i); lia). ddestruct E as (k & Hk & ->).
      do 8 (destruct k as [|k]; [vm_compute; discriminate|]). lia. }
  split. { unfold rauxv_list. apply (auxv_bytes_of_rdn m _ av RV); [lia| cbn [length]; lia]. }
  split. { unfold wz. apply bytes_at_of_rdn_h; rewrite ?length_le8; [exact RZ| lia| lia]. }
  change (@rceil hRP) with (run_ceil sp0). lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma KL_mo_other L0 pbrk mo mo' : ltac2:(CDefT.buildp (gd_tbl_P_heap ()) "P,(8.$83.(84.O1.)(84.O2.))P,(8.(37.(1:.&40.))(85.O1.)(85.O2.))P,(8.(9.(2=.(1:.&40.)(1:.&40.)))(86.O1.)(86.O2.))P,(87.O4.O3.O2.)(87.O4.O3.O1.)")
(* [comment removed for export] *).
Proof.
  intros E1 E2 E3 K. destruct K as [K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13].
  constructor; unfold minv in *; rewrite ?E1, ?E2, ?E3; assumption.
Qed.

#[using="Type"] Lemma PHEAP_mo_other h LB m mo mo' : ltac2:(CDefT.buildp (gd_tbl_P_heap ()) "P,(8.$83.(84.O1.)(84.O2.))P,(8.(37.(1:.&40.))(85.O1.)(85.O2.))P,(8.(9.(2=.(1:.&40.)(1:.&40.)))(86.O1.)(86.O2.))P,(29.O5.O4.O3.O2.)(29.O5.O4.O3.O1.)")
(* [comment removed for export] *).
Proof.
  (intros E1 E2 E3 dd_H; ddestruct dd_H as (ELB & RH & [(L0 & CR & K & INCL) [ND _]] & REST)).
  split; [exact ELB|]. split; [exact RH|]. split; [| exact REST].
  split; [| split; [exact ND| exact Logic.I]]. exists L0. split; [exact CR|]. split; [eapply KL_mo_other; eassumption| exact INCL].
Qed.

(* [comment removed for export] *)
Definition U_HI : heap_iface usegs PL := ltac2:(CDefT.buildp (gd_tbl_P_heap ()) "(88.$3:.(2?.Vsp0,)$5;.$29.$18.$89.$8:.$8;.Lh,$5;.LLB,(9.$:.)Lm,P,(1:.&40.)(37.(1:.&8.))Lmo,$3;.Lmo',$3;.LHH,(29.R5.R4.R3.R2.)LE1,(8.$83.(84.R2.)(84.R3.))LE2,(8.(9.(2=.(1:.&40.)(1:.&40.)))(86.R3.)(86.R4.))LE3,(8.(37.(1:.&40.))(85.R4.)(85.R5.))(8<.R9.R8.R7.R6.R5.R3.R1.R2.R4.)$8=.$8>.$8?.$90.)")
(* [comment removed for export] *).

End PHeap.
