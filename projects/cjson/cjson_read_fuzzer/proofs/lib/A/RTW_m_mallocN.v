(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require MState.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Cells.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Step.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Exec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Spin.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require SRealizes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_rep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_cost.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_sec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_leaves_memset.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_nn_specs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_lib2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_p_abs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_tpz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_specs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_unwind.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_sec_dstateP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_bandtac4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
Module RTW_m_malloc.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Exec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_sec.RTW_secondary_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_depot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_a1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_lib2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_lib3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_tpz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_specs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_aspec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_i1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_unwind OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstateP.RTW_m_live OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_bandtac4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma uwt_mem : forall m m' lo top pc0 prev f k tl,
  uwt m lo top pc0 prev f k tl -> (forall a, lo <= a -> a < 2^64 -> m' (wa a) = m (wa a)) -> uwt m' lo top pc0 prev f k tl.
Proof.
  intros m m' lo top pc0 prev f k tl H EQ. induction H.
  - apply uwt_stop. assumption.
  - eapply uwt_lowpc; eauto. (nelim H4 3%nat; intros B0 B1 BB). split; [exact B0|]. split; [exact B1|].
    intros i Hi. unfold mrd in *. rewrite EQ by (rewrite length_app, !length_le8 in Hi, B1; lia). apply BB. exact Hi.
  - eapply uwt_hop; eauto. (nelim H4 3%nat; intros B0 B1 BB). split; [exact B0|]. split; [exact B1|].
    intros i Hi. unfold mrd in *. rewrite EQ by (rewrite length_app, !length_le8 in Hi, B1; lia). apply BB. exact Hi.
Qed.

Lemma uwt_range : forall m lo top pc0 prev f k tl, uwt m lo top pc0 prev f k tl -> Forall (fun pc => 0 <= pc < 2^64) tl.
Proof.
  intros m lo top pc0 prev f k tl H. induction H as [| | prev f k nxt pc1 tl H H0 H1 H2 H3 H4 H5 H6 IH]; [constructor| constructor|].
  apply Forall_app. split; [| exact IH]. destruct (bv_unsigned pc1 =? pc0); [constructor|].
  pose proof (bv_unsigned_in_range 64 pc1) as R. unfold bv_modulus in R. cbn in R.
  constructor; [lia| constructor].
Qed.

Lemma hook_tr_facts : forall pc0 sp0 sp ra tl m top prev f,
  0 <= pc0 < 2^64 -> 0 <= ra < 2^64 -> uwt m sp top pc0 prev f 2 tl ->
  1 <= zlen (hook_tr pc0 sp0 sp ra tl) <= TRACE_MAX_LEN /\ Forall (fun pc => 0 <= pc < 2^64) (hook_tr pc0 sp0 sp ra tl).
Proof.
  intros pc0 sp0 sp ra tl m top prev f Hp Hr U. pose proof (uwt_len _ _ _ _ _ _ _ _ U ltac:(unfold TRACE_MAX_LEN; lia)) as L.
  pose proof (uwt_range _ _ _ _ _ _ _ _ U) as R. unfold hook_tr. destruct (hop1_ok sp0 sp).
  - rewrite !zlen_cons. pose proof (zlen_nonneg tl). split; [unfold TRACE_MAX_LEN in *; lia|]. constructor; [lia|]. constructor; [lia| exact R].
  - cbn. split; [unfold TRACE_MAX_LEN; unfold zlen; cbn; lia|]. constructor; [lia| constructor].
Qed.

Lemma alloc_deposit_le_cost : forall n, 0 <= n < 2^32 -> 0 <= alloc_deposit n <= cost_malloc n.
Proof.
  intros n Hn. unfold alloc_deposit, calloc_deposit, cost_malloc, fp, rp. pose proof (Z.div_pos n 32 ltac:(lia) ltac:(lia)).
  pose proof (cl24_tax_nonneg n). set (tx := if is_cl24 n then CL24_TAX else 0) in *.
  pose proof (rz_size_range n) as [RZ _]. change (is_primary n) with (bprim n).
  destruct (bprim n) eqn:HP.
  - (nelimp (prim_facts n HP) 5%nat; intros P1 P2 P3 P4 P5). unfold pslot in *. rewrite P5. pose proof (csize_pos (pclass n) ltac:(lia)).
    unfold usz in P2. Z.div_mod_to_equations. lia.
  - (nelimp (sec_facts n HP) 6%nat; intros S1 S2 S3 S4 S5 S6). rewrite S5. unfold SEC_ALLOC_COST, SEC_SLOT_TAX. unfold usz in S4.
    Z.div_mod_to_equations. lia.
Qed.

Lemma wr_at_weaken : forall m a n a' n', wr_at asegs m a n -> a <= a' -> a' + n' <= a + n -> wr_at asegs m a' n'.
Proof. intros m a n a' n' (H0 & H1 & HW) L1 L2. split; [lia|]. split; [lia|]. intros i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply HW. lia. Qed.

(* [comment removed for export] *)
Lemma rw_cells_same : forall m m' A cs, rw_cells asegs m A cs ->
  (forall a, A <= a < A + Z.of_nat (cells_size cs) -> m' (wa a) = m (wa a)) -> rw_cells asegs m' A cs.
Proof.
  intros m m' A cs [[Hwf (B0 & B1 & HB)] (W0 & W1 & HW)] EQ. pose proof (cells_bytes_length cs Hwf) as L.
  split; [split; [exact Hwf|]|].
  - split; [lia|]. split; [lia|]. intros i Hi. unfold mrd in *. rewrite (EQ (A + Z.of_nat i)) by (rewrite L in Hi; lia). apply HB. exact Hi.
  - split; [lia|]. split; [lia|]. intros i Hi. unfold wview in *. rewrite (EQ (A + i)) by lia. apply HW. exact Hi.
Qed.

Lemma errno_not_client : forall sp0 LB LF SP a, AERRNO <= a < AERRNO + 4 -> CEIL <= SP ->
  (forall A n, In (A, n) LB -> AIMG_HI <= A) -> (forall F k, In (F, k) LF -> AIMG_HI <= F) ->   (* [comment removed for export] *)
  ~ cj_client_addr sp0 LB LF SP a.
Proof.
  intros sp0 LB LF SP a Ha HSP HLB HLF HC. unfold AERRNO, ATP, CEIL, KHIGHMEM_BEG, AIMG_HI in *.
  destruct HC as [H|[H|[(A & n & Hb & Hr)|[(F & k & Hb & Hr)|H]]]].
  - lia.
  - unfold aclient_image, AERRNO, AGERROR0, AGERROR1, ADATA_LO, AIMG_HI, ATP in H. lia.
  - pose proof (HLB A n Hb). lia.
  - pose proof (HLF F k Hb). destruct Hr as [Hr|Hr]; [lia|]. pose proof (rt_SH_mono 0 F ltac:(lia)) as B. change (SH 0) with 0x7fff8000 in B. lia.
  - unfold astack_shadow in H. rewrite CEIL_eq, SH_CEIL in H. lia.
Qed.

Section MALLOC.
Hypothesis try_asan_init_proof : try_asan_init_spec.
Hypothesis get_malloc_ctx_size_proof : get_malloc_ctx_size_spec.
Hypothesis get_current_pc_proof : get_current_pc_spec.
Hypothesis set_errno_enomem_proof : set_errno_enomem_spec.
Hypothesis unwind_ok : unwind_spec.
Hypothesis allocate_ok : allocate_spec.

Theorem art_malloc_proof : malloc_lscps_stmt ARTd.
Proof.
  unfold malloc_lscps_stmt. intros until tl. intros HART SPB0 ST HCL LO ERR MI TP -> Hn COST [RA1 RA2] UWT ROOM.
  pose proof tpx_ok_of_RTWF as tpx_all.
  destruct (ARTd_RTS _ _ _ _ _ _ _ _ _ HART) as (st & (HR & WF & HM & HG & HFR & HSWR) & HO & HB & Esp0 & Elb & Elf & Etrs & HQ & B0 & BB & HSPB).
  pose proof (wb_sp0 st (wf_base_ok st WF)) as SP0. rewrite Esp0 in SP0. unfold AMALLOC_STACK in LO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. idtac.
  pose proof (bv_unsigned_in_range 64 ra) as RRA. unfold bv_modulus in RRA. cbn in RRA.
  pose proof (t_range st WF) as TR. olin TR. unfold KHIGHMEM_BEG, AIMG_HI in TR. olin_all.
  pose proof (alloc_deposit_le_cost n Hn) as DEP.
  pose proof (stk_wr_at m lo (bv_unsigned sp) (bv_unsigned sp + -2144) 2144 ST ltac:(lia) ltac:(lia)) as WR0.
  change AERRNO with 6148524 in ERR.
  apply lscps_assume. intros NWX _ _. pose proof HR as HR0.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  eapply lscps_step_evt.
  callx ltac:(eapply (malloc_i1_spec try_asan_init_proof get_malloc_ctx_size_proof get_current_pc_proof) with (lo := lo) (st := st) (n := n);
              [exact HR| exact WF| exact MI| reflexivity| exact Hn| exact ST| idtac; lia| unfold I1_DEPTH; lia]).
  cbv beta delta [wz] in *.
  match goal with H : stk _ _ lo _ |- _ => rename H into ST1 end.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -2128) _ |- _ => rename H into OBJ1 end.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -72) _ |- _ => rename H into BP1 end.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -56) _ |- _ => rename H into FR1 end.
  match goal with H : stk _ _ (bv_unsigned sp + -2112) _ |- _ => rename H into BUF1 end.
  match goal with H : mem_inv _ _ |- _ => rename H into MI1 end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  pose proof HR0 as HR1. rtrep_high HR1 WF MU WM.
  replace (bv_unsigned sp + -2128 + 16) with (bv_unsigned sp + -2112) in OBJ1 by lia.
  (* [comment removed for export] *)
  pose proof (rw_cells_take m1 _ [C8 (Z_to_bv 64 (bv_unsigned sp + -2112))] [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] OBJ1) as OBa.
  pose proof (rw_cells_drop m1 _ [C8 (Z_to_bv 64 (bv_unsigned sp + -2112)); C4 (Z_to_bv 64 0)] [C4 (Z_to_bv 64 0)] OBJ1) as OBc.
  cbn [cells_size Cells.csize Nat.add] in OBc. replace (bv_unsigned sp + -2128 + Z.of_nat 12) with (bv_unsigned sp + -2116) in OBc by lia.
  (* [comment removed for export] *)
  destruct (stk_split asegs m1 _ (bv_unsigned sp + -2112 + 8 * zlen (hook_tr PC0_MALLOC sp0 (bv_unsigned sp) (bv_unsigned ra) tl)) _ BUF1) as [_ BUF2].
  { pose proof (hook_tr_facts PC0_MALLOC sp0 (bv_unsigned sp) (bv_unsigned ra) tl m _ _ _ ltac:(unfold PC0_MALLOC; lia) ltac:(lia) UWT) as [L _].
    unfold TRACE_MAX_LEN in L. lia. }
  clear BUF1.
  (* [comment removed for export] *)
  assert (REC : bytes_at asegs m1 (bv_unsigned sp - 16) (le8 s0 ++ le8 ra)).
  { pose proof (rw_cells_drop m1 _ [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR1) as [[_ RB] _].
    cbn [cells_size Cells.csize Nat.add cells_bytes cbytes] in RB. rewrite app_nil_r in RB.
    replace (bv_unsigned sp + -56 + Z.of_nat 40) with (bv_unsigned sp - 16) in RB by lia. exact RB. }
  assert (UWT1 : uwt m1 (bv_unsigned sp) (ASTACK_TOP sp0) PC0_MALLOC (bv_unsigned sp) (bv_unsigned s0) 2 tl).
  { eapply uwt_mem; [exact UWT|]. intros a Ha Ha'. apply MU. rewrite wa_unsigned by lia. cbn. lia. }
  pose proof (hook_tr_facts PC0_MALLOC sp0 (bv_unsigned sp) (bv_unsigned ra) tl m _ _ _ ltac:(unfold PC0_MALLOC; lia) ltac:(lia) UWT) as [TRL TRR].
  pose proof TRL as TRL30. unfold TRACE_MAX_LEN in TRL30.
  assert (CP01 : cli_pres st (bv_unsigned sp) m m1).
  { eapply (cli_pres_tpz st WF); [| exact MU| exact WM|]; [unfold CEIL; lia|]. constructor; [| constructor]. cbn [fst snd]. right. unfold CEIL. lia. }
  assert (ES01 : errno_same m m1).
  { eapply errno_same_munch; [exact MU|]. constructor; [cbn; unfold AERRNO, ATP; lia| constructor]. }
  clear MU. pose proof (munch_refl [(lo, bv_unsigned sp); (st_t st + 3168, st_t st + 3168 + 1)] m1) as MU.
  pose proof (wmono_refl asegs m1) as WM1.
  callxp ltac:(eapply unwind_ok with (st := st) (S := bv_unsigned sp + -2128) (pc0 := PC0_MALLOC) (bp := bv_unsigned sp) (rac := ra) (s0c := s0) (tl := tl) (lo := lo);
    [ exact (RTS_intro _ _ _ _ HR1 WF HM ltac:(eapply GWIN_mem; [exact HG| exact HO| exact WM]) HFR HSWR)
    | reflexivity| reflexivity| symmetry; apply Z_to_bv_bv_unsigned| reflexivity| reflexivity| reflexivity| exact TP
    | replace (bv_unsigned sp + -2128 + 16) with (bv_unsigned sp + -2112) by lia; exact OBJ1
    | eapply wr_at_weaken; [exact WR0| lia| unfold BST_SIZE; lia]
    | rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; lia| lia| unfold PC0_MALLOC; lia
    | exact REC| exact RA1| exact RA2
    | intros _; rewrite Esp0; exact UWT1
    | left; unfold BST_SIZE; lia
    | rewrite unsigned_lit by lia; exact ST1| idtac; lia| rewrite unsigned_lit by lia; unfold AUNWIND_STACK; lia| exact MI1 ])
    ltac:(unfold unwind_post, T_UNWINDING; rewrite !Esp0, !unsigned_lit by lia).
  cbv beta delta [wz] in *.
  match goal with H : stk _ _ lo _ |- _ => rename H into ST2 end.
  match goal with H : RTREP st ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into HR2; rename mx into m2 end.
  match goal with H : rw_cells _ m2 (bv_unsigned sp + -2128 + 8) _ |- _ => rename H into SZ2 end.
  match goal with H : rw_cells _ m2 (bv_unsigned sp + -2128 + 16) _ |- _ => rename H into TRC2 end.
  match goal with H : mem_inv _ m2 |- _ => rename H into MI2 end.
  assert (CP12 : cli_pres st (bv_unsigned sp) m1 m2).
  { eapply (cli_pres_tpz st WF); [| exact MU| exact WM1|]; [unfold CEIL; lia|].
    unfold T_ACACHE, CEIL. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
  assert (ES02 : errno_same m m2).
  { eapply errno_same_trans; [exact ES01|].
    eapply errno_same_munch; [exact MU|]. unfold AERRNO, ATP. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
  clear MU WM1.
  (* [comment removed for export] *)
  assert (SOBJ : rw_cells asegs m2 (bv_unsigned sp + -2128)
            [C8 (Z_to_bv 64 (bv_unsigned sp + -2112)); C4 (Z_to_bv 64 (zlen (hook_tr PC0_MALLOC sp0 (bv_unsigned sp) (bv_unsigned ra) tl))); C4 (Z_to_bv 64 0)]).
  { apply (proj2 (rw_cells_app m2 _ [C8 _] [C4 _; C4 _])). split; [assumption|]. cbn [cells_size Cells.csize Nat.add].
    apply (proj2 (rw_cells_app m2 _ [C4 _] [C4 _])). split; [exact SZ2|]. cbn [cells_size Cells.csize Nat.add].
    replace (bv_unsigned sp + -2128 + Z.of_nat 8 + Z.of_nat 4) with (bv_unsigned sp + -2116) by lia. assumption. }
  clear SZ2.
  (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  pose proof (munch_refl [(lo, bv_unsigned sp)] m2) as MU. pose proof (wmono_refl asegs m2) as WM2.
  carve_frame 16%nat ST2.
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  match goal with H : rw_cells _ _ (bv_unsigned sp + -2144) [C8 sp; C8 _] |- _ => rename H into FRM end.
  match goal with H : stk _ _ lo (bv_unsigned sp + -2144) |- _ => rename H into ST3 end.
  match goal with H : mem_inv _ _ |- _ => rename H into MI3 end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
  pose proof HR2 as HR3. rtrep_high HR3 WF MU WM2.
  assert (CP23 : cli_pres st (bv_unsigned sp) m2 m3).
  { eapply (cli_pres_tpz st WF); [| exact MU| exact WM2|]; [unfold CEIL; lia|]. constructor; [cbn; unfold CEIL; lia| constructor]. }
  assert (ES03 : errno_same m m3).
  { eapply errno_same_trans; [exact ES02|]. eapply errno_same_munch; [exact MU|]. constructor; [cbn; unfold AERRNO, ATP; lia| constructor]. }
  assert (HG3 : GWIN st m3 mo g) by (eapply GWIN_mem; [exact HG| exact HO| exact WM]).
  assert (WR3 : wr_at asegs m3 (bv_unsigned sp + -2144) 2144) by (first [exact WR0| eapply wr_at_wmono; [exact WR0| exact WM2]]).
  clear MU WM2 WR0.
  apply evt_done. eapply lscps_bind.
  { pose proof allocate_ok as AL. unfold allocate_spec in AL.
    eapply AL with (lo := lo) (st := st) (n := n) (S := bv_unsigned sp + -2128) (tr := hook_tr PC0_MALLOC sp0 (bv_unsigned sp) (bv_unsigned ra) tl); try reflexivity.
    - exact (RTS_intro _ _ _ _ HR3 WF HM HG3 HFR HSWR).
    - exact tpx_all. - exact (proj1 HQ). - exact Hn. - exact TP.
    - replace (bv_unsigned sp + -2128 + 16) with (bv_unsigned sp + -2112) by lia. exact SOBJ.
    - replace (bv_unsigned sp + -2128 + 16) with (bv_unsigned sp + -2128 + 16) by lia. exact (proj1 TRC2).
    - exact TRL. - exact TRR.
    - rewrite unsigned_lit by lia. lia. - rewrite Esp0. unfold BST_SIZE. lia.
    - rewrite Etrs. exact ROOM.
    - lia.
    - rewrite unsigned_lit by lia. exact ST3. - idtac. lia. - rewrite unsigned_lit by lia. unfold AALLOCATE_STACK. lia.
    - rewrite unsigned_lit, Esp0 by lia. lia. - exact MI3. }
  cbv beta. intros ms4 mo4 g4 PO.
  (nelim PO 30%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m4 st4 -> MI4 r -> RTS4 ST4 CP4 ES4 GM4 Esp04 Elf4 AS4 RES).
  assert (HQ4 : QUIET st4).
  { (nelim AS4 5%nat; intros Q1 Q2 Q3 Q4 Q5). unfold QUIET in *. rewrite Q1, Q2, Q3, Q4, Q5. exact HQ. }
  rewrite unsigned_lit in ST4, CP4 by lia.
  replace (ret_pc (Z_to_bv 64 0x31ec4)) with (Z_to_bv 64 0x31ec4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  (nelim RTS4 6%nat; intros HR4 WF4 HM4 HG4 HF4 HSW4).
  (* [comment removed for export] *)
  apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ CP4) in FRM; [| left; cbn; rewrite Esp0; lia].
  apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ CP4) in FR1; [| left; cbn; rewrite Esp0; lia].
  apply (cj_pres_wr_at _ _ _ _ _ _ _ _ CP4) in WR3; [| left; rewrite Esp0; lia].
  assert (ERR4 : rw_cells asegs m4 6148524 [C4 errv]).
  { eapply rw_cells_same; [exact ERR|]. intros a Ha. cbn in Ha. apply ES4 || (replace a with (AERRNO + (a - 6148524)) by (unfold AERRNO, ATP; lia); apply ES4; lia). }
  assert (CP04 : cj_pres sp0 LB LF (bv_unsigned sp) m m4).
  { unfold cli_pres in *. rewrite Esp0, Elb, Elf in CP01, CP12, CP23, CP4.
    eapply cj_pres_trans; [exact CP01|]. eapply cj_pres_trans; [exact CP12|]. eapply cj_pres_trans; [exact CP23|].
    eapply cj_pres_weaken; [exact CP4| lia| auto| auto]. }
  clear CP01 CP12 CP23 CP4 ES01 ES02 ES03 ERR.
  apply lscps_assume. intros _ HO4 HB4.
  eapply lscps_step_evt. cbv beta delta [wz] in *.
  (* [comment removed for export] *)
  assert (HLB : forall A k, In (A, k) LB -> AIMG_HI <= A).
  { intros A k Hin. rewrite <- Elb in Hin. (nelimp (block_geom st WF A k ltac:(unfold all_blocks; apply in_or_app; left; exact Hin)) 5%nat; intros _ _ G1 G2 _). blia. }
  assert (HLF : forall Fr k, In (Fr, k) LF -> AIMG_HI <= Fr).
  { intros Fr k Hin. rewrite <- Elf in Hin. (nelimp (frame_range st WF Fr k Hin) 3%nat; intros _ X _). pose proof (fs_range st WF) as (F1 & _).
    change FS_FRAMES_OFF with 36864 in X. blia. }
  assert (B4 : 0 <= B - cost_malloc n) by lia.
  destruct RES as [(-> & Elb4 & Etrs4 & BO4)|(RNZ & ABR & NIN & NFR & Elb4 & TP4 & BO4 & JK)].
  - (* [comment removed for export] *)
    assert (ART4 : ARTd sp0 SPB LB LF TRS (B - cost_malloc n) m4 mo4 g4).
    { eapply (ARTd_intro st4); [exact HR4| exact WF4| exact HM4| exact HO4| exact HB4| exact HG4| exact HF4
        | rewrite Esp04; exact Esp0| rewrite Elb4; exact Elb| rewrite Elf4; exact Elf| rewrite Etrs4; exact Etrs| exact HQ4| exact B4| | exact HSPB| exact HSW4].
      unfold budget_ok in BO4. lia. }
    lstep; if_lia. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    pose proof (munch_refl [(lo, bv_unsigned sp); (6148524, 6148524 + 4)] m4) as MU.
    pose proof (wmono_refl asegs m4) as WM4.
    callxp ltac:(eapply set_errno_enomem_proof with (lo := lo) (errv := errv);
      [ exact MI4| exact TP| exact ERR4| rewrite unsigned_lit by lia; exact ST4| idtac; lia| rewrite unsigned_lit by lia; lia ])
      ltac:(unfold leaf_post, AERRNO, ATP; change (6148688 - 164) with 6148524; rewrite !unsigned_lit by lia).
    cbv beta delta [wz] in *.
    match goal with H : mem_inv _ _ |- _ => rename H into MI5 end.
    match goal with H : stk _ _ lo (bv_unsigned sp + -2144) |- _ => rename H into ST5 end.
    match goal with H : rw_cells _ _ 6148524 [C4 (Z_to_bv 64 ENOMEM)] |- _ => rename H into ERR5 end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    lstep. do 7 lstep. lstep. lstep. (* [comment removed for export] *)
    try rewrite unsigned_lit in * by lia. try rewrite Z_to_bv_bv_unsigned.
    apply evt_done. apply lscps_done. unfold amalloc_post.
    nexists 15%nat. exists m5, (Z_to_bv 64 ENOMEM), TRS. split; [reflexivity|]. split; [exact MI5|].
    split.
    { eapply stk_merge; [exact ST5| | lia]. replace (bv_unsigned sp) with (bv_unsigned sp + -2144 + 2144) at 2 by lia.
      apply stk_of_wr_high; [| unfold AIMG_HI; lia]. match goal with H : wr_at _ m5 _ _ |- _ => exact H end. }
    split; [exact ERR5|].
    split.
    { eapply cj_pres_trans; [exact CP04|]. eapply cj_pres_of_munch; [exact MU| exact WM4|].
      intros a Ha HC. cbn. split; [| split; [| exact I]].
      - intros Hin. apply (below_sp_not_client st WF (bv_unsigned sp) a); [unfold CEIL; lia| rewrite Esp0, Elb, Elf; exact HC].
      - intros Hin. apply (errno_not_client sp0 LB LF (bv_unsigned sp) a); [unfold AERRNO, ATP; lia| unfold CEIL; lia| exact HLB| exact HLF| exact HC]. }
    split; [exact GM4|]. split; [right; reflexivity|].
    left. split; [reflexivity|].
    eapply artd_frame; [exact ART4| exact MU| exact WM4|].
    constructor; [| constructor; [| constructor]]; unfold cj_write_ok; cbn [fst snd].
    + right. left. idtac. lia.
    + do 3 right. left. unfold AERRNO, ATP. lia.
  - (* [comment removed for export] *)
    assert (ART4 : ARTd sp0 SPB ((r, n) :: LB) LF (st_trs st4) (B - cost_malloc n) m4 mo4 g4).
    { eapply (ARTd_intro st4); [exact HR4| exact WF4| exact HM4| exact HO4| exact HB4| exact HG4| exact HF4
        | rewrite Esp04; exact Esp0| rewrite Elb4, Elb; reflexivity| rewrite Elf4; exact Elf| reflexivity| exact HQ4| exact B4| | exact HSPB| exact HSW4].
      unfold budget_ok in BO4. lia. }
    pose proof ABR as ABR'. unfold ablock_range, KHIGHMEM_BEG, AIMG_HI in ABR'. idtac.
    lstep; if_lia. (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    lstep. do 7 lstep. lstep. lstep. (* [comment removed for export] *)
    try rewrite unsigned_lit in * by lia. try rewrite Z_to_bv_bv_unsigned.
    apply evt_done. apply lscps_done. unfold amalloc_post.
    nexists 15%nat. exists m4, errv, (st_trs st4). split; [reflexivity|]. split; [exact MI4|].
    split.
    { eapply stk_merge; [exact ST4| | lia]. replace (bv_unsigned sp) with (bv_unsigned sp + -2144 + 2144) at 2 by lia.
      apply stk_of_wr_high; [exact WR3| unfold AIMG_HI; lia]. }
    split; [exact ERR4|].
    split; [exact CP04|].
    split; [exact GM4|]. split; [left; rewrite <- Etrs; exact TP4|].
    right. (nelim JK 3%nat; intros uj JK1 JK2). exists r, uj.
    split; [reflexivity|]. split; [exact ABR|]. split; [rewrite <- Elb; exact NIN|]. split; [rewrite <- Elf; exact NFR|].
    split; [exact ART4|]. split; [exact JK1| exact JK2].
Qed.
End MALLOC.


End CeilWrap.
End RTW_m_malloc.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_memset.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
Module RTW_m_at2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Exec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_a1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_lib2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_leaves2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_a6 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_a7 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_at1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_bandtac4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma alloc_t2_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : rtstate)
         (n r id b1 lo : Z) (j1 j0 bj uj : list byte) (sj0 sj1 sj2 sj3 : word) (vra v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : word),
  leafc st m -> RTWF st -> mem_inv asegs m -> fill_cells m -> tp = wz ATP ->
  s1 = wz (usz n) -> s2 = wz r -> s3 = wz (needed n) -> s4 = wz (r + rz_size n) -> s5 = wz (r + rz_size n + -16) ->
  0 <= n < 2^32 -> bprim n = true -> 0 <= id < 2^32 -> 0 <= b1 < 256 -> Z.land b1 115 = 17 ->
  KHIGHMEM_BEG <= r -> r + csize (pclass n) + 4096 <= alloc_ceiling -> r mod 32 = 0 ->
  (st_ctx st + 160 <= KLOWSHADOW_BEG \/ KHIGHMEM_BEG <= st_ctx st) -> st_ctx st + 160 <= alloc_ceiling -> (r + csize (pclass n) <= st_ctx st \/ st_ctx st + 160 <= r) ->
  (st_t st + 4096 <= r \/ r + csize (pclass n) <= st_t st) -> (st_ctx st + 160 <= st_t st \/ st_t st + 4096 <= st_ctx st) ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 32 <= bv_unsigned sp -> bv_unsigned sp + 128 <= 2^64 ->
  rw_cells asegs m (bv_unsigned sp) (alloc_frame j0 vra v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11) ->
  rw_cells asegs m (st_t st + 2800) [C8 sj0; C8 sj1; C8 sj2] ->
  rw_cells asegs m (st_t st + 2912 + 8 * pclass n) [C8 sj3] ->
  rw_cells asegs m (r + rz_size n + -16) [CB 1 j1; C1 (zb b1); C2 (wz 0); C4 (wz (usz n)); C8 (wz id)] ->
  (16 < rz_size n -> rw_cells asegs m r [CB 16 bj]) ->
  rw_cells asegs m (r + rz_size n) [CB (Z.to_nat (usz n)) uj] ->
  evt asegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (b1' : Z) (sj0' sj1' sj2' sj3' : word)
                               (ujr : list byte) (m' : word -> option byte),
      ms' = MS (mkR vra (wz (bv_unsigned sp + 128)) gp tp t0' t1' t2' v0 v1 (wz (r + rz_size n)) a1' a2' a3' a4' a5' a6' a7'
                    v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 t3' t4' t5' t6')
               F (ret_pc vra) fc None m' (seg_rom asegs)
      /\ munch [(r, r + 16); (r + rz_size n + -16, r + rz_size n); (r + rz_size n, r + rz_size n + usz n);
                (st_t st + 2800, st_t st + 2824); (st_t st + 2912 + 8 * pclass n, st_t st + 2912 + 8 * pclass n + 8);
                (bv_unsigned sp - 32, bv_unsigned sp)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp + 128)
      /\ rw_cells asegs m' (r + rz_size n + -16) [C1 (zb CHUNK_ALLOCATED); C1 (zb b1'); C2 (wz 0); C4 (wz (usz n)); C8 (wz id)]
      /\ Z.land b1' 127 = HDR_BYTE1_MALLOC /\ 0 <= b1' < 256
      /\ (16 < rz_size n -> rw_cells asegs m' r [C8 (wz KALLOCBEG_MAGIC); C8 (wz (r + rz_size n + -16))])
      /\ rw_cells asegs m' (st_t st + 2800) [C8 sj0'; C8 sj1'; C8 sj2']
      /\ rw_cells asegs m' (st_t st + 2912 + 8 * pclass n) [C8 sj3']
      /\ rw_cells asegs m' (r + rz_size n)
           [CB (Z.to_nat (Z.min (usz n) MALLOC_FILL_MAX)) (repeat (zb MALLOC_FILL_BYTE) (Z.to_nat (Z.min (usz n) MALLOC_FILL_MAX)));
            CB (Z.to_nat (usz n - Z.min (usz n) MALLOC_FILL_MAX)) ujr])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x32440) fc None m (seg_rom asegs)).
Proof.
  intros until v11. intros LC WF MI FC TP -> -> -> -> -> Hn HP Hid Hb1 Hb1' R1 R2 R3 X1 X2 X3 TC X4 ST HCL LO SPH FR TS1 TS2 HDR BH USR.
  (nelimp (prim_facts n HP) 5%nat; intros PCL URZ P32 PM32 ASZ). unfold pslot in *.
  pose proof (rz_size_range n) as [RZ RZ16]. pose proof (csize_pos (pclass n) ltac:(lia)) as CSP.
  assert (U1 : 1 <= usz n) by (unfold usz; lia).
  assert (NDp : needed n = needed0 n) by (unfold needed; unfold bprim in HP; rewrite HP; reflexivity).
  assert (NCS : needed n <= csize (pclass n)).
  { rewrite NDp. pose proof (needed0_range n Hn) as NR.
    assert (NP : needed0 n <= 65536) by (unfold bprim, is_primary, KMAXSIZE in HP; apply Z.leb_le in HP; exact HP).
    destruct (class_ok (needed0 n) ltac:(lia)) as [C1 _]. unfold pclass. exact C1. }
  assert (FL : 1 <= Z.min (usz n) MALLOC_FILL_MAX <= usz n /\ Z.min (usz n) MALLOC_FILL_MAX <= 4096) by (unfold usz, MALLOC_FILL_MAX in *; lia).
  set (fl := Z.min (usz n) MALLOC_FILL_MAX) in *.
  pose proof (t_range st WF) as TR.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold KHIGHMEM_BEG, AIMG_HI in *. idtac.
  pose proof (munch_refl [(r, r + 16); ((r + rz_size n) + -16, (r + rz_size n)); ((r + rz_size n), (r + rz_size n) + usz n); (st_t st + 2800, st_t st + 2824); ((st_t st + 2912 + 8 * pclass n), (st_t st + 2912 + 8 * pclass n) + 8);
                          (bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (munch_refl [((r + rz_size n), (r + rz_size n) + usz n); (st_t st + 2800, st_t st + 2824); ((st_t st + 2912 + 8 * pclass n), (st_t st + 2912 + 8 * pclass n) + 8); (bv_unsigned sp - 32, bv_unsigned sp)] m) as MU'.
  pose proof (wmono_refl asegs m) as WM.
  assert (HWL : Forall (fun iv : Z * Z => (snd iv <= AIMG_LO \/ AIMG_HI <= fst iv) /\ (snd iv <= st_ctx st + 152 \/ st_ctx st + 160 <= fst iv))
            [(r, r + 16); ((r + rz_size n) + -16, (r + rz_size n)); ((r + rz_size n), (r + rz_size n) + usz n); (st_t st + 2800, st_t st + 2824); ((st_t st + 2912 + 8 * pclass n), (st_t st + 2912 + 8 * pclass n) + 8); (bv_unsigned sp - 32, bv_unsigned sp)]).
  { olin_all. unfold AIMG_LO, AIMG_HI. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; (lia_on R1 X3 TC X4 P32 RZ CSP R3 URZ RZ16 U1 FL OLx PCL X2 HCL LO). }
  (* [comment removed for export] *)
  apply (rw_cells_split_CB asegs m (r + rz_size n) [] (Z.to_nat (usz n)) uj [] [Z.to_nat fl; Z.to_nat (usz n - fl)]) in USR; [| cbn [sum_nat]; lia].
  cbn [mk_CB_cells app] in USR.
  apply (proj1 (rw_cells_app m (r + rz_size n) [CB (Z.to_nat fl) (firstn (Z.to_nat fl) uj)] _)) in USR as [USR1 USR2].
  cbn [cells_size Cells.csize Nat.add] in USR2. rewrite Nat.add_0_r, Z2Nat.id in USR2 by lia.
  (* [comment removed for export] *)
  sepM. callxp ltac:(eapply alloc_a6p_spec with (lo := lo) (st := st) (n := n) (ub := r + rz_size n);
    [ exact LC| exact WF| exact MI| exact FC| exact TP| reflexivity| reflexivity| reflexivity| exact Hn| exact HP
    | exact ST| idtac; lia| lia| lia| exact FR| exact TS1| exact TS2 ]) ltac:(clear TS2 TS1).
  cbv beta delta [wz] in *. fold fl.
  match goal with H : mem_inv _ _ |- _ => rename H into MI1 end.
  (* [comment removed for export] *)
  sepM. callxp ltac:(eapply memset_spec; [rewrite !unsigned_lit by lia; exact USR1| exact MI1])
         ltac:(unfold memset_post; rewrite !unsigned_lit by (unfold MALLOC_FILL_BYTE; lia); clear USR1).
  cbv beta delta [wz] in *.
  match goal with H : mem_inv _ _ |- _ => rename H into MI2 end.
  match goal with H : rw_cells _ _ (r + rz_size n) [CB _ (repeat _ _)] |- _ => rename H into FILL end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
  assert (BH9 : 16 < rz_size n -> rw_cells asegs m9 r [CB 16 bj]).
  { intros HB. eapply (rw_cells_transport asegs _ m m9); [exact (BH HB)| exact MU'| exact WM| cbn; lia]. }
  clear MU' BH.
  assert (LC9 : leafc st m9) by (eapply leafc_out; [exact MU| exact WM| exact HWL| exact LC]).
  match goal with H : stk _ _ lo _ |- _ => rename H into ST9 end.
  match goal with H : rw_cells _ _ (bv_unsigned sp) (alloc_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _) |- _ => rename H into FR9 end.
  match goal with H : rw_cells _ _ ((r + rz_size n) + -16) _ |- _ => rename H into HDR9 end.
  (* [comment removed for export] *)
  sepM. callxp ltac:(eapply alloc_a7_spec with (st := st) (n := n) (r := r) (id := id) (b1 := b1) (lo := lo) (bj := bj);
    [ exact LC9| exact MI2| exact TP| reflexivity| reflexivity| reflexivity| reflexivity| exact Hn| exact Hid| exact Hb1| exact Hb1'
    | unfold KHIGHMEM_BEG, AIMG_HI; lia| idtac; lia| Z.div_mod_to_equations; lia| unfold KHIGHMEM_BEG, AIMG_HI; lia| idtac; lia| lia
    | exact ST9| idtac; lia| lia| lia| exact FR9| exact HDR9| exact BH9 ]) ltac:(clear HDR9).
  cbv beta delta [wz] in *.
  match goal with H : mem_inv _ _ |- _ => rename H into MI3 end.
  apply evt_done. nexists 14%nat.
  match goal with H : Z.land ?b 127 = HDR_BYTE1_MALLOC |- _ => exists b end.
  nexists 4%nat. eexists. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [eassumption|]. split; [eassumption|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  apply (proj2 (rw_cells_app _ (r + rz_size n) [CB _ _] [CB _ _])). split.
  - unfold MALLOC_FILL_BYTE, zb in *. change (190 mod 256) with 190 in FILL. exact FILL.
  - cbn [cells_size Cells.csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia. eassumption.
Qed.


End CeilWrap.
End RTW_m_at2.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_poison8.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_apz.
Module RTW_m_atail.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Exec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_a1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_lib2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_leaves2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_tpz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_apz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_a4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_a5 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_a6 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_a7 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_lib3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstateP.RTW_m_live OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_at1 RTW_m_at2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_bandtac4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma fill_prefix : forall (k fl : nat) (rest : list byte) (v : byte), (k <= fl)%nat ->
  Forall (fun b => b = v) (firstn k (repeat v fl ++ rest)).
Proof.
  induction k as [|k IH]; intros fl rest v Hk; [constructor|].
  destruct fl as [|fl]; [lia|]. cbn. constructor; [reflexivity|]. apply IH. lia.
Qed.

(* [comment removed for export] *)
Definition atail_W (st : rtstate) (c : Z) (r n sp : Z) : list (Z * Z) :=
  [(SH r + rz_size n / 8, SH r + rz_size n / 8 + (usz n + 7) / 8); (r + rz_size n + -8, r + rz_size n); (sp - 1024, sp);
   (r, r + 16); (r + rz_size n + -16, r + rz_size n); (r + rz_size n, r + rz_size n + usz n);
   (st_t st + 2800, st_t st + 2824); (st_t st + 2912 + 8 * c, st_t st + 2912 + 8 * c + 8); (sp - 32, sp)].

Section ATAIL.
Hypothesis poison_shadow_proof : poison_shadow_spec.

Lemma alloc_tail_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : rtstate)
         (c k n r id b1 lo : Z) (j1 j8 j0 : list byte) (vra v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : word),
  RTREP st m -> RTWF st -> tpx_ok st -> In (c, k) (st_apend st) -> c = pclass n -> bprim n = true -> r = cptr_addr st c k ->
  mem_inv asegs m -> tp = wz ATP ->
  a0 = wz id -> s0 = wz 1 -> s1 = wz (usz n) -> s2 = wz r -> s3 = wz (needed n) -> s4 = wz (r + rz_size n) ->
  s5 = wz (r + rz_size n + -16) -> s8 = wz 0 ->
  0 <= n < 2^32 -> 0 <= id < 2^32 -> 0 <= b1 < 256 -> Z.land b1 115 = 17 ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 1024 <= bv_unsigned sp -> bv_unsigned sp + 128 <= 2^64 ->
  rw_cells asegs m (bv_unsigned sp) (alloc_frame j0 vra v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11) ->
  rw_cells asegs m (r + rz_size n + -16) [CB 1 j1; C1 (zb b1); C2 (wz 0); C4 (wz (usz n)); CB 8 j8] ->
  evt asegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
      ms' = MS (mkR vra (wz (bv_unsigned sp + 128)) gp tp t0' t1' t2' v0 v1 (wz (r + rz_size n)) a1' a2' a3' a4' a5' a6' a7'
                    v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 t3' t4' t5' t6')
               F (ret_pc vra) fc None m' (seg_rom asegs)
      /\ munch (atail_W st c r n (bv_unsigned sp)) m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp + 128)
      /\ RTREP (st_liveP st c k (r + rz_size n) n) m'
      /\ cli_pres st (bv_unsigned sp + 128) m m'
      /\ (exists junk, rw_cells asegs m' (r + rz_size n) [CB (Z.to_nat n) junk]
                      /\ Forall (fun b => b = zb MALLOC_FILL_BYTE) (firstn (Z.to_nat (Z.min n MALLOC_FILL_MAX)) junk)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x322a0) fc None m (seg_rom asegs)).
Proof.
  intros until v11. intros HR WF HX HIN HC HP Er MI TP -> -> -> -> -> -> -> -> Hn Hid Hb1 Hb1' ST HCL LO SPH FR HDR.
  (nelimp (prim_facts n HP) 5%nat; intros PCL URZ P32 PM32 ASZ). unfold pslot in *. rewrite <- HC in *.
  pose proof (rz_size_range n) as [RZ RZ16]. pose proof (csize_pos c ltac:(lia)) as CSP.
  assert (U1 : 1 <= usz n) by (unfold usz; lia). assert (UN : n <= usz n) by (unfold usz; lia).
  (nelimp (geomA st WF c k HIN) 11%nat; intros G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11). rewrite <- Er in *.
  (nelimp (shA st WF c k HIN) 4%nat; intros S1 S2 S3 S4). rewrite <- Er in *. rewrite SH_CEIL in *.
  change (SH KHIGHMEM_BEG) with 0x2008fff7000 in S1.
  pose proof (t_vs_chunk st WF c k HIN) as TC. rewrite <- Er in TC.
  pose proof (t_range st WF) as TR.
  (nelim (wb_ctx_loose st (wf_base_ok st WF)) 5%nat; intros cb ck CL1 CL2 CL3).
  pose proof (loose_vs_chunk st WF c k HIN cb ck CL1) as CC. rewrite <- Er in CC.
  (nelimp (loose0_range st WF cb ck CL1) 4%nat; intros CR1 CR2 CR3 CR4).
  pose proof (wb_ctx_t st (wf_base_ok st WF)) as CT.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (RZ8 : rz_size n = 8 * (rz_size n / 8)) by (Z.div_mod_to_equations; lia).
  assert (SHNB : 1 <= (usz n + 7) / 8 /\ 8 * (rz_size n / 8) + 8 * ((usz n + 7) / 8) <= csize c + 7) by (Z.div_mod_to_equations; lia).
  assert (CS8 : csize c / 8 * 8 = csize c) by (Z.div_mod_to_equations; lia).
  olin_all.
  unfold KHIGHMEM_BEG, AIMG_HI, KREGIONSIZE, KFREEARRAY_OFF, CEIL in *. idtac.
  (* [comment removed for export] *)
  pose proof (rtrep_artcells st m HR) as HA.
  pose proof (artcells_icpt m HA) as IC. pose proof (artcells_poison m HA) as PC.
  pose proof (rtrep_fill_cells st m HR HA) as FC. pose proof (rtrep_memtoshadow_cells st m HR HA) as MC.
  pose proof (leafc_of_RTREP st m HR) as LC. clear HA.
  (* [comment removed for export] *)
  pose proof (rr_avail st m HR c k ltac:(unfold KNUMCLASSES; lia) ltac:(apply in_or_app; right; exact (apend_in_cptrs st c k HIN))) as SHA.
  rewrite <- Er in SHA.
  (* [comment removed for export] *)
  destruct (rr_regions st m HR c ltac:(unfold KNUMCLASSES; lia)) as (RV & _).
  destruct (vis_carve m _ _ r 16 RV ltac:(lia) ltac:(cbn; lia)) as [bj BH0].
  destruct (vis_carve m _ _ (r + rz_size n) (Z.to_nat (usz n)) RV ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as [uj USR].
  destruct (rr_thread st m HR) as (TV & _).
  (nelim (vis_c8x3 m _ _ (st_t st + 2800) TV ltac:(lia) ltac:(lia)) 4%nat; intros sj0 sj1 sj2 TS1).
  destruct (vis_c8 m _ _ (st_t st + 2912 + 8 * c) TV ltac:(lia) ltac:(lia)) as [sj3 TS2].
  assert (BH : 16 < rz_size n -> rw_cells asegs m r [CB 16 bj]) by (intros _; exact BH0). clear BH0 RV TV.
  pose proof (munch_refl (atail_W st c r n (bv_unsigned sp)) m) as MU. unfold atail_W in MU.
  pose proof (munch_refl [(SH r + (rz_size n / 8), SH r + (rz_size n / 8) + ((usz n + 7) / 8)); ((r + rz_size n) + -8, (r + rz_size n)); (bv_unsigned sp - 1024, bv_unsigned sp)] m) as MU1.
  pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  sepM. callxp ltac:(eapply (alloc_t1_spec poison_shadow_proof) with (st := st) (n := n) (r := r) (id := id) (b1 := b1) (lo := lo) (q := usz n / 8) (rem := usz n mod 8);
    [ exact MI| exact IC| exact PC| exact MC| exact LC
    | reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity
    | exact Hn| exact HP| exact Hid| Z.div_mod_to_equations; lia| Z.div_mod_to_equations; lia
    | unfold KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG; lia| rewrite <- HC; lia| lia
    | unfold KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG; lia| idtac; lia| rewrite <- HC; (lia_on CL2 CL3 CC)
    | exact ST| idtac; lia| lia| lia| exact HDR| rewrite <- HC; exact SHA ]) ltac:(clear SHA HDR; clear ST).
  cbv beta delta [wz] in *.
  match goal with H : mem_inv _ _ |- _ => rename H into MI1 end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m8 end.
  assert (BH8 : 16 < rz_size n -> rw_cells asegs m8 r [CB 16 bj]).
  { intros HB. eapply (rw_cells_transport asegs _ _ m8); [exact (BH HB)| exact MU1| exact WM| cbn; Z.div_mod_to_equations; lia]. }
  clear MU1 BH.
  assert (LC8 : leafc st m8).
  { eapply leafc_out; [exact MU| exact WM| | exact LC]. unfold AIMG_LO, AIMG_HI.
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; (lia_on P32 RZ U1 G1 G5 S1 S2 S3 CL2 CL3 OLx0 URZ CC CT HCL LO CR3 OLx PCL). }
  assert (FC8 : fill_cells m8).
  { eapply fill_cells_out; [exact MU| | exact FC]. unfold AIMG_LO, AIMG_HI. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
  match goal with H : stk _ _ lo _ |- _ => rename H into ST8 end.
  match goal with H : rw_cells _ _ (bv_unsigned sp) (alloc_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _) |- _ => rename H into FR8 end.
  match goal with H : rw_cells _ _ ((r + rz_size n) + -16) _ |- _ => rename H into HDR8 end.
  match goal with H : rw_cells _ _ (st_t st + 2800) _ |- _ => rename H into TS18 end.
  match goal with H : rw_cells _ _ (st_t st + 2912 + 8 * c) _ |- _ => rename H into TS28 end.
  match goal with H : rw_cells _ _ (r + rz_size n) [CB _ uj] |- _ => rename H into USR8 end.
  match goal with H : rw_cells _ _ (SH r) (zcells (sh_live n)) |- _ => rename H into SHL8 end.
  assert (SHL8' : True -> rw_cells asegs m8 (SH r) (zcells (sh_live n))) by (intros _; exact SHL8).
  pose proof (munch_refl [(r, r + 16); (r + rz_size n + -16, r + rz_size n); (r + rz_size n, r + rz_size n + usz n);
                (st_t st + 2800, st_t st + 2824); (st_t st + 2912 + 8 * pclass n, st_t st + 2912 + 8 * pclass n + 8);
                (bv_unsigned sp - 32, bv_unsigned sp)] m8) as MU2.
  pose proof (wmono_refl asegs m8) as WM2.
  (* [comment removed for export] *)
  sepM. callxp ltac:(eapply alloc_t2_spec with (st := st) (n := n) (r := r) (id := id) (b1 := b1) (lo := lo) (bj := bj) (uj := uj);
    [ exact LC8| exact WF| exact MI1| exact FC8| exact TP
    | reflexivity| reflexivity| reflexivity| reflexivity| reflexivity
    | exact Hn| exact HP| exact Hid| exact Hb1| exact Hb1'
    | unfold KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG; lia| rewrite <- HC; lia| lia
    | unfold KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG; lia| idtac; lia| rewrite <- HC; (lia_on CL2 CL3 CC)| rewrite <- HC; lia| lia
    | exact ST8| idtac; lia| lia| lia| exact FR8| exact TS18| rewrite <- HC; exact TS28| exact HDR8| exact BH8| exact USR8 ]) ltac:(clear SHL8 HDR8 TS28 TS18 USR8; clear ST8).
  cbv beta delta [wz] in *.
  match goal with H : mem_inv _ _ |- _ => rename H into MI2 end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m10 end.
  assert (SHLF : rw_cells asegs m10 (SH r) (zcells (sh_live n))).
  { eapply rw_cells_transport; [exact (SHL8' I)| exact MU2| exact WM2|]. rewrite zcells_size, sh_live_len by lia.
    unfold sh_tot. rewrite ASZ, <- HC. cbn. lia. }
  clear MU2 WM2 SHL8'.
  match goal with H : rw_cells _ m10 ((r + rz_size n) + -16) _ |- _ => rename H into HDRF end.
  match goal with H : 16 < rz_size n -> rw_cells _ m10 r _ |- _ => rename H into BHF end.
  match goal with H : rw_cells _ m10 (r + rz_size n) [CB _ _; CB _ _] |- _ => rename H into USRF end.
  match goal with H : Z.land ?b 127 = HDR_BYTE1_MALLOC |- _ => rename H into HB1F; rename b into b1f end.
  match goal with H : 0 <= b1f < 256 |- _ => rename H into HB1R end.
  (* [comment removed for export] *)
  assert (HWA : Forall (apzc_ok st c k (bv_unsigned sp + 128)) (atail_W st c r n (bv_unsigned sp))).
  { unfold atail_W, apzc_ok. rewrite <- Er. unfold T_STATS, T_UNWINDING, CEIL.
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; (lia_on HCL LO P32 RZ U1 G1 G2 G3 G4 G5 G10 S2 S3 S4 RZ8 SHNB CS8 OLx0 URZ G7 G8 PCL). }
  apply evt_done. nexists 15%nat. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI2|]. split; [assumption|].
  split.
  { rewrite Er. eapply (RTREP_liveP' st WF HX c k n HIN HP HC _ m m10); [exact (apzc_apz _ _ _ _ _ HWA)| exact MU| exact WM| exact HR|].
    rewrite <- Er. unfold R_block. split; [| split; [| split; [| split]]].
    - exists (zb b1f), (Z_to_bv 64 id). split.
      + unfold hdr_cells, b_chunk_beg, bm_state, hdr_state_live, size_hi, size_lo.
        replace (usz n / 2 ^ 32) with 0 by (symmetry; apply Z.div_small; lia). rewrite Z.mod_small by lia.
        replace (r + rz_size n - 16) with ((r + rz_size n) + -16) by lia. exact HDRF.
      + unfold hdr_b1_ok. unfold zb. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_small by lia. exact HB1F.
    - unfold R_bighdr, b_alloc_beg, b_chunk_beg. intros HB. replace (r + rz_size n - rz_size n) with r by lia.
      replace (r + rz_size n - 16) with ((r + rz_size n) + -16) by lia. exact (BHF HB).
    - unfold R_sechdr. rewrite HP. intros; discriminate.
    - unfold b_hi, b_lo, b_alloc_beg. rewrite HP, ASZ. replace (r + rz_size n - rz_size n) with r by lia.
      (* [comment removed for export] *)
      destruct (rr_regions st m HR c ltac:(unfold KNUMCLASSES; lia)) as (RV & _).
      destruct (stk_split asegs m _ r _ RV ltac:(lia)) as [_ RV1].
      destruct (stk_split asegs m r (r + csize c) _ RV1 ltac:(lia)) as [RV2 _]. clear RV RV1.
      pose proof (stk_of_rw_cells asegs m10 _ _ HDRF) as V2. cbn [cells_size Cells.csize Nat.add] in V2. change (Z.of_nat 16) with 16 in V2.
      pose proof (stk_of_rw_cells asegs m10 _ _ USRF) as V3. cbn [cells_size Cells.csize] in V3.
      match type of V3 with stk _ _ _ (?a + Z.of_nat ?kk) => replace (Z.of_nat kk) with (usz n) in V3 by (unfold MALLOC_FILL_MAX; lia) end.
      destruct (stk_split asegs m _ ((r + rz_size n) + usz n) _ RV2 ltac:(lia)) as [RVa RV4].
      eapply (stk_transport_disjoint asegs) in RV4; [| exact MU| exact WM| cbn; Z.div_mod_to_equations; (lia_on HCL LO PCL RZ U1 G1 G2 G3 G4 G5 G7 G8 G10 S2 S3 TC CL2 CL3 CC CT RZ8 SHNB CS8 H4 H5 H14 H15)].
      destruct (Z_lt_le_dec 16 (rz_size n)) as [BIG|SMALL].
      + pose proof (stk_of_rw_cells asegs m10 _ _ (BHF BIG)) as V1. cbn [cells_size Cells.csize Nat.add] in V1. change (Z.of_nat 16) with 16 in V1.
        destruct (stk_split asegs m _ (r + 16) _ RVa ltac:(lia)) as [_ RVb].
        destruct (stk_split asegs m _ ((r + rz_size n) + -16) _ RVb ltac:(Z.div_mod_to_equations; lia)) as [RVc _].
        eapply (stk_transport_disjoint asegs) in RVc; [| exact MU| exact WM| cbn; Z.div_mod_to_equations; (lia_on HCL LO PCL URZ U1 G1 G2 G3 G4 G5 G7 G8 G10 S2 S3 TC CL2 CL3 CC CT RZ8 SHNB CS8 H14 H15)].
        eapply stk_merge; [exact V1| | lia]. eapply stk_merge; [exact RVc| | Z.div_mod_to_equations; lia].
        eapply stk_merge; [exact V2| | lia]. replace ((r + rz_size n) + -16 + 16) with (r + rz_size n) by lia.
        eapply stk_merge; [exact V3| exact RV4| lia].
      + assert (E16 : rz_size n = 16) by lia. replace r with ((r + rz_size n) + -16) at 1 by lia.
        eapply stk_merge; [exact V2| | lia]. replace ((r + rz_size n) + -16 + 16) with (r + rz_size n) by lia.
        eapply stk_merge; [exact V3| exact RV4| lia].
    - unfold R_bshadow. rewrite HP. unfold b_lo, b_alloc_beg. rewrite HP. replace (r + rz_size n - rz_size n) with r by lia. assumption. }
  split.
  { eapply (cli_pres_apz st WF c k HIN); [unfold CEIL; lia| exact MU| exact WM| exact HWA]. }
  (* [comment removed for export] *)
  pose proof (rw_cells_merge asegs m10 (r + rz_size n) [] [CB _ _; CB _ _] [] ltac:(rewrite app_nil_r; exact USRF)) as UM.
  cbn [cells_size cells_bytes Cells.csize cbytes app Nat.add] in UM. rewrite app_nil_r, Nat.add_0_r in UM.
  replace (Z.to_nat (Z.min (usz n) MALLOC_FILL_MAX) + Z.to_nat (usz n - Z.min (usz n) MALLOC_FILL_MAX))%nat with (Z.to_nat (usz n)) in UM
    by (unfold MALLOC_FILL_MAX; lia).
  apply (rw_cells_split_CB asegs m10 (r + rz_size n) [] (Z.to_nat (usz n)) _ [] [Z.to_nat n; Z.to_nat (usz n - n)]) in UM; [| cbn; lia].
  cbn [mk_CB_cells app] in UM.
  lazymatch type of UM with rw_cells _ _ _ [CB _ ?l1; CB ?n2 ?l2] =>
    apply (proj1 (rw_cells_app m10 (r + rz_size n) [CB (Z.to_nat n) l1] [CB n2 l2])) in UM as [UM _] end.
  eexists. split; [exact UM|].
  rewrite firstn_firstn. rewrite Nat.min_l by (unfold MALLOC_FILL_MAX; lia).
  apply fill_prefix. unfold MALLOC_FILL_MAX. lia.
Qed.
End ATAIL.


End CeilWrap.
End RTW_m_atail.

(* [comment removed for export] *)
Module RTW_m_alloc.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Exec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_sec.RTW_secondary_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_depot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_a1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_lib2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_leaves2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_tpz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_apz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_specs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_a3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_lib3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstateP.RTW_m_live OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_at1 RTW_m_at2 RTW_m_atail OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_aspec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstateP.RT_trans OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_bandtac4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma wstatic_not_client : forall st SP a, RTWF st -> CEIL <= SP -> 0xa6c18 <= a < 0x5cc8d0 ->
  ~ cj_client_addr (st_sp0 st) (st_lb st) (st_lf st) SP a.
Proof.
  intros st SP a WF HSP Ha HC. unfold CEIL in *.
  destruct HC as [H|[H|[(A & n & Hb & Hr)|[(F & k & Hb & Hr)|H]]]].
  - lia.
  - unfold aclient_image, AERRNO, AGERROR0, AGERROR1, ADATA_LO, AIMG_HI, ATP in H.
    destruct H as [H|[H|(H1 & H2 & H3)]]; [lia| lia|]. apply H2. exists 0xa6c18, 0x5cc8d0. split; [right; left; reflexivity| lia].
  - assert (HB : In (A, n) (all_blocks st)) by (unfold all_blocks; apply in_or_app; left; exact Hb).
    pose proof (block_geom st WF A n HB) as (_ & _ & X0 & X & Y & _). unfold usz, KHIGHMEM_BEG, AIMG_HI in *. blia.
  - pose proof (frame_range st WF F k Hb) as (Hk & X & Y & AL). pose proof (fs_range st WF) as (F1 & F2 & _).
    change FS_FRAMES_OFF with 36864 in X. unfold KHIGHMEM_BEG, AIMG_HI, CEIL in *.
    assert (8 <= fsz k) by (destruct Hk as [-> | ->]; [change (fsz 1) with 128| change (fsz 2) with 256]; lia).
    destruct Hr as [Hr|Hr]; [blia|].
    pose proof (rt_SH_bounds F ltac:(blia)) as B. lia.
  - unfold astack_shadow in H. rewrite CEIL_eq, SH_CEIL in H. lia.
Qed.

(* [comment removed for export] *)
Lemma apend_vs_depot_fp : forall st c k a, RTWF st -> In (c, k) (st_apend st) ->
  cptr_addr st c k <= a < cptr_addr st c k + csize c -> ~ in_ivs (depot_fp st) a.
Proof.
  intros st c k a WF HIN Ha (lo & hi & Hin & Hr).
  pose proof (geomA st WF c k HIN) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
  unfold depot_fp, fp_depot_blocks in Hin. destruct Hin as [E|Hin].
  - injection E as E1 E2. subst lo hi. unfold A_STACKSTORE, A_DEPOT_MAP1, KHIGHMEM_BEG, AIMG_HI in *. lia.
  - destruct (prim_vs_tail st WF (lo, hi)) as [D|D].
    { apply in_or_app. right. apply in_or_app. right. exact Hin. }
    all: cbn [fst snd] in D; unfold KREGIONSIZE, KFREEARRAY_OFF in *; lia.
Qed.

Lemma gmono_trans : forall g1 g2 g3, gmono g1 g2 -> gmono g2 g3 -> gmono g1 g3.
Proof. unfold gmono. intros. auto. Qed.

Lemma trace_cells_size : forall tr, Z.of_nat (cells_size (trace_cells tr)) = 8 * zlen tr.
Proof.
  intros tr. unfold trace_cells. induction tr as [|x tr IH]; [reflexivity|].
  cbn [map cells_size Cells.csize]. rewrite zlen_cons, Nat2Z.inj_add, IH. lia.
Qed.
Lemma trace_cells_wf : forall tr, cells_wf (trace_cells tr).
Proof. intros tr. unfold trace_cells. induction tr as [|x tr IH]; [exact I|]. cbn [map cells_wf cell_wf]. split; [exact I| exact IH]. Qed.

Section ALLOC.
Hypothesis combined_alloc_proof : combined_alloc_spec.
Hypothesis depot_put_proof : depot_put_specS.   (* [comment removed for export] *)
Hypothesis poison_shadow_proof : poison_shadow_spec.
Hypothesis asan_inited_proof : asan_inited_spec.
Hypothesis rss_exceeded_proof : rss_exceeded_spec.
Hypothesis rzsize2log_proof : rzsize2log_spec.
Hypothesis get_current_thread_proof : get_current_thread_spec.
Hypothesis set_oom_proof : set_oom_spec.
Hypothesis may_return_null_proof : may_return_null_spec.
Hypothesis alloc_sec_case : alloc_sec_stmt.

Theorem allocate_proof : allocate_spec.
Proof.
  unfold allocate_spec. intros until lo. intros (HR & WF & HM & HG & HF & HSW) HTPX HAP0 Hn -> -> -> -> -> -> TP SOBJ STR TRL TRR SPS1 SPS2 ROOM HDEP ST HCL LO SPS MI.
  pose proof (wb_sp0 st (wf_base_ok st WF)) as SP0. unfold AALLOCATE_STACK in LO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. idtac.
  apply lscps_assume. intros NWX HO HB. pose proof HR as HR0.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (t_range st WF) as TR. unfold KHIGHMEM_BEG, AIMG_HI in TR. olin_all. unfold BST_SIZE in SPS2.
  (* [comment removed for export] *)
  eapply lscps_step_evt.
  callx ltac:(eapply (alloc_a1_spec asan_inited_proof rss_exceeded_proof rzsize2log_proof) with (lo := lo) (st := st) (n := n) (Sz := S);
              [exact HR| exact WF| exact MI| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| exact Hn
              | lia| exact ST| idtac; lia| unfold ALLOC_DEPTH; lia]).
  cbv beta delta [wz] in *.
  match goal with H : stk _ _ lo _ |- _ => rename H into STA end.
  match goal with H : rw_cells _ _ _ (alloc_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _) |- _ => rename H into FRA end.
  match goal with H : mem_inv _ _ |- _ => rename H into MIA end.
  pose proof HR0 as HRA. rtrep_high HRA WF MU WM.
  (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  callxp ltac:(eapply get_current_thread_proof with (lo := lo) (st := st);
              [exact HRA| exact WF| exact MIA| exact TP| rewrite unsigned_lit by lia; exact STA| idtac; lia| rewrite unsigned_lit by lia; lia]) ltac:(clear STA).
  clear HRA. cbv beta delta [wz] in *. match goal with H : ?x = Z_to_bv 64 (st_t st) |- _ => subst x end.
  match goal with H : stk _ _ lo _ |- _ => rename H into STA end.
  match goal with H : mem_inv _ _ |- _ => rename H into MIA end.
  rewrite unsigned_lit in STA by lia.
  lstep. lstep; if_lia. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  pose proof HR0 as HRB. rtrep_high HRB WF MU WM.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mB end.
  assert (CP0 : cli_pres st (bv_unsigned sp) m mB).
  { eapply (cli_pres_tpz st WF); [| exact MU| exact WM|]; [unfold CEIL; lia|]. constructor; [| constructor]. cbn [fst snd]. right. unfold CEIL. lia. }
  assert (HG0 : GWIN st mB mo g) by (eapply GWIN_mem; eauto).
  assert (STRB : cells_at asegs mB (S + 16) (trace_cells tr)).
  { eapply (ro_cells_transport asegs _ m mB); [exact STR| exact MU|]. cbn [disjoint_from]. rewrite trace_cells_size. lia. }
  assert (ES0 : errno_same m mB).
  { eapply errno_same_munch; [exact MU|]. constructor; [| constructor]. cbn [fst snd]. left. unfold AERRNO, ATP. lia. }
  apply evt_done.
  eapply lscps_bind.
  { pose proof combined_alloc_proof as CA. unfold combined_alloc_spec in CA. eapply CA with (lo := lo) (n := n); try reflexivity.
    - exact (RTS_intro _ _ _ _ HRB WF HM HG0 HF HSW).
    - exact HTPX. - exact HAP0. - exact Hn. - exact TP.
    - unfold alloc_deposit in HDEP. pose proof (fp_nonneg n ltac:(lia)). pose proof (rp_nonneg n). pose proof (cl24_tax_nonneg n). lia.
    - rewrite unsigned_lit by lia. exact STA. - idtac; lia. - rewrite unsigned_lit by lia. unfold ACALLOC_STACK, AREFILL_STACK. lia.
    - rewrite unsigned_lit by lia. lia. - exact MIA. }
  cbv beta. intros ms1 mo1 g1 PO.
  destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & st1 & -> & MI1 & r & -> & Hr & CR & RTS1 & ST1 & CP1 & ES1 & GM1 & BO1 & SECF).
  rewrite unsigned_lit in ST1, CP1 by lia.
  replace (ret_pc (Z_to_bv 64 0x32194)) with (Z_to_bv 64 0x32194) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ CP1) in FRA; [| left; cbn; lia].
  apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ CP1) in SOBJ; [| left; cbn; lia].
  assert (STR1 : cells_at asegs m1 (S + 16) (trace_cells tr)).
  { destruct STRB as [SWF SB]. split; [exact SWF|]. eapply cj_pres_bytes_at; [exact CP1| exact SB|]. left.
    rewrite cells_bytes_length by exact SWF. rewrite trace_cells_size. unfold TRACE_MAX_LEN in TRL. lia. }
  destruct RTS1 as (HR1 & WF1 & HM1 & HG1 & HF1 & HSW1).
  destruct CR as (SC & Eqp & Eqt & Eqc & Eqth & Eqg & Edep & Efs & Et & Esb & Epb & Epa & RES).
  destruct SC as (Esp0 & Elb & Elf & Etrs).
  assert (CP01 : cli_pres st (bv_unsigned sp) m m1).
  { unfold cli_pres in *. eapply cj_pres_trans; [exact CP0|]. eapply cj_pres_weaken; [exact CP1| lia| auto| auto]. }
  assert (ES01 : errno_same m m1) by (eapply errno_same_trans; [exact ES0| exact ES1]).
  clear STA MIA CP0 CP1 HG0 MU WM STR STRB ES0 ES1.
  apply lscps_assume. intros _ HO1 HB1.
  eapply lscps_step_evt. cbv beta delta [wz] in *.
  lstep. (* [comment removed for export] *)
  destruct (Z.eq_dec r 0) as [R0|RNZ].
  - (* [comment removed for export] *)
    subst r. unfold alloc_frame in FRA.
    lstep; if_lia. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    pose proof (munch_refl [(A_ALLOC_OOM, A_ALLOC_OOM + 1); (lo, bv_unsigned sp + -128)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    unfold A_ALLOC_OOM in MU.
    callxp ltac:(eapply set_oom_proof with (lo := lo) (st := st1);
                [exact HR1| exact WF1| exact MI1| rewrite unsigned_lit by lia; exact ST1| idtac; lia| rewrite unsigned_lit by lia; lia])
           ltac:(unfold A_ALLOC_OOM).
    cbv beta delta [wz] in *.
    match goal with H : RTREP st1 _ |- _ => rename H into HR2 end.
    match goal with H : stk _ _ lo _ |- _ => rename H into ST2 end.
    match goal with H : mem_inv _ _ |- _ => rename H into MI2 end.
    rewrite unsigned_lit in ST2 by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => pose proof (munch_refl [(lo, bv_unsigned sp + -128)] mx) as MU'; pose proof (wmono_refl asegs mx) as WM' end.
    lstep. (* [comment removed for export] *)
    callxp ltac:(eapply may_return_null_proof with (lo := lo) (st := st1);
                [exact HR2| exact MI2| intros; discriminate| rewrite unsigned_lit by lia; exact ST2| idtac; lia| rewrite unsigned_lit by lia; lia]) ltac:(clear ST2 ST1).
    cbv beta delta [wz] in *. match goal with H : ?x = Z_to_bv 64 1 |- _ => subst x end.
    match goal with H : stk _ _ lo _ |- _ => rename H into ST3 end.
    match goal with H : mem_inv _ _ |- _ => rename H into MI3 end.
    rewrite unsigned_lit in ST3 by lia.
    rtrep_high HR2 WF1 MU' WM'. clear MU' WM'.
    lstep; if_lia. (* [comment removed for export] *)
    lstep. lstep. (* [comment removed for export] *)
    lstep. do 13 lstep. lstep. lstep. (* [comment removed for export] *)
    try rewrite unsigned_lit in * by lia. try replace (bv_unsigned sp + -128 + 128) with (bv_unsigned sp) in * by lia. try rewrite Z_to_bv_bv_unsigned.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    release_frame FRA ST3 (bv_unsigned sp).
    apply evt_done. apply lscps_done.
    unfold alloc_post, rt_post_std. do 15 eexists. exists m2, st1. split; [reflexivity|]. split; [exact MI3|].
    exists 0. split; [reflexivity|].
    split; [exact (RTS_intro _ _ _ _ HR2 WF1 HM1 ltac:(eapply GWIN_mem; [exact HG1| exact HO1| exact WM]) HF1 HSW1)|].
    split; [exact ST3|].
    split.
    { unfold cli_pres in *. eapply cj_pres_trans; [exact CP01|]. rewrite <- Esp0, <- Elb, <- Elf.
      eapply cj_pres_of_munch; [exact MU| exact WM|]. intros a Ha HC. cbn. split; [| split; [| exact I]].
      - intros Hin. apply (wstatic_not_client st1 (bv_unsigned sp) a WF1 ltac:(unfold CEIL; lia)); [lia| exact HC].
      - intros Hin. apply (below_sp_not_client st1 WF1 (bv_unsigned sp) a); [unfold CEIL; lia| exact HC]. }
    split.
    { eapply errno_same_trans; [exact ES01|]. eapply errno_same_munch; [exact MU|].
      constructor; [| constructor; [| constructor]]; cbn [fst snd]; unfold AERRNO, ATP; lia. }
    split; [exact GM1|]. split; [exact Esp0|]. split; [exact Elf|].
    split.
    { destruct RES as [(_ & Eap & Esp & _)|[(HP' & k' & Er' & Eap' & _)|(HPs' & mb' & Er' & M1' & _)]].
      - split; [exact Eap| split; [exact Esp| split; [exact Eqp| split; [exact Eqt| exact Eqc]]]].
      - exfalso. pose proof (apend_geom st1 WF1 (pclass n) k' ltac:(rewrite Eap'; left; reflexivity)) as (G1 & _ & _ & _ & G5 & _).
        unfold cptr_addr, rbeg in Er', G1, G5. rewrite Esb in G1, G5. unfold KHIGHMEM_BEG, AIMG_HI in G5. olin_all. lia.
      - exfalso. unfold sec_alloc_beg, SEC_HDR, KHIGHMEM_BEG, AIMG_HI in *. blia. }
    left. split; [reflexivity|]. split; [exact Elb|]. split; [exact Etrs|]. cbn [Z.eqb] in BO1. exact BO1.
  - (* [comment removed for export] *)
    replace (r =? 0) with false in BO1 by (symmetry; apply Z.eqb_neq; exact RNZ).
    destruct RES as [(R0 & _)|[(HP & k & Er & Eap & Esp & Esec)|(HPs & mb & Er & M1 & M2 & M3 & Eap & Esp & Esec & Ereg & Ecch)]].
    { lia. }
    2:{ (* [comment removed for export] *)
      subst r. replace (if is_primary n then 1 else 0) with 0 by (unfold bprim in HPs; rewrite HPs; reflexivity).
      apply evt_done. pose proof alloc_sec_case as ASC. unfold alloc_sec_stmt in ASC.
      replace (bv_unsigned sp + -128) with (bv_unsigned sp - 128) in * by lia.
      eapply lscps_mono; [| intros msx mox gx; apply alloc_post_blk_post].
      eapply ASC with (st := st); try eassumption; try reflexivity.
      - exact (RTS_intro _ _ _ _ HR1 WF1 HM1 HG1 HF1 HSW1).
      - split; [exact Esp0| split; [exact Elb| split; [exact Elf| exact Etrs]]].
      - exact (proj1 (SECF HPs mb eq_refl M1)).
      - exact (proj1 (proj2 (SECF HPs mb eq_refl M1))).
      - exact (proj2 (proj2 (SECF HPs mb eq_refl M1))). }
    pose proof (prim_facts n HP) as (PCL & URZ & P32 & PM32 & ASZ). unfold pslot in *.
    replace (if is_primary n then 1 else 0) with 1 by (unfold bprim in HP; rewrite HP; reflexivity).
    set (c := pclass n) in *.
    assert (HIN1 : In (c, k) (st_apend st1)) by (rewrite Eap; left; reflexivity).
    assert (ECP : cptr_addr st1 c k = cptr_addr st c k) by (unfold cptr_addr, rbeg; rewrite Esb; reflexivity).
    rewrite <- ECP in Er.
    pose proof (geomA st1 WF1 c k HIN1) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11). rewrite <- Er in *.
    pose proof (t_vs_chunk st1 WF1 c k HIN1) as TC. rewrite <- Er, Et in TC.
    pose proof (rz_size_range n) as [RZ RZ16]. pose proof (csize_pos c ltac:(lia)) as CSP.
    assert (U1 : 1 <= usz n) by (unfold usz; lia).
    assert (NDp : needed n = needed0 n) by (unfold needed; unfold bprim in HP; rewrite HP; reflexivity).
    assert (NCS : needed n <= csize c).
    { rewrite NDp. pose proof (needed0_range n Hn) as NR.
      assert (NP : needed0 n <= 65536) by (unfold bprim, is_primary, KMAXSIZE in HP; apply Z.leb_le in HP; exact HP).
      destruct (class_ok (needed0 n) ltac:(lia)) as [C1 _]. subst c. unfold pclass. exact C1. }
    destruct (wb_ctx_loose st1 (wf_base_ok st1 WF1)) as (cb & ck & CL1 & CL2 & CL3).
    pose proof (loose_vs_chunk st1 WF1 c k HIN1 cb ck CL1) as CC. rewrite <- Er in CC.
    pose proof (loose0_range st1 WF1 cb ck CL1) as (CR1 & CR2 & CR3 & CR4). olin CR1.
    unfold KHIGHMEM_BEG, AIMG_HI, KREGIONSIZE, KFREEARRAY_OFF, CEIL in *. try idtac.
    (* [comment removed for export] *)
    destruct (rr_regions st1 m1 HR1 c ltac:(unfold KNUMCLASSES; lia)) as (RV & _).
    destruct (vis_carve m1 _ _ ((r + rz_size n) + -16) 16 RV ltac:(lia) ltac:(cbn; lia)) as [hj HDR0]. clear RV.
    destruct (rr_thread st1 m1 HR1) as (_ & (tj1 & tj2 & tj3 & tj4 & tj5 & TT) & _ & _ & TID & _).
    pose proof (rw_cells_merge asegs m1 (st_t st1) [C8 (wz (st_ctx st1))] _ [] ltac:(rewrite app_nil_r; exact TT)) as TT'.
    cbn [cells_size cells_bytes Cells.csize cbytes app Nat.add length] in TT'. clear TT. rewrite Et in TT'.
    pose proof (rw_cells_drop m1 S [C8 (Z_to_bv 64 (S + 16))] [C4 (Z_to_bv 64 (zlen tr)); C4 (Z_to_bv 64 0)] SOBJ) as SO2.
    cbn [cells_size Cells.csize Nat.add] in SO2. change (Z.of_nat 8) with 8 in SO2.
    apply c44_c8 in SO2; [| unfold TRACE_MAX_LEN in TRL; lia].
    pose proof (proj2 (rw_cells_app m1 S [C8 (Z_to_bv 64 (S + 16))] [C8 (Z_to_bv 64 (zlen tr))])
                  (conj (rw_cells_take m1 S [C8 (Z_to_bv 64 (S + 16))] [C4 (Z_to_bv 64 (zlen tr)); C4 (Z_to_bv 64 0)] SOBJ) SO2)) as SO.
    clear SO2.
    lstep; if_lia. (* [comment removed for export] *)
    pose proof (munch_refl [((r + rz_size n) + -16, (r + rz_size n))] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    callxp ltac:(eapply alloc_a3_spec with (n := n) (r := r) (t := st_t st) (ctx := st_ctx st1) (S := S) (ntr := zlen tr);
      [ exact MI1| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity
      | exact Hn| unfold KHIGHMEM_BEG, AIMG_HI; lia| idtac; lia| Z.div_mod_to_equations; lia
      | unfold KHIGHMEM_BEG, AIMG_HI; lia| idtac; lia| unfold KHIGHMEM_BEG, AIMG_HI; lia| idtac; lia| lia| lia
      | idtac; lia| lia| unfold TRACE_MAX_LEN in TRL; lia| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; lia
      | exact HDR0| rewrite unsigned_lit by lia; exact FRA| exact TT'| exact TID| exact SO ]) ltac:(clear TID HDR0).
    cbv beta delta [wz] in *.
    match goal with H : mem_inv _ _ |- _ => rename H into MI3 end.
    match goal with H : rw_cells _ _ ((r + rz_size n) + -16) _ |- _ => rename H into HDR3 end.
    match goal with H : Z.land ?b 115 = 17 |- _ => rename H into Hb1; rename b into b1 end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    assert (HW3 : Forall (apz_ok st1 c k) [((r + rz_size n) + -16, (r + rz_size n))]).
    { constructor; [| constructor]. unfold apz_ok. cbn [fst snd]. left. rewrite <- Er. lia. }
    pose proof (apz_all st1 WF1 (HTPX st1 WF1) c k HIN1 _ HW3 m1 m3 MU WM HR1
                  ltac:(constructor; [| constructor]; cbn [fst snd]; left; rewrite <- Er; lia)) as HR3.
    assert (CP13 : cli_pres st1 (bv_unsigned sp) m1 m3).
    { eapply (cli_pres_apz st1 WF1 c k HIN1); [unfold CEIL; lia| exact MU| exact WM|]. constructor; [| constructor]. unfold apzc_ok. cbn [fst snd]. left. rewrite <- Er. lia. }
    assert (STR3 : cells_at asegs m3 (S + 16) (trace_cells tr)).
    { eapply (ro_cells_transport asegs _ m1 m3); [exact STR1| exact MU|]. cbn [disjoint_from]. rewrite trace_cells_size. lia. }
    match goal with H : stk _ m3 lo _ |- _ => rename H into ST3 end.
    match goal with H : rw_cells _ m3 (bv_unsigned sp + -128) _ |- _ => rename H into FR3 end.
    assert (HG3 : GWIN st1 m3 mo1 g1) by (eapply GWIN_mem; [exact HG1| exact HO1| exact WM]).
    assert (ES3 : errno_same m m3).
    { eapply errno_same_trans; [exact ES01|]. eapply errno_same_munch; [exact MU|]. constructor; [| constructor]. cbn [fst snd]. unfold AERRNO, ATP. lia. }
    clear MU WM.
    lstep. (* [comment removed for export] *)
    apply evt_done.
    eapply lscps_bind.
    { pose proof depot_put_proof as DP. unfold depot_put_specS in DP. eapply DP with (lo := lo) (P := S + 16) (tr := tr) (st := st1); try reflexivity.
      - exact (RTS_intro _ _ _ _ HR3 WF1 HM1 HG3 HF1 HSW1).
      - exact TRL. - exact TRR.
      - exact STR3.
      - right. rewrite unsigned_lit by lia. lia.
      - idtac. lia.
      - unfold TRACE_MAX_LEN in TRL. lia.
      - exact TP.
      - rewrite Etrs. exact ROOM.
      - unfold budget_ok in BO1. unfold alloc_deposit in HDEP. pose proof (fp_nonneg n ltac:(lia)). pose proof (rp_nonneg n). pose proof (cl24_tax_nonneg n). lia.
      - rewrite unsigned_lit by lia. exact ST3. - idtac; lia. - rewrite unsigned_lit by lia. unfold ADEPOT_STACK. lia.
      - exact MI3. }
    cbv beta. intros ms2 mo2 g2 PO.
    destruct PO as (t0'' & t1'' & t2'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m4 & st2 & -> & MI4 & id & -> & Hid
                    & SBD & TP2 & RTS2 & ST4 & CP2 & RF2 & GM2 & BO2).
    rewrite unsigned_lit in ST4, CP2, RF2 by lia.
    replace (ret_pc (Z_to_bv 64 0x322a0)) with (Z_to_bv 64 0x322a0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    destruct RTS2 as (HR4 & WF2 & HM2 & HG2 & HF2 & HSW2).
    destruct SBD as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & D15 & D16 & D17 & D18 & D19 & D20 & D21 & D22 & D23 & D24 & D25 & D26).
    assert (HIN2 : In (c, k) (st_apend st2)) by (rewrite D22; exact HIN1).
    assert (ECP2 : cptr_addr st2 c k = r) by (rewrite Er; unfold cptr_addr, rbeg; rewrite D3; reflexivity).
    (* [comment removed for export] *)
    apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ CP2) in FR3; [| left; cbn; lia].
    destruct (rr_regions st2 m4 HR4 c ltac:(unfold KNUMCLASSES; lia)) as (RV2 & _).
    unfold rg, rbeg in RV2. rewrite D3, D4 in RV2. change (nthz (st_regions st1) c region0) with (rg st1 c) in RV2.
    change (region_beg (st_spacebeg st1) c) with (rbeg st1 c) in RV2.
    lazymatch type of HDR3 with rw_cells _ _ _ ?cs =>
      assert (HDR4 : rw_cells asegs m4 ((r + rz_size n) + -16) cs) end.
    { eapply (rw_cells_rt_frame _ _ _ _ _ _ _ _ _ RF2 HDR3 RV2); [lia| cbn; lia| lia|].
      intros a Ha. cbn in Ha. split; [lia|]. apply (apend_vs_depot_fp st2 c k a WF2 HIN2). rewrite ECP2. lia. }
    clear HDR3.
    assert (ES4 : errno_same m m4).
    { eapply errno_same_trans; [exact ES3|]. eapply errno_same_rt_frame; [exact RF2| unfold AERRNO, ATP; lia|].
      intros a Ha. apply (errno_notin_depot_fp st2 a WF2 Ha). }
    apply lscps_assume. intros _ HO2 HB2.
    eapply lscps_step_evt. cbv beta delta [wz] in *.
    pose proof (wmono_refl asegs m4) as WM5. pose proof (munch_refl (atail_W st2 c r n (bv_unsigned sp + -128)) m4) as MU5. unfold atail_W in MU5.
    callxp ltac:(eapply (alloc_tail_spec poison_shadow_proof) with (st := st2) (c := c) (k := k) (n := n) (r := r) (id := id) (b1 := b1) (lo := lo);
      [ exact HR4| exact WF2| exact (HTPX st2 WF2)| exact HIN2| reflexivity| exact HP| symmetry; exact ECP2| exact MI4| exact TP
      | reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity
      | exact Hn| exact Hid| lia| exact Hb1
      | rewrite unsigned_lit by lia; exact ST4| idtac; lia| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; lia
      | rewrite unsigned_lit by lia; exact FR3| exact HDR4 ])
      ltac:(unfold atail_W; rewrite !unsigned_lit by lia; clear HDR4 FR3 RV2 ST4).
    cbv beta delta [wz] in *.
    try rewrite unsigned_lit in * by lia. replace (bv_unsigned sp + -128 + 128) with (bv_unsigned sp) in * by lia. try rewrite Z_to_bv_bv_unsigned.
    match goal with H : mem_inv _ _ |- _ => rename H into MI5 end.
    match goal with H : RTREP (st_liveP st2 c k _ n) ?mx |- _ => rename H into HR5; rename mx into m5 end.
    match goal with H : cli_pres st2 _ m4 m5 |- _ => rename H into CP5 end.
    match goal with H : stk _ m5 lo _ |- _ => rename H into ST5 end.
    match goal with H : exists junk, _ |- _ => rename H into JK end.
    apply evt_done. apply lscps_done.
    unfold alloc_post, rt_post_std. do 15 eexists. exists m5, (st_liveP st2 c k (r + rz_size n) n). split; [reflexivity|]. split; [exact MI5|].
    exists (r + rz_size n). split; [reflexivity|].
    pose proof (st_liveP_same st2 c k (r + rz_size n) n) as (L1 & L2 & L3 & L4 & _).
    split.
    { apply RTS_intro.
      - exact HR5.
      - apply RTWF_liveP'; [exact WF2| exact HP| reflexivity| exact HIN2| rewrite ECP2; reflexivity| lia].
      - apply RTMODEL_liveP'. exact HM2.
      - apply GWIN_liveP'. eapply GWIN_mem; [exact HG2| exact HO2| exact WM5].
      - exact HF2.
      - apply SWIN_liveP'. exact HSW2. }
    split; [exact ST5|].
    split.
    { unfold cli_pres in *. rewrite D1, D15, D21 in CP5. rewrite Esp0, Elb, Elf in CP13, CP2, CP5.
      eapply cj_pres_trans; [exact CP01|]. eapply cj_pres_trans; [exact CP13|].
      eapply cj_pres_trans; [eapply cj_pres_weaken; [exact CP2| lia| auto| auto]|]. exact CP5. }
    split.
    { eapply errno_same_trans; [exact ES4|]. eapply errno_same_munch; [exact MU5|]. rewrite D16, Et.
      pose proof (rt_SH_mono 17594333495296 r ltac:(lia)) as SB. change (SH 17594333495296) with 0x2008fff7000 in SB.
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold AERRNO, ATP; lia. }
    split; [eapply gmono_trans; [exact GM1| exact GM2]|].
    split; [rewrite L1, D1; exact Esp0|]. split; [rewrite L3, D15; exact Elf|].
    split.
    { pose proof (st_liveP_same st2 c k (r + rz_size n) n) as (_ & _ & _ & _ & L5 & L6 & _ & L8 & L9 & L10 & _).
      split; [| split; [| split; [| split]]].
      - rewrite L5, D22, Eap. cbn [remove_first]. rewrite (proj2 (ck_eqb_eq _ _) eq_refl). reflexivity.
      - rewrite L6, D23. exact Esp.
      - rewrite L8, D24. exact Eqp.
      - rewrite L9, D25. exact Eqt.
      - rewrite L10, D26. exact Eqc. }
    right.
    split; [lia|].
    split.
    { unfold ablock_range, KHIGHMEM_BEG, AIMG_HI. idtac. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [lia|]. unfold usz in *. lia. }
    split.
    { intros Hin. apply in_map_iff in Hin as ([A' n'] & EA & Hin). cbn in EA. subst A'.
      apply (liveP_fresh st2 c k n WF2 HIN2 eq_refl HP (r + rz_size n) n'); [| rewrite ECP2; reflexivity].
      unfold all_blocks. apply in_or_app. left. rewrite D21, Elb. exact Hin. }
    split.
    { intros Fr kk Hin. rewrite <- Elf, <- D15 in Hin.
      pose proof (frame_range st2 WF2 Fr kk Hin) as (Hk & X & Y & AL). change FS_FRAMES_OFF with 36864 in X.
      pose proof (loose_vs_chunk st2 WF2 c k HIN2 _ _ (wb_fs_loose st2 (wf_base_ok st2 WF2))) as D. rewrite ECP2 in D.
      assert (8 <= fsz kk) by (destruct Hk as [-> | ->]; [change (fsz 1) with 128| change (fsz 2) with 256]; lia). unfold usz in URZ. (lia_on SP0 Hr RNZ URZ P32 G1 G5 RZ CSP U1 OLx0 X Y AL D). }
    split; [rewrite L2, D21, Elb; reflexivity|].
    split; [rewrite L4, <- Etrs; exact TP2|].
    split.
    { unfold budget_ok in *. rewrite (rt_prov_liveP' st2 c k (r + rz_size n) n HP). unfold alloc_deposit. rewrite (cl24_prim n HP). pose proof (rp_nonneg n).
      assert (0 <= (if pclass n =? 24 then CL24_TAX else 0)) by (unfold CL24_TAX; destruct (pclass n =? 24); lia). lia. }
    exact JK.
Qed.
End ALLOC.


End CeilWrap.
End RTW_m_alloc.

(* [comment removed for export] *)
Module RTW_m_allocN.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Exec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_sec.RTW_secondary_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_depot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_a1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_lib2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_leaves2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_tpz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_apz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_specs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_a3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_lib3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstateP.RTW_m_live OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_at1 RTW_m_at2 RTW_m_atail OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_aspec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstateP.RT_trans OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_bandtac4 RTW_m_alloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma alloc_post_blk_nz : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n tr lo m g ms mo' g',
  alloc_post_blk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n tr lo m g ms mo' g' ->
  alloc_post_nn ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n tr lo m g ms mo' g'.
Proof.
  intros until g'. intros H. split; [| intros _; exact H]. split; [apply alloc_post_blk_post; exact H|].
  unfold alloc_post_blk, rt_post_std in H.
  (nelim H 32%nat; intros t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' st' -> MI' r -> _ _ _ _ _ _ _ _ NZ ABR _).
  rewrite ms_a0_MS. apply wz_nz. pose proof alloc_ceiling_range as CR. unfold ablock_range, AIMG_HI in ABR. lia.
Qed.

Section ALLOCN.
Hypothesis combined_alloc_nn_proof : combined_alloc_nn_spec.
Hypothesis depot_put_proof : depot_put_specS.   (* [comment removed for export] *)
Hypothesis poison_shadow_proof : poison_shadow_spec.
Hypothesis asan_inited_proof : asan_inited_spec.
Hypothesis rss_exceeded_proof : rss_exceeded_spec.
Hypothesis rzsize2log_proof : rzsize2log_spec.
Hypothesis get_current_thread_proof : get_current_thread_spec.
Hypothesis set_oom_proof : set_oom_spec.
Hypothesis may_return_null_proof : may_return_null_spec.
Hypothesis alloc_sec_case : alloc_sec_stmt.

Theorem allocate_nn_proof : allocate_nn_spec.
Proof.
  unfold allocate_nn_spec. intros until lo. intros (HR & WF & HM & HG & HF & HSW) HTPX HAP0 Hn -> -> -> -> -> -> TP SOBJ STR TRL TRR SPS1 SPS2 ROOM HDEP HNN ST HCL LO SPS MI.
  pose proof (wb_sp0 st (wf_base_ok st WF)) as SP0. unfold AALLOCATE_STACK in LO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. idtac.
  apply lscps_assume. intros NWX HO HB. pose proof HR as HR0.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (t_range st WF) as TR. unfold KHIGHMEM_BEG, AIMG_HI in TR. olin_all. unfold BST_SIZE in SPS2.
  (* [comment removed for export] *)
  eapply lscps_step_evt.
  callx ltac:(eapply (alloc_a1_spec asan_inited_proof rss_exceeded_proof rzsize2log_proof) with (lo := lo) (st := st) (n := n) (Sz := S);
              [exact HR| exact WF| exact MI| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| exact Hn
              | lia| exact ST| idtac; lia| unfold ALLOC_DEPTH; lia]).
  cbv beta delta [wz] in *.
  match goal with H : stk _ _ lo _ |- _ => rename H into STA end.
  match goal with H : rw_cells _ _ _ (alloc_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _) |- _ => rename H into FRA end.
  match goal with H : mem_inv _ _ |- _ => rename H into MIA end.
  pose proof HR0 as HRA. rtrep_high HRA WF MU WM.
  (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  callx ltac:(eapply get_current_thread_proof with (lo := lo) (st := st);
              [exact HRA| exact WF| exact MIA| exact TP| rewrite unsigned_lit by lia; exact STA| idtac; lia| rewrite unsigned_lit by lia; lia]).
  clear HRA. cbv beta delta [wz] in *. match goal with H : ?x = Z_to_bv 64 (st_t st) |- _ => subst x end.
  match goal with H : stk _ _ lo _ |- _ => rename H into STA end.
  match goal with H : mem_inv _ _ |- _ => rename H into MIA end.
  rewrite unsigned_lit in STA by lia.
  lstep. lstep; if_lia. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  pose proof HR0 as HRB. rtrep_high HRB WF MU WM.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mB end.
  assert (CP0 : cli_pres st (bv_unsigned sp) m mB).
  { eapply (cli_pres_tpz st WF); [| exact MU| exact WM|]; [unfold CEIL; lia|]. constructor; [| constructor]. cbn [fst snd]. right. unfold CEIL. lia. }
  assert (HG0 : GWIN st mB mo g) by (eapply GWIN_mem; eauto).
  assert (STRB : cells_at asegs mB (S + 16) (trace_cells tr)).
  { eapply (ro_cells_transport asegs _ m mB); [exact STR| exact MU|]. cbn [disjoint_from]. rewrite trace_cells_size. lia. }
  assert (ES0 : errno_same m mB).
  { eapply errno_same_munch; [exact MU|]. constructor; [| constructor]. cbn [fst snd]. left. unfold AERRNO, ATP. lia. }
  apply evt_done.
  eapply lscps_bind.
  { pose proof combined_alloc_nn_proof as CA. unfold combined_alloc_nn_spec in CA. eapply CA with (lo := lo) (n := n); try reflexivity.
    - exact (RTS_intro _ _ _ _ HRB WF HM HG0 HF HSW).
    - exact HTPX. - exact HAP0. - exact Hn. - exact TP.
    - unfold alloc_deposit in HDEP. pose proof (fp_nonneg n ltac:(lia)). pose proof (rp_nonneg n). pose proof (cl24_tax_nonneg n). lia.
    - exact HNN.
    - rewrite unsigned_lit by lia. exact STA. - idtac; lia. - rewrite unsigned_lit by lia. unfold ACALLOC_STACK, AREFILL_STACK. lia.
    - rewrite unsigned_lit by lia. lia. - exact MIA. }
  cbv beta. intros ms1 mo1 g1 [PO NZ1].
  (nelim PO 30%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m1 st1 -> MI1 r -> Hr CR RTS1 ST1 CP1 ES1 GM1 BO1 SECF).
  rewrite unsigned_lit in ST1, CP1 by lia.
  replace (ret_pc (Z_to_bv 64 0x32194)) with (Z_to_bv 64 0x32194) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ CP1) in FRA; [| left; cbn; lia].
  apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ CP1) in SOBJ; [| left; cbn; lia].
  assert (STR1 : cells_at asegs m1 (S + 16) (trace_cells tr)).
  { destruct STRB as [SWF SB]. split; [exact SWF|]. eapply cj_pres_bytes_at; [exact CP1| exact SB|]. left.
    rewrite cells_bytes_length by exact SWF. rewrite trace_cells_size. unfold TRACE_MAX_LEN in TRL. lia. }
  (nelim RTS1 6%nat; intros HR1 WF1 HM1 HG1 HF1 HSW1).
  (nelim CR 13%nat; intros SC Eqp Eqt Eqc Eqth Eqg Edep Efs Et Esb Epb Epa RES).
  (nelim SC 4%nat; intros Esp0 Elb Elf Etrs).
  assert (CP01 : cli_pres st (bv_unsigned sp) m m1).
  { unfold cli_pres in *. eapply cj_pres_trans; [exact CP0|]. eapply cj_pres_weaken; [exact CP1| lia| auto| auto]. }
  assert (ES01 : errno_same m m1) by (eapply errno_same_trans; [exact ES0| exact ES1]).
  clear STA MIA CP0 CP1 HG0 MU WM STR STRB ES0 ES1.
  apply lscps_assume. intros _ HO1 HB1.
  eapply lscps_step_evt. cbv beta delta [wz] in *.
  lstep. (* [comment removed for export] *)
  destruct (Z.eq_dec r 0) as [R0|RNZ].
  - (* [comment removed for export] *)
    exfalso. apply NZ1. rewrite R0. reflexivity.
  - (* [comment removed for export] *)
    replace (r =? 0) with false in BO1 by (symmetry; apply Z.eqb_neq; exact RNZ).
    destruct RES as [(R0 & _)|[(HP & k & Er & Eap & Esp & Esec)|(HPs & mb & Er & M1 & M2 & M3 & Eap & Esp & Esec & Ereg & Ecch)]].
    { lia. }
    2:{ (* [comment removed for export] *)
      subst r. replace (if is_primary n then 1 else 0) with 0 by (unfold bprim in HPs; rewrite HPs; reflexivity).
      apply evt_done. pose proof alloc_sec_case as ASC. unfold alloc_sec_stmt in ASC.
      replace (bv_unsigned sp + -128) with (bv_unsigned sp - 128) in * by lia.
      eapply lscps_mono; [| intros msx mox gx PX; apply alloc_post_blk_nz; exact PX].
      eapply ASC with (st := st); try eassumption; try reflexivity.
      - exact (RTS_intro _ _ _ _ HR1 WF1 HM1 HG1 HF1 HSW1).
      - split; [exact Esp0| split; [exact Elb| split; [exact Elf| exact Etrs]]].
      - exact (proj1 (SECF HPs mb eq_refl M1)).
      - exact (proj1 (proj2 (SECF HPs mb eq_refl M1))).
      - exact (proj2 (proj2 (SECF HPs mb eq_refl M1))). }
    (nelimp (prim_facts n HP) 5%nat; intros PCL URZ P32 PM32 ASZ). unfold pslot in *.
    replace (if is_primary n then 1 else 0) with 1 by (unfold bprim in HP; rewrite HP; reflexivity).
    set (c := pclass n) in *.
    assert (HIN1 : In (c, k) (st_apend st1)) by (rewrite Eap; left; reflexivity).
    assert (ECP : cptr_addr st1 c k = cptr_addr st c k) by (unfold cptr_addr, rbeg; rewrite Esb; reflexivity).
    rewrite <- ECP in Er.
    (nelimp (geomA st1 WF1 c k HIN1) 11%nat; intros G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11). rewrite <- Er in *.
    pose proof (t_vs_chunk st1 WF1 c k HIN1) as TC. rewrite <- Er, Et in TC.
    pose proof (rz_size_range n) as [RZ RZ16]. pose proof (csize_pos c ltac:(lia)) as CSP.
    assert (U1 : 1 <= usz n) by (unfold usz; lia).
    assert (NDp : needed n = needed0 n) by (unfold needed; unfold bprim in HP; rewrite HP; reflexivity).
    assert (NCS : needed n <= csize c).
    { rewrite NDp. pose proof (needed0_range n Hn) as NR.
      assert (NP : needed0 n <= 65536) by (unfold bprim, is_primary, KMAXSIZE in HP; apply Z.leb_le in HP; exact HP).
      destruct (class_ok (needed0 n) ltac:(lia)) as [C1 _]. subst c. unfold pclass. exact C1. }
    (nelim (wb_ctx_loose st1 (wf_base_ok st1 WF1)) 5%nat; intros cb ck CL1 CL2 CL3).
    pose proof (loose_vs_chunk st1 WF1 c k HIN1 cb ck CL1) as CC. rewrite <- Er in CC.
    (nelimp (loose0_range st1 WF1 cb ck CL1) 4%nat; intros CR1 CR2 CR3 CR4). olin CR1.
    unfold KHIGHMEM_BEG, AIMG_HI, KREGIONSIZE, KFREEARRAY_OFF, CEIL in *. try idtac.
    (* [comment removed for export] *)
    destruct (rr_regions st1 m1 HR1 c ltac:(unfold KNUMCLASSES; lia)) as (RV & _).
    destruct (vis_carve m1 _ _ ((r + rz_size n) + -16) 16 RV ltac:(lia) ltac:(cbn; lia)) as [hj HDR0]. clear RV.
    destruct (rr_thread st1 m1 HR1) as (_ & (tj1 & tj2 & tj3 & tj4 & tj5 & TT) & _ & _ & TID & _).
    pose proof (rw_cells_merge asegs m1 (st_t st1) [C8 (wz (st_ctx st1))] _ [] ltac:(rewrite app_nil_r; exact TT)) as TT'.
    cbn [cells_size cells_bytes Cells.csize cbytes app Nat.add length] in TT'. clear TT. rewrite Et in TT'.
    pose proof (rw_cells_drop m1 S [C8 (Z_to_bv 64 (S + 16))] [C4 (Z_to_bv 64 (zlen tr)); C4 (Z_to_bv 64 0)] SOBJ) as SO2.
    cbn [cells_size Cells.csize Nat.add] in SO2. change (Z.of_nat 8) with 8 in SO2.
    apply c44_c8 in SO2; [| unfold TRACE_MAX_LEN in TRL; lia].
    pose proof (proj2 (rw_cells_app m1 S [C8 (Z_to_bv 64 (S + 16))] [C8 (Z_to_bv 64 (zlen tr))])
                  (conj (rw_cells_take m1 S [C8 (Z_to_bv 64 (S + 16))] [C4 (Z_to_bv 64 (zlen tr)); C4 (Z_to_bv 64 0)] SOBJ) SO2)) as SO.
    clear SO2.
    lstep; if_lia. (* [comment removed for export] *)
    pose proof (munch_refl [((r + rz_size n) + -16, (r + rz_size n))] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    callxp ltac:(eapply alloc_a3_spec with (n := n) (r := r) (t := st_t st) (ctx := st_ctx st1) (S := S) (ntr := zlen tr);
      [ exact MI1| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity
      | exact Hn| unfold KHIGHMEM_BEG, AIMG_HI; lia| idtac; lia| Z.div_mod_to_equations; lia
      | unfold KHIGHMEM_BEG, AIMG_HI; lia| idtac; lia| unfold KHIGHMEM_BEG, AIMG_HI; lia| idtac; lia| lia| lia
      | idtac; lia| lia| unfold TRACE_MAX_LEN in TRL; lia| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; lia
      | exact HDR0| rewrite unsigned_lit by lia; exact FRA| exact TT'| exact TID| exact SO ]) ltac:(clear TID HDR0).
    cbv beta delta [wz] in *.
    match goal with H : mem_inv _ _ |- _ => rename H into MI3 end.
    match goal with H : rw_cells _ _ ((r + rz_size n) + -16) _ |- _ => rename H into HDR3 end.
    match goal with H : Z.land ?b 115 = 17 |- _ => rename H into Hb1; rename b into b1 end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    assert (HW3 : Forall (apz_ok st1 c k) [((r + rz_size n) + -16, (r + rz_size n))]).
    { constructor; [| constructor]. unfold apz_ok. cbn [fst snd]. left. rewrite <- Er. lia. }
    pose proof (apz_all st1 WF1 (HTPX st1 WF1) c k HIN1 _ HW3 m1 m3 MU WM HR1
                  ltac:(constructor; [| constructor]; cbn [fst snd]; left; rewrite <- Er; lia)) as HR3.
    assert (CP13 : cli_pres st1 (bv_unsigned sp) m1 m3).
    { eapply (cli_pres_apz st1 WF1 c k HIN1); [unfold CEIL; lia| exact MU| exact WM|]. constructor; [| constructor]. unfold apzc_ok. cbn [fst snd]. left. rewrite <- Er. lia. }
    assert (STR3 : cells_at asegs m3 (S + 16) (trace_cells tr)).
    { eapply (ro_cells_transport asegs _ m1 m3); [exact STR1| exact MU|]. cbn [disjoint_from]. rewrite trace_cells_size. lia. }
    match goal with H : stk _ m3 lo _ |- _ => rename H into ST3 end.
    match goal with H : rw_cells _ m3 (bv_unsigned sp + -128) _ |- _ => rename H into FR3 end.
    assert (HG3 : GWIN st1 m3 mo1 g1) by (eapply GWIN_mem; [exact HG1| exact HO1| exact WM]).
    assert (ES3 : errno_same m m3).
    { eapply errno_same_trans; [exact ES01|]. eapply errno_same_munch; [exact MU|]. constructor; [| constructor]. cbn [fst snd]. unfold AERRNO, ATP. lia. }
    clear MU WM.
    lstep. (* [comment removed for export] *)
    apply evt_done.
    eapply lscps_bind.
    { pose proof depot_put_proof as DP. unfold depot_put_specS in DP. eapply DP with (lo := lo) (P := S + 16) (tr := tr) (st := st1); try reflexivity.
      - exact (RTS_intro _ _ _ _ HR3 WF1 HM1 HG3 HF1 HSW1).
      - exact TRL. - exact TRR.
      - exact STR3.
      - right. rewrite unsigned_lit by lia. lia.
      - idtac. lia.
      - unfold TRACE_MAX_LEN in TRL. lia.
      - exact TP.
      - rewrite Etrs. exact ROOM.
      - unfold budget_ok in BO1. unfold alloc_deposit in HDEP. pose proof (fp_nonneg n ltac:(lia)). pose proof (rp_nonneg n). pose proof (cl24_tax_nonneg n). lia.
      - rewrite unsigned_lit by lia. exact ST3. - idtac; lia. - rewrite unsigned_lit by lia. unfold ADEPOT_STACK. lia.
      - exact MI3. }
    cbv beta. intros ms2 mo2 g2 PO.
    (nelim PO 30%nat; intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' m4 st2 -> MI4 id -> Hid SBD TP2 RTS2 ST4 CP2 RF2 GM2 BO2)
.
    rewrite unsigned_lit in ST4, CP2, RF2 by lia.
    replace (ret_pc (Z_to_bv 64 0x322a0)) with (Z_to_bv 64 0x322a0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (nelim RTS2 6%nat; intros HR4 WF2 HM2 HG2 HF2 HSW2).
    destruct SBD as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & D15 & D16 & D17 & D18 & D19 & D20 & D21 & D22 & D23 & D24 & D25 & D26). (* [comment removed for export] *)
    assert (HIN2 : In (c, k) (st_apend st2)) by (rewrite D22; exact HIN1).
    assert (ECP2 : cptr_addr st2 c k = r) by (rewrite Er; unfold cptr_addr, rbeg; rewrite D3; reflexivity).
    (* [comment removed for export] *)
    apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ CP2) in FR3; [| left; cbn; lia].
    destruct (rr_regions st2 m4 HR4 c ltac:(unfold KNUMCLASSES; lia)) as (RV2 & _).
    unfold rg, rbeg in RV2. rewrite D3, D4 in RV2. change (nthz (st_regions st1) c region0) with (rg st1 c) in RV2.
    change (region_beg (st_spacebeg st1) c) with (rbeg st1 c) in RV2.
    lazymatch type of HDR3 with rw_cells _ _ _ ?cs =>
      assert (HDR4 : rw_cells asegs m4 ((r + rz_size n) + -16) cs) end.
    { eapply (rw_cells_rt_frame _ _ _ _ _ _ _ _ _ RF2 HDR3 RV2); [lia| cbn; lia| lia|].
      intros a Ha. cbn in Ha. split; [lia|]. apply (apend_vs_depot_fp st2 c k a WF2 HIN2). rewrite ECP2. lia. }
    clear HDR3.
    assert (ES4 : errno_same m m4).
    { eapply errno_same_trans; [exact ES3|]. eapply errno_same_rt_frame; [exact RF2| unfold AERRNO, ATP; lia|].
      intros a Ha. apply (errno_notin_depot_fp st2 a WF2 Ha). }
    apply lscps_assume. intros _ HO2 HB2.
    eapply lscps_step_evt. cbv beta delta [wz] in *.
    pose proof (wmono_refl asegs m4) as WM5. pose proof (munch_refl (atail_W st2 c r n (bv_unsigned sp + -128)) m4) as MU5. unfold atail_W in MU5.
    callxp ltac:(eapply (alloc_tail_spec poison_shadow_proof) with (st := st2) (c := c) (k := k) (n := n) (r := r) (id := id) (b1 := b1) (lo := lo);
      [ exact HR4| exact WF2| exact (HTPX st2 WF2)| exact HIN2| reflexivity| exact HP| symmetry; exact ECP2| exact MI4| exact TP
      | reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity
      | exact Hn| exact Hid| lia| exact Hb1
      | rewrite unsigned_lit by lia; exact ST4| idtac; lia| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; lia
      | rewrite unsigned_lit by lia; exact FR3| exact HDR4 ])
      ltac:(unfold atail_W; rewrite !unsigned_lit by lia; clear HDR4 FR3 RV2 ST4).
    cbv beta delta [wz] in *.
    try rewrite unsigned_lit in * by lia. replace (bv_unsigned sp + -128 + 128) with (bv_unsigned sp) in * by lia. try rewrite Z_to_bv_bv_unsigned.
    match goal with H : mem_inv _ _ |- _ => rename H into MI5 end.
    match goal with H : RTREP (st_liveP st2 c k _ n) ?mx |- _ => rename H into HR5; rename mx into m5 end.
    match goal with H : cli_pres st2 _ m4 m5 |- _ => rename H into CP5 end.
    match goal with H : stk _ m5 lo _ |- _ => rename H into ST5 end.
    match goal with H : exists junk, _ |- _ => rename H into JK end.
    apply evt_done. apply lscps_done. split; [split; [|] | intros HFx; rewrite HP in HFx; discriminate]. 2:{ rewrite ms_a0_MS; apply wz_nz; pose proof alloc_ceiling_range as ACR; clear - G1 G2 G3 G4 G5 G7 G8 G10 RZ ACR; lia. }
    unfold alloc_post, rt_post_std. nexists 15%nat. exists m5, (st_liveP st2 c k (r + rz_size n) n). split; [reflexivity|]. split; [exact MI5|].
    exists (r + rz_size n). split; [reflexivity|].
    (nelimp (st_liveP_same st2 c k (r + rz_size n) n) 5%nat; intros L1 L2 L3 L4 _).
    split.
    { apply RTS_intro.
      - exact HR5.
      - apply RTWF_liveP'; [exact WF2| exact HP| reflexivity| exact HIN2| rewrite ECP2; reflexivity| lia].
      - apply RTMODEL_liveP'. exact HM2.
      - apply GWIN_liveP'. eapply GWIN_mem; [exact HG2| exact HO2| exact WM5].
      - exact HF2.
      - apply SWIN_liveP'. exact HSW2. }
    split; [exact ST5|].
    split.
    { unfold cli_pres in *. rewrite D1, D15, D21 in CP5. rewrite Esp0, Elb, Elf in CP13, CP2, CP5.
      eapply cj_pres_trans; [exact CP01|]. eapply cj_pres_trans; [exact CP13|].
      eapply cj_pres_trans; [eapply cj_pres_weaken; [exact CP2| lia| auto| auto]|]. exact CP5. }
    split.
    { eapply errno_same_trans; [exact ES4|]. eapply errno_same_munch; [exact MU5|]. rewrite D16, Et.
      pose proof (rt_SH_mono 17594333495296 r ltac:(lia)) as SB. change (SH 17594333495296) with 0x2008fff7000 in SB.
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold AERRNO, ATP; (lia_on SP0 Hr P32 RZ U1 OLx0 SB G1 G5 HCL LO OLx Et D16 PCL). }
    split; [eapply gmono_trans; [exact GM1| exact GM2]|].
    split; [rewrite L1, D1; exact Esp0|]. split; [rewrite L3, D15; exact Elf|].
    split.
    { (nelimp (st_liveP_same st2 c k (r + rz_size n) n) 11%nat; intros _ _ _ _ L5 L6 _ L8 L9 L10 _).
      split; [| split; [| split; [| split]]].
      - rewrite L5, D22, Eap. cbn [remove_first]. rewrite (proj2 (ck_eqb_eq _ _) eq_refl). reflexivity.
      - rewrite L6, D23. exact Esp.
      - rewrite L8, D24. exact Eqp.
      - rewrite L9, D25. exact Eqt.
      - rewrite L10, D26. exact Eqc. }
    right.
    split; [lia|].
    split.
    { unfold ablock_range, KHIGHMEM_BEG, AIMG_HI. idtac. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [lia|]. unfold usz in *. lia. }
    split.
    { intros Hin. apply in_map_iff in Hin as ([A' n'] & EA & Hin). cbn in EA. subst A'.
      apply (liveP_fresh st2 c k n WF2 HIN2 eq_refl HP (r + rz_size n) n'); [| rewrite ECP2; reflexivity].
      unfold all_blocks. apply in_or_app. left. rewrite D21, Elb. exact Hin. }
    split.
    { intros Fr kk Hin. rewrite <- Elf, <- D15 in Hin.
      (nelimp (frame_range st2 WF2 Fr kk Hin) 4%nat; intros Hk X Y AL). change FS_FRAMES_OFF with 36864 in X.
      pose proof (loose_vs_chunk st2 WF2 c k HIN2 _ _ (wb_fs_loose st2 (wf_base_ok st2 WF2))) as D. rewrite ECP2 in D.
      assert (8 <= fsz kk) by (destruct Hk as [-> | ->]; [change (fsz 1) with 128| change (fsz 2) with 256]; lia). unfold usz in URZ. (lia_on SP0 Hr RNZ URZ P32 G1 G5 RZ CSP U1 OLx0 X Y AL D). }
    split; [rewrite L2, D21, Elb; reflexivity|].
    split; [rewrite L4, <- Etrs; exact TP2|].
    split.
    { unfold budget_ok in *. rewrite (rt_prov_liveP' st2 c k (r + rz_size n) n HP). unfold alloc_deposit. rewrite (cl24_prim n HP). pose proof (rp_nonneg n).
      assert (0 <= (if pclass n =? 24 then CL24_TAX else 0)) by (unfold CL24_TAX; destruct (pclass n =? 24); lia). lia. }
    exact JK.
Qed.
End ALLOCN.

End CeilWrap.
End RTW_m_allocN.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_quarantine_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_quarantine_iface2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_lib4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_fz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_q1.
Module RTW_m_dcore.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Exec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_depot_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_quarantine_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_quarantine_iface2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_a1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_lib2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_lib3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_lib4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_tpz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_fz.RTW_m_lbz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_leaves2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_specs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_d1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_q1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_fz RTW_m_alloc RTW_m_malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstateP.RTW_m_live OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstateP.RT_trans OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_bandtac4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma leafc_freeP' : forall st A n m, leafc st m -> leafc (st_freeP st A n) m.
Proof. intros st A n m H. destruct st. exact H. Qed.

Definition ADEALLOC_STACK : Z := 2864.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition dealloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : rtstate) (tr : list Z) (A n lo : Z) (m : word -> option byte) (g : lghost)
    : machine_state -> Model -> lghost -> Prop :=
  fun ms' mo' g' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte) (st' : rtstate),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ errno_same m m'
    /\ cli_pres st' (bv_unsigned sp) m m'
    /\ gmono g g' /\ trs_put tr (st_trs st) (st_trs st')
    /\ RTS st' m' mo' g' /\ LOK asegs mo' /\ BINV mo' g'
    /\ st_sp0 st' = st_sp0 st /\ st_lb st' = remove_first ck_eqb (A, n) (st_lb st) /\ st_lf st' = st_lf st
    /\ st_apend st' = st_apend st /\ st_spend st' = st_spend st /\ st_qpend st' = st_qpend st
    /\ st_qtmp st' = [] /\ st_qcur st' = []
    /\ budget_ok st g st' g' cost_free.

Definition dealloc_core_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (st : rtstate) (A n S : Z) (tr : list Z) (lo : Z),
  RTS st m mo g -> In (A, n) (st_lb st) -> st_qtmp st = [] -> st_qcur st = [] -> st_qpend st = [] -> st_apend st = [] ->
  a0 = wz A_ALLOC -> a1 = wz A -> a2 = wz 0 -> a3 = wz 0 -> a4 = wz S -> a5 = wz 1 -> tp = wz ATP ->
  (* [comment removed for export] *)
  rw_cells asegs m S [C8 (wz (S + 16)); C8 (wz (zlen tr))] -> cells_at asegs m (S + 16) (trace_cells tr) ->
  1 <= zlen tr <= TRACE_MAX_LEN -> Forall (fun pc => 0 <= pc < 2^64) tr -> trs_room tr (st_trs st) ->
  bv_unsigned sp <= S -> S + BST_SIZE <= 2^64 -> bv_unsigned sp <= st_sp0 st ->
  rt_prov st + cost_free <= g_res g ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + ADEALLOC_STACK <= bv_unsigned sp ->
  mem_inv asegs m ->
  LSCPS asegs (dealloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st tr A n lo m g)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz ADEALLOCATE) fc None m (seg_rom asegs)) mo g.

(* [comment removed for export] *)
Lemma band_notin_depot_fp : forall st a, RTWF st -> KLOWSHADOW_BEG <= a < KHIGHMEM_BEG -> ~ in_ivs (depot_fp st) a.
Proof.
  intros st a WF Ha nelH_; (nelim nelH_ 4%nat; intros lo hi Hin Hr). unfold depot_fp, fp_depot_blocks, A_STACKSTORE, A_DEPOT_MAP1 in *.
  destruct Hin as [E|Hin]; [injection E as E1 E2; subst lo hi; unfold KLOWSHADOW_BEG in Ha; lia|].
  pose proof (wb_ranges st (wf_base_ok st WF) (lo, hi)) as R.
  specialize (R ltac:(rewrite rt_ranges_tail; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hin)).
  cbn [fst snd] in R. destruct R as ([R1 _] & _). unfold sclr in R1. lia.
Qed.

Section DCORE.
Hypothesis depot_put_proof : depot_put_specS.   (* [comment removed for export] *)
Hypothesis quarantine_put_proof : quarantine_put_spec2.   (* [comment removed for export] *)

Theorem dealloc_core_proof : dealloc_core_stmt.
Proof.
  unfold dealloc_core_stmt. intros until lo. intros (HR & WF & HM & HG & HFR & HSWR) HIN HQT HQC HQP HAP -> -> -> -> -> -> TP SOBJ STR TRL TRR ROOM HS1 HS2 SPB0 COST ST HCL LO MI.
  pose proof (wb_sp0 st (wf_base_ok st WF)) as SP0. unfold ADEALLOC_STACK in LO. unfold BST_SIZE in HS2. unfold cost_free in COST.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. idtac.
  pose proof (t_range st WF) as TR. olin TR. unfold KHIGHMEM_BEG, AIMG_HI in TR. olin_all. pose proof TRL as TRL30. unfold TRACE_MAX_LEN in TRL30.
  assert (HB : In (A, n) (all_blocks st)) by (unfold all_blocks; apply in_or_app; left; exact HIN).
  (nelimp (block_geom st WF A n HB) 10%nat; intros Gn GA GK GX GY GCE GL16 GH16 GEA _). unfold usz in GY. unfold KHIGHMEM_BEG, AIMG_HI in GK. olin_all.
  (nelimp (block_extra st WF A n HB) 5%nat; intros E8 EAB EABA EMB ERZ32). pose proof (rz_size_range n) as [RZ _].
  pose proof (fp_nonneg n ltac:(lia)) as FPN. pose proof (tpx_ok_of_RTWF st WF) as HX. pose proof (proj1 HX) as CT.
  apply lscps_assume. intros NWX HO HBI.
  pose proof (wmono_refl asegs m) as WM01.
  eapply lscps_step_evt. cbv beta delta [wz] in *.
  (* [comment removed for export] *)
  pose proof (rr_live st m HR A n HIN) as RB2.
  assert (SHL2 : bprim n = true -> rw_cells asegs m (SH (b_lo A n)) (zcells (sh_live n))).
  { intros BP. (nelim RB2 5%nat; intros _ _ _ _ BS). unfold R_bshadow in BS. rewrite BP in BS. exact BS. }
  destruct (rr_live st m HR A n HIN) as ((b1 & cid & HC2 & HB1ok) & _ & _ & V2 & _).
  unfold hdr_cells, hdr_state_live, b_chunk_beg in HC2. replace (A - 16) with (A + -16) in HC2 by lia.
  destruct (vis_c8 m _ _ A V2 ltac:(lia) ltac:(lia)) as [uw UW2].
  destruct (rr_thread st m HR) as (TV2 & _).
  destruct (vis_c8 m _ _ (st_t st + 2824) TV2 ltac:(lia) ltac:(lia)) as [sj3 TS3].
  destruct (vis_c8 m _ _ (st_t st + 2832) TV2 ltac:(lia) ltac:(lia)) as [sj4 TS4].
  assert (TS2 : rw_cells asegs m (st_t st + 2824) [C8 sj3; C8 sj4]).
  { apply (proj2 (rw_cells_app m (st_t st + 2824) [C8 sj3] [C8 sj4])). split; [exact TS3|]. cbn [cells_size Cells.csize Nat.add].
    replace (st_t st + 2824 + Z.of_nat 8) with (st_t st + 2832) by lia. exact TS4. }
  clear TS3 TS4 TV2.
  pose proof (leafc_of_RTREP st m HR) as LC2.
  pose proof (t_vs_block st WF A n HB) as TB.
  (nelim (wb_ctx_loose st (wf_base_ok st WF)) 5%nat; intros cb ck CL1 CL2 CL3).
  pose proof (loose_blockfree st WF cb ck CL1 A n HB) as CBF. (nelimp (loose0_range st WF cb ck CL1) 4%nat; intros CR1 CR2 CR3 CR4). unfold KHIGHMEM_BEG, AIMG_HI in CR1. olin_all.
  pose proof (munch_refl [(A + -16, A + -12); (A, A + 8); (st_t st + 2824, st_t st + 2840); (bv_unsigned sp - 96, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM2.
  (* [comment removed for export] *)
  sepM. callxp ltac:(eapply free_d1_spec with (st := st) (A := A) (n := n) (S := S) (lo := lo);
    [ exact LC2| exact WF| exact MI| exact TP| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity
    | lia| exact GA| unfold KHIGHMEM_BEG, AIMG_HI; lia| idtac; lia| lia| exact HB1ok
    | (lia_on GA GX GY GH16 TB)| (lia_on GA GX GY GH16 CL2 CL3 CBF)
    | exact ST| idtac; lia| lia
    | exact HC2| exact UW2| exact TS2 ])
    ltac:(unfold AQCHUNK, A_ALLOC, CHUNK_QUARANTINE; rewrite ?unsigned_lit by lia; clear TS2 UW2 HC2; clear V2 ST).
  cbv beta delta [wz] in *.
  match goal with H : stk _ _ lo _ |- _ => rename H into ST3 end.
  match goal with H : mem_inv _ ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into MI3; rename mx into m3 end.
  match goal with H : rw_cells _ m3 (A + -16) _ |- _ => rename H into HC3 end.
  (* [comment removed for export] *)
  (nelimp (st_freeP_same st A n) 20%nat; intros Fsp0 Flb Flf Ftrs Fap Fsp Fsec Fqp Fqt Fqc Fqth Fqg Fdep Ffs Ft Fsb Fpb Fpa Fctx _).
  set (st2 := st_freeP st A n) in *.
  assert (WF2 : RTWF st2) by (apply RTWF_freeP'; [exact WF| exact HIN| exact HQP]).
  pose proof (RTMODEL_freeP' st A n mo HM) as HM2. change (st_freeP st A n) with st2 in HM2.
  pose proof (tpx_ok_of_RTWF st2 WF2) as HX2.
  pose proof (rt_prov_freeP' st A n HIN) as PV2. change (st_freeP st A n) with st2 in PV2.
  assert (TX0 : 0 <= (if is_cl24 n then CL24_TAX else 0)) by (unfold CL24_TAX; destruct (is_cl24 n); lia).
  assert (HINQ2 : In (A, n) (st_qpend st2)) by (rewrite Fqp; left; reflexivity).
  assert (HB2 : In (A, n) (all_blocks st2)) by (unfold all_blocks; rewrite !in_app_iff; right; right; exact HINQ2).
  assert (HR3 : RTREP st2 m3).
  { eapply (RTREP_freeP' st WF HX A n HIN _ m m3); [| exact MU| exact WM2| exact HR|].
    - unfold lbz_ok. unfold T_STATS, T_UNWINDING, CEIL. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia.
    - eapply (R_block_to_pend st WF A n HB _); [| exact MU| exact WM2| exact RB2| | exact HB1ok].
      + repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia.
      + unfold b_chunk_beg, hdr_cells, hdr_state_quar. replace (A - 16) with (A + -16) by lia. exact HC3. }
  assert (CP23 : cli_pres st2 (bv_unsigned sp) m m3).
  { eapply (cli_pres_qz st2 WF2 A n (or_intror HINQ2) (bv_unsigned sp)); [unfold CEIL; lia| exact MU| exact WM2|].
    unfold lbzc_ok. rewrite Ft. unfold T_STATS, T_UNWINDING, CEIL. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
  assert (ES23 : errno_same m m3).
  { eapply errno_same_munch; [exact MU|]. unfold AERRNO, ATP. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
  assert (LC3 : leafc st2 m3).
  { apply leafc_freeP'. eapply (leafc_keep st _ m m3 MU WM2); [| exact LC2]. olin_all. unfold AIMG_LO, AIMG_HI.
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; (lia_on GA GX GY GH16 ALx CT CL2 CL3 CBF OLx HCL LO CR3). }
  assert (SO3 : rw_cells asegs m3 S [C8 (Z_to_bv 64 (S + 16)); C8 (Z_to_bv 64 (zlen tr))]).
  { first [exact SOBJ| eapply rw_cells_transport; [exact SOBJ| exact MU| exact WM2|]; cbn; lia]. }
  assert (STR3 : cells_at asegs m3 (S + 16) (trace_cells tr)).
  { first [exact STR| eapply (ro_cells_transport asegs _ m m3); [exact STR| exact MU|]; cbn [disjoint_from]; rewrite trace_cells_size; (lia_on HS1 HCL LO SP0 TR GA GX GY GH16 ALx E8 CT TB CL2 CL3 CBF CR3 OLx1)]. }
  assert (SHL3 : bprim n = true -> rw_cells asegs m3 (SH (b_lo A n)) (zcells (sh_live n))).
  { intros BP. eapply rw_cells_transport; [exact (SHL2 BP)| exact MU| exact WM2|].
    rewrite zcells_size, sh_live_len by lia. apply (LZ_block_self_shadow st WF A n HB).
    unfold lbz_ok. unfold T_STATS, T_UNWINDING, CEIL. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
  clear MU WM2. try clear SOBJ. try clear STR. try clear HC2. try clear UW2. try clear TS2. try clear RB2. try clear V2. try clear LC2.
  (* [comment removed for export] *)
  destruct (rr_thread st2 m3 HR3) as (_ & (tj1 & tj2 & tj3 & tj4 & tj5 & TT) & _ & _ & TID & _).
  pose proof (rw_cells_merge asegs m3 (st_t st2) [C8 (wz (st_ctx st2))] _ [] ltac:(rewrite app_nil_r; exact TT)) as TT3.
  cbn [cells_size cells_bytes Cells.csize cbytes app Nat.add length] in TT3. clear TT.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m3) as MU. pose proof (wmono_refl asegs m3) as WM3.
  sepM. callxp ltac:(eapply free_q1_spec with (st := st2) (A := A) (n := n) (S := S) (lo := lo) (tr := tr);
    [ exact LC3| exact WF2| exact MI3| exact TP| reflexivity| reflexivity| reflexivity| reflexivity
    | lia| unfold KHIGHMEM_BEG, AIMG_HI; lia| idtac; lia| lia| lia| lia
    | exact ST3| idtac; lia| lia
    | exact HC3| exact TT3| exact TID| exact SO3 ])
    ltac:(unfold ADEPOT_PUT, A_ALLOC; rewrite ?unsigned_lit by lia; clear TID; clear ST3).
  cbv beta delta [wz] in *.
  match goal with H : stk _ _ lo _ |- _ => rename H into ST4 end.
  match goal with H : mem_inv _ ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into MI4; rename mx into m4 end.
  match goal with H : rw_cells _ m4 (bv_unsigned sp - 48) _ |- _ => rename H into FRQ4 end.
  pose proof HR3 as HR4. rtrep_high HR4 WF2 MU WM3.
  assert (CP34 : cli_pres st2 (bv_unsigned sp) m3 m4).
  { eapply (cli_pres_tpz st2 WF2); [| exact MU| exact WM3|]; [unfold CEIL; lia|]. constructor; [cbn [fst snd]; unfold CEIL; lia| constructor]. }
  assert (ES34 : errno_same m3 m4).
  { eapply errno_same_munch; [exact MU|]. constructor; [cbn [fst snd]; unfold AERRNO, ATP; lia| constructor]. }
  assert (STR4 : cells_at asegs m4 (S + 16) (trace_cells tr)).
  { first [exact STR3| eapply (ro_cells_transport asegs _ m3 m4); [exact STR3| exact MU|]; cbn [disjoint_from]; rewrite trace_cells_size; lia]. }
  assert (HG4 : GWIN st2 m4 mo g) by (apply GWIN_freeP'; eapply GWIN_mem; [exact HG| exact HO| exact WM01]).
  assert (SHL4 : bprim n = true -> rw_cells asegs m4 (SH (b_lo A n)) (zcells (sh_live n))).
  { intros BP. eapply rw_cells_transport; [exact (SHL3 BP)| exact MU| exact WM3|].
    rewrite zcells_size, sh_live_len by lia. apply (LZ_block_self_shadow st2 WF2 A n HB2).
    constructor; [unfold lbz_ok; cbn [fst snd]; right; right; unfold CEIL; lia| constructor]. }
  clear MU WM3. try clear STR3.
  (* [comment removed for export] *)
  apply evt_done. eapply lscps_bind.
  { pose proof depot_put_proof as DP. unfold depot_put_specS in DP.
    eapply DP with (lo := lo) (P := S + 16) (tr := tr) (st := st2); try reflexivity.
    - exact (RTS_intro _ _ _ _ HR4 WF2 HM2 HG4 HFR (SWIN_freeP' st A n g HSWR)).
    - exact TRL. - exact TRR.
    - exact STR4.
    - right. rewrite unsigned_lit by lia. lia.
    - idtac. lia.
    - unfold TRACE_MAX_LEN in TRL. lia.
    - exact TP.
    - rewrite Ftrs. exact ROOM.
    - lia.
    - rewrite unsigned_lit by lia. exact ST4. - idtac; lia. - rewrite unsigned_lit by lia. unfold ADEPOT_STACK. lia.
    - exact MI4. }
  cbv beta. intros ms5 mo5 g5 PO.
  (nelim PO 30%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m5 st3 -> MI5 id -> Hid SBD TP3 RTS3 ST5 CP45 RF45 GM5 BO45)
.
  rewrite unsigned_lit in ST5, CP45, RF45 by lia.
  replace (ret_pc (Z_to_bv 64 0x360e0)) with (Z_to_bv 64 0x360e0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  (nelim RTS3 6%nat; intros HR5 WF3 HM3 HG5 HF3 HSW3).
  destruct SBD as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & D15 & D16 & D17 & D18 & D19 & D20 & D21 & D22 & D23 & D24 & D25 & D26). (* [comment removed for export] *)
  assert (HINQ3 : In (A, n) (st_qpend st3)) by (rewrite D24; exact HINQ2).
  assert (HB3 : In (A, n) (all_blocks st3)) by (unfold all_blocks; rewrite !in_app_iff; right; right; exact HINQ3).
  pose proof (tpx_ok_of_RTWF st3 WF3) as HX3.
  assert (SHL5 : bprim n = true -> rw_cells asegs m5 (SH (b_lo A n)) (zcells (sh_live n))).
  { intros BP. (nelim (proj2 (rr_quar st3 m5 HR5) A n HINQ3) 5%nat; intros _ _ _ _ BS5). unfold R_bshadow in BS5. rewrite BP in BS5.
    assert (SHB' : SH (b_lo A n) + sh_tot n <= SH CEIL).
    { unfold sh_tot. rewrite <- rt_SH_aligned_add by (Z.div_mod_to_equations; lia). apply rt_SH_mono. change (b_lo A n + asz n) with (b_hi A n). unfold CEIL. lia. }
    rewrite SH_CEIL in SHB'.
    pose proof (rt_SH_mono 0 (b_lo A n) ltac:(lia)) as SHB0'. change (SH 0) with 0x7fff8000 in SHB0'.
    eapply (rw_cells_rt_frame _ _ _ m4 m5 _ _ _ _ RF45 (SHL4 BP) BS5); [lia| rewrite zcells_size, sh_live_len by lia; lia| lia|].
    rewrite zcells_size, sh_live_len by lia. intros a Ha. split; [lia|].
    apply (band_notin_depot_fp st3 a WF3). unfold KLOWSHADOW_BEG, KHIGHMEM_BEG. lia. }
  (* [comment removed for export] *)
  apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ CP45) in FRQ4; [| left; cbn; lia].
  assert (ES45 : errno_same m4 m5).
  { eapply errno_same_rt_frame; [exact RF45| unfold AERRNO, ATP; lia|]. intros a Ha. apply (errno_notin_depot_fp st3 a WF3 Ha). }
  destruct (proj2 (rr_quar st3 m5 HR5) A n HINQ3) as ((b1' & cid' & HC5 & HB1ok') & _ & _ & V5 & _).
  unfold hdr_cells, hdr_state_quar, b_chunk_beg in HC5. replace (A - 16) with (A + -16) in HC5 by lia.
  destruct (vis_c8 m5 _ _ A V5 ltac:(lia) ltac:(lia)) as [fw UW5].
  apply lscps_assume. intros _ HO5 HB5.
  eapply lscps_step_evt. cbv beta delta [wz] in *.
  (* [comment removed for export] *)
  pose proof (munch_refl [(A, A + 8)] m5) as MU. pose proof (wmono_refl asegs m5) as WM5.
  rewrite <- D16.
  sepM. callxp ltac:(eapply free_q2_spec with (st := st3) (A := A) (n := n) (S := S) (id := id);
    [ exact MI5| reflexivity| exact Hid| lia| unfold KHIGHMEM_BEG, AIMG_HI; lia| idtac; lia
    | rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; lia
    | exact HC5| exact UW5| rewrite unsigned_lit by lia; exact FRQ4 ])
    ltac:(unfold AQPUT, A_QUAR, A_ALLOC; rewrite !unsigned_lit by lia; clear UW5; clear V5).
  cbv beta delta [wz] in *.
  match goal with H : mem_inv _ ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into MI6; rename mx into m6 end.
  assert (SHB : SH (b_lo A n) + sh_tot n <= SH CEIL).
  { unfold sh_tot. rewrite <- rt_SH_aligned_add by (Z.div_mod_to_equations; lia). apply rt_SH_mono. change (b_lo A n + asz n) with (b_hi A n). unfold CEIL. lia. }
  rewrite SH_CEIL in SHB.
  pose proof (rt_SH_mono 0 (b_lo A n) ltac:(lia)) as SHB0. change (SH 0) with 0x7fff8000 in SHB0.   (* [comment removed for export] *)
  assert (HR6 : RTREP st3 m6).
  { eapply (lbz_all st3 WF3 HX3 A n HB3 [(A, A + 8)] ltac:(constructor; [unfold lbz_ok; cbn [fst snd]; left; lia| constructor]) m5 m6 MU WM5 HR5).
    unfold WOK_block, b_chunk_beg.
    split; [cbn; lia|]. split; [intros HRZ; cbn; specialize (ERZ32 HRZ); unfold b_alloc_beg in *; lia|].
    split; [intros EP; specialize (EMB EP); pose proof EMB as EMB'; unfold b_map_beg, SEC_RZ, SEC_HDR in EMB'; cbn; lia|].
    cbn. lia. }
  assert (CP56 : cli_pres st3 (bv_unsigned sp) m5 m6).
  { eapply (cli_pres_qz st3 WF3 A n (or_intror HINQ3) (bv_unsigned sp)); [unfold CEIL; lia| exact MU| exact WM5|].
    constructor; [| constructor]. unfold lbzc_ok. cbn [fst snd]. left. lia. }
  assert (ES56 : errno_same m5 m6).
  { eapply errno_same_munch; [exact MU|]. constructor; [cbn [fst snd]; unfold AERRNO, ATP; lia| constructor]. }
  assert (HG6 : GWIN st3 m6 mo5 g5) by (eapply GWIN_mem; [exact HG5| exact HO5| exact WM5]).
  match goal with H : stk _ m6 lo _ |- _ => rename H into ST6 end.
  match goal with H : rw_cells _ m6 (bv_unsigned sp - 48) _ |- _ => rename H into FRQ6 end.
  replace (bv_unsigned sp - 48 + 48) with (bv_unsigned sp) by lia.
  release_frame FRQ6 ST6 (bv_unsigned sp).
  assert (SHL6 : bprim n = true -> rw_cells asegs m6 (SH (b_lo A n)) (zcells (sh_live n))).
  { intros BP. eapply rw_cells_transport; [exact (SHL5 BP)| exact MU| exact WM5|].
    rewrite zcells_size, sh_live_len by lia. apply (LZ_block_self_shadow st3 WF3 A n HB3).
    constructor; [unfold lbz_ok; cbn [fst snd]; left; lia| constructor]. }
  clear MU WM5.
  (* [comment removed for export] *)
  apply evt_done. eapply lscps_bind.
  { pose proof quarantine_put_proof as QP. unfold quarantine_put_spec2 in QP.
    eapply QP with (lo := lo) (st := st3) (A := A) (n := n) (S := S); try reflexivity.
    - exact (RTS_intro _ _ _ _ HR6 WF3 HM3 HG6 HF3 HSW3).
    - exact HINQ3.
    - rewrite D25, Fqt. exact HQT.
    - rewrite D26, Fqc. exact HQC.
    - rewrite D22, Fap. exact HAP.   (* [comment removed for export] *)
    - exact SHL6.   (* [comment removed for export] *)
    - exact TP.
    - rewrite ?unsigned_lit by lia. rewrite D1, Fsp0. lia.   (* [comment removed for export] *)
    - unfold budget_ok in BO45. unfold cost_free. lia.
    - rewrite unsigned_lit by lia. exact ST6. - idtac; lia. - rewrite unsigned_lit by lia. unfold AQPUT_STACK. lia.
    - exact MI6. }
  cbv beta. intros ms7 mo7 g7 PO.
  (nelim PO 26%nat; intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' m7 st4 -> MI7 QR RTS4 ST7 CP67 ES67 GM7 BO67)
.
  rewrite unsigned_lit in ST7, CP67 by lia.
  (nelim QR 5%nat; intros SQ Eqp4 Eqt4 Eqc4 FRESHK).
  (nelim SQ 18%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 Q13 Q14 Q15 Q16 Q17 Q18).
  apply lscps_assume. intros _ HO7 HB7. try rewrite Z_to_bv_bv_unsigned.
  apply lscps_done. unfold dealloc_post.
  nexists 15%nat. exists m7, st4. split; [reflexivity|]. split; [exact MI7|]. split; [exact ST7|].
  split.
  { exact (errno_same_trans _ _ _ (errno_same_trans _ _ _ (errno_same_trans _ _ _ (errno_same_trans _ _ _ ES23 ES34) ES45) ES56) ES67). }
  split.
  { unfold cli_pres in *.
    rewrite Q1, Q16, Q10, D1, D21, D15. rewrite D1, D21, D15 in CP56, CP67.
    eapply cj_pres_trans; [exact CP23|]. eapply cj_pres_trans; [exact CP34|].
    eapply cj_pres_trans; [eapply cj_pres_weaken; [exact CP45| lia| auto| auto]|].
    eapply cj_pres_trans; [exact CP56| exact CP67]. }
  split; [eapply gmono_trans; [exact GM5| exact GM7]|].
  split; [rewrite Q6, <- Ftrs; exact TP3|].
  split; [exact RTS4|]. split; [exact HO7|]. split; [exact HB7|].
  split; [rewrite Q1, D1; exact Fsp0|].
  split; [rewrite Q16, D21; exact Flb|].
  split; [rewrite Q10, D15; exact Flf|].
  split; [rewrite Q17, D22; exact Fap|].
  split; [rewrite Q18, D23; exact Fsp|].
  split; [rewrite Eqp4, D24, Fqp; cbn [remove_first]; rewrite (proj2 (ck_eqb_eq _ _) eq_refl); reflexivity|].
  split; [exact Eqt4|]. split; [exact Eqc4|].
  unfold budget_ok, cost_free in *. lia.
Qed.
End DCORE.


End CeilWrap.
End RTW_m_dcore.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes PropExec MState Mem Cells Step Frame Exec SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import Spin SRealizes LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_wf RT_rep RT_kit CJ_iface RT_art RT_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_fp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_cost.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_kit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_sec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_sec.RTW_secondary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_depot_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_leaves_memset.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_nn_specs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_a1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_m_lib2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_p_abs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_lib3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_m_tpz RTW_m_specs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_nn_specs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_aspec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_p_abs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_i1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_unwind.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_sec_dstateP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstateP.RTW_m_live.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_bandtac4 RT_front RT_cost.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_sec_dstate.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstate.RT_fresh.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_sec.
Import RTW_m_malloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import Drv_iface2 RT_drv RTW_nn_specs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section MALLOCN.
Hypothesis try_asan_init_proof : try_asan_init_spec.
Hypothesis get_malloc_ctx_size_proof : get_malloc_ctx_size_spec.
Hypothesis get_current_pc_proof : get_current_pc_spec.
Hypothesis set_errno_enomem_proof : set_errno_enomem_spec.
Hypothesis unwind_ok : unwind_spec.
Hypothesis allocate_nn_ok : allocate_nn_spec.

Theorem art_malloc_nn_proof : malloc_nn_stmt ARTd ADRVd.
Proof.
  unfold malloc_nn_stmt. intros until tl. rename k into kd. intros HART HDRV SPB0 ST HCL LO ERR MI TP -> Hn0 COST HBF HPK [RA1 RA2] UWT ROOM.
  assert (Hn : 0 <= n < 2^32) by (unfold DRV_REQ_MAX in Hn0; lia).
  pose proof tpx_ok_of_RTWF as tpx_all.
  destruct (ARTd_RTS _ _ _ _ _ _ _ _ _ HART) as (st & (HR & WF & HM & HG & HFR & HSWR) & HO & HB & Esp0 & Elb & Elf & Etrs & HQ & B0 & BB & HSPB).
  pose proof (wb_sp0 st (wf_base_ok st WF)) as SP0. rewrite Esp0 in SP0. unfold AMALLOC_STACK in LO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. idtac.
  pose proof (bv_unsigned_in_range 64 ra) as RRA. unfold bv_modulus in RRA. cbn in RRA.
  pose proof (t_range st WF) as TR. olin TR. unfold KHIGHMEM_BEG, AIMG_HI in TR. olin_all.
  pose proof (alloc_deposit_le_cost n Hn) as DEP.
  pose proof (stk_wr_at m lo (bv_unsigned sp) (bv_unsigned sp + -2144) 2144 ST ltac:(lia) ltac:(lia)) as WR0.
  change AERRNO with 6148524 in ERR.
  apply lscps_assume. intros NWX _ _. pose proof HR as HR0.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  eapply lscps_step_evt.
  callx ltac:(eapply (malloc_i1_spec try_asan_init_proof get_malloc_ctx_size_proof get_current_pc_proof) with (lo := lo) (st := st) (n := n);
              [exact HR| exact WF| exact MI| reflexivity| exact Hn| exact ST| idtac; lia| unfold I1_DEPTH; lia]).
  cbv beta delta [wz] in *.
  match goal with H : stk _ _ lo _ |- _ => rename H into ST1 end.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -2128) _ |- _ => rename H into OBJ1 end.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -72) _ |- _ => rename H into BP1 end.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -56) _ |- _ => rename H into FR1 end.
  match goal with H : stk _ _ (bv_unsigned sp + -2112) _ |- _ => rename H into BUF1 end.
  match goal with H : mem_inv _ _ |- _ => rename H into MI1 end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  pose proof HR0 as HR1. rtrep_high HR1 WF MU WM.
  replace (bv_unsigned sp + -2128 + 16) with (bv_unsigned sp + -2112) in OBJ1 by lia.
  (* [comment removed for export] *)
  pose proof (rw_cells_take m1 _ [C8 (Z_to_bv 64 (bv_unsigned sp + -2112))] [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] OBJ1) as OBa.
  pose proof (rw_cells_drop m1 _ [C8 (Z_to_bv 64 (bv_unsigned sp + -2112)); C4 (Z_to_bv 64 0)] [C4 (Z_to_bv 64 0)] OBJ1) as OBc.
  cbn [cells_size Cells.csize Nat.add] in OBc. replace (bv_unsigned sp + -2128 + Z.of_nat 12) with (bv_unsigned sp + -2116) in OBc by lia.
  (* [comment removed for export] *)
  destruct (stk_split asegs m1 _ (bv_unsigned sp + -2112 + 8 * zlen (hook_tr PC0_MALLOC sp0 (bv_unsigned sp) (bv_unsigned ra) tl)) _ BUF1) as [_ BUF2].
  { pose proof (hook_tr_facts PC0_MALLOC sp0 (bv_unsigned sp) (bv_unsigned ra) tl m _ _ _ ltac:(unfold PC0_MALLOC; lia) ltac:(lia) UWT) as [L _].
    unfold TRACE_MAX_LEN in L. lia. }
  clear BUF1.
  (* [comment removed for export] *)
  assert (REC : bytes_at asegs m1 (bv_unsigned sp - 16) (le8 s0 ++ le8 ra)).
  { pose proof (rw_cells_drop m1 _ [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR1) as [[_ RB] _].
    cbn [cells_size Cells.csize Nat.add cells_bytes cbytes] in RB. rewrite app_nil_r in RB.
    replace (bv_unsigned sp + -56 + Z.of_nat 40) with (bv_unsigned sp - 16) in RB by lia. exact RB. }
  assert (UWT1 : uwt m1 (bv_unsigned sp) (ASTACK_TOP sp0) PC0_MALLOC (bv_unsigned sp) (bv_unsigned s0) 2 tl).
  { eapply uwt_mem; [exact UWT|]. intros a Ha Ha'. apply MU. rewrite wa_unsigned by lia. cbn. lia. }
  pose proof (hook_tr_facts PC0_MALLOC sp0 (bv_unsigned sp) (bv_unsigned ra) tl m _ _ _ ltac:(unfold PC0_MALLOC; lia) ltac:(lia) UWT) as [TRL TRR].
  pose proof TRL as TRL30. unfold TRACE_MAX_LEN in TRL30.
  assert (CP01 : cli_pres st (bv_unsigned sp) m m1).
  { eapply (cli_pres_tpz st WF); [| exact MU| exact WM|]; [unfold CEIL; lia|]. constructor; [| constructor]. cbn [fst snd]. right. unfold CEIL. lia. }
  assert (ES01 : errno_same m m1).
  { eapply errno_same_munch; [exact MU|]. constructor; [cbn; unfold AERRNO, ATP; lia| constructor]. }
  clear MU. pose proof (munch_refl [(lo, bv_unsigned sp); (st_t st + 3168, st_t st + 3168 + 1)] m1) as MU.
  pose proof (wmono_refl asegs m1) as WM1.
  callxp ltac:(eapply unwind_ok with (st := st) (S := bv_unsigned sp + -2128) (pc0 := PC0_MALLOC) (bp := bv_unsigned sp) (rac := ra) (s0c := s0) (tl := tl) (lo := lo);
    [ exact (RTS_intro _ _ _ _ HR1 WF HM ltac:(eapply GWIN_mem; [exact HG| exact HO| exact WM]) HFR HSWR)
    | reflexivity| reflexivity| symmetry; apply Z_to_bv_bv_unsigned| reflexivity| reflexivity| reflexivity| exact TP
    | replace (bv_unsigned sp + -2128 + 16) with (bv_unsigned sp + -2112) by lia; exact OBJ1
    | eapply wr_at_weaken; [exact WR0| lia| unfold BST_SIZE; lia]
    | rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; lia| lia| unfold PC0_MALLOC; lia
    | exact REC| exact RA1| exact RA2
    | intros _; rewrite Esp0; exact UWT1
    | left; unfold BST_SIZE; lia
    | rewrite unsigned_lit by lia; exact ST1| idtac; lia| rewrite unsigned_lit by lia; unfold AUNWIND_STACK; lia| exact MI1 ])
    ltac:(unfold unwind_post, T_UNWINDING; rewrite !Esp0, !unsigned_lit by lia).
  cbv beta delta [wz] in *.
  match goal with H : stk _ _ lo _ |- _ => rename H into ST2 end.
  match goal with H : RTREP st ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into HR2; rename mx into m2 end.
  match goal with H : rw_cells _ m2 (bv_unsigned sp + -2128 + 8) _ |- _ => rename H into SZ2 end.
  match goal with H : rw_cells _ m2 (bv_unsigned sp + -2128 + 16) _ |- _ => rename H into TRC2 end.
  match goal with H : mem_inv _ m2 |- _ => rename H into MI2 end.
  assert (CP12 : cli_pres st (bv_unsigned sp) m1 m2).
  { eapply (cli_pres_tpz st WF); [| exact MU| exact WM1|]; [unfold CEIL; lia|].
    unfold T_ACACHE, CEIL. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
  assert (ES02 : errno_same m m2).
  { eapply errno_same_trans; [exact ES01|].
    eapply errno_same_munch; [exact MU|]. unfold AERRNO, ATP. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
  clear MU WM1.
  (* [comment removed for export] *)
  assert (SOBJ : rw_cells asegs m2 (bv_unsigned sp + -2128)
            [C8 (Z_to_bv 64 (bv_unsigned sp + -2112)); C4 (Z_to_bv 64 (zlen (hook_tr PC0_MALLOC sp0 (bv_unsigned sp) (bv_unsigned ra) tl))); C4 (Z_to_bv 64 0)]).
  { apply (proj2 (rw_cells_app m2 _ [C8 _] [C4 _; C4 _])). split; [assumption|]. cbn [cells_size Cells.csize Nat.add].
    apply (proj2 (rw_cells_app m2 _ [C4 _] [C4 _])). split; [exact SZ2|]. cbn [cells_size Cells.csize Nat.add].
    replace (bv_unsigned sp + -2128 + Z.of_nat 8 + Z.of_nat 4) with (bv_unsigned sp + -2116) by lia. assumption. }
  clear SZ2.
  (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  pose proof (munch_refl [(lo, bv_unsigned sp)] m2) as MU. pose proof (wmono_refl asegs m2) as WM2.
  carve_frame 16%nat ST2.
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  match goal with H : rw_cells _ _ (bv_unsigned sp + -2144) [C8 sp; C8 _] |- _ => rename H into FRM end.
  match goal with H : stk _ _ lo (bv_unsigned sp + -2144) |- _ => rename H into ST3 end.
  match goal with H : mem_inv _ _ |- _ => rename H into MI3 end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
  pose proof HR2 as HR3. rtrep_high HR3 WF MU WM2.
  assert (CP23 : cli_pres st (bv_unsigned sp) m2 m3).
  { eapply (cli_pres_tpz st WF); [| exact MU| exact WM2|]; [unfold CEIL; lia|]. constructor; [cbn; unfold CEIL; lia| constructor]. }
  assert (ES03 : errno_same m m3).
  { eapply errno_same_trans; [exact ES02|]. eapply errno_same_munch; [exact MU|]. constructor; [cbn; unfold AERRNO, ATP; lia| constructor]. }
  assert (HG3 : GWIN st m3 mo g) by (eapply GWIN_mem; [exact HG| exact HO| exact WM]).
  assert (WR3 : wr_at asegs m3 (bv_unsigned sp + -2144) 2144) by (first [exact WR0| eapply wr_at_wmono; [exact WR0| exact WM2]]).
  clear MU WM2 WR0.
  assert (HNN : cnn_ok st mo n).
  { unfold cnn_ok. destruct (bprim n) eqn:HPn.
    - (* [comment removed for export] *)
      pose proof (adrvd_use _ _ _ _ st HDRV HR0 WF) as FX. pose proof (prim_facts n HPn) as (PC & _).
      unfold refill_room. destruct (Z.eq_dec (pclass n) 24) as [E24|N24].
      + rewrite E24. intros NA. apply (class24_populate_ok st WF); [| exact NA].
        pose proof (g_res_le_limit st mo g HB HM) as GL. clear - GL BB B0. lia.
      + intros _. (nelim (fresh_cls_facts st (pclass n) (FX (pclass n) ltac:(unfold KNUMCLASSES; lia) N24)) 3%nat; intros _ F2 _).
        rewrite F2. unfold KFREEARRAY_OFF. lia.
    - (* [comment removed for export] *)
      pose proof (smapsize_le n ltac:(lia) HPn) as SL. pose proof (smapsize_pos n ltac:(lia)) as [SP _].
      pose proof (rt_prov_nonneg st WF) as PN.
      apply (FRONTR_placeable_big mo (g_res g) (smapsize n) HO HFR); [lia| unfold FR_NBIG; unfold DRV_REQ_MAX in Hn0; lia| unfold FR_RBIG; unfold DRV_BFLOOR in HBF; clear - HBF BB PN; lia]. }
  apply evt_done. eapply lscps_bind.
  { pose proof allocate_nn_ok as AL. unfold allocate_nn_spec in AL.
    eapply AL with (lo := lo) (st := st) (n := n) (S := bv_unsigned sp + -2128) (tr := hook_tr PC0_MALLOC sp0 (bv_unsigned sp) (bv_unsigned ra) tl); try reflexivity.
    - exact (RTS_intro _ _ _ _ HR3 WF HM HG3 HFR HSWR).
    - exact tpx_all. - exact (proj1 HQ). - exact Hn. - exact TP.
    - replace (bv_unsigned sp + -2128 + 16) with (bv_unsigned sp + -2112) by lia. exact SOBJ.
    - replace (bv_unsigned sp + -2128 + 16) with (bv_unsigned sp + -2128 + 16) by lia. exact (proj1 TRC2).
    - exact TRL. - exact TRR.
    - rewrite unsigned_lit by lia. lia. - rewrite Esp0. unfold BST_SIZE. lia.
    - rewrite Etrs. exact ROOM.
    - lia.
    - exact HNN.
    - rewrite unsigned_lit by lia. exact ST3. - idtac. lia. - rewrite unsigned_lit by lia. unfold AALLOCATE_STACK. lia.
    - rewrite unsigned_lit, Esp0 by lia. lia. - exact MI3. }
  cbv beta. intros ms4 mo4 g4 [[PO NZ4] BLK4].
  (nelim PO 30%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m4 st4 -> MI4 r -> RTS4 ST4 CP4 ES4 GM4 Esp04 Elf4 AS4 RES).
  assert (HQ4 : QUIET st4).
  { (nelim AS4 5%nat; intros Q1 Q2 Q3 Q4 Q5). unfold QUIET in *. rewrite Q1, Q2, Q3, Q4, Q5. exact HQ. }
  rewrite unsigned_lit in ST4, CP4 by lia.
  replace (ret_pc (Z_to_bv 64 0x31ec4)) with (Z_to_bv 64 0x31ec4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  (nelim RTS4 6%nat; intros HR4 WF4 HM4 HG4 HF4 HSW4).
  (* [comment removed for export] *)
  apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ CP4) in FRM; [| left; cbn; rewrite Esp0; lia].
  apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ CP4) in FR1; [| left; cbn; rewrite Esp0; lia].
  apply (cj_pres_wr_at _ _ _ _ _ _ _ _ CP4) in WR3; [| left; rewrite Esp0; lia].
  assert (ERR4 : rw_cells asegs m4 6148524 [C4 errv]).
  { eapply rw_cells_same; [exact ERR|]. intros a Ha. cbn in Ha. apply ES4 || (replace a with (AERRNO + (a - 6148524)) by (unfold AERRNO, ATP; lia); apply ES4; lia). }
  assert (CP04 : cj_pres sp0 LB LF (bv_unsigned sp) m m4).
  { unfold cli_pres in *. rewrite Esp0, Elb, Elf in CP01, CP12, CP23, CP4.
    eapply cj_pres_trans; [exact CP01|]. eapply cj_pres_trans; [exact CP12|]. eapply cj_pres_trans; [exact CP23|].
    eapply cj_pres_weaken; [exact CP4| lia| auto| auto]. }
  clear CP01 CP12 CP23 CP4 ES01 ES02 ES03 ERR.
  apply lscps_assume. intros _ HO4 HB4.
  eapply lscps_step_evt. cbv beta delta [wz] in *.
  (* [comment removed for export] *)
  assert (HLB : forall A k, In (A, k) LB -> AIMG_HI <= A).
  { intros A k Hin. rewrite <- Elb in Hin. (nelimp (block_geom st WF A k ltac:(unfold all_blocks; apply in_or_app; left; exact Hin)) 5%nat; intros _ _ G1 G2 _). blia. }
  assert (HLF : forall Fr k, In (Fr, k) LF -> AIMG_HI <= Fr).
  { intros Fr k Hin. rewrite <- Elf in Hin. (nelimp (frame_range st WF Fr k Hin) 3%nat; intros _ X _). pose proof (fs_range st WF) as (F1 & _).
    change FS_FRAMES_OFF with 36864 in X. blia. }
  assert (B4 : 0 <= B - cost_malloc n) by lia.
  destruct RES as [(-> & Elb4 & Etrs4 & BO4)|(RNZ & ABR & NIN & NFR & Elb4 & TP4 & BO4 & JK)].
  - (* [comment removed for export] *)
    exfalso. apply NZ4. reflexivity.
  - (* [comment removed for export] *)
    assert (ART4 : ARTd sp0 SPB ((r, n) :: LB) LF (st_trs st4) (B - cost_malloc n) m4 mo4 g4).
    { eapply (ARTd_intro st4); [exact HR4| exact WF4| exact HM4| exact HO4| exact HB4| exact HG4| exact HF4
        | rewrite Esp04; exact Esp0| rewrite Elb4, Elb; reflexivity| rewrite Elf4; exact Elf| reflexivity| exact HQ4| exact B4| | exact HSPB| exact HSW4].
      unfold budget_ok in BO4. lia. }
    pose proof ABR as ABR'. unfold ablock_range, KHIGHMEM_BEG, AIMG_HI in ABR'. idtac.
    lstep; if_lia. (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    lstep. do 7 lstep. lstep. lstep. (* [comment removed for export] *)
    try rewrite unsigned_lit in * by lia. try rewrite Z_to_bv_bv_unsigned.
    apply evt_done. apply lscps_done. unfold amalloc_nn_post.
    (nelim JK 3%nat; intros uj JK1 JK2).
    nexists 14%nat. exists m4, errv, (st_trs st4), r, uj. split; [reflexivity|]. split; [exact MI4|].
    split.
    { eapply stk_merge; [exact ST4| | lia]. replace (bv_unsigned sp) with (bv_unsigned sp + -2144 + 2144) at 2 by lia.
      apply stk_of_wr_high; [exact WR3| unfold AIMG_HI; lia]. }
    split; [exact ERR4|].
    split; [exact CP04|].
    split; [exact GM4|]. split; [rewrite <- Etrs; exact TP4|].
    split; [exact RNZ|]. split; [exact ABR|]. split; [rewrite <- Elb; exact NIN|]. split; [rewrite <- Elf; exact NFR|].
    split; [exact ART4|]. split; [| exact JK1].
    (* [comment removed for export] *)
    destruct (bprim n) eqn:HPn; [left; apply HPK; exact HPn|].
    pose proof (adrvd_use _ _ _ _ st HDRV HR0 WF) as FX.
    pose proof (ltac:(first [exact (BLK4 HPn)| exact (BLK4 eq_refl)])) as BLK.
    (nelim BLK 39%nat; intros u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 m4' st4' EQ _ r' _ RTS4' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ EREG ECCH).
    apply (f_equal ms_mem) in EQ. cbn [MS ms_mem] in EQ. subst m4'.
    (nelim RTS4' 3%nat; intros HR4' WF4' _).
    apply (adrvd_keep kd m4 mo4 g4 st4' HR4' WF4'). intros c Hc H24. specialize (FX c Hc H24).
    unfold fresh_cls, rg, cch in *. rewrite EREG, ECCH. exact FX.
Qed.
End MALLOCN.

End CeilWrap.
