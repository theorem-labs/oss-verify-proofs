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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LRz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require BImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_rep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_cost.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_quarantine_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_sec_dstateP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_leaves_memset.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_q_drainw.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_p_abs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_m_tpz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_m_apz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_m_pop.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_q_wf2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_q_zone.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_q_wf3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_sec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
Module RTW_q_enq.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Exec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_quarantine_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstateP.RT_trans.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drainw.RTW_m_a1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_abs.RTW_m_lib3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_tpz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_apz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_pop OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_wf2.RTW_m_c1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstateP.RTW_m_live OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstateP.RTW_q_trans OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_wf2.RTW_q_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_zone OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_wf3.RTW_q_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_wf3.RTW_q_enqw OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_wf3.RTW_q_enq2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_wf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_sec.RTW_q_needs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.ABand.
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

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma snoc_or_nil : forall {X} (l : list X), l = [] \/ exists q x, l = q ++ [x].
Proof.
  intros X l. destruct l as [|y l']; [left; reflexivity| right].
  destruct (exists_last (l := y :: l') ltac:(discriminate)) as (q & x & E). exists q, x. exact E. (* [comment removed for export] *)
Qed.

Lemma live_bytes_nonneg : forall l, 0 <= live_bytes l.
Proof. induction l as [|[a sz] l IH]; cbn; [lia|]. pose proof (bv_unsigned_in_range 64 sz). lia. Qed.

Lemma g_res_le_limit : forall st mo g, BINV mo g -> RTMODEL st mo -> g_res g <= 2^39.
Proof.
  intros st mo g (_ & _ & HB) HM. (nelim HM 9%nat; intros _ _ _ _ _ _ _ M8 _).
  rewrite M8 in HB. unfold target_alloc_limit in HB. pose proof (npages_nonneg (g_win g)).
  unfold eager_used in HB. pose proof (live_bytes_nonneg (maps_subtract_all (vm_backed_maps (m_vmmaps mo)) (m_vm_lazy mo))). lia.
Qed.

Lemma errno_notin_primary_fp_fine : forall st c a, RTWF st -> 0 <= c < KNUMCLASSES -> AERRNO <= a < AERRNO + 4 -> ~ in_ivs (primary_fp_fine st c) a.
Proof.
  intros st c a WF Hc Ha nelH_; (nelim nelH_ 4%nat; intros lo hi Hin Hr). unfold primary_fp_fine, fp_class_fine, fp_tpage in Hin.
  pose proof (region_facts st WF c Hc) as RF. cbn zeta in RF. (nelim RF 7%nat; intros Y1 Y2 Y3 Y4 Y5 Y6 _).
  pose proof (t_range st WF) as TR. pose proof (ris_range st WF) as RR.
  pose proof (rt_SH_bounds (rbeg st c + r_mapped (rg st c)) ltac:(unfold KHIGHMEM_BEG, AIMG_HI, KREGIONSIZE, PRIM_RES_SIZE, KFREEARRAY_OFF in *; lia)) as SB.
  rewrite !in_app_iff in Hin. cbn [In] in Hin. unfold AERRNO, ATP, KHIGHMEM_BEG, AIMG_HI, rinfo in *.
  destruct Hin as [[E|[E|[E|[]]]]|[E|[]]]; injection E as <- <-; blia.
Qed.

(* [comment removed for export] *)
Lemma blk_shadow_notin_fine : forall st st2 A n a, RTWF st -> RTWF st2 -> In (A, n) (all_blocks st) -> bprim n = true ->
  SH (b_lo A n) <= a < SH (b_lo A n) + sh_tot n -> ~ in_ivs (primary_fp_fine st 24 ++ fp_emb st2) a.
Proof.
  intros st st2 A n a WF WF2 HB HP Ha nelH_; (nelim nelH_ 4%nat; intros lo hi Hin Hr).
  (nelimp (block_geom st WF A n HB) 11%nat; intros Gn GA K X Y CE L16 H16 EA Gp Gs). unfold usz in Y.
  (nelim (Gp HP) 6%nat; intros Hcl RB RE _ _ BH). cbn zeta in *.
  assert (H24 : 0 <= 24 < KNUMCLASSES) by (unfold KNUMCLASSES; lia).
  pose proof (region_facts st WF 24 H24) as RF. cbn zeta in RF. (nelim RF 10%nat; intros Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 Y9 Y10).
  pose proof (region_facts st WF (pclass n) ltac:(unfold KNUMCLASSES; lia)) as RF. cbn zeta in RF. (nelim RF 10%nat; intros Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 Z10).
  assert (L8 : b_lo A n mod 8 = 0) by (apply (mod0_trans _ 8 16); [lia|lia|reflexivity|exact L16]).
  assert (EH : SH (b_lo A n) + sh_tot n = SH (b_hi A n)).
  { unfold sh_tot. rewrite <- (rt_SH_aligned_add (b_lo A n) (asz n) L8). reflexivity. }
  rewrite EH in Ha.
  pose proof (rt_SH_bounds (b_lo A n) ltac:(unfold KHIGHMEM_BEG, AIMG_HI in *; (lia_on X Y CE RB Y1 Y5 Z1 Z5))) as SB1.
  pose proof (rt_SH_bounds (b_hi A n) ltac:(unfold KHIGHMEM_BEG, AIMG_HI in *; (lia_on X Y CE RB RE Y1 Y5 Z1 Z5))) as SB2.
  pose proof (t_range st WF) as TR. pose proof (ris_range st WF) as RR.
  unfold primary_fp_fine, fp_class_fine, fp_tpage, fp_emb in Hin. rewrite !in_app_iff in Hin. cbn [In] in Hin. unfold rinfo in Hin.
  destruct Hin as [[[E|[E|[E|[]]]]|[E|[]]]|[E|Hin]]; try (injection E as <- <-).
  - unfold KHIGHMEM_BEG, AIMG_HI in *. (lia_on Ha Hr X Y RB RE Y1 Y5 Z1 Z5 SB2).
  - (* [comment removed for export] *)
    destruct (Z.lt_trichotomy (pclass n) 24) as [LT|[EQ|GT]].
    + pose proof (rt_SH_mono (b_hi A n) (rbeg st 24 + r_mapped (rg st 24))) as M.
      rewrite (rbeg_val st (pclass n)) in *. rewrite (rbeg_val st 24) in *. unfold KREGIONSIZE, KFREEARRAY_OFF in *. (cut_on [Ha Hr X Y H16 EA RB RE Y5 Y8 Y10 Z5 Z6 Z10 L8 LT M] nia).
    + rewrite EQ in *. pose proof (rt_SH_mono (b_hi A n) (rbeg st 24 + r_mapped (rg st 24)) ltac:(lia)). (lia_on Ha Hr X Y RB RE Y5 H).
    + pose proof (rt_SH_mono (rbeg st 24 + KREGIONSIZE) (b_lo A n)) as M. rewrite (rt_SH_aligned_add (rbeg st 24) KREGIONSIZE Y8) in M.
      rewrite (rbeg_val st (pclass n)) in *. rewrite (rbeg_val st 24) in *. unfold KREGIONSIZE, KFREEARRAY_OFF in *.
      change (2 ^ 32 / 8) with 536870912 in M. (cut_on [Ha Hr X Y H16 EA RB RE Y5 Y8 Y10 Z5 Z10 L8 GT M] nia).
  - unfold KHIGHMEM_BEG, AIMG_HI in *. lia.
  - unfold KHIGHMEM_BEG, AIMG_HI in *. (cut_on [Ha Hr K X Y RB RE Y1 Y5 Z1 Z5 SB1 SB2 TR] blia).
  - unfold A_EMB, KHIGHMEM_BEG, AIMG_HI in *. lia.
  - destruct (Z.eqb_spec (emb_d st2) 0) as [E0|NE]; [destruct Hin|]. destruct Hin as [E|[]]. injection E as <- <-.
    pose proof (emb_block_range st2 WF2 NE) as (R1 & _). unfold KHIGHMEM_BEG, AIMG_HI in *. (cut_on [Ha Hr K X Y RB RE Y1 Y5 Z1 Z5 SB1 SB2 R1] blia).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AENQ_STACK : Z := 64 + AREFILL_STACK.

Definition enq_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : rtstate) (A n lo : Z) (m : word -> option byte) (g : lghost) : machine_state -> Model -> lghost -> Prop :=
  rt_post_std ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
    (fun _ m' st' mo' g' =>
        enq_rel st st' A n
        /\ RTREP st' m' /\ RTWFq st' /\ RTMODEL st' mo' /\ GWIN st' m' mo' g' /\ FRONTR mo' (g_res g') /\ SWIN st' g'
        /\ stk bsegs m' lo (bv_unsigned sp)
        /\ cli_pres st (bv_unsigned sp) m m' /\ errno_same m m'
        /\ gmono g g' /\ budget_ok st g st' g' (fp n)).

Section ENQ.
Hypothesis refill_spin : refill_spec_spin.

(* [comment removed for export] *)
Lemma enq_newbatch :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (j0 : list byte) (vs5 vs4 vs3 vs2 vs1 vs0 vra : word)
         (F : bvmap 5 word) (fc : bv 32) (m0 mA : word -> option byte) (mo : Model) (g : lghost)
         (st : rtstate) (A n S lo : Z) (spo : word),
  bv_unsigned spo = bv_unsigned sp + 64 ->
  RTREP st mA -> RTWF st -> RTMODEL st mo -> GWIN st mA mo g -> FRONTR mo (g_res g) -> SWIN st g ->
  In (A, n) (st_qpend st) -> st_apend st = [] ->
  (st_qthread st = [] \/ exists q l, st_qthread st = q ++ [l] /\ qb_count l = QBATCH_CAP) ->
  (bprim n = true -> rw_cells bsegs mA (SH (b_lo A n)) (zcells (sh_quar n))) ->
  a0 = wz (qcache_t st) -> a1 = wz (acache st) -> a2 = wz S -> a3 = wz (b_chunk_beg A) -> a4 = wz (usz n) -> tp = wz ATP ->
  rt_prov st + fp n <= g_res g ->
  stk bsegs mA lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - AREFILL_STACK -> bv_unsigned sp + 64 < 2^64 ->
  bv_unsigned sp + 64 <= st_sp0 st ->
  mem_inv bsegs mA ->
  rw_cells bsegs mA (bv_unsigned sp) (enq_frame j0 vs5 vs4 vs3 vs2 vs1 vs0 vra) ->
  cli_pres st (bv_unsigned sp + 64) m0 mA -> errno_same m0 mA ->
  LSCPS bsegs (enq_post vra spo gp tp vs0 vs1 vs2 vs3 vs4 vs5 s6 s7 s8 s9 s10 s11 F fc st A n lo m0 g)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz 0x36414) fc None mA (seg_rom bsegs)) mo g.
Proof.
  intros until spo. intros Hspo HR WF HM HG HFR HSW HIN HAP CASE SHQ -> -> -> -> -> TP HRES ST HCL LO SPH SPB MI FR CP0 ES0.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. idtac. unfold AREFILL_STACK in LO.
  apply lscps_assume. intros NWX HO HB.
  assert (Hc24 : 0 <= 24 < KNUMCLASSES) by (unfold KNUMCLASSES; lia).
  assert (HBA : In (A, n) (all_blocks st)) by (unfold all_blocks; rewrite !in_app_iff; right; right; exact HIN).
  pose proof (block_geom st WF A n HBA) as (Gn & _).
  pose proof (t_range st WF) as TR.
  (* [comment removed for export] *)
  destruct (rr_cache st mA HR 24 Hc24) as [PC _].
  replace (pcaddr st 24) with (acache st + 1920) in PC by (unfold pcaddr; lia).
  pose proof (wc_cache_max st 24 (wf_class_ok st WF 24 Hc24)) as CM. change (cmaxcount 24) with 2 in CM. pose proof (zlen_nonneg (cch st 24)) as CZ.
  eapply lscps_step_evt. cbv beta delta [wz] in *. unfold ATP in *. subst tp.
  lstep. (* [comment removed for export] *) rewrite (sx32_lit (zlen (cch st 24))) by lia.
  destruct (snoc_or_nil (cch st 24)) as [HC0|(pre & k & HC)].
  - (* [comment removed for export] *)
    rewrite HC0. change (zlen (@nil Z)) with 0.
    lstep; if_lia. (* [comment removed for export] *)
    do 12 lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    apply evt_done. eapply lscps_bind.
    { pose proof refill_spin as RP. unfold refill_spec_spin in RP.
      eapply RP with (st := st) (cls := 24) (lo := lo); try reflexivity.
      - exact (RTS_intro _ _ _ _ HR WF HM HG HFR HSW).
      - lia.
      - exact HC0.
      - intros HN. apply (class24_populate_ok st WF); [| exact HN]. pose proof (g_res_le_limit st mo g HB HM). pose proof (fp_nonneg n ltac:(lia)). lia.
      - pose proof (fp_nonneg n ltac:(lia)). lia.
      - exact ST.
      - idtac; lia.
      - unfold AREFILL_STACK. lia.
      - exact MI.
      - (* [comment removed for export] *)
        intros ms' R0. (nelim R0 23%nat; intros u0 u1 u2 w1 w2 w3 w4 w5 w6 w7 u3 u4 u5 u6 m' st' -> MI' RR' HR' WF' ST' RF').
        destruct (rtrep_spin_cells st' m' HR') as [GS DY].
        replace (ret_pc (Z_to_bv 64 222512)) with (Z_to_bv 64 222512) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        eapply enq_spin_spec; [exact MI'| reflexivity| exact GS| exact DY]. }
    cbv beta. intros ms2 mo2 g2 PO.
    (nelim PO 27%nat; intros u0 u1 u2 a0' w1 w2 w3 w4 w5 w6 w7 u3 u4 u5 u6 m2 st2 -> MI2 -> RR RTS2 ST2 CP2 RF2 GM2 BO2).
    replace (ret_pc (Z_to_bv 64 222512)) with (Z_to_bv 64 222512) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (nelim RTS2 6%nat; intros HR2 WF2 HM2 HG2 HF2 HSW2).
    pose proof RR as RR0. (nelim RR 5%nat; intros SBP AP2 CI2 OTH RES).
    (nelim SBP 24%nat; intros P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P20 P21 P22 P23 P24).
    destruct RES as [[_ LEN1]|[X _]]; [| discriminate].
    change (nrefill 24) with 1 in LEN1.
    assert (exists k, cch st2 24 = [k]) as [k HC2].
    { destruct (cch st2 24) as [|k0 [|k1 l1]]; [cbn in LEN1; unfold zlen in LEN1; cbn in LEN1; lia| exists k0; reflexivity|].
      rewrite !zlen_cons in LEN1. pose proof (zlen_nonneg l1). lia. }
    assert (HAP2 : st_apend st2 = []) by (rewrite AP2; exact HAP).
    assert (HIN2 : In (A, n) (st_qpend st2)) by (rewrite P22; exact HIN).
    assert (EQT : st_qthread st2 = st_qthread st) by exact P7.
    assert (CASE2 : st_qthread st2 = [] \/ exists q l, st_qthread st2 = q ++ [l] /\ qb_count l = QBATCH_CAP) by (rewrite EQT; exact CASE).
    assert (CP02 : cli_pres st (bv_unsigned sp + 64) m0 m2).
    { unfold cli_pres in *. eapply cj_pres_trans; [exact CP0|]. eapply cj_pres_weaken; [exact CP2| lia| auto| auto]. }
    assert (ES02 : errno_same m0 m2).
    { eapply errno_same_trans; [exact ES0|]. eapply errno_same_rt_frame; [exact RF2| unfold AERRNO, ATP; lia|].
      intros a Ha. apply notin_ivs_app; [apply (errno_notin_primary_fp_fine st 24 a WF Hc24 Ha)| apply (errno_notin_fp_emb st2 a WF2 Ha)]. }
    assert (FR2 : rw_cells bsegs m2 (bv_unsigned sp) (enq_frame j0 vs5 vs4 vs3 vs2 vs1 vs0 vra)).
    { eapply (cj_pres_rw_cells _ _ _ _ _ _ _ _ CP2); [exact FR|]. left. cbn. lia. }
    assert (SHQ2 : bprim n = true -> rw_cells bsegs m2 (SH (b_lo A n)) (zcells (sh_quar n))).
    { intros EP. (nelim (proj2 (rr_quar st2 m2 HR2) A n HIN2) 5%nat; intros _ _ _ _ VSH). unfold R_bshadow in VSH. rewrite EP in VSH.
      (nelimp (block_geom st WF A n HBA) 8%nat; intros _ _ K X Y CE L16 _). unfold usz in Y.
      assert (L8 : b_lo A n mod 8 = 0) by (apply (mod0_trans _ 8 16); [lia|lia|reflexivity|exact L16]).
      pose proof (rt_SH_bounds (b_lo A n) ltac:(unfold KHIGHMEM_BEG, AIMG_HI in *; blia)) as SB1.
      assert (EH : SH (b_lo A n) + sh_tot n = SH (b_hi A n)) by (unfold sh_tot; rewrite <- (rt_SH_aligned_add (b_lo A n) (asz n) L8); reflexivity).
      pose proof (rt_SH_bounds (b_hi A n) ltac:(unfold b_hi, KHIGHMEM_BEG, AIMG_HI in *; blia)) as SB2.
      replace (b_lo A n) with (b_lo A n) in VSH by reflexivity.
      eapply (rw_cells_rt_frame _ lo (bv_unsigned sp) mA m2 (SH (b_lo A n)) (zcells (sh_quar n)));
        [exact RF2| exact (SHQ EP)| destruct st, st2; exact VSH| lia| rewrite zcells_size, sh_quar_len by lia; lia| rewrite EH; unfold KHIGHMEM_BEG, AIMG_HI in *; lia|].
      intros a Ha. rewrite zcells_size, sh_quar_len in Ha by lia. split; [rewrite EH in Ha; unfold KHIGHMEM_BEG, AIMG_HI in *; lia|].
      apply (blk_shadow_notin_fine st st2 A n a WF WF2 HBA EP Ha). }
    clear ST FR.
    (* [comment removed for export] *)
    destruct (rr_cache st2 m2 HR2 24 Hc24) as [PC2 _].
    replace (pcaddr st2 24) with (acache st + 1920) in PC2 by (unfold pcaddr, acache; rewrite P15; lia). rewrite LEN1 in PC2.
    apply lscps_assume. intros _ HO2 HB2.
    eapply lscps_step_evt. cbv beta delta [wz].
    lstep. (* [comment removed for export] *)
    lstep; if_lia. (* [comment removed for export] *)
    lstep. lstep. lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *) cbv beta delta [wz]. rewrite (sx32_lit 1) by lia.
    lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    set (pre := @nil Z).
    eapply evt_cut.
    { destruct CASE2 as [HQE|(q & l & HQN & HFULL)].
      - eapply enq_t2_full_e with (st := st2) (pre := pre) (k := k) (A := A) (n := n) (lo := lo);
          [exact HR2| exact WF2| exact MI2| subst pre; exact HC2| exact HAP2| exact HIN2| exact HQE| exact SHQ2
          | unfold qcache_t; rewrite P15; reflexivity| unfold acache; rewrite P15; reflexivity| reflexivity| reflexivity| subst pre; reflexivity
          | exact ST2| idtac; lia| lia| lia| exact FR2].
      - eapply (enq_t2_full_n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j0 vs5 vs4 vs3 vs2 vs1 vs0 vra F fc m2 st2 pre k A n lo q l HFULL);
          [exact HR2| exact WF2| exact MI2| subst pre; exact HC2| exact HAP2| exact HIN2| exact HQN| exact SHQ2
          | unfold qcache_t; rewrite P15; reflexivity| unfold acache; rewrite P15; reflexivity| reflexivity| reflexivity| subst pre; reflexivity
          | exact ST2| idtac; lia| lia| lia| exact FR2]. }
    assert (HC2' : cch st2 24 = pre ++ [k]) by (subst pre; exact HC2).
    pose proof CP02 as CP0X. pose proof ES02 as ES0X. pose proof GM2 as GMX.
    cbv beta. intros ms3 PO. (nelim PO 16%nat; intros a1' a2' a4' a5' a6' m3 W3 -> MU3 WM3 MI3 HW3 ST3 CP3 ES3 HR3).
    apply evt_done. apply lscps_assume. intros _ HO3 HB3. apply lscps_done.
    assert (CP3' : cli_pres st (bv_unsigned sp + 64) m2 m3) by (unfold cli_pres in *; rewrite P1, P20, P14 in CP3; exact CP3).
    set (st' := st_enq_new (st_pop st2 24 k pre) k A n) in *.
    assert (WFP : RTWF (st_pop st2 24 k pre)) by (apply RTWF_pop'; [exact WF2| lia| exact HC2'| exact HAP2]).
    assert (HKP : In (24, k) (st_apend (st_pop st2 24 k pre))).
    { (nelim (st_pop_same st2 24 k pre) 6%nat; intros _ _ _ _ E5 _). rewrite E5. left. reflexivity. }
    assert (HINP : In (A, n) (st_qpend (st_pop st2 24 k pre))).
    { (nelim (st_pop_same st2 24 k pre) 9%nat; intros _ _ _ _ _ _ _ E8 _). rewrite E8. exact HIN2. }
    assert (FULLP : st_qthread (st_pop st2 24 k pre) = [] \/ thread_room (st_pop st2 24 k pre) = 0).
    { (nelim (st_pop_same st2 24 k pre) 12%nat; intros _ _ _ _ _ _ _ _ _ _ E11 _). unfold thread_room. rewrite E11. try rewrite EQT.
      destruct CASE as [E|(q & l & E & HF')]; [left; exact E| right]. rewrite E. destruct (q ++ [l]) eqn:E2; [destruct q; discriminate|]. rewrite <- E2, last_last. lia. }
    unfold enq_post, rt_post_std.
    replace spo with (Z_to_bv 64 (bv_unsigned sp + 64)) by (rewrite <- Hspo; apply Z_to_bv_bv_unsigned).
    rewrite (unsigned_lit (bv_unsigned sp + 64)) by lia. nexists 15%nat. exists m3, st'.
    split; [reflexivity|]. split; [exact MI3|].
    split; [subst st'; apply (enq_rel_new st st2 pre k A n); [left; exact RR0| exact HAP| exact HC2']|].
    split; [exact HR3|].
    split; [subst st'; apply RTWFq_enq_new'; [apply RTWFq_of; exact WFP| exact HINP| exact HKP| lia]|].
    split; [subst st'; apply RTMODEL_enq_new'; apply RTMODEL_pop'; exact HM2|].
    split; [subst st'; apply GWIN_enq_new'; apply GWIN_pop'; eapply GWIN_mem; [exact HG2| exact HO3| exact WM3]|].
    split; [exact HF2|].
    split; [subst st'; apply SWIN_enq_new'; apply SWIN_pop'; exact HSW2|].
    split; [exact ST3|].
    split; [unfold cli_pres in *; eapply cj_pres_trans; [exact CP0X| exact CP3']|].
    split; [eapply errno_same_trans; [exact ES0X| exact ES3]|].
    split; [exact GMX|].
    pose proof (rt_prov_pop' st2 24 k pre WF2 ltac:(lia) HC2' HAP2) as PV1.
    pose proof (rt_prov_enq_new' (st_pop st2 24 k pre) k A n (RTWFq_of _ WFP) HINP HKP ltac:(lia) FULLP) as PV2. fold st' in PV2.
    unfold budget_ok in *. lia.
  - (* [comment removed for export] *)
    rewrite HC. rewrite zlen_app, zlen_cons, zlen_nil. replace (zlen pre + (1 + 0)) with (zlen pre + 1) by lia. pose proof (zlen_nonneg pre) as PZ.
    assert (PB : zlen pre + 1 <= 2) by (rewrite HC, zlen_app, zlen_cons, zlen_nil in CM; lia).
    lstep; if_lia. (* [comment removed for export] *)
    assert (EQT : st_qthread st = st_qthread st) by reflexivity.
    eapply evt_cut.
    { destruct CASE as [HQE|(q & l & HQN & HFULL)].
      - eapply enq_t2_full_e with (st := st) (pre := pre) (k := k) (A := A) (n := n) (lo := lo);
          [exact HR| exact WF| exact MI| exact HC| exact HAP| exact HIN| exact HQE| exact SHQ
          | reflexivity| reflexivity| reflexivity| reflexivity| reflexivity
          | exact ST| idtac; lia| lia| lia| exact FR].
      - eapply (enq_t2_full_n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j0 vs5 vs4 vs3 vs2 vs1 vs0 vra F fc mA st pre k A n lo q l HFULL);
          [exact HR| exact WF| exact MI| exact HC| exact HAP| exact HIN| exact HQN| exact SHQ
          | reflexivity| reflexivity| reflexivity| reflexivity| reflexivity
          | exact ST| idtac; lia| lia| lia| exact FR]. }
    pose proof CP0 as CP0X. pose proof ES0 as ES0X. assert (GMX : gmono g g) by (intros w Hw; exact Hw).
    cbv beta. intros ms3 PO. (nelim PO 16%nat; intros a1' a2' a4' a5' a6' m3 W3 -> MU3 WM3 MI3 HW3 ST3 CP3 ES3 HR3).
    apply evt_done. apply lscps_assume. intros _ HO3 HB3. apply lscps_done.
    assert (CP3' : cli_pres st (bv_unsigned sp + 64) mA m3) by exact CP3.
    set (st' := st_enq_new (st_pop st 24 k pre) k A n) in *.
    assert (WFP : RTWF (st_pop st 24 k pre)) by (apply RTWF_pop'; [exact WF| lia| exact HC| exact HAP]).
    assert (HKP : In (24, k) (st_apend (st_pop st 24 k pre))).
    { (nelim (st_pop_same st 24 k pre) 6%nat; intros _ _ _ _ E5 _). rewrite E5. left. reflexivity. }
    assert (HINP : In (A, n) (st_qpend (st_pop st 24 k pre))).
    { (nelim (st_pop_same st 24 k pre) 9%nat; intros _ _ _ _ _ _ _ E8 _). rewrite E8. exact HIN. }
    assert (FULLP : st_qthread (st_pop st 24 k pre) = [] \/ thread_room (st_pop st 24 k pre) = 0).
    { (nelim (st_pop_same st 24 k pre) 12%nat; intros _ _ _ _ _ _ _ _ _ _ E11 _). unfold thread_room. rewrite E11. try rewrite EQT.
      destruct CASE as [E|(q & l & E & HF')]; [left; exact E| right]. rewrite E. destruct (q ++ [l]) eqn:E2; [destruct q; discriminate|]. rewrite <- E2, last_last. lia. }
    unfold enq_post, rt_post_std.
    replace spo with (Z_to_bv 64 (bv_unsigned sp + 64)) by (rewrite <- Hspo; apply Z_to_bv_bv_unsigned).
    rewrite (unsigned_lit (bv_unsigned sp + 64)) by lia. nexists 15%nat. exists m3, st'.
    split; [reflexivity|]. split; [exact MI3|].
    split; [subst st'; apply (enq_rel_new st st pre k A n); [right; reflexivity| exact HAP| exact HC]|].
    split; [exact HR3|].
    split; [subst st'; apply RTWFq_enq_new'; [apply RTWFq_of; exact WFP| exact HINP| exact HKP| lia]|].
    split; [subst st'; apply RTMODEL_enq_new'; apply RTMODEL_pop'; exact HM|].
    split; [subst st'; apply GWIN_enq_new'; apply GWIN_pop'; eapply GWIN_mem; [exact HG| exact HO3| exact WM3]|].
    split; [exact HFR|].
    split; [subst st'; apply SWIN_enq_new'; apply SWIN_pop'; exact HSW|].
    split; [exact ST3|].
    split; [unfold cli_pres in *; eapply cj_pres_trans; [exact CP0X| exact CP3']|].
    split; [eapply errno_same_trans; [exact ES0X| exact ES3]|].
    split; [exact GMX|].
    pose proof (rt_prov_pop' st 24 k pre WF ltac:(lia) HC HAP) as PV1.
    pose proof (rt_prov_enq_new' (st_pop st 24 k pre) k A n (RTWFq_of _ WFP) HINP HKP ltac:(lia) FULLP) as PV2. fold st' in PV2.
    unfold budget_ok in *. lia.
Qed.

(* [comment removed for export] *)
Definition enqueue_spec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (st : rtstate) (A n S lo : Z),
  RTS st m mo g -> In (A, n) (st_qpend st) -> st_apend st = [] ->
  (bprim n = true -> rw_cells bsegs m (SH (b_lo A n)) (zcells (sh_quar n))) ->
  a0 = wz (qcache_t st) -> a1 = wz (acache st) -> a2 = wz S -> a3 = wz (b_chunk_beg A) -> a4 = wz (usz n) -> tp = wz ATP ->
  rt_prov st + fp n <= g_res g ->
  bv_unsigned sp <= st_sp0 st ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - AENQ_STACK -> mem_inv bsegs m ->
  LSCPS bsegs (enq_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st A n lo m g)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz AQENQ) fc None m (seg_rom bsegs)) mo g.

Theorem enqueue_proof : enqueue_spec.
Proof.
  unfold enqueue_spec. intros until lo. intros (HR & WF & HM & HG & HFR & HSW) HIN HAP SHQ -> -> -> -> -> TP HRES SPB ST HCL LO MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. idtac. unfold AENQ_STACK, AREFILL_STACK in LO.
  apply lscps_assume. intros NWX HO HB.
  assert (Hc24 : 0 <= 24 < KNUMCLASSES) by (unfold KNUMCLASSES; lia).
  assert (HBA : In (A, n) (all_blocks st)) by (unfold all_blocks; rewrite !in_app_iff; right; right; exact HIN).
  (nelimp (block_geom st WF A n HBA) 8%nat; intros Gn GA K X Y CE L16 _). unfold usz in Y.
  assert (L8 : b_lo A n mod 8 = 0) by (apply (mod0_trans _ 8 16); [lia|lia|reflexivity|exact L16]).
  pose proof (t_range st WF) as TR.
  (* [comment removed for export] *)
  eapply lscps_step_evt. cbv beta delta [wz] in *. unfold AQENQ, ATP in *. subst tp.
  eapply evt_cut; [eapply (enq_pro_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m lo); [exact MI| exact ST| idtac; lia| lia]|].
  cbv beta. intros ms1 nelH_; (nelim nelH_ 8%nat; intros j0 mA -> MUA WMA MIA STA FRA). cbv beta delta [wz].
  assert (HRA : RTREP st mA).
  { eapply (RTREP_high st _ m mA WF); [| exact MUA| exact WMA| exact HR]. constructor; [cbn; lia| constructor]. }
  assert (HGA : GWIN st mA mo g) by (eapply GWIN_mem; [exact HG| exact HO| exact WMA]).
  assert (CP0 : cli_pres st (bv_unsigned sp) m mA).
  { eapply (cli_pres_tpz st WF (bv_unsigned sp) ltac:(unfold CEIL; lia)); [exact MUA| exact WMA|]. constructor; [| constructor]. cbn [fst snd]. right. unfold CEIL. lia. }
  assert (ES0 : errno_same m mA).
  { eapply errno_same_munch; [exact MUA|]. constructor; [| constructor]. cbn [fst snd]. left. unfold AERRNO, ATP. lia. }
  assert (SHQA : bprim n = true -> rw_cells bsegs mA (SH (b_lo A n)) (zcells (sh_quar n))).
  { intros EP. eapply rw_cells_transport; [exact (SHQ EP)| exact MUA| exact WMA|]. rewrite zcells_size, sh_quar_len by lia.
    unfold sh_tot. cbn. rewrite <- (rt_SH_aligned_add (b_lo A n) (asz n) L8).
    pose proof (rt_SH_bounds (b_lo A n + asz n) ltac:(unfold b_hi, KHIGHMEM_BEG, AIMG_HI in *; blia)). unfold KHIGHMEM_BEG, AIMG_HI in *. lia. }
  clear MUA ST MI SHQ.
  (nelimp (rr_thread st mA HRA) 4%nat; intros _ _ QC _).
  (nelim (qthread_facts st mA HRA WF) 4%nat; intros QF1 QF2 QF3 QF4).
  assert (NT : (4096 <= qcache_t st - 80 /\ (qcache_t st + 4016 <= 65536 \/ 6287360 <= qcache_t st - 80)) /\ qcache_t st + 32 <= alloc_ceiling) by   (* [comment removed for export] *)
    (clear - TR; unfold qcache_t, T_QCACHE, AIMG_HI, KHIGHMEM_BEG in *; blia).
  destruct (snoc_or_nil (st_qthread st)) as [HQE|(q & b & HQ)].
  - (* [comment removed for export] *)
    rewrite HQE in QC. cbn [qc_first qc_last qc_bytes fold_right] in QC. change (zlen (@nil qbatch)) with 0 in QC. cbv beta delta [wz] in QC.
    lstep. (* [comment removed for export] *)
    lstep; if_lia. (* [comment removed for export] *)
    apply evt_done.
    eapply enq_newbatch with (m0 := m) (st := st) (A := A) (n := n) (S := S) (lo := lo) (spo := sp);
      [rewrite unsigned_lit by lia; lia| exact HRA| exact WF| exact HM| exact HGA| exact HFR| exact HSW| exact HIN| exact HAP
      | left; exact HQE| exact SHQA| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| exact HRES
      | rewrite unsigned_lit by lia; exact STA| idtac; lia| rewrite unsigned_lit by lia; unfold AREFILL_STACK; lia
      | rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; lia| exact MIA
      | rewrite unsigned_lit by lia; exact FRA
      | rewrite unsigned_lit by lia; replace (bv_unsigned sp - 64 + 64) with (bv_unsigned sp) by lia; exact CP0
      | exact ES0].
  - assert (Hb : In b (qall st)) by (unfold qall; rewrite HQ, !in_app_iff; left; right; left; reflexivity).
    pose proof (wq_batch st (wf_quar_ok st WF) b Hb) as [CNT _].
    rewrite HQ in QC. rewrite zlen_app, qc_last_snoc in QC. change (zlen [b]) with 1 in QC.
    rewrite HQ in QF1, QF2. rewrite zlen_app in QF1. change (zlen [b]) with 1 in QF1. pose proof (zlen_nonneg q) as ZQ.
    destruct (Z.eq_dec (qb_count b) QBATCH_CAP) as [FULL|ROOM].
    + (* [comment removed for export] *)
      destruct (proj1 (R_qlist_iff mA (st_qthread st)) (proj1 (rr_batches st mA HRA)) q b [] HQ) as [LB _]. cbn [qc_first] in LB.
      (nelimp (batch_geom st WF b Hb) 5%nat; intros _ _ BG1 BG2 _).
      pose proof (region_facts st WF 24 Hc24) as RF. cbn zeta in RF. (nelim RF 7%nat; intros Y1 Y2 Y3 Y4 Y5 Y6 _).
      assert (NBb : 17594333495296 <= qb_addr b /\ qb_addr b + 8192 <= alloc_ceiling)
        by (clear - BG1 BG2 Y1 Y2 Y3 Y4 Y5 Y6; unfold KHIGHMEM_BEG, AIMG_HI, QBATCH_SIZE, KREGIONSIZE, KFREEARRAY_OFF, PRIM_RES_SIZE in *; lia).
      rewrite FULL in LB. unfold QBATCH_CAP in LB. cbv beta delta [wz] in QC, LB.
      lstep. (* [comment removed for export] *)
      lstep; if_lia. (* [comment removed for export] *)
      lstep. (* [comment removed for export] *)
      lstep. (* [comment removed for export] *)
      lstep. (* [comment removed for export] *)
      lstep; if_lia. (* [comment removed for export] *)
      apply evt_done.
      eapply enq_newbatch with (m0 := m) (st := st) (A := A) (n := n) (S := S) (lo := lo) (spo := sp);
        [rewrite unsigned_lit by lia; lia| exact HRA| exact WF| exact HM| exact HGA| exact HFR| exact HSW| exact HIN| exact HAP
        | right; exists q, b; split; [exact HQ| exact FULL]| exact SHQA| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| exact HRES
        | rewrite unsigned_lit by lia; exact STA| idtac; lia| rewrite unsigned_lit by lia; unfold AREFILL_STACK; lia
        | rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; lia| exact MIA
        | rewrite unsigned_lit by lia; exact FRA
        | rewrite unsigned_lit by lia; replace (bv_unsigned sp - 64 + 64) with (bv_unsigned sp) by lia; exact CP0
        | exact ES0].
    + (* [comment removed for export] *)
      assert (ROOM' : qb_count b < QBATCH_CAP) by (unfold QBATCH_CAP in *; lia).
      eapply evt_cut.
      { eapply enq_t1_full with (st := st) (q := q) (b := b) (A := A) (n := n) (lo := lo);
          [exact HRA| exact WF| exact MIA| exact HQ| exact ROOM| exact HIN| exact SHQA| reflexivity| reflexivity| reflexivity
          | rewrite unsigned_lit by lia; exact STA| idtac; lia| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; lia
          | rewrite unsigned_lit by lia; exact FRA]. }
      cbv beta. intros ms2 PO. (nelim PO 14%nat; intros a1' a2' a5' a6' a7' m2 -> MU2 WM2 MI2 ST2 CP2 ES2 HR2).
      rewrite (unsigned_lit (bv_unsigned sp - 64)) in * by lia. replace (bv_unsigned sp - 64 + 64) with (bv_unsigned sp) in * by lia. cbv beta delta [wz]. rewrite Z_to_bv_bv_unsigned.
      apply evt_done. apply lscps_done.
      set (st' := st_enq_last st A n) in *.
      unfold enq_post, rt_post_std. nexists 15%nat. exists m2, st'.
      split; [reflexivity|]. split; [exact MI2|].
      split; [subst st'; apply (enq_rel_last st q b A n HQ)|].
      split; [exact HR2|].
      split; [subst st'; apply (RTWFq_enq_last' st q b A n (RTWFq_of st WF) HQ HIN ROOM' ltac:(lia))|].
      split; [subst st'; apply RTMODEL_enq_last'; exact HM|].
      split; [subst st'; apply GWIN_enq_last'; eapply GWIN_mem; [exact HGA| exact HO| exact WM2]|].
      split; [exact HFR|].
      split; [subst st'; apply SWIN_enq_last'; exact HSW|].
      split; [exact ST2|].
      split; [unfold cli_pres in *; eapply cj_pres_trans; [exact CP0| exact CP2]|].
      split; [eapply errno_same_trans; [exact ES0| exact ES2]|].
      split; [intros w Hw; exact Hw|].
      pose proof (rt_prov_enq_last' st q b A n (RTWFq_of st WF) HQ HIN ROOM' ltac:(lia)) as PV. fold st' in PV.
      unfold budget_ok. lia.
Qed.
End ENQ.


End CeilWrap.
End RTW_q_enq.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_m_lib4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_q_drain.
Module RTW_q_put1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_sec.RTW_secondary_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_quarantine_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_lib4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drain.RTW_q_stmts.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition APUT_ENQ   : Z := 0x363dc.   (* [comment removed for export] *)
Definition APUT_DRAIN : Z := 0x33b34.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition put_frame (cbcache cbstack : Z) (vs6 vs5 vs4 vs3 vs2 vs1 vs0 vra : word) : list cell :=
  [W8 cbcache; W8 cbstack; C8 vs6; C8 vs5; C8 vs4; C8 vs3; C8 vs2; C8 vs1; C8 vs0; C8 vra].

(* [comment removed for export] *)
Definition quar_cells (j1 j2 : list byte) : list cell :=
  [CB 64 j1; W8 QUAR_MAX_SIZE; W8 QUAR_MIN_SIZE; W8 QUAR_MAX_CACHE; CB 64 j2].

(* [comment removed for export] *)
Definition freefill_cells (m : word -> option byte) : Prop :=
  ro_cells bsegs m 0xa16f8 [C8 (Z_to_bv 64 0xa71b8)] /\ ro_cells bsegs m 0xa71e8 [C4 (Z_to_bv 64 0)].

Lemma put_lits : A_ALLOC = 680792 /\ A_QUAR = 681520 /\ QUAR_MAX_SIZE = 268435456 /\ QUAR_MIN_SIZE = 241591905 /\ QUAR_MAX_CACHE = 1048576
                 /\ KSPACESIZE = 137438953472 /\ KHIGHMEM_BEG = 17594333495296 /\ AIMG_HI = 6287360 /\ AQCR = 213368 /\ AQPUT = 221740
                 /\ APOISON_SHADOW = 349864 /\ APUT_ENQ = 222172 /\ APUT_DRAIN = 211764.
Proof. repeat split; reflexivity. Qed.
Ltac plits := pose proof put_lits as (EA1 & EQ & EMS & EMN & EMC & EKS & EKH & EIH & EQCR & EPUT & EPS & EENQ & EDRN).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition put_pro_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cbcache cbstack size lo : Z) (j1 j2 : list byte),
  mem_inv bsegs m ->
  a0 = wz A_QUAR -> a2 = wz cbcache -> a3 = wz cbstack -> a5 = wz size ->
  0 <= cbcache < 2^64 -> 0 <= cbstack < 2^64 -> 0 <= size < 2^64 ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 80 <= bv_unsigned sp ->
  rw_cells bsegs m A_QUAR (quar_cells j1 j2) ->
  evt bsegs (fun ms' => exists (m' : word -> option byte),
      ms' = MS (mkR ra (wz (bv_unsigned sp - 80)) gp tp t0 t1 t2 (wz A_QUAR) a1 (wz QUAR_MAX_SIZE) a1 a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 (wz QUAR_MAX_CACHE) s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz (if size <=? QUAR_MAX_SIZE then 0x36330 else 0x36270)) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m'
      /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp - 80)
      /\ rw_cells bsegs m' (bv_unsigned sp - 80) (put_frame cbcache cbstack s6 s5 s4 s3 s2 s1 s0 ra)
      /\ rw_cells bsegs m' A_QUAR (quar_cells j1 j2))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz AQPUT) fc None m (seg_rom bsegs)).

Theorem put_pro_proof : put_pro_stmt.
Proof.
  unfold put_pro_stmt. intros until j2. intros MI -> -> -> -> Hc Hs Hz ST HCL LO QC.
  plits. unfold put_frame, quar_cells in *.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  rewrite EPUT, EQ, EMS, EMN, EMC in *. leaf_prep. cbv beta delta [wz] in QC.
  carve_frame 80%nat ST.
  do 9 lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  destruct (Z.leb_spec size 268435456) as [LE|GT].
  - lstep; if_lia. rewrite <- EQ, <- EMS, <- EMN, <- EMC. finish; eassumption.
  - lstep; if_lia. rewrite <- EQ, <- EMS, <- EMN, <- EMC. finish; eassumption.
Qed.

(* [comment removed for export] *)
Lemma land_m8'' : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551608 = x / 8 * 8.
Proof.
  intros x Hx. replace 18446744073709551608 with ((-8) mod 2^64) by reflexivity.
  rewrite land_mod_pow2_r by lia. replace (-8) with (Z.lnot (Z.ones 3)) by reflexivity. rewrite <- Z.ldiff_land.
  rewrite Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition put_poison_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cbcache cbstack mA size n : Z) (b1 : byte) (cid : word),
  mem_inv bsegs m -> freefill_cells m ->
  a2 = wz cbcache -> a3 = wz cbstack -> a4 = wz mA -> a5 = wz size ->
  0 <= cbcache < 2^64 -> 0 <= cbstack < 2^64 -> 0 <= size < 2^64 -> 0 <= n < 2^40 ->
  AIMG_HI <= mA -> mA + 16 <= alloc_ceiling ->
  rw_cells bsegs m mA (hdr_cells CHUNK_QUARANTINE n b1 cid) ->
  evt bsegs (fun ms' => exists (a3' : word),
      ms' = MS (mkR (wz 0x363b8) sp gp tp t0 t1 t2 s0 s1 (wz (mA + 16)) (wz ((usz n + 7) / 8 * 8)) (wz 253) a3' a4 a5 a6 a7
                    (wz size) (wz cbstack) (wz cbcache) (wz mA) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz APOISON_SHADOW) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x36330) fc None m (seg_rom bsegs)).

Theorem put_poison_proof : put_poison_stmt.
Proof.
  unfold put_poison_stmt. intros until cid. intros MI [G1 G2] -> -> -> -> Hc Hs Hz Hn MLO MHI HDR.
  plits. unfold hdr_cells, CHUNK_QUARANTINE, hdr_state_quar in *. rewrite EIH in MLO. rewrite EPS.
  pose proof (size_hilo n Hn) as (SH1 & SH2 & SH3).
  leaf_prep. cbv beta delta [wz] in HDR.
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *) rewrite zx16_lit by lia.
  lstep. (* [comment removed for export] *) rewrite zx32_lit by lia.
  lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *) rewrite size_join by lia.
  lstep. lstep. (* [comment removed for export] *) rewrite land_m8'' by lia.
  lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition put_enq_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt bsegs (fun ms' =>
      ms' = MS (mkR (wz 0x363d0) sp gp tp t0 t1 t2 s0 s1 s1 s4 s3 s5 s2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz APUT_ENQ) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x363b8) fc None m (seg_rom bsegs)).

Theorem put_enq_proof : put_enq_stmt.
Proof.
  unfold put_enq_stmt. intros. plits. rewrite EENQ. leaf_prep.
  lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  try rewrite Z_to_bv_bv_unsigned. finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition put_test_post (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bytes maxc : Z) : machine_state -> Prop :=
  fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz bytes) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (wz (if maxc <? bytes then 0x362f4 else 0x36308)) fc None m (seg_rom bsegs).

Definition put_test1_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c bytes maxc : Z),
  mem_inv bsegs m -> s1 = wz c -> s6 = wz maxc -> 0 <= bytes < 2^64 -> 0 <= maxc < 2^64 -> 16 <= c -> c + 32 <= 2^64 ->
  rw_cells bsegs m (c + 24) [W8 bytes] ->
  evt bsegs (put_test_post ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bytes maxc)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x363d0) fc None m (seg_rom bsegs)).

Definition put_test2_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c bytes maxc : Z),
  mem_inv bsegs m -> s1 = wz c -> s6 = wz maxc -> 0 <= bytes < 2^64 -> 0 <= maxc < 2^64 -> 16 <= c -> c + 32 <= 2^64 ->
  rw_cells bsegs m (c + 24) [W8 bytes] ->
  evt bsegs (put_test_post ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bytes maxc)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x362ec) fc None m (seg_rom bsegs)).

Theorem put_test1_proof : put_test1_stmt.
Proof.
  unfold put_test1_stmt, put_test_post. intros until maxc. intros MI -> -> Hb Hm CLO CHI CELL.
  plits. leaf_prep. cbv beta delta [wz] in CELL.
  lstep. (* [comment removed for export] *)
  destruct (Z.ltb_spec maxc bytes) as [LT|GE].
  - lstep; if_lia. finish.
  - lstep; if_lia. lstep. (* [comment removed for export] *) finish.
Qed.

Theorem put_test2_proof : put_test2_stmt.
Proof.
  unfold put_test2_stmt, put_test_post. intros until maxc. intros MI -> -> Hb Hm CLO CHI CELL.
  plits. leaf_prep. cbv beta delta [wz] in CELL.
  lstep. (* [comment removed for export] *)
  destruct (Z.ltb_spec maxc bytes) as [LT|GE].
  - lstep; if_lia. finish.
  - lstep; if_lia. finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition put_drain_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cbcache cbstack : Z) (vs6 vs5 vs4 vs3 vs2 vs1 vs0 vra : word),
  mem_inv bsegs m -> 0 <= cbcache < 2^64 -> 0 <= cbstack < 2^64 -> alloc_ceiling <= bv_unsigned sp -> bv_unsigned sp + 80 <= 2^64 ->
  rw_cells bsegs m (bv_unsigned sp) (put_frame cbcache cbstack vs6 vs5 vs4 vs3 vs2 vs1 vs0 vra) ->
  evt bsegs (fun ms' =>
      ms' = MS (mkR (wz 0x36308) sp gp tp t0 t1 t2 s0 s1 s0 s1 (wz cbcache) (wz cbstack) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz APUT_DRAIN) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x362f4) fc None m (seg_rom bsegs)).

Theorem put_drain_proof : put_drain_stmt.
Proof.
  unfold put_drain_stmt. intros until vra. intros MI Hc Hs SPL SPH FR.
  plits. unfold put_frame in *. rewrite EDRN. leaf_prep. try idtac. cbv beta delta [wz] in FR.
  lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  try rewrite Z_to_bv_bv_unsigned. finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition put_epi_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cbcache cbstack lo : Z) (vs6 vs5 vs4 vs3 vs2 vs1 vs0 vra : word),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp -> bv_unsigned sp + 80 <= 2^64 ->
  rw_cells bsegs m (bv_unsigned sp) (put_frame cbcache cbstack vs6 vs5 vs4 vs3 vs2 vs1 vs0 vra) ->
  evt bsegs (fun ms' =>
      ms' = MS (mkR vra (wz (bv_unsigned sp + 80)) gp tp t0 t1 t2 vs0 vs1 a0 a1 a2 a3 a4 a5 a6 a7 vs2 vs3 vs4 vs5 vs6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc vra) fc None m (seg_rom bsegs)
      /\ stk bsegs m lo (bv_unsigned sp + 80))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x36308) fc None m (seg_rom bsegs)).

Theorem put_epi_proof : put_epi_stmt.
Proof.
  unfold put_epi_stmt. intros until vra. intros MI ST HCL LO SPH FR.
  unfold put_frame in *. try idtac. leaf_prep. cbv beta delta [wz] in FR.
  do 8 lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  try rewrite unsigned_lit in * by lia. try rewrite Z_to_bv_bv_unsigned.
  release_frame FR ST (bv_unsigned sp + 80).
  finish; eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition put_big_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P S mA : Z) (j1 j2 j3 : list byte),
  mem_inv bsegs m -> freefill_cells m ->
  a4 = wz mA -> 0 <= mA < 2^64 -> KHIGHMEM_BEG <= S -> S + KSPACESIZE <= alloc_ceiling -> bv_unsigned sp + 80 <= 2^64 ->
  rw_cells bsegs m A_ALLOC (alloc_cells P S j1 j2 j3) ->
  evt bsegs (fun ms' => exists (a3' : word),
      ms' = MS (mkR (wz 0x362ec) sp gp tp t0 t1 t2 s0 s1 sp (wz mA) a2 a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz AQCR) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x36270) fc None m (seg_rom bsegs)).

Theorem put_big_proof : put_big_stmt.
Proof.
  unfold put_big_stmt. intros until j3. intros MI [G1 G2] -> HmA SLO SHI SPH AC.
  plits. unfold alloc_cells, KSPACESIZE in *. rewrite EKH in SLO. rewrite EA1 in AC. rewrite EQCR.
  leaf_prep. try idtac. cbv beta delta [wz] in AC.
  (* [comment removed for export] *)
  assert (TAIL : forall a0x a1x a3x : word,
    evt bsegs (fun ms' => exists (a3' : word),
        ms' = MS (mkR (Z_to_bv 64 0x362ec) sp gp tp t0 t1 t2 s0 s1 sp (Z_to_bv 64 mA) a2 a3' (Z_to_bv 64 mA) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 213368) fc None m (seg_rom bsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0x a1x a2 a3x (Z_to_bv 64 mA) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x362e0) fc None m (seg_rom bsegs))).
  { intros a0x a1x a3x. lstep. lstep. lstep. try rewrite Z_to_bv_bv_unsigned. finish. }
  lstep. lstep. (* [comment removed for export] *)
  destruct (Z.lt_ge_cases mA S) as [LT|GE].
  - lstep; if_lia. (* [comment removed for export] *) apply TAIL.
  - lstep; if_lia.
    lstep. lstep. lstep. (* [comment removed for export] *)
    destruct (Z.lt_ge_cases mA (S + 137438953472)) as [IN|OUT].
    + lstep; if_lia. (* [comment removed for export] *)
      lstep. lstep. (* [comment removed for export] *)
      lstep. (* [comment removed for export] *)
      lstep; if_lia. (* [comment removed for export] *) apply TAIL.
    + lstep; if_lia. apply TAIL.
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac plits := pose proof put_lits as (EA1 & EQ & EMS & EMN & EMC & EKS & EKH & EIH & EQCR & EPUT & EPS & EENQ & EDRN).
End RTW_q_put1.

(* [comment removed for export] *)
From Stdlib Require Permutation.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_secz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_poison8.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_m_spz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_sec_dstate.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_m_fz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_bandtac4.
Module RTW_q_rep2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_secz.RT_artZ OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_secz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_poison8.RT_poison_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstateP.RT_trans OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_abs.RTW_m_lib3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_tpz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_apz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstateP.RTW_m_live OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drainw.RTW_m_leaves2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstateP.RTW_q_trans OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_wf2.RTW_q_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_zone OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_wf3.RTW_q_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drain.RTW_q_stmts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drain.RTW_q_stmts2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_spz.RTW_sec_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstate OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_fz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_fz.RTW_m_lbz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_bandtac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_bandtac2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_bandtac4.
Import ListNotations.
Open Scope Z_scope.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem RTREP_keepS_proof : RTREP_keepS_stmt.
Proof.
  intros st m m' W WF HR MU WM HW (j & MX).
  assert (HWz : Forall (sz_ok st []) W).
  { eapply Forall_impl; [| exact HW]. intros [lo hi] X. unfold secw_ok in X. cbn [fst snd] in X.
    destruct X as [X|[X|X]]; [apply sz_ok_stack; exact X| apply sz_ok_stats; tauto|].
    apply sz_ok_static; [lia| unfold A_QUAR, A_SECONDARY, A_ALLOC in *; lia]. }
  assert (HFR : fresh_ok st []) by (intros f []).
  assert (HFC : forall f : Z * Z, In f [] -> snd f <= CEIL) by (intros f []).
  pose proof (szi_others st WF W [] HWz HFR HFC m m' MU WM HR) as NS.
  pose proof (t_range st WF) as [TR TC]. (nelimp (oclr_lin _ _ TR ltac:(lia)) 3%nat; intros TR1 TR2 TR3).
  unfold KLOWSHADOW_BEG, KHIGHMEM_BEG, AIMG_LO, AIMG_HI in TR2, TR3.
  (* [comment removed for export] *)
  assert (D : forall a sz, (a + sz <= A_SECONDARY + 616 \/ A_SECONDARY + 620 <= a) ->
                           (a + sz <= st_t st + T_STATS \/ st_t st + T_UNWINDING <= a) -> a + sz <= CEIL -> disjoint_from W a sz).
  { intros a sz H1 H2 H3. apply (disjoint_from_forallq _ W a sz HW). intros lo hi X. unfold secw_ok in X. cbn [fst snd] in X. lia. }
  assert (DI : forall a sz, AIMG_LO <= a -> a + sz <= AIMG_HI -> (a + sz <= A_SECONDARY + 616 \/ A_SECONDARY + 620 <= a) -> disjoint_from W a sz).
  { intros a sz H0 H1 H2. apply D; [exact H2| unfold T_STATS, T_UNWINDING, AIMG_LO, AIMG_HI in *; lia| unfold CEIL, AIMG_HI in *; lia]. }
  apply RTREP_of_nsec; [exact NS| |].
  - (* [comment removed for export] *)
    destruct (rr_alloc st m HR) as ((j1 & j2 & j3 & H1) & (k1 & k2 & k3 & H2) & [jg H3] & (l1 & l2 & l3 & l4 & H4) & H5).
    split; [exists j1, j2, j3; eapply rw_cells_transport; [exact H1| exact MU| exact WM|]; apply DI; unfold AIMG_LO, AIMG_HI, A_SECONDARY, A_ALLOC; cbn; lia|].
    split.
    { apply (proj1 (rw_cells_app m A_SECONDARY [_; _; _; _; _; _; _; _] [_; _])) in H2 as [H2a H2b].
      cbn [cells_size Cells.csize Nat.add] in H2b. change (Z.of_nat 616) with 616 in H2b.
      apply (rw_cells_split_CB _ _ _ [W1 0] _ _ _ [3; 4]%nat) in H2b; [| reflexivity]. cbn [mk_CB_cells app] in H2b.
      apply (proj1 (rw_cells_app m (A_SECONDARY + 616) [_; _] [_])) in H2b as [_ H2c].
      cbn [cells_size Cells.csize Nat.add] in H2c. change (Z.of_nat 4) with 4 in H2c.
      assert (H2a' : rw_cells bsegs m' A_SECONDARY [W8 4096; W8 (st_pa st); W8 (st_pa st); W8 PTRARR_RES_SIZE; CB 16 k1; W8 (st_nreserved st); W8 (nsec st); CB 552 k2])
        by (eapply rw_cells_transport; [exact H2a| exact MU| exact WM|]; apply DI; unfold AIMG_LO, AIMG_HI, A_SECONDARY, A_ALLOC; cbn; lia).
      assert (H2c' : rw_cells bsegs m' (A_SECONDARY + 616 + 4) [CB 4 (firstn 4 (skipn 3 k3))])
        by (eapply rw_cells_transport; [exact H2c| exact MU| exact WM|]; apply DI; unfold AIMG_LO, AIMG_HI, A_SECONDARY, A_ALLOC; cbn; lia).
      assert (TL : rw_cells bsegs m' (A_SECONDARY + 616) [W1 0; CB 3 j; CB 4 (firstn 4 (skipn 3 k3))]).
      { apply (proj2 (rw_cells_app m' (A_SECONDARY + 616) [W1 0; CB 3 j] [CB 4 (firstn 4 (skipn 3 k3))])). split; [exact MX|].
        cbn [cells_size Cells.csize Nat.add]. exact H2c'. }
      pose proof (rw_cells_merge bsegs m' (A_SECONDARY + 616) [W1 0] [CB 3 j; CB 4 (firstn 4 (skipn 3 k3))] []) as MG.
      cbn [app cells_size cells_bytes Cells.csize cbytes Nat.add] in MG. specialize (MG TL).
      exists k1, k2, (j ++ firstn 4 (skipn 3 k3) ++ []).
      apply (proj2 (rw_cells_app m' A_SECONDARY [_; _; _; _; _; _; _; _] [_; _])). split; [exact H2a'|].
      cbn [cells_size Cells.csize Nat.add]. change (Z.of_nat 616) with 616. exact MG. }
    split; [exists jg; eapply rw_cells_transport; [exact H3| exact MU| exact WM|]; apply DI; unfold AIMG_LO, AIMG_HI, A_GSTATS, A_SECONDARY, A_ALLOC; cbn; lia|].
    split; [exists l1, l2, l3, l4; eapply rw_cells_transport; [exact H4| exact MU| exact WM|]; apply DI; unfold AIMG_LO, AIMG_HI, A_QUAR, A_SECONDARY, A_ALLOC; cbn; lia|].
    eapply (ro_cells_transport bsegs W m m'); [exact H5| exact MU|]. apply DI; unfold AIMG_LO, AIMG_HI, A_MAXUSERSZ, A_SECONDARY, A_ALLOC; cbn; lia.
  - (* [comment removed for export] *)
    eapply (T_ptrarr st WF W m m' MU WM (rr_ptrarr st m HR)). split.
    + intros i Hi. (nelimp (pa_range st WF) 5%nat; intros P1 P2 P3 P4 P5). pose proof (t_vs_pa st WF) as TP. pose proof (ablk_img _ _ P1) as PI.
      unfold PTRARR_RES_SIZE, AIMG_HI in *. apply D; unfold A_SECONDARY, A_ALLOC, T_STATS, T_UNWINDING, CEIL in *; lia.
    + intros e He. destruct (ws_spend st (wf_sec_ok st WF) e He) as [HE _].
      (nelim (ws_entry st (wf_sec_ok st WF) e HE) 4%nat; intros E1 E2 E3 _).
      pose proof (wb_ranges st (wf_base_ok st WF) (fst e, fst e + smapsize (snd e))) as R. cbn [fst snd] in R.
      specialize (R ltac:(unfold rt_ranges; do 2 right; rewrite !in_app_iff; right; left; apply in_map_iff; exists e; auto)).
      destruct e as [mb n]. cbn [fst snd] in *. (nelim (sec_facts n E1) 5%nat; intros _ _ _ F4 _). pose proof (usz_le_rounded8 n) as (U1 & _).
      pose proof (t_vs_sec st WF mb n HE).
      (nelim R 4%nat; intros R1 R2 R3 R4). (nelimp (oclr_lin _ _ R1 ltac:(lia)) 3%nat; intros O1 O2 O3). unfold AIMG_LO, AIMG_HI in O3.
      apply D; unfold A_SECONDARY, A_ALLOC, T_STATS, T_UNWINDING, CEIL, usz in *; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma qblock_in_blocks : forall st A n, qblock st A n -> In (A, n) (all_blocks st).
Proof. intros st A n HQ. unfold all_blocks. rewrite !in_app_iff. destruct HQ; tauto. Qed.

Theorem qcr_carve_sec_proof : qcr_carve_sec_stmt.
Proof.
  intros st m A n WF HR HQ HP. cbv zeta.
  pose proof (qblock_in_blocks st A n HQ) as HB.
  (nelimp (block_geom st WF A n HB) 11%nat; intros Gn GA K X Y CE L16 H16 EA Gp Gs).
  (nelim (Gs HP) 4%nat; intros HSEC EH Y2 M4).
  assert (ELO : b_lo A n = b_map_beg A) by (unfold b_lo; rewrite HP; reflexivity). rewrite ELO in *.
  (nelimp (P_range st WF) 3%nat; intros P1 P2 P3). (nelimp (S_range st WF) 3%nat; intros S1 S2 S3).
  pose proof (prim_vs_tail st WF (b_map_beg A, b_map_beg A + smapsize n)) as PT. cbn [fst snd] in PT.
  specialize (PT ltac:(apply in_or_app; right; apply in_or_app; left; apply in_map_iff; exists (b_map_beg A, n); split; [reflexivity| exact HSEC])).
  pose proof (t_vs_sec st WF (b_map_beg A) n HSEC) as TS.
  (nelimp (ablk_lin _ _ K) 4%nat; intros KI K0 KT _). unfold AIMG_HI in KI.
  unfold b_chunk_beg, sec_alloc_beg, sec_user, b_map_beg, SEC_HDR, SEC_RZ, KHIGHMEM_BEG, PRIM_RES_SIZE, KSPACESIZE, usz in *.
  split; [exact HSEC|]. repeat split; (lia_on EH Y2 P1 S1 KI GA H16 S2 S3 PT KT TS P2).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem qcr_carve_proof : qcr_carve_stmt.
Proof.
  intros st m A n WF HR HQ.
  pose proof (qblock_in_blocks st A n HQ) as HB.
  (nelimp (block_geom st WF A n HB) 11%nat; intros Gn GA K X Y CE L16 H16 EA Gp Gs).
  (nelimp (S_range st WF) 3%nat; intros S1 S2 S3). (nelimp (P_range st WF) 3%nat; intros P1 P2 P3).
  pose proof (t_range st WF) as [TR TC]. (nelimp (oclr_lin _ _ TR ltac:(lia)) 3%nat; intros TR1 TR2 TR3).
  destruct (rr_alloc st m HR) as ((j1 & j2 & j3 & AL) & _).
  assert (HBK : exists md, R_block st m md A n /\ bm_state md = CHUNK_QUARANTINE).
  { destruct HQ as [HQ|HQ]; [exists BQuar; split; [exact (proj1 (rr_quar st m HR) A n HQ)| reflexivity]
                           | exists BPend; split; [exact (proj2 (rr_quar st m HR) A n HQ)| reflexivity]]. }
  destruct HBK as (md & ((b1 & cid & HDR & HB1) & _) & EMD). rewrite EMD in HDR.
  pose proof (proj1 (rr_thread st m HR)) as V.
  assert (C1 : exists f1 : word, rw_cells bsegs m (st_t st + T_STATS + 40) [C8 f1]).
  { apply c8_of_bytes; [unfold T_STATS; lia| unfold T_STATS; lia|]. intros i Hi. (nelim V 3%nat; intros _ _ V). apply V. unfold T_STATS. lia. }
  assert (C2 : exists f2 : word, rw_cells bsegs m (st_t st + T_STATS + 40 + 8) [C8 f2]).
  { apply c8_of_bytes; [unfold T_STATS; lia| unfold T_STATS; lia|]. intros i Hi. (nelim V 3%nat; intros _ _ V). apply V. unfold T_STATS. lia. }
  destruct C1 as [f1 C1]. destruct C2 as [f2 C2].
  pose proof (rtrep_artcells st m HR) as AC.
  exists j1, j2, j3, b1, cid, f1, f2.
  split; [exact AL|]. split; [exact HDR|]. split; [exact HB1|].
  split; [apply (proj2 (rw_cells_app m (st_t st + T_STATS + 40) [C8 f1] [C8 f2])); split; [exact C1| exact C2]|].
  split; [exact (leafc_of_RTREP st m HR)|]. split; [exact (artcells_icpt m AC)|]. split; [exact (artcells_poison m AC)|].
  split; [exact Gn|]. split; [exact GA|]. split; [exact K|]. split; [unfold b_chunk_beg; lia|]. split; [exact Y|]. split; [exact CE|].
  split; [exact (t_vs_block st WF A n HB)|].
  split; [unfold PRIM_RES_SIZE, KSPACESIZE in *; lia|]. split; [unfold PRIM_RES_SIZE, KSPACESIZE in *; lia|]. split; [exact S3|].
  split; [exact TR| exact TC].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma qchunk_qelems' : forall st b d A n, st_qcur st = [(b, d)] -> 0 <= d < qb_count b -> nthz (qb_elems b) d (0, 0) = (A, n) ->
  forall c k, Permutation (qelems st) ((A, n) :: qelems (st_qchunk st c k)).
Proof.
  intros st b d A n HC HD HE c k. rewrite (st_qchunk_eq st b d c k HC). rewrite qelems_q_set. unfold qelems. rewrite HC.
  cbn [flat_map fst snd]. rewrite !app_nil_r. rewrite (RTW_sec_dstate.skipn_nthz_cons (qb_elems b) d (A, n) (0, 0) HD HE).
  apply Permutation_sym. apply Permutation_middle.
Qed.

Theorem RTREP_qchunk_proof : RTREP_qchunk_stmt.
Proof.
  intros st m m' W b d A n WF HR HC HD HE HP HAP MU WM HW SHF.
  set (c := pclass n). set (k := b_cptr st A n). set (st1 := st_qchunk st c k).
  pose proof (qchunk_qelems' st b d A n HC HD HE c k) as PQ. fold st1 in PQ.
  assert (HQE : In (A, n) (qelems st)) by (eapply Permutation_in; [apply Permutation_sym; exact PQ| left; reflexivity]).
  assert (HB : In (A, n) (all_blocks st)) by (unfold all_blocks; rewrite !in_app_iff; right; left; exact HQE).
  (nelimp (block_geom st WF A n HB) 11%nat; intros Gn GA K X Y CE L16 H16 EA Gp Gs).
  (nelim (Gp HP) 6%nat; intros Hc G1 G2 G3 G4 G5). fold c in Hc, G1, G2, G5.
  (nelim (prim_block_cptr st WF A n HB HP) 4%nat; intros INP IK CV ELO). fold c k in INP, IK, CV, ELO.
  assert (HcK : 0 <= c < KNUMCLASSES) by (unfold KNUMCLASSES; lia). assert (Hc1 : 1 <= c) by lia.
  assert (UK : In k (used_cptrs st c)) by (rewrite used_cptrs_split; apply in_or_app; right; apply in_or_app; left; exact IK).
  pose proof (tpx_ok_of_RTWF st WF) as HX.
  set (ru := (usz n + 7) / 8 * 8) in *.
  assert (RUB : ru mod 8 = 0 /\ usz n <= ru < usz n + 8) by (subst ru; clear; Z.div_mod_to_equations; lia).
  assert (L8 : b_lo A n mod 8 = 0) by (clear - L16; Z.div_mod_to_equations; lia).
  assert (A8 : A mod 8 = 0) by (clear - GA; Z.div_mod_to_equations; lia).
  pose proof (csize_mod32 c ltac:(lia)) as CM32.
  assert (SHIN : SH (b_lo A n) <= SH A /\ SH A + ru / 8 <= SH (b_hi A n)).
  { split; [apply rt_SH_mono; lia|]. rewrite <- (rt_SH_aligned_add A ru A8). apply rt_SH_mono.
    rewrite G5. rewrite G5 in Y. clear - Y RUB CM32 A8 L8. Z.div_mod_to_equations. lia. }
  assert (HWU : Forall (ucz_ok st c k) W).
  { eapply Forall_impl; [| exact HW]. intros [lo hi] Z. unfold qcz_ok in Z. unfold ucz_ok. cbn [fst snd] in *. rewrite <- ELO, <- G5.
    destruct Z as [Z|[Z|[Z|Z]]]; [left; exact Z| right; left; (lia_on SHIN Z)| right; right; right; right; left; exact Z| right; right; right; right; right; exact Z]. }
  (nelim (ucz_others st WF c k HcK Hc1 UK W HWU m m' MU WM HR) 11%nat; intros X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 XA).
  pose proof (t_range st WF) as [TR TC]. (nelimp (oclr_lin _ _ TR ltac:(lia)) 3%nat; intros TR1 TR2 TR3).
  pose proof (t_vs_block st WF A n HB) as TB.
  (nelimp (ablk_lin _ _ K) 4%nat; intros KI K0 KT _).
  pose proof (ablk_shad_lin _ _ K ltac:(unfold usz in *; (lia_on X Y G5 K0))) as (KS1 & KS2).
  pose proof (ablk_shad_disj _ _ K ltac:(unfold usz in *; (lia_on X Y G5 K0))) as KSD.
  pose proof (rt_SH_mono (b_hi A n) (b_hi A n + 7) ltac:(lia)) as KSM.
  (* [comment removed for export] *)
  assert (DZ : forall a sz, (a + sz <= b_lo A n \/ b_hi A n <= a) -> (a + sz <= SH A \/ SH A + ru / 8 <= a) ->
                            (a + sz <= st_t st + T_STATS \/ st_t st + T_UNWINDING <= a) -> a + sz <= CEIL -> disjoint_from W a sz).
  { intros a sz H1 H2 H3 H4. apply (disjoint_from_forallq _ W a sz HW). intros lo hi Z. unfold qcz_ok in Z. cbn [fst snd] in Z. fold ru in Z.
    clear - H1 H2 H3 H4 Z. set (r8 := ru / 8) in *. clearbody r8. lia. }
  assert (DQ : disjoint_from W A_QUAR 256).
  { apply DZ; unfold A_QUAR, A_ALLOC, T_STATS, T_UNWINDING, CEIL, KLOWSHADOW_BEG, KHIGHMEM_BEG, AIMG_LO, AIMG_HI in *; (lia_on KI SHIN KS1 TR3). }
  assert (DC : disjoint_from W (qcache_t st) 32).
  { apply DZ; unfold qcache_t, T_QCACHE, T_STATS, T_UNWINDING, CEIL, KLOWSHADOW_BEG, KHIGHMEM_BEG, AIMG_LO, AIMG_HI in *; (lia_on TB SHIN TR2 KS1 KS2 TC). }
  (* [comment removed for export] *)
  assert (OTH : forall A' n', In (A', n') (all_blocks st) -> A' <> A -> chunk_ne st c k A' n').
  { intros A' n' HB' NE EP' E. injection E as E1 E2.
    (nelim (prim_block_cptr st WF A' n' HB' EP') 4%nat; intros _ _ _ L'). rewrite E1, E2 in L'.
    (nelimp (block_geom st WF A' n' HB') 6%nat; intros _ _ _ X' Y' _).
    destruct (blocks_disj st WF A' n' A n HB' HB NE) as [D|D]; unfold usz in *; (lia_on X Y G5 ELO K0 L' X' Y' D). }
  assert (NA : forall A' n', In (A', n') (st_lb st ++ qelems st1 ++ st_qpend st) -> A' <> A).
  { intros A' n' Hin EA'. subst A'.
    assert (PM : Permutation (all_blocks st) ((A, n) :: st_lb st ++ qelems st1 ++ st_qpend st)).
    { unfold all_blocks. etransitivity; [apply Permutation_app_head; apply Permutation_app_tail; exact PQ|]. cbn [app].
      apply Permutation_sym, Permutation_middle. }
    pose proof (Permutation_NoDup (Permutation_map fst PM) (wk_nodup st (wf_blocks_ok st WF))) as ND'. cbn [map fst] in ND'.
    apply NoDup_cons_iff in ND' as [NI _]. apply NI. apply in_map_iff. exists (A, n'). split; [reflexivity| exact Hin]. }
  assert (INQ1 : forall x, In x (qelems st1) -> In x (qelems st)).
  { intros x Hx. eapply Permutation_in; [apply Permutation_sym; exact PQ| right; exact Hx]. }
  (* [comment removed for export] *)
  assert (BNE : forall b0, In b0 (qall st) -> batch_ne st c k b0).
  { intros b0 Hb0 [Ec Ea]. destruct (bk_used st WF b0 Hb0) as [_ Eb0].
    apply (bk_vs_block st WF b0 Hb0 A n HB HP). fold c k. rewrite Ec. f_equal.
    rewrite Ea, Ec in Eb0. unfold cptr_addr in Eb0. (lia_on X K0 Eb0). }
  assert (HBQ : In b (qall st)) by (unfold qall; rewrite HC, !in_app_iff; cbn [map fst In]; (cut_on [HD Gn Hc HcK RUB SHIN TR2 TR3 TB KSD] tauto)).
  (* [comment removed for export] *)
  assert (RA : R_alloc st m').
  { (nelim (UZ_alloc4 st WF c k HcK Hc1 UK W HWU m m' MU WM (rr_alloc st m HR)) 4%nat; intros A1 A2 A3 A5).
    pose proof (UZ_quarcells st W m m' MU WM (rr_alloc st m HR) DQ) as A4.
    split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4| exact A5]. }
  (* [comment removed for export] *)
  assert (RT : R_thread st m').
  { (nelim (UZ_thread st WF c k HcK Hc1 UK W HWU m m' MU WM (rr_thread st m HR) HX) 12%nat; intros T1 T2 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13).
    pose proof (UZ_qcache st W m m' MU WM (rr_thread st m HR) DC) as T3.
    split; [exact T1|]. split; [exact T2|]. split; [exact T3|]. repeat (split; [assumption|]). assumption. }
  (* [comment removed for export] *)
  assert (RL : R_live st m').
  { intros A' n' Hin'. apply (UZ_live st WF c k HcK Hc1 UK W HWU m m' MU WM (rr_live st m HR) A' n' Hin').
    apply OTH; [unfold all_blocks; rewrite !in_app_iff; left; exact Hin'| apply (NA A' n'); rewrite !in_app_iff; left; exact Hin']. }
  destruct (UZ_quar st WF c k HcK Hc1 UK W HWU m m' MU WM (rr_quar st m HR)) as [Q1 Q2].
  (* [comment removed for export] *)
  assert (RVN : rw_cells bsegs m' (SH (cptr_addr st c k)) (zcells (sh_avail c))).
  { rewrite <- ELO.
    (nelimp (proj1 (rr_quar st m HR) A n HQE) 5%nat; intros _ _ _ _ SHD). unfold R_bshadow in SHD. rewrite HP in SHD.
    pose proof (sh_fits n ltac:(lia)) as [SF1 SF2].
    assert (EE : zlen (shadow_enc (usz n)) = ru / 8).
    { subst ru. unfold zlen. rewrite rt_shadow_enc_length by (unfold usz; (lia_on X Y G5 RUB K0)). clear. Z.div_mod_to_equations. lia. }
    assert (ESA : SH A = SH (b_lo A n) + sh_left n).
    { rewrite EA at 1. rewrite (rt_SH_aligned_add (b_lo A n) (8 * sh_left n) L8). f_equal. clear. Z.div_mod_to_equations. lia. }
    assert (ET : csize c / 8 = sh_left n + (ru / 8 + (sh_tot n - sh_left n - ru / 8))).
    { (nelim (prim_facts n HP) 5%nat; intros _ _ _ _ F5). unfold sh_tot. rewrite F5. unfold pslot. fold c. lia. }
    rewrite EE in SF2.
    assert (Z1 : 0 <= sh_left n) by exact SF1.
    assert (Z2 : 0 <= ru / 8) by (clear - RUB; unfold usz in RUB; Z.div_mod_to_equations; lia).
    assert (Z3 : 0 <= sh_tot n - sh_left n - ru / 8) by (clear - SF2; lia).
    assert (Z4 : 0 <= ru / 8 + (sh_tot n - sh_left n - ru / 8)) by (clear - Z2 Z3; lia).
    unfold sh_quar, sh_chunk in SHD. rewrite EE in SHD.
    replace (zlen (zrep SV_HEAP_FREED (ru / 8))) with (ru / 8) in SHD by (unfold zlen; rewrite zrep_length by exact Z2; reflexivity).
    rewrite !zcells_app' in SHD.
    apply (proj1 (rw_cells_app m _ _ _)) in SHD as [SL SR]. apply (proj1 (rw_cells_app m _ _ _)) in SR as [SM SR].
    rewrite (zcells_zrep_size _ _ Z1), (zcells_zrep_size _ _ Z2) in SR.
    unfold sh_avail. rewrite ET. rewrite (zrep_split _ _ _ Z1 Z4), (zrep_split _ _ _ Z2 Z3). rewrite !zcells_app'.
    apply (proj2 (rw_cells_app m' _ _ _)). split.
    { eapply (rwT W m m' MU WM); [exact SL|]. rewrite (zcells_zrep_size _ _ Z1). apply DZ.
      - clear - SHIN ESA KSD KSM Z1 Z2. lia.
      - left. clear - ESA. lia.
      - clear - TR2 KS1 KS2 SHIN ESA Z1 Z2. unfold T_STATS, T_UNWINDING, KLOWSHADOW_BEG, KHIGHMEM_BEG in *. lia.
      - clear - KS2 SHIN ESA Z2. unfold CEIL, KHIGHMEM_BEG in *. lia. }
    rewrite (zcells_zrep_size _ _ Z1).
    apply (proj2 (rw_cells_app m' _ _ _)). split.
    { apply CB_to_zcells_zrep; [exact Z2|]. rewrite <- ESA. exact SHF. }
    rewrite (zcells_zrep_size _ _ Z2).
    assert (ESH : SH (b_hi A n) = SH (b_lo A n) + sh_tot n) by (unfold b_hi, sh_tot; apply rt_SH_aligned_add; exact L8).
    eapply (rwT W m m' MU WM); [exact SR|]. rewrite (zcells_zrep_size _ _ Z3). apply DZ.
    - clear - SHIN ESA ESH KSD KSM Z1 Z2 Z3. lia.
    - right. clear - ESA. lia.
    - clear - TR2 KS1 KS2 SHIN ESA ESH Z1 Z2 Z3. unfold T_STATS, T_UNWINDING, KLOWSHADOW_BEG, KHIGHMEM_BEG in *. lia.
    - clear - KS2 ESA ESH Z1 Z2 Z3. unfold CEIL, KHIGHMEM_BEG in *. lia. }
  (* [comment removed for export] *)
  assert (RV : R_avail st1 m').
  { subst st1. rewrite (st_qchunk_eq st b d c k HC). intros c' k' Hc' Hin'. rewrite q_set_cptr_addr. rewrite q_set_avail in Hin'.
    unfold apend_cptrs in Hin'. rewrite (proj1 (proj2 (proj2 (q_set_fields st _ _ _ _ _ _)))), HAP in Hin'.
    apply in_app_iff in Hin' as [H|H].
    - apply XA; [exact Hc'| apply in_or_app; left; exact H|].
      intros E. injection E as -> ->. pose proof (wc_used_nodup st c (wf_class_ok st WF c HcK)) as ND. rewrite used_cptrs_split in ND.
      eapply (nodup_app_disj _ _ k ND H). apply in_or_app. left. exact IK.
    - cbn [List.filter fst] in H. destruct (c =? c') eqn:EC; cbn [map snd In] in H; [| destruct H]. destruct H as [<-|[]].
      apply Z.eqb_eq in EC. subst c'. exact RVN. }
  assert (RQ : R_quar st1 m').
  { split.
    - intros A' n' Hin'. pose proof (INQ1 _ Hin') as Hin0.
      assert (HB' : In (A', n') (all_blocks st)) by (unfold all_blocks; rewrite !in_app_iff; right; left; exact Hin0).
      pose proof (Q1 A' n' Hin0 (OTH A' n' HB' (NA A' n' ltac:(rewrite !in_app_iff; right; left; exact Hin')))) as RB.
      subst st1. rewrite (st_qchunk_eq st b d c k HC). destruct st; exact RB.
    - intros A' n' Hin'.
      assert (Hin0 : In (A', n') (st_qpend st)).
      { subst st1. rewrite (st_qchunk_eq st b d c k HC) in Hin'. rewrite (proj1 (proj2 (proj2 (proj2 (q_set_fields st _ _ _ _ _ _))))) in Hin'. exact Hin'. }
      assert (HB' : In (A', n') (all_blocks st)) by (unfold all_blocks; rewrite !in_app_iff; right; right; exact Hin0).
      pose proof (Q2 A' n' Hin0 (OTH A' n' HB' (NA A' n' ltac:(rewrite !in_app_iff; right; right; exact Hin0)))) as RB.
      subst st1. rewrite (st_qchunk_eq st b d c k HC). destruct st; exact RB. }
  assert (RB : R_batches st1 m').
  { subst st1. rewrite (st_qchunk_eq st b d c k HC). unfold R_batches.
    (nelim (q_set_fields st (st_qthread st) (st_qglobal st) ((c, k) :: st_apend st) (st_qpend st) (st_qtmp st) [(b, d + 1)]) 6%nat; intros F1 F2 F3 F4 F5 F6).
    rewrite F1, F2, F5, F6.
    (nelim (UZ_batches st WF c k HcK Hc1 UK W HWU m m' MU WM (rr_batches st m HR)) 4%nat; intros B1 B2 B3 B4).
    split; [| split; [| split]].
    - apply (proj2 (R_qlist_iff m' _)). intros q1 b0 q2 E. apply (B1 q1 b0 q2 E). apply BNE. unfold qall. rewrite E, !in_app_iff. cbn [In]. (cut_on [HD Gn Hc HcK RUB SHIN TR2 TR3 TB KSD] tauto).
    - apply (proj2 (R_qlist_iff m' _)). intros q1 b0 q2 E. apply (B2 q1 b0 q2 E). apply BNE. unfold qall. rewrite E, !in_app_iff. cbn [In]. (cut_on [HD Gn Hc HcK RUB SHIN TR2 TR3 TB KSD] tauto).
    - apply (proj2 (R_qlist_iff m' _)). intros q1 b0 q2 E. apply (B3 q1 b0 q2 E). apply BNE. unfold qall. rewrite E, !in_app_iff. cbn [In]. (cut_on [HD Gn Hc HcK RUB SHIN TR2 TR3 TB KSD] tauto).
    - intros bd [<-|[]]. cbn [fst]. apply (B4 (b, d)); [rewrite HC; left; reflexivity| cbn [fst]; apply BNE; exact HBQ]. }
  subst st1. rewrite (st_qchunk_eq st b d c k HC) in *. destruct st. constructor; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem qcr_carve_prim_proof : qcr_carve_prim_stmt.
Proof.
  intros st m A n WF HR HQE HP. cbv zeta.
  assert (HB : In (A, n) (all_blocks st)) by (unfold all_blocks; rewrite !in_app_iff; right; left; exact HQE).
  (nelimp (block_geom st WF A n HB) 11%nat; intros Gn GA K X Y CE L16 H16 EA Gp Gs).
  (nelim (Gp HP) 6%nat; intros Hc G1 G2 G3 G4 G5).
  (nelim (prim_block_cptr st WF A n HB HP) 4%nat; intros INP IK CV ELO).
  set (c := pclass n) in *. set (k := b_cptr st A n) in *.
  assert (HcK : 0 <= c < KNUMCLASSES) by (unfold KNUMCLASSES; lia).
  (nelim (carved_chunk st WF c k HcK ltac:(lia) CV) 3%nat; intros CC1 CC2 CC3).
  pose proof (region_facts st WF c HcK) as RF. cbn zeta in RF. (nelim RF 10%nat; intros Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 Y9 Y10).
  pose proof (csize_pos c ltac:(lia)) as SP. pose proof (csize_mod32 c ltac:(lia)) as CM32.
  pose proof (rz_size_range n) as (RZ1 & RZ2).
  assert (EPB : b_lo A n = b_alloc_beg A n) by (unfold b_lo; rewrite HP; reflexivity).
  set (ru := (usz n + 7) / 8 * 8) in *.
  assert (RUB : ru mod 8 = 0 /\ usz n <= ru < usz n + 8) by (subst ru; clear; Z.div_mod_to_equations; lia).
  assert (L8 : b_lo A n mod 8 = 0) by (clear - L16; Z.div_mod_to_equations; lia).
  assert (A8 : A mod 8 = 0) by (clear - GA; Z.div_mod_to_equations; lia).
  assert (ARU : A + ru <= b_hi A n).
  { rewrite G5. rewrite G5 in Y. clear - Y RUB CM32 A8 L8. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  (nelimp (proj1 (rr_quar st m HR) A n HQE) 5%nat; intros _ BIG _ _ SHD). unfold R_bshadow in SHD. rewrite HP in SHD.
  pose proof (sh_fits n ltac:(lia)) as [SF1 SF2].
  assert (EE : zlen (shadow_enc (usz n)) = ru / 8).
  { subst ru. unfold zlen. rewrite rt_shadow_enc_length by (unfold usz; (lia_on G2 G5 ELO CC1 CC2 Y5 SP RZ1)). clear. Z.div_mod_to_equations. lia. }
  assert (ESA : SH A = SH (b_lo A n) + sh_left n).
  { rewrite EA at 1. rewrite (rt_SH_aligned_add (b_lo A n) (8 * sh_left n) L8). f_equal. clear. Z.div_mod_to_equations. lia. }
  rewrite EE in SF2.
  assert (Z1 : 0 <= sh_left n) by exact SF1.
  assert (Z2 : 0 <= ru / 8) by (clear - RUB; unfold usz in RUB; Z.div_mod_to_equations; lia).
  unfold sh_quar, sh_chunk in SHD. rewrite EE in SHD. rewrite !zcells_app' in SHD.
  apply (proj1 (rw_cells_app m _ _ _)) in SHD as [_ SR]. apply (proj1 (rw_cells_app m _ _ _)) in SR as [SM _].
  rewrite (zcells_zrep_size _ _ Z1) in SM. rewrite <- ESA in SM. apply zcells_zrep_to_CB in SM; [| exact Z2].
  (* [comment removed for export] *)
  (nelim (proj2 (rr_rinfo st m HR) c HcK) 4%nat; intros jr je js RI). unfold rinfo_cells in RI. cbv zeta in RI.
  apply (proj1 (rw_cells_app m (rinfo st c) [_; _; _; _; _; _] (_ :: _))) in RI as [_ RI].
  apply (proj1 (rw_cells_app m _ [_] (_ :: _))) in RI as [RI _].
  cbn [cells_size Cells.csize Nat.add] in RI. change (Z.of_nat 48) with 48 in RI.
  eexists. 
  split; [exact Hc|]. split; [rewrite <- EPB; exact ELO|]. split; [symmetry; exact EPB|]. split; [rewrite <- EPB; exact G5|].
  split; [exact (proj1 RZ1)|]. split; [reflexivity|].
  pose proof (rbeg_val st c) as RBV.
  assert (IDX : exists idx, 0 <= idx /\ b_lo A n - rbeg st c = idx * csize c).
  { exists ((b_lo A n - rbeg st c) / csize c). rewrite ELO. split; [apply Z.div_pos; lia|].
    pose proof (Z.div_mod (cptr_addr st c k - rbeg st c) (csize c) ltac:(lia)) as DM. rewrite CC3 in DM. (lia_on G2 G5 ELO CC1 Y5 SP RZ1 DM). }
  (nelim IDX 3%nat; intros idx IDX0 IDXE).
  rewrite <- EPB.
  split; [rewrite <- RBV; exact G1|].
  split; [rewrite <- G5; unfold KREGIONSIZE, KFREEARRAY_OFF in *; (lia_on G5 ELO CC1 CC2 Y5 Y6 SP RZ1 RBV)|].
  split; [exists idx; split; [exact IDX0|]; split; [rewrite <- RBV; (lia_on G2 G5 CC1 Y5 SP RZ1 IDX0 IDXE)| (lia_on G2 G5 CC1 Y5 SP RZ1 IDX0 IDXE)]|].
  split; [(lia_on ELO CC1 CC2 Y5 Y6 SP RZ1 IDX0 IDXE)|].
  split; [unfold rinfo, ris in RI; exact RI|].
  split; [rewrite EPB; exact BIG|].
  split; [exact SM|]. split; [exact A8|].
  split.
  { pose proof (ablk_disj_band _ _ K) as [KB|KB]; [left| right]; unfold lowmem_range, highmem_range.
    - (nelimp (ablk_lin _ _ K) 3%nat; intros KI K0 _). unfold AIMG_HI in KI. clear - KB KI X ARU RUB. unfold usz in *. lia.
    - clear - KB X ARU RUB CE. unfold KHIGHMEM_END, usz in *. lia. }
  clear - RUB. unfold usz in RUB. Z.div_mod_to_equations. lia.
Qed.

End CeilWrap.
End RTW_q_rep2.

(* [comment removed for export] *)
Module RTW_q_psz.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_secz.RT_artZ OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_secz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_poison8.RT_poison_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstateP.RT_trans OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_abs.RTW_m_lib3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_tpz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_apz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstateP.RTW_m_live OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drainw.RTW_m_leaves2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstateP.RTW_q_trans OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_wf2.RTW_q_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_zone OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_wf3.RTW_q_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drain.RTW_q_stmts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drain.RTW_q_stmts2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_spz.RTW_sec_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstate OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_fz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_fz.RTW_m_lbz RTW_q_rep2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_spz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_bandtac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_bandtac2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_bandtac4.
Import ListNotations.
Open Scope Z_scope.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition psz_ok (A n : Z) (iv : Z * Z) : Prop :=
     (SH A <= fst iv /\ snd iv <= SH A + (usz n + 7) / 8 * 8 / 8)
  \/ CEIL <= fst iv.

Lemma nodup_fst_app : forall (l1 l2 : list (Z * Z)) a x y, List.NoDup (map fst (l1 ++ l2)) -> In (a, x) l1 -> In (a, y) l2 -> False.
Proof.
  intros l1 l2 a x y ND H1 H2. rewrite map_app in ND.
  eapply (nodup_app_disj _ _ a ND); [apply in_map_iff; exists (a, x); split; [reflexivity| exact H1]| apply in_map_iff; exists (a, y); split; [reflexivity| exact H2]].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem RTREP_pshadow_prim : forall st m m' W A n,
  RTWF st -> RTREP st m -> In (A, n) (st_qpend st) -> bprim n = true ->
  munch W m m' -> wmono bsegs m m' -> Forall (psz_ok A n) W ->
  RTREP st m'.
Proof.
  intros st m m' W A n WF HR HIN HP MU WM HW.
  set (c := pclass n). set (k := b_cptr st A n).
  assert (HB : In (A, n) (all_blocks st)) by (unfold all_blocks; rewrite !in_app_iff; right; right; exact HIN).
  (nelimp (block_geom st WF A n HB) 11%nat; intros Gn GA K X Y CE L16 H16 EA Gp Gs).
  (nelim (Gp HP) 6%nat; intros Hc G1 G2 G3 G4 G5). fold c in Hc, G1, G2, G5.
  (nelim (prim_block_cptr st WF A n HB HP) 4%nat; intros INP IK CV ELO). fold c k in INP, IK, CV, ELO.
  assert (HcK : 0 <= c < KNUMCLASSES) by (unfold KNUMCLASSES; lia). assert (Hc1 : 1 <= c) by lia.
  assert (UK : In k (used_cptrs st c)) by (rewrite used_cptrs_split; apply in_or_app; right; apply in_or_app; left; exact IK).
  pose proof (tpx_ok_of_RTWF st WF) as HX.
  set (ru := (usz n + 7) / 8 * 8) in *.
  assert (RUB : ru mod 8 = 0 /\ usz n <= ru < usz n + 8) by (subst ru; clear; Z.div_mod_to_equations; lia).
  assert (L8 : b_lo A n mod 8 = 0) by (clear - L16; Z.div_mod_to_equations; lia).
  assert (A8 : A mod 8 = 0) by (clear - GA; Z.div_mod_to_equations; lia).
  pose proof (csize_mod32 c ltac:(lia)) as CM32.
  assert (SHIN : SH (b_lo A n) <= SH A /\ SH A + ru / 8 <= SH (b_hi A n)).
  { split; [apply rt_SH_mono; lia|]. rewrite <- (rt_SH_aligned_add A ru A8). apply rt_SH_mono.
    rewrite G5. rewrite G5 in Y. clear - Y RUB CM32 A8 L8. Z.div_mod_to_equations. lia. }
  assert (HWU : Forall (ucz_ok st c k) W).
  { eapply Forall_impl; [| exact HW]. intros [lo hi] Z. unfold psz_ok in Z. unfold ucz_ok. cbn [fst snd] in *. rewrite <- ELO, <- G5. fold ru in Z.
    destruct Z as [Z|Z]; [right; left; clear - Z SHIN; lia| right; right; right; right; right; exact Z]. }
  (nelim (ucz_others st WF c k HcK Hc1 UK W HWU m m' MU WM HR) 11%nat; intros X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 XA).
  pose proof (t_range st WF) as [TR TC]. (nelimp (oclr_lin _ _ TR ltac:(lia)) 3%nat; intros TR1 TR2 TR3).
  (nelimp (ablk_lin _ _ K) 4%nat; intros KI K0 KT _).
  pose proof (ablk_shad_lin _ _ K ltac:(unfold usz in *; (lia_on X Y G5 K0))) as (KS1 & KS2).
  pose proof (ablk_shad_disj _ _ K ltac:(unfold usz in *; (lia_on X Y G5 K0))) as KSD.
  pose proof (rt_SH_mono (b_hi A n) (b_hi A n + 7) ltac:(lia)) as KSM.
  assert (Z2 : 0 <= ru / 8) by (clear - RUB; unfold usz in RUB; Z.div_mod_to_equations; lia).
  assert (DZ : forall a sz, (a + sz <= SH A \/ SH A + ru / 8 <= a) -> a + sz <= CEIL -> disjoint_from W a sz).
  { intros a sz H1 H2. apply (disjoint_from_forallq _ W a sz HW). intros lo hi Z. unfold psz_ok in Z. cbn [fst snd] in Z. fold ru in Z.
    clear - H1 H2 Z. set (r8 := ru / 8) in *. clearbody r8. lia. }
  assert (DQ : disjoint_from W A_QUAR 256).
  { apply DZ; [left| ]; clear - KS1 SHIN; unfold A_QUAR, A_ALLOC, CEIL, KLOWSHADOW_BEG in *; lia. }
  assert (DC : disjoint_from W (qcache_t st) 32).
  { apply DZ; [| clear - TC; unfold qcache_t, T_QCACHE, CEIL in *; lia].
    clear - TR2 KS1 KS2 SHIN Z2. unfold qcache_t, T_QCACHE, KLOWSHADOW_BEG, KHIGHMEM_BEG in *. lia. }
  assert (OTH : forall A' n', In (A', n') (all_blocks st) -> A' <> A -> chunk_ne st c k A' n').
  { intros A' n' HB' NE EP' E. injection E as E1 E2.
    (nelim (prim_block_cptr st WF A' n' HB' EP') 4%nat; intros _ _ _ L'). rewrite E1, E2 in L'.
    (nelimp (block_geom st WF A' n' HB') 6%nat; intros _ _ _ X' Y' _).
    destruct (blocks_disj st WF A' n' A n HB' HB NE) as [D|D]; unfold usz in *; (lia_on X Y G5 ELO K0 L' X' Y' D). }
  pose proof (wk_nodup st (wf_blocks_ok st WF)) as NDA. unfold all_blocks in NDA.
  assert (BNE : forall b0, In b0 (qall st) -> batch_ne st c k b0).
  { intros b0 Hb0 [Ec Ea]. destruct (bk_used st WF b0 Hb0) as [_ Eb0].
    apply (bk_vs_block st WF b0 Hb0 A n HB HP). fold c k. rewrite Ec. f_equal.
    rewrite Ea, Ec in Eb0. unfold cptr_addr in Eb0. (lia_on X K0 Eb0). }
  assert (RA : R_alloc st m').
  { (nelim (UZ_alloc4 st WF c k HcK Hc1 UK W HWU m m' MU WM (rr_alloc st m HR)) 4%nat; intros A1 A2 A3 A5).
    pose proof (UZ_quarcells st W m m' MU WM (rr_alloc st m HR) DQ) as A4.
    split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4| exact A5]. }
  assert (RT : R_thread st m').
  { (nelim (UZ_thread st WF c k HcK Hc1 UK W HWU m m' MU WM (rr_thread st m HR) HX) 12%nat; intros T1 T2 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13).
    pose proof (UZ_qcache st W m m' MU WM (rr_thread st m HR) DC) as T3.
    split; [exact T1|]. split; [exact T2|]. split; [exact T3|]. repeat (split; [assumption|]). assumption. }
  assert (RV : R_avail st m').
  { intros c' k' Hc' Hin'. apply XA; [exact Hc'| exact Hin'|].
    intros E. injection E as -> ->. pose proof (wc_used_nodup st c (wf_class_ok st WF c HcK)) as ND. rewrite used_cptrs_split in ND.
    apply in_app_iff in Hin' as [H|H].
    - eapply (nodup_app_disj _ _ k ND H). apply in_or_app. left. exact IK.
    - rewrite app_assoc in ND. rewrite app_assoc in ND. eapply (nodup_app_disj _ _ k ND); [| exact H].
      apply in_or_app. left. apply in_or_app. right. exact IK. }
  assert (RL : R_live st m').
  { intros A' n' Hin'. apply (UZ_live st WF c k HcK Hc1 UK W HWU m m' MU WM (rr_live st m HR) A' n' Hin').
    apply OTH; [unfold all_blocks; rewrite !in_app_iff; left; exact Hin'|].
    intros ->. rewrite app_assoc in NDA. eapply (nodup_fst_app _ _ A n' n NDA); [apply in_or_app; left; exact Hin'| exact HIN]. }
  destruct (UZ_quar st WF c k HcK Hc1 UK W HWU m m' MU WM (rr_quar st m HR)) as [Q1 Q2].
  (* [comment removed for export] *)
  assert (RBP : R_block st m' BPend A n).
  { destruct (proj2 (rr_quar st m HR) A n HIN) as ((b1 & cid & HDR & HB1) & BG & SC & V & SHD).
    assert (DB : forall a sz, b_lo A n <= a -> a + sz <= b_hi A n -> disjoint_from W a sz).
    { intros a sz H1 H2. apply DZ; [| clear - H2 CE; unfold CEIL; lia]. clear - H1 H2 KSD KSM SHIN Z2. lia. }
    split; [exists b1, cid; split; [| exact HB1]; eapply (rwT W m m' MU WM); [exact HDR|]; apply DB; unfold b_chunk_beg, hdr_cells; cbn [cells_size Cells.csize Nat.add]; clear - X Y; unfold usz in *; lia|].
    split; [intros HRZ; eapply (rwT W m m' MU WM); [exact (BG HRZ)|]; apply DB; cbn [cells_size Cells.csize Nat.add]; unfold b_hi, b_lo in *; rewrite HP in *; clear - X Y HRZ; unfold b_alloc_beg, usz in *; lia|].
    split; [intros EPF; rewrite HP in EPF; discriminate EPF|].
    split; [eapply (visTo m m' WM); [exact V| apply oclr_of_ablk; exact K| exact CE]|].
    unfold R_bshadow in *. rewrite HP in *.
    eapply stk_wmono_noseg; [exact SHD| exact WM|]. clear - KS1. unfold AIMG_HI, KLOWSHADOW_BEG in *. lia. }
  assert (RQ : R_quar st m').
  { split.
    - intros A' n' Hin'. apply Q1; [exact Hin'|]. apply OTH; [unfold all_blocks; rewrite !in_app_iff; right; left; exact Hin'|].
      intros ->. eapply (nodup_fst_app _ _ A n' n); [| apply in_or_app; right; exact Hin'| exact HIN]. rewrite <- app_assoc. exact NDA.
    - intros A' n' Hin'. destruct (Z.eq_dec A' A) as [->|NE].
      + assert (n' = n).
        { pose proof (NoDup_map_fst_unique (st_lb st ++ qelems st ++ st_qpend st) A n' n NDA) as U. apply U; rewrite !in_app_iff; (cut_on [Gn Hc HcK RUB SHIN TR2 TR3 KSD Hin' HIN] tauto). }
        subst n'. exact RBP.
      + apply Q2; [exact Hin'|]. apply OTH; [unfold all_blocks; rewrite !in_app_iff; right; right; exact Hin'| exact NE]. }
  assert (RB : R_batches st m').
  { (nelim (UZ_batches st WF c k HcK Hc1 UK W HWU m m' MU WM (rr_batches st m HR)) 4%nat; intros B1 B2 B3 B4).
    split; [| split; [| split]].
    - apply (proj2 (R_qlist_iff m' _)). intros q1 b0 q2 E. apply (B1 q1 b0 q2 E). apply BNE. unfold qall. rewrite E, !in_app_iff. cbn [In]. tauto.
    - apply (proj2 (R_qlist_iff m' _)). intros q1 b0 q2 E. apply (B2 q1 b0 q2 E). apply BNE. unfold qall. rewrite E, !in_app_iff. cbn [In]. tauto.
    - apply (proj2 (R_qlist_iff m' _)). intros q1 b0 q2 E. apply (B3 q1 b0 q2 E). apply BNE. unfold qall. rewrite E, !in_app_iff. cbn [In]. (cut_on [Gn Hc HcK RUB SHIN TR2 TR3 KSD] tauto).
    - intros bd Hbd. apply (B4 bd Hbd). apply BNE. unfold qall. rewrite !in_app_iff. right. right. right. apply in_map. exact Hbd. }
  constructor; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section PSZ2.
Variable st : rtstate.
Hypothesis WF : RTWF st.
Variables (mb n : Z).
Hypothesis HSEC : In (mb, n) (st_sec st).
Variable W : list (Z * Z).
Hypothesis HW : Forall (spz_ok st mb n) W.
Local Abbreviation P := (st_pbase st).
Local Abbreviation T := (st_t st).

Lemma spz_sec : In (mb, n) (st_sec st). Proof. exact HSEC. Qed.

(* [comment removed for export] *)
Lemma spz_disj : forall a sz,
  (a + sz <= mb + 32 \/ mb + smapsize n <= a) ->
  (a + sz <= SH mb \/ SH (mb + smapsize n) <= a) ->
  (a + sz <= T + T_STATS \/ T + T_UNWINDING <= a) ->
  a + sz <= CEIL ->
  disjoint_from W a sz.
Proof.
  intros a sz D1 D2 D3 D4. pose proof HW as HW'. clear HW. induction W as [|[lo hi] W' IH]; [exact I|].
  pose proof (Forall_inv HW') as K. unfold spz_ok in K. cbn [fst snd] in K. cbn. split; [| apply IH; exact (Forall_inv_tail HW')].
  lia.
Qed.

Local Ltac geom :=
  (nelimp (map_range st WF mb n spz_sec) 4%nat; intros MR1 MR2 MR3 MR4);
  (nelimp (map_sh_range st WF mb n spz_sec) 3%nat; intros MS1 MS2 MS3);
  pose proof (t_range st WF) as (TR1 & TR2);
  unfold KHIGHMEM_BEG, AIMG_HI in *.

(* [comment removed for export] *)
Lemma S1 : forall a sz, AIMG_LO <= a -> a + sz <= A_SECONDARY -> disjoint_from W a sz.
Proof. intros a sz H0 H. geom. rewrite A_SECONDARY_val in H. apply spz_disj; unfold CEIL, T_STATS, T_UNWINDING, AIMG_LO in *; blia. Qed.
Lemma S2 : forall a sz, A_QUAR <= a -> a + sz <= KHIGHSHADOW_BEG ->
  (a + sz <= AIMG_HI \/ (KLOWSHADOW_BEG <= a /\ a + sz <= SH AIMG_HI)) -> disjoint_from W a sz.
Proof.
  intros a sz H1 H2 H3. change (SH AIMG_HI) with 0x800b7e00 in H3. geom. rewrite KHIGHSHADOW_BEG_val in H2. rewrite A_QUAR_val in H1.
  apply spz_disj; unfold CEIL, T_STATS, T_UNWINDING, AIMG_LO, KLOWSHADOW_BEG in *; blia.
Qed.
Lemma S5 : forall b a sz, In b (d_nblocks (st_depot st)) -> b <= a -> a + sz <= b + NODEBLOCK_SIZE -> disjoint_from W a sz.
Proof.
  intros b a sz Hb H1 H2. geom. pose proof (nb_vs_map st WF mb n spz_sec b Hb) as D1. pose proof (nb_vs_t st WF b Hb) as D2.
  pose proof (nb_range st WF b Hb) as (R1 & R2). unfold KHIGHMEM_BEG, AIMG_HI in R1.
  apply spz_disj; unfold T_STATS, T_UNWINDING in *; (cut_on [H1 H2 D1 MS1 MS3 D2 R1 R2] blia).
Qed.
Lemma SZprim : forall a sz, P <= a -> a + sz <= P + PRIM_RES_SIZE -> disjoint_from W a sz.
Proof.
  intros a sz H1 H2. geom. pose proof (prim_vs_map st WF mb n spz_sec) as D1. pose proof (prim_vs_t st WF) as D2.
  (nelimp (P_range st WF) 3%nat; intros Q1 Q2 _). unfold KHIGHMEM_BEG, AIMG_HI in Q1.
  apply spz_disj; unfold CEIL, T_STATS, T_UNWINDING in *; lia.
Qed.
Lemma SZprim_sh : forall a b, P <= a -> a <= b -> b <= P + PRIM_RES_SIZE -> disjoint_from W (SH a) (SH b - SH a).
Proof.
  intros a b H1 H2 H3. geom. pose proof (prim_vs_map st WF mb n spz_sec) as D1.
  (nelimp (P_range st WF) 3%nat; intros Q1 Q2 _). unfold KHIGHMEM_BEG, AIMG_HI in Q1.
  pose proof (rt_SH_mono a b H2) as M0.
  pose proof (rt_SH_mono (P + PRIM_RES_SIZE) (@CEIL ACEIL) ltac:(unfold CEIL in *; lia)) as M1. rewrite SH_CEIL in M1.
  pose proof (rt_SH_mono b (P + PRIM_RES_SIZE) H3) as M2.
  assert (D : SH b <= SH mb \/ SH (mb + smapsize n) <= SH a).
  { destruct D1 as [D1|D1]; [left; apply rt_SH_mono; lia| right; apply rt_SH_mono; lia]. }
  pose proof alloc_ceiling_range as ACR.
  pose proof (rt_SH_bounds a ltac:(unfold CEIL in *; lia)) as BA. pose proof (rt_SH_bounds b ltac:(unfold CEIL in *; lia)) as BB.
  apply spz_disj; unfold CEIL, T_STATS, T_UNWINDING in *; blia.
Qed.
(* [comment removed for export] *)
Lemma SZsec : forall e a sz, In e (st_sec st) -> fst e <> mb -> fst e <= a -> a + sz <= fst e + smapsize (snd e) -> disjoint_from W a sz.
Proof.
  intros e a sz He NE H1 H2. geom. pose proof (sec_vs_map st WF mb n spz_sec e He NE) as D1. pose proof (t_vs_sec st WF e He) as D2.
  pose proof (sec_range st WF e He) as (R1 & R2). unfold KHIGHMEM_BEG, AIMG_HI in R1.
  apply spz_disj; unfold CEIL, T_STATS, T_UNWINDING in *; (cut_on [NE H1 H2 MR1 MR2 D1 MS1 MS3 R1 D2] blia).
Qed.
Lemma SZsec_sh : forall e a b, In e (st_sec st) -> fst e <> mb -> fst e <= a -> a <= b -> b <= fst e + smapsize (snd e) ->
  disjoint_from W (SH a) (SH b - SH a).
Proof.
  intros e a b He NE H1 H2 H3. geom. pose proof (sec_vs_map st WF mb n spz_sec e He NE) as D1.
  pose proof (sec_range st WF e He) as (R1 & R2). unfold KHIGHMEM_BEG, AIMG_HI in R1.
  pose proof (rt_SH_mono a b H2) as M0.
  pose proof (rt_SH_mono (fst e + smapsize (snd e)) CEIL R2) as M1. rewrite SH_CEIL in M1.
  pose proof (rt_SH_mono b (fst e + smapsize (snd e)) H3) as M2.
  assert (D : SH b <= SH mb \/ SH (mb + smapsize n) <= SH a).
  { destruct D1 as [D1|D1]; [left; apply rt_SH_mono; lia| right; apply rt_SH_mono; lia]. }
  pose proof alloc_ceiling_range as ACR. (nelimp (ablk_lin _ _ R1) 4%nat; intros L1 L2 L3 L4).
  pose proof (rt_SH_bounds a ltac:(unfold CEIL in *; lia)) as BA. pose proof (rt_SH_bounds b ltac:(unfold CEIL in *; lia)) as BB.
  apply spz_disj; unfold CEIL, T_STATS, T_UNWINDING in *; blia.
Qed.
(* [comment removed for export] *)
Lemma block_map_other : forall A n', In (A, n') (all_blocks st) -> bprim n' = false -> A <> sec_user mb -> b_map_beg A <> mb.
Proof. intros A n' HB HP NE E. apply NE. unfold sec_user. rewrite <- E. unfold b_map_beg. lia. Qed.
Lemma SZloose : forall b k a sz, In (b, k) (st_loose0 st) -> b <= a -> a + sz <= b + k ->
  (b + k <= T \/ T + 4096 <= b \/ a + sz <= T + T_STATS \/ T + T_UNWINDING <= a) -> disjoint_from W a sz.
Proof.
  intros b k a sz Hin H1 H2 H3. geom. pose proof (loose_vs_map st WF mb n spz_sec b k Hin) as D1.
  (nelimp (loose0_range st WF b k Hin) 4%nat; intros R1 R2 R3 R4). unfold KHIGHMEM_BEG, AIMG_HI in R1.
  apply spz_disj; unfold CEIL, T_STATS, T_UNWINDING in *; (cut_on [H1 H2 MR1 D1 R1 R3 MS1 MS3 H3] blia).
Qed.

Local Ltac s12 := first [ apply S1; rewrite ?A_SECONDARY_val; unfold AIMG_LO; lia
                         | apply S2; rewrite ?A_QUAR_val, ?KHIGHSHADOW_BEG_val; change (SH AIMG_HI) with 0x800b7e00; unfold AIMG_HI, KLOWSHADOW_BEG; lia ].

Lemma SP_link : WOK_link W.
Proof. split; [intros a v Hin; destruct (alink_range a v Hin); s12| unfold A_GLOBREC_LO, A_GLOBREC_HI; s12]. Qed.
Lemma SP_consts : WOK_consts W.
Proof.
  unfold WOK_consts.
  unfold A_SHADOW_OFF_CELL, A_UAR_OPTION, A_AFLAGS, A_CFLAGS, A_PAGESIZE_CACHED, A_KHIGHMEMEND, A_KMIDMEMBEG, A_KMIDMEMEND,
    A_ASAN_INITED, A_MCS, A_CAN_POISON, A_TSD_KEY_INITED, A_TSD_KEY, A_MAY_RETURN_NULL, A_ALLOC_OOM, A_DYING, A_VERBOSITY,
    A_MFHOOKS, A_LSAN_DISABLE, A_IA_INITED, AHOOKS, A_LIBC_PAGESIZE, A_MU_GLOBALS, A_GLOBALS_REGD, A_TPCG_INITED, A_TOOLNAME, A_PRINTF_CB, A_EMB, ATP.
  repeat lazymatch goal with |- _ /\ _ => split | _ => idtac end; s12.
Qed.
Lemma SP_alloc : WOK_alloc W.
Proof.
  unfold WOK_alloc, A_MAXUSERSZ. rewrite A_SECONDARY_val, A_QUAR_val. unfold A_ALLOC, A_GSTATS, A_ALLOC.
  geom. repeat lazymatch goal with |- _ /\ _ => split | _ => idtac end; apply spz_disj; unfold CEIL, T_STATS, T_UNWINDING, AIMG_LO in *; (cut_on [MR1 MS1 TR1 TR2] blia).
Qed.
Lemma SP_ia : WOK_ia W.
Proof. intros i Hi. unfold A_IA_MAP1. s12. Qed.
Lemma SP_lowshadow : WOK_lowshadow W.
Proof. intros g Hg. change (SH AIMG_LO) with 0x7fffa000 in Hg. change (SH AIMG_HI) with 0x800b7e00 in Hg. s12. Qed.
Lemma SP_depot : WOK_depot st W.
Proof.
  pose proof (wf_depot_ok st WF) as WD. unfold WOK_depot.
  unfold A_DEPOT, A_DEPOT_NIDS, A_DEPOT_MAP1, A_STACKSTORE, DEPOT_TAB_LOG, SSTORE_NBLOCKS in *.
  split; [| split; [| split; [| split; [| split]]]].
  - intros i Hi. s12.
  - s12.
  - intros k Hk. s12.
  - intros id Hid.
    set (q := id / DEPOT_L2_NODES). set (b := nthz (d_nblocks (st_depot st)) q 0).
    assert (Hq : 0 <= q < d_nnb (st_depot st)).
    { pose proof (wd_nnb st WD) as E. unfold d_nnb in *. rewrite E. subst q. unfold DEPOT_L2_NODES. Z.div_mod_to_equations. (cut_on [Hid H H0 H4 H5 H9 H10 H11 H12 H13] nia). }
    assert (Hb : In b (d_nblocks (st_depot st))) by (subst b; apply nthz_In; unfold d_nnb in Hq; exact Hq).
    assert (ADDR : dnode_addr (st_depot st) id = b + DEPOT_NODE_SZ * (id mod DEPOT_L2_NODES)) by reflexivity.
    rewrite ADDR. unfold DEPOT_NODE_SZ, DEPOT_L2_NODES, NODEBLOCK_SIZE in *.
    apply (S5 b); [exact Hb| Z.div_mod_to_equations; lia| unfold NODEBLOCK_SIZE; Z.div_mod_to_equations; lia].
  - s12.
  - intros b Hb. s12.
Qed.
Lemma SP_rinfo : WOK_rinfo st W.
Proof. intros c Hc. (nelimp (ris_range st WF) 4%nat; intros X1 X2 X3 X4). unfold KNUMCLASSES in Hc. apply SZprim; unfold rinfo; lia. Qed.
Lemma SP_regions : WOK_regions st W.
Proof.
  intros c Hc. pose proof (region_facts st WF c Hc) as RF. cbn zeta in RF.
  (nelim RF 10%nat; intros X1 X2 X3 X4 X5 X6 X7 X8 X9 X10).
  assert (FB : fabeg st c = rbeg st c + KFREEARRAY_OFF) by reflexivity.
  unfold KHIGHMEM_BEG, AIMG_HI, KREGIONSIZE, KFREEARRAY_OFF, KFREEARRAY_SIZE in *.
  split.
  - intros i Hi. pose proof (wc_num_freed st c (wf_class_ok st WF c Hc)) as NF. apply SZprim; lia.
  - replace ((r_mapped (rg st c) - r_allocated (rg st c)) / 8) with (SH (rbeg st c + r_mapped (rg st c)) - SH (rbeg st c + r_allocated (rg st c)))
      by (rewrite !rt_SH_aligned_add by exact X8; Z.div_mod_to_equations; lia).
    apply SZprim_sh; lia.
Qed.
Lemma SP_avail : WOK_avail st W.
Proof.
  intros c k Hc Hk.
  pose proof (region_facts st WF c Hc) as RF. cbn zeta in RF. (nelim RF 10%nat; intros X1 X2 X3 X4 X5 X6 X7 X8 X9 X10).
  destruct (Z.eq_dec c 0) as [->|NZ].
  { exfalso. unfold avail_cptrs in Hk. pose proof (wb_class0 st (wf_base_ok st WF)) as [E1 E2]. rewrite E1, E2 in Hk. cbn in Hk.
    unfold apend_cptrs in Hk. apply in_map_iff in Hk as ([c' k'] & _ & Hf). apply filter_In in Hf as [Hin Hb]. cbn [fst] in Hb.
    apply Z.eqb_eq in Hb. subst c'. pose proof (wq_apend st (wf_quar_ok st WF) _ Hin). cbn [fst] in *. lia. }
  assert (CV : carved_cptr st c k).
  { apply (wc_used_carved st c (wf_class_ok st WF c Hc)). unfold used_cptrs. rewrite !in_app_iff. apply in_app_iff in Hk. tauto. }
  (nelim (carved_chunk st WF c k Hc ltac:(lia) CV) 3%nat; intros C1 C2 C3).
  pose proof (csize_pos c ltac:(unfold KNUMCLASSES in Hc; lia)) as SP. pose proof (csize_mod32 c ltac:(unfold KNUMCLASSES in Hc; lia)) as SM.
  assert (AL : cptr_addr st c k mod 8 = 0).
  { apply (mod0_of_sub _ (rbeg st c) 8 ltac:(lia)); [| exact X8]. apply (mod0_trans _ 8 (csize c)); [lia|lia| apply (mod0_trans _ 8 32); [lia|lia|reflexivity|exact SM]| exact C3]. }
  replace (csize c / 8) with (SH (cptr_addr st c k + csize c) - SH (cptr_addr st c k)) by (rewrite rt_SH_aligned_add by exact AL; lia).
  unfold KHIGHMEM_BEG, AIMG_HI, KREGIONSIZE, KFREEARRAY_OFF in *. apply SZprim_sh; lia.
Qed.
Lemma SPt : forall a sz, T <= a -> a + sz <= T + T_STATS -> disjoint_from W a sz.
Proof.
  intros a sz H1 H2. eapply SZloose; [exact (wb_t_loose st (wf_base_ok st WF))| lia| unfold T_STATS in *; lia| lia].
Qed.
Lemma SP_cache : WOK_cache st W.
Proof.
  intros c Hc. pose proof (wc_cache_max st c (wf_class_ok st WF c Hc)) as CM. pose proof (cmaxcount_le16 c). unfold KNUMCLASSES in Hc.
  split.
  - apply SPt; unfold pcaddr, acache, T_ACACHE, T_STATS; lia.
  - intros i Hi. apply SPt; unfold pcaddr, acache, T_ACACHE, T_STATS; lia.
Qed.
Lemma SP_thread : WOK_thread st W.
Proof.
  unfold WOK_thread.
  split; [apply SPt; unfold T_STATS; lia|].
  split; [apply SPt; unfold qcache_t, T_QCACHE, T_STATS; lia|].
  split; [eapply SZloose; [exact (wb_t_loose st (wf_base_ok st WF))| unfold T_UNWINDING; lia| unfold T_UNWINDING; lia| lia]|].
  (nelim (wb_ctx_loose st (wf_base_ok st WF)) 5%nat; intros cb ck CL1 CL2 CL3). pose proof (wb_ctx_t st (wf_base_ok st WF)) as CT.
  (nelim (loose0_range st WF _ _ CL1) 4%nat; intros Q1 Q2 Q3 Q4).
  assert (CTX : forall a sz, st_ctx st <= a -> a + sz <= st_ctx st + 160 -> disjoint_from W a sz).
  { intros a sz H1 H2. eapply SZloose; [exact CL1| lia| lia|]. unfold T_STATS, T_UNWINDING. lia. }
  split; [apply CTX; unfold CTX_TID; lia|].
  split; [apply CTX; unfold CTX_THREAD; lia|].
  unfold A_TSD_PTR, A_TSD_MAIN, A_DTV_PTR, A_DTV, A_TLSMOD, A_FSTLS_CELL, A_DTLS_OFF, ATP in *.
  split; [s12|]. split; [s12|]. split; [s12|]. split; [s12|]. split; [s12|]. split; [s12|].
  (nelim (wb_dtls_loose st (wf_base_ok st WF)) 5%nat; intros db dk DL1 DL2 DL3). pose proof (wb_dtls_t st (wf_base_ok st WF)) as DT.
  eapply SZloose; [exact DL1| lia| lia| unfold T_STATS, T_UNWINDING; lia].
Qed.
Lemma SP_block : forall A n', In (A, n') (all_blocks st) -> A <> sec_user mb -> WOK_block W A n'.
Proof.
  intros A n' HB NEU.
  (nelimp (block_geom st WF A n' HB) 11%nat; intros Gn GA K X Y CE L16 H16 EA Gp Gs). unfold usz in Y. unfold KHIGHMEM_BEG, AIMG_HI in K.
  pose proof (rz_size_range n') as (Z1 & Z2).
  assert (ASZ : b_hi A n' = b_lo A n' + asz n') by reflexivity.
  apply WOK_block_intro.
  - intros a sz Ha Hs. destruct (bprim n') eqn:EP.
    + (nelim (Gp eq_refl) 6%nat; intros _ _ _ Q1 Q2 _). apply SZprim; lia.
    + (nelim (Gs eq_refl) 3%nat; intros S1' T1 _). eapply (SZsec (b_lo A n', n')); [exact S1'| | cbn [fst]; lia| cbn [fst snd]; lia].
      cbn [fst]. unfold b_lo. rewrite EP. exact (block_map_other A n' HB EP NEU).
  - unfold sh_tot. replace (asz n' / 8) with (SH (b_hi A n') - SH (b_lo A n')).
    2:{ rewrite ASZ, rt_SH_aligned_add by (apply (mod0_trans _ 8 16); [lia|lia|reflexivity|exact L16]).
        destruct (bprim n') eqn:EP; [(nelim (prim_facts n' EP) 5%nat; intros _ _ F3 F4 F5); rewrite F5 | (nelim (sec_facts n' EP) 6%nat; intros _ _ F3 _ F5 _); rewrite F5]; Z.div_mod_to_equations; lia. }
    destruct (bprim n') eqn:EP.
    + (nelim (Gp eq_refl) 6%nat; intros _ _ _ Q1 Q2 _). apply SZprim_sh; lia.
    + (nelim (Gs eq_refl) 3%nat; intros S1' T1 _). eapply (SZsec_sh (b_lo A n', n')); [exact S1'| | cbn [fst]; lia| lia| cbn [fst snd]; lia].
      cbn [fst]. unfold b_lo. rewrite EP. exact (block_map_other A n' HB EP NEU).
  - rewrite EA at 2. unfold sh_left, SEC_HDR, SEC_RZ. destruct (bprim n') eqn:EP.
    + Z.div_mod_to_equations. lia.
    + (nelim (sec_facts n' EP) 3%nat; intros _ F2 _). rewrite F2. cbn. lia.
Qed.
Lemma SP_batches : WOK_batches st W.
Proof.
  intros b Hb.
  (nelim (batch_geom st WF b Hb) 5%nat; intros BB BF R1 R2 AL).
  destruct (wq_batch st (wf_quar_ok st WF) b Hb) as [CNT _].
  pose proof (region_facts st WF 24 ltac:(unfold KNUMCLASSES; lia)) as RF. cbn zeta in RF. (nelim RF 10%nat; intros X1 X2 X3 X4 X5 X6 X7 X8 X9 X10).
  unfold KHIGHMEM_BEG, AIMG_HI, KREGIONSIZE, KFREEARRAY_OFF, QBATCH_SIZE, QBATCH_CAP in *.
  split; [| split].
  - apply SZprim; lia.
  - intros i Hi. apply SZprim; lia.
  - assert (AL8 : qb_addr b mod 8 = 0) by (apply (mod0_trans _ 8 32); [lia|lia|reflexivity|exact AL]).
    replace 1024 with (SH (qb_addr b + 8192) - SH (qb_addr b)) by (rewrite rt_SH_aligned_add by exact AL8; change (8192 / 8) with 1024; lia).
    apply SZprim_sh; lia.
Qed.
Lemma SP_ptrarr : WOK_ptrarr st W.
Proof.
  geom. (nelimp (pa_range st WF) 5%nat; intros Q1 Q2 Q3 Q4 Q5). unfold KHIGHMEM_BEG, AIMG_HI in Q1. pose proof (pa_vs_map st WF mb n spz_sec) as D1.
  assert (PT : st_pa st + PTRARR_RES_SIZE <= T \/ T + 4096 <= st_pa st).
  { pose proof (wb_pwdj st (wf_base_ok st WF)) as PW. rewrite rt_ranges_tail in PW.
    pose proof (pwdj_app_disj _ _ (st_pa st, st_pa st + PTRARR_RES_SIZE) (T, T + 4096) PW ltac:(right; left; reflexivity)
      ltac:(apply in_or_app; left; apply in_map_iff; exists (st_t st, 4096); split; [reflexivity| exact (wb_t_loose st (wf_base_ok st WF))])) as D.
    cbn [fst snd] in D. lia. }
  split.
  - intros i Hi. apply spz_disj; unfold CEIL, T_STATS, T_UNWINDING in *; blia.
  - intros e He. destruct (ws_spend st (wf_sec_ok st WF) e He) as [HE _]. pose proof (sec_range st WF e HE) as (R1 & R2). unfold KHIGHMEM_BEG, AIMG_HI in R1.
    pose proof (t_vs_sec st WF e HE) as D2.
    pose proof (ws_entry st (wf_sec_ok st WF) e HE) as (EP & _). (nelimp (sec_facts (snd e) EP) 5%nat; intros _ _ _ SZ _). unfold usz in SZ.
    destruct (Z.eq_dec (fst e) mb) as [E|NE].
    + apply spz_disj; unfold CEIL, T_STATS, T_UNWINDING in *; blia.
    + pose proof (sec_vs_map st WF mb n spz_sec e HE NE) as D3. apply spz_disj; unfold CEIL, T_STATS, T_UNWINDING in *; blia.
Qed.
Lemma SP_fs : WOK_fs st W.
Proof.
  pose proof (wb_fs_loose st (wf_base_ok st WF)) as FL. (nelimp (t_page st WF) 4%nat; intros _ _ _ TF). unfold framefree in TF.
  assert (OBJ : forall a sz, st_fs st <= a -> a + sz <= st_fs st + FS_TOTAL -> disjoint_from W a sz).
  { intros a sz H1 H2. eapply SZloose; [exact FL| exact H1| exact H2| lia]. }
  unfold WOK_fs. split; [| split; [| split; [| split]]].
  - intros k Hk. apply OBJ; unfold FS_TOTAL; lia.
  - apply OBJ; unfold FS_TOTAL; lia.
  - apply OBJ; unfold FS_TOTAL; lia.
  - intros k pos Hk Hp. pose proof (flags_ok k Hk) as [O1 O2]. apply OBJ; unfold fflag_addr, FS_TOTAL in *; lia.
  - intros F k Hin. (nelimp (frame_range st WF F k Hin) 4%nat; intros Hk X1 X2 _). pose proof (fsz_12 k Hk) as (FZ & _).
    assert (8 <= fsz k) by (rewrite FZ; destruct Hk as [-> | ->]; cbn; lia).
    apply OBJ; unfold FS_FRAMES_OFF in *; lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma psz2_others : forall m m', munch W m m' -> wmono bsegs m m' -> RTREP st m ->
  R_link m' /\ R_consts st m' /\ R_alloc st m' /\ R_rinfo st m' /\ R_regions st m' /\ R_avail st m' /\ R_cache st m' /\ R_thread st m'
  /\ R_batches st m' /\ R_ptrarr st m' /\ R_depot st m' /\ R_fs st m' /\ R_ia m' /\ R_lowshadow m'.
Proof.
  intros m m' MU WM HR.
  Local Ltac tapp2 T st WF W m m' MU WM :=
    first [ eapply (T st WF W m m' MU WM) | eapply (T st W m m' MU WM) | eapply (T st W m m' MU) | eapply (T W m m' MU WM) | eapply (T W m m' MU) ].
  split; [tapp2 T_link st WF W m m' MU WM; [exact (rr_link st m HR)| apply SP_link]|].
  split; [tapp2 T_consts st WF W m m' MU WM; [exact (rr_consts st m HR)| apply SP_consts]|].
  split; [tapp2 T_alloc st WF W m m' MU WM; [exact (rr_alloc st m HR)| apply SP_alloc]|].
  split; [tapp2 T_rinfo st WF W m m' MU WM; [exact (rr_rinfo st m HR)| apply SP_rinfo]|].
  split; [tapp2 T_regions st WF W m m' MU WM; [exact (rr_regions st m HR)| apply SP_regions]|].
  split; [tapp2 T_avail st WF W m m' MU WM; [exact (rr_avail st m HR)| apply SP_avail]|].
  split; [tapp2 T_cache st WF W m m' MU WM; [exact (rr_cache st m HR)| apply SP_cache]|].
  split; [tapp2 T_thread st WF W m m' MU WM; [exact (rr_thread st m HR)| apply SP_thread]|].
  split; [tapp2 T_batches st WF W m m' MU WM; [exact (rr_batches st m HR)| apply SP_batches]|].
  split; [tapp2 T_ptrarr st WF W m m' MU WM; [exact (rr_ptrarr st m HR)| apply SP_ptrarr]|].
  split; [tapp2 T_depot st WF W m m' MU WM; [exact (rr_depot st m HR)| apply SP_depot]|].
  split; [tapp2 T_fs st WF W m m' MU WM; [exact (rr_fs st m HR)| apply SP_fs]|].
  split; [tapp2 T_ia st WF W m m' MU WM; [exact (rr_ia st m HR)| apply SP_ia]|].
  tapp2 T_lowshadow st WF W m m' MU WM; [exact (rr_lowshadow st m HR)| apply SP_lowshadow].
Qed.

Lemma psz2_block : forall m m' md A n', munch W m m' -> wmono bsegs m m' -> In (A, n') (all_blocks st) -> A <> sec_user mb ->
  R_block st m md A n' -> R_block st m' md A n'.
Proof. intros m m' md A n' MU WM HB NE RB. eapply (T_block st WF W m m' MU WM); [exact HB| exact RB| exact (SP_block A n' HB NE)]. Qed.
End PSZ2.


Theorem RTREP_pshadow_sec : forall st m m' W A n,
  RTWF st -> RTREP st m -> In (A, n) (st_qpend st) -> bprim n = false ->
  munch W m m' -> wmono bsegs m m' -> Forall (psz_ok A n) W ->
  RTREP st m'.
Proof.
  intros st m m' W A n WF HR HIN HP MU WM HW.
  assert (HB : In (A, n) (all_blocks st)) by (unfold all_blocks; rewrite !in_app_iff; right; right; exact HIN).
  (nelimp (block_geom st WF A n HB) 11%nat; intros Gn GA K X Y CE L16 H16 EA Gp Gs).
  (nelim (Gs HP) 4%nat; intros HSEC EH Y2 M4).
  pose proof (qcr_carve_sec_proof st m A n WF HR ltac:(right; exact HIN) HP) as CS. cbv zeta in CS. (nelim CS 3%nat; intros _ EAU _).
  assert (ELO : b_lo A n = b_map_beg A) by (unfold b_lo; rewrite HP; reflexivity).
  set (mb := b_map_beg A) in *. rewrite ELO in *.
  set (ru := (usz n + 7) / 8 * 8) in *.
  assert (RUB : ru mod 8 = 0 /\ usz n <= ru < usz n + 8) by (subst ru; clear; Z.div_mod_to_equations; lia).
  assert (L8 : mb mod 8 = 0) by (clear - L16; Z.div_mod_to_equations; lia).
  assert (A8 : A mod 8 = 0) by (clear - GA; Z.div_mod_to_equations; lia).
  assert (Z2 : 0 <= ru / 8) by (clear - RUB; unfold usz in RUB; Z.div_mod_to_equations; lia).
  assert (SHIN : SH mb <= SH A /\ SH A + ru / 8 <= SH (mb + smapsize n)).
  { split; [apply rt_SH_mono; lia|]. rewrite <- (rt_SH_aligned_add A ru A8). apply rt_SH_mono. rewrite <- EH. clear - Y2 RUB. lia. }
  assert (HW' : Forall (spz_ok st mb n) W).
  { eapply Forall_impl; [| exact HW]. intros [lo hi] Z. unfold psz_ok in Z. unfold spz_ok. cbn [fst snd] in *. fold ru in Z.
    destruct Z as [Z|Z]; [right; left; clear - Z SHIN; lia| right; right; right; exact Z]. }
  (nelim (psz2_others st WF mb n HSEC W HW' m m' MU WM HR) 14%nat; intros X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14).
  pose proof (wk_nodup st (wf_blocks_ok st WF)) as NDA. unfold all_blocks in NDA.
  rewrite EH in K, Y, CE.
  (nelimp (ablk_lin _ _ K) 4%nat; intros KI K0 KT _).
  pose proof (ablk_shad_lin _ _ K ltac:(unfold usz in *; lia)) as (KS1 & KS2).
  pose proof (ablk_shad_disj _ _ K ltac:(unfold usz in *; lia)) as KSD.
  pose proof (rt_SH_mono (mb + smapsize n) (mb + smapsize n + 7) ltac:(lia)) as KSM.
  assert (DB : forall a sz, mb <= a -> a + sz <= mb + smapsize n -> disjoint_from W a sz).
  { intros a sz H1 H2. apply (disjoint_from_forallq _ W a sz HW). intros lo hi Z. unfold psz_ok in Z. cbn [fst snd] in Z. fold ru in Z.
    clear - H1 H2 Z KSD KSM SHIN Z2 CE. unfold CEIL in *. set (r8 := ru / 8) in *. clearbody r8. lia. }
  assert (RBP : R_block st m' BPend A n).
  { destruct (proj2 (rr_quar st m HR) A n HIN) as ((b1 & cid & HDR & HB1) & BG & SC & V & SHD).
    pose proof (rz_size_range n) as (RZ1 & _).
    split; [exists b1, cid; split; [| exact HB1]; eapply (rwT W m m' MU WM); [exact HDR|]; apply DB; unfold b_chunk_beg, hdr_cells; cbn [cells_size Cells.csize Nat.add]; clear - X Y; unfold usz in *; lia|].
    split; [intros HRZ; eapply (rwT W m m' MU WM); [exact (BG HRZ)|]; apply DB; cbn [cells_size Cells.csize Nat.add]; unfold b_alloc_beg;
            unfold sh_left in EA; rewrite HP in EA; unfold SEC_HDR, SEC_RZ in EA; clear - EA RZ1 Y HRZ; unfold usz in *; lia|].
    split.
    { intros _. (nelim (SC HP) 3%nat; intros V1 V2 HCS). fold mb in V1, V2, HCS. unfold R_secmap. fold mb.
      split; [eapply (visTo m m' WM); [exact V1| apply oclr_of_ablk; exact K| exact CE]|].
      split; [eapply stk_wmono_noseg; [exact V2| exact WM| clear - KS1; unfold AIMG_HI, KLOWSHADOW_BEG in *; lia]|].
      eapply (rwT W m m' MU WM); [exact HCS|]. apply DB; cbn [cells_size Cells.csize Nat.add]; [lia|].
      clear - Y2 EH X. unfold usz in *. lia. }
    split; [eapply (visTo m m' WM); [exact V| rewrite ELO, EH; apply oclr_of_ablk; exact K| rewrite EH; exact CE]|].
    unfold R_bshadow. rewrite HP. exact I. }
  assert (RL : R_live st m').
  { intros A' n' Hin'. apply (psz2_block st WF mb n HSEC W HW' m m' BLive A' n' MU WM); [unfold all_blocks; rewrite !in_app_iff; left; exact Hin'| | exact (rr_live st m HR A' n' Hin')].
    rewrite <- EAU. intros ->. rewrite app_assoc in NDA. eapply (nodup_fst_app _ _ A n' n NDA); [apply in_or_app; left; exact Hin'| exact HIN]. }
  assert (RQ : R_quar st m').
  { split.
    - intros A' n' Hin'. apply (psz2_block st WF mb n HSEC W HW' m m' BQuar A' n' MU WM); [unfold all_blocks; rewrite !in_app_iff; right; left; exact Hin'| | exact (proj1 (rr_quar st m HR) A' n' Hin')].
      rewrite <- EAU. intros ->. eapply (nodup_fst_app _ _ A n' n); [| apply in_or_app; right; exact Hin'| exact HIN]. rewrite <- app_assoc. exact NDA.
    - intros A' n' Hin'. destruct (Z.eq_dec A' A) as [->|NE].
      + assert (n' = n).
        { pose proof (NoDup_map_fst_unique (st_lb st ++ qelems st ++ st_qpend st) A n' n NDA) as U. apply U; rewrite !in_app_iff; tauto. }
        subst n'. exact RBP.
      + apply (psz2_block st WF mb n HSEC W HW' m m' BPend A' n' MU WM); [unfold all_blocks; rewrite !in_app_iff; right; right; exact Hin'| rewrite <- EAU; exact NE| exact (proj2 (rr_quar st m HR) A' n' Hin')]. }
  constructor; assumption.
Qed.

(* [comment removed for export] *)
Theorem RTREP_pshadow : forall st m m' W A n,
  RTWF st -> RTREP st m -> In (A, n) (st_qpend st) ->
  munch W m m' -> wmono bsegs m m' -> Forall (psz_ok A n) W ->
  RTREP st m'.
Proof.
  intros st m m' W A n WF HR HIN MU WM HW. destruct (bprim n) eqn:EP;
    [eapply RTREP_pshadow_prim| eapply RTREP_pshadow_sec]; eassumption.
Qed.

End CeilWrap.
End RTW_q_psz.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LMeasure.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_front.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_sec_hz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_sec_fpU.
Module RTW_sec_dstate2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LMeasure OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_secz.RT_artZ OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_front OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_sec.RTW_secondary_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_secz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_sec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_spz.RTW_sec_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstate OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_hz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_fpU OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.ABand.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma munch_interpolate : forall W lo hi (m m' : word -> option byte),
  munch (W ++ [(lo, hi)]) m m' -> wmono bsegs m m' ->
  exists mX, munch W m mX /\ wmono bsegs m mX /\ munch [(lo, hi)] mX m' /\ wmono bsegs mX m'.
Proof.
  intros W lo hi m m' MU WM.
  exists (fun x => if ((lo <=? bv_unsigned x) && (bv_unsigned x <? hi))%bool then m x else m' x).
  assert (OUTS : forall x : word, outside (W ++ [(lo, hi)]) (bv_unsigned x) <-> outside W (bv_unsigned x) /\ ~ (lo <= bv_unsigned x < hi)).
  { intros x. clear. induction W as [|[a b] W IH]; cbn; tauto. }
  split; [| split; [| split]].
  - intros x Hx. destruct (Z.leb_spec0 lo (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) hi); cbn [andb]; try reflexivity;
      (apply MU; apply OUTS; split; [exact Hx| lia]).
  - intros x Hv. unfold wview in *. destruct (Z.leb_spec0 lo (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) hi); cbn [andb]; try exact Hv; apply WM; exact Hv.
  - intros x Hx. cbn in Hx. destruct Hx as [Hx _]. destruct (Z.leb_spec0 lo (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) hi); cbn [andb]; try reflexivity. exfalso. lia.
  - intros x Hv. unfold wview in *. destruct (Z.leb_spec0 lo (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) hi); cbn [andb] in *; try exact Hv. apply WM. exact Hv.
Qed.

Lemma outside_In' : forall W lo hi x, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi).
Proof. induction W as [|[a c] W IH]; intros lo hi x Hx Hin; [destruct Hin|]. cbn in Hx. destruct Hx as [H1 H2].
  destruct Hin as [E|Hin]; [injection E; intros; subst; lia| exact (IH _ _ _ H2 Hin)]. Qed.

(* [comment removed for export] *)
Lemma munch_perm : forall W W' (m m' : word -> option byte), (forall iv, In iv W -> In iv W') -> munch W m m' -> munch W' m m'.
Proof.
  intros W W' m m' HI MU. eapply munch_weaken; [| exact MU]. unfold sub_fp. intros x Hx.
  assert (K : forall L, (forall iv, In iv L -> In iv W') -> outside L x).
  { induction L as [|[lo hi] L IH]; intros HL; [exact I|]. cbn. split; [| apply IH; intros iv Hiv; apply HL; right; exact Hiv].
    exact (outside_In' W' lo hi x Hx (HL _ (or_introl eq_refl))). }
  exact (K W HI).
Qed.

Lemma last_In : forall {A} (l : list A) d, l <> [] -> In (last l d) l.
Proof. intros A l d H. rewrite (app_removelast_last d H) at 2. apply in_or_app. right. left. reflexivity. Qed.

(* [comment removed for export] *)
Section DREP.
  Variables (st : rtstate) (mb n : Z) (b : qbatch) (d : Z).
  Hypothesis WF : RTWF st.
  Hypothesis HP : bprim n = false.
  Hypothesis QC : st_qcur st = [(b, d)].
  Hypothesis Hd : 0 <= d < qb_count b.
  Hypothesis EL : nthz (qb_elems b) d (0,0) = (sec_user mb, n).
  Let stD := st_secdereg st mb b d.
  Let idx := sec_index st mb.
  Let lst := last (st_sec st) (0,0).
  (* [comment removed for export] *)
  Definition dM : Z := if sec_index st mb <? nsec st - 1 then fst (last (st_sec st) (0,0)) else mb.
  Definition dMn : Z := if sec_index st mb <? nsec st - 1 then snd (last (st_sec st) (0,0)) else n.

  Lemma WFD : RTWF stD. Proof. exact (RTWF_dereg' st mb n b d WF HP QC Hd EL). Qed.

  (* [comment removed for export] *)
  Lemma sec_ne : st_sec st <> [].
  Proof. intros E. pose proof (mbn_in_sec' st mb n b d WF HP QC Hd EL) as H. rewrite E in H. exact H. Qed.
  Lemma lst_In' : In lst (st_sec st).
  Proof. unfold lst. apply last_In. exact sec_ne. Qed.
  Lemma lst_nth' : nthz (st_sec st) (nsec st - 1) (0,0) = lst.
  Proof.
    pose proof (idx_facts' st mb n b d WF HP QC Hd EL) as [HI HN]. unfold nsec, lst.
    exact (lst_nth (st_sec st) (sec_index st mb) (mb, n) (ws_nodup st (wf_sec_ok st WF)) HI HN).
  Qed.
  Lemma dM_In : In (dM, dMn) (st_sec st).
  Proof.
    unfold dM, dMn. destruct (sec_index st mb <? nsec st - 1); [| exact (mbn_in_sec' st mb n b d WF HP QC Hd EL)].
    rewrite <- surjective_pairing. exact lst_In'.
  Qed.
  Lemma dM_range : ablk dM (dM + smapsize dMn) /\ dM + smapsize dMn <= CEIL /\ dM mod 4096 = 0 /\ 8192 <= smapsize dMn.
  Proof.
    pose proof (sec_entry_range st WF dM dMn dM_In) as (R1 & R2 & R3 & R4 & R5 & R6).
    pose proof (smapsize_pos dMn ltac:(lia)) as [S1 _]. split; [exact R1| unfold CEIL in *; lia].
  Qed.
  Lemma mb_range : ablk mb (mb + smapsize n) /\ mb + smapsize n <= CEIL /\ mb mod 4096 = 0 /\ 8192 <= smapsize n.
  Proof.
    pose proof (sec_entry_range st WF mb n (mbn_in_sec' st mb n b d WF HP QC Hd EL)) as (R1 & R2 & R3 & R4 & R5 & R6).
    pose proof (smapsize_pos n ltac:(lia)) as [S1 _]. split; [exact R1| unfold CEIL in *; lia].
  Qed.
  (* [comment removed for export] *)
  Lemma dM_other : idx < nsec st - 1 -> dM = fst lst /\ fst lst <> mb /\ (fst lst + smapsize (snd lst) <= mb \/ mb + smapsize n <= fst lst).
  Proof.
    intros LT. pose proof (idx_facts' st mb n b d WF HP QC Hd EL) as [HI HN]. fold idx in HI, HN.
    assert (E : dM = fst lst) by (unfold dM; fold idx; destruct (Z.ltb_spec0 idx (nsec st - 1)); [reflexivity| lia]).
    split; [exact E|].
    assert (NE : fst lst <> mb).
    { intros EQ. pose proof (ws_nodup st (wf_sec_ok st WF)) as ND.
      pose proof (index_of_nthz (st_sec st) idx (0,0) ND ltac:(unfold nsec in *; lia)) as I1. rewrite HN in I1. cbn [fst] in I1.
      pose proof (index_of_nthz (st_sec st) (nsec st - 1) (0,0) ND ltac:(unfold nsec in *; lia)) as I2. rewrite lst_nth', EQ in I2. lia. }
    split; [exact NE|].
    destruct (sec_disj st WF mb n (fst lst) (snd lst) (mbn_in_sec' st mb n b d WF HP QC Hd EL) ltac:(rewrite <- surjective_pairing; exact lst_In')) as [H|H]; [exfalso; exact (NE H)| exact H].
  Qed.
  Lemma spend_not_mb : forall e, In e (st_spend st) -> fst e <> mb.
  Proof.
    intros e He E. destruct (ws_spend st (wf_sec_ok st WF) e He) as [HE HNB].
    assert (EE : e = (mb, n)).
    { pose proof (NoDup_map_fst_unique (st_sec st) mb (snd e) n (ws_nodup st (wf_sec_ok st WF))) as U.
      rewrite (surjective_pairing e), E. f_equal. apply U; [rewrite <- E, <- surjective_pairing; exact HE| exact (mbn_in_sec' st mb n b d WF HP QC Hd EL)]. }
    subst e. cbn [fst snd] in HNB. exact (HNB (A_in_blocks' st mb n b d WF QC Hd EL)).
  Qed.
  (* [comment removed for export] *)
  Lemma blockD_sec : forall A k, In (A, k) (all_blocks stD) -> bprim k = false ->
    In (b_map_beg A, k) (st_sec stD) /\ In (b_map_beg A) (map fst (st_sec stD)) /\ b_map_beg A <> mb.
  Proof.
    intros A k HB HPk.
    pose proof (wk_block stD (wf_blocks_ok stD WFD) (A, k) HB) as WB. unfold wf_block in WB. cbn [fst snd] in WB. destruct WB as (_ & _ & _ & HS).
    specialize (HS HPk). split; [exact HS|]. split; [apply in_map_iff; exists (b_map_beg A, k); split; [reflexivity| exact HS]|].
    intros E. assert (EA : A = sec_user mb) by (unfold b_map_beg, sec_user in *; lia). subst A.
    exact (A_notin_blocksD' st mb n b d WF QC Hd EL k HB).
  Qed.

  (* [comment removed for export] *)
  Lemma R_consts_dereg : forall m, R_consts st m -> R_consts stD m.   Proof. unfold stD. destruct st. intros m H. exact H. Qed.
  Lemma R_rinfo_dereg : forall m, R_rinfo st m -> R_rinfo stD m.     Proof. unfold stD. destruct st. intros m H. exact H. Qed.
  Lemma R_regions_dereg : forall m, R_regions st m -> R_regions stD m. Proof. unfold stD. destruct st. intros m H. exact H. Qed.
  Lemma R_avail_dereg : forall m, R_avail st m -> R_avail stD m.     Proof. unfold stD. destruct st. intros m H. exact H. Qed.
  Lemma R_cache_dereg : forall m, R_cache st m -> R_cache stD m.     Proof. unfold stD. destruct st. intros m H. exact H. Qed.
  Lemma R_thread_dereg : forall m, R_thread st m -> R_thread stD m.   Proof. unfold stD. destruct st. intros m H. exact H. Qed.
  Lemma R_depot_dereg : forall m, R_depot st m -> R_depot stD m.     Proof. unfold stD. destruct st. intros m H. exact H. Qed.
  Lemma R_fs_dereg : forall m, R_fs st m -> R_fs stD m.              Proof. unfold stD. destruct st. intros m H. exact H. Qed.

  Lemma R_batches_dereg : forall m, R_batches st m -> R_batches stD m.
  Proof.
    intros m (Q1 & Q2 & Q3 & Q4). pose proof (st_secdereg_fields st mb b d WF QC) as (_ & EQ & _). fold stD in EQ.
    unfold R_batches. rewrite EQ.
    replace (st_qthread stD) with (st_qthread st) by (unfold stD; destruct st; reflexivity).
    replace (st_qglobal stD) with (st_qglobal st) by (unfold stD; destruct st; reflexivity).
    replace (st_qtmp stD) with (st_qtmp st) by (unfold stD; destruct st; reflexivity).
    split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|].
    intros bd [<-|[]]. cbn [fst]. apply (Q4 (b, d)). rewrite QC. left. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma R_block_dereg : forall m md A k, In (A, k) (all_blocks stD) ->
    (bprim k = false -> b_map_beg A <> dM) -> R_block st m md A k -> R_block stD m md A k.
  Proof.
    intros m md A k HB NM (H1 & H2 & H3 & H4 & H5). split; [exact H1|]. split; [exact H2|]. split; [| split; [exact H4| exact H5]].
    intros HPk. destruct (H3 HPk) as (V1 & V2 & HC). split; [exact V1|]. split; [exact V2|].
    replace (sec_index stD (b_map_beg A)) with (sec_index st (b_map_beg A)); [exact HC|].
    destruct (blockD_sec A k HB HPk) as (_ & HIn & _).
    pose proof (dereg_index' st mb n b d WF HP QC Hd EL (b_map_beg A) HIn) as (E & _ & _). fold stD in E. rewrite E.
    specialize (NM HPk). unfold dM in NM.
    destruct (Z.eqb_spec (b_map_beg A) (fst (last (st_sec st) (0,0)))) as [EQ|NE]; [| reflexivity].
    destruct (sec_index st mb <? nsec st - 1); [exfalso; exact (NM EQ)| reflexivity].
  Qed.

  Lemma R_block_dereg_moved : forall mX m1 md A k, idx < nsec st - 1 ->
    munch [(fst lst + 24, fst lst + 32)] mX m1 -> wmono bsegs mX m1 ->
    In (A, k) (all_blocks stD) -> bprim k = false -> b_map_beg A = fst lst ->
    R_block st mX md A k -> rw_cells bsegs m1 (fst lst + 24) [W8 idx] -> R_block stD m1 md A k.
  Proof.
    intros until k. intros LT MU WM HB HPk EM (H1 & H2 & H3 & H4 & H5) NEW.
    pose proof (dM_other LT) as (ED & NE & _). pose proof dM_range as (D1 & D2 & D3 & D4). rewrite ED in D1, D2, D3.
    assert (EA : A = sec_user (fst lst)) by (unfold b_map_beg, sec_user in *; lia).
    pose proof (rz_size_range k) as [RZ _]. unfold KHIGHMEM_BEG, AIMG_HI, CEIL in D1, D2.
    split.
    { destruct H1 as (b1 & cid & HC & HB1). exists b1, cid. split; [| exact HB1].
      eapply rw_cells_transport; [exact HC| exact MU| exact WM| cbn; unfold b_chunk_beg, sec_user, SEC_HDR, SEC_RZ in *; lia]. }
    split.
    { intros Hrz. eapply rw_cells_transport; [exact (H2 Hrz)| exact MU| exact WM| cbn; unfold b_alloc_beg, sec_user, SEC_HDR, SEC_RZ in *; lia]. }
    split.
    { intros _. destruct (H3 HPk) as (V1 & V2 & HC). rewrite EM in *.
      pose proof (rt_SH_bounds (fst lst) ltac:(blia)) as SB.
      split; [eapply stk_wmono_noseg; [exact V1| exact WM| unfold AIMG_HI; blia]|].
      split; [eapply stk_wmono_noseg; [exact V2| exact WM| unfold AIMG_HI; lia]|].
      change [W8 (fst lst); W8 (smapsize k); W8 (needed k); W8 (sec_index stD (fst lst))]
        with ([W8 (fst lst); W8 (smapsize k); W8 (needed k)] ++ [W8 (sec_index stD (fst lst))]).
      apply rw_cells_app. split.
      - eapply rw_cells_transport; [exact (rw_cells_take mX (fst lst) [_; _; _] [_] HC)| exact MU| exact WM| cbn; lia].
      - cbn [cells_size Cells.csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. replace (sec_index stD (fst lst)) with idx; [exact NEW|].
        destruct (blockD_sec A k HB HPk) as (_ & HIn & _). rewrite EM in HIn.
        pose proof (dereg_index' st mb n b d WF HP QC Hd EL (fst lst) HIn) as (E & _ & _). fold stD in E. rewrite E.
        rewrite Z.eqb_refl. fold idx. destruct (Z.ltb_spec0 idx (nsec st - 1)); [reflexivity| lia]. }
    split.
    { eapply stk_wmono_noseg; [exact H4| exact WM|]. unfold b_lo. rewrite HPk, EM. unfold AIMG_HI. blia. }
    unfold R_bshadow in *. rewrite HPk in *. destruct md; [| exact I| exact I].
    destruct (blockD_sec A k HB HPk) as (HSk & _ & _). rewrite EM in HSk.
    destruct (secD_In' st mb n b d WF HP QC Hd EL _ HSk) as [HSk' _].
    pose proof (sec_entry_range st WF (fst lst) k HSk') as (_ & K2 & _). pose proof (sec_facts k HPk) as (_ & _ & _ & K4 & _).
    eapply rw_cells_transport; [exact H5| exact MU| exact WM|]. unfold disjoint_from. split; [| exact I].
    rewrite zcells_size. unfold zlen. rewrite rt_shadow_enc_length by (unfold usz; lia).
    (* [comment removed for export] *)
    pose proof (ablk_disj_band _ _ D1) as BD.
    unfold SH, SHADOW_OFFSET, sec_user, SEC_HDR, SEC_RZ, CEIL in *.
    destruct BD as [BD|BD]; [right|left]; Z.div_mod_to_equations; blia.
  Qed.

  (* [comment removed for export] *)
  Lemma RTREP_nsec_dereg : forall mX m1, RTREP_nsec st mX -> munch [(dM + 24, dM + 32)] mX m1 -> wmono bsegs mX m1 ->
    (idx < nsec st - 1 -> rw_cells bsegs m1 (fst lst + 24) [W8 idx]) -> RTREP_nsec stD m1.
  Proof.
    intros mX m1 HN MU WM NEW.
    pose proof (hz_xfer st WF [(dM + 24, dM + 32)] dM dMn dM_In ltac:(constructor; [cbn; lia| constructor]) mX m1 MU WM HN)
      as (X1 & X2 & X4 & X5 & X6 & X7 & X8 & X11 & X13 & X14 & X15 & X16 & XB).
    destruct HN as (_ & _ & _ & _ & _ & _ & _ & L9 & Q10 & _).
    assert (BLK : forall md A k, In (A, k) (all_blocks stD) -> R_block st mX md A k -> R_block stD m1 md A k).
    { intros md A k HB RB. pose proof (blocksD_sub' st mb n b d WF QC Hd EL _ HB) as HBo.
      destruct (bprim k) eqn:Pk.
      - apply R_block_dereg; [exact HB| intros; congruence|]. apply XB; [exact HBo| intros; congruence| exact RB].
      - destruct (Z.eq_dec (b_map_beg A) dM) as [EQ|NEQ].
        + destruct (blockD_sec A k HB Pk) as (_ & _ & NMB).
          assert (LT : idx < nsec st - 1).
          { unfold dM in EQ. fold idx in EQ. destruct (Z.ltb_spec0 idx (nsec st - 1)); [assumption| exfalso; exact (NMB EQ)]. }
          pose proof (dM_other LT) as (ED & _). rewrite ED in MU, EQ.
          eapply R_block_dereg_moved; [exact LT| exact MU| exact WM| exact HB| exact Pk| exact EQ| exact RB| exact (NEW LT)].
        + apply R_block_dereg; [exact HB| intros _; exact NEQ|]. apply XB; [exact HBo| intros _; unfold b_lo; rewrite Pk; exact NEQ| exact RB]. }
    unfold RTREP_nsec.
    split; [exact X1|]. split; [exact (R_consts_dereg m1 X2)|]. split; [exact (R_rinfo_dereg m1 X4)|]. split; [exact (R_regions_dereg m1 X5)|].
    split; [exact (R_avail_dereg m1 X6)|]. split; [exact (R_cache_dereg m1 X7)|]. split; [exact (R_thread_dereg m1 X8)|].
    split. { intros A k Hin. replace (st_lb stD) with (st_lb st) in Hin by (unfold stD; destruct st; reflexivity).
             apply BLK; [unfold all_blocks; apply in_or_app; left; replace (st_lb stD) with (st_lb st) by (unfold stD; destruct st; reflexivity); exact Hin| exact (L9 A k Hin)]. }
    split. { destruct Q10 as [QA QB]. split.
             - intros A k Hin. apply BLK; [unfold all_blocks; rewrite !in_app_iff; right; left; exact Hin|].
               exact (QA A k (qelems_stD' st mb n b d WF QC Hd EL _ Hin)).
             - intros A k Hin. replace (st_qpend stD) with (st_qpend st) in Hin by (unfold stD; destruct st; reflexivity).
               apply BLK; [| exact (QB A k Hin)]. unfold all_blocks; rewrite !in_app_iff; right; right.
               replace (st_qpend stD) with (st_qpend st) by (unfold stD; destruct st; reflexivity). exact Hin. }
    split; [exact (R_batches_dereg m1 X11)|]. split; [exact (R_depot_dereg m1 X13)|]. split; [exact (R_fs_dereg m1 X14)|].
    split; [exact X15| exact X16].
  Qed.

  (* [comment removed for export] *)
  Lemma R_alloc_dereg_intro : forall W mv m j1 j2 j3 jg, R_alloc st mv -> munch W mv m -> wmono bsegs mv m ->
    disjoint_from W A_ALLOC 64 -> disjoint_from W A_QUAR 256 -> disjoint_from W A_MAXUSERSZ 13 ->
    rw_cells bsegs m A_SECONDARY [W8 4096; W8 (st_pa st); W8 (st_pa st); W8 PTRARR_RES_SIZE; CB 16 j1; W8 (st_nreserved st); W8 (nsec st - 1); CB 552 j2; W1 0; CB 7 j3] ->
    rw_cells bsegs m A_GSTATS [CB 40 jg] ->
    R_alloc stD m.
  Proof.
    intros W mv m j1 j2 j3 jg HA MU WM D1 D2 D3 SEC GST.
    destruct HA as ((k1 & k2 & k3 & X1) & _ & _ & (l1 & l2 & l3 & l4 & X4) & X5).
    pose proof (st_secdereg_fields st mb b d WF QC) as (_ & _ & _ & E4 & E5 & _). fold stD in E4, E5.
    pose proof (dereg_nsec' st mb n b d WF HP QC Hd EL) as EN. fold stD in EN. unfold R_alloc. rewrite E4, E5, EN.
    replace (st_pbase stD) with (st_pbase st) by (unfold stD; destruct st; reflexivity).
    replace (st_spacebeg stD) with (st_spacebeg st) by (unfold stD; destruct st; reflexivity).
    replace (st_qglobal stD) with (st_qglobal st) by (unfold stD; destruct st; reflexivity).
    split; [exists k1, k2, k3; eapply rw_cells_transport; [exact X1| exact MU| exact WM| exact D1]|].
    split; [exists j1, j2, j3; exact SEC|].
    split; [exists jg; exact GST|].
    split; [exists l1, l2, l3, l4; eapply rw_cells_transport; [exact X4| exact MU| exact WM| exact D2]|].
    eapply (ro_cells_transport bsegs W mv m); [exact X5| exact MU| exact D3].
  Qed.

  Lemma R_ptrarr_dereg_intro : forall W mv m, R_ptrarr st mv -> munch W mv m -> wmono bsegs mv m ->
    (forall i, 0 <= i < nsec st - 1 -> i <> idx -> disjoint_from W (st_pa st + 8 * i) 8) ->
    (forall e, In e (st_spend st) -> fst e <> dM -> disjoint_from W (fst e) 32) ->
    (forall e, In e (st_spend st) -> disjoint_from W (fst e) 24) ->
    (idx < nsec st - 1 -> rw_cells bsegs m (st_pa st + 8 * idx) [W8 (fst lst)]) ->
    (idx < nsec st - 1 -> rw_cells bsegs m (fst lst + 24) [W8 idx]) ->
    R_ptrarr stD m.
  Proof.
    intros W mv m (V & HC & HS) MU WM K1 K2 K3 NSLOT NHDR.
    pose proof (st_secdereg_fields st mb b d WF QC) as (E1 & _ & E3 & E4 & E5 & _). fold stD in E1, E3, E4, E5.
    pose proof (pa_range st WF) as (P1 & P2 & P3 & P4 & P5). pose proof (idx_facts' st mb n b d WF HP QC Hd EL) as [HI _]. fold idx in HI.
    pose proof (dereg_nsec' st mb n b d WF HP QC Hd EL) as EN. fold stD in EN. unfold R_ptrarr. rewrite E4, E3, E5, EN.
    split; [eapply stk_wmono_noseg; [exact V| exact WM| unfold AIMG_HI, KHIGHMEM_BEG in *; blia]|]. split.
    - intros i Hi. pose proof (secD_nth' st mb n b d WF HP QC Hd EL i Hi) as NT. fold stD idx lst in NT. rewrite NT.
      destruct (Z.eqb_spec i idx) as [->|NE]; [exact (NSLOT ltac:(lia))|].
      eapply rw_cells_transport; [exact (HC i ltac:(lia))| exact MU| exact WM| exact (K1 i Hi NE)].
    - intros e He. destruct (HS e He) as (V1 & V2 & HCe).
      destruct (ws_spend st (wf_sec_ok st WF) e He) as [HE _].
      pose proof (sec_entry_range st WF (fst e) (snd e) ltac:(rewrite <- surjective_pairing; exact HE)) as (R1 & R2 & R3 & R4 & _).
      pose proof (rt_SH_bounds (fst e) ltac:(unfold KHIGHMEM_BEG, AIMG_HI, CEIL in *; blia)) as SB.
      split; [eapply stk_wmono_noseg; [exact V1| exact WM| unfold AIMG_HI, KHIGHMEM_BEG in *; blia]|].
      split; [eapply stk_wmono_noseg; [exact V2| exact WM| unfold AIMG_HI in *; lia]|].
      (* [comment removed for export] *)
      assert (HIn : In (fst e) (map fst (st_sec stD))).
      { destruct (ws_spend stD (wf_sec_ok stD WFD) e ltac:(rewrite E3; exact He)) as [HE' _]. apply in_map_iff. exists e. split; [reflexivity| exact HE']. }
      pose proof (dereg_index' st mb n b d WF HP QC Hd EL (fst e) HIn) as (E & _ & _). fold stD in E. rewrite E. fold idx lst.
      destruct (Z.eqb_spec (fst e) (fst lst)) as [EQ|NEQ].
      + destruct (Z.ltb_spec0 idx (nsec st - 1)) as [LT|GE].
        * (* [comment removed for export] *)
          change [W8 (fst e); W8 (smapsize (snd e)); W8 (needed (snd e)); W8 idx]
            with ([W8 (fst e); W8 (smapsize (snd e)); W8 (needed (snd e))] ++ [W8 idx]).
          apply rw_cells_app. split.
          -- eapply rw_cells_transport; [exact (rw_cells_take mv (fst e) [_; _; _] [_] HCe)| exact MU| exact WM| exact (K3 e He)].
          -- cbn [cells_size Cells.csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite EQ. exact (NHDR LT).
        * eapply rw_cells_transport; [exact HCe| exact MU| exact WM| apply (K2 e He)].
          unfold dM. fold idx. destruct (Z.ltb_spec0 idx (nsec st - 1)); [lia| exact (spend_not_mb e He)].
      + eapply rw_cells_transport; [exact HCe| exact MU| exact WM| apply (K2 e He)].
        unfold dM. fold idx lst. destruct (Z.ltb_spec0 idx (nsec st - 1)); [exact NEQ| exact (spend_not_mb e He)].
  Qed.
End DREP.


End CeilWrap.
End RTW_sec_dstate2.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_sec_lib.
Module RTW_sec_dealloc3.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LMeasure OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_secz.RT_artZ OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_front OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_sec.RTW_secondary_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_secz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_sec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_spz.RTW_sec_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_lib.RTW_sec_alloc5 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstate RTW_sec_dstate2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.ABand.
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
(* [comment removed for export] *)
Lemma sec_map_has : forall st mo mb n, RTMODEL st mo -> In (mb, n) (st_sec st) -> 0 <= mb -> mb + smapsize n <= 2^64 -> 0 <= smapsize n ->
  map_has (vm_maps (m_vmmaps mo)) (Z_to_bv 64 mb) (Z_to_bv 64 (smapsize n)) = true.
Proof.
  intros st mo mb n HM Hin H0 H1 H2. destruct HM as (_ & _ & _ & _ & M5 & _).
  specialize (M5 (mb, smapsize n) ltac:(unfold rt_loose; rewrite !in_app_iff; right; left; apply in_map_iff; exists (mb, n); split; [reflexivity| exact Hin])).
  unfold zin, wz in M5. cbn [fst snd] in M5. unfold map_has. apply existsb_exists. exists (Z_to_bv 64 mb, Z_to_bv 64 (smapsize n)).
  split; [exact M5|]. cbn [fst snd]. rewrite !bv_eqb_refl. reflexivity.
Qed.
Lemma sec_plain_of : forall st mo mb n, RTMODEL st mo -> In (mb, n) (st_sec st) -> sec_plain mo mb (smapsize n).
Proof. intros st mo mb n HM Hin. destruct HM as (_ & _ & _ & _ & _ & _ & _ & _ & M9). exact (M9 (mb, n) Hin). Qed.
Lemma sec_win_of : forall st g mb n, SWIN st g -> In (mb, n) (st_sec st) -> sec_win g mb n.
Proof. intros st g mb n HS Hin. exact (HS (mb, n) Hin). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma RTSH_below_ceil : forall st x, RTWF st -> RTSH st x -> x < CEIL.
Proof.
  intros st x WF [H|[H|(b & Hb & H)]].
  - unfold SH, SHADOW_OFFSET, AIMG_HI, CEIL in *. Z.div_mod_to_equations. blia.
  - unfold KHIGHMEM_BEG, AIMG_HI, CEIL in *. lia.
  - pose proof (sb_range st WF b Hb). unfold CEIL. lia.
Qed.

Lemma GWIN_unmap : forall st m m' mo g mb S lo hi, RTWF st -> LOK bsegs mo -> GWIN st m mo g ->
  0 <= mb -> 0 < S -> mb + S <= CEIL -> CEIL <= lo ->      (* [comment removed for export] *)
  munch [(lo, hi); (mb, mb + S)] m m' ->
  GWIN st m' (mm_unmap (wz mb) (wz S) mo) g.
Proof.
  intros st m m' mo g mb S lo hi WF HO HG H1 H2 H3 H4 MU x Hw Hz Hr.
  pose proof (nowrap_of_wf _ (lok_na_ceil _ _ HO)) as Hna. pose proof (nowrap_of_ceil _ (lok_lazy_ceil _ _ HO)) as Hlz.
  assert (U1 : bv_unsigned (wz mb) = mb) by (unfold wz; apply unsigned_lit; unfold KHIGHMEM_BEG, AIMG_HI, CEIL in *; lia).
  assert (U2 : bv_unsigned (wz S) = S) by (unfold wz; apply unsigned_lit; unfold KHIGHMEM_BEG, AIMG_HI, CEIL in *; lia).
  unfold lzf in Hz. rewrite mm_unmap_lazy, mm_unmap_na, U1, U2 in Hz. rewrite !inzr_maps_subtract in Hz by (first [exact Hna| exact Hlz| lia]).
  apply andb_true_iff in Hz as [L N]. apply andb_true_iff in L as [L1 L2].
  pose proof (RTSH_below_ceil st (bv_unsigned x) WF Hr) as XC.
  assert (OUT : ~ (mb <= bv_unsigned x < mb + S)).
  { intros C. destruct (Z.leb_spec0 mb (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (mb + S)); cbn in L2; try discriminate; lia. }
  rewrite (MU x); [| cbn; lia].
  apply (HG x Hw); [| exact Hr]. unfold lzf. rewrite L1. cbn [andb].
  destruct (Z.leb_spec0 mb (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (mb + S)); try (exfalso; lia);
    cbn [andb negb] in N; rewrite ?andb_true_r in N; exact N.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma szi_wok_all : forall st W FR, RTWF st -> Forall (sz_ok st FR) W -> fresh_ok st FR -> (forall f, In f FR -> snd f <= CEIL) ->
  WOK_alloc W -> WOK_ptrarr st W -> WOK_all st W.
Proof.
  intros st W FR WF HW HFR HC WA WP.
  pose proof (szi_S1 st WF W FR HW HFR HC) as S1. pose proof (szi_S2 st WF W FR HW HFR HC) as S2.
  pose proof (szi_S3 st WF W FR HW HFR HC) as S3. pose proof (szi_S4 st WF W FR HW HFR HC) as S4.
  pose proof (szi_S5 st WF W FR HW HFR HC) as S5.
  unfold WOK_all.
  split; [eapply SZ_link; eassumption|]. split; [eapply SZ_consts; eassumption|]. split; [exact WA|].
  split; [eapply SZ_rinfo; eassumption|]. split; [eapply SZ_regions; eassumption|]. split; [eapply SZ_avail; eassumption|].
  split; [eapply SZ_cache; eassumption|]. split; [eapply SZ_thread; eassumption|].
  split; [eapply SZ_live; eassumption|]. split; [eapply SZ_quar; eassumption|]. split; [eapply SZ_batches; eassumption|].
  split; [exact WP|]. split; [eapply SZ_depot; eassumption|]. split; [eapply SZ_fs; eassumption|].
  split; [eapply SZ_ia; eassumption| eapply SZ_lowshadow; eassumption].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cj_pres_of_munch0 : forall sp0 LB LF SP W m m',
  munch W m m' ->
  (forall a, 0 <= a < 2^64 -> cj_client_addr sp0 LB LF SP a -> outside W a) ->
  cj_pres sp0 LB LF SP m m'.
Proof.
  intros sp0 LB LF SP W m m' MU HO a Ha HC.
  assert (E : m' (wa a) = m (wa a)) by (apply MU; rewrite wa_unsigned by lia; apply HO; assumption).
  split; [exact E|]. unfold wview. rewrite E. intros H. exact H.
Qed.

(* [comment removed for export] *)
Section NC.
Variable st : rtstate.
Hypothesis WF : RTWF st.

Lemma pa_vs_sec : forall h nh, In (h, nh) (st_sec st) -> st_pa st + PTRARR_RES_SIZE <= h \/ h + smapsize nh <= st_pa st.
Proof.
  intros h nh Hin. pose proof (wb_pwdj st (wf_base_ok st WF)) as PW. rewrite rt_ranges_tail in PW. cbn [app] in PW. destruct PW as [_ [F1 _]].
  rewrite Forall_forall in F1.
  specialize (F1 (h, h + smapsize nh) ltac:(apply in_or_app; right; apply in_or_app; left; apply in_map_iff; exists (h, nh); split; [reflexivity| exact Hin])).
  cbn [fst snd] in F1. lia.
Qed.

Variable SP : Z.
Hypothesis HSP : CEIL <= SP.
Lemma sechdr_not_client : forall M nM a, In (M, nM) (st_sec st) -> M <= a < M + 4096 ->
  ~ cj_client_addr (st_sp0 st) (st_lb st) (st_lf st) SP a.
Proof.
  intros M nM a HM Ha HC. pose proof (sec_entry_range st WF M nM HM) as (R1 & R2 & R3 & R4 & R5 & R6).
  pose proof (smapsize_pos nM ltac:(lia)) as [SMP _].
  unfold CEIL, KHIGHMEM_BEG, AIMG_HI in *.
  destruct HC as [H|[H|[(A & n0 & Hb & Hr)|[(F & k & Hb & Hr)|H]]]].
  - lia.
  - unfold aclient_image, AERRNO, AGERROR0, AGERROR1, ADATA_LO, AIMG_HI, ATP in H. blia.
  - assert (HB : In (A, n0) (all_blocks st)) by (unfold all_blocks; apply in_or_app; left; exact Hb).
    pose proof (block_geom st WF A n0 HB) as (_ & _ & G1 & G2 & G3 & G4 & _ & _ & _ & Gp & Gs).
    destruct (bprim n0) eqn:EP.
    + destruct (Gp eq_refl) as (_ & _ & _ & Q1 & Q2 & _).
      pose proof (wb_pwdj st (wf_base_ok st WF)) as PW. rewrite rt_ranges_tail in PW. cbn [app] in PW. destruct PW as [F0 _].
      rewrite Forall_forall in F0.
      specialize (F0 (M, M + smapsize nM) ltac:(right; apply in_or_app; right; apply in_or_app; left; apply in_map_iff; exists (M, nM); split; [reflexivity| exact HM])).
      cbn [fst snd] in F0. unfold usz in G3. lia.
    + destruct (Gs eq_refl) as (S1 & T1 & T2 & _).
      destruct (sec_disj st WF M nM (b_lo A n0) n0 HM S1) as [E|D].
      * (* [comment removed for export] *)
        unfold b_lo in E. rewrite EP in E. unfold b_map_beg, SEC_RZ, SEC_HDR in E. lia.
      * unfold usz in G3. lia.
  - pose proof (frame_range st WF F k Hb) as (Hk & X & Y & AL). pose proof (fs_range st WF) as (F1 & F2 & _).
    assert (8 <= fsz k) by (destruct Hk as [-> | ->]; [change (fsz 1) with 128| change (fsz 2) with 256]; lia).
    destruct Hr as [Hr|Hr].
    + (* [comment removed for export] *)
      pose proof (wb_pwdj st (wf_base_ok st WF)) as PW. rewrite rt_ranges_tail in PW.
      pose proof (pwdj_app_r _ _ PW) as PW2.
      pose proof (pwdj_app_disj _ _ (st_fs st, st_fs st + FS_TOTAL) (M, M + smapsize nM) PW2
                    ltac:(apply in_map_iff; exists (st_fs st, FS_TOTAL); split; [reflexivity| exact (wb_fs_loose st (wf_base_ok st WF))])
                    ltac:(apply in_or_app; left; apply in_map_iff; exists (M, nM); split; [reflexivity| exact HM])) as D.
      cbn [fst snd] in D. unfold FS_FRAMES_OFF in *. lia.
    + pose proof (rt_SH_bounds (F + fsz k) ltac:(unfold FS_FRAMES_OFF, KHIGHMEM_BEG, AIMG_HI, CEIL in *; blia)) as B. rewrite (rt_SH_aligned_add F (fsz k) AL) in B.
      pose proof (rt_SH_bounds F ltac:(unfold FS_FRAMES_OFF, KHIGHMEM_BEG, AIMG_HI, CEIL in *; blia)) as B0. blia.
  - unfold astack_shadow in H. rewrite CEIL_eq, SH_CEIL in H. change (SH (2^47)) with 0x10007fff8000 in H. blia.
Qed.
End NC.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section LDC.
  Variables (st : rtstate) (m : word -> option byte) (mb n : Z) (b : qbatch) (d : Z).
  Hypothesis HR : RTREP st m.
  Hypothesis WF : RTWF st.
  Hypothesis HP : bprim n = false.
  Hypothesis QC : st_qcur st = [(b, d)].
  Hypothesis Hd : 0 <= d < qb_count b.
  Hypothesis EL : nthz (qb_elems b) d (0,0) = (sec_user mb, n).

  Lemma ld_cells : exists j1 j2 k b1 b2 b3 j4 jg,
    rw_cells bsegs m A_SECONDARY [W8 4096; W8 (st_pa st); W8 (st_pa st); W8 PTRARR_RES_SIZE; CB 16 j1; W8 (st_nreserved st); W8 (nsec st); CB 552 j2]
    /\ 0 <= k < 2^24 /\ le4 (wz (256 * k)) = [zb 0; b1; b2; b3] /\ le4 (wz (256 * k + 1)) = [zb 1; b1; b2; b3]
    /\ rw_cells bsegs m 0xa6600 [C4 (wz (256 * k))] /\ rw_cells bsegs m 0xa6604 [CB 4 j4]
    /\ rw_cells bsegs m mb [W8 mb; W8 (smapsize n); W8 (needed n); W8 (sec_index st mb)]
    /\ rw_cells bsegs m (st_pa st + 8 * sec_index st mb) [W8 mb]
    /\ rw_cells bsegs m A_GSTATS [CB 40 jg]
    /\ vis m (SH mb) (SH mb + smapsize n / 8) /\ vis m mb (mb + smapsize n)
    /\ (sec_index st mb < nsec st - 1 ->
          rw_cells bsegs m (st_pa st + 8 * (nsec st - 1)) [W8 (fst (last (st_sec st) (0,0)))]
          /\ exists hl, rw_cells bsegs m (fst (last (st_sec st) (0,0)) + 24) [C8 hl]).
  Proof.
    pose proof (sec_obj_cells st m HR) as (j1 & j2 & j3 & SEC & MUT). rewrite A_SECONDARY_val in MUT.
    replace (680856 + 616) with 0xa6600 in MUT by reflexivity.
    destruct (mutex_cells_of m 0xa6600 j3 MUT) as (k & j4 & b1 & b2 & b3 & HK & E0 & E1 & MW & MJ). replace (0xa6600 + 4) with 0xa6604 in MJ by reflexivity.
    pose proof (idx_facts' st mb n b d WF HP QC Hd EL) as [HI HN].
    destruct (secmap_cells st m HR WF mb n (mbn_in_sec' st mb n b d WF HP QC Hd EL)) as (VM & VS & HDR).
    pose proof (ptr_cells st m HR (sec_index st mb) HI) as PIX. rewrite HN in PIX. cbn [fst] in PIX.
    pose proof (rr_alloc st m HR) as (_ & _ & [jg GST] & _).
    exists j1, j2, k, b1, b2, b3, j4, jg.
    split; [exact SEC|]. split; [exact HK|]. split; [exact E0|]. split; [exact E1|]. split; [exact MW|]. split; [exact MJ|].
    split; [exact HDR|]. split; [exact PIX|]. split; [exact GST|]. split; [exact VS|]. split; [exact VM|].
    intros LT. split.
    - pose proof (ptr_cells st m HR (nsec st - 1) ltac:(lia)) as PL. rewrite (lst_nth' st mb n b d WF HP QC Hd EL) in PL. exact PL.
    - destruct (secmap_cells st m HR WF (fst (last (st_sec st) (0,0))) (snd (last (st_sec st) (0,0)))
                 ltac:(rewrite <- surjective_pairing; exact (lst_In' st mb n b d WF HP QC Hd EL))) as (_ & _ & HL).
      exists (wz (sec_index st (fst (last (st_sec st) (0,0))))).
      exact (rw_cells_drop m _ [W8 _; W8 _; W8 _] [W8 _] HL).
  Qed.

  Lemma ld_facts :
    (* [comment removed for export] *)
    0 <= n < 2^40 /\ (AIMG_HI <= mb /\ (mb + smapsize n <= KLOWSHADOW_BEG \/ KHIGHMEM_BEG <= mb)) /\ mb + smapsize n <= CEIL /\ mb mod 4096 = 0 /\ 8192 <= smapsize n /\ smapsize n mod 4096 = 0
    /\ (AIMG_HI <= st_pa st /\ (st_pa st + PTRARR_RES_SIZE <= KLOWSHADOW_BEG \/ KHIGHMEM_BEG <= st_pa st)) /\ st_pa st + PTRARR_RES_SIZE <= CEIL /\ 8 * nsec st <= PTRARR_RES_SIZE
    /\ (st_pa st + PTRARR_RES_SIZE <= mb \/ mb + smapsize n <= st_pa st)
    /\ 0 <= st_nreserved st < 2^64 /\ 0 <= sec_index st mb < nsec st /\ nsec st <= 2^20
    /\ (st_t st + 4096 <= mb \/ mb + smapsize n <= st_t st) /\ (4096 <= st_t st /\ (st_t st + 4096 <= AIMG_LO \/ AIMG_HI <= st_t st) /\ (st_t st + 4096 <= KLOWSHADOW_BEG \/ KHIGHMEM_BEG <= st_t st)) /\ st_t st + 4096 <= CEIL
    /\ (sec_index st mb < nsec st - 1 -> let M := fst (last (st_sec st) (0,0)) in
          (AIMG_HI <= M /\ (M + 4096 <= KLOWSHADOW_BEG \/ KHIGHMEM_BEG <= M)) /\ M + 4096 <= CEIL /\ M <> mb /\ (M + 4096 <= mb \/ mb + smapsize n <= M)
          /\ (st_pa st + PTRARR_RES_SIZE <= M \/ M + 4096 <= st_pa st) /\ (st_t st + 4096 <= M \/ M + 4096 <= st_t st)).
  Proof.
    pose proof (mbn_in_sec' st mb n b d WF HP QC Hd EL) as HIN.
    pose proof (sec_entry_range st WF mb n HIN) as (R1 & R2 & R3 & R4 & R5 & R6). pose proof (smapsize_pos n ltac:(lia)) as [S1 S2].
    pose proof (pa_range st WF) as (P1 & P2 & P3 & P4 & P5). pose proof (pa_vs_sec st WF mb n HIN) as DJ.
    pose proof (idx_facts' st mb n b d WF HP QC Hd EL) as [HI _].
    pose proof (sec_vs_t st WF (mb, n) HIN) as DT. cbn [fst snd] in DT. pose proof (t_range st WF) as [T1 T2].
    pose proof (ablk_lin _ _ R1) as R1l. pose proof (ablk_disj_band _ _ R1) as R1d. pose proof (ablk_lin _ _ P1) as P1l. pose proof (ablk_disj_band _ _ P1) as P1d.
    pose proof (oclr_lin _ _ T1 ltac:(lia)) as T1l.
    unfold CEIL, PTRARR_RES_SIZE in *.
    repeat lazymatch goal with |- _ /\ _ => split | _ => idtac end; try lia.
    intros LT. pose proof (lst_In' st mb n b d WF HP QC Hd EL) as LIN.
    pose proof (dM_other st mb n b d WF HP QC Hd EL LT) as (_ & NE & DD).
    set (lst := last (st_sec st) (0,0)) in *.
    pose proof (sec_entry_range st WF (fst lst) (snd lst) ltac:(rewrite <- surjective_pairing; exact LIN)) as (L1 & L2 & L3 & L4 & L5 & L6).
    pose proof (smapsize_pos (snd lst) ltac:(lia)) as [LS1 LS2].
    pose proof (pa_vs_sec st WF (fst lst) (snd lst) ltac:(rewrite <- surjective_pairing; exact LIN)) as DJL.
    pose proof (sec_vs_t st WF lst LIN) as DTL. pose proof (ablk_lin _ _ L1) as L1l. pose proof (ablk_disj_band _ _ L1) as L1d.
    unfold CEIL, PTRARR_RES_SIZE, KHIGHMEM_BEG, AIMG_HI in *.
    cbv zeta. repeat lazymatch goal with |- _ /\ _ => split | _ => idtac end; (lia_on L1l R3 NE DD L3 L4 LS1 DJL DTL L1d).
  Qed.
End LDC.


End CeilWrap.
End RTW_sec_dealloc3.

(* [comment removed for export] *)
Module RTW_sec_dstate2P.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LMeasure OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_secz.RT_artZ OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_front OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_sec.RTW_secondary_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_secz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_sec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_spz.RTW_sec_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstate RTW_sec_dstate2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_hz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_fpU OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstateP.RT_trans OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_sec.RTW_q_needs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstateP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.ABand.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section DREPP.
  Variables (st : rtstate) (mb n : Z).
  Hypothesis WF : RTWF st.
  Hypothesis HP : bprim n = false.
  Hypothesis PEND : In (sec_user mb, n) (st_qpend st).
  Let stD := st_secderegP st mb n.
  Let idx := sec_index st mb.
  Let lst := last (st_sec st) (0,0).
  (* [comment removed for export] *)
  Definition dM : Z := if sec_index st mb <? nsec st - 1 then fst (last (st_sec st) (0,0)) else mb.
  Definition dMn : Z := if sec_index st mb <? nsec st - 1 then snd (last (st_sec st) (0,0)) else n.

  Lemma WFD : RTWF stD. Proof using WF HP PEND. exact (RTWF_dereg' st mb n WF HP PEND). Qed.

  (* [comment removed for export] *)
  Lemma sec_ne : st_sec st <> [].
  Proof using WF HP PEND. intros E. pose proof (mbn_in_sec' st mb n WF HP PEND) as H. rewrite E in H. exact H. Qed.
  Lemma lst_In' : In lst (st_sec st).
  Proof using WF HP PEND. unfold lst. apply last_In. exact sec_ne. Qed.
  Lemma lst_nth' : nthz (st_sec st) (nsec st - 1) (0,0) = lst.
  Proof using WF HP PEND.
    pose proof (idx_facts' st mb n WF HP PEND) as [HI HN]. unfold nsec, lst.
    exact (lst_nth (st_sec st) (sec_index st mb) (mb, n) (ws_nodup st (wf_sec_ok st WF)) HI HN).
  Qed.
  Lemma dM_In : In (dM, dMn) (st_sec st).
  Proof using WF HP PEND.
    unfold dM, dMn. destruct (sec_index st mb <? nsec st - 1); [| exact (mbn_in_sec' st mb n WF HP PEND)].
    rewrite <- surjective_pairing. exact lst_In'.
  Qed.
  Lemma dM_range : ablk dM (dM + smapsize dMn) /\ dM + smapsize dMn <= CEIL /\ dM mod 4096 = 0 /\ 8192 <= smapsize dMn.
  Proof using WF HP PEND.
    pose proof (sec_entry_range st WF dM dMn dM_In) as (R1 & R2 & R3 & R4 & R5 & R6).
    pose proof (smapsize_pos dMn ltac:(lia)) as [S1 _]. split; [exact R1| unfold CEIL in *; lia].
  Qed.
  Lemma mb_range : ablk mb (mb + smapsize n) /\ mb + smapsize n <= CEIL /\ mb mod 4096 = 0 /\ 8192 <= smapsize n.
  Proof using WF HP PEND.
    pose proof (sec_entry_range st WF mb n (mbn_in_sec' st mb n WF HP PEND)) as (R1 & R2 & R3 & R4 & R5 & R6).
    pose proof (smapsize_pos n ltac:(lia)) as [S1 _]. split; [exact R1| unfold CEIL in *; lia].
  Qed.
  (* [comment removed for export] *)
  Lemma dM_other : idx < nsec st - 1 -> dM = fst lst /\ fst lst <> mb /\ (fst lst + smapsize (snd lst) <= mb \/ mb + smapsize n <= fst lst).
  Proof using WF HP PEND.
    intros LT. pose proof (idx_facts' st mb n WF HP PEND) as [HI HN]. fold idx in HI, HN.
    assert (E : dM = fst lst) by (unfold dM; fold idx; destruct (Z.ltb_spec0 idx (nsec st - 1)); [reflexivity| lia]).
    split; [exact E|].
    assert (NE : fst lst <> mb).
    { intros EQ. pose proof (ws_nodup st (wf_sec_ok st WF)) as ND.
      pose proof (index_of_nthz (st_sec st) idx (0,0) ND ltac:(unfold nsec in *; lia)) as I1. rewrite HN in I1. cbn [fst] in I1.
      pose proof (index_of_nthz (st_sec st) (nsec st - 1) (0,0) ND ltac:(unfold nsec in *; lia)) as I2. rewrite lst_nth', EQ in I2. lia. }
    split; [exact NE|].
    destruct (sec_disj st WF mb n (fst lst) (snd lst) (mbn_in_sec' st mb n WF HP PEND) ltac:(rewrite <- surjective_pairing; exact lst_In')) as [H|H]; [exfalso; exact (NE H)| exact H].
  Qed.
  Lemma spend_not_mb : forall e, In e (st_spend st) -> fst e <> mb.
  Proof using WF HP PEND.
    intros e He E. destruct (ws_spend st (wf_sec_ok st WF) e He) as [HE HNB].
    assert (EE : e = (mb, n)).
    { pose proof (NoDup_map_fst_unique (st_sec st) mb (snd e) n (ws_nodup st (wf_sec_ok st WF))) as U.
      rewrite (surjective_pairing e), E. f_equal. apply U; [rewrite <- E, <- surjective_pairing; exact HE| exact (mbn_in_sec' st mb n WF HP PEND)]. }
    subst e. cbn [fst snd] in HNB. exact (HNB (A_in_blocks' st mb n WF HP PEND)).
  Qed.
  (* [comment removed for export] *)
  Lemma blockD_sec : forall A k, In (A, k) (all_blocks stD) -> bprim k = false ->
    In (b_map_beg A, k) (st_sec stD) /\ In (b_map_beg A) (map fst (st_sec stD)) /\ b_map_beg A <> mb.
  Proof using WF HP PEND.
    intros A k HB HPk.
    pose proof (wk_block stD (wf_blocks_ok stD WFD) (A, k) HB) as WB. unfold wf_block in WB. cbn [fst snd] in WB. destruct WB as (_ & _ & _ & HS).
    specialize (HS HPk). split; [exact HS|]. split; [apply in_map_iff; exists (b_map_beg A, k); split; [reflexivity| exact HS]|].
    intros E. assert (EA : A = sec_user mb) by (unfold b_map_beg, sec_user in *; lia). subst A.
    exact (A_notin_blocksD' st mb n WF HP PEND k HB).
  Qed.

  (* [comment removed for export] *)
  Lemma R_consts_dereg : forall m, R_consts st m -> R_consts stD m.   Proof using WF HP PEND. unfold stD. destruct st. intros m H. exact H. Qed.
  Lemma R_rinfo_dereg : forall m, R_rinfo st m -> R_rinfo stD m.     Proof using WF HP PEND. unfold stD. destruct st. intros m H. exact H. Qed.
  Lemma R_regions_dereg : forall m, R_regions st m -> R_regions stD m. Proof using WF HP PEND. unfold stD. destruct st. intros m H. exact H. Qed.
  Lemma R_avail_dereg : forall m, R_avail st m -> R_avail stD m.     Proof using WF HP PEND. unfold stD. destruct st. intros m H. exact H. Qed.
  Lemma R_cache_dereg : forall m, R_cache st m -> R_cache stD m.     Proof using WF HP PEND. unfold stD. destruct st. intros m H. exact H. Qed.
  Lemma R_thread_dereg : forall m, R_thread st m -> R_thread stD m.   Proof using WF HP PEND. unfold stD. destruct st. intros m H. exact H. Qed.
  Lemma R_depot_dereg : forall m, R_depot st m -> R_depot stD m.     Proof using WF HP PEND. unfold stD. destruct st. intros m H. exact H. Qed.
  Lemma R_fs_dereg : forall m, R_fs st m -> R_fs stD m.              Proof using WF HP PEND. unfold stD. destruct st. intros m H. exact H. Qed.

  Lemma R_batches_dereg : forall m, R_batches st m -> R_batches stD m. Proof using WF HP PEND. unfold stD. destruct st. intros m H. exact H. Qed.

  (* [comment removed for export] *)
  Lemma R_block_dereg : forall m md A k, In (A, k) (all_blocks stD) ->
    (bprim k = false -> b_map_beg A <> dM) -> R_block st m md A k -> R_block stD m md A k.
  Proof using WF HP PEND.
    intros m md A k HB NM (H1 & H2 & H3 & H4 & H5). split; [exact H1|]. split; [exact H2|]. split; [| split; [exact H4| exact H5]].
    intros HPk. destruct (H3 HPk) as (V1 & V2 & HC). split; [exact V1|]. split; [exact V2|].
    replace (sec_index stD (b_map_beg A)) with (sec_index st (b_map_beg A)); [exact HC|].
    destruct (blockD_sec A k HB HPk) as (_ & HIn & _).
    pose proof (dereg_index' st mb n WF HP PEND (b_map_beg A) HIn) as (E & _ & _). fold stD in E. rewrite E.
    specialize (NM HPk). unfold dM in NM.
    destruct (Z.eqb_spec (b_map_beg A) (fst (last (st_sec st) (0,0)))) as [EQ|NE]; [| reflexivity].
    destruct (sec_index st mb <? nsec st - 1); [exfalso; exact (NM EQ)| reflexivity].
  Qed.

  Lemma R_block_dereg_moved : forall mX m1 md A k, idx < nsec st - 1 ->
    munch [(fst lst + 24, fst lst + 32)] mX m1 -> wmono bsegs mX m1 ->
    In (A, k) (all_blocks stD) -> bprim k = false -> b_map_beg A = fst lst ->
    R_block st mX md A k -> rw_cells bsegs m1 (fst lst + 24) [W8 idx] -> R_block stD m1 md A k.
  Proof using WF HP PEND.
    intros until k. intros LT MU WM HB HPk EM (H1 & H2 & H3 & H4 & H5) NEW.
    pose proof (dM_other LT) as (ED & NE & _). pose proof dM_range as (D1 & D2 & D3 & D4). rewrite ED in D1, D2, D3.
    assert (EA : A = sec_user (fst lst)) by (unfold b_map_beg, sec_user in *; lia).
    pose proof (rz_size_range k) as [RZ _]. unfold KHIGHMEM_BEG, AIMG_HI, CEIL in D1, D2.
    split.
    { destruct H1 as (b1 & cid & HC & HB1). exists b1, cid. split; [| exact HB1].
      eapply rw_cells_transport; [exact HC| exact MU| exact WM| cbn; unfold b_chunk_beg, sec_user, SEC_HDR, SEC_RZ in *; lia]. }
    split.
    { intros Hrz. eapply rw_cells_transport; [exact (H2 Hrz)| exact MU| exact WM| cbn; unfold b_alloc_beg, sec_user, SEC_HDR, SEC_RZ in *; lia]. }
    split.
    { intros _. destruct (H3 HPk) as (V1 & V2 & HC). rewrite EM in *.
      pose proof (rt_SH_bounds (fst lst) ltac:(blia)) as SB.
      split; [eapply stk_wmono_noseg; [exact V1| exact WM| unfold AIMG_HI; blia]|].
      split; [eapply stk_wmono_noseg; [exact V2| exact WM| unfold AIMG_HI; lia]|].
      change [W8 (fst lst); W8 (smapsize k); W8 (needed k); W8 (sec_index stD (fst lst))]
        with ([W8 (fst lst); W8 (smapsize k); W8 (needed k)] ++ [W8 (sec_index stD (fst lst))]).
      apply rw_cells_app. split.
      - eapply rw_cells_transport; [exact (rw_cells_take mX (fst lst) [_; _; _] [_] HC)| exact MU| exact WM| cbn; lia].
      - cbn [cells_size Cells.csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. replace (sec_index stD (fst lst)) with idx; [exact NEW|].
        destruct (blockD_sec A k HB HPk) as (_ & HIn & _). rewrite EM in HIn.
        pose proof (dereg_index' st mb n WF HP PEND (fst lst) HIn) as (E & _ & _). fold stD in E. rewrite E.
        rewrite Z.eqb_refl. fold idx. destruct (Z.ltb_spec0 idx (nsec st - 1)); [reflexivity| lia]. }
    split.
    { eapply stk_wmono_noseg; [exact H4| exact WM|]. unfold b_lo. rewrite HPk, EM. unfold AIMG_HI. blia. }
    unfold R_bshadow in *. rewrite HPk in *. destruct md; [| exact I| exact I].
    destruct (blockD_sec A k HB HPk) as (HSk & _ & _). rewrite EM in HSk.
    destruct (secD_In' st mb n WF HP PEND _ HSk) as [HSk' _].
    pose proof (sec_entry_range st WF (fst lst) k HSk') as (_ & K2 & _). pose proof (sec_facts k HPk) as (_ & _ & _ & K4 & _).
    eapply rw_cells_transport; [exact H5| exact MU| exact WM|]. unfold disjoint_from. split; [| exact I].
    rewrite zcells_size. unfold zlen. rewrite rt_shadow_enc_length by (unfold usz; lia).
    (* [comment removed for export] *)
    pose proof (ablk_disj_band _ _ D1) as BD.
    unfold SH, SHADOW_OFFSET, sec_user, SEC_HDR, SEC_RZ, CEIL in *.
    destruct BD as [BD|BD]; [right|left]; Z.div_mod_to_equations; blia.
  Qed.

  (* [comment removed for export] *)
  Lemma RTREP_nsec_dereg : forall mX m1, RTREP_nsec st mX -> munch [(dM + 24, dM + 32)] mX m1 -> wmono bsegs mX m1 ->
    (idx < nsec st - 1 -> rw_cells bsegs m1 (fst lst + 24) [W8 idx]) -> RTREP_nsec stD m1.
  Proof using WF HP PEND.
    intros mX m1 HN MU WM NEW.
    pose proof (hz_xfer st WF [(dM + 24, dM + 32)] dM dMn dM_In ltac:(constructor; [cbn; lia| constructor]) mX m1 MU WM HN)
      as (X1 & X2 & X4 & X5 & X6 & X7 & X8 & X11 & X13 & X14 & X15 & X16 & XB).
    destruct HN as (_ & _ & _ & _ & _ & _ & _ & L9 & Q10 & _).
    assert (BLK : forall md A k, In (A, k) (all_blocks stD) -> R_block st mX md A k -> R_block stD m1 md A k).
    { intros md A k HB RB. pose proof (blocksD_sub' st mb n WF HP PEND _ HB) as HBo.
      destruct (bprim k) eqn:Pk.
      - apply R_block_dereg; [exact HB| intros; congruence|]. apply XB; [exact HBo| intros; congruence| exact RB].
      - destruct (Z.eq_dec (b_map_beg A) dM) as [EQ|NEQ].
        + destruct (blockD_sec A k HB Pk) as (_ & _ & NMB).
          assert (LT : idx < nsec st - 1).
          { unfold dM in EQ. fold idx in EQ. destruct (Z.ltb_spec0 idx (nsec st - 1)); [assumption| exfalso; exact (NMB EQ)]. }
          pose proof (dM_other LT) as (ED & _). rewrite ED in MU, EQ.
          eapply R_block_dereg_moved; [exact LT| exact MU| exact WM| exact HB| exact Pk| exact EQ| exact RB| exact (NEW LT)].
        + apply R_block_dereg; [exact HB| intros _; exact NEQ|]. apply XB; [exact HBo| intros _; unfold b_lo; rewrite Pk; exact NEQ| exact RB]. }
    unfold RTREP_nsec.
    split; [exact X1|]. split; [exact (R_consts_dereg m1 X2)|]. split; [exact (R_rinfo_dereg m1 X4)|]. split; [exact (R_regions_dereg m1 X5)|].
    split; [exact (R_avail_dereg m1 X6)|]. split; [exact (R_cache_dereg m1 X7)|]. split; [exact (R_thread_dereg m1 X8)|].
    split. { intros A k Hin. replace (st_lb stD) with (st_lb st) in Hin by (unfold stD; destruct st; reflexivity).
             apply BLK; [unfold all_blocks; apply in_or_app; left; replace (st_lb stD) with (st_lb st) by (unfold stD; destruct st; reflexivity); exact Hin| exact (L9 A k Hin)]. }
    split. { destruct Q10 as [QA QB]. split.
             - intros A k Hin. apply BLK; [unfold all_blocks; rewrite !in_app_iff; right; left; exact Hin|].
               exact (QA A k (qelems_stD' st mb n WF HP PEND _ Hin)).
             - intros A k Hin. apply BLK; [unfold all_blocks; rewrite !in_app_iff; right; right; exact Hin|].
               exact (QB A k (qpend_stD' st mb n WF HP PEND _ Hin)). }
    split; [exact (R_batches_dereg m1 X11)|]. split; [exact (R_depot_dereg m1 X13)|]. split; [exact (R_fs_dereg m1 X14)|].
    split; [exact X15| exact X16].
  Qed.

  (* [comment removed for export] *)
  Lemma R_alloc_dereg_intro : forall W mv m j1 j2 j3 jg, R_alloc st mv -> munch W mv m -> wmono bsegs mv m ->
    disjoint_from W A_ALLOC 64 -> disjoint_from W A_QUAR 256 -> disjoint_from W A_MAXUSERSZ 13 ->
    rw_cells bsegs m A_SECONDARY [W8 4096; W8 (st_pa st); W8 (st_pa st); W8 PTRARR_RES_SIZE; CB 16 j1; W8 (st_nreserved st); W8 (nsec st - 1); CB 552 j2; W1 0; CB 7 j3] ->
    rw_cells bsegs m A_GSTATS [CB 40 jg] ->
    R_alloc stD m.
  Proof using WF HP PEND.
    intros W mv m j1 j2 j3 jg HA MU WM D1 D2 D3 SEC GST.
    destruct HA as ((k1 & k2 & k3 & X1) & _ & _ & (l1 & l2 & l3 & l4 & X4) & X5).
    pose proof (st_secdereg_fields st mb n WF HP PEND) as (_ & _ & _ & E4 & E5 & _). fold stD in E4, E5.
    pose proof (dereg_nsec' st mb n WF HP PEND) as EN. fold stD in EN. unfold R_alloc. rewrite E4, E5, EN.
    replace (st_pbase stD) with (st_pbase st) by (unfold stD; destruct st; reflexivity).
    replace (st_spacebeg stD) with (st_spacebeg st) by (unfold stD; destruct st; reflexivity).
    replace (st_qglobal stD) with (st_qglobal st) by (unfold stD; destruct st; reflexivity).
    split; [exists k1, k2, k3; eapply rw_cells_transport; [exact X1| exact MU| exact WM| exact D1]|].
    split; [exists j1, j2, j3; exact SEC|].
    split; [exists jg; exact GST|].
    split; [exists l1, l2, l3, l4; eapply rw_cells_transport; [exact X4| exact MU| exact WM| exact D2]|].
    eapply (ro_cells_transport bsegs W mv m); [exact X5| exact MU| exact D3].
  Qed.

  Lemma R_ptrarr_dereg_intro : forall W mv m, R_ptrarr st mv -> munch W mv m -> wmono bsegs mv m ->
    (forall i, 0 <= i < nsec st - 1 -> i <> idx -> disjoint_from W (st_pa st + 8 * i) 8) ->
    (forall e, In e (st_spend st) -> fst e <> dM -> disjoint_from W (fst e) 32) ->
    (forall e, In e (st_spend st) -> disjoint_from W (fst e) 24) ->
    (idx < nsec st - 1 -> rw_cells bsegs m (st_pa st + 8 * idx) [W8 (fst lst)]) ->
    (idx < nsec st - 1 -> rw_cells bsegs m (fst lst + 24) [W8 idx]) ->
    R_ptrarr stD m.
  Proof using WF HP PEND.
    intros W mv m (V & HC & HS) MU WM K1 K2 K3 NSLOT NHDR.
    pose proof (st_secdereg_fields st mb n WF HP PEND) as (E1 & _ & E3 & E4 & E5 & _). fold stD in E1, E3, E4, E5.
    pose proof (pa_range st WF) as (P1 & P2 & P3 & P4 & P5). pose proof (idx_facts' st mb n WF HP PEND) as [HI _]. fold idx in HI.
    pose proof (dereg_nsec' st mb n WF HP PEND) as EN. fold stD in EN. unfold R_ptrarr. rewrite E4, E3, E5, EN.
    split; [eapply stk_wmono_noseg; [exact V| exact WM| unfold AIMG_HI, KHIGHMEM_BEG in *; blia]|]. split.
    - intros i Hi. pose proof (secD_nth' st mb n WF HP PEND i Hi) as NT. fold stD idx lst in NT. rewrite NT.
      destruct (Z.eqb_spec i idx) as [->|NE]; [exact (NSLOT ltac:(lia))|].
      eapply rw_cells_transport; [exact (HC i ltac:(lia))| exact MU| exact WM| exact (K1 i Hi NE)].
    - intros e He. destruct (HS e He) as (V1 & V2 & HCe).
      destruct (ws_spend st (wf_sec_ok st WF) e He) as [HE _].
      pose proof (sec_entry_range st WF (fst e) (snd e) ltac:(rewrite <- surjective_pairing; exact HE)) as (R1 & R2 & R3 & R4 & _).
      pose proof (rt_SH_bounds (fst e) ltac:(unfold KHIGHMEM_BEG, AIMG_HI, CEIL in *; blia)) as SB.
      split; [eapply stk_wmono_noseg; [exact V1| exact WM| unfold AIMG_HI, KHIGHMEM_BEG in *; blia]|].
      split; [eapply stk_wmono_noseg; [exact V2| exact WM| unfold AIMG_HI in *; lia]|].
      (* [comment removed for export] *)
      assert (HIn : In (fst e) (map fst (st_sec stD))).
      { destruct (ws_spend stD (wf_sec_ok stD WFD) e ltac:(rewrite E3; exact He)) as [HE' _]. apply in_map_iff. exists e. split; [reflexivity| exact HE']. }
      pose proof (dereg_index' st mb n WF HP PEND (fst e) HIn) as (E & _ & _). fold stD in E. rewrite E. fold idx lst.
      destruct (Z.eqb_spec (fst e) (fst lst)) as [EQ|NEQ].
      + destruct (Z.ltb_spec0 idx (nsec st - 1)) as [LT|GE].
        * (* [comment removed for export] *)
          change [W8 (fst e); W8 (smapsize (snd e)); W8 (needed (snd e)); W8 idx]
            with ([W8 (fst e); W8 (smapsize (snd e)); W8 (needed (snd e))] ++ [W8 idx]).
          apply rw_cells_app. split.
          -- eapply rw_cells_transport; [exact (rw_cells_take mv (fst e) [_; _; _] [_] HCe)| exact MU| exact WM| exact (K3 e He)].
          -- cbn [cells_size Cells.csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite EQ. exact (NHDR LT).
        * eapply rw_cells_transport; [exact HCe| exact MU| exact WM| apply (K2 e He)].
          unfold dM. fold idx. destruct (Z.ltb_spec0 idx (nsec st - 1)); [lia| exact (spend_not_mb e He)].
      + eapply rw_cells_transport; [exact HCe| exact MU| exact WM| apply (K2 e He)].
        unfold dM. fold idx lst. destruct (Z.ltb_spec0 idx (nsec st - 1)); [exact NEQ| exact (spend_not_mb e He)].
  Qed.
End DREPP.


End CeilWrap.
End RTW_sec_dstate2P.

(* [comment removed for export] *)
Module RTW_sec_dealloc3P.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LMeasure OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_secz.RT_artZ OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_front OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_sec.RTW_secondary_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_secz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_sec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_spz.RTW_sec_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_lib.RTW_sec_alloc5 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstate RTW_sec_dstate2 RTW_sec_dealloc3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstateP.RT_trans OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_sec.RTW_q_needs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstateP RTW_sec_dstate2P.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section LDCP.
  Variables (st : rtstate) (m : word -> option byte) (mb n : Z).
  Hypothesis HR : RTREP st m.
  Hypothesis WF : RTWF st.
  Hypothesis HP : bprim n = false.
  Hypothesis PEND : In (sec_user mb, n) (st_qpend st).

  Lemma ld_cells : exists j1 j2 k b1 b2 b3 j4 jg,
    rw_cells bsegs m A_SECONDARY [W8 4096; W8 (st_pa st); W8 (st_pa st); W8 PTRARR_RES_SIZE; CB 16 j1; W8 (st_nreserved st); W8 (nsec st); CB 552 j2]
    /\ 0 <= k < 2^24 /\ le4 (wz (256 * k)) = [zb 0; b1; b2; b3] /\ le4 (wz (256 * k + 1)) = [zb 1; b1; b2; b3]
    /\ rw_cells bsegs m 0xa6600 [C4 (wz (256 * k))] /\ rw_cells bsegs m 0xa6604 [CB 4 j4]
    /\ rw_cells bsegs m mb [W8 mb; W8 (smapsize n); W8 (needed n); W8 (sec_index st mb)]
    /\ rw_cells bsegs m (st_pa st + 8 * sec_index st mb) [W8 mb]
    /\ rw_cells bsegs m A_GSTATS [CB 40 jg]
    /\ vis m (SH mb) (SH mb + smapsize n / 8) /\ vis m mb (mb + smapsize n)
    /\ (sec_index st mb < nsec st - 1 ->
          rw_cells bsegs m (st_pa st + 8 * (nsec st - 1)) [W8 (fst (last (st_sec st) (0,0)))]
          /\ exists hl, rw_cells bsegs m (fst (last (st_sec st) (0,0)) + 24) [C8 hl]).
  Proof using HR WF HP PEND.
    pose proof (sec_obj_cells st m HR) as (j1 & j2 & j3 & SEC & MUT). rewrite A_SECONDARY_val in MUT.
    replace (680856 + 616) with 0xa6600 in MUT by reflexivity.
    destruct (mutex_cells_of m 0xa6600 j3 MUT) as (k & j4 & b1 & b2 & b3 & HK & E0 & E1 & MW & MJ). replace (0xa6600 + 4) with 0xa6604 in MJ by reflexivity.
    pose proof (idx_facts' st mb n WF HP PEND) as [HI HN].
    destruct (secmap_cells st m HR WF mb n (mbn_in_sec' st mb n WF HP PEND)) as (VM & VS & HDR).
    pose proof (ptr_cells st m HR (sec_index st mb) HI) as PIX. rewrite HN in PIX. cbn [fst] in PIX.
    pose proof (rr_alloc st m HR) as (_ & _ & [jg GST] & _).
    exists j1, j2, k, b1, b2, b3, j4, jg.
    split; [exact SEC|]. split; [exact HK|]. split; [exact E0|]. split; [exact E1|]. split; [exact MW|]. split; [exact MJ|].
    split; [exact HDR|]. split; [exact PIX|]. split; [exact GST|]. split; [exact VS|]. split; [exact VM|].
    intros LT. split.
    - pose proof (ptr_cells st m HR (nsec st - 1) ltac:(lia)) as PL. rewrite (lst_nth' st mb n WF HP PEND) in PL. exact PL.
    - destruct (secmap_cells st m HR WF (fst (last (st_sec st) (0,0))) (snd (last (st_sec st) (0,0)))
                 ltac:(rewrite <- surjective_pairing; exact (lst_In' st mb n WF HP PEND))) as (_ & _ & HL).
      exists (wz (sec_index st (fst (last (st_sec st) (0,0))))).
      exact (rw_cells_drop m _ [W8 _; W8 _; W8 _] [W8 _] HL).
  Qed.

  Lemma ld_facts :
    (* [comment removed for export] *)
    0 <= n < 2^40 /\ (AIMG_HI <= mb /\ (mb + smapsize n <= KLOWSHADOW_BEG \/ KHIGHMEM_BEG <= mb)) /\ mb + smapsize n <= CEIL /\ mb mod 4096 = 0 /\ 8192 <= smapsize n /\ smapsize n mod 4096 = 0
    /\ (AIMG_HI <= st_pa st /\ (st_pa st + PTRARR_RES_SIZE <= KLOWSHADOW_BEG \/ KHIGHMEM_BEG <= st_pa st)) /\ st_pa st + PTRARR_RES_SIZE <= CEIL /\ 8 * nsec st <= PTRARR_RES_SIZE
    /\ (st_pa st + PTRARR_RES_SIZE <= mb \/ mb + smapsize n <= st_pa st)
    /\ 0 <= st_nreserved st < 2^64 /\ 0 <= sec_index st mb < nsec st /\ nsec st <= 2^20
    /\ (st_t st + 4096 <= mb \/ mb + smapsize n <= st_t st) /\ (4096 <= st_t st /\ (st_t st + 4096 <= AIMG_LO \/ AIMG_HI <= st_t st) /\ (st_t st + 4096 <= KLOWSHADOW_BEG \/ KHIGHMEM_BEG <= st_t st)) /\ st_t st + 4096 <= CEIL
    /\ (sec_index st mb < nsec st - 1 -> let M := fst (last (st_sec st) (0,0)) in
          (AIMG_HI <= M /\ (M + 4096 <= KLOWSHADOW_BEG \/ KHIGHMEM_BEG <= M)) /\ M + 4096 <= CEIL /\ M <> mb /\ (M + 4096 <= mb \/ mb + smapsize n <= M)
          /\ (st_pa st + PTRARR_RES_SIZE <= M \/ M + 4096 <= st_pa st) /\ (st_t st + 4096 <= M \/ M + 4096 <= st_t st)).
  Proof using WF HP PEND.
    pose proof (mbn_in_sec' st mb n WF HP PEND) as HIN.
    pose proof (sec_entry_range st WF mb n HIN) as (R1 & R2 & R3 & R4 & R5 & R6). pose proof (smapsize_pos n ltac:(lia)) as [S1 S2].
    pose proof (pa_range st WF) as (P1 & P2 & P3 & P4 & P5). pose proof (pa_vs_sec st WF mb n HIN) as DJ.
    pose proof (idx_facts' st mb n WF HP PEND) as [HI _].
    pose proof (sec_vs_t st WF (mb, n) HIN) as DT. cbn [fst snd] in DT. pose proof (t_range st WF) as [T1 T2].
    pose proof (ablk_lin _ _ R1) as R1l. pose proof (ablk_disj_band _ _ R1) as R1d. pose proof (ablk_lin _ _ P1) as P1l. pose proof (ablk_disj_band _ _ P1) as P1d.
    pose proof (oclr_lin _ _ T1 ltac:(lia)) as T1l.
    unfold CEIL, PTRARR_RES_SIZE in *.
    repeat lazymatch goal with |- _ /\ _ => split | _ => idtac end; try lia.
    intros LT. pose proof (lst_In' st mb n WF HP PEND) as LIN.
    pose proof (dM_other st mb n WF HP PEND LT) as (_ & NE & DD).
    set (lst := last (st_sec st) (0,0)) in *.
    pose proof (sec_entry_range st WF (fst lst) (snd lst) ltac:(rewrite <- surjective_pairing; exact LIN)) as (L1 & L2 & L3 & L4 & L5 & L6).
    pose proof (smapsize_pos (snd lst) ltac:(lia)) as [LS1 LS2].
    pose proof (pa_vs_sec st WF (fst lst) (snd lst) ltac:(rewrite <- surjective_pairing; exact LIN)) as DJL.
    pose proof (sec_vs_t st WF lst LIN) as DTL. pose proof (ablk_lin _ _ L1) as L1l. pose proof (ablk_disj_band _ _ L1) as L1d.
    unfold CEIL, PTRARR_RES_SIZE, KHIGHMEM_BEG, AIMG_HI in *.
    cbv zeta. repeat lazymatch goal with |- _ /\ _ => split | _ => idtac end; (lia_on L1l R3 NE DD L3 L4 LS1 DJL DTL L1d).
  Qed.
End LDCP.


End CeilWrap.
End RTW_sec_dealloc3P.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_cd_stmt.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_m_specs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_quarantine_iface2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_q_lock.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_q_ms.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_q_rec2.
Module RTW_q_put.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Exec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_sec.RTW_secondary_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_quarantine_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_poison8.RT_poison_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_cd_stmt OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstateP.RT_trans.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_specs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drainw.RTW_m_a1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_abs.RTW_m_lib3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_tpz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_apz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_pop OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_wf2.RTW_m_c1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstateP.RTW_m_live OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_abs.RTW_m_at1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drainw.RTW_m_leaves2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_lib4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_depot_lock OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstateP.RTW_q_trans OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_wf2.RTW_q_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_zone OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_wf3.RTW_q_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_wf3.RTW_q_enq2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_wf2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_sec.RTW_q_needs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drain.RTW_q_stmts OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drain.RTW_q_stmts2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drain.RTW_q_qcr1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drain.RTW_q_qcr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drain.RTW_q_dor1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drain.RTW_q_rep3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drain.RTW_q_dorec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstate OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drain RTW_q_psz RTW_q_rep2 RTW_q_put1 RTW_q_enq OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_quarantine_iface2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_lock OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_wf3.RTW_q_car OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_wf3.RTW_q_zone2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_ms OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drainw OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_wf3.RTW_q_drain2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_wf3.RTW_q_bz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_rec2.RTW_q_recw OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_rec2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drain.RTW_q_rec3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_wf3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_bandtac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_bandtac2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_bandtac4.
Import ListNotations.
Open Scope Z_scope.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rtrep_freefill : forall st m, RTREP st m -> freefill_cells m.
Proof.
  intros st m HR. pose proof (rtrep_artcells st m HR) as HA. pose proof (rtrep_memtoshadow_cells st m HR HA) as (M1 & _).
  pose proof (rr_consts st m HR) as HC. (nelim HC 4%nat; intros _ _ HAF _).
  split; [exact M1|]. unfold ro_cells.
  change 0xa71e8 with (A_AFLAGS + Z.of_nat 48). change (Z_to_bv 64 0) with (wz 0). apply (aflags_word m 48 0 HAF); [lia| lia|].
  intros i Hi. do 4 (destruct i as [|i]; [vm_compute; reflexivity|]). lia.
Qed.

Lemma prim_small : forall n, bprim n = true -> usz n <= 65536.
Proof.
  intros n HP. (nelim (prim_facts n HP) 3%nat; intros Hc F2 _). pose proof (csize_max' (pclass n) Hc) as CM.
  pose proof (rz_size_range n) as (RZ & _). unfold pslot in F2. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section QPUT.
Hypothesis PS : poison_shadow_spec.
Hypothesis ENQ : enqueue_spec.
Hypothesis DRAIN : drain_spec.
Hypothesis QCRPEND : qcr_pend_spec.

Theorem quarantine_put_core : quarantine_put_spec2.
Proof.
  unfold quarantine_put_spec2. intros until lo.
  intros HRTS HIN HQT HQC HAP SHL -> -> -> HA3 -> -> TP SPB HRES ST HCL LO MI.
  set (Sx := bv_unsigned a3).
  assert (HSX : 0 <= Sx < 2^64) by (subst Sx; pose proof (bv_unsigned_in_range 64 a3) as R; unfold bv_modulus in R; cbn in R; lia).
  assert (EA3 : a3 = wz Sx) by (subst Sx; unfold wz; rewrite Z_to_bv_bv_unsigned; reflexivity).
  clearbody Sx. clear HA3. subst a3.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. idtac. unfold AQPUT_STACK in LO.
  apply lscps_assume. intros NWX HO HB0.
  (nelimp HRTS 6%nat; intros HR WF HM HG HFR HSW).
  assert (HB : In (A, n) (all_blocks st)) by (unfold all_blocks; rewrite !in_app_iff; right; right; exact HIN).
  (nelimp (block_geom st WF A n HB) 11%nat; intros Gn GA K X Y CE L16 H16 EA Gp Gs).
  (nelimp (ablk_lin _ _ K) 4%nat; intros KI K0 KT _).
  pose proof (t_range st WF) as [TR TC]. (nelimp (oclr_lin _ _ TR ltac:(lia)) 3%nat; intros TR1 TR2 TR3).
  (nelimp (wb_sp0 st (wf_base_ok st WF)) 3%nat; intros _ SP047 _).
  assert (ACR : 0 <= acache st < 2^64) by (unfold acache, T_ACACHE, CEIL in *; lia).
  assert (USR : 0 <= usz n < 2^64) by (unfold usz; lia).
  assert (HSPC : CEIL <= bv_unsigned sp) by (unfold CEIL; lia).
  destruct (rr_alloc st m HR) as (_ & _ & _ & (q1 & q2 & q3 & q4 & AQ) & _).
  apply (proj1 (rw_cells_app m A_QUAR [_; _; _; _; _] (_ :: _))) in AQ as [AQ _].
  (* [comment removed for export] *)
  eapply lscps_step_evt.
  eapply evt_cut.
  { eapply (put_pro_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m (acache st) Sx (usz n) lo q1 q2);
      [exact MI| reflexivity| reflexivity| reflexivity| reflexivity| exact ACR| exact HSX| exact USR| exact ST| exact HCL| lia| exact AQ]. }
  cbv beta. intros ms1 nelH_; (nelim nelH_ 8%nat; intros m1 -> MU1 WM1 MI1 ST1 FR1 QC1).
  assert (SPV : bv_unsigned (wz (bv_unsigned sp - 80) : word) = bv_unsigned sp - 80) by (apply bvu_wz; lia).
  assert (HR1 : RTREP st m1).
  { eapply (RTREP_high st [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 WF); [| exact MU1| exact WM1| exact HR]. constructor; [cbn [fst]; lia| constructor]. }
  assert (RTS1 : RTS st m1 mo g).
  { apply RTS_intro; [exact HR1| exact WF| exact HM| eapply GWIN_mem; [exact HG| exact HO| exact WM1]| exact HFR| exact HSW]. }
  assert (CP1 : cli_pres st (bv_unsigned sp) m m1).
  { eapply (cli_pres_secw st WF (bv_unsigned sp) HSPC [(bv_unsigned sp - 80, bv_unsigned sp)]); [exact MU1| exact WM1| |].
    - constructor; [left; cbn [fst]; unfold CEIL; lia| constructor].
    - intros iv [<-|[]] _. cbn [snd]. lia. }
  assert (ES1 : errno_same m m1) by (eapply errno_same_munch; [exact MU1|]; constructor; [cbn [fst snd]; left; unfold AERRNO, ATP; lia| constructor]).
  (* [comment removed for export] *)
  assert (FIN : forall (ra' t0' t1' t2' s0' s1' b0 b1 b2 b3 b4 b5 b6 b7 s2' s3' s4' s5' s6' t3' t4' t5' t6' : word)
                       (m' : word -> option byte) (mo' : Model) (g' : lghost) (st' : rtstate),
            mem_inv bsegs m' -> qput_rel st st' A n -> RTS st' m' mo' g' -> stk bsegs m' lo (bv_unsigned sp - 80) ->
            rw_cells bsegs m' (bv_unsigned sp - 80) (put_frame (acache st) Sx s6 s5 s4 s3 s2 s1 s0 ra) ->
            cli_pres st (bv_unsigned sp) m m' -> errno_same m m' -> gmono g g' -> budget_ok st g st' g' (fp n + cost_free) ->
            LSCPS bsegs (qput_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st A n lo m g)
              (MS (mkR ra' (wz (bv_unsigned sp - 80)) gp tp t0' t1' t2' s0' s1' b0 b1 b2 b3 b4 b5 b6 b7
                       s2' s3' s4' s5' s6' s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (wz 0x36308) fc None m' (seg_rom bsegs)) mo' g').
  { intros until st'. intros MI' REL' RTS' ST' FR' CP' ES' GM' BO'.
    eapply lscps_step_evt.
    eapply evt_cut.
    { eapply (put_epi_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m' (acache st) Sx lo s6 s5 s4 s3 s2 s1 s0 ra);
        [exact MI'| rewrite SPV; exact ST'| exact HCL| rewrite SPV; lia| rewrite SPV; lia| rewrite SPV; exact FR']. }
    cbv beta. intros ms9 (-> & ST9). rewrite SPV in *. replace (bv_unsigned sp - 80 + 80) with (bv_unsigned sp) in * by lia.
    apply evt_done. apply lscps_done.
    unfold qput_post, rt_post_std. cbv beta delta [wz]. rewrite Z_to_bv_bv_unsigned. nexists 15%nat. exists m', st'.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact REL'|]. split; [exact RTS'|]. split; [exact ST9|].
    split; [exact CP'|]. split; [exact ES'|]. split; [exact GM'| exact BO']. }
  destruct (usz n <=? QUAR_MAX_SIZE) eqn:ESZ.
  - apply Z.leb_le in ESZ.
    (* [comment removed for export] *)
    set (ru := (usz n + 7) / 8 * 8).
    assert (RUB : ru mod 8 = 0 /\ usz n <= ru < usz n + 8) by (subst ru; clear; Z.div_mod_to_equations; lia).
    assert (L8 : b_lo A n mod 8 = 0) by (clear - L16; Z.div_mod_to_equations; lia).
    assert (A8 : A mod 8 = 0) by (clear - GA; Z.div_mod_to_equations; lia).
    assert (Z2 : 0 <= ru / 8) by (clear - RUB; unfold usz in RUB; Z.div_mod_to_equations; lia).
    assert (RU8 : 8 <= ru) by (clear - RUB; unfold usz in RUB; Z.div_mod_to_equations; lia).
    assert (ARU : A + ru <= b_hi A n) by (clear - Y RUB GA H16; Z.div_mod_to_equations; lia).
    assert (ESH : SH (b_hi A n) = SH (b_lo A n) + asz n / 8) by (unfold b_hi; apply rt_SH_aligned_add; exact L8).
    assert (SHIN : SH (b_lo A n) <= SH A /\ SH A + ru / 8 <= SH (b_hi A n)).
    { split; [apply rt_SH_mono; lia|]. rewrite <- (rt_SH_aligned_add A ru A8). apply rt_SH_mono. exact ARU. }
    pose proof (ablk_shad_lin _ _ K ltac:(unfold usz in *; lia)) as (KS1 & KS2).
    pose proof (ablk_shad_disj _ _ K ltac:(unfold usz in *; lia)) as KSD.
    pose proof (rt_SH_mono (b_hi A n) (b_hi A n + 7) ltac:(lia)) as KSM.
    assert (APR : app_range A ru).
    { pose proof (ablk_disj_band _ _ K) as [KB|KB]; [left| right]; unfold lowmem_range, highmem_range.
      - unfold AIMG_HI in KI. clear - KB KI X ARU RUB. unfold usz in *. lia.
      - clear - KB X ARU RUB CE. unfold KHIGHMEM_END, usz in *. lia. }
    (* [comment removed for export] *)
    pose proof (rtrep_freefill st m1 HR1) as FF1.
    destruct (proj2 (rr_quar st m1 HR1) A n HIN) as ((b1 & cid & HDR1 & HB1) & _ & SC1 & _ & SHD1).
    assert (VSH : stk bsegs m1 (SH (b_lo A n)) (SH (b_hi A n))).
    { rewrite ESH. unfold R_bshadow in SHD1. destruct (bprim n) eqn:EP; [exact SHD1|].
      (nelim (SC1 EP) 3%nat; intros _ V2 _). (nelim (Gs eq_refl) 3%nat; intros _ EH _).
      assert (ELO : b_lo A n = b_map_beg A) by (unfold b_lo; rewrite EP; reflexivity).
      assert (EAS : asz n = smapsize n) by (unfold b_hi in EH; lia). rewrite ELO, EAS. exact V2. }
    destruct (vis_carve m1 _ _ (SH A) (Z.to_nat (ru / 8)) VSH ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (junk & JK1).
    eapply evt_cut.
    { eapply (put_poison_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (acache st) Sx (b_chunk_beg A) (usz n) n b1 cid);
        [exact MI1| exact FF1| reflexivity| reflexivity| reflexivity| reflexivity| exact ACR| exact HSX| exact USR| exact Gn
        | unfold b_chunk_beg; lia| unfold b_chunk_beg, usz in *; lia| exact HDR1]. }
    cbv beta. intros ms2 (a3' & ->).
    replace (b_chunk_beg A + 16) with A by (unfold b_chunk_beg; lia). fold ru.
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply (PS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 A ru 253 lo junk);
        [ exact (artcells_icpt m1 (rtrep_artcells st m1 HR1)) | exact (artcells_poison m1 (rtrep_artcells st m1 HR1)) | exact MI1
        | rewrite SPV; exact ST1| exact HCL| rewrite SPV; unfold APOISON_STACK; lia
        | reflexivity| reflexivity| reflexivity| exact A8| tauto| exact RU8| exact APR| lia| intros; lia| exact JK1 ]. }
    cbv beta. intros ms3 nelH_; (nelim nelH_ 22%nat; intros v0 v1 v2 x0 x1 x2 x3 x4 x5 x6 x7 v3 v4 v5 v6 m2 -> MU2 WM2 MI2 SHF ST2).
    rewrite SPV in *.
    set (W12 := [(bv_unsigned sp - 80, bv_unsigned sp)] ++ [(SH A, SH A + ru / 8); (bv_unsigned sp - 80 - APOISON_STACK, bv_unsigned sp - 80)]).
    assert (MU12 : munch W12 m m2) by (eapply munch_cat; [exact MU1| exact MU2]).
    assert (WM12 : wmono bsegs m m2) by (eapply wmono_trans; [exact WM1| exact WM2]).
    assert (HW12 : Forall (psz_ok A n) W12).
    { subst W12. repeat apply Forall_cons; try apply Forall_nil; unfold psz_ok; cbn [fst snd]; fold ru; unfold APOISON_STACK, CEIL; [right; lia| left; lia| right; lia]. }
    assert (HR2 : RTREP st m2) by (eapply (RTREP_pshadow st m m2 W12 A n); eassumption).
    assert (RTS2 : RTS st m2 mo g).
    { apply RTS_intro; [exact HR2| exact WF| exact HM| eapply GWIN_mem; [exact HG| exact HO| exact WM12]| exact HFR| exact HSW]. }
    (* [comment removed for export] *)
    assert (SHQ2 : bprim n = true -> rw_cells bsegs m2 (SH (b_lo A n)) (zcells (sh_quar n))).
    { intros EP. pose proof (SHL EP) as SL0. pose proof (sh_fits n ltac:(lia)) as [SF1 SF2].
      assert (EE : zlen (shadow_enc (usz n)) = ru / 8).
      { subst ru. unfold zlen. rewrite rt_shadow_enc_length by (unfold usz; lia). clear. Z.div_mod_to_equations. lia. }
      assert (ESA : SH A = SH (b_lo A n) + sh_left n).
      { rewrite EA at 1. rewrite (rt_SH_aligned_add (b_lo A n) (8 * sh_left n) L8). f_equal. clear. Z.div_mod_to_equations. lia. }
      assert (EST : sh_tot n = asz n / 8) by reflexivity.
      rewrite EE in SF2.
      assert (Z1 : 0 <= sh_left n) by exact SF1.
      assert (Z3 : 0 <= sh_tot n - sh_left n - ru / 8) by (clear - SF2; lia).
      assert (DW : forall a sz, (a + sz <= SH A \/ SH A + ru / 8 <= a) -> a + sz <= CEIL -> disjoint_from W12 a sz).
      { intros a sz H1 H2. subst W12. cbn. unfold APOISON_STACK, CEIL in *. clear - H1 H2 LO HCL. set (r8 := ru / 8) in *. clearbody r8. lia. }
      rewrite sh_live_split in SL0. rewrite EE in SL0. rewrite !zcells_app' in SL0.
      apply (proj1 (rw_cells_app m _ _ _)) in SL0 as [SLl SLr]. apply (proj1 (rw_cells_app m _ _ _)) in SLr as [_ SLr].
      rewrite (zcells_zrep_size _ _ Z1) in SLr. rewrite zcells_size, EE in SLr.
      unfold sh_quar, sh_chunk. rewrite EE.
      replace (zlen (zrep SV_HEAP_FREED (ru / 8))) with (ru / 8) by (unfold zlen; rewrite zrep_length by exact Z2; reflexivity).
      rewrite !zcells_app'.
      apply (proj2 (rw_cells_app m2 _ _ _)). split.
      { eapply rw_cells_transport; [exact SLl| exact MU12| exact WM12|]. rewrite (zcells_zrep_size _ _ Z1). apply DW.
        - left. clear - ESA. lia.
        - clear - KS2 SHIN ESA Z2. unfold CEIL, KHIGHMEM_BEG in *. lia. }
      rewrite (zcells_zrep_size _ _ Z1).
      apply (proj2 (rw_cells_app m2 _ _ _)). split.
      { apply CB_to_zcells_zrep; [exact Z2|]. rewrite <- ESA. exact SHF. }
      rewrite (zcells_zrep_size _ _ Z2).
      eapply rw_cells_transport; [exact SLr| exact MU12| exact WM12|]. rewrite (zcells_zrep_size _ _ Z3). apply DW.
      - right. clear - ESA. lia.
      - clear - KS2 ESA ESH EST Z1 Z2 Z3. unfold CEIL, KHIGHMEM_BEG in *. lia. }
    assert (FR2 : rw_cells bsegs m2 (bv_unsigned sp - 80) (put_frame (acache st) Sx s6 s5 s4 s3 s2 s1 s0 ra)).
    { eapply rw_cells_transport; [exact FR1| exact MU2| exact WM2|]. unfold put_frame. cbn -[Z.add Z.sub Z.mul Z.div Z.le Z.lt SH].
      clear - KS2 SHIN LO HCL Z2. unfold APOISON_STACK, KHIGHMEM_BEG in *. repeat split; lia. }
    assert (CP12 : cli_pres st (bv_unsigned sp) m m2).
    { eapply (cli_pres_qcz st WF (bv_unsigned sp) HSPC A n W12 m m2 (or_intror HIN) MU12 WM12).
      - eapply Forall_impl; [| exact HW12]. intros [l h] Z. unfold psz_ok in Z. unfold qcz_ok. cbn [fst snd] in *. (cut_on [HSX RSP Gn TR2 TR3 ACR USR RUB SHIN KSD Z] tauto).
      - intros iv Hin HCE. subst W12. cbn [app] in Hin. destruct Hin as [<-|[<-|[<-|[]]]]; cbn [fst snd] in *; [lia| | unfold APOISON_STACK; lia].
        exfalso. clear - HCE KS2 SHIN Z2. unfold CEIL, KHIGHMEM_BEG in *. lia. }
    assert (ES12 : errno_same m m2).
    { eapply errno_same_munch; [exact MU12|]. subst W12. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold AERRNO, ATP, APOISON_STACK;
        [left; lia| left; clear - KS1 SHIN; unfold KLOWSHADOW_BEG in *; lia| left; lia]. }
    (* [comment removed for export] *)
    cbv beta delta [wz].
    replace (ret_pc (Z_to_bv 64 222136)) with (Z_to_bv 64 222136) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    eapply evt_cut; [eapply put_enq_proof|].
    cbv beta. intros ms4 ->. apply evt_done.
    eapply lscps_bind.
    { eapply (ENQ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 mo g st A n Sx lo);
        [exact RTS2| exact HIN| exact HAP| exact SHQ2| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| exact TP
        | unfold cost_free in HRES; lia| fold (wz (bv_unsigned sp - 80)); rewrite SPV; lia| fold (wz (bv_unsigned sp - 80)); rewrite SPV; exact ST2| exact HCL
        | fold (wz (bv_unsigned sp - 80)); rewrite SPV; unfold AENQ_STACK, AREFILL_STACK; lia| exact MI2]. }
    cbv beta. intros ms5 mo3 g3 PO.
    (nelim PO 31%nat; intros e0 e1 e2 r0 r1 r2 r3 r4 r5 r6 r7 e3 e4 e5 e6 m3 st3 -> MI3 REL3 HR3 WQ3 HM3 HG3 HFR3 HSW3 ST3 CP3 ES3 GM3 BO3).
    fold (wz (bv_unsigned sp - 80)) in *. rewrite SPV in ST3, CP3.
    (nelim REL3 8%nat; intros SBQ3 QP3 QG3 QTM3 QC3 QTNE3 QTB3 FRC3).
    (nelimp SBQ3 18%nat; intros E1 _ _ _ _ _ _ _ _ E10 E11 _ _ _ _ E16 E17 _).
    assert (FR3 : rw_cells bsegs m3 (bv_unsigned sp - 80) (put_frame (acache st) Sx s6 s5 s4 s3 s2 s1 s0 ra)).
    { unfold cli_pres in CP3. eapply (cj_pres_rw_cells _ _ _ _ _ _ _ _ CP3); [exact FR2|]. left. unfold put_frame. cbn [cells_size Cells.csize Nat.add]. lia. }
    assert (CP13 : cli_pres st (bv_unsigned sp) m m3).
    { unfold cli_pres in *. eapply cj_pres_trans; [exact CP12|]. eapply cj_pres_weaken; [exact CP3| lia| auto| auto]. }
    assert (ES13 : errno_same m m3) by (eapply errno_same_trans; [exact ES12| exact ES3]).
    (* [comment removed for export] *)
    pose proof (proj1 (proj2 (proj2 (rr_thread st3 m3 HR3)))) as QC3c.
    apply (proj1 (rw_cells_app m3 (qcache_t st3) [_; _; _] [_])) in QC3c as [_ QC3c].
    cbn [cells_size Cells.csize Nat.add] in QC3c. change (Z.of_nat 24) with 24 in QC3c.
    assert (QCT3 : qcache_t st3 = qcache_t st) by (unfold qcache_t; rewrite E11; reflexivity).
    assert (ACT3 : acache st3 = acache st) by (unfold acache; rewrite E11; reflexivity).
    rewrite QCT3 in QC3c.
    pose proof (wq_thread_max st (wf_quar_ok st WF)) as TMX. pose proof (wq_global_max st (wf_quar_ok st WF)) as GMX.
    pose proof (qc_bytes_nonneg (st_qthread st3)) as TB3. pose proof (qc_bytes_nonneg (st_qglobal st)) as GB0.
    cbv beta delta [wz].
    replace (ret_pc (Z_to_bv 64 222160)) with (Z_to_bv 64 222160) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    eapply lscps_step_evt.
    eapply evt_cut.
    { eapply (put_test1_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 (qcache_t st) (qc_bytes (st_qthread st3)) QUAR_MAX_CACHE);
        [exact MI3| reflexivity| reflexivity| unfold QUAR_MAX_CACHE, QUAR_MAX_SIZE, QBATCH_SIZE in *; lia| unfold QUAR_MAX_CACHE; lia
        | unfold qcache_t, T_QCACHE; lia| unfold qcache_t, T_QCACHE, CEIL in *; lia| exact QC3c]. }
    cbv beta. unfold put_test_post. intros ms6 ->.
    assert (REL03 : forall st', same_but_quarantine st3 st' -> st_qpend st' = st_qpend st3 ->
                       (forall c, 0 <= c < KNUMCLASSES -> c <> 24 -> fresh_cls st3 c -> fresh_cls st' c) ->
                       st_qtmp st' = [] -> st_qcur st' = [] -> qput_rel st st' A n).
    { intros st' SB' QP' FR' QT' QC'. split; [eapply sbq_trans; eassumption|]. split; [rewrite QP'; exact QP3|]. split; [exact QT'|]. split; [exact QC'|].
      intros c Hc NE FRc. apply (FR' c Hc NE). apply (FRC3 c Hc NE). exact FRc. }
    destruct (QUAR_MAX_CACHE <? qc_bytes (st_qthread st3)) eqn:EB.
    + (* [comment removed for export] *)
      apply Z.ltb_lt in EB.
      eapply evt_cut.
      { eapply (put_drain_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 (acache st) Sx s6 s5 s4 s3 s2 s1 s0 ra);
          [exact MI3| exact ACR| exact HSX| fold (wz (bv_unsigned sp - 80)); rewrite SPV; lia| fold (wz (bv_unsigned sp - 80)); rewrite SPV; lia
          | fold (wz (bv_unsigned sp - 80)); rewrite SPV; exact FR3]. }
      cbv beta. intros ms7 ->. apply evt_done.
      eapply lscps_bind.
      { eapply (DRAIN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 mo3 g3 st3 Sx lo);
          [exact HR3| exact WQ3| exact HM3| exact HG3| exact HFR3| exact HSW3| exact QTNE3| rewrite QTM3; exact HQT| rewrite QC3; exact HQC| rewrite E17; exact HAP
          | exact EB| rewrite QG3; unfold QREC_MAX, QUAR_MAX_CACHE, QUAR_MAX_SIZE, QBATCH_SIZE in *; lia
          | reflexivity| rewrite QCT3; reflexivity| rewrite ACT3; reflexivity| reflexivity| exact TP| exact HSX
          | fold (wz (bv_unsigned sp - 80)); rewrite SPV, E1; lia| unfold budget_ok, cost_free in *; lia
          | fold (wz (bv_unsigned sp - 80)); rewrite SPV; exact ST3| exact HCL
          | fold (wz (bv_unsigned sp - 80)); rewrite SPV; unfold ADRAIN_STACK, ADOREC_STACK; lia| exact MI3]. }
      cbv beta. intros ms8 mo4 g4 PO.
      (nelim PO 26%nat; intros f0 f1 f2 k0 k1 k2 k3 k4 k5 k6 k7 f3 f4 f5 f6 m4 st4 -> MI4 REL4 RTS4 ST4 CP4 ES4 GM4 BO4).
      fold (wz (bv_unsigned sp - 80)) in *. rewrite SPV in ST4, CP4.
      (nelim REL4 6%nat; intros SBQ4 QP4 QT4 QTM4 QC4 FRC4).
      assert (FR4 : rw_cells bsegs m4 (bv_unsigned sp - 80) (put_frame (acache st) Sx s6 s5 s4 s3 s2 s1 s0 ra)).
      { unfold cli_pres in CP4. eapply (cj_pres_rw_cells _ _ _ _ _ _ _ _ CP4); [exact FR3|]. left. unfold put_frame. cbn [cells_size Cells.csize Nat.add]. rewrite E1. lia. }
      cbv beta delta [wz].
      replace (ret_pc (Z_to_bv 64 221960)) with (Z_to_bv 64 221960) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      eapply FIN; [exact MI4| exact (REL03 st4 SBQ4 QP4 FRC4 QTM4 QC4)| exact RTS4| exact ST4| exact FR4| | | | ].
      * unfold cli_pres in *. rewrite E1, E10, E16 in CP4. eapply cj_pres_trans; [exact CP13|]. eapply cj_pres_weaken; [exact CP4| lia| auto| auto].
      * eapply errno_same_trans; [exact ES13| exact ES4].
      * eapply gmono_trans'; eassumption.
      * unfold budget_ok, cost_free in *. lia.
    + (* [comment removed for export] *)
      apply Z.ltb_ge in EB. apply evt_done.
      assert (WF3 : RTWF st3) by (apply RTWF_ofq; [exact WQ3| exact EB| rewrite QG3; exact GMX]).
      eapply FIN; [exact MI3| | apply RTS_intro; [exact HR3| exact WF3| exact HM3| exact HG3| exact HFR3| exact HSW3]| exact ST3| exact FR3| exact CP13| exact ES13| exact GM3| ].
      * apply REL03; [apply sbq_refl| reflexivity| intros; assumption| rewrite QTM3; exact HQT| rewrite QC3; exact HQC].
      * unfold budget_ok, cost_free in *. lia.
  - (* [comment removed for export] *)
    apply Z.leb_gt in ESZ.
    assert (HP : bprim n = false).
    { destruct (bprim n) eqn:EP; [| reflexivity]. pose proof (prim_small n EP). unfold QUAR_MAX_SIZE in ESZ. lia. }
    pose proof (rtrep_freefill st m1 HR1) as FF1.
    destruct (rr_alloc st m1 HR1) as ((j1 & j2 & j3 & AL1) & _).
    (nelimp (S_range st WF) 3%nat; intros S1 S2 S3). (nelimp (P_range st WF) 3%nat; intros P1 P2 P3).
    eapply evt_cut.
    { eapply (put_big_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (st_pbase st) (st_spacebeg st) (b_chunk_beg A) j1 j2 j3);
        [exact MI1| exact FF1| reflexivity| unfold b_chunk_beg, AIMG_HI, usz in *; lia| unfold PRIM_RES_SIZE, KSPACESIZE in *; lia
        | unfold PRIM_RES_SIZE, KSPACESIZE in *; lia| rewrite SPV; lia| exact AL1]. }
    cbv beta. intros ms2 (a3' & ->). apply evt_done.
    assert (CBC : rw_cells bsegs m1 (bv_unsigned sp - 80) [W8 (acache st); W8 Sx]).
    { unfold put_frame in FR1. apply (proj1 (rw_cells_app m1 (bv_unsigned sp - 80) [_; _] (_ :: _))) in FR1 as [FR1 _]. exact FR1. }
    eapply lscps_bind.
    { eapply (QCRPEND _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 mo g st A n (bv_unsigned sp - 80) Sx lo);
        [exact RTS1| exact HIN| exact HP| reflexivity| reflexivity| exact TP| rewrite SPV; lia| lia| exact CBC
        | unfold cost_free in HRES; pose proof (fp_nonneg n); (lia_on HRES Gn H)| rewrite SPV; exact ST1| exact HCL| rewrite SPV; unfold AQCR_STACK; lia| exact MI1]. }
    cbv beta. intros ms3 mo3 g3 PO.
    (nelim PO 26%nat; intros e0 e1 e2 r0 r1 r2 r3 r4 r5 r6 r7 e3 e4 e5 e6 m3 st3 -> MI3 REL3 RTS3 ST3 CP3 ES3 GM3 BO3).
    rewrite SPV in ST3, CP3.
    (nelim REL3 7%nat; intros SBQ3 QT3 QG3 QTM3 QC3 QP3 FRC3).
    (nelimp SBQ3 12%nat; intros E1 _ _ _ _ _ _ _ _ _ E11 _).
    (nelimp RTS3 3%nat; intros HR3 WF3 _).
    assert (FR3 : rw_cells bsegs m3 (bv_unsigned sp - 80) (put_frame (acache st) Sx s6 s5 s4 s3 s2 s1 s0 ra)).
    { unfold cli_pres in CP3. eapply (cj_pres_rw_cells _ _ _ _ _ _ _ _ CP3); [exact FR1|]. left. unfold put_frame. cbn [cells_size Cells.csize Nat.add]. lia. }
    (* [comment removed for export] *)
    pose proof (proj1 (proj2 (proj2 (rr_thread st3 m3 HR3)))) as QC3c.
    apply (proj1 (rw_cells_app m3 (qcache_t st3) [_; _; _] [_])) in QC3c as [_ QC3c].
    cbn [cells_size Cells.csize Nat.add] in QC3c. change (Z.of_nat 24) with 24 in QC3c.
    assert (QCT3 : qcache_t st3 = qcache_t st) by (unfold qcache_t; rewrite E11; reflexivity).
    rewrite QCT3, QT3 in QC3c.
    pose proof (wq_thread_max st (wf_quar_ok st WF)) as TMX. pose proof (qc_bytes_nonneg (st_qthread st)) as TB0.
    cbv beta delta [wz].
    replace (ret_pc (Z_to_bv 64 221932)) with (Z_to_bv 64 221932) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    eapply lscps_step_evt.
    eapply evt_cut.
    { eapply (put_test2_proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 (qcache_t st) (qc_bytes (st_qthread st)) QUAR_MAX_CACHE);
        [exact MI3| reflexivity| reflexivity| unfold QUAR_MAX_CACHE in *; lia| unfold QUAR_MAX_CACHE; lia
        | unfold qcache_t, T_QCACHE; lia| unfold qcache_t, T_QCACHE, CEIL in *; lia| exact QC3c]. }
    cbv beta. unfold put_test_post. intros ms4 ->.
    replace (QUAR_MAX_CACHE <? qc_bytes (st_qthread st)) with false by (symmetry; apply Z.ltb_ge; exact TMX).
    apply evt_done.
    eapply FIN; [exact MI3| | exact RTS3| exact ST3| exact FR3| | | exact GM3| ].
    + split; [exact SBQ3|]. split; [exact QP3|]. split; [rewrite QTM3; exact HQT|]. split; [rewrite QC3; exact HQC|].
      intros c Hc _ FRc. exact (FRC3 c Hc FRc).
    + unfold cli_pres in *. eapply cj_pres_trans; [exact CP1|]. eapply cj_pres_weaken; [exact CP3| lia| auto| auto].
    + eapply errno_same_trans; [exact ES1| exact ES3].
    + unfold budget_ok, cost_free in *. pose proof (fp_nonneg n). lia.
Qed.
End QPUT.


(* [comment removed for export] *)
(* [comment removed for export] *)
Section QPKG.
Hypothesis PS : poison_shadow_spec.
Hypothesis CD : cache_dealloc_specC.
Hypothesis GBB : get_block_begin_spec.
Hypothesis LD : large_dealloc_spec.
Hypothesis LDP : large_dealloc_pend_spec.
Hypothesis RSPIN : refill_spec_spin.

Local Ltac infra := first [ exact qcr_carve_proof | exact qcr_carve_prim_proof | exact qcr_carve_sec_proof | exact RTREP_qchunk_proof
                          | exact RTREP_keepS_proof | exact PS | exact CD | exact GBB | exact LD | exact LDP ].

Lemma pkg_qcr_prim : qcr_prim_spec. Proof. eapply qcr_prim_proof; infra. Qed.
Lemma pkg_qcr_sec : qcr_sec_spec. Proof. eapply qcr_sec_proof; infra. Qed.
Lemma pkg_qcr_pend : qcr_pend_spec. Proof. eapply qcr_pend_proof; infra. Qed.
Lemma pkg_dorec : dorec_spec. Proof. apply dorec_proof; [exact pkg_qcr_prim| exact pkg_qcr_sec| exact CD]. Qed.
Lemma pkg_drain : drain_spec. Proof. apply drain_proof. exact pkg_dorec. Qed.
Lemma pkg_enqueue : enqueue_spec. Proof. apply enqueue_proof. exact RSPIN. Qed.

Theorem quarantine_put_proof : quarantine_put_spec2.
Proof. apply quarantine_put_core; [exact PS| exact pkg_enqueue| exact pkg_drain| exact pkg_qcr_pend]. Qed.
End QPKG.

End CeilWrap.
End RTW_q_put.

(* [comment removed for export] *)
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
Module RTW_sec_madvgate.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LMeasure OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMadv.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_sec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_depot_mmap OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_lib.RTW_sec_dealloc1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CeilWrap.
Context {ACEIL : Ceil}.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma madv_gate_sec : forall st mo g mb n,
  RTWF st -> LOK bsegs mo -> RTMODEL st mo -> SWIN st g -> noaccess_pos mo -> In (mb, n) (st_sec st) ->
  rp_beg (SH mb) < rp_end (SH (mb + smapsize n)) ->
  madv_gate mo (g_win g) (rp_beg (SH mb)) (rp_end (SH (mb + smapsize n)) - rp_beg (SH mb)).
Proof.
  intros st mo g mb n WF HO HM HSW NP HIN HLT.
  destruct (sec_range st WF (mb, n) HIN) as (AB & _ & _). cbn [fst snd] in AB.
  set (S := smapsize n) in *.
  pose proof (ablk_lin _ _ AB) as (A1 & A2 & A3 & A4). pose proof (ablk_disj_band _ _ AB) as AD.
  pose proof (@alloc_ceiling_hi ACEIL) as CH. pose proof (@alloc_ceiling_lo ACEIL) as CL.
  destruct (ws_entry st (wf_sec_ok st WF) (mb, n) HIN) as (_ & EN & _). cbn [fst snd] in EN.
  assert (HS : 0 <= S) by (pose proof (smapsize_pos n ltac:(lia)); subst S; lia).
  pose proof (rt_SH_bounds mb ltac:(lia)) as B1. pose proof (rt_SH_bounds (mb + S) ltac:(lia)) as B2.
  rewrite rp_beg_val in * by lia. rewrite rp_end_val in * by lia.
  set (b' := (SH mb + 4095) / 4096 * 4096) in *. set (e' := SH (mb + S) / 4096 * 4096) in *.
  assert (Rb : SH mb <= b' /\ b' mod 4096 = 0) by (subst b'; Z.div_mod_to_equations; lia).
  assert (Re : e' <= SH (mb + S) /\ e' mod 4096 = 0) by (subst e'; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  destruct HM as (_ & _ & M3 & M4 & _ & _ & M7 & _).
  assert (ENT : exists lo sz, zin lo sz (vm_maps (m_vmmaps mo)) /\ 0 <= lo /\ lo + sz < 2^64 /\ 0 <= sz /\ lo <= b' /\ e' <= lo + sz
                 /\ ((KLOWSHADOW_BEG <= lo /\ lo + sz <= KLOWSHADOW_END) \/ (KHIGHSHADOW_BEG <= lo /\ lo + sz <= KHIGHMEM_BEG))).
  { unfold SH, SHADOW_OFFSET, KLOWSHADOW_BEG, KLOWSHADOW_END, KHIGHSHADOW_BEG, KHIGHMEM_BEG, AIMG_HI in *.
    destruct AD as [AD|AD].
    - exists 0x7fff7000, (0x8fff7000 - 0x7fff7000). split; [exact M4|]. Z.div_mod_to_equations. lia.
    - exists 0x2008fff7000, (0x10007fff8000 - 0x2008fff7000). split; [exact M3|]. Z.div_mod_to_equations. lia. }
  destruct ENT as (elo & esz & EIN & E0 & E1 & E2 & E3 & E4 & EB).
  assert (BND : KLOWSHADOW_BEG <= b' /\ e' <= KHIGHMEM_BEG) by (unfold KLOWSHADOW_BEG, KLOWSHADOW_END, KHIGHSHADOW_BEG, KHIGHMEM_BEG in *; lia).
  unfold KLOWSHADOW_BEG, KHIGHMEM_BEG in BND.
  unfold madv_gate. replace (b' + (e' - b')) with e' by lia.
  assert (Ub : bv_unsigned (Z_to_bv 64 b' : word) = b') by (apply unsigned_lit; lia).
  assert (Un : bv_unsigned (Z_to_bv 64 (e' - b') : word) = e' - b') by (apply unsigned_lit; lia).
  split; [unfold AIMG_HI; lia|]. split; [lia|]. split; [| split; [| split]].
  - (* [comment removed for export] *)
    apply region_free_intro. intros b k Hin. pose proof (reserved_below mo b k HO Hin) as RB. unfold AIMG_HI in RB.
    unfold iv_overlap. rewrite Ub, Un. apply andb_false_iff. left. apply Z.ltb_ge. lia.
  - unfold map_contains. apply existsb_exists. exists (wz elo, wz esz). split; [exact EIN|]. cbn [fst snd]. unfold wz.
    rewrite Ub, Un, !unsigned_lit by lia. apply andb_true_iff. split; apply Z.leb_le; lia.
  - apply region_free_of_pointwise; [exact NP| | rewrite Un; lia| rewrite Ub, Un; lia].
    intros x Hx. rewrite Ub, Un in Hx.
    assert (LZ : lzf mo x = true).
    { apply M7. unfold KLOWSHADOW_BEG, KLOWSHADOW_END, KHIGHSHADOW_BEG, KHIGHMEM_BEG in *. lia. }
    unfold lzf in LZ. apply andb_true_iff in LZ as [_ LZ]. apply negb_true_iff in LZ. exact LZ.
  - intros x Hx _. apply (HSW (mb, n) HIN). cbn [fst snd]. fold S. lia.
Qed.

End CeilWrap.
End RTW_sec_madvgate.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ITree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require AShadow.
Module RTW_sec_dealloc.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LMeasure OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_secz.RT_artZ OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_front OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_sec.RTW_secondary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_abs.RTW_m_lib3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drainw.RTW_m_leaves2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_tpz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_poison8.RT_poison_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_poison8.RT_poison3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_bandtac RTW_sec_madvgate OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_spz.RTW_sec_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_lib.RTW_sec_alloc1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_lib.RTW_sec_alloc5 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_secz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_sec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstate RTW_sec_dstate2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_hz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_fpU OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_lib.RTW_sec_dealloc1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_lib.RTW_sec_unmap OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_lib.RTW_sec_dealloc2 RTW_sec_dealloc3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.ABand.
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

Ltac djs := cbn [disjoint_from cells_size Cells.csize fst snd length app]; rewrite ?Nat.add_0_r, ?Z2Nat.id by lia; unfold PTRARR_RES_SIZE, APOISON_STACK, CEIL, KHIGHMEM_BEG, AIMG_HI in *; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section LD.
  Variables (ra sp gp tp s0e s1e s2e s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : word -> option byte) (mo : Model) (G : list (Z * Z)) (R : Z) (st : rtstate) (b : qbatch) (d mb n lo : Z).
  Hypothesis HR : RTREP st m.
  Hypothesis WF : RTWF st.
  Hypothesis HM : RTMODEL st mo.
  Hypothesis HG : GWIN st m mo (mkG G R).
  Hypothesis HFR : FRONTR mo R.
  Hypothesis HSW : SWIN st (mkG G R).
  Hypothesis HP : bprim n = false.
  Hypothesis QC : st_qcur st = [(b, d)].
  Hypothesis Hd : 0 <= d < qb_count b.
  Hypothesis EL : nthz (qb_elems b) d (0,0) = (sec_user mb, n).
  Hypothesis TP : tp = wz ATP.
  Hypothesis ST : stk bsegs m lo (bv_unsigned sp).
  Hypothesis HCEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - 2048.
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis NWX : no_wx bsegs.
  Hypothesis HOK : LOK bsegs mo.
  Hypothesis HBINV : BINV mo (mkG G R).

  Let stD := st_secdereg st mb b d.
  Let S := smapsize n.
  Let idx := sec_index st mb.
  Let PA := st_pa st.
  Let T := st_t st.
  Let M := dM st mb.

  (* [comment removed for export] *)
  Definition Wd : list (Z * Z) :=
    [(lo, bv_unsigned sp); (A_SECONDARY, A_SECONDARY + 624); (A_GSTATS, A_GSTATS + 40); (PA + 8 * idx, PA + 8 * idx + 8);
     (M + 24, M + 32); (SH mb, SH (mb + S)); (T + 2888, T + 2904); (mb, mb + S)].
  Ltac inW n := lazymatch n with O => left; reflexivity | Datatypes.S ?k => right; inW k end.
  Ltac sub1 := first [ eapply sub_fp_cons_in; [inW 0%nat| lia| lia|] | eapply sub_fp_cons_in; [inW 1%nat| lia| lia|]
                     | eapply sub_fp_cons_in; [inW 2%nat| lia| lia|] | eapply sub_fp_cons_in; [inW 3%nat| lia| lia|]
                     | eapply sub_fp_cons_in; [inW 4%nat| lia| lia|] | eapply sub_fp_cons_in; [inW 5%nat| lia| lia|]
                     | eapply sub_fp_cons_in; [inW 6%nat| lia| lia|] | eapply sub_fp_cons_in; [inW 7%nat| lia| lia|] ].
  Ltac subfp := unfold Wd; rewrite ?A_SECONDARY_val, ?A_GSTATS_val; unfold PTRARR_RES_SIZE, APOISON_STACK in *;
                repeat (first [apply sub_fp_nil | sub1]).
  (* [comment removed for export] *)
  Ltac sub1k K := first [ eapply sub_fp_cons_in; [inW 0%nat| K; lia| K; lia|] | eapply sub_fp_cons_in; [inW 1%nat| K; lia| K; lia|]
                     | eapply sub_fp_cons_in; [inW 2%nat| K; lia| K; lia|] | eapply sub_fp_cons_in; [inW 3%nat| K; lia| K; lia|]
                     | eapply sub_fp_cons_in; [inW 4%nat| K; lia| K; lia|] | eapply sub_fp_cons_in; [inW 5%nat| K; lia| K; lia|]
                     | eapply sub_fp_cons_in; [inW 6%nat| K; lia| K; lia|] | eapply sub_fp_cons_in; [inW 7%nat| K; lia| K; lia|] ].
  Ltac subfpk K := unfold Wd; rewrite ?A_SECONDARY_val, ?A_GSTATS_val; unfold PTRARR_RES_SIZE, APOISON_STACK in *;
                repeat (first [apply sub_fp_nil | sub1k K]).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ld_tail2 : forall (m1 m2 : word -> option byte) (mo2 : Model) (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    munch Wd m m2 -> wmono bsegs m m2 ->
    RTREP stD m1 -> munch [(SH mb, SH mb + S / 8); (bv_unsigned sp + -32 - APOISON_STACK, bv_unsigned sp + -32)] m1 m2 -> wmono bsegs m1 m2 ->
    mem_inv bsegs m2 -> stk bsegs m2 lo (bv_unsigned sp + -32) ->
    rw_cells bsegs m2 (bv_unsigned sp + -32) [C8 s2e; C8 s1e; C8 s0e; C8 ra] ->
    rw_cells bsegs m2 mb [W8 mb; W8 S; W8 (needed n); W8 idx] ->
    RTMODEL st mo2 -> FRONTR mo2 R -> sec_plain mo2 mb S -> GWIN st m2 mo2 (mkG G R) -> LOK bsegs mo2 ->
    LSCPS bsegs (sec_dealloc_post ra sp gp tp s0e s1e s2e s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st b d mb n lo m (mkG G R))
      (MS (mkR (wz 0x34838) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp x5 x6 x7 (wz mb) (wz mb)
               x10 x11 x12 x13 x14 x15 x16 x17 (wz S) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x34838) fc None m2 (seg_rom bsegs)) mo2 (mkG G R).
  Proof.
    intros until x31. intros MU02 WM02 HRD1 MU12 WM12 MI2 ST2 FR2 HDR2 HM2 HFR2 PL2 GW2 HOK2.
    (nelimp (ld_facts st mb n b d WF HP QC Hd EL) 17%nat; intros N40 B1 B2 B3 S1 S2 P1 P2 P3 DJ NR HI N20 DJT T1 T2 _).
    fold S idx PA T in B2, S1, S2, P1, P2, P3, DJ, HI, DJT, T1, T2.
    (* [comment removed for export] *)
    unfold KHIGHMEM_BEG, KLOWSHADOW_BEG, AIMG_HI, AIMG_LO in B1, P1, T1.
    assert (NUM : 0x5ff000 <= mb /\ mb + S <= alloc_ceiling /\ 0x5ff000 <= PA /\ PA + 8388608 <= alloc_ceiling /\ 4096 <= T /\ T + 4096 <= alloc_ceiling)
      by (unfold CEIL, PTRARR_RES_SIZE in B2, P2, T2; lia).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    assert (ES : S = smapsize n) by reflexivity.
    pose proof HCEIL as CEIL'. idtac. pose proof (t_vs_pa st WF) as TPA. fold T PA in TPA.
    pose proof (WFD st mb n b d WF HP QC Hd EL) as WFD'. fold stD in WFD'.
    (nelimp (st_secdereg_fields st mb b d WF QC) 14%nat; intros Esec Eqc Espend Enres Epa Et Esp0 Elb Elf Etrs Edep Ectx Eqp Epb).
    fold stD PA T in Espend, Enres, Epa, Et, Esp0, Elb, Elf, Etrs, Edep, Ectx, Eqp, Epb.
    pose proof (mb_fresh' st mb n b d WF HP QC Hd EL) as MF. fold stD S in MF.
    assert (FOK : fresh_ok stD [(mb, mb + S)]).
    { intros f [<-|[]]. cbn [fst snd]. split; [blia|]. intros r Hr. destruct (MF r Hr); lia. }
    assert (SHB : SH mb + S / 8 = SH (mb + S) /\ 0x7fff8000 <= SH mb /\ SH (mb + S) <= 0x10007fef8000   (* [comment removed for export] *)
                  /\ ((SH (mb + S) <= 0x8fff7000 /\ mb + S <= 0x7fff7000) \/ (0x2008fff7000 <= SH mb /\ 0x10007fff8000 <= mb))).   (* [comment removed for export] *)
    { unfold CEIL in B2. pose proof (@alloc_ceiling_hi ACEIL) as CHI. rewrite !SH_def. unfold SHADOW_OFFSET. Z.div_mod_to_equations. (lia_on B1 S2 NUM H H0 H4 H5 H9 H10 H14). }
    (nelim SHB 4%nat; intros SHE SHlo SHhi SHband).
    (* [comment removed for export] *)
    assert (RTT : forall mx, munch [(lo, bv_unsigned sp); (SH mb, SH (mb + S)); (T + 2888, T + 2904)] m1 mx -> wmono bsegs m1 mx -> RTREP stD mx).
    { intros mx MUx WMx.
      eapply (RTREP_szi stD _ [(mb, mb + S)] m1 mx WFD'); [| exact FOK| intros f [<-|[]]; cbn; lia| | | exact MUx| exact WMx| exact HRD1].
      - constructor; [apply sz_ok_stack; cbn; unfold CEIL; lia|].
        constructor; [eapply (sz_ok_fresh_sh stD _ (mb, mb + S)); [left; reflexivity| cbn; lia| cbn; lia]|].
        constructor; [apply sz_ok_stats; cbn; rewrite Et; unfold T_STATS, T_UNWINDING; lia| constructor].
      - unfold WOK_alloc. unfold A_SECONDARY, A_GSTATS, A_QUAR, A_MAXUSERSZ. unfold A_ALLOC. cbn [disjoint_from]. unfold KHIGHMEM_BEG, AIMG_HI, CEIL in *. repeat split; lia.
      - split; [intros i Hi| intros e He]; cbn [disjoint_from fst snd].
        + rewrite Epa. unfold KHIGHMEM_BEG, AIMG_HI, CEIL, PTRARR_RES_SIZE in *.
          pose proof (dereg_nsec' st mb n b d WF HP QC Hd EL) as EN. fold stD in EN. repeat split; (lia_on P3 NUM CEIL' Hi EN P1 TPA SHlo SHhi).
        + rewrite Espend in He.
          destruct (ws_spend st (wf_sec_ok st WF) e He) as [HE _].
          pose proof (sec_entry_range st WF (fst e) (snd e) ltac:(rewrite <- surjective_pairing; exact HE)) as ER. unfold CEIL, KHIGHMEM_BEG, AIMG_HI in ER.
          pose proof (sec_vs_t st WF e HE) as ET. fold T in ET.
          destruct (sec_disj st WF mb n (fst e) (snd e) (mbn_in_sec' st mb n b d WF HP QC Hd EL) ltac:(rewrite <- surjective_pairing; exact HE)) as [EQ|ED];
            [exfalso; exact (spend_not_mb st mb n b d WF HP QC Hd EL e He EQ)|].
          pose proof (smapsize_pos (snd e) ltac:(lia)) as [SP8 _]. fold S in ED.
          unfold KHIGHMEM_BEG, AIMG_HI, CEIL in *. repeat split; (cut_on [CEIL' ER SP8 SHlo SHhi ET] blia). }
    assert (MT2 : munch [(lo, bv_unsigned sp); (SH mb, SH (mb + S)); (T + 2888, T + 2904)] m1 m2) by (eapply munch_weaken; [| exact MU12]; subfp).
    pose proof (RTT m2 MT2 WM12) as HRD2.
    pose proof (rtrep_artcells stD m2 HRD2) as AC. pose proof (artcells_icpt m2 AC) as IC2. pose proof (artcells_poison m2 AC) as PC2. clear AC.
    (* [comment removed for export] *)
    apply lscps_step_evt. unfold S.
    eapply (ld_D1 sp gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m2 n mb). unfold AFLUSH_SHADOW. cbv beta delta [wz]. fold S.
    (* [comment removed for export] *)
    pose proof (sec_entry_range st WF mb n (mbn_in_sec' st mb n b d WF HP QC Hd EL)) as (ABK & _). fold S in ABK.
    assert (RPB : SH mb <= rp_beg (SH mb) /\ rp_end (SH (mb + S)) <= SH (mb + S)).
    { rewrite rp_beg_val, rp_end_val by lia. Z.div_mod_to_equations. (lia_on H H0 H4 H5). }
    apply evt_done.
    eapply (flush_shadow_spec) with (lo := lo) (p := mb) (sz := S);
      [ exact IC2 | exact PC2 | exact MI2 | rewrite unsigned_lit by lia; exact ST2 | split; [exact HCEIL| rewrite unsigned_lit by lia; lia]
      | split; [exact ABK| lia]
      | intros HLT; exact (madv_gate_sec st mo2 (mkG G R) mb n WF HOK2 HM2 HSW (FRONTR_noaccess_pos _ _ HFR2) (mbn_in_sec' st mb n b d WF HP QC Hd EL) HLT) | ].
    intros y5 y10 y11 y12 y13 y14 y15 y16 y17 m3 MI3 MU23 WM23 ST3.
    rewrite unsigned_lit in MU23, ST3 by lia.
    apply lscps_step_evt.
    replace (ret_pc (Z_to_bv 64 0x34844)) with (Z_to_bv 64 0x34844 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (MT3 : munch [(lo, bv_unsigned sp); (SH mb, SH (mb + S)); (T + 2888, T + 2904)] m1 m3) by (eapply munch_trans; [exact MT2|]; eapply munch_weaken; [| exact MU23]; subfp).
    assert (MU03 : munch Wd m m3) by (eapply munch_trans; [exact MU02|]; eapply munch_weaken; [| exact MU23]; subfpk ltac:(cut_to LO S1 NUM SHlo RPB)).
    pose proof (wmono_trans bsegs _ _ _ WM12 WM23) as WM13. pose proof (wmono_trans bsegs _ _ _ WM02 WM23) as WM03.
    pose proof FR2 as FR3. eapply (rw_cells_transport bsegs _ m2 m3) in FR3; [| exact MU23| exact WM23| djs].
    pose proof HDR2 as HDR3. eapply (rw_cells_transport bsegs _ m2 m3) in HDR3; [| exact MU23| exact WM23| djs].
    pose proof (GWIN_mem st m2 m3 mo2 _ GW2 HOK2 WM23) as GW3.
    clear IC2 PC2 MI2 ST2 FR2 HDR2 GW2 MT2 HRD2 MU23 WM23.
    pose proof (RTT m3 MT3 WM13) as HRD3.
    (* [comment removed for export] *)
    unfold S. eapply (ld_D2 sp gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m3 n mb). fold S.
    eapply evt_cut.
    { eapply get_thread_stats_c; [exact (leafc_of_RTREP stD m3 HRD3)| exact WFD'| exact MI3| exact TP| rewrite unsigned_lit by lia; exact ST3| exact HCEIL| rewrite unsigned_lit by lia; lia]. }
    cbv beta delta [leaf_post]. intros ms4 nelH_; (nelim nelH_ 22%nat; intros z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 m4 -> MU34 WM34 MI4 ST4 ->).
    rewrite unsigned_lit in MU34, ST4 by lia. rewrite Et.
    replace (ret_pc (wz 0x34848)) with (Z_to_bv 64 0x34848 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (MT4 : munch [(lo, bv_unsigned sp); (SH mb, SH (mb + S)); (T + 2888, T + 2904)] m1 m4) by (eapply munch_trans; [exact MT3|]; eapply munch_weaken; [| exact MU34]; subfp).
    assert (MU04 : munch Wd m m4) by (eapply munch_trans; [exact MU03|]; eapply munch_weaken; [| exact MU34]; subfp).
    pose proof (wmono_trans bsegs _ _ _ WM13 WM34) as WM14. pose proof (wmono_trans bsegs _ _ _ WM03 WM34) as WM04.
    pose proof FR3 as FR4. eapply (rw_cells_transport bsegs _ m3 m4) in FR4; [| exact MU34| exact WM34| djs].
    pose proof HDR3 as HDR4. eapply (rw_cells_transport bsegs _ m3 m4) in HDR4; [| exact MU34| exact WM34| djs].
    pose proof (GWIN_mem st m3 m4 mo2 _ GW3 HOK2 WM34) as GW4.
    clear MI3 ST3 FR3 HDR3 GW3 MT3 HRD3 MU34 WM34 MU03 WM13 WM03.
    pose proof (RTT m4 MT4 WM14) as HRD4.
    (* [comment removed for export] *)
    pose proof (rr_thread stD m4 HRD4) as RT4. destruct RT4 as (VT4 & _). rewrite Et in VT4.
    (nelim (vis_c8x2 m4 _ _ (T + 2888) VT4 ltac:(lia) ltac:(lia)) 3%nat; intros j88 j96 TS4).
    assert (HBK : (AIMG_HI <= mb /\ (mb + smapsize n <= KLOWSHADOW_BEG \/ KHIGHMEM_BEG <= mb)) /\ mb + smapsize n <= CEIL /\ mb mod 4096 = 0)
      by (clear - B1 B2 B3; unfold S, CEIL in *; unfold AIMG_HI, KLOWSHADOW_BEG, KHIGHMEM_BEG; lia).
    assert (HTK : 4096 <= T /\ (T + 4096 <= AIMG_LO \/ AIMG_HI <= T) /\ (T + 4096 <= KLOWSHADOW_BEG \/ KHIGHMEM_BEG <= T))
      by (clear - T1; unfold AIMG_LO, AIMG_HI, KLOWSHADOW_BEG, KHIGHMEM_BEG; lia).
    unfold S. eapply (ld_D3 ra sp gp tp s0e s1e s2e s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m4 n mb lo T ltac:(lia) HP ltac:(lia) HBK HCEIL LO _ j88 j96);
      [exact HTK| unfold T, CEIL in *; lia| exact DJT| exact MI4| exact TS4| exact HDR4| exact FR4| exact ST4|]. fold S.
    intros m5 v13 v14 MI5 MU45 WM45 ST5 TS5.
    assert (MT5 : munch [(lo, bv_unsigned sp); (SH mb, SH (mb + S)); (T + 2888, T + 2904)] m1 m5) by (eapply munch_trans; [exact MT4|]; eapply munch_weaken; [| exact MU45]; subfpk ltac:(cut_all)).
    assert (MU05 : munch Wd m m5) by (eapply munch_trans; [exact MU04|]; eapply munch_weaken; [| exact MU45]; subfpk ltac:(cut_all)).
    pose proof (wmono_trans bsegs _ _ _ WM14 WM45) as WM15.
    pose proof (GWIN_mem st m4 m5 mo2 _ GW4 HOK2 WM45) as GW5.
    clear MI4 ST4 FR4 HDR4 GW4 MT4 HRD4 MU45 WM45 MU04 WM14 TS4 VT4 TS5.
    pose proof (RTT m5 MT5 WM15) as HRD5.
    pose proof (rtrep_artcells stD m5 HRD5) as AC. pose proof (artcells_icpt m5 AC) as IC5. pose proof (artcells_poison m5 AC) as PC5. clear AC.
    apply evt_done. unfold A_UNMAP_OR_DIE, S. cbv beta delta [wz]. fold S.
    (* [comment removed for export] *)
    eapply (unmap_or_die_spec ra sp gp tp _ _ _ s0e s1e _ _ _ _ _ s2e s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m5 mo2 G R mb S lo IC5 PC5 MI5 ST5);
      [lia| idtac; unfold CEIL in B2; lia| exact (sec_map_has st mo2 mb n HM2 (mbn_in_sec' st mb n b d WF HP QC Hd EL) ltac:(lia) ltac:(lia) ltac:(lia))| exact PL2|].
    intros w5 w10 w11 w12 w13 w14 w15 w16 w17 m6 MI6 MU56 ST6.
    (nelimp HBINV 3%nat; intros _ R0 _). cbn [g_res] in R0.
    eapply (lscps_res_le _ _ _ _ G (R + S) R); [lia|].
    assert (MU06 : munch Wd m m6) by (eapply munch_trans; [exact MU05|]; eapply munch_weaken; [| exact MU56]; subfpk ltac:(cut_to NUM)).
    (* [comment removed for export] *)
    apply lscps_done. unfold sec_dealloc_post, rt_post_std. nexists 15%nat. exists m6, stD.
    split; [reflexivity|]. split; [exact MI6|].
    split; [exact (dereg_rel' st mb n b d WF HP QC Hd EL)|].
    assert (HSPc : CEIL <= bv_unsigned sp) by (unfold CEIL; lia).
    split.
    { apply RTS_intro.
      - eapply (RTREP_transportU stD WFD' [(lo, bv_unsigned sp); (mb, mb + S)] m5 m6 MU56); [| exact HRD5|].
        + intros lo' hi' [Hl|(r & Hr & Hr1 & Hr2)]; cbn [disjoint_from]; [unfold KHIGHMEM_BEG, AIMG_HI, CEIL in *; repeat split; (lia_on CEIL' Hl HBK)|].
          (nelimp (wb_ranges stD (wf_base_ok stD WFD') r Hr) 4%nat; intros Q1 Q2 Q3 _). pose proof (MF r Hr) as Q4. unfold KHIGHMEM_BEG, AIMG_HI, CEIL in *. repeat split; (lia_on CEIL' Hr2 Q3 Hr1 Q4).
        + eapply (szi_wok_all stD _ [(mb, mb + S)] WFD'); [| exact FOK| intros f [<-|[]]; cbn; lia| |].
          * constructor; [apply sz_ok_stack; cbn; unfold CEIL; lia|].
            constructor; [eapply (sz_ok_fresh stD _ (mb, mb + S)); [left; reflexivity| cbn; lia| cbn; lia]| constructor].
          * unfold WOK_alloc. unfold A_SECONDARY, A_GSTATS, A_QUAR, A_MAXUSERSZ. unfold A_ALLOC. cbn [disjoint_from]. unfold KHIGHMEM_BEG, AIMG_HI, CEIL in *. repeat split; lia.
          * split; [intros i Hi| intros e He]; cbn [disjoint_from fst snd].
            -- rewrite Epa. unfold KHIGHMEM_BEG, AIMG_HI, CEIL, PTRARR_RES_SIZE in *.
               pose proof (dereg_nsec' st mb n b d WF HP QC Hd EL) as EN. fold stD in EN. repeat split; (lia_on P3 NUM CEIL' Hi EN DJ).
            -- rewrite Espend in He. destruct (ws_spend st (wf_sec_ok st WF) e He) as [HE _].
               pose proof (sec_entry_range st WF (fst e) (snd e) ltac:(rewrite <- surjective_pairing; exact HE)) as ER. unfold CEIL, KHIGHMEM_BEG, AIMG_HI in ER.
               destruct (sec_disj st WF mb n (fst e) (snd e) (mbn_in_sec' st mb n b d WF HP QC Hd EL) ltac:(rewrite <- surjective_pairing; exact HE)) as [EQ|ED];
                 [exfalso; exact (spend_not_mb st mb n b d WF HP QC Hd EL e He EQ)|].
               pose proof (smapsize_pos (snd e) ltac:(lia)) as [SP8 _]. fold S in ED.
               unfold KHIGHMEM_BEG, AIMG_HI, CEIL in *. repeat split; (lia_on CEIL' HBK ER SP8 ED).
      - exact WFD'.
      - unfold S. apply (RTMODEL_dereg' st mb n b d WF HP QC Hd EL mo2 HOK2 HM2).
      - apply (GWIN_dereg' st mb b d WF QC). eapply (GWIN_unmap st m5 m6 mo2 _ mb S lo (bv_unsigned sp) WF HOK2 GW5); [lia| lia| exact B2| unfold CEIL; lia| exact MU56].
      - apply FRONTR_unmap. exact HFR2.
      - apply (SWIN_dereg' st mb n b d WF HP QC Hd EL). exact HSW. }
    split; [exact ST6|].
    split.
    { unfold cli_pres. eapply cj_pres_of_munch0; [exact MU06|].
      pose proof (dM_In st mb n b d WF HP QC Hd EL) as DMI. fold M in DMI.
      intros x Hx HC. unfold Wd. cbn [outside]. rewrite A_SECONDARY_val, A_GSTATS_val.
      split; [intros Hin; exact (below_sp_not_client st WF (bv_unsigned sp) x ltac:(unfold CEIL; lia) HC)|].
      split; [intros Hin; exact (wstatic_not_client' st (bv_unsigned sp) x WF HSPc ltac:(lia) HC)|].
      split; [intros Hin; exact (wstatic_not_client' st (bv_unsigned sp) x WF HSPc ltac:(lia) HC)|].
      split; [intros Hin; exact (pa_not_client st WF (bv_unsigned sp) HSPc x ltac:(unfold PA, PTRARR_RES_SIZE in *; lia) HC)|].
      split; [intros Hin; exact (sechdr_not_client st WF (bv_unsigned sp) HSPc M (dMn st mb n) x DMI ltac:(lia) HC)|].
      split; [intros Hin; apply (fresh_shadow_not_client stD WFD' (bv_unsigned sp) HSPc mb S MF ABK x Hin); rewrite Esp0, Elb, Elf; exact HC|].
      split; [intros Hin; exact (tpage_not_client st WF (bv_unsigned sp) HSPc x ltac:(unfold T, T_ACACHE in *; lia) HC)|].
      split; [intros Hin; apply (fresh_not_client stD WFD' (bv_unsigned sp) HSPc mb S MF ABK x Hin); rewrite Esp0, Elb, Elf; exact HC| exact I]. }
    split.
    { eapply rt_frame_of_munch; [exact MU06|].
      pose proof (dM_In st mb n b d WF HP QC Hd EL) as DMI. fold M in DMI.
      intros iv Hiv. unfold Wd in Hiv. unfold secondary_fp, fp_tpage. fold PA T S.
      cbn in Hiv. destruct Hiv as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; cbn [fst snd]; [left; lia| right..].
      - exists (A_SECONDARY, A_SECONDARY + 624). split; [cbn; solve [repeat (first [left; reflexivity| right])]| cbn [fst snd]; lia].
      - exists (A_GSTATS, A_GSTATS + 40). split; [cbn; solve [repeat (first [left; reflexivity| right])]| cbn [fst snd]; lia].
      - exists (PA, PA + PTRARR_RES_SIZE). split; [cbn; solve [repeat (first [left; reflexivity| right])]| cbn [fst snd]; unfold PTRARR_RES_SIZE in *; lia].
      - exists (M, M + 32). split; [| cbn [fst snd]; lia]. cbn [app]. do 6 right. apply in_map_iff. exists (M, dMn st mb n). split; [reflexivity| exact DMI].
      - exists (SH mb - 4096, SH (mb + S) + 4096). split; [cbn; solve [repeat (first [left; reflexivity| right])]| cbn [fst snd]; lia].
      - exists (T, T + 4096). split; [cbn; solve [repeat (first [left; reflexivity| right])]| cbn [fst snd]; lia].
      - exists (mb, mb + S). split; [cbn; solve [repeat (first [left; reflexivity| right])]| cbn [fst snd]; lia]. }
    split; [intros w Hw; exact Hw|].
    unfold budget_ok. cbn [g_res]. pose proof (rt_prov_dereg' st mb n b d WF HP QC Hd EL) as PV. fold stD in PV. unfold SEC_SLOT_TAX in PV. lia.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ld_ps : forall (m1 : word -> option byte) (y5 y6 y7 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
    munch Wd m m1 -> wmono bsegs m m1 -> RTREP stD m1 -> mem_inv bsegs m1 -> stk bsegs m1 lo (bv_unsigned sp + -32) ->
    rw_cells bsegs m1 (bv_unsigned sp + -32) [C8 s2e; C8 s1e; C8 s0e; C8 ra] ->
    rw_cells bsegs m1 mb [W8 mb; W8 S; W8 (needed n); W8 idx] ->
    vis m1 (SH mb) (SH mb + S / 8) -> GWIN st m1 mo (mkG G R) ->
    LSCPS bsegs (sec_dealloc_post ra sp gp tp s0e s1e s2e s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st b d mb n lo m (mkG G R))
      (MS (mkR (wz 0x34838) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp y5 y6 y7 (wz mb) (wz mb)
               (wz mb) (wz S) (wz 0) y13 y14 y15 y16 y17 (wz S) s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
          F (wz APOISON_SHADOW) fc None m1 (seg_rom bsegs)) mo (mkG G R).
  Proof.
    intros until y31. intros MU01 WM01 HRD1 MI1 ST1 FR1 HDR1 VSH1 GW1.
    (nelimp (ld_facts st mb n b d WF HP QC Hd EL) 7%nat; intros N40 B1 B2 B3 S1 S2 _).
    fold S in B2, S1, S2.
    unfold KHIGHMEM_BEG, KLOWSHADOW_BEG, AIMG_HI in B1.   (* [comment removed for export] *)
    assert (NUM : 0x5ff000 <= mb /\ mb + S <= alloc_ceiling) by (unfold CEIL in B2; lia).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    assert (ES : S = smapsize n) by reflexivity.
    pose proof HCEIL as CEIL'. idtac.
    pose proof (sec_win_of st (mkG G R) mb n HSW (mbn_in_sec' st mb n b d WF HP QC Hd EL)) as SHW.
    pose proof (sec_plain_of st mo mb n HM (mbn_in_sec' st mb n b d WF HP QC Hd EL)) as PLN. fold S in PLN.
    assert (SHB : SH mb + S / 8 = SH (mb + S) /\ 0x7fff8000 <= SH mb /\ SH (mb + S) <= 0x10007fef8000 /\ (SH mb) mod 512 = 0 /\ S mod 8 = 0).   (* [comment removed for export] *)
    { pose proof (@alloc_ceiling_hi ACEIL) as CHI. clear - B1 B3 S1 S2 NUM CHI. rewrite !SH_def. unfold SHADOW_OFFSET. Z.div_mod_to_equations. lia. }
    (nelim SHB 5%nat; intros SHE SHlo SHhi SHal S8).
    pose proof (rtrep_artcells stD m1 HRD1) as AC. pose proof (artcells_icpt m1 AC) as IC1. pose proof (artcells_poison m1 AC) as PC1. clear AC.
    destruct (vis_carve m1 _ _ (SH mb) (Z.to_nat (S / 8)) VSH1 ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as [junk SHJ].
    unfold APOISON_SHADOW. cbv beta delta [wz].
    (* [comment removed for export] *)
    { (* [comment removed for export] *)
      apply lscps_step_evt.
      eapply evt_mono; [eapply poison_shadow_ok; [exact IC1| exact PC1| exact MI1| rewrite unsigned_lit by lia; exact ST1| exact HCEIL
          | rewrite unsigned_lit by lia; unfold APOISON_STACK; lia| reflexivity| reflexivity| reflexivity| lia| exact S8| lia
          | clear - B1 NUM S1; unfold app_range, lowmem_range, highmem_range, KLOWSHADOW_BEG, KHIGHMEM_BEG, AIMG_HI, KHIGHMEM_END; pose proof (@alloc_ceiling_hi ACEIL); lia| lia| intros _; lia| exact SHJ]|].
      cbv beta. intros ms2 nelH_; (nelim nelH_ 22%nat; intros u5 u6 u7 u10 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 m2 -> MU12 WM12 MI2 PSH ST2).
      rewrite unsigned_lit in MU12, ST2 by lia.
      replace (ret_pc (Z_to_bv 64 0x34838)) with (wz 0x34838 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (MU02 : munch Wd m m2) by (eapply munch_trans; [exact MU01|]; eapply munch_weaken; [| exact MU12]; subfp).
      eapply (ld_tail2 m1 m2 mo); [exact MU02| exact (wmono_trans bsegs _ _ _ WM01 WM12)| exact HRD1| exact MU12| exact WM12| exact MI2| exact ST2
        | eapply rw_cells_transport; [exact FR1| exact MU12| exact WM12| djs]
        | eapply rw_cells_transport; [exact HDR1| exact MU12| exact WM12| djs]
        | exact HM| exact HFR| exact PLN| exact (GWIN_mem st m1 m2 mo _ GW1 HOK WM12)| exact HOK]. }
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition W0 : list (Z * Z) :=
    [(lo, bv_unsigned sp); (0xa6398 + 56, 0xa6398 + 96); (0xa6600, 0xa6604); (PA + 8 * idx, PA + 8 * idx + 8); (M + 24, M + 32); (0xa6608 + 16, 0xa6608 + 32)].

  (* [comment removed for export] *)
  Lemma ld_rep : forall (m1 : word -> option byte) j1 j2' b1 b2 b3 j4 jg',
    munch W0 m m1 -> wmono bsegs m m1 ->
    rw_cells bsegs m1 A_SECONDARY [W8 4096; W8 PA; W8 PA; W8 PTRARR_RES_SIZE; CB 16 j1; W8 (st_nreserved st); W8 (nsec st - 1); CB 552 j2'] ->
    rw_cells bsegs m1 0xa6600 [C1 (zb 0); CB 3 [b1; b2; b3]; CB 4 j4] ->
    rw_cells bsegs m1 A_GSTATS [CB 40 jg'] ->
    (idx < nsec st - 1 -> rw_cells bsegs m1 (PA + 8 * idx) [W8 (fst (last (st_sec st) (0,0)))] /\ rw_cells bsegs m1 (fst (last (st_sec st) (0,0)) + 24) [W8 idx]) ->
    RTREP stD m1.
  Proof.
    intros m1 j1 j2' b1 b2 b3 j4 jg' MU01 WM01 SEC1 MX1 GST1 NEWc.
    (nelimp (ld_facts st mb n b d WF HP QC Hd EL) 17%nat; intros N40 B1 B2 B3 S1 S2 P1 P2 P3 DJ NR HI N20 DJT T1 T2 CASEA).
    fold S idx PA T in B2, S1, S2, P1, P2, P3, DJ, HI, DJT, T1, T2.
    (* [comment removed for export] *)
    destruct B1 as [B1 B1d]. destruct P1 as [P1 P1d]. apply bandf_intro in B1d. apply bandf_intro in P1d. unfold AIMG_HI in B1, P1.
    assert (NUM : 0x5ff000 <= mb /\ mb + S <= alloc_ceiling /\ 0x5ff000 <= PA /\ PA + 8388608 <= alloc_ceiling)
      by (unfold CEIL, PTRARR_RES_SIZE in B2, P2; lia).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof HCEIL as CEIL'. idtac.
    (nelimp (dM_range st mb n b d WF HP QC Hd EL) 4%nat; intros D1 D2 D3 D4). fold M in D1, D2, D3.
    pose proof (dM_In st mb n b d WF HP QC Hd EL) as DMI. fold M in DMI.
    unfold KHIGHMEM_BEG, AIMG_HI, CEIL in D1, D2.
    pose proof (pa_vs_sec st WF M (dMn st mb n) DMI) as DMP. fold PA in DMP. unfold PTRARR_RES_SIZE in DMP.
    (* [comment removed for export] *)
    assert (MUp : munch ([(lo, bv_unsigned sp); (0xa6398 + 56, 0xa6398 + 96); (0xa6600, 0xa6604); (PA + 8 * idx, PA + 8 * idx + 8); (0xa6608 + 16, 0xa6608 + 32)] ++ [(M + 24, M + 32)]) m m1).
    { eapply munch_perm; [| exact MU01]. unfold W0. intros iv Hiv. cbn in Hiv |- *. clear - Hiv. tauto. }
    (nelim (munch_interpolate _ _ _ m m1 MUp WM01) 5%nat; intros mX MUa WMa MUb WMb). clear MUp.
    assert (HRnX : RTREP_nsec st mX).
    { unshelve (eapply (szi_others st WF _ [] _ _ _ m mX MUa WMa HR)).
      - constructor; [apply sz_ok_stack; cbn; unfold CEIL; lia|].
        constructor; [apply sz_ok_static; cbn; unfold A_QUAR, A_SECONDARY, A_ALLOC; lia|].
        constructor; [apply sz_ok_static; cbn; unfold A_QUAR, A_SECONDARY, A_ALLOC; lia|].
        constructor; [apply sz_ok_pa; cbn; fold PA; unfold PTRARR_RES_SIZE; lia|].
        constructor; [apply sz_ok_static; cbn; unfold A_QUAR, A_SECONDARY, A_ALLOC; lia| constructor].
      - intros f [].
      - intros f []. }
    assert (HRnD : RTREP_nsec stD m1).
    { eapply (RTREP_nsec_dereg st mb n b d WF HP QC Hd EL mX m1 HRnX); [exact MUb| exact WMb|].
      intros LT. exact (proj2 (NEWc LT)). }
    apply (RTREP_of_nsec stD m1 HRnD).
    - eapply (R_alloc_dereg_intro st mb n b d WF HP QC Hd EL W0 m m1 j1 j2' ([b1; b2; b3] ++ j4) jg' (rr_alloc st m HR) MU01 WM01).
      + unfold W0, A_ALLOC. cbn. lia.
      + unfold W0, A_QUAR, A_ALLOC. cbn. lia.
      + unfold W0, A_MAXUSERSZ, A_ALLOC. cbn. lia.
      + apply (proj2 (RT_kit.rw_cells_app m1 A_SECONDARY [W8 4096; W8 PA; W8 PA; W8 PTRARR_RES_SIZE; CB 16 j1; W8 (st_nreserved st); W8 (nsec st - 1); CB 552 j2'] [W1 0; CB 7 ([b1; b2; b3] ++ j4)])).
        split; [exact SEC1|]. rewrite A_SECONDARY_val. cbn [cells_size Cells.csize Nat.add]. apply mutex_cells_merge. exact MX1.
      + exact GST1.
    - eapply (R_ptrarr_dereg_intro st mb n b d WF HP QC Hd EL W0 m m1 (rr_ptrarr st m HR) MU01 WM01).
      + intros i Hi NE. unfold W0. cbn. repeat split; first [lia| fold PA idx; nia].
      + intros e He NEM. destruct (ws_spend st (wf_sec_ok st WF) e He) as [HE _].
        pose proof (sec_entry_range st WF (fst e) (snd e) ltac:(rewrite <- surjective_pairing; exact HE)) as ER. unfold CEIL, KHIGHMEM_BEG, AIMG_HI in ER.
        pose proof (pa_vs_sec st WF (fst e) (snd e) ltac:(rewrite <- surjective_pairing; exact HE)) as EP. fold PA in EP. unfold PTRARR_RES_SIZE in EP.
        pose proof (smapsize_pos (snd e) ltac:(lia)) as [SP8 _].
        destruct (sec_disj st WF M (dMn st mb n) (fst e) (snd e) DMI ltac:(rewrite <- surjective_pairing; exact HE)) as [EQ|ED]; [exfalso; exact (NEM EQ)|].
        unfold W0. cbn. repeat split; first [(lia_on CEIL' D3 NEM ER EP SP8 HI N20)| fold PA idx; nia].
      + intros e He. destruct (ws_spend st (wf_sec_ok st WF) e He) as [HE _].
        pose proof (sec_entry_range st WF (fst e) (snd e) ltac:(rewrite <- surjective_pairing; exact HE)) as ER. unfold CEIL, KHIGHMEM_BEG, AIMG_HI in ER.
        pose proof (pa_vs_sec st WF (fst e) (snd e) ltac:(rewrite <- surjective_pairing; exact HE)) as EP. fold PA in EP. unfold PTRARR_RES_SIZE in EP.
        pose proof (smapsize_pos (snd e) ltac:(lia)) as [SP8 _].
        destruct (sec_disj st WF M (dMn st mb n) (fst e) (snd e) DMI ltac:(rewrite <- surjective_pairing; exact HE)) as [EQ|ED];
          unfold W0; cbn; repeat split; first [(lia_on CEIL' D3 HI N20 ER EP SP8)| fold PA idx; nia].
      + intros LT. exact (proj1 (NEWc LT)).
      + intros LT. exact (proj2 (NEWc LT)).
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ld_main : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    LSCPS bsegs (sec_dealloc_post ra sp gp tp s0e s1e s2e s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st b d mb n lo m (mkG G R))
      (MS (mkR ra sp gp tp t0 t1 t2 s0e s1e (wz A_SECONDARY) (wz A_GSTATS) (wz (sec_alloc_beg mb)) a3 a4 a5 a6 a7
               s2e s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz ALARGE_DEALLOC) fc None m (seg_rom bsegs)) mo (mkG G R).
  Proof.
    intros.
    (nelim (ld_cells st m mb n b d HR WF HP QC Hd EL) 20%nat; intros j1 j2 k b1 b2 b3 j4 jg SEC HK E0 E1 MW MJ HDR PIX GST VS VM CASEc).
    (nelimp (ld_facts st mb n b d WF HP QC Hd EL) 17%nat; intros N40 B1 B2 B3 S1 S2 P1 P2 P3 DJ NR HI N20 DJT T1 T2 CASEf).
    fold S idx PA T in B2, S1, S2, P1, P2, P3, DJ, HI, DJT, T1, T2, PIX, VS, VM, HDR, CASEc.
    (* [comment removed for export] *)
    destruct B1 as [B1 B1d]. destruct P1 as [P1 P1d]. apply bandf_intro in B1d. apply bandf_intro in P1d. unfold AIMG_HI in B1, P1.
    assert (NUM : 0x5ff000 <= mb /\ mb + S <= alloc_ceiling /\ 0x5ff000 <= PA /\ PA + 8388608 <= alloc_ceiling)
      by (unfold CEIL, PTRARR_RES_SIZE in B2, P2; lia).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof HCEIL as CEIL'. idtac.
    rewrite A_SECONDARY_val in SEC. rewrite A_GSTATS_val in GST.
    assert (HB : (AIMG_HI <= mb /\ (mb + smapsize n <= KLOWSHADOW_BEG \/ KHIGHMEM_BEG <= mb)) /\ mb + smapsize n <= CEIL /\ mb mod 4096 = 0) by (split; [exact (conj B1 B1d)| split; [exact B2| exact B3]]).
    apply bandf_intro in HB.
    assert (HPA : (AIMG_HI <= PA /\ (PA + PTRARR_RES_SIZE <= KLOWSHADOW_BEG \/ KHIGHMEM_BEG <= PA)) /\ PA + PTRARR_RES_SIZE <= CEIL /\ 8 * nsec st <= PTRARR_RES_SIZE) by (split; [exact (conj P1 P1d)| split; [exact P2| exact P3]]).
    apply bandf_intro in HPA.
    assert (NRS : 0 <= st_nreserved st < 2^64 /\ 0 <= idx < nsec st /\ nsec st <= 2^20) by (split; [exact NR| split; [exact HI| exact N20]]).
    pose proof (SH_def mb) as SHd. unfold SHADOW_OFFSET in SHd.
    apply lscps_step_evt.
    destruct (Z_lt_le_dec idx (nsec st - 1)) as [LT|GE].
    - (* [comment removed for export] *)
      (nelim (CASEc LT) 3%nat; intros PLS hl HL24). pose proof (CASEf LT) as CF. cbv zeta in CF. (nelim CF 6%nat; intros F1 F2 F3 F4 F5 F6).
      pose proof (dM_other st mb n b d WF HP QC Hd EL LT) as (ED & _). fold M in ED. rewrite <- ED in PLS, HL24, F1, F2, F3, F4, F5, F6.
      eapply (ld_D0a ra sp gp tp s0e s1e s2e s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m n mb k lo PA (wz PTRARR_RES_SIZE) j1 (st_nreserved st) (nsec st) idx j2
                 (wz (needed n)) b1 b2 b3 j4 jg ltac:(lia) HP ltac:(lia) HB HPA DJ NRS HK E1 HCEIL LO _ M hl);
        [exact LT| clear - F1 F2 F3 F4 F5 S1; unfold S, AIMG_HI, KLOWSHADOW_BEG, KHIGHMEM_BEG in *; lia| exact MI| exact ST| exact SEC| exact MW| exact MJ| exact HDR| exact PIX| exact PLS| exact HL24| exact GST|].
      cbv beta. intros ms1 nelH_; (nelim nelH_ 19%nat; intros y5 y6 y7 y13 y14 y15 y16 y17 y28 y29 y30 y31 m1 -> D0M HDR1 PIX1 PLS1 HL1).
      (nelim D0M 8%nat; intros MU01 WM01 MI1 ST1 FR1 [j2' SEC1] MX1 [jg' GST1]).
      apply evt_done.
      assert (HRD1 : RTREP stD m1).
      { eapply (ld_rep m1 j1 j2' b1 b2 b3 j4 jg'); [exact MU01| exact WM01| rewrite A_SECONDARY_val; exact SEC1| exact MX1| rewrite A_GSTATS_val; exact GST1|].
        intros _. rewrite <- ED. split; [exact PIX1| exact HL1]. }
      eapply (ld_ps m1); [eapply munch_weaken; [| exact MU01]; subfpk ltac:(cut_to B1 S1 NUM NRS)| exact WM01| exact HRD1| exact MI1| exact ST1| exact FR1| exact HDR1
        | eapply stk_wmono_noseg; [exact VS| exact WM01| unfold AIMG_HI; lia]
        | exact (GWIN_mem st m m1 mo _ HG HOK WM01)].
    - (* [comment removed for export] *)
      assert (EM : M = mb) by (unfold M, dM; fold idx; destruct (Z.ltb_spec0 idx (nsec st - 1)); [lia| reflexivity]).
      eapply (ld_D0b ra sp gp tp s0e s1e s2e s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m n mb k lo PA (wz PTRARR_RES_SIZE) j1 (st_nreserved st) (nsec st) idx j2
                 (wz (needed n)) b1 b2 b3 j4 jg ltac:(lia) HP ltac:(lia) HB HPA DJ NRS HK E1 HCEIL LO);
        [lia| exact MI| exact ST| exact SEC| exact MW| exact MJ| exact HDR| exact PIX| exact GST|].
      cbv beta. intros ms1 nelH_; (nelim nelH_ 17%nat; intros y5 y6 y7 y13 y14 y15 y16 y17 y28 y29 y30 y31 m1 -> D0M HDR1 PIX1).
      (nelim D0M 8%nat; intros MU01 WM01 MI1 ST1 FR1 [j2' SEC1] MX1 [jg' GST1]).
      replace (mb + 24, mb + 32) with (M + 24, M + 32) in MU01 by (rewrite EM; reflexivity).
      apply evt_done.
      assert (HRD1 : RTREP stD m1).
      { eapply (ld_rep m1 j1 j2' b1 b2 b3 j4 jg'); [exact MU01| exact WM01| rewrite A_SECONDARY_val; exact SEC1| exact MX1| rewrite A_GSTATS_val; exact GST1|].
        intros LT. exfalso. lia. }
      eapply (ld_ps m1); [eapply munch_weaken; [| exact MU01]; subfpk ltac:(cut_to B1 S1 NUM NRS EM)| exact WM01| exact HRD1| exact MI1| exact ST1| exact FR1| exact HDR1
        | eapply stk_wmono_noseg; [exact VS| exact WM01| unfold AIMG_HI; lia]
        | exact (GWIN_mem st m m1 mo _ HG HOK WM01)].
  Qed.
End LD.

Theorem large_dealloc_proof : large_dealloc_spec.
Proof.
  unfold large_dealloc_spec. intros until lo. intros RTS0 QC Hd EL HP -> -> -> TP ST HCEIL LO MI.
  (nelim RTS0 6%nat; intros HR WF HM HG HFR HSW).
  apply lscps_assume. intros NWX HOK HBINV. destruct g as [G R]. cbn [g_res g_win] in *.
  unfold ALARGE_DEALLOC_STACK in LO.
  eapply (ld_main ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo G R st b d mb n lo); eassumption.
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac djs := cbn [disjoint_from cells_size Cells.csize fst snd length app]; rewrite ?Nat.add_0_r, ?Z2Nat.id by lia; unfold PTRARR_RES_SIZE, APOISON_STACK, CEIL, KHIGHMEM_BEG, AIMG_HI in *; lia.
End RTW_sec_dealloc.

(* [comment removed for export] *)
Module RTW_sec_deallocP.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LMeasure OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_secz.RT_artZ OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_front OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_sec.RTW_secondary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_abs.RTW_m_lib3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drainw.RTW_m_leaves2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_tpz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_poison8.RT_poison_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_poison8.RT_poison3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_bandtac RTW_sec_madvgate OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_spz.RTW_sec_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_lib.RTW_sec_alloc1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_lib.RTW_sec_alloc5 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_secz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_sec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstate RTW_sec_dstate2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_hz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_fpU OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_lib.RTW_sec_dealloc1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_lib.RTW_sec_unmap OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_lib.RTW_sec_dealloc2 RTW_sec_dealloc3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstateP.RT_trans OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_sec.RTW_q_needs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstateP RTW_sec_dstate2P RTW_sec_dealloc3P OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.ABand.
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

Ltac djs := cbn [disjoint_from cells_size Cells.csize fst snd length app]; rewrite ?Nat.add_0_r, ?Z2Nat.id by lia; unfold PTRARR_RES_SIZE, APOISON_STACK, CEIL, KHIGHMEM_BEG, AIMG_HI in *; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section LDP.
  Variables (ra sp gp tp s0e s1e s2e s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : word -> option byte) (mo : Model) (G : list (Z * Z)) (R : Z) (st : rtstate) (mb n lo : Z).
  Hypothesis HR : RTREP st m.
  Hypothesis WF : RTWF st.
  Hypothesis HM : RTMODEL st mo.
  Hypothesis HG : GWIN st m mo (mkG G R).
  Hypothesis HFR : FRONTR mo R.
  Hypothesis HSW : SWIN st (mkG G R).
  Hypothesis HP : bprim n = false.
  Hypothesis PEND : In (sec_user mb, n) (st_qpend st).
  Hypothesis TP : tp = wz ATP.
  Hypothesis ST : stk bsegs m lo (bv_unsigned sp).
  Hypothesis HCEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - 2048.
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis NWX : no_wx bsegs.
  Hypothesis HOK : LOK bsegs mo.
  Hypothesis HBINV : BINV mo (mkG G R).

  Let stD := st_secderegP st mb n.
  Let S := smapsize n.
  Let idx := sec_index st mb.
  Let PA := st_pa st.
  Let T := st_t st.
  Let M := dM st mb.

  (* [comment removed for export] *)
  Definition Wd : list (Z * Z) :=
    [(lo, bv_unsigned sp); (A_SECONDARY, A_SECONDARY + 624); (A_GSTATS, A_GSTATS + 40); (PA + 8 * idx, PA + 8 * idx + 8);
     (M + 24, M + 32); (SH mb, SH (mb + S)); (T + 2888, T + 2904); (mb, mb + S)].
  Ltac inW n := lazymatch n with O => left; reflexivity | Datatypes.S ?k => right; inW k end.
  Ltac sub1 := first [ eapply sub_fp_cons_in; [inW 0%nat| lia| lia|] | eapply sub_fp_cons_in; [inW 1%nat| lia| lia|]
                     | eapply sub_fp_cons_in; [inW 2%nat| lia| lia|] | eapply sub_fp_cons_in; [inW 3%nat| lia| lia|]
                     | eapply sub_fp_cons_in; [inW 4%nat| lia| lia|] | eapply sub_fp_cons_in; [inW 5%nat| lia| lia|]
                     | eapply sub_fp_cons_in; [inW 6%nat| lia| lia|] | eapply sub_fp_cons_in; [inW 7%nat| lia| lia|] ].
  Ltac subfp := unfold Wd; rewrite ?A_SECONDARY_val, ?A_GSTATS_val; unfold PTRARR_RES_SIZE, APOISON_STACK in *;
                repeat (first [apply sub_fp_nil | sub1]).
  (* [comment removed for export] *)
  Ltac sub1k K := first [ eapply sub_fp_cons_in; [inW 0%nat| K; lia| K; lia|] | eapply sub_fp_cons_in; [inW 1%nat| K; lia| K; lia|]
                     | eapply sub_fp_cons_in; [inW 2%nat| K; lia| K; lia|] | eapply sub_fp_cons_in; [inW 3%nat| K; lia| K; lia|]
                     | eapply sub_fp_cons_in; [inW 4%nat| K; lia| K; lia|] | eapply sub_fp_cons_in; [inW 5%nat| K; lia| K; lia|]
                     | eapply sub_fp_cons_in; [inW 6%nat| K; lia| K; lia|] | eapply sub_fp_cons_in; [inW 7%nat| K; lia| K; lia|] ].
  Ltac subfpk K := unfold Wd; rewrite ?A_SECONDARY_val, ?A_GSTATS_val; unfold PTRARR_RES_SIZE, APOISON_STACK in *;
                repeat (first [apply sub_fp_nil | sub1k K]).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ld_tail2 : forall (m1 m2 : word -> option byte) (mo2 : Model) (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    munch Wd m m2 -> wmono bsegs m m2 ->
    RTREP stD m1 -> munch [(SH mb, SH mb + S / 8); (bv_unsigned sp + -32 - APOISON_STACK, bv_unsigned sp + -32)] m1 m2 -> wmono bsegs m1 m2 ->
    mem_inv bsegs m2 -> stk bsegs m2 lo (bv_unsigned sp + -32) ->
    rw_cells bsegs m2 (bv_unsigned sp + -32) [C8 s2e; C8 s1e; C8 s0e; C8 ra] ->
    rw_cells bsegs m2 mb [W8 mb; W8 S; W8 (needed n); W8 idx] ->
    RTMODEL st mo2 -> FRONTR mo2 R -> sec_plain mo2 mb S -> GWIN st m2 mo2 (mkG G R) -> LOK bsegs mo2 ->
    LSCPS bsegs (sec_dealloc_pend_post ra sp gp tp s0e s1e s2e s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st (sec_user mb) n mb lo m (mkG G R))
      (MS (mkR (wz 0x34838) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp x5 x6 x7 (wz mb) (wz mb)
               x10 x11 x12 x13 x14 x15 x16 x17 (wz S) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x34838) fc None m2 (seg_rom bsegs)) mo2 (mkG G R).
  Proof.
    intros until x31. intros MU02 WM02 HRD1 MU12 WM12 MI2 ST2 FR2 HDR2 HM2 HFR2 PL2 GW2 HOK2.
    (nelimp (ld_facts st mb n WF HP PEND) 17%nat; intros N40 B1 B2 B3 S1 S2 P1 P2 P3 DJ NR HI N20 DJT T1 T2 _).
    fold S idx PA T in B2, S1, S2, P1, P2, P3, DJ, HI, DJT, T1, T2.
    (* [comment removed for export] *)
    unfold KHIGHMEM_BEG, KLOWSHADOW_BEG, AIMG_HI, AIMG_LO in B1, P1, T1.
    assert (NUM : 0x5ff000 <= mb /\ mb + S <= alloc_ceiling /\ 0x5ff000 <= PA /\ PA + 8388608 <= alloc_ceiling /\ 4096 <= T /\ T + 4096 <= alloc_ceiling)
      by (unfold CEIL, PTRARR_RES_SIZE in B2, P2, T2; lia).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    assert (ES : S = smapsize n) by reflexivity.
    pose proof HCEIL as CEIL'. idtac. pose proof (t_vs_pa st WF) as TPA. fold T PA in TPA.
    pose proof (WFD st mb n WF HP PEND) as WFD'. fold stD in WFD'.
    (nelimp (st_secdereg_fields st mb n WF HP PEND) 14%nat; intros Esec Eqc Espend Enres Epa Et Esp0 Elb Elf Etrs Edep Ectx Eqp Epb).
    fold stD PA T in Espend, Enres, Epa, Et, Esp0, Elb, Elf, Etrs, Edep, Ectx, Eqp, Epb.
    pose proof (mb_fresh' st mb n WF HP PEND) as MF. fold stD S in MF.
    assert (FOK : fresh_ok stD [(mb, mb + S)]).
    { intros f [<-|[]]. cbn [fst snd]. split; [blia|]. intros r Hr. destruct (MF r Hr); lia. }
    assert (SHB : SH mb + S / 8 = SH (mb + S) /\ 0x7fff8000 <= SH mb /\ SH (mb + S) <= 0x10007fef8000   (* [comment removed for export] *)
                  /\ ((SH (mb + S) <= 0x8fff7000 /\ mb + S <= 0x7fff7000) \/ (0x2008fff7000 <= SH mb /\ 0x10007fff8000 <= mb))).   (* [comment removed for export] *)
    { unfold CEIL in B2. pose proof (@alloc_ceiling_hi ACEIL) as CHI. rewrite !SH_def. unfold SHADOW_OFFSET. Z.div_mod_to_equations. (lia_on B1 S2 NUM H H0 H4 H5 H9 H10 H14). }
    (nelim SHB 4%nat; intros SHE SHlo SHhi SHband).
    (* [comment removed for export] *)
    assert (RTT : forall mx, munch [(lo, bv_unsigned sp); (SH mb, SH (mb + S)); (T + 2888, T + 2904)] m1 mx -> wmono bsegs m1 mx -> RTREP stD mx).
    { intros mx MUx WMx.
      eapply (RTREP_szi stD _ [(mb, mb + S)] m1 mx WFD'); [| exact FOK| intros f [<-|[]]; cbn; lia| | | exact MUx| exact WMx| exact HRD1].
      - constructor; [apply sz_ok_stack; cbn; unfold CEIL; lia|].
        constructor; [eapply (sz_ok_fresh_sh stD _ (mb, mb + S)); [left; reflexivity| cbn; lia| cbn; lia]|].
        constructor; [apply sz_ok_stats; cbn; rewrite Et; unfold T_STATS, T_UNWINDING; lia| constructor].
      - unfold WOK_alloc. unfold A_SECONDARY, A_GSTATS, A_QUAR, A_MAXUSERSZ. unfold A_ALLOC. cbn [disjoint_from]. unfold KHIGHMEM_BEG, AIMG_HI, CEIL in *. repeat split; lia.
      - split; [intros i Hi| intros e He]; cbn [disjoint_from fst snd].
        + rewrite Epa. unfold KHIGHMEM_BEG, AIMG_HI, CEIL, PTRARR_RES_SIZE in *.
          pose proof (dereg_nsec' st mb n WF HP PEND) as EN. fold stD in EN. repeat split; (lia_on P3 NUM CEIL' Hi EN P1 TPA SHlo SHhi).
        + rewrite Espend in He.
          destruct (ws_spend st (wf_sec_ok st WF) e He) as [HE _].
          pose proof (sec_entry_range st WF (fst e) (snd e) ltac:(rewrite <- surjective_pairing; exact HE)) as ER. unfold CEIL, KHIGHMEM_BEG, AIMG_HI in ER.
          pose proof (sec_vs_t st WF e HE) as ET. fold T in ET.
          destruct (sec_disj st WF mb n (fst e) (snd e) (mbn_in_sec' st mb n WF HP PEND) ltac:(rewrite <- surjective_pairing; exact HE)) as [EQ|ED];
            [exfalso; exact (spend_not_mb st mb n WF HP PEND e He EQ)|].
          pose proof (smapsize_pos (snd e) ltac:(lia)) as [SP8 _]. fold S in ED.
          unfold KHIGHMEM_BEG, AIMG_HI, CEIL in *. repeat split; (cut_on [CEIL' ER SP8 SHlo SHhi ET] blia). }
    assert (MT2 : munch [(lo, bv_unsigned sp); (SH mb, SH (mb + S)); (T + 2888, T + 2904)] m1 m2) by (eapply munch_weaken; [| exact MU12]; subfp).
    pose proof (RTT m2 MT2 WM12) as HRD2.
    pose proof (rtrep_artcells stD m2 HRD2) as AC. pose proof (artcells_icpt m2 AC) as IC2. pose proof (artcells_poison m2 AC) as PC2. clear AC.
    (* [comment removed for export] *)
    apply lscps_step_evt. unfold S.
    eapply (ld_D1 sp gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m2 n mb). unfold AFLUSH_SHADOW. cbv beta delta [wz]. fold S.
    (* [comment removed for export] *)
    pose proof (sec_entry_range st WF mb n (mbn_in_sec' st mb n WF HP PEND)) as (ABK & _). fold S in ABK.
    assert (RPB : SH mb <= rp_beg (SH mb) /\ rp_end (SH (mb + S)) <= SH (mb + S)).
    { rewrite rp_beg_val, rp_end_val by lia. Z.div_mod_to_equations. (lia_on H H0 H4 H5). }
    apply evt_done.
    eapply (flush_shadow_spec) with (lo := lo) (p := mb) (sz := S);
      [ exact IC2 | exact PC2 | exact MI2 | rewrite unsigned_lit by lia; exact ST2 | split; [exact HCEIL| rewrite unsigned_lit by lia; lia]
      | split; [exact ABK| lia]
      | intros HLT; exact (madv_gate_sec st mo2 (mkG G R) mb n WF HOK2 HM2 HSW (FRONTR_noaccess_pos _ _ HFR2) (mbn_in_sec' st mb n WF HP PEND) HLT) | ].
    intros y5 y10 y11 y12 y13 y14 y15 y16 y17 m3 MI3 MU23 WM23 ST3.
    rewrite unsigned_lit in MU23, ST3 by lia.
    apply lscps_step_evt.
    replace (ret_pc (Z_to_bv 64 0x34844)) with (Z_to_bv 64 0x34844 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (MT3 : munch [(lo, bv_unsigned sp); (SH mb, SH (mb + S)); (T + 2888, T + 2904)] m1 m3) by (eapply munch_trans; [exact MT2|]; eapply munch_weaken; [| exact MU23]; subfp).
    assert (MU03 : munch Wd m m3) by (eapply munch_trans; [exact MU02|]; eapply munch_weaken; [| exact MU23]; subfpk ltac:(cut_to LO S1 NUM SHlo RPB)).
    pose proof (wmono_trans bsegs _ _ _ WM12 WM23) as WM13. pose proof (wmono_trans bsegs _ _ _ WM02 WM23) as WM03.
    pose proof FR2 as FR3. eapply (rw_cells_transport bsegs _ m2 m3) in FR3; [| exact MU23| exact WM23| djs].
    pose proof HDR2 as HDR3. eapply (rw_cells_transport bsegs _ m2 m3) in HDR3; [| exact MU23| exact WM23| (cut_on [LO B1 S1 NUM CEIL' SHlo SHhi RPB] djs)].
    pose proof (GWIN_mem st m2 m3 mo2 _ GW2 HOK2 WM23) as GW3.
    clear IC2 PC2 MI2 ST2 FR2 HDR2 GW2 MT2 HRD2 MU23 WM23.
    pose proof (RTT m3 MT3 WM13) as HRD3.
    (* [comment removed for export] *)
    unfold S. eapply (ld_D2 sp gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m3 n mb). fold S.
    eapply evt_cut.
    { eapply get_thread_stats_c; [exact (leafc_of_RTREP stD m3 HRD3)| exact WFD'| exact MI3| exact TP| rewrite unsigned_lit by lia; exact ST3| exact HCEIL| rewrite unsigned_lit by lia; lia]. }
    cbv beta delta [leaf_post]. intros ms4 nelH_; (nelim nelH_ 22%nat; intros z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 m4 -> MU34 WM34 MI4 ST4 ->).
    rewrite unsigned_lit in MU34, ST4 by lia. rewrite Et.
    replace (ret_pc (wz 0x34848)) with (Z_to_bv 64 0x34848 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (MT4 : munch [(lo, bv_unsigned sp); (SH mb, SH (mb + S)); (T + 2888, T + 2904)] m1 m4) by (eapply munch_trans; [exact MT3|]; eapply munch_weaken; [| exact MU34]; subfp).
    assert (MU04 : munch Wd m m4) by (eapply munch_trans; [exact MU03|]; eapply munch_weaken; [| exact MU34]; subfp).
    pose proof (wmono_trans bsegs _ _ _ WM13 WM34) as WM14. pose proof (wmono_trans bsegs _ _ _ WM03 WM34) as WM04.
    pose proof FR3 as FR4. eapply (rw_cells_transport bsegs _ m3 m4) in FR4; [| exact MU34| exact WM34| djs].
    pose proof HDR3 as HDR4. eapply (rw_cells_transport bsegs _ m3 m4) in HDR4; [| exact MU34| exact WM34| djs].
    pose proof (GWIN_mem st m3 m4 mo2 _ GW3 HOK2 WM34) as GW4.
    clear MI3 ST3 FR3 HDR3 GW3 MT3 HRD3 MU34 WM34 MU03 WM13 WM03.
    pose proof (RTT m4 MT4 WM14) as HRD4.
    (* [comment removed for export] *)
    pose proof (rr_thread stD m4 HRD4) as RT4. destruct RT4 as (VT4 & _). rewrite Et in VT4.
    (nelim (vis_c8x2 m4 _ _ (T + 2888) VT4 ltac:(lia) ltac:(lia)) 3%nat; intros j88 j96 TS4).
    assert (HBK : (AIMG_HI <= mb /\ (mb + smapsize n <= KLOWSHADOW_BEG \/ KHIGHMEM_BEG <= mb)) /\ mb + smapsize n <= CEIL /\ mb mod 4096 = 0)
      by (clear - B1 B2 B3; unfold S, CEIL in *; unfold AIMG_HI, KLOWSHADOW_BEG, KHIGHMEM_BEG; lia).
    assert (HTK : 4096 <= T /\ (T + 4096 <= AIMG_LO \/ AIMG_HI <= T) /\ (T + 4096 <= KLOWSHADOW_BEG \/ KHIGHMEM_BEG <= T))
      by (clear - T1; unfold AIMG_LO, AIMG_HI, KLOWSHADOW_BEG, KHIGHMEM_BEG; lia).
    unfold S. eapply (ld_D3 ra sp gp tp s0e s1e s2e s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m4 n mb lo T ltac:(lia) HP ltac:(lia) HBK HCEIL LO _ j88 j96);
      [exact HTK| unfold T, CEIL in *; lia| exact DJT| exact MI4| exact TS4| exact HDR4| exact FR4| exact ST4|]. fold S.
    intros m5 v13 v14 MI5 MU45 WM45 ST5 TS5.
    assert (MT5 : munch [(lo, bv_unsigned sp); (SH mb, SH (mb + S)); (T + 2888, T + 2904)] m1 m5) by (eapply munch_trans; [exact MT4|]; eapply munch_weaken; [| exact MU45]; subfpk ltac:(cut_all)).
    assert (MU05 : munch Wd m m5) by (eapply munch_trans; [exact MU04|]; eapply munch_weaken; [| exact MU45]; subfpk ltac:(cut_all)).
    pose proof (wmono_trans bsegs _ _ _ WM14 WM45) as WM15.
    pose proof (GWIN_mem st m4 m5 mo2 _ GW4 HOK2 WM45) as GW5.
    clear MI4 ST4 FR4 HDR4 GW4 MT4 HRD4 MU45 WM45 MU04 WM14 TS4 VT4 TS5.
    pose proof (RTT m5 MT5 WM15) as HRD5.
    pose proof (rtrep_artcells stD m5 HRD5) as AC. pose proof (artcells_icpt m5 AC) as IC5. pose proof (artcells_poison m5 AC) as PC5. clear AC.
    apply evt_done. unfold A_UNMAP_OR_DIE, S. cbv beta delta [wz]. fold S.
    (* [comment removed for export] *)
    eapply (unmap_or_die_spec ra sp gp tp _ _ _ s0e s1e _ _ _ _ _ s2e s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m5 mo2 G R mb S lo IC5 PC5 MI5 ST5);
      [lia| idtac; unfold CEIL in B2; (lia_on B1 B2 B3 S1 S2 HBK)| exact (sec_map_has st mo2 mb n HM2 (mbn_in_sec' st mb n WF HP PEND) ltac:(lia) ltac:(lia) ltac:(lia))| exact PL2|].
    intros w5 w10 w11 w12 w13 w14 w15 w16 w17 m6 MI6 MU56 ST6.
    (nelimp HBINV 3%nat; intros _ R0 _). cbn [g_res] in R0.
    eapply (lscps_res_le _ _ _ _ G (R + S) R); [lia|].
    assert (MU06 : munch Wd m m6) by (eapply munch_trans; [exact MU05|]; eapply munch_weaken; [| exact MU56]; subfpk ltac:(cut_to NUM)).
    (* [comment removed for export] *)
    apply lscps_done. unfold sec_dealloc_pend_post, rt_post_std. nexists 15%nat. exists m6, stD.
    split; [reflexivity|]. split; [exact MI6|].
    split; [exact (dereg_rel' st mb n WF HP PEND)|].
    assert (HSPc : CEIL <= bv_unsigned sp) by (unfold CEIL; lia).
    split.
    { apply RTS_intro.
      - eapply (RTREP_transportU stD WFD' [(lo, bv_unsigned sp); (mb, mb + S)] m5 m6 MU56); [| exact HRD5|].
        + intros lo' hi' [Hl|(r & Hr & Hr1 & Hr2)]; cbn [disjoint_from]; [unfold KHIGHMEM_BEG, AIMG_HI, CEIL in *; repeat split; (lia_on CEIL' Hl HBK)|].
          (nelimp (wb_ranges stD (wf_base_ok stD WFD') r Hr) 4%nat; intros Q1 Q2 Q3 _). pose proof (MF r Hr) as Q4. unfold KHIGHMEM_BEG, AIMG_HI, CEIL in *. repeat split; (lia_on CEIL' Hr2 Q3 Hr1 Q4).
        + eapply (szi_wok_all stD _ [(mb, mb + S)] WFD'); [| exact FOK| intros f [<-|[]]; cbn; lia| |].
          * constructor; [apply sz_ok_stack; cbn; unfold CEIL; lia|].
            constructor; [eapply (sz_ok_fresh stD _ (mb, mb + S)); [left; reflexivity| cbn; lia| cbn; lia]| constructor].
          * unfold WOK_alloc. unfold A_SECONDARY, A_GSTATS, A_QUAR, A_MAXUSERSZ. unfold A_ALLOC. cbn [disjoint_from]. unfold KHIGHMEM_BEG, AIMG_HI, CEIL in *. repeat split; lia.
          * split; [intros i Hi| intros e He]; cbn [disjoint_from fst snd].
            -- rewrite Epa. unfold KHIGHMEM_BEG, AIMG_HI, CEIL, PTRARR_RES_SIZE in *.
               pose proof (dereg_nsec' st mb n WF HP PEND) as EN. fold stD in EN. repeat split; (lia_on P3 NUM CEIL' Hi EN DJ).
            -- rewrite Espend in He. destruct (ws_spend st (wf_sec_ok st WF) e He) as [HE _].
               pose proof (sec_entry_range st WF (fst e) (snd e) ltac:(rewrite <- surjective_pairing; exact HE)) as ER. unfold CEIL, KHIGHMEM_BEG, AIMG_HI in ER.
               destruct (sec_disj st WF mb n (fst e) (snd e) (mbn_in_sec' st mb n WF HP PEND) ltac:(rewrite <- surjective_pairing; exact HE)) as [EQ|ED];
                 [exfalso; exact (spend_not_mb st mb n WF HP PEND e He EQ)|].
               pose proof (smapsize_pos (snd e) ltac:(lia)) as [SP8 _]. fold S in ED.
               unfold KHIGHMEM_BEG, AIMG_HI, CEIL in *. repeat split; (lia_on CEIL' HBK ER SP8 ED).
      - exact WFD'.
      - unfold S. apply (RTMODEL_dereg' st mb n WF HP PEND mo2 HOK2 HM2).
      - apply (GWIN_dereg' st mb n WF HP PEND). eapply (GWIN_unmap st m5 m6 mo2 _ mb S lo (bv_unsigned sp) WF HOK2 GW5); [lia| lia| exact B2| unfold CEIL; lia| exact MU56].
      - apply FRONTR_unmap. exact HFR2.
      - apply (SWIN_dereg' st mb n WF HP PEND). exact HSW. }
    split; [exact ST6|].
    split.
    { unfold cli_pres. eapply cj_pres_of_munch0; [exact MU06|].
      pose proof (dM_In st mb n WF HP PEND) as DMI. fold M in DMI.
      intros x Hx HC. unfold Wd. cbn [outside]. rewrite A_SECONDARY_val, A_GSTATS_val.
      split; [intros Hin; exact (below_sp_not_client st WF (bv_unsigned sp) x ltac:(unfold CEIL; lia) HC)|].
      split; [intros Hin; exact (wstatic_not_client' st (bv_unsigned sp) x WF HSPc ltac:(lia) HC)|].
      split; [intros Hin; exact (wstatic_not_client' st (bv_unsigned sp) x WF HSPc ltac:(lia) HC)|].
      split; [intros Hin; exact (pa_not_client st WF (bv_unsigned sp) HSPc x ltac:(unfold PA, PTRARR_RES_SIZE in *; lia) HC)|].
      split; [intros Hin; exact (sechdr_not_client st WF (bv_unsigned sp) HSPc M (dMn st mb n) x DMI ltac:(lia) HC)|].
      split; [intros Hin; apply (fresh_shadow_not_client stD WFD' (bv_unsigned sp) HSPc mb S MF ABK x Hin); rewrite Esp0, Elb, Elf; exact HC|].
      split; [intros Hin; exact (tpage_not_client st WF (bv_unsigned sp) HSPc x ltac:(unfold T, T_ACACHE in *; lia) HC)|].
      split; [intros Hin; apply (fresh_not_client stD WFD' (bv_unsigned sp) HSPc mb S MF ABK x Hin); rewrite Esp0, Elb, Elf; exact HC| exact I]. }
    split.
    { eapply rt_frame_of_munch; [exact MU06|].
      pose proof (dM_In st mb n WF HP PEND) as DMI. fold M in DMI.
      intros iv Hiv. unfold Wd in Hiv. unfold secondary_fp, fp_tpage. fold PA T S.
      cbn in Hiv. destruct Hiv as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; cbn [fst snd]; [left; lia| right..].
      - exists (A_SECONDARY, A_SECONDARY + 624). split; [cbn; solve [repeat (first [left; reflexivity| right])]| cbn [fst snd]; lia].
      - exists (A_GSTATS, A_GSTATS + 40). split; [cbn; solve [repeat (first [left; reflexivity| right])]| cbn [fst snd]; lia].
      - exists (PA, PA + PTRARR_RES_SIZE). split; [cbn; solve [repeat (first [left; reflexivity| right])]| cbn [fst snd]; unfold PTRARR_RES_SIZE in *; lia].
      - exists (M, M + 32). split; [| cbn [fst snd]; lia]. cbn [app]. do 6 right. apply in_map_iff. exists (M, dMn st mb n). split; [reflexivity| exact DMI].
      - exists (SH mb - 4096, SH (mb + S) + 4096). split; [cbn; solve [repeat (first [left; reflexivity| right])]| cbn [fst snd]; lia].
      - exists (T, T + 4096). split; [cbn; solve [repeat (first [left; reflexivity| right])]| cbn [fst snd]; lia].
      - exists (mb, mb + S). split; [cbn; solve [repeat (first [left; reflexivity| right])]| cbn [fst snd]; lia]. }
    split; [intros w Hw; exact Hw|].
    unfold budget_ok. cbn [g_res]. pose proof (rt_prov_dereg' st mb n WF HP PEND) as PV. fold stD in PV. unfold SEC_SLOT_TAX in PV. lia.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ld_ps : forall (m1 : word -> option byte) (y5 y6 y7 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
    munch Wd m m1 -> wmono bsegs m m1 -> RTREP stD m1 -> mem_inv bsegs m1 -> stk bsegs m1 lo (bv_unsigned sp + -32) ->
    rw_cells bsegs m1 (bv_unsigned sp + -32) [C8 s2e; C8 s1e; C8 s0e; C8 ra] ->
    rw_cells bsegs m1 mb [W8 mb; W8 S; W8 (needed n); W8 idx] ->
    vis m1 (SH mb) (SH mb + S / 8) -> GWIN st m1 mo (mkG G R) ->
    LSCPS bsegs (sec_dealloc_pend_post ra sp gp tp s0e s1e s2e s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st (sec_user mb) n mb lo m (mkG G R))
      (MS (mkR (wz 0x34838) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp y5 y6 y7 (wz mb) (wz mb)
               (wz mb) (wz S) (wz 0) y13 y14 y15 y16 y17 (wz S) s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
          F (wz APOISON_SHADOW) fc None m1 (seg_rom bsegs)) mo (mkG G R).
  Proof.
    intros until y31. intros MU01 WM01 HRD1 MI1 ST1 FR1 HDR1 VSH1 GW1.
    (nelimp (ld_facts st mb n WF HP PEND) 7%nat; intros N40 B1 B2 B3 S1 S2 _).
    fold S in B2, S1, S2.
    unfold KHIGHMEM_BEG, KLOWSHADOW_BEG, AIMG_HI in B1.   (* [comment removed for export] *)
    assert (NUM : 0x5ff000 <= mb /\ mb + S <= alloc_ceiling) by (unfold CEIL in B2; lia).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    assert (ES : S = smapsize n) by reflexivity.
    pose proof HCEIL as CEIL'. idtac.
    pose proof (sec_win_of st (mkG G R) mb n HSW (mbn_in_sec' st mb n WF HP PEND)) as SHW.
    pose proof (sec_plain_of st mo mb n HM (mbn_in_sec' st mb n WF HP PEND)) as PLN. fold S in PLN.
    assert (SHB : SH mb + S / 8 = SH (mb + S) /\ 0x7fff8000 <= SH mb /\ SH (mb + S) <= 0x10007fef8000 /\ (SH mb) mod 512 = 0 /\ S mod 8 = 0).   (* [comment removed for export] *)
    { pose proof (@alloc_ceiling_hi ACEIL) as CHI. clear - B1 B3 S1 S2 NUM CHI. rewrite !SH_def. unfold SHADOW_OFFSET. Z.div_mod_to_equations. lia. }
    (nelim SHB 5%nat; intros SHE SHlo SHhi SHal S8).
    pose proof (rtrep_artcells stD m1 HRD1) as AC. pose proof (artcells_icpt m1 AC) as IC1. pose proof (artcells_poison m1 AC) as PC1. clear AC.
    destruct (vis_carve m1 _ _ (SH mb) (Z.to_nat (S / 8)) VSH1 ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as [junk SHJ].
    unfold APOISON_SHADOW. cbv beta delta [wz].
    (* [comment removed for export] *)
    { (* [comment removed for export] *)
      apply lscps_step_evt.
      eapply evt_mono; [eapply poison_shadow_ok; [exact IC1| exact PC1| exact MI1| rewrite unsigned_lit by lia; exact ST1| exact HCEIL
          | rewrite unsigned_lit by lia; unfold APOISON_STACK; lia| reflexivity| reflexivity| reflexivity| lia| exact S8| lia
          | clear - B1 NUM S1; unfold app_range, lowmem_range, highmem_range, KLOWSHADOW_BEG, KHIGHMEM_BEG, AIMG_HI, KHIGHMEM_END; pose proof (@alloc_ceiling_hi ACEIL); lia| lia| intros _; lia| exact SHJ]|].
      cbv beta. intros ms2 nelH_; (nelim nelH_ 22%nat; intros u5 u6 u7 u10 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 m2 -> MU12 WM12 MI2 PSH ST2).
      rewrite unsigned_lit in MU12, ST2 by lia.
      replace (ret_pc (Z_to_bv 64 0x34838)) with (wz 0x34838 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (MU02 : munch Wd m m2) by (eapply munch_trans; [exact MU01|]; eapply munch_weaken; [| exact MU12]; subfp).
      eapply (ld_tail2 m1 m2 mo); [exact MU02| exact (wmono_trans bsegs _ _ _ WM01 WM12)| exact HRD1| exact MU12| exact WM12| exact MI2| exact ST2
        | eapply rw_cells_transport; [exact FR1| exact MU12| exact WM12| djs]
        | eapply rw_cells_transport; [exact HDR1| exact MU12| exact WM12| djs]
        | exact HM| exact HFR| exact PLN| exact (GWIN_mem st m1 m2 mo _ GW1 HOK WM12)| exact HOK]. }
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition W0 : list (Z * Z) :=
    [(lo, bv_unsigned sp); (0xa6398 + 56, 0xa6398 + 96); (0xa6600, 0xa6604); (PA + 8 * idx, PA + 8 * idx + 8); (M + 24, M + 32); (0xa6608 + 16, 0xa6608 + 32)].

  (* [comment removed for export] *)
  Lemma ld_rep : forall (m1 : word -> option byte) j1 j2' b1 b2 b3 j4 jg',
    munch W0 m m1 -> wmono bsegs m m1 ->
    rw_cells bsegs m1 A_SECONDARY [W8 4096; W8 PA; W8 PA; W8 PTRARR_RES_SIZE; CB 16 j1; W8 (st_nreserved st); W8 (nsec st - 1); CB 552 j2'] ->
    rw_cells bsegs m1 0xa6600 [C1 (zb 0); CB 3 [b1; b2; b3]; CB 4 j4] ->
    rw_cells bsegs m1 A_GSTATS [CB 40 jg'] ->
    (idx < nsec st - 1 -> rw_cells bsegs m1 (PA + 8 * idx) [W8 (fst (last (st_sec st) (0,0)))] /\ rw_cells bsegs m1 (fst (last (st_sec st) (0,0)) + 24) [W8 idx]) ->
    RTREP stD m1.
  Proof.
    intros m1 j1 j2' b1 b2 b3 j4 jg' MU01 WM01 SEC1 MX1 GST1 NEWc.
    (nelimp (ld_facts st mb n WF HP PEND) 17%nat; intros N40 B1 B2 B3 S1 S2 P1 P2 P3 DJ NR HI N20 DJT T1 T2 CASEA).
    fold S idx PA T in B2, S1, S2, P1, P2, P3, DJ, HI, DJT, T1, T2.
    (* [comment removed for export] *)
    destruct B1 as [B1 B1d]. destruct P1 as [P1 P1d]. apply bandf_intro in B1d. apply bandf_intro in P1d. unfold AIMG_HI in B1, P1.
    assert (NUM : 0x5ff000 <= mb /\ mb + S <= alloc_ceiling /\ 0x5ff000 <= PA /\ PA + 8388608 <= alloc_ceiling)
      by (unfold CEIL, PTRARR_RES_SIZE in B2, P2; lia).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof HCEIL as CEIL'. idtac.
    (nelimp (dM_range st mb n WF HP PEND) 4%nat; intros D1 D2 D3 D4). fold M in D1, D2, D3.
    pose proof (dM_In st mb n WF HP PEND) as DMI. fold M in DMI.
    unfold KHIGHMEM_BEG, AIMG_HI, CEIL in D1, D2.
    pose proof (pa_vs_sec st WF M (dMn st mb n) DMI) as DMP. fold PA in DMP. unfold PTRARR_RES_SIZE in DMP.
    (* [comment removed for export] *)
    assert (MUp : munch ([(lo, bv_unsigned sp); (0xa6398 + 56, 0xa6398 + 96); (0xa6600, 0xa6604); (PA + 8 * idx, PA + 8 * idx + 8); (0xa6608 + 16, 0xa6608 + 32)] ++ [(M + 24, M + 32)]) m m1).
    { eapply munch_perm; [| exact MU01]. unfold W0. intros iv Hiv. cbn in Hiv |- *. clear - Hiv. tauto. }
    (nelim (munch_interpolate _ _ _ m m1 MUp WM01) 5%nat; intros mX MUa WMa MUb WMb). clear MUp.
    assert (HRnX : RTREP_nsec st mX).
    { unshelve (eapply (szi_others st WF _ [] _ _ _ m mX MUa WMa HR)).
      - constructor; [apply sz_ok_stack; cbn; unfold CEIL; lia|].
        constructor; [apply sz_ok_static; cbn; unfold A_QUAR, A_SECONDARY, A_ALLOC; lia|].
        constructor; [apply sz_ok_static; cbn; unfold A_QUAR, A_SECONDARY, A_ALLOC; lia|].
        constructor; [apply sz_ok_pa; cbn; fold PA; unfold PTRARR_RES_SIZE; lia|].
        constructor; [apply sz_ok_static; cbn; unfold A_QUAR, A_SECONDARY, A_ALLOC; lia| constructor].
      - intros f [].
      - intros f []. }
    assert (HRnD : RTREP_nsec stD m1).
    { eapply (RTREP_nsec_dereg st mb n WF HP PEND mX m1 HRnX); [exact MUb| exact WMb|].
      intros LT. exact (proj2 (NEWc LT)). }
    apply (RTREP_of_nsec stD m1 HRnD).
    - eapply (R_alloc_dereg_intro st mb n WF HP PEND W0 m m1 j1 j2' ([b1; b2; b3] ++ j4) jg' (rr_alloc st m HR) MU01 WM01).
      + unfold W0, A_ALLOC. cbn. lia.
      + unfold W0, A_QUAR, A_ALLOC. cbn. lia.
      + unfold W0, A_MAXUSERSZ, A_ALLOC. cbn. lia.
      + apply (proj2 (RT_kit.rw_cells_app m1 A_SECONDARY [W8 4096; W8 PA; W8 PA; W8 PTRARR_RES_SIZE; CB 16 j1; W8 (st_nreserved st); W8 (nsec st - 1); CB 552 j2'] [W1 0; CB 7 ([b1; b2; b3] ++ j4)])).
        split; [exact SEC1|]. rewrite A_SECONDARY_val. cbn [cells_size Cells.csize Nat.add]. apply mutex_cells_merge. exact MX1.
      + exact GST1.
    - eapply (R_ptrarr_dereg_intro st mb n WF HP PEND W0 m m1 (rr_ptrarr st m HR) MU01 WM01).
      + intros i Hi NE. unfold W0. cbn. repeat split; first [lia| fold PA idx; nia].
      + intros e He NEM. destruct (ws_spend st (wf_sec_ok st WF) e He) as [HE _].
        pose proof (sec_entry_range st WF (fst e) (snd e) ltac:(rewrite <- surjective_pairing; exact HE)) as ER. unfold CEIL, KHIGHMEM_BEG, AIMG_HI in ER.
        pose proof (pa_vs_sec st WF (fst e) (snd e) ltac:(rewrite <- surjective_pairing; exact HE)) as EP. fold PA in EP. unfold PTRARR_RES_SIZE in EP.
        pose proof (smapsize_pos (snd e) ltac:(lia)) as [SP8 _].
        destruct (sec_disj st WF M (dMn st mb n) (fst e) (snd e) DMI ltac:(rewrite <- surjective_pairing; exact HE)) as [EQ|ED]; [exfalso; exact (NEM EQ)|].
        unfold W0. cbn. repeat split; first [(lia_on CEIL' D3 NEM ER EP SP8 HI N20)| fold PA idx; nia].
      + intros e He. destruct (ws_spend st (wf_sec_ok st WF) e He) as [HE _].
        pose proof (sec_entry_range st WF (fst e) (snd e) ltac:(rewrite <- surjective_pairing; exact HE)) as ER. unfold CEIL, KHIGHMEM_BEG, AIMG_HI in ER.
        pose proof (pa_vs_sec st WF (fst e) (snd e) ltac:(rewrite <- surjective_pairing; exact HE)) as EP. fold PA in EP. unfold PTRARR_RES_SIZE in EP.
        pose proof (smapsize_pos (snd e) ltac:(lia)) as [SP8 _].
        destruct (sec_disj st WF M (dMn st mb n) (fst e) (snd e) DMI ltac:(rewrite <- surjective_pairing; exact HE)) as [EQ|ED];
          unfold W0; cbn; repeat split; first [(lia_on CEIL' D3 HI N20 ER EP SP8)| fold PA idx; nia].
      + intros LT. exact (proj1 (NEWc LT)).
      + intros LT. exact (proj2 (NEWc LT)).
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ld_main : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    LSCPS bsegs (sec_dealloc_pend_post ra sp gp tp s0e s1e s2e s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st (sec_user mb) n mb lo m (mkG G R))
      (MS (mkR ra sp gp tp t0 t1 t2 s0e s1e (wz A_SECONDARY) (wz A_GSTATS) (wz (sec_alloc_beg mb)) a3 a4 a5 a6 a7
               s2e s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz ALARGE_DEALLOC) fc None m (seg_rom bsegs)) mo (mkG G R).
  Proof.
    intros.
    (nelim (ld_cells st m mb n HR WF HP PEND) 20%nat; intros j1 j2 k b1 b2 b3 j4 jg SEC HK E0 E1 MW MJ HDR PIX GST VS VM CASEc).
    (nelimp (ld_facts st mb n WF HP PEND) 17%nat; intros N40 B1 B2 B3 S1 S2 P1 P2 P3 DJ NR HI N20 DJT T1 T2 CASEf).
    fold S idx PA T in B2, S1, S2, P1, P2, P3, DJ, HI, DJT, T1, T2, PIX, VS, VM, HDR, CASEc.
    (* [comment removed for export] *)
    destruct B1 as [B1 B1d]. destruct P1 as [P1 P1d]. apply bandf_intro in B1d. apply bandf_intro in P1d. unfold AIMG_HI in B1, P1.
    assert (NUM : 0x5ff000 <= mb /\ mb + S <= alloc_ceiling /\ 0x5ff000 <= PA /\ PA + 8388608 <= alloc_ceiling)
      by (unfold CEIL, PTRARR_RES_SIZE in B2, P2; lia).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof HCEIL as CEIL'. idtac.
    rewrite A_SECONDARY_val in SEC. rewrite A_GSTATS_val in GST.
    assert (HB : (AIMG_HI <= mb /\ (mb + smapsize n <= KLOWSHADOW_BEG \/ KHIGHMEM_BEG <= mb)) /\ mb + smapsize n <= CEIL /\ mb mod 4096 = 0) by (split; [exact (conj B1 B1d)| split; [exact B2| exact B3]]).
    apply bandf_intro in HB.
    assert (HPA : (AIMG_HI <= PA /\ (PA + PTRARR_RES_SIZE <= KLOWSHADOW_BEG \/ KHIGHMEM_BEG <= PA)) /\ PA + PTRARR_RES_SIZE <= CEIL /\ 8 * nsec st <= PTRARR_RES_SIZE) by (split; [exact (conj P1 P1d)| split; [exact P2| exact P3]]).
    apply bandf_intro in HPA.
    assert (NRS : 0 <= st_nreserved st < 2^64 /\ 0 <= idx < nsec st /\ nsec st <= 2^20) by (split; [exact NR| split; [exact HI| exact N20]]).
    pose proof (SH_def mb) as SHd. unfold SHADOW_OFFSET in SHd.
    apply lscps_step_evt.
    destruct (Z_lt_le_dec idx (nsec st - 1)) as [LT|GE].
    - (* [comment removed for export] *)
      (nelim (CASEc LT) 3%nat; intros PLS hl HL24). pose proof (CASEf LT) as CF. cbv zeta in CF. (nelim CF 6%nat; intros F1 F2 F3 F4 F5 F6).
      pose proof (dM_other st mb n WF HP PEND LT) as (ED & _). fold M in ED. rewrite <- ED in PLS, HL24, F1, F2, F3, F4, F5, F6.
      eapply (ld_D0a ra sp gp tp s0e s1e s2e s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m n mb k lo PA (wz PTRARR_RES_SIZE) j1 (st_nreserved st) (nsec st) idx j2
                 (wz (needed n)) b1 b2 b3 j4 jg ltac:(lia) HP ltac:(lia) HB HPA DJ NRS HK E1 HCEIL LO _ M hl);
        [exact LT| clear - F1 F2 F3 F4 F5 S1; unfold S, AIMG_HI, KLOWSHADOW_BEG, KHIGHMEM_BEG in *; lia| exact MI| exact ST| exact SEC| exact MW| exact MJ| exact HDR| exact PIX| exact PLS| exact HL24| exact GST|].
      cbv beta. intros ms1 nelH_; (nelim nelH_ 19%nat; intros y5 y6 y7 y13 y14 y15 y16 y17 y28 y29 y30 y31 m1 -> D0M HDR1 PIX1 PLS1 HL1).
      (nelim D0M 8%nat; intros MU01 WM01 MI1 ST1 FR1 [j2' SEC1] MX1 [jg' GST1]).
      apply evt_done.
      assert (HRD1 : RTREP stD m1).
      { eapply (ld_rep m1 j1 j2' b1 b2 b3 j4 jg'); [exact MU01| exact WM01| rewrite A_SECONDARY_val; exact SEC1| exact MX1| rewrite A_GSTATS_val; exact GST1|].
        intros _. rewrite <- ED. split; [exact PIX1| exact HL1]. }
      eapply (ld_ps m1); [eapply munch_weaken; [| exact MU01]; subfpk ltac:(cut_to B1 S1 NUM NRS)| exact WM01| exact HRD1| exact MI1| exact ST1| exact FR1| exact HDR1
        | eapply stk_wmono_noseg; [exact VS| exact WM01| unfold AIMG_HI; lia]
        | exact (GWIN_mem st m m1 mo _ HG HOK WM01)].
    - (* [comment removed for export] *)
      assert (EM : M = mb) by (unfold M, dM; fold idx; destruct (Z.ltb_spec0 idx (nsec st - 1)); [lia| reflexivity]).
      eapply (ld_D0b ra sp gp tp s0e s1e s2e s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m n mb k lo PA (wz PTRARR_RES_SIZE) j1 (st_nreserved st) (nsec st) idx j2
                 (wz (needed n)) b1 b2 b3 j4 jg ltac:(lia) HP ltac:(lia) HB HPA DJ NRS HK E1 HCEIL LO);
        [lia| exact MI| exact ST| exact SEC| exact MW| exact MJ| exact HDR| exact PIX| exact GST|].
      cbv beta. intros ms1 nelH_; (nelim nelH_ 17%nat; intros y5 y6 y7 y13 y14 y15 y16 y17 y28 y29 y30 y31 m1 -> D0M HDR1 PIX1).
      (nelim D0M 8%nat; intros MU01 WM01 MI1 ST1 FR1 [j2' SEC1] MX1 [jg' GST1]).
      replace (mb + 24, mb + 32) with (M + 24, M + 32) in MU01 by (rewrite EM; reflexivity).
      apply evt_done.
      assert (HRD1 : RTREP stD m1).
      { eapply (ld_rep m1 j1 j2' b1 b2 b3 j4 jg'); [exact MU01| exact WM01| rewrite A_SECONDARY_val; exact SEC1| exact MX1| rewrite A_GSTATS_val; exact GST1|].
        intros LT. exfalso. lia. }
      eapply (ld_ps m1); [eapply munch_weaken; [| exact MU01]; subfpk ltac:(cut_to B1 S1 NUM NRS EM)| exact WM01| exact HRD1| exact MI1| exact ST1| exact FR1| exact HDR1
        | eapply stk_wmono_noseg; [exact VS| exact WM01| unfold AIMG_HI; lia]
        | exact (GWIN_mem st m m1 mo _ HG HOK WM01)].
  Qed.
End LDP.

Theorem large_dealloc_pend_proof : large_dealloc_pend_spec.
Proof.
  unfold large_dealloc_pend_spec. intros until lo. intros RTS0 PEND HP EA -> -> -> TP ST HCEIL LO MI. subst A.
  (nelim RTS0 6%nat; intros HR WF HM HG HFR HSW).
  apply lscps_assume. intros NWX HOK HBINV. destruct g as [G R]. cbn [g_res g_win] in *.
  unfold ALARGE_DEALLOC_STACK in LO.
  eapply (ld_main ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo G R st mb n lo); eassumption.
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac djs := cbn [disjoint_from cells_size Cells.csize fst snd length app]; rewrite ?Nat.add_0_r, ?Z2Nat.id by lia; unfold PTRARR_RES_SIZE, APOISON_STACK, CEIL, KHIGHMEM_BEG, AIMG_HI in *; lia.
End RTW_sec_deallocP.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_poison8.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_poison8.RT_poison_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_poison8.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_poison8.RT_poison3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_cd_stmt RTW_cd_main.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_sec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_sec.RTW_secondary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_sec_gbb.
Import RTW_sec_dealloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_sec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_sec.RTW_q_needs.
Import RTW_sec_deallocP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_p_refill RTW_quarantine_iface2.
Import RTW_q_put.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Theorem quarantine_put_closed : forall ACEIL : Ceil, quarantine_put_spec2.
Proof.
  intros ACEIL. apply quarantine_put_proof;
    [ exact poison_shadow_ok | exact cache_dealloc_proof | exact get_block_begin_proof | exact large_dealloc_proof
    | exact large_dealloc_pend_proof | exact refill_spin_proof ].
Qed.

