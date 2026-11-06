(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2 OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocM8Lkq.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3.AsanPlanSoundSums OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i.BoAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e.BoAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c.BoAllocM8q OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La.BoAllocM8v OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8w OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocM8Lk.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).



Section WithCeil.
Context {RC : run_ceil}.

Section POPKIT.
  Variable bt : as_boot.
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Variables (TP TSDP PGP FL MIDEND : Z).
  Hypothesis CELLS : malloc_cells bt TP TSDP PGP FL MIDEND.
  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation CTX := (bt_tctx bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  Variables (Y : Z -> Prop) (st : ast) (Lc FF : list (Z * Z)) (M M0 : mem) (mdl : Model).
  Variables (qt qg : Z).
  Hypothesis W : WFq bt st Lc FF qt qg.
  Hypothesis RP : Rep bt st Lc FF M0 mdl.
  Hypothesis D : forall a : word, M a <> M0 a -> Y (U a) /\ M a <> None.
  Hypothesis YIMG : forall z, Y z -> AIMGLO <= z < AIMGHI -> IB bt + 888 <= z < IB bt + 920.
  Hypothesis QHDR_CONST : forall z, IB bt + 888 <= z < IB bt + 920 -> ~ consts_cells bt z.

  Lemma pk_IB : IB bt = 0x10ab58.
  Proof using BT_ia. (lazymatch goal with |- ?G => let G' := eval unfold IB in G in change_no_check G' end). rewrite BT_ia. reflexivity. Qed.
  Hypothesis YCTX : forall z, Y z -> ~ (CTX + 152 <= z < CTX + 160).

  Lemma pk_def : forall a : word, M0 a <> None -> M a <> None.
  Proof using D Y.
    intros a H0. destruct (decide (M a = M0 a)) as [E | NE]; [rewrite E; exact H0 | exact (proj2 (D a NE))].
  Qed.

  Lemma pk_const : forall a (n : nat) v, In (a, n, v) (bt_consts bt) -> AIMGLO <= a -> a + Z.of_nat n <= AIMGHI ->
    rdn BSEGS M (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v)).
  Proof using QHDR_CONST YIMG D RP mdl M0 FF Lc st Y BT_segs RC.
    intros a n v Hin A0 A1. pose proof RP as (R1 & _). rewrite BT_segs in R1.
    apply (repx_rd Y M M0 D a n); [lia | lia | intros i Hi; intros HY; apply (QHDR_CONST i (YIMG i HY ltac:(lia))); exists (a, n, v); split; [exact Hin | (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end); lia] | exact (const_cell bt M0 _ _ _ R1 Hin)].
  Qed.

  Lemma pk_shadow_def : forall z, shmaps z -> M (Z_to_bv 64 z) <> None.
  Proof using D RP mdl M0 FF Lc st Y bt RC.
    intros z Hz. apply pk_def. pose proof RP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R15).
    destruct R15 as (_ & _ & _ & _ & SHD). first [exact (SHD z Hz) | exact (proj1 SHD z Hz)].   (* [comment removed for export] *)
  Qed.

  Lemma pk_thread_geom : 0 < T /\ T + 4096 <= CEIL /\ 0 < CTX /\ CTX + 0x10000 <= CEIL /\ T mod 4096 = 0
    /\ (T + 4096 <= AIMGLO \/ AIMGHI <= T) /\ (CTX + 0x10000 <= AIMGLO \/ AIMGHI <= CTX).
  Proof using W qg qt FF Lc st BT_ia.
    pose proof (fixed_facts bt st Lc FF W) as (T1 & T2 & C1 & C2 & _).
    pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & WM & _).
    destruct WM as (RNG & _ & _ & _ & _ & _ & _ & INT & _ & _ & INC & _).
    destruct (RNG _ _ (all_ranges_fixed bt st _ INT)) as ((D1 & D2 & D3 & D4 & D5) & _ & D6 & _).
    destruct (RNG _ _ (all_ranges_fixed bt st _ INC)) as ((E1 & E2 & E3 & E4 & E5) & _).
    rewrite BT_ia in D4, E4. cbn [ia_img_lo ia_img_hi both_addrs] in D4, E4. unfold PG in *.
    repeat split; try assumption; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma pk_T_writable : writableZ BSEGS M T (T + 4096).
  Proof using D RP W qg qt mdl M0 FF Lc st Y BT_ia BT_segs RC.
    pose proof pk_thread_geom as (T1 & T2 & _). pose proof ceil_rng as CR.
    pose proof RP as (_ & _ & R3 & _). destruct R3 as (_ & _ & _ & _ & _ & _ & _ & _ & TW & _). rewrite BT_segs in TW. unfold PG in TW.
    apply (repx_wr Y M M0 D); [lia | lia | exact TW].
  Qed.

  (* [comment removed for export] *)
  Lemma pk_junk8 : forall lo hi z, writableZ BSEGS M lo hi -> lo <= z -> z + 8 <= hi -> 0 <= z -> hi < 2 ^ 64 ->
    exists v : word, rdn BSEGS M (Z_to_bv 64 z) 8 = Some (LE8 v).
  Proof using.
    intros lo hi z WR L H Z0 H1.
    destruct (rdn_defined_ex BSEGS M (Z_to_bv 64 z) 8) as (bs & Cbs & Lbs).
    { intros i Hi. rewrite u_Z2bv in Hi by lia. cbn in Hi. exact (proj1 (WR i ltac:(lia))). }
    { rewrite u_Z2bv by lia. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. }
    exists (Z_to_bv 64 (bytes_le_to_Z bs)). rewrite Cbs. f_equal. symmetry. apply APSX.word_to_le_bytes_of_bytes_n; [exact Lbs | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma pk_poisonH : forall (slot : Z) (ra fsp : word),
    AS_HEAPLO <= slot -> slot + 2 ^ 18 <= CEIL -> slot mod 8 = 0 ->
    CEIL + 64 <= U fsp -> U fsp + 16 <= 2 ^ 47 -> writableZ BSEGS M (U fsp - 64) (U fsp) -> ret_ok ra ->
    poisonH BSEGS both_poison_tab M (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 250) ra fsp (Z_to_bv 8 1) (Z_to_bv 64 MIDEND) 0.
  Proof using QHDR_CONST YIMG D RP mdl M0 FF Lc st Y CELLS FL PGP TSDP TP BT_ia BT_segs bt.
    intros slot ra fsp S0 S1 S8 F0 F1 WST Hret. pose proof ceil_rng as CR. pose proof (u64_range fsp) as Hf.
    destruct CELLS as (CELL_mcs & CELL_gcf & CELL_fum & CELL_inited & CELL_pg & CELL_P & CELL_kif & CELL_key & CELL_tsdp & CELL_tctx
                      & CELL_rss & CELL_lmag & CELL_tbl2 & CELL_t16 & CELL_t2048 & CELL_minrz & CELL_maxrz & CELL_maxsz & CELL_sbeg
                      & CELL_cpm & CELL_gsh & CELL_gmb & CELL_mb & CELL_gme & CELL_me & CELL_ghe & CELL_he & CELL_gfl & CELL_pp & CELL_mfs & CELL_fill
                      & CELL_grm & CELL_rm & CELL_glsn & CELL_lsn & CELL_magic & CELL_hook & CELL_thr64 & G_consts).
    assert (CSB : rdn BSEGS M (Z_to_bv 64 0x10e1b8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7fff8000))).
    { pose proof RP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R15). destruct R15 as (_ & _ & Csb & _).
      rewrite BT_ia, BT_segs in Csb. cbn [ia_rtc_sb both_addrs] in Csb. unfold SB in Csb.
      apply (repx_rd Y M M0 D 0x10e1b8 8); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; intros HY; cbn in Hi; pose proof (YIMG i HY ltac:(lia)) as YQ; rewrite pk_IB in YQ; lia | exact Csb]. }
    unfold AS_HEAPLO in S0.
    split; (lazymatch goal with |- ?G => let G' := eval cbn [pt_base pt_mset pt_g_shoff pt_p_shoff pt_g_midbeg pt_p_midbeg pt_g_midend pt_p_midend pt_g_hiend pt_p_hiend pt_g_rms pt_p_rms pt_g_cfl pt_p_cfl pt_c_cpm both_poison_tab] in G in change_no_check G' end).
    - exact (pk_const _ _ _ CELL_gsh ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - exact CSB.
    - exact (pk_const _ _ _ CELL_gmb ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - exact (pk_const _ _ _ CELL_mb ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - exact (pk_const _ _ _ CELL_gme ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - exact (pk_const _ _ _ CELL_me ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - exact (pk_const _ _ _ CELL_ghe ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - exact (pk_const _ _ _ CELL_he ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - exact (pk_const _ _ _ CELL_grm ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - replace (word_to_le_bytes 8 (1033100 : word)) with (LE8 (Z_to_bv 64 0xfc38c)) by reflexivity.
      exact (pk_const _ _ _ CELL_rm ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - vm_compute. discriminate.
    - apply ret_ok_even. reflexivity.
    - intros _. split; [| vm_compute; discriminate]. rewrite <- (w2b1 1) by lia. exact (pk_const _ _ _ CELL_cpm ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - intros E0. exfalso. rewrite u_Z2bv in E0 by lia. lia.
    - (lazymatch goal with |- ?G => let G' := eval unfold poison_cells in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [pt_g_shoff pt_p_shoff pt_g_midbeg pt_p_midbeg pt_g_midend pt_p_midend pt_g_hiend pt_p_hiend pt_g_rms pt_p_rms pt_g_cfl pt_p_cfl pt_c_cpm both_poison_tab] in G in change_no_check G' end).
      repeat (constructor; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]). constructor.
    - rewrite u_Z2bv by lia. exact S8.
    - rewrite u_Z2bv by lia. reflexivity.
    - left. rewrite !u_Z2bv by lia. lia.
    - lia.
    - apply (writableZ_sok M (U fsp - 64) (U fsp)); [exact WST | rewrite at_u by lia; lia | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia].
    - (lazymatch goal with |- ?G => let G' := eval unfold shad, shlen in G in change_no_check G' end). rewrite !u_Z2bv by lia.
      assert (Q : 0x10007fff8000 / 8 <= slot / 8 /\ slot / 8 + 2 ^ 15 <= CEIL / 8).
      { split; [apply Z.div_le_mono; lia|]. replace (slot / 8 + 2 ^ 15) with ((slot + 2 ^ 18) / 8) by (rewrite <- (Z.div_add slot (2 ^ 15) 8) by lia; f_equal).
        apply Z.div_le_mono; lia. }
      assert (Q2 : CEIL / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia).
      assert (E1 : 0x10007fff8000 / 8 = 2199291686912) by reflexivity. assert (E2 : 0x7fffff800000 / 8 = 17592184995840) by reflexivity.
      rewrite E1 in Q. rewrite E2 in Q2.
      apply store_ok_of_all; [rewrite u_Z2bv by lia; change (2 ^ 18 / 8) with (2 ^ 15); rewrite Z2Nat.id by lia; lia|].
      intros x Hx. rewrite u_Z2bv in Hx by lia. change (2 ^ 18 / 8) with (2 ^ 15) in Hx. rewrite Z2Nat.id in Hx by lia.
      assert (DEF : M x <> None).
      { rewrite <- (Z_to_bv_bv_unsigned _ x). apply pk_shadow_def. (lazymatch goal with |- ?G => let G' := eval unfold shmaps, AS_GAPHI, AS_HEAPLO, AS_LO, AS_GAPLO in G in change_no_check G' end). right. lia. }
      (lazymatch goal with |- ?G => let G' := eval unfold wview in G in change_no_check G' end). destruct (M x); [discriminate | exfalso; exact (DEF eq_refl)].
    - exact Hret.
  Qed.

  (* [comment removed for export] *)
  Lemma pk_gctH : forall (gsp tp : word), U tp = TP -> CEIL + 16 <= U gsp -> U gsp + 8 <= 2 ^ 47 -> writableZ BSEGS M (U gsp - 8) (U gsp) ->
    gctH BSEGS both_gct_tab M gsp tp (Z_to_bv 64 TSDP) (Z_to_bv 64 CTX) (Z_to_bv 64 T).
  Proof using YCTX QHDR_CONST YIMG D RP W qg qt mdl M0 FF Lc st Y CELLS MIDEND FL PGP BT_ia BT_segs.
    intros gsp tp Etp G0 G1 WST. pose proof ceil_rng as CR. pose proof (u64_range gsp) as Hg. pose proof (u64_range tp) as Htp.
    pose proof pk_thread_geom as (T1 & T2 & C1 & C2 & _).
    destruct CELLS as (CELL_mcs & CELL_gcf & CELL_fum & CELL_inited & CELL_pg & CELL_P & CELL_kif & CELL_key & CELL_tsdp & CELL_tctx & CREST).
    assert (G_consts : 0x10000 <= TSDP /\ TSDP + 8 <= 0x663000 /\ 0x10000 + 88 <= TP /\ TP + 0x40 <= 0x663000).
    { do 28 (destruct CREST as (_ & CREST)). destruct CREST as (A1 & A2 & _ & _ & _ & _ & _ & A8 & A9). repeat split; assumption. }
    destruct G_consts as (Gc1 & Gc2 & Gc8 & Gc9).
    pose proof RP as (_ & _ & R3 & _). destruct R3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Tback & _). rewrite BT_segs in Tback.
    split; (lazymatch goal with |- ?G => let G' := eval cbn [gt_tsd both_gct_tab] in G in change_no_check G' end).
    - rewrite <- (w2b1 1) by lia. exact (pk_const _ _ _ CELL_kif ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - replace (at_ (Z_to_bv 64 0x10da20) 4) with (Z_to_bv 64 0x10da24 : word) by (apply bv_eq; reflexivity).
      exact (pk_const _ _ _ CELL_key ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - replace (at_ tp (-88)) with (Z_to_bv 64 (TP - 88)) by (apply bv_eq; rewrite at_u by lia; rewrite u_Z2bv by lia; lia).
      exact (pk_const _ _ _ CELL_tsdp ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - exact (pk_const _ _ _ CELL_tctx ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - replace (at_ (Z_to_bv 64 CTX) 152) with (Z_to_bv 64 (CTX + 152)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); rewrite (u_Z2bv CTX) by lia; reflexivity).
      apply (repx_rd Y M M0 D (CTX + 152) 8); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; intros HY; exact (YCTX i HY ltac:(cbn in Hi; lia)) | exact Tback].
    - rewrite u_Z2bv by lia. lia.
    - apply (writableZ_sok M (U gsp - 8) (U gsp)); [exact WST | rewrite at_u by lia; lia | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia].
    - lia.
    - rewrite u_Z2bv by lia. lia.
    - lia.
    - rewrite u_Z2bv by lia. lia.
    - rewrite u_Z2bv by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma pk_thread_geom2 :
    (T + 4096 <= AS_LO \/ AS_HEAPLO <= T) /\ (CTX + 0x10000 <= AS_LO \/ AS_HEAPLO <= CTX)
    /\ (T + 4096 <= SBEG \/ SBEG + KSPACE + 4096 <= T) /\ (CTX + 0x10000 <= SBEG \/ SBEG + KSPACE + 4096 <= CTX)
    /\ 0 < SBEG /\ SBEG + KSPACE + 4096 <= CEIL /\ AS_HEAPLO <= SBEG.
  Proof using W qg qt FF Lc st.
    pose proof (fixed_facts bt st Lc FF W) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & S3).
    destruct (space_facts bt st Lc FF W) as ((SP1 & SP2 & SP3 & _ & _) & SP6 & SP7 & SP8 & SPH).
    pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & WM & _).
    destruct WM as (RNG & _ & _ & _ & _ & _ & _ & INT & _ & _ & INC & _).
    destruct (RNG _ _ (all_ranges_fixed bt st _ INT)) as ((D1 & D2 & D3 & D4 & D5) & _ & D6 & _).
    destruct (RNG _ _ (all_ranges_fixed bt st _ INC)) as ((E1 & E2 & E3 & E4 & E5) & _).
    pose proof (space_vs_fixed bt st Lc FF W _ _ INT ltac:((lazymatch goal with |- ?G => let G' := eval unfold KSPACE, PG in G in change_no_check G' end); lia)) as TS.
    pose proof (space_vs_fixed bt st Lc FF W _ _ INC ltac:((lazymatch goal with |- ?G => let G' := eval unfold KSPACE in G in change_no_check G' end); lia)) as CS.
    unfold PG in *. repeat split; try assumption; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma pk_nolazy_rt : forall z, (T <= z < T + 4096) \/ (CTX <= z < CTX + 0x10000) -> lzb mdl z = false.
  Proof using RP W qg qt M0 FF Lc st RC.
    intros z Hz. apply (OBL_nolazy_rt_pf bt st Lc FF W M0 mdl z RP). (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). tauto.
  Qed.
End POPKIT.
Section QCEIL.
  Variable bt : as_boot.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  (* [comment removed for export] *)
  Lemma rep_cells_lt_ceil_q : forall st Lc FF a qt qg, WFq bt st Lc FF qt qg -> rep_cells bt st Lc FF a -> a < CEIL.
  Proof using BT_ia.
    intros st Lc FF a qt qg W RCa. pose proof ceil_rng as CR. pose proof (img_lits bt st Lc FF W) as [I1 I2].
    destruct (rep_cells_zone bt st Lc FF W a RCa) as [K | [K | K]].
    - destruct K as [K _]. rewrite BT_ia in K. cbn [ia_img_lo ia_img_hi both_addrs] in K. lia.
    - exact (proj1 (proj2 (dyn_kind_facts bt st Lc FF W a K))).
    - destruct K as [K _]. unfold SB in K. assert (CEIL / 8 <= CEIL / 2) by (apply Z.div_le_compat_l; lia).
      assert (2 * (CEIL / 2) <= CEIL) by (apply Z.mul_div_le; lia). lia.
  Qed.
  (* [comment removed for export] *)
  Lemma repx_frame_step_q : forall (Y : Z -> Prop) st Lc FF (M M' : mem) mdl mdl' qt qg,
    WFq bt st Lc FF qt qg -> RepX bt Y st Lc FF M mdl ->
    (forall a : word, M' a <> M a -> ~ rep_cells bt st Lc FF (U a) /\ M' a <> None) ->
    MInv (a_aa st) mdl' -> same_but_materialized mdl mdl' ->
    RepX bt Y st Lc FF M' mdl'.
  Proof using.
    intros Y st Lc FF M M' mdl mdl' qt qg W RX CH MI SBM.
    apply (AsAinvOpsRc73.AsAinvRepX3.RepX_mono bt (fun z => Y z /\ ~ False) Y); [intros z [Hz _]; exact Hz|].
    apply (repx_step bt Y (fun _ => False) (fun z => ~ rep_cells bt st Lc FF z) Xdec_false st st Lc Lc FF FF M M' mdl mdl' RX CH ltac:(intros a F; destruct F)).
    intros N0 N0' RPn Dn DIFF _ _.
    apply (Rep_sbm bt st Lc FF N0' mdl mdl'); [| exact MI | exact SBM].
    apply (Rep_frame_q bt st Lc FF N0 N0' mdl W RPn). intros a Ha. destruct (DIFF a Ha) as [[F | []] Dd]. exact (conj F Dd).
  Qed.
End QCEIL.
End WithCeil.
End BoAllocM8Lkq.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsanNodesLibE.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require AsKSys7b.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleU3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleU3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMQRepF OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMQRepH. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i.BoAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e.BoAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c.BoAllocM8q OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8r OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u.BoAllocM8t OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La.BoAllocM8v OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8w OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8x OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8y OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocM8z OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocM8pa OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocM8Lk BoAllocM8Lkq OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMQRepF OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMQRepH.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2. Import OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8yq.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac am_inner ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
#[local] Ltac lia ::= am_lia.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma mod4096_sum : forall x y, x mod 4096 = 0 -> y mod 4096 = 0 -> (x + y) mod 4096 = 0.
Proof. intros x y Hx Hy. lia. Qed.
Lemma pos_mod4096 : forall t, 0 < t -> t mod 4096 = 0 -> 4096 <= t /\ t mod 8 = 0.
Proof. intros t H0 Ht. lia. Qed.
Lemma mod8_of_4096_sum : forall x y, x mod 4096 = 0 -> y mod 4096 = 0 -> (x + y) mod 8 = 0.
Proof. intros x y Hx Hy. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section WithCeil.
Context {RC : run_ceil}.
Context {fx : FPState}.

Section L3.
  Variable bt : as_boot.
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Variables (TP TSDP PGP FL MIDEND : Z).
  Hypothesis CELLS : malloc_cells bt TP TSDP PGP FL MIDEND.
  Hypothesis PCELLS : pop_cells bt.
  Variable X : Z -> Prop.
  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation CTX := (bt_tctx bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation XL := (XL bt X).
  #[local] Abbreviation IA := (bt_ia bt).

  (* [comment removed for export] *)
  Definition famap_ledger (st : ast) (c : Z) (mdl mdl' : Model) : Prop :=
    let lo := fa_beg SBEG c + r_mapped_fa (a_reg st c) in
    (r_fhole (a_reg st c) = false -> vm_maps (m_vmmaps mdl') = vm_maps (m_vmmaps mdl))
    /\ (r_fhole (a_reg st c) = true -> Permutation (vm_maps (m_vmmaps mdl')) ((Z_to_bv 64 lo, Z_to_bv 64 KFAMAP) :: vm_maps (m_vmmaps mdl)))
    /\ (forall a, in_ivz (vm_noaccess (m_vmmaps mdl')) a <-> in_ivz (vm_noaccess (m_vmmaps mdl)) a /\ ~ (lo <= a < lo + KFAMAP))
    /\ Forall (fun e : word * word => 0 < bv_unsigned (snd e)) (vm_noaccess (m_vmmaps mdl'))
    /\ (forall a, pg_in_ivz (m_vm_lazy mdl') a <-> pg_in_ivz (m_vm_lazy mdl) a /\ ~ (lo <= a < lo + KFAMAP))
    /\ Forall (fun iv : word * word => bv_unsigned (fst iv) mod PG = 0 /\ bv_unsigned (snd iv) mod PG = 0 /\ 0 < bv_unsigned (fst iv)
                                   /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= CEIL
                                   /\ (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= ia_img_lo IA \/ ia_img_hi IA <= bv_unsigned (fst iv)))
              (m_vm_lazy mdl')
    /\ vm_reserved (m_vmmaps mdl') = vm_reserved (m_vmmaps mdl) /\ vm_brk (m_vmmaps mdl') = vm_brk (m_vmmaps mdl)
    /\ vm_start_brk (m_vmmaps mdl') = vm_start_brk (m_vmmaps mdl) /\ vm_mmap_base (m_vmmaps mdl') = vm_mmap_base (m_vmmaps mdl)
    /\ vm_init_sp (m_vmmaps mdl') = vm_init_sp (m_vmmaps mdl) /\ vm_limit (m_vmmaps mdl') = vm_limit (m_vmmaps mdl)
    /\ eager_used mdl' <= eager_used mdl + KFAMAP.

  (* [comment removed for export] *)
  Definition N3Fq_stmt : Prop := forall st Lc FF M0 mdl c qt qg,
    WFq bt st Lc FF qt qg -> AsKSys7b.qroom Lc qt qg -> Rep bt st Lc FF M0 mdl -> 1 <= c <= 30 -> r_fhole (a_reg st c) = false ->
    r_mapped_fa (a_reg st c) + KFAMAP <= 2 ^ 29 -> BackingAlgebra.model_ivs_wf mdl -> m_halted mdl = None -> a_kact st <= KCAP ->
    let lo := fa_beg SBEG c + r_mapped_fa (a_reg st c) in
    let addr : word := Z_to_bv 64 lo in let size : word := Z_to_bv 64 KFAMAP in
    let A2 := a_aa st ++ [(sh_lo lo, sh_lo lo + KFAMAP / 8)] in
    let OK := fixedin_ok_model 3 (Z_to_bv 64 50) addr size in let DS := fixedin_destroyed_model addr size in
    A_wf A2
    /\ (forall mdlm, same_but_materialized mdl mdlm -> MInv (a_aa st) mdlm ->
          U addr + U size <= alloc_top (m_vmmaps mdlm) /\ alloc_top (m_vmmaps mdlm) < two_pow_64
          /\ region_free (vm_reserved (m_vmmaps mdlm)) addr size = true /\ map_contains (vm_maps (m_vmmaps mdlm)) addr size = true
          /\ mmap_fixed_rw_budget_ok (Z_to_bv 64 50) mdlm addr size = true
          /\ m_halted (OK mdlm) = None /\ MInv (a_aa st) (OK mdlm)
          /\ (forall p, page_in_ranges p (m_vm_lazy (OK mdlm)) = true -> page_in_ranges p (m_vm_lazy mdl) = true)
          /\ m_halted (DS mdlm) = None /\ MInv (a_aa st) (DS mdlm)
          /\ (forall p, page_in_ranges p (m_vm_lazy (DS mdlm)) = true -> page_in_ranges p (m_vm_lazy mdl) = true))
    /\ (forall mdlm mdl4, same_but_materialized mdl mdlm -> same_but_materialized (OK mdlm) mdl4 -> MInv (a_aa st) mdl4 -> MInv A2 mdl4)
    /\ (forall mdlm mdl', same_but_materialized mdl mdlm -> same_but_materialized (OK mdlm) mdl' ->
          famap_ledger st c mdl mdl' /\ same_except_vm mdl mdl' /\ lazy_kept IA Lc FF mdl mdl' /\ BackingAlgebra.model_ivs_wf mdl' /\ m_halted mdl' = None)
    /\ (forall mdlm mdl', same_but_materialized mdl mdlm -> same_but_materialized (DS mdlm) mdl' ->
          ledger_destroyed bt mdl mdl' lo KFAMAP /\ eager_used mdl' <= eager_used mdl
          /\ same_except_vm mdl mdl' /\ lazy_kept IA Lc FF mdl mdl' /\ BackingAlgebra.model_ivs_wf mdl' /\ m_halted mdl' = None).
  Hypothesis N3F : N3Fq_stmt.
  Hypothesis QHDR_CONST : forall z, IB bt + 888 <= z < IB bt + 920 -> ~ consts_cells bt z.
  Context {qt qg : Z}.

  (* [comment removed for export] *)
  Lemma WFq_meter0 : forall st Lc FF naa, WFq bt st Lc FF qt qg -> WFq bt (add_meter st 0 naa 0) Lc FF qt qg.
  Proof using.
    intros st Lc FF naa W. exact (WFq_meter bt st Lc FF 0 naa 0 qt qg W (Z.le_refl 0) eq_refl).
  Qed.


  (* [comment removed for export] *)
  Lemma writableZ_of_def : forall (M : mem) lo hi, 0 <= lo -> hi < 2 ^ 64 -> (forall i, lo <= i < hi -> M (Z_to_bv 64 i) <> None) -> writableZ BSEGS M lo hi.
  Proof using.
    intros M lo hi L0 H1 DEF i Hi. split; [exact (DEF i Hi)|]. apply store_ok_of_all; [rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|].
    intros x Hx. rewrite u_Z2bv in Hx by lia. cbn in Hx. assert (x = Z_to_bv 64 i) as -> by (apply bv_eq; rewrite u_Z2bv by lia; lia).
    (lazymatch goal with |- ?G => let G' := eval unfold wview in G in change_no_check G' end). pose proof (DEF i Hi) as Dd. destruct (M (Z_to_bv 64 i)); [discriminate | exfalso; exact (Dd eq_refl)].
  Qed.
  Lemma lazy_kept_sbm : forall Lc FF mdl mdl', same_but_materialized mdl mdl' -> lazy_kept IA Lc FF mdl mdl'.
  Proof using.
    intros Lc FF mdl mdl' S a _. pose proof (same_but_materialized_frame mdl mdl' S) as (_ & _ & E & _). (lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end). rewrite E. reflexivity.
  Qed.
  Lemma halted_sbm : forall mdl mdl', same_but_materialized mdl mdl' -> m_halted mdl = None -> m_halted mdl' = None.
  Proof using. intros mdl mdl' S H. pose proof (same_but_materialized_frame mdl mdl' S) as (_&_&_&_&_&_&_&_&_&_&_&_&Hh&_). rewrite Hh. exact H. Qed.

  Theorem popBf_katwD_q :
    forall (c : Z) st Lc FF (M : mem) (rom : mem) mdl (regs : bvmap 5 word) (sp ra s0v s1v s2v s3v s4v s5v tp gp : word) (tot : Z) (Qok Qf : config -> Prop),
    1 <= c <= 30 -> WFq bt st Lc FF qt qg -> AsKSys7b.qroom Lc qt qg -> RepX bt (XL c) st Lc FF M mdl -> m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
    r_fhole (a_reg st c) = false -> r_mapped_fa (a_reg st c) + KFAMAP <= 2 ^ 29 ->
    r_mapped_fa (a_reg st c) <= 4 * (r_mapped_user (a_reg st c) / csize c) -> a_kact st <= KCAP ->       (* [comment removed for export] *)
    let r := a_reg st c in let mfa := r_mapped_fa r in let lo := fa_beg SBEG c + mfa in
    (forall z, X z -> ~ (reginfo bt c <= z < reginfo bt c + 128) /\ (AIMGLO <= z < AIMGHI -> IB bt + 888 <= z < IB bt + 920) /\ ~ (CTX + 152 <= z < CTX + 160)
                      /\ ~ (lo <= z < lo + KFAMAP) /\ ~ (sh_lo lo <= z < sh_lo lo + KFAMAP / 8)) ->
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 4 = tp -> getr regs 3 = gp -> U tp = TP -> getr regs 10 = Z_to_bv 64 0x10ab58 ->
    getr regs 11 = Z_to_bv 64 (reginfo bt c) -> getr regs 12 = Z_to_bv 64 (region_beg SBEG c) -> getr regs 13 = Z_to_bv 64 tot ->
    getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v -> getr regs 19 = s3v -> getr regs 20 = s4v -> getr regs 21 = s5v ->
    (CEIL + 448 <= U sp /\ U sp + 16 <= 2 ^ 47) -> ret_ok ra -> (0 <= tot /\ 4 * tot <= 2 ^ 29) -> (mfa < 4 * tot <= mfa + 2 ^ 18) ->
    writableZ BSEGS M (U sp - 448) (U sp) ->
    (* [comment removed for export] *)
    (forall (r' : bvmap 5 word) (M' : mem) mdl',
        let st' := add_meter (op_famap st c) 0 [(sh_lo lo, sh_lo lo + KFAMAP / 8)] 0 in
        WFq bt st' Lc FF qt qg -> RepX bt (XL c) st' Lc FF M' mdl' ->
        same_except_vm mdl mdl' -> lazy_kept IA Lc FF mdl mdl' -> BackingAlgebra.model_ivs_wf mdl' -> m_halted mdl' = None ->
        (forall a : word, M' a <> M a ->
            ((U sp - 448 <= U a < U sp) \/ (lo <= U a < lo + KFAMAP) \/ (sh_lo lo <= U a < sh_lo lo + KFAMAP / 8)
             \/ (T + 2872 <= U a < T + 2888) \/ (reginfo bt c + 24 <= U a < reginfo bt c + 32)) /\ M' a <> None) ->
        getr r' 10 = Z_to_bv 64 1 -> getr r' 2 = sp -> getr r' 1 = ra ->
        getr r' 8 = s0v -> getr r' 9 = s1v -> getr r' 18 = s2v -> getr r' 19 = s3v -> getr r' 20 = s4v -> getr r' 21 = s5v -> getr r' 4 = tp -> getr r' 3 = gp ->
        getr r' 22 = getr regs 22 -> getr r' 23 = getr regs 23 -> getr r' 24 = getr regs 24 -> getr r' 25 = getr regs 25 ->
        katwD BSEGS (mkCfg (mkst r' ra M' rom) mdl') Qok Qf) ->
    (* [comment removed for export] *)
    (forall (r0 r' : bvmap 5 word) (M' : mem) mdl' st',
        (st' = st \/ st' = op_fhole st c) ->
        WFq bt st' Lc FF qt qg -> RepX bt (XL c) st' Lc FF M' mdl' ->
        same_except_vm mdl mdl' -> lazy_kept IA Lc FF mdl mdl' -> BackingAlgebra.model_ivs_wf mdl' -> m_halted mdl' = None ->
        (forall a : word, M' a <> M a -> ((U sp - 448 <= U a < U sp) /\ M' a <> None) \/ (lo <= U a < lo + KFAMAP)) ->
        regs_agree (fun i : reg => In i efs_clob) regs r0 -> efs_post sp ra s0v s1v s2v s3v 0 r0 r' ->
        katD BSEGS (mkCfg (mkst r' ra M' rom) mdl') Qf) ->
    katwD BSEGS (mkCfg (mkst regs (0x4f508%bv : word) M rom) mdl) Qok Qf.
  Proof using QHDR_CONST N3F PCELLS CELLS MIDEND FL PGP TSDP BT_ia BT_segs.
    intros c st Lc FF M rom mdl regs sp ra s0v s1v s2v s3v s4v s5v tp gp tot Qok Qf Hc W QR RX HALT MW FH ROOM FAQ KC r mfa lo XOFF
           H1 H2 H4 H3 Etp H10 H11 H12 H13 H8 H9 H18 H19 H20 H21 Hsp Hret Htot Hneed WSTK CONT1 CONT0.
    pose proof ceil_rng as CR. destruct Hsp as [SP1 SP2]. pose proof (u64_range sp) as Hspr.
    pose proof RX as (M0 & RP & D).
    pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. fold r in RF.
    destruct RF as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14). fold mfa in E6, E7, E14.
    pose proof W as ((WR1 & _) & _). destruct (WR1 c Hc) as (_ & _ & _ & _ & Y5 & Y6 & _). fold r mfa in Y5, Y6.
    pose proof CELLS as (CELL_mcs & CELL_gcf & CELL_fum & CELL_inited & CELL_pg & CELL_P & CREST).
    assert (G_consts : 0x10000 <= TSDP /\ TSDP + 8 <= 0x663000 /\ 0x10000 <= PGP /\ PGP + 8 <= 0x663000 /\ 0x10000 + 88 <= TP /\ TP + 0x40 <= 0x663000).
    { do 32 (destruct CREST as (_ & CREST)). destruct CREST as (A1 & A2 & A3 & A4 & _ & _ & _ & A8 & A9). repeat split; assumption. }
    destruct G_consts as (Gs1 & Gs2 & Gp1 & Gp2 & Gt1 & Gt2).
    pose proof PCELLS as (PC_rel & PC_rib & PC_pre & PC_dpm & PC_lim).
    set (RIz := reginfo bt c) in *. set (rbeg := region_beg SBEG c) in *.
    assert (ERI : RIz = SBEG + KSPACE + 128 * c) by reflexivity.
    assert (ERB : rbeg = SBEG + c * 2 ^ 32) by ((lazymatch goal with |- ?G => let G' := eval unfold rbeg, region_beg, KREGION in G in change_no_check G' end); reflexivity).
    assert (ELO : lo = rbeg + 0xE0000000 + mfa) by ((lazymatch goal with |- ?G => let G' := eval unfold lo, fa_beg, KFAOFF in G in change_no_check G' end); fold rbeg; reflexivity).
    assert (ESH : sh_lo lo = (rbeg + 0xE0000000 + mfa) / 8 + 0x7fff8000) by (rewrite ELO; (lazymatch goal with |- ?G => let G' := eval unfold sh_lo, SB in G in change_no_check G' end); lia).
    (* [comment removed for export] *)
    pose proof RP as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15).
    destruct (R4 c Hc) as [(G0 & G8 & G16 & G24 & G32 & G40 & G48 & G56 & G68 & GW) (F1 & F2 & F3)]. fold r RIz mfa in G24, GW.
    rewrite BT_segs in *. destruct R14 as (Bw1 & Bw2 & _).
    (* [comment removed for export] *)
    pose proof (pk_thread_geom bt BT_ia st Lc FF qt qg W) as (T1 & T2 & C1 & C2 & T4k & TIMG & CIMG).
    pose proof (pk_thread_geom2 bt st Lc FF qt qg W) as (TBAND & CBAND & TSP & CSP & S1 & S2 & S3).
    unfold KSPACE, PG, KFAMAP, KFAOFF, AS_HEAPLO, AS_LO in *.
    assert (SLOT : SBEG <= lo /\ lo + 2 ^ 18 <= SBEG + 2 ^ 37 /\ lo mod 8 = 0).
    { split; [rewrite ELO, ERB; lia|]. split; [rewrite ELO; fold rbeg in E5; unfold fa_beg in E5; lia|].
      (lazymatch goal with |- ?G => let G' := eval unfold lo in G in change_no_check G' end). apply mod8_of_4096_sum; [exact E12 | exact E14]. }
    destruct SLOT as (SL0 & SL1 & SL8).
    assert (SLa : 17594333495296 <= lo) by lia.
    assert (SLb : lo + 2 ^ 18 <= CEIL) by lia.
    destruct (sh_band lo (2 ^ 18) SLa ltac:(lia) SLb ltac:(reflexivity)) as (SHB0 & SHB1 & SHB2).
    unfold AS_GAPHI, AS_HEAPLO in SHB0, SHB1. replace (2 ^ 18 / 8) with (2 ^ 15) in SHB1, SHB2 by reflexivity.
    set (SH := sh_lo lo) in *. assert (ESH' : SH = SB + lo / 8) by reflexivity. rewrite <- ESH' in SHB0, SHB1, SHB2.
    (* [comment removed for export] *)
    assert (YIMG : forall z, XL c z -> AIMGLO <= z < AIMGHI -> IB bt + 888 <= z < IB bt + 920).
    { intros z [Hx | Hl] Hz; [exact (proj1 (proj2 (XOFF z Hx)) Hz) | exfalso; fold RIz in Hl; lia]. }
    assert (YCTX : forall z, XL c z -> ~ (CTX + 152 <= z < CTX + 160)).
    { intros z [Hx | Hl]; [exact (proj1 (proj2 (proj2 (XOFF z Hx)))) | fold RIz in Hl; clear - Hl CSP ERI E9 E10 C1; lia]. }
    assert (XRI : forall i, RIz + 8 <= i < RIz + 128 -> ~ XL c i).
    { intros i Hi [Hx | Hl]; [exact (proj1 (XOFF i Hx) ltac:(fold RIz; lia)) | fold RIz in Hl; lia]. }
    assert (XSL : forall i, lo <= i < lo + 2 ^ 18 -> ~ XL c i).
    { intros i Hi [Hx | Hl]; [exact (proj1 (proj2 (proj2 (proj2 (XOFF i Hx)))) Hi) | fold RIz in Hl; lia]. }
    assert (XSH : forall i, SH <= i < SH + 2 ^ 15 -> ~ XL c i).
    { intros i Hi [Hx | Hl]; [apply (proj2 (proj2 (proj2 (proj2 (XOFF i Hx))))); fold SH; replace (2 ^ 18 / 8) with (2 ^ 15) by reflexivity; exact Hi | fold RIz in Hl; lia]. }
    (* [comment removed for export] *)
    destruct (N3F st Lc FF M0 mdl c qt qg W QR RP Hc FH ROOM MW HALT KC) as (AWF2 & NODEF & BUD & LEDOK & LEDDS).
    fold r mfa lo SH in AWF2, NODEF, BUD, LEDOK, LEDDS. unfold KFAMAP in AWF2, NODEF, BUD, LEDOK, LEDDS.
    set (addr := Z_to_bv 64 lo : word) in *. set (size := Z_to_bv 64 (2 ^ 18) : word) in *.
    set (A2 := a_aa st ++ [(SH, SH + 2 ^ 18 / 8)]) in *.
    set (OKm := fixedin_ok_model 3 (Z_to_bv 64 50) addr size) in *. set (DSm := fixedin_destroyed_model addr size) in *.
    (* [comment removed for export] *)
    set (Hd := HID st mdl). set (Hd2 := mkH (m_vm_lazy mdl) A2).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ AIMGLO <= z < AIMGHI) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st mdl z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). clear - Hr. lia. }
    assert (NHri : forall z, RIz <= z < RIz + 128 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply (rep_nolazy_reginfo bt st Lc FF M0 mdl W RP). (lazymatch goal with |- ?G => let G' := eval unfold KSPACE, PG in G in change_no_check G' end). lia. }
    assert (NH2s : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ AIMGLO <= z < AIMGHI) -> Hd2 (Z_to_bv 64 z) = false).
    { intros z Hz Hr. exact (mkH_off_zone bt BT_ia st mdl A2 z R13 Hz Hr). }
    assert (NH2ri : forall z, RIz <= z < RIz + 128 -> Hd2 (Z_to_bv 64 z) = false).
    { intros z Hz. apply mkH_notlazy; [lia|]. apply (rep_nolazy_reginfo bt st Lc FF M0 mdl W RP). (lazymatch goal with |- ?G => let G' := eval unfold KSPACE, PG in G in change_no_check G' end). lia. }
    assert (NH2rt : forall z, (T <= z < T + 4096) \/ (CTX <= z < CTX + 0x10000) -> Hd2 (Z_to_bv 64 z) = false).
    { intros z Hz. apply mkH_notlazy; [clear - Hz T1 T2 C1 C2 CR; lia|]. exact (pk_nolazy_rt bt st Lc FF M0 mdl qt qg W RP z Hz). }
    assert (NH2sh : forall z, SH <= z < SH + 2 ^ 15 -> Hd2 (Z_to_bv 64 z) = false).
    { intros z Hz. apply mkH_allowed. (lazymatch goal with |- ?G => let G' := eval unfold A2 in G in change_no_check G' end). apply (range_allowed_last (a_aa st) SH (SH + 2 ^ 18 / 8)); [ | | lia | replace (2 ^ 18 / 8) with (2 ^ 15) by reflexivity; lia | replace (2 ^ 18 / 8) with (2 ^ 15) by reflexivity; exact Hz].
      - pose proof AWF2 as AW. unfold A2, A_wf in AW. apply Forall_app in AW as [_ AW]. apply Forall_cons_iff in AW as [(_ & AW1 & _) _]. cbn [fst] in AW1. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). exact AW1.
      - pose proof AWF2 as AW. unfold A2, A_wf in AW. apply Forall_app in AW as [_ AW]. apply Forall_cons_iff in AW as [(_ & _ & AW2) _]. cbn [snd] in AW2. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). exact AW2. }
    assert (HOFF : forall (H : word -> bool) lo0 n, (forall z, lo0 <= z < lo0 + n -> H (Z_to_bv 64 z) = false) -> hid_off H lo0 n).
    { intros H lo0 n Hz x Hx. rewrite <- (Z_to_bv_bv_unsigned _ x). apply Hz. exact Hx. }
    (* [comment removed for export] *)
    pose proof (pk_T_writable bt BT_segs BT_ia (XL c) st Lc FF M M0 mdl qt qg W RP D) as TWR.
    destruct (pk_junk8 M T (T + 4096) (T + 2872) TWR ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (v72 & R72).
    destruct (pk_junk8 M T (T + 4096) (T + 2880) TWR ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (v80 & R80).
    set (thr := Z_to_bv 64 T : word).
    assert (UT : U thr = T) by ((lazymatch goal with |- ?G => let G' := eval unfold thr in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
    apply (efs_map_arm_katwD_x Hd (HID_off_segments bt st Lc FF M0 mdl BT_ia RP) asanF_segs_wx Hd2 (mkH_off_segments bt BT_ia st mdl A2 R13) A2 AWF2 (a_aa st)
             regs M rom mdl sp ra s0v s1v s2v s3v s4v s5v thr tp gp (Z_to_bv 64 TSDP) (Z_to_bv 64 CTX) v72 v80 (Z_to_bv 64 MIDEND) (Z_to_bv 8 1)
             RIz rbeg tot mfa PGP 0x19fce8 T 0 Qok Qf OKm (fun m => m) DSm).
    all: try (first [exact H1 | exact H2 | exact H4 | exact H3 | exact H10 | exact H11 | exact H12 | exact H13 | exact H8 | exact H9 | exact H18 | exact H19 | exact H20 | exact H21
                    | exact Hret | exact Htot | exact HALT | exact Bw1 | exact Bw2 | exact Hneed]).
    - (* [comment removed for export] *) lia.
    - split; [lia | exact Y6].
    - exact ROOM.
    - split; [lia|]. split; [lia | exact E11].
    - lia.
    - lia.
    - lia.
    - apply (writableZ_sok M (U sp - 448) (U sp)); [exact WSTK | rewrite at_u by lia; lia | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia].
    - apply (repx_rd (XL c) M M0 D (RIz + 24) 8 _); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply XRI; cbn in Hi; lia | exact G24].
    - change (1092440 + 56) with 0x10ab90. rewrite <- (w2b1 0) by lia. exact (pk_const bt BT_segs (XL c) st Lc FF M M0 mdl RP D YIMG QHDR_CONST _ _ _ PC_pre ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - exact (pk_const bt BT_segs (XL c) st Lc FF M M0 mdl RP D YIMG QHDR_CONST _ _ _ CELL_pg ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - exact (pk_const bt BT_segs (XL c) st Lc FF M M0 mdl RP D YIMG QHDR_CONST _ _ _ CELL_P ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - exact (pk_const bt BT_segs (XL c) st Lc FF M M0 mdl RP D YIMG QHDR_CONST _ _ _ CELL_gcf ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - change (1703144 + 260) with 0x19fdec. rewrite <- (w2b1 0) by lia. exact (pk_const bt BT_segs (XL c) st Lc FF M M0 mdl RP D YIMG QHDR_CONST _ _ _ PC_dpm ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - change (1703144 + 144) with 0x19fd78. exact (pk_const bt BT_segs (XL c) st Lc FF M M0 mdl RP D YIMG QHDR_CONST _ _ _ PC_lim ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - left. rewrite <- ELO. lia.
    - apply HOFF. intros z Hz. apply NHri. lia.
    - apply HOFF. intros z Hz. apply NHs; lia.
    - apply HOFF. intros z Hz. apply NHs; lia.
    - apply HOFF. intros z Hz. apply NHs; lia.
    - apply HOFF. intros z Hz. apply NHs; lia.
    - apply HOFF. intros z Hz. apply NHs; lia.
    - apply HOFF. intros z Hz. apply NHs; lia.
    - apply HOFF. intros z Hz. apply NHs; lia.
    - apply lazy_cover_HID.
    - (* [comment removed for export] *)
      intros mdlm r1 SBm MIm HLm G10 G11 G12 G13 G14 G15 Qok' Qf' K1.
      destruct (NODEF mdlm SBm MIm) as (N1 & N2 & N3 & N4 & N5 & _).
      apply (node1_of_fixedin3_s r1 _ rom mdlm addr size Qok' Qf' HLm G10 G11 G12 G13 G14 G15); [ | | | | exact N1 | exact N2 | exact N3 | exact N4 | exact N5 | exact K1].
      + (lazymatch goal with |- ?G => let G' := eval unfold addr in G in change_no_check G' end). rewrite u_Z2bv by lia. (lazymatch goal with |- ?G => let G' := eval unfold lo in G in change_no_check G' end). apply mod4096_sum; [exact E12 | exact E14].
      + (lazymatch goal with |- ?G => let G' := eval unfold addr in G in change_no_check G' end). rewrite u_Z2bv by lia. lia.
      + (lazymatch goal with |- ?G => let G' := eval unfold size in G in change_no_check G' end). rewrite u_Z2bv by lia. lia.
      + (lazymatch goal with |- ?G => let G' := eval unfold size in G in change_no_check G' end). rewrite u_Z2bv by lia. reflexivity.
    - (* [comment removed for export] *)
      intros mdlm SBm MIm. destruct (NODEF mdlm SBm MIm) as (_ & _ & _ & _ & _ & HOK & MOKI & LZOK & HDS & MDSI & LZDS).
      split; [| split].
      + split; [exact HOK|]. split; [| exact MOKI]. exact (lazy_cover_sub Hd _ _ _ (lazy_cover_HID st mdl) LZOK).
      + split; [exact (halted_sbm mdl mdlm SBm HALT)|]. split; [| exact MIm].
        pose proof (same_but_materialized_frame mdl mdlm SBm) as (_ & _ & EL & _). rewrite EL. apply lazy_cover_HID.
      + split; [exact HDS|]. split; [| exact MDSI]. exact (lazy_cover_sub Hd _ _ _ (lazy_cover_HID st mdl) LZDS).
    - (* [comment removed for export] *)
      intros mdlm mdl4 SBm MIm SB4 MI4. split; [| exact (BUD mdlm mdl4 SBm SB4 MI4)].
      destruct (NODEF mdlm SBm MIm) as (_ & _ & _ & _ & _ & _ & _ & LZOK & _).
      pose proof (same_but_materialized_frame _ _ SB4) as (_ & _ & EL & _). rewrite EL.
      exact (lazy_cover_sub Hd2 _ _ _ (lazy_cover_mkH (m_vm_lazy mdl) A2 (m_vm_lazy mdl) (incl_refl _)) LZOK).
    - destruct (pos_mod4096 T T1 T4k) as [T4 T8]. split; [exact UT|]. split; [exact T4|]. split; [lia | exact T8].
    - clear - TSP ERI E9 E10. lia.
    - rewrite <- ESH. clear - TBAND SHB0 SHB1. lia.
    - rewrite <- ESH. right. lia.
    - rewrite <- ESH. right. lia.
    - rewrite <- ELO. clear - TSP SL0 SL1. lia.
    - rewrite <- ELO.
      apply (pk_poisonH bt BT_segs BT_ia TP TSDP PGP FL MIDEND CELLS (XL c) st Lc FF M M0 mdl RP D YIMG QHDR_CONST lo (Z_to_bv 64 325060) (at_ sp (-48)));
        [(lazymatch goal with |- ?G => let G' := eval unfold AS_HEAPLO in G in change_no_check G' end); lia | lia | exact SL8 | rewrite at_u by lia; lia | rewrite at_u by lia; lia | | apply ret_ok_lit; [lia | reflexivity]].
      intros i Hi. rewrite at_u in Hi by lia. apply WSTK. lia.
    - eapply Forall_impl; [| exact both_poison_cells_img]. cbv beta. intros c0 [_ Hc0]. exact Hc0.
    - apply (pk_gctH bt BT_segs BT_ia TP TSDP PGP FL MIDEND CELLS (XL c) st Lc FF M M0 mdl qt qg W RP D YIMG QHDR_CONST YCTX (at_ (at_ sp (-48)) (-16)) tp Etp);
        [rewrite !at_u by (rewrite ?at_u by lia; lia); lia | rewrite !at_u by (rewrite ?at_u by lia; lia); lia |].
      intros i Hi. rewrite !at_u in Hi by (rewrite ?at_u by lia; lia). apply WSTK. lia.
    - (lazymatch goal with |- ?G => let G' := eval cbn [gt_tsd both_gct_tab] in G in change_no_check G' end). rewrite !u_Z2bv by lia. rewrite Etp. lia.
    - (lazymatch goal with |- ?G => let G' := eval cbn [gt_tsd both_gct_tab] in G in change_no_check G' end). rewrite !u_Z2bv by lia. rewrite Etp. rewrite <- ELO.
      split; [left; lia|]. split; [left; lia|]. split; [left; lia|]. clear - CSP SL0 SL1. lia.
    - (lazymatch goal with |- ?G => let G' := eval cbn [gt_tsd both_gct_tab] in G in change_no_check G' end). rewrite !u_Z2bv by lia. rewrite <- ESH. left. lia.
    - rewrite Etp. rewrite <- ESH. left. lia.
    - rewrite !u_Z2bv by lia. rewrite <- ESH. left. lia.
    - rewrite !u_Z2bv by lia. rewrite <- ESH. clear - CBAND SHB0 SHB1. lia.
    - replace (at_ thr 2872) with (Z_to_bv 64 (T + 2872)) by (apply bv_eq; rewrite at_u by lia; rewrite u_Z2bv by lia; lia). exact R72.
    - replace (at_ thr 2880) with (Z_to_bv 64 (T + 2880)) by (apply bv_eq; rewrite at_u by lia; rewrite u_Z2bv by lia; lia). exact R80.
    - apply (writableZ_sok M T (T + 4096)); [exact TWR | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia].
    - apply (writableZ_sok M RIz (RIz + 128)); [apply (repx_wr (XL c) M M0 D); [lia | lia | exact GW] | rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia].
    - (lazymatch goal with |- ?G => let G' := eval unfold poison_cells, both_poison_tab in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [pt_g_shoff pt_p_shoff pt_g_midbeg pt_p_midbeg pt_g_midend pt_p_midend pt_g_hiend pt_p_hiend pt_g_rms pt_p_rms pt_g_cfl pt_p_cfl pt_c_cpm] in G in change_no_check G' end).
      repeat (constructor; [apply HOFF; intros z Hz; apply NH2s; lia|]). constructor.
    - rewrite <- ESH. apply HOFF. exact NH2sh.
    - (lazymatch goal with |- ?G => let G' := eval cbn [gt_tsd both_gct_tab] in G in change_no_check G' end). rewrite u_Z2bv by lia. apply HOFF. intros z Hz. apply NH2s; lia.
    - rewrite Etp. apply HOFF. intros z Hz. apply NH2s; lia.
    - rewrite u_Z2bv by lia. apply HOFF. intros z Hz. apply NH2s; lia.
    - rewrite u_Z2bv by lia. apply HOFF. intros z Hz. apply NH2rt. right. lia.
    - apply HOFF. intros z Hz. apply NH2rt. left. lia.
    - apply HOFF. exact NH2ri.
    - apply HOFF. intros z Hz. apply NH2s; lia.
    - (* [comment removed for export] *)
      intros r' mdlm mdl5 SBm MIm SB5 MI5 Q10 Q2 Q1 Q8 Q9 Q18 Q19 Q20 Q21 Q4 Q3 QX.
      rewrite <- ELO.
      destruct (LEDOK mdlm mdl5 SBm SB5) as (LED & SEV & LK & MW5 & HL5).
      set (MR := efs_mr M sp ra s0v s1v s2v s3v s4v s5v RIz lo mfa PGP).
      set (M' := eam_3 MR sp s4v s5v thr v72 v80 RIz lo mfa).
      assert (ESH2 : SH = lo / 8 + 2147450880) by (rewrite ESH'; (lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end); lia).
      assert (OUTM : forall a : word, (U a < U sp - 448 \/ U sp <= U a) -> (U a < lo \/ lo + 2 ^ 18 <= U a) -> (U a < SH \/ SH + 2 ^ 15 <= U a) ->
                 (U a < T + 2872 \/ T + 2888 <= U a) -> (U a < RIz + 24 \/ RIz + 32 <= U a) -> M' a = M a).
      { intros a X1 X2 X3 X4 X5. (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end).
        rewrite (eam_3_outside MR sp s4v s5v thr v72 v80 RIz lo mfa ltac:(lia) ltac:(lia) a
                   ltac:(lia) ltac:(lia) ltac:(lia) ltac:(clear - X1; lia)
                   ltac:(rewrite <- ESH2; exact X3) ltac:(rewrite UT; exact X4) X5).
        (lazymatch goal with |- ?G => let G' := eval unfold MR in G in change_no_check G' end). apply efs_mr_outside; [lia | lia | exact X1 | exact X2]. }
      assert (GRM : mem_grows M M').
      { (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). eapply mem_grows_trans; [| apply eam_3_grows]. (lazymatch goal with |- ?G => let G' := eval unfold MR in G in change_no_check G' end). apply efs_mr_grows. }
      assert (DEFSL : forall a : word, lo <= U a < lo + 2 ^ 18 -> M' a <> None).
      { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). apply eam_3_grows. (lazymatch goal with |- ?G => let G' := eval unfold MR, efs_mr in G in change_no_check G' end). apply wbytes_grows. (lazymatch goal with |- ?G => let G' := eval unfold zfill, zmem in G in change_no_check G' end). rewrite !u_Z2bv by lia.
        rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. discriminate. }
      assert (WRIM : writableZ BSEGS M RIz (RIz + 128)) by (apply (repx_wr (XL c) M M0 D); [lia | lia | exact GW]).
      assert (FOOTM : forall a : word, M' a <> M a ->
                ((U sp - 448 <= U a < U sp) \/ (lo <= U a < lo + 2 ^ 18) \/ (SH <= U a < SH + 2 ^ 15)
                 \/ (T + 2872 <= U a < T + 2888) \/ (RIz + 24 <= U a < RIz + 32)) /\ M' a <> None).
      { intros a Ha.
        assert (IN : ((U sp - 448 <= U a < U sp) \/ (lo <= U a < lo + 2 ^ 18) \/ (SH <= U a < SH + 2 ^ 15)
                      \/ (T + 2872 <= U a < T + 2888) \/ (RIz + 24 <= U a < RIz + 32))
                     \/ ((U a < U sp - 448 \/ U sp <= U a) /\ (U a < lo \/ lo + 2 ^ 18 <= U a) /\ (U a < SH \/ SH + 2 ^ 15 <= U a)
                         /\ (U a < T + 2872 \/ T + 2888 <= U a) /\ (U a < RIz + 24 \/ RIz + 32 <= U a))) by (clear; lia).
        destruct IN as [IN | (O1 & O2 & O3 & O4 & O5)]; [| exfalso; exact (Ha (OUTM a O1 O2 O3 O4 O5))].
        split; [exact IN|].
        destruct IN as [I1 | [I2 | [I3 | [I4 | I5]]]].
        - apply GRM. destruct (WSTK (U a) I1) as [Dd _]. rewrite Z_to_bv_bv_unsigned in Dd. exact Dd.
        - exact (DEFSL a I2).
        - apply GRM. rewrite <- (Z_to_bv_bv_unsigned _ a). apply (pk_shadow_def bt (XL c) st Lc FF M M0 mdl RP D). (lazymatch goal with |- ?G => let G' := eval unfold shmaps, AS_GAPHI, AS_HEAPLO in G in change_no_check G' end). right. clear - I3 SHB0 SHB1. lia.
        - apply GRM. destruct (TWR (U a) ltac:(clear - I4; lia)) as [Dd _]. rewrite Z_to_bv_bv_unsigned in Dd. exact Dd.
        - apply GRM. destruct (WRIM (U a) ltac:(clear - I5; lia)) as [Dd _]. rewrite Z_to_bv_bv_unsigned in Dd. exact Dd. }
      assert (W' : WFq bt (add_meter (op_famap st c) 0 [(SH, SH + 2 ^ 18 / 8)] 0) Lc FF qt qg).
      { exact (WFq_meter0 (op_famap st c) Lc FF [(SH, SH + 2 ^ 18 / 8)] (OPS_WFq_famap_pf bt st Lc FF c W Hc ROOM FAQ)). }
      assert (RX' : RepX bt (XL c) (add_meter (op_famap st c) 0 [(SH, SH + 2 ^ 18 / 8)] 0) Lc FF M' mdl5).
      { apply (AsAinvOpsRc73.AsAinvRepX3.RepX_mono bt (fun z => XL c z /\ ~ False) (XL c)); [intros z [Hz _]; exact Hz|].
        apply (repx_step bt (XL c) (fun _ => False)
                 (fun z => (U sp - 448 <= z < U sp) \/ (lo <= z < lo + 2 ^ 18) \/ (SH <= z < SH + 2 ^ 15) \/ (T + 2872 <= z < T + 2888) \/ (RIz + 24 <= z < RIz + 32))
                 Xdec_false st _ Lc Lc FF FF M M' mdl mdl5 RX FOOTM ltac:(intros a F; destruct F)).
        intros N0 N0' RPn Dn DIFF _ SAME.
        assert (EQF : forall a : word, ~ XL c (U a) -> N0' a = M' a) by (intros a Ha; apply SAME; exact (repx_off (XL c) M N0 Dn a Ha)).
        pose proof RPn as (_ & _ & _ & R4n & _). destruct (R4n c Hc) as [(_ & _ & _ & _ & _ & _ & _ & _ & _ & GWn) _]. rewrite BT_segs in GWn. fold RIz in GWn.
        destruct LED as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13).
        apply (OPS_REPq_famap_pf bt st Lc FF N0 N0' mdl mdl5 c qt qg W RPn Hc ROOM); rewrite ?BT_segs.
        - intros a Ha. destruct (DIFF a Ha) as [[F | []] Dd]. split; [|exact Dd]. (lazymatch goal with |- ?G => let G' := eval unfold foot_famap, fslot in G in change_no_check G' end). fold r mfa lo RIz SH. (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP, T_UNW in G in change_no_check G' end).
          replace (2 ^ 18 / 8) with (2 ^ 15) by reflexivity. clear - F SP1 CR. lia.
        - (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). fold r mfa RIz. rewrite (rdn_ext BSEGS 8 N0' M' (Z_to_bv 64 (RIz + 24))); [ | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | ].
          + (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP in G in change_no_check G' end). exact (eam_3_mfa BSEGS MR sp s4v s5v thr v72 v80 RIz lo mfa ltac:(lia)).
          + intros x Hx. rewrite u_Z2bv in Hx by lia. cbn in Hx. apply EQF. apply XRI. lia.
        - fold RIz. apply (repx_wr (fun _ => True) N0' N0 (fun a Ha => conj I (proj2 (DIFF a Ha)))); [lia | lia | exact GWn].
        - fold r mfa lo. (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP in G in change_no_check G' end). apply writableZ_of_def; [lia | lia |]. intros i Hi.
          rewrite (EQF (Z_to_bv 64 i)) by (rewrite u_Z2bv by lia; apply XSL; exact Hi). apply DEFSL. rewrite u_Z2bv by lia. exact Hi.
        - fold r mfa lo SH. (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP, fillZ, byteZ, cellN in G in change_no_check G' end). replace (2 ^ 18 / 8) with (2 ^ 15) by reflexivity. intros i Hi.
          rewrite w2b1 by ((lazymatch goal with |- ?G => let G' := eval unfold FA in G in change_no_check G' end); lia).
          rewrite (rdn_ext BSEGS 1 N0' M' (Z_to_bv 64 i)); [ | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros x Hx; rewrite u_Z2bv in Hx by lia; cbn in Hx; apply EQF, XSH; lia].
          replace i with (lo / 8 + 2147450880 + (i - SH)) by lia.
          exact (eam_3_fill BSEGS MR sp thr v72 v80 RIz lo ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite <- ESH2; right; lia)
                   ltac:(rewrite <- ESH2, UT; clear - TBAND SHB0 SHB1; lia) ltac:(rewrite <- ESH2; right; lia) ltac:(rewrite <- ESH2; right; lia) s4v s5v mfa (i - SH) ltac:(lia)).
        - exact L1. - exact L2. - exact L3. - exact L4. - exact L5. - exact L6. - exact L7. - exact L8. - exact L9. - exact L10. - exact L11. - exact L12.
        - exact MI5.
        - exact L13. }
      apply (CONT1 r' M' mdl5 W' RX' SEV LK MW5 HL5); [| exact Q10 | exact Q2 | exact Q1 | exact Q8 | exact Q9 | exact Q18 | exact Q19 | exact Q20 | exact Q21 | exact Q4 | exact Q3
                                                      | apply QX; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10 | apply QX; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10 | apply QX; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10 | apply QX; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10].
      intros a Ha. destruct (FOOTM a Ha) as [F Dd]. split; [| exact Dd]. replace (2 ^ 18 / 8) with (2 ^ 15) by reflexivity. fold RIz. clear - F. lia.
    - (* [comment removed for export] *)
      intros r0 r' mdlm mdl5 SBm MIm SB5 MI5 AG POST. cbv beta in SB5.
      match goal with |- katD _ (mkCfg (mkst _ _ ?MKK _) _) _ => set (MK := MKK) end.
      pose proof (same_but_materialized_trans _ _ _ SBm SB5) as SBK.
      assert (OUTK : forall a : word, (U a < U sp - 448 \/ U sp <= U a) -> MK a = M a).
      { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold MK in G in change_no_check G' end).
        repeat (rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
        rewrite mfi_m1_outside by (rewrite ?at_u by lia; lia). apply efs_m0_outside; lia. }
      assert (GRK : mem_grows M MK).
      { (lazymatch goal with |- ?G => let G' := eval unfold MK in G in change_no_check G' end). do 2 (eapply mem_grows_trans; [| apply wbytes_grows]). eapply mem_grows_trans; [apply efs_m0_grows | apply mfi_m1_grows]. }
      assert (FOOTK : forall a : word, MK a <> M a -> (U sp - 448 <= U a < U sp) /\ MK a <> None).
      { intros a Ha. assert (IN : (U sp - 448 <= U a < U sp) \/ (U a < U sp - 448 \/ U sp <= U a)) by (clear; lia).
        destruct IN as [IN | O1]; [| exfalso; exact (Ha (OUTK a O1))]. split; [exact IN|].
        apply GRK. destruct (WSTK (U a) IN) as [Dd _]. rewrite Z_to_bv_bv_unsigned in Dd. exact Dd. }
      apply (CONT0 r0 r' MK mdl5 st (or_introl eq_refl) W); [ | exact (same_but_materialized_except_vm _ _ SBK) | exact (lazy_kept_sbm Lc FF mdl mdl5 SBK)
                                                              | exact (model_ivs_wf_sbm mdl mdl5 SBK MW) | exact (halted_sbm mdl mdl5 SBK HALT) | | exact AG | exact POST].
      + apply (repx_frame_step_q bt (XL c) st Lc FF M MK mdl mdl5 qt qg W RX); [| exact MI5 | exact SBK].
        intros a Ha. destruct (FOOTK a Ha) as [IN Dd]. split; [|exact Dd].
        intros RCa. pose proof (rep_cells_lt_ceil_q bt BT_ia st Lc FF (U a) qt qg W RCa). lia.
      + intros a Ha. left. exact (FOOTK a Ha).
    - (* [comment removed for export] *)
      intros r0 r' mdlm mdl5 SBm MIm SB5 MI5 AG POST. rewrite <- ELO.
      match goal with |- katD _ (mkCfg (mkst _ _ ?MKK _) _) _ => set (MD := MKK) end.
      destruct (LEDDS mdlm mdl5 SBm SB5) as (LD & EAG & SEV & LK & MW5 & HL5).
      assert (OUTD : forall a : word, (U a < U sp - 448 \/ U sp <= U a) -> (U a < lo \/ lo + 2 ^ 18 <= U a) -> MD a = M a).
      { intros a Ha Hb. (lazymatch goal with |- ?G => let G' := eval unfold MD in G in change_no_check G' end).
        repeat (rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
        rewrite unfill_out by (rewrite !u_Z2bv by lia; exact Hb).
        rewrite mfi_m1_outside by (rewrite ?at_u by lia; lia). apply efs_m0_outside; lia. }
      assert (SLD : forall a : word, lo <= U a < lo + 2 ^ 18 -> MD a = None).
      { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold MD in G in change_no_check G' end).
        repeat (rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
        (lazymatch goal with |- ?G => let G' := eval unfold unfill in G in change_no_check G' end). rewrite !u_Z2bv by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
      assert (STD : forall a : word, U sp - 448 <= U a < U sp -> MD a <> None).
      { intros a Ha. destruct (decide (MD a = M a)) as [E | NE]; [rewrite E; destruct (WSTK (U a) Ha) as [Dd _]; rewrite Z_to_bv_bv_unsigned in Dd; exact Dd|].
        (* [comment removed for export] *)
        unfold MD in NE |- *.
        set (MU := unfill (Z_to_bv 64 lo) (Z_to_bv 64 (2 ^ 18)) _) in *.
        assert (GU : forall x : word, U sp - 448 <= U x < U sp -> MU x <> None).
        { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold MU in G in change_no_check G' end). rewrite unfill_out by (rewrite !u_Z2bv by lia; lia).
          apply mfi_m1_grows. apply efs_m0_grows. destruct (WSTK (U x) Hx) as [Dd _]. rewrite Z_to_bv_bv_unsigned in Dd. exact Dd. }
        do 2 apply wbytes_grows. exact (GU a Ha). }
      assert (FOOTD : forall a : word, MD a <> M a -> ((U sp - 448 <= U a < U sp) /\ MD a <> None) \/ (lo <= U a < lo + 2 ^ 18)).
      { intros a Ha. assert (IN : (U sp - 448 <= U a < U sp) \/ (lo <= U a < lo + 2 ^ 18) \/ ((U a < U sp - 448 \/ U sp <= U a) /\ (U a < lo \/ lo + 2 ^ 18 <= U a))) by (clear; lia).
        destruct IN as [IN | [IN | [O1 O2]]]; [left; split; [exact IN | exact (STD a IN)] | right; exact IN | exfalso; exact (Ha (OUTD a O1 O2))]. }
      assert (W1 : WFq bt (op_fhole st c) Lc FF qt qg) by (apply (WF_fhole bt st Lc FF c Hc ROOM W)).
      apply (CONT0 r0 r' MD mdl5 (op_fhole st c) (or_intror eq_refl) W1); [ | exact SEV | exact LK | exact MW5 | exact HL5 | | exact AG | exact POST].
      + (* [comment removed for export] *)
        set (N1 := unfill (Z_to_bv 64 lo) (Z_to_bv 64 (2 ^ 18)) M0).
        assert (RP1 : Rep bt (op_fhole st c) Lc FF N1 mdl5).
        { apply (OPS_REPq_fhole_pf bt st Lc FF M0 N1 mdl mdl5 c qt qg W RP Hc FH ROOM); [ | exact LD | exact MI5 | exact EAG].
          intros a Ha. unfold N1, unfill in Ha |- *. rewrite !u_Z2bv in Ha |- * by lia. (lazymatch goal with |- ?G => let G' := eval unfold fslot in G in change_no_check G' end). fold r mfa lo. (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP in G in change_no_check G' end).
          destruct (Z.leb_spec lo (U a)); destruct (Z.ltb_spec (U a) (lo + 2 ^ 18)); cbn [andb] in Ha |- *; first [split; [lia | reflexivity] | exfalso; exact (Ha eq_refl)]. }
        set (N := fun a : word => if Z_le_dec lo (U a) then (if Z_lt_dec (U a) (lo + 2 ^ 18) then None else if decide (M a = M0 a) then MD a else M0 a)
                                  else if decide (M a = M0 a) then MD a else M0 a).
        assert (N1in : forall a : word, lo <= U a < lo + 2 ^ 18 -> N1 a = None).
        { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold N1, unfill in G in change_no_check G' end). rewrite !u_Z2bv by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
        assert (N1out : forall a : word, (U a < lo \/ lo + 2 ^ 18 <= U a) -> N1 a = M0 a).
        { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold N1 in G in change_no_check G' end). apply unfill_out. rewrite !u_Z2bv by lia. exact Ha. }
        exists N. split.
        * apply (Rep_frame_q bt (op_fhole st c) Lc FF N1 N mdl5 W1 RP1). intros a Ha. unfold N in Ha |- *.
          destruct (Z_le_dec lo (U a)) as [L1|L1]; [destruct (Z_lt_dec (U a) (lo + 2 ^ 18)) as [L2|L2]|].
          -- exfalso. apply Ha. symmetry. apply N1in. lia.
          -- rewrite (N1out a ltac:(lia)) in Ha. destruct (decide (M a = M0 a)) as [E | NE]; [| exfalso; exact (Ha eq_refl)].
             rewrite <- E in Ha. destruct (FOOTD a Ha) as [[IN Dd] | IN]; [| lia]. split; [|exact Dd].
             intros RCa. pose proof (rep_cells_lt_ceil_q bt BT_ia (op_fhole st c) Lc FF (U a) qt qg W1 RCa). lia.
          -- rewrite (N1out a ltac:(lia)) in Ha. destruct (decide (M a = M0 a)) as [E | NE]; [| exfalso; exact (Ha eq_refl)].
             rewrite <- E in Ha. destruct (FOOTD a Ha) as [[IN Dd] | IN]; [| lia]. split; [|exact Dd].
             intros RCa. pose proof (rep_cells_lt_ceil_q bt BT_ia (op_fhole st c) Lc FF (U a) qt qg W1 RCa). lia.
        * intros a Ha. unfold N in Ha.
          assert (CASE : forall (E : M a <> M0 a), XL c (U a) /\ MD a <> None).
          { intros NE. destruct (D a NE) as [HX Dd]. split; [exact HX|].
            destruct (decide (MD a = M a)) as [EQ2 | NE2]; [rewrite EQ2; exact Dd|].
            destruct (FOOTD a NE2) as [[_ Dd2] | IN]; [exact Dd2 | exfalso; exact (XSL (U a) IN HX)]. }
          destruct (Z_le_dec lo (U a)) as [L1|L1]; [destruct (Z_lt_dec (U a) (lo + 2 ^ 18)) as [L2|L2]|].
          -- exfalso. apply Ha. apply SLD. lia.
          -- destruct (decide (M a = M0 a)) as [E | NE]; [exfalso; exact (Ha eq_refl) | exact (CASE NE)].
          -- destruct (decide (M a = M0 a)) as [E | NE]; [exfalso; exact (Ha eq_refl) | exact (CASE NE)].
      + intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP in G in change_no_check G' end). exact (FOOTD a Ha).
  Qed.


End L3.
End WithCeil.
