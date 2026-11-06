(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.glaze.binary_reflection.images Require Import Ubsan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaN OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNest2 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMmapK OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaM OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhUnmap OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaS OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMmapWF OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaR OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.Nodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsanNodesMmLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys.MhKX OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.MhKSys OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhExt OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhList OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhRepT OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaN.UbMhNtfLib OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNest2.UbMhNest OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys.MhGap OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMmapK.UbMhAcct OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaM.UbMhRsegs OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys.MhBrkK OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMmapK OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhUnmap OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaS.UbMhAMetaW OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaM.UbMhAMetaWF OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMmapWF.UbMhMmapW OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMmapWF OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaN OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaR OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaF OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaS.UbMhMSpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaS OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaM.UbMhAMetaT OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaM.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import PuAtom.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
#[local] Ltac mh_lia_nx := rnfix; first [ solve [hclr; lean zlia] | pa_arith_concl; lia_goal_ok; lia_hsep; first [ with_img1f_ zlia | with_img1_ zlia | lia_pairs; with_img2 zlia ] ].
#[local] Ltac lia ::= first [ solve [ rnfix; pa_tiers ltac:(zlia) ] | solve [ rnfix; pa_big; lia_goal_ok; lia_hsep; pa_tierB ltac:(zlia) ] | mh_lia_nx ].
#[local] Ltac lia_fast ::= first [ solve [ rnfix; pa_tiers ltac:(zlia) ] | solve [ rnfix; pa_big; lia_goal_ok; lia_hsep; pa_tierB ltac:(zlia) ] | first [ solve [ clear_disj; lia ] | lia ] ].
Section AMC. (* [comment removed for export] *)
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st : mst) (L : list (Z * Z)) (X : list (word * word)) (M : mem) (mdl : Model)
            (regs : bvmap 5 word) (rom : word -> option byte) (sp : Z).
  Variables (F : kfam) (bi : bool).
  Hypothesis HL : kfam_laws RSEGS F.
  Hypothesis HWF : WF st L.
  Hypothesis HREP : REP st M.
  Hypothesis HLG : LEDGERX st X (m_vmmaps mdl).
  Hypothesis XOK : xok X.
  Hypothesis Hh : m_halted mdl = None.
  Hypothesis Hlz : m_vm_lazy mdl = [].
  Hypothesis Hmat : m_vm_materialized mdl = [].
  Hypothesis HCNT : s_flist st = [] -> c_avail_cnt (s_ctx st) = 0 -> Z.of_nat (length (s_areas st)) + 1 <= AREAMAX.
  Hypothesis HLEN : Z.of_nat (length X) + Z.of_nat (length (s_regions st)) <= 246.
  Hypothesis HBUD : XSUM X + RSUM (s_regions st) + 2 ^ 24 <= vm_limit (m_vmmaps mdl).
  Hypothesis H2 : getr regs 2 = Z_to_bv 64 sp.
  Hypothesis Hra : ret_ok (getr regs 1).
  Hypothesis Hsp : CEIL + AMSTK <= sp /\ sp < 2 ^ 64.
  Hypothesis H4 : getr regs 4 = Z_to_bv 64 TPV.
  Hypothesis DEF : defined M (sp - AMSTK) sp.
  Hypothesis Hok : forall c', am_post st L X sp regs M mdl rom c' -> kfx F bi c'.
  Hypothesis Hfail : forall c', am_fail st L X sp regs M mdl rom c' -> Kf F c'.

  #[local] Notation cx := (s_ctx st).
  #[local] Notation can := (UbMhAMetaS.can st).
  #[local] Notation M1 := (UbMhAMetaS.M1 st M regs sp).
  #[local] Notation ctxV := (UbMhAMetaM.UbMhAMetaT.ctxV).
  #[local] Notation kfx := (kfx F).

  Lemma Hsp' : CEIL + 144 <= sp /\ sp < 2 ^ 64. Proof using Hsp. unfold AMSTK in Hsp. exact Hsp. Qed.
  Lemma Hsp64 : CEIL + 64 <= sp /\ sp < 2 ^ 64. Proof using Hsp X st. unfold AMSTK in Hsp. lia. Qed.
  Lemma pru_4096 : page_round_up_Z 4096 = 4096. Proof using. reflexivity. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section ArmC1.
    Hypothesis Hfl : s_flist st = [].
    Hypothesis Hac0 : c_avail_cnt cx = 0.
    #[local] Notation ac := (c_area_cnt (s_ctx st)).
    #[local] Notation cur := (c_cursor (s_ctx st)).
    Hypothesis Hac : ac > 0.

    Lemma arm_C1 : forall b r1, getr r1 2 = Z_to_bv 64 (sp - 64) -> getr r1 19 = Z_to_bv 64 MLOCK -> getr r1 8 = Z_to_bv 64 4096 ->
      getr r1 18 = Z_to_bv 64 A_CANARY -> keeps_but clobI regs r1 ->
      kfx b (mkCfg (mkst r1 (0x66d1c%bv : word) M1 rom) mdl).
    Proof using Hac Hac0 Hfl Hfail Hok DEF H4 Hsp Hra H2 HBUD HCNT Hmat Hlz Hh HLG HREP HWF HL bi X L RN.
      intros b r1 G2 G19 G8 G18 K1. pose proof Hsp' as [S1 S2]. ceil.
      destruct (wc_cursor st (WF_ctx st L HWF) Hac) as (bb & len & e & HRin & He & Hc1 & Hc2).
      pose proof (conj HRin (conj He (conj Hc1 Hc2))) as HR.
      pose proof (UbMhAMetaR.c1_R_rng st L HWF bb len e HR) as (R1 & R2 & R3 & R4 & R5). ceil; unfold HEAPLO in R1, R2.
      pose proof (UbMhAMetaR.c1_R_meta st L HWF bb len e HR) as (E1 & E2 & E3).
      pose proof (UbMhAMetaR.c1_Hp st L HWF Hac bb len e HR) as HP. unfold UbMhAMetaR.c1_p in HP. destruct HP as (P0 & P1 & P2). ceil; unfold HEAPLO in P1, P2.
      pose proof (UbMhAMetaR.c1_Hp_img st L HWF Hac bb len e HR) as PI. unfold UbMhAMetaR.c1_p, img_free in PI.
      pose proof (UbMhAMetaS.M1_REP st L X M regs sp HWF HREP Hsp) as REP1. pose proof (rp_ctx st M1 REP1) as RC1.
      pose proof (rc_fmh st M1 RC1) as Cfh. rewrite (wc_fhead st (WF_ctx st L HWF)), Hfl in Cfh. cbn [head_of] in Cfh.
      pose proof (rc_amc st M1 RC1) as Ccnt. rewrite Hac0 in Ccnt.
      pose proof (rc_amac st M1 RC1) as Cac. pose proof (rc_amas st M1 RC1) as Ccur.
      pose proof (UbMhAMetaS.can_rng st L HWF) as CANR.
      (* [comment removed for export] *)
      destruct (amC1a M1 Cfh Ccnt ac cur ltac:(lia) ltac:(lia) Cac Ccur r1 rom G19 G8 ltac:(lia) P0) as (rC & RUN1 & C10 & C11 & C12 & C9 & C1 & KC).
      eapply (kfx_msteps RSEGS F HL); [exact Hh | exact Hlz | exact RUN1 |].
      (* [comment removed for export] *)
      assert (SOK16 : store_ok RSEGS M1 (Z_to_bv 64 (sp - 64 - 16)) 16%nat = true).
      { eapply store_ok_defined; [exact (UbMhAMetaS.M1_def st M regs sp DEF) | unfold AMSTK; lia | unfold AMSTK; cbn; lia | unfold AMSTK; lia | lia]. }
      destruct (mpW1 M1 (sp - 64) cur 3 ltac:(lia) SOK16 ltac:(lia) (rc_pagesize st M1 (rp_statics st M1 REP1)) rC rom
                  ltac:(kept_rw KC; exact G2) C10 C11 C12) as (rD & RUN2 & D2 & D17 & D10 & D11 & D12 & KD).
      eapply (kfx_msteps RSEGS F HL); [exact Hh | exact Hlz | exact RUN2 |].
      (* [comment removed for export] *)
      assert (NAin : exists nb nl, In (Z_to_bv 64 nb, Z_to_bv 64 nl) (vm_noaccess (m_vmmaps mdl)) /\ nb <= cur /\ cur + 4096 <= nb + nl /\ 0 <= nb /\ nb + nl < 2 ^ 64).
      { assert (INf : forall en, In en (noacc_of_region (RG bb len (RMeta e))) -> In en (vm_noaccess (m_vmmaps mdl))).
        { intros en Hen. apply (Permutation_in _ (Permutation_sym (lx_noacc st X _ HLG))). unfold noacc_of. apply in_app_iff. right.
          apply in_flat_map. exists (RG bb len (RMeta e)). split; [exact HRin | exact Hen]. }
        destruct (Z.eq_dec e 0) as [E0|E0].
        - exists bb, len. split; [apply INf; cbn [noacc_of_region rg_kind rg_base rg_len]; rewrite (proj2 (Z.eqb_eq _ _) E0); left; reflexivity | lia].
        - exists cur, (len - 4096 * (1 + e)). split; [|lia]. apply INf. cbn [noacc_of_region rg_kind rg_base rg_len]. rewrite (proj2 (Z.eqb_neq _ _) E0).
          right. rewrite (proj2 (Z.ltb_lt _ _)) by lia. left. rewrite Hc1. reflexivity. }
      assert (MPin : In (Z_to_bv 64 bb, Z_to_bv 64 len) (vm_maps (m_vmmaps mdl))).
      { exact (UbMhAMetaR.region_in_maps st X (m_vmmaps mdl) HLG _ HRin). }
      set (M2 := mp_frame M1 (sp - 64) (getr rC 1)).
      assert (M2W : forall a, 0 <= a < 2 ^ 64 -> M2 (Z_to_bv 64 a) <> M (Z_to_bv 64 a) -> sp - 72 <= a < sp).
      { intros a Ha NE. unfold M2, mp_frame in NE.
        destruct (decide (M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E4|NE4].
        - rewrite <- E4 in NE. apply wbytes_diff_g in NE; [| lia | zsimp; lia | exact Ha]. rewrite length_N_to_le_bytes in NE. cbn in NE. lia.
        - pose proof (UbMhAMetaS.M1_writes st X M regs sp Hsp a Ha NE4). lia. }
      assert (M2G : mem_grows M M2) by (unfold M2, mp_frame; eapply mem_grows_trans; [exact (UbMhAMetaS.M1_grows st M regs sp) | apply wbytes_grows]).
      assert (AG2 : forall a1 k v, cell M a1 k v -> IMG_LO <= a1 -> a1 + Z.of_nat k <= IMG_HI -> cell M2 a1 k v).
      { intros a1 k v C Ha Hk. eapply cell_agree; [lia | lia | | exact C]. intros y Hr Hy.
        destruct (decide (M2 (Z_to_bv 64 y) = M (Z_to_bv 64 y))) as [E|NE]; [exact E|]. exfalso. pose proof (M2W y Hr NE). lia. }
      destruct NAin as (nb & nl & NAin & NA1 & NA2 & NA3 & NA4).
      apply (kfx_mprotect RSEGS F HL bi b rD (0x68404%bv : word) M2 rom mdl W_683b0 (Z_to_bv 64 cur) 4096
               Hh Hlz F_683b0 E_683b0 D17 D10 ltac:(unfold page_size; rewrite u_Z2bv by lia; exact P0) D11 ltac:(lia)
               ltac:(rewrite pru_4096, u_Z2bv by lia; unfold two_pow_64; lia) D12).
      { rewrite pru_4096. eapply map_contains_In; [exact NAin | rewrite !u_Z2bv by lia; lia | rewrite !u_Z2bv by lia; lia]. }
      { rewrite pru_4096. eapply map_contains_In; [exact MPin | rewrite !u_Z2bv by lia; lia | rewrite !u_Z2bv by lia; lia]. }
      { apply (mprotect_budget_of_ledgerx st L HWF X mdl _ _ HLG Hlz Hmat). lia. }
      { (* [comment removed for export] *)
        unfold mpr_fail. rewrite errno_ret_ENOMEM. replace (v_addi (0x68404%bv : word) 4) with (0x68408%bv : word) by (apply bv_eq; reflexivity).
        assert (SOK16f : store_ok RSEGS M2 (Z_to_bv 64 (sp - 64 - 32)) 16%nat = true).
        { eapply (store_ok_defined M2 (sp - AMSTK) sp); [| unfold AMSTK; lia | unfold AMSTK; cbn; lia | unfold AMSTK; lia | lia].
          eapply defined_grows; [exact M2G | exact DEF]. }
        destruct (mpW2f M2 (sp - 64) ltac:(unfold A_ERRNO, TPV; lia) SOK16f (UbMhAMetaM.errno_sok M2) (regupd rD 10 (Z_to_bv 64 (2 ^ 64 - 12))) rom (getr rC 1)
                    ltac:(rewrite C1; apply ret_ok_even; reflexivity) ltac:(gres; exact D2) ltac:(rewrite getr_same by (intros E; discriminate E); reflexivity)
                    ltac:(gres; kept_rw KD; kept_rw KC; exact (UbMhAMetaM.x4_clobI regs H4 r1 K1))
                    ltac:(unfold M2, mp_frame; apply rdn_wbytes_hit8; zsimp; lia))
          as (rF & RUNF & F2 & F10 & F1 & F8 & KF).
        eapply (kf_msteps RSEGS F HL); [exact Hh | exact Hlz | exact RUNF |].
        rewrite C1. replace (Z_to_bv 64 421664) with (421664%bv : word) by (apply bv_eq; reflexivity).
        set (Mf := mp_ffail M2 (sp - 64) (getr (regupd rD 10 (Z_to_bv 64 (2 ^ 64 - 12))) 8)).
        set (Mpre := wbytes (wbytes M2 (Z_to_bv 64 (sp - 64 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x6840c)))
                            (Z_to_bv 64 (sp - 64 - 32)) (word_to_le_bytes 8 (getr (regupd rD 10 (Z_to_bv 64 (2 ^ 64 - 12))) 8))).
        assert (EMf : Mf = wbytes Mpre (Z_to_bv 64 A_ERRNO) errno12) by reflexivity.
        assert (MpreW : forall x, 0 <= x < 2 ^ 64 -> Mpre (Z_to_bv 64 x) <> M (Z_to_bv 64 x) -> sp - 144 <= x < sp).
        { intros x Hx NE. destruct (decide (sp - 144 <= x < sp)) as [IN|OUT]; [exact IN|]. exfalso. apply NE. unfold Mpre.
          rewrite !wbytes_outZ by (wd_lenlit; rewrite ?length_N_to_le_bytes; cbn; lia).
          destruct (decide (M2 (Z_to_bv 64 x) = M (Z_to_bv 64 x))) as [E4|NE4]; [exact E4|]. exfalso. pose proof (M2W x Hx NE4). lia. }
        assert (MfW : forall x, 0 <= x < 2 ^ 64 -> Mf (Z_to_bv 64 x) <> M (Z_to_bv 64 x) -> (sp - 144 <= x < sp) \/ (A_ERRNO <= x < A_ERRNO + 4)).
        { intros x Hx NE. destruct (decide (A_ERRNO <= x < A_ERRNO + 4)) as [IN|OUT]; [right; exact IN | left]. apply (MpreW x Hx).
          intros E. apply NE. rewrite EMf. unfold errno12, A_ERRNO, TPV in *. rewrite wbytes_outZ by (wd_lenlit; rewrite ?length_N_to_le_bytes; cbn; lia). exact E. }
        assert (MpreG : mem_grows M Mpre) by (unfold Mpre; do 2 (eapply mem_grows_trans; [|apply wbytes_grows]); exact M2G).
        assert (AGf : forall a1 k v, cell M a1 k v -> IMG_LO <= a1 -> a1 + Z.of_nat k <= IMG_HI ->
                       (forall y, a1 <= y < a1 + Z.of_nat k -> ~ (A_ERRNO <= y < A_ERRNO + 4)) -> cell Mf a1 k v).
        { intros a1 k v C Ha Hk OUT. eapply (UbMhAMetaM.cell_keep st X M Mf _ a1 k v); [| exact C | exact Ha | exact Hk | exact OUT].
          intros y Hy NE. destruct (MfW y Hy NE) as [A|A]; [left; right; ceil; lia | right; exact A]. }
        assert (STKf : forall d v, 8 <= d <= 56 -> rdn RSEGS M1 (Z_to_bv 64 (sp - d)) 8%nat = Some (word_to_le_bytes 8 v) ->
                       rdn RSEGS Mf (Z_to_bv 64 (sp - d)) 8%nat = Some (word_to_le_bytes 8 v)).
        { intros d v Hd R. rewrite <- R. apply rdn_ext; [rewrite u_Z2bv by lia; lia|].
          intros x Hx. rewrite u_Z2bv in Hx by lia. pose proof (u64_range x) as XR. rewrite <- (Z_to_bv_u_eq' x (bv_unsigned x) eq_refl).
          rewrite EMf. unfold Mpre, M2, mp_frame, errno12, A_ERRNO, TPV. rewrite !wbytes_outZ by (wd_lenlit; rewrite ?length_N_to_le_bytes; cbn; lia). reflexivity. }
        destruct (amPf Mf sp can (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) Hsp64 Hra
                    ltac:(pose proof (rc_canary st M (rp_statics st M HREP)) as C; unfold cell in C; apply (AGf _ _ _ C); unfold A_CANARY, A_ERRNO, TPV; cbn; intros; lia)
                    (STKf 56 _ ltac:(lia) (UbMhAMetaS.M1_can st X M regs sp Hsp)) (STKf 8 _ ltac:(lia) (UbMhAMetaS.M1_ra st X M regs sp Hsp))
                    (STKf 16 _ ltac:(lia) (UbMhAMetaS.M1_s0 st X M regs sp Hsp)) (STKf 24 _ ltac:(lia) (UbMhAMetaS.M1_s1 st X M regs sp Hsp))
                    (STKf 32 _ ltac:(lia) (UbMhAMetaS.M1_s2 st X M regs sp Hsp)) (STKf 40 _ ltac:(lia) (UbMhAMetaS.M1_s3 st X M regs sp Hsp))
                    (STKf 48 _ ltac:(lia) (UbMhAMetaS.M1_s4 st X M regs sp Hsp))
                    ltac:(rewrite EMf; unfold errno12; pose proof (rdn_wbytes_hit RSEGS (word_to_le_bytes 4 (Z_to_bv 64 12)) Mpre (Z_to_bv 64 A_ERRNO)) as RH;
                          rewrite length_N_to_le_bytes in RH; apply RH; unfold A_ERRNO, TPV; zsimp; lia)
                    rF rom F2 ltac:(kept_rw KF; gres; kept_rw KD; kept_rw KC; exact G18) F10
                    ltac:(kept_rw KF; gres; kept_rw KD; kept_rw KC; exact (UbMhAMetaM.x4_clobI regs H4 r1 K1)))
          as (rZ & RUNZ & Z2 & Z10 & Z1 & Z8 & Z9 & Z18 & Z19 & Z20 & KZ).
        eapply (kf_msteps RSEGS F HL); [exact Hh | exact Hlz | exact RUNZ |].
        apply Hfail. rewrite EMf.
        apply (UbMhAMetaM.am_fail_fst st L X M mdl regs rom sp (s_regions st) (d_brk st false) cur ac (c_shift cx) (d_cb st false) Mpre _ mdl rZ).
        - exact (d_WF st L HWF false).
        - apply (f_REP st L M Mpre HWF HREP (s_regions st) (d_brk st false) cur ac (c_shift cx) (d_cb st false));
            [exact (d_Hac' st L HWF) | exact (d_Hsh' st L HWF) | ..].
          + intros a Hr Ha. destruct (decide (Mpre (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
            pose proof (MpreW a Hr NE). ceil; unfold CTX in *; lia.
          + intros a Hr [Ha NW]. destruct (decide (Mpre (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
            pose proof (MpreW a Hr NE). ceil; unfold CTX_END, CTX in *; lia.
          + eapply cell_agree; [| | | exact (rc_amac st M (rp_ctx st M HREP))]; [unfold ctx_avail_meta_area_count, CTX; lia | unfold ctx_avail_meta_area_count, CTX; cbn; lia |].
            intros y Hr Hy. destruct (decide (Mpre (Z_to_bv 64 y) = M (Z_to_bv 64 y))) as [E|NE]; [exact E|]. exfalso. pose proof (MpreW y Hr NE). ceil; unfold ctx_avail_meta_area_count, CTX in *; cbn in Hy; lia.
          + eapply cell_agree; [| | | exact (rc_mas st M (rp_ctx st M HREP))]; [unfold ctx_meta_alloc_shift, CTX; lia | unfold ctx_meta_alloc_shift, CTX; cbn; lia |].
            intros y Hr Hy. destruct (decide (Mpre (Z_to_bv 64 y) = M (Z_to_bv 64 y))) as [E|NE]; [exact E|]. exfalso. pose proof (MpreW y Hr NE). ceil; unfold ctx_meta_alloc_shift, CTX in *; cbn in Hy; lia.
          + eapply cell_agree; [| | | exact (rc_amas st M (rp_ctx st M HREP))]; [unfold ctx_avail_meta_areas, CTX; lia | unfold ctx_avail_meta_areas, CTX; cbn; lia |].
            intros y Hr Hy. destruct (decide (Mpre (Z_to_bv 64 y) = M (Z_to_bv 64 y))) as [E|NE]; [exact E|]. exfalso. pose proof (MpreW y Hr NE). ceil; unfold ctx_avail_meta_areas, CTX in *; cbn in Hy; lia.
          + unfold d_cb. eapply cell_agree; [| | | exact (rc_brk st M (rp_ctx st M HREP))]; [unfold ctx_brk, CTX; lia | unfold ctx_brk, CTX; cbn; lia |].
            intros y Hr Hy. destruct (decide (Mpre (Z_to_bv 64 y) = M (Z_to_bv 64 y))) as [E|NE]; [exact E|]. exfalso. pose proof (MpreW y Hr NE). ceil; unfold ctx_brk, CTX in *; cbn in Hy; lia.
          + intros a Hd D. apply MpreG. exact D.
          + intros ar a Har Ha. destruct (wa_rng st (WF_areas st L HWF) ar Har) as (Aal & Alo & Ahi).
            destruct (decide (Mpre (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
            pose proof (MpreW a ltac:(ceil; unfold HEAPLO in *; lia) NE). ceil; lia.
          + intros t a Ht Kt Ha. destruct (group_range st L HWF t Ht) as [Q1 Q2].
            pose proof (wg_kind st L t (wG_each st L (WF_groups st L HWF) t Ht)) as KD2. rewrite Kt in KD2. destruct KD2 as (K1' & K2 & _).
            destruct (wr_rng st (WF_regions st L HWF) _ K2) as (W1 & W2 & _). cbn in W1, W2. unfold g_map_end in Ha.
            destruct (decide (Mpre (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
            pose proof (MpreW a ltac:(ceil; unfold HEAPLO in *; lia) NE). ceil; lia.
        - apply (d_ledger st X (m_vmmaps mdl) HLG false); try reflexivity. intros _; split; reflexivity.
        - apply (UbMhAMetaM.errno_write_intro st X).
        - exact Hh. - exact Hlz. - exact Hmat. - reflexivity. - reflexivity. - reflexivity.
        - split; [cbn [s_regions fst]; lia|]. split; [cbn [s_regions fst]; lia|]. cbn [s_regions fst]. intros r Hr. left. exists r. split; [exact Hr | split; reflexivity].
        - exact Z10.
        - rewrite Z2, H2. reflexivity.
        - apply (UbMhAMetaS.keeps_final_am regs rZ (clobI ++ ([1; 9; 10; 11; 12]%bv ++ ([2; 11; 13; 14; 17]%bv ++ ([10]%bv ++ ([1; 2; 8; 10; 11]%bv ++ clobZ)))))).
          + eapply UbMhAMetaS.keeps_join; [exact K1|]. eapply UbMhAMetaS.keeps_join; [exact KC|]. eapply UbMhAMetaS.keeps_join; [exact KD|].
            eapply UbMhAMetaS.keeps_join; [apply keeps_but_upd; [apply keeps_but_refl | left; reflexivity]|].
            eapply UbMhAMetaS.keeps_join; [exact KF | exact KZ].
          + reflexivity.
          + exact Z1. + rewrite Z2, H2; reflexivity. + exact Z8. + exact Z9. + exact Z18. + exact Z19. + exact Z20.
          + kept_rw KZ. kept_rw KF. gres. kept_rw KD. kept_rw KC. kept_rw K1. reflexivity.
        - intros a Ha NE. rewrite <- EMf in NE. destruct (MfW a Ha NE) as [W|W].
          + left. unfold AMSTK. exact W.
          + right; right; left. exact W.
        - rewrite <- EMf. intros y Hy. unfold Mf, mp_ffail. do 3 apply (wbytes_grows _ _ _ (Z_to_bv 64 y)). apply M2G. exact (DEF y Hy). }
      (* [comment removed for export] *)
      unfold mpr_ok. rewrite pru_4096. replace (v_addi (0x68404%bv : word) 4) with (0x68408%bv : word) by (apply bv_eq; reflexivity).
      set (M3 := zfill (Z_to_bv 64 cur) (Z_to_bv 64 4096) M2).
      set (mdl1 := mprotect_model (Z_to_bv 64 cur) (Z_to_bv 64 4096) mdl).
      pose (h1 := mkVmMapsFull (vm_reserved (m_vmmaps mdl)) (vm_maps (m_vmmaps mdl))
                 (maps_subtract (vm_noaccess (m_vmmaps mdl)) (bv_unsigned (Z_to_bv 64 cur)) (bv_unsigned (Z_to_bv 64 cur) + bv_unsigned (Z_to_bv 64 4096)))
                 (vm_start_brk (m_vmmaps mdl)) (vm_brk (m_vmmaps mdl)) (vm_limit (m_vmmaps mdl)) (vm_mmap_base (m_vmmaps mdl)) (vm_init_sp (m_vmmaps mdl))).
      pose proof (with_vmmaps_facts h1 mdl) as MF. change (with_vmmaps h1 mdl) with mdl1 in MF. destruct MF as (MF1 & MF2 & MF3 & MF4 & MF5 & MF6).
      (* [comment removed for export] *)
      assert (RA3 : rdn RSEGS M3 (Z_to_bv 64 (sp - 64 - 8)) 8%nat = Some (word_to_le_bytes 8 (getr rC 1))).
      { unfold M3, M2, mp_frame. rewrite rdn_zfill_outZ by (cbn; lia). apply rdn_wbytes_hit8. zsimp; lia. }
      destruct (mpW2 (sp - 64) cur ltac:(lia) (regupd rD 10 (Z_to_bv 64 0)) rom M3 (getr rC 1) ltac:(rewrite C1; apply ret_ok_even; reflexivity)
                  ltac:(gres; exact D2) ltac:(gres; reflexivity) RA3) as (rF & RUN3 & F2 & F10 & F1 & KF).
      eapply (kfx_msteps RSEGS F HL); [rewrite MF2; exact Hh | rewrite MF3; exact Hlz | exact RUN3 |].
      rewrite C1. replace (Z_to_bv 64 421664) with (421664%bv : word) by (apply bv_eq; reflexivity).
      eapply (kfx_msteps RSEGS F HL); [rewrite MF2; exact Hh | rewrite MF3; exact Hlz | exact (amC1b rF rom M3 F10) |].
      (* [comment removed for export] *)
      assert (KT : keeps_but (clobI ++ ([1; 9; 10; 11; 12]%bv ++ ([2; 11; 13; 14; 17]%bv ++ ([10]%bv ++ [1; 2; 10; 11]%bv)))) regs rF).
      { eapply UbMhAMetaS.keeps_join; [exact K1|]. eapply UbMhAMetaS.keeps_join; [exact KC|]. eapply UbMhAMetaS.keeps_join; [exact KD|]. eapply UbMhAMetaS.keeps_join; [|exact KF].
        apply keeps_but_upd; [apply keeps_but_refl | left; reflexivity]. }
      assert (M3W : forall a, 0 <= a < 2 ^ 64 -> M3 (Z_to_bv 64 a) <> M (Z_to_bv 64 a) -> (sp - AMSTK <= a < sp) \/ ctxV a \/ (cur <= a < cur + 4096)).
      { intros a Ha NE. unfold M3 in NE.
        destruct (decide (zfill (Z_to_bv 64 cur) (Z_to_bv 64 4096) M2 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a))) as [E0|NE0].
        - rewrite E0 in NE. left. pose proof (M2W a Ha NE). unfold AMSTK. lia.
        - right; right. exact (zfill_diffZ _ cur 4096 a ltac:(lia) ltac:(lia) ltac:(lia) Ha NE0). }
      apply (kfx_kat RSEGS F HL bi _ (kfx bi)); [|intros c' Hc'; exact Hc'].
      apply (UbMhAMetaM.UbMhAMetaT.am_tail st L X M mdl regs rom sp (kfx bi) HWF HREP HCNT H2 Hra Hsp Hok
               rF M3 mdl1 cur (UbMhAMetaR.c1_regions1 st bb len e) (s_brk st) ac (c_shift cx) (c_brk cx) (s_errno st) (fun a => cur <= a < cur + 4096)
               (clobI ++ ([1; 9; 10; 11; 12]%bv ++ ([2; 11; 13; 14; 17]%bv ++ ([10]%bv ++ [1; 2; 10; 11]%bv)))) Hfl Hac0).
      - exact F2.
      - kept_rw KF. gres. kept_rw KD. exact C9.
      - kept_rw KF. gres. kept_rw KD. kept_rw KC. exact G19.
      - kept_rw KF. gres. kept_rw KD. kept_rw KC. exact G18.
      - kept_rw KF. gres. kept_rw KD. kept_rw KC. kept_rw K1. reflexivity.
      - exact KT.
      - reflexivity.
      - rewrite MF2; exact Hh. - rewrite MF3; exact Hlz. - rewrite MF4; exact Hmat. - exact MF5. - exact MF6. - rewrite MF1; reflexivity.
      - intros a Ha NE. destruct (M3W a Ha NE) as [W|[W|W]]; [left; exact W | right; left; exact W | right; right; left; exact W].
      - (* [comment removed for export] *) pose proof (rc_errno st M (rp_statics st M HREP)) as C.
        eapply cell_agree; [unfold A_ERRNO, TPV; lia | unfold A_ERRNO, TPV; cbn; lia | | exact C]. intros y Hr Hy. cbn in Hy.
        destruct (decide (M3 (Z_to_bv 64 y) = M (Z_to_bv 64 y))) as [E|NE]; [exact E|]. exfalso.
        destruct (M3W y Hr NE) as [W|[W|W]]; unfold UbMhAMetaM.UbMhAMetaT.ctxV, ctx_avail_meta_area_count, ctx_avail_meta_areas, ctx_brk, CTX, AMSTK, A_ERRNO, TPV in *; [lia | lia | clear -W PI Hy; lia].
      - intros y Hy NE. exfalso. destruct (M3W y ltac:(unfold A_ERRNO, TPV in Hy; lia) NE) as [W|[W|W]];
          unfold UbMhAMetaM.UbMhAMetaT.ctxV, ctx_avail_meta_area_count, ctx_avail_meta_areas, ctx_brk, CTX, AMSTK, A_ERRNO, TPV in *; [lia | lia | clear -W PI Hy; lia].
      - left; reflexivity.
      - (* [comment removed for export] *) intros a Ha. split; [unfold HEAPLO; lia|]. split; [lia|]. split.
        + intros ar Har IN. destruct (UbMhAMetaR.c1_Hp_areas st L HWF Hac bb len e HR ar Har); unfold UbMhAMetaR.c1_p in *; lia.
        + intros t Ht Kt IN. pose proof (wg_kind st L t (wG_each st L (WF_groups st L HWF) t Ht)) as KD2. rewrite Kt in KD2. destruct KD2 as (_ & Hin & _).
          destruct (UbMhAMetaR.c1_other_apart st L HWF bb len e HR _ Hin ltac:(unfold UbMhAMetaR.c1_R; intros E; discriminate E)) as [DJ|DJ]; cbn in DJ; unfold g_map_end in IN; lia.
      - intros a Ha. left. exists (UbMhAMetaR.c1_R' bb len e). split; [apply (UbMhAMetaR.c1_regions1_In st bb len e); left; reflexivity|].
        unfold UbMhAMetaR.c1_R'. cbn. split; [intros x E; discriminate E | lia].
      - (* [comment removed for export] *) intros a Hd D. unfold M3. apply zfill_grows. apply M2G. exact D.
      - (* [comment removed for export] *) intros a Ha. unfold M3. apply zfill_inZ; lia.
      - (* [comment removed for export] *) unfold M3. eapply defined_grows; [apply zfill_grows|]. eapply defined_grows; [exact M2G | exact DEF].
      - (* [comment removed for export] *) unfold cell, M3, M2, mp_frame. rewrite rdn_zfill_outZ by (unfold ctx_avail_meta_area_count, CTX; cbn; lia).
        unfold ctx_avail_meta_area_count, CTX in *. rdn_peel1. exact Cac.
      - unfold cell, M3, M2, mp_frame. rewrite rdn_zfill_outZ by (unfold ctx_meta_alloc_shift, CTX; cbn; lia).
        unfold ctx_meta_alloc_shift, CTX in *. rdn_peel1. exact (rc_mas st M1 RC1).
      - unfold cell, M3, M2, mp_frame. rewrite rdn_zfill_outZ by (unfold ctx_brk, CTX; cbn; lia).
        unfold ctx_brk, CTX in *. rdn_peel1. exact (rc_brk st M1 RC1).
      - lia.
      - exact (UbMhAMetaR.c1_Hp st L HWF Hac bb len e HR).
      - exact (UbMhAMetaR.c1_Hp_img st L HWF Hac bb len e HR).
      - exact (UbMhAMetaR.c1_Hp_areas st L HWF Hac bb len e HR).
      - exact (UbMhAMetaR.c1_Hp_groups st L HWF Hac bb len e HR).
      - exact (HCNT Hfl Hac0).
      - exact (UbMhAMetaR.c1_HRgrp st bb len e).
      - exact (UbMhAMetaR.c1_HRsub st bb len e).
      - exact (UbMhAMetaR.c1_HRold st L HWF bb len e HR).
      - exact (UbMhAMetaR.c1_HRnew st L HWF bb len e HR).
      - exact (UbMhAMetaR.c1_Hcur' st L HWF bb len e HR).
      - exact (UbMhAMetaR.c1_Hsh' st L HWF Hac).
      - pose proof (wc_shacc st (WF_ctx st L HWF)) as SA. clear -SA Hac. lia.
      - exact (UbMhAMetaR.c1_Hbrk' st L HWF).
      - exact (UbMhAMetaR.c1_t_wf_regions st L HWF Hac bb len e HR).
      - exact (UbMhAMetaR.c1_t_wf_img st L HWF Hac bb len e HR).
      - rewrite MF1. pose proof (UbMhAMetaR.c1_t_ledger st L X (m_vmmaps mdl) HWF HLG Hac bb len e HR) as LG.
        unfold UbMhAMetaR.c1_vm1, UbMhAMetaR.c1_p in LG. unfold h1. rewrite !u_Z2bv by lia. exact LG.
      - rewrite (UbMhAMetaR.c1_RSUM st L HWF bb len e HR). lia.
      - rewrite (UbMhAMetaR.c1_len st L HWF bb len e HR). lia.
      - exact (UbMhAMetaR.c1_new_apart_X st X bb len e HR).
      - (* [comment removed for export] *)
        intros t Ht Kt. pose proof (wg_kind st L t (wG_each st L (WF_groups st L HWF) t Ht)) as KD2. rewrite Kt in KD2. destruct KD2 as (_ & Hin & _).
        destruct (UbMhAMetaR.c1_other_apart st L HWF bb len e HR _ Hin ltac:(unfold UbMhAMetaR.c1_R; intros E; discriminate E)) as [DJ|DJ]; cbn in DJ; unfold g_map_end; lia.
      - (* [comment removed for export] *)
        intros a n bs Ha Hn R. unfold M3, M2, mp_frame. rewrite rdn_zfill_outZ by lia. rdn_peel1. exact R.
    Qed.
  End ArmC1.

  (* [comment removed for export] *)
  Lemma errno12_some : forall (Mpre : mem) a, A_ERRNO <= a < A_ERRNO + 4 -> wbytes Mpre (Z_to_bv 64 A_ERRNO) errno12 (Z_to_bv 64 a) <> None.
  Proof using X st.
    intros Mpre a Ha. unfold errno12, A_ERRNO, TPV in *.
    rewrite UbMhAMetaM.UbMhAMetaT.wbytes_get_inside by (wd_lenlit; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia).
    rewrite !u_Z2bv by lia.
    match goal with |- nth_error _ (Z.to_nat ?d) <> None =>
      assert (E : d = 0 \/ d = 1 \/ d = 2 \/ d = 3) by lia;
      destruct E as [E|[E|[E|E]]]; rewrite E; cbn; discriminate end.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section ArmC2.
    Hypothesis Hfl : s_flist st = [].
    Hypothesis Hac0 : c_avail_cnt cx = 0.
    Hypothesis Hac : c_area_cnt cx = 0.
    Hypothesis HBU : s_brk st = BrkUntried.

    (* [comment removed for export] *)
    Section C2Fin.
      Variables (bo : bool) (B : Z) (gk : gkd) (rP : bvmap 5 word) (M4 M5 : mem) (mdl2 : Model) (eT : Z) (bigP : list reg).
      Hypothesis Hside : bo = true -> bi = true.
      Hypothesis HB : bv_unsigned (vm_brk (m_vmmaps mdl)) = B.
      Hypothesis Hce : B + 8192 <= CEIL.
      Hypothesis HRF : region_free (vm_reserved (m_vmmaps mdl) ++ vm_maps (m_vmmaps mdl)) (Z_to_bv 64 B) (Z_to_bv 64 8192) = true.
      (* [comment removed for export] *)
      Hypothesis P2 : getr rP 2 = Z_to_bv 64 (sp - 64).
      Hypothesis P9 : getr rP 9 = Z_to_bv 64 (B + 8192).
      Hypothesis P19 : getr rP 19 = Z_to_bv 64 MLOCK.
      Hypothesis P8 : getr rP 8 = Z_to_bv 64 4096.
      Hypothesis P18 : getr rP 18 = Z_to_bv 64 A_CANARY.
      Hypothesis P21 : getr rP 21 = getr regs 21.
      Hypothesis KP : keeps_but bigP regs rP.
      Hypothesis COVP : forallb (fun r => existsb (fun x => bv_eqb x r) AM_CLOB || existsb (fun x => bv_eqb x r) AM_SAVED)%bool (bigP ++ [8; 9]%bv) = true.
      (* [comment removed for export] *)
      Hypothesis Th : m_halted mdl2 = None.
      Hypothesis Tlz : m_vm_lazy mdl2 = [].
      Hypothesis Tmat : m_vm_materialized mdl2 = [].
      Hypothesis Tfs : m_fs mdl2 = m_fs mdl.
      Hypothesis Tfds : m_fds mdl2 = m_fds mdl.
      Hypothesis Tvm : m_vmmaps mdl2 = UbMhAMetaR.c2_vm2 (m_vmmaps mdl) B gk.
      (* [comment removed for export] *)
      Hypothesis M4W : forall x, 0 <= x < 2 ^ 64 -> M4 (Z_to_bv 64 x) <> M (Z_to_bv 64 x) -> (sp - AMSTK <= x < sp) \/ ctxV x \/ (B <= x < B + 8192).
      Hypothesis M4G : mem_grows M M4.
      Hypothesis M4D : defined M4 (sp - AMSTK) sp.
      Hypothesis M4Z : forall x, B <= x < B + 8192 -> M4 (Z_to_bv 64 x) = Some (Z_to_bv 8 0).
      Hypothesis M4sh : rdn RSEGS M4 (Z_to_bv 64 ctx_meta_alloc_shift) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (c_shift cx))).
      Hypothesis M4S : forall a n bs, sp - 56 <= a -> a + Z.of_nat n <= sp -> rdn RSEGS M1 (Z_to_bv 64 a) n = Some bs -> rdn RSEGS M4 (Z_to_bv 64 a) n = Some bs.
      (* [comment removed for export] *)
      Hypothesis H5W : forall x, 0 <= x < 2 ^ 64 -> M5 (Z_to_bv 64 x) <> M4 (Z_to_bv 64 x) ->
                         (sp - 144 <= x < sp - 128) \/ (A_ERRNO <= x < A_ERRNO + 4) \/ (B <= x < B + 4096).
      Hypothesis H5out : forall x, 0 <= x < 2 ^ 64 -> ~ (B <= x < B + 4096) -> ~ (sp - 144 <= x < sp - 128) -> ~ (A_ERRNO <= x < A_ERRNO + 4) ->
                           M5 (Z_to_bv 64 x) = M4 (Z_to_bv 64 x).
      Hypothesis H5E : cell M5 A_ERRNO 4 eT.
      Hypothesis HeT : eT = s_errno st \/ eT = 12.
      Hypothesis H5ED : forall a, A_ERRNO <= a < A_ERRNO + 4 -> M5 (Z_to_bv 64 a) <> M (Z_to_bv 64 a) -> M5 (Z_to_bv 64 a) <> None.
      Hypothesis H5D : defined M5 (sp - AMSTK) sp.

      #[local] Notation MT := (wbytes (wbytes M5 (Z_to_bv 64 ctx_brk) (word_to_le_bytes 8 (Z_to_bv 64 (B + 8192))))
                                      (Z_to_bv 64 ctx_avail_meta_area_count) (word_to_le_bytes 8 (Z_to_bv 64 1))).

      Lemma c2_fin : kfx bo (mkCfg (mkst rP (0x66df4%bv : word) M5 rom) mdl2).
      Proof using H5D H5ED HeT H5E H5out H5W M4S M4sh M4Z M4G M4W Tvm Tfds Tfs Tmat Tlz Th COVP KP P21 P18 P8 P19 P9 P2 HRF Hce HB Hside bigP eT M4 gk B HBU Hac Hac0 Hfl Hok Hsp Hra H2 HCNT XOK HLG HREP HWF HL bi sp regs mdl M X L st RN.
        pose proof Hsp' as [S1 S2]. ceil.
        pose proof (HCNT Hfl Hac0) as Hcnt.
        pose proof (UbMhAMetaR.c2_B_facts st X _ HLG HBU B HB) as (B1 & B2 & B3 & B4).
        pose proof (UbMhAMetaR.c2_apart st L X _ HWF HLG XOK HBU B HB Hce HRF) as [AP APX].
        pose proof (UbMhAMetaS.M1_REP st L X M regs sp HWF HREP Hsp) as REP1. pose proof (rp_ctx st M1 REP1) as RC1.
        (* [comment removed for export] *)
        destruct (amB3 rP rom M5 (B + 8192) ltac:(lia) P9 P19 P8 (UbMhAMetaM.ctx_sok M5)) as (rT & RUN6 & T9 & T8 & KT0).
        eapply (kfx_msteps RSEGS F HL); [exact Th | exact Tlz | exact RUN6 |].
        (* [comment removed for export] *)
        assert (MTW5 : forall x, 0 <= x < 2 ^ 64 -> MT (Z_to_bv 64 x) <> M5 (Z_to_bv 64 x) -> ctxV x).
        { intros x Hx NE. unfold UbMhAMetaM.UbMhAMetaT.ctxV, ctx_avail_meta_area_count, ctx_avail_meta_areas, ctx_brk, CTX in NE |- *. wdiff NE M5 x. }
        assert (MT5 : forall x, 0 <= x < 2 ^ 64 -> ~ ctxV x -> MT (Z_to_bv 64 x) = M5 (Z_to_bv 64 x)).
        { intros x Hx NC. destruct (decide (MT (Z_to_bv 64 x) = M5 (Z_to_bv 64 x))) as [E|NE]; [exact E|]. exfalso. exact (NC (MTW5 x Hx NE)). }
        assert (TW : forall x, 0 <= x < 2 ^ 64 -> MT (Z_to_bv 64 x) <> M (Z_to_bv 64 x) ->
                     (sp - AMSTK <= x < sp) \/ ctxV x \/ (B <= x < B + 8192) \/ (A_ERRNO <= x < A_ERRNO + 4)).
        { intros x Hx NE. destruct (decide (MT (Z_to_bv 64 x) = M5 (Z_to_bv 64 x))) as [E5|NE5]; [|right; left; exact (MTW5 x Hx NE5)].
          rewrite E5 in NE. destruct (decide (M5 (Z_to_bv 64 x) = M4 (Z_to_bv 64 x))) as [E4|NE4].
          - rewrite E4 in NE. destruct (M4W x Hx NE) as [W|[W|W]]; [left; exact W | right; left; exact W | right; right; left; exact W].
          - destruct (H5W x Hx NE4) as [W|[W|W]]; [left; unfold AMSTK; lia | right; right; right; exact W | right; right; left; lia]. }
        (* [comment removed for export] *)
        assert (RB5 : forall a k, 0 <= a -> a + Z.of_nat k < 2 ^ 64 ->
                      (forall x, a <= x < a + Z.of_nat k -> ~ (B <= x < B + 4096) /\ ~ (sp - 144 <= x < sp - 128) /\ ~ (A_ERRNO <= x < A_ERRNO + 4)) ->
                      rdn RSEGS M5 (Z_to_bv 64 a) k = rdn RSEGS M4 (Z_to_bv 64 a) k).
        { intros a k Ha Hk OUT. apply rdn_ext; [rewrite u_Z2bv by lia; lia|].
          intros x Hx. rewrite u_Z2bv in Hx by lia. pose proof (u64_range x) as XR. rewrite <- (Z_to_bv_u_eq' x (bv_unsigned x) eq_refl).
          destruct (OUT (bv_unsigned x) ltac:(lia)) as (O1 & O2 & O3). apply (H5out (bv_unsigned x) ltac:(lia) O1 O2 O3). }
        apply (kfx_kat RSEGS F HL bo _ (kfx bo)); [|intros c' Hc'; exact Hc'].
        apply (UbMhAMetaM.UbMhAMetaT.am_tail st L X M mdl regs rom sp (kfx bo) HWF HREP HCNT H2 Hra Hsp (fun c' Hc' => kfx_mono RSEGS F HL bi bo c' Hside (Hok c' Hc'))
                 rT MT mdl2 (B + 4096) (UbMhAMetaR.c2_regions2 st B gk) (UbMhAMetaR.c2_brk2 B gk) 1 (c_shift cx) (B + 8192) eT (fun x => B <= x < B + 8192)
                 (bigP ++ [8; 9]%bv) Hfl Hac0).
        - kept_rw KT0. exact P2.
        - rewrite T9. f_equal. lia.
        - kept_rw KT0. exact P19.
        - kept_rw KT0. exact P18.
        - kept_rw KT0. exact P21.
        - eapply UbMhAMetaS.keeps_join; [exact KP | exact KT0].
        - exact COVP.
        - exact Th. - exact Tlz. - exact Tmat. - exact Tfs. - exact Tfds.
        - rewrite Tvm. unfold UbMhAMetaR.c2_vm2, UbMhAMetaR.c2_vm1. destruct gk; reflexivity.
        - exact TW.
        - (* [comment removed for export] *) unfold cell in H5E |- *. rewrite <- H5E. unfold ctx_brk, ctx_avail_meta_area_count, CTX, A_ERRNO, TPV. do 2 rdn_peel1. reflexivity.
        - intros a Ha NE. rewrite (MT5 a ltac:(unfold A_ERRNO, TPV in Ha; lia) ltac:(unfold UbMhAMetaM.UbMhAMetaT.ctxV, ctx_avail_meta_area_count, ctx_avail_meta_areas, ctx_brk, CTX, A_ERRNO, TPV in *; lia)) in NE |- *.
          exact (H5ED a Ha NE).
        - exact HeT.
        - (* [comment removed for export] *) intros x Hx. split; [unfold HEAPLO; lia|]. split; [lia|]. split.
          + intros ar Har IN. destruct (area_in_region st L HWF ar Har) as (rr & Hrr & _ & Z1 & Z2). destruct (AP rr Hrr); lia.
          + intros t Ht Kt IN. pose proof (wg_kind st L t (wG_each st L (WF_groups st L HWF) t Ht)) as KD2. rewrite Kt in KD2. destruct KD2 as (_ & Hin & _).
            destruct (AP _ Hin) as [DJ|DJ]; cbn in DJ; unfold g_map_end in IN; lia.
        - (* [comment removed for export] *)
          intros x Hx. pose proof (UbMhAMetaR.c2_Rn_shape B gk) as SH. pose proof (UbMhAMetaR.c2_Rn_kind B gk) as RK.
          destruct (decide (rg_base (UbMhAMetaR.c2_Rn B gk) <= x)) as [IN|OUT].
          + left. exists (UbMhAMetaR.c2_Rn B gk). split; [left; reflexivity|]. split; [intros y E; rewrite RK in E; discriminate E|].
            destruct SH as [(E1 & E2 & _)|(E1 & E2 & _)]; rewrite E1 in IN |- *; rewrite E2; lia.
          + right. destruct SH as [(E1 & E2 & _)|(E1 & E2 & EG)]; [exfalso; rewrite E1 in OUT; lia|]. rewrite E1 in OUT.
            split; [unfold HEAPLO; lia|]. split; [right; lia|]. split.
            * intros r Hr. unfold UbMhAMetaR.c2_regions2 in Hr. destruct Hr as [<-|Hr]; [rewrite E1, E2; lia|]. destruct (AP r Hr); lia.
            * intros ea en INX Hea Hen Hce2 INa. destruct (APX _ INX) as (ea' & en' & EE & Y1 & Y2 & Y3 & Y4).
              pose proof (f_equal (fun e => bv_unsigned (Datatypes.fst e)) EE) as E3. pose proof (f_equal (fun e => bv_unsigned (Datatypes.snd e)) EE) as E4. cbn [Datatypes.fst Datatypes.snd] in E3, E4.
              unfold HEAPLO in Hea, Y1. rewrite !u_Z2bv in E3 by lia. rewrite !u_Z2bv in E4 by lia. lia.
        - (* [comment removed for export] *)
          intros x Hd D. pose proof (UbMhAMetaM.UbMhAMetaT.dfoot_rng st L X HWF x Hd) as XR. do 2 apply (wbytes_grows _ _ _ (Z_to_bv 64 x)).
          destruct (decide (M5 (Z_to_bv 64 x) = M (Z_to_bv 64 x))) as [E|NE]; [rewrite E; exact D|].
          destruct (decide (A_ERRNO <= x < A_ERRNO + 4)) as [IE|NIE]; [exact (H5ED x IE NE)|].
          assert (NH : ~ (B <= x < B + 4096)).
          { intros IN. destruct Hd as [Hd1|[Hd1|[(ar & Har & Ra)|(t & Ht & Kt & Rt)]]].
            - unfold A_ERRNO, TPV, HEAPLO in *. lia.
            - unfold CTX_END, CTX, HEAPLO in *. lia.
            - destruct (area_in_region st L HWF ar Har) as (rr & Hrr & _ & Z1 & Z2). destruct (AP rr Hrr); lia.
            - pose proof (wg_kind st L t (wG_each st L (WF_groups st L HWF) t Ht)) as KD2. rewrite Kt in KD2. destruct KD2 as (_ & Hin & _).
              destruct (AP _ Hin) as [DJ|DJ]; cbn in DJ; lia. }
          assert (NS : ~ (sp - 144 <= x < sp - 128)).
          { intros IN. destruct Hd as [Hd1|[Hd1|[(ar & Har & Ra)|(t & Ht & Kt & Rt)]]].
            - unfold A_ERRNO, TPV, HEAPLO in *. lia.
            - unfold CTX_END, CTX, HEAPLO in *. lia.
            - destruct (wa_rng st (WF_areas st L HWF) ar Har) as (_ & R1 & R2). lia.
            - destruct (group_range st L HWF t Ht) as [R _].
              pose proof (wg_kind st L t (wG_each st L (WF_groups st L HWF) t Ht)) as KD2. rewrite Kt in KD2. destruct KD2 as (_ & Hin & _).
              destruct (wr_rng st (WF_regions st L HWF) _ Hin) as (_ & R2 & _). cbn in R2. unfold g_map_end in Rt. lia. }
          rewrite (H5out x XR NH NS NIE). apply M4G. exact D.
        - (* [comment removed for export] *) intros x Hx. rewrite (MT5 x ltac:(lia) ltac:(unfold UbMhAMetaM.UbMhAMetaT.ctxV, ctx_avail_meta_area_count, ctx_avail_meta_areas, ctx_brk, CTX; lia)).
          rewrite (H5out x ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold A_ERRNO, TPV; lia)). apply M4Z. lia.
        - (* [comment removed for export] *) do 2 apply defined_wbytes. exact H5D.
        - unfold cell, ctx_brk, ctx_avail_meta_area_count, CTX. apply rdn_wbytes_hit8. zsimp; lia.
        - unfold cell, ctx_brk, ctx_avail_meta_area_count, ctx_meta_alloc_shift, CTX in *. do 2 rdn_peel1.
          lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ => rewrite (RB5 a 8%nat ltac:(lia) ltac:(cbn; lia) ltac:(unfold A_ERRNO, TPV; cbn; intros; lia)) end. exact M4sh.
        - unfold cell, ctx_brk, ctx_avail_meta_area_count, CTX. rdn_peel1. apply rdn_wbytes_hit8. zsimp; lia.
        - lia.
        - pose proof (UbMhAMetaR.c2_Hp st X _ HLG HBU B HB Hce) as HP. unfold UbMhAMetaR.c2_p in HP. exact HP.
        - pose proof (UbMhAMetaR.c2_Hp_img st X _ HLG HBU B HB) as HP. unfold UbMhAMetaR.c2_p in HP. exact HP.
        - pose proof (UbMhAMetaR.c2_Hp_areas st L X _ HWF HLG XOK HBU B HB Hce HRF) as HP. unfold UbMhAMetaR.c2_p in HP. exact HP.
        - pose proof (UbMhAMetaR.c2_Hp_groups st L X _ HWF HLG XOK HBU B HB Hce HRF) as HP. unfold UbMhAMetaR.c2_p in HP. exact HP.
        - exact Hcnt.
        - exact (UbMhAMetaR.c2_HRgrp st B gk).
        - exact (UbMhAMetaR.c2_HRsub st B gk).
        - exact (UbMhAMetaR.c2_HRold st L HWF HBU B gk).
        - pose proof (UbMhAMetaR.c2_HRnew st B gk) as HP. unfold UbMhAMetaR.c2_p in HP. exact HP.
        - intros HH. lia.
        - pose proof (UbMhAMetaR.c2_Hsh' st L HWF Hac) as HS. replace (1 - 1) with 0 by lia. exact HS.
        - pose proof (wc_shacc st (WF_ctx st L HWF)) as SA. clear -SA Hac. lia.
        - exact (UbMhAMetaR.c2_Hbrk' st X _ HLG HBU B HB Hce gk).
        - pose proof (UbMhAMetaR.c2_t_wf_regions st L X _ HWF HLG XOK HBU B HB Hce HRF gk) as WR.
          unfold UbMhAMetaR.c2_st2, UbMhAMetaR.c2_p in WR. replace (1 - 1) with 0 by lia. exact WR.
        - pose proof (UbMhAMetaR.c2_t_wf_img st L X _ HWF HLG HBU B HB gk) as WI.
          unfold UbMhAMetaR.c2_st2, UbMhAMetaR.c2_p in WI. replace (1 - 1) with 0 by lia. exact WI.
        - rewrite Tvm. pose proof (UbMhAMetaR.c2_t_ledger st L X _ HWF HLG XOK HBU B HB Hce HRF gk) as LG.
          unfold UbMhAMetaR.c2_st2, UbMhAMetaR.c2_p in LG. replace (1 - 1) with 0 by lia. exact LG.
        - pose proof (UbMhAMetaR.c2_RSUM st B gk). lia.
        - rewrite (UbMhAMetaR.c2_len st B gk). lia.
        - exact (UbMhAMetaR.c2_new_apart_X st L X _ HWF HLG XOK HBU B HB Hce HRF gk).
        - intros t Ht Kt. pose proof (wg_kind st L t (wG_each st L (WF_groups st L HWF) t Ht)) as KD2. rewrite Kt in KD2. destruct KD2 as (_ & Hin & _).
          destruct (AP _ Hin) as [DJ|DJ]; cbn in DJ; unfold g_map_end; lia.
        - intros a n bs Ha Hn R. unfold ctx_brk, ctx_avail_meta_area_count, CTX. do 2 rdn_peel1.
          rewrite (RB5 a n ltac:(lia) ltac:(lia) ltac:(unfold A_ERRNO, TPV; intros; lia)). exact (M4S a n bs Ha Hn R).
      Qed.
    End C2Fin.

    Lemma arm_C2 : forall bo r1, (bo = true -> bi = true) ->
      getr r1 2 = Z_to_bv 64 (sp - 64) -> getr r1 19 = Z_to_bv 64 MLOCK -> getr r1 8 = Z_to_bv 64 4096 ->
      getr r1 18 = Z_to_bv 64 A_CANARY -> keeps_but clobI regs r1 ->
      kfx bo (mkCfg (mkst r1 (0x66d1c%bv : word) M1 rom) mdl).
    Proof using HBU Hac Hac0 Hfl Hfail Hok DEF H4 Hsp Hra H2 HBUD HLEN HCNT Hmat Hlz Hh XOK HLG HREP HWF HL X L RN.
      intros bo r1 Hside G2 G19 G8 G18 K1. pose proof Hsp' as [S1 S2]. ceil.
      pose proof (HCNT Hfl Hac0) as Hcnt. pose proof (UbMhAMetaR.c4_sh_rng st L HWF Hcnt Hac 0) as [SH1 SH2].
      pose proof (UbMhAMetaS.M1_REP st L X M regs sp HWF HREP Hsp) as REP1. pose proof (rp_ctx st M1 REP1) as RC1.
      pose proof (rc_fmh st M1 RC1) as Cfh. rewrite (wc_fhead st (WF_ctx st L HWF)), Hfl in Cfh. cbn [head_of] in Cfh.
      pose proof (rc_amc st M1 RC1) as Ccnt. rewrite Hac0 in Ccnt.
      pose proof (rc_amac st M1 RC1) as Cac. rewrite Hac in Cac.
      pose proof (rc_brk st M1 RC1) as Cbrk. pose proof (wc_brk st (WF_ctx st L HWF)) as WB. rewrite HBU in WB. rewrite WB in Cbrk.
      pose proof (lx_brk st X _ HLG) as LB. rewrite HBU in LB. destruct LB as (LB1 & LB2 & LB3 & LB4).
      set (B := bv_unsigned (vm_brk (m_vmmaps mdl))).
      assert (HB : bv_unsigned (vm_brk (m_vmmaps mdl)) = B) by reflexivity.
      rewrite <- LB1 in LB2, LB3, LB4. rewrite HB in LB2, LB3, LB4.
      assert (EB : vm_brk (m_vmmaps mdl) = Z_to_bv 64 B) by (symmetry; apply Z_to_bv_u_eq'; exact HB).
      (* [comment removed for export] *)
      destruct (amB0 M1 Cfh Ccnt 0 0 Cac Cbrk r1 rom G19 G8 eq_refl eq_refl) as (rB & RUN1 & B10 & B17 & B11 & KB).
      eapply (kfx_msteps RSEGS F HL); [exact Hh | exact Hlz | exact RUN1 |].
      apply (kfx_brk_query RSEGS F HL bo rB (0x66dac%bv : word) M1 rom mdl W_66d58 Hh Hlz F_66d58 E_66d58 B17 B10).
      replace (v_addi (0x66dac%bv : word) 4) with (0x66db0%bv : word) by (apply bv_eq; reflexivity). rewrite EB.
      (* [comment removed for export] *)
      destruct (amB1 M1 (UbMhAMetaM.ctx_sok M1) (regupd rB 10 (Z_to_bv 64 B)) rom B ltac:(unfold HEAPLO; lia) ltac:(lia) LB2
                  ltac:(gres; kept_rw KB; exact G19) ltac:(gres; kept_rw KB; exact G8) ltac:(rewrite getr_same by (intros E; discriminate E); reflexivity) ltac:(gres; exact B11))
        as (rC & RUN2 & C10 & C9 & C17 & KC).
      eapply (kfx_msteps RSEGS F HL); [exact Hh | exact Hlz | exact RUN2 |].
      set (M2 := wbytes M1 (Z_to_bv 64 ctx_brk) (word_to_le_bytes 8 (Z_to_bv 64 B))).
      assert (M2W : forall x, 0 <= x < 2 ^ 64 -> M2 (Z_to_bv 64 x) <> M (Z_to_bv 64 x) -> (sp - 56 <= x < sp) \/ (ctx_brk <= x < ctx_brk + 8)).
      { intros x Hx NE. unfold M2 in NE.
        destruct (decide (M1 (Z_to_bv 64 x) = M (Z_to_bv 64 x))) as [E4|NE4].
        - rewrite <- E4 in NE. right. unfold ctx_brk, CTX in NE |- *. wdiff NE (UbMhAMetaS.M1 st M regs sp) x.
        - left. exact (UbMhAMetaS.M1_writes st X M regs sp Hsp x Hx NE4). }
      (* [comment removed for export] *)
      apply (kfx_brk_grow RSEGS F HL bo rC (0x66dd0%bv : word) M2 rom mdl W_66d7c 8192 Hh Hlz F_66d7c E_66d7c C17);
        rewrite ?HB; [unfold page_size; exact LB2 | reflexivity | lia | lia | lia | rewrite <- LB1, HB; lia | exact C10 | |].
      - (* [comment removed for export] *)
        replace (v_addi (0x66dd0%bv : word) 4) with (0x66dd4%bv : word) by (apply bv_eq; reflexivity). rewrite EB.
        eapply (kfx_msteps RSEGS F HL); [exact Hh | exact Hlz | exact (amB2r (regupd rC 10 (Z_to_bv 64 B)) rom M2 (B + 8192) B ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite getr_same by (intros E; discriminate E); reflexivity) ltac:(gres; exact C9)) |].
        assert (Cac2 : rdn RSEGS M2 (Z_to_bv 64 ctx_avail_meta_area_count) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))).
        { unfold M2, ctx_avail_meta_area_count, ctx_brk, CTX in *. rdn_peel1. exact Cac. }
        assert (Csh2 : rdn RSEGS M2 (Z_to_bv 64 ctx_meta_alloc_shift) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (c_shift cx)))).
        { unfold M2, ctx_meta_alloc_shift, ctx_brk, CTX in *. rdn_peel1. exact (rc_mas st M1 RC1). }
        destruct (amRef (regupd rC 10 (Z_to_bv 64 B)) rom M2 (c_shift cx) ltac:(lia) ltac:(gres; kept_rw KC; gres; kept_rw KB; exact G19) ltac:(gres; kept_rw KC; gres; kept_rw KB; exact G8) Cac2 Csh2 (UbMhAMetaM.ctx_sok M2))
          as (rM & RUN3 & R10 & R11 & R12 & R13 & R14 & R15 & R9 & R20 & R1 & KM).
        eapply (kfx_msteps RSEGS F HL); [exact Hh | exact Hlz | exact RUN3 |].
        set (Mm := wbytes M2 (Z_to_bv 64 ctx_brk) (word_to_le_bytes 8 (Z_to_bv 64 (2 ^ 64 - 1)))).
        apply (UbMhAMetaM.arm_MM st L X M mdl regs rom sp F bi HL HWF HREP HLG XOK Hh Hlz Hmat HCNT HLEN HBUD H2 Hra Hsp DEF Hok Hfail Hfl Hac0 Hac
                 rM Mm (clobI ++ ([9; 10; 11; 17]%bv ++ ([10]%bv ++ ([9; 10; 11; 12; 17]%bv ++ ([10]%bv ++ [1; 9; 10; 11; 12; 13; 14; 15; 20]%bv)))))).
        + kept_rw KM. gres. kept_rw KC. gres. kept_rw KB. exact G2.
        + exact R10. + unfold UbMhAMetaR.c4_N. exact R11. + exact R12. + exact R13. + exact R14. + exact R15. + exact R9. + exact R20. + exact R1.
        + kept_rw KM. gres. kept_rw KC. gres. kept_rw KB. exact G19.
        + kept_rw KM. gres. kept_rw KC. gres. kept_rw KB. exact G8.
        + kept_rw KM. gres. kept_rw KC. gres. kept_rw KB. exact G18.
        + kept_rw KM. gres. kept_rw KC. gres. kept_rw KB. kept_rw K1. reflexivity.
        + kept_rw KM. gres. kept_rw KC. gres. kept_rw KB. exact (UbMhAMetaM.x4_clobI regs H4 r1 K1).
        + eapply UbMhAMetaS.keeps_join; [exact K1|]. eapply UbMhAMetaS.keeps_join; [exact KB|]. eapply UbMhAMetaS.keeps_join; [apply keeps_but_upd; [apply keeps_but_refl | left; reflexivity]|].
          eapply UbMhAMetaS.keeps_join; [exact KC|]. eapply UbMhAMetaS.keeps_join; [apply keeps_but_upd; [apply keeps_but_refl | left; reflexivity] | exact KM].
        + reflexivity.
        + intros a Ha NE. unfold Mm in NE.
          destruct (decide (M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E4|NE4].
          * rewrite <- E4 in NE. right. unfold ctx_brk, CTX in NE |- *. wdiff NE M2 a.
          * exact (M2W a Ha NE4).
        + unfold cell, Mm, ctx_brk, CTX. apply rdn_wbytes_hit8. zsimp; lia.
        + unfold Mm, M2. eapply mem_grows_trans; [exact (UbMhAMetaS.M1_grows st M regs sp)|]. eapply mem_grows_trans; apply wbytes_grows.
        + intros a n bs Ha Hn R. unfold Mm, M2, ctx_brk, CTX. do 2 rdn_peel1. exact R.
        + unfold Mm, M2. do 2 apply defined_wbytes. exact (UbMhAMetaS.M1_def st M regs sp DEF).
      - (* [comment removed for export] *)
        intros GOK. replace (v_addi (0x66dd0%bv : word) 4) with (0x66dd4%bv : word) by (apply bv_eq; reflexivity).
        rewrite <- HB in GOK.
        pose proof (brk_grow_ok_facts mdl 8192 ltac:(lia) ltac:(rewrite HB; lia) ltac:(rewrite HB; lia) ltac:(rewrite HB; unfold page_size; exact LB2) ltac:(reflexivity) GOK) as (GF1 & GF2 & GF3).
        rewrite HB in GF1. rewrite EB in GF2 |- *. rewrite ?HB.
        assert (HRF : region_free (vm_reserved (m_vmmaps mdl) ++ vm_maps (m_vmmaps mdl)) (Z_to_bv 64 B) (Z_to_bv 64 8192) = true).
        { pose proof GF2 as RF12. unfold page_size in RF12. replace (8192 + 4096) with 12288 in RF12 by reflexivity.
          apply (UbMhAMetaM.UbMhAMetaT.region_free_shrink st X _ B 12288 B 8192); try lia. exact RF12. }
        assert (Hce : B + 8192 <= CEIL).
        { apply (grant_end_le_CEIL (m_vmmaps mdl) B 8192 (lx_top st X _ HLG)); try lia. rewrite Z.add_mod, LB2 by lia. reflexivity. }
        pose proof (UbMhAMetaR.c2_apart st L X _ HWF HLG XOK HBU B HB Hce HRF) as [AP APX].
        set (M3 := zfill (Z_to_bv 64 B) (Z_to_bv 64 8192) M2).
        set (mdl1 := with_vmmaps (brk_grow_vm (m_vmmaps mdl) 8192) mdl).
        pose proof (with_vmmaps_facts (brk_grow_vm (m_vmmaps mdl) 8192) mdl) as MF. change (with_vmmaps (brk_grow_vm (m_vmmaps mdl) 8192) mdl) with mdl1 in MF.
        destruct MF as (MF1 & MF2 & MF3 & MF4 & MF5 & MF6).
        assert (CB3 : rdn RSEGS M3 (Z_to_bv 64 ctx_brk) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 B))).
        { unfold M3, M2, ctx_brk, CTX in *. rewrite rdn_zfill_outZ by (cbn; lia). apply rdn_wbytes_hit8. zsimp; lia. }
        destruct (amB2g (regupd rC 10 (Z_to_bv 64 (B + 8192))) rom M3 (B + 8192) B ltac:(lia) ltac:(rewrite getr_same by (intros E; discriminate E); reflexivity)
                    ltac:(gres; exact C9) ltac:(gres; kept_rw KC; gres; kept_rw KB; exact G19) ltac:(gres; kept_rw KC; gres; kept_rw KB; exact G8) CB3)
          as (rG & RUN3 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15 & Y1 & KG).
        eapply (kfx_msteps RSEGS F HL); [rewrite MF2; exact Hh | rewrite MF3; exact Hlz | exact RUN3 |].
        (* [comment removed for export] *)
        assert (M3D : defined M3 (sp - AMSTK) sp).
        { unfold M3. eapply defined_grows; [apply zfill_grows|]. unfold M2. apply defined_wbytes. exact (UbMhAMetaS.M1_def st M regs sp DEF). }
        assert (SOK64 : store_ok RSEGS M3 (Z_to_bv 64 (sp - 64 - 64)) 64%nat = true).
        { eapply (store_ok_defined M3 (sp - AMSTK) sp); [exact M3D | unfold AMSTK; lia | unfold AMSTK; cbn; lia | unfold AMSTK; lia | lia]. }
        destruct (mmW1_50 M3 (sp - 64) B 4096 0 50 ltac:(lia) SOK64 ltac:(lia) rG rom eq_refl
                    ltac:(kept_rw KG; gres; kept_rw KC; gres; kept_rw KB; exact G2) Y10 Y11 Y12 Y13 Y14 Y15)
          as (rN & RUN4 & Q2 & Q17 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q16 & KN).
        eapply (kfx_msteps RSEGS F HL); [rewrite MF2; exact Hh | rewrite MF3; exact Hlz | exact RUN4 |].
        set (M4 := mm_frame M3 (sp - 64) (getr rG 1) (getr rG 8) (getr rG 9) (getr rG 18) (getr rG 19) (getr rG 20) (getr rG 21)).
        (* [comment removed for export] *)
        assert (M4W : forall x, 0 <= x < 2 ^ 64 -> M4 (Z_to_bv 64 x) <> M (Z_to_bv 64 x) -> (sp - AMSTK <= x < sp) \/ ctxV x \/ (B <= x < B + 8192)).
        { intros x Hx NE. unfold M4, mm_frame in NE.
          destruct (decide (M3 (Z_to_bv 64 x) = M (Z_to_bv 64 x))) as [E6|NE6].
          - rewrite <- E6 in NE. left. unfold AMSTK. wdiff NE M3 x.
          - unfold M3 in NE6. destruct (decide (zfill (Z_to_bv 64 B) (Z_to_bv 64 8192) M2 (Z_to_bv 64 x) = M2 (Z_to_bv 64 x))) as [E7|NE7].
            + rewrite E7 in NE6. destruct (M2W x Hx NE6) as [W|W]; [left; unfold AMSTK; lia | right; left; unfold UbMhAMetaM.UbMhAMetaT.ctxV; right; right; exact W].
            + right; right. exact (zfill_diffZ _ B 8192 x ltac:(lia) ltac:(lia) ltac:(lia) Hx NE7). }
        assert (M4G : mem_grows M M4).
        { unfold M4, mm_frame. do 7 (eapply mem_grows_trans; [|apply wbytes_grows]). unfold M3. eapply mem_grows_trans; [|apply zfill_grows].
          unfold M2. eapply mem_grows_trans; [exact (UbMhAMetaS.M1_grows st M regs sp) | apply wbytes_grows]. }
        assert (M4D : defined M4 (sp - AMSTK) sp) by (unfold M4, mm_frame; repeat apply defined_wbytes; exact M3D).
        assert (M4Z : forall x, B <= x < B + 8192 -> M4 (Z_to_bv 64 x) = Some (Z_to_bv 8 0)).
        { intros x Hx. unfold M4, mm_frame. rewrite !wbytes_outZ by (wd_lenlit; rewrite ?length_N_to_le_bytes; cbn; lia). unfold M3. apply zfill_inZ; lia. }
        assert (M4sh : rdn RSEGS M4 (Z_to_bv 64 ctx_meta_alloc_shift) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (c_shift cx)))).
        { unfold M4, mm_frame, M3, M2, ctx_meta_alloc_shift, ctx_brk, CTX in *. do 7 rdn_peel1. rewrite rdn_zfill_outZ by (cbn; lia). rdn_peel1. exact (rc_mas st M1 RC1). }
        assert (M4S : forall a n bs, sp - 56 <= a -> a + Z.of_nat n <= sp -> rdn RSEGS M1 (Z_to_bv 64 a) n = Some bs -> rdn RSEGS M4 (Z_to_bv 64 a) n = Some bs).
        { intros a n bs Ha Hn R. unfold M4, mm_frame, M3, M2, ctx_brk, CTX. do 7 rdn_peel1. rewrite rdn_zfill_outZ by lia. rdn_peel1. exact R. }
        assert (M4E : cell M4 A_ERRNO 4 (s_errno st)).
        { pose proof (rc_errno st M (rp_statics st M HREP)) as C.
          eapply cell_agree; [unfold A_ERRNO, TPV; lia | unfold A_ERRNO, TPV; cbn; lia | | exact C]. intros y Hr Hy. cbn in Hy.
          destruct (decide (M4 (Z_to_bv 64 y) = M (Z_to_bv 64 y))) as [E|NE]; [exact E|]. exfalso.
          destruct (M4W y Hr NE) as [W|[W|W]]; unfold UbMhAMetaM.UbMhAMetaT.ctxV, ctx_avail_meta_area_count, ctx_avail_meta_areas, ctx_brk, CTX, AMSTK, A_ERRNO, TPV in *; lia. }
        assert (STK4 : forall d v, rdn RSEGS M4 (Z_to_bv 64 (sp - 64 - d)) 8%nat = Some (word_to_le_bytes 8 v) ->
                       forall Mx : mem, (forall y, sp - 128 <= y < sp - 64 -> Mx (Z_to_bv 64 y) = M4 (Z_to_bv 64 y)) -> 8 <= d <= 64 ->
                       rdn RSEGS Mx (Z_to_bv 64 (sp - 64 - d)) 8%nat = Some (word_to_le_bytes 8 v)).
        { intros d v R Mx AG Hd. rewrite <- R. apply rdn_ext; [rewrite u_Z2bv by lia; lia|].
          intros x Hx. rewrite u_Z2bv in Hx by lia. pose proof (u64_range x) as Xr. rewrite <- (Z_to_bv_u_eq' x (bv_unsigned x) eq_refl). apply AG. lia. }
        assert (F8 : rdn RSEGS M4 (Z_to_bv 64 (sp - 64 - 8)) 8%nat = Some (word_to_le_bytes 8 (getr rG 1))) by (unfold M4, mm_frame; rdn_solve).
        assert (F16 : rdn RSEGS M4 (Z_to_bv 64 (sp - 64 - 16)) 8%nat = Some (word_to_le_bytes 8 (getr rG 8))) by (unfold M4, mm_frame; rdn_solve).
        assert (F24 : rdn RSEGS M4 (Z_to_bv 64 (sp - 64 - 24)) 8%nat = Some (word_to_le_bytes 8 (getr rG 9))) by (unfold M4, mm_frame; rdn_solve).
        assert (F32 : rdn RSEGS M4 (Z_to_bv 64 (sp - 64 - 32)) 8%nat = Some (word_to_le_bytes 8 (getr rG 18))) by (unfold M4, mm_frame; rdn_solve).
        assert (F40 : rdn RSEGS M4 (Z_to_bv 64 (sp - 64 - 40)) 8%nat = Some (word_to_le_bytes 8 (getr rG 19))) by (unfold M4, mm_frame; rdn_solve).
        assert (F48 : rdn RSEGS M4 (Z_to_bv 64 (sp - 64 - 48)) 8%nat = Some (word_to_le_bytes 8 (getr rG 20))) by (unfold M4, mm_frame; rdn_solve).
        assert (F56 : rdn RSEGS M4 (Z_to_bv 64 (sp - 64 - 56)) 8%nat = Some (word_to_le_bytes 8 (getr rG 21))) by (unfold M4, mm_frame; rdn_solve).
        (* [comment removed for export] *)
        assert (RA : ret_ok (getr rG 1)) by (rewrite Y1; apply ret_ok_even; reflexivity).
        assert (X4 : getr rN 4 = Z_to_bv 64 TPV) by (kept_rw KN; kept_rw KG; gres; kept_rw KC; gres; kept_rw KB; exact (UbMhAMetaM.x4_clobI regs H4 r1 K1)).
        assert (G9v : getr rG 9 = Z_to_bv 64 (B + 8192)) by (kept_rw KG; gres; exact C9).
        assert (G19v : getr rG 19 = Z_to_bv 64 MLOCK) by (kept_rw KG; gres; kept_rw KC; gres; kept_rw KB; exact G19).
        assert (G8v : getr rG 8 = Z_to_bv 64 4096) by (kept_rw KG; gres; kept_rw KC; gres; kept_rw KB; exact G8).
        assert (G18v : getr rG 18 = Z_to_bv 64 A_CANARY) by (kept_rw KG; gres; kept_rw KC; gres; kept_rw KB; exact G18).
        assert (G21v : getr rG 21 = getr regs 21) by (kept_rw KG; gres; kept_rw KC; gres; kept_rw KB; kept_rw K1; reflexivity).
        set (bigG := clobI ++ ([9; 10; 11; 17]%bv ++ ([10]%bv ++ ([9; 10; 11; 12; 17]%bv ++ ([10]%bv ++ ([1; 10; 11; 12; 13; 14; 15]%bv ++ (clobMM1 ++ [1; 21]%bv))))))).
        assert (KGall : keeps_but bigG regs rN).
        { eapply UbMhAMetaS.keeps_join; [exact K1|]. eapply UbMhAMetaS.keeps_join; [exact KB|]. eapply UbMhAMetaS.keeps_join; [apply keeps_but_upd; [apply keeps_but_refl | left; reflexivity]|].
          eapply UbMhAMetaS.keeps_join; [exact KC|]. eapply UbMhAMetaS.keeps_join; [apply keeps_but_upd; [apply keeps_but_refl | left; reflexivity]|].
          eapply UbMhAMetaS.keeps_join; [exact KG | exact KN]. }
        (* [comment removed for export] *)
        apply (kfx_mmap_fixed RSEGS F HL bo rN (0x683ac%bv : word) M4 rom mdl1 W_68358 (Z_to_bv 64 B) 4096
                 ltac:(rewrite MF2; exact Hh) ltac:(rewrite MF3; exact Hlz) ltac:(rewrite MF4; exact Hmat) F_68358 E_68358 Q17 Q10
                 ltac:(unfold page_size; rewrite u_Z2bv by lia; exact LB2) ltac:(rewrite u_Z2bv by lia; lia) Q11 ltac:(lia)
                 ltac:(rewrite pru_4096, u_Z2bv by lia; change (alloc_top (m_vmmaps mdl1)) with (alloc_top (brk_grow_vm (m_vmmaps mdl) 8192)); unfold alloc_top, brk_grow_vm in *; cbn [vm_init_sp]; lia)
                 Q12 Q13 Q15).
        { rewrite pru_4096, MF1. unfold brk_grow_vm. cbn [vm_reserved].
          pose proof GF2 as RF. rewrite region_free_app in RF. apply andb_true_iff in RF. destruct RF as [RF _].
          apply (UbMhAMetaM.UbMhAMetaT.region_free_shrink st X _ B 12288 B 4096); try lia. unfold page_size in RF. replace (8192 + 4096) with 12288 in RF by reflexivity. exact RF. }
        { rewrite pru_4096, MF1. unfold brk_grow_vm. cbn [vm_maps]. rewrite EB. apply map_contains_head; rewrite !u_Z2bv by lia; lia. }
        + (* [comment removed for export] *)
          intros e He. unfold mmfx_fail. rewrite (mmap_errno_is e He). replace (v_addi (0x683ac%bv : word) 4) with (0x683b0%bv : word) by (apply bv_eq; reflexivity).
          assert (SOK16 : store_ok RSEGS M4 (Z_to_bv 64 (sp - 64 - 80)) 16%nat = true).
          { eapply (store_ok_defined M4 (sp - AMSTK) sp); [exact M4D | unfold AMSTK; lia | unfold AMSTK; cbn; lia | unfold AMSTK; lia | lia]. }
          destruct (mmW2f M4 (sp - 64) B ltac:(unfold A_ERRNO, TPV; lia) SOK16 (UbMhAMetaM.errno_sok M4) ltac:(lia)
                      (regupd rN 10 (Z_to_bv 64 (2 ^ 64 - 12))) rom (getr rG 1) (getr rG 8) (getr rG 9) (getr rG 18) (getr rG 19) (getr rG 20) (getr rG 21)
                      RA ltac:(gres; exact Q2) ltac:(rewrite getr_same by (intros E; discriminate E); reflexivity) ltac:(gres; exact Q16) ltac:(gres; exact X4)
                      (STK4 8 _ F8 M4 ltac:(intros; reflexivity) ltac:(lia)) (STK4 16 _ F16 M4 ltac:(intros; reflexivity) ltac:(lia))
                      (STK4 24 _ F24 M4 ltac:(intros; reflexivity) ltac:(lia)) (STK4 32 _ F32 M4 ltac:(intros; reflexivity) ltac:(lia))
                      (STK4 40 _ F40 M4 ltac:(intros; reflexivity) ltac:(lia)) (STK4 48 _ F48 M4 ltac:(intros; reflexivity) ltac:(lia))
                      (STK4 56 _ F56 M4 ltac:(intros; reflexivity) ltac:(lia)))
            as (rP & RUN5 & P2 & P10 & P1 & P8 & P9 & P18 & P19 & P20 & P21 & KP).
          eapply (kfx_msteps RSEGS F HL); [rewrite MF2; exact Hh | rewrite MF3; exact Hlz | exact RUN5 |].
          rewrite Y1. replace (Z_to_bv 64 421364) with (0x66df4%bv : word) by (apply bv_eq; reflexivity).
          set (Mpre := wbytes (wbytes M4 (Z_to_bv 64 (sp - 64 - 72)) (word_to_le_bytes 8 (Z_to_bv 64 0x683d0)))
                              (Z_to_bv 64 (sp - 64 - 80)) (word_to_le_bytes 8 (getr (regupd rN 10 (Z_to_bv 64 (2 ^ 64 - 12))) 8))).
          assert (EM5 : mm_ffail M4 (sp - 64) (getr (regupd rN 10 (Z_to_bv 64 (2 ^ 64 - 12))) 8) = wbytes Mpre (Z_to_bv 64 A_ERRNO) errno12) by reflexivity.
          rewrite EM5. pose proof (UbMhAMetaM.errno_write_intro st X Mpre) as [EW1 EW2].
          assert (MpreW : forall x, 0 <= x < 2 ^ 64 -> Mpre (Z_to_bv 64 x) <> M4 (Z_to_bv 64 x) -> sp - 144 <= x < sp - 128).
          { intros x Hx NE. unfold Mpre in NE. wdiff NE M4 x. }
          apply (c2_fin bo B GPlain rP M4 (wbytes Mpre (Z_to_bv 64 A_ERRNO) errno12) mdl1 12
                   (bigG ++ ([10]%bv ++ [1; 2; 8; 9; 10; 11; 18; 19; 20; 21]%bv))
                   Hside HB Hce HRF).
          * exact P2. * rewrite P9. exact G9v. * rewrite P19. exact G19v. * rewrite P8. exact G8v. * rewrite P18. exact G18v. * rewrite P21. exact G21v.
          * eapply UbMhAMetaS.keeps_join; [exact KGall|]. eapply UbMhAMetaS.keeps_join; [apply keeps_but_upd; [apply keeps_but_refl | left; reflexivity] | exact KP].
          * reflexivity.
          * rewrite MF2; exact Hh. * rewrite MF3; exact Hlz. * rewrite MF4; exact Hmat. * exact MF5. * exact MF6.
          * rewrite MF1. unfold brk_grow_vm, UbMhAMetaR.c2_vm2, UbMhAMetaR.c2_vm1. rewrite ?HB. reflexivity.
          * exact M4W. * exact M4G. * exact M4Z. * exact M4sh. * exact M4S.
          * intros x Hx NE. destruct (decide (wbytes Mpre (Z_to_bv 64 A_ERRNO) errno12 (Z_to_bv 64 x) = Mpre (Z_to_bv 64 x))) as [E|NE1].
            -- rewrite E in NE. left. exact (MpreW x Hx NE).
            -- right; left. pose proof (EW2 (Z_to_bv 64 x) NE1) as [R _]. rewrite u_Z2bv in R by lia. exact R.
          * intros x Hx O1 O2 O3. unfold Mpre, errno12, A_ERRNO, TPV in *. rewrite !wbytes_outZ by (wd_lenlit; rewrite ?length_N_to_le_bytes; cbn; lia). reflexivity.
          * exact EW1.
          * right; reflexivity.
          * intros a Ha _. exact (errno12_some Mpre a Ha).
          * unfold Mpre. do 3 apply defined_wbytes. exact M4D.
        + (* [comment removed for export] *)
          unfold mmfx_ok. cbv zeta. rewrite ?pru_4096. replace (v_addi (0x683ac%bv : word) 4) with (0x683b0%bv : word) by (apply bv_eq; reflexivity).
          set (M5 := unfill (Z_to_bv 64 B) (Z_to_bv 64 4096) M4). unfold fixed_noaccess_model.
          lazymatch goal with |- kfx _ (mkCfg _ (with_vmmaps ?hh ?mm)) => pose proof (with_vmmaps_facts hh mm) as MG; set (mdl2 := with_vmmaps hh mm) in MG |- * end.
          destruct MG as (MG1 & MG2 & MG3 & MG4 & MG5 & MG6).
          assert (AG5 : forall y, sp - 128 <= y < sp - 64 -> M5 (Z_to_bv 64 y) = M4 (Z_to_bv 64 y)) by (intros y Hy; unfold M5; apply unfill_outZ; lia).
          destruct (mmW2 (sp - 64) B ltac:(lia) ltac:(lia) (regupd rN 10 (Z_to_bv 64 B)) rom M5 B
                      (getr rG 1) (getr rG 8) (getr rG 9) (getr rG 18) (getr rG 19) (getr rG 20) (getr rG 21)
                      ltac:(lia) ltac:(left; lia) RA ltac:(gres; exact Q2) ltac:(rewrite getr_same by (intros E; discriminate E); reflexivity) ltac:(gres; exact Q16)
                      (STK4 8 _ F8 M5 AG5 ltac:(lia)) (STK4 16 _ F16 M5 AG5 ltac:(lia)) (STK4 24 _ F24 M5 AG5 ltac:(lia)) (STK4 32 _ F32 M5 AG5 ltac:(lia))
                      (STK4 40 _ F40 M5 AG5 ltac:(lia)) (STK4 48 _ F48 M5 AG5 ltac:(lia)) (STK4 56 _ F56 M5 AG5 ltac:(lia)))
            as (rP & RUN5 & P2 & P10 & P1 & P8 & P9 & P18 & P19 & P20 & P21 & KP).
          eapply (kfx_msteps RSEGS F HL); [rewrite MG2, MF2; exact Hh | rewrite MG3, MF3; exact Hlz | exact RUN5 |].
          rewrite Y1. replace (Z_to_bv 64 421364) with (0x66df4%bv : word) by (apply bv_eq; reflexivity).
          apply (c2_fin bo B GNoAcc rP M4 M5 mdl2 (s_errno st)
                   (bigG ++ ([10]%bv ++ [1; 2; 8; 9; 11; 18; 19; 20; 21]%bv))
                   Hside HB Hce HRF).
          * exact P2. * rewrite P9. exact G9v. * rewrite P19. exact G19v. * rewrite P8. exact G8v. * rewrite P18. exact G18v. * rewrite P21. exact G21v.
          * eapply UbMhAMetaS.keeps_join; [exact KGall|]. eapply UbMhAMetaS.keeps_join; [apply keeps_but_upd; [apply keeps_but_refl | left; reflexivity] | exact KP].
          * reflexivity.
          * rewrite MG2, MF2; exact Hh. * rewrite MG3, MF3; exact Hlz. * rewrite MG4, MF4; exact Hmat. * rewrite MG5, MF5; reflexivity. * rewrite MG6, MF6; reflexivity.
          * rewrite MG1, MF1. unfold brk_grow_vm, UbMhAMetaR.c2_vm2. cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp].
            rewrite ?pru_4096. rewrite !u_Z2bv by lia. rewrite ?HB. reflexivity.
          * exact M4W. * exact M4G. * exact M4Z. * exact M4sh. * exact M4S.
          * intros x Hx NE. right; right. exact (unfill_diffZ _ B 4096 x ltac:(lia) ltac:(lia) ltac:(lia) Hx NE).
          * intros x Hx O1 O2 O3. unfold M5. apply unfill_outZ; lia.
          * unfold cell, M5. unfold A_ERRNO, TPV in *. rewrite rdn_unfill_outZ by (cbn; lia). exact M4E.
          * left; reflexivity.
          * intros a Ha NE. exfalso. apply NE. unfold M5. unfold A_ERRNO, TPV in *. rewrite unfill_outZ by lia.
            destruct (decide (M4 (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E5|NE5]; [exact E5 | exfalso].
            destruct (M4W a ltac:(lia) NE5) as [W|[W|W]]; unfold UbMhAMetaM.UbMhAMetaT.ctxV, ctx_avail_meta_area_count, ctx_avail_meta_areas, ctx_brk, CTX, AMSTK in *; lia.
          * intros y Hy. unfold M5. rewrite unfill_outZ by (unfold AMSTK in Hy; lia). exact (M4D y Hy).
        + (* [comment removed for export] *)
          intros e He. unfold mmfx_gone. cbv zeta. rewrite ?pru_4096. rewrite (mmap_errno_is e He). replace (v_addi (0x683ac%bv : word) 4) with (0x683b0%bv : word) by (apply bv_eq; reflexivity).
          set (M5 := unfill (Z_to_bv 64 B) (Z_to_bv 64 4096) M4). unfold fixed_destroyed_model.
          lazymatch goal with |- kfx _ (mkCfg _ (with_vmmaps ?hh ?mm)) => pose proof (with_vmmaps_facts hh mm) as MG; set (mdl2 := with_vmmaps hh mm) in MG |- * end.
          destruct MG as (MG1 & MG2 & MG3 & MG4 & MG5 & MG6).
          assert (AG5 : forall y, sp - 128 <= y < sp - 64 -> M5 (Z_to_bv 64 y) = M4 (Z_to_bv 64 y)) by (intros y Hy; unfold M5; apply unfill_outZ; lia).
          assert (M5D : defined M5 (sp - AMSTK) sp) by (intros y Hy; unfold M5; rewrite unfill_outZ by (unfold AMSTK in Hy; lia); exact (M4D y Hy)).
          assert (SOK16 : store_ok RSEGS M5 (Z_to_bv 64 (sp - 64 - 80)) 16%nat = true).
          { eapply (store_ok_defined M5 (sp - AMSTK) sp); [exact M5D | unfold AMSTK; lia | unfold AMSTK; cbn; lia | unfold AMSTK; lia | lia]. }
          destruct (mmW2f M5 (sp - 64) B ltac:(unfold A_ERRNO, TPV; lia) SOK16 (UbMhAMetaM.errno_sok M5) ltac:(lia)
                      (regupd rN 10 (Z_to_bv 64 (2 ^ 64 - 12))) rom (getr rG 1) (getr rG 8) (getr rG 9) (getr rG 18) (getr rG 19) (getr rG 20) (getr rG 21)
                      RA ltac:(gres; exact Q2) ltac:(rewrite getr_same by (intros E; discriminate E); reflexivity) ltac:(gres; exact Q16) ltac:(gres; exact X4)
                      (STK4 8 _ F8 M5 AG5 ltac:(lia)) (STK4 16 _ F16 M5 AG5 ltac:(lia)) (STK4 24 _ F24 M5 AG5 ltac:(lia)) (STK4 32 _ F32 M5 AG5 ltac:(lia))
                      (STK4 40 _ F40 M5 AG5 ltac:(lia)) (STK4 48 _ F48 M5 AG5 ltac:(lia)) (STK4 56 _ F56 M5 AG5 ltac:(lia)))
            as (rP & RUN5 & P2 & P10 & P1 & P8 & P9 & P18 & P19 & P20 & P21 & KP).
          eapply (kfx_msteps RSEGS F HL); [rewrite MG2, MF2; exact Hh | rewrite MG3, MF3; exact Hlz | exact RUN5 |].
          rewrite Y1. replace (Z_to_bv 64 421364) with (0x66df4%bv : word) by (apply bv_eq; reflexivity).
          set (Mpre := wbytes (wbytes M5 (Z_to_bv 64 (sp - 64 - 72)) (word_to_le_bytes 8 (Z_to_bv 64 0x683d0)))
                              (Z_to_bv 64 (sp - 64 - 80)) (word_to_le_bytes 8 (getr (regupd rN 10 (Z_to_bv 64 (2 ^ 64 - 12))) 8))).
          assert (EM5 : mm_ffail M5 (sp - 64) (getr (regupd rN 10 (Z_to_bv 64 (2 ^ 64 - 12))) 8) = wbytes Mpre (Z_to_bv 64 A_ERRNO) errno12) by reflexivity.
          rewrite EM5. pose proof (UbMhAMetaM.errno_write_intro st X Mpre) as [EW1 EW2].
          assert (MpreW : forall x, 0 <= x < 2 ^ 64 -> Mpre (Z_to_bv 64 x) <> M4 (Z_to_bv 64 x) -> (sp - 144 <= x < sp - 128) \/ (B <= x < B + 4096)).
          { intros x Hx NE. unfold Mpre in NE. destruct (decide (M5 (Z_to_bv 64 x) = M4 (Z_to_bv 64 x))) as [E5|NE5].
            - rewrite <- E5 in NE. left. wdiff NE M5 x.
            - right. exact (unfill_diffZ _ B 4096 x ltac:(lia) ltac:(lia) ltac:(lia) Hx NE5). }
          apply (c2_fin bo B GGone rP M4 (wbytes Mpre (Z_to_bv 64 A_ERRNO) errno12) mdl2 12
                   (bigG ++ ([10]%bv ++ [1; 2; 8; 9; 10; 11; 18; 19; 20; 21]%bv))
                   Hside HB Hce HRF).
          * exact P2. * rewrite P9. exact G9v. * rewrite P19. exact G19v. * rewrite P8. exact G8v. * rewrite P18. exact G18v. * rewrite P21. exact G21v.
          * eapply UbMhAMetaS.keeps_join; [exact KGall|]. eapply UbMhAMetaS.keeps_join; [apply keeps_but_upd; [apply keeps_but_refl | left; reflexivity] | exact KP].
          * reflexivity.
          * rewrite MG2, MF2; exact Hh. * rewrite MG3, MF3; exact Hlz. * rewrite MG4, MF4; exact Hmat. * rewrite MG5, MF5; reflexivity. * rewrite MG6, MF6; reflexivity.
          * rewrite MG1. unfold mmap_fixed_destroyed_next. rewrite MF1. unfold brk_grow_vm, UbMhAMetaR.c2_vm2.
            cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp].
            rewrite ?pru_4096. rewrite !u_Z2bv by lia. rewrite ?HB, ?EB. reflexivity.
          * exact M4W. * exact M4G. * exact M4Z. * exact M4sh. * exact M4S.
          * intros x Hx NE. destruct (decide (wbytes Mpre (Z_to_bv 64 A_ERRNO) errno12 (Z_to_bv 64 x) = Mpre (Z_to_bv 64 x))) as [E|NE1].
            -- rewrite E in NE. destruct (MpreW x Hx NE); [left | right; right]; assumption.
            -- right; left. pose proof (EW2 (Z_to_bv 64 x) NE1) as [R _]. rewrite u_Z2bv in R by lia. exact R.
          * intros x Hx O1 O2 O3. unfold Mpre, errno12, A_ERRNO, TPV in *. rewrite !wbytes_outZ by (wd_lenlit; rewrite ?length_N_to_le_bytes; cbn; lia). unfold M5. apply unfill_outZ; lia.
          * exact EW1.
          * right; reflexivity.
          * intros a Ha _. exact (errno12_some Mpre a Ha).
          * unfold Mpre. do 3 apply defined_wbytes. exact M5D.
    Qed.
  End ArmC2.
End AMC.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem alloc_meta_run3 `{RN : mh_run} `{fx : FPState} : AM_SPEC3.
Proof.
  intros F bi bo st L X M mdl regs rom sp HL Hside HWF HREP HLG XOK Hh Hlz Hmat HCNT HLEN HBUD H2 Hra Hsplo Hsphi H4 DEF Hok Hfail.
  assert (Hsp : CEIL + AMSTK <= sp /\ sp < 2 ^ 64) by (split; assumption).
  assert (Hok' : forall c', UbMhAMetaS.am_post st L X sp regs M mdl rom c' -> kfx F bi c') by (intros c' Hc'; exact (Hok c' (UbMhAMetaS.am_post_ok _ _ _ _ _ _ _ _ _ Hc'))).
  assert (HQ : forall c', UbMhAMetaS.am_post st L X sp regs M mdl rom c' -> kfx F bo c') by (intros c' Hc'; exact (kfx_mono RSEGS F HL bi bo c' Hside (Hok' c' Hc'))).
  unfold AM_ENTRY. replace (Z_to_bv 64 420968) with (0x66c68%bv : word) by (apply bv_eq; reflexivity).
  apply (kfx_kat RSEGS F HL bo _ (kfx F bo)); [|intros c' Hc'; exact Hc'].
  apply (UbMhAMetaS.am_head st X M mdl regs rom sp (kfx F bo) HREP Hh Hlz H2 Hsp DEF (fun _ => True)).
  intros r1 G2 G19 G8 G18 K1.
  destruct (list_eq_dec Z.eq_dec (s_flist st) []) as [Efl|Hnn].
  - destruct (Z_lt_le_dec 0 (c_avail_cnt (s_ctx st))) as [Hcnt|Hcnt0].
    + apply (UbMhAMetaS.arm_B st L X M mdl regs rom sp (kfx F bo) HWF HREP HLG Hh Hlz Hmat H2 Hra Hsp DEF HQ Efl ltac:(lia) r1 G2 G19 G8 G18 K1).
    + pose proof (wc_acnt st (WF_ctx st L HWF)) as AC.
      assert (Hac0 : c_avail_cnt (s_ctx st) = 0) by lia.
      apply kat_refl.
      destruct (Z_lt_le_dec 0 (c_area_cnt (s_ctx st))) as [Hac|Hacz].
      * apply (arm_C1 st L X M mdl regs rom sp F bi HL HWF HREP HLG Hh Hlz Hmat HCNT HBUD H2 Hra Hsp H4 DEF Hok' Hfail Efl Hac0 ltac:(lia) bo r1 G2 G19 G8 G18 K1).
      * pose proof (wc_areacnt st (WF_ctx st L HWF)) as ARC. assert (Hac : c_area_cnt (s_ctx st) = 0) by lia.
        destruct (s_brk st) as [|b0 b gk|gd] eqn:EB.
        -- apply (arm_C2 st L X M mdl regs rom sp F bi HL HWF HREP HLG XOK Hh Hlz Hmat HCNT HLEN HBUD H2 Hra Hsp H4 DEF Hok' Hfail Efl Hac0 Hac EB bo r1 Hside G2 G19 G8 G18 K1).
        -- apply (UbMhAMetaM.arm_C3 st L X M mdl regs rom sp F bi HL HWF HREP HLG XOK Hh Hlz Hmat HCNT HLEN HBUD H2 Hra Hsp H4 DEF Hok' Hfail Efl Hac0 Hac b0 b gk EB bo r1 Hside G2 G19 G8 G18 K1).
        -- apply (UbMhAMetaM.arm_C4d st L X M mdl regs rom sp F bi HL HWF HREP HLG XOK Hh Hlz Hmat HCNT HLEN HBUD H2 Hra Hsp H4 DEF Hok' Hfail Efl Hac0 Hac gd EB bo r1 G2 G19 G8 G18 K1).
  - apply (UbMhAMetaS.arm_A st L X M mdl regs rom sp (kfx F bo) HWF HREP HLG Hh Hlz Hmat H2 Hra Hsp DEF HQ Hnn r1 G2 G19 G8 G18 K1).
Qed.
