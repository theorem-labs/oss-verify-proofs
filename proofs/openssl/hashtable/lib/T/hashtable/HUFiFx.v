(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ModelAmb PropExec HUTargetPre HUWorld HUWorldK HUReadBase HUReadStage HUTargetFull HUHandoff HUInitPcs HUFiPre.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.Cfg Require Import ShapeAlgBase ShapeCfg NodesCfg LedgerCfg AllocCfg MiscCfg.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxRn FxImage FxHandoff FxHoBuild FxSys FxMisc FxDrive FxDriveId FxHb.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import HoBridge HoDrive HoDriveX.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import H0Lim.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require ConeCfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ConeCfg.   (* [comment removed for export] *)
Import ListNotations.
Import ConeCfg.
Open Scope Z_scope.

Lemma Rn_mono : forall segs IM n n' rho F ms, to_Z n <= to_Z n' -> Rn segs IM n rho F ms -> Rn segs IM n' rho F ms.
Proof. intros segs IM n n' rho F ms Hle H rho' [A0 A]. apply H. split; [exact A0|]. intros t Ht. apply A. lia. Qed.

Lemma tgt_k_range : forall sp0 k buf can content VM R M, tgt_entry_full sp0 k buf can content VM R M -> In k KS.
Proof.
  intros sp0 k buf can content VM R M [_ _ (mb & bw & B & brkv & mas & tid & sec & _ & [(-> & _) | (Hk & _)])]; [left; reflexivity|].
  assert (E : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10) by lia.
  unfold KS. cbn [In]. lia.
Qed.

Lemma Forall_filter_keep : forall (A : Type) (P : A -> Prop) (f : A -> bool) l, Forall P l -> Forall P (List.filter f l).
Proof. intros A P f l H. apply Forall_forall. intros x Hx. apply filter_In in Hx as [Hx _]. exact (proj1 (Forall_forall P l) H x Hx). Qed.

Section FI.
  Variables (sp0 : word) (k buf : Z) (can : word) (content : list byte) (VM : VmMaps) (R : bvmap 5 word) (M : word -> option byte).
  Variables (stdin0 : AmbIn) (fs0 : Fs) (tid : word).
  Hypothesis TF : tgt_entry_full sp0 k buf can content VM R M.

  Definition fi_ms : machine_state := mkst R (Z_to_bv 64 PC_TARGET) M (seg_rom RSEGS).
  Definition fi_m : Model := model_post VM stdin0 fs0 tid.
  (* [comment removed for export] *)
  Definition fi_rho (mb B : word) (sec tdz err : Z) : int -> word :=
    rho_of sp0 mb B (bv_unsigned can) sec tdz err R (Z_to_bv 64 0) (Z_to_bv 64 0).
  (* [comment removed for export] *)
  Definition FiInv : int -> (int -> word) -> fstate -> fledger -> machine_state -> Model -> Prop :=
    DInvX ConeCfg.CFG RSEGS IMH (segments_reserved RSEGS) LIM RTgt KEEP M (XI_frame fi_m) []
          (ms_fregs fi_ms) (ms_fcsr fi_ms) (seg_rom RSEGS) (fun x => bv_unsigned sp0 <= bv_unsigned x).

  (* [comment removed for export] *)
  Record fi_root_facts (mb bw B : word) (sec tdz err : Z) : Prop := {
    fr_rho0  : fi_rho mb B sec tdz err 0%uint63 = Z_to_bv 64 0;
    fr_buf   : buf = bv_unsigned B + (if k =? 0 then 32 else offk k);
    fr_facts : Forall (hholds RSEGS (fi_rho mb B sec tdz err) fi_ms) (hfacts_all k);      (* [comment removed for export] *)
    fr_res   : vm_reserved VM = segments_reserved RSEGS;
    fr_lim   : LIM <= vm_limit VM;                 (* [comment removed for export] *)
    fr_isp   : vm_init_sp VM = sp0;
    fr_exact : vm_exact VM sp0 mb bw B (hnb k);
    fr_li    : ledger_inv (segments_reserved RSEGS) LIM 2 (hnb k + 8192) VM;
    fr_tid   : 0 < tdz < 2 ^ 22;
    fr_err   : 0 <= err < 2 ^ 32          (* [comment removed for export] *)
  }.

  Lemma fi_root : exists (mb bw B : word) (sec tdz err : Z),
    fi_root_facts mb bw B sec tdz err /\ FiInv 200%uint63 (fi_rho mb B sec tdz err) (F0 k) (L0 k) fi_ms fi_m.
  Proof.
    pose proof (tgt_k_range _ _ _ _ _ _ _ _ TF) as Hk.
    pose proof (proj1 (forallb_forall _ _) pre_all k Hk) as Hpre. apply andb_true_iff in Hpre as [Hpre Hprist].
    apply andb_true_iff in Hpre as [Hchk Htags].
    assert (Hex : exists (mb bw B : word) (sec tdz err : Z), fi_root_facts mb bw B sec tdz err).
    { unfold hfacts_all, hnb. destruct (Z.eqb_spec k 0) as [Hk0 | Hk0].
      - assert (TF0 : tgt_entry_full sp0 0 buf can content VM R M) by (rewrite <- Hk0; exact TF).
        destruct (handoff_k0x sp0 buf can content VM R M (Z_to_bv 64 PC_TARGET) (Z_to_bv 64 0) (Z_to_bv 64 0) TF0)
          as (mb & bw & B & sec & tdz & err & H0 & Hb & HF & Vres & Vlim & Visp & Vex & Hli & Htid & Herr).
        exists mb, bw, B, sec, tdz, err.
        constructor; try assumption; unfold hfacts_all, hnb; destruct (Z.eqb_spec k 0); try lia; assumption.
      - assert (Hk1 : 1 <= k <= 10) by (unfold KS in Hk; cbn [In] in Hk; lia).
        destruct (handoff_kx sp0 k buf can content VM R M (Z_to_bv 64 PC_TARGET) (Z_to_bv 64 0) (Z_to_bv 64 0) Hk1 TF)
          as (mb & bw & B & sec & tdz & err & H0 & Hb & HF & Vres & Vlim & Visp & Vex & Hli & Htid & Herr).
        exists mb, bw, B, sec, tdz, err.
        constructor; try assumption; unfold hfacts_all, hnb; destruct (Z.eqb_spec k 0); try lia; assumption. }
    destruct Hex as (mb & bw & B & sec & tdz & err & HR). exists mb, bw, B, sec, tdz, err. split; [exact HR|].
    destruct HR as [H0 Hb HFall Vres Vlim Visp Vex Hli Htid Herr0].
    set (rho := fi_rho mb B sec tdz err) in *.
    assert (HF : Forall (hholds RSEGS rho fi_ms) (hfacts k)) by (unfold hfacts; apply Forall_filter_keep; exact HFall).
    destruct Vex as (Xm & Xn & Xs & Xb & Xbw & Xr & Xal & Xpos & Xtop & Xrf & Xdj & Xbrk).
    assert (Hnbr : 0 < hnb k < 2 ^ 62).
    { unfold hnb. destruct (Z.eqb_spec k 0); [lia|]. assert (Hk1 : 1 <= k <= 10) by (unfold KS in Hk; cbn [In] in Hk; lia).
      pose proof (capk_bounds k Hk1). unfold nbk. lia. }
    destruct res_bounds as (_ & _ & Hcov).
    pose proof (li_sp_lo _ _ _ _ _ Hli) as Hsplo. rewrite Visp in Hsplo. unfold sp_window_lo in Hsplo.
    pose proof (u64_range mb) as Um. pose proof (u64_range sp0) as Us. pose proof (u64_range B) as Ub.
    assert (Hmbtop : bv_unsigned mb + 8192 <= bv_unsigned sp0 - 8388608).
    { pose proof (li_top _ _ _ _ _ Hli) as LT. rewrite Xm in LT. apply Forall_cons_iff in LT as [_ LT]. apply Forall_cons_iff in LT as [[_ LT] _].
      unfold e_hi, e_lo, e_sz, alloc_top, stack_max_size in LT. cbn [fst snd] in LT. rewrite Visp in LT.
      rewrite (LedgerCfg.u64_lit 8192) in LT by lia. lia. }
    assert (HRn : Rn RSEGS IMH 200%uint63 rho (F0 k) fi_ms).
    { apply (handoff_Rn RSEGS IMH (mk_fimage_ok RSEGS IMH IMH_eq) (mk_fimage_wr_ok RSEGS IMH IMH_eq) (hfacts k) (HD k) 200%uint63 rho fi_ms Hchk Htags H0 HF);
        [ | reflexivity | reflexivity].
      unfold fi_ms, HD, ho_build. cbn [ms_pc_val mkst sd_pc]. rewrite to_Z_ioz by (vm_compute; split; [discriminate | reflexivity]). reflexivity. }
    unfold FiInv.
    change M with (ms_mem fi_ms) at 1.
    change (seg_rom RSEGS) with (ms_rom fi_ms).
    apply (dinvx_root ConeCfg.CFG RSEGS IMH (segments_reserved RSEGS) LIM (XI_frame fi_m) []
             (hfacts k) (ioz PC_TARGET) (ioz 0x10000) (ioz 0x354000) (ioz (hnb k)) (Some PKUnk) 200%uint63 rho fi_ms fi_m sp0 mb B (hnb k) KEEP HRn H0).
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - apply to_Z_ioz. lia.
    - vm_compute. reflexivity.
    - exact Hnbr.
    - lia.
    - lia.
    - reflexivity.
    - split; reflexivity.
    - exact Hli.
    - exact Vres.
    - exact Visp.
    - exact Xm.
    - exact Xn.
    - exact Xb.
    - exact Hcov.
    - apply XI_frame_init.
    - intros t [].
    - exact Hprist.
    - change (to_Z (ioz 0x354000)) with 0x354000. lia.
    - lia.
    - lia.
  Qed.

  (* [comment removed for export] *)
  Theorem fi_universal : forall (fuel : nat) (T : TSet),
    (forall (mb bw B : word) (sec tdz err : Z), fi_root_facts mb bw B sec tdz err ->
       forall F' L' n' r rho' ms' m',
         leaf_in (F', L', n', r) (the_tree k fuel) ->
         FiInv n' rho' F' L' ms' m' ->
         dext 200%uint63 (fi_rho mb B sec tdz err) fi_m n' rho' m' ->
         (r = SEcall -> RiscvSemantics.step RSEGS ms' = MachineOk (ms_pend ms')) ->
         realizes_cfg ConeCfg.CFG RSEGS (mkCfg ms' m') T) ->
    realizes_cfg ConeCfg.CFG RSEGS (mkCfg fi_ms fi_m) T.
  Proof.
    intros fuel T HK. destruct fi_root as (mb & bw & B & sec & tdz & err & HR & HDI). destruct res_bounds as (HRb & HRc & _).
    apply (drive_universalX ConeCfg.CFG RSEGS IMH CODE CODE_ok eq_refl (segments_reserved RSEGS) RB RC LIM HRb HRc
             RTgt KEEP M (XI_frame fi_m) [] (XI_frame_rho fi_m []) (XI_frame_vm fi_m) XS (xask_b5 IMH CODE)
             (fun n rho F L ms m res (H : XS F L n = Some res) => ltac:(discriminate H))
             (ms_fregs fi_ms) (ms_fcsr fi_ms) (seg_rom RSEGS) (fun x => bv_unsigned sp0 <= bv_unsigned x)
             (ioz BP) 20%nat ltac:(lia) fuel 200%uint63 (fi_rho mb B sec tdz err) (F0 k) (L0 k) fi_ms fi_m T HDI).
    intros F' L' n' r Hleaf rho' ms' m' HD' Hext Hec.
    exact (HK mb bw B sec tdz err HR F' L' n' r rho' ms' m' Hleaf HD' Hext Hec).
  Qed.

  (* [comment removed for export] *)
  Theorem fi_existential : forall (fuel : nat),
    exists (mb bw B : word) (sec tdz err : Z) F' L' n' r rho' ms' m',
      fi_root_facts mb bw B sec tdz err
      /\ leaf_in (F', L', n', r) (the_tree k fuel)
      /\ star_cfg RSEGS ConeCfg.CFG (mkCfg fi_ms fi_m) [] (mkCfg ms' m')
      /\ FiInv n' rho' F' L' ms' m'
      /\ dext 200%uint63 (fi_rho mb B sec tdz err) fi_m n' rho' m'
      /\ (r = SEcall -> RiscvSemantics.step RSEGS ms' = MachineOk (ms_pend ms')).
  Proof.
    intros fuel. destruct fi_root as (mb & bw & B & sec & tdz & err & HR & HDI). destruct res_bounds as (HRb & HRc & _).
    destruct (drive_existentialX ConeCfg.CFG RSEGS IMH CODE CODE_ok eq_refl (segments_reserved RSEGS) RB RC LIM HRb HRc
             RTgt KEEP M (XI_frame fi_m) [] (XI_frame_rho fi_m []) (XI_frame_vm fi_m) XS (xask_b5 IMH CODE)
             (fun n rho F L ms m res (H : XS F L n = Some res) => ltac:(discriminate H))
             (ms_fregs fi_ms) (ms_fcsr fi_ms) (seg_rom RSEGS) (fun x => bv_unsigned sp0 <= bv_unsigned x)
             (ioz BP) 20%nat ltac:(lia) fuel 200%uint63 (fi_rho mb B sec tdz err) (F0 k) (L0 k) fi_ms fi_m HDI)
      as (F' & L' & n' & r & rho' & ms' & m' & Hleaf & Hstar & HD' & Hext & Hec).
    exists mb, bw, B, sec, tdz, err, F', L', n', r, rho', ms', m'. tauto.
  Qed.

  (* [comment removed for export] *)
  Lemma fi_kfacts : forall mb bw B sec tdz err, fi_root_facts mb bw B sec tdz err ->
    Forall (hholds RSEGS (fi_rho mb B sec tdz err) fi_ms) (kfacts k).
  Proof. intros mb bw B sec tdz err HR. unfold kfacts. apply Forall_filter_keep. exact (fr_facts _ _ _ _ _ _ HR). Qed.
End FI.
