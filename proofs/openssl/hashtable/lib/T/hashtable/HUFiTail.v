(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ModelAmb PropExec ShapeAlg HUTargetPre HUWorld HUWorldK HUReadBase HUReadStage HUTargetFull HUHandoff
  HUInitPcs HUFiPre HUFiFx HUFull.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.Cfg Require Import ShapeAlgBase ShapeCfg.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.FX Require Import W64 ITrie FxSpec FxState FxExec FxRel FxDrive FxHb.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require ConeCfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ConeCfg.   (* [comment removed for export] *)
Import ListNotations.
Import ConeCfg.
Open Scope Z_scope.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

Definition FUEL : nat := 400%nat.

(* [comment removed for export] *)
Definition root_extra (sp0 : word) (VM : VmMaps) (M : word -> option byte) : Prop :=
  (exists envc : Z, 0 <= envc /\ bv_unsigned sp0 + 192 + 8 * envc < 2 ^ 47 - 32
                    /\ M (Z_to_bv 64 (bv_unsigned sp0 + 192 + 8 * envc)) = Some (Z_to_bv 8 0))
  /\ reserved_top (segments_reserved RSEGS) <= bv_unsigned (vm_start_brk VM) <= reserved_top (segments_reserved RSEGS) + brk_aslr_max.

Lemma root_extra_of_full : forall sp0 k buf can content VM R M, tgt_entry_full sp0 k buf can content VM R M -> root_extra sp0 VM M.
Proof.
  intros sp0 k buf can content VM R M TF. pose proof (tgt_k_range _ _ _ _ _ _ _ _ TF) as Hk. split.
  - destruct TF as [TE MF _]. destruct (mf_hi _ _ MF) as (s & Hs & Hs8 & Hz).
    pose proof (proj2 (te_sp0 _ _ _ _ _ _ TE)) as Hal.
    exists ((s - bv_unsigned sp0 - 192) / 8).
    assert (E : s = bv_unsigned sp0 + 192 + 8 * ((s - bv_unsigned sp0 - 192) / 8)).
    { assert (Hm : (s - bv_unsigned sp0 - 192) mod 8 = 0).
      { destruct (proj1 (Z.mod_divide (bv_unsigned sp0) 16 ltac:(lia)) Hal) as [q Hq].
        destruct (proj1 (Z.mod_divide s 8 ltac:(lia)) Hs8) as [r Hr].
        replace (s - bv_unsigned sp0 - 192) with ((r - 2 * q - 24) * 8) by lia. apply Z_mod_mult. }
      pose proof (Z_div_mod_eq_full (s - bv_unsigned sp0 - 192) 8). lia. }
    split; [apply Z.div_pos; lia|]. rewrite <- E. split; [lia | exact Hz].
  - assert (Hex : exists (mb bw B : word) (nb : Z), vm_exact VM sp0 mb bw B nb).
    { destruct (Z.eqb_spec k 0) as [Hk0 | Hk0].
      - assert (TF0 : tgt_entry_full sp0 0 buf can content VM R M) by (rewrite <- Hk0; exact TF).
        destruct (handoff_k0x sp0 buf can content VM R M (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) TF0)
          as (mb & bw & B & sec & tdz & err & _ & _ & _ & _ & _ & _ & Vex & _). exists mb, bw, B, 69632. exact Vex.
      - assert (Hk1 : 1 <= k <= 10) by (unfold KS in Hk; cbn [In] in Hk; lia).
        destruct (handoff_kx sp0 k buf can content VM R M (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) Hk1 TF)
          as (mb & bw & B & sec & tdz & err & _ & _ & _ & _ & _ & _ & Vex & _). exists mb, bw, B, (nbk k). exact Vex. }
    destruct Hex as (mb & bw & B & nb & (_ & _ & Xs & _ & _ & Xr & _ & _ & _ & _ & _ & Xbrk)). rewrite Xs. lia.
Qed.

Definition leaf_tail_stmt (KT : list byte -> Fs -> TSet) : Prop :=
  forall (sp0 : word) (k buf : Z) (can : word) (content : list byte) (VM : VmMaps) (R : bvmap 5 word) (M : word -> option byte)
         (stdin0 : AmbIn) (fs0 : Fs) (tid : word),
    valid_sp sp0 -> 0 < bv_unsigned tid < 2 ^ 22 ->
    tgt_entry_full sp0 k buf can content VM R M ->
    root_extra sp0 VM M ->
    forall (mb bw B : word) (sec tdz err : Z),
      fi_root_facts sp0 k buf can VM R M mb bw B sec tdz err ->
      forall F' L' n' r rho' ms' m',
        leaf_in (F', L', n', r) (the_tree k FUEL) ->
        FiInv sp0 VM R M stdin0 fs0 tid n' rho' F' L' ms' m' ->
        dext 200%uint63 (fi_rho sp0 can R mb B sec tdz err) (fi_m VM stdin0 fs0 tid) n' rho' m' ->
        (r = SEcall -> RiscvSemantics.step RSEGS ms' = MachineOk (ms_pend ms')) ->
        realizes_cfg ConeCfg.CFG RSEGS (mkCfg ms' m') (KT content fs0).

Theorem tail_of_leaves : forall KT, leaf_tail_stmt KT -> tail_stmt KT.
Proof.
  intros KT HL sp0 tid stdin0 fs0 can k buf fdata V' R' M' Hsp Htid TF.
  change (realizes_cfg ConeCfg.CFG RSEGS (mkCfg (fi_ms R' M') (fi_m V' stdin0 fs0 tid)) (KT fdata fs0)).
  apply (fi_universal sp0 k buf can fdata V' R' M' stdin0 fs0 tid TF FUEL (KT fdata fs0)).
  intros mb bw B sec tdz err HR F' L' n' r rho' ms' m' Hleaf HD Hext Hec.
  exact (HL sp0 k buf can fdata V' R' M' stdin0 fs0 tid Hsp Htid TF (root_extra_of_full _ _ _ _ _ _ _ _ TF) mb bw B sec tdz err HR F' L' n' r rho' ms' m' Hleaf HD Hext Hec).
Qed.
