(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS1 OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocMRunSf.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA.BoAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c.BoAllocM9a OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c.BoAllocM9d OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS1.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).

Section FPGen.
Context {fx : FPState}.

Section RUNSF.
  Variables (mem MP : word -> option byte) (S : word) (n : Z) (x18 x19 x22 x23 x24 x25 x26 x27 : word).
  Hypothesis GS : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47)%Z.
  Hypothesis Pfoot : forall x : word, MP x <> mem x -> (U S - 2272 <= U x < U S)%Z.
  Hypothesis Pgrows : mem_grows mem MP.
  #[local] Abbreviation MA := (ma_A MP S n x18 x19 x22 x23 x24 x25 x26 x27).
  #[local] Abbreviation sp2 := (at_ S (-2272)).
  #[local] Abbreviation spL := (at_ S (-2320)).
  #[local] Abbreviation MF := (ms_pre_mem S n MA).

  Lemma msf_MA : forall x : word, (U x < U S - 2416 \/ U S - 2272 <= U x)%Z -> MF x = MA x.
  Proof using GS.
    intros x Hx. pose proof (u64_range S) as HSr. destruct GS as [G1 G2]. (lazymatch goal with |- ?G => let G' := eval unfold ms_pre_mem, la_m0, cbs_m0 in G in change_no_check G' end).
    repeat (rewrite wbytes_outside; [ | rewrite length_N_to_le_bytes, ?at_at, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, ?at_at, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
    reflexivity.
  Qed.
  Lemma msf_outside : forall x : word, (U x < U S - 2416 \/ U S <= U x)%Z -> MF x = mem x.
  Proof using Pfoot GS.
    intros x Hx. rewrite msf_MA by lia. rewrite (ma_A_outside MP S n x18 x19 x22 x23 x24 x25 x26 x27 GS) by lia.
    destruct (decide (MP x = mem x)) as [E | NE]; [exact E|]. pose proof (Pfoot x NE). lia.
  Qed.
  Lemma msf_above : forall x : word, (U S - 2128 <= U x)%Z -> MF x = MP x.
  Proof using GS. intros x Hx. rewrite msf_MA by lia. apply (ma_A_outside MP S n x18 x19 x22 x23 x24 x25 x26 x27 GS). lia. Qed.
  Lemma msf_grows : mem_grows mem MF.
  Proof using Pgrows.
    eapply mem_grows_trans; [exact Pgrows|]. apply (mem_grows_trans _ MA); [exact (ma_A_grows MP S n x18 x19 x22 x23 x24 x25 x26 x27)|].
    (lazymatch goal with |- ?G => let G' := eval unfold ms_pre_mem, la_m0, cbs_m0 in G in change_no_check G' end). do 18 (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl.
  Qed.
  Lemma msf_rd_above : forall (k : Z) (w : nat) (bs : list byte), (-2128 <= k)%Z -> (k + Z.of_nat w <= 0)%Z ->
    rdn BSEGS MP (at_ S k) w = Some bs -> rdn BSEGS MF (at_ S k) w = Some bs.
  Proof using GS.
    intros k w bs K1 K2 Hr. pose proof (u64_range S). destruct GS as [G1 G2]. rewrite <- Hr.
    apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]|]. intros x Hx. rewrite at_u in Hx by lia. apply msf_above. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma msf_slotsA : forall (k : Z) (v : word), In (k, v) (ma_slotsA S n x18 x19 x22 x23 x24 x25 x26 x27) ->
    rdn BSEGS MF (at_ S k) 8 = Some (LE8 v).
  Proof using GS.
    intros k v Hin. pose proof (u64_range S) as HSr. pose proof GS as [G1 G2].
    pose proof (ma_slotsA_range S n x18 x19 x22 x23 x24 x25 x26 x27 k v Hin) as [Hk1 Hk2].
    assert (OUT : rdn BSEGS MF (at_ S k) 8 = rdn BSEGS MA (at_ S k) 8).
    { apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply msf_MA. lia. }
    rewrite OUT. unfold ma_slotsA in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; (lazymatch goal with |- ?G => let G' := eval unfold ma_A in G in change_no_check G' end); rewrite ?at_at; (lazymatch goal with |- ?G => let G' := eval cbn [Z.add Z.opp Pos.add Z.pos_sub] in G in change_no_check G' end); rd8_chain |]).
    destruct Hin.
  Qed.
  (* [comment removed for export] *)
  Lemma msf_cb_slots : forall (o : Z) (v : word),
    In (o, v) [(-8, Z_to_bv 64 0x4c834); (-16, Z_to_bv 64 0); (-24, Z_to_bv 64 n); (-32, Z_to_bv 64 8); (-40, Z_to_bv 64 (sec_needed n)); (-48, Z_to_bv 64 2048)]%Z ->
    rdn BSEGS MF (at_ sp2 o) 8 = Some (LE8 v).
  Proof using GS.
    intros o v Hin. pose proof (u64_range S) as HSr. destruct GS as [G1 G2]. (lazymatch goal with |- ?G => let G' := eval unfold ms_pre_mem, la_m0, cbs_m0 in G in change_no_check G' end). cbn [In] in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rewrite ?at_at; (lazymatch goal with |- ?G => let G' := eval cbn [Z.add Z.opp Pos.add Z.pos_sub] in G in change_no_check G' end); rd8_chain |]). destruct Hin.
  Qed.
  Lemma msf_la_slots : forall (o : Z) (v : word),
    In (o, v) [(-8, Z_to_bv 64 0x50d94); (-16, Z_to_bv 64 8); (-24, Z_to_bv 64 n); (-32, Z_to_bv 64 8); (-40, Z_to_bv 64 (sec_needed n)); (-48, Z_to_bv 64 2048);
               (-56, Z_to_bv 64 n); (-64, Z_to_bv 64 0x10ab58); (-72, at_ S (-2128)); (-80, Z_to_bv 64 18446744073709551608); (-88, Z_to_bv 64 7)]%Z ->
    rdn BSEGS MF (at_ spL o) 8 = Some (LE8 v).
  Proof using GS.
    intros o v Hin. pose proof (u64_range S) as HSr. destruct GS as [G1 G2]. (lazymatch goal with |- ?G => let G' := eval unfold ms_pre_mem, la_m0, cbs_m0 in G in change_no_check G' end). cbn [In] in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rewrite ?at_at; (lazymatch goal with |- ?G => let G' := eval cbn [Z.add Z.opp Pos.add Z.pos_sub] in G in change_no_check G' end); rd8_chain |]). destruct Hin.
  Qed.
End RUNSF.
End FPGen.
End BoAllocMRunSf.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23.AsAinvOpsQ3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP2. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA.BoAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP2.BoAllocMTopA.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys7b OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopSd. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys7b OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9b OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys11 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocM8Lk OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c.BoAllocM9a OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i.BoAllocM9m OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i.BoAllocM9k OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS1.BoAllocM2s OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS1 BoAllocMRunSf OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopSd.BoAllocMSecK OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopSd.BoAllocMSecDefs OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsDepotBud.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac ha_prev := first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
#[local] Ltac lia ::= first [ solve [ ha_tiers ltac:(ha_lia0) ] | ha_prev ].   (* [comment removed for export] *)
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

From Stdlib Require Import FunctionalExtensionality.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma mod4096_mod8s : forall t, t mod 4096 = 0 -> t mod 8 = 0.
Proof. intros t Ht. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma restrict_mkst_s : forall {fx : FPState} (Hd : word -> bool) (r : bvmap 5 word) pc m rom,
  restrict Hd (@mkst fx r pc m rom) = @mkst fx r pc (mrestrict Hd m) rom.
Proof. intros. reflexivity. Qed.

Section WithCeil.
Context {RC : run_ceil}.

(* [comment removed for export] *)
Definition sec_cells (bt : as_boot) : Prop :=
  In (0x10ab98, 8%nat, 0x1000) (bt_consts bt)                  (* [comment removed for export] *)
  /\ In (0x105f00, 8%nat, 0x107e90) (bt_consts bt)               (* [comment removed for export] *)
  /\ In (0x107e90, 8%nat, 0x1a290) (bt_consts bt)               (* [comment removed for export] *)
  /\ In (0x10aba0, 8%nat, bt_ptrarr bt) (bt_consts bt)          (* [comment removed for export] *)
  /\ In (0x10aba8, 8%nat, bt_ptrarr bt) (bt_consts bt)          (* [comment removed for export] *)
  /\ In (0x105f58, 8%nat, 1) (bt_consts bt) /\ In (0x19fcdc, 4%nat, 0) (bt_consts bt)
  /\ In (0x1e1d5, 8%nat, 0x612079726f6d656d) (bt_consts bt) /\ In (0x1e1dd, 8%nat, 0x7365726464612074) (bt_consts bt)
  /\ In (0x1e1e5, 4%nat, 0x70252073) (bt_consts bt) /\ In (0x1e1e9, 1%nat, 0) (bt_consts bt)
  /\ In (0x22730, 4%nat, 0x613e0) (bt_consts bt) /\ In (0x104a8, 8%nat, 0xaaaaaaaaaaaaaaaa) (bt_consts bt).

Section TOPSA.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND : Z).
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis CELLS : malloc_cells bt TP TSDP PGP FL MIDEND.
  Hypothesis PCELLS : pop_cells bt.
  Hypothesis SCELLS : sec_cells bt.
  Hypothesis GEOM : free_boot_geom bt.
  Hypothesis BOOTG : boot_geom bt.
  Hypothesis BOK : boot_ok bt.
  Hypothesis BTOT : boot_totals bt.
  Hypothesis HTP : TP = ia_tp both_addrs.

  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation CTX := (bt_tctx bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).

  Theorem malloc_sec_to_mmap :
    forall fx (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF : list (Z * Z)) (B C K ret sp n : Z) (st : ast) (h : option Z) (Qok Qf : config -> Prop),
      FXOK fx -> m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
      WF bt st Lc FF -> Rep bt st Lc FF M mdl -> bounds st Lc B C K -> holes_le h st -> hole_ok h n ->
      call_pre BSEGS both_addrs R M ret sp MSTK_A -> U (getr R 10) = n -> 64512 < n <= NMAX -> fpc M (U (getr R 8)) sp DMAX ->
      B + (n + MBLK) <= GBUDGET -> C + 1 <= LMAX -> K + kcost_malloc n <= KCAP ->
      (forall c', at_sec_grant bt fx R M mdl Lc FF n st c' -> katwD BSEGS c' Qok Qf) ->
      (forall c', at_sec_null bt fx R M mdl Lc FF n st c' -> katD BSEGS c' Qf) ->
      katsD BSEGS (cfg BSEGS fx R (ia_malloc both_addrs) M mdl) Qok Qf.
  Proof using HTP BTOT BOK BOOTG GEOM SCELLS PCELLS CELLS BT_ia BT_segs MIDEND FL PGP TSDP TP.
    intros fx R M mdl Lc FF B C K ret sp n st h Qok Qf HFX HH MW W RP BD HPH HO CP HR10 Hn FPC HB HC HK CONT1 CONT0.
    assert (KC : a_kact st <= KCAP) by (destruct BD as (_ & _ & BK); unfold kcost_malloc, EVT in HK; lia).
    assert (Hn34 : 64513 <= n <= 2 ^ 34) by (destruct BD as ((BP & BP2) & _); unfold GBUDGET, MBLK in HB; lia).
    pose proof ceil_rng as CR. pose proof ceil_pg as CPG.
    set (S := getr R 2) in *. set (ra0 := getr R 1). set (tp := getr R 4).
    destruct CP as (CP1 & CPr & CPe & CP2 & CP16 & CPlo & CPhi & CP4 & CPstk). fold S ra0 tp in CP1, CP2, CP4. pose proof CP4 as CP4'. rewrite <- HTP in CP4.
    pose proof CELLS as (CELL_mcs & CELL_gcf & CELL_fum & CELL_inited & CELL_pg & CELL_P & CELL_kif & CELL_key & CELL_tsdp & CELL_tctx
                      & CELL_rss & CELL_lmag & CELL_tbl2 & CELL_t16 & CELL_t2048 & CELL_minrz & CELL_maxrz & CELL_maxsz & CELL_sbeg
                      & CELL_cpm & CELL_gsh & CELL_gmb & CELL_mb & CELL_gme & CELL_me & CELL_ghe & CELL_he & CELL_gfl & CELL_pp & CELL_mfs & CELL_fill
                      & CELL_grm & CELL_rm & CELL_glsn & CELL_lsn & CELL_magic & CELL_hook & CELL_thr64 & G_consts).
    destruct G_consts as (Gc1 & Gc2 & Gc3 & Gc4 & Gc5 & Gc6 & Gc7 & Gc8 & Gc9).
    pose proof GEOM as (GCT & Gtop & Gbot).
    pose proof (free_obls_pf bt) as (OBL_nolazy_rt & _ & OBL_rt_private & _).
    unfold OBL_nolazy_rt_stmt in OBL_nolazy_rt. unfold OBL_rt_private_stmt in OBL_rt_private.
    hidehyp GCT.
    (* [comment removed for export] *)
    pose proof (thread_dyn bt st Lc FF W) as (GT0 & GTC & GTI & GTB & TPG & GC0 & GCC & GCI & GCB & _ & SB1). hidehyp GCB.
    hidehyp GTB.
    assert (GT4 : 4096 <= T) by (unfold PG in TPG; clear - GT0 TPG; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    pose proof RP as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18).
    destruct R3 as (Tctx & Ttop & Tbot & Tsw & Tfs & Tunw & TQ & TPC & TW & Tback & Ttid & Ttls1 & Ttls2).
    rewrite BT_segs in *. rewrite BT_ia in *. cbn [ia_img_lo ia_img_hi both_addrs] in GTI, GCI.
    pose proof (u64_range S) as HSr.
    unfold PTRHI in CPlo, CPhi. unfold AS_HEAPLO, AS_LO, MSTK_A, PG, KSPACE, NMAX in *.
    (* [comment removed for export] *)
    set (Hd := HID st mdl).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st mdl z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). lia. }
    assert (NHrt : forall z, (T <= z < T + 4096) \/ (CTX <= z < CTX + 0x10000) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply (OBL_nolazy_rt st Lc FF M mdl z W RP). (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). tauto. }
    destruct R14 as (Bw1 & Bw2 & Bw3 & Bw4 & Bw5).
    set (Mr := mrestrict Hd M).
    Ltac hoff NH := apply hid_off_of; intros z Hz; unfold T_UNW, T_QC, T_PC, PC_SZ in *; split; [lia | apply NH; lia].
    Ltac konst Hd M R1 NHs C := apply (cellZ_restrict Hd M _ _ _ (const_cell bt M _ _ _ R1 C)); [lia | lia | hoff NHs].
    (* [comment removed for export] *)
    assert (K_mcs : rdn BSEGS Mr (Z_to_bv 64 0x10eebc) 4 = Some (LE4 30)) by konst Hd M R1 NHs CELL_mcs.
    assert (K_gcf : rdn BSEGS Mr (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 0x19fce8))) by konst Hd M R1 NHs CELL_gcf.
    assert (K_fum : rdn BSEGS Mr (Z_to_bv 64 0x19fd0a) 1 = Some [Z_to_bv 8 1]) by konst Hd M R1 NHs CELL_fum.
    assert (K_inited : rdn BSEGS Mr (Z_to_bv 64 0x10ee98) 1 = Some [Z_to_bv 8 1]) by konst Hd M R1 NHs CELL_inited.
    assert (K_pg : rdn BSEGS Mr (Z_to_bv 64 0x105ef8) 8 = Some (LE8 (Z_to_bv 64 PGP))) by konst Hd M R1 NHs CELL_pg.
    assert (K_P : rdn BSEGS Mr (Z_to_bv 64 PGP) 8 = Some (LE8 (Z_to_bv 64 4096))) by konst Hd M R1 NHs CELL_P.
    assert (K_kif : rdn BSEGS Mr (Z_to_bv 64 0x10da20) 1 = Some [Z_to_bv 8 1]) by konst Hd M R1 NHs CELL_kif.
    assert (K_key : rdn BSEGS Mr (at_ (Z_to_bv 64 0x10da20) 4) 4 = Some (LE4 0)).
    { replace (at_ (Z_to_bv 64 0x10da20) 4) with (Z_to_bv 64 0x10da24 : word) by (apply bv_eq; reflexivity). konst Hd M R1 NHs CELL_key. }
    assert (K_tsdp : rdn BSEGS Mr (at_ tp (-88)) 8 = Some (LE8 (Z_to_bv 64 TSDP))).
    { replace (at_ tp (-88)) with (Z_to_bv 64 (TP - 88)) by (apply bv_eq; rewrite at_u by (rewrite CP4; wd_ulia_c); rewrite CP4; wd_ulia_c). konst Hd M R1 NHs CELL_tsdp. }
    assert (K_tctx : rdn BSEGS Mr (Z_to_bv 64 TSDP) 8 = Some (LE8 (Z_to_bv 64 CTX))) by konst Hd M R1 NHs CELL_tctx.
    assert (K_rss : rdn BSEGS Mr (Z_to_bv 64 0x190422) 1 = Some [Z_to_bv 8 0]) by konst Hd M R1 NHs CELL_rss.
    assert (K_lmag : rdn BSEGS Mr (Z_to_bv 64 0x10488) 8 = Some (LE8 MAGICw)).
    { (lazymatch goal with |- ?G => let G' := eval unfold MAGICw in G in change_no_check G' end). konst Hd M R1 NHs CELL_lmag. }
    assert (K_tbl2 : rdn BSEGS Mr (at_ (Z_to_bv 64 0x104f8) 4) 1 = Some [Z_to_bv 8 3]).
    { replace (at_ (Z_to_bv 64 0x104f8) 4) with (Z_to_bv 64 0x104fc : word) by (apply bv_eq; reflexivity). rewrite <- w2b1 by lia. konst Hd M R1 NHs CELL_tbl2. }
    assert (K_t16 : rdn BSEGS Mr (at_ (Z_to_bv 64 0x105f8) 8) 1 = Some [Z_to_bv 8 4]).
    { replace (at_ (Z_to_bv 64 0x105f8) 8) with (Z_to_bv 64 0x10600 : word) by (apply bv_eq; reflexivity). rewrite <- w2b1 by lia. konst Hd M R1 NHs CELL_t16. }
    assert (K_t2048 : rdn BSEGS Mr (at_ (Z_to_bv 64 0x105f8) 49) 1 = Some [Z_to_bv 8 11]).
    { replace (at_ (Z_to_bv 64 0x105f8) 49) with (Z_to_bv 64 0x10629 : word) by (apply bv_eq; reflexivity). rewrite <- w2b1 by lia. konst Hd M R1 NHs CELL_t2048. }
    assert (K_minrz : rdn BSEGS Mr (at_ (Z_to_bv 64 0x10ab58) 3624) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 16))).
    { replace (at_ (Z_to_bv 64 0x10ab58) 3624) with (Z_to_bv 64 0x10b980 : word) by (apply bv_eq; reflexivity). konst Hd M R1 NHs CELL_minrz. }
    assert (K_maxrz : rdn BSEGS Mr (at_ (Z_to_bv 64 0x10ab58) 3626) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 2048))).
    { replace (at_ (Z_to_bv 64 0x10ab58) 3626) with (Z_to_bv 64 0x10b982 : word) by (apply bv_eq; reflexivity). konst Hd M R1 NHs CELL_maxrz. }
    assert (K_maxsz : rdn BSEGS Mr (at_ (Z_to_bv 64 0x10ab58) 3616) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 40)))).
    { replace (at_ (Z_to_bv 64 0x10ab58) 3616) with (Z_to_bv 64 0x10b978 : word) by (apply bv_eq; reflexivity). konst Hd M R1 NHs CELL_maxsz. }
    assert (K_sbeg : rdn BSEGS Mr (at_ (Z_to_bv 64 0x10ab58) 32) 8 = Some (LE8 (Z_to_bv 64 SBEG))).
    { replace (at_ (Z_to_bv 64 0x10ab58) 32) with (Z_to_bv 64 0x10ab78 : word) by (apply bv_eq; reflexivity). konst Hd M R1 NHs CELL_sbeg. }
    (* [comment removed for export] *)
    Ltac thr_cell Hd M NHrt C := apply (cellZ_restrict Hd M _ _ _ C); [(lazymatch goal with |- ?G => let G' := eval unfold T_UNW, T_QC, T_PC, PC_SZ in G in change_no_check G' end); lia | unfold T_UNW, T_QC, T_PC, PC_SZ in *; lia | hoff NHrt].
    assert (K_thr : rdn BSEGS Mr (at_ (Z_to_bv 64 CTX) 152) 8 = Some (LE8 (Z_to_bv 64 T))).
    { replace (at_ (Z_to_bv 64 CTX) 152) with (Z_to_bv 64 (CTX + 152)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Tback. }
    assert (K_T0 : rdn BSEGS Mr (Z_to_bv 64 T) 8 = Some (LE8 (Z_to_bv 64 CTX))) by thr_cell Hd M NHrt Tctx.
    assert (K_tid : rdn BSEGS Mr (at_ (Z_to_bv 64 CTX) 8) 4 = Some (LE4 0)).
    { replace (at_ (Z_to_bv 64 CTX) 8) with (Z_to_bv 64 (CTX + 8)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Ttid. }
    assert (K_unw : rdn BSEGS Mr (at_ (Z_to_bv 64 T) 3168) 1 = Some [Z_to_bv 8 0]).
    { replace (at_ (Z_to_bv 64 T) 3168) with (Z_to_bv 64 (T + T_UNW)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_, T_UNW in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Tunw. }
    assert (K_sw : rdn BSEGS Mr (at_ (Z_to_bv 64 T) 40) 1 = Some [Z_to_bv 8 0]).
    { replace (at_ (Z_to_bv 64 T) 40) with (Z_to_bv 64 (T + 40)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Tsw. }
    assert (K_top : rdn BSEGS Mr (at_ (Z_to_bv 64 T) 8) 8 = Some (LE8 (Z_to_bv 64 (bt_stack_top bt)))).
    { replace (at_ (Z_to_bv 64 T) 8) with (Z_to_bv 64 (T + 8)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Ttop. }
    assert (K_bot : rdn BSEGS Mr (at_ (Z_to_bv 64 T) 16) 8 = Some (LE8 (Z_to_bv 64 (bt_stack_bottom bt)))).
    { replace (at_ (Z_to_bv 64 T) 16) with (Z_to_bv 64 (T + 16)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Tbot. }
    destruct SCELLS as (CELL_ipg & CELL_gnm & CELL_nm & CELL_pa & CELL_pab & SCREST).
    assert (K_ipg : rdn BSEGS Mr (Z_to_bv 64 (0x10ab58 + 64)) 8 = Some (LE8 (Z_to_bv 64 4096))) by konst Hd M R1 NHs CELL_ipg.
    assert (K_gnm : rdn BSEGS Mr (Z_to_bv 64 0x105f00) 8 = Some (LE8 (Z_to_bv 64 0x107e90))) by konst Hd M R1 NHs CELL_gnm.
    assert (K_nm : rdn BSEGS Mr (Z_to_bv 64 0x107e90) 8 = Some (LE8 (Z_to_bv 64 0x1a290))) by konst Hd M R1 NHs CELL_nm.
    (* [comment removed for export] *)
    assert (SOKstk : store_ok BSEGS Mr (at_ S (-3584)) 3584 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; hoff NHs].
      apply store_ok_bytes; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. intros x Hx. rewrite at_u in Hx by lia. apply CPstk. cbn in Hx. lia. }
    assert (SOKT : store_ok BSEGS Mr (Z_to_bv 64 T) 4096 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| wd_ulia_c | unorm; hoff NHrt].
      apply (writableZ_store_ok M _ _ _ _ TW); wd_ulia_c. }
    assert (FPCr : fpc Mr (U (getr R 8)) (U S) DMAX).
    { rewrite CP2. apply (fpc_kept_gen M _ _ _ FPC Mr). destruct (fpc_shape _ _ _ _ FPC) as [ST|FR]; [left; exact ST | right].
      intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). apply mrestrict_off. apply NHs; unfold PTRHI in *; lia. }
    (* [comment removed for export] *)
    assert (En : getr R 10 = Z_to_bv 64 n) by (rewrite <- HR10; symmetry; apply Z_to_bv_bv_unsigned).
    destruct (run_mS_pre Mr (seg_rom BSEGS) R S ra0 tp (Z_to_bv 64 TSDP) (Z_to_bv 64 PGP) (Z_to_bv 64 (bt_stack_top bt)) (Z_to_bv 64 (bt_stack_bottom bt))
                (Z_to_bv 64 0x1a290) T CTX n DMAX eq_refl eq_refl eq_refl En)
      as (r5 & MP & sz & bsz & x18 & x19 & URUN).
    all: try assumption.
    all: try (wd_ulia_c).
    all: try (rewrite CP4; wd_ulia_c).
    all: try (lazymatch goal with |- _ \/ _ => rewrite ?CP2; unfold hide in *; unfold PG in *; lia end).
    all: try (rewrite CP2; split; [lia|]; split; [lia | apply mod4096_mod8s; exact TPG]).
    all: try (lazymatch goal with |- _ /\ _ => rewrite ?CP2; unfold hide in *; unfold PG in *; lia end).
    all: let k := numgoals in guard k = 1.
    clear K_mcs K_gcf K_fum K_inited K_kif K_key K_tsdp K_tctx K_rss K_lmag K_tbl2 K_t16 K_t2048 K_minrz K_maxrz K_maxsz K_gnm K_nm.
    cbn zeta in URUN.
    destruct URUN as (RUN & PRL & A1 & A21 & A10 & A11 & B3 & B4 & A26 & A27
                      & SZ1 & SZ2 & FOOTP & GRP & Psz4 & Psz8 & Lsz & Ptr & Pslots).
    assert (GSm : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47) by (rewrite CP2; lia).
    pose proof (msf_outside Mr MP S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) GSm FOOTP) as MFO.
    pose proof (msf_grows Mr MP S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) GRP) as MFG.
    pose proof (msf_slotsA MP S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) GSm) as MFS.
    pose proof (msf_rd_above MP S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) GSm) as MFR.
    pose proof (msf_cb_slots MP S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) GSm) as MFC.
    pose proof (msf_la_slots MP S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) GSm) as MFL.
    set (MA := ma_A MP S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27)) in *.
    set (MF := ms_pre_mem S n MA) in *.
    clearbody MF. clear MA.
    (* [comment removed for export] *)
    (lazymatch goal with |- ?G => let G' := eval unfold cfg in G in change_no_check G' end). replace (Z_to_bv 64 (ia_malloc both_addrs)) with (Z_to_bv 64 0x6ef3c : word) by (apply bv_eq; reflexivity).
    replace (0x82a74%bv : word) with (Z_to_bv 64 0x82a74 : word) in RUN by (apply bv_eq; reflexivity).
    apply (katsD_msteps_acct BSEGS Hd (HID_off_segments bt st Lc FF M mdl BT_ia RP) asanF_segs_wx (a_aa st)
             (@mkst fx R (Z_to_bv 64 0x6ef3c) M (seg_rom BSEGS)) (@mkst fx r5 (Z_to_bv 64 0x82a74) MF (seg_rom BSEGS)) mdl);
      [apply lazy_cover_HID | exact Bw1 | exact Bw2 | exact HH | rewrite restrict_mkst_s; exact RUN |].
    intros mdl1 MI1 SBM1 HC1. rewrite unrestrict_mkst.
    replace (ms_mem (@mkst fx R (Z_to_bv 64 0x6ef3c) M (seg_rom BSEGS))) with M by reflexivity.
    set (M1 := munrestrict Hd M MF).
    (* [comment removed for export] *)
    assert (VISstk : forall a : word, U S - 3584 <= U a < U S -> M1 a = MF a).
    { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end). apply munrestrict_off. rewrite <- (Z_to_bv_bv_unsigned 64 a). apply NHs; [pose proof (u64_range a); lia | left; rewrite CP2 in Ha; lia]. }
    assert (OUT1 : forall a : word, M1 a <> M a -> U S - 2416 <= U a < U S).
    { intros a NE. unfold M1, munrestrict in NE. destruct (Hd a) eqn:Eh; [exfalso; exact (NE eq_refl)|].
      assert (EMr : Mr a = M a) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); apply mrestrict_off; exact Eh).
      destruct (Z_lt_le_dec (U a) (U S - 2416)) as [L|L]; [exfalso; apply NE; rewrite <- EMr; apply MFO; left; exact L|].
      destruct (Z_lt_le_dec (U a) (U S)) as [L2|L2]; [lia | exfalso; apply NE; rewrite <- EMr; apply MFO; right; exact L2]. }
    assert (GRin : mem_grows M M1).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold M1, munrestrict in G in change_no_check G' end). destruct (Hd x) eqn:Ex; [exact Hx|].
      apply MFG. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite mrestrict_off by exact Ex. exact Hx. }
    assert (M1def : forall a : word, M1 a <> M a -> M1 a <> None).
    { intros a NE. destruct (M1 a) eqn:E1; [discriminate|]. exfalso. apply NE. destruct (M a) eqn:E2; [|reflexivity].
      exfalso. assert (X : M a <> None) by (rewrite E2; discriminate). apply GRin in X. rewrite E1 in X. exact (X eq_refl). }
    assert (STK1 : forall a : word, U S - 3584 <= U a < U S -> M1 a <> None /\ store_ok BSEGS M1 a 1%nat = true).
    { intros a Ha. split.
      - apply GRin. apply store_ok1_heap; [lia|]. apply CPstk. rewrite <- CP2. lia.
      - eapply store_ok_mono; [exact GRin|]. apply CPstk. rewrite <- CP2. lia. }
    assert (RX1 : RepX bt (fun _ : Z => False) st Lc FF M1 mdl1).
    { apply (repx_frame_step bt (fun _ : Z => False) st Lc FF M M1 mdl mdl1 W).
      - exists M. split; [exact RP | intros a NE; exfalso; exact (NE eq_refl)].
      - intros a NE. split; [| exact (M1def a NE)]. intros RCa.
        pose proof (rep_cells_lt_ceil bt BT_ia st Lc FF (U a) W RCa) as LT. pose proof (OUT1 a NE) as O. rewrite CP2 in O. lia.
      - exact MI1.
      - exact SBM1. }
    (* [comment removed for export] *)
    assert (RD1 : forall (k : Z) (w : nat) (bs : list byte), -3584 <= k -> k + Z.of_nat w <= 0 -> rdn BSEGS MF (at_ S k) w = Some bs -> rdn BSEGS M1 (at_ S k) w = Some bs).
    { intros k w bs K1 K2 Hr. rewrite <- Hr. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]|]. intros x Hx. rewrite at_u in Hx by lia. apply VISstk. lia. }
    assert (FA1 : forall (k0 : Z) (v : word), In (k0, v) (ma_slotsA S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27)) ->
              rdn BSEGS M1 (at_ S k0) 8 = Some (LE8 v)).
    { intros k0 v Hin. pose proof (ma_slotsA_range S n x18 x19 _ _ _ _ _ _ k0 v Hin) as [Hk1 Hk2].
      apply RD1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. exact (MFS k0 v Hin). }
    assert (FI1 : forall (k0 : Z) (v : word),
              In (k0, v) [(-8, getr R 1); (-16, getr R 8); (-24, getr R 9); (-32, getr R 18); (-40, getr R 19); (-48, getr R 20); (-56, getr R 21)]%Z ->
              rdn BSEGS M1 (at_ S k0) 8 = Some (LE8 v)).
    { intros k0 v Hin.
      assert (Hk : -56 <= k0 /\ k0 + 8 <= 0) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      apply RD1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. apply MFR; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact (Pslots k0 v Hin)]. }
    assert (FS41 : rdn BSEGS M1 (at_ S (-2120)) 4 = Some (LE4 sz)) by (apply RD1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]; apply MFR; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Psz4]).
    assert (FS81 : rdn BSEGS M1 (at_ S (-2120)) 8 = Some bsz) by (apply RD1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]; apply MFR; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Psz8]).
    assert (FTR1 : rdn BSEGS M1 (at_ S (-2128)) 8 = Some (LE8 (at_ S (-2112)))) by (apply RD1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]; apply MFR; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Ptr]).
    assert (FC1 : forall (o : Z) (v : word),
              In (o, v) [(-8, Z_to_bv 64 0x4c834); (-16, Z_to_bv 64 0); (-24, Z_to_bv 64 n); (-32, Z_to_bv 64 8); (-40, Z_to_bv 64 (sec_needed n)); (-48, Z_to_bv 64 2048)]%Z ->
              rdn BSEGS M1 (at_ (at_ S (-2272)) o) 8 = Some (LE8 v)).
    { intros o v Hin.
      assert (Ho : -48 <= o <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      rewrite at_at. apply RD1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. rewrite <- at_at. exact (MFC o v Hin). }
    assert (FL1 : forall (o : Z) (v : word),
              In (o, v) [(-8, Z_to_bv 64 0x50d94); (-16, Z_to_bv 64 8); (-24, Z_to_bv 64 n); (-32, Z_to_bv 64 8); (-40, Z_to_bv 64 (sec_needed n)); (-48, Z_to_bv 64 2048);
                         (-56, Z_to_bv 64 n); (-64, Z_to_bv 64 0x10ab58); (-72, at_ S (-2128)); (-80, Z_to_bv 64 18446744073709551608); (-88, Z_to_bv 64 7)]%Z ->
              rdn BSEGS M1 (at_ (at_ S (-2320)) o) 8 = Some (LE8 v)).
    { intros o v Hin.
      assert (Ho : -88 <= o <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      rewrite at_at. apply RD1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. rewrite <- at_at. exact (MFL o v Hin). }

    (* [comment removed for export] *)
    set (spL := at_ S (-2320)). set (spM := at_ (at_ S (-2320)) (-96)).
    set (szW := Z_to_bv 64 (la_msz (sec_needed n)) : word). set (nmW := Z_to_bv 64 0x1a290 : word).
    assert (Hn1 : 64512 < n) by lia.
    pose proof BD as ((BP0 & BP1) & BC1 & (BK0 & BK1)).
    assert (HnG : 64513 <= n <= GBUDGET) by (unfold GBUDGET, MBLK in *; lia).
    assert (MSZ : la_msz (sec_needed n) = sec_map_size n) by apply la_msz_sec.
    destruct (sec_msz_bnd n Hn1) as [MZ1 MZ2].
    assert (Usz : U szW = sec_map_size n) by ((lazymatch goal with |- ?G => let G' := eval unfold szW in G in change_no_check G' end); rewrite MSZ, u_Z2bv by lia; reflexivity).
    assert (UspM : U spM = U S - 2416) by ((lazymatch goal with |- ?G => let G' := eval unfold spM in G in change_no_check G' end); rewrite at_at, at_u by lia; lia).
    pose proof (same_but_materialized_frame mdl mdl1 SBM1) as (_ & Evm1 & Elz1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehl1 & _ & _ & _ & Eeg1).
    pose proof PRL as (P2 & P8 & P9 & P18 & P19 & P24).
    assert (IMG1 : forall (z : Z) (k : nat) v, In (z, k, v) (bt_consts bt) -> AIMGLO <= z -> z + Z.of_nat k <= AIMGHI ->
              rdn BSEGS M1 (Z_to_bv 64 z) k = Some (word_to_le_bytes k (Z_to_bv 64 v))).
    { intros z k v Hin Hz Hk. pose proof (const_cell bt M _ _ _ R1 Hin) as Cc. unfold cellZ, cellN in Cc. rewrite <- Cc.
      apply rdn_ext; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia.
      destruct (decide (M1 x = M x)) as [E|NE]; [exact E|]. pose proof (OUT1 x NE). lia. }
    assert (NHw : forall x : word, (CEIL <= U x \/ (AIMGLO <= U x /\ U x < AIMGHI)) -> Hd x = false).
    { intros x Hx. pose proof (u64_range x) as Hxr. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHs; [lia | exact Hx]. }
    pose proof (sec_pre_budget bt st Lc FF M mdl B C K n 0 RP W BD Hn1 HB HK ltac:(clear; lia)) as BUD0.   (* [comment removed for export] *)
    pose proof (sec_shs_bnd 0 n ltac:(clear; lia) Hn1) as BUDH.
    assert (NOH : forall z, ~ holes bt st z) by exact (sec_no_holes bt h n st HPH HO Hn1).
    assert (GFACTS : forall mdlm (a : word), same_but_materialized mdl1 mdlm -> grant_ok (Z_to_bv 64 0) mdlm a (sec_map_size n) = true ->
              same_but_materialized mdl mdlm /\ m_vmmaps mdlm = m_vmmaps mdl /\ m_vm_lazy mdlm = m_vm_lazy mdl
              /\ dyn_ok (bt_ia bt) (U a) (U a + sec_map_size n) /\ U a mod PG = 0
              /\ (forall lo hi, In (lo, hi) (all_ranges bt st) -> U a + sec_map_size n <= lo \/ hi <= U a)
              /\ AIMGHI <= U a /\ U a + sec_map_size n <= CEIL).
    { intros mdlm a SBMm G. pose proof (same_but_materialized_trans _ _ _ SBM1 SBMm) as SBM0m.
      destruct (sbm_vmmaps _ _ SBM0m) as [EVm ELm].
      destruct (grant_ok_facts bt st Lc FF M mdl mdlm (2 ^ 20) (2 ^ 28) W RP BOOTG EVm (Z_to_bv 64 0) a (sec_map_size n) h ltac:(lia) MZ1
                  (or_introl NOH) G) as (DY & AL & AP).
      split; [exact SBM0m|]. split; [exact EVm|]. split; [exact ELm|]. split; [exact DY|]. split; [exact AL|]. split; [exact AP|].
      destruct DY as (Y1 & Y2 & Y3 & Y4 & Y5). rewrite BT_ia in Y4. cbn [ia_img_lo ia_img_hi both_addrs] in Y4. split; [lia | exact Y3]. }
    destruct PCELLS as (_ & _ & _ & CELL_dpm & CELL_lim).
    replace (Z_to_bv 64 0x82a74) with (0x82a74%bv : word) by (apply bv_eq; reflexivity).
    apply (mmapordie_katsD Hd (HID_off_segments bt st Lc FF M mdl BT_ia RP) asanF_segs_wx (a_aa st) r5 M1 (seg_rom BSEGS) mdl1 spM (Z_to_bv 64 0x51080)
             (Z_to_bv 64 0x10ae08) (Z_to_bv 64 (0x10ab58 + 64)) szW (Z_to_bv 64 (sec_needed n)) (getr r5 20) (Z_to_bv 64 8) szW nmW PGP 0x19fce8 Qok Qf
             (fun mdlm a => grant_ok (Z_to_bv 64 0) mdlm a (sec_map_size n) = true) (fun mdlm a => mmap_model a szW mdlm)).
    - exact A1.
    - exact P2.
    - exact A10.
    - exact A11.
    - exact P8.
    - exact P9.
    - exact P18.
    - exact P19.
    - reflexivity.
    - exact A21.
    - rewrite UspM. lia.
    - apply ret_ok_lit; [lia | reflexivity].
    - rewrite Usz. split; [exact MZ1 | lia].
    - (lazymatch goal with |- ?G => let G' := eval unfold nmW in G in change_no_check G' end). rewrite u_Z2bv by lia. lia.
    - lia.
    - lia.
    - apply store_ok_bytes; [| rewrite at_u by (rewrite UspM; lia); rewrite UspM; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. intros x Hx. rewrite at_u in Hx by (rewrite UspM; lia). rewrite UspM in Hx. cbn in Hx.
      exact (proj2 (STK1 x ltac:(lia))).
    - exact (IMG1 _ _ _ CELL_pg ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - exact (IMG1 _ _ _ CELL_P ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - exact (IMG1 _ _ _ CELL_gcf ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - change (Some [Z_to_bv 8 0]) with (Some (word_to_le_bytes 1 (Z_to_bv 64 0))). exact (IMG1 _ _ _ CELL_dpm ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - exact (IMG1 _ _ _ CELL_lim ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - intros x Hx. apply NHw. right. lia.
    - intros x Hx. apply NHw. right. lia.
    - intros x Hx. apply NHw. right. lia.
    - intros x Hx. apply NHw. right. lia.
    - intros x Hx. apply NHw. right. lia.
    - intros x Hx. apply NHw. left. rewrite UspM in Hx. lia.
    - rewrite Ehl1. exact HH.
    - rewrite Elz1. apply lazy_cover_HID.
    - exact Bw1.
    - exact MI1.
    - (* [comment removed for export] *) intros mdlm a SBMm G. destruct (GFACTS mdlm a SBMm G) as (_ & _ & _ & _ & _ & _ & GA & GC). rewrite Usz, UspM. lia.
    - (* [comment removed for export] *) intros mdlm rr SBMm MIm HLm B10 B11 B12 B13 B14 B15 Qok' Qf' KOK KKP.
      apply (node2_of_mmap_rw rr _ _ mdlm szW Qok' Qf' HLm B10 B11 B12 B13 B14 B15 ltac:(rewrite Usz; lia) ltac:(rewrite Usz; exact MZ1)).
      + rewrite Usz. apply (sec_grant_ex bt BOK BTOT st Lc FF M mdl mdlm n W RP (same_but_materialized_trans _ _ _ SBM1 SBMm) MIm KC HnG). lia.
      + intros a Ha. rewrite Usz in Ha. exact (KOK a Ha).
      + exact KKP.
    - (* [comment removed for export] *) intros mdlm a SBMm MIm G. destruct (GFACTS mdlm a SBMm G) as (SBM0m & EVm & ELm & _ & _ & _ & GA & GC).
      split; [rewrite mmap_model_halted; pose proof (same_but_materialized_frame mdl mdlm SBM0m) as F;
              destruct F as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HL & _); rewrite HL; exact HH|].
      split; [rewrite mmap_model_lazy, ELm; apply lazy_cover_HID|].
      apply (plain_child_MInv mdl mdlm a szW MW EVm ELm ltac:(rewrite Usz; lia) (a_aa st) MIm). rewrite Usz. lia.
    - (* [comment removed for export] *)
      intros a r' mdlm mdl4 SBMm MIm G SBM4 MI4 MR.
      destruct (GFACTS mdlm a SBMm G) as (SBM0m & EVm & ELm & DY & AL & AP & GA & GC).
      pose proof (u64_range a) as Har.
      destruct MR as (Q10 & Q2 & Q1 & Q8 & Q9 & Q18 & AGm).
      assert (END64 : U a + U szW <= 2 ^ 64) by (rewrite Usz; lia).
      pose proof (plain_child_ledger mdl mdlm mdl4 a szW MW EVm ELm END64 SBM4) as (LV & LN & LL & LR & LB & LSB & LMB & LIS & LLIM & LEG & LMW).
      assert (HL4 : m_halted mdl4 = None).
      { pose proof (same_but_materialized_frame _ _ SBM4) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hh4 & _). rewrite Hh4, mmap_model_halted.
        pose proof (same_but_materialized_frame mdl mdlm SBM0m) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hhm & _). rewrite Hhm. exact HH. }
      match goal with |- katwD _ (mkCfg (mkst _ _ ?m _) _) _ _ => set (MG := m) end.
      assert (CEILS : CEIL + 3584 <= U S) by (rewrite CP2; lia).
      assert (MGout : forall x : word, (U x < U S - 2736 \/ U S - 2416 <= U x) -> ~ (U a <= U x < U a + sec_map_size n) -> MG x = M1 x).
      { intros x Hx Hna. (lazymatch goal with |- ?G => let G' := eval unfold MG in G in change_no_check G' end).
        rewrite wbytes_outside by (wd_lenlit; rewrite ?length_N_to_le_bytes, at_u by (rewrite UspM; lia); rewrite UspM; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia).
        rewrite zfill_out by (rewrite Usz; lia). apply mod_m1_outside; [rewrite UspM; lia | rewrite UspM; lia]. }
      assert (MGgr : mem_grows M1 MG).
      { (lazymatch goal with |- ?G => let G' := eval unfold MG in G in change_no_check G' end). eapply mem_grows_trans; [| apply wbytes_grows]. eapply mem_grows_trans; [| apply zfill_grows_s]. apply mod_m1_grows. }
      assert (MGz : forall x : word, U a <= U x < U a + sec_map_size n -> MG x = Some (Z_to_bv 8 0)).
      { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold MG in G in change_no_check G' end).
        rewrite wbytes_outside by (wd_lenlit; rewrite ?length_N_to_le_bytes, at_u by (rewrite UspM; lia); rewrite UspM; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia).
        apply zfill_in_s. rewrite Usz. exact Hx. }
      assert (RDG : forall (k : Z) (w : nat) (bs : list byte), -2416 <= k -> k + Z.of_nat w <= 0 -> rdn BSEGS M1 (at_ S k) w = Some bs -> rdn BSEGS MG (at_ S k) w = Some bs).
      { intros k w bs K1 K2 Hr. rewrite <- Hr. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]|]. intros x Hx. rewrite at_u in Hx by lia. apply MGout; lia. }
      assert (NCm : forall i : reg, ~ In i mod_clob -> getr r' i = getr r5 i) by (intros i Hi; exact (AGm i Hi)).
      Ltac ncm := (lazymatch goal with |- ?G => let G' := eval unfold mod_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X.
      apply CONT1.
      exists r', MG, mdl4, a. (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). fold S.
      split; [reflexivity|].
      split. { (lazymatch goal with |- ?G => let G' := eval unfold chunk_child in G in change_no_check G' end). replace (Z_to_bv 64 (sec_map_size n)) with szW by ((lazymatch goal with |- ?G => let G' := eval unfold szW in G in change_no_check G' end); rewrite MSZ; reflexivity).
               repeat (split; [assumption|]). exact HL4. }
      split; [exact MI4|]. split; [exact DY|]. split; [exact AL|]. split; [exact AP|].
      split. { intros b0 n0 Hin. exact (grant_apart_maps0 bt st Lc FF M mdl mdlm (2 ^ 20) (2 ^ 28) (Z_to_bv 64 0) a (sec_map_size n) W RP EVm ltac:(lia) MZ1 G b0 n0 Hin). }
      split; [exact Q10|].
      split.
      { exists x18, x19, sz, bsz. (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). fold S.
        split. { (lazymatch goal with |- ?G => let G' := eval unfold la_regs in G in change_no_check G' end). split; [exact Q2|]. split; [exact Q8|]. split; [exact Q9|]. split; [exact Q18|].
                 split; [rewrite NCm by ncm; exact P19 | rewrite NCm by ncm; exact P24]. }
        split; [rewrite NCm by ncm; exact A21|].
        split; [rewrite NCm by ncm; exact B4|]. split; [rewrite NCm by ncm; exact B3|].
        split; [rewrite NCm by ncm; exact A26|]. split; [rewrite NCm by ncm; exact A27|].
        split. { intros k0 v Hin. pose proof (ma_slotsA_range S n x18 x19 _ _ _ _ _ _ k0 v Hin) as [Hk1 Hk2]. apply RDG; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact (FA1 k0 v Hin)]. }
        split. { intros k0 v Hin.
                 assert (Hk : -56 <= k0 /\ k0 + 8 <= 0) by (clear - Hin; cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
                 apply RDG; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact (FI1 k0 v Hin)]. }
        split; [apply RDG; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact FS41]|].
        split; [apply RDG; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact FS81]|].
        split; [exact Lsz|].
        split; [clear - SZ1 SZ2; change (Z.of_nat DMAX) with 6 in SZ2; lia|].
        split; [apply RDG; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact FTR1]|].
        split. { intros o v Hin.
                 assert (Ho : -48 <= o <= -8) by (clear - Hin; cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
                 rewrite at_at. apply RDG; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. rewrite <- at_at. exact (FC1 o v Hin). }
        split. { intros o v Hin.
                 assert (Ho : -88 <= o <= -8) by (clear - Hin; cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
                 rewrite at_at. apply RDG; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. rewrite <- at_at. exact (FL1 o v Hin). }
        intros x Hx. unfold MSTK_A in Hx. destruct (STK1 x ltac:(lia)) as [D1 D2]. split; [exact (MGgr x D1) | eapply store_ok_mono; [exact MGgr | exact D2]]. }
      split. { intros x NE. destruct (Z_lt_le_dec (U x) (U a)) as [L1|L1]; [| destruct (Z_lt_le_dec (U x) (U a + sec_map_size n)) as [L2|L2]; [right; lia|]].
               - left. destruct (Z_lt_le_dec (U x) (U S - 2736)) as [L3|L3]; [exfalso; apply NE; rewrite MGout by lia; destruct (decide (M1 x = M x)) as [E|NE1]; [exact E | pose proof (OUT1 x NE1); lia]|].
                 destruct (Z_lt_le_dec (U x) (U S)) as [L4|L4]; [lia|]. exfalso; apply NE; rewrite MGout by lia; destruct (decide (M1 x = M x)) as [E|NE1]; [exact E | pose proof (OUT1 x NE1); lia].
               - left. destruct (Z_lt_le_dec (U x) (U S - 2736)) as [L3|L3]; [exfalso; apply NE; rewrite MGout by lia; destruct (decide (M1 x = M x)) as [E|NE1]; [exact E | pose proof (OUT1 x NE1); lia]|].
                 destruct (Z_lt_le_dec (U x) (U S)) as [L4|L4]; [lia|]. exfalso; apply NE; rewrite MGout by lia; destruct (decide (M1 x = M x)) as [E|NE1]; [exact E | pose proof (OUT1 x NE1); lia]. }
      split; [exact MGz|].
      split; [eapply mem_grows_trans; [exact GRin | exact MGgr]|].
      apply (same_except_vm_trans mdl mdlm mdl4); [apply same_but_materialized_except_vm; exact SBM0m|].
      apply (same_except_vm_trans mdlm (mmap_model a szW mdlm) mdl4); [apply mmap_except_vm | apply same_but_materialized_except_vm; exact SBM4].
    - (* [comment removed for export] *)
      intros r' mdlm mdl4 SBMm MIm SBM4 MI4 MR.
      pose proof (same_but_materialized_trans _ _ _ SBM1 SBMm) as SBM0m.
      pose proof (same_but_materialized_trans _ _ _ SBM0m SBM4) as SBM04.
      destruct MR as (Q10 & Q2 & Q1 & Q8 & Q9 & Q18 & AGm).
      assert (HL4 : m_halted mdl4 = None).
      { pose proof (same_but_materialized_frame mdl mdl4 SBM04) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hh4 & _). rewrite Hh4. exact HH. }
      match goal with |- katD _ (mkCfg (mkst _ _ ?m _) _) _ => set (MN := m) end.
      assert (CEILS : CEIL + 3584 <= U S) by (rewrite CP2; lia).
      assert (MNout : forall x : word, (U x < U S - 2736 \/ U S - 2416 <= U x) -> MN x = M1 x).
      { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold MN in G in change_no_check G' end).
        rewrite !wbytes_outside by (wd_lenlit; rewrite ?length_N_to_le_bytes, at_u by (rewrite UspM; lia); rewrite UspM; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia).
        apply mod_m1_outside; [rewrite UspM; lia | rewrite UspM; lia]. }
      assert (MNgr : mem_grows M1 MN).
      { (lazymatch goal with |- ?G => let G' := eval unfold MN in G in change_no_check G' end). eapply mem_grows_trans; [| apply wbytes_grows]. eapply mem_grows_trans; [| apply wbytes_grows]. apply mod_m1_grows. }
      assert (RDN : forall (k : Z) (w : nat) (bs : list byte), -2416 <= k -> k + Z.of_nat w <= 0 -> rdn BSEGS M1 (at_ S k) w = Some bs -> rdn BSEGS MN (at_ S k) w = Some bs).
      { intros k w bs K1 K2 Hr. rewrite <- Hr. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]|]. intros x Hx. rewrite at_u in Hx by lia. apply MNout; lia. }
      assert (NCm : forall i : reg, ~ In i mod_clob -> getr r' i = getr r5 i) by (intros i Hi; exact (AGm i Hi)).
      assert (RXN : RepX bt (fun _ : Z => False) st Lc FF MN mdl4).
      { apply (repx_frame_step bt (fun _ : Z => False) st Lc FF M1 MN mdl1 mdl4 W RX1).
        - intros x NE. split.
          + intros RCx. pose proof (rep_cells_lt_ceil bt BT_ia st Lc FF (U x) W RCx) as LT.
            destruct (Z_lt_le_dec (U x) (U S - 2736)) as [L3|L3]; [apply NE; apply MNout; lia|].
            destruct (Z_lt_le_dec (U x) (U S - 2416)) as [L4|L4]; [lia | apply NE; apply MNout; lia].
          + destruct (MN x) eqn:E1; [discriminate|]. exfalso. apply NE. destruct (M1 x) eqn:E2; [|reflexivity].
            exfalso. assert (X : M1 x <> None) by (rewrite E2; discriminate). apply MNgr in X. rewrite E1 in X. exact (X eq_refl).
        - exact MI4.
        - exact (same_but_materialized_trans _ _ _ SBMm SBM4). }
      destruct RXN as (M0n & RPn & DXn).
      assert (EMn : MN = M0n).
      { apply functional_extensionality. intros x. destruct (decide (MN x = M0n x)) as [E|NE]; [exact E | destruct (DXn x NE) as [[] _]]. }
      subst M0n.
      apply CONT0.
      exists r', MN, mdl4. (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). fold S.
      split; [reflexivity|]. split; [exact HL4|]. split; [exact (model_ivs_wf_sbm mdl mdl4 SBM04 MW)|]. split; [exact RPn|].
      split; [exact Q10|].
      split.
      { exists x18, x19, sz, bsz. (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). fold S.
        split. { (lazymatch goal with |- ?G => let G' := eval unfold la_regs in G in change_no_check G' end). split; [exact Q2|]. split; [exact Q8|]. split; [exact Q9|]. split; [exact Q18|].
                 split; [rewrite NCm by ncm; exact P19 | rewrite NCm by ncm; exact P24]. }
        split; [rewrite NCm by ncm; exact A21|].
        split; [rewrite NCm by ncm; exact B4|]. split; [rewrite NCm by ncm; exact B3|].
        split; [rewrite NCm by ncm; exact A26|]. split; [rewrite NCm by ncm; exact A27|].
        split. { intros k0 v Hin. pose proof (ma_slotsA_range S n x18 x19 _ _ _ _ _ _ k0 v Hin) as [Hk1 Hk2]. apply RDN; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact (FA1 k0 v Hin)]. }
        split. { intros k0 v Hin.
                 assert (Hk : -56 <= k0 /\ k0 + 8 <= 0) by (clear - Hin; cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
                 apply RDN; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact (FI1 k0 v Hin)]. }
        split; [apply RDN; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact FS41]|].
        split; [apply RDN; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact FS81]|].
        split; [exact Lsz|].
        split; [clear - SZ1 SZ2; change (Z.of_nat DMAX) with 6 in SZ2; lia|].
        split; [apply RDN; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact FTR1]|].
        split. { intros o v Hin.
                 assert (Ho : -48 <= o <= -8) by (clear - Hin; cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
                 rewrite at_at. apply RDN; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. rewrite <- at_at. exact (FC1 o v Hin). }
        split. { intros o v Hin.
                 assert (Ho : -88 <= o <= -8) by (clear - Hin; cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
                 rewrite at_at. apply RDN; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. rewrite <- at_at. exact (FL1 o v Hin). }
        intros x Hx. unfold MSTK_A in Hx. destruct (STK1 x ltac:(lia)) as [D1 D2]. split; [exact (MNgr x D1) | eapply store_ok_mono; [exact MNgr | exact D2]]. }
      split. { intros x NE. destruct (Z_lt_le_dec (U x) (U S - 2736)) as [L3|L3]; [exfalso; apply NE; rewrite MNout by lia; destruct (decide (M1 x = M x)) as [E|NE1]; [exact E | pose proof (OUT1 x NE1); lia]|].
               destruct (Z_lt_le_dec (U x) (U S)) as [L4|L4]; [lia|]. exfalso; apply NE; rewrite MNout by lia; destruct (decide (M1 x = M x)) as [E|NE1]; [exact E | pose proof (OUT1 x NE1); lia]. }
      split; [apply same_but_materialized_except_vm; exact SBM04|].
      intros z Hz. exact (lazy_kept_sbm bt Lc FF mdl mdl4 SBM04 z Hz).
  Qed.
End TOPSA.
End WithCeil.
