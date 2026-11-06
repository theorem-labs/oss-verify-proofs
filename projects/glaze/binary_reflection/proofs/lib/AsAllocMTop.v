(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA OSSVerify.glaze.binary_reflection.images.Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocMMemAm.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2.AsAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA.AsAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation LE2 z := (word_to_le_bytes 2 (Z_to_bv 64 z)).

Section FPGen.
Context {fx : FPState}.

(* [comment removed for export] *)
Definition ma_Bm (M4 : word -> option byte) (T n mm : Z) (stw csz : word) : word -> option byte :=
  wbytes (wbytes M4 (at_ (Z_to_bv 64 T) (208 + 80 * class_of (needed n))) (LE4 (mm - 1))) (at_ (Z_to_bv 64 T) 2784) (LE8 (v_add stw csz)).
Definition ma_P2m (M4 : word -> option byte) (T n mm : Z) (stw csz m : word) (b1 : byte) : word -> option byte :=
  amC_mem (ma_Bm M4 T n mm stw csz) m b1 n.

Section MEMAM.
  Variables (MP M4 : word -> option byte) (S : word) (T n mm : Z) (stw csz m : word) (b1 : byte) (x18 x19 x22 x23 x24 x25 x26 x27 : word).
  Hypothesis GS : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47)%Z.
  Hypothesis GT : (4096 <= T /\ T + 4096 <= U S - 3584)%Z.
  Hypothesis Gn : (1 <= n <= 64512)%Z.
  Hypothesis Gm : (AIMGHI <= U m /\ U m + needed n <= U S - 3584)%Z.
  #[local] Abbreviation MA := (ma_A MP S n x18 x19 x22 x23 x24 x25 x26 x27).
  #[local] Abbreviation MB := (ma_Bm M4 T n mm stw csz).
  #[local] Abbreviation MC := (ma_P2m M4 T n mm stw csz m b1).
  (* [comment removed for export] *)
  Hypothesis G4 : mem_grows MA M4.
  Hypothesis A4 : forall x : word, (U S - 2272 <= U x)%Z -> M4 x = MA x.

  Lemma mam_B_outside : forall x : word,
    (U x < T + 208 + 80 * class_of (needed n) \/ T + 208 + 80 * class_of (needed n) + 4 <= U x)%Z ->
    (U x < T + 2784 \/ T + 2792 <= U x)%Z -> MB x = M4 x.
  Proof using Gn GT GS S.
    intros x Hy Hz. pose proof (u64_range S). destruct GS as [G1 G2]. destruct GT as [G3 G4']. pose proof (cofn_range n Gn). (lazymatch goal with |- ?G => let G' := eval unfold ma_Bm in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; rewrite ?at_u; unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); try lia. reflexivity.
  Qed.
  Lemma mam_B_grows : mem_grows M4 MB.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold ma_Bm in G in change_no_check G' end). do 2 (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
  Lemma mam_P2_outside : forall x : word, (U x < U m + rz n - 15 \/ U m + rz n - 8 <= U x)%Z -> MC x = MB x.
  Proof using Gm Gn GS S.
    intros x Hx. pose proof (u64_range m). pose proof (u64_range S). destruct Gm as [G1 G2]. pose proof (rzn_range n Gn). pose proof (needed_rz n Gn). (lazymatch goal with |- ?G => let G' := eval unfold ma_P2m, amC_mem in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); rewrite ?at_u; try lia. reflexivity.
  Qed.
  Lemma mam_P2_grows : mem_grows MB MC.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold ma_P2m, amC_mem in G in change_no_check G' end). do 4 (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.





  (* [comment removed for export] *)
  Lemma mam_P2_hdr :
    MC (at_ m (rz n - 15)) = Some (Z_to_bv 8 (U (hb1w (Z_to_bv 64 (U b1)))))
    /\ rdn ASEGS MC (at_ m (rz n - 14)) 2 = Some (LE2 0)
    /\ rdn ASEGS MC (at_ m (rz n - 12)) 4 = Some (LE4 n).
  Proof using Gm Gn GS S.
    pose proof (u64_range S). pose proof (u64_range m). destruct GS as [G1 G2]. destruct Gm as [G5 G6]. pose proof (rzn_range n Gn). pose proof (needed_rz n Gn).
    (lazymatch goal with |- ?G => let G' := eval unfold ma_P2m, amC_mem in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). split; [|split].
    - rewrite wbytes_inside; [| (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); rewrite at_u; lia | (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); rewrite at_u; lia].
      rewrite Z.sub_diag. reflexivity.
    - rewrite wc_rdn_wbytes_out3; [ | rd8_side ]. rewrite wc_rdn_wbytes_out3; [ | rd8_side ].
      apply rdn_wbytes_hitw. rewrite at_u by lia. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia.
    - rewrite wc_rdn_wbytes_out3; [ | rd8_side ].
      apply rdn_wbytes_hitw. rewrite at_u by lia. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mam_P2_cnt : (U m + needed n <= T \/ T + 4096 <= U m)%Z ->
    rdn ASEGS MC (at_ (Z_to_bv 64 T) (208 + 80 * class_of (needed n))) 4 = Some (LE4 (mm - 1)).
  Proof using Gm Gn GT GS S.
    intros GmT. pose proof (u64_range S). pose proof (u64_range m). destruct GS as [G1 G2]. destruct GT as [G3 G4']. destruct Gm as [G5 G6].
    pose proof (cofn_range n Gn) as Hc. pose proof (rzn_range n Gn). pose proof (needed_rz n Gn).
    assert (HB : rdn ASEGS MB (at_ (Z_to_bv 64 T) (208 + 80 * class_of (needed n))) 4 = Some (LE4 (mm - 1))).
    { (lazymatch goal with |- ?G => let G' := eval unfold ma_Bm in G in change_no_check G' end). rewrite wc_rdn_wbytes_out3; [ | rd8_side ]. apply rdn_wbytes_hitw. rewrite at_u by (wd_ulia). unorm. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. }
    eapply (rd_same ASEGS); [| rewrite at_u by (wd_ulia); wd_ulia_c | exact HB].
    intros x Hx. rewrite at_u in Hx by (wd_ulia). revert Hx; unorm; intros Hx. cbn in Hx. apply mam_P2_outside. lia.
  Qed.
End MEMAM.
End FPGen.
End AsAllocMMemAm.
Require LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsDepotHyp8.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp.

#[local] Abbreviation U := bv_unsigned.

Section WithCeil.
Context {RC : run_ceil}.

End WithCeil.
End AsDepotHyp8.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocMXTrk.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvXTrk3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocMHyp.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section XTrk.
  Context {RC : run_ceil}.
  Variable bt : as_boot.

  Lemma Xm_xtracked : forall st Lc FF (M : mem) mdl n ks kk S T0 p,
    WF bt st Lc FF -> Rep bt st Lc FF M mdl -> 1 <= n <= 64512 -> a_cache st (class_of (needed n)) = ks ++ [kk] ->
    T0 = bt_thread bt -> CEIL + 2480 <= S ->
    (let c := class_of (needed n) in let ab := chunk_of_compact (bt_spacebeg bt) c kk in ab + 16 <= p /\ p <= ab + csize c) ->
    forall a, Xm S T0 (class_of (needed n)) p a ->
      CEIL <= a \/ exists lo hi, In (lo, hi) (bt_fixed bt ++ List.map (fun s => (sc_map s, sc_map s + sc_mapsz s)) (a_sec st))
                                 /\ lo <= a < hi /\ lo <> bt_nodes0 bt /\ lo <> bt_store0 bt.
  Proof using.
    intros st Lc FF M mdl n ks kk S T0 p W RP Hn HC ET HS HP a Ha. cbv zeta in HP.
    pose proof (mc_needed n Hn) as (_ & _ & Hc & _).
    pose proof (mc_chunk bt st Lc FF M mdl n ks kk W RP Hn HC) as (CV & _).
    destruct (carved_range bt st Lc FF W _ _ Hc CV) as (_ & _ & S1 & S2 & _).
    unfold Xm, T_PC, PC_SZ in Ha. destruct Ha as [Ha|[Ha|[Ha|Ha]]].
    - left. lia.
    - subst T0. apply (xtracked_thread bt st Lc FF (2 ^ 20) (2 ^ 28) W a). (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). pose proof Hc. lia.
    - subst T0. apply (xtracked_thread bt st Lc FF (2 ^ 20) (2 ^ 28) W a). (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). lia.
    - apply (xtracked_space bt st Lc FF (2 ^ 20) (2 ^ 28) W a). (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). lia.
  Qed.
End XTrk.
End AsAllocMXTrk.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunA OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys7b OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocMTopA.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23.AsAinvOpsQ3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2.AsAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA.AsAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocMHyp.
Import AsDepotHyp8 AsAllocMXTrk.

Import OSSVerify.glaze.binary_reflection.images.Asan.

Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac am_inner ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
#[local] Ltac lia ::= ha_first_lia.   (* [comment removed for export] *)
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma mod4096_mod8 : forall t, t mod 4096 = 0 -> t mod 8 = 0.
Proof. intros t Ht. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma restrict_mkst' : forall {fx : FPState} (Hd : word -> bool) (r : bvmap 5 word) pc m rom,
  restrict Hd (@mkst fx r pc m rom) = @mkst fx r pc (mrestrict Hd m) rom.
Proof. intros. reflexivity. Qed.

Section WithCeil.
Context {RC : run_ceil}.

Section TOPA.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND KD : Z).
  Hypothesis BT_segs : bt_segs bt = ASEGS.
  Hypothesis BT_ia : bt_ia bt = asan_addrs.
  Hypothesis CELLS : malloc_cells bt TP TSDP PGP FL MIDEND.
  Hypothesis GEOM : free_boot_geom bt.
  Hypothesis G_KD : 0 <= KD <= 1312.
  Hypothesis HYP_DEPOT : AsAllocFHyp.HYP_DEPOT_stmt bt FXOK KD.   (* [comment removed for export] *)
  Hypothesis HTP : TP = ia_tp asan_addrs.

  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation CTX := (bt_tctx bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).

  (* [comment removed for export] *)
  Lemma thread_dyn : forall st Lc FF, WF bt st Lc FF ->
    0 < T /\ T + PG <= CEIL /\ (T + PG <= ia_img_lo (bt_ia bt) \/ ia_img_hi (bt_ia bt) <= T) /\ (T + PG <= AS_LO \/ AS_HEAPLO <= T) /\ T mod PG = 0
    /\ 0 < CTX /\ CTX + 0x10000 <= CEIL /\ (CTX + 0x10000 <= ia_img_lo (bt_ia bt) \/ ia_img_hi (bt_ia bt) <= CTX)
    /\ (CTX + 0x10000 <= AS_LO \/ AS_HEAPLO <= CTX)
    /\ 0 <= SBEG /\ SBEG + KSPACE + PG <= CEIL.
  Proof using.
    intros st Lc FF W.
    pose proof (fixed_facts bt st Lc FF W) as (T1 & T2 & C1 & C2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Y1 & Y2 & _).
    destruct W as (_ & _ & _ & _ & _ & _ & _ & _ & WM & _).
    destruct WM as (RNG & _ & _ & _ & _ & _ & _ & INT & _ & _ & INC & _).
    destruct (RNG _ _ (all_ranges_fixed bt st _ INT)) as ((D1 & D2 & D3 & D4 & D5) & _ & D6 & _).
    destruct (RNG _ _ (all_ranges_fixed bt st _ INC)) as ((E1 & E2 & E3 & E4 & E5) & _).
    unfold KSPACE, PG in *.
    repeat split; try assumption; lia.
  Qed.

  (* [comment removed for export] *)
  Definition runA_st (st : ast) (d' : depot) (naa : list (Z * Z)) : ast :=
    AST (a_reg st) (a_cinit st) (a_cache st) (a_tq st) (a_gq st) (a_sec st) (a_nres st) d' (a_hint st) (a_ialloc st)
        (a_aa st ++ naa) (a_kact st + EVT) (a_shsec st).

  (* [comment removed for export] *)
  Definition runA_post (st : ast) (ks : list Z) (kk : Z) (Lc FF : list (Z * Z)) (R : bvmap 5 word) (M : mem) (mdl : Model) (n : Z)
             (c' : config) : Prop :=
    exists fx' (R' : bvmap 5 word) (M' M0 : mem) (mdl' : Model) (d' : depot) (naa : list (Z * Z)) (id : Z) (b1 : byte) (x18 x19 : word),
      let S := getr R 2 in
      let c := class_of (needed n) in
      let ab := chunk_of_compact SBEG c kk in
      let p := ab + rz n in
      let st' := runA_st st d' naa in
      c' = mkCfg (@mkst fx' R' (Z_to_bv 64 0x4bed0) M' (seg_rom ASEGS)) mdl'
      /\ FXOK fx' /\ m_halted mdl' = None /\ BackingAlgebra.model_ivs_wf mdl'
      /\ WF bt st' Lc FF /\ Rep bt st' Lc FF M0 mdl'
      /\ (forall a : word, M' a <> M0 a -> Xm (U S) T c p (U a) /\ M' a <> None)
      /\ (forall a : word, M' a <> M a ->
            (Xm (U S) T c p (U a) \/ (U S - 3584 <= U a < U S - 2272)
             \/ rt_priv (bt_ia bt) Lc FF (U a) \/ in_wins (ia_priv (bt_ia bt)) (U a))
            /\ M' a <> None)
      (* [comment removed for export] *)
      /\ (forall (k0 : Z) (v : word),
             In (k0, v) (ma_slotsA S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27)) ->
             rdn ASEGS M' (at_ S k0) 8 = Some (LE8 v))
      /\ (forall (k0 : Z) (v : word),
             In (k0, v) [(-8, getr R 1); (-16, getr R 8); (-24, getr R 9); (-32, getr R 18); (-40, getr R 19); (-48, getr R 20); (-56, getr R 21)]%Z ->
             rdn ASEGS M' (at_ S k0) 8 = Some (LE8 v))
      (* [comment removed for export] *)
      /\ M' (Z_to_bv 64 (p - 15)) = Some (Z_to_bv 8 (U (hb1w (Z_to_bv 64 (U b1)))))
      /\ rdn ASEGS M' (Z_to_bv 64 (p - 14)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 0))
      /\ rdn ASEGS M' (Z_to_bv 64 (p - 12)) 4 = Some (LE4 n)
      (* [comment removed for export] *)
      /\ rdn ASEGS M' (Z_to_bv 64 (T + T_PC + PC_SZ * c)) 4 = Some (LE4 (Z.of_nat (length ks)))
      (* [comment removed for export] *)
      /\ getr R' 2 = at_ S (-2272) /\ getr R' 4 = getr R 4 /\ getr R' 3 = getr R 3
      /\ getr R' 8 = Z_to_bv 64 1 /\ getr R' 9 = Z_to_bv 64 n /\ getr R' 10 = Z_to_bv 64 id /\ getr R' 18 = Z_to_bv 64 ab
      /\ getr R' 19 = Z_to_bv 64 (needed n) /\ getr R' 20 = at_ (Z_to_bv 64 ab) (rz n) /\ getr R' 21 = at_ (Z_to_bv 64 ab) (rz n - 16)
      /\ getr R' 22 = Z_to_bv 64 0x103f18 /\ getr R' 23 = at_ S (-2128) /\ getr R' 24 = Z_to_bv 64 0
      /\ getr R' 25 = at_ (Z_to_bv 64 ab) (rz n + n) /\ getr R' 26 = Z_to_bv 64 T /\ getr R' 27 = Z_to_bv 64 1
      /\ 0 <= id < 2 ^ 32
      /\ same_except_vm mdl mdl'
      /\ lazy_kept (bt_ia bt) Lc FF mdl mdl'.     (* [comment removed for export] *)

  Theorem malloc_runA :
    forall fx (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF : list (Z * Z)) (B C K ret sp n : Z) (st : ast) (ks : list Z) (kk : Z),
      FXOK fx -> m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
      WF bt st Lc FF -> Rep bt st Lc FF M mdl -> bounds st Lc B C K ->
      call_pre ASEGS asan_addrs R M ret sp MSTK_A -> U (getr R 10) = n -> 1 <= n <= 64512 -> fpc M (U (getr R 8)) sp DMAX ->
      K + kcost_malloc n <= KCAP ->
      a_cache st (class_of (needed n)) = ks ++ [kk] ->
      (exists h : option Z, holes_le h st) ->                                           (* [comment removed for export] *)
      katD ASEGS (cfg ASEGS fx R (ia_malloc asan_addrs) M mdl) (runA_post st ks kk Lc FF R M mdl n).
  Proof using HTP HYP_DEPOT G_KD GEOM CELLS BT_ia BT_segs KD MIDEND FL PGP TSDP TP.
    intros fx R M mdl Lc FF B C K ret sp n st ks kk HFX HH MW W RP BD CP HR10 Hn FPC HK HC HOLES.
    pose proof ceil_rng as CR. pose proof ceil_pg as CPG.
    set (S := getr R 2) in *. set (ra0 := getr R 1). set (tp := getr R 4).
    set (c := class_of (needed n)) in *. set (ab := chunk_of_compact SBEG c kk) in *. set (p := ab + rz n) in *.
    destruct CP as (CP1 & CPr & CPe & CP2 & CP16 & CPlo & CPhi & CP4 & CPstk). fold S ra0 tp in CP1, CP2, CP4. rewrite <- HTP in CP4.
    destruct CELLS as (CELL_mcs & CELL_gcf & CELL_fum & CELL_inited & CELL_pg & CELL_P & CELL_kif & CELL_key & CELL_tsdp & CELL_tctx
                      & CELL_rss & CELL_lmag & CELL_tbl2 & CELL_t16 & CELL_t2048 & CELL_minrz & CELL_maxrz & CELL_maxsz & CELL_sbeg
                      & CELL_cpm & CELL_gsh & CELL_gmb & CELL_mb & CELL_gme & CELL_me & CELL_ghe & CELL_he & CELL_gfl & CELL_pp & CELL_mfs & CELL_fill
                      & CELL_grm & CELL_rm & CELL_glsn & CELL_lsn & CELL_magic & CELL_hook & CELL_thr64 & G_consts).
    destruct G_consts as (Gc1 & Gc2 & Gc3 & Gc4 & Gc5 & Gc6 & Gc7 & Gc8 & Gc9).
    destruct GEOM as (GCT & Gtop & Gbot).
    pose proof (free_obls_pf bt) as (OBL_nolazy_rt & _ & OBL_rt_private & OBL_stats_not_rep & _ & _ & _ & OBL_X_vs_node & OBL_store_private).
    unfold OBL_nolazy_rt_stmt in OBL_nolazy_rt. unfold OBL_rt_private_stmt in OBL_rt_private. unfold OBL_stats_not_rep_stmt in OBL_stats_not_rep.
    unfold OBL_X_vs_node_stmt in OBL_X_vs_node. unfold OBL_store_private_stmt in OBL_store_private.
    (* [comment removed for export] *)
    pose proof (mc_needed n Hn) as (NF1 & NF2 & NF3 & NF4 & NF5 & NF6 & NF7 & NF8). fold c in NF3, NF4.
    pose proof (mc_chunk bt st Lc FF M mdl n ks kk W RP Hn HC) as (CV & A1 & A2 & A16 & Hkk & AT & ACT & ALIV & ABAT & ANL & AW & APRIV).
    fold c in CV, A1, A2, A16, AT, ACT, ALIV, ABAT, ANL, AW, APRIV. fold ab in CV, A1, A2, A16, AT, ACT, ALIV, ABAT, ANL, AW, APRIV.
    pose proof (mc_pclass bt st Lc FF M mdl n ks kk W RP Hn HC) as (Pcnt & Pk & (cszv & Pcsz) & Plen). fold c in Pcnt, Pk, Pcsz.
    pose proof (mc_vs_node bt st Lc FF M mdl n ks kk W RP Hn HC) as ANODE. fold c ab in ANODE.
    hidehyp AT. hidehyp ACT. hidehyp GCT.
    (* [comment removed for export] *)
    pose proof (thread_dyn st Lc FF W) as (GT0 & GTC & GTI & GTB & TPG & GC0 & GCC & GCI & GCB & SB0 & SB1). hidehyp GCB.
    hidehyp GTB.
    assert (GT4 : 4096 <= T) by (unfold PG in TPG; clear - GT0 TPG; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    pose proof RP as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18).
    destruct R3 as (Tctx & Ttop & Tbot & Tsw & Tfs & Tunw & TQ & TPC & TW & Tback & Ttid & Ttls1 & Ttls2).
    rewrite BT_segs in *. rewrite BT_ia in *. cbn [ia_img_lo ia_img_hi asan_addrs] in GTI, GCI.
    pose proof (u64_range S) as HSr.
    unfold PTRHI in CPlo, CPhi. unfold AS_HEAPLO, AS_LO, MSTK_A, PG, KSPACE, NMAX in *.
    (* [comment removed for export] *)
    set (Hd := HID st mdl).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st mdl z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi asan_addrs] in G in change_no_check G' end). lia. }
    assert (NHrt : forall z, (T <= z < T + 4096) \/ (CTX <= z < CTX + 0x10000) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply (OBL_nolazy_rt st Lc FF M mdl z W RP). (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). (first [clear - Hz | idtac]; am_tauto). }
    assert (NHab : forall z, ab <= z < ab + csize c -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. exact (ANL z Hz). }
    destruct R14 as (Bw1 & Bw2 & Bw3 & Bw4 & Bw5).
    set (Mr := mrestrict Hd M).
    Ltac hoff NH := apply hid_off_of; intros z Hz; unfold T_UNW, T_QC, T_PC, PC_SZ in *; split; [lia | apply NH; lia].
    Ltac konst Hd M R1 NHs C := apply (cellZ_restrict Hd M _ _ _ (const_cell bt M _ _ _ R1 C)); [lia | lia | hoff NHs].
    (* [comment removed for export] *)
    assert (K_mcs : rdn ASEGS Mr (Z_to_bv 64 0x10827c) 4 = Some (LE4 30)) by konst Hd M R1 NHs CELL_mcs.
    assert (K_gcf : rdn ASEGS Mr (Z_to_bv 64 0xff260) 8 = Some (LE8 (Z_to_bv 64 0x1990a8))) by konst Hd M R1 NHs CELL_gcf.
    assert (K_fum : rdn ASEGS Mr (Z_to_bv 64 0x1990ca) 1 = Some [Z_to_bv 8 1]) by konst Hd M R1 NHs CELL_fum.
    assert (K_inited : rdn ASEGS Mr (Z_to_bv 64 0x108258) 1 = Some [Z_to_bv 8 1]) by konst Hd M R1 NHs CELL_inited.
    assert (K_pg : rdn ASEGS Mr (Z_to_bv 64 0xff250) 8 = Some (LE8 (Z_to_bv 64 PGP))) by konst Hd M R1 NHs CELL_pg.
    assert (K_P : rdn ASEGS Mr (Z_to_bv 64 PGP) 8 = Some (LE8 (Z_to_bv 64 4096))) by konst Hd M R1 NHs CELL_P.
    assert (K_kif : rdn ASEGS Mr (Z_to_bv 64 0x106de0) 1 = Some [Z_to_bv 8 1]) by konst Hd M R1 NHs CELL_kif.
    assert (K_key : rdn ASEGS Mr (at_ (Z_to_bv 64 0x106de0) 4) 4 = Some (LE4 0)).
    { replace (at_ (Z_to_bv 64 0x106de0) 4) with (Z_to_bv 64 0x106de4 : word) by (apply bv_eq; reflexivity). konst Hd M R1 NHs CELL_key. }
    assert (K_tsdp : rdn ASEGS Mr (at_ tp (-88)) 8 = Some (LE8 (Z_to_bv 64 TSDP))).
    { replace (at_ tp (-88)) with (Z_to_bv 64 (TP - 88)) by (apply bv_eq; rewrite at_u by (rewrite CP4; wd_ulia_c); rewrite CP4; wd_ulia_c). konst Hd M R1 NHs CELL_tsdp. }
    assert (K_tctx : rdn ASEGS Mr (Z_to_bv 64 TSDP) 8 = Some (LE8 (Z_to_bv 64 CTX))) by konst Hd M R1 NHs CELL_tctx.
    assert (K_rss : rdn ASEGS Mr (Z_to_bv 64 0x1897e2) 1 = Some [Z_to_bv 8 0]) by konst Hd M R1 NHs CELL_rss.
    assert (K_lmag : rdn ASEGS Mr (Z_to_bv 64 0x10490) 8 = Some (LE8 MAGICw)).
    { (lazymatch goal with |- ?G => let G' := eval unfold MAGICw in G in change_no_check G' end). konst Hd M R1 NHs CELL_lmag. }
    assert (K_tbl2 : rdn ASEGS Mr (at_ (Z_to_bv 64 0x10500) 4) 1 = Some [Z_to_bv 8 3]).
    { replace (at_ (Z_to_bv 64 0x10500) 4) with (Z_to_bv 64 0x10504 : word) by (apply bv_eq; reflexivity). rewrite <- w2b1 by lia. konst Hd M R1 NHs CELL_tbl2. }
    assert (K_t16 : rdn ASEGS Mr (at_ (Z_to_bv 64 0x10600) 8) 1 = Some [Z_to_bv 8 4]).
    { replace (at_ (Z_to_bv 64 0x10600) 8) with (Z_to_bv 64 0x10608 : word) by (apply bv_eq; reflexivity). rewrite <- w2b1 by lia. konst Hd M R1 NHs CELL_t16. }
    assert (K_t2048 : rdn ASEGS Mr (at_ (Z_to_bv 64 0x10600) 49) 1 = Some [Z_to_bv 8 11]).
    { replace (at_ (Z_to_bv 64 0x10600) 49) with (Z_to_bv 64 0x10631 : word) by (apply bv_eq; reflexivity). rewrite <- w2b1 by lia. konst Hd M R1 NHs CELL_t2048. }
    assert (K_minrz : rdn ASEGS Mr (at_ (Z_to_bv 64 0x103f18) 3624) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 16))).
    { replace (at_ (Z_to_bv 64 0x103f18) 3624) with (Z_to_bv 64 0x104d40 : word) by (apply bv_eq; reflexivity). konst Hd M R1 NHs CELL_minrz. }
    assert (K_maxrz : rdn ASEGS Mr (at_ (Z_to_bv 64 0x103f18) 3626) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 2048))).
    { replace (at_ (Z_to_bv 64 0x103f18) 3626) with (Z_to_bv 64 0x104d42 : word) by (apply bv_eq; reflexivity). konst Hd M R1 NHs CELL_maxrz. }
    assert (K_maxsz : rdn ASEGS Mr (at_ (Z_to_bv 64 0x103f18) 3616) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 40)))).
    { replace (at_ (Z_to_bv 64 0x103f18) 3616) with (Z_to_bv 64 0x104d38 : word) by (apply bv_eq; reflexivity). konst Hd M R1 NHs CELL_maxsz. }
    assert (K_sbeg : rdn ASEGS Mr (at_ (Z_to_bv 64 0x103f18) 32) 8 = Some (LE8 (Z_to_bv 64 SBEG))).
    { replace (at_ (Z_to_bv 64 0x103f18) 32) with (Z_to_bv 64 0x103f38 : word) by (apply bv_eq; reflexivity). konst Hd M R1 NHs CELL_sbeg. }
    (* [comment removed for export] *)
    Ltac thr_cell Hd M NHrt C := apply (cellZ_restrict Hd M _ _ _ C); [(lazymatch goal with |- ?G => let G' := eval unfold T_UNW, T_QC, T_PC, PC_SZ in G in change_no_check G' end); lia | unfold T_UNW, T_QC, T_PC, PC_SZ in *; lia | hoff NHrt].
    assert (K_thr : rdn ASEGS Mr (at_ (Z_to_bv 64 CTX) 152) 8 = Some (LE8 (Z_to_bv 64 T))).
    { replace (at_ (Z_to_bv 64 CTX) 152) with (Z_to_bv 64 (CTX + 152)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Tback. }
    assert (K_T0 : rdn ASEGS Mr (Z_to_bv 64 T) 8 = Some (LE8 (Z_to_bv 64 CTX))) by thr_cell Hd M NHrt Tctx.
    assert (K_tid : rdn ASEGS Mr (at_ (Z_to_bv 64 CTX) 8) 4 = Some (LE4 0)).
    { replace (at_ (Z_to_bv 64 CTX) 8) with (Z_to_bv 64 (CTX + 8)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Ttid. }
    assert (K_unw : rdn ASEGS Mr (at_ (Z_to_bv 64 T) 3168) 1 = Some [Z_to_bv 8 0]).
    { replace (at_ (Z_to_bv 64 T) 3168) with (Z_to_bv 64 (T + T_UNW)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_, T_UNW in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Tunw. }
    assert (K_sw : rdn ASEGS Mr (at_ (Z_to_bv 64 T) 40) 1 = Some [Z_to_bv 8 0]).
    { replace (at_ (Z_to_bv 64 T) 40) with (Z_to_bv 64 (T + 40)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Tsw. }
    assert (K_top : rdn ASEGS Mr (at_ (Z_to_bv 64 T) 8) 8 = Some (LE8 (Z_to_bv 64 (bt_stack_top bt)))).
    { replace (at_ (Z_to_bv 64 T) 8) with (Z_to_bv 64 (T + 8)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Ttop. }
    assert (K_bot : rdn ASEGS Mr (at_ (Z_to_bv 64 T) 16) 8 = Some (LE8 (Z_to_bv 64 (bt_stack_bottom bt)))).
    { replace (at_ (Z_to_bv 64 T) 16) with (Z_to_bv 64 (T + 16)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Tbot. }
    assert (K_cnt : rdn ASEGS Mr (at_ (Z_to_bv 64 T) (208 + 80 * c)) 4 = Some (LE4 (Z.of_nat (length ks) + 1))).
    { replace (at_ (Z_to_bv 64 T) (208 + 80 * c)) with (Z_to_bv 64 (T + T_PC + PC_SZ * c)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_, T_PC, PC_SZ in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Pcnt. }
    assert (K_k : rdn ASEGS Mr (at_ (Z_to_bv 64 T) (208 + 80 * c + 16 + 4 * (Z.of_nat (length ks) + 1 - 1))) 4 = Some (LE4 kk)).
    { replace (at_ (Z_to_bv 64 T) (208 + 80 * c + 16 + 4 * (Z.of_nat (length ks) + 1 - 1))) with (Z_to_bv 64 (T + T_PC + PC_SZ * c + 16 + 4 * Z.of_nat (length ks)))
        by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_, T_PC, PC_SZ in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Pk. }
    assert (K_csz : rdn ASEGS Mr (at_ (Z_to_bv 64 T) (208 + 80 * c + 8)) 8 = Some (LE8 (Z_to_bv 64 cszv))).
    { replace (at_ (Z_to_bv 64 T) (208 + 80 * c + 8)) with (Z_to_bv 64 (T + T_PC + PC_SZ * c + 8)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_, T_PC, PC_SZ in G in change_no_check G' end); wd_ulia). thr_cell Hd M NHrt Pcsz. }
    (* [comment removed for export] *)
    assert (SOKstk : store_ok ASEGS Mr (at_ S (-3584)) 3584 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| rewrite at_u by (first [clear - CR CPlo CP2 CPhi | idtac]; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); (first [clear - CPhi CP2 | idtac]; lia) | rewrite at_u by (first [clear - CR CPlo CP2 CPhi | idtac]; lia); hoff NHs].
      apply store_ok_bytes; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. intros x Hx. rewrite at_u in Hx by lia. apply CPstk. cbn in Hx. lia. }
    assert (SOKT : store_ok ASEGS Mr (Z_to_bv 64 T) 4096 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); (first [clear - GTC CPhi CPlo | idtac]; lia) | unorm; hoff NHrt].
      apply (writableZ_store_ok M _ _ _ _ TW); unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); (first [clear - GTC CPhi CPlo | idtac]; lia). }
    assert (SOKab : store_ok ASEGS Mr (Z_to_bv 64 ab) (Z.to_nat (needed n)) = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| unorm; rewrite Z2Nat.id by (first [clear - NF1 | idtac]; lia); (first [clear - A2 NF4 CPhi CPlo | idtac]; lia) | unorm; rewrite Z2Nat.id by (first [clear - NF1 | idtac]; lia); hoff NHab].
      apply (writableZ_store_ok M _ _ _ _ AW); unorm; rewrite ?Z2Nat.id by (first [clear - NF1 | idtac]; lia); (first [clear - NF4 A2 CPhi CPlo | idtac]; lia). }
    destruct (rdn_defined_ex ASEGS Mr (Z_to_bv 64 (T + 2784)) 8) as (bst & Cst & Lst).
    { intros i Hi. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite mrestrict_off; [| apply NHrt; revert Hi; unorm; intros Hi; lia].
      apply (writableZ_def M _ _ _ TW). revert Hi; unorm; intros Hi. lia. }
    { unorm. lia. }
    destruct (rdn_defined_ex ASEGS Mr (at_ (Z_to_bv 64 ab) (rz n - 15)) 1) as (bb1 & Cb1 & Lb1).
    { intros i Hi. rewrite at_u in Hi by (unorm; (first [clear - A1 NF7 NF6 NF1 Hn A2 NF4 CPhi CPlo | idtac]; lia)). (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite mrestrict_off; [| apply NHab; revert Hi; unorm; intros Hi; lia].
      apply (writableZ_def M _ _ _ AW). revert Hi; unorm; intros Hi. lia. }
    { rewrite at_u by (unorm; (first [clear - A1 NF7 NF6 NF1 Hn A2 NF4 CPhi CPlo | idtac]; lia)). unorm. lia. }
    destruct bb1 as [|b1 [|]]; try discriminate Lb1.
    (* [comment removed for export] *)
    assert (FPCr : fpc Mr (U (getr R 8)) (U S) DMAX).
    { rewrite CP2. apply (fpc_kept_gen M _ _ _ FPC Mr). destruct (fpc_shape _ _ _ _ FPC) as [ST|FR]; [left; exact ST | right].
      intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). apply mrestrict_off. apply NHs; unfold PTRHI in *; lia. }
    (* [comment removed for export] *)
    assert (En : getr R 10 = Z_to_bv 64 n) by (rewrite <- HR10; symmetry; apply Z_to_bv_bv_unsigned).
    destruct (run_mA Mr (seg_rom ASEGS) R S ra0 tp (Z_to_bv 64 TSDP) (Z_to_bv 64 PGP) (Z_to_bv 64 (bt_stack_top bt)) (Z_to_bv 64 (bt_stack_bottom bt))
                (Z_to_bv 64 cszv) (Z_to_bv 64 (bytes_le_to_Z bst)) T CTX n SBEG (Z.of_nat (length ks) + 1) kk DMAX b1
                eq_refl eq_refl eq_refl En)
      as (r4 & MP & sz & bsz & x18 & x19 & RUN & X1 & X2 & X4 & X3 & X10 & X11 & X8 & X9 & X18 & X19 & X20 & X21 & X22 & X23 & X24 & X25 & X26 & X27
          & SZ1 & SZ2 & FOOTP & GRP & Psz4 & Psz8 & Lsz & Ptr & Pslots).
    (* [comment removed for export] *)
    all: try assumption.
    all: try (unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); (first [clear - Gc2 Gc1 Gc4 Gc3 Gtop Gbot SB1 SB0 CPhi CPlo Plen | idtac]; lia)).
    all: try (rewrite CP4; wd_ulia_c).
    all: try (rewrite CP2; unfold hide in *; unfold PG in *; (first [clear - CR CPhi CPlo CP16 GCC GC0 GCT | idtac]; lia)).
    all: try (change (ma_ab n SBEG kk) with ab; rewrite ?CP2; unfold hide in *; unfold PG in *; (first [clear - A16 A2 A1 NF4 NF1 CR CPlo AT ACT | idtac]; lia)).
    all: try (rewrite CP2; split; [lia|]; split; [lia | apply mod4096_mod8; exact TPG]).
    all: try ((* [comment removed for export] *) rewrite (word_to_le_bytes_of_bytes8 bst Lst);
              replace (at_ (Z_to_bv 64 T) 2784) with (Z_to_bv 64 (T + 2784)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; (repeat match goal with H : _ |- _ => clear H end; lia)); exact Cst).
    all: let k := numgoals in guard k = 1.
    (* [comment removed for export] *)
    (lazymatch goal with |- ?G => let G' := eval unfold cfg in G in change_no_check G' end). replace (Z_to_bv 64 (ia_malloc asan_addrs)) with (Z_to_bv 64 0x6e4cc : word) by (apply bv_eq; reflexivity).
    set (MC := ma_P2 MP S T n (Z.of_nat (length ks) + 1) (Z_to_bv 64 (bytes_le_to_Z bst)) (Z_to_bv 64 cszv) (Z_to_bv 64 (ma_ab n SBEG kk)) b1 x18 x19
                       (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27)) in RUN.
    apply (katD_msteps_acct ASEGS Hd (HID_off_segments bt st Lc FF M mdl BT_ia RP) asanF_segs_wx (a_aa st)
             (@mkst fx R (Z_to_bv 64 0x6e4cc) M (seg_rom ASEGS)) (@mkst fx r4 (Z_to_bv 64 0x8ea80) MC (seg_rom ASEGS)) mdl).
    { apply lazy_cover_HID. }
    { exact Bw1. }
    { exact Bw2. }
    { exact HH. }
    { rewrite restrict_mkst'. exact RUN. }
    intros mdl1 MI1 SBM1 HC1. rewrite unrestrict_mkst.
    replace (ms_mem (@mkst fx R (Z_to_bv 64 0x6e4cc) M (seg_rom ASEGS))) with M by reflexivity.
    pose proof (same_but_materialized_frame mdl mdl1 SBM1) as SF1.
    set (MDin := munrestrict Hd M MC).
    (* [comment removed for export] *)
    set (st1 := op_meter st EVT [] 0).
    assert (W1 : WF bt st1 Lc FF) by (apply WF_meter; [exact W | (lazymatch goal with |- ?G => let G' := eval unfold EVT in G in change_no_check G' end); lia | reflexivity]   (* [comment removed for export] *)).
    destruct SF1 as (_ & Evm & Elz & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehl & _ & _ & _ & Eeg).
    assert (RP1 : Rep bt st1 Lc FF M mdl1).
    { pose proof (Rep_sbm bt st Lc FF M mdl mdl1 RP MI1 SBM1) as RPm.
      apply (OPS_REP_meter_pf bt st Lc FF M mdl1 mdl1 EVT [] 0 RPm eq_refl).
      - intros a; am_tauto.
      - pose proof RPm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & FA & _) & _). exact FA.
      - rewrite app_nil_r. exact Bw1.
      - rewrite app_nil_r. exact MI1.
      - lia.
      - (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. }
    (* [comment removed for export] *)
    assert (Uab : U (Z_to_bv 64 (ma_ab n SBEG kk)) = ab) by (change (ma_ab n SBEG kk) with ab; unorm; reflexivity).
    assert (GSm : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47) by (rewrite CP2; lia).
    assert (GTm : 4096 <= T /\ T + 4096 <= U S - 3584) by (rewrite CP2; lia).
    assert (Gmm : AIMGHI <= U (Z_to_bv 64 (ma_ab n SBEG kk)) /\ U (Z_to_bv 64 (ma_ab n SBEG kk)) + needed n <= U S - 3584) by (rewrite Uab, CP2; lia).
    assert (GRall : mem_grows Mr MC).
    { eapply mem_grows_trans; [exact GRP|]. (lazymatch goal with |- ?G => let G' := eval unfold MC in G in change_no_check G' end). apply ma_P2_grows_all. }
    assert (GRin : mem_grows M MDin).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold MDin, munrestrict in G in change_no_check G' end). destruct (Hd x) eqn:Ex; [exact Hx|]. apply GRall. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite mrestrict_off by exact Ex. exact Hx. }
    (* [comment removed for export] *)
    assert (DIFF1 : forall a : word, MDin a <> M a -> Xm (U S) T c p (U a) /\ MDin a <> None).
    { intros a NE. pose proof (u64_range a) as Ha.
      split; cycle 1.
      { destruct (MDin a) eqn:E1; [discriminate|]. exfalso. apply NE. destruct (M a) eqn:E2; [|reflexivity].
        exfalso. assert (X : M a <> None) by (rewrite E2; discriminate). apply GRin in X. rewrite E1 in X. exact (X eq_refl). }
      unfold MDin, munrestrict in NE. destruct (Hd a) eqn:Eh; [exfalso; exact (NE eq_refl)|].
      assert (EMr : Mr a = M a) by ((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); apply mrestrict_off; exact Eh).
      (lazymatch goal with |- ?G => let G' := eval unfold Xm, T_PC, PC_SZ in G in change_no_check G' end).
      destruct (decide (MC a = MP a)) as [E1|N1].
      - rewrite E1 in NE. rewrite <- EMr in NE. pose proof (FOOTP a NE). lia.
      - pose proof (ma_P2_foot MP S T n (Z.of_nat (length ks) + 1) (Z_to_bv 64 (bytes_le_to_Z bst)) (Z_to_bv 64 cszv) (Z_to_bv 64 (ma_ab n SBEG kk)) b1 x18 x19
                      (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) GSm GTm Hn Gmm a N1) as F.
        unfold ma_footA in F. rewrite Uab in F. fold c in F. (lazymatch goal with |- ?G => let G' := eval unfold p in G in change_no_check G' end). lia. }
    (* [comment removed for export] *)
    assert (VIS : forall a : word, Hd a = false -> MDin a = MC a) by (intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold MDin in G in change_no_check G' end); apply munrestrict_off; exact Ha).
    assert (VISstk : forall a : word, U S - 3584 <= U a < U S -> MDin a = MC a).
    { intros a Ha. apply VIS. rewrite <- (Z_to_bv_bv_unsigned 64 a). apply NHs; [lia|]. left. rewrite CP2 in Ha. lia. }
    (* [comment removed for export] *)
    assert (SZW : U (Z_to_bv 64 (bytes_le_to_Z bsz)) mod 2 ^ 32 = sz).
    { pose proof (bytes_le_to_Z_bound bsz) as Bb. rewrite Lsz in Bb. pose proof (bytes_le_to_Z_nonneg bsz). unorm. apply (lez_low32 ASEGS MP (at_ S (-2120)) bsz sz Psz8 Psz4). lia. }
    assert (SZ8 : 1 <= sz <= 8) by (clear - SZ1 SZ2; change (Z.of_nat DMAX) with 6 in SZ2; lia).
    assert (TAGW : U (Z_to_bv 64 (bytes_le_to_Z bsz)) / 2 ^ 32 < 256).
    { rewrite (proj2 SZ1). rewrite u_Z2bv by (clear - SZ8; lia). rewrite Z.div_small by (clear - SZ8; lia). lia. }
    assert (KCW : a_kact st1 <= KCAP).
    { (lazymatch goal with |- ?G => let G' := eval unfold st1, op_meter, add_meter in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_kact] in G in change_no_check G' end). destruct BD as (_ & _ & BK). unfold kcost_malloc in HK. clear - BK HK Hn. lia. }
    apply (katD_bind ASEGS _ (depot_post bt FXOK KD (Xm (U S) T c p) st1 Lc FF MDin mdl1 r4 (at_ S (-2272)) (Z_to_bv 64 0x4bed0))).
    { apply (HYP_DEPOT fx (Xm (U S) T c p) st1 Lc FF MDin mdl1 r4 (at_ S (-2272)) (at_ S (-2112)) (Z_to_bv 64 (bytes_le_to_Z bsz)) (Z_to_bv 64 0x4bed0) sz HFX).
      { rewrite Ehl. exact HH. }
      { exact (model_ivs_wf_sbm mdl mdl1 SBM1 MW). }
      { exact W1. }
      { exists M. split; [exact RP1 | exact DIFF1]. }
      { intros a Ha. split.
        - unfold Xm, T_PC, PC_SZ in Ha. unfold p in Ha. rewrite CP2 in Ha. rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi asan_addrs] in G in change_no_check G' end).
          destruct Ha as [Ha|[Ha|[Ha|Ha]]]; [(first [clear - Ha CR CPlo | idtac]; lia) | | | (first [clear - Ha A1 NF7 NF6 NF1 Hn | idtac]; lia)]; (destruct GTI as [GTI'|GTI']; (first [clear - Ha GTI' NF3 | idtac]; lia)).
        - intros id Hid. cbn [st1 op_meter add_meter a_dep] in Hid |- *.
          unfold Xm, T_PC, PC_SZ in Ha. destruct Ha as [Ha|[Ha|[Ha|Ha]]].
          + apply (mc_T_stack_vs_node bt st Lc FF W id a Hid). right. rewrite CP2 in Ha. lia.
          + apply (mc_T_stack_vs_node bt st Lc FF W id a Hid). left. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). lia.
          + apply (mc_T_stack_vs_node bt st Lc FF W id a Hid). left. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). lia.
          + apply (ANODE id a Hid). unfold p in Ha. pose proof (csize_pos c NF3) as ((Cz1 & Cz2) & Cz3). lia. }
      { intros a Ha. refine (Xm_xtracked bt st Lc FF M mdl n ks kk (U S) T p W RP Hn HC eq_refl _ _ a Ha).
        - rewrite CP2. lia.
        - (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). fold c ab. (lazymatch goal with |- ?G => let G' := eval unfold p in G in change_no_check G' end). pose proof (csize_pos c NF3) as ((Cz1 & Cz2) & Cz3). lia. }
      { destruct HOLES as [h0 HOLE]. exists h0. exact (AsAinvEntry3.AsAinvHole3.holes_le_same_reg h0 st st1 eq_refl HOLE). }
      { (lazymatch goal with |- ?G => let G' := eval cbn [st1 op_meter add_meter a_dep a_kact] in G in change_no_check G' end). destruct W as (_ & _ & _ & _ & _ & _ & (D1 & D2 & Drest) & (WM1 & _) & _).
        rewrite meter_div by exact WM1. lia. }
      { (lazymatch goal with |- ?G => let G' := eval cbn [st1 op_meter add_meter a_dep a_kact] in G in change_no_check G' end). destruct W as (_ & _ & _ & _ & _ & _ & (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & Drest) & (WM1 & _) & _).
        rewrite meter_div by exact WM1. lia. }
      { exact X1. } { exact X2. } { exact X10. } { exact X11. }
      { rewrite at_u by lia. rewrite CP2. clear - CP16 CPlo HSr CR. Z.div_mod_to_equations. lia. }
      { rewrite at_u by lia. rewrite CP2. lia. }
      { rewrite at_u by lia. (lazymatch goal with |- ?G => let G' := eval unfold PTRHI in G in change_no_check G' end). lia. }
      { apply ret_ok_lit; [lia | reflexivity]. }
      { intros a Ha. rewrite at_u in Ha by lia. split.
        - apply GRin. apply store_ok1_heap; [lia|]. apply CPstk. rewrite <- CP2. lia.
        - eapply store_ok_mono; [exact GRin|]. apply CPstk. rewrite <- CP2. lia. }
      { exact SZ8. }
      { exact SZW. }
      { exact TAGW. }
      { exact KCW. }
      { intros i Hi. rewrite at_u in Hi by lia. apply GRin. apply store_ok1_heap; [wd_ulia|].
        replace (Z_to_bv 64 i) with (Z_to_bv 64 (U (Z_to_bv 64 i))) by (first [clear - Hi SZ1 CR CPhi CPlo CP2 | idtac]; (apply bv_eq; unorm; reflexivity)).
        rewrite Z_to_bv_bv_unsigned. apply CPstk. unorm. rewrite <- CP2. lia. }
      { rewrite at_u by lia. rewrite CP2. lia. }
      { rewrite !at_u by lia. lia. }
      { rewrite at_u by lia. lia. } }
    (* [comment removed for export] *)
    intros c' POST.
    destruct POST as (fx' & st' & M' & mdl' & R' & id & Ec' & HFX' & (d' & naa & Est') & W2 & RX2 & KEPTX & DIFF2 & CHG2 & RK & A0 & Hid & SEV & LZ & HH2 & MW2).
    subst c'. apply katD_refl.
    unfold depot_st in Est'. cbn [st1 op_meter add_meter a_reg a_cinit a_cache a_tq a_gq a_sec a_nres a_dep a_hint a_ialloc a_aa a_kact a_shsec] in Est'.
    rewrite app_nil_r, Z.add_0_r in Est'. subst st'.
    destruct RX2 as (M0' & RP2 & DX2).
    (* [comment removed for export] *)
    assert (XF : forall k bs0 (w : nat), -2272 <= k -> k + Z.of_nat w <= 0 -> rdn ASEGS MC (at_ S k) w = Some bs0 -> rdn ASEGS M' (at_ S k) w = Some bs0).
    { intros k bs0 w Hk1 Hk2 Hr. apply (rd_same ASEGS M' MC); [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | exact Hr].
      intros x Hx. rewrite at_u in Hx by lia. rewrite (KEPTX x); [| (lazymatch goal with |- ?G => let G' := eval unfold Xm in G in change_no_check G' end); (first [clear - Hx Hk2 Hk1 | idtac]; lia) | rewrite at_u by (first [clear - CR CPlo CP2 CPhi | idtac]; lia); (first [clear - Hx Hk1 | idtac]; lia)]. apply VISstk. lia. }
    (* [comment removed for export] *)
    assert (XLO : forall x : word, Xm (U S) T c p (U x) -> U x < U S - 3584 -> Hd x = false -> M' x = MC x).
    { intros x Hx Hlo Hh. rewrite (KEPTX x); [| exact Hx | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]]. apply VIS. exact Hh. }
    destruct (ma_P2_hdr MP S T n (Z.of_nat (length ks) + 1) (Z_to_bv 64 (bytes_le_to_Z bst)) (Z_to_bv 64 cszv) (Z_to_bv 64 (ma_ab n SBEG kk)) b1 x18 x19
                (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) GSm Hn Gmm) as (H15 & H14 & H12).
    Ltac incs := apply in_cs; reflexivity.
    Ltac viaRK RK k X := etransitivity; [| exact X];
      match goal with |- getr _ ?x = getr _ _ => replace x with (Z_to_bv 5 k) by (apply bv_eq; reflexivity) end; apply RK; incs.
    (lazymatch goal with |- ?G => let G' := eval unfold runA_post in G in change_no_check G' end).
    exists fx', R', M', M0', mdl', d', naa, id, b1, x18, x19.
    (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). fold S c ab p. rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi asan_addrs] in G in change_no_check G' end).
    split; [reflexivity|]. split; [exact HFX'|]. split; [exact HH2|]. split; [exact MW2|]. split; [exact W2|]. split; [exact RP2|]. split; [exact DX2|].
    split.
    { (* [comment removed for export] *) intros a NE. destruct (decide (M' a = MDin a)) as [E|N].
      + rewrite E in NE |- *. destruct (DIFF1 a NE) as [X D]. split; [left; exact X | exact D].
      + destruct (DIFF2 a N) as [_ D]. split; [| exact D]. right. pose proof (CHG2 a N) as CX. rewrite at_u in CX by lia. rewrite ?BT_ia in CX.
        destruct CX as [X|[X|X]]; [left; lia | right; left; exact X | right; right; exact X]. }
    split.
    { (* [comment removed for export] *) intros k0 v Hin.
      pose proof (ma_slotsA_range S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) k0 v Hin) as [Hk1 Hk2].
      apply (XF k0 (LE8 v) 8%nat); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |].
      (lazymatch goal with |- ?G => let G' := eval unfold MC in G in change_no_check G' end). apply (ma_P2_slotsA MP S T n _ _ _ _ b1 x18 x19 _ _ _ _ _ _ GSm GTm Hn Gmm k0 v Hin). }
    split.
    { (* [comment removed for export] *) intros k0 v Hin.
      assert (Hk : -56 <= k0 /\ k0 + 8 <= 0).
      { cbn [In] in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; (repeat match goal with H : _ |- _ => clear H end; lia)|]). destruct Hin. }
      apply (XF k0 (LE8 v) 8%nat); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |].
      apply (rd_same ASEGS MC MP); [| rewrite at_u by (first [clear - Hk CR CPlo CP2 CPhi | idtac]; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); (first [clear - Hk CPhi CP2 | idtac]; lia) | exact (Pslots k0 v Hin)].
      intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. (lazymatch goal with |- ?G => let G' := eval unfold MC in G in change_no_check G' end). apply ma_P2_above; [exact GSm | exact GTm | exact Hn | exact Gmm | lia]. }
    split.
    { (* [comment removed for export] *)
      replace (Z_to_bv 64 (p - 15)) with (at_ (Z_to_bv 64 (ma_ab n SBEG kk)) (rz n - 15)) by (first [clear - Uab A2 A1 NF7 NF6 NF4 NF1 Hn CPhi CPlo | idtac]; (apply bv_eq; rewrite at_u by (rewrite Uab; lia); rewrite Uab; (lazymatch goal with |- ?G => let G' := eval unfold p in G in change_no_check G' end); wd_ulia)).
      rewrite XLO; [(lazymatch goal with |- ?G => let G' := eval unfold MC in G in change_no_check G' end); exact H15 | rewrite at_u, Uab by (rewrite Uab; (first [clear - A1 NF7 NF6 NF1 Hn A2 NF4 CPhi CPlo | idtac]; lia)); (lazymatch goal with |- ?G => let G' := eval unfold Xm, p in G in change_no_check G' end); (repeat match goal with H : _ |- _ => clear H end; lia) | rewrite at_u, Uab by (rewrite Uab; (first [clear - A1 NF7 NF6 NF1 Hn A2 NF4 CPhi CPlo | idtac]; lia)); (first [clear - A2 NF7 NF6 NF4 CPlo CP2 | idtac]; lia) |].
      rewrite <- (Z_to_bv_bv_unsigned 64 (at_ _ _)). rewrite at_u, Uab by (rewrite Uab; lia). apply NHab. lia. }
    split.
    { (* [comment removed for export] *)
      apply (rd_same ASEGS M' MC); [| unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); (first [clear - A2 NF7 NF6 NF4 CPhi CPlo | idtac]; lia) |].
      + intros x Hx. revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx. apply XLO; [(lazymatch goal with |- ?G => let G' := eval unfold Xm in G in change_no_check G' end); (first [clear - Hx | idtac]; lia) | (first [clear - Hx A2 NF7 NF6 NF4 CPlo CP2 | idtac]; lia) | rewrite <- (Z_to_bv_bv_unsigned 64 x); apply NHab; (first [clear - Hx NF8 NF7 NF6 NF4 | idtac]; lia)].
      + replace (Z_to_bv 64 (p - 14)) with (at_ (Z_to_bv 64 (ma_ab n SBEG kk)) (rz n - 14)) by (first [clear - Uab A2 A1 NF7 NF6 NF4 NF1 Hn CPhi CPlo | idtac]; (apply bv_eq; rewrite at_u by (rewrite Uab; lia); rewrite Uab; (lazymatch goal with |- ?G => let G' := eval unfold p in G in change_no_check G' end); wd_ulia)).
        (lazymatch goal with |- ?G => let G' := eval unfold MC in G in change_no_check G' end). exact H14. }
    split.
    { (* [comment removed for export] *)
      apply (rd_same ASEGS M' MC); [| unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); (first [clear - A2 NF7 NF6 NF4 CPhi CPlo | idtac]; lia) |].
      + intros x Hx. revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx. apply XLO; [(lazymatch goal with |- ?G => let G' := eval unfold Xm in G in change_no_check G' end); (first [clear - Hx | idtac]; lia) | (first [clear - Hx A2 NF7 NF6 NF4 CPlo CP2 | idtac]; lia) | rewrite <- (Z_to_bv_bv_unsigned 64 x); apply NHab; (first [clear - Hx NF8 NF7 NF6 NF4 | idtac]; lia)].
      + replace (Z_to_bv 64 (p - 12)) with (at_ (Z_to_bv 64 (ma_ab n SBEG kk)) (rz n - 12)) by (first [clear - Uab A2 A1 NF7 NF6 NF4 NF1 Hn CPhi CPlo | idtac]; (apply bv_eq; rewrite at_u by (rewrite Uab; lia); rewrite Uab; (lazymatch goal with |- ?G => let G' := eval unfold p in G in change_no_check G' end); wd_ulia)).
        (lazymatch goal with |- ?G => let G' := eval unfold MC in G in change_no_check G' end). exact H12. }
    split.
    { (* [comment removed for export] *)
      apply (rd_same ASEGS M' MC); [| (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end); unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); (first [clear - GTC NF3 CPhi CPlo | idtac]; lia) |].
      + intros x Hx. revert Hx; (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end); unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx.
        apply XLO; [(lazymatch goal with |- ?G => let G' := eval unfold Xm, T_PC, PC_SZ in G in change_no_check G' end); (first [clear - Hx | idtac]; lia) | (first [clear - Hx GTC NF3 CPlo CP2 | idtac]; lia) | rewrite <- (Z_to_bv_bv_unsigned 64 x); apply NHrt; (first [clear - Hx NF3 | idtac]; lia)].
      + replace (Z_to_bv 64 (T + T_PC + PC_SZ * c)) with (at_ (Z_to_bv 64 T) (208 + 80 * class_of (needed n))) by (first [clear - GTC GT0 NF3 CPhi CPlo | idtac]; (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_, T_PC, PC_SZ in G in change_no_check G' end); fold c; wd_ulia)).
        replace (Z.of_nat (length ks)) with (Z.of_nat (length ks) + 1 - 1) by lia.
        (lazymatch goal with |- ?G => let G' := eval unfold MC in G in change_no_check G' end). apply (ma_P2_cnt MP S T n _ _ _ _ b1 x18 x19 _ _ _ _ _ _ GSm GTm Hn Gmm). rewrite Uab. unfold hide in AT. lia. }
    split; [viaRK RK 2 X2|]. split; [viaRK RK 4 X4|]. split; [viaRK RK 3 X3|]. split; [viaRK RK 8 X8|]. split; [viaRK RK 9 X9|].
    split; [exact A0|]. split; [viaRK RK 18 X18|]. split; [viaRK RK 19 X19|]. split; [viaRK RK 20 X20|]. split; [viaRK RK 21 X21|].
    split; [viaRK RK 22 X22|]. split; [viaRK RK 23 X23|]. split; [viaRK RK 24 X24|]. split; [viaRK RK 25 X25|]. split; [viaRK RK 26 X26|].
    split; [viaRK RK 27 X27|]. split; [exact Hid|].
    split; [eapply same_except_vm_trans; [apply same_but_materialized_except_vm; exact SBM1 | exact SEV]|].
    (lazymatch goal with |- ?G => let G' := eval unfold lazy_kept in G in change_no_check G' end). rewrite ?BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi asan_addrs] in G in change_no_check G' end).
    intros a Ha. cbn [a_dep] in LZ. assert (RNGa : 0 <= a < 2 ^ 64).
    { destruct Ha as [V|[V|V]]; [refine (proj1 (AsKSys7b.app_visible_cases bt _ Lc FF (2 ^ 20) (2 ^ 28) W2 a _)); rewrite ?BT_ia; exact V | pose proof ceil_rng; lia | lia]. }
    (* [comment removed for export] *)
    first [destruct (LZ a RNGa) as [E|(blk & Hin & Hnin & Hr)] | destruct (LZ a) as [E|(blk & Hin & Hnin & Hr)]]; [rewrite E; (lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end); rewrite Elz; reflexivity|].
    exfalso. destruct (OBL_store_private _ Lc FF blk a W2 Hin Hr) as (Z1 & Z2 & Z3). rewrite ?BT_ia in Z2, Z3. cbn [ia_img_lo ia_img_hi asan_addrs] in Z2.
    destruct Ha as [V|[V|V]]; [exact (Z3 V) | lia | lia].
  Qed.
End TOPA.
End WithCeil.
End AsAllocMTopA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsKInst OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocMHyp AsAllocMTopA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocMHypR.
Import AsDepotHyp8.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation U := bv_unsigned.

Section TOP.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND KD : Z).
  Hypothesis BT_segs : bt_segs bt = ASEGS.
  Hypothesis BT_ia : bt_ia bt = asan_addrs.
  Hypothesis CELLS : malloc_cells bt TP TSDP PGP FL MIDEND.
  Hypothesis GEOM : free_boot_geom bt.
  Hypothesis G_KD : 0 <= KD <= 1312.
  Hypothesis HYP_DEPOT : AsAllocFHyp.HYP_DEPOT_stmt bt FXOK KD.
  Hypothesis HTP : TP = ia_tp asan_addrs.

  #[local] Abbreviation AAINVH := (AAINV_HS bt).
  #[local] Abbreviation MOK := (malloc_ok ASEGS FXOK asan_addrs AAINVH MSTK_A).
  #[local] Abbreviation MNULL := (malloc_null ASEGS FXOK asan_addrs AAINVH MSTK_A).

  (* [comment removed for export] *)
  Definition MCASE (entry : Z) (P : Z -> ast -> Prop) : Prop :=
    forall (h : option Z) fx (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF : list (Z * Z)) (B C K ret n sp : Z) (st : ast),
      m_halted mdl = None -> FXOK fx ->
      WF bt st Lc FF -> Rep bt st Lc FF M mdl -> bounds st Lc B C K -> holes_lsopt h st -> BackingAlgebra.model_ivs_wf mdl -> hole_ok h n ->
      call_pre ASEGS asan_addrs R M ret sp MSTK_A ->
      U (getr R 10) = n -> 1 <= n <= NMAX -> fpc M (U (getr R 8)) sp DMAX ->
      B + (n + MBLK) <= GBUDGET -> C + 1 <= LMAX -> K + kcost_malloc n <= KCAP ->
      P n st ->
      katwD ASEGS (cfg ASEGS fx R entry M mdl) (MOK R M mdl Lc FF B C K ret n sp) (MNULL R M mdl Lc FF B C K ret n sp).

  (* [comment removed for export] *)
  Definition hole_flags (n : Z) (st : ast) : bool :=
    r_uhole (a_reg st (class_of (needed n))) || r_fhole (a_reg st (class_of (needed n))).
  Definition P_hit (n : Z) (st : ast) : Prop := n <= 64512 /\ a_cache st (class_of (needed n)) <> [] /\ hole_flags n st = false.
  Definition P_miss (n : Z) (st : ast) : Prop := n <= 64512 /\ a_cache st (class_of (needed n)) = [].
  Definition P_sec (n : Z) (st : ast) : Prop := 64512 < n.

  Lemma hole_flags_hit_absurd : forall h n st, holes_lsopt h st -> hole_ok h n ->
    a_cache st (class_of (needed n)) <> [] -> hole_flags n st = true -> False.
  Proof using.
    intros h n st HL HO NE HF. unfold hole_flags in HF. apply Bool.orb_true_iff in HF.
    pose proof (holes_ls_of_opt h n st HL HO) as HS.
    destruct (HS (class_of (needed n)) HF) as (_ & EC & _). exact (NE EC).
  Qed.

  Theorem malloc_katw_of_cases : forall entry,
    MCASE entry P_hit -> MCASE entry P_miss -> MCASE entry P_sec ->
    MALLOC_KATW ASEGS FXOK asan_addrs AAINVH MSTK_A entry true.
  Proof using.
    intros entry HH HM HS h fx R M mdl Lc FF B C K ret n sp PRE.
    destruct PRE as (HLT & HFX & AI & HO & CP & HR10 & Hn & FPC & HB & HC & HK).
    destruct AI as (st & W & RP & [BD HL] & MW).
    destruct (Z_lt_le_dec 64512 n) as [Hs|Hp].
    - exact (HS h fx R M mdl Lc FF B C K ret n sp st HLT HFX W RP BD HL MW HO CP HR10 Hn (FPC eq_refl) HB HC HK Hs).
    - destruct (a_cache st (class_of (needed n))) as [|k0 ks0] eqn:E.
      + exact (HM h fx R M mdl Lc FF B C K ret n sp st HLT HFX W RP BD HL MW HO CP HR10 Hn (FPC eq_refl) HB HC HK (conj Hp E)).
      + assert (NE : a_cache st (class_of (needed n)) <> []) by (rewrite E; discriminate).
        destruct (hole_flags n st) eqn:HF.
        * exfalso. exact (hole_flags_hit_absurd h n st HL HO NE HF).
        * exact (HH h fx R M mdl Lc FF B C K ret n sp st HLT HFX W RP BD HL MW HO CP HR10 Hn (FPC eq_refl) HB HC HK (conj Hp (conj NE HF))).
  Qed.

  (* [comment removed for export] *)
  Definition partB_stmt : Prop :=
    forall (h : option Z) fx (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF : list (Z * Z)) (B C K ret n sp : Z) (st : ast)
           (ks : list Z) (kk : Z) (c' : config),
      m_halted mdl = None -> FXOK fx ->
      bounds st Lc B C K -> holes_le h st -> hole_ok h n ->
      call_pre ASEGS asan_addrs R M ret sp MSTK_A ->
      U (getr R 10) = n -> 1 <= n <= 64512 -> fpc M (U (getr R 8)) sp DMAX ->
      B + (n + MBLK) <= GBUDGET -> C + 1 <= LMAX -> K + kcost_malloc n <= KCAP ->
      a_cache st (class_of (needed n)) = ks ++ [kk] -> hole_flags n st = false ->
      runA_post bt FXOK st ks kk Lc FF R M mdl n c' ->
      katD ASEGS c' (MOK R M mdl Lc FF B C K ret n sp).

  (* [comment removed for export] *)
  Theorem case_hit : partB_stmt -> MCASE (ia_malloc asan_addrs) P_hit.
  Proof using HTP HYP_DEPOT G_KD GEOM CELLS BT_ia BT_segs KD MIDEND FL PGP TSDP TP.
    intros PB h fx R M mdl Lc FF B C K ret n sp st HLT HFX W RP BD HL MW HO CP HR10 Hn FPC HB HC HK (Hp & NE & HF).
    pose proof (app_removelast_last 0 NE) as E.
    set (ks := removelast (a_cache st (class_of (needed n)))) in E. set (kk := last (a_cache st (class_of (needed n))) 0) in E.
    apply katwD_of_katD.
    apply (katD_bind ASEGS _ (runA_post bt FXOK st ks kk Lc FF R M mdl n)).
    - eapply (malloc_runA bt FXOK TP TSDP PGP FL MIDEND KD); try eassumption; [lia | exists h; exact (holes_lsopt_le _ _ HL)].
    - intros c' PC. eapply PB; try eassumption; try exact (holes_lsopt_le _ _ HL). lia.
  Qed.





End TOP.
