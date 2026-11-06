(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.glaze.binary_reflection.images.AsanUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoDepotHyp9.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Import OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp.

#[local] Abbreviation U := bv_unsigned.

Section WithCeil.
Context {RC : run_ceil}.
Definition HYP_DEPOT9_stmt (bt : as_boot) (FXOK : FPState -> Prop) (KD : Z) : Prop :=
  forall fx (X : Z -> Prop) st Lc FF (M : mem) mdl (R : bvmap 5 word) (sp buf szw ret : word) (sz : Z),
    FXOK fx -> m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
    WF bt st Lc FF -> RepX bt X st Lc FF M mdl ->
    (forall a, X a -> ~ (ia_img_lo (bt_ia bt) <= a < ia_img_hi (bt_ia bt))                 (* [comment removed for export] *)
               /\ (forall id, 1 <= id <= dp_nids (a_dep st) -> ~ foot_node bt (a_dep st) id a)) ->
    (forall a, X a -> CEIL <= a \/ in_band a \/ exists lo hi, In (lo, hi) (bt_fixed bt ++ List.map (fun s => (sc_map s, sc_map s + sc_mapsz s)) (a_sec st))
                                    /\ lo <= a < hi /\ lo <> bt_nodes0 bt /\ lo <> bt_store0 bt) ->     (* [comment removed for export] *)
    (exists h : option Z, holes_le h st) ->                                                 (* [comment removed for export] *)
    dp_nids (a_dep st) + 1 <= dp_nids (bt_dep0 bt) + a_kact st / EVT ->
    dp_frames (a_dep st) + FRW <= dp_frames (bt_dep0 bt) + FRW * (a_kact st / EVT) + FRW * Z.of_nat (length (dp_storeblocks (a_dep st))) ->   (* [comment removed for export] *)
    getr R 1 = ret -> getr R 2 = sp -> getr R 10 = buf -> getr R 11 = szw ->
    U sp mod 16 = 0 -> CEIL + KD <= U sp -> U sp + 2192 <= PTRHI -> ret_ok ret ->
    (forall a : word, U sp - KD <= U a < U sp -> M a <> None /\ store_ok BSEGS M a 1%nat = true) ->
    1 <= sz <= 8 -> U szw mod 2 ^ 32 = sz -> U szw / 2 ^ 32 < 256 ->
    a_kact st <= KCAP ->
    (forall i, U buf <= i < U buf + 8 * sz -> M (Z_to_bv 64 i) <> None) -> CEIL <= U buf ->
    U sp <= U buf -> U buf + 8 * sz < 2 ^ 64 ->                                                                          (* [comment removed for export] *)
    katD BSEGS (mkCfg (@mkst fx R (Z_to_bv 64 0x8f4f0) M (seg_rom BSEGS)) mdl)
         (depot_post bt FXOK KD X st Lc FF M mdl R sp ret).
End WithCeil.
End BoDepotHyp9.
Require LinuxProcessSemantics.Riscv.Sem OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotHit OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoDepotRunP.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.StartupAux.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotHit OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.BoDepotStore OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove.AsDepotSum.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 v := (word_to_le_bytes 4 v).
#[local] Abbreviation U := bv_unsigned.

Lemma le8_halves : forall v : word, LE8 v = LE4 v ++ LE4 (Z_to_bv 64 (U v / 2 ^ 32)).
Proof.
  intros v. pose proof (u64_range v) as Hv. (lazymatch goal with |- ?G => let G' := eval unfold word_to_le_bytes in G in change_no_check G' end).
  assert (Q : (0 <= U v / 2 ^ 32 < 2 ^ 32)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite (u_Z2bv (U v / 2 ^ 32)) by lia.
  assert (E : Z.shiftr (Z.shiftr (Z.shiftr (Z.shiftr (U v) 8) 8) 8) 8 = (U v / 2 ^ 32)%Z).
  { rewrite !Z.shiftr_shiftr by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
  (lazymatch goal with |- ?G => let G' := eval cbn [Z_to_le_bytes app] in G in change_no_check G' end). rewrite E. reflexivity.
Qed.

Section FPGen.
Context {fx : FPState}.

Section FRAME.
  Variables (mem : word -> option byte) (sp ra tr : word) (sz tag : Z) (regs : bvmap 5 word).
  Hypothesis Hsp : (2 ^ 32 + 112 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hsz : (0 <= sz < 2 ^ 32)%Z.
  Hypothesis Htag : (0 <= tag < 2 ^ 32)%Z.
  #[local] Abbreviation a1w := (Z_to_bv 64 (sz + tag * 2 ^ 32)).
  #[local] Abbreviation SM := (sd_frame mem sp regs ra tr a1w).

  Lemma sdf_sum : msum (ivl (U sp - 112) 112) mem SM.
  Proof using Hsp.
    pose proof (u64_range sp). destruct Hsp as [S1 S2]. apply msum_outside.
    - intros x Hx. apply sd_frame_outside; [lia|]. unfold ivl in Hx. lia.
    - (lazymatch goal with |- ?G => let G' := eval unfold sd_frame in G in change_no_check G' end). do 13 (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl.
  Qed.

  Lemma sdf_slots : forall (k : Z) (v : word),
    In (k, v) [(-8, ra); (-16, getr regs 8); (-24, getr regs 9); (-32, getr regs 18); (-40, getr regs 19); (-48, getr regs 20);
               (-56, getr regs 21); (-64, getr regs 22); (-72, getr regs 23); (-80, getr regs 24); (-88, getr regs 25)]%Z ->
    rdn BSEGS SM (at_ sp k) 8 = Some (LE8 v).
  Proof using Hsp.
    intros k v Hin. pose proof (u64_range sp). destruct Hsp as [S1 S2]. (lazymatch goal with |- ?G => let G' := eval unfold sd_frame in G in change_no_check G' end). cbn [In] in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rd8_chain|]). destruct Hin.
  Qed.

  Lemma sdf_args :
    rdn BSEGS SM (at_ sp (-104)) 8 = Some (LE8 tr)
    /\ rdn BSEGS SM (at_ (at_ sp (-104)) 8) 4 = Some (LE4 (Z_to_bv 64 sz))
    /\ rdn BSEGS SM (at_ (at_ sp (-104)) 12) 4 = Some (LE4 (Z_to_bv 64 tag)).
  Proof using Htag Hsz Hsp.
    pose proof (u64_range sp). destruct Hsp as [S1 S2].
    assert (Ua : U a1w = (sz + tag * 2 ^ 32)%Z) by (rewrite u_Z2bv by lia; reflexivity).
    assert (R8 : rdn BSEGS SM (at_ sp (-96)) 8 = Some (LE8 a1w)) by ((lazymatch goal with |- ?G => let G' := eval unfold sd_frame in G in change_no_check G' end); apply rdn_wbytes_hit8; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (Elo : LE4 a1w = LE4 (Z_to_bv 64 sz)).
    { apply le4_congr. rewrite Ua, (u_Z2bv sz) by lia. (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap in G in change_no_check G' end). change (bv_modulus 32) with (2 ^ 32)%Z. apply Z_mod_plus_full. }
    assert (Ehi : (U a1w / 2 ^ 32 = tag)%Z).
    { rewrite Ua. rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
    split. { (lazymatch goal with |- ?G => let G' := eval unfold sd_frame in G in change_no_check G' end). rd8_chain. }
    split.
    - rewrite at_at. change (-104 + 8)%Z with (-96)%Z. rewrite <- Elo. apply (SumsLib.StartupAux.rdn_low_bytes BSEGS SM (at_ sp (-96)) a1w 4 ltac:(lia) R8).
    - rewrite at_at. change (-104 + 12)%Z with (-92)%Z.
      pose proof (rdn_skip BSEGS SM (at_ sp (-96)) 8 _ 4 R8 ltac:(lia) ltac:(first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ])) as RS.
      rewrite at_at in RS. change (-96 + Z.of_nat 4)%Z with (-92)%Z in RS. change (8 - 4)%nat with 4%nat in RS.
      rewrite RS. rewrite (le8_halves a1w), Ehi. f_equal.
  Qed.
End FRAME.
End FPGen.
End BoDepotRunP.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoDepotTop1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsKInst OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotHit OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove.AsDepotSum BoDepotRunP BoDepotHyp9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsDepotTop0.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= am_lia.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 v := (word_to_le_bytes 4 v).
#[local] Abbreviation U := bv_unsigned.

Section FPGen.
Context {fx : FPState}.
(* [comment removed for export] *)
Lemma trace_words : forall (Mm : mem) (n : nat) (a : word),
  (forall i, U a <= i < U a + 8 * Z.of_nat n -> Mm (Z_to_bv 64 i) <> None) -> U a + 8 * Z.of_nat n < 2 ^ 64 ->
  exists ws : list word, length ws = n /\ forall i, (i < n)%nat -> rdn BSEGS Mm (at_ a (8 * Z.of_nat i)) 8 = Some (LE8 (nth i ws (Z_to_bv 64 0))).
Proof using.
  intros Mm n. induction n as [|n IH]; intros a Hdef Hnw.
  - exists []. split; [reflexivity | intros i Hi; lia].
  - pose proof (u64_range a) as Ha.
    destruct (rdn_defined_ex BSEGS Mm a 8) as (bs & Hr & Hl); [intros i Hi; apply Hdef; cbn in Hi; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |].
    destruct (IH (at_ a 8)) as (ws & Lw & Hw).
    { intros i Hi. rewrite at_u in Hi by lia. apply Hdef. lia. }
    { rewrite at_u by lia. lia. }
    exists (Z_to_bv 64 (bytes_le_to_Z bs) :: ws). split; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); rewrite Lw; reflexivity|].
    intros [|i] Hi.
    + (lazymatch goal with |- ?G => let G' := eval cbn [nth Z.of_nat Z.mul] in G in change_no_check G' end). rewrite at_0. rewrite (word_to_le_bytes_of_bytes8 bs Hl). exact Hr.
    + (lazymatch goal with |- ?G => let G' := eval cbn [nth] in G in change_no_check G' end). rewrite <- (Hw i ltac:(lia)). rewrite at_at. f_equal. f_equal. lia.
Qed.
End FPGen.

Section TOP.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.

  (* [comment removed for export] *)
  Definition depot_cells : Prop :=
    In (0x10310, 8%nat, 0xc6a4a7935bd1e995) (bt_consts bt) /\ In (0x10348, 8%nat, 0x35253c9ade8f4ca8) (bt_consts bt)
    /\ In (0x10448, 8%nat, 0x9747b28c9747b28c) (bt_consts bt)
    /\ In (0x105f08, 8%nat, 0x19fce8) (bt_consts bt) /\ In (0x19fdd8, 4%nat, 0) (bt_consts bt).
  (* [comment removed for export] *)
  Definition depot_obls : Prop :=
    (forall st Lc FF M mdl b a, WF bt st Lc FF -> Rep bt st Lc FF M mdl -> In b (node_blocks bt (a_dep st)) -> b <= a < b + 2 ^ 20 -> lzb mdl a = false)
    /\ (forall st Lc FF b a, WF bt st Lc FF -> In b (node_blocks bt (a_dep st)) -> b <= a < b + 2 ^ 20 -> rt_priv (bt_ia bt) Lc FF a)
    /\ (forall st Lc FF b a, WF bt st Lc FF -> In b (store_blocks bt (a_dep st)) -> b <= a < b + 2 ^ 23 -> rt_priv (bt_ia bt) Lc FF a).
  Hypothesis DCELLS : depot_cells.
  Hypothesis DOBL : depot_obls.

  Lemma depot_st_id : forall st, depot_st st (a_dep st) [] = st.
  Proof using. intros [a b c d e f g h i j k l m]. (lazymatch goal with |- ?G => let G' := eval unfold depot_st in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). rewrite app_nil_r. reflexivity. Qed.

  Lemma regs_kept_of_agree : forall (CLB : list reg) (R R' : bvmap 5 word),
    regs_agree (fun r => In r CLB) R R' ->
    (forall z, In z as_callee_saved -> ~ In (Z_to_bv 5 z) CLB \/ getr R' (Z_to_bv 5 z) = getr R (Z_to_bv 5 z)) -> regs_kept R R'.
  Proof using. intros CLB R R' AG F z Hz. destruct (F z Hz) as [N | E]; [apply AG; exact N | exact E]. Qed.

  (* [comment removed for export] *)
  Definition miss_arm_stmt (KD : Z) : Prop :=
    forall fx (X : Z -> Prop) st Lc FF (M M0 : mem) mdl (R r : bvmap 5 word) (sp buf ret : word) (sz tag : Z) (ws : list word),
      FXOK fx -> m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
      WF bt st Lc FF -> Rep bt st Lc FF M0 mdl -> (forall a : word, M a <> M0 a -> X (U a) /\ M a <> None) ->
      (forall a, X a -> ~ (ia_img_lo (bt_ia bt) <= a < ia_img_hi (bt_ia bt))) -> PX bt st X -> (exists h : option Z, holes_le h st) ->
      dp_nids (a_dep st) + 1 <= dp_nids (bt_dep0 bt) + a_kact st / EVT ->
      dp_frames (a_dep st) + FRW <= dp_frames (bt_dep0 bt) + FRW * (a_kact st / EVT) + FRW * Z.of_nat (length (dp_storeblocks (a_dep st))) ->
      getr R 1 = ret -> getr R 2 = sp -> getr R 10 = buf -> getr R 11 = Z_to_bv 64 (sz + tag * 2 ^ 32) ->
      U sp mod 16 = 0 -> CEIL + KD <= U sp -> U sp + 2192 <= PTRHI -> ret_ok ret ->
      (forall a : word, U sp - KD <= U a < U sp -> M a <> None /\ store_ok BSEGS M a 1%nat = true) ->
      1 <= sz <= 8 -> 0 <= tag < 256 -> a_kact st <= KCAP ->
      Z.of_nat (length ws) = sz -> U sp <= U buf -> U buf + 8 * sz < 2 ^ 64 ->
      let Hd := HID st mdl in let Mr := mrestrict Hd M in let h := sd_hashN ws tag in
      (forall i, (i < length ws)%nat -> rdn BSEGS Mr (at_ buf (8 * Z.of_nat i)) 8 = Some (LE8 (nth i ws (Z_to_bv 64 0)))) ->
      msteps BSEGS (@mkst fx R (Z_to_bv 64 0x8f4f0) Mr (seg_rom BSEGS))
                   (@mkst fx r (Z_to_bv 64 0x8f688) (sd_frame Mr sp R ret buf (Z_to_bv 64 (sz + tag * 2 ^ 32))) (seg_rom BSEGS)) ->
      getr r 2 = at_ sp (-112) /\ getr r 8 = Z_to_bv 64 0 /\ getr r 9 = Z_to_bv 64 0x1f0098
      /\ getr r 18 = Z_to_bv 64 (0x1f0098 + 4 * sd_bix h) /\ getr r 19 = h /\ getr r 20 = Z_to_bv 64 (0x1f0098 + 4194312)
      /\ getr r 22 = Z_to_bv 64 65535 /\ getr r 24 = Z_to_bv 64 (0x1f0098 + 4194320) /\ getr r 25 = Z_to_bv 64 (dp_tab (a_dep st) (sd_bix h))
      /\ regs_agree (fun i : reg => In i sd_clobx) R r ->
      katD BSEGS (mkCfg (@mkst fx R (Z_to_bv 64 0x8f4f0) M (seg_rom BSEGS)) mdl)
           (depot_post bt FXOK KD X st Lc FF M mdl R sp ret).

  Lemma restrict_mkst9 : forall {fx : FPState} (Hd : word -> bool) (r : bvmap 5 word) pc m rom,
    restrict Hd (@mkst fx r pc m rom) = @mkst fx r pc (mrestrict Hd m) rom.
  Proof using. intros. reflexivity. Qed.

  Theorem depot_put_of_miss : forall KD, 112 <= KD -> miss_arm_stmt KD -> HYP_DEPOT9_stmt bt FXOK KD.
  Proof using DOBL DCELLS BT_ia BT_segs.
    intros KD HKD MISS fx X st Lc FF M mdl R sp buf szw ret sz HFX HH MW W RX XIMG PXH HOLES ROOM1 ROOM2 E1 E2 E10 E11 SP16 SPC SPHI RET STK SZ SZW TAGW KC BUFD BUFC BUFS BUFW.
    destruct RX as (M0 & RP & DIFF).
    pose proof ceil_rng as CR. pose proof (u64_range sp) as Hspr. pose proof (u64_range buf) as Hbufr. pose proof (u64_range szw) as Hszwr.
    unfold PTRHI in SPHI.
    set (tag := U szw / 2 ^ 32).
    assert (Htag : 0 <= tag < 256) by ((lazymatch goal with |- ?G => let G' := eval unfold tag in G in change_no_check G' end); split; [apply Z.div_pos; lia | exact TAGW]).
    assert (Eszw : szw = Z_to_bv 64 (sz + tag * 2 ^ 32)).
    { apply bv_eq. pose proof (Z.div_mod (U szw) (2 ^ 32) ltac:(lia)) as DM. rewrite SZW in DM. fold tag in DM. rewrite u_Z2bv by lia. lia. }
    (* [comment removed for export] *)
    pose proof RP as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15).
    rewrite BT_segs in *.
    destruct R9 as (Dtab & Dnids & Dmu & Dmap & Dnode & Dnw & Dfr & Dblk & Dsw).
    assert (ETAB : DEPOT_TAB bt = 0x1f0098) by ((lazymatch goal with |- ?G => let G' := eval unfold DEPOT_TAB in G in change_no_check G' end); rewrite BT_ia; reflexivity).
    assert (EMAP : DEPOT_MAP1 bt = 0x1f0098 + 4194320) by ((lazymatch goal with |- ?G => let G' := eval unfold DEPOT_MAP1 in G in change_no_check G' end); rewrite ETAB; reflexivity).
    pose proof W as (_ & _ & _ & _ & _ & _ & (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12) & _).
    set (d := a_dep st) in *. set (NIDS := dp_nids d) in *.
    destruct R14 as (Bw1 & Bw2 & _).
    destruct DOBL as (DO1 & DO2 & DO3). destruct DCELLS as (C_m & C_m8 & C_seed & C_cf & C_csd).
    (* [comment removed for export] *)
    set (Hd := HID st mdl).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st mdl z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). lia. }
    assert (NHn : forall b z, In b (node_blocks bt d) -> b <= z < b + 2 ^ 20 -> 0 <= z < 2 ^ 64 -> Hd (Z_to_bv 64 z) = false).
    { intros b z Hb Hz Hr. apply HID_notlazy; [exact Hr|]. exact (DO1 st Lc FF M0 mdl b z W RP Hb Hz). }
    set (Mr := mrestrict Hd M).
    assert (EQ0 : forall a : word, ~ X (U a) -> M a = M0 a).
    { intros a NX. destruct (decide (M a = M0 a)) as [E|NE]; [exact E|]. exfalso. exact (NX (proj1 (DIFF a NE))). }
    assert (XMr : forall (z : Z) (k : nat) bs,
              (forall i, z <= i < z + Z.of_nat k -> ~ X i /\ Hd (Z_to_bv 64 i) = false) -> 0 <= z -> z + Z.of_nat k < 2 ^ 64 ->
              rdn BSEGS M0 (Z_to_bv 64 z) k = Some bs -> rdn BSEGS Mr (Z_to_bv 64 z) k = Some bs).
    { intros z k bs F Hz Hk Hr. rewrite <- Hr. apply rdn_ext; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]|].
      intros x Hx. rewrite u_Z2bv in Hx by lia. destruct (F (U x) Hx) as [NX NHx]. rewrite Z_to_bv_bv_unsigned in NHx.
      (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite (mrestrict_off Hd M x NHx). apply EQ0. exact NX. }
    assert (XI : forall i, AIMGLO <= i < AIMGHI -> ~ X i /\ Hd (Z_to_bv 64 i) = false).
    { intros i Hi. split; [| apply NHs; lia]. intros Xi. apply (XIMG i Xi). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). lia. }
    (* [comment removed for export] *)
    assert (K_m : rdn BSEGS Mr (Z_to_bv 64 0x10310) 8 = Some (LE8 mmM)).
    { apply (XMr 0x10310 8%nat); [intros i Hi; apply XI; cbn in Hi; lia | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact (const_cell bt M0 _ _ _ R1 C_m)]. }
    assert (K_m8 : rdn BSEGS Mr (Z_to_bv 64 0x10348) 8 = Some (LE8 mmM8)).
    { apply (XMr 0x10348 8%nat); [intros i Hi; apply XI; cbn in Hi; lia | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact (const_cell bt M0 _ _ _ R1 C_m8)]. }
    assert (K_seed : rdn BSEGS Mr (Z_to_bv 64 0x10448) 8 = Some (LE8 mmSEED)).
    { apply (XMr 0x10448 8%nat); [intros i Hi; apply XI; cbn in Hi; lia | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact (const_cell bt M0 _ _ _ R1 C_seed)]. }
    (* [comment removed for export] *)
    set (DW := Z_to_bv 64 0x1f0098 : word).
    assert (UDW : U DW = 0x1f0098) by reflexivity.
    assert (N0 : 0 <= NIDS) by (pose proof (D4 0 ltac:(lia)); lia).
    set (blkf := fun i : Z => Z_to_bv 64 (nth (Z.to_nat i) (node_blocks bt d) 0) : word).
    assert (LNB : Z.of_nat (length (node_blocks bt d)) = NIDS / 2 ^ 16 + 1) by ((lazymatch goal with |- ?G => let G' := eval unfold node_blocks in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); rewrite Nat2Z.inj_succ; unfold d, NIDS in *; lia).
    assert (Q16 : 0 <= NIDS / 2 ^ 16 < 2 ^ 15) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (BLK : forall i, 0 <= i <= NIDS / 2 ^ 16 -> In (nth (Z.to_nat i) (node_blocks bt d) 0) (node_blocks bt d)) by (intros i Hi; apply nth_In; lia).
    assert (BGEO : forall b, In b (node_blocks bt d) -> AIMGHI <= b /\ b + 2 ^ 20 <= CEIL).
    { intros b Hb. destruct (node_blocks_dyn bt st Lc FF W b Hb) as ((G0 & G1 & G2 & G3 & _) & _). rewrite BT_ia in G3. cbn [ia_img_lo ia_img_hi both_addrs] in G3.  lia. }
    assert (Rtab : forall b, 0 <= b < 2 ^ 20 -> rdn BSEGS Mr (Z_to_bv 64 (U DW + 4 * b)) 4 = Some (LE4 (Z_to_bv 64 (dp_tab d b))) /\ 0 <= dp_tab d b <= NIDS).
    { intros b Hb. split; [| exact (D4 b Hb)]. rewrite UDW.
      apply (XMr (0x1f0098 + 4 * b) 4%nat); [intros i Hi; apply XI; cbn in Hi; lia | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |].
      pose proof (Dtab b Hb) as C. rewrite ETAB, BT_segs in C. exact C. }
    assert (Rmap : forall i, 0 <= i <= NIDS / 2 ^ 16 -> rdn BSEGS Mr (Z_to_bv 64 (U DW + 4194320 + 8 * i)) 8 = Some (LE8 (blkf i)) /\ U (blkf i) <> 0 /\ U (blkf i) + 2 ^ 20 <= 2 ^ 64).
    { intros i Hi. destruct (BGEO _ (BLK i Hi)) as [G1 G2]. 
      assert (UB : U (blkf i) = nth (Z.to_nat i) (node_blocks bt d) 0) by ((lazymatch goal with |- ?G => let G' := eval unfold blkf in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
      split; [| rewrite UB; lia]. rewrite UDW.
      apply (XMr (0x1f0098 + 4194320 + 8 * i) 8%nat); [intros j Hj; apply XI; cbn in Hj; lia | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |].
      pose proof (Dmap i ltac:(lia)) as C. rewrite EMAP, BT_segs in C. exact C. }
    assert (NADDR : forall id, 1 <= id <= NIDS -> nd blkf id = Z_to_bv 64 (node_addr bt d id) /\ In (nth (Z.to_nat (id / 2 ^ 16)) (node_blocks bt d) 0) (node_blocks bt d)
                                               /\ 0 <= id mod 2 ^ 16 < 2 ^ 16).
    { intros id Hid. assert (I16 : 0 <= id / 2 ^ 16 <= NIDS / 2 ^ 16) by (split; [apply Z.div_pos; lia | apply Z.div_le_mono; lia]).
      pose proof (Z.mod_pos_bound id (2 ^ 16) ltac:(lia)) as M16. destruct (BGEO _ (BLK _ I16)) as [G1 G2]. 
      split; [| split; [exact (BLK _ I16) | exact M16]]. (lazymatch goal with |- ?G => let G' := eval unfold nd, node_addr, blkf in G in change_no_check G' end). apply bv_eq. rewrite at_u; first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite !u_Z2bv by lia; lia ]. }
    assert (Rnode : forall id, 1 <= id <= NIDS ->
              rdn BSEGS Mr (nd blkf id) 8 = Some (LE8 (Z_to_bv 64 (dp_hash d id))) /\ rdn BSEGS Mr (at_ (nd blkf id) 8) 4 = Some (LE4 (Z_to_bv 64 (dp_link d id))) /\ 0 <= dp_link d id < id).
    { intros id Hid. destruct (NADDR id Hid) as (EN & INB & M16). destruct (BGEO _ INB) as [G1 G2]. 
      destruct (Dnode id Hid) as (Ch & Cl & _). rewrite BT_segs in Ch, Cl. destruct (D5 id Hid) as (L1 & _).
      assert (NA : node_addr bt d id = nth (Z.to_nat (id / 2 ^ 16)) (node_blocks bt d) 0 + 16 * (id mod 2 ^ 16)) by reflexivity.
      assert (OFF : forall i, node_addr bt d id <= i < node_addr bt d id + 16 -> ~ X i /\ Hd (Z_to_bv 64 i) = false).
      { intros i Hi. split; [intros Xi; exact (proj2 (XIMG i Xi) id Hid Hi) | apply (NHn _ i INB); lia]. }
      rewrite EN. split; [| split; [| exact L1]].
      - apply (XMr (node_addr bt d id) 8%nat); [intros i Hi; apply OFF; cbn in Hi; lia | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Ch].
      - replace (at_ (Z_to_bv 64 (node_addr bt d id)) 8) with (Z_to_bv 64 (node_addr bt d id + 8) : word) by (apply bv_eq; rewrite at_u; first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite !u_Z2bv by lia; lia ]).
        apply (XMr (node_addr bt d id + 8) 4%nat); [intros i Hi; apply OFF; cbn in Hi; lia | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Cl]. }
    (* [comment removed for export] *)
    assert (NHstk : forall x : word, U sp - KD <= U x -> Hd x = false).
    { intros x Hx. pose proof (u64_range x) as Hxr. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHs; [lia | left; lia]. }
    assert (SOKstk : store_ok BSEGS Mr (at_ sp (-112)) 112 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; rewrite at_u in Hx by lia; apply NHstk; lia].
      apply store_ok_bytes; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply STK. lia. }
    destruct (trace_words Mr (Z.to_nat sz) buf) as (ws & Lws & Rws).
    { intros i Hi. rewrite Z2Nat.id in Hi by lia. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite mrestrict_off by (rewrite <- (Z_to_bv_bv_unsigned 64 (Z_to_bv 64 i)); apply NHs; rewrite u_Z2bv by lia; [lia | left; lia]).
      apply BUFD. exact Hi. }
    { rewrite Z2Nat.id by lia. lia. }
    assert (Lws' : Z.of_nat (length ws) = sz) by (rewrite Lws, Z2Nat.id by lia; reflexivity).
    (* [comment removed for export] *)
    pose proof both_sd_tab_ok as TOK.
    assert (PA1 : U DW + 5242880 < 2 ^ 64) by (rewrite UDW; lia).
    assert (PA2 : Z.of_nat (length ws) = sz /\ 1 <= sz < 2 ^ 31) by (split; [exact Lws' | lia]).
    assert (PA3 : 0 <= tag < 2 ^ 32) by lia.
    assert (PA4 : forall i : nat, (i < length ws)%nat -> rdn BSEGS Mr (at_ buf (8 * Z.of_nat i)) 8 = Some (LE8 (nth i ws (Z_to_bv 64 0)))) by (rewrite Lws; exact Rws).
    assert (PA5 : 0 <= NIDS < 2 ^ 31 - 1) by lia.
    assert (PA6 : 2 ^ 32 + 112 <= U sp < 2 ^ 64) by lia.
    assert (PA7 : (U buf + 8 * sz <= U sp - 112 \/ U sp <= U buf) /\ 0 < U buf /\ U buf + 8 * sz < 2 ^ 64) by lia.
    assert (PA8 : Forall (fun c : Z => 0 <= c /\ c + 8 <= 2 ^ 32) [0x10348; 0x10448; 0x10310]) by (repeat constructor; lia).
    assert (PA9 : U DW + 5242880 <= 2 ^ 32) by (rewrite UDW; lia).
    assert (PA10 : forall i : Z, 0 <= i <= NIDS / 2 ^ 16 -> U (blkf i) + 2 ^ 20 <= U sp - 112 \/ U sp <= U (blkf i)).
    { intros i Hi. destruct (BGEO _ (BLK i Hi)) as [G1 G2]. left. (lazymatch goal with |- ?G => let G' := eval unfold blkf in G in change_no_check G' end). rewrite u_Z2bv by lia. lia. }
    assert (PA11 : getr R 11 = Z_to_bv 64 (sz + tag * 2 ^ 32)) by (rewrite E11; exact Eszw).
    destruct (sd_probe BSEGS (Z_to_bv 64 0x8f4f0) DW 0x10348 0x10448 0x10310 (sto_code _ _ TOK) (sto_a4 _ _ TOK) (sto_g128 _ _ TOK) (sto_g132 _ _ TOK) (sto_g148 _ _ TOK)
                PA1 Mr (seg_rom BSEGS) buf sp ret ws sz tag NIDS (dp_tab d) blkf (fun id => Z_to_bv 64 (dp_hash d id)) (dp_link d)
                PA2 PA3 PA4 K_m8 K_seed K_m PA5 Rtab Rmap Rnode PA6 SOKstk PA7 PA8 PA9 PA10 RET R E1 E2 E10 PA11)
      as [(r & id & RUN & H10 & Hid & Hh & AG) | (r & RUN & F2 & F8 & F9 & F11 & F18 & F19 & F20 & F22 & F23 & F24 & F25 & AG)].
    (* [comment removed for export] *)
    {
    change (SM1 Mr buf sp ret sz tag R) with (sd_frame Mr sp R ret buf (Z_to_bv 64 (sz + tag * 2 ^ 32))) in RUN.
    set (SM := sd_frame Mr sp R ret buf (Z_to_bv 64 (sz + tag * 2 ^ 32))) in RUN.
    apply (katD_msteps_acct BSEGS Hd (HID_off_segments bt st Lc FF M0 mdl BT_ia RP) asanF_segs_wx (a_aa st)
             (@mkst fx R (Z_to_bv 64 0x8f4f0) M (seg_rom BSEGS)) (@mkst fx r ret SM (seg_rom BSEGS)) mdl).
    { apply lazy_cover_HID. } { exact Bw1. } { exact Bw2. } { exact HH. }
    { rewrite restrict_mkst9. exact RUN. }
    intros mdl1 MI1 SBM1 HC1. rewrite unrestrict_mkst.
    replace (ms_mem (@mkst fx R (Z_to_bv 64 0x8f4f0) M (seg_rom BSEGS))) with M by reflexivity.
    set (M' := munrestrict Hd M SM).
    assert (SUM : msum (ivl (U sp - 112) 112) M M').
    { apply msum_unrestrict; [intros x Hx; apply NHstk; unfold ivl in Hx; lia|].
      apply (sdf_sum Mr sp ret buf sz tag R); lia. }
    destruct SUM as [FR GR].
    pose proof (same_but_materialized_frame mdl mdl1 SBM1) as (_ & _ & Elz & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehl & _).
    assert (CHG : forall a : word, M' a <> M a -> U sp - 112 <= U a < U sp /\ M' a <> None).
    { intros a NE. assert (IV : ivl (U sp - 112) 112 (U a)) by (destruct (Z_lt_le_dec (U a) (U sp - 112)) as [C|C]; [exfalso; apply NE; apply FR; (lazymatch goal with |- ?G => let G' := eval unfold ivl in G in change_no_check G' end); lia|];
                                                                destruct (Z_lt_le_dec (U a) (U sp)) as [C'|C']; [(lazymatch goal with |- ?G => let G' := eval unfold ivl in G in change_no_check G' end); lia | exfalso; apply NE; apply FR; (lazymatch goal with |- ?G => let G' := eval unfold ivl in G in change_no_check G' end); lia]).
      unfold ivl in IV. split; [lia|]. apply GR. apply STK. lia. }
    apply katD_refl. exists fx, st, M', mdl1, r, id.
    split; [reflexivity|]. split; [exact HFX|]. split; [exists (a_dep st), []; symmetry; apply depot_st_id|]. split; [exact W|].
    split.
    { apply (repx_frame_step bt X st Lc FF M M' mdl mdl1 W); [exists M0; split; [exact RP | exact DIFF] | | exact MI1 | exact SBM1].
      intros a NE. destruct (CHG a NE) as [RG DF]. split; [| exact DF]. intros RCa. pose proof (rep_cells_lt_ceil bt BT_ia st Lc FF (U a) W RCa). lia. }
    split. { intros a Xa OUT. apply FR. (lazymatch goal with |- ?G => let G' := eval unfold ivl in G in change_no_check G' end). lia. }
    split. { intros a NE. destruct (CHG a NE) as [RG DF]. split; [| exact DF]. (lazymatch goal with |- ?G => let G' := eval unfold depot_foot in G in change_no_check G' end). right. right. right. lia. }
    split. { intros a NE. destruct (CHG a NE) as [RG DF]. left. lia. }
    split.
    { apply (regs_kept_of_agree sd_clob R r AG). intros z Hz. left. unfold as_callee_saved in Hz. (lazymatch goal with |- ?G => let G' := eval unfold sd_clob in G in change_no_check G' end). cbn [In] in Hz |- *.
      repeat (destruct Hz as [<-|Hz]; [intros HX; repeat (destruct HX as [HX|HX]; [discriminate HX|]); exact HX|]). destruct Hz. }
    split; [exact H10|]. split; [unfold NIDS in *; lia|].
    split; [exact (same_but_materialized_except_vm mdl mdl1 SBM1)|].
    split; [intros a; first [left | intros _; left]; (lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end); rewrite Elz; reflexivity|].   (* [comment removed for export] *)
    split; [rewrite Ehl; exact HH | exact (model_ivs_wf_sbm mdl mdl1 SBM1 MW)]. }
    (* [comment removed for export] *)
    apply (MISS fx X st Lc FF M M0 mdl R r sp buf ret sz tag ws HFX HH MW W RP DIFF (fun a Xa => proj1 (XIMG a Xa)) PXH HOLES ROOM1 ROOM2 E1 E2 E10 PA11 SP16 SPC
                ltac:((lazymatch goal with |- ?G => let G' := eval unfold PTRHI in G in change_no_check G' end); lia) RET STK SZ Htag KC Lws' BUFS BUFW).
    - intros i Hi. apply PA4. exact Hi.
    - exact RUN.
    - rewrite UDW in *. repeat (split; [assumption|]). exact AG.
  Qed.
End TOP.
End BoDepotTop1.
Require Stdlib.Sorting.Permutation OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsDp3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsDp23 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoDepotTop2.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsKInst OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsDp3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsDp23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotHit OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotIns OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.BoDepotStore OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotStoreR OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp.BoDepotImg OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove.AsDepotSum OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotRunT OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotRunH OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotRunS OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI BoDepotRunP BoDepotHyp9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsDepotTop0 BoDepotTop1.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac wm_clear_disj2_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj2_or A | wm_clear_disj2_or B] | ?A <-> ?B => first [wm_clear_disj2_or A | wm_clear_disj2_or B] | ?A -> ?B => first [wm_clear_disj2_or A | wm_clear_disj2_or B] end.
Ltac wm_clear_disj2 := repeat match goal with H : ?T |- _ => wm_clear_disj2_or T; clear H end.
Ltac wm_lia02 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                 else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac am_inner ::= first [ solve [wm_clear_disj2; wm_lia02] | wm_lia02 ].
#[local] Ltac lia ::= am_lia.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 v := (word_to_le_bytes 4 v).
#[local] Abbreviation U := bv_unsigned.

Lemma stored_le4 : forall sov c, 0 <= sov < 2 ^ 32 -> 0 <= c < 2 ^ 32 ->
  word_to_le_bytes 4 (v_add (Z_to_bv 64 sov) (Z_to_bv 64 c)) = word_to_le_bytes 4 (Z_to_bv 64 ((sov + c) mod 2 ^ 32)).
Proof.
  intros sov c Hs Hc. apply le4_congr. pose proof (Z.mod_pos_bound (sov + c) (2 ^ 32) ltac:(lia)) as MB.
  (lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end). rewrite (u_Z2bv sov), (u_Z2bv c) by lia. rewrite (u_Z2bv (sov + c)) by lia. rewrite (u_Z2bv ((sov + c) mod 2 ^ 32)) by lia.
  (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap in G in change_no_check G' end). change (bv_modulus 32) with (2 ^ 32). rewrite Z.mod_mod by lia. reflexivity.
Qed.

Section TOP2.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis DCELLS : depot_cells bt.
  Hypothesis DOBL : depot_obls bt.
  (* [comment removed for export] *)
  Hypothesis DEPOT_FRAMES_ROOM : forall st Lc FF, WF bt st Lc FF -> depot_room bt st -> a_kact st <= KCAP -> dp_frames (a_dep st) + 2 * FRW <= 2 ^ 32.
  Hypothesis DEP0 : dp_nids (bt_dep0 bt) <= 2 ^ 20.

  (* [comment removed for export] *)
  Definition nogrow (st : ast) (sz : Z) : Prop :=
    let d := a_dep st in
    (dp_nids d + 1) / 2 ^ 16 = dp_nids d / 2 ^ 16
    /\ dp_frames d / 2 ^ 20 = (dp_frames d + sz) / 2 ^ 20 /\ (dp_frames d mod 2 ^ 20 <> 0 \/ dp_frames d = 0).

  Lemma miss_nogrow_run : forall KD, 224 <= KD ->
    forall fx (X : Z -> Prop) st Lc FF (M M0 : mem) mdl (R r : bvmap 5 word) (sp buf ret : word) (sz tag : Z) (ws : list word),
      WF bt st Lc FF -> Rep bt st Lc FF M0 mdl -> (forall a : word, M a <> M0 a -> X (U a) /\ M a <> None) ->
      (forall a, X a -> ~ (ia_img_lo (bt_ia bt) <= a < ia_img_hi (bt_ia bt))) -> PX bt st X ->
      depot_room bt st -> a_kact st <= KCAP ->
      getr R 1 = ret -> getr R 2 = sp ->
      CEIL + KD <= U sp -> U sp + 2192 <= 2 ^ 47 -> ret_ok ret ->
      (forall a : word, U sp - KD <= U a < U sp -> M a <> None /\ store_ok BSEGS M a 1%nat = true) ->
      1 <= sz <= 8 -> 0 <= tag < 256 -> U sp <= U buf -> U buf + 8 * sz < 2 ^ 64 ->
      (forall i, U buf <= i < U buf + 8 * sz -> M (Z_to_bv 64 i) <> None) ->
      nogrow st sz ->
      let Hd := HID st mdl in let Mr := mrestrict Hd M in let h := sd_hashN ws tag in
      let d := a_dep st in let tot := dp_frames d in let q := tot / 2 ^ 20 in let b := sd_bix h in
      let blk := nth (Z.to_nat ((dp_nids d + 1) / 2 ^ 16)) (node_blocks bt d) 0 in let blkd := nth (Z.to_nat q) (store_blocks bt d) 0 in
      let nda := blk + 16 * ((dp_nids d + 1) mod 2 ^ 16) in
      let SM := sd_frame Mr sp R ret buf (Z_to_bv 64 (sz + tag * 2 ^ 32)) in
      getr r 2 = at_ sp (-112) /\ getr r 8 = Z_to_bv 64 0 /\ getr r 9 = Z_to_bv 64 0x1f0098
      /\ getr r 18 = Z_to_bv 64 (0x1f0098 + 4 * b) /\ getr r 19 = h /\ getr r 20 = Z_to_bv 64 (0x1f0098 + 4194312)
      /\ getr r 22 = Z_to_bv 64 65535 /\ getr r 24 = Z_to_bv 64 (0x1f0098 + 4194320) /\ getr r 25 = Z_to_bv 64 (dp_tab d b)
      /\ regs_agree (fun i : reg => In i sd_clobx) R r ->
      exists r' M'r,
        msteps BSEGS (@mkst fx r (Z_to_bv 64 0x8f688) SM (seg_rom BSEGS)) (@mkst fx r' ret M'r (seg_rom BSEGS))
        /\ msum (wun (ivl (U sp - 112) 112)
                     (ins_W sp (Z_to_bv 64 0x1f0098) (Z_to_bv 64 (0x1f0098 + 4 * b)) (Z_to_bv 64 nda) (1966216 + 16 * q + 24) (blkd + 8 * (tot mod 2 ^ 20)) (8 + 8 * sz))) Mr M'r
        /\ getr r' 10 = Z_to_bv 64 (dp_nids d + 1) /\ getr r' 2 = sp
        /\ (forall k, In k [8; 9; 18; 19; 20; 21; 22; 23; 24; 25] -> getr r' (Z_to_bv 5 k) = getr R (Z_to_bv 5 k))
        /\ rdn BSEGS M'r (Z_to_bv 64 (0x1f0098 + 4 * b)) 4 = Some (LE4 (Z_to_bv 64 (dp_nids d + 1)))
        /\ rdn BSEGS M'r (Z_to_bv 64 (0x1f0098 + 4194304)) 4 = Some (LE4 (Z_to_bv 64 (dp_nids d + 1)))
        /\ rdn BSEGS M'r (Z_to_bv 64 nda) 8 = Some (LE8 h) /\ rdn BSEGS M'r (Z_to_bv 64 (nda + 8)) 4 = Some (LE4 (Z_to_bv 64 (dp_tab d b)))
        /\ rdn BSEGS M'r (Z_to_bv 64 (nda + 12)) 4 = Some (LE4 (Z_to_bv 64 (tot + 1)))
        /\ rdn BSEGS M'r (Z_to_bv 64 1966216) 8 = Some (LE8 (Z_to_bv 64 (tot + sz + 1)))
        /\ rdn BSEGS M'r (Z_to_bv 64 (1966216 + 16 * q + 24)) 4 = Some (LE4 (Z_to_bv 64 ((dp_stored d q + sz + 1) mod 2 ^ 32)))
        /\ regs_agree (fun i : reg => In i put_clob) r r'
        (* [comment removed for export] *)
        /\ In blk (node_blocks bt d) /\ In blkd (store_blocks bt d) /\ 0x663000 <= blk /\ blk + 2 ^ 20 <= CEIL /\ 0x663000 <= blkd /\ blkd + 2 ^ 23 <= CEIL
        /\ 0 <= tot mod 2 ^ 20 /\ tot mod 2 ^ 20 + sz < 2 ^ 20 /\ 0 <= tot /\ tot + 18 <= 2 ^ 32 /\ 0 <= (dp_nids d + 1) mod 2 ^ 16 < 2 ^ 16
        /\ (forall z, blk <= z < blk + 2 ^ 20 -> Hd (Z_to_bv 64 z) = false) /\ (forall z, blkd <= z < blkd + 2 ^ 23 -> Hd (Z_to_bv 64 z) = false).
  Proof using DEPOT_FRAMES_ROOM DOBL DCELLS BT_ia BT_segs.
    intros KD HKD fx X st Lc FF M M0 mdl R r sp buf ret sz tag ws W RP DIFF XIMG PXH ROOM KC E1 E2 SPC SPHI RET STK SZ Htag BUFS BUFW BUFD NG
           Hd Mr h d tot q b blk blkd nda SM (F2 & F8 & F9 & F18 & F19 & F20 & F22 & F24 & F25 & AGp).
    pose proof ceil_rng as CR. pose proof (u64_range sp) as Hspr. pose proof (u64_range buf) as Hbufr.
    destruct NG as (CA & CI1 & CI2). fold d in CA, CI1, CI2. fold tot in CI1, CI2.
    pose proof RP as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15).
    rewrite BT_segs in R1.
    destruct R9 as (Dtab & Dnids & Dmu & Dmap & Dnode & Dnw & Dfr & Dblk & Dsw).
    assert (ETAB : DEPOT_TAB bt = 0x1f0098) by ((lazymatch goal with |- ?G => let G' := eval unfold DEPOT_TAB in G in change_no_check G' end); rewrite BT_ia; reflexivity).
    assert (EMAP : DEPOT_MAP1 bt = 0x1f0098 + 4194320) by ((lazymatch goal with |- ?G => let G' := eval unfold DEPOT_MAP1 in G in change_no_check G' end); rewrite ETAB; reflexivity).
    assert (ENID : DEPOT_NIDS bt = 0x1f0098 + 4194304) by ((lazymatch goal with |- ?G => let G' := eval unfold DEPOT_NIDS in G in change_no_check G' end); rewrite ETAB; reflexivity).
    assert (ESS : SSOBJ bt = 1966216) by ((lazymatch goal with |- ?G => let G' := eval unfold SSOBJ in G in change_no_check G' end); rewrite BT_ia; reflexivity).
    pose proof W as (_ & _ & _ & _ & _ & _ & (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12) & _).
    fold d in D1, D2, D3, D4, D5, D6, D7, D8, D9, D10, D11, D12, Dtab, Dnids, Dmu, Dmap, Dnode, Dnw, Dfr, Dblk, Dsw. fold tot in D7, D9, D10, Dfr.
    set (NIDS := dp_nids d) in *.
    assert (N0 : 0 <= NIDS) by (first [clear - D4 | idtac]; (pose proof (D4 0 ltac:(lia)); lia)).
    pose proof (DEPOT_FRAMES_ROOM st Lc FF W ROOM KC) as FROOM. fold d tot in FROOM. unfold FRW in FROOM.
    destruct R14 as (Bw1 & Bw2 & _ & _ & _ & _ & Bw7 & _).
    destruct DOBL as (DO1 & DO2 & DO3). destruct DCELLS as (C_m & C_m8 & C_seed & C_cf & C_csd).
    assert (Q20 : 0 <= q < 2 ^ 12) by ((lazymatch goal with |- ?G => let G' := eval unfold q in G in change_no_check G' end); split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (M20 : 0 <= tot mod 2 ^ 20 /\ tot mod 2 ^ 20 + sz < 2 ^ 20).
    { pose proof (Z.div_mod tot (2 ^ 20) ltac:(lia)) as X1. pose proof (Z.mod_pos_bound tot (2 ^ 20) ltac:(lia)) as X2.
      pose proof (Z.div_mod (tot + sz) (2 ^ 20) ltac:(lia)) as X3. pose proof (Z.mod_pos_bound (tot + sz) (2 ^ 20) ltac:(lia)) as X4.
      rewrite <- CI1 in X3. lia. }
    assert (I16 : 0 <= (NIDS + 1) / 2 ^ 16 < 2 ^ 15) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (M16 : 0 <= (NIDS + 1) mod 2 ^ 16 < 2 ^ 16) by (apply Z.mod_pos_bound; lia).
    (* [comment removed for export] *)
    assert (INB : In blk (node_blocks bt d)).
    { (lazymatch goal with |- ?G => let G' := eval unfold blk in G in change_no_check G' end). apply nth_In. (lazymatch goal with |- ?G => let G' := eval unfold node_blocks in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end). fold NIDS. rewrite CA. lia. }
    destruct (node_blocks_dyn bt st Lc FF W blk INB) as ((GB0 & GB1 & GB2 & GB3 & _) & _). rewrite BT_ia in GB3. cbn [ia_img_lo ia_img_hi both_addrs] in GB3.
    assert (LQ : Z.of_nat (length (dp_storeblocks d)) = q \/ (tot = 0 /\ q = 0)).
    { destruct CI2 as [NZ | Z0]; [left | right; (lazymatch goal with |- ?G => let G' := eval unfold q in G in change_no_check G' end); rewrite Z0; split; reflexivity].
      assert (E : (tot - 1) / 2 ^ 20 = q).
      { (lazymatch goal with |- ?G => let G' := eval unfold q in G in change_no_check G' end). pose proof (Z.div_mod tot (2 ^ 20) ltac:(lia)) as X1. pose proof (Z.mod_pos_bound tot (2 ^ 20) ltac:(lia)) as X2.
        symmetry. apply (Z.div_unique (tot - 1) (2 ^ 20) (tot / 2 ^ 20) (tot mod 2 ^ 20 - 1)); lia. }
      rewrite D10, E. (first [clear - Q20 | idtac]; lia). }
    assert (INQ : In blkd (store_blocks bt d)).
    { (lazymatch goal with |- ?G => let G' := eval unfold blkd in G in change_no_check G' end). apply nth_In. (lazymatch goal with |- ?G => let G' := eval unfold store_blocks in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end). destruct LQ as [LQ | [_ LQ]]; (first [clear - LQ | idtac]; lia). }
    destruct (store_blocks_dyn bt st Lc FF W blkd INQ) as ((GQ0 & GQ1 & GQ2 & GQ3 & _) & _). rewrite BT_ia in GQ3. cbn [ia_img_lo ia_img_hi both_addrs] in GQ3.
    pose proof (node_vs_store bt st Lc FF W blk blkd INB INQ) as NVS.
    (* [comment removed for export] *)
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st mdl z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). lia. }
    assert (NHn : forall z, blk <= z < blk + 2 ^ 20 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. exact (DO1 st Lc FF M0 mdl blk z W RP INB Hz). }
    assert (NHq : forall z, blkd <= z < blkd + 2 ^ 23 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_allowed. apply (Bw7 blkd INQ). exact Hz. }
    assert (NHx : forall x : word, U sp - KD <= U x -> Hd x = false).
    { intros x Hx. pose proof (u64_range x) as Hxr. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHs; [lia | left; lia]. }
    assert (EQ0 : forall a : word, ~ X (U a) -> M a = M0 a).
    { intros a NX. destruct (decide (M a = M0 a)) as [E|NE]; [exact E|]. exfalso. exact (NX (proj1 (DIFF a NE))). }
    assert (XMr : forall (z : Z) (k : nat) bs,
              (forall i, z <= i < z + Z.of_nat k -> ~ X i /\ Hd (Z_to_bv 64 i) = false) -> 0 <= z -> z + Z.of_nat k < 2 ^ 64 ->
              rdn BSEGS M0 (Z_to_bv 64 z) k = Some bs -> rdn BSEGS Mr (Z_to_bv 64 z) k = Some bs).
    { intros z k bs F Hz Hk Hr. rewrite <- Hr. apply rdn_ext; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]|].
      intros x Hx. rewrite u_Z2bv in Hx by lia. destruct (F (U x) Hx) as [NX NHx']. rewrite Z_to_bv_bv_unsigned in NHx'.
      (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite (mrestrict_off Hd M x NHx'). apply EQ0. exact NX. }
    assert (XI : forall i, AIMGLO <= i < AIMGHI -> ~ X i /\ Hd (Z_to_bv 64 i) = false).
    { intros i Hi. split; [| apply NHs; lia]. intros Xi. apply (XIMG i Xi). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). lia. }
    (* [comment removed for export] *)
    assert (SF : msum (ivl (U sp - 112) 112) Mr SM) by (apply (sdf_sum Mr sp ret buf sz tag R); lia).
    assert (THRU : forall (z : Z) (k : nat) bs, 0 <= z -> z + Z.of_nat k <= U sp - 112 -> rdn BSEGS Mr (Z_to_bv 64 z) k = Some bs -> rdn BSEGS SM (Z_to_bv 64 z) k = Some bs).
    { intros z k bs Hz Hk Hr. apply (msum_rdn_eq BSEGS _ Mr SM _ _ _ SF); [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | | exact Hr].
      intros i Hi. rewrite u_Z2bv in Hi by lia. (lazymatch goal with |- ?G => let G' := eval unfold ivl in G in change_no_check G' end). lia. }
    assert (IMG : forall (z : Z) (k : nat) v, AIMGLO <= z -> z + Z.of_nat k <= AIMGHI -> cellZ BSEGS M0 z k v ->
              rdn BSEGS SM (Z_to_bv 64 z) k = Some (word_to_le_bytes k (Z_to_bv 64 v))).
    { intros z k v Hz Hk C. apply THRU; [lia | lia|]. apply (XMr z k); [intros i Hi; apply XI; (first [clear - Hi Hk Hz | idtac]; lia) | (first [clear - Hz | idtac]; lia) | (first [clear - Hk | idtac]; lia) | exact C]. }
    pose proof (Dtab b ltac:(apply bix_range)) as Cb. rewrite ETAB, BT_segs in Cb.
    pose proof Dnids as Cn. rewrite ENID, BT_segs in Cn.
    pose proof (Dmap ((NIDS + 1) / 2 ^ 16) ltac:(lia)) as Cm. rewrite EMAP, BT_segs in Cm. fold blk in Cm.
    pose proof Dfr as Ct. rewrite ESS, BT_segs in Ct.
    destruct (Dblk q Q20) as (Cbd & Cso & _). rewrite ESS, BT_segs in Cbd, Cso. fold blkd in Cbd.
    pose proof (bix_range h) as Hbix. fold b in Hbix.
    set (DW := Z_to_bv 64 0x1f0098 : word). assert (UDW : U DW = 0x1f0098) by reflexivity.
    set (blkW := Z_to_bv 64 blk : word). assert (UbW : U blkW = blk) by ((lazymatch goal with |- ?G => let G' := eval unfold blkW in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
    set (blkdW := Z_to_bv 64 blkd : word). assert (UbdW : U blkdW = blkd) by ((lazymatch goal with |- ?G => let G' := eval unfold blkdW in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
    set (CFW := Z_to_bv 64 0x19fce8 : word). assert (UCF : U CFW = 0x19fce8) by reflexivity.
    assert (Rb : rdn BSEGS SM (Z_to_bv 64 (U DW + 4 * b)) 4 = Some (LE4 (Z_to_bv 64 (dp_tab d b)))) by (rewrite UDW; apply IMG; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Cb]).
    assert (Rcnt : rdn BSEGS SM (at_ DW 0x400000) 4 = Some (LE4 (Z_to_bv 64 NIDS))).
    { replace (at_ DW 0x400000) with (Z_to_bv 64 (0x1f0098 + 4194304) : word) by (apply bv_eq; reflexivity). apply IMG; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Cn]. }
    assert (Rmap : rdn BSEGS SM (Z_to_bv 64 (U DW + 0x400010 + 8 * ((NIDS + 1) / 2 ^ 16))) 8 = Some (LE8 blkW)).
    { rewrite UDW. apply IMG; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Cm]. }
    assert (Rtot : rdn BSEGS SM SSW 8 = Some (LE8 (Z_to_bv 64 tot))) by (apply IMG; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Ct]).
    assert (Rblk : rdn BSEGS SM (Z_to_bv 64 (U SSW + 16 * (tot / 2 ^ 20) + 16)) 8 = Some (LE8 blkdW)).
    { replace (U SSW + 16 * (tot / 2 ^ 20) + 16) with (1966216 + 16 + 16 * q) by ((lazymatch goal with |- ?G => let G' := eval unfold q in G in change_no_check G' end); change (U SSW) with 1966216; lia). apply IMG; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Cbd]. }
    assert (Rso : rdn BSEGS SM (st_cell SSW tot) 4 = Some (LE4 (Z_to_bv 64 (dp_stored d q)))).
    { (lazymatch goal with |- ?G => let G' := eval unfold st_cell in G in change_no_check G' end). replace (U SSW + 16 * (tot / 2 ^ 20) + 24) with (1966216 + 24 + 16 * q) by ((lazymatch goal with |- ?G => let G' := eval unfold q in G in change_no_check G' end); change (U SSW) with 1966216; lia). apply IMG; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Cso]. }
    assert (Rcfp : rdn BSEGS SM (Z_to_bv 64 1072904) 8 = Some (LE8 CFW)) by (apply IMG; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact (const_cell bt M0 _ _ _ R1 C_cf)]).
    assert (Rflag : rdn BSEGS SM (at_ CFW 240) 4 = Some (LE4 (Z_to_bv 64 0))).
    { replace (at_ CFW 240) with (Z_to_bv 64 0x19fdd8 : word) by (apply bv_eq; reflexivity). apply IMG; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact (const_cell bt M0 _ _ _ R1 C_csd)]. }
    destruct (sdf_args Mr sp ret buf sz tag R ltac:(lia) ltac:(lia) ltac:(lia)) as (Atr & Asz & Atag). fold SM in Atr, Asz, Atag.
    pose proof (sdf_slots Mr sp ret buf sz tag R ltac:(lia)) as SLs. fold SM in SLs.
    (* [comment removed for export] *)
    assert (DEFr : forall x : word, M x <> None -> Hd x = false -> SM x <> None).
    { intros x Dx Hx. apply (proj2 SF). (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite (mrestrict_off Hd M x Hx). exact Dx. }
    assert (DEF0 : forall x : word, M0 x <> None -> M x <> None).
    { intros x Dx. destruct (decide (M x = M0 x)) as [E|NE]; [rewrite E; exact Dx | exact (proj2 (DIFF x NE))]. }
    assert (SOKB : forall (a : word) (n : nat) lo, U a + Z.of_nat n <= 2 ^ 64 -> writableZ BSEGS M0 lo (lo + 2 ^ 23) \/ writableZ BSEGS M0 lo (lo + 2 ^ 20) ->
              (forall x : word, U a <= U x < U a + Z.of_nat n -> (lo <= U x < lo + 2 ^ 20 \/ (lo <= U x < lo + 2 ^ 23 /\ writableZ BSEGS M0 lo (lo + 2 ^ 23))) /\ Hd x = false) ->
              store_ok BSEGS SM a n = true).
    { intros a n lo Hnw WZ F. apply store_ok_bytes; [| exact Hnw]. intros x Hx. destruct (F x Hx) as [RG NHh]. apply store_ok1_some. apply DEFr; [| exact NHh].
      apply DEF0. rewrite <- (Z_to_bv_bv_unsigned 64 x). destruct RG as [RG | [RG WZ']]; [destruct WZ as [WZ|WZ]; [apply (WZ (U x)); lia | apply (WZ (U x)); lia] | apply (WZ' (U x)); lia]. }
    pose proof (Dnw blk INB) as WN. rewrite BT_segs in WN. pose proof (Dsw blkd INQ) as WQ. rewrite BT_segs in WQ.
    set (ndW := di_node blkW NIDS).
    assert (Und : U ndW = nda) by ((lazymatch goal with |- ?G => let G' := eval unfold ndW, di_node, nda in G in change_no_check G' end); rewrite UbW; fold NIDS; rewrite u_Z2bv by lia; reflexivity).
    assert (SOKn : store_ok BSEGS SM ndW 16 = true).
    { apply (SOKB ndW 16%nat blk); [rewrite Und; (lazymatch goal with |- ?G => let G' := eval unfold nda in G in change_no_check G' end); change (Z.of_nat 16) with 16; lia | right; exact WN|]. intros x Hx. rewrite Und in Hx. unfold nda in Hx. change (Z.of_nat 16) with 16 in Hx.
      split; [left; (first [clear - Hx M16 | idtac]; lia)|]. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHn. (first [clear - Hx M16 | idtac]; lia). }
    destruct (rdn_defined_ex BSEGS SM buf (Z.to_nat (8 * sz))) as (bs & Rws & Lbs).
    { intros i Hi. rewrite Z2Nat.id in Hi by (first [clear - SZ | idtac]; lia). apply DEFr; [apply BUFD; lia|]. apply NHx. rewrite u_Z2bv by (first [clear - Hi CR BUFS SPC HKD BUFW | idtac]; lia). lia. }
    { rewrite Z2Nat.id by lia. lia. }
    assert (Lbs' : Z.of_nat (length bs) = 8 * sz) by (rewrite Lbs, Z2Nat.id by lia; reflexivity).
    rewrite <- Lbs in Rws.
    assert (Udst : U (st_dst blkdW tot) = blkd + 8 * (tot mod 2 ^ 20)) by (first [clear - UbdW GQ2 GQ0 M20 SZ SPHI SPC HKD | idtac]; ((lazymatch goal with |- ?G => let G' := eval unfold st_dst in G in change_no_check G' end); rewrite UbdW; rewrite u_Z2bv by lia; reflexivity)).
    assert (SOKd : store_ok BSEGS SM (st_dst blkdW tot) (8 + length bs) = true).
    { apply (SOKB _ _ blkd); [rewrite Udst, Nat2Z.inj_add, Lbs'; change (Z.of_nat 8) with 8; lia | left; exact WQ|]. intros x Hx. rewrite Udst, Nat2Z.inj_add, Lbs' in Hx. change (Z.of_nat 8) with 8 in Hx.
      split; [right; split; [(first [clear - Hx M20 | idtac]; lia) | exact WQ]|]. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHq. (first [clear - Hx M20 | idtac]; lia). }
    assert (Hstk : store_ok BSEGS SM (at_ sp (-224)) 112 = true).
    { apply store_ok_bytes; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. intros x Hx. rewrite at_u in Hx by (first [clear - CR SPC HKD SPHI | idtac]; lia). cbn in Hx. apply store_ok1_some.
      apply DEFr; [apply STK; (first [clear - Hx HKD | idtac]; lia) | apply NHx; (first [clear - Hx HKD | idtac]; lia)]. }
    (* [comment removed for export] *)
    destruct (put_ins_run SM (seg_rom BSEGS) sp ret DW h blkW buf blkdW CFW (dp_tab d b) NIDS b sz tag tot (dp_stored d q) bs
                (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25) r
                F2 F8 F9 ltac:(rewrite UDW; exact F18) F19 F22 ltac:(rewrite UDW; exact F24) F25
                ltac:((first [clear - CR SPHI SPC HKD | idtac]; lia)) RET ltac:(rewrite UDW; split; [reflexivity | (repeat match goal with H : _ |- _ => clear H end; lia)]) ltac:(rewrite UCF; (repeat match goal with H : _ |- _ => clear H end; lia)) Hbix ltac:(pose proof (D4 b Hbix); (first [clear - H D3 | idtac]; lia)) ltac:((first [clear - N0 D3 | idtac]; lia))
                ltac:(rewrite UDW, UbW; (first [clear - GB3 GB2 GB0 SPC HKD | idtac]; lia)) ltac:(rewrite UDW, UbW, UbdW; (first [clear - NVS GQ3 GQ2 GQ0 SPC HKD | idtac]; lia)) ltac:((first [clear - BUFW BUFS | idtac]; lia)) ltac:((first [clear - SZ | idtac]; lia)) Htag ltac:((first [clear - FROOM D7 SZ | idtac]; lia)) CI1 (D11 q) Lbs
                Rb Rcnt Rmap Asz Atag Atr Rws Rtot Rblk Rso Rcfp Rflag)
      as (r' & M'r & RUN & SI & G10 & G2 & G1 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & Kb & Kn & Kh & Kl & Ks & Kt & Kso & AGi).
    { intros k v Hin. apply SLs. exact Hin. }
    { eapply (readable_store_ok BSEGS 0x107000 SM _ 4 _ both_rw_above); [rewrite UDW, u_Z2bv by (first [clear - Hbix | idtac]; lia); (first [clear - Hbix | idtac]; lia) | rewrite UDW, u_Z2bv by (first [clear - Hbix | idtac]; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); (first [clear - Hbix | idtac]; lia) | exact Rb]. }
    { eapply (readable_store_ok BSEGS 0x107000 SM _ 4 _ both_rw_above); [rewrite at_u; rewrite UDW; lia | rewrite at_u; rewrite UDW; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rcnt]. }
    { exact SOKn. } { exact Hstk. }
    { eapply (readable_store_ok BSEGS 0x107000 SM _ 8 _ both_rw_above); [change (U SSW) with 1966216; lia | change (U SSW) with 1966216; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rtot]. }
    { eapply (readable_store_ok BSEGS 0x107000 SM _ 4 _ both_rw_above); [| | exact Rso]; (lazymatch goal with |- ?G => let G' := eval unfold st_cell in G in change_no_check G' end); change (U SSW) with 1966216; fold q; rewrite u_Z2bv by (first [clear - D7 Q20 | idtac]; lia); [(first [clear - D7 | idtac]; lia) | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); (first [clear - Q20 | idtac]; lia)]. }
    { exact SOKd. }
    exists r', M'r. split; [replace (Z_to_bv 64 0x8f688) with (0x8f688%bv : word) by (apply bv_eq; reflexivity); exact RUN|].
    split.
    { apply (msum_trans _ _ Mr SM M'r SF). fold ndW in SI. unfold ins_W in *. fold q in SI. rewrite UbdW in SI.
      replace (Z_to_bv 64 (U DW + 4 * b)) with (Z_to_bv 64 (0x1f0098 + 4 * b) : word) in SI by (rewrite UDW; reflexivity).
      replace ndW with (Z_to_bv 64 nda : word) in SI by (first [clear - Und GB2 GB0 M16 SPHI SPC HKD | idtac]; (apply bv_eq; rewrite Und; rewrite u_Z2bv by ((lazymatch goal with |- ?G => let G' := eval unfold nda in G in change_no_check G' end); lia); reflexivity)).
      exact SI. }
    split; [exact G10|]. split; [exact G2|].
    split.
    { intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [assumption|]). destruct Hk. }
    split; [rewrite UDW in Kb; exact Kb|].
    split.
    { replace (Z_to_bv 64 (0x1f0098 + 4194304)) with (at_ DW 0x400000 : word) by (apply bv_eq; reflexivity). rewrite Kn. f_equal. f_equal.
      (lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end). rewrite !u_Z2bv by lia. reflexivity. }
    assert (END : Z_to_bv 64 nda = ndW :> word) by (first [clear - Und GB2 GB0 M16 SPHI SPC HKD | idtac]; (apply bv_eq; rewrite Und; rewrite u_Z2bv by ((lazymatch goal with |- ?G => let G' := eval unfold nda in G in change_no_check G' end); lia); reflexivity)).
    split; [rewrite END; exact Kh|].
    split. { replace (Z_to_bv 64 (nda + 8)) with (at_ ndW 8 : word) by (first [clear - Und GB2 GB0 M16 SPHI SPC HKD | idtac]; (apply bv_eq; rewrite at_u; rewrite Und; (lazymatch goal with |- ?G => let G' := eval unfold nda in G in change_no_check G' end); first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite ?u_Z2bv by lia; lia ])). exact Kl. }
    split. { replace (Z_to_bv 64 (nda + 12)) with (at_ ndW 12 : word) by (first [clear - Und GB2 GB0 M16 SPHI SPC HKD | idtac]; (apply bv_eq; rewrite at_u; rewrite Und; (lazymatch goal with |- ?G => let G' := eval unfold nda in G in change_no_check G' end); first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite ?u_Z2bv by lia; lia ])).
             (lazymatch goal with |- ?G => let G' := eval unfold ndW in G in change_no_check G' end). rewrite Ks. f_equal. apply st_id_le4; lia. }
    split. { change (Z_to_bv 64 1966216) with SSW. rewrite Kt. f_equal. f_equal. (lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end). rewrite !u_Z2bv by lia. f_equal. lia. }
    split.
    { replace (Z_to_bv 64 (1966216 + 16 * q + 24)) with (st_cell SSW tot : word) by ((lazymatch goal with |- ?G => let G' := eval unfold st_cell in G in change_no_check G' end); change (U SSW) with 1966216; fold q; reflexivity).
      rewrite Kso. f_equal. replace (dp_stored d q + sz + 1) with (dp_stored d q + (sz + 1)) by lia. apply stored_le4; [exact (D11 q) | lia]. }
    split; [exact AGi|].
    split; [exact INB|]. split; [exact INQ|]. repeat (split; [(first [clear - GB3 GB0 GB2 GQ3 GQ0 GQ2 D7 M20 FROOM M16 | idtac]; lia)|]). split; [exact NHn | exact NHq].
  Qed.
End TOP2.
End BoDepotTop2.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsKInst OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsDp3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsDp23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsDp3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsDp23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotHit OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotHit OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotIns OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.BoDepotStore OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove.AsDepotSum OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove.AsDepotSum2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI.BoDepotRunT OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotRunI BoDepotRunP BoDepotHyp9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsDepotTop0 BoDepotTop1 BoDepotTop2.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import HsLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac am_inner ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
#[local] Ltac lia ::= hs_am_lia.   (* [comment removed for export] *)
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 v := (word_to_le_bytes 4 v).
#[local] Abbreviation U := bv_unsigned.

Ltac nin5 := let HX := fresh "HX" in intro HX; cbn [In] in HX; repeat (destruct HX as [HX|HX]; [discriminate HX|]); exact HX.

Section TOP3.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis DCELLS : depot_cells bt.
  Hypothesis DOBL : depot_obls bt.
  Hypothesis DEPOT_FRAMES_ROOM : forall st Lc FF, WF bt st Lc FF -> depot_room bt st -> a_kact st <= KCAP -> dp_frames (a_dep st) + 2 * FRW <= 2 ^ 32.
  Hypothesis DEP0 : dp_nids (bt_dep0 bt) <= 2 ^ 20.

  Lemma max_blocks_nogrow : forall tot sz, 0 <= tot -> 1 <= sz -> tot / 2 ^ 20 = (tot + sz) / 2 ^ 20 -> (tot mod 2 ^ 20 <> 0 \/ tot = 0) ->
    Z.max 0 ((tot - 1) / 2 ^ 20) = Z.max 0 ((tot + sz + 1 - 1) / 2 ^ 20).
  Proof using.
    intros tot sz T0 S1 E [NZ | Z0].
    - replace (tot + sz + 1 - 1) with (tot + sz) by lia. rewrite <- E. f_equal.
      pose proof (Z.div_mod tot (2 ^ 20) ltac:(lia)) as X1. pose proof (Z.mod_pos_bound tot (2 ^ 20) ltac:(lia)) as X2.
      symmetry. apply (Z.div_unique (tot - 1) (2 ^ 20) (tot / 2 ^ 20) (tot mod 2 ^ 20 - 1)); lia.
    - subst tot. replace (0 + sz + 1 - 1) with (0 + sz) by lia. rewrite <- E. reflexivity.
  Qed.

  Theorem miss_nogrow : forall KD, 224 <= KD ->
    forall fx (X : Z -> Prop) st Lc FF (M M0 : mem) mdl (R r : bvmap 5 word) (sp buf ret : word) (sz tag : Z) (ws : list word),
      FXOK fx -> m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
      WF bt st Lc FF -> Rep bt st Lc FF M0 mdl -> (forall a : word, M a <> M0 a -> X (U a) /\ M a <> None) ->
      (forall a, X a -> ~ (ia_img_lo (bt_ia bt) <= a < ia_img_hi (bt_ia bt))) -> PX bt st X -> (exists h : option Z, holes_le h st) ->
      depot_room bt st -> a_kact st <= KCAP ->
      getr R 1 = ret -> getr R 2 = sp ->
      CEIL + KD <= U sp -> U sp + 2192 <= 2 ^ 47 -> ret_ok ret ->
      (forall a : word, U sp - KD <= U a < U sp -> M a <> None /\ store_ok BSEGS M a 1%nat = true) ->
      1 <= sz <= 8 -> 0 <= tag < 256 -> U sp <= U buf -> U buf + 8 * sz < 2 ^ 64 ->
      (forall i, U buf <= i < U buf + 8 * sz -> M (Z_to_bv 64 i) <> None) ->
      nogrow st sz ->
      let Hd := HID st mdl in let Mr := mrestrict Hd M in let h := sd_hashN ws tag in
      msteps BSEGS (@mkst fx R (Z_to_bv 64 0x8f4f0) Mr (seg_rom BSEGS))
                   (@mkst fx r (Z_to_bv 64 0x8f688) (sd_frame Mr sp R ret buf (Z_to_bv 64 (sz + tag * 2 ^ 32))) (seg_rom BSEGS)) ->
      getr r 2 = at_ sp (-112) /\ getr r 8 = Z_to_bv 64 0 /\ getr r 9 = Z_to_bv 64 0x1f0098
      /\ getr r 18 = Z_to_bv 64 (0x1f0098 + 4 * sd_bix h) /\ getr r 19 = h /\ getr r 20 = Z_to_bv 64 (0x1f0098 + 4194312)
      /\ getr r 22 = Z_to_bv 64 65535 /\ getr r 24 = Z_to_bv 64 (0x1f0098 + 4194320) /\ getr r 25 = Z_to_bv 64 (dp_tab (a_dep st) (sd_bix h))
      /\ regs_agree (fun i : reg => In i sd_clobx) R r ->
      katD BSEGS (mkCfg (@mkst fx R (Z_to_bv 64 0x8f4f0) M (seg_rom BSEGS)) mdl)
           (depot_post bt FXOK KD X st Lc FF M mdl R sp ret).
  Proof using DEP0 DEPOT_FRAMES_ROOM DOBL DCELLS BT_ia BT_segs.
    intros KD HKD fx X st Lc FF M M0 mdl R r sp buf ret sz tag ws HFX HH MW W RP DIFF XIMG PXH HOLES ROOM KC E1 E2 SPC SPHI RET STK SZ Htag BUFS BUFW BUFD NG
           Hd Mr h RUNp FACTS.
    pose proof ceil_rng as CR. pose proof (u64_range sp) as Hspr.
    destruct (miss_nogrow_run bt BT_segs BT_ia DCELLS DOBL DEPOT_FRAMES_ROOM KD HKD fx X st Lc FF M M0 mdl R r sp buf ret sz tag ws
                W RP DIFF XIMG PXH ROOM KC E1 E2 SPC SPHI RET STK SZ Htag BUFS BUFW BUFD NG FACTS)
      as (r' & M'r & RUN2 & SUMr & G10 & G2 & GS & Kb & Kn & Kh & Kl & Ks & Kt & Kso & AGi
          & INB & INQ & GB1 & GB2 & GQ1 & GQ2 & M20a & M20b & T0 & T32 & M16 & NHn & NHq).
    fold Hd Mr h in RUN2, SUMr, NHn, NHq.
    destruct FACTS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & AGp). destruct NG as (CA & CI1 & CI2).
    set (d := a_dep st) in *. set (tot := dp_frames d) in *. set (q := tot / 2 ^ 20) in *. set (b := sd_bix h) in *. set (NIDS := dp_nids d) in *.
    set (blk := nth (Z.to_nat ((NIDS + 1) / 2 ^ 16)) (node_blocks bt d) 0) in *. set (blkd := nth (Z.to_nat q) (store_blocks bt d) 0) in *.
    set (nda := blk + 16 * ((NIDS + 1) mod 2 ^ 16)) in *.
    set (Wall := wun (ivl (U sp - 112) 112) (ins_W sp (Z_to_bv 64 0x1f0098) (Z_to_bv 64 (0x1f0098 + 4 * b)) (Z_to_bv 64 nda) (1966216 + 16 * q + 24) (blkd + 8 * (tot mod 2 ^ 20)) (8 + 8 * sz))) in *.
    pose proof (bix_range h) as Hbix. fold b in Hbix.
    assert (Q20 : 0 <= q < 2 ^ 12) by ((lazymatch goal with |- ?G => let G' := eval unfold q in G in change_no_check G' end); split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    (* [comment removed for export] *)
    assert (CLS : forall z, Wall z -> (U sp - 224 <= z < U sp) \/ (0x1f0098 + 4 * b <= z < 0x1f0098 + 4 * b + 4) \/ (0x1f0098 + 4194304 <= z < 0x1f0098 + 4194304 + 4)
                                      \/ (nda <= z < nda + 16) \/ (1966216 <= z < 1966216 + 8) \/ (1966216 + 16 * q + 24 <= z < 1966216 + 16 * q + 24 + 4)
                                      \/ (blkd + 8 * (tot mod 2 ^ 20) <= z < blkd + 8 * (tot mod 2 ^ 20) + 8 + 8 * sz)).
    { intros z Hz. unfold Wall, ins_W, wun, ivl in Hz. rewrite !u_Z2bv in Hz by ((lazymatch goal with |- ?G => let G' := eval unfold nda in G in change_no_check G' end); lia). change (U (Z_to_bv 64 2031768)) with 2031768 in Hz. lia. }
    pose proof RP as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15).
    destruct R14 as (Bw1 & Bw2 & _).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st mdl z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). lia. }
    assert (NHW : forall x : word, Wall (U x) -> Hd x = false).
    { intros x Hx. pose proof (u64_range x) as Hxr. rewrite <- (Z_to_bv_bv_unsigned 64 x).
      destruct (CLS _ Hx) as [C|[C|[C|[C|[C|[C|C]]]]]].
      - apply NHs; [lia | left; lia].
      - apply NHs; [lia | right; lia].
      - apply NHs; [lia | right; lia].
      - apply NHn. unfold nda in C. lia.
      - apply NHs; [lia | right; lia].
      - apply NHs; [lia | right; lia].
      - apply NHq. lia. }
    assert (XW : forall z, Wall z -> z < U sp - 224 -> ~ X z).
    { intros z Hz Hlt Xz. destruct (CLS _ Hz) as [C|[C|[C|[C|[C|[C|C]]]]]]; [lia | | | | | | ].
      1,2,4,5: apply (XIMG z Xz); rewrite BT_ia; (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end); lia.
      - apply (px_off_nodes bt st Lc FF W X z blk PXH Xz INB). unfold nda in C. lia.
      - apply (px_off_stores bt st Lc FF W X z blkd PXH Xz INQ). lia. }
    (* [comment removed for export] *)
    apply (katD_msteps_acct BSEGS Hd (HID_off_segments bt st Lc FF M0 mdl BT_ia RP) asanF_segs_wx (a_aa st)
             (@mkst fx R (Z_to_bv 64 0x8f4f0) M (seg_rom BSEGS)) (@mkst fx r' ret M'r (seg_rom BSEGS)) mdl).
    { apply lazy_cover_HID. } { exact Bw1. } { exact Bw2. } { exact HH. }
    { rewrite restrict_mkst9. eapply msteps_trans; [exact RUNp | exact RUN2]. }
    intros mdl1 MI1 SBM1 HC1. rewrite unrestrict_mkst.
    replace (ms_mem (@mkst fx R (Z_to_bv 64 0x8f4f0) M (seg_rom BSEGS))) with M by reflexivity.
    set (M' := munrestrict Hd M M'r).
    pose proof (msum_unrestrict Hd Wall M M'r NHW SUMr) as [FR GR]. fold M' in FR, GR.
    pose proof (same_but_materialized_frame mdl mdl1 SBM1) as (_ & Evm & Elz & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehl & _ & _ & _ & Eeg).
    assert (VIS : forall (z : Z) (k : nat), 0 <= z -> z + Z.of_nat k < 2 ^ 64 -> (forall i, z <= i < z + Z.of_nat k -> Hd (Z_to_bv 64 i) = false) ->
              rdn BSEGS M' (Z_to_bv 64 z) k = rdn BSEGS M'r (Z_to_bv 64 z) k).
    { intros z k Hz Hk F. apply rdn_munrestrict; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia.
      rewrite <- (Z_to_bv_bv_unsigned 64 x). apply F. exact Hx. }
    (* [comment removed for export] *)
    pose proof W as (_ & _ & _ & _ & _ & _ & (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12) & _).
    fold d in D1, D2, D3, D4, D5, D6, D7, D8, D9, D10, D11, D12. fold tot in D7, D9, D10. fold NIDS in D1, D2, D3, D4, D5, D6.
    assert (NN0 : 0 <= NIDS) by (first [clear - D4 | idtac]; (pose proof (D4 0 ltac:(lia)) as X0; lia)).
    set (std' := fupdZ (dp_stored d) q ((dp_stored d q + sz + 1) mod 2 ^ 32)).
    set (st' := op_depot_insert st b (U h) (dp_tab d b) (tot + 1) (tot + sz + 1) std' None None).
    assert (W' : WF bt st' Lc FF).
    { apply (OPS_WF_depot_insert_pf bt st Lc FF b (U h) (dp_tab d b) (tot + 1) (tot + sz + 1) std' None None W Hbix).
      - pose proof (u64_range h). lia.
      - lia.
      - intros i. (lazymatch goal with |- ?G => let G' := eval unfold std', fupdZ in G in change_no_check G' end). destruct (i =? q); [apply Z.mod_pos_bound; lia | exact (D11 i)].
      - reflexivity.
      - exact ROOM.
      - exact (depot_nids_room bt st Lc FF W ROOM KC DEP0).
      - fold d NIDS. split; [intros _; rewrite D6; exact CA | reflexivity].
      - fold d tot. (lazymatch goal with |- ?G => let G' := eval cbn [blk_opt length Z.of_nat] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold FRW in G in change_no_check G' end). lia.
      - fold d tot. (lazymatch goal with |- ?G => let G' := eval cbn [blk_opt] in G in change_no_check G' end). rewrite app_nil_r. rewrite D10. rewrite (max_blocks_nogrow tot sz T0 ltac:(lia) CI1 CI2). reflexivity.
      - fold d. (lazymatch goal with |- ?G => let G' := eval cbn [blk_opt] in G in change_no_check G' end). rewrite app_nil_r. exact D8.
      - intros p E. discriminate E.
      - intros p E. discriminate E.
      - intros p q0 E. discriminate E.
      - intros p b0 n0 E. discriminate E.
      - intros p b0 n0 E. discriminate E. }
    assert (EST : st' = depot_st st (a_dep st') []) by ((lazymatch goal with |- ?G => let G' := eval unfold st', op_depot_insert, depot_st in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [blk_opt store_aa List.map a_dep] in G in change_no_check G' end); reflexivity).
    assert (ETAB : DEPOT_TAB bt = 0x1f0098) by ((lazymatch goal with |- ?G => let G' := eval unfold DEPOT_TAB in G in change_no_check G' end); rewrite BT_ia; reflexivity).
    assert (ENID : DEPOT_NIDS bt = 0x1f0098 + 4194304) by ((lazymatch goal with |- ?G => let G' := eval unfold DEPOT_NIDS in G in change_no_check G' end); rewrite ETAB; reflexivity).
    assert (ESS : SSOBJ bt = 1966216) by ((lazymatch goal with |- ?G => let G' := eval unfold SSOBJ in G in change_no_check G' end); rewrite BT_ia; reflexivity).
    assert (ENA : node_addr bt (a_dep st') (NIDS + 1) = nda).
    { (lazymatch goal with |- ?G => let G' := eval unfold node_addr, st', op_depot_insert in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_dep dp_nodeblocks blk_opt] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold node_blocks in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [dp_nodeblocks] in G in change_no_check G' end). rewrite app_nil_r. reflexivity. }
    assert (ESB : store_blocks bt (a_dep st') = store_blocks bt d).
    { (lazymatch goal with |- ?G => let G' := eval unfold store_blocks, st', op_depot_insert in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_dep dp_storeblocks blk_opt] in G in change_no_check G' end). rewrite app_nil_r. reflexivity. }
    assert (ENB : node_blocks bt (a_dep st') = node_blocks bt d).
    { (lazymatch goal with |- ?G => let G' := eval unfold node_blocks, st', op_depot_insert in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_dep dp_nodeblocks blk_opt] in G in change_no_check G' end). rewrite app_nil_r. reflexivity. }
    (* [comment removed for export] *)
    assert (NWALL : forall z, (forall zz, Wall zz -> zz <> z) -> ~ Wall z) by (intros z F WZ; exact (F z WZ eq_refl)).
    assert (OUTW : forall z, AIMGLO <= z < AIMGHI -> ~ (0x1f0098 + 4 * b <= z < 0x1f0098 + 4 * b + 4) -> ~ (0x1f0098 + 4194304 <= z < 0x1f0098 + 4194304 + 4)
                     -> ~ (1966216 <= z < 1966216 + 8) -> ~ (1966216 + 16 * q + 24 <= z < 1966216 + 16 * q + 24 + 4) -> ~ Wall z).
    { intros z Hz N1 N2 N3 N4 WZ.
      assert (NDA_LO : 0x663000 <= nda) by ((lazymatch goal with |- ?G => let G' := eval unfold nda in G in change_no_check G' end); clear - GB1 M16; lia).
      destruct (CLS _ WZ) as [C|[C|[C|[C|[C|[C|C]]]]]]; [clear - C Hz SPC CR HKD; lia | exact (N1 C) | exact (N2 C) | clear - C Hz NDA_LO; lia | exact (N3 C) | exact (N4 C) | clear - C Hz GQ1 M20a; lia]. }
    assert (XIMG' : forall i, AIMGLO <= i < AIMGHI -> ~ X i /\ Hd (Z_to_bv 64 i) = false).
    { intros i Hi. split; [| apply NHs; lia]. intros Xi. apply (XIMG i Xi). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). lia. }
    assert (XND : forall i, nda <= i < nda + 16 -> ~ X i /\ Hd (Z_to_bv 64 i) = false).
    { intros i Hi. unfold nda in Hi. first [clear - Hi NHn M16 INB PXH W | idtac]; (split; [intros Xi; apply (px_off_nodes bt st Lc FF W X i blk PXH Xi INB); lia | apply NHn; lia]). }
    assert (RX' : RepX bt X st' Lc FF M' mdl1).
    { apply (RepX_mono bt (fun z => X z /\ ~ False) X); [intros z [Hz _]; exact Hz|].
      apply (repx_step bt X (fun _ => False) Wall Xdec_false st st' Lc Lc FF FF M M' mdl mdl1).
      - exists M0. split; [exact RP | exact DIFF].
      - intros a NE. apply (msum_changed Wall M M'); [(lazymatch goal with |- ?G => let G' := eval unfold Wall, ins_W in G in change_no_check G' end); repeat apply wun_dec; apply ivl_dec | split; [exact FR | exact GR] | exact NE].
      - intros a F. destruct F.
      - intros N0 N0' RPn Dn DIFF' EQX EQM.
        assert (CELLNEW : forall (z : Z) (k : nat) bs, 0 <= z -> z + Z.of_nat k < 2 ^ 64 -> (forall i, z <= i < z + Z.of_nat k -> ~ X i /\ Hd (Z_to_bv 64 i) = false) ->
                  rdn BSEGS M'r (Z_to_bv 64 z) k = Some bs -> rdn BSEGS N0' (Z_to_bv 64 z) k = Some bs).
        { intros z k bs Hz Hk F Hr. rewrite <- Hr, <- (VIS z k Hz Hk (fun i Hi => proj2 (F i Hi))). apply rdn_ext; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]|].
          intros x Hx. rewrite u_Z2bv in Hx by lia. apply EQX. left. exact (proj1 (F (U x) Hx)). }
        assert (CELLOLD : forall (z : Z) (k : nat) bs, 0 <= z -> z + Z.of_nat k < 2 ^ 64 -> (forall i, z <= i < z + Z.of_nat k -> ~ Wall i) ->
                  rdn BSEGS N0 (Z_to_bv 64 z) k = Some bs -> rdn BSEGS N0' (Z_to_bv 64 z) k = Some bs).
        { intros z k bs Hz Hk F Hr. rewrite <- Hr. apply rdn_ext; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia.
          destruct (decide (N0' x = N0 x)) as [E|NE]; [exact E|]. exfalso. destruct (DIFF' x NE) as [[WA|[]] _]. exact (F (U x) Hx WA). }
        pose proof RPn as (_ & _ & _ & _ & _ & _ & _ & _ & (Dtab & Dnids & Dmu & Dmap & Dnode & Dnw & Dfr & Dblk & Dsw) & _ & _ & _ & (_ & _ & _ & FAl & _) & _).
        fold d in Dtab, Dnids, Dmu, Dmap, Dnode, Dnw, Dfr, Dblk, Dsw.
        apply (OPS_REP_depot_insert_pf bt st Lc FF N0 N0' mdl mdl1 b (U h) (dp_tab d b) (tot + 1) (tot + sz + 1) std' None None W W' RPn Hbix).
        + intros p E. discriminate E.
        + intros p E. discriminate E.
        + intros p q0 E. discriminate E.
        + intros a NE. destruct (DIFF' a NE) as [[WA|[]] DF]. split; [| exact DF]. (lazymatch goal with |- ?G => let G' := eval unfold foot_depot_ins in G in change_no_check G' end). rewrite ETAB, ENID, ESS. fold st' d; fold NIDS; rewrite ENA, ESB.
          destruct (CLS _ WA) as [C|[C|[C|[C|[C|[C|C]]]]]].
          * do 7 right. lia.
          * left. exact C.
          * right; left. lia.
          * do 4 right; left. exact C.
          * do 3 right; left. lia.
          * do 3 right; left. lia.
          * do 5 right; left. exists blkd. split; [exact INQ | lia].
        + rewrite BT_segs, ETAB. first [clear - CELLNEW XIMG' Hbix Kb | idtac]; (apply CELLNEW; [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | intros i Hi; apply XIMG'; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hi; lia | exact Kb]).
        + rewrite BT_segs, ENID. apply CELLNEW; [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | intros i Hi; apply XIMG'; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hi; lia | exact Kn].
        + rewrite BT_segs, ENID. apply CELLOLD; [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | | rewrite ENID, BT_segs in Dmu; exact Dmu].
          intros i Hi. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hi. first [clear - Hi OUTW Q20 Hbix | idtac]; (apply OUTW; lia).
        + rewrite BT_segs. fold st' d; fold NIDS; rewrite ENA. (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite Z_to_bv_bv_unsigned.
          apply CELLNEW; [(lazymatch goal with |- ?G => let G' := eval unfold nda in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval unfold nda in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | intros i Hi; apply XND; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hi; lia | exact Kh].
        + rewrite BT_segs. fold st' d; fold NIDS; rewrite ENA. apply CELLNEW; [(lazymatch goal with |- ?G => let G' := eval unfold nda in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval unfold nda in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | intros i Hi; apply XND; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hi; lia | exact Kl].
        + rewrite BT_segs. fold st' d; fold NIDS; rewrite ENA. apply CELLNEW; [(lazymatch goal with |- ?G => let G' := eval unfold nda in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval unfold nda in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | intros i Hi; apply XND; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hi; lia | exact Ks].
        + intros p E. discriminate E.
        + rewrite BT_segs, ESS. apply CELLNEW; [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | intros i Hi; apply XIMG'; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hi; lia | exact Kt].
        + intros i Hi. fold st'. rewrite ESB. fold d. destruct (Dblk i Hi) as (C1 & C2 & C3). rewrite BT_segs, ESS in *.
          split; [| split].
          * apply CELLOLD; [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | | exact C1]. intros j Hj. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hj. first [clear - Hj Hi OUTW Hbix | idtac]; (apply OUTW; lia).
          * destruct (Z.eq_dec i q) as [->|NEq].
            -- (lazymatch goal with |- ?G => let G' := eval unfold std' in G in change_no_check G' end). rewrite fupdZ_same. replace (1966216 + 24 + 16 * q) with (1966216 + 16 * q + 24) by lia.
               first [clear - CELLNEW XIMG' Q20 Kso | idtac]; (apply CELLNEW; [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | intros j Hj; apply XIMG'; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hj; lia | exact Kso]).
            -- (lazymatch goal with |- ?G => let G' := eval unfold std' in G in change_no_check G' end). rewrite fupdZ_other by exact NEq. apply CELLOLD; [(first [clear - Hi | idtac]; lia) | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); (first [clear - Hi | idtac]; lia) | | exact C2]. intros j Hj. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hj. first [clear - Hj NEq Hi OUTW Hbix | idtac]; (apply OUTW; lia).
          * apply CELLOLD; [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | | exact C3]. intros j Hj. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hj. first [clear - Hj Hi OUTW Hbix | idtac]; (apply OUTW; lia).
        + intros q0 E. discriminate E.
        + (lazymatch goal with |- ?G => let G' := eval cbn [blk_opt List.map app] in G in change_no_check G' end). rewrite Evm. apply Permutation_refl.
        + rewrite Evm. reflexivity.
        + intros a. rewrite Elz. split; [intros H; left; exact H | intros [H | (q0 & E & _)]; [exact H | discriminate E]].
        + rewrite Elz. exact FAl.
        + rewrite Evm. reflexivity.
        + rewrite Evm. reflexivity.
        + rewrite Evm. reflexivity.
        + rewrite Evm. reflexivity.
        + rewrite Evm. reflexivity.
        + rewrite Evm. reflexivity.
        + (lazymatch goal with |- ?G => let G' := eval cbn [store_aa blk_opt List.map] in G in change_no_check G' end). rewrite app_nil_r. exact MI1.
        + rewrite Eeg. (lazymatch goal with |- ?G => let G' := eval cbn [blk_opt length Z.of_nat] in G in change_no_check G' end). lia. }
    (* [comment removed for export] *)
    assert (CHG : forall a : word, M' a <> M a -> Wall (U a) /\ M' a <> None).
    { intros a NE. apply (msum_changed Wall M M'); [(lazymatch goal with |- ?G => let G' := eval unfold Wall, ins_W in G in change_no_check G' end); repeat apply wun_dec; apply ivl_dec | split; [exact FR | exact GR] | exact NE]. }
    apply katD_refl. exists fx, st', M', mdl1, r', (NIDS + 1).
    split; [reflexivity|]. split; [exact HFX|]. split; [exists (a_dep st'), []; exact EST|]. split; [exact W'|]. split; [exact RX'|].
    split.
    { intros a Xa OUT. apply FR. intros WA. destruct (Z_lt_le_dec (U a) (U sp - 224)) as [L|L]; [exact (XW _ WA L Xa)|].
      first [clear - L WA OUT CLS Q20 Hbix M16 M20b GQ2 GB2 CR SPC HKD | idtac]; (destruct (CLS _ WA) as [C|[C|[C|[C|[C|[C|C]]]]]]; unfold nda in *; lia). }
    split.
    { intros a NE. destruct (CHG a NE) as [WA DF]. split; [| exact DF]. (lazymatch goal with |- ?G => let G' := eval unfold depot_foot, foot_depot_static in G in change_no_check G' end). rewrite ETAB, ENID, ESS, ENB, ESB.
      destruct (CLS _ WA) as [C|[C|[C|[C|[C|[C|C]]]]]].
      - do 3 right. lia.
      - left. left. lia.
      - left. left. lia.
      - right; left. exists blk. split; [exact INB | unfold nda in C; lia].
      - left. do 3 right; left. lia.
      - left. do 4 right. lia.
      - right; right; left. exists blkd. split; [exact INQ | lia]. }
    split.
    { intros a NE. destruct (CHG a NE) as [WA DF]. destruct DOBL as (_ & DO2 & DO3).
      assert (IP : forall z, 0x1a0061 <= z < 0x630810 -> in_wins (ia_priv (bt_ia bt)) z).
      { intros z Hz. rewrite BT_ia. exists 0x1a0061, 0x630810. split; [(lazymatch goal with |- ?G => let G' := eval cbn [ia_priv both_addrs In] in G in change_no_check G' end); do 6 right; left; reflexivity | exact Hz]. }
      destruct (CLS _ WA) as [C|[C|[C|[C|[C|[C|C]]]]]].
      - left. lia.
      - right; right. apply IP. lia.
      - right; right. apply IP. lia.
      - right; left. apply (DO2 st Lc FF blk (U a) W INB). unfold nda in C. lia.
      - right; right. apply IP. lia.
      - right; right. apply IP. lia.
      - right; left. apply (DO3 st Lc FF blkd (U a) W INQ). lia. }
    split.
    { intros z Hz. unfold as_callee_saved in Hz. cbn [In] in Hz.
      destruct Hz as [<-|Hz]; [transitivity sp; [exact G2 | symmetry; exact E2]|].
      assert (KEEP : forall k, ~ In (Z_to_bv 5 k) put_clob -> ~ In (Z_to_bv 5 k) sd_clobx -> getr r' (Z_to_bv 5 k) = getr R (Z_to_bv 5 k)).
      { intros k N1 N2. rewrite (AGi _ N1). exact (AGp _ N2). }
      repeat (destruct Hz as [<-|Hz]; [first [apply GS; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])] | apply KEEP; [(lazymatch goal with |- ?G => let G' := eval unfold put_clob in G in change_no_check G' end); nin5 | (lazymatch goal with |- ?G => let G' := eval unfold sd_clobx in G in change_no_check G' end); nin5]]|]).
      destruct Hz. }
    split; [exact G10|]. split; [lia|].
    split; [exact (same_but_materialized_except_vm mdl mdl1 SBM1)|].
    split; [intros a; first [left | intros _; left]; (lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end); rewrite Elz; reflexivity|].   (* [comment removed for export] *)
    split; [rewrite Ehl; exact HH | exact (model_ivs_wf_sbm mdl mdl1 SBM1 MW)].
  Qed.
End TOP3.
