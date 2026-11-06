(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require SpinAlg Ledger Hull Restrict Refund Lazyiq4 Fixej5z EvtAcct Divembc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Refund.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.SpinAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Ledger OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Hull OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Restrict OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Refund OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Lazyiq4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Fixej5z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.EvtAcct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Divembc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Refund.Madv3tp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts ARtSscs ARtSrgm AMallocI AMalmys.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMaly5g.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMaly5g ATransp ATranspH.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeB1 AFreeB2 AFreeB3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AQWf ABudget ACover ASecImg AFreeT AFreeH AFreeH0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt4chi.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeWDc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeS AFreeWD AFreeWDc AFreeB5 AFreeB6 ANodijx APgGeo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeS.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ANod9v0 AFreeX1 AFreeX2 AFreeX3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeGD0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeGD0 ACoresk.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSrgm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMaly5g.AMal5j7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMaly5g OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ATranspH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQWf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ABudget OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ACover OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecImg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeT OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt4chi.AFreePB OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeWDc.AFreePc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeS OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeWD OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeWDc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ANodijx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APgGeo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeS.ARtSxaw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ANod9v0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeX1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeX2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeX3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeGD0.AFreeX4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeGD0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ACoresk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import AInvWfp.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac hot2_mid := match goal with H : context [Z.modulo _ _] |- _ => idtac | H : context [Z.div _ _] |- _ => idtac end;
  (repeat match goal with H : context [Z.modulo _ _] |- _ => clear H | H : context [Z.div _ _] |- _ => clear H end); Zify.zify; xlia zchecker.
Local Ltac lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dl_first | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Zify.zify; xlia zchecker | hot2_mid | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
#[local] Notation WF := (WF AL_pboth).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Notation wz z := (Z_to_bv 64 z) (only parsing).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kHighShadowMapSize, kSpaceReserve, kMaxSize, kLowShadowMapBeg, kLowShadowBeg, kShadowGapBeg,
                        kPtrArrayReserve, kChunksBlockCount, kFakeStackBytes, kPageSize, kSecondaryHeaderSize, kMaxPrimaryUser,
                        kQuarantineMaxSize, kQuarantineCacheSize, kQuarantineBatchBytes in *.
Ltac splits := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac sidetac K := cbn [disjoint_from cells_size csize Nat.add Nat.mul length a8_frames unmap_frame app]; rewrite ?upd_length, ?repeat_length;
  clear - K; decompose [and] K; unfold apart, AMallocA.apart, IAB in *; kung_all; lia.
Ltac hop3 H MA KA MB KB MC KC :=
  eapply rw_cells_mu; [eapply rw_cells_mu; [eapply rw_cells_mu; [exact H| exact MA| sidetac KA]| exact MB| sidetac KB]| exact MC| sidetac KC].
Ltac nexc := let X := fresh "X" in let Xe := fresh "Xe" in intros X; unfold AFreeX3.EXC, ia_blk in X;
  destruct X as [X|[X|[X|[X|[X|[X|[[Xe X]|[X|[X|[X|[X|[X|[X|[X|X]]]]]]]]]]]]]]; kung_all; first [lia | congruence].

(* [comment removed for export] *)
Lemma bytes_zero_raw : forall (m : mem) a n, bytes_at rsegs m a (repeat (Z_to_bv 8 0) n) -> 0x60a000 <= a ->
  forall k, 0 <= k < Z.of_nat n -> m (wz (a + k)) = Some (Z_to_bv 8 0).
Proof.
  (intros m a n; (first [ intro dR_37; dand3 dR_37 as B0 B1 B | intros (B0 & B1 & B) ]); intros Ha k Hk). rewrite repeat_length in B1.
  specialize (B (Z.to_nat k) ltac:(rewrite repeat_length; lia)). rewrite Z2Nat.id in B by lia.
  rewrite (nth_error_repeat (Z_to_bv 8 0)) in B by lia. unfold mrd, wa in B.
  destruct (m (wz (a + k))) as [b'|] eqn:E; try rewrite E in B; [congruence|].
  exfalso. pose proof (pa_seg_rom_none (wz (a + k)) ltac:(rewrite unsigned_lit by lia; right; lia)) as X.
  assert (Y : Some (Z_to_bv 8 0) = None) by (rewrite <- B; exact X). discriminate Y.
Qed.

Section FreeDirectCoreG.
Context {Clg : Ceiling}.
  Variables (rac spd gp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AState) (p n0 stkobj lo hi : Z) (key : list Z) (T : TSet).
  (* [comment removed for export] *)
  Hypothesis AI : @pa_ainv _ DepotRepL A m md.
  Hypothesis MI : mem_inv rsegs (aview_of (pa_hull A) m).
  Hypothesis HL : as_live A p = Some n0.
  Hypothesis IAT : a_ia_inited A = true.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LOW : lo <= bv_unsigned spd - 4096.
  Hypothesis SPHI : bv_unsigned spd <= hi.
  Hypothesis HISP : hi <= 2^47.
  Hypothesis SPA : bv_unsigned spd mod 16 = 0.
  Hypothesis RA2 : bv_unsigned rac mod 2 = 0.
  Hypothesis ST : stk rsegs (aview_of (pa_hull A) m) lo (bv_unsigned spd).
  Hypothesis SMH : mapped (aview_of (pa_hull A) m) (bv_unsigned spd) (hi - bv_unsigned spd).
  Hypothesis STLO : bv_unsigned spd <= stkobj.
  Hypothesis STHI : stkobj + 2064 <= hi.
  Hypothesis STO : ro_cells rsegs (aview_of (pa_hull A) m) stkobj [C8 (wz (stkobj + 16)); C8 (wz (Z.of_nat (length key)))].
  Hypothesis TRW : bytes_at rsegs (aview_of (pa_hull A) m) (stkobj + 16) (u64s (map (Z_to_bv 64) key)).
  Hypothesis KEYU : In key (p_dkeys (a_pl A)).
  Hypothesis KR : Forall (fun w => 0 <= w < 2^64) key.
  Hypothesis NQB : kQuarantineMaxSize < n0.
  (* [comment removed for export] *)
  Hypothesis KK : forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AState) (m' : mem) (md' : Model),
          let v' := aview_of (pa_hull A') m' in
          @pa_ainv _ DepotRepL A' m' md' -> mem_inv (cl_segs LPA) v' -> amd_frame md md' ->
          (forall ff, as_fframe A' ff = as_fframe A ff) ->
          a_pl A' = a_pl A ->
          as_live A' p = None -> (forall q, q <> p -> as_live A' q = as_live A q) ->
          as_livebytes A' = as_livebytes A - n0 -> as_tinycred A' = as_tinycred A -> as_seccred A' = as_seccred A -> as_primcred A' = as_primcred A (* [comment removed for export] *) ->
          as_nlive A' = as_nlive A - (if Z.eqb p 0 then 0 else 1) ->
          (forall c, c <> kQuarantineBatchClass -> a_virgin A c -> a_virgin A' c) ->
          (forall i, 0 <= i < 4 -> mrd (cl_segs LPA) v' (wz (cl_errno LPA + i)) = mrd (cl_segs LPA) (aview_of (pa_hull A) m) (wz (cl_errno LPA + i))) ->
          frame_ok LPA (pa_owned A) (pa_owned A') hi (hi - lo) (newblk p n0) nowhere (aview_of (pa_hull A) m) v' ->
          (forall a, bv_unsigned spd <= a < hi -> v' (wz a) = aview_of (pa_hull A) m (wz a)) ->
          stk (cl_segs LPA) v' lo (bv_unsigned spd) ->
          srealizes (cl_segs LPA) (mkCfg (MS (mkR rac spd gp (cl_tp LPA) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc rac) fc None m' (seg_rom (cl_segs LPA))) md') T.

  #[warnings="-notation-for-abbreviation"] Local Notation v := (aview_of (pa_hull A) m).
  #[warnings="-notation-for-abbreviation"] Local Notation P := (a_pl A).
  #[warnings="-notation-for-abbreviation"] Local Notation chunks := (sr_chunks (a_sec A)).
  #[warnings="-notation-for-abbreviation"] Local Notation nch := (Z.of_nat (length (sr_chunks (a_sec A)))).
  #[warnings="-notation-for-abbreviation"] Local Notation h := (p - 6144).
  #[warnings="-notation-for-abbreviation"] Local Notation msz := (map_size n0).
  #[warnings="-notation-for-abbreviation"] Local Notation sb := (a_sb A).
  #[warnings="-notation-for-abbreviation"] Local Notation pa := (p_pa (a_pl A)).
  #[warnings="-notation-for-abbreviation"] Local Notation thr := (p_thr (a_pl A)).
  #[warnings="-notation-for-abbreviation"] Local Notation pbeg := (a8_pbeg (p - 6144)).
  #[warnings="-notation-for-abbreviation"] Local Notation pend := (a8_pend (p - 6144) (map_size n0)).
  #[warnings="-notation-for-abbreviation"] Local Notation len := (a8_pend (p - 6144) (map_size n0) - a8_pbeg (p - 6144)).
  #[warnings="-notation-for-abbreviation"] Local Notation hla := (cs_map (sec_last A)).
  #[warnings="-notation-for-abbreviation"] Local Notation uspd := (bv_unsigned spd).

  Let NQ' : kMaxPrimaryUser < n0. Proof. unfold kQuarantineMaxSize, kMaxPrimaryUser in *. lia. Qed.

  (* [comment removed for export] *)
  #[using="SPHI rac"] Lemma frame_ok_widen : forall (ow ow' vic nb : Z -> Prop) (w w' : mem),
    frame_ok LPA ow ow' uspd (uspd - lo) vic nb w w' ->
    (forall a, uspd <= a < hi -> w' (wz a) = w (wz a)) -> mapped w uspd (hi - uspd) ->
    frame_ok LPA ow ow' hi (hi - lo) vic nb w w'.
  Proof.
    (intros ow ow' vic nb w w'; (first [ intro dR_38; dand7 dR_38 as F1 F2 F3 F4 F5 F6 F7 | intros (F1 & F2 & F3 & F4 & F5 & F6 & F7) ]); intros AGH MH). unfold frame_ok.
    replace (uspd - (uspd - lo)) with lo in * by lia. replace (hi - (hi - lo)) with lo by lia.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try assumption.
    - intros a Ha NO NO' NW. apply (F1 a Ha NO NO'). clear -NW SPHI. lia.
    - intros k Hk. destruct (Z.lt_ge_cases (lo + k) uspd) as [B|B].
      + apply F3. lia.
      + rewrite (AGH (lo + k)) by lia. replace (lo + k) with (uspd + (lo + k - uspd)) by lia. apply MH. lia.
  Qed.

  (* [comment removed for export] *)
  Definition S1_post (usp lo : Z) (i : nat) (nf ca gA gM rf rfd mu mdv : Z) (m7 : mem) : machine_state -> Prop := fun ms' =>
    exists (t0'' t1'' t2'' a3'' a4'' a5'' a6'' t3'' t4'' t5'' t6'' : word) (scr : list byte) (m' : mem),
    ms' = MSsvc (mkR (wz unmap_resume) (wz (usp + -48)) gp (cl_tp LPA) t0'' t1'' t2'' (wz msz) (wz 0)
                     (wz h) (wz msz) (wz 0) a3'' a4'' a5'' a6'' (wz 215)
                     (wz h) s3 s4 s5 (wz (2^20)) s7 s8 s9 s10 s11 t3'' t4'' t5'' t6'')
                F (wz munmap_ecall_pc) (wz 215) fc None m' (seg_rom rsegs)
    /\ rw_cells rsegs m' (usp + -48) (unmap_frame scr s2 (wz (thr + 80)) (wz QINST) (wz qput_recret))
    /\ rw_cells rsegs m' 0xb15d0 [C8 (wz (nch - 1)); C1 (Z_to_bv 8 0)]
    /\ rw_cells rsegs m' 0xb15e8 [C8 (wz (nf + 1)); C8 (wz (ca - msz))]
    /\ rw_cells rsegs m' 0xb1800 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C2 (wz 0)]
    /\ rw_cells rsegs m' 0xb1818 [C8 (wz (gA - msz)); C8 (wz (gM - msz))]
    /\ u64arr rsegs m' pa (upd (sec_words A) (Z.to_nat (Z.of_nat i)) (wz hla))
    /\ rw_cells rsegs m' h [C8 (wz h); C8 (wz msz); C8 (wz (needed_size2 n0)); C8 (wz (Z.of_nat i))]
    /\ (hla = h \/ rw_cells rsegs m' hla [C8 (wz hla); C8 (wz (map_size (cs_n (sec_last A)))); C8 (wz (needed_size2 (cs_n (sec_last A)))); C8 (wz (Z.of_nat i))])
    /\ rw_cells rsegs m' (thr + 2840) [C8 (wz (rf + 1)); C8 (wz (rfd + n0))]
    /\ rw_cells rsegs m' (thr + 2888) [C8 (wz (mu + 1)); C8 (wz (mdv + msz))]
    /\ munch [(usp - 112, usp); (thr + 2888, thr + 2904)] m7 m' /\ wmono rsegs m7 m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (usp + -48).

  #[using="NQ' KK NQB KR KEYU TRW STO STHI STLO SMH ST RA2 SPA HISP SPHI LOW CEIL IAT HL MI AI key hi lo n0 A Clg"] Theorem dealloc_directG :
    srealizes (cl_segs LPA) (mkCfg (dealloc_entry_ms rac spd gp (cl_tp LPA) t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p stkobj) md) T.
  Proof.
    unfold dealloc_entry_ms. cbn [cl_segs cl_free_pc LPA] in MI, KK |- *.
    pose proof (ai_wf _ _ _ _ _ _ _ AI) as WF0.
    pose proof (conj (ai_wf _ _ _ _ _ _ _ AI) (ai_repr _ _ _ _ _ _ _ AI) : WF A /\ @arepr _ DepotRepL LPA AL_pboth [] A v) as AR.
    pose proof alloc_ceiling_val as CE.
    pose proof (place_facts A WF0) as PFx. cbv zeta in PFx.
    (first [ dand14 PFx as _ _ _ _ _ _ _ _ _ _ _ _ (Psp0 & _) _ | destruct PFx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Psp0 & _) & _) ]).
    assert (SPH : uspd <= 2^47) by (clear -SPHI HISP; lia).
    pose proof (zr_word spd) as SPR; unfold inr64 in SPR. pose proof (zr_word rac) as RAR; unfold inr64 in RAR.
    destruct (free_n0 A m md p n0 AI HL) as [NR US]. unfold REQ_MAX in NR.
    (first [ pose proof ((free_geom A m md p n0 AI HL)) as dR_2; dand4 dR_2 as PAL PLO PCE PHI | destruct (free_geom A m md p n0 AI HL) as (PAL & PLO & PCE & PHI) ]).
    (first [ pose proof ((free_HDR A m md p n0 AI HL)) as dR_3; dex2 dR_3 as b1 ido; dand6 dR_3 as B1R B1M3 B1M IDR HDR CTXID | pose proof ((free_HDR A m md p n0 AI HL)) as dR_3; dand8 dR_3 as b1 ido B1R B1M3 B1M IDR HDR CTXID | destruct (free_HDR A m md p n0 AI HL) as (b1 & ido & B1R & B1M3 & B1M & IDR & HDR & CTXID) ]).
    destruct (free_CTX0 A m md p n0 AI HL) as (old & CTX0).
    pose proof (free_FCo A m md AI) as FCo.
    (first [ pose proof ((free_TST A m md AI)) as dR_4; dex2 dR_4 as fr fd; dand3 dR_4 as FRR FDR TST | pose proof ((free_TST A m md AI)) as dR_4; dand5 dR_4 as fr fd FRR FDR TST | destruct (free_TST A m md AI) as (fr & fd & FRR & FDR & TST) ]).
    pose proof (free_sep A m md p n0 AI HL) as SEPp. cbv zeta in SEPp. (first [ dand4 SEPp as SEP_pc SEP_pt SEP_pn SEP_pf | destruct SEPp as (SEP_pc & SEP_pt & SEP_pn & SEP_pf) ]).
    (first [ pose proof ((hit_sep A m md AI)) as dR_6; dand13 dR_6 as SEP_thr SEP_ctx SEP_tc SEP_n0 SEP_f0 SEP_n0t SEP_f0t SEP_n0c SEP_f0c DN01 DN02 DF01 DF02 | pose proof (hit_sep A m md AI) as (SEP_thr & SEP_ctx & SEP_tc & SEP_n0 & SEP_f0 & SEP_n0t & SEP_f0t & SEP_n0c & SEP_f0c & DN01 & DN02 & DF01 & DF02) ]).
    (first [ pose proof ((hit_place A m md AI)) as dR_7; dand7 dR_7 as TH1 TH2 THRA CT1 CT2 TOPR BOTR | pose proof (hit_place A m md AI) as (TH1 & TH2 & THRA & CT1 & CT2 & TOPR & BOTR) ]).
    (first [ pose proof ((hit_depot_wf A m md AI)) as dR_8; dand5 dR_8 as DND DLEN _ DKEY _ | pose proof (hit_depot_wf A m md AI) as (DND & DLEN & _ & DKEY & _) ]).
    pose proof (hit_DR A m md AI) as DR0. pose proof (hit_TC A m md AI) as TC. pose proof (hit_tsd A m md AI) as [TSD1 TSD2].
    assert (TSDL : 0x5e7b28 <= pa_tsd /\ pa_tsd + 8 <= 0x60a000) by (unfold pa_tsd; lia).
    assert (LO : alloc_ceiling <= lo /\ lo <= uspd - 704) by (clear -CEIL LOW; lia).
    (* [comment removed for export] *)
    assert (KL : (1 <= length key <= 255)%nat /\ depot_total (a_depot A) + 256 < kStackStoreBlockFrames).
    { (first [ pose proof ((wfD A WF0)) as dR_9; dand3 dR_9 as INC ND NN | destruct (wfD A WF0) as (INC & ND & NN) ]). pose proof (wfP A WF0) as PL. pose proof (wf_place_dkeys _ _ PL) as DK.
      (first [ dand3 DK as DK1 DK2 DK3 | destruct DK as (DK1 & DK2 & DK3) ]). clear PL.
      assert (INC' : incl (a_depot A) (p_dkeys (a_pl A))) by (intros k Hk; exact (proj1 (Forall_forall _ _) INC k Hk)).
      (first [ pose proof ((depot_universe_bounds _ _ DK1 DK3 ND INC')) as dR_11; dand3 dR_11 as L1 _ L3 | pose proof (depot_universe_bounds _ _ DK1 DK3 ND INC') as (L1 & _ & L3) ]).
      split; [exact (proj1 (Forall_forall _ _) DK1 key KEYU)| unfold kStackStoreBlockFrames; clear -L1 L3; lia]. }
    destruct KL as [KL DTOT].
    assert (STOR : uspd <= stkobj /\ stkobj + 2064 <= 2^47) by (clear -STLO STHI HISP; lia).
    assert (TPE : cl_tp LPA = wz TP) by reflexivity.
    pose proof (Z_div_mod_eq_full (n0 + 7) 8) as NDE. pose proof (Z.mod_pos_bound (n0 + 7) 8 ltac:(lia)) as ER.
    assert (R8 : 8 * ((n0 + 7) / 8) - 8 < n0 <= 8 * ((n0 + 7) / 8)) by lia.
    assert (NQB' : 2^28 < n0) by (clear -NQB; unfold kQuarantineMaxSize in NQB; exact NQB).
    assert (NR' : 1 <= n0 < 2^32) by (clear -NR; lia).
    (* [comment removed for export] *)
    destruct (sk_idx A m md p n0 AI HL NQ') as [i NTH].
    (first [ pose proof ((sk_geo A m md p n0 AI HL NQ')) as dR_12; dand11 dR_12 as HLO HAL MSZ MSZAL HHI PH PIN N6 _ H5 PM | pose proof (sk_geo A m md p n0 AI HL NQ') as (HLO & HAL & MSZ & MSZAL & HHI & PH & PIN & N6 & _ & H5 & PM) ]).
    (first [ pose proof ((sk_shr A m md p n0 AI HL NQ')) as dR_13; dand4 dR_13 as SHA M512 D512 SIDE | pose proof (sk_shr A m md p n0 AI HL NQ') as (SHA & M512 & D512 & SIDE) ]).
    (first [ pose proof ((sk_sb A m md p n0 AI HL NQ')) as dR_14; dand4 dR_14 as SBL SBH HSB POUT | pose proof (sk_sb A m md p n0 AI HL NQ') as (SBL & SBH & HSB & POUT) ]).
    (first [ pose proof ((sk_nch A m md p n0 AI HL NQ')) as dR_15; dand4 dR_15 as NRC NLE NRES NEC | pose proof (sk_nch A m md p n0 AI HL NQ') as (NRC & NLE & NRES & NEC) ]).
    (first [ pose proof ((sk_pa A m md p n0 AI HL NQ')) as dR_16; dand5 dR_16 as PALO PAHI PAAL PARES PALE | pose proof (sk_pa A m md p n0 AI HL NQ') as (PALO & PAHI & PAAL & PARES & PALE) ]).
    pose proof (sk_arr A m md p n0 AI HL NQ') as ARR.
    pose proof (sk_nearest A m md p n0 AI HL NQ') as NRST.
    (first [ pose proof ((sk_last A m md p n0 AI HL NQ')) as dR_17; dand4 dR_17 as EL INL ELw HLU | pose proof (sk_last A m md p n0 AI HL NQ') as (EL & INL & ELw & HLU) ]).
    (first [ pose proof ((sk_regs A m md AI)) as dR_18; dex5 dR_18 as srt nf ca gA gM; dand9 dR_18 as SRTR NFR CAR GAR GMR NSRT NFCA LCK GAM | pose proof ((sk_regs A m md AI)) as dR_18; dand14 dR_18 as srt nf ca gA gM SRTR NFR CAR GAR GMR NSRT NFCA LCK GAM | destruct (sk_regs A m md AI) as (srt & nf & ca & gA & gM & SRTR & NFR & CAR & GAR & GMR & NSRT & NFCA & LCK & GAM) ]).
    (first [ pose proof ((sk_consts A m md AI)) as dR_19; dand4 dR_19 as CLMA CSEAL CSB CGCF | pose proof (sk_consts A m md AI) as (CLMA & CSEAL & CSB & CGCF) ]).
    destruct (sk_a8 A m md AI) as [canary A8C].
    (first [ pose proof ((sk_thr_stats A m md AI)) as dR_20; dex4 dR_20 as rf rfd mu mdv; dand6 dR_20 as RFR RFDR MUR MDR TRF TMU | pose proof ((sk_thr_stats A m md AI)) as dR_20; dand10 dR_20 as rf rfd mu mdv RFR RFDR MUR MDR TRF TMU | destruct (sk_thr_stats A m md AI) as (rf & rfd & mu & mdv & RFR & RFDR & MUR & MDR & TRF & TMU) ]).
    (first [ pose proof ((sk_shadow A m md p n0 AI HL NQ')) as dR_21; dand3 dR_21 as SHB SHL SHC | pose proof (sk_shadow A m md p n0 AI HL NQ') as (SHB & SHL & SHC) ]).
    pose proof (sk_i A p n0 i NTH) as [IR NTHw].
    pose proof (sk_hdr A m md p n0 AI HL NQ' i NTH) as [HDRL CSR].
    (first [ pose proof ((sk_sep_h A m md p n0 AI HL NQ' i NTH)) as dR_22; dand5 dR_22 as SEP_hp SEP_ht SEP_hc SEP_hn SEP_hf | pose proof (sk_sep_h A m md p n0 AI HL NQ' i NTH) as (SEP_hp & SEP_ht & SEP_hc & SEP_hn & SEP_hf) ]).
    (first [ pose proof ((sk_sep_pa A m md AI)) as dR_23; dand5 dR_23 as SEP_At SEP_Ac SEP_An SEP_Af _ | pose proof (sk_sep_pa A m md AI) as (SEP_At & SEP_Ac & SEP_An & SEP_Af & _) ]).
    pose proof (sk_hl A m md p n0 AI HL NQ' i NTH) as HLX. cbv zeta in HLX. (first [ dand11 HLX as HLLO HLHI HLAL HLE HLA HLC SEP_lp SEP_lt SEP_lc SEP_ln SEP_lf | destruct HLX as (HLLO & HLHI & HLAL & HLE & HLA & HLC & SEP_lp & SEP_lt & SEP_lc & SEP_ln & SEP_lf) ]).
    (first [ pose proof ((a8_geo A m md p n0 AI HL NQB)) as dR_25; dand15 dR_25 as G1 G2 G3 G4 G5 G6 G7 G8 GM1 GM2 GM3 GM4 _ BIG _ | pose proof (a8_geo A m md p n0 AI HL NQB) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GM1 & GM2 & GM3 & GM4 & _ & BIG & _) ]).
    pose proof (sec_words_length A) as NCH.
    assert (PNB : 0x60a000 <= p + -16) by (clear -H5; lia).
    assert (SHR : 0x7fff8200 <= sh h /\ sh h + msz / 8 <= kHighMemBeg) by (clear -SIDE; kung_all; lia).
    assert (SEP_at : apart pa (8 * nch) thr 4096) by (clear -SEP_At PALE; unfold apart in *; lia).
    assert (SEP_ac : apart pa (8 * nch) (p_ctx P) 0x10000) by (clear -SEP_Ac PALE; unfold apart in *; lia).
    assert (SEP_an : apart pa (8 * nch) (p_nodes0 P) kDepotNodesBlock) by (clear -SEP_An PALE; unfold apart in *; lia).
    assert (SEP_af : apart pa (8 * nch) (p_frames0 P) kStackStoreBlockBytes) by (clear -SEP_Af PALE; unfold apart in *; lia).
    assert (NTL : nth_error (sec_words A) (Z.to_nat (nch - 1)) = Some (wz hla)) by (exact (sec_words_nth A _ _ EL)).
    assert (SEALR : 1 <> 0 /\ 0 <= 1 < 2^64) by lia.
    rewrite <- NCH in PALO, PAHI, NRC, IR, NTL, SEP_hp, SEP_lp, SEP_at, SEP_ac, SEP_an, SEP_af, NSRT, HLC.
    (* [comment removed for export] *)
    pose proof (free_directS0c rac spd gp (cl_tp LPA) t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc v
                  lo p n0 b1 pa_tsd (p_ctx P) thr ((n0 + 7) / 8) (p_nodes0 P) (p_frames0 P) fr fd stkobj (a_depot A) key old
                  sb pa 0 0 srt h msz (needed_size2 n0) (Z.of_nat i) nf ca gA gM rf rfd mu mdv 1 (sec_words A)
                  (wz hla) (wz hla) (wz (map_size (cs_n (sec_last A)))) (wz (needed_size2 (cs_n (sec_last A)))) (sshadow_live n0)
                  MI ST LO SPA SPH RA2 TPE PAL PLO PNB NR' NQB' R8 B1R B1M3 HDR CTX0 (conj SBL SBH) POUT CSB FCo (hit_PCo A m md AI)
                  TC (hit_TH0 A m md AI) (hit_CT8 A m md AI) TSDL (hit_TDT A m md AI) TST FRR FDR TRF TMU RFR RFDR
                  DR0 DND DLEN DTOT (conj DN01 DN02) (conj DF01 DF02) STO TRW STOR KL KR
                  PALO PAHI PAAL NRC ltac:(lia) ltac:(lia) SRTR IR NTHw NTL ltac:(rewrite HLU; exact HLLO) ltac:(rewrite HLU; exact HLHI) ltac:(rewrite HLU; exact HLAL)
                  NFR CAR GAR GMR CSR HLO HAL MSZ MSZAL HHI HSB PH PIN BIG SHR NRST SEALR SEP_hp ltac:(rewrite HLU; exact SEP_lp) SEP_ht SEP_hn SEP_hf SEP_at SEP_ac SEP_an SEP_af
                  ltac:(rewrite HLU; exact SEP_lt) ltac:(rewrite HLU; exact SEP_lc) ltac:(rewrite HLU; exact SEP_ln) ltac:(rewrite HLU; exact SEP_lf) ltac:(rewrite HLU; exact HLA)
                  SEP_pc SEP_pt SEP_pn SEP_pf SEP_n0t SEP_f0t SEP_n0c SEP_f0c SEP_tc CLMA CSEAL NSRT NFCA LCK GAM ARR HDRL ltac:(rewrite HLU; exact HLC) SHC) as EV0.
    idtac "S0 walk ok".
    (* [comment removed for export] *)
    destruct (asI_minv A m md AI) as [HMI HH].
    pose proof (MInv_perm _ _ _ _ _ _ (hull_perm0 A m md p n0 i AI HL NQB NTH) (lhull_perm0 A m md p n0 i AI HL NQB NTH) HMI) as HMI0.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (CR0 : hull_cover (REST A i) (LREST A i) (m_vm_lazy md) /\ lazy_free (m_vm_lazy md) h (h + msz)).
    { pose proof (ai_ledger _ _ _ _ _ _ _ AI) as (_ & _ & _ & _ & _ & L6 & _ & _ & Z9). split.
      - apply (cover_REST A m md p n0 i AI HL NQB NTH md Z9). apply Forall_forall. intros sc Hsc. apply (proj1 (Forall_forall _ _) L6). exact (in_firstn_skipn_S _ _ _ Hsc).
      - pose proof (proj1 (Forall_forall _ _) L6 (CS h n0) (sk_In A m md p n0 AI HL NQ')) as EM. cbn [cs_map cs_n] in EM.
        (first [ pose proof ((sk_geo A m md p n0 AI HL NQ')) as dR; dand5 dR as HLO' HAL' MSZ' MSZAL' _ | pose proof (sk_geo A m md p n0 AI HL NQ') as (HLO' & HAL' & MSZ' & MSZAL' & _) ]).
        pose proof alloc_ceiling_val as CE'. pose proof (lazy_free_of_eager_map _ _ md EM) as LF. rewrite !unsigned_lit in LF by lia. exact LF. }
    pose proof (hidc_H0p A m md p n0 i AI HL NQB NTH) as HD0.
    pose proof (off_segments_H A p n0 i (H0p A p n0 i) ltac:(right; right; right; apply Permutation_refl)) as OFF0.
    pose proof (off_segments_H A p n0 i (H1 A p n0 i) ltac:(right; left; apply Permutation_refl)) as OFF1.
    pose proof (off_segments_H A p n0 i (H2 A p n0 i) ltac:(right; right; left; apply Permutation_refl)) as OFF2.
    (first [ pose proof ((len_facts A m md p n0 AI HL NQB)) as dR_26; dand17 dR_26 as F1 F2 F3 F4 F5 F6 U1 U2 U3 U4 _ _ MP _ _ PL PMZ | pose proof (len_facts A m md p n0 AI HL NQB) as (F1 & F2 & F3 & F4 & F5 & F6 & U1 & U2 & U3 & U4 & _ & _ & MP & _ & _ & PL & PMZ) ]).
    eapply (srz_evt_restrict rsegs (H0p A p n0 i) OFF0 pa_wx _ (pa_eager A) _ _ md T HMI0 HH).
    { rewrite restrict_MS, <- HD0. exact EV0. }
    clear EV0. intros msr0 md1 Q0 HI1 SB1 Hcl0.
    (first [ dex11 Q0 as xt0 xt1 xt2 xa4 xa5 xa6 xt3 xt4 xt5 xt6 mv0'; dand21 Q0 as -> MU0 WM0 MI0 ST0 P_usp P_dfr P_nsrt P_nfca P_lck P_gam P_arr P_hdrl P_hlc P_tst P_trf P_tmu P_hdr P_ctx P_dr P_sh | dand32 Q0 as xt0 xt1 xt2 xa4 xa5 xa6 xt3 xt4 xt5 xt6 mv0' -> MU0 WM0 MI0 ST0 P_usp P_dfr P_nsrt P_nfca P_lck P_gam P_arr P_hdrl P_hlc P_tst P_trf P_tmu P_hdr P_ctx P_dr P_sh | destruct Q0 as (xt0 & xt1 & xt2 & xa4 & xa5 & xa6 & xt3 & xt4 & xt5 & xt6 & mv0' & -> & MU0 & WM0 & MI0 & ST0
                    & P_usp & P_dfr & P_nsrt & P_nfca & P_lck & P_gam & P_arr & P_hdrl & P_hlc
                    & P_tst & P_trf & P_tmu & P_hdr & P_ctx & P_dr & P_sh) ]).
    rewrite unrestrict_MSsvc. unfold hclean in Hcl0. cbn [ms_mem MSsvc] in Hcl0. rewrite HLU in MU0, P_hlc.
    pose proof (same_but_materialized_frame _ _ SB1) as FRM1.
    assert (HH1 : m_halted md1 = None).
    { (first [ dand18 FRM1 as _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X17 _ | destruct FRM1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X17 & _) ]). rewrite X17. exact HH. }
    assert (TOP1 : alloc_top (m_vmmaps md1) = alloc_ceiling).
    { rewrite (same_but_materialized_vmmaps _ _ SB1). exact (ai_ceil _ _ _ _ _ _ _ AI). }
    idtac "S0 done".
    (* [comment removed for export] *)
    pose proof (aobj_facts _ _ TH1) as T'. pose proof (aobj_facts _ _ CT1) as C'. pose proof (aobj_facts _ _ PALO) as PA'.
    pose proof (aobj_facts _ _ HLO) as HM'. pose proof (aobj_facts _ _ HLLO) as HL'. pose proof (aobj_facts _ _ DN01) as N0'. pose proof (aobj_facts _ _ DF01) as F0'.
    assert (AG0 : forall a, 0 <= a < 2^64 -> ~ AFreeX3.EXC A p n0 i lo uspd a -> mv0' (wz a) = v (wz a)).
    { intros a Ha NE.
      apply MU0. rewrite (unsigned_lit a Ha). unfold free_directS0c_W, free_cprefixB_W. rewrite !AFreeH0.outside_app.
      unfold AFreeX3.EXC in NE.
      split.
      - cbn [outside]. splits; try exact I.
        + intros X; apply NE. left. clear -X LOW. lia.
        + intros X; apply NE. do 12 right; left. clear -X N6 NR'. lia.
        + intros X; apply NE. do 12 right; left. clear -X N6 NR' PIN R8. lia.
        + intros X; apply NE. right; left. clear -X. lia.
        + intros X; apply NE. do 3 right; left. clear -X. lia.
        + intros X; apply NE. do 4 right; left. clear -X. kung_all. lia.
        + intros X; apply NE. do 5 right; left. clear -X. kung_all. lia.
      - cbn [outside]. splits; try exact I.
        + intros X; apply NE. do 14 right. clear -X. lia.
        + intros X; apply NE. right; left. clear -X. lia.
        + intros X; apply NE. do 7 right; left. clear -X. lia.
        + intros X; apply NE. do 8 right; left. clear -X. lia.
        + intros X; apply NE. do 9 right; left. clear -X. lia.
        + intros X; apply NE. do 10 right; left. clear -X. lia.
        + intros X; apply NE. do 11 right; left. exact X.
        + intros X; apply NE. do 13 right; left. clear -X. lia.
        + intros X; apply NE. do 2 right; left. clear -X. lia. }
    assert (AGq0 : forall x, img_quiet x -> mv0' (wz x) = v (wz x)).
    { intros x Hx. unfold img_quiet in Hx. apply AG0; [clear -Hx; lia|]. clear -Hx T' N0' F0' PA' HL' H5 SHR CEIL LOW CE IR. kung_all. nexc. }
    pose proof (poison_consts_agq v mv0' AGq0 (hit_PCo A m md AI)) as PC0.
    pose proof (a8_consts_agq v mv0' AGq0 canary A8C) as A8C0.
    idtac "AG0 ok".
    (* [comment removed for export] *)
    unfold a8_len.
    match goal with |- srealizes _ (mkCfg ?ms _) _ => set (ms1 := ms) end.
    assert (A0E : ms_gpr ms1 0 = wz pbeg) by (subst ms1; rewrite ms_gpr_MSsvc; simp_regs; reflexivity).
    assert (A1E : ms_gpr ms1 1 = wz len) by (subst ms1; rewrite ms_gpr_MSsvc; simp_regs; reflexivity).
    assert (A2E : ms_gpr ms1 2 = wz 4) by (subst ms1; rewrite ms_gpr_MSsvc; simp_regs; reflexivity).
    eapply (srz_madvise rsegs ms1 md1 (wz 233) T HH1 eq_refl eq_refl).
    - exact (fsm_madvise_args A m md p n0 AI HL NQB md1 SB1 ms1 A0E A1E A2E).
    - (* [comment removed for export] *)
      idtac "N1 side goals ok".
      unfold madvise_eff. rewrite !A0E, !A1E, U2, PL. subst ms1.
      rewrite advance_apply_MSsvc, apply_mem_zeros, mkR_set_a0, lit_add_lit. change (madvise_ecall_pc + 4) with madvise_after_pc.
      set (md2 := madvise_model (wz pbeg) (wz len) md1).
      assert (CR1 : hull_cover (REST A i) (LREST A i) (m_vm_lazy md1) /\ lazy_free (m_vm_lazy md1) h (h + msz)) by (rewrite (sbm_lazy _ _ SB1); exact CR0).
      pose proof (MInv_H1 A m md p n0 i AI HL NQB (pa_eager A) md1 (MInv_H0s A m md p n0 i AI HL NQB (pa_eager A) md1 HI1 (proj1 CR1) (proj2 CR1)) (proj1 CR1) (proj2 CR1)) as HI2. fold md2 in HI2.
      assert (HH2 : m_halted md2 = None) by (unfold md2; rewrite madvise_model_halted; exact HH1).
      match goal with |- context [munrestrict _ (ms_mem ?X) _] => change (ms_mem X) with m end.
      change (apply_zeros (munrestrict (hidc (H0p A p n0 i)) m mv0') [(wz pbeg, wz len)]) with (AFreeGD0.rm2 A m p n0 i mv0').
      (* [comment removed for export] *)
      set (mv1 := AFreeGD0.mv1 A m p n0 i mv0').
      pose proof (AFreeGD0.T01 A m md p n0 i AI HL NQB mv0' Hcl0) as MU01. fold mv1 in MU01.
      pose proof (AFreeGD0.hop01 A m md p n0 i AI HL NQB mv0' Hcl0) as HOP01. fold mv1 in HOP01.
      pose proof (AFreeGD0.MI1 A m md p n0 i AI HL NQB mv0' MI0) as MIv1. fold mv1 in MIv1.
      pose proof (AFreeGD0.mv1_clean A m p n0 i mv0') as Hcl1s. fold mv1 in Hcl1s.
      assert (AG1 : forall a, 0 <= a < 2^64 -> ~ AFreeX3.EXC A p n0 i lo uspd a -> mv1 (wz a) = v (wz a)).
      { intros a Ha NE. rewrite (HOP01 a Ha); [exact (AG0 a Ha NE)|]. intros X. apply NE. unfold AFreeX3.EXC. do 13 right; left. clear -X G1 G6. lia. }
      assert (AGq1 : forall x, img_quiet x -> mv1 (wz x) = v (wz x)).
      { intros x Hx. unfold img_quiet in Hx. apply AG1; [clear -Hx; lia|]. clear -Hx T' N0' F0' PA' HL' H5 SHR CEIL LOW CE IR. kung_all. nexc. }
      (* [comment removed for export] *)
      pose proof (conj F4 (conj G1 (conj SHR (conj CE (conj CEIL (conj LOW (conj T' (conj PA' (conj HM' (conj HL' (conj C' IR))))))))))) as K01.
      assert (STv1 : stk rsegs mv1 lo (uspd + -80 + -32)) by (eapply stk_mu; [exact ST0| exact MU01| sidetac K01]).
      assert (TCv1 : thread_cells mv1 (cl_tp LPA) pa_tsd (p_ctx P) thr).
      { apply (thread_cells_agq v mv1 AGq1 _ _ _ _ TC TPE TSDL). intros k Hk.
        apply (AGapp A m md p n0 i mv1 lo uspd AI HL NQB NTH CEIL AG1 (p_ctx P) 0x10000); try (clear -Hk C' SEP_tc SEP_n0c SEP_f0c SEP_Ac SEP_lc SEP_hc SEP_pc; unfold apart, AMallocA.apart in *; kung_all; lia). }
      pose proof (poison_consts_agq v mv1 AGq1 (hit_PCo A m md AI)) as PCv1.
      pose proof (a8_consts_agq v mv1 AGq1 canary A8C) as A8Cv1.
      assert (CGCFv1 : ro_cells rsegs mv1 0xa8b60 [C8 (wz CF)]) by (eapply ro_cells_agq; [exact AGq1| exact CGCF| intros k Hk; cbn in Hk; unfold img_quiet; clear -Hk; lia]).
      assert (CSEALv1 : ro_cells rsegs mv1 0xa8bb0 [C8 (wz 1)]) by (eapply ro_cells_agq; [exact AGq1| exact CSEAL| intros k Hk; cbn in Hk; unfold img_quiet; clear -Hk; lia]).
      assert (P_dfr1 : rw_cells rsegs mv1 (uspd + -80 + -32) [C8 s2; C8 (wz (thr + 80)); C8 (wz QINST); C8 (wz qput_recret)]) by (eapply rw_cells_mu; [exact P_dfr| exact MU01| sidetac K01]).
      assert (P_nsrt1 : rw_cells rsegs mv1 0xb15d0 [C8 (wz (nch - 1)); C1 (Z_to_bv 8 0)]) by (rewrite <- NCH; eapply rw_cells_mu; [exact P_nsrt| exact MU01| sidetac K01]).
      assert (P_nfca1 : rw_cells rsegs mv1 0xb15e8 [C8 (wz (nf + 1)); C8 (wz (ca - msz))]) by (eapply rw_cells_mu; [exact P_nfca| exact MU01| sidetac K01]).
      assert (P_lck1 : rw_cells rsegs mv1 0xb1800 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C2 (wz 0)]) by (eapply rw_cells_mu; [exact P_lck| exact MU01| sidetac K01]).
      assert (P_gam1 : rw_cells rsegs mv1 0xb1818 [C8 (wz (gA - msz)); C8 (wz (gM - msz))]) by (eapply rw_cells_mu; [exact P_gam| exact MU01| sidetac K01]).
      assert (P_arr1 : u64arr rsegs mv1 pa (upd (sec_words A) (Z.to_nat (Z.of_nat i)) (wz hla))) by (eapply u64arr_mu; [exact P_arr| exact MU01| sidetac K01]).
      assert (P_hdrl1 : rw_cells rsegs mv1 h [C8 (wz h); C8 (wz msz); C8 (wz (needed_size2 n0)); C8 (wz (Z.of_nat i))]) by (eapply rw_cells_mu; [exact P_hdrl| exact MU01| sidetac K01]).
      assert (P_hlc1 : hla = h \/ rw_cells rsegs mv1 hla [C8 (wz hla); C8 (wz (map_size (cs_n (sec_last A)))); C8 (wz (needed_size2 (cs_n (sec_last A)))); C8 (wz (Z.of_nat i))]).
      { destruct P_hlc as [E|C]; [left; exact E| right]. eapply rw_cells_mu; [exact C| exact MU01| sidetac K01]. }
      assert (P_trf1 : rw_cells rsegs mv1 (thr + 2840) [C8 (wz (rf + 1)); C8 (wz (rfd + n0))]) by (eapply rw_cells_mu; [exact P_trf| exact MU01| sidetac K01]).
      assert (P_tmu1 : rw_cells rsegs mv1 (thr + 2888) [C8 (wz mu); C8 (wz mdv)]) by (eapply rw_cells_mu; [exact P_tmu| exact MU01| sidetac K01]).
      idtac "mv1 cells ok".
      (* [comment removed for export] *)
      assert (USP : bv_unsigned (wz (uspd + -80)) = uspd + -80) by (apply unsigned_lit; clear -SPR CEIL LOW CE; lia).
      assert (LOw : uspd + -80 <= 2^47) by (clear -SPH; lia).
      assert (SPAw : (uspd + -80) mod 16 = 0) by (clear -SPA; lia).
      assert (P_nsrt1' : rw_cells rsegs mv1 0xb15d0 [C8 (wz (Z.of_nat (length (sec_words A)) - 1)); C1 (Z_to_bv 8 0)]) by (rewrite NCH; exact P_nsrt1).
      eapply (srz_evt_restrict rsegs (H1 A p n0 i) OFF1 pa_wx _ (pa_eager A) (S1_post (uspd + -80) lo i nf ca gA gM rf rfd mu mdv mv1) _ md2 T HI2 HH2).
      { rewrite restrict_MS. change (mrestrict (hidc (H1 A p n0 i)) (AFreeGD0.rm2 A m p n0 i mv0')) with mv1.
        replace (uspd + -80 + -32) with (bv_unsigned (wz (uspd + -80)) + -32) by (rewrite USP; reflexivity).
        rewrite <- USP in STv1, P_dfr1.
        eapply (sdeal_mid (wz qput_recret) (wz (uspd + -80)) gp (cl_tp LPA) (wz QINST) (wz (thr + 80)) s2 s3 s4 s5 (wz (2^20))
                  s7 s8 s9 s10 s11 F fc lo (uspd + -80) (p + -16) pa 0 0 h msz (needed_size2 n0) (Z.of_nat i) nf ca gA gM n0 pa_tsd (p_ctx P) thr rf rfd mu mdv 1
                  (sec_words A) (wz hla) (wz hla) (wz (map_size (cs_n (sec_last A)))) (wz (needed_size2 (cs_n (sec_last A))))
                  CEIL ltac:(rewrite USP; exact LOw) ltac:(rewrite USP; exact SPAw) ltac:(rewrite unsigned_lit by (unfold qput_recret; lia); reflexivity) TPE ltac:(clear -CEIL LOW; lia)
                  PALO ltac:(rewrite HLU; exact HLLO) HLO MSZ ltac:(clear -PIN N6 NR' R8; lia) MUR MDR SEALR SEP_ht SEP_at ltac:(rewrite HLU; exact SEP_lt) SEP_tc TSDL
                  _ mv1 xt0 xt1 xt2 _ _ _ _ _ _ _ xt3 xt4 xt5 xt6
                  ltac:(rewrite USP; clear -CEIL LOW; lia) MIv1 STv1 TCv1 P_dfr1 P_nsrt1' P_nfca1 P_lck1 P_gam1 P_arr1 P_hdrl1 ltac:(rewrite HLU; exact P_hlc1) P_trf1 P_tmu1).
        idtac "S1 applied".
        intros yt0 yt1 yt2 ya3 ya4 ya5 ya6 yt3 yt4 yt5 yt6 scr mv1' UF1 Q_nsrt Q_nfca Q_lck Q_gam Q_arr Q_hdrl Q_hlc Q_trf Q_tmu MU1 WM1 MI1' ST1'.
        unfold S1_post. rewrite USP in *. do 13 eexists. split; [reflexivity|].
        rewrite NCH in Q_nsrt. rewrite HLU in Q_hlc.
        splits; first [eassumption | match goal with |- ?g => idtac "S1post FAIL" g end]. }
      idtac "S1 done".
      intros msr1 md3 Q1 HI3 SB3 Hcl1.
      (first [ dex13 Q1 as yt0 yt1 yt2 ya3 ya4 ya5 ya6 yt3 yt4 yt5 yt6 scr mv1'; dand15 Q1 as -> UF1 Q_nsrt Q_nfca Q_lck Q_gam Q_arr Q_hdrl Q_hlc Q_trf Q_tmu MU1 WM1 MIv1' STv1' | dand28 Q1 as yt0 yt1 yt2 ya3 ya4 ya5 ya6 yt3 yt4 yt5 yt6 scr mv1' -> UF1 Q_nsrt Q_nfca Q_lck Q_gam Q_arr Q_hdrl Q_hlc Q_trf Q_tmu MU1 WM1 MIv1' STv1' | destruct Q1 as (yt0 & yt1 & yt2 & ya3 & ya4 & ya5 & ya6 & yt3 & yt4 & yt5 & yt6 & scr & mv1' & -> & UF1 & Q_nsrt & Q_nfca & Q_lck & Q_gam & Q_arr & Q_hdrl & Q_hlc & Q_trf & Q_tmu & MU1 & WM1 & MIv1' & STv1') ]).
      rewrite unrestrict_MSsvc. unfold hclean in Hcl1. cbn [ms_mem MSsvc] in Hcl1.
      match goal with |- context [munrestrict _ (ms_mem ?X) _] => change (ms_mem X) with (AFreeGD0.rm2 A m p n0 i mv0') end.
      change (munrestrict (hidc (H1 A p n0 i)) (AFreeGD0.rm2 A m p n0 i mv0') mv1') with (AFreeGD0.rm3 A m p n0 i mv0' mv1').
      pose proof (same_but_materialized_frame _ _ SB3) as FRM3.
      assert (HH3 : m_halted md3 = None).
      { (first [ dand18 FRM3 as _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X17 _ | destruct FRM3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X17 & _) ]). rewrite X17. exact HH2. }
      assert (MD2 : md2 = madvise_model (wz pbeg) (wz len) md1) by reflexivity.
      pose proof (fsm_has A m md p n0 i AI NTH md1 md2 md3 SB1 MD2 SB3) as HAS3.
      pose proof (fsm_eager A m md p n0 AI HL NQB md1 md2 md3 SB1 MD2 SB3) as EM3.
      (* [comment removed for export] *)
      match goal with |- srealizes _ (mkCfg ?ms _) _ => set (ms3 := ms) end.
      assert (B0E : ms_gpr ms3 0 = wz h) by (subst ms3; rewrite ms_gpr_MSsvc; simp_regs; reflexivity).
      assert (B1E : ms_gpr ms3 1 = wz msz) by (subst ms3; rewrite ms_gpr_MSsvc; simp_regs; reflexivity).
      assert (PRU : page_round_up (wz msz) = wz msz) by (unfold page_round_up; rewrite U4, PMZ; reflexivity).
      eapply (srz_munmap_lazy rsegs ms3 md3 (wz 215) T HH3 eq_refl eq_refl).
      { unfold munmap_args_ok. rewrite B0E, B1E, PRU, U3, U4, PMZ. unfold page_size, TASK_SIZE.
        split; [exact HAL|]. split; [intros E; apply (f_equal bv_unsigned) in E; rewrite U4, unsigned_lit in E by lia; clear -E MP; lia|].
        split; [clear -HHI CE; lia| exact HAS3]. }
      unfold munmap_eff. rewrite B0E, B1E, PRU. subst ms3.
      rewrite advance_apply_MSsvc, apply_mem_unmaps, mkR_set_a0, lit_add_lit, munmap_model_modelL. change (munmap_ecall_pc + 4) with munmap_after_pc.
      set (md4 := munmap_modelL (wz h) (wz msz) md3).
      pose proof (MInv_H2 A m md p n0 i AI HL NQB (pa_eager A) md3 HI3 HAS3 EM3) as HI4. fold md4 in HI4.
      assert (HH4 : m_halted md4 = None) by (unfold md4; rewrite <- munmap_model_modelL, munmap_model_halted; exact HH3).
      change (apply_unmaps (AFreeGD0.rm3 A m p n0 i mv0' mv1') [(wz h, wz msz)]) with (AFreeGD0.rm4 A m p n0 i mv0' mv1').
      idtac "N2 done".
      (* [comment removed for export] *)
      set (mv2 := AFreeGD0.mv2 A m p n0 i mv0' mv1').
      pose proof (AFreeGD0.T12 A m md p n0 i AI HL NQB mv0' mv1' Hcl1) as MU12. fold mv2 in MU12.
      pose proof (AFreeGD0.hop12 A m md p n0 i AI HL NQB mv0' mv1' Hcl1) as HOP12. fold mv2 in HOP12.
      pose proof (AFreeGD0.MI2 A m md p n0 i AI HL NQB mv0' mv1' MIv1') as MIv2. fold mv2 in MIv2.
      assert (AG1' : forall a, 0 <= a < 2^64 -> ~ AFreeX3.EXC A p n0 i lo uspd a -> mv1' (wz a) = v (wz a)).
      { intros a Ha NE. rewrite (MU1 (wz a)); [exact (AG1 a Ha NE)|]. rewrite (unsigned_lit a Ha). cbn [outside].
        split; [| split; [| exact I]]; intros X; apply NE; unfold AFreeX3.EXC; [left; clear -X CEIL LOW; lia| do 2 right; left; exact X]. }
      assert (AG2 : forall a, 0 <= a < 2^64 -> ~ AFreeX3.EXC A p n0 i lo uspd a -> mv2 (wz a) = v (wz a)).
      { intros a Ha NE. rewrite (HOP12 a Ha); [exact (AG1' a Ha NE)|]. intros X. apply NE. unfold AFreeX3.EXC. do 12 right; left. exact X. }
      assert (AGq2 : forall x, img_quiet x -> mv2 (wz x) = v (wz x)).
      { intros x Hx. unfold img_quiet in Hx. apply AG2; [clear -Hx; lia|]. clear -Hx T' N0' F0' PA' HL' H5 SHR CEIL LOW CE IR. kung_all. nexc. }
      pose proof (conj HHI (conj H5 (conj CE (conj CEIL (conj LOW (conj SEP_ht (conj SEP_hp (conj SEP_hc (conj HLA (conj NCH IR)))))))))) as K12.
      pose proof (conj CEIL (conj LOW (conj T' CE))) as K11.
      assert (STv2 : stk rsegs mv2 lo (uspd + -80 + -48)) by (eapply stk_mu; [exact STv1'| exact MU12| sidetac K12]).
      assert (UF2 : rw_cells rsegs mv2 (uspd + -80 + -48) (unmap_frame scr s2 (wz (thr + 80)) (wz QINST) (wz qput_recret))) by (eapply rw_cells_mu; [exact UF1| exact MU12| sidetac K12]).
      pose proof (a8_consts_agq v mv2 AGq2 canary A8C) as A8Cv2. destruct A8Cv2 as (C144v2 & _).
      assert (CGCFv2 : ro_cells rsegs mv2 0xa8b60 [C8 (wz CF)]) by (eapply ro_cells_agq; [exact AGq2| exact CGCF| intros k Hk; cbn in Hk; unfold img_quiet; clear -Hk; lia]).
      assert (QCv2 : rw_cells rsegs mv2 (thr + 80) [C8 (wz (Z.of_nat (length (a_qthread A)))); C8 (wz (qc_first A (a_qthread A))); C8 (wz (qc_last A (a_qthread A))); C8 (wz (q_bytes (a_qthread A)))]).
      { eapply rw_cells_agp; [exact (free_QC A m md AI)|]. intros k Hk. cbn in Hk. apply (AGthr A m md p n0 i mv2 lo uspd AI HL NQB NTH CEIL AG2); clear -Hk; lia. }
      (* [comment removed for export] *)
      assert (P_usp2 : rw_cells rsegs mv2 (uspd + -80) [C8 (wz (thr + 208)); C8 (wz stkobj); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 rac]) by hop3 P_usp MU01 K01 MU1 K11 MU12 K12.
      idtac "mv2 cells ok".
      (* [comment removed for export] *)
      assert (QWF : forall e, In e (q_entries (a_qthread A ++ a_qglobal A)) -> 0 <= qe_n e).
      { intros e He. destruct (qentry_wf A v AR e He) as [N _]. clear -N. lia. }
      assert (QB0 : 0 <= q_bytes (a_qthread A)).
      { assert (QBall : forall bs, (forall e, In e (q_entries bs) -> 0 <= qe_n e) -> 0 <= q_bytes bs).
        { clear. intros bs QW. induction bs as [|b r IH]; [cbn; lia|]. rewrite q_bytes_cons, batch_bytes_ebytes.
          assert (IHr : 0 <= q_bytes r) by (apply IH; intros e He; apply QW; rewrite q_entries_cons; apply in_or_app; right; exact He).
          assert (EW : forall e, In e (ba_entries b) -> 0 <= qe_n e) by (intros e He; apply QW; rewrite q_entries_cons; apply in_or_app; left; exact He).
          assert (0 <= ebytes (ba_entries b)); [| unfold kQuarantineBatchBytes; lia].
          clear -EW. induction (ba_entries b) as [|e es IHe]; [cbn; lia|].
          rewrite ebytes_cons. unfold qe_bytes. pose proof (user_size_pos (qe_n e) ltac:(apply EW; left; reflexivity)).
          assert (0 <= ebytes es) by (apply IHe; intros e' He'; apply EW; right; exact He'). lia. }
        apply QBall. intros e He. apply QWF. unfold q_entries in He |- *. rewrite flat_map_app. apply in_or_app. left. exact He. }
      assert (QB : 0 <= q_bytes (a_qthread A) <= 2^20).
      { split; [exact QB0|]. (first [ pose proof ((wfQ A WF0)) as dR_31; dand5 dR_31 as _ _ _ QTB _ | destruct (wfQ A WF0) as (_ & _ & _ & QTB & _) ]). clear -QTB. unfold kQuarantineCacheSize in QTB. exact QTB. }
      (* [comment removed for export] *)
      eapply (srz_evt_restrict rsegs (H2 A p n0 i) OFF2 pa_wx _ (pa_eager A - msz)
                (free_directS2c_post rac spd gp (cl_tp LPA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo mv2 (q_bytes (a_qthread A))) _ md4 T HI4 HH4).
      { rewrite restrict_MS. change (mrestrict (hidc (H2 A p n0 i)) (AFreeGD0.rm4 A m p n0 i mv0' mv1')) with mv2.
        eapply (free_directS2c rac spd gp (cl_tp LPA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc v lo p pa_tsd (p_ctx P) thr ((n0 + 7) / 8)
                  (p_nodes0 P) (p_frames0 P) stkobj (a_depot A) key pa h msz 1 (sec_words A) (wz hla)
                  LO SPH PLO PNB TC (conj DN01 DN02) (conj DF01 DF02) KL PALO ltac:(rewrite HLU; exact HLLO) HLO MSZ SEALR
                  mv2 yt0 yt1 yt2 ya3 ya4 ya5 ya6 yt3 yt4 yt5 yt6 scr
                  (Z.of_nat (length (a_qthread A))) (qc_first A (a_qthread A)) (qc_last A (a_qthread A)) (q_bytes (a_qthread A))
                  MIv2 STv2 UF2 CGCFv2 C144v2 QB P_usp2 QCv2). }
      idtac "S2 done".
      intros msr2 md5 Q2 HI5 SB5 Hcl2.
      (first [ dex15 Q2 as zt0 zt1 zt2 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 mv2'; dand5 Q2 as -> MU2 WM2 MIv2' STv2' | dand20 Q2 as zt0 zt1 zt2 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 mv2' -> MU2 WM2 MIv2' STv2' | destruct Q2 as (zt0 & zt1 & zt2 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & zt3 & zt4 & zt5 & zt6 & mv2' & -> & MU2 & WM2 & MIv2' & STv2') ]).
      rewrite unrestrict_MS. unfold hclean in Hcl2. cbn [ms_mem MS] in Hcl2.
      match goal with |- context [munrestrict _ (ms_mem ?X) _] => change (ms_mem X) with (AFreeGD0.rm4 A m p n0 i mv0' mv1') end.
      change (munrestrict (hidc (H2 A p n0 i)) (AFreeGD0.rm4 A m p n0 i mv0' mv1') mv2') with (AFreeGD0.rm5 A m p n0 i mv0' mv1' mv2').
      set (rm5 := AFreeGD0.rm5 A m p n0 i mv0' mv1' mv2').
      idtac "post S2".
      (* [comment removed for export] *)
      set (KEY := key) in *.
      set (D' := fst (depot_putC (a_depot A) KEY)) in *.
      set (A' := freeS A p i D' true (dead2 p n0)).
      pose proof (conj CEIL (conj LOW (conj CE (conj PA' (conj HL' (conj T' IR)))))) as K22.
      assert (AG2' : forall a, 0 <= a < 2^64 -> ~ AFreeX3.EXC A p n0 i lo uspd a -> mv2' (wz a) = v (wz a)).
      { intros a Ha NE. rewrite (MU2 (wz a)); [exact (AG2 a Ha NE)|]. rewrite (unsigned_lit a Ha). cbn [outside].
        split; [| exact I]. intros X; apply NE; unfold AFreeX3.EXC; left; clear -X CEIL LOW; lia. }
      assert (NN : forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> a < 2^64 -> ~ AFreeX3.holeD p n0 a -> v (wz a) <> None -> mv2' (wz a) <> None).
      { intros a H0 H1 H2 NH Hv. unfold AFreeX3.holeD in NH.
        apply (wmono_NN _ _ a WM2 H1 ltac:(lia)). apply (AFreeGD0.T12_NN A m md p n0 i AI HL NQB mv0' mv1' Hcl1 (wz a)); [rewrite (unsigned_lit a) by lia; clear -NH; lia|].
        apply (wmono_NN _ _ a WM1 H1 ltac:(lia)). apply (AFreeGD0.T01_NN A m md p n0 i AI HL NQB mv0' Hcl0 (wz a)); [rewrite (unsigned_lit a) by lia; clear -NH; lia|].
        apply (wmono_NN _ _ a WM0 H1 ltac:(lia)). exact Hv. }
      assert (VIEW : aview_of (pa_hull A') rm5 = mv2').
      { unfold aview_of. subst A'. rewrite (hidc_H2 A p n0 i NTH D' true). subst rm5. apply (AFreeGD0.rm5_view A m p n0 i mv0' mv1' mv2'). exact Hcl2. }
      (* [comment removed for export] *)
      assert (PNSRT : rw_cells rsegs mv2' 0xb15d0 [C8 (wz (nch - 1)); C1 (Z_to_bv 8 0)])
        by (eapply rw_cells_mu; [eapply rw_cells_mu; [exact Q_nsrt| exact MU12| sidetac K12]| exact MU2| sidetac K22]).
      assert (PLCK : rw_cells rsegs mv2' 0xb1800 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C2 (wz 0)])
        by (eapply rw_cells_mu; [eapply rw_cells_mu; [exact Q_lck| exact MU12| sidetac K12]| exact MU2| sidetac K22]).
      assert (PARR : u64arr rsegs mv2' pa (upd (sec_words A) i (wz hla))).
      { rewrite Nat2Z.id in Q_arr. eapply u64arr_mu; [eapply u64arr_mu; [exact Q_arr| exact MU12| sidetac K12]| exact MU2| sidetac K22]. }
      assert (PHLC : hla = h \/ rw_cells rsegs mv2' hla [C8 (wz hla); C8 (wz (map_size (cs_n (sec_last A)))); C8 (wz (needed_size2 (cs_n (sec_last A)))); C8 (wz (Z.of_nat i))]).
      { destruct HLA as [E|AP]; [left; exact E|]. destruct Q_hlc as [E|C]; [left; exact E| right].
        pose proof (conj AP K12) as K12'.
        eapply rw_cells_mu; [eapply rw_cells_mu; [exact C| exact MU12| sidetac K12']| exact MU2| sidetac K22]. }
      assert (AGd : forall a, depot_foot AL_pboth (p_nodes0 P) (p_frames0 P) a -> mv2' (wz a) = mv0' (wz a)).
      { intros a Fa. unfold depot_foot in Fa. cbn [al_stackStore al_depot_nodes_map1 AL_pboth] in Fa. unfold kDepotNodesL1 in Fa.
        assert (Ha : 0 <= a < 2^64) by (clear -Fa N0' F0' CE; kung_all; lia).
        rewrite (MU2 (wz a)), (HOP12 a Ha), (MU1 (wz a)), (HOP01 a Ha); [reflexivity| | | |]; rewrite ?(unsigned_lit a Ha); cbn [outside];
          clear -Fa N0' F0' SHR G1 F4 CEIL LOW CE T' SEP_n0t SEP_f0t H5 SEP_hn SEP_hf; splits; try exact I; unfold apart, AMallocA.apart in *; kung_all; lia. }
      pose proof (depot_repL_agree AL_pboth rsegs D' (p_nodes0 P) (p_frames0 P) mv0' mv2' P_dr AGd) as PDR.
      (* [comment removed for export] *)
      assert (IAQ : ((a_ia_inited A = true /\ (forall a, iafoot a -> mv2' (wz a) = v (wz a))) \/ ia_repr_ LPA AL_pboth true mv2')
                    /\ u8_at rsegs mv2' (al_internal_alloc_inited AL_pboth + 1) 0 /\ bytes_at rsegs mv2' 0x14464a [Z_to_bv 8 0; Z_to_bv 8 0]).
      { assert (IAW : forall a, 0xb5dc0 <= a < 0x14464c -> mv2' (wz a) = v (wz a)).
        { intros a Ha. apply AG2'; [clear -Ha; lia|]. clear -Ha IAT CEIL LOW CE T' N0' F0' PA' HL' H5 SHR IR. kung_all. nexc. }
        split; [| split].
        + left. split; [exact IAT|]. intros a Ha. apply IAW. unfold iafoot in Ha. cbn [al_internal_allocator_inst al_internal_alloc_inited AL_pboth] in Ha. clear -Ha. lia.
        + pose proof (ar_locks _ _ _ _ _ (proj2 AR)) as LK. unfold locks_repr_ in LK. cbv zeta in LK. (first [ dand6 LK as _ _ _ _ _ LK | destruct LK as (_ & _ & _ & _ & _ & LK) ]).
          change (al_internal_alloc_inited AL_pboth + 1) with 0x144649 in LK |- *. rewrite lockb_nil in LK.
          eapply (bytes_at_agree_gen _ _ _ _ _ LK). intros k Hk. cbn in Hk. apply IAW. lia.
        + pose proof (consts_cell v 0x14464a [Z_to_bv 8 0; Z_to_bv 8 0] (proj1 (ar_consts _ _ _ _ _ (proj2 AR))) eq_refl) as PD.
          eapply (bytes_at_agree_gen _ _ _ _ _ PD). intros k Hk. cbn in Hk. apply IAW. lia. }
      (first [ dand3 IAQ as IAH IAL IAP | destruct IAQ as (IAH & IAL & IAP) ]).
      assert (HNONE : forall a, h <= a < h + msz -> mv2' (wz a) = None).
      { intros a Ha. rewrite (MU2 (wz a)); [exact (AFreeGD0.mv2_none_map A m md p n0 i AI HL NQB mv0' mv1' a Ha)|].
        rewrite unsigned_lit by (clear -Ha H5 HHI CE; lia). cbn [outside]. split; [clear -Ha HHI CEIL LOW; lia| exact I]. }
      assert (SM' : mapped v lo (uspd - lo)).
      { intros k Hk. destruct ST as (_ & _ & STx). destruct (STx (lo + k) ltac:(lia)) as [Wv _]. unfold wview, wa in Wv.
        rewrite unsigned_lit in Wv by (clear -Hk CEIL LOW CE SPR; lia). rewrite (pa_find_segment_none (lo + k) 1) in Wv by (clear -Hk CEIL LOW CE SPR; lia).
        destruct (v (wz (lo + k))); [discriminate| exact Wv]. }
      idtac "finale facts ok".
      (* [comment removed for export] *)
      assert (HID1 : forall z, in_shadow_maps z -> ~ (sh h <= z < sh h + msz / 8) -> rm5 (wz z) = m (wz z)).
      { intros z Z1 Z2. assert (Zr : 0 <= z < 2^64) by (unfold in_shadow_maps in Z1; clear -Z1; kung_all; lia).
        assert (NZ : ~ (h <= z < h + msz)) by (unfold in_shadow_maps in Z1; clear -Z1 HM'; kung_all; lia).
        destruct (in_hullb (H2 A p n0 i) z) eqn:V2.
        - subst rm5. rewrite (AFreeGD0.rm5_vis A m p n0 i mv0' mv1' mv2' (wz z)) by (unfold hidc; rewrite (unsigned_lit z Zr), V2; reflexivity).
          rewrite (AG2' z Zr) by (unfold in_shadow_maps in Z1; clear -Z1 Z2 CEIL LOW CE T' N0' F0' PA' HL' HM' IR; kung_all; nexc).
          unfold aview_of, mrestrict. rewrite HD0. unfold hidc. rewrite (unsigned_lit z Zr), <- (AFreeGD0.vis_same A m md p n0 i AI HL NQB z Z2 NZ), V2. reflexivity.
        - subst rm5. apply (AFreeGD0.rm5_hid A m md p n0 i AI HL NQB mv0' mv1' mv2' z Zr); [| exact NZ].
          rewrite <- (AFreeGD0.vis_same A m md p n0 i AI HL NQB z Z2 NZ). exact V2. }
      assert (HID2 : forall z, sh h <= z < sh h + msz / 8 -> rm5 (wz z) = Some (Z_to_bv 8 0)).
      { intros z Hz. assert (Zr : 0 <= z < 2^64) by (clear -Hz SHR; kung_all; lia).
        destruct (decide (pbeg <= z < pend)) as [MID|EDGE].
        - destruct (in_hullb (H2 A p n0 i) z) eqn:V2.
          + subst rm5. rewrite (AFreeGD0.rm5_vis A m p n0 i mv0' mv1' mv2' (wz z)) by (unfold hidc; rewrite (unsigned_lit z Zr), V2; reflexivity).
            rewrite (MU2 (wz z)) by (rewrite (unsigned_lit z Zr); cbn [outside]; split; [clear -Hz SHR CEIL LOW CE; kung_all; lia| exact I]).
            rewrite (HOP12 z Zr) by (clear -Hz SHR HM'; kung_all; lia).
            rewrite (MU1 (wz z)) by (rewrite (unsigned_lit z Zr); cbn [outside]; split; [clear -Hz SHR CEIL LOW CE; kung_all; lia| split; [clear -Hz SHR T'; kung_all; lia| exact I]]).
            apply (AFreeGD0.mv1_mid A m md p n0 i AI HL NQB mv0' z MID). unfold hidc. rewrite (unsigned_lit z Zr), (vis_H2_H1 A p n0 i z V2). reflexivity.
          + subst rm5. exact (AFreeGD0.rm5_mid A m md p n0 i AI HL NQB mv0' mv1' mv2' z MID V2).
        - subst rm5. rewrite (AFreeGD0.rm5_vis A m p n0 i mv0' mv1' mv2' (wz z)) by (unfold hidc; rewrite (unsigned_lit z Zr), (AFreeGD0.vis_edges A p n0 i z ltac:(clear -Hz EDGE G1 G6; lia)); reflexivity).
          rewrite (MU2 (wz z)) by (rewrite (unsigned_lit z Zr); cbn [outside]; split; [clear -Hz SHR CEIL LOW CE; kung_all; lia| exact I]).
          rewrite (HOP12 z Zr) by (clear -Hz SHR HM'; kung_all; lia).
          rewrite (MU1 (wz z)) by (rewrite (unsigned_lit z Zr); cbn [outside]; split; [clear -Hz SHR CEIL LOW CE; kung_all; lia| split; [clear -Hz SHR T'; kung_all; lia| exact I]]).
          rewrite (HOP01 z Zr) by exact EDGE.
          assert (SH5 : 0x60a000 <= sh h) by (clear -SHR; lia).
          replace z with (sh h + (z - sh h)) by lia. apply (bytes_zero_raw mv0' (sh h) _ P_sh SH5).
          rewrite Z2Nat.id by (apply Z.div_pos; [clear -MSZ; lia| lia]). clear -Hz. lia. }
      idtac "HID ok".
      (* [comment removed for export] *)
      pose proof (sk_li A m md p n0 AI HL NQ') as LU.
      (first [ pose proof ((dead2_ok A m md p n0 AI HL NQB)) as dR_35; dand3 dR_35 as DEADF DEADL DEADB | pose proof (dead2_ok A m md p n0 AI HL NQB) as (DEADF & DEADL & DEADB) ]).
      assert (MD4 : md4 = munmap_modelL (wz h) (wz msz) md3) by reflexivity.
      pose proof (MInv_perm _ _ _ _ _ _ (Permutation_sym (hull_perm0 A m md p n0 i AI HL NQB NTH)) (Permutation_sym (lhull_perm0 A m md p n0 i AI HL NQB NTH)) HI1) as HI1p.
      assert (HI3x : exists Hx HLx Ex, MInv Hx HLx Ex md3) by (exists (H1 A p n0 i), (L1 A p n0 i), (pa_eager A); exact HI3).
      pose proof (same_but_materialized_frame _ _ SB5) as FRM5.
      eapply (KK zt0 zt1 zt2 (wz (q_bytes (a_qthread A))) za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 A' rm5 md5).
      + (* [comment removed for export] *)
        constructor.
        * subst A' D'. exact (freeS_WF A m md p (LI (ChS (CS h n0)) n0) KEY (CS h n0) i true (dead2 p n0) AI LU eq_refl NTH KEYU DEADF DEADL DEADB).
        * change (ahull_of pa_image_ivs AL_pboth A') with (pa_hull A'). rewrite VIEW. subst A'.
          exact (freeS_arepr A m md p n0 i mv2' lo uspd AI HL NQB NTH CEIL AG2' NN D' PNSRT PLCK PARR PHLC PDR IAH IAL IAP).
        * subst A'. cbn [freeS a_pl a_reg a_sec]. exact (freeS_hidden A m md p n0 i rm5 AI NTH HID1 HID2).
        * subst A'. cbn [freeS a_pl]. exact (ai_extra _ _ _ _ _ _ _ AI).
        * subst A'. cbn [freeS a_pl a_sec]. exact (fsm_ledger A m md p n0 i AI HL NQB NTH md1 md2 md3 md4 md5 SB1 MD2 SB3 MD4 SB5 HI3x).
        * subst A' D'. rewrite (freeS_eager A p KEY (CS h n0) i true (dead2 p n0) NTH DEADL). cbn [cs_n].
          apply (MInv_perm _ _ _ _ _ _ (hull_permF A p n0 i NTH _ true) (lhull_permF A p n0 i NTH _ true)). exact HI5.
        * (first [ dand18 FRM5 as _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X17 _ | destruct FRM5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X17 & _) ]). rewrite X17. exact HH4.
        * subst A'. cbn [freeS a_pl a_sec]. exact (fsm_cover A m md p n0 i AI HL NQB NTH md1 md2 md3 md4 md5 SB1 MD2 SB3 MD4 SB5).
        * exact (proj1 (fsm_ceil A m md p n0 AI md1 md2 md3 md4 md5 SB1 MD2 SB3 MD4 SB5)).
      + (* [comment removed for export] *)
        rewrite VIEW. exact MIv2'.
      + exact (fsm_frame A m md p n0 AI md1 md2 md3 md4 md5 SB1 MD2 SB3 MD4 SB5).
      + intros ff. reflexivity.
      + subst A'. reflexivity.
      + subst A'. unfold as_live, as_live_. cbn [freeS a_livemap]. unfold free_lm. rewrite lookup_delete_eq. reflexivity.
      + intros q Hq. subst A'. unfold as_live, as_live_. cbn [freeS a_livemap]. unfold free_lm. rewrite lookup_delete_ne by congruence. reflexivity.
      + subst A' D'. exact (freeS_livebytes A p n0 (LI (ChS (CS h n0)) n0) KEY i true (dead2 p n0) LU eq_refl).
      + reflexivity.
      + reflexivity.
      + reflexivity.   (* [comment removed for export] *)
      + subst A' D'. rewrite (freeS_nlive A p (LI (ChS (CS h n0)) n0) KEY i true (dead2 p n0) LU).
        destruct (Z.eqb_spec p 0) as [E0|_]; [exfalso; clear -E0 H5; lia| reflexivity].
      + (* [comment removed for export] *)
        intros c Hc [R0 K0]. subst A'. split; [exact R0| exact K0].
      + (* [comment removed for export] *)
        intros k Hk. rewrite VIEW. cbn [cl_errno LPA]. unfold mrd.
        rewrite (AGimg A m md p n0 i mv2' lo uspd AI HL NQB NTH CEIL AG2' (6191924 + k)); [reflexivity| clear -Hk; lia| clear -Hk; lia| unfold ia_blk; clear -Hk; lia| clear -Hk; lia| clear -Hk; lia| clear -Hk; lia| clear -Hk; lia].
      + (* [comment removed for export] *)
        rewrite VIEW. apply frame_ok_widen; [| | exact SMH].
        * subst A'. exact (freeS_frame A m md p n0 i mv2' lo uspd AI HL NQB NTH CEIL AG2' NN D' PARR PHLC IAH HNONE SM' SPH).
        * intros a Ha. apply AG2'; [clear -Ha SPR SPHI HISP; lia|]. clear -Ha CEIL LOW CE T' N0' F0' PA' HL' HM' SHR IR. kung_all. nexc.
      + (* [comment removed for export] *)
        intros a Ha. rewrite VIEW. apply AG2'; [clear -Ha SPR SPHI HISP; lia|]. clear -Ha CEIL LOW CE T' N0' F0' PA' HL' HM' SHR IR. kung_all. nexc.
      + (* [comment removed for export] *)
        rewrite VIEW. exact STv2'.
  Qed.
End FreeDirectCoreG.
