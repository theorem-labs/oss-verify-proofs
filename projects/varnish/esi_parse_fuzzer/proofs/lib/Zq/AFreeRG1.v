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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts ARtSscs AMTac AMallocA AMallocI AMalmys AMal9l1 AFreeH AFreeH0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeT AFreeHc AFreeDc AFreeH1c AFreeW1c AFrea6l ACoresk ARtSnjd.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMal9l1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeT OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeHc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeDc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH1c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeW1c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFrea6l OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ACoresk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSnjd.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import AInvWfp.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ATranspR AFreeRS AFreeRX AFreeRI AFreeRT AFreeRC.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeRE.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeRE.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeRE.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeRE AWrapKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ATranspR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRS OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRX OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRT OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRC OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRE.AFreeRI1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRE.AFreeRL OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRE.AFreeRN OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRE OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AWrapKit.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AQPart.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeB1 AFreeB2 ATransp AFreeB3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeB4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeB4 AFreeB4c AFreeB5.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQWf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQPart.AQWfJ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB4.AFreeB3R OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB4c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
#[local] Notation WF := (WF AL_pboth).   (* [comment removed for export] *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Notation wz z := (Z_to_bv 64 z) (only parsing).
(* [comment removed for export] *)
Lemma pa_wx : wx_segs_nowrap rsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kSpaceReserve, kMaxSize in *.
Lemma qc_first_push_last : forall A qt e, qt <> [] -> qc_first A (qpush_last qt e) = qc_first A qt.
Proof.
  intros A qt e NE. destruct qt as [|b r]; [reflexivity|]. destruct (qpush_last_head (b :: r) e NE b r eq_refl) as [r' E]. rewrite E.
  unfold qc_first. destruct r; reflexivity.
Qed.
Lemma qc_last_push_last : forall A qt e, qt <> [] -> qc_last A (qpush_last qt e) = qc_last A qt.
Proof.
  intros A qt e NE. unfold qc_last. rewrite (qpush_last_last qt e NE).
  destruct (qpush_last qt e) eqn:E; [exfalso; exact (qpush_last_nonnil qt e NE E)|]. destruct qt; [congruence|]. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma ro_C8C8 : forall (mm : mem) a x y, u64_at rsegs mm a x -> u64_at rsegs mm (a + 8) y -> ro_cells rsegs mm a [C8 (wz x); C8 (wz y)].
Proof.
  intros mm a x y Bx By. unfold ro_cells, cells_at. split; [cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; apply length_le8|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
  apply bytes_at_app. split; [exact Bx|]. rewrite length_le8. exact By.
Qed.

Section FreeHitsR.
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
  Hypothesis NQ : n0 <= 2^28.
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
  #[warnings="-notation-for-abbreviation"] Local Notation uspd := (bv_unsigned spd).
  #[warnings="-notation-for-abbreviation"] Local Notation T160 := (bv_unsigned spd - 160).
  #[warnings="-notation-for-abbreviation"] Local Notation dsp := (bv_unsigned spd - 160 - 112).
  #[warnings="-notation-for-abbreviation"] Local Notation xs2 := (Z_to_bv 64 n0 : word).
  #[warnings="-notation-for-abbreviation"] Local Notation xs5 := (Z_to_bv 64 (p + -16) : word).
  (* [comment removed for export] *)
  #[warnings="-notation-for-abbreviation"] Local Notation CUR := (CURG rac spd s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 A m md p n0 stkobj lo hi xs2 xs5).
  #[warnings="-notation-for-abbreviation"] Local Notation it_cfg := (it_cfgG spd gp s10 s11 F fc).
  #[warnings="-notation-for-abbreviation"] Local Notation blk_cfg := (blk_cfgG spd gp s10 s11 F fc).
  Hypothesis VB : forall a, newblk p n0 a -> a < alloc_ceiling.
  (* [comment removed for export] *)
  Hypothesis STEP_PDM : forall (A1 : AState) (m1 : mem) (md1 : Model) (b0 : batch) (i : nat) (more : list batch) (scr : list byte)
      (ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) (c k n : Z),
    CUR A1 m1 md1 (Some (b0, i)) more scr ->
    nth_error (ba_entries b0) i = Some (QE (ChP (CP c k)) n) ->
    Z.of_nat (length (pk_chunks (a_cache A1 c))) = max_count c ->
    rg_mapped_fa (a_reg A1 c) < 4 * (Z.of_nat (length (rg_free (a_reg A1 c))) + max_count c / 2) ->
    KMORE rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A m md p n0 stkobj lo hi T xs2 xs5 A1 b0 i more scr ->
    KDONE rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A m md p n0 stkobj lo hi T xs2 xs5 A1 b0 i more scr ->
    srealizes rsegs (it_cfg A1 m1 md1 b0 (Z.of_nat i) dorec_callblk ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6') T.
  Hypothesis STEP_SEC : forall (A1 : AState) (m1 : mem) (md1 : Model) (b0 : batch) (i : nat) (more : list batch) (scr : list byte)
      (ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) (s : chunkS) (n : Z),
    CUR A1 m1 md1 (Some (b0, i)) more scr ->
    nth_error (ba_entries b0) i = Some (QE (ChS s) n) ->
    KMORE rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A m md p n0 stkobj lo hi T xs2 xs5 A1 b0 i more scr ->
    KDONE rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A m md p n0 stkobj lo hi T xs2 xs5 A1 b0 i more scr ->
    srealizes rsegs (it_cfg A1 m1 md1 b0 (Z.of_nat i) dorec_callblk ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6') T.
  Hypothesis STEP_BDM : forall (A1 : AState) (m1 : mem) (md1 : Model) (b0 : batch) (more : list batch) (scr : list byte)
      (ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s6' s7' s8' s9' : word),
    CUR A1 m1 md1 (Some (b0, length (ba_entries b0))) more scr ->
    Z.of_nat (length (pk_chunks (a_cache A1 kQuarantineBatchClass))) = max_count kQuarantineBatchClass ->
    rg_mapped_fa (a_reg A1 kQuarantineBatchClass) < 4 * (Z.of_nat (length (rg_free (a_reg A1 kQuarantineBatchClass))) + max_count kQuarantineBatchClass / 2) ->
    KHEAD rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A m md p n0 stkobj lo hi T xs2 xs5 A1 more scr ->
    KEXIT rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A m md p n0 stkobj lo hi T xs2 xs5 A1 ->
    srealizes rsegs (blk_cfg A1 m1 md1 b0 ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s6' s7' s8' s9') T.

  (* [comment removed for export] *)
  Local Ltac prefix :=
    cbn [cl_segs cl_free_pc LPA] in MI, KK |- *;
    (cbn [cl_segs cl_free_pc LPA] in MI |- *);
    (pose proof (ai_wf _ _ _ _ _ _ _ AI) as WF0);
    (pose proof (conj (ai_wf _ _ _ _ _ _ _ AI) (ai_repr _ _ _ _ _ _ _ AI) : WF A /\ @arepr _ DepotRepL LPA AL_pboth [] A (aview_of (pa_hull A) m)) as AR);
    (assert (SPH : uspd <= 2^47) by (clear -SPHI HISP; lia));
    (pose proof alloc_ceiling_val as CE);
    (pose proof (zr_word spd) as SPR; unfold inr64 in SPR);
    (pose proof (zr_word rac) as RAR; unfold inr64 in RAR);
    (destruct (free_li A p n0 HL) as (li & LU & LN));
    (destruct (free_n0 A m md p n0 AI HL) as [NR US]);
    (unfold REQ_MAX in NR);
    ((first [ pose proof ((free_geom A m md p n0 AI HL)) as dR_1; dand4 dR_1 as PAL PLO PCE PHI | destruct (free_geom A m md p n0 AI HL) as (PAL & PLO & PCE & PHI) ]));
    (pose proof (GEO A (aview_of (pa_hull A) m) p n0 li spd AR LU LN) as Gx0);
    (assert (PNB : 0x60a000 <= p + -16) by (clear -Gx0; lia)); (clear Gx0);
    ((first [ pose proof ((free_HDR A m md p n0 AI HL)) as dR_2; dex2 dR_2 as b1 ido; dand6 dR_2 as B1R B1M3 B1M IDR HDR CTXID | pose proof ((free_HDR A m md p n0 AI HL)) as dR_2; dand8 dR_2 as b1 ido B1R B1M3 B1M IDR HDR CTXID | destruct (free_HDR A m md p n0 AI HL) as (b1 & ido & B1R & B1M3 & B1M & IDR & HDR & CTXID) ]));
    (destruct (free_CTX0 A m md p n0 AI HL) as (old & CTX0));
    (pose proof (free_SHC A m md p n0 AI HL) as SHC);
    (pose proof (free_FCo A m md AI) as FCo);
    ((first [ pose proof ((free_TST A m md AI)) as dR_3; dex2 dR_3 as fr fd; dand3 dR_3 as FRR FDR TST | pose proof ((free_TST A m md AI)) as dR_3; dand5 dR_3 as fr fd FRR FDR TST | destruct (free_TST A m md AI) as (fr & fd & FRR & FDR & TST) ]));
    (pose proof (free_sep A m md p n0 AI HL) as SEPp);
    (cbv zeta in SEPp);
    ((first [ dand4 SEPp as SEP_pc SEP_pt SEP_pn SEP_pf | destruct SEPp as (SEP_pc & SEP_pt & SEP_pn & SEP_pf) ]));
    ((first [ pose proof ((hit_sep A m md AI)) as dR_5; dand13 dR_5 as SEP_thr SEP_ctx SEP_tc SEP_n0 SEP_f0 SEP_n0t SEP_f0t SEP_n0c SEP_f0c DN01 DN02 DF01 DF02 | pose proof (hit_sep A m md AI) as (SEP_thr & SEP_ctx & SEP_tc & SEP_n0 & SEP_f0 & SEP_n0t & SEP_f0t & SEP_n0c & SEP_f0c & DN01 & DN02 & DF01 & DF02) ]));
    ((first [ pose proof ((hit_place A m md AI)) as dR_6; dand7 dR_6 as TH1 TH2 THRA CT1 CT2 TOPR BOTR | pose proof (hit_place A m md AI) as (TH1 & TH2 & THRA & CT1 & CT2 & TOPR & BOTR) ]));
    ((first [ pose proof ((hit_depot_wf A m md AI)) as dR_7; dand5 dR_7 as DND DLEN _ DKEY _ | pose proof (hit_depot_wf A m md AI) as (DND & DLEN & _ & DKEY & _) ]));
    (pose proof (hit_DR A m md AI) as DR0);
    (pose proof (hit_TC A m md AI) as TC);
    (pose proof (hit_tsd A m md AI) as [TSD1 TSD2]);
    (assert (TSDL : 0x5e7b28 <= pa_tsd /\ pa_tsd + 8 <= 0x60a000) by (unfold pa_tsd; lia));
    (assert (LO : alloc_ceiling <= lo /\ lo <= uspd - 704) by (clear -CEIL LOW; lia));
    (* [comment removed for export] *)
    (assert (KL : (1 <= length key <= 255)%nat /\ depot_total (a_depot A) + 256 < kStackStoreBlockFrames) by
      (destruct (wfD A WF0) as (INC & ND & NN); pose proof (wfP A WF0) as PL; pose proof (wf_place_dkeys _ _ PL) as DK;
       destruct DK as (DK1 & DK2 & DK3); clear PL;
       assert (INC' : incl (a_depot A) (p_dkeys (a_pl A))) by (intros k Hk; exact (proj1 (Forall_forall _ _) INC k Hk));
       pose proof (depot_universe_bounds _ _ DK1 DK3 ND INC') as (L1 & _ & L3);
       split; [exact (proj1 (Forall_forall _ _) DK1 key KEYU)| unfold kStackStoreBlockFrames; clear -L1 L3; lia]));
    (destruct KL as [KL DTOT]);
    (assert (STOR : uspd <= stkobj /\ stkobj + 2064 <= 2^47) by (clear -STLO STHI HISP; lia));
    (assert (TPE : cl_tp LPA = wz TP) by reflexivity);
    (pose proof (Z_div_mod_eq_full (n0 + 7) 8) as NDE);
    (pose proof (Z.mod_pos_bound (n0 + 7) 8 ltac:(lia)) as ER);
    (assert (R8 : 8 * ((n0 + 7) / 8) - 8 < n0 <= 8 * ((n0 + 7) / 8)) by lia);
    (assert (IDR' : 0 <= snd (depot_putC (a_depot A) key) < 2^32) by (pose proof (depot_putC_id_range (a_depot A) key); lia)).

  (* [comment removed for export] *)
  Definition tailQt (tk : ftail) (qt' : list batch) : list batch := match tk with TN => qt' | _ => [] end.
  Definition tailQg (tk : ftail) (qt' qg : list batch) : list batch := match tk with TN => qg | _ => qg ++ qt' end.

  Lemma tailQ_entries : forall tk qt' qg e, In e (q_entries (tailQt tk qt' ++ tailQg tk qt' qg)) <-> In e (q_entries (qt' ++ qg)).
  Proof.
    intros tk qt' qg e. unfold q_entries. destruct tk; cbn [tailQt tailQg app]; [tauto| |]; rewrite !flat_map_app, !in_app_iff; tauto.
  Qed.
  Lemma tailQ_batches : forall tk qt' qg b, In b (tailQt tk qt' ++ tailQg tk qt' qg) <-> In b (qt' ++ qg).
  Proof. intros tk qt' qg b. destruct tk; cbn [tailQt tailQg app]; [tauto| |]; rewrite !in_app_iff; tauto. Qed.

  Theorem dealloc_fastR : forall tk : ftail,
    a_qthread A <> [] ->
    Z.of_nat (length (ba_entries (last (a_qthread A) (BA 0 [])))) < kQuarantineBatchCount ->
    match tk with
    | TN => False
    | T0 => kQuarantineCacheSize < q_bytes (a_qthread A) + n0 /\ a_qglobal A = [] /\ kQuarantineMaxSize < q_bytes (a_qthread A) + n0
    | TA => kQuarantineCacheSize < q_bytes (a_qthread A) + n0 /\ a_qglobal A <> [] /\ kQuarantineMaxSize < q_bytes (a_qglobal A) + (q_bytes (a_qthread A) + n0)
    end ->
    srealizes (cl_segs LPA) (mkCfg (dealloc_entry_ms rac spd gp (cl_tp LPA) t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p stkobj) md) T.
  Proof.
    intros tk QNE ROOM TKC. unfold dealloc_entry_ms. prefix.
    (* [comment removed for export] *)
    pose proof (free_QC A m md AI) as QC.
    set (qt := a_qthread A) in *. set (bl := last qt (BA 0 [])) in *. set (l := removelast qt).
    assert (EQT : qt = l ++ [bl]) by (symmetry; apply removelast_last_app; exact QNE).
    pose proof (free_LB A m md AI l bl EQT) as LBX. cbv zeta in LBX. (first [ dand7 LBX as LB SLOT LBM CNT LBL LBH LB16 | destruct LBX as (LB & SLOT & LBM & CNT & LBL & LBH & LB16) ]).
    destruct (SLOT ROOM) as [slot SL].
    set (lb := batch_addr (a_sb A) bl) in *. set (cnt := Z.of_nat (length (ba_entries bl))) in *.
    assert (QL : qc_last A qt = lb) by (unfold qc_last; subst lb bl; destruct qt; [congruence| reflexivity]).
    rewrite QL in QC.
    assert (NB0 : Z.of_nat (length qt) <> 0) by (destruct qt; [congruence| cbn; lia]).
    assert (QWF : forall e, In e (q_entries (qt ++ a_qglobal A)) -> 0 <= qe_n e).
    { intros e He. destruct (qentry_wf A (aview_of (pa_hull A) m) AR e He) as [N _]. lia. }
    assert (QBall : forall bs, (forall e, In e (q_entries bs) -> 0 <= qe_n e) -> Z.of_nat (length bs) * kQuarantineBatchBytes <= q_bytes bs).
    { clear. intros bs QW. induction bs as [|b r IH]; [cbn; lia|]. rewrite q_bytes_cons, batch_bytes_ebytes. cbn [length]. rewrite Nat2Z.inj_succ.
      assert (IHr : Z.of_nat (length r) * kQuarantineBatchBytes <= q_bytes r) by (apply IH; intros e He; apply QW; rewrite q_entries_cons; apply in_or_app; right; exact He).
      assert (EW : forall e, In e (ba_entries b) -> 0 <= qe_n e) by (intros e He; apply QW; rewrite q_entries_cons; apply in_or_app; left; exact He).
      assert (0 <= ebytes (ba_entries b)); [| lia].
      clear -EW. induction (ba_entries b) as [|e es IHe]; [cbn; lia|].
      rewrite ebytes_cons. unfold qe_bytes. pose proof (user_size_pos (qe_n e) ltac:(apply EW; left; reflexivity)).
      assert (0 <= ebytes es) by (apply IHe; intros e' He'; apply EW; right; exact He'). lia. }
    assert (LENB : Z.of_nat (length qt) * kQuarantineBatchBytes <= q_bytes qt).
    { apply QBall. intros e He. apply QWF. unfold q_entries in He |- *. rewrite flat_map_app. apply in_or_app. left. exact He. }
    assert (LENG : Z.of_nat (length (a_qglobal A)) * kQuarantineBatchBytes <= q_bytes (a_qglobal A)).
    { apply QBall. intros e He. apply QWF. unfold q_entries in He |- *. rewrite flat_map_app. apply in_or_app. right. exact He. }
    assert (QB0 : 0 <= q_bytes qt) by (clear -LENB; unfold kQuarantineBatchBytes in LENB; lia).
    assert (GQ0 : 0 <= q_bytes (a_qglobal A)) by (clear -LENG; unfold kQuarantineBatchBytes in LENG; lia).
    (* [comment removed for export] *)
    pose proof (wfQ A WF0) as WQ0. (first [ dand6 WQ0 as _ _ _ QTB QGB _ | destruct WQ0 as (_ & _ & _ & QTB & QGB & _) ]). change (a_qthread A) with qt in QTB. unfold kQuarantineCacheSize in QTB. unfold kQuarantineMaxSize in QGB.
    (* [comment removed for export] *)
    assert (INbl : In bl (qt ++ a_qglobal A)) by (apply in_or_app; left; rewrite EQT; apply in_or_app; right; left; reflexivity).
    pose proof (batch_carved A (aview_of (pa_hull A) m) AR bl INbl) as CBL.
    pose proof (KN A (aview_of (pa_hull A) m) p n0 li AR LU LN) as KNp. pose proof (known_carved A (aview_of (pa_hull A) m) AR _ _ KNp) as CVp.
    pose proof (GEO A (aview_of (pa_hull A) m) p n0 li spd AR LU LN) as G.
    assert (Alt : apart lb 8192 (p_thr (a_pl A)) 4096).
    { pose proof (carved_apart_thr A (aview_of (pa_hull A) m) AR _ CBL) as D. rewrite (proj1 (c24_range A (ba_idx bl))), (proj2 (c24_range A (ba_idx bl))) in D. subst lb. try (generalize alloc_ceiling_val); clear -D; try pose proof alloc_ceiling_val. unfold apart, AMallocA.apart, batch_addr, kQuarantineBatchBytes in *. lia. }
    assert (Alc : apart lb 8192 (p_ctx (a_pl A)) 0x10000).
    { pose proof (carved_apart_ctx A (aview_of (pa_hull A) m) AR _ CBL) as D. rewrite (proj1 (c24_range A (ba_idx bl))), (proj2 (c24_range A (ba_idx bl))) in D. subst lb. try (generalize alloc_ceiling_val); clear -D; try pose proof alloc_ceiling_val. unfold apart, AMallocA.apart, batch_addr, kQuarantineBatchBytes in *. lia. }
    assert (Aln : apart lb 8192 (p_nodes0 (a_pl A)) kDepotNodesBlock).
    { pose proof (carved_apart_n0 A (aview_of (pa_hull A) m) AR _ CBL) as D. rewrite (proj1 (c24_range A (ba_idx bl))), (proj2 (c24_range A (ba_idx bl))) in D. subst lb. try (generalize alloc_ceiling_val); clear -D; try pose proof alloc_ceiling_val. unfold apart, AMallocA.apart, batch_addr, kQuarantineBatchBytes in *. lia. }
    assert (Alf : apart lb 8192 (p_frames0 (a_pl A)) kStackStoreBlockBytes).
    { pose proof (carved_apart_f0 A (aview_of (pa_hull A) m) AR _ CBL) as D. rewrite (proj1 (c24_range A (ba_idx bl))), (proj2 (c24_range A (ba_idx bl))) in D. subst lb. try (generalize alloc_ceiling_val); clear -D; try pose proof alloc_ceiling_val. unfold apart, AMallocA.apart, batch_addr, kQuarantineBatchBytes in *. lia. }
    assert (Alp : apart lb 8192 (p + -16) (8 * ((n0 + 7) / 8) + 16)).
    { pose proof (carved_disjoint A (aview_of (pa_hull A) m) AR _ _ CBL CVp ltac:(intros E; exact (live_not_batch A (aview_of (pa_hull A) m) AR p li bl LU INbl (eq_sym E)))) as D.
      rewrite (proj1 (c24_range A (ba_idx bl))), (proj2 (c24_range A (ba_idx bl))) in D. subst lb.
      (first [ dand5 G as _ _ L1 L2 _ | destruct G as (_ & _ & L1 & L2 & _) ]). try (generalize alloc_ceiling_val); clear -D L1 L2; try pose proof alloc_ceiling_val. unfold apart, AMallocA.apart, batch_addr, kQuarantineBatchBytes in *. lia. }
    pose proof (batches_nodup A (aview_of (pa_hull A) m) AR) as BND0. change (a_qthread A) with qt in BND0. pose proof BND0 as BND. rewrite EQT, !map_app in BND. cbn [map] in BND.
    (* [comment removed for export] *)
    set (gn := Z.of_nat (length (a_qglobal A))). set (gf := qc_first A (a_qglobal A)). set (gl := qc_last A (a_qglobal A)). set (gqb := q_bytes (a_qglobal A)) in *.
    assert (TPRE : tail_pre tk gn gf gl gqb (wz 0) (aview_of (pa_hull A) m)).
    { destruct tk; cbn [tail_pre]; [exact I| |].
      - (first [ dand3 TKC as _ QGE _ | destruct TKC as (_ & QGE & _) ]). split; [exact (q_lockword A _ AR)|]. pose proof (q_global_hdr A _ AR) as X. subst gn gf gl gqb. rewrite QGE in X |- *. exact X.
      - (first [ dand3 TKC as _ QGN _ | destruct TKC as (_ & QGN & _) ]). split; [exact (q_lockword A _ AR)|]. split; [exact (q_global_hdr A _ AR)| exact (proj1 (q_gl_cell A _ AR QGN))]. }
    pose proof (qall_count_bound rac spd key KL A [] (aview_of (pa_hull A) m) (conj (WFT_of_WF A WF0) (proj2 AR))) as [CNTq CAPq].
    rewrite !length_app in CNTq. change (a_qthread A) with qt in CNTq.
    assert (GNB : Z.of_nat (length (a_qglobal A)) < 2^40) by (clear -CNTq CAPq; lia).
    assert (NBR40 : 0 <= Z.of_nat (length qt) < 2^40) by (clear -CNTq CAPq; lia).
    assert (TOK : tail_okR tk gn gqb (q_bytes qt + n0)).
    { destruct tk; cbn [tail_okR].
      - exact TKC.
      - (first [ dand3 TKC as T1 QGE T3 | destruct TKC as (T1 & QGE & T3) ]). subst gqb. rewrite QGE, q_bytes_nil. unfold kQuarantineCacheSize, kQuarantineMaxSize in *. clear -T1 T3 QTB NQ NR. lia.
      - (first [ dand3 TKC as T1 QGN T3 | destruct TKC as (T1 & QGN & T3) ]). subst gn gqb. unfold kQuarantineCacheSize, kQuarantineMaxSize, kQuarantineBatchBytes in *.
        assert (Z.of_nat (length (a_qglobal A)) <> 0) by (destruct (a_qglobal A); [congruence| cbn; lia]). clear -T1 T3 LENG H GQ0 NR QTB QGB NQ GNB. lia. }
    (* [comment removed for export] *)
    assert (QMM : ro_cells rsegs (aview_of (pa_hull A) m) (QINST + 64) [C8 (wz (2^28)); C8 (wz kQuarantineMinSize)]).
    { pose proof (ar_consts _ _ _ _ _ (proj2 AR)) as CC. unfold consts_repr_ in CC. cbv zeta in CC.
      assert (X1 : u64_at rsegs (aview_of (pa_hull A) m) (726360 + off_q_max_size) kQuarantineMaxSize) by tauto.
      assert (X2 : u64_at rsegs (aview_of (pa_hull A) m) (726360 + off_q_min_size) kQuarantineMinSize) by tauto.
      change (726360 + off_q_max_size) with (QINST + 64) in X1. change (726360 + off_q_min_size) with (QINST + 64 + 8) in X2. change kQuarantineMaxSize with (2^28) in X1.
      exact (ro_C8C8 _ _ _ _ X1 X2). }
    assert (QMR : 0 <= kQuarantineMinSize < 2^64) by (unfold kQuarantineMinSize; clear; lia).
    (* [comment removed for export] *)
    set (glb := last (a_qglobal A) (BA 0 [])).
    assert (GLX : a_qglobal A <> [] ->
              gl = batch_addr (a_sb A) glb /\ In glb (qt ++ a_qglobal A) /\ kHighMemBeg <= gl /\ gl + kQuarantineBatchBytes <= alloc_ceiling /\
              carved A (ChP (CP kQuarantineBatchClass (ba_idx glb))) /\ ba_idx glb <> ba_idx bl /\ (forall x, In x l -> ba_idx x <> ba_idx glb)).
    { intros QGN. (first [ pose proof ((q_gl_cell A _ AR QGN)) as dR_15; dand5 dR_15 as _ E INg R1 R2 | destruct (q_gl_cell A _ AR QGN) as (_ & E & INg & R1 & R2) ]). change (a_qthread A) with qt in INg.
      split; [exact E|]. split; [exact INg|]. split; [exact R1|]. split; [exact R2|]. split; [exact (batch_carved A (aview_of (pa_hull A) m) AR glb INg)|].
      assert (INg' : In glb (a_qglobal A)) by (subst glb; pattern (a_qglobal A) at 2; rewrite <- (removelast_last_app (a_qglobal A) (BA 0 []) QGN); apply in_or_app; right; left; reflexivity).
      split.
      - intros E2. apply (NoDup_app_In _ _ (ba_idx bl) BND); [apply in_or_app; right; left; reflexivity| rewrite <- E2; apply in_map; exact INg'].
      - intros x Hx E2. apply (NoDup_app_In _ _ (ba_idx x) BND); [apply in_or_app; left; apply in_map; exact Hx| rewrite E2; apply in_map; exact INg']. }
    assert (TAP : tail_apart tk gl (p_thr (a_pl A)) p ((n0 + 7) / 8) (p_nodes0 (a_pl A)) (p_frames0 (a_pl A)) [lb]).
    { destruct tk; cbn [tail_apart]; [exact I| exact I|]. (first [ dand3 TKC as _ QGN _ | destruct TKC as (_ & QGN & _) ]). (first [ pose proof ((GLX QGN)) as dR_17; dand7 dR_17 as E INg R1 R2 Cg NIb _ | destruct (GLX QGN) as (E & INg & R1 & R2 & Cg & NIb & _) ]).
      pose proof (carved_apart_thr A (aview_of (pa_hull A) m) AR _ Cg) as Dt. pose proof (carved_apart_n0 A (aview_of (pa_hull A) m) AR _ Cg) as Dn.
      pose proof (carved_apart_f0 A (aview_of (pa_hull A) m) AR _ Cg) as Df.
      pose proof (carved_disjoint A (aview_of (pa_hull A) m) AR _ _ Cg CVp ltac:(intros EE; exact (live_not_batch A (aview_of (pa_hull A) m) AR p li glb LU INg (eq_sym EE)))) as Dp.
      pose proof (carved_disjoint A (aview_of (pa_hull A) m) AR _ _ Cg CBL ltac:(intros EE; injection EE as EE; exact (NIb EE))) as Dl.
      rewrite (proj1 (c24_range A (ba_idx glb))), (proj2 (c24_range A (ba_idx glb))) in Dt, Dn, Df, Dp, Dl. rewrite (proj1 (c24_range A (ba_idx bl))), (proj2 (c24_range A (ba_idx bl))) in Dl.
      (first [ dand5 G as _ _ L1 L2 _ | destruct G as (_ & _ & L1 & L2 & _) ]).
      subst lb. clear -E R1 R2 Dt Dn Df Dp Dl L1 L2 CE. unfold apart, AMallocA.apart, batch_addr, kQuarantineBatchBytes in *.
      OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try lia. constructor; [lia| constructor]. }
    (* [comment removed for export] *)
    assert (NBR : 0 <= Z.of_nat (length qt) < 2^64) by (clear -LENB QTB NR; unfold kQuarantineBatchBytes in *; lia).
    assert (FBR : 0 <= qc_first A qt < 2^64).
    { unfold qc_first. destruct qt as [|b0 r] eqn:Eq; [lia|]. (first [ pose proof ((batch_range A (aview_of (pa_hull A) m) AR b0 ltac:(change (a_qthread A) with qt; rewrite Eq; left; reflexivity))) as dR_19; dand3 dR_19 as X1 X2 _ | pose proof (batch_range A (aview_of (pa_hull A) m) AR b0 ltac:(change (a_qthread A) with qt; rewrite Eq; left; reflexivity)) as (X1 & X2 & _) ]).
      clear -X1 X2 CE. unfold kQuarantineBatchBytes in *. kung_all. lia. }
    assert (CNR : 0 <= cnt < 1021) by (try (generalize alloc_ceiling_val); clear -ROOM; try pose proof alloc_ceiling_val; subst cnt; unfold kQuarantineBatchCount in ROOM; lia).
    assert (LBH' : lb + 8192 <= alloc_ceiling) by (try (generalize alloc_ceiling_val); clear -LBH CE; try pose proof alloc_ceiling_val; unfold kQuarantineBatchBytes in LBH; lia).
    assert (PHI' : p + 8 * ((n0 + 7) / 8) <= alloc_ceiling) by (try (generalize alloc_ceiling_val); clear -PHI CE; try pose proof alloc_ceiling_val; lia).
    assert (NR' : 1 <= n0 < 2^32) by (try (generalize alloc_ceiling_val); clear -NR; try pose proof alloc_ceiling_val; lia).
    pose proof (free_chitR_fast rac spd gp (cl_tp LPA) t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
                  (aview_of (pa_hull A) m) lo p n0 b1 pa_tsd (p_ctx (a_pl A)) (p_thr (a_pl A))
                  ((n0 + 7) / 8) (p_nodes0 (a_pl A)) (p_frames0 (a_pl A)) fr fd stkobj (a_depot A) key old (shpat n0)
                  MI ST LO SPH RA2 TPE PAL PLO PNB PHI' NR' NQ R8 B1R B1M3 HDR CTX0 SHC FCo
                  (hit_PCo A m md AI) TC (hit_TH0 A m md AI) (hit_CT8 A m md AI) TSDL
                  TST FRR FDR DR0 DND DLEN DTOT (conj DN01 DN02) (conj DF01 DF02) STO TRW STOR KL KR SEP_pc SEP_pt SEP_pn SEP_pf SEP_n0t SEP_f0t SEP_n0c SEP_f0c SEP_tc
                  tk gn gf gl gqb (wz 0) (Z.of_nat (length qt)) (qc_first A qt) lb (q_bytes qt) 0 (batch_bytes bl) cnt slot kQuarantineMinSize
                  TPRE TOK TAP QMR QMM NB0 NBR40 FBR CNR QB0 LBL LBH' Alt Alp Alc Aln Alf QC LB SL) as EV.
    (* [comment removed for export] *)
    destruct (asI_minv A m md AI) as [HMI HH].
    eapply (srz_evt_restrict rsegs (pa_hull A) (asI_hull_segs A m md AI) pa_wx _ (pa_eager A) _ _ md T HMI HH).
    { rewrite restrict_MS. exact EV. }
    intros msr' md' HQ HI' Hsame Hcl.
    (first [ dex12 HQ as t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' v'; dand14 HQ as -> MU WM' MI' ST' PFR' Ptst Phdr Pctx Psh Pdr Plb Pslot TPOST | dand26 HQ as t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' v' -> MU WM' MI' ST' PFR' Ptst Phdr Pctx Psh Pdr Plb Pslot TPOST | destruct HQ as (t0' & t1' & t2' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & v' & -> & MU & WM' & MI' & ST' & PFR' & Ptst & Phdr & Pctx & Psh & Pdr & Plb & Pslot & TPOST) ]).
    rewrite unrestrict_MS. cbn [ms_mem] in Hcl.
    pose proof (same_but_materialized_frame _ _ Hsame) as FRM.
    assert (VIEW : aview_of (pa_hull A) (munrestrict (hidc (pa_hull A)) m v') = v').
    { unfold aview_of. rewrite mrestrict_munrestrict. apply mrestrict_clean_id. exact Hcl. }
    assert (NN : forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> a < 2^64 -> aview_of (pa_hull A) m (wz a) <> None -> v' (wz a) <> None).
    { intros a H0 H1 H2. apply (wmono_NN _ _ a WM'); lia. }
    (* [comment removed for export] *)
    pose proof G as G'. (first [ dand18 G' as PM CL1 L1 L2 CL2 _ R8' PU T1 T2 N1 N2 F1 F2 S1 S2 CEQ _ | destruct G' as (PM & CL1 & L1 & L2 & CL2 & _ & R8' & PU & T1 & T2 & N1 & N2 & F1 & F2 & S1 & S2 & CEQ & _) ]).
    (first [ pose proof ((GEOP A (aview_of (pa_hull A) m) p n0 li AR LU LN)) as dR_22; dand4 dR_22 as Gc Gt Gn Gf | pose proof (GEOP A (aview_of (pa_hull A) m) p n0 li AR LU LN) as (Gc & Gt & Gn & Gf) ]). aobj_lin1 Gc. aobj_lin1 Gt. aobj_lin1 Gn. aobj_lin1 Gf.
    pose proof (GEOS A (aview_of (pa_hull A) m) p n0 li spd AR LU LN) as Gs. unfold kLowShadowMapBeg, kHighShadowMapBeg, kHighMemBeg in Gs.
    set (BX := fun a => (lb <= a < lb + 24) \/ (lb + 24 + 8 * cnt <= a < lb + 32 + 8 * cnt)
                        \/ (tk <> TN /\ gq_blk a) \/ (tk = TA /\ gl <= a < gl + 8) \/ (a_ia_inited A = false /\ ia_blk a)).
    assert (BXW : forall a, BX a ->
         (exists b, In b (a_qthread A ++ a_qglobal A) /\ batch_addr (a_sb A) b <= a < batch_addr (a_sb A) b + kQuarantineBatchBytes)
      \/ (p_thr (a_pl A) + 2128 <= a < p_thr (a_pl A) + 2208) \/ (p_thr (a_pl A) + 2784 <= a < p_thr (a_pl A) + 2792)
      \/ (exists k, p_cached_ (a_cache A) kQuarantineBatchClass k /\
                    chunk_addr (a_sb A) kQuarantineBatchClass k <= a < chunk_addr (a_sb A) kQuarantineBatchClass k + kQuarantineBatchBytes)
      \/ xblk a).
    { intros a Ha. subst BX. cbv beta in Ha. destruct Ha as [Ha|[Ha|[[_ Ha]|[[Htk Ha]|[_ Ha]]]]].
      - left. exists bl. split; [exact INbl|]. subst lb. clear -Ha CNR. unfold kQuarantineBatchBytes. lia.
      - left. exists bl. split; [exact INbl|]. subst lb. clear -Ha CNR. unfold kQuarantineBatchBytes. lia.
      - do 4 right. right. exact Ha.
      - subst tk. (first [ dand3 TKC as _ QGN _ | destruct TKC as (_ & QGN & _) ]). (first [ pose proof ((GLX QGN)) as dR_24; dand3 dR_24 as E INg _ | destruct (GLX QGN) as (E & INg & _) ]). left. exists glb. split; [exact INg|]. rewrite <- E. clear -Ha. unfold kQuarantineBatchBytes. lia.
      - do 4 right. left. exact Ha. }
    assert (MU' : forall a, 0 <= a < 2^64 -> ~ W0 lo uspd (p_thr (a_pl A)) p ((n0 + 7) / 8) (p_nodes0 (a_pl A)) (p_frames0 (a_pl A)) a ->
                   ~ BX a -> v' (wz a) = aview_of (pa_hull A) m (wz a)).
    { intros a Ha NW NB. apply MU. rewrite unsigned_lit by lia. unfold free_chitR_fast_W, free_cprefix_W, free_coreR_fast_W. rewrite !outside_app.
      unfold W0 in NW. subst BX. cbv beta in NB.
      split; [| split].
      - cbn [outside]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; intros X; apply NW; clear -X LO; lia.
      - cbn [outside]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; intros X; [apply NW| apply NB| apply NB]; clear -X; lia.
      - destruct tk; cbn [ctail_W]; [exact I| |]; unfold free_cdtail_W, free_cdtail_WA, QINST; cbn [outside]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; intros X;
          first [apply NW; clear -X LO; lia | apply NB; right; right; first [left; split; [discriminate| unfold gq_blk; clear -X; lia] | right; left; split; [reflexivity| clear -X; lia]]]. }
    (* [comment removed for export] *)
    assert (Punw : rw_cells rsegs v' (p_thr (a_pl A) + off_th_unwinding) [C1 (Z_to_bv 8 0)]).
    { pose proof Alt as Dt. unfold apart, AMallocA.apart in Dt.
      assert (Dg : tk = TA -> gl + 24 <= p_thr (a_pl A) \/ p_thr (a_pl A) + 4096 <= gl).
      { intros ->. (first [ dand6 TAP as _ _ _ _ Agt _ | destruct TAP as (_ & _ & _ & _ & Agt & _) ]). clear -Agt. unfold apart, AMallocA.apart in Agt. lia. }
      eapply rw_cells_transport; [exact (hit_TUNW A m md AI)| exact MU| exact WM'|].
      unfold free_chitR_fast_W, free_cprefix_W, free_coreR_fast_W, off_th_unwinding.
      pose proof SEP_pt as Dp. pose proof SEP_n0t as Dn. pose proof SEP_f0t as Df. unfold apart, AMallocA.apart in Dp, Dn, Df.
      destruct tk; [| | specialize (Dg eq_refl)]; cbn [ctail_W free_cdtail_W free_cdtail_WA app disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]; unfold QINST;
        clear -Dt Dp Dn Df Dg T1 T2 L1 L2 CL1 CE CEIL LOW N1 F1 S1 S2 Gc Gt Gn Gf Gs CNR LBL NR R8; kung_all; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia. }
    (* [comment removed for export] *)
    assert (AGlb : forall x a', In x l -> batch_addr (a_sb A) x <= a' < batch_addr (a_sb A) x + kQuarantineBatchBytes -> v' (wz a') = aview_of (pa_hull A) m (wz a')).
    { intros x a' Hx Ha'.
      assert (INx : In x (a_qthread A ++ a_qglobal A)) by (change (a_qthread A) with qt; rewrite EQT; apply in_or_app; left; apply in_or_app; left; exact Hx).
      pose proof (batch_carved A (aview_of (pa_hull A) m) AR x INx) as Cx.
      pose proof (carved_apart_thr A (aview_of (pa_hull A) m) AR _ Cx) as Dt. pose proof (carved_apart_n0 A (aview_of (pa_hull A) m) AR _ Cx) as Dn. pose proof (carved_apart_f0 A (aview_of (pa_hull A) m) AR _ Cx) as Df.
      pose proof (carved_disjoint A (aview_of (pa_hull A) m) AR _ _ Cx CVp ltac:(intros E; exact (live_not_batch A (aview_of (pa_hull A) m) AR p li x LU INx (eq_sym E)))) as Dp.
      assert (NI : ba_idx x <> ba_idx bl).
      { intros E. apply stdpp.list_relations.list.NoDup_app in BND as (BND1 & _ & _).
        exact (NoDup_app_In _ _ (ba_idx x) BND1 ltac:(apply in_map; exact Hx) ltac:(rewrite E; left; reflexivity)). }
      pose proof (carved_disjoint A (aview_of (pa_hull A) m) AR _ _ Cx CBL ltac:(intros E; injection E as E; exact (NI E))) as Dl.
      rewrite (proj1 (c24_range A (ba_idx x))), (proj2 (c24_range A (ba_idx x))) in Dt, Dn, Df, Dp, Dl. rewrite (proj1 (c24_range A (ba_idx bl))), (proj2 (c24_range A (ba_idx bl))) in Dl.
      (first [ pose proof ((batch_range A (aview_of (pa_hull A) m) AR x INx)) as dR_26; dand3 dR_26 as Rx1 Rx2 _ | pose proof (batch_range A (aview_of (pa_hull A) m) AR x INx) as (Rx1 & Rx2 & _) ]).
      (* [comment removed for export] *)
      assert (Dg : tk = TA -> gl + 8 <= batch_addr (a_sb A) x \/ batch_addr (a_sb A) x + kQuarantineBatchBytes <= gl).
      { intros ->. (first [ dand3 TKC as _ QGN _ | destruct TKC as (_ & QGN & _) ]). (first [ pose proof ((GLX QGN)) as dR_28; dand7 dR_28 as E _ _ _ Cg _ NIl | destruct (GLX QGN) as (E & _ & _ & _ & Cg & _ & NIl) ]).
        pose proof (carved_disjoint A (aview_of (pa_hull A) m) AR _ _ Cx Cg ltac:(intros EE; injection EE as EE; exact (NIl x Hx EE))) as D.
        rewrite (proj1 (c24_range A (ba_idx x))), (proj2 (c24_range A (ba_idx x))), (proj1 (c24_range A (ba_idx glb))), (proj2 (c24_range A (ba_idx glb))) in D.
        clear -D E. unfold batch_addr, kQuarantineBatchBytes in *. lia. }
      apply MU'; [try (generalize alloc_ceiling_val); clear -Ha' Rx1 Rx2 CE; try pose proof alloc_ceiling_val; unfold kQuarantineBatchBytes in *; kung_all; lia| |].
      - unfold W0. subst lb. clear -Ha' Dt Dn Df Dp Rx1 Rx2 L1 L2 CE CEIL S2 NR Gc Gt Gn Gf Gs; try pose proof alloc_ceiling_val. unfold batch_addr, kQuarantineBatchBytes in *. kung_all. intros [X|[X|[X|[X|[X|[X|[X|[X|[X|X]]]]]]]]]; lia.
      - subst BX lb. cbv beta. intros [X|[X|[[_ X]|[[Htk X]|[_ X]]]]].
        + clear -Ha' Dl CNR X. unfold batch_addr, kQuarantineBatchBytes in *. lia.
        + clear -Ha' Dl CNR X. unfold batch_addr, kQuarantineBatchBytes in *. lia.
        + clear -Ha' Rx1 X. unfold gq_blk, batch_addr, kQuarantineBatchBytes in *. kung_all. lia.
        + specialize (Dg Htk). clear -Ha' Dg X. unfold kQuarantineBatchBytes in *. lia.
        + clear -Ha' Rx1 X. unfold ia_blk, batch_addr, kQuarantineBatchBytes in *. kung_all. lia. }
    assert (Dgl : tk = TA -> gl + 8 <= lb \/ lb + 8192 <= gl).
    { intros ->. (first [ dand3 TKC as _ QGN _ | destruct TKC as (_ & QGN & _) ]). (first [ pose proof ((GLX QGN)) as dR_30; dand7 dR_30 as E _ _ _ Cg NIb _ | destruct (GLX QGN) as (E & _ & _ & _ & Cg & NIb & _) ]).
      pose proof (carved_disjoint A (aview_of (pa_hull A) m) AR _ _ Cg CBL ltac:(intros EE; injection EE as EE; exact (NIb EE))) as D.
      rewrite (proj1 (c24_range A (ba_idx glb))), (proj2 (c24_range A (ba_idx glb))), (proj1 (c24_range A (ba_idx bl))), (proj2 (c24_range A (ba_idx bl))) in D.
      subst lb. clear -D E. unfold batch_addr, kQuarantineBatchBytes in *. lia. }
    assert (AGslot : forall i, 0 <= i < cnt -> forall a', lb + 24 + 8 * i <= a' < lb + 32 + 8 * i -> v' (wz a') = aview_of (pa_hull A) m (wz a')).
    { intros i Hi a' Ha'. pose proof Alt as Dt. pose proof Aln as Dn. pose proof Alf as Df. pose proof Alp as Dp. unfold apart, AMallocA.apart in Dt, Dn, Df, Dp.
      apply MU'; [try (generalize alloc_ceiling_val); clear -Ha' Hi LBL LBH CE CNR; try pose proof alloc_ceiling_val; unfold kQuarantineBatchBytes in *; kung_all; lia| |].
      - unfold W0. clear -Ha' Hi Dt Dn Df Dp LBL LBH L1 L2 CE CEIL CNR S2 NR Gc Gt Gn Gf Gs; try pose proof alloc_ceiling_val. unfold kQuarantineBatchBytes in *. kung_all. intros [X|[X|[X|[X|[X|[X|[X|[X|[X|X]]]]]]]]]; lia.
      - subst BX. cbv beta. intros [X|[X|[[_ X]|[[Htk X]|[_ X]]]]].
        + clear -Ha' Hi X. lia.
        + clear -Ha' Hi X. lia.
        + clear -Ha' Hi CNR LBL X. unfold gq_blk in *. kung_all. lia.
        + specialize (Dgl Htk). clear -Ha' Hi CNR Dgl X. lia.
        + clear -Ha' Hi CNR LBL X. unfold ia_blk in *. kung_all. lia. }
    assert (AG24 : forall a', p_thr (a_pl A) + off_th_per_class kQuarantineBatchClass <= a' < p_thr (a_pl A) + off_th_per_class kQuarantineBatchClass + 80 -> v' (wz a') = aview_of (pa_hull A) m (wz a')).
    { intros a' Ha'. offs_h Ha'. cbv beta in Ha'. unfold kQuarantineBatchClass in Ha'. pose proof Alt as Dt. unfold apart, AMallocA.apart in Dt.
      assert (Dgt : tk = TA -> p_thr (a_pl A) + 4096 <= gl \/ gl + 8192 <= p_thr (a_pl A)).
      { intros ->. (first [ dand3 TKC as _ QGN _ | destruct TKC as (_ & QGN & _) ]). (first [ pose proof ((GLX QGN)) as dR_32; dand6 dR_32 as E _ _ _ Cg _ | destruct (GLX QGN) as (E & _ & _ & _ & Cg & _) ]).
        pose proof (carved_apart_thr A (aview_of (pa_hull A) m) AR _ Cg) as D. rewrite (proj1 (c24_range A (ba_idx glb))), (proj2 (c24_range A (ba_idx glb))) in D.
        clear -D E. unfold batch_addr, kQuarantineBatchBytes in *. lia. }
      apply MU'; [try (generalize alloc_ceiling_val); clear -Ha' T1 T2 CE Gc Gt Gn Gf Gs; try pose proof alloc_ceiling_val; kung_all; lia| |].
      - unfold W0. clear -Ha' Dt T1 T2 L1 L2 CL1 CE CEIL N1 F1 S2 SEP_n0t SEP_f0t SEP_pt NR Gc Gt Gn Gf Gs; try pose proof alloc_ceiling_val. unfold apart, AMallocA.apart in *. kung_all. intros [X|[X|[X|[X|[X|[X|[X|[X|[X|X]]]]]]]]]; lia.
      - subst BX. cbv beta. intros [X|[X|[[_ X]|[[Htk X]|[_ X]]]]].
        + clear -Ha' Dt CNR X. lia.
        + clear -Ha' Dt CNR X. lia.
        + clear -Ha' Gt X. unfold gq_blk in *. kung_all. lia.
        + specialize (Dgt Htk). clear -Ha' Dgt X. lia.
        + clear -Ha' Gt X. unfold ia_blk in *. kung_all. lia. }
    (* [comment removed for export] *)
    set (fe := free_entry li). set (qt' := qpush_last qt fe).
    assert (FE : fe = QE (li_chunk li) n0) by (subst fe; unfold free_entry; rewrite LN; reflexivity).
    assert (QT'S : qt' = l ++ [BA (ba_idx bl) (ba_entries bl ++ [fe])]) by (subst qt'; exact (qpush_last_shape qt fe QNE)).
    (first [ pose proof ((ar_quar _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI))) as dR_33; dand3 dR_33 as QT0 QG0 _ | destruct (ar_quar _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI)) as (QT0 & QG0 & _) ]). (first [ dand5 QT0 as _ _ _ _ BR0 | destruct QT0 as (_ & _ & _ & _ & BR0) ]). change (p_sb (a_pl A)) with (a_sb A) in BR0. change (a_qthread A) with qt in BR0.
    (first [ dand5 QG0 as _ _ _ _ BRG0 | destruct QG0 as (_ & _ & _ & _ & BRG0) ]). change (p_sb (a_pl A)) with (a_sb A) in BRG0.
    rewrite EQT in BR0.
    pose proof (batches_repr_last _ _ l bl BR0) as OLDL. cbv zeta in OLDL. (first [ dand5 OLDL as On Os Oc Oe Om | destruct OLDL as (On & Os & Oc & Oe & Om) ]).
    assert (Pbr : batches_repr LPA v' (a_sb A) qt').
    { rewrite QT'S. apply (batches_repr_relast (aview_of (pa_hull A) m) v' (a_sb A) l bl); [exact BR0| reflexivity| | exact AGlb|].
      - intros x Hx i Hi. assert (INx : In x (a_qthread A ++ a_qglobal A)).
        { change (a_qthread A) with qt. rewrite EQT. apply in_or_app. left. destruct Hx as [Hx| ->]; [apply in_or_app; left; exact Hx| apply in_or_app; right; left; reflexivity]. }
        pose proof (batch_known A (aview_of (pa_hull A) m) AR x INx) as [_ LX]. unfold kQuarantineBatchCount in LX. lia.
      - unfold batch_addr. cbn [ba_idx ba_entries]. change (chunk_addr (a_sb A) kQuarantineBatchClass (ba_idx bl)) with lb.
        destruct Plb as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
        apply bytes_at_app in B as [B0 B]. apply bytes_at_app in B as [B1 B2]. rewrite !length_le8 in B1, B2. unfold u64_at. offs.
        split; [rewrite Z.add_0_r; exact B0|]. split.
        { replace (batch_bytes {| ba_idx := ba_idx bl; ba_entries := ba_entries bl ++ [fe] |}) with (batch_bytes bl + n0).
          2:{ rewrite !batch_bytes_ebytes. cbn [ba_entries]. rewrite entries_bytes_app, ebytes_cons. cbn [ebytes fold_right].
              subst fe. unfold free_entry, qe_bytes. cbn [qe_n]. rewrite LN, US. lia. }
          replace (lb + 8) with (lb + Z.of_nat 8) by lia. exact B1. }
        split.
        { rewrite length_app. cbn [length]. replace (Z.of_nat (length (ba_entries bl) + 1)) with (cnt + 1) by (subst cnt; lia).
          replace (lb + 16) with (lb + Z.of_nat 8 + Z.of_nat 8) by lia. exact B2. }
        split.
        { intros i e' Hi. destruct (Nat.lt_ge_cases i (length (ba_entries bl))) as [LT|GE].
          - rewrite nth_error_app1 in Hi by exact LT. pose proof (Oe i e' Hi) as X. offs_h X.
            eapply u64_at_agree; [exact X|]. intros j Hj. apply (AGslot (Z.of_nat i)); subst cnt; lia.
          - rewrite nth_error_app2 in Hi by exact GE. destruct (i - length (ba_entries bl))%nat eqn:EI; [| destruct n; discriminate]. cbn in Hi. injection Hi as <-.
            assert (IE : Z.of_nat i = cnt) by (subst cnt; lia). rewrite IE. rewrite FE. cbn [qe_chunk qe_n].
            destruct Pslot as [[_ BS] _]. cbn [cells_bytes cbytes] in BS. rewrite app_nil_r in BS.
            unfold hdr_of. rewrite <- PU. unfold kChunkHeaderSize. replace (p - 16) with (p + -16) by lia. replace (lb + (24 + 8 * cnt)) with (lb + 24 + 8 * cnt) by lia. exact BS. }
        apply (mapped_N (aview_of (pa_hull A) m) v' NN); [try (generalize alloc_ceiling_val); clear -LBL; try pose proof alloc_ceiling_val; kung_all; lia|try (generalize alloc_ceiling_val); clear -LBL; try pose proof alloc_ceiling_val; kung_all; lia| try (generalize alloc_ceiling_val); clear -LBH CE; try pose proof alloc_ceiling_val; unfold kQuarantineBatchBytes in *; lia| exact LBM]. }
    pose proof (cache_line_P A (aview_of (pa_hull A) m) v' AR NN (a_cache A) kQuarantineBatchClass ltac:(unfold kQuarantineBatchClass; lia) eq_refl AG24) as Pl24.
    (* [comment removed for export] *)
    assert (HQ' : Z.of_nat (length qt') = Z.of_nat (length qt) /\ qc_first A qt' = qc_first A qt /\ qc_last A qt' = lb /\ q_bytes qt' = q_bytes qt + n0).
    { subst qt'. rewrite (qpush_last_length _ _ QNE), (qc_first_push_last A _ _ QNE), (qc_last_push_last A _ _ QNE), (qpush_last_bytes _ _ QNE), QL.
      replace (qe_bytes fe) with n0 by (subst fe; unfold free_entry, qe_bytes; cbn [qe_n]; rewrite LN, US; reflexivity). OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity. }
    (first [ dand4 HQ' as HQ1 HQ2 HQ3 HQ4 | destruct HQ' as (HQ1 & HQ2 & HQ3 & HQ4) ]).
    assert (QT'NE : qt' <> []) by (rewrite QT'S; intros X; apply app_eq_nil in X; destruct X; discriminate).
    (* [comment removed for export] *)
    set (qt1 := tailQt tk qt'). set (qg1 := tailQg tk qt' (a_qglobal A)).
    set (A' := freeA A p qt1 qg1 (a_cache A) (fst (depot_putC (a_depot A) key)) true).
    (* [comment removed for export] *)
    assert (Pqc' : rw_cells rsegs v' (p_thr (a_pl A) + 80)
              [C8 (wz (Z.of_nat (length qt1))); C8 (wz (qc_first A qt1)); C8 (wz (qc_last A qt1)); C8 (wz (q_bytes qt1))]).
    { subst qt1. destruct tk; cbn [tailQt tail_postR] in TPOST |- *.
      - destruct TPOST.
      - destruct TPOST as (X & _). exact X.
      - destruct TPOST as (X & _). exact X. }
    assert (Pbr' : batches_repr LPA v' (a_sb A) qt1) by (subst qt1; destruct tk; cbn [tailQt]; [exact Pbr| exact I| exact I]).
    assert (NGQ : tk = TN -> forall a, BX a -> ~ gq_blk a).
    { intros -> a HB GQ. subst BX. cbv beta in HB. destruct HB as [X|[X|[[X _]|[[X _]|[_ X]]]]]; [| | exact (X eq_refl)| discriminate|].
      - clear -X GQ LBL CNR. unfold gq_blk, kHighMemBeg in *. lia.
      - clear -X GQ LBL CNR. unfold gq_blk, kHighMemBeg in *. lia.
      - clear -X GQ. unfold gq_blk, ia_blk in *. lia. }
    assert (NBXg : forall g a, In g (a_qglobal A) -> batch_addr (a_sb A) g <= a < batch_addr (a_sb A) g + kQuarantineBatchBytes -> tk = TN -> ~ BX a).
    { intros g a Hg Ha -> HB. assert (INg : In g (a_qthread A ++ a_qglobal A)) by (apply in_or_app; right; exact Hg).
      assert (NI : ba_idx g <> ba_idx bl).
      { intros E. apply (NoDup_app_In _ _ (ba_idx bl) BND); [apply in_or_app; right; left; reflexivity| rewrite <- E; apply in_map; exact Hg]. }
      pose proof (carved_disjoint A (aview_of (pa_hull A) m) AR _ _ (batch_carved A (aview_of (pa_hull A) m) AR g INg) CBL ltac:(intros E; injection E as E; exact (NI E))) as Dl.
      rewrite (proj1 (c24_range A (ba_idx g))), (proj2 (c24_range A (ba_idx g))), (proj1 (c24_range A (ba_idx bl))), (proj2 (c24_range A (ba_idx bl))) in Dl.
      pose proof (batch_range A (aview_of (pa_hull A) m) AR g INg) as (Rg1 & _).
      subst BX lb. cbv beta in HB. destruct HB as [X|[X|[[X _]|[[X _]|[_ X]]]]]; [| | exact (X eq_refl)| discriminate|].
      - clear -Ha Dl CNR X. unfold batch_addr, kQuarantineBatchBytes in *. lia.
      - clear -Ha Dl CNR X. unfold batch_addr, kQuarantineBatchBytes in *. lia.
      - clear -Ha Rg1 X. unfold ia_blk, batch_addr, kQuarantineBatchBytes in *. kung_all. lia. }
    assert (Pqcg : let I := al_instance AL_pboth + off_q_cache_list_size in
              u64_at rsegs v' (I + 0) (Z.of_nat (length qg1)) /\
              u64_at rsegs v' (I + 8) (match qg1 with [] => 0 | b :: _ => batch_addr (a_sb A) b end) /\
              u64_at rsegs v' (I + 16) (match qg1 with [] => 0 | _ => batch_addr (a_sb A) (last qg1 (BA 0 [])) end) /\
              u64_at rsegs v' (I + 24) (q_bytes qg1)).
    { subst qg1. destruct tk; cbn [tailQg tail_postR] in TPOST |- *.
      - destruct TPOST.
      - (first [ dand3 TKC as _ QGE _ | destruct TKC as (_ & QGE & _) ]). (first [ dand4 TPOST as _ _ X _ | destruct TPOST as (_ & _ & X & _) ]). rewrite QGE. cbn [app]. change (al_instance AL_pboth + off_q_cache_list_size) with (QINST + 160).
        subst gqb. rewrite QGE in X. rewrite q_bytes_nil, Z.add_0_l in X. rewrite <- HQ1, <- HQ2, <- HQ4 in X.
        apply u64x4_of_rw.
        replace (match qt' with [] => 0 | b :: _ => batch_addr (a_sb A) b end) with (qc_first A qt') by (unfold qc_first; destruct qt'; reflexivity).
        replace (match qt' with [] => 0 | _ :: _ => batch_addr (a_sb A) (last qt' (BA 0 [])) end) with lb by (rewrite <- HQ3; unfold qc_last; destruct qt'; [congruence| reflexivity]).
        exact X.
      - (first [ dand3 TKC as _ QGN _ | destruct TKC as (_ & QGN & _) ]). (first [ dand5 TPOST as _ _ X _ _ | destruct TPOST as (_ & _ & X & _ & _) ]). change (al_instance AL_pboth + off_q_cache_list_size) with (QINST + 160).
        apply u64x4_of_rw. rewrite length_app, Nat2Z.inj_add, q_bytes_app.
        replace (match a_qglobal A ++ qt' with [] => 0 | b :: _ => batch_addr (a_sb A) b end) with gf by (subst gf; unfold qc_first; destruct (a_qglobal A); [congruence| reflexivity]).
        replace (match a_qglobal A ++ qt' with [] => 0 | _ :: _ => batch_addr (a_sb A) (last (a_qglobal A ++ qt') (BA 0 [])) end) with lb.
        2:{ rewrite QT'S, app_assoc, last_last. unfold batch_addr. cbn [ba_idx]. subst lb. unfold batch_addr. destruct (a_qglobal A ++ l); reflexivity. }
        subst gn gqb. rewrite <- HQ1, <- HQ4 in X. exact X. }
    assert (Pbrg : batches_repr LPA v' (a_sb A) qg1).
    { subst qg1. destruct tk; cbn [tailQg tail_postR] in TPOST |- *.
      - destruct TPOST.
      - (first [ dand3 TKC as _ QGE _ | destruct TKC as (_ & QGE & _) ]). rewrite QGE. exact Pbr.
      - (first [ dand3 TKC as _ QGN _ | destruct TKC as (_ & QGN & _) ]). (first [ dand5 TPOST as _ _ _ Pgl _ | destruct TPOST as (_ & _ & _ & Pgl & _) ]). (first [ pose proof ((GLX QGN)) as dR_45; dand7 dR_45 as E INg R1 R2 Cg NIb NIl | destruct (GLX QGN) as (E & INg & R1 & R2 & Cg & NIb & NIl) ]).
        apply breprN_cat; [| exact Pbr].
        replace (hd_addr (a_sb A) qt') with (qc_first A qt) by (rewrite <- HQ2; unfold qc_first, hd_addr; destruct qt'; reflexivity).
        pattern (a_qglobal A) at 1. rewrite <- (removelast_last_app (a_qglobal A) (BA 0 []) QGN). fold glb.
        apply (breprN_relink (aview_of (pa_hull A) m) v' (a_sb A) (removelast (a_qglobal A)) glb 0).
        + apply breprN_0. unfold glb. rewrite (removelast_last_app (a_qglobal A) (BA 0 []) QGN). exact BRG0.
        + intros x Hx i Hi. assert (INx : In x (a_qthread A ++ a_qglobal A)).
          { apply in_or_app. right. destruct Hx as [Hx| ->]; [| subst glb]. 
            - pattern (a_qglobal A) at 1. rewrite <- (removelast_last_app (a_qglobal A) (BA 0 []) QGN). apply in_or_app. left. exact Hx.
            - pattern (a_qglobal A) at 2. rewrite <- (removelast_last_app (a_qglobal A) (BA 0 []) QGN). apply in_or_app. right. left. reflexivity. }
          pose proof (batch_known A (aview_of (pa_hull A) m) AR x INx) as [_ LX]. unfold kQuarantineBatchCount in LX. lia.
        + (* [comment removed for export] *)
          intros x a' Hx Ha'.
          assert (INxg : In x (a_qglobal A)) by (pattern (a_qglobal A) at 1; rewrite <- (removelast_last_app (a_qglobal A) (BA 0 []) QGN); apply in_or_app; left; exact Hx).
          assert (INx : In x (a_qthread A ++ a_qglobal A)) by (apply in_or_app; right; exact INxg).
          pose proof (batch_carved A (aview_of (pa_hull A) m) AR x INx) as Cx.
          pose proof (carved_apart_thr A (aview_of (pa_hull A) m) AR _ Cx) as Dt. pose proof (carved_apart_n0 A (aview_of (pa_hull A) m) AR _ Cx) as Dn. pose proof (carved_apart_f0 A (aview_of (pa_hull A) m) AR _ Cx) as Df.
          pose proof (carved_disjoint A (aview_of (pa_hull A) m) AR _ _ Cx CVp ltac:(intros EE; exact (live_not_batch A (aview_of (pa_hull A) m) AR p li x LU INx (eq_sym EE)))) as Dp.
          assert (NI : ba_idx x <> ba_idx bl).
          { intros EE. apply (NoDup_app_In _ _ (ba_idx bl) BND); [apply in_or_app; right; left; reflexivity| rewrite <- EE; apply in_map; exact INxg]. }
          pose proof (carved_disjoint A (aview_of (pa_hull A) m) AR _ _ Cx CBL ltac:(intros EE; injection EE as EE; exact (NI EE))) as Dl.
          assert (NIg : ba_idx x <> ba_idx glb).
          { intros EE. pose proof BND0 as ND. rewrite map_app in ND. apply stdpp.list_relations.list.NoDup_app in ND as (_ & _ & NDg).
            pattern (a_qglobal A) at 1 in NDg. rewrite <- (removelast_last_app (a_qglobal A) (BA 0 []) QGN), map_app in NDg. cbn [map] in NDg.
            exact (NoDup_app_In _ _ (ba_idx x) NDg ltac:(apply in_map; exact Hx) ltac:(rewrite EE; left; reflexivity)). }
          pose proof (carved_disjoint A (aview_of (pa_hull A) m) AR _ _ Cx Cg ltac:(intros EE; injection EE as EE; exact (NIg EE))) as Dgx.
          rewrite (proj1 (c24_range A (ba_idx x))), (proj2 (c24_range A (ba_idx x))) in Dt, Dn, Df, Dp, Dl, Dgx.
          rewrite (proj1 (c24_range A (ba_idx bl))), (proj2 (c24_range A (ba_idx bl))) in Dl. rewrite (proj1 (c24_range A (ba_idx glb))), (proj2 (c24_range A (ba_idx glb))) in Dgx.
          (first [ pose proof ((batch_range A (aview_of (pa_hull A) m) AR x INx)) as dR_46; dand3 dR_46 as Rx1 Rx2 _ | pose proof (batch_range A (aview_of (pa_hull A) m) AR x INx) as (Rx1 & Rx2 & _) ]).
          apply MU'; [clear -Ha' Rx1 Rx2 CE; unfold kQuarantineBatchBytes in *; kung_all; lia| |].
          * unfold W0. subst lb. clear -Ha' Dt Dn Df Dp Rx1 Rx2 L1 L2 CE CEIL S2 NR Gc Gt Gn Gf Gs. unfold batch_addr, kQuarantineBatchBytes in *. kung_all. intros [X|[X|[X|[X|[X|[X|[X|[X|[X|X]]]]]]]]]; lia.
          * subst BX lb. cbv beta. intros [X|[X|[[_ X]|[[_ X]|[_ X]]]]].
            -- clear -Ha' Dl CNR X. unfold batch_addr, kQuarantineBatchBytes in *. lia.
            -- clear -Ha' Dl CNR X. unfold batch_addr, kQuarantineBatchBytes in *. lia.
            -- clear -Ha' Rx1 X. unfold gq_blk, batch_addr, kQuarantineBatchBytes in *. kung_all. lia.
            -- clear -Ha' Dgx X E. unfold batch_addr, kQuarantineBatchBytes in *. lia.
            -- clear -Ha' Rx1 X. unfold ia_blk, batch_addr, kQuarantineBatchBytes in *. kung_all. lia.
        + (* [comment removed for export] *)
          intros a' Ha'.
          pose proof (carved_apart_thr A (aview_of (pa_hull A) m) AR _ Cg) as Dt. pose proof (carved_apart_n0 A (aview_of (pa_hull A) m) AR _ Cg) as Dn. pose proof (carved_apart_f0 A (aview_of (pa_hull A) m) AR _ Cg) as Df.
          pose proof (carved_disjoint A (aview_of (pa_hull A) m) AR _ _ Cg CVp ltac:(intros EE; exact (live_not_batch A (aview_of (pa_hull A) m) AR p li glb LU INg (eq_sym EE)))) as Dp.
          pose proof (carved_disjoint A (aview_of (pa_hull A) m) AR _ _ Cg CBL ltac:(intros EE; injection EE as EE; exact (NIb EE))) as Dl.
          rewrite (proj1 (c24_range A (ba_idx glb))), (proj2 (c24_range A (ba_idx glb))) in Dt, Dn, Df, Dp, Dl. rewrite (proj1 (c24_range A (ba_idx bl))), (proj2 (c24_range A (ba_idx bl))) in Dl.
          apply MU'; [clear -Ha' R1 R2 CE E; unfold batch_addr, kQuarantineBatchBytes in *; kung_all; lia| |].
          * unfold W0. subst lb. clear -Ha' E Dt Dn Df Dp R1 R2 L1 L2 CE CEIL S2 NR Gc Gt Gn Gf Gs. unfold batch_addr, kQuarantineBatchBytes in *. kung_all. intros [X|[X|[X|[X|[X|[X|[X|[X|[X|X]]]]]]]]]; lia.
          * subst BX lb. cbv beta. intros [X|[X|[[_ X]|[[_ X]|[_ X]]]]].
            -- clear -Ha' Dl CNR X E. unfold batch_addr, kQuarantineBatchBytes in *. lia.
            -- clear -Ha' Dl CNR X E. unfold batch_addr, kQuarantineBatchBytes in *. lia.
            -- clear -Ha' R1 X E. unfold gq_blk, batch_addr, kQuarantineBatchBytes in *. kung_all. lia.
            -- clear -Ha' X E. unfold batch_addr in *. lia.
            -- clear -Ha' R1 X E. unfold ia_blk, batch_addr, kQuarantineBatchBytes in *. kung_all. lia.
        + rewrite <- E. unfold off_qb_next. rewrite Z.add_0_r. destruct Pgl as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
        + rewrite <- E. destruct Pgl as [_ WR]. (first [ pose proof ((batches_repr_last _ _ (removelast (a_qglobal A)) glb ltac:(unfold glb; rewrite (removelast_last_app (a_qglobal A) (BA 0 []) QGN); exact BRG0))) as dR_47; dand5 dR_47 as _ _ _ _ Mg | pose proof (batches_repr_last _ _ (removelast (a_qglobal A)) glb ltac:(unfold glb; rewrite (removelast_last_app (a_qglobal A) (BA 0 []) QGN); exact BRG0)) as (_ & _ & _ & _ & Mg) ]).
          rewrite <- E in Mg. apply (mapped_N (aview_of (pa_hull A) m) v' NN); [clear -R1; kung_all; lia| clear -R1; kung_all; lia| clear -R2 CE; unfold kQuarantineBatchBytes in *; lia| exact Mg]. }
    assert (QT'E : forall e, In e (q_entries (qt1 ++ qg1)) -> In e (q_entries (a_qthread A ++ a_qglobal A)) \/ e = QE (li_chunk li) n0).
    { intros e He. subst qt1 qg1. apply (proj1 (tailQ_entries tk qt' (a_qglobal A) e)) in He. change (a_qthread A) with qt.
      unfold q_entries in He |- *. rewrite flat_map_app in He |- *. subst qt'. change (flat_map ba_entries (qpush_last qt fe)) with (q_entries (qpush_last qt fe)) in He.
      rewrite (qpush_last_entries _ _ QNE) in He. rewrite <- FE. apply in_app_iff in He as [He|He]; [apply in_app_iff in He as [He|[<-|[]]]|]; [left| right; reflexivity| left]; apply in_or_app; [left; exact He| right; exact He]. }
    assert (QT'N : In (QE (li_chunk li) n0) (q_entries (qt1 ++ qg1))).
    { subst qt1 qg1. apply (proj2 (tailQ_entries tk qt' (a_qglobal A) _)).
      unfold q_entries. rewrite flat_map_app. apply in_or_app. left. subst qt'. change (flat_map ba_entries (qpush_last qt fe)) with (q_entries (qpush_last qt fe)).
      rewrite (qpush_last_entries _ _ QNE), <- FE. apply in_or_app. right. left. reflexivity. }
    assert (QT'B : forall b, In b (qt1 ++ qg1) -> In (ba_idx b) (map ba_idx (a_qthread A ++ a_qglobal A)) \/ p_cached_ (a_cache A) kQuarantineBatchClass (ba_idx b)).
    { intros b Hb. left. subst qt1 qg1. apply (proj1 (tailQ_batches tk qt' (a_qglobal A) b)) in Hb. change (a_qthread A) with qt.
      rewrite map_app. apply in_app_iff in Hb as [Hb|Hb]; apply in_or_app; [left| right; apply in_map; exact Hb].
      subst qt'. rewrite <- (qpush_last_indices _ fe QNE). apply in_map. exact Hb. }
    (* [comment removed for export] *)
    assert (IAQ : ((true = a_ia_inited A /\ (forall a, iafoot a -> v' (wz a) = aview_of (pa_hull A) m (wz a))) \/ (true = true /\ ia_repr_ LPA AL_pboth true v'))
                  /\ u8_at rsegs v' 0x144649 0 /\ bytes_at rsegs v' 0x14464a [Z_to_bv 8 0; Z_to_bv 8 0]).
    { destruct (a_ia_inited A) eqn:EIA.
      - assert (IAW : forall a, 0xb5dc0 <= a < 0x14464c -> v' (wz a) = aview_of (pa_hull A) m (wz a)).
        { intros a Ha. apply MU'; [clear -Ha; lia| |].
          - unfold W0. clear -Ha T1 L1 L2 CL1 CE CEIL N1 F1 S1 S2 Gc Gt Gn Gf Gs. kung_all. intros [X|[X|[X|[X|[X|[X|[X|[X|[X|X]]]]]]]]]; lia.
          - subst BX. cbv beta. intros [X|[X|[[_ X]|[[Htk X]|[X _]]]]]; [clear -Ha X LBL; unfold kHighMemBeg in LBL; lia| clear -Ha X LBL; unfold kHighMemBeg in LBL; lia| clear -Ha X; unfold gq_blk in X; lia| | discriminate].
            subst tk. (first [ dand3 TKC as _ QGN _ | destruct TKC as (_ & QGN & _) ]). (first [ pose proof ((GLX QGN)) as dR_49; dand4 dR_49 as _ _ R1 _ | destruct (GLX QGN) as (_ & _ & R1 & _) ]). clear -Ha X R1. kung_all. lia. }
        split; [| split].
        + left. split; [reflexivity|]. intros a Ha. apply IAW. unfold iafoot in Ha. cbn [al_internal_allocator_inst al_internal_alloc_inited AL_pboth] in Ha. clear -Ha. lia.
        + pose proof (ar_locks _ _ _ _ _ (proj2 AR)) as LK. unfold locks_repr_ in LK. cbv zeta in LK. (first [ dand6 LK as _ _ _ _ _ LK | destruct LK as (_ & _ & _ & _ & _ & LK) ]).
          change (al_internal_alloc_inited AL_pboth + 1) with 0x144649 in LK. rewrite lockb_nil in LK.
          eapply (bytes_at_agree_gen _ _ _ _ _ LK). intros i Hi. cbn in Hi. apply IAW. lia.
        + pose proof (consts_cell (aview_of (pa_hull A) m) 0x14464a [Z_to_bv 8 0; Z_to_bv 8 0] (proj1 (ar_consts _ _ _ _ _ (proj2 AR))) eq_refl) as PD.
          eapply (bytes_at_agree_gen _ _ _ _ _ PD). intros i Hi. cbn in Hi. apply IAW. lia.
      - exfalso. clear -EIA IAT. congruence. }
    (first [ dand3 IAQ as IAH IAL IAP | destruct IAQ as (IAH & IAL & IAP) ]).
    (* [comment removed for export] *)
    assert (LW : rw_cells rsegs v' (QINST + 152) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C2 (wz 0)]).
    { destruct tk; cbn [tail_postR] in TPOST; [destruct TPOST| exact (proj1 (proj2 TPOST))| exact (proj1 (proj2 TPOST))]. }
    assert (QLX : u8_at rsegs v' 0xb18c8 0 /\ u8_at rsegs v' 0xb18c9 1 /\ bytes_at rsegs v' 0xb18ca [Z_to_bv 8 0; Z_to_bv 8 0]).
    { destruct LW as [[_ B] _]. cbn [cells_bytes cbytes app] in B. change (le2 (wz 0)) with [Z_to_bv 8 0; Z_to_bv 8 0] in B. change (QINST + 152) with 0xb18c8 in B.
      apply (bytes_at_app _ v' 0xb18c8 [Z_to_bv 8 0] [Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0]) in B as [B1 B]. apply (bytes_at_app _ v' _ [Z_to_bv 8 1] [Z_to_bv 8 0; Z_to_bv 8 0]) in B as [B2 B3].
      cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add] in B2, B3. exact (conj B1 (conj B2 B3)). }
    (first [ dand3 QLX as QLK QRL1 QPD | destruct QLX as (QLK & QRL1 & QPD) ]).
    (* [comment removed for export] *)
    set (A1e := freeA A p qt' (a_qglobal A) (a_cache A) (fst (depot_putC (a_depot A) key)) true).
    assert (TKX : tk <> TN /\ kQuarantineCacheSize < q_bytes qt + n0 /\ kQuarantineMaxSize < q_bytes (a_qglobal A) + (q_bytes qt + n0)).
    { destruct tk; [destruct TKC| |].
      - (first [ dand3 TKC as TK1 QGE TK3 | destruct TKC as (TK1 & QGE & TK3) ]). split; [discriminate|]. split; [exact TK1|]. subst gqb. rewrite QGE, q_bytes_nil. clear -TK3. lia.
      - (first [ dand3 TKC as TK1 _ TK3 | destruct TKC as (TK1 & _ & TK3) ]). split; [discriminate|]. exact (conj TK1 TK3). }
    (first [ dand3 TKX as TKN DRN BIGN | destruct TKX as (TKN & DRN & BIGN) ]).
    assert (QG1 : qg1 = a_qglobal A ++ qt') by (subst qg1; destruct tk; [exfalso; exact (TKN eq_refl)| reflexivity| reflexivity]).
    assert (QT1 : qt1 = []) by (subst qt1; destruct tk; [exfalso; exact (TKN eq_refl)| reflexivity| reflexivity]).
    assert (XE : xferA A1e = A') by (subst A1e A'; rewrite xferA_freeA, QT1, QG1; reflexivity).
    assert (WB1 : WFB (q_bytes (a_qthread A1e)) A1e).
    { subst A1e. cbn [freeA a_qthread]. rewrite <- (set_ia_freeA A p qt' (a_qglobal A) (a_cache A) _ (a_ia_inited A) true), IAT.
      unfold set_ia. cbn [a_pl a_reg a_cache_inited a_cache a_livemap a_qthread a_qglobal a_sec a_depot a_fhint a_fframes a_oom a_tiny a_qlimbo a_scred a_deadsh a_pcred a_paid freeA].
      pose proof (free_fast_WFB A m md p li key AI LU KEYU QNE ROOM) as X. rewrite freeA_fast_eq, IAT in X. change (a_qthread A) with qt in X. subst qt' fe.
      rewrite (qpush_last_bytes _ _ QNE). exact X. }
    assert (HDRX : rw_cells rsegs v' (726360 + off_q_cache_list_size)
               [C8 (wz (Z.of_nat (length (qtransfer qt' (a_qglobal A)))));
                C8 (wz (match qtransfer qt' (a_qglobal A) with [] => 0 | b :: _ => batch_addr (a_sb A) b end));
                C8 (wz (match qtransfer qt' (a_qglobal A) with [] => 0 | _ :: _ => batch_addr (a_sb A) (last (qtransfer qt' (a_qglobal A)) (BA 0 [])) end));
                C8 (wz (q_bytes (qtransfer qt' (a_qglobal A))))]).
    { change (726360 + off_q_cache_list_size) with (QINST + 160). unfold qtransfer. rewrite length_app, Nat2Z.inj_add, q_bytes_app, HQ1, HQ4.
      replace (match a_qglobal A ++ qt' with [] => 0 | _ :: _ => batch_addr (a_sb A) (last (a_qglobal A ++ qt') (BA 0 [])) end) with lb.
      2:{ rewrite QT'S, app_assoc, last_last. unfold batch_addr. cbn [ba_idx]. subst lb. unfold batch_addr. destruct (a_qglobal A ++ l); reflexivity. }
      destruct tk; cbn [tail_postR] in TPOST; [destruct TPOST| |].
      - (first [ dand3 TKC as _ QGE _ | destruct TKC as (_ & QGE & _) ]). (first [ dand4 TPOST as _ _ X _ | destruct TPOST as (_ & _ & X & _) ]). rewrite QGE. cbn [app length Z.of_nat]. rewrite q_bytes_nil, Z.add_0_l, Z.add_0_l.
        replace (match qt' with [] => 0 | b :: _ => batch_addr (a_sb A) b end) with (qc_first A qt') by (unfold qc_first; destruct qt'; reflexivity).
        rewrite HQ2. subst gqb. rewrite QGE, q_bytes_nil, Z.add_0_l in X. exact X.
      - (first [ dand3 TKC as _ QGN _ | destruct TKC as (_ & QGN & _) ]). (first [ dand5 TPOST as _ _ X _ _ | destruct TPOST as (_ & _ & X & _ & _) ]).
        replace (match a_qglobal A ++ qt' with [] => 0 | b :: _ => batch_addr (a_sb A) b end) with gf by (subst gf; unfold qc_first; destruct (a_qglobal A); [congruence| reflexivity]).
        subst gn gqb. exact X. }
    assert (QMX : ro_cells rsegs v' (QINST + 64) [C8 (wz (2^28)); C8 (wz kQuarantineMinSize)]).
    { destruct tk; cbn [tail_postR] in TPOST; [destruct TPOST| exact (proj2 (proj2 (proj2 TPOST)))| exact (proj2 (proj2 (proj2 (proj2 TPOST))))]. }
    (* [comment removed for export] *)
    assert (FROK : frame_ok LPA (pa_owned A) (pa_owned A1e) uspd (uspd - lo) (newblk p n0) nowhere (aview_of (pa_hull A) m) v').
    { subst A1e. apply (free_frame_okC A m md p n0 li spd v' lo AI LU LN CEIL qt' (a_qglobal A) (a_cache A) _ true BX BXW MU' WM').
      intros k Hk. destruct ST as (_ & _ & STx). destruct (STx (lo + k) ltac:(lia)) as [Wv _]. unfold wview, wa in Wv.
      rewrite unsigned_lit in Wv by (clear -Hk CEIL LOW CE SPR; lia). rewrite (pa_find_segment_none (lo + k) 1) in Wv by (clear -Hk CEIL LOW CE SPR; lia).
      destruct (aview_of (pa_hull A) m (wz (lo + k))); [discriminate| exact Wv]. }
    assert (ABOVE : forall a, uspd <= a < hi -> v' (wz a) = aview_of (pa_hull A) m (wz a)).
    { intros a Ha. apply MU'; [clear -Ha SPR SPHI HISP; lia| |].
      + unfold W0. clear -Ha T1 T2 L1 L2 CL1 CL2 CE CEIL LOW N1 N2 F1 F2 S1 S2 Gc Gt Gn Gf Gs NR R8. kung_all. intros [X|[X|[X|[X|[X|[X|[X|[X|[X|X]]]]]]]]]; lia.
      + intros HB. destruct (BXW a HB) as [(b & Hb & Rb)|[X|[X|[(k & Ck & Rk)|X]]]].
        * (first [ pose proof ((batch_range A (aview_of (pa_hull A) m) AR b Hb)) as dR_60; dand3 dR_60 as _ Rb2 _ | pose proof (batch_range A (aview_of (pa_hull A) m) AR b Hb) as (_ & Rb2 & _) ]). clear -Ha Rb Rb2 CE CEIL LOW. unfold kQuarantineBatchBytes in *. lia.
        * clear -Ha X T2 CEIL LOW. lia.
        * clear -Ha X T2 CEIL LOW. lia.
        * pose proof (carved_prim_where A (aview_of (pa_hull A) m) AR _ _ (cached_carved A (aview_of (pa_hull A) m) AR kQuarantineBatchClass k ltac:(unfold kQuarantineBatchClass; lia) Ck)) as W.
          pose proof class_size_24 as C24. clear -Ha Rk W C24 CE CEIL LOW. unfold kQuarantineBatchBytes in *. kung_all. lia.
        * clear -Ha X CEIL LOW CE. unfold xblk, ia_blk, gq_blk in X. lia. }
    assert (ERRNO : forall i, 0 <= i < 4 -> v' (wz (cl_errno LPA + i)) = aview_of (pa_hull A) m (wz (cl_errno LPA + i))).
    { intros i Hi. cbn [cl_errno LPA].
      exact (AGimg A (aview_of (pa_hull A) m) p n0 li spd v' lo AR LU LN ltac:(clear -CEIL LOW; lia) BX BXW MU' (6191924 + i) ltac:(lia) ltac:(lia) ltac:(unfold xblk, ia_blk, gq_blk; lia)). }
    assert (RX : RECX rac spd s0 s1 s2 s3 s4 s5 s6 A m md p n0 stkobj lo hi A1e (munrestrict (hidc (pa_hull A)) m v') md').
    { constructor; change (pa_hull A1e) with (pa_hull A); rewrite ?VIEW.
      - exact WB1.
      - subst A1e. cbn [freeA a_cache_inited]. (first [ pose proof ((wfR A WF0)) as dR_61; dand3 dR_61 as R1 _ R3 | destruct (wfR A WF0) as (R1 & _ & R3) ]). apply R3. exists kQuarantineBatchClass. split; [unfold kQuarantineBatchClass; clear; lia|].
        (first [ pose proof ((carved_prim_where A (aview_of (pa_hull A) m) AR _ _ CBL)) as dR_62; dand4 dR_62 as W1 W2 W3 _ | pose proof (carved_prim_where A (aview_of (pa_hull A) m) AR _ _ CBL) as (W1 & W2 & W3 & _) ]). pose proof class_size_24 as C24. unfold kQuarantineBatchBytes in C24. clear -W1 W2 W3 C24. lia.
      - subst A1e. cbn [freeA a_qthread]. subst qt'. rewrite (qpush_last_bytes _ _ QNE). subst fe. unfold free_entry, qe_bytes. cbn [qe_n]. rewrite LN, US. exact DRN.
      - subst A1e. cbn [freeA a_qthread a_qglobal]. subst qt'. rewrite (qpush_last_bytes _ _ QNE). subst fe. unfold free_entry, qe_bytes. cbn [qe_n]. rewrite LN, US. exact BIGN.
      - subst A1e. cbn [freeA a_qthread a_qglobal]. subst qt'. rewrite (qpush_last_bytes _ _ QNE). subst fe. unfold free_entry, qe_bytes. cbn [qe_n]. rewrite LN, US.
        clear -QTB QGB NQ NR. lia.
      - rewrite XE. subst A'.
        eapply (free_arepr2R A (aview_of (pa_hull A) m) p n0 li spd v' lo AR LU LN ltac:(clear -CEIL LOW; lia) qt1 qg1 (a_cache A) _ true BX BXW MU' NN b1 _ B1R B1M IDR'
                  Punw Phdr Pctx Psh Pdr Pqc' Pbr' Pqcg Pbrg Pl24 IAH IAL IAP QLK QPD QT'E QT'B ltac:(intros; reflexivity) ltac:(intros k Ck; exact Ck) QRL1).
      - subst A1e. cbn [freeA a_pl a_reg a_sec]. apply (free_hiddenC A m md p n0 li spd v' lo AI LU LN CEIL BX BXW MU' WM'). exact (ai_hidden _ _ _ _ _ _ _ AI).
      - subst A1e. cbn [freeA a_pl]. exact (ai_extra _ _ _ _ _ _ _ AI).
      - subst A1e. cbn [freeA a_pl a_sec]. exact (aledger_sbm _ _ _ _ md md' Hsame (ai_ledger _ _ _ _ _ _ _ AI)).
      - exact HI'.
      - (first [ dand18 FRM as _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLT _ | destruct FRM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLT & _) ]). rewrite HLT. exact HH.
      - rewrite (same_but_materialized_vmmaps _ _ Hsame). subst A1e. exact (ai_cover _ _ _ _ _ _ _ AI).
      - rewrite (same_but_materialized_vmmaps _ _ Hsame). exact (ai_ceil _ _ _ _ _ _ _ AI).
      - (* [comment removed for export] *)
        constructor; try reflexivity.
        + intros c Hc [R0 K0]. subst A1e. split; [exact R0| exact K0].
        + exact (wamd_sbm md md' Hsame HH).
        + exact ERRNO.
        + exact FROK.
        + exact ABOVE.
      - exact MI'.
      - exact ST'.
      - exact PFR'.
      - exact LW.
      - exact HDRX.
      - exact QMX. }
    (* [comment removed for export] *)
    apply (rec_to_loop rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A m md p n0 stkobj lo hi T xs2 xs5 CEIL LOW SPHI HISP SPA VB key KL
             A1e (munrestrict (hidc (pa_hull A)) m v') md' t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' RX).
    intros A2 m2 md2 scr ra a1x a2x a3x a4x a5x a6x a7x t0x t1x t2x t3x t4x t5x t6x s4x s6x s7x s8x s9x more NEM CU2 PL2.
    apply (rloop rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A m md p n0 stkobj lo hi T xs2 xs5 CEIL LOW SPHI HISP SPA VB STEP_PDM STEP_SEC STEP_BDM
             (length more) A2 m2 md2 more scr ra a1x a2x a3x a4x a5x a6x a7x t0x t1x t2x t3x t4x t5x t6x s4x s6x s7x s8x s9x (le_n _) NEM CU2).
    intros A3 m3 md3 t0y t1y t2y a1y a2y a3y a4y a5y a6y a7y t3y t4y t5y t6y X3 PL3.
    apply (loop_exit rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A m md p n0 stkobj lo hi T xs2 xs5 CEIL LOW SPHI HISP SPA VB key KL PNB SMH li LU LN
             A3 m3 md3 t0y t1y t2y a1y a2y a3y a4y a5y a6y a7y t3y t4y t5y t6y X3).
    - rewrite PL3, PL2. subst A1e. reflexivity.
    - unfold dealloc_core_K. cbv zeta. exact KK.
  Qed.
End FreeHitsR.
