(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts ARtSscs AMTac AMalmys AMaly5g.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeT.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeT.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AQWf AFreeB1 ATransp AFreeB5 ACoresk AWrapKit AFreeG1c AFreeG2c AFreeG3c.

Module ACoreF.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts ARtSscs AMTac AMalmys AMaly5g.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeT.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeT.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AQWf AFreeB1 ATransp AFreeB5 ACoresk AWrapKit AFreeGDc AFreeG1c AFreeG2c AFreeG3c.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMaly5g OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeT.AFreeN OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeT OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQWf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ACoresk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AWrapKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeGDc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeG1c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeG2c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeG3c.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.solve_load_guarded | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
#[local] Notation WF := (WF AL_pboth).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma pa_wx : wx_segs_nowrap rsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

Section CoreF.
Context {Clg : Ceiling}.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Null.
  Variables (rac spd gp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AState) (n0 stkobj lo hi : Z) (T : TSet).
  Hypothesis AI : @pa_ainv _ DepotRepL A m md.
  Hypothesis MI : mem_inv rsegs (aview_of (pa_hull A) m).
  Hypothesis LV : (0 = 0 /\ n0 = 0) \/ as_live A 0 = Some n0.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LOW : lo <= bv_unsigned spd - 4096.
  Hypothesis SPHI : bv_unsigned spd <= hi.
  Hypothesis HISP : hi <= 2^47.
  Hypothesis RA2 : bv_unsigned rac mod 2 = 0.
  Hypothesis ST : stk rsegs (aview_of (pa_hull A) m) lo (bv_unsigned spd).
  Hypothesis SMH : mapped (aview_of (pa_hull A) m) (bv_unsigned spd) (hi - bv_unsigned spd).
  Hypothesis KK : forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AState) (m' : mem) (md' : Model),
          let v' := aview_of (pa_hull A') m' in
          @pa_ainv _ DepotRepL A' m' md' -> mem_inv (cl_segs LPA) v' -> amd_frame md md' ->
          (forall ff, as_fframe A' ff = as_fframe A ff) ->
          a_pl A' = a_pl A ->
          as_live A' 0 = None -> (forall q, q <> 0 -> as_live A' q = as_live A q) ->
          as_livebytes A' = as_livebytes A - n0 -> as_tinycred A' = as_tinycred A -> as_seccred A' = as_seccred A -> as_primcred A' = as_primcred A (* [comment removed for export] *) ->
          as_nlive A' = as_nlive A - (if Z.eqb 0 0 then 0 else 1) ->
          (forall c, c <> kQuarantineBatchClass -> a_virgin A c -> a_virgin A' c) ->
          (forall i, 0 <= i < 4 -> mrd (cl_segs LPA) v' (wz (cl_errno LPA + i)) = mrd (cl_segs LPA) (aview_of (pa_hull A) m) (wz (cl_errno LPA + i))) ->
          frame_ok LPA (pa_owned A) (pa_owned A') hi (hi - lo) (newblk 0 n0) nowhere (aview_of (pa_hull A) m) v' ->
          (forall a, bv_unsigned spd <= a < hi -> v' (wz a) = aview_of (pa_hull A) m (wz a)) ->
          stk (cl_segs LPA) v' lo (bv_unsigned spd) ->
          srealizes (cl_segs LPA) (mkCfg (MS (mkR rac spd gp (cl_tp LPA) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc rac) fc None m' (seg_rom (cl_segs LPA))) md') T.

  Theorem dealloc_nullG :
    srealizes (cl_segs LPA) (mkCfg (dealloc_entry_ms rac spd gp (cl_tp LPA) t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m 0 stkobj) md) T.
  Proof.
    unfold dealloc_entry_ms. cbn [cl_segs LPA] in MI, KK |- *.
    pose proof (ai_wf _ _ _ _ _ _ _ AI) as WF0.
    pose proof (conj (ai_wf _ _ _ _ _ _ _ AI) (ai_repr _ _ _ _ _ _ _ AI) : WF A /\ @arepr _ DepotRepL LPA AL_pboth [] A (aview_of (pa_hull A) m)) as AR.
    pose proof alloc_ceiling_val as CE. pose proof (zr_word spd) as SPR; unfold inr64 in SPR.
    pose proof (hit_place A m md AI) as (TH1 & _). pose proof (aobj_facts _ _ TH1) as THF.
    pose proof (hit_TUNW A m md AI) as TUNW. unfold off_th_unwinding in TUNW.
    destruct (asI_minv A m md AI) as [HMI HH].
    set (uspd := bv_unsigned spd) in *. set (v := aview_of (pa_hull A) m) in *.
    (* [comment removed for export] *)
    assert (NL : as_live A 0 = None /\ n0 = 0).
    { assert (NL0 : forall li, a_livemap A !! 0 = Some li -> False).
      { intros li E. destruct (wfV A WF0) as (V1 & _). (first [ pose proof ((V1 0 li E)) as dR_1; dand3 dR_1 as N U _ | pose proof (V1 0 li E) as (N & U & _) ]). cbv zeta in U.
        pose proof (ATransp.user_in A _ _ (ATransp.known_live A v AR 0 li E)) as [U1 _].
        pose proof (ATransp.known_range A v AR _ _ (ATransp.known_live A v AR 0 li E)) as [R1 _].
        rewrite <- U in U1. unfold kHighMemBeg in *. clear -R1 U1. lia. }
      unfold as_live, as_live_ in LV |- *. destruct (a_livemap A !! 0) as [li|] eqn:E; [exfalso; eapply NL0; first [exact E| reflexivity]|].
      split; [reflexivity|]. destruct LV as [[_ N]|X]; [exact N| discriminate]. }
    destruct NL as [NL N0].
    (* [comment removed for export] *)
    pose (Q1 := fun ms' : machine_state => exists m',
        ms' = MS (mkR rac spd gp (cl_tp LPA) t0 t1 t2 s0 s1 (wz 0xb1558) (wz 0) a2 a3 (wz stkobj) (wz 1) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc rac) fc None m' (seg_rom rsegs)
        /\ munch [(uspd - 64, uspd)] v m' /\ wmono rsegs v m' /\ mem_inv rsegs m' /\ stk rsegs m' lo uspd).
    eapply (srz_evt_restrict rsegs (pa_hull A) (asI_hull_segs A m md AI) pa_wx _ (pa_eager A) Q1 _ md T HMI HH).
    { rewrite restrict_MS. change (mrestrict (hidc (pa_hull A)) m) with v.
      eapply evt_cut; [eapply (dealloc_null_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc v lo)|];
        [exact MI| exact ST| subst uspd; clear -LOW; lia| exact CEIL| exact RA2|].
      intros ms' PO. destruct PO as [m' (E & MU & WM & MI' & ST')]. subst ms'. apply evt_done. unfold Q1. exists m'.
      split; [reflexivity|]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; assumption. }
    intros msr1 md1 HQ1 HI1 SB1 CL1. (first [ dex1 HQ1 as v'; dand5 HQ1 as -> MU WM' MI' ST' | dand6 HQ1 as v' -> MU WM' MI' ST' | destruct HQ1 as (v' & -> & MU & WM' & MI' & ST') ]).
    rewrite unrestrict_MS. cbn [ms_mem] in CL1.
    lazymatch goal with |- context [munrestrict ?Hh (ms_mem (MS ?R ?FF ?pc ?fcx ?rv ?mm ?ro)) ?v2] => change (ms_mem (MS R FF pc fcx rv mm ro)) with mm end.
    assert (AG : forall a, 0 <= a < 2^64 -> ~ (uspd - 64 <= a < uspd) -> v' (wz a) = v (wz a)).
    { intros a Ha NW. apply MU. rewrite unsigned_lit by lia. cbn [outside]. split; [exact NW| exact I]. }
    assert (TUNW1 : rw_cells rsegs v' (p_thr (a_pl A) + 3168) [C1 (Z_to_bv 8 0)]).
    { eapply rw_cells_transport; [exact TUNW| exact MU| exact WM'|]. cbn. clear -THF CE CEIL LOW. lia. }
    assert (SMW : mapped v lo (uspd - lo)) by (eapply stk_mapped_pa; [exact ST| exact CEIL| lia| lia]).
    pose proof (shell_ainvW A m md md1 lo uspd v' nowhere AI CEIL SMW
                  ltac:(intros a Ha NW _ _ _; apply AG; [exact Ha| clear -NW LOW; lia]) ltac:(intros a []) TUNW1 WM' CL1 HI1 SB1) as AI1.
    pose proof (shell_viewW A m v' CL1) as VIEW1.
    eapply (KK t0 t1 t2 (wz 0xb1558) (wz 0) a2 a3 (wz stkobj) (wz 1) a6 a7 t3 t4 t5 t6 A (munrestrict (hidc (pa_hull A)) m v') md1).
    - exact AI1.
    - rewrite VIEW1. exact MI'.
    - apply wamd_sbm; [exact SB1| exact HH].
    - intros ff. reflexivity.
    - reflexivity.
    - exact NL.
    - intros q Hq. reflexivity.
    - rewrite N0. lia.
    - reflexivity.
    - reflexivity.
    - reflexivity.   (* [comment removed for export] *)
    - cbn [Z.eqb]. lia.
    - intros c Hc Vc. exact Vc.
    - intros i Hi. rewrite VIEW1. cbn [cl_errno LPA]. unfold mrd. rewrite (AG (6191924 + i)); [reflexivity| clear -Hi; lia| clear -Hi CE CEIL LOW; lia].
    - rewrite VIEW1. unfold frame_ok. replace (hi - (hi - lo)) with lo by lia.
      OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits.
      + intros a Ha NO NO' NW _ _ _. apply AG; [exact Ha| clear -NW LOW SPHI; lia].
      + intros a Ha NI Hv. right; right. apply (wmono_NN _ _ a WM'); [| exact Ha| exact Hv]. unfold in_image in NI. cbn [cl_image_lo cl_image_hi LPA] in NI. clear -NI Ha. lia.
      + assert (M1 : mapped v' lo (uspd - lo)) by (eapply stk_mapped_pa; [exact ST'| exact CEIL| lia| lia]).
        intros k Hk. destruct (Z.lt_ge_cases (lo + k) uspd) as [B|B].
        * apply M1. clear -Hk B. lia.
        * rewrite (AG (lo + k)) by (clear -Hk B CE CEIL SPR SPHI HISP; lia).
          replace (lo + k) with (uspd + (lo + k - uspd)) by lia. apply SMH. clear -Hk B. lia.
      + intros a Ha [].
      + intros a Ha O'. left. exact O'.
      + intros a Ha O NO'. exfalso. exact (NO' O).
      + intros a Ha NB. unfold newblk, blk in NB. exfalso. clear -NB. lia.
    - intros a Ha. rewrite VIEW1. apply AG; [clear -Ha SPR SPHI HISP; lia| clear -Ha; lia].
    - rewrite VIEW1. exact ST'.
  Qed.
  End Null.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition ctail_covered (A : AState) (qb' : Z) : Prop :=
    qb' <= kQuarantineCacheSize \/ q_bytes (a_qglobal A) + qb' <= kQuarantineMaxSize.

  (* [comment removed for export] *)
  Definition dcore_covered (A : AState) (p n0 : Z) : Prop :=
    p = 0 \/
    kQuarantineMaxSize < n0 \/
    (n0 <= kQuarantineMaxSize /\
     (   (a_qthread A <> [] /\ Z.of_nat (length (ba_entries (last (a_qthread A) (BA 0 [])))) < kQuarantineBatchCount /\
          ctail_covered A (q_bytes (a_qthread A) + n0))
      \/ (a_qthread A = [] /\ pk_chunks (a_cache A kQuarantineBatchClass) <> [] /\
          ctail_covered A (n0 + kQuarantineBatchBytes))
      \/ (a_qthread A <> [] /\ Z.of_nat (length (ba_entries (last (a_qthread A) (BA 0 [])))) = kQuarantineBatchCount /\
          pk_chunks (a_cache A kQuarantineBatchClass) <> [] /\
          ctail_covered A (q_bytes (a_qthread A) + n0 + kQuarantineBatchBytes)))).

  (* [comment removed for export] *)
  Definition dealloc_core_rest : Prop :=
    forall (rac spd gp tp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AState) (p n0 stkobj lo hi : Z) (key : list Z) (T : TSet),
      dealloc_core_pre rac spd tp m md A p n0 stkobj lo hi key ->
      ~ dcore_covered A p n0 ->
      dealloc_core_K rac spd gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md A p n0 lo hi T ->
      srealizes (cl_segs LPA) (mkCfg (dealloc_entry_ms rac spd gp tp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p stkobj) md) T.

  Lemma ctail_pick : forall A qb', ctail_covered A qb' ->
    qb' <= kQuarantineCacheSize \/
    (kQuarantineCacheSize < qb' /\ a_qglobal A = [] /\ qb' <= kQuarantineMaxSize) \/
    (kQuarantineCacheSize < qb' /\ a_qglobal A <> [] /\ q_bytes (a_qglobal A) + qb' <= kQuarantineMaxSize).
  Proof.
    intros A qb' [H|H]; [left; exact H|]. destruct (Z.le_gt_cases qb' kQuarantineCacheSize) as [L|G]; [left; exact L| right].
    destruct (a_qglobal A) as [|g r] eqn:E; [left| right]; (split; [exact G| split; [congruence|]]);
      [try (rewrite E in H); cbn in H; lia| first [exact H| rewrite <- E; exact H| rewrite E in H; exact H]].
  Qed.

  Theorem dealloc_core_of_rest : dealloc_core_rest -> dealloc_core_cps.
  Proof.
    intros REST. unfold dealloc_core_cps.
    intros rac spd gp tp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A p n0 stkobj lo hi key T PRE KK.
    destruct (classic (dcore_covered A p n0)) as [COV|NCOV]; [| exact (REST rac spd gp tp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A p n0 stkobj lo hi key T PRE NCOV KK)].
    pose proof PRE as PRE'. unfold dealloc_core_pre in PRE'. cbv zeta in PRE'.
    (first [ dand19 PRE' as AI MI LV IAT TP CEIL LOW SPHI HISP SPA RA2 ST SMH STLO STHI STO TRW KEYU KR | destruct PRE' as (AI & MI & LV & IAT & TP & CEIL & LOW & SPHI & HISP & SPA & RA2 & ST & SMH & STLO & STHI & STO & TRW & KEYU & KR) ]).
    subst tp. unfold dealloc_core_K in KK. cbv zeta in KK.
    destruct (Z.eq_dec p 0) as [->|PNZ].
    - exact (dealloc_nullG rac spd gp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A n0 stkobj lo hi T
               AI MI LV CEIL LOW SPHI HISP RA2 ST SMH KK).
    - assert (HL : as_live A p = Some n0) by (destruct LV as [[E _]|LV]; [exfalso; exact (PNZ E)| exact LV]).
      destruct COV as [P0|[BIGN|(NQ & ARMS)]]; [exfalso; exact (PNZ P0)| |].
      { exact (dealloc_directG rac spd gp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A p n0 stkobj lo hi key T
                 AI MI HL IAT CEIL LOW SPHI HISP SPA RA2 ST SMH STLO STHI STO TRW KEYU KR BIGN KK). }
      unfold kQuarantineMaxSize in NQ.
      destruct ARMS as [(QNE & ROOM & TC0)|[(QTE & NE24 & TC0)|(QNE & FULL & NE24 & TC0)]]; apply ctail_pick in TC0.
      + destruct TC0 as [C|[C|C]].
        * exact (dealloc_fastG rac spd gp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A p n0 stkobj lo hi key T
                   AI MI HL IAT CEIL LOW SPHI HISP RA2 ST SMH STLO STHI STO TRW KEYU KR NQ KK TN QNE ROOM C).
        * exact (dealloc_fastG rac spd gp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A p n0 stkobj lo hi key T
                   AI MI HL IAT CEIL LOW SPHI HISP RA2 ST SMH STLO STHI STO TRW KEYU KR NQ KK T0 QNE ROOM C).
        * exact (dealloc_fastG rac spd gp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A p n0 stkobj lo hi key T
                   AI MI HL IAT CEIL LOW SPHI HISP RA2 ST SMH STLO STHI STO TRW KEYU KR NQ KK TA QNE ROOM C).
      + destruct TC0 as [C|[C|C]].
        * exact (dealloc_new0G rac spd gp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A p n0 stkobj lo hi key T
                   AI MI HL IAT CEIL LOW SPHI HISP RA2 ST SMH STLO STHI STO TRW KEYU KR NQ KK TN QTE NE24 C).
        * exact (dealloc_new0G rac spd gp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A p n0 stkobj lo hi key T
                   AI MI HL IAT CEIL LOW SPHI HISP RA2 ST SMH STLO STHI STO TRW KEYU KR NQ KK T0 QTE NE24 C).
        * exact (dealloc_new0G rac spd gp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A p n0 stkobj lo hi key T
                   AI MI HL IAT CEIL LOW SPHI HISP RA2 ST SMH STLO STHI STO TRW KEYU KR NQ KK TA QTE NE24 C).
      + destruct TC0 as [C|[C|C]].
        * exact (dealloc_newfullG rac spd gp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A p n0 stkobj lo hi key T
                   AI MI HL IAT CEIL LOW SPHI HISP RA2 ST SMH STLO STHI STO TRW KEYU KR NQ KK TN QNE FULL NE24 C).
        * exact (dealloc_newfullG rac spd gp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A p n0 stkobj lo hi key T
                   AI MI HL IAT CEIL LOW SPHI HISP RA2 ST SMH STLO STHI STO TRW KEYU KR NQ KK T0 QNE FULL NE24 C).
        * exact (dealloc_newfullG rac spd gp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A p n0 stkobj lo hi key T
                   AI MI HL IAT CEIL LOW SPHI HISP RA2 ST SMH STLO STHI STO TRW KEYU KR NQ KK TA QNE FULL NE24 C).
  Qed.
End CoreF.
End ACoreF.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARtSnjd AFreeR AFreeRC.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeRE.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeRG1 AFreeRG2 AFreeRG3.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMaly5g OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeT.AFreeN OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeT OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQWf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ACoresk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AWrapKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeG1c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeG2c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeG3c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ACoreF2.ACoreF OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSnjd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRC OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRE.AFreeRL OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRG1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRG2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRG3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
#[local] Notation WF := (WF AL_pboth).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
Section Stmts.
Context {Clg : Ceiling}.
  Definition step_pdm_stmt : Prop :=
    forall (rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (A0 : AState) (m0 : mem) (md0 : Model) (p n0 stkobj lo hi : Z) (TS : TSet) (xs2 xs5 : word)
           (A1 : AState) (m1 : mem) (md1 : Model) (b0 : batch) (i : nat) (more : list batch) (scr : list byte)
           (ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) (c k n : Z),
    alloc_ceiling <= lo -> lo <= bv_unsigned spd - 4096 -> bv_unsigned spd <= hi -> hi <= 2^47 -> bv_unsigned spd mod 16 = 0 ->
    (forall a, newblk p n0 a -> a < alloc_ceiling) ->
    CURG rac spd s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 A0 m0 md0 p n0 stkobj lo hi xs2 xs5 A1 m1 md1 (Some (b0, i)) more scr ->
    nth_error (ba_entries b0) i = Some (QE (ChP (CP c k)) n) ->
    Z.of_nat (length (pk_chunks (a_cache A1 c))) = max_count c ->
    rg_mapped_fa (a_reg A1 c) < 4 * (Z.of_nat (length (rg_free (a_reg A1 c))) + max_count c / 2) ->
    KMORE rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A0 m0 md0 p n0 stkobj lo hi TS xs2 xs5 A1 b0 i more scr ->
    KDONE rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A0 m0 md0 p n0 stkobj lo hi TS xs2 xs5 A1 b0 i more scr ->
    srealizes rsegs (it_cfgG spd gp s10 s11 F fc A1 m1 md1 b0 (Z.of_nat i) dorec_callblk ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6') TS.
  Definition step_sec_stmt : Prop :=
    forall (rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (A0 : AState) (m0 : mem) (md0 : Model) (p n0 stkobj lo hi : Z) (TS : TSet) (xs2 xs5 : word)
           (A1 : AState) (m1 : mem) (md1 : Model) (b0 : batch) (i : nat) (more : list batch) (scr : list byte)
           (ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) (s : chunkS) (n : Z),
    alloc_ceiling <= lo -> lo <= bv_unsigned spd - 4096 -> bv_unsigned spd <= hi -> hi <= 2^47 -> bv_unsigned spd mod 16 = 0 ->
    (forall a, newblk p n0 a -> a < alloc_ceiling) ->
    CURG rac spd s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 A0 m0 md0 p n0 stkobj lo hi xs2 xs5 A1 m1 md1 (Some (b0, i)) more scr ->
    nth_error (ba_entries b0) i = Some (QE (ChS s) n) ->
    KMORE rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A0 m0 md0 p n0 stkobj lo hi TS xs2 xs5 A1 b0 i more scr ->
    KDONE rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A0 m0 md0 p n0 stkobj lo hi TS xs2 xs5 A1 b0 i more scr ->
    srealizes rsegs (it_cfgG spd gp s10 s11 F fc A1 m1 md1 b0 (Z.of_nat i) dorec_callblk ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6') TS.
  Definition step_bdm_stmt : Prop :=
    forall (rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
           (A0 : AState) (m0 : mem) (md0 : Model) (p n0 stkobj lo hi : Z) (TS : TSet) (xs2 xs5 : word)
           (A1 : AState) (m1 : mem) (md1 : Model) (b0 : batch) (more : list batch) (scr : list byte)
           (ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s6' s7' s8' s9' : word),
    alloc_ceiling <= lo -> lo <= bv_unsigned spd - 4096 -> bv_unsigned spd <= hi -> hi <= 2^47 -> bv_unsigned spd mod 16 = 0 ->
    (forall a, newblk p n0 a -> a < alloc_ceiling) ->
    CURG rac spd s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 A0 m0 md0 p n0 stkobj lo hi xs2 xs5 A1 m1 md1 (Some (b0, length (ba_entries b0))) more scr ->
    Z.of_nat (length (pk_chunks (a_cache A1 kQuarantineBatchClass))) = max_count kQuarantineBatchClass ->
    rg_mapped_fa (a_reg A1 kQuarantineBatchClass) < 4 * (Z.of_nat (length (rg_free (a_reg A1 kQuarantineBatchClass))) + max_count kQuarantineBatchClass / 2) ->
    KHEAD rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A0 m0 md0 p n0 stkobj lo hi TS xs2 xs5 A1 more scr ->
    KEXIT rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A0 m0 md0 p n0 stkobj lo hi TS xs2 xs5 A1 ->
    srealizes rsegs (blk_cfgG spd gp s10 s11 F fc A1 m1 md1 b0 ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s6' s7' s8' s9') TS.
End Stmts.

Section CoreF2.
Context {Clg : Ceiling}.
  Hypothesis SPDM : step_pdm_stmt.
  Hypothesis SSEC : step_sec_stmt.
  Hypothesis SBDM : step_bdm_stmt.

  (* [comment removed for export] *)
  Definition dcore_covered2 (A : AState) (p n0 : Z) : Prop :=
    p = 0 \/
    kQuarantineMaxSize < n0 \/
    (n0 <= kQuarantineMaxSize /\
     (   (a_qthread A <> [] /\ Z.of_nat (length (ba_entries (last (a_qthread A) (BA 0 [])))) < kQuarantineBatchCount)
      \/ (a_qthread A = [] /\ pk_chunks (a_cache A kQuarantineBatchClass) <> [])
      \/ (a_qthread A <> [] /\ Z.of_nat (length (ba_entries (last (a_qthread A) (BA 0 [])))) = kQuarantineBatchCount /\
          pk_chunks (a_cache A kQuarantineBatchClass) <> []))).

  (* [comment removed for export] *)
  Definition dealloc_core_restF : Prop :=
    forall (rac spd gp tp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AState) (p n0 stkobj lo hi : Z) (key : list Z) (T : TSet),
      dealloc_core_pre rac spd tp m md A p n0 stkobj lo hi key ->
      ~ dcore_covered2 A p n0 ->
      dealloc_core_K rac spd gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md A p n0 lo hi T ->
      srealizes (cl_segs LPA) (mkCfg (dealloc_entry_ms rac spd gp tp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p stkobj) md) T.

  Theorem dealloc_core_of_restF : dealloc_core_restF -> dealloc_core_cps.
  Proof.
    intros REST. apply dealloc_core_of_rest. unfold dealloc_core_rest.
    intros rac spd gp tp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A p n0 stkobj lo hi key T PRE NCOV KK.
    destruct (classic (dcore_covered2 A p n0)) as [COV|NCOV2]; [| exact (REST rac spd gp tp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A p n0 stkobj lo hi key T PRE NCOV2 KK)].
    pose proof PRE as PRE'. unfold dealloc_core_pre in PRE'. cbv zeta in PRE'.
    (first [ dand19 PRE' as AI MI LV IAT TP CEIL LOW SPHI HISP SPA RA2 ST SMH STLO STHI STO TRW KEYU KR | destruct PRE' as (AI & MI & LV & IAT & TP & CEIL & LOW & SPHI & HISP & SPA & RA2 & ST & SMH & STLO & STHI & STO & TRW & KEYU & KR) ]).
    subst tp. pose proof KK as KK0. unfold dealloc_core_K in KK. cbv zeta in KK.
    cbn [cl_segs cl_free_pc LPA] in MI, KK |- *.
    destruct COV as [P0|[BIGN|(NQ & ARMS)]]; [exfalso; apply NCOV; left; exact P0| exfalso; apply NCOV; right; left; exact BIGN|].
    assert (PNZ : p <> 0) by (intros E; apply NCOV; left; exact E).
    assert (HL : as_live A p = Some n0) by (destruct LV as [[E _]|LV]; [exfalso; exact (PNZ E)| exact LV]).
    (* [comment removed for export] *)
    assert (VB : forall a, newblk p n0 a -> a < alloc_ceiling).
    { intros a Ha. pose proof alloc_ceiling_val as CE. (first [ pose proof ((free_geom A m md p n0 AI HL)) as dR_2; dand4 dR_2 as PAL PLO PCE PHI | destruct (free_geom A m md p n0 AI HL) as (PAL & PLO & PCE & PHI) ]). destruct (free_n0 A m md p n0 AI HL) as [NR _].
      unfold newblk, blk in Ha. destruct Ha as [Ha|[_ Ha]].
      - clear -Ha PHI CE NR. lia.
      - unfold sh in Ha. clear -Ha PHI CE NR. kung_all.
        assert (p / 8 <= 2^44) by (apply Z.div_le_upper_bound; lia).
        assert ((n0 + 7) / 8 <= n0) by (apply Z.div_le_upper_bound; lia). unfold REQ_MAX in NR. lia. }
    (* [comment removed for export] *)
    assert (NCT : forall qb', ctail_covered A qb' -> dcore_covered A p n0 -> False) by (intros qb' _ C; exact (NCOV C)).
    unfold kQuarantineMaxSize in NQ.
    set (SP := fun A1 m1 md1 b0 i more scr ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' c k n =>
                 SPDM rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A m md p n0 stkobj lo hi T (Z_to_bv 64 n0) (Z_to_bv 64 (p + -16))
                      A1 m1 md1 b0 i more scr ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' c k n CEIL LOW SPHI HISP SPA VB).
    set (SS := fun A1 m1 md1 b0 i more scr ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s n =>
                 SSEC rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A m md p n0 stkobj lo hi T (Z_to_bv 64 n0) (Z_to_bv 64 (p + -16))
                      A1 m1 md1 b0 i more scr ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s n CEIL LOW SPHI HISP SPA VB).
    set (SB := fun A1 m1 md1 b0 more scr ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s6' s7' s8' s9' =>
                 SBDM rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A m md p n0 stkobj lo hi T (Z_to_bv 64 n0) (Z_to_bv 64 (p + -16))
                      A1 m1 md1 b0 more scr ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s6' s7' s8' s9' CEIL LOW SPHI HISP SPA VB).
    (* [comment removed for export] *)
    assert (TKE : forall qb', ~ ctail_covered A qb' ->
              (a_qglobal A = [] /\ kQuarantineCacheSize < qb' /\ kQuarantineMaxSize < qb') \/
              (a_qglobal A <> [] /\ kQuarantineCacheSize < qb' /\ kQuarantineMaxSize < q_bytes (a_qglobal A) + qb')).
    { intros qb' NC. unfold ctail_covered in NC.
      destruct (a_qglobal A) as [|g r] eqn:EG.
      - left. split; [reflexivity|]. cbn in NC. clear -NC. lia.
      - right. split; [discriminate|]. rewrite <- EG in NC |- *. clear -NC. lia. }
    destruct ARMS as [(QNE & ROOM)|[(QTE & NE24)|(QNE & FULL & NE24)]].
    - destruct (TKE (q_bytes (a_qthread A) + n0) ltac:(intros C; apply NCOV; right; right; split; [unfold kQuarantineMaxSize; exact NQ|]; left; exact (conj QNE (conj ROOM C)))) as [(QGE & C1 & C2)|(QGN & C1 & C2)].
      + exact (dealloc_fastR rac spd gp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A p n0 stkobj lo hi key T
                 AI MI HL IAT CEIL LOW SPHI HISP SPA RA2 ST SMH STLO STHI STO TRW KEYU KR NQ KK VB SP SS SB T0 QNE ROOM (conj C1 (conj QGE C2))).
      + exact (dealloc_fastR rac spd gp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A p n0 stkobj lo hi key T
                 AI MI HL IAT CEIL LOW SPHI HISP SPA RA2 ST SMH STLO STHI STO TRW KEYU KR NQ KK VB SP SS SB TA QNE ROOM (conj C1 (conj QGN C2))).
    - destruct (TKE (n0 + kQuarantineBatchBytes) ltac:(intros C; apply NCOV; right; right; split; [unfold kQuarantineMaxSize; exact NQ|]; right; left; exact (conj QTE (conj NE24 C)))) as [(QGE & C1 & C2)|(QGN & C1 & C2)].
      + exact (dealloc_new0R rac spd gp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A p n0 stkobj lo hi key T
                 AI MI HL IAT CEIL LOW SPHI HISP SPA RA2 ST SMH STLO STHI STO TRW KEYU KR NQ KK VB SP SS SB T0 QTE NE24 (conj C1 (conj QGE C2))).
      + exact (dealloc_new0R rac spd gp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A p n0 stkobj lo hi key T
                 AI MI HL IAT CEIL LOW SPHI HISP SPA RA2 ST SMH STLO STHI STO TRW KEYU KR NQ KK VB SP SS SB TA QTE NE24 (conj C1 (conj QGN C2))).
    - destruct (TKE (q_bytes (a_qthread A) + n0 + kQuarantineBatchBytes) ltac:(intros C; apply NCOV; right; right; split; [unfold kQuarantineMaxSize; exact NQ|]; right; right; exact (conj QNE (conj FULL (conj NE24 C))))) as [(QGE & C1 & C2)|(QGN & C1 & C2)].
      + exact (dealloc_newfullR rac spd gp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A p n0 stkobj lo hi key T
                 AI MI HL IAT CEIL LOW SPHI HISP SPA RA2 ST SMH STLO STHI STO TRW KEYU KR NQ KK VB SP SS SB T0 QNE FULL NE24 (conj C1 (conj QGE C2))).
      + exact (dealloc_newfullR rac spd gp t0 t1 t2 s0 s1 a2 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A p n0 stkobj lo hi key T
                 AI MI HL IAT CEIL LOW SPHI HISP SPA RA2 ST SMH STLO STHI STO TRW KEYU KR NQ KK VB SP SS SB TA QNE FULL NE24 (conj C1 (conj QGN C2))).
  Qed.
End CoreF2.
