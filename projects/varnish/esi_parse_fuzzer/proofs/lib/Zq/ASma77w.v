(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM ACells.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts ARtSscs AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ASm_mu9.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ASm_mu9.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ASm_mu9.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ASm_mu9 ATransp AMalmys AFreeSF1.

Module AFreeSF.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM ACells.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts ARtSscs AMTac ARt_png.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ASm_mu9.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ATransp AMalmys AFreeSF1.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_png OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d.ARt_m2s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASm_mu9.ARt2ewq OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeSF1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.solve_load_guarded | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Notation wz z := (Z_to_bv 64 z) (only parsing).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kSpaceReserve, kMaxSize in *.

(* [comment removed for export] *)
Lemma sf_mrd_some_neq : forall (mm : mem) a b, mrd rsegs mm (wa a) = Some b -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) /\ 0 <= a < 2^64 -> mm (Z_to_bv 64 a) <> None.
Proof.
  intros mm a b H [Ha Hr]. unfold mrd, wa in H. destruct (mm (Z_to_bv 64 a)) eqn:E; [congruence|]. exfalso.
  rewrite pa_seg_rom_none in H; [discriminate|]. rewrite unsigned_lit by lia. exact Ha.
Qed.
Lemma sf_mrd_some_eq : forall (mm : mem) a b, mm a <> None -> mrd rsegs mm a = Some b -> mm a = Some b.
Proof. intros mm a b H1 H2. unfold mrd in H2. destruct (mm a); congruence. Qed.

(* [comment removed for export] *)
Lemma sf_pa_wx : wx_segs_nowrap rsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma sf_wmono_NN : forall (v v' : mem) a, wmono rsegs v v' -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> 0 <= a < 2^64 ->
  v (wz a) <> None -> v' (wz a) <> None.
Proof.
  intros v v' a WM Ha Hr Hv. specialize (WM (wz a)). unfold wview in WM.
  rewrite unsigned_lit in WM by lia. rewrite (pa_find_segment_none a 1 ltac:(lia) Ha) in WM.
  destruct (v (wz a)); [| congruence]. destruct (v' (wz a)); [congruence|]. exfalso. apply WM; [discriminate| reflexivity].
Qed.

Section SFree7.
  Context {Clg : Ceiling}.
  Variables (ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AState) (ff sz : Z) (age : nat) (T : TSet).
  Hypothesis AI : @pa_ainv _ DepotRepL A m md.
  Hypothesis MI : mem_inv rsegs (aview_of (pa_hull A) m).
  Hypothesis FF : as_fframe A ff = Some (7, age).
  Hypothesis SZ : 0 < sz <= fsize 7.
  Hypothesis SZ8 : sz mod 8 = 0.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis RA2 : bv_unsigned ra mod 2 = 0.
  Hypothesis CEIL : alloc_ceiling <= bv_unsigned sp - ASTK.
  Hypothesis SM : mapped (aview_of (pa_hull A) m) (bv_unsigned sp - ASTK) ASTK.
  Hypothesis KK : forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (md' : Model),
          let A' := as_release A ff in
          let v' := aview_of (pa_hull A') m' in
          @pa_ainv _ DepotRepL A' m' md' -> mem_inv (cl_segs LPA) v' -> amd_frame md md' ->
          frame_ok LPA (pa_owned A) (pa_owned A') (bv_unsigned sp) ASTK (frm ff 7) nowhere (aview_of (pa_hull A) m) v' ->
          srealizes (cl_segs LPA) (mkCfg (MS (mkR ra sp gp (cl_tp LPA) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom (cl_segs LPA))) md') T.

  Theorem pa_sfree7 :
    srealizes (cl_segs LPA) (mkCfg (MS (mkR ra sp gp (cl_tp LPA) t0 t1 t2 s0 s1 (wz ff) (wz sz) a2 a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (cl_sfree_pc LPA 7) fc None m (seg_rom (cl_segs LPA))) md) T.
  Proof.
    cbn [cl_segs cl_sfree_pc LPA pa_sfree] in MI, KK |- *.
    pose proof (ai_wf _ _ _ _ _ _ _ AI) as WF0. pose proof alloc_ceiling_val as CE.
    pose proof (hit_stk A m sp CEIL SM) as ST. pose proof (hit_sp47 A m md sp AI CEIL SM) as SPH. unfold ASTK in *.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof (zr_word ra) as RAR; unfold inr64 in RAR.
    (first [ pose proof ((sf_geom A m md ff age AI FF)) as dR_1; dand14 dR_1 as Eff M8 OBJ CEf OBJF CEl AP1 AP2 R1 R2 FR SH1 SH2 NB | pose proof (sf_geom A m md ff age AI FF) as (Eff & M8 & OBJ & CEf & OBJF & CEl & AP1 & AP2 & R1 & R2 & FR & SH1 & SH2 & NB) ]).
    pose proof (sf_SFP A m md ff age AI FF) as SFP. pose proof (sf_FLG A m md ff age AI FF) as FLG.
    destruct (sf_SHC A m md ff age AI FF sz ltac:(lia)) as [oldsh SHC].
    set (fl := sf_fl A age) in *.
    (first [ pose proof ((aobj_facts _ _ OBJ)) as dR_2; dand5 dR_2 as O1 O2 O3 O4 O5 | pose proof (aobj_facts _ _ OBJ) as (O1 & O2 & O3 & O4 & O5) ]). (first [ pose proof ((aobj_facts _ _ OBJF)) as dR_3; dand5 dR_3 as Q1 Q2 Q3 Q4 Q5 | pose proof (aobj_facts _ _ OBJF) as (Q1 & Q2 & Q3 & Q4 & Q5) ]).
    assert (LO : bv_unsigned sp - 8192 <= bv_unsigned sp - 96) by lia.
    pose proof (sfree7_ok ra sp gp (cl_tp LPA) t0 t1 t2 s0 s1 (wz ff) (wz sz) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
                  (aview_of (pa_hull A) m) ff fl sz (bv_unsigned sp - 8192) (Z_to_bv 8 1) oldsh
                  MI ST LO CEIL eq_refl eq_refl SZ8 ltac:(lia) M8 OBJ CEf OBJF CEl (hit_PCo A m md AI) SFP FLG SHC AP1
                  ltac:(clear - AP2 SZ; pose proof (Z.div_le_mono sz (fsize 7) 8 ltac:(lia) ltac:(lia)); lia) RA2) as EVW.
    idtac "walkSF ok".
    destruct (asI_minv A m md AI) as [HMI HH].
    eapply (srz_evt_restrict rsegs (pa_hull A) (asI_hull_segs A m md AI) sf_pa_wx _ (pa_eager A) _ _ md T HMI HH).
    { rewrite restrict_MS. exact EVW. }
    intros msr' md' HQ HI' Hsame Hcl.
    (first [ dex16 HQ as t0' t1' t2' a0' a1' a2'' a3' a4' a5' a6' a7' t3' t4' t5' t6' v'; dand7 HQ as -> MU WM' MI' ST' PFL PSH | dand23 HQ as t0' t1' t2' a0' a1' a2'' a3' a4' a5' a6' a7' t3' t4' t5' t6' v' -> MU WM' MI' ST' PFL PSH | destruct HQ as (t0' & t1' & t2' & a0' & a1' & a2'' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & v' & -> & MU & WM' & MI' & ST' & PFL & PSH) ]).
    rewrite unrestrict_MS. cbn [ms_mem] in Hcl.
    pose proof (same_but_materialized_frame _ _ Hsame) as FRM.
    assert (VIEW : aview_of (pa_hull A) (munrestrict (hidc (pa_hull A)) m v') = v').
    { unfold aview_of. rewrite mrestrict_munrestrict. apply mrestrict_clean_id. exact Hcl. }
    assert (NN : forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> a < 2^64 -> aview_of (pa_hull A) m (wz a) <> None -> v' (wz a) <> None).
    { intros a H0 H1 H2. apply (sf_wmono_NN _ _ a WM'); lia. }
    (* [comment removed for export] *)
    assert (AG : forall a, 0 <= a < 2^64 -> ~ (bv_unsigned sp - 8192 <= a < bv_unsigned sp) -> a <> fl -> ~ (sh ff <= a < sh ff + sz / 8) ->
                 v' (wz a) = aview_of (pa_hull A) m (wz a)).
    { intros a Ha NS NF NSH. apply MU. rewrite unsigned_lit by lia. cbn [outside]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; intros X; [apply NS| apply NF| apply NSH]; clear -X; lia. }
    (* [comment removed for export] *)
    (first [ pose proof ((asI_release_spec A m md ff 7 age AI FF)) as dR_5; dand11 dR_5 as RS1 RS2 RS3 RS4 RS5 RS6 RSP RS7 RS8 RS9 RS10 | pose proof (asI_release_spec A m md ff 7 age AI FF) as (RS1 & RS2 & RS3 & RS4 & RS5 & RS6 & RSP & RS7 & RS8 & RS9 & RS10) ]).   (* [comment removed for export] *)
    (first [ pose proof ((asI_frame_ok A m md ff 7 age AI FF)) as dR_6; dand11 dR_6 as _ _ _ _ _ _ MP1 _ MP2 NOF NOS | pose proof (asI_frame_ok A m md ff 7 age AI FF) as (_ & _ & _ & _ & _ & _ & MP1 & _ & MP2 & NOF & NOS) ]).
    (* [comment removed for export] *)
    assert (FLP0 : aview_of (pa_hull A) m (wz fl) <> None).
    { destruct FLG as [[_ B] _]. cbn [cells_bytes cbytes app] in B. pose proof (proj2 (proj2 B) 0%nat ltac:(cbn; lia)) as B0.
      cbn [nth_error Z.of_nat] in B0. rewrite Z.add_0_r in B0. apply (sf_mrd_some_neq _ _ _ B0). split; [exact Q4| lia]. }
    assert (FLP : v' (wz fl) <> None) by (apply NN; [lia| exact Q4| lia| exact FLP0]).
    assert (FL0 : v' (wz fl) = Some (Z_to_bv 8 0)).
    { pose proof (proj2 (proj2 PFL) 0%nat ltac:(cbn; lia)) as B0. cbn [nth_error Z.of_nat] in B0. rewrite Z.add_0_r in B0.
      exact (sf_mrd_some_eq v' _ _ FLP B0). }
    assert (AI' : @pa_ainv _ DepotRepL (as_release A ff) (munrestrict (hidc (pa_hull A)) m v') md').
    { pose proof (asI_frame A [ff] m (munrestrict (hidc (pa_hull A)) m v') md md' AI
                    ltac:(intros g [<-|[]]; exists 7, age; exact FF) (NoDup_singleton ff)) as FRX.
      cbv zeta in FRX. cbn [fold_left] in FRX. rewrite VIEW in FRX. apply FRX; clear FRX.
      - intros a Ha. unfold munrestrict. rewrite Ha. reflexivity.
      - intros a OW. destruct (Z.eq_dec a fl) as [->|NF].
        + right. exists ff, 7, age, fl. split; [left; reflexivity|]. split; [exact FF|]. split; [reflexivity|]. split.
          * destruct SFP as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. unfold saved_flag_ptr in B. exact B.
          * exact FL0.
        + left. apply AG; [exact (owned_lt64 A m md a AI OW)| | exact NF|].
          * intros X. destruct (asI_owned_where A m md a AI OW) as [S|HZ]; [cbn [cl_static LPA] in S; pose proof (pa_static_low a S); clear -X H CEIL CE; lia| unfold heap_zone in HZ; clear -X HZ CEIL; lia].
          * intros X. apply (NOS (a - sh ff) ltac:(clear -X SZ; pose proof (Z.div_le_mono sz (fsize 7) 8 ltac:(lia) ltac:(lia)); lia)). replace (sh ff + (a - sh ff)) with a by lia. exact OW.
      - intros g k' age' fa [<-|[]] Hg B.
        rewrite FF in Hg. injection Hg as <- <-.
        assert (Efa : wz fa = wz fl).
        { destruct SFP as [_ B0]. cbn [cells_bytes cbytes] in B0. rewrite app_nil_r in B0. unfold saved_flag_ptr in B0.
          pose proof (bytes_at_func _ (aview_of (pa_hull A) m) _ _ _ B B0 ltac:(rewrite !length_le8; reflexivity)) as LE.
          exact (ALogic2.le8_wz_inj _ _ LE). }
        rewrite Efa. exact FL0.
      - intros a SHD. pose proof (asI_shared_where a SHD) as SW. cbn [cl_rw_lo cl_image_hi LPA] in SW. apply AG; [clear -SW; lia| clear -SW CEIL CE; lia| clear -SW Q4; lia| clear -SW SH1 SZ; lia].
      - intros a Ha NI Hv. destruct (decide (bv_unsigned sp - 8192 <= a < bv_unsigned sp)) as [X|X].
        + (first [ dand3 ST' as _ _ STW | destruct ST' as (_ & _ & STW) ]). destruct (STW a X) as [_ [bb Hb]]. apply (sf_mrd_some_neq v' _ _ Hb). unfold in_image in NI. cbn [cl_image_lo cl_image_hi LPA] in NI. clear -NI Ha. lia.
        + apply NN; [lia| unfold in_image in NI; cbn [cl_image_lo cl_image_hi LPA] in NI; clear -NI Ha; lia| lia| exact Hv].
      - intros a Ha NI Hv'. destruct (decide (bv_unsigned sp - 8192 <= a < bv_unsigned sp)) as [X|X].
        + replace a with (bv_unsigned sp - 8192 + (a - (bv_unsigned sp - 8192))) by lia. apply SM. lia.
        + destruct (Z.eq_dec a fl) as [->|NF].
          * exact FLP0.
          * destruct (decide (sh ff <= a < sh ff + sz / 8)) as [Y|Y].
            -- replace a with (sh ff + (a - sh ff)) by lia. apply MP2. clear -Y SZ. pose proof (Z.div_le_mono sz (fsize 7) 8 ltac:(lia) ltac:(lia)). lia.
            -- rewrite <- (AG a Ha X NF Y). exact Hv'.
      - exact HI'.
      - exact Hsame. }
    replace (ret_pc ra) with (ret_pc ra) by reflexivity.
    eapply (KK t0' t1' t2' a0' a1' a2'' a3' a4' a5' a6' a7' t3' t4' t5' t6' (munrestrict (hidc (pa_hull A)) m v') md').
    - exact AI'.
    - rewrite RS8, VIEW. exact MI'.
    - unfold amd_frame. (first [ dand18 FRM as X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15 X16 X17 Xr | destruct FRM as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16 & X17 & Xr) ]).
      rewrite X2, X17, HH. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [assumption| reflexivity].
    - rewrite RS8, VIEW. unfold frame_ok. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits.
      + intros a Ha NO NO' NW _ NV _. apply AG; [exact Ha| unfold ASTK in NW; exact NW| |].
        * intros ->. apply NO. exact (sf_fl_owned A m md ff age AI FF).
        * intros Y. apply NV. unfold frm. right. clear -Y SZ. pose proof (Z.div_le_mono sz (fsize 7) 8 ltac:(lia) ltac:(lia)). lia.
      + intros a Ha NI Hv. right. right. apply NN; [lia| unfold in_image in NI; cbn [cl_image_lo cl_image_hi LPA] in NI; clear -NI Ha; lia| lia| exact Hv].
      + eapply mapped_mono; [exact SM|]. intros i Hi. unfold ASTK in *. apply NN; lia.
      + intros a Ha [].
      + intros a Ha O'. apply (proj1 (RS10 a)) in O'. destruct O' as [O|[F1|F2]]; [left; exact O| right; left; unfold frm; left; lia| right; left; unfold frm; right; lia].
      + intros a Ha O NO'. exfalso. apply NO'. apply (proj2 (RS10 a)). left. exact O.
      + intros a Ha FRM'. left. apply (proj2 (RS10 a)). unfold frm in FRM'.
        destruct (decide (ff + fsize 7 - 8 <= a < ff + fsize 7)) as [E8|E8]; [| right; lia].
        left. exact (sf_tail_owned A m md ff age AI FF a E8).
  Qed.
End SFree7.

(* [comment removed for export] *)
Section Full.
  Context {Clg : Ceiling}.
  Theorem pa_sfree_full : @pa_sfree_obligation _ DepotRepL.
  Proof.
    unfold pa_sfree_obligation. intros k ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A ff sz age T.
    cbv zeta. intros AI MI K7 A0 A1 SZ SZM FF TP SPA RA2 CEIL SM KK. subst k a0 a1 tp.
    eapply (pa_sfree7 ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A ff sz age T); try eassumption; try exact (SZM ltac:(lia)).
  Qed.
End Full.
End AFreeSF.


Module ASmawx5.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM ACells.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ATransp ARtStmts ARtSscs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ASm_mu9.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMalmys AFreeSF1.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASm_mu9.ASmStmt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeSF1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.solve_load_guarded | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image].
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
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition bumpk (k : Z) (f : fframe) : fframe :=
  if Z.eqb (ff_class f) k then FF (ff_class f) (S (ff_age f)) else f.

Definition acq_frames (k ff : Z) (g : gmap Z fframe) : gmap Z fframe :=
  <[ ff := FF k 0%nat ]> (fmap (bumpk k) g).

Definition acq_hint (k : Z) (h : Z -> Z) : Z -> Z :=
  fun j => if Z.eqb j k then (h k + 1) mod 2^64 else h j.

Definition as_acquire (A : AState) (k ff : Z) : AState :=
  set_fhint (set_fframes A (acq_frames k ff (a_fframes A))) (acq_hint k (a_fhint A)).

(* [comment removed for export] *)
Definition acq_pos (A : AState) (k : Z) : Z := (a_fhint A k) mod fslots k.
Definition acq_ff (A : AState) (k : Z) : Z := fframe_addr (a_fs A) k (acq_pos A k).
Definition acq_fl (A : AState) (k : Z) : Z := fflag_addr (a_fs A) k (acq_pos A k).

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fslots_dvd64 : forall k, 0 <= k <= 10 -> exists q, 0 < q /\ 2^64 = fslots k * q.
Proof.
  intros k Hk. unfold fslots, kFakeStackSizeLog.
  assert (E : 2^64 = 2^(20 - 6 - k) * 2^(44 + 6 + k)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  exists (2^(44 + 6 + k)). split; [apply Z.pow_pos_nonneg; lia| exact E].
Qed.

Lemma mod_mod_dvd : forall a n q, 0 < n -> 0 < q -> (a mod (n * q)) mod n = a mod n.
Proof.
  intros a n q Hn Hq. rewrite Z.rem_mul_r by lia.
  rewrite (Z.mul_comm n), Z_mod_plus_full. apply Z.mod_mod. lia.
Qed.

(* [comment removed for export] *)

Lemma ff_pos_zero : forall h k, 0 <= k <= 10 -> ff_pos ((h + 1) mod 2^64) k 0 = h mod fslots k.
Proof.
  intros h k Hk. unfold ff_pos. cbn [Z.of_nat]. rewrite Z.sub_0_r.
  (first [ pose proof ((fslots_dvd64 k Hk)) as dR_2; dex1 dR_2 as q; destruct dR_2 as [Hq E] | pose proof ((fslots_dvd64 k Hk)) as dR_2; dand3 dR_2 as q Hq E | destruct (fslots_dvd64 k Hk) as (q & Hq & E) ]). pose proof (fslots_pos k Hk) as SP.
  rewrite E. rewrite <- Zminus_mod_idemp_l. rewrite mod_mod_dvd by lia. rewrite Zminus_mod_idemp_l. f_equal. lia.
Qed.

Lemma ff_pos_bump : forall h k age, 0 <= k <= 10 -> ff_pos ((h + 1) mod 2^64) k (S age) = ff_pos h k age.
Proof.
  intros h k age Hk. unfold ff_pos. rewrite Nat2Z.inj_succ.
  (first [ pose proof ((fslots_dvd64 k Hk)) as dR_3; dex1 dR_3 as q; destruct dR_3 as [Hq E] | pose proof ((fslots_dvd64 k Hk)) as dR_3; dand3 dR_3 as q Hq E | destruct (fslots_dvd64 k Hk) as (q & Hq & E) ]). pose proof (fslots_pos k Hk) as SP. rewrite E.
  replace ((h + 1) mod (fslots k * q) - 1 - Z.succ (Z.of_nat age)) with ((h + 1) mod (fslots k * q) - (2 + Z.of_nat age)) by lia.
  rewrite <- Zminus_mod_idemp_l. rewrite mod_mod_dvd by lia. rewrite Zminus_mod_idemp_l. f_equal. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma acq_frames_lookup_new : forall k ff g, acq_frames k ff g !! ff = Some (FF k 0%nat).
Proof. intros. unfold acq_frames. apply lookup_insert_eq. Qed.
Lemma acq_frames_lookup_old : forall k ff g x, x <> ff -> acq_frames k ff g !! x = bumpk k <$> (g !! x).
Proof. intros k ff g x NE. unfold acq_frames. rewrite lookup_insert_ne by (intros E; apply NE; symmetry; exact E). apply lookup_fmap. Qed.
Lemma acq_frames_inv : forall k ff g x f', acq_frames k ff g !! x = Some f' ->
  (x = ff /\ f' = FF k 0%nat) \/ (x <> ff /\ exists f, g !! x = Some f /\ f' = bumpk k f).
Proof.
  intros k ff g x f' H. destruct (decide (x = ff)) as [->|NE].
  - left. rewrite acq_frames_lookup_new in H. split; congruence.
  - right. split; [exact NE|]. rewrite acq_frames_lookup_old in H by exact NE.
    destruct (g !! x) as [f|]; cbn in H; [| discriminate]. exists f. split; congruence.
Qed.
Lemma bumpk_class : forall k f, ff_class (bumpk k f) = ff_class f.
Proof. intros. unfold bumpk. destruct (Z.eqb_spec (ff_class f) k); reflexivity. Qed.
Lemma bumpk_pos : forall k h f, 0 <= ff_class f <= 10 ->
  ff_pos (acq_hint k h (ff_class (bumpk k f))) (ff_class (bumpk k f)) (ff_age (bumpk k f)) = ff_pos (h (ff_class f)) (ff_class f) (ff_age f).
Proof.
  intros k h f Hk. unfold bumpk, acq_hint. destruct (Z.eqb_spec (ff_class f) k) as [E|NE]; cbn [ff_class ff_age].
  - rewrite E, Z.eqb_refl. apply ff_pos_bump. lia.
  - destruct (Z.eqb_spec (ff_class f) k); [congruence|]. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma probe_pos_not_aged : forall h k age, 0 <= k <= 10 -> Z.of_nat age + 2 < fslots k ->
  ff_pos h k age <> h mod fslots k.
Proof.
  intros h k age Hk Hage E. unfold ff_pos in E. pose proof (fslots_pos k Hk) as SP.
  set (s := fslots k) in *.
  pose proof (Z_div_mod_eq_full h s) as D1. pose proof (Z_div_mod_eq_full (h - 1 - Z.of_nat age) s) as D2.
  rewrite E in D2. set (q1 := h / s) in *. set (q2 := (h - 1 - Z.of_nat age) / s) in *.
  assert (D : s * (q1 - q2) = 1 + Z.of_nat age) by lia.
  destruct (Z.le_gt_cases 1 (q1 - q2)) as [C|C].
  - pose proof (Z.mul_le_mono_nonneg_l 1 (q1 - q2) s ltac:(lia) C). lia.
  - pose proof (Z.mul_le_mono_nonneg_l (q1 - q2) 0 s ltac:(lia) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Section SlotFacts.
  Context {Clg : Ceiling}.
  Lemma slot_facts : forall A k pos, WF AL_pboth A -> 0 <= k <= 10 -> 0 <= pos < fslots k ->
    let fs := a_fs A in let ff := fframe_addr fs k pos in
    fs + kFakeFramesOffset <= ff /\ ff + fsize k <= fs + kFakeStackBytes /\
    app_rangeA AL_pboth fs kFakeStackBytes /\ fs + kFakeStackBytes <= alloc_ceiling /\ fs mod 4096 = 0 /\
    64 <= fsize k <= 65536 /\ ff mod 64 = 0 /\ ff mod Z.min (fsize k) 4096 = 0 /\
    sh fs <= sh ff /\ sh ff + fsize k / 8 <= sh fs + kFakeStackBytes / 8 /\
    0x7fff8200 <= sh fs /\ sh fs + kFakeStackBytes / 8 <= kHighMemBeg.
  Proof.
    intros A k pos W K PR fs ff. pose proof alloc_ceiling_val as CE.
    (first [ pose proof ((place_fs A W)) as dR_4; dand3 dR_4 as FS1 FS2 FSM | pose proof (place_fs A W) as (FS1 & FS2 & FSM) ]). unfold a_fs in *. subst fs.
    (first [ pose proof ((fframe_addr_range (p_fs (a_pl A)) k _ K PR)) as dR_5; dand3 dR_5 as R1 R2 R3 | pose proof (fframe_addr_range (p_fs (a_pl A)) k _ K PR) as (R1 & R2 & R3) ]). fold ff in R1, R2, R3.
    pose proof (fsize_pos _ K) as [FS _]. (first [ pose proof ((fsize_facts _ K)) as dR_6; dand4 dR_6 as M8 C8 D8 M64 | pose proof (fsize_facts _ K) as (M8 & C8 & D8 & M64) ]).
    pose proof (fframe_addr_align (p_fs (a_pl A)) k pos K ltac:(lia) FSM) as AL. fold ff in AL.
    assert (M64f : ff mod 64 = 0).
    { subst ff. unfold fframe_addr, kFakeFramesOffset, kFakeStackSizeLog. unfold fsize.
      pose proof (Z_div_exact_full_2 (p_fs (a_pl A)) 4096 ltac:(lia) FSM) as Efs. rewrite Efs at 1.
      match goal with |- ?x mod 64 = 0 =>
        replace x with ((p_fs (a_pl A) / 4096 * 64 + 576 + 2 ^ 14 * k + 2 ^ k * pos) * 64) by ring end.
      apply Z_mod_mult. }
    pose proof (sh_ceil_le ff (fsize k) (p_fs (a_pl A)) kFakeStackBytes ltac:(apply (mod0_down _ 64 8); [exists 8; reflexivity| exact M64f])
      ltac:(apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact FSM]) eq_refl ltac:(unfold kFakeFramesOffset in *; lia) R3) as [S1 S2].
    rewrite C8 in S2.
    (first [ pose proof ((app_facts _ _ FS1)) as dR_7; dand5 dR_7 as G1 G2 G3 G4 G5 | pose proof (app_facts _ _ FS1) as (G1 & G2 & G3 & G4 & G5) ]).
    pose proof (sh_add (p_fs (a_pl A)) (kFakeStackBytes - 8) ltac:(apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact FSM]) eq_refl) as SA.
    change ((kFakeStackBytes - 8) / 8) with (kFakeStackBytes / 8 - 1) in SA.
    assert (X1 : p_fs (a_pl A) + kFakeFramesOffset <= ff) by (unfold kFakeFramesOffset in *; lia).
    assert (SR : 0x7fff8200 <= sh (p_fs (a_pl A)) /\ sh (p_fs (a_pl A)) + kFakeStackBytes / 8 <= kHighMemBeg).
    { destruct G5 as [LO|HI].
      - pose proof (sh_lowapp_range (p_fs (a_pl A)) ltac:(unfold kFakeStackBytes in *; lia)).
        pose proof (sh_lowapp_range (p_fs (a_pl A) + (kFakeStackBytes - 8)) ltac:(unfold kFakeStackBytes in *; lia)). unfold kHighMemBeg. lia.
      - pose proof (sh_high_range (p_fs (a_pl A)) ltac:(unfold kFakeStackBytes in *; lia)).
        pose proof (sh_high_range (p_fs (a_pl A) + (kFakeStackBytes - 8)) ltac:(unfold kFakeStackBytes in *; lia)).
        unfold kHighShadowMapBeg, kHighMemBeg in *. lia. }
    destruct SR as [SR1 X2].
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; first [assumption | lia].
  Qed.
End SlotFacts.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Probe.
  Context {Clg : Ceiling} {DR : DepotRep}.
  Variables (A : AState) (m : mem) (md : Model) (k : Z).
  Hypothesis AI : pa_ainv A m md.
  Hypothesis HK : 0 <= k <= 10.
  Hypothesis YOUNG : forall ff age, as_fframe A ff = Some (k, age) -> Z.of_nat age + 2 < fslots k.
  Let v := aview_of (pa_hull A) m.
  Let W : WF AL_pboth A. Proof. exact (ai_wf _ _ _ _ _ _ _ AI). Qed.
  Let R : arepr LPA AL_pboth [] A v. Proof. exact (ai_repr _ _ _ _ _ _ _ AI). Qed.

  Definition sm_h : Z := a_fhint A k.
  Definition sm_pos : Z := sm_h mod fslots k.
  Definition sm_ff : Z := fframe_addr (a_fs A) k sm_pos.
  Definition sm_fl : Z := fflag_addr (a_fs A) k sm_pos.

  #[using="W AI md m DR Clg"] Lemma sm_h_range : 0 <= sm_h < 2^64.
  Proof. (first [ pose proof ((wfF A W)) as dR_8; dand3 dR_8 as _ F2 _ | destruct (wfF A W) as (_ & F2 & _) ]). exact (F2 k). Qed.
  #[using="HK"] Lemma sm_pos_range : 0 <= sm_pos < fslots k.
  Proof. unfold sm_pos. apply Z.mod_pos_bound. pose proof (fslots_pos k HK). lia. Qed.

  #[using="YOUNG HK"] Lemma sm_not_live : ~ slot_live_ (a_fhint A) (a_fframes A) k sm_pos.
  Proof.
    ((first [ intro dR_38; dex2 dR_38 as ff f; dand3 dR_38 as Hf Hc Hp | intro dR_38; dand5 dR_38 as ff f Hf Hc Hp | intros (ff & f & Hf & Hc & Hp) ])).
    assert (FF : as_fframe A ff = Some (k, ff_age f)) by (unfold as_fframe, as_fframe_; rewrite Hf; cbn; rewrite Hc; reflexivity).
    exact (probe_pos_not_aged (a_fhint A k) k (ff_age f) HK (YOUNG _ _ FF) Hp).
  Qed.

  #[using="W YOUNG HK AI md m DR Clg"] Lemma sm_free_f : a_fframes A !! sm_ff = None.
  Proof.
    destruct (a_fframes A !! sm_ff) as [f|] eqn:Hf; [| reflexivity]. exfalso.
    (first [ pose proof ((wfF A W)) as dR_9; dand3 dR_9 as F1 _ _ | destruct (wfF A W) as (F1 & _ & _) ]). (first [ pose proof ((F1 _ f Hf)) as dR_10; dand3 dR_10 as K' E AG' | destruct (F1 _ f Hf) as (K' & E & AG') ]). cbv zeta in *. unfold ff_addr_of_ in E.
    pose proof sm_pos_range as PR. pose proof (ff_pos_range (a_fhint A (ff_class f)) (ff_class f) (ff_age f) K') as PR'.
    destruct (decide ((k, sm_pos) = (ff_class f, ff_pos (a_fhint A (ff_class f)) (ff_class f) (ff_age f)))) as [EQ|NE].
    - injection EQ as E1 E2. apply sm_not_live. exists sm_ff, f. split; [exact Hf|]. split; [symmetry; exact E1|]. rewrite E2, <- E1. reflexivity.
    - pose proof (fframe_addr_disjoint (a_fs A) k sm_pos (ff_class f) _ HK K' PR PR' NE) as D. unfold sm_ff in E. rewrite <- E in D.
      pose proof (fsize_pos k HK). pose proof (fsize_pos (ff_class f) K'). unfold sm_ff in D. lia.
  Qed.
  #[using="W YOUNG HK AI md m DR Clg"] Lemma sm_free : as_fframe A sm_ff = None.
  Proof. unfold as_fframe, as_fframe_. rewrite sm_free_f. reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="W HK AI md m DR"] Lemma sm_geom :
    sm_ff mod 8 = 0 /\ aobj sm_ff (fsize k) /\ sm_ff + fsize k <= alloc_ceiling /\
    aobj sm_fl 1 /\ sm_fl + 1 <= alloc_ceiling /\
    (sm_fl + 1 <= sm_ff \/ sm_ff + fsize k <= sm_fl) /\ (sm_fl + 1 <= sh sm_ff \/ sh sm_ff + fsize k / 8 <= sm_fl) /\
    a_fs A + kFakeFramesOffset <= sm_ff /\ sm_ff + fsize k <= a_fs A + kFakeStackBytes /\
    a_fs A + kFakeFlagsOffset <= sm_fl < a_fs A + kFakeFramesOffset - 16 /\
    0x7fff8200 <= sh sm_ff /\ sh sm_ff + fsize k / 8 <= kHighMemBeg /\ 0x60a000 <= sm_ff /\
    sm_ff mod 64 = 0 /\ sm_ff mod Z.min (fsize k) 4096 = 0 /\ 64 <= fsize k <= 65536 /\ fsize k mod 8 = 0 /\
    aobj (a_fs A) kFakeStackBytes /\ a_fs A + kFakeStackBytes <= alloc_ceiling /\ a_fs A mod 4096 = 0.
  Proof.
    pose proof alloc_ceiling_val as CE. pose proof sm_pos_range as PR.
    pose proof (slot_facts A k sm_pos W HK PR) as X. cbv zeta in X. fold sm_ff in X.
    (first [ dand12 X as R1 R2 FS1 FS2 FSM SZ M64 AL S1 S2 SR1 SR2 | destruct X as (R1 & R2 & FS1 & FS2 & FSM & SZ & M64 & AL & S1 & S2 & SR1 & SR2) ]).
    (first [ pose proof ((app_facts _ _ FS1)) as dR_12; dand5 dR_12 as G1 G2 G3 G4 G5 | pose proof (app_facts _ _ FS1) as (G1 & G2 & G3 & G4 & G5) ]).
    pose proof (fflag_addr_range (a_fs A) k sm_pos HK PR) as FR. fold sm_fl in FR.
    (first [ pose proof ((fsize_facts _ HK)) as dR_13; dand4 dR_13 as M8 _ D8 _ | pose proof (fsize_facts _ HK) as (M8 & _ & D8 & _) ]).
    unfold kFakeFramesOffset, kFakeFlagsOffset, kFakeStackBytes in *.
    assert (OBJ : aobj sm_ff (fsize k)).
    { apply (proj1 (aobj_app_rangeA _ _)). eapply app_rangeA_sub; [exact FS1| lia| lia| lia]. }
    assert (OBJF : aobj sm_fl 1).
    { apply (proj1 (aobj_app_rangeA _ _)). eapply app_rangeA_sub; [exact FS1| lia| lia| lia]. }
    assert (OBJS : aobj (a_fs A) 11571200) by (apply (proj1 (aobj_app_rangeA _ _)); exact FS1).
    assert (SHA : sm_fl + 1 <= sh sm_ff \/ sh sm_ff + fsize k / 8 <= sm_fl).
    { destruct G5 as [LO|HI].
      - left. unfold kLowShadowMapBeg in LO. lia.
      - right. unfold kHighMemBeg in *. lia. }
    assert (M8f : sm_ff mod 8 = 0) by (apply (mod0_down _ 64 8); [exists 8; reflexivity| exact M64]).
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try assumption; try lia.
  Qed.

  (* [comment removed for export] *)
  #[using="R W HK AI md DR"] Lemma sm_HINT : bytes_at rsegs v (a_fs A + 8 * k) (le8 (wz sm_h)).
  Proof.
    pose proof (ar_fsbase _ _ _ _ _ R) as (H0 & _). pose proof (H0 k HK) as X. unfold u64_at in X. fold v in X.
    pose proof sm_h_range as HR. unfold sm_h in HR |- *. rewrite (Z.mod_small _ _ HR) in X. exact X.
  Qed.
  #[using="R YOUNG HK AI md DR"] Lemma sm_FLAG : bytes_at rsegs v sm_fl [Z_to_bv 8 0].
  Proof.
    (first [ pose proof ((ar_fsflags _ _ _ _ _ R k sm_pos HK sm_pos_range)) as dR_14; dex1 dR_14 as b; destruct dR_14 as [U CASES] | pose proof ((ar_fsflags _ _ _ _ _ R k sm_pos HK sm_pos_range)) as dR_14; dand3 dR_14 as b U CASES | pose proof (ar_fsflags _ _ _ _ _ R k sm_pos HK sm_pos_range) as (b & U & CASES) ]). fold v in U.
    destruct CASES as [[_ L]|[-> _]]; [exfalso; exact (sm_not_live L)|]. unfold u8_at in U. exact U.
  Qed.
  #[using="R AI md DR"] Lemma sm_MAP : mapped v (a_fs A) kFakeStackBytes.
  Proof. (first [ pose proof ((ar_fsbase _ _ _ _ _ R)) as dR_15; dand5 dR_15 as _ _ _ M _ | pose proof (ar_fsbase _ _ _ _ _ R) as (_ & _ & _ & M & _) ]). exact M. Qed.
  #[using="R AI md DR"] Lemma sm_MAPSH : mapped v (sh (a_fs A)) (kFakeStackBytes / 8).
  Proof. (first [ pose proof ((ar_fsbase _ _ _ _ _ R)) as dR_16; dand5 dR_16 as _ _ _ _ M | pose proof (ar_fsbase _ _ _ _ _ R) as (_ & _ & _ & _ & M) ]). exact M. Qed.

  #[using="R W HK AI md DR"] Lemma sm_SHC : forall nsh, 0 <= nsh <= fsize k / 8 -> exists old, rw_cells rsegs v (sh sm_ff) [CB (Z.to_nat nsh) old].
  Proof.
    intros nsh Hn. (first [ dand14 sm_geom as M8 OBJ CEf _ _ _ _ R1 R2 FR SH1 SH2 NB _ | destruct sm_geom as (M8 & OBJ & CEf & _ & _ & _ & _ & R1 & R2 & FR & SH1 & SH2 & NB & _) ]).
    pose proof (slot_facts A k sm_pos W HK sm_pos_range) as X. cbv zeta in X. fold sm_ff in X.
    (first [ dand11 X as _ _ _ _ _ _ _ _ S1 S2 _ | destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & _) ]).
    (first [ pose proof ((sf_mapped_CB v (sh sm_ff) (Z.to_nat nsh))) as dR_19; dex1 dR_19 as bs; destruct dR_19 as [L RW] | pose proof ((sf_mapped_CB v (sh sm_ff) (Z.to_nat nsh))) as dR_19; dand3 dR_19 as bs L RW | destruct (sf_mapped_CB v (sh sm_ff) (Z.to_nat nsh)) as (bs & L & RW) ]).
    - intros i Hi. replace (sh sm_ff + i) with (sh (a_fs A) + (sh sm_ff + i - sh (a_fs A))) by lia. apply sm_MAPSH. lia.
    - unfold kHighMemBeg in *. lia.
    - right. lia.
    - unfold kHighMemBeg in *. lia.
    - exists bs. exact RW.
  Qed.

  (* [comment removed for export] *)
  #[using="W HK AI md m DR"] Lemma sm_fl_owned : pa_owned A sm_fl.
  Proof.
    (first [ dand11 sm_geom as _ _ _ _ _ _ _ R1 R2 FR _ | destruct sm_geom as (_ & _ & _ & _ & _ & _ & _ & R1 & R2 & FR & _) ]).
    (first [ pose proof ((bm_nth_fixed A)) as dR_21; dand8 dR_21 as _ _ _ _ _ _ E6 _ | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & _ & _ & E6 & _) ]).
    eapply (owned_rt A sm_fl (a_fs A) kFakeStackBytes); [apply rt_fixed_in; cbn; tauto| unfold a_fs, kFakeFlagsOffset, kFakeFramesOffset, kFakeStackBytes in *; lia| |].
    - eapply (fixed_bm_no_live_user A 6); [exact W| lia| exact E6| unfold a_fs, kFakeFlagsOffset, kFakeFramesOffset, kFakeStackBytes in *; lia].
    - intros LF. pose proof (live_frame_zone A sm_fl W LF). unfold a_fs, kFakeFlagsOffset, kFakeFramesOffset in *. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="W YOUNG HK AI md m DR Clg"] Lemma sm_apart_live : forall g f, a_fframes A !! g = Some f -> g + fsize (ff_class f) <= sm_ff \/ sm_ff + fsize k <= g.
  Proof.
    intros g f Hg. (first [ pose proof ((wfF A W)) as dR_22; dand3 dR_22 as F1 _ _ | destruct (wfF A W) as (F1 & _ & _) ]). (first [ pose proof ((F1 _ f Hg)) as dR_23; dand3 dR_23 as K' E AG' | destruct (F1 _ f Hg) as (K' & E & AG') ]). cbv zeta in *. unfold ff_addr_of_ in E.
    pose proof sm_pos_range as PR. pose proof (ff_pos_range (a_fhint A (ff_class f)) (ff_class f) (ff_age f) K') as PR'.
    destruct (decide ((k, sm_pos) = (ff_class f, ff_pos (a_fhint A (ff_class f)) (ff_class f) (ff_age f)))) as [EQ|NE].
    - exfalso. injection EQ as E1 E2. apply sm_not_live. exists g, f. split; [exact Hg|]. split; [symmetry; exact E1|]. rewrite E2, <- E1. reflexivity.
    - pose proof (fframe_addr_disjoint (a_fs A) k sm_pos (ff_class f) _ HK K' PR PR' NE) as D. fold sm_ff in D. rewrite <- E in D. lia.
  Qed.

  #[using="W YOUNG HK AI md m DR"] Lemma sm_frame_owned : forall a, sm_ff <= a < sm_ff + fsize k -> pa_owned A a.
  Proof.
    intros a Ha. (first [ dand11 sm_geom as _ _ _ _ _ _ _ R1 R2 FR _ | destruct sm_geom as (_ & _ & _ & _ & _ & _ & _ & R1 & R2 & FR & _) ]).
    (first [ pose proof ((bm_nth_fixed A)) as dR_25; dand8 dR_25 as _ _ _ _ _ _ E6 _ | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & _ & _ & E6 & _) ]).
    eapply (owned_rt A a (a_fs A) kFakeStackBytes); [apply rt_fixed_in; cbn; tauto| unfold kFakeFramesOffset in *; lia| |].
    - eapply (fixed_bm_no_live_user A 6); [exact W| lia| exact E6| unfold kFakeFramesOffset in *; lia].
    - ((first [ intro dR_39; dex2 dR_39 as g f'; destruct dR_39 as [Hg Hr] | intro dR_39; dand4 dR_39 as g f' Hg Hr | intros (g & f' & Hg & Hr) ])). pose proof (sm_apart_live g f' Hg). pose proof (fsize_pos (ff_class f') ltac:(destruct (wfF A W) as (F1 & _); exact (proj1 (F1 _ _ Hg)))). lia.
  Qed.

  #[using="W YOUNG HK AI md m DR"] Lemma sm_shadow_owned : forall a, sh sm_ff <= a < sh sm_ff + fsize k / 8 -> pa_owned A a.
  Proof.
    intros a Ha. pose proof (slot_facts A k sm_pos W HK sm_pos_range) as X. cbv zeta in X. fold sm_ff in X.
    (first [ dand12 X as R1 R2 FS1 FS2 FSM SZ M64 AL S1 S2 SR1 SR2 | destruct X as (R1 & R2 & FS1 & FS2 & FSM & SZ & M64 & AL & S1 & S2 & SR1 & SR2) ]).
    left. right. left. right. right. split; [unfold a_fs in *; lia|].
    ((first [ intro dR_40; dex2 dR_40 as g f'; destruct dR_40 as [Hg Hr] | intro dR_40; dand4 dR_40 as g f' Hg Hr | intros (g & f' & Hg & Hr) ])).
    (first [ pose proof ((wfF A W)) as dR_27; dand3 dR_27 as F1 _ _ | destruct (wfF A W) as (F1 & _ & _) ]). (first [ pose proof ((F1 _ f' Hg)) as dR_28; dand3 dR_28 as K' E _ | destruct (F1 _ f' Hg) as (K' & E & _) ]). cbv zeta in K'.
    pose proof (frame_facts A m md g f' AI Hg) as FF. cbv zeta in FF. (first [ dand11 FF as _ _ _ _ _ _ _ _ _ M64g _ | destruct FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & M64g & _) ]).
    (first [ pose proof ((fsize_facts _ K')) as dR_30; dand4 dR_30 as M8g _ _ _ | pose proof (fsize_facts _ K') as (M8g & _ & _ & _) ]). (first [ pose proof ((fsize_facts _ HK)) as dR_31; dand4 dR_31 as M8k _ _ _ | pose proof (fsize_facts _ HK) as (M8k & _ & _ & _) ]).
    assert (M8f : sm_ff mod 8 = 0) by (apply (mod0_down _ 64 8); [exists 8; reflexivity| exact M64]).
    assert (M8g' : g mod 8 = 0) by (apply (mod0_down _ 64 8); [exists 8; reflexivity| exact M64g]).
    destruct (sm_apart_live g f' Hg) as [D|D].
    - pose proof (sh_mono _ _ D) as SD. rewrite (sh_add g (fsize (ff_class f')) M8g' M8g) in SD. lia.
    - pose proof (sh_mono _ _ D) as SD. rewrite (sh_add sm_ff (fsize k) M8f M8k) in SD. lia.
  Qed.
End Probe.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section SmConsts.
  Context {Clg : Ceiling} {DR : DepotRep}.
  Variables (A : AState) (m : mem) (md : Model).
  Hypothesis AI : pa_ainv A m md.
  Let v := aview_of (pa_hull A) m.
  Let P := a_pl A.
  Let W : WF AL_pboth A. Proof. exact (ai_wf _ _ _ _ _ _ _ AI). Qed.
  Let CF : Forall (fun c => bytes_at rsegs v (fst c) (snd c)) (cl_consts LPA).
  Proof. exact (proj1 (ar_consts _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI))). Qed.
  Let CR : consts_repr_ LPA AL_pboth (a_pl A) v.
  Proof. exact (ar_consts _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI)). Qed.
  Ltac cell H a bs := pose proof (consts_cell v a bs CF eq_refl) as H.
  Ltac crtac := pose proof CR as C; unfold consts_repr_ in C; cbv zeta in C;
    cbn [al_instance al_kHighMemEnd_var al_kMidMemBeg_var al_kMidMemEnd_var al_malloc_context_size al_can_poison_memory
         al_page_size_cache al_may_return_null al_rss_limit_exceeded al_dying_flag al_malloc_hooks AL_pboth cl_tp cl_shared cl_consts cl_segs LPA] in C;
    rewrite ?unsigned_lit in C by lia;
    unfold off_th_context, off_th_stack_top, off_th_stack_bottom, off_th_stack_switching, off_th_unwinding in C.

  #[using="CF AI md DR"] Lemma sm_TLS : tls_consts v.
  Proof.
    unfold tls_consts.
    cell H1 0xb5898 [Z_to_bv 8 1]. cell H2 0xaa948 (le8 (Z_to_bv 64 0xa2868)).
    cell H3 0xa9870 (le8 (Z_to_bv 64 1) ++ le8 (Z_to_bv 64 (-0x800))).
    cell H4 0x5e7bd0 (le8 (Z_to_bv 64 0x5e7bf8)). cell H5 0x5e7c00 (le8 (Z_to_bv 64 0x5e83d8)).
    cell H6 0xa8b60 (le8 (Z_to_bv 64 0x1466e8)). cell H7 0x146771 [Z_to_bv 8 1].
    cell H8 0xa8bc0 (le8 (Z_to_bv 64 0x144658)). cell H9 0x144658 (le4 (Z_to_bv 64 0)). cell H10 0xa9880 (le8 (Z_to_bv 64 8)).
    split; [apply bytes_ro_C1; exact H1|]. split; [apply bytes_ro_C8; exact H2|].
    split.
    { split; [exact (conj I (conj I I))|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
      apply (bytes_at_as v _ _ _ H3). byteseq. }
    split; [apply bytes_ro_C8; exact H4|]. split; [apply bytes_ro_C8; exact H5|].
    split; [apply bytes_ro_C8; exact H6|]. split; [apply bytes_ro_C1; change (0x1466e8 + 137) with 0x146771; exact H7|].
    split; [apply bytes_ro_C8; exact H8|]. split; [apply bytes_ro_C4; exact H9|].
    apply bytes_ro_C8; exact H10.
  Qed.

  #[using="CR W AI md DR"] Lemma sm_TDYN : tls_dyn v (p_dtls P) TP.
  Proof.
    crtac. pose proof alloc_ceiling_val as CE.
    pose proof (place_facts A W) as PF. cbv zeta in PF.
    (first [ dand12 PF as _ _ _ _ _ _ _ _ _ _ Pdt _ | destruct PF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Pdt & _) ]). (first [ dand3 Pdt as Pd1 Pd2 Pd3 | destruct Pdt as (Pd1 & Pd2 & Pd3) ]).
    apply (proj1 (aobj_app_rangeA _ _)) in Pd1.
    assert (T1 : u64_at rsegs v (0x5e7bd8 + 8) (p_dtls P)) by (subst P; tauto).
    assert (T2 : u64_at rsegs v (p_dtls P + 24) 0x5e7bd8) by (subst P; tauto).
    unfold tls_dyn, TP. split; [apply u64_ro; exact T1|]. split; [apply u64_ro; exact T2|].
    split; [lia|]. split; [lia|]. subst P. split; [eapply aobj_sub; [exact Pd1| lia| lia| lia]| lia].
  Qed.

  #[using="CR W P AI md DR"] Lemma sm_FSH : fs_hdr v (a_fs A).
  Proof.
    crtac. pose proof alloc_ceiling_val as CE. (first [ pose proof ((place_fs A W)) as dR_34; dand3 dR_34 as FS1 FS2 FSM | pose proof (place_fs A W) as (FS1 & FS2 & FSM) ]).
    (first [ pose proof ((ar_fsbase _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI))) as dR_35; dand5 dR_35 as _ B88 B96 _ _ | pose proof (ar_fsbase _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI)) as (_ & B88 & B96 & _ & _) ]). fold v in B88, B96.
    assert (T0 : u64_at rsegs v 0x5e7bd8 (p_fs P)) by (subst P; tauto).
    unfold fs_hdr, a_fs. split; [apply u64_ro; exact T0|]. split; [apply u64_ro; exact B88|]. split; [apply u8_ro; exact B96|].
    split; [exact FSM|]. split; [apply (proj1 (aobj_app_rangeA _ _)); exact FS1| exact FS2].
  Qed.

  #[using="CR AI md DR"] Lemma sm_TLSB : ro_cells rsegs v (p_thr P + 48) [C8 (wz (p_tlsb P)); C8 (wz (p_tlse P))].
  Proof.
    crtac.
    assert (T1 : u64_at rsegs v (p_thr P + 48) (p_tlsb P)) by (subst P; tauto).
    assert (T2 : u64_at rsegs v (p_thr P + 56) (p_tlse P)) by (subst P; tauto).
    split; [exact (conj I (conj I I))|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    apply bytes_at_app. split; [exact T1|]. rewrite length_le8. replace (p_thr P + 48 + Z.of_nat 8) with (p_thr P + 56) by lia. exact T2.
  Qed.
End SmConsts.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section AcquireSpec.
  Context {Clg : Ceiling} {DR : DepotRep}.
  Variables (A : AState) (m : mem) (md : Model) (k : Z).
  Hypothesis AI : pa_ainv A m md.
  Hypothesis HK : 0 <= k <= 10.
  Hypothesis YOUNG : forall ff age, as_fframe A ff = Some (k, age) -> Z.of_nat age + 2 < fslots k.
  Let W : WF AL_pboth A. Proof. exact (ai_wf _ _ _ _ _ _ _ AI). Qed.
  Local Notation ff := (sm_ff A k).
  Local Notation A' := (as_acquire A k (sm_ff A k)).

  #[using="HK"] Lemma bumpk_pos' : forall h f, 0 <= ff_class f <= 10 ->
    ff_pos (acq_hint k h (ff_class f)) (ff_class f) (ff_age (bumpk k f)) = ff_pos (h (ff_class f)) (ff_class f) (ff_age f).
  Proof.
    intros h f Hk. unfold bumpk, acq_hint. destruct (Z.eqb_spec (ff_class f) k) as [E|NE]; cbn [ff_class ff_age].
    - rewrite E. apply ff_pos_bump. lia.
    - reflexivity.
  Qed.

  #[using="W YOUNG HK AI md m DR"] Lemma acq_WF : WF AL_pboth A'.
  Proof.
    pose proof (sm_free_f A m md k AI HK YOUNG) as FREE.
    destruct W as [wP wM wR wC wX wV wQ wS wD wF wB wI wE wJ].
    constructor; unfold a_fs; cbn [as_acquire set_fhint set_fframes a_pl a_sb a_reg a_cache a_cache_inited a_livemap a_qthread a_qglobal a_sec a_depot
                      a_ia_inited a_fhint a_fframes a_tiny a_qlimbo a_scred a_deadsh a_pcred a_paid]; try assumption.
    (first [ dand3 wF as F1 F2 F3 | destruct wF as (F1 & F2 & F3) ]). split; [| split].
    - intros g f Hg. destruct (acq_frames_inv k ff (a_fframes A) g f Hg) as [[-> ->]|(NE & f0 & Hf0 & ->)].
      + unfold wf_fframe_. cbn [ff_class ff_age]. split; [exact HK|]. split.
        * unfold ff_addr_of_, acq_hint. rewrite Z.eqb_refl. rewrite ff_pos_zero by exact HK. reflexivity.
        * pose proof (fslots_pos k HK). cbn. lia.
      + (first [ pose proof ((F1 g f0 Hf0)) as dR_37; dand3 dR_37 as K0 E0 AG0 | destruct (F1 g f0 Hf0) as (K0 & E0 & AG0) ]). cbv zeta in *. unfold wf_fframe_. cbv zeta. unfold ff_addr_of_ in *.
        rewrite bumpk_pos by exact K0. rewrite !bumpk_class.
        split; [exact K0|]. split; [exact E0|].
        unfold bumpk, acq_hint. destruct (Z.eqb_spec (ff_class f0) k) as [E|NE']; cbn [ff_class ff_age]; [| exact AG0].
        rewrite Nat2Z.inj_succ.
        assert (FF : as_fframe A g = Some (k, ff_age f0)) by (unfold as_fframe, as_fframe_; rewrite Hf0; cbn; rewrite E; reflexivity).
        pose proof (YOUNG _ _ FF). rewrite E. lia.
    - intros k'. unfold acq_hint. destruct (Z.eqb_spec k' k); [apply Z.mod_pos_bound; lia| apply F2].
    - intros g g' f f' Hg Hg' NE EK.
      destruct (acq_frames_inv k ff (a_fframes A) g f Hg) as [[-> ->]|(NEg & f0 & Hf0 & ->)];
      destruct (acq_frames_inv k ff (a_fframes A) g' f' Hg') as [[-> ->]|(NEg' & f0' & Hf0' & ->)].
      + exfalso. exact (NE eq_refl).
      + cbn [ff_class ff_age] in *. rewrite bumpk_class in EK. unfold bumpk. rewrite <- EK, Z.eqb_refl. cbn. lia.
      + cbn [ff_class ff_age] in *. rewrite bumpk_class in EK. unfold bumpk. rewrite EK, Z.eqb_refl. cbn. lia.
      + rewrite !bumpk_class in EK. pose proof (F3 g g' f0 f0' Hf0 Hf0' NE EK) as NA.
        unfold bumpk. rewrite <- EK. destruct (Z.eqb_spec (ff_class f0) k); cbn [ff_age]; [| exact NA]. intros X. apply NA. lia.
  Qed.

  #[using="YOUNG HK AI md m DR"] Lemma acq_spec :
    as_fframe A' ff = Some (k, 0%nat)
    /\ (forall g k' age', g <> ff -> as_fframe A g = Some (k', age') -> as_fframe A' g = Some (k', if Z.eqb k' k then S age' else age'))
    /\ (forall g, g <> ff -> as_fframe A g = None -> as_fframe A' g = None)
    /\ (forall q, as_live A' q = as_live A q)
    /\ as_livebytes A' = as_livebytes A /\ as_tinycred A' = as_tinycred A /\ as_seccred A' = as_seccred A /\ as_nlive A' = as_nlive A
    /\ pa_hull A' = pa_hull A /\ pa_eager A' = pa_eager A
    /\ (forall a, pa_owned A' a -> pa_owned A a)
    /\ (forall a, pa_owned A a -> ~ (ff <= a < ff + fsize k - 8) -> ~ (sh ff <= a < sh ff + fsize k / 8) -> pa_owned A' a).
  Proof.
    pose proof (sm_free_f A m md k AI HK YOUNG) as FREE.
    unfold as_fframe, as_live, as_livebytes, as_tinycred, as_seccred, as_nlive. cbn [as_acquire set_fhint set_fframes a_fframes a_livemap a_tiny a_scred].
    split; [unfold as_fframe_; rewrite acq_frames_lookup_new; reflexivity|].
    split.
    { intros g k' age' NE H. unfold as_fframe_ in *. rewrite acq_frames_lookup_old by exact NE.
      destruct (a_fframes A !! g) as [f|]; cbn in H |- *; [| discriminate]. injection H as <- <-.
      unfold bumpk. destruct (Z.eqb_spec (ff_class f) k); reflexivity. }
    split.
    { intros g NE H. unfold as_fframe_ in *. rewrite acq_frames_lookup_old by exact NE.
      destruct (a_fframes A !! g) as [f|]; cbn in H |- *; [discriminate| reflexivity]. }
    split; [intros; reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    (* [comment removed for export] *)
    assert (LF : forall a, in_live_frame_ (acq_frames k ff (a_fframes A)) a <-> in_live_frame_ (a_fframes A) a \/ (ff <= a < ff + fsize k - 8)).
    { intros a. unfold in_live_frame_. split.
      - ((first [ intro dR_41; dex2 dR_41 as g f; destruct dR_41 as [Hg Ha] | intro dR_41; dand4 dR_41 as g f Hg Ha | intros (g & f & Hg & Ha) ])). destruct (acq_frames_inv k ff (a_fframes A) g f Hg) as [[-> ->]|(NE & f0 & Hf0 & ->)].
        + right. cbn [ff_class] in Ha. exact Ha.
        + left. exists g, f0. rewrite bumpk_class in Ha. split; assumption.
      - intros [(g & f & Hg & Ha)|Ha].
        + exists g, (bumpk k f). split; [| rewrite bumpk_class; exact Ha]. rewrite acq_frames_lookup_old; [rewrite Hg; reflexivity|].
          intros ->. rewrite FREE in Hg. discriminate.
        + exists ff, (FF k 0%nat). split; [apply acq_frames_lookup_new| cbn [ff_class]; exact Ha]. }
    assert (LS : forall a, in_live_frame_shadow_ (acq_frames k ff (a_fframes A)) a <-> in_live_frame_shadow_ (a_fframes A) a \/ (sh ff <= a < sh ff + fsize k / 8)).
    { intros a. unfold in_live_frame_shadow_. split.
      - ((first [ intro dR_42; dex2 dR_42 as g f; destruct dR_42 as [Hg Ha] | intro dR_42; dand4 dR_42 as g f Hg Ha | intros (g & f & Hg & Ha) ])). destruct (acq_frames_inv k ff (a_fframes A) g f Hg) as [[-> ->]|(NE & f0 & Hf0 & ->)].
        + right. cbn [ff_class] in Ha. exact Ha.
        + left. exists g, f0. rewrite bumpk_class in Ha. split; assumption.
      - intros [(g & f & Hg & Ha)|Ha].
        + exists g, (bumpk k f). split; [| rewrite bumpk_class; exact Ha]. rewrite acq_frames_lookup_old; [rewrite Hg; reflexivity|].
          intros ->. rewrite FREE in Hg. discriminate.
        + exists ff, (FF k 0%nat). split; [apply acq_frames_lookup_new| cbn [ff_class]; exact Ha]. }
    unfold pa_owned. athin. unfold aowned_, fs_shadow_owned_. cbn [a_pl a_reg a_livemap a_sec a_fframes].
    split.
    - intros a [[S|[[(IR & NU & NF)|[HS|[R NFS]]]|GH]]|IS].
      + left. left. exact S.
      + left. right. left. left. split; [exact IR|]. split; [exact NU|]. intros LFa. apply NF. apply (proj2 (LF a)). left. exact LFa.
      + left. right. left. right. left. exact HS.
      + left. right. left. right. right. split; [exact R|]. intros LSa. apply NFS. apply (proj2 (LS a)). left. exact LSa.
      + left. right. right. exact GH.
      + right. exact IS.
    - intros a [[S|[[(IR & NU & NF)|[HS|[R NFS]]]|GH]]|IS] NI NS.
      + left. left. exact S.
      + left. right. left. left. split; [exact IR|]. split; [exact NU|]. intros LFa. apply (proj1 (LF a)) in LFa. destruct LFa as [LFa|LFa]; [exact (NF LFa)| exact (NI LFa)].
      + left. right. left. right. left. exact HS.
      + left. right. left. right. right. split; [exact R|]. intros LSa. apply (proj1 (LS a)) in LSa. destruct LSa as [LSa|LSa]; [exact (NFS LSa)| exact (NS LSa)].
      + left. right. right. exact GH.
      + right. exact IS.
  Qed.
End AcquireSpec.
End ASmawx5.


Module ASmax2u.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim AgentLib.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM ACells.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ATransp ARtStmts ARtSscs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ASm_mu9.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMalmys AFreeSF1.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASm_mu9.ASmStmt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeSF1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASma77w.ASmawx5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.solve_load_guarded | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image].
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)

Notation wz z := (Z_to_bv 64 z) (only parsing).
Ltac alc_h H := cbn [al_instance al_kHighMemEnd_var al_kMidMemBeg_var al_kMidMemEnd_var al_malloc_context_size al_can_poison_memory al_page_size_cache
       al_may_return_null al_rss_limit_exceeded al_dying_flag al_malloc_hooks al_internal_alloc_inited al_internal_allocator_inst
       al_theDepot al_depot_n_uniq_ids al_depot_nodes_map1 al_stackStore al_tp AL_pboth cl_tp cl_shared cl_consts cl_segs LPA] in H.
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kSpaceReserve, kMaxSize in *.

(* [comment removed for export] *)
Section HeapShadow.
  Context {Clg : Ceiling}.
  Lemma heap_shadow_not_fs_shadow : forall A a, WF AL_pboth A -> heap_shadow A a ->
    ~ (sh (a_fs A) <= a < sh (a_fs A) + kFakeStackBytes / 8).
  Proof.
    intros A a W HS X. pose proof alloc_ceiling_val as CE. (first [ pose proof ((place_fs A W)) as dR_1; dand3 dR_1 as FS1 FS2 FSM | pose proof (place_fs A W) as (FS1 & FS2 & FSM) ]).
    (first [ pose proof ((bm_nth_fixed A)) as dR_2; dand8 dR_2 as E0 _ _ _ _ _ E6 _ | pose proof (bm_nth_fixed A) as (E0 & _ & _ & _ & _ & _ & E6 & _) ]).
    assert (M8fs : a_fs A mod 8 = 0) by (apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact FSM]).
    assert (M8B : kFakeStackBytes mod 8 = 0) by reflexivity.
    unfold heap_shadow, heap_shadow_ in HS. change (p_sb (a_pl A)) with (a_sb A) in HS.
    (first [ pose proof ((sb_facts A W)) as dR_3; dand5 dR_3 as _ SBA HB6 RSB SCE | pose proof (sb_facts A W) as (_ & SBA & HB6 & RSB & SCE) ]).
    pose proof (bm_sep A 0 6 _ _ _ _ W E0 E6 ltac:(lia)) as D06.
    destruct HS as [(c & Hc & R)|[(c & Hc & R)|(sc & Hsc & R)]]; cbv zeta in R.
    - pose proof (region_piece_bounds A c W Hc) as RB. cbv zeta in RB.
      (first [ dand11 RB as R1 R2 R3 R4 R5 R6 R7 R8 AL MU _ | destruct RB as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & AL & MU & _) ]).
      destruct (sh_disjoint (region_beg (a_sb A) c) (rg_mapped_user (a_reg A c)) (a_fs A) kFakeStackBytes
                 ltac:(apply (mod0_down _ 0x10000 8); [exists 8192; reflexivity| exact AL]) M8fs MU M8B) as [D|D];
        [unfold a_b6 in *; kung_all; lia| lia| lia].
    - pose proof (region_piece_bounds A c W Hc) as RB. cbv zeta in RB.
      (first [ dand12 RB as R1 R2 R3 R4 R5 R6 R7 R8 AL _ _ MF | destruct RB as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & AL & _ & _ & MF) ]).
      destruct (sh_disjoint (region_beg (a_sb A) c + kFreeArrayOffset) (rg_mapped_fa (a_reg A c)) (a_fs A) kFakeStackBytes
                 ltac:(rewrite Z.add_mod by lia; rewrite (mod0_down _ 0x10000 8 ltac:(exists 8192; reflexivity) AL); reflexivity) M8fs MF M8B) as [D|D];
        [unfold a_b6 in *; kung_all; lia| lia| lia].
    - (first [ pose proof ((sec_chunk_bounds A sc W Hsc)) as dR_6; dand5 dR_6 as B1 B2 B3 B4 B5 | pose proof (sec_chunk_bounds A sc W Hsc) as (B1 & B2 & B3 & B4 & B5) ]). pose proof (map_size_page (cs_n sc)) as MP.
      destruct (In_nth_error' _ _ Hsc) as [j Hj]. pose proof (bm_nth_sec A j sc Hj) as Ej.
      pose proof (bm_sep A (15 + j) 6 _ _ _ _ W Ej E6 ltac:(lia)) as Dj.
      destruct (sh_disjoint (cs_map sc) (map_size (cs_n sc)) (a_fs A) kFakeStackBytes
                 ltac:(apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact B2])  M8fs
                 ltac:(apply (mod0_down _ kPageSize 8); [exists 512; reflexivity| exact MP]) M8B Dj) as [D|D]; lia.
  Qed.
End HeapShadow.

(* [comment removed for export] *)
Section HdrOwned.
  Context {Clg : Ceiling} {DR : DepotRep}.
  Lemma sm_hdr_owned : forall A m md, pa_ainv A m md -> forall a, a_fs A <= a < a_fs A + kFakeFlagsOffset -> pa_owned A a.
  Proof.
    intros A m md AI a Ha. pose proof (ai_wf _ _ _ _ _ _ _ AI) as W.
    (first [ pose proof ((bm_nth_fixed A)) as dR_7; dand8 dR_7 as _ _ _ _ _ _ E6 _ | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & _ & _ & E6 & _) ]).
    eapply (owned_rt A a (a_fs A) kFakeStackBytes); [apply rt_fixed_in; cbn; tauto| unfold kFakeFlagsOffset, kFakeStackBytes in *; lia| |].
    - eapply (fixed_bm_no_live_user A 6); [exact W| lia| exact E6| unfold kFakeFlagsOffset, kFakeStackBytes in *; lia].
    - intros LF. pose proof (live_frame_zone A a W LF). unfold kFakeFlagsOffset, kFakeFramesOffset in *. lia.
  Qed.
End HdrOwned.

Section Acquire.
  Context {Clg : Ceiling} {DR : DepotRep}.
  Variables (A : AState) (m m' : mem) (md md' : Model) (k : Z).
  Hypothesis AI : pa_ainv A m md.
  Hypothesis HK : 0 <= k <= 10.
  Hypothesis YOUNG : forall ff age, as_fframe A ff = Some (k, age) -> Z.of_nat age + 2 < fslots k.
  Local Notation fs := (a_fs A).
  Local Notation h := (sm_h A k).
  Local Notation ff := (sm_ff A k).
  Local Notation fl := (sm_fl A k).
  Local Notation A' := (as_acquire A k (sm_ff A k)).
  Let v := aview_of (pa_hull A) m.
  Let v' := aview_of (pa_hull A) m'.
  (* [comment removed for export] *)
  Hypothesis HID : forall a : word, hidc (pa_hull A) a = true -> m' a = m a.
  Hypothesis AG : forall a, 0 <= a < alloc_ceiling ->
      ~ (fs + 8 * k <= a < fs + 8 * k + 8) -> a <> fl -> ~ (ff <= a < ff + fsize k) -> ~ (sh ff <= a < sh ff + fsize k / 8) ->
      v' (wz a) = v (wz a).
  Hypothesis HINT' : bytes_at rsegs v' (fs + 8 * k) (le8 (wz (h + 1))).
  Hypothesis FLAG' : bytes_at rsegs v' fl [Z_to_bv 8 1].
  Hypothesis PTR' : bytes_at rsegs v' (saved_flag_ptr ff k) (le8 (wz fl)).
  Hypothesis NN : forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> a < 2^64 -> v (wz a) <> None -> v' (wz a) <> None.
  Hypothesis NN2 : forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> a < 2^64 -> v' (wz a) <> None -> v (wz a) <> None.
  Hypothesis MI : MInv (pa_hull A) (pa_lhull A) (pa_eager A) md'.
  Hypothesis SBM : same_but_materialized md md'.

  Let W : WF AL_pboth A. Proof. exact (ai_wf _ _ _ _ _ _ _ AI). Qed.
  Let R : arepr LPA AL_pboth [] A v. Proof. exact (ai_repr _ _ _ _ _ _ _ AI). Qed.
  Let AR : WF AL_pboth A /\ arepr LPA AL_pboth [] A v. Proof. exact (conj W R). Qed.

  #[using="AR R W SBM MI NN PTR' FLAG' HINT' AG HID v' v YOUNG HK AI md m"] Theorem asI_acquire : pa_ainv A' m' md'.
  Proof.
    pose proof alloc_ceiling_val as CE.
    pose proof (sm_geom A m md k AI HK) as GE.
    (first [ dand20 GE as M8 OBJ CEf OBJF CEl AP1 AP2 R1 R2 FR SH1 SH2 NB M64 AL SZ SZ8 OBJS FS2 FSM | destruct GE as (M8 & OBJ & CEf & OBJF & CEl & AP1 & AP2 & R1 & R2 & FR & SH1 & SH2 & NB & M64 & AL & SZ & SZ8 & OBJS & FS2 & FSM) ]).
    (first [ pose proof ((aobj_facts _ _ OBJS)) as dR_9; dand5 dR_9 as G1 G2 G3 G4 G5 | pose proof (aobj_facts _ _ OBJS) as (G1 & G2 & G3 & G4 & G5) ]).
    pose proof (slot_facts A k (sm_pos A k) W HK (sm_pos_range A k HK)) as X. cbv zeta in X.
    change (fframe_addr fs k (sm_pos A k)) with ff in X.
    (first [ dand12 X as _ _ _ _ _ _ _ _ S1 S2 SR1 SR2 | destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & SR1 & SR2) ]).
    assert (FSLO : 0x60a000 <= fs) by (unfold kFakeStackBytes in *; lia).
    assert (SHFS : 0x800b9400 <= sh fs) by (pose proof (sh_mono 0x60a000 fs FSLO) as SM; change (sh 0x60a000) with 0x800b9400 in SM; exact SM).
    (* [comment removed for export] *)
    assert (AGB : forall a, 0 <= a < alloc_ceiling -> ~ (fs <= a < fs + kFakeStackBytes) -> ~ (sh fs <= a < sh fs + kFakeStackBytes / 8) -> v' (wz a) = v (wz a)).
    { intros a Ha NF NS. apply AG; [exact Ha| | | |].
      - clear -NF HK. unfold kFakeStackBytes in *. lia.
      - intros ->. apply NF. clear -FR. unfold kFakeFlagsOffset, kFakeFramesOffset, kFakeStackBytes in *. lia.
      - clear -NF R1 R2. unfold kFakeFramesOffset in *. lia.
      - clear -NS S1 S2. lia. }
    (* [comment removed for export] *)
    assert (AGimg : forall a, 0 <= a < 0x60a000 -> v' (wz a) = v (wz a)).
    { intros a Ha. apply AGB; [clear -Ha CE; lia| clear -Ha FSLO; lia| clear -Ha SHFS; lia]. }
    assert (AGish : forall a, pa_image_shadow a -> v' (wz a) = v (wz a)).
    { intros a Ha. unfold pa_image_shadow in Ha. change (sh 0x10000) with 0x7fffa000 in Ha. change (sh 0x60a000) with 0x800b9400 in Ha.
      apply AGB; [clear -Ha CE; lia| clear -Ha G5; unfold kLowShadowMapBeg, kHighMemBeg in *; lia| clear -Ha SHFS; lia]. }
    (* [comment removed for export] *)
    assert (AGapp : forall b0 n1 a, aobj b0 n1 -> (b0 + n1 <= fs \/ fs + kFakeStackBytes <= b0) -> b0 <= a < b0 + n1 -> v' (wz a) = v (wz a)).
    { intros b0 n1 a Hb D Ha. (first [ pose proof ((aobj_facts _ _ Hb)) as dR_11; dand5 dR_11 as Q1 Q2 Q3 Q4 Q5 | pose proof (aobj_facts _ _ Hb) as (Q1 & Q2 & Q3 & Q4 & Q5) ]).
      apply AGB; [clear -Ha Q1 Q3; lia| clear -Ha D; lia| clear -Ha Q5 SR1 SR2; unfold kLowShadowMapBeg, kHighMemBeg in *; lia]. }
    (* [comment removed for export] *)
    (first [ pose proof ((bm_nth_fixed A)) as dR_12; dand15 dR_12 as E0 E1 _ _ E4 E5 E6 E7 E8 _ _ _ _ _ E14 | pose proof (bm_nth_fixed A) as (E0 & E1 & _ & _ & E4 & E5 & E6 & E7 & E8 & _ & _ & _ & _ & _ & E14) ]).
    pose proof (place_facts A W) as PF. cbv zeta in PF.
    (first [ dand13 PF as Pthr Pctx Pn0 Pf0 _ _ _ _ _ _ Pdt Ppa _ | destruct PF as (Pthr & Pctx & Pn0 & Pf0 & _ & _ & _ & _ & _ & _ & Pdt & Ppa & _) ]).
    (first [ dand3 Pthr as Pthr _ _ | destruct Pthr as (Pthr & _ & _) ]). (first [ dand3 Pctx as Pctx _ _ | destruct Pctx as (Pctx & _ & _) ]). (first [ dand3 Pn0 as Pn0 _ _ | destruct Pn0 as (Pn0 & _ & _) ]). (first [ dand3 Pf0 as Pf0 _ _ | destruct Pf0 as (Pf0 & _ & _) ]).
    (first [ dand3 Pdt as Pdt _ _ | destruct Pdt as (Pdt & _ & _) ]). (first [ dand3 Ppa as Ppa _ _ | destruct Ppa as (Ppa & _ & _) ]).
    apply (proj1 (aobj_app_rangeA _ _)) in Pthr. apply (proj1 (aobj_app_rangeA _ _)) in Pctx. apply (proj1 (aobj_app_rangeA _ _)) in Pn0.
    apply (proj1 (aobj_app_rangeA _ _)) in Pf0. apply (proj1 (aobj_app_rangeA _ _)) in Pdt. apply (proj1 (aobj_app_rangeA _ _)) in Ppa.
    pose proof (bm_sep A 4 6 _ _ _ _ W E4 E6 ltac:(lia)) as D4. pose proof (bm_sep A 5 6 _ _ _ _ W E5 E6 ltac:(lia)) as D5.
    pose proof (bm_sep A 7 6 _ _ _ _ W E7 E6 ltac:(lia)) as D7. pose proof (bm_sep A 8 6 _ _ _ _ W E8 E6 ltac:(lia)) as D8.
    pose proof (bm_sep A 14 6 _ _ _ _ W E14 E6 ltac:(lia)) as D14. pose proof (bm_sep A 1 6 _ _ _ _ W E1 E6 ltac:(lia)) as D1.
    pose proof (bm_sep A 0 6 _ _ _ _ W E0 E6 ltac:(lia)) as D0.
    unfold a_thr, a_ctx, a_nodes0, a_frames0, a_pa in D4, D5, D7, D8, D1.
    (first [ pose proof ((sb_facts A W)) as dR_20; dand5 dR_20 as _ SBA HB6 RSB SCE | pose proof (sb_facts A W) as (_ & SBA & HB6 & RSB & SCE) ]).
    (* [comment removed for export] *)
    assert (AGb6 : forall a, a_b6 A <= a < a_sb A + kSpaceSize + 4096 -> v' (wz a) = v (wz a)).
    { intros a Ha. apply AGB; [clear -Ha HB6 RSB SCE CE; kung_all; lia| clear -Ha D0 RSB; unfold a_b6 in *; kung_all; lia| clear -Ha HB6 SR2; kung_all; lia]. }
    assert (AGcarved : forall ch a, carved A ch -> chunk_lo (a_sb A) ch <= a < chunk_hi (a_sb A) ch -> v' (wz a) = v (wz a)).
    { intros ch a C Ha. (first [ pose proof ((carved_range A v AR ch C)) as dR_21; dand3 dR_21 as C1' C2' _ | pose proof (carved_range A v AR ch C) as (C1' & C2' & _) ]). pose proof (carved_apart_fs A v AR ch C) as CA.
      pose proof (carved_app A v AR ch C) as CP. apply (proj1 (aobj_app_rangeA _ _)) in CP.
      apply (AGapp _ _ a CP); [clear -CA; unfold a_fs; lia| clear -Ha; lia]. }
    (first [ pose proof ((hit_place A m md AI)) as dR_22; dand7 dR_22 as TH1 TH2 THRA CT1 CT2 TOPR BOTR | pose proof (hit_place A m md AI) as (TH1 & TH2 & THRA & CT1 & CT2 & TOPR & BOTR) ]). pose proof (aobj_facts _ _ TH1) as THF.
    (* [comment removed for export] *)
    assert (R' : arepr LPA AL_pboth [] A' v').
    { constructor; unfold a_fs; cbn [as_acquire set_fhint set_fframes a_pl a_sb a_reg a_cache a_cache_inited a_livemap a_qthread a_qglobal a_sec a_depot a_ia_inited a_fhint a_fframes a_qlimbo a_scred a_deadsh].
      - (* [comment removed for export] *) apply (consts_P A v v' AR).
        + intros cst a Hin Ha. cbn [cl_consts LPA] in Hin.
          destruct (pa_consts_where cst a Hin Ha) as [S|[S|S]].
          * apply AGimg. unfold pa_shared in S. clear -S. lia.
          * exact (AGish a S).
          * apply AGimg. pose proof (pa_static_low a S). unfold pa_static in S. clear -S H. lia.
        + intros a H. cbn [cl_shared LPA] in H. unfold pa_shared in H. apply AGimg. clear -H. lia.
        + intros a H. unfold cfoot_stat in H. offs_h H. alc_h H. apply AGimg. clear -H. lia.
        + intros a H. unfold cfoot_thr in H. offs_h H. apply (AGapp _ _ a TH1); [clear -D4; lia| clear -H; lia].
        + intros a H. unfold cfoot_misc in H. pose proof TPV as TP. rewrite TP in H.
          destruct H as [H|[H|[H|[H|[H|H]]]]].
          * apply (AGapp _ _ a CT1); [clear -D5; lia| clear -H; lia].
          * apply (AGapp _ _ a CT1); [clear -D5; lia| clear -H; lia].
          * apply AGimg. clear -H. lia.
          * apply AGimg. clear -H. lia.
          * apply AGimg. clear -H. lia.
          * apply (AGapp _ _ a Pdt); [clear -D14; lia| clear -H; lia].
      - (* [comment removed for export] *) apply (locks_P A v v' AR). intros a H. unfold lfoot in H. alc_h H. unfold p_ri in H. change (p_sb (a_pl A)) with (a_sb A) in H.
        destruct H as [H|H].
        + apply AGb6. clear -H RSB. unfold kRegionInfoSize in H. kung_all. lia.
        + offs_h H. apply AGimg. clear -H. lia.
      - (* [comment removed for export] *) intros c' Hc. apply (region_P A v v' AR NN c' Hc). intros a H. unfold rfoot in H.
        pose proof (region_piece_bounds A c' W Hc) as RB. cbv zeta in RB. unfold region_info_addr, free_array_beg in H. change (p_sb (a_pl A)) with (a_sb A) in *.
        destruct H as [H|H]; (apply AGb6; clear -H RB RSB Hc; unfold kRegionInfoSize in *; kung_all; lia).
      - (* [comment removed for export] *) apply (cache_P A v v' AR NN). intros c' Hc'. apply (cache_line_P A v v' AR NN (a_cache A) c' Hc' eq_refl).
        intros a Ha. offs_h Ha. cbv beta in Ha. apply (AGapp _ _ a TH1); [clear -D4; lia| clear -Ha Hc'; lia].
      - (* [comment removed for export] *) apply (live_sub_P A v v' AR NN (a_livemap A) (fun u li H => H)). intros u li a Hu Ha.
        exact (AGcarved _ a (known_carved A v AR _ _ (known_live A v AR u li Hu)) Ha).
      - (* [comment removed for export] *) apply (quar_P A v v' AR NN).
        + intros a Ha. unfold off_th_qcache in Ha. apply (AGapp _ _ a TH1); [clear -D4; lia| clear -Ha; lia].
        + intros a Ha. alc_h Ha. unfold off_q_cache_list_size in Ha. apply AGimg. clear -Ha. lia.
        + intros b a Hb Ha. (first [ pose proof ((batch_range A v AR b Hb)) as dR_23; dand3 dR_23 as Rb1 Rb2 _ | pose proof (batch_range A v AR b Hb) as (Rb1 & Rb2 & _) ]).
          exact (AGcarved _ a (batch_carved A v AR b Hb) ltac:(cbn [chunk_lo chunk_hi]; unfold batch_addr in Ha; exact Ha)).
        + intros e a He Ha. exact (AGcarved _ a (known_carved A v AR _ _ (known_quar A v AR e He)) Ha).
      - (* [comment removed for export] *) (first [ pose proof ((wfS A W)) as dR_24; dand4 dR_24 as _ LEN RES _ | destruct (wfS A W) as (_ & LEN & RES & _) ]). unfold kChunksBlockCount in RES. apply (sec_P A v v' AR NN).
        + intros a H. unfold sfoot_stat in H. offs_h H. alc_h H. apply AGimg. clear -H. lia.
        + intros a Ha. apply (AGapp _ _ a Ppa); [clear -D1; lia| unfold kPtrArrayReserve; clear -Ha LEN RES; lia].
        + intros sc a Hin Ha. apply (AGcarved (ChS sc) a); [exact Hin|]. cbn [chunk_lo chunk_hi]. destruct sc as [mb n0]; cbn [cs_map cs_n] in *.
          (first [ pose proof ((sec_chunk_bounds A _ W Hin)) as dR_25; dand5 dR_25 as SB1 _ _ _ SB5 | pose proof (sec_chunk_bounds A _ W Hin) as (SB1 & _ & _ & _ & SB5) ]). cbn [cs_map cs_n] in SB1, SB5.
          pose proof (needed_size2_secondary n0 (proj1 SB1)) as NS2. pose proof (rounded_size_ge n0) as RG. unfold kSecondaryHeaderSize, kPageSize in *. clear -Ha SB5 NS2 RG. lia.
      - (* [comment removed for export] *) apply (depot_P A v' (a_depot A) v (ar_depot _ _ _ _ _ R)). intros a Ha.
        unfold depot_foot in Ha. cbn [al_stackStore al_depot_nodes_map1 AL_pboth] in Ha. unfold kDepotNodesL1 in Ha.
        destruct Ha as [Ha|[Ha|Ha]]; [apply AGimg; clear -Ha; lia| apply (AGapp _ _ a Pn0); [clear -D7; lia| exact Ha]| apply (AGapp _ _ a Pf0); [clear -D8; lia| exact Ha]].
      - (* [comment removed for export] *) apply (ia_P A v v' AR). intros a H. unfold iafoot in H. cbn [al_internal_allocator_inst al_internal_alloc_inited AL_pboth] in H. apply AGimg. clear -H. lia.
      - (* [comment removed for export] *)
        pose proof (ar_fsbase _ _ _ _ _ R) as C. unfold fs_base_ in *. cbv zeta in *. unfold a_fs in *. (first [ dand5 C as H0 H88 H96 M1 M2 | destruct C as (H0 & H88 & H96 & M1 & M2) ]).
        assert (AGh : forall a, p_fs (a_pl A) <= a < p_fs (a_pl A) + kFakeFlagsOffset -> ~ (p_fs (a_pl A) + 8 * k <= a < p_fs (a_pl A) + 8 * k + 8) -> v' (wz a) = v (wz a)).
        { intros a Ha NH. apply AG; [clear -Ha FS2 FSLO; unfold kFakeFlagsOffset, kFakeStackBytes in *; lia| exact NH| clear -Ha FR; unfold kFakeFlagsOffset in *; lia| clear -Ha R1; unfold kFakeFlagsOffset, kFakeFramesOffset in *; lia| clear -Ha SR1 S1 G5 SH2; unfold kFakeFlagsOffset, kFakeStackBytes, kLowShadowMapBeg, kHighMemBeg in *; lia]. }
        split; [| split; [| split; [| split]]].
        + intros k' Hk'. unfold acq_hint. destruct (Z.eqb_spec k' k) as [->|NE].
          * unfold u64_at. rewrite Z.mod_mod by lia. rewrite AgentLib.Z_to_bv_64_mod in HINT'. unfold sm_h in HINT'. exact HINT'.
          * eapply u64_at_agree; [exact (H0 k' Hk')|]. intros i Hi. apply AGh; [clear -Hi Hk'; unfold kFakeFlagsOffset; lia| clear -Hi Hk' NE HK; lia].
        + eapply u64_at_agree; [exact H88|]. intros i Hi. apply AGh; [clear -Hi; unfold kFakeFlagsOffset; lia| clear -Hi HK; lia].
        + eapply u8_at_agree; [exact H96|]. apply AGh; [unfold kFakeFlagsOffset; lia| clear -HK; lia].
        + apply (mapped_N v v' NN); [lia| right; lia| lia| exact M1].
        + apply (mapped_N v v' NN); [lia| right; lia| unfold kHighMemBeg in *; lia| exact M2].
      - (* [comment removed for export] *)
        intros g f Hg. unfold a_fs. destruct (acq_frames_inv k ff (a_fframes A) g f Hg) as [[-> ->]|(NE & f0 & Hf0 & ->)].
        + cbn [ff_class ff_age]. unfold acq_hint. rewrite Z.eqb_refl. rewrite ff_pos_zero by exact HK.
          unfold u64_at. change (fflag_addr (p_fs (a_pl A)) k (sm_h A k mod fslots k)) with fl. exact PTR'.
        + rewrite bumpk_pos by (destruct (wfF A W) as (F1 & _); exact (proj1 (F1 _ _ Hf0))). rewrite !bumpk_class.
          pose proof (ar_fsptrs _ _ _ _ _ R g f0 Hf0) as L. unfold a_fs in L.
          (first [ pose proof ((wfF A W)) as dR_27; dand3 dR_27 as F1 _ _ | destruct (wfF A W) as (F1 & _ & _) ]). (first [ pose proof ((F1 g f0 Hf0)) as dR_28; dand3 dR_28 as K0 _ _ | destruct (F1 g f0 Hf0) as (K0 & _ & _) ]). cbv zeta in K0. pose proof (fsize_pos _ K0) as [FSg _].
          (first [ pose proof ((live_frame_where A g f0 g W Hf0 ltac:(lia))) as dR_29; dand4 dR_29 as _ _ Rg1 Rg2 | destruct (live_frame_where A g f0 g W Hf0 ltac:(lia)) as (_ & _ & Rg1 & Rg2) ]). unfold a_fs in Rg1, Rg2.
          pose proof (sm_apart_live A m md k AI HK YOUNG g f0 Hf0) as APg.
          pose proof (frame_facts A m md g f0 AI Hf0) as FFg. cbv zeta in FFg. (first [ dand7 FFg as _ _ _ _ _ FSg1 _ | destruct FFg as (_ & _ & _ & _ & _ & FSg1 & _) ]).
          (first [ pose proof ((app_facts _ _ FSg1)) as dR_31; dand5 dR_31 as _ _ _ _ Gg5 | pose proof (app_facts _ _ FSg1) as (_ & _ & _ & _ & Gg5) ]).
          eapply u64_at_agree; [exact L|]. intros i Hi. unfold saved_flag_ptr. apply AG.
          * clear -Hi Rg1 Rg2 FS2 FSLO FSg. unfold a_fs, kFakeFramesOffset in *. lia.
          * clear -Hi Rg1 HK FSg. unfold a_fs, kFakeFramesOffset in *. lia.
          * clear -Hi Rg1 FR FSg. unfold a_fs, kFakeFramesOffset in *. lia.
          * clear -Hi APg FSg. unfold a_fs in *. lia.
          * clear -Hi Rg1 Rg2 Gg5 SR1 S1 SH2 FSg. unfold a_fs, kFakeStackBytes, kFakeFramesOffset, kLowShadowMapBeg, kHighMemBeg in *. lia.
      - (* [comment removed for export] *)
        intros k' pos Hk' Hpos. unfold a_fs.
        assert (SL : forall k2 p2, 0 <= k2 <= 10 ->
                  slot_live_ (acq_hint k (a_fhint A)) (acq_frames k ff (a_fframes A)) k2 p2 <->
                  slot_live_ (a_fhint A) (a_fframes A) k2 p2 \/ (k2 = k /\ p2 = sm_pos A k)).
        { intros k2 p2 Hk2. unfold slot_live_. split.
          - ((first [ intro dR_35; dex2 dR_35 as g f; dand3 dR_35 as Hg Hc Hp | intro dR_35; dand5 dR_35 as g f Hg Hc Hp | intros (g & f & Hg & Hc & Hp) ])). destruct (acq_frames_inv k ff (a_fframes A) g f Hg) as [[-> ->]|(NE & f0 & Hf0 & ->)].
            + right. cbn [ff_class ff_age] in Hc, Hp. subst k2. unfold acq_hint in Hp. rewrite Z.eqb_refl in Hp. rewrite ff_pos_zero in Hp by exact HK.
              split; [reflexivity| symmetry; exact Hp].
            + left. exists g, f0. rewrite bumpk_class in Hc. subst k2.
              rewrite bumpk_pos' in Hp by first [exact HK| exact Hk2]. split; [exact Hf0| split; [reflexivity| exact Hp]].
          - intros [(g & f & Hg & Hc & Hp)|[-> ->]].
            + exists g, (bumpk k f). split; [rewrite acq_frames_lookup_old; [rewrite Hg; reflexivity| intros ->; rewrite (sm_free_f A m md k AI HK YOUNG) in Hg; discriminate]|].
              rewrite bumpk_class. split; [exact Hc|]. subst k2. rewrite bumpk_pos' by first [exact HK| exact Hk2]. exact Hp.
            + exists ff, (FF k 0%nat). split; [apply acq_frames_lookup_new|]. cbn [ff_class ff_age]. split; [reflexivity|].
              unfold acq_hint. rewrite Z.eqb_refl. apply ff_pos_zero. exact HK. }
        destruct (decide ((k', pos) = (k, sm_pos A k))) as [EQ|NEQ].
        + injection EQ as -> ->. exists 1. split; [unfold u8_at; change (fflag_addr (p_fs (a_pl A)) k (sm_pos A k)) with fl; exact FLAG'|].
          left. split; [reflexivity|]. apply (proj2 (SL k (sm_pos A k) HK)). right. split; reflexivity.
        + (first [ pose proof ((ar_fsflags _ _ _ _ _ R k' pos Hk' Hpos)) as dR_32; dex1 dR_32 as b; destruct dR_32 as [U CASES] | pose proof ((ar_fsflags _ _ _ _ _ R k' pos Hk' Hpos)) as dR_32; dand3 dR_32 as b U CASES | destruct (ar_fsflags _ _ _ _ _ R k' pos Hk' Hpos) as (b & U & CASES) ]). unfold a_fs in U.
          pose proof (fflag_addr_range (p_fs (a_pl A)) k' pos Hk' Hpos) as FR'.
          assert (NEF : fflag_addr (p_fs (a_pl A)) k' pos <> fl).
          { intros E. apply NEQ. destruct (fflag_addr_inj _ _ _ _ _ Hk' HK Hpos (sm_pos_range A k HK) E) as [-> ->]. reflexivity. }
          exists b. split.
          * eapply u8_at_agree; [exact U|]. apply AG.
            -- clear -FR' FS2 FSLO. unfold a_fs, kFakeFlagsOffset, kFakeFramesOffset, kFakeStackBytes in *. lia.
            -- clear -FR' HK. unfold a_fs, kFakeFlagsOffset, kFakeFramesOffset in *. lia.
            -- exact NEF.
            -- clear -FR' R1. unfold a_fs, kFakeFlagsOffset, kFakeFramesOffset in *. lia.
            -- clear -FR' SR1 S1 G5 SH2. unfold a_fs, kFakeFlagsOffset, kFakeFramesOffset, kFakeStackBytes, kLowShadowMapBeg, kHighMemBeg in *. lia.
          * destruct CASES as [[-> L]|[-> NL]].
            -- left. split; [reflexivity|]. apply (proj2 (SL k' pos Hk')). left. exact L.
            -- right. split; [reflexivity|]. intros L. apply (proj1 (SL k' pos Hk')) in L. destruct L as [L|[-> ->]]; [exact (NL L)| apply NEQ; reflexivity].
      - exact (maps_P A v v' AR NN).
      - apply (shadow_P0 A v v' AR). intros z Hz. pose proof (heap_shadow_range A z W Hz) as SRz. pose proof (heap_shadow_not_fs_shadow A z W Hz) as NFS.
        unfold in_shadow_maps, kLowShadowMapBeg in SRz.
        apply AGB; [clear -SRz CE; unfold kHighShadowMapSize in SRz; kung_all; lia| clear -SRz G5; unfold a_fs, kLowShadowMapBeg, kHighShadowMapSize in *; kung_all; lia| exact NFS]. }
    (* [comment removed for export] *)
    pose proof (same_but_materialized_frame md md' SBM) as SF.
    (first [ dand18 SF as _ VMM _ _ _ _ _ _ _ _ _ _ _ _ _ _ HALT _ | destruct SF as (_ & VMM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HALT & _) ]).
    (first [ pose proof (asI_layout_order) as dR_34; dand4 dR_34 as _ _ _ LO4 | pose proof asI_layout_order as (_ & _ & _ & LO4) ]).
    constructor.
    - exact (acq_WF A m md k AI HK YOUNG).
    - change (ahull_of pa_image_ivs AL_pboth A') with (pa_hull A). exact R'.
    - (* [comment removed for export] *)
      cbn [as_acquire set_fhint set_fframes a_pl a_reg a_sec]. pose proof (ai_hidden _ _ _ _ _ _ _ AI) as [H1 H2]. unfold hidden_repr.
      assert (VIS' : forall z, 0x60a000 <= z < 2^64 -> m (wz z) <> None -> hidc (pa_hull A) (wz z) = false -> m' (wz z) <> None).
      { intros z Hz Hm E. assert (VV' : v' (wz z) = m' (wz z)) by (unfold v', aview_of; apply view_visible; exact E).
        rewrite <- VV'. apply NN; [lia| right; lia| lia|]. unfold v, aview_of. rewrite (view_visible _ _ _ E). exact Hm. }
      split.
      + intros z GZ. destruct (H1 z GZ) as [P1 P2]. pose proof GZ as [Hz _]. pose proof (fs_shadow_not_ghost A z W) as NG.
        assert (EQ : m' (wz z) = m (wz z)).
        { destruct (hidc (pa_hull A) (wz z)) eqn:E; [exact (HID _ E)|].
          assert (VV : v (wz z) = m (wz z)) by (unfold v, aview_of; apply view_visible; exact E).
          assert (VV' : v' (wz z) = m' (wz z)) by (unfold v', aview_of; apply view_visible; exact E).
          rewrite <- VV, <- VV'. unfold in_shadow_maps, kHighShadowMapSize, kLowShadowMapBeg in Hz.
          apply AGB; [clear -Hz LO4; kung_all; lia| clear -Hz G5; unfold kLowShadowMapBeg in *; kung_all; lia| intros X; exact (NG X GZ)]. }
        rewrite EQ. exact (conj P1 P2).
      + intros z Hz NVS. destruct (hidc (pa_hull A) (wz z)) eqn:E; [rewrite (HID _ E); exact (H2 z Hz NVS)|].
        apply VIS'; [unfold kLowShadowMapBeg in Hz; lia| exact (H2 z Hz NVS)| exact E].
    - cbn [as_acquire set_fhint set_fframes a_pl]. exact (ai_extra _ _ _ _ _ _ _ AI).
    - cbn [as_acquire set_fhint set_fframes a_pl a_sec]. exact (aledger_sbm _ _ _ _ md md' SBM (ai_ledger _ _ _ _ _ _ _ AI)).
    - exact MI.
    - rewrite HALT. exact (ai_halted _ _ _ _ _ _ _ AI).
    - cbn [as_acquire set_fhint set_fframes a_pl a_sec]. rewrite (same_but_materialized_vmmaps _ _ SBM). exact (ai_cover _ _ _ _ _ _ _ AI).
    - rewrite (same_but_materialized_vmmaps _ _ SBM). exact (ai_ceil _ _ _ _ _ _ _ AI).
  Qed.
End Acquire.
End ASmax2u.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASm_mu9.ASmStmt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASm_mu9.ASm_imo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASm_mu9.ASm_0x1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASm_mu9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeSF1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASma77w.AFreeSF OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASma77w.ASmawx5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASma77w.ASmax2u.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
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
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)

Notation wz z := (Z_to_bv 64 z) (only parsing).

Section SMalloc.
  Context {Clg : Ceiling}.
  Variables (k : Z) (ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AState) (sz : Z) (T : TSet).
  Hypothesis AI : @pa_ainv _ DepotRepL A m md.
  Hypothesis MI : mem_inv rsegs (aview_of (pa_hull A) m).
  Hypothesis HK3 : k = 0 \/ k = 1 \/ k = 7.
  Hypothesis SZ : 0 < sz <= fsize k.
  Hypothesis SZ8 : 7 <= k -> sz mod 8 = 0.
  Hypothesis YOUNG : forall ff age, as_fframe A ff = Some (k, age) -> Z.of_nat age + 2 < fslots k.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis RA2 : bv_unsigned ra mod 2 = 0.
  Hypothesis CEIL : alloc_ceiling <= bv_unsigned sp - ASTK.
  Hypothesis SM : mapped (aview_of (pa_hull A) m) (bv_unsigned sp - ASTK) ASTK.
  Local Notation ff := (sm_ff A k).
  Local Notation A' := (as_acquire A k (sm_ff A k)).
  Hypothesis KK : forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (ff0 : Z) (A'' : AState) (m' : mem) (md' : Model),
          let v' := aview_of (pa_hull A'') m' in
          @pa_ainv _ DepotRepL A'' m' md' -> mem_inv (cl_segs LPA) v' -> amd_frame md md' ->
          pa_hull A'' = pa_hull A -> pa_eager A'' = pa_eager A ->
          (forall q, as_live A'' q = as_live A q) -> as_livebytes A'' = as_livebytes A ->
          as_tinycred A'' = as_tinycred A -> as_nlive A'' = as_nlive A -> as_seccred A'' = as_seccred A ->
          as_primcred A'' = as_primcred A (* [comment removed for export] *) ->
          ff0 <> 0 -> as_fframe A ff0 = None -> as_fframe A'' ff0 = Some (k, 0%nat) ->
          (forall g k' age', g <> ff0 -> as_fframe A g = Some (k', age') ->
              as_fframe A'' g = Some (k', if Z.eqb k' k then S age' else age')) ->
          (forall g, g <> ff0 -> as_fframe A g = None -> as_fframe A'' g = None) ->
          all_zero v' (sh ff0) (if Z.leb k 6 then fsize k / 8 else sz / 8) ->
          frame_ok LPA (pa_owned A) (pa_owned A'') (bv_unsigned sp) ASTK nowhere (frm ff0 k) (aview_of (pa_hull A) m) v' ->
          srealizes (cl_segs LPA) (mkCfg (MS (mkR ra sp gp (cl_tp LPA) t0' t1' t2' s0 s1 (wz ff0) a1' a2' a3' a4' a5' a6' a7'
                                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom (cl_segs LPA))) md') T.

  #[using="HK3"] Lemma HK : 0 <= k <= 10. Proof. clear -HK3. lia. Qed.
  #[using="KK YOUNG SZ8 SZ HK3 T sz A md m fc F s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 gp sp ra"] Lemma WALK : smallocG_stmt k.
  Proof. destruct HK3 as [->|[->| ->]]; [exact smallocG0_ok| exact smallocG1_ok| exact smallocG7_ok]. Qed.
  #[using="KK YOUNG SZ8 SZ HK3 T sz A md m fc F s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 gp sp ra Clg"] Lemma ENTRY : cl_smalloc_pc LPA k = wz (smalloc_entry k).
  Proof. destruct HK3 as [->|[->| ->]]; reflexivity. Qed.

  #[using="KK SM CEIL RA2 YOUNG SZ8 SZ HK3 MI AI A Clg"] Theorem pa_smalloc_k :
    srealizes (cl_segs LPA) (mkCfg (MS (mkR ra sp gp (cl_tp LPA) t0 t1 t2 s0 s1 (wz sz) a1 a2 a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (cl_smalloc_pc LPA k) fc None m (seg_rom (cl_segs LPA))) md) T.
  Proof.
    pose proof HK as HK'. rewrite ENTRY. cbn [cl_segs LPA] in MI, KK |- *.
    pose proof (ai_wf _ _ _ _ _ _ _ AI) as WF0. pose proof alloc_ceiling_val as CE.
    pose proof (hit_stk A m sp CEIL SM) as ST. pose proof (hit_sp47 A m md sp AI CEIL SM) as SPH. unfold ASTK in *.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof (zr_word ra) as RAR; unfold inr64 in RAR.
    (first [ pose proof ((sm_geom A m md k AI HK')) as dR_1; dand20 dR_1 as M8 OBJ CEf OBJF CEl AP1 AP2 R1 R2 FR SH1 SH2 NB M64 AL FSZ FS8 OBJS FS2 FSM | pose proof (sm_geom A m md k AI HK') as (M8 & OBJ & CEf & OBJF & CEl & AP1 & AP2 & R1 & R2 & FR & SH1 & SH2 & NB & M64 & AL & FSZ & FS8 & OBJS & FS2 & FSM) ]).
    (first [ pose proof ((aobj_facts _ _ OBJS)) as dR_2; dand5 dR_2 as G1 G2 G3 G4 G5 | pose proof (aobj_facts _ _ OBJS) as (G1 & G2 & G3 & G4 & G5) ]).
    set (nsh := if Z.leb k 6 then fsize k / 8 else sz / 8).
    assert (NSH : 0 <= nsh <= fsize k / 8).
    { subst nsh. (first [ pose proof ((fsize_facts _ HK')) as dR_3; dand4 dR_3 as _ _ D8 _ | pose proof (fsize_facts _ HK') as (_ & _ & D8 & _) ]). destruct (Z.leb_spec k 6); [lia|].
      clear -SZ D8 HK'. pose proof (Z.div_le_mono sz (fsize k) 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_pos sz 8). lia. }
    destruct (sm_SHC A m md k AI HK' nsh NSH) as [oldsh SHC].
    pose proof (sm_HINT A m md k AI HK') as HINT. pose proof (sm_FLAG A m md k AI HK' YOUNG) as FLAG. pose proof (sm_MAP A m md AI) as MAP.
    pose proof (sm_h_range A m md k AI) as HR.
    pose proof (sm_TLS A m md AI) as TLS. pose proof (sm_TDYN A m md AI) as TDYN. pose proof (sm_FSH A m md AI) as FSH. pose proof (sm_TLSB A m md AI) as TLSB.
    pose proof (hit_TC A m md AI) as TC. pose proof (hit_PCo A m md AI) as PCo.
    assert (LO : bv_unsigned sp - 8192 <= bv_unsigned sp - 224) by lia.
    assert (TPE : cl_tp LPA = wz TP) by reflexivity.
    assert (K7 : k = 7 -> sz mod 8 = 0 /\ 8 <= sz <= fsize 7).
    { intros ->. split; [exact (SZ8 ltac:(lia))|]. pose proof (SZ8 ltac:(lia)) as M. clear -SZ M. split; [| lia].
      pose proof (Z_div_mod_eq_full sz 8). pose proof (Z.div_pos sz 8). lia. }
    pose proof (WALK ra sp gp (cl_tp LPA) t0 t1 t2 s0 s1 (wz sz) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
                  (aview_of (pa_hull A) m) pa_tsd (p_ctx (a_pl A)) (p_thr (a_pl A)) (p_tlsb (a_pl A)) (p_tlse (a_pl A)) (p_dtls (a_pl A)) TP
                  (a_fs A) (sm_h A k) sz (bv_unsigned sp - 8192) oldsh
                  MI ST LO CEIL TPE eq_refl K7 TLS TDYN TC TLSB PCo FSH HR HINT FLAG MAP SHC RA2) as EVW.
    idtac "walkSM ok".
    destruct (asI_minv A m md AI) as [HMI HH].
    eapply (srz_evt_restrict rsegs (pa_hull A) (asI_hull_segs A m md AI) sf_pa_wx _ (pa_eager A) _ _ md T HMI HH).
    { rewrite restrict_MS. exact EVW. }
    intros msr' md' HQ HI' Hsame Hcl.
    (first [ dex15 HQ as t0' t1' t2' a1' a2'' a3' a4' a5' a6' a7' t3' t4' t5' t6' v'; dand10 HQ as -> MU WM' MI' ST' PH PFL PRS PPT PSH | dand25 HQ as t0' t1' t2' a1' a2'' a3' a4' a5' a6' a7' t3' t4' t5' t6' v' -> MU WM' MI' ST' PH PFL PRS PPT PSH | destruct HQ as (t0' & t1' & t2' & a1' & a2'' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & v' & -> & MU & WM' & MI' & ST' & PH & PFL & PRS & PPT & PSH) ]).
    rewrite unrestrict_MS. cbn [ms_mem] in Hcl.
    fold nsh in PSH. change (fframe_addr (a_fs A) k (sm_h A k mod fslots k)) with ff in *.
    change (fflag_addr (a_fs A) k (sm_h A k mod fslots k)) with (sm_fl A k) in *.
    pose proof (same_but_materialized_frame _ _ Hsame) as FRM.
    assert (VIEW : aview_of (pa_hull A) (munrestrict (hidc (pa_hull A)) m v') = v').
    { unfold aview_of. rewrite mrestrict_munrestrict. apply mrestrict_clean_id. exact Hcl. }
    assert (NN : forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> a < 2^64 -> aview_of (pa_hull A) m (wz a) <> None -> v' (wz a) <> None).
    { intros a H0 H1 H2. apply (sf_wmono_NN _ _ a WM'); lia. }
    (* [comment removed for export] *)
    assert (AG : forall a, 0 <= a < 2^64 -> ~ (bv_unsigned sp - 8192 <= a < bv_unsigned sp) ->
                 ~ (a_fs A + 8 * k <= a < a_fs A + 8 * k + 8) -> a <> sm_fl A k -> ~ (ff <= a < ff + fsize k) -> ~ (sh ff <= a < sh ff + fsize k / 8) ->
                 v' (wz a) = aview_of (pa_hull A) m (wz a)).
    { intros a Ha NS NH NF NFR NSH'. apply MU. rewrite unsigned_lit by lia. cbn [outside]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; intros X;
        [apply NS| apply NH| apply NF| apply NFR| apply NSH']; clear -X NSH; lia. }
    assert (CEILW : forall a, a < alloc_ceiling -> ~ (bv_unsigned sp - 8192 <= a < bv_unsigned sp)) by (intros a Ha X; clear -Ha X CEIL; lia).
    (* [comment removed for export] *)
    assert (FLP0 : aview_of (pa_hull A) m (wz (sm_fl A k)) <> None).
    { pose proof (proj2 (proj2 FLAG) 0%nat ltac:(cbn; lia)) as B0. cbn [nth_error Z.of_nat] in B0. rewrite Z.add_0_r in B0.
      apply (sf_mrd_some_neq _ _ _ B0). (first [ pose proof ((aobj_facts _ _ OBJF)) as dR_5; dand5 dR_5 as Q1 _ Q3 Q4 _ | pose proof (aobj_facts _ _ OBJF) as (Q1 & _ & Q3 & Q4 & _) ]). split; [exact Q4| clear -Q1 Q3 CE; lia]. }
    assert (HDP0 : forall a, a_fs A <= a < a_fs A + kFakeStackBytes -> aview_of (pa_hull A) m (wz a) <> None).
    { intros a Ha. replace a with (a_fs A + (a - a_fs A)) by lia. apply MAP. lia. }
    assert (SHP0 : forall a, sh (a_fs A) <= a < sh (a_fs A) + kFakeStackBytes / 8 -> aview_of (pa_hull A) m (wz a) <> None).
    { intros a Ha. replace a with (sh (a_fs A) + (a - sh (a_fs A))) by lia. apply (sm_MAPSH A m md AI). lia. }
    pose proof (slot_facts A k (sm_pos A k) WF0 HK' (sm_pos_range A k HK')) as X. cbv zeta in X.
    change (fframe_addr (a_fs A) k (sm_pos A k)) with ff in X. (first [ dand12 X as _ _ _ _ _ _ _ _ S1 S2 SR1 SR2 | destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & SR1 & SR2) ]).
    (* [comment removed for export] *)
    assert (AI' : @pa_ainv _ DepotRepL A' (munrestrict (hidc (pa_hull A)) m v') md').
    { apply (asI_acquire A m (munrestrict (hidc (pa_hull A)) m v') md md' k AI HK' YOUNG); rewrite ?VIEW.
      - intros a Ha. unfold munrestrict. rewrite Ha. reflexivity.
      - intros a Ha NH NF NFR NSH'. apply AG; [clear -Ha CE; lia| apply CEILW; clear -Ha; lia| exact NH| exact NF| exact NFR| exact NSH'].
      - exact PH.
      - exact PFL.
      - exact PPT.
      - exact NN.
      - exact HI'.
      - exact Hsame. }
    (* [comment removed for export] *)
    (first [ pose proof ((acq_spec A m md k AI HK' YOUNG)) as dR_7; dand12 dR_7 as Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 OW1 OW2 | pose proof (acq_spec A m md k AI HK' YOUNG) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & OW1 & OW2) ]).
    eapply (KK t0' t1' t2' a1' a2'' a3' a4' a5' a6' a7' t3' t4' t5' t6' ff A' (munrestrict (hidc (pa_hull A)) m v') md').
    - exact AI'.
    - rewrite Q9, VIEW. exact MI'.
    - unfold amd_frame. (first [ dand18 FRM as X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15 X16 X17 Xr | destruct FRM as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16 & X17 & Xr) ]).
      rewrite X2, X17, HH. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [assumption| reflexivity].
    - exact Q9.
    - exact Q10.
    - exact Q4.
    - exact Q5.
    - exact Q6.
    - exact Q8.
    - exact Q7.
    - (* [comment removed for export] *)
      unfold as_primcred. cbn [as_acquire set_fhint set_fframes a_pcred]. reflexivity.
    - clear -NB. lia.
    - exact (sm_free A m md k AI HK' YOUNG).
    - exact Q1.
    - exact Q2.
    - exact Q3.
    - rewrite Q9, VIEW. fold nsh. intros i Hi.
      pose proof (bytes_at_bound _ _ _ _ PSH) as BB. rewrite repeat_length in BB.
      pose proof (proj2 (proj2 PSH) (Z.to_nat i) ltac:(rewrite repeat_length; lia)) as Bi. rewrite nth_error_repeat in Bi by lia. rewrite Z2Nat.id in Bi by lia.
      apply (sf_mrd_some_eq v' _ _); [| exact Bi]. apply NN; [clear -Hi SH1; lia| right; clear -Hi SH1; lia| clear -Hi NSH SH2; unfold kHighMemBeg in *; lia|].
      apply SHP0. clear -Hi NSH S1 S2. lia.
    - rewrite Q9, VIEW. unfold frame_ok. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits.
      + intros a Ha NO NO' NW _ _ NV. apply AG; [exact Ha| unfold ASTK in NW; exact NW| | | |].
        * intros X. apply NO. apply (sm_hdr_owned A m md AI). clear -X HK'. unfold kFakeFlagsOffset. lia.
        * intros ->. apply NO. exact (sm_fl_owned A m md k AI HK').
        * intros X. apply NV. unfold frm. left. exact X.
        * intros X. apply NV. unfold frm. right. exact X.
      + intros a Ha NI Hv. right. right. apply NN; [clear -Ha; lia| unfold in_image in NI; cbn [cl_image_lo cl_image_hi LPA] in NI; clear -NI Ha; lia| clear -Ha; lia| exact Hv].
      + eapply mapped_mono; [exact SM|]. intros i Hi. unfold ASTK in *. apply NN; [clear -Hi SPR CEIL CE; lia| clear -Hi CEIL CE; lia| clear -Hi SPR; lia].
      + intros a Ha NBa. left. unfold frm in NBa. destruct NBa as [X|X]; [exact (sm_frame_owned A m md k AI HK' YOUNG a X)| exact (sm_shadow_owned A m md k AI HK' YOUNG a X)].
      + intros a Ha O'. left. exact (OW1 a O').
      + intros a Ha O NO'. left. unfold frm.
        destruct (decide (ff <= a < ff + fsize k - 8)) as [X|X]; [left; clear -X; lia|].
        destruct (decide (sh ff <= a < sh ff + fsize k / 8)) as [Y|Y]; [right; exact Y|].
        exfalso. exact (NO' (OW2 a O X Y)).
      + intros a Ha [].
  Qed.
End SMalloc.

(* [comment removed for export] *)
Section Full.
  Context {Clg : Ceiling}.
  Theorem pa_smalloc_full : @pa_smalloc_obligation _ DepotRepL.
  Proof.
    unfold pa_smalloc_obligation. intros k ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A sz T.
    cbv zeta. intros AI MI HK3 A0 SZ SZM YOUNG TP SPA RA2 CEIL SM KK. subst a0 tp.
    eapply (pa_smalloc_k k ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A sz T); try eassumption.
  Qed.
End Full.
