(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts AMTac
     AMalmys AMaly5g ASecB1.
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
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Notation wz z := (Z_to_bv 64 z) (only parsing).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kSpaceReserve, kMaxSize in *.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition wkey (pc top bot fp : Z) (ra : word) : list Z :=
  if unwind_depth2 top bot fp then [pc; bv_unsigned ra] else [pc].
Lemma wkey_range : forall pc top bot fp ra, 0 <= pc < 2^64 -> Forall (fun w => 0 <= w < 2^64) (wkey pc top bot fp ra).
Proof.
  intros pc top bot fp ra H. pose proof (bv_unsigned_in_range _ ra) as R. unfold bv_modulus in R. cbn in R.
  unfold wkey. destruct (unwind_depth2 top bot fp); repeat constructor; lia.
Qed.

(* [comment removed for export] *)

Lemma mrd_some_eq_ : forall (mm : mem) a b, mm a <> None -> mrd rsegs mm a = Some b -> mm a = Some b.
Proof. intros mm a b H E. unfold mrd in E. destruct (mm a); [exact E| exfalso; exact (H eq_refl)]. Qed.

(* [comment removed for export] *)
Lemma bytes_at_agree : forall (v v' : mem) a bs,
  bytes_at rsegs v a bs -> (forall i, 0 <= i < Z.of_nat (length bs) -> v' (wz (a + i)) = v (wz (a + i))) -> bytes_at rsegs v' a bs.
Proof.
  (intros v v' a bs; (first [ intro dR_10; dand3 dR_10 as B0 B1 B | intros (B0 & B1 & B) ]); intros AG). split; [exact B0|]. split; [exact B1|]. intros i Hi. unfold mrd, wa. rewrite (AG (Z.of_nat i)) by lia.
  specialize (B i Hi). unfold mrd, wa in B. exact B.
Qed.
Lemma ro_cells_agree : forall (v v' : mem) a cs,
  ro_cells rsegs v a cs -> (forall i, 0 <= i < Z.of_nat (cells_size cs) -> v' (wz (a + i)) = v (wz (a + i))) -> ro_cells rsegs v' a cs.
Proof.
  intros v v' a cs [WF B] AG. split; [exact WF|]. eapply bytes_at_agree; [exact B|]. rewrite (cells_bytes_length cs WF). exact AG.
Qed.
Lemma rw_cells_agree : forall (v v' : mem) a cs,
  rw_cells rsegs v a cs -> (forall i, 0 <= i < Z.of_nat (cells_size cs) -> v' (wz (a + i)) = v (wz (a + i))) -> rw_cells rsegs v' a cs.
Proof.
  intros v v' a cs [RO W] AG. split; [exact (ro_cells_agree v v' a cs RO AG)|].
  (first [ dand3 W as W0 W1 W2 | destruct W as (W0 & W1 & W2) ]). split; [exact W0|]. split; [exact W1|]. intros i Hi.
  specialize (W2 i Hi). unfold wview, wa in *. rewrite (AG i Hi). exact W2.
Qed.
Lemma ro_C44_C8 : forall (v : mem) a (d : Z), le8 (wz d) = le4 (wz d) ++ le4 (wz 0) ->
  rw_cells rsegs v a [C4 (wz d)] -> rw_cells rsegs v (a + 4) [C4 (wz 0)] -> ro_cells rsegs v a [C8 (wz d)].
Proof.
  intros v a d E [[_ B1] _] [[_ B2] _]. split; [exact (conj I I)|].
  cbn [cells_bytes cbytes app] in *. rewrite app_nil_r in *. rewrite E. apply bytes_at_app. split; [exact B1|]. rewrite length_le4. exact B2.
Qed.

(* [comment removed for export] *)
Section Shell.
Context {Clg : Ceiling}.
  Variables (A : AState) (m : mem) (md md1 : Model) (fp : Z) (v1 : mem) (X : Z -> Prop).
  Hypothesis AI : @pa_ainv _ DepotRepL A m md.
  Hypothesis CEIL : alloc_ceiling <= fp - ASTK.
  Hypothesis SM : mapped (aview_of (pa_hull A) m) (fp - ASTK) ASTK.
  #[warnings="-notation-for-abbreviation"] Local Notation v := (aview_of (pa_hull A) m).
  #[warnings="-notation-for-abbreviation"] Local Notation thr := (p_thr (a_pl A)).
  (* [comment removed for export] *)
  Hypothesis AG : forall a, 0 <= a < 2^64 -> ~ (fp - ASTK <= a < fp) -> a <> thr + 3168 -> ~ (cl_errno LPA <= a < cl_errno LPA + 4) ->
                  ~ X a -> v1 (wz a) = v (wz a).
  (* [comment removed for export] *)
  Hypothesis XOK : forall a, X a -> ~ pa_owned A a /\ ~ cl_shared LPA a /\ v (wz a) <> None.
  Hypothesis UNWB : rw_cells rsegs v1 (thr + 3168) [C1 (Z_to_bv 8 0)].
  Hypothesis WM : wmono rsegs v v1.
  Hypothesis CL : forall a, hidc (pa_hull A) a = true -> v1 a = None.
  Hypothesis HI : MInv (pa_hull A) (pa_lhull A) (pa_eager A) md1.
  Hypothesis SB : same_but_materialized md md1.

  Lemma shell_unw : v1 (wz (thr + 3168)) = v (wz (thr + 3168)).
  Proof.
    pose proof (conj (ai_wf _ _ _ _ _ _ _ AI) (ai_repr _ _ _ _ _ _ _ AI) : WF AL_pasan A /\ @arepr _ DepotRepL LPA AL_pasan [] A v) as AR.
    pose proof (hit_place A m md AI) as (TH1 & _). pose proof (aobj_facts _ _ TH1) as THF. pose proof alloc_ceiling_val as CE.
    pose proof (ar_consts _ _ _ _ _ (proj2 AR)) as C. unfold consts_repr_ in C. cbv zeta in C.
    (first [ dand36 C as _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dR_C_t0; destruct dR_C_t0 as [U0 _] | destruct C as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & U0 & _) ]).
    (first [ dand3 U0 as _ _ U | destruct U0 as (_ & _ & U) ]). destruct UNWB as [[_ (_ & _ & U')] _]. cbn [cells_bytes cbytes app length] in U'.
    specialize (U 0%nat ltac:(cbn; lia)). specialize (U' 0%nat ltac:(cbn; lia)). cbn [nth_error Z.of_nat] in U, U'. offs_h U. offs_h U'. rewrite Z.add_0_r in U, U'.
    assert (Vn : v (wz (thr + 3168)) <> None).
    { (first [ pose proof ((ar_cache _ _ _ _ _ (proj2 AR))) as dR_4; dand5 dR_4 as _ _ _ MT _ | pose proof (ar_cache _ _ _ _ _ (proj2 AR)) as (_ & _ & _ & MT & _) ]). apply (MT 3168). lia. }
    assert (V'n : v1 (wz (thr + 3168)) <> None) by (apply (wmono_NN _ _ _ WM); [clear -THF; lia| clear -THF CE; lia| exact Vn]).
    unfold off_th_unwinding in U'.
    rewrite (mrd_some_eq_ v _ _ Vn U), (mrd_some_eq_ v1 _ _ V'n U'). reflexivity.
  Qed.

  Lemma shell_view : aview_of (pa_hull A) (munrestrict (hidc (pa_hull A)) m v1) = v1.
  Proof. unfold aview_of. rewrite mrestrict_munrestrict. apply mrestrict_clean_id. exact CL. Qed.

  Theorem shell_ainv : @pa_ainv _ DepotRepL A (munrestrict (hidc (pa_hull A)) m v1) md1.
  Proof.
    pose proof alloc_ceiling_val as CE. pose proof shell_unw as UNW.
    pose proof (asI_frame A [] m (munrestrict (hidc (pa_hull A)) m v1) md md1 AI) as FR. cbn [fold_left] in FR. cbv zeta in FR.
    rewrite shell_view in FR. apply FR; clear FR.
    - intros ff [].
    - constructor.
    - intros a Ha. unfold munrestrict. rewrite Ha. reflexivity.
    - intros a OW. left. destruct (Z.eq_dec a (thr + 3168)) as [->|NT]; [exact UNW|].
      assert (NX : ~ X a) by (intros Xa; exact (proj1 (XOK a Xa) OW)).
      pose proof (owned_lt64 A m md a AI OW) as R. destruct (asI_owned_where A m md a AI OW) as [ST|HZ].
      + cbn [cl_static LPA] in ST. unfold pa_static in ST. apply AG; [clear -ST CE; lia| clear -ST CE CEIL; unfold ASTK in *; lia| exact NT| | exact NX].
        intros E. cbn [cl_errno LPA] in E. clear -ST E. lia.
      + unfold heap_zone in HZ. apply AG; [clear -HZ CE; lia| clear -HZ CEIL; unfold ASTK in *; lia| exact NT| | exact NX].
        intros E. destruct HZ as [_ NI]. apply NI. unfold in_image. cbn [cl_errno cl_image_lo cl_image_hi LPA] in E |- *. clear -E. lia.
    - intros ff k age fa [].
    - intros a SH. pose proof (asI_shared_where a SH) as W. cbn [cl_rw_lo cl_image_hi LPA] in W.
      apply AG; [clear -W CE; lia| clear -W CE CEIL; unfold ASTK in *; lia| | | intros Xa; exact (proj1 (proj2 (XOK a Xa)) SH)].
      + pose proof (hit_place A m md AI) as (TH1 & _). pose proof (aobj_facts _ _ TH1) as THF. clear -W THF. lia.
      + intros E. destruct (asI_errno_not_static (a - cl_errno LPA) ltac:(clear -E; lia)) as [_ NS].
        replace (cl_errno LPA + (a - cl_errno LPA)) with a in NS by lia. exact (NS SH).
    - intros a Ha NI Hv. apply (wmono_NN _ _ a WM); [| exact Ha| exact Hv]. unfold in_image in NI. cbn [cl_image_lo cl_image_hi LPA] in NI. clear -NI Ha. lia.
    - intros a Ha NI Hv1. pose proof (hit_place A m md AI) as (TH1 & _). pose proof (aobj_facts _ _ TH1) as THF.
      assert (IW : fp - ASTK <= a < fp \/ ~ (fp - ASTK <= a < fp)) by lia. destruct IW as [IW|NW].
      { replace a with (fp - ASTK + (a - (fp - ASTK))) by lia. apply SM. clear -IW. lia. }
      destruct (Z.eq_dec a (thr + 3168)) as [->|NT].
      { (first [ pose proof ((ar_cache _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI))) as dR_5; dand5 dR_5 as _ _ _ MT _ | pose proof (ar_cache _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI)) as (_ & _ & _ & MT & _) ]). apply (MT 3168). lia. }
      destruct (classic (X a)) as [Xa|NX]; [exact (proj2 (proj2 (XOK a Xa)))|].
      rewrite <- (AG a Ha NW NT). { exact Hv1. } 2: exact NX.
      intros E. apply NI. unfold in_image. cbn [cl_errno cl_image_lo cl_image_hi LPA] in E |- *. clear -E. lia.
    - exact HI.
    - exact SB.
  Qed.
End Shell.

(* [comment removed for export] *)
Section ShellW.
Context {Clg : Ceiling}.
  Variables (A : AState) (m : mem) (md md1 : Model) (wlo whi : Z) (v1 : mem) (X : Z -> Prop).
  Hypothesis AI : @pa_ainv _ DepotRepL A m md.
  Hypothesis CEIL : alloc_ceiling <= wlo.
  Hypothesis SM : mapped (aview_of (pa_hull A) m) wlo (whi - wlo).
  #[warnings="-notation-for-abbreviation"] Local Notation v := (aview_of (pa_hull A) m).
  #[warnings="-notation-for-abbreviation"] Local Notation thr := (p_thr (a_pl A)).
  (* [comment removed for export] *)
  Hypothesis AG : forall a, 0 <= a < 2^64 -> ~ (wlo <= a < whi) -> a <> thr + 3168 -> ~ (cl_errno LPA <= a < cl_errno LPA + 4) ->
                  ~ X a -> v1 (wz a) = v (wz a).
  (* [comment removed for export] *)
  Hypothesis XOK : forall a, X a -> ~ pa_owned A a /\ ~ cl_shared LPA a /\ v (wz a) <> None.
  Hypothesis UNWB : rw_cells rsegs v1 (thr + 3168) [C1 (Z_to_bv 8 0)].
  Hypothesis WM : wmono rsegs v v1.
  Hypothesis CL : forall a, hidc (pa_hull A) a = true -> v1 a = None.
  Hypothesis HI : MInv (pa_hull A) (pa_lhull A) (pa_eager A) md1.
  Hypothesis SB : same_but_materialized md md1.

  Lemma shell_unwW : v1 (wz (thr + 3168)) = v (wz (thr + 3168)).
  Proof.
    pose proof (conj (ai_wf _ _ _ _ _ _ _ AI) (ai_repr _ _ _ _ _ _ _ AI) : WF AL_pasan A /\ @arepr _ DepotRepL LPA AL_pasan [] A v) as AR.
    pose proof (hit_place A m md AI) as (TH1 & _). pose proof (aobj_facts _ _ TH1) as THF. pose proof alloc_ceiling_val as CE.
    pose proof (ar_consts _ _ _ _ _ (proj2 AR)) as C. unfold consts_repr_ in C. cbv zeta in C.
    (first [ dand36 C as _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dR_C_t0; destruct dR_C_t0 as [U0 _] | destruct C as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & U0 & _) ]).
    (first [ dand3 U0 as _ _ U | destruct U0 as (_ & _ & U) ]). destruct UNWB as [[_ (_ & _ & U')] _]. cbn [cells_bytes cbytes app length] in U'.
    specialize (U 0%nat ltac:(cbn; lia)). specialize (U' 0%nat ltac:(cbn; lia)). cbn [nth_error Z.of_nat] in U, U'. offs_h U. offs_h U'. rewrite Z.add_0_r in U, U'.
    assert (Vn : v (wz (thr + 3168)) <> None).
    { (first [ pose proof ((ar_cache _ _ _ _ _ (proj2 AR))) as dR_8; dand5 dR_8 as _ _ _ MT _ | pose proof (ar_cache _ _ _ _ _ (proj2 AR)) as (_ & _ & _ & MT & _) ]). apply (MT 3168). lia. }
    assert (V'n : v1 (wz (thr + 3168)) <> None) by (apply (wmono_NN _ _ _ WM); [clear -THF; lia| clear -THF CE; lia| exact Vn]).
    unfold off_th_unwinding in U'.
    rewrite (mrd_some_eq_ v _ _ Vn U), (mrd_some_eq_ v1 _ _ V'n U'). reflexivity.
  Qed.

  Lemma shell_viewW : aview_of (pa_hull A) (munrestrict (hidc (pa_hull A)) m v1) = v1.
  Proof. unfold aview_of. rewrite mrestrict_munrestrict. apply mrestrict_clean_id. exact CL. Qed.

  Theorem shell_ainvW : @pa_ainv _ DepotRepL A (munrestrict (hidc (pa_hull A)) m v1) md1.
  Proof.
    pose proof alloc_ceiling_val as CE. pose proof shell_unwW as UNW.
    pose proof (asI_frame A [] m (munrestrict (hidc (pa_hull A)) m v1) md md1 AI) as FR. cbn [fold_left] in FR. cbv zeta in FR.
    rewrite shell_viewW in FR. apply FR; clear FR.
    - intros ff [].
    - constructor.
    - intros a Ha. unfold munrestrict. rewrite Ha. reflexivity.
    - intros a OW. left. destruct (Z.eq_dec a (thr + 3168)) as [->|NT]; [exact UNW|].
      assert (NX : ~ X a) by (intros Xa; exact (proj1 (XOK a Xa) OW)).
      pose proof (owned_lt64 A m md a AI OW) as R. destruct (asI_owned_where A m md a AI OW) as [ST|HZ].
      + cbn [cl_static LPA] in ST. unfold pa_static in ST. apply AG; [clear -ST CE; lia| clear -ST CE CEIL; lia| exact NT| | exact NX].
        intros E. cbn [cl_errno LPA] in E. clear -ST E. lia.
      + unfold heap_zone in HZ. apply AG; [clear -HZ CE; lia| clear -HZ CEIL; lia| exact NT| | exact NX].
        intros E. destruct HZ as [_ NI]. apply NI. unfold in_image. cbn [cl_errno cl_image_lo cl_image_hi LPA] in E |- *. clear -E. lia.
    - intros ff k age fa [].
    - intros a SH. pose proof (asI_shared_where a SH) as W. cbn [cl_rw_lo cl_image_hi LPA] in W.
      apply AG; [clear -W CE; lia| clear -W CE CEIL; lia| | | intros Xa; exact (proj1 (proj2 (XOK a Xa)) SH)].
      + pose proof (hit_place A m md AI) as (TH1 & _). pose proof (aobj_facts _ _ TH1) as THF. clear -W THF. lia.
      + intros E. destruct (asI_errno_not_static (a - cl_errno LPA) ltac:(clear -E; lia)) as [_ NS].
        replace (cl_errno LPA + (a - cl_errno LPA)) with a in NS by lia. exact (NS SH).
    - intros a Ha NI Hv. apply (wmono_NN _ _ a WM); [| exact Ha| exact Hv]. unfold in_image in NI. cbn [cl_image_lo cl_image_hi LPA] in NI. clear -NI Ha. lia.
    - intros a Ha NI Hv1. pose proof (hit_place A m md AI) as (TH1 & _). pose proof (aobj_facts _ _ TH1) as THF.
      assert (IW : wlo <= a < whi \/ ~ (wlo <= a < whi)) by lia. destruct IW as [IW|NW].
      { replace a with (wlo + (a - wlo)) by lia. apply SM. clear -IW. lia. }
      destruct (Z.eq_dec a (thr + 3168)) as [->|NT].
      { (first [ pose proof ((ar_cache _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI))) as dR_9; dand5 dR_9 as _ _ _ MT _ | pose proof (ar_cache _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI)) as (_ & _ & _ & MT & _) ]). apply (MT 3168). lia. }
      destruct (classic (X a)) as [Xa|NX]; [exact (proj2 (proj2 (XOK a Xa)))|].
      rewrite <- (AG a Ha NW NT). { exact Hv1. } 2: exact NX.
      intros E. apply NI. unfold in_image. cbn [cl_errno cl_image_lo cl_image_hi LPA] in E |- *. clear -E. lia.
    - exact HI.
    - exact SB.
  Qed.
End ShellW.


(* [comment removed for export] *)
Lemma wamd_sbm : forall md md', same_but_materialized md md' -> m_halted md = None -> amd_frame md md'.
Proof.
  intros md md' SB Hh. unfold same_but_materialized in SB. unfold amd_frame. rewrite SB.
  unfold with_vm_backing. destruct md as [fd [maps lazy mat] io fs proc lim tm sc sg]; cbn.
  OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try reflexivity. unfold m_halted in *. cbn in *. exact Hh.
Qed.
Lemma wamd_sbm_l : forall md0 md md', same_but_materialized md0 md -> m_halted md0 = None -> amd_frame md md' -> amd_frame md0 md'.
Proof. intros md0 md md' SB Hh AF. eapply amd_frame_trans; [apply wamd_sbm; eassumption | exact AF]. Qed.
Lemma wamd_sbm_r : forall md md' md'', amd_frame md md' -> same_but_materialized md' md'' -> amd_frame md md''.
Proof.
  intros md md' md'' AF SB. eapply amd_frame_trans; [exact AF | apply wamd_sbm; [exact SB|]].
  unfold amd_frame in AF. tauto.
Qed.

(* [comment removed for export] *)
Lemma stk_mapped_pa `{Clg : Ceiling} : forall (v : mem) lo hi a n, stk rsegs v lo hi -> alloc_ceiling <= lo -> lo <= a -> a + n <= hi -> mapped v a n.
Proof.
  (intros v lo hi a n; (first [ intro dR_11; dand3 dR_11 as S0 S1 S | intros (S0 & S1 & S) ]); intros Hlo Ha Hn i Hi). pose proof alloc_ceiling_val as CE.
  destruct (S (a + i) ltac:(lia)) as [W _]. unfold wview, wa in W. rewrite unsigned_lit in W by lia.
  rewrite (pa_find_segment_none (a + i) 1 ltac:(lia) ltac:(lia)) in W. destruct (v (wz (a + i))); [discriminate| exact W].
Qed.

Section FrameShell.
Context {Clg : Ceiling}.
  Variables (owned owned' victim newb : Z -> Prop) (hi win : Z) (v v1 v' v2 : mem).
  Let window (a : Z) : Prop := hi - win <= a < hi.
  Let errno (a : Z) : Prop := cl_errno LPA <= a < cl_errno LPA + 4.
  Let notimg (a : Z) : Prop := a + 1 <= 0x10000 \/ 0x60a000 <= a.
  Hypothesis CORE : frame_ok LPA owned owned' hi win victim newb v1 v'.
  (* [comment removed for export] *)
  Hypothesis P1 : forall a, 0 <= a < 2^64 -> ~ window a -> ~ owned a -> v1 (wz a) = v (wz a).
  Hypothesis P2 : forall a, notimg a -> 0 <= a < 2^64 -> v (wz a) <> None -> v1 (wz a) <> None.
  (* [comment removed for export] *)
  Hypothesis E1 : forall a, 0 <= a < 2^64 -> ~ window a -> ~ errno a -> ~ newb a -> v2 (wz a) = v' (wz a).
  Hypothesis E2 : forall a, notimg a -> 0 <= a < 2^64 -> v' (wz a) <> None -> v2 (wz a) <> None.
  Hypothesis E3 : mapped v2 (hi - win) win.
  (* [comment removed for export] *)
  Hypothesis OW : forall a, owned a -> ~ window a /\ ~ errno a.
  Hypothesis VW : forall a, victim a -> ~ window a /\ ~ errno a.

  Lemma frame_ok_shell : frame_ok LPA owned owned' hi win victim newb v v2.
  Proof.
    destruct CORE as (F1 & F2 & F3 & F4 & F5 & F6 & F7). unfold frame_ok.
    assert (HZN : forall a, heap_zone LPA a -> notimg a).
    { intros a [_ NI]. unfold in_image in NI. cbn [cl_image_lo cl_image_hi LPA] in NI. unfold notimg. lia. }
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits.
    - intros a Ha NO NO' NW NE NV NN. rewrite (E1 a Ha NW NE NN), (F1 a Ha NO NO' NW NE NV NN). exact (P1 a Ha NW NO).
    - intros a Ha NI Hv. unfold in_image in NI. cbn [cl_image_lo cl_image_hi LPA] in NI.
      destruct (F2 a Ha ltac:(unfold in_image; cbn [cl_image_lo cl_image_hi LPA]; exact NI) (P2 a ltac:(unfold notimg; lia) Ha Hv)) as [O|[V|P]];
        [left; exact O| right; left; exact V| right; right]. apply (E2 a ltac:(unfold notimg; lia) Ha P).
    - exact E3.
    - intros a Ha NB. destruct (F4 a Ha NB) as [O|[V|[N HZ]]]; [left; exact O| right; left; exact V| right; right].
      split; [|exact HZ]. destruct (v (wz a)) eqn:E; [|reflexivity]. exfalso. apply (P2 a (HZN a HZ) Ha); [rewrite E; discriminate| exact N].
    - intros a Ha O'. destruct (F5 a Ha O') as [O|[V|[N HZ]]]; [left; exact O| right; left; exact V| right; right].
      split; [|exact HZ]. destruct (v (wz a)) eqn:E; [|reflexivity]. exfalso. apply (P2 a (HZN a HZ) Ha); [rewrite E; discriminate| exact N].
    - intros a Ha O NO'. destruct (F6 a Ha O NO') as [NB|N]; [left; exact NB|]. destruct (Classical_Prop.classic (newb a)) as [NB|NNB]; [left; exact NB| right].
      destruct (OW a O) as [NW NE]. rewrite (E1 a Ha NW NE NNB). exact N.
    - intros a Ha V. destruct (F7 a Ha V) as [O'|[NB|N]]; [left; exact O'| right; left; exact NB|].
      destruct (Classical_Prop.classic (newb a)) as [NB|NNB]; [right; left; exact NB| right; right].
      destruct (VW a V) as [NW NE]. rewrite (E1 a Ha NW NE NNB). exact N.
  Qed.
End FrameShell.

(* [comment removed for export] *)
(* [comment removed for export] *)
