(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require TP_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX Exec Frame.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ref Require Import XE_kit.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AsConst AsIface AsIface5 AsIface7 AsIface8 AsCXXHeap AsWalk AsStack0 AXPres AXKit AXRep AXRep2 AXPRep AXPRep2
     AXRep_fields AXRep_mbuf AXImgKit X8Kit X8LeafKit X8SRKit X8_P_ftab_rep X8_F_insert2 X8_F_insert4 X8_state1_stmt X8_state2_stmt X8_mbuf_stmt X8_pst
     X8_rsfree X8_put_stmt X8_cobj X8_S_place X8_stream_stmt X8_stream_stmt4 X8_S_kit X8_read_stmt X8_read2 X8_read3.
From OSSVerify.Proofs.boost_beast.http_request.lib.RB Require Import RBMem RBShape DList.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma in_app_keep : forall {A} (b x : A) (L1 L2 : list A), In b (L1 ++ x :: L2) -> b = x \/ In b (L1 ++ L2).
Proof.
  intros A b x L1 L2 IN. apply in_app_or in IN. destruct IN as [IN | [<- | IN]]; [right | left; reflexivity | right]; apply in_or_app; [left | right]; exact IN.
Qed.

Lemma AFieldsOwn_keep : forall LB LB' em (X : Z),
  AFieldsOwn LB em -> (forall b, In b LB -> In b LB' \/ blk_addr b = X) -> (forall e d, em !! e = Some d -> e <> X) -> AFieldsOwn LB' em.
Proof.
  intros LB LB' em X OWN KEEP NX e d Le. destruct (OWN e d Le) as [p [IN SZ]]. exists p. split; [| exact SZ].
  destruct (KEEP _ IN) as [K | K]; [exact K | exfalso; exact (NX e d Le K)].
Qed.

Lemma AMBufOwn_keep : forall LB LB' es (X : Z),
  AMBufOwn LB es -> (forall b, In b LB -> In b LB' \/ blk_addr b = X) -> (forall x s, In (x, s) es -> x <> X) -> AMBufOwn LB' es.
Proof.
  intros LB LB' es X OWN KEEP NX x s IN. destruct (OWN x s IN) as [p INb]. exists p.
  destruct (KEEP _ INb) as [K | K]; [exact K | exfalso; exact (NX x s IN K)].
Qed.

Lemma ASvOwn_keep : forall LB LB' m ptr len (X : Z),
  ASvOwn LB m ptr len -> (forall b, In b LB -> In b LB' \/ blk_addr b = X) -> (1 <= len -> ptr <> X) -> ASvOwn LB' m ptr len.
Proof.
  intros LB LB' m ptr len X [K | (L1 & p & bs & IN & C & AD)] KEEP NX; [left; exact K | right]. split; [exact L1|]. exists p, bs.
  split; [| split; [exact C| exact AD]]. destruct (KEEP _ IN) as [K | K]; [exact K | exfalso; exact (NX L1 K)].
Qed.

Lemma HdrOwnA_keep : forall LB LB' m h (X : Z),
  HdrOwnA LB m h -> (forall b, In b LB -> In b LB' \/ blk_addr b = X) ->
  (1 <= hv_ml h -> hv_mp h <> X) -> (1 <= hv_tl h -> hv_tp h <> X) -> HdrOwnA LB' m h.
Proof.
  intros LB LB' m h X (O1 & O2 & R1 & R2) KEEP N1 N2. split; [| split; [| split; [exact R1 | exact R2]]].
  - eapply ASvOwn_keep; [exact O1 | exact KEEP | exact N1].
  - eapply ASvOwn_keep; [exact O2 | exact KEEP | exact N2].
Qed.

Section KEEP.
  Context {HCEIL : HeapCeil}.
Lemma fb_ok_keep : forall LB LB' F (X : Z),
  fb_ok LB F -> (forall b, In b LB -> In b LB' \/ blk_addr b = X) -> (F <> FB_empty -> fb_begin F <> X) -> fb_ok LB' F.
Proof.
  intros LB LB' F X [K | (p & IN & R)] KEEP NX; [left; exact K | right]. exists p. split; [| exact R].
  destruct (KEEP _ IN) as [K | K]; [exact K | exfalso]. apply NX; [| exact K]. intros ->. destruct R as ((R1 & _) & _). cbn in R1. lia.
Qed.

Lemma AFlatBuf_keep : forall LB LB' m a F ds (X : Z),
  AFlatBuf LB m a F ds -> (forall b, In b LB -> In b LB' \/ blk_addr b = X) -> (F <> FB_empty -> fb_begin F <> X) -> AFlatBuf LB' m a F ds.
Proof.
  intros LB LB' m a F ds X (C & OK & R) KEEP NX. split; [exact C|]. split; [eapply fb_ok_keep; [exact OK | exact KEEP | exact NX]| exact R].
Qed.

Lemma AStateBlock_keep : forall LB LB' m b ioc implb S ds (X : Z),
  AStateBlock LB m b ioc implb S ds -> (forall x, In x LB -> In x LB' \/ blk_addr x = X) -> b <> X ->
  (st_fb S <> FB_empty -> fb_begin (st_fb S) <> X) -> AStateBlock LB' m b ioc implb S ds.
Proof.
  intros LB LB' m b ioc implb S ds X (p & j7 & j16 & j4 & IN & RB & CH & OK & EV & CE & CW & PM & FB & REST) KEEP NB NF.
  exists p, j7, j16, j4. split; [destruct (KEEP _ IN) as [K | K]; [exact K | exfalso; exact (NB K)]|].
  split; [exact RB|]. split; [exact CH|]. split; [exact OK|]. split; [exact EV|]. split; [exact CE|]. split; [exact CW|]. split; [exact PM|].
  split; [eapply AFlatBuf_keep; [exact FB | exact KEEP | exact NF] | exact REST].
Qed.

End KEEP.

(* [comment removed for export] *)
Definition dbp_dA (FB : fbv) (n : Z) : Z :=
  if fb_prep_inplace FB n || fb_prep_slide FB n then 0
  else if fb_begin FB =? 0 then fb_newsize FB n else fb_newsize FB n + fb_cap FB + AWILDB.

(* [comment removed for export] *)
Definition pst_lbnA (d : pst) (LBn : list block) (A : Z) : pst :=
  mkPST (ps_c d) (ps_S d) (ps_L d) (ps_ns d) (ps_ls d) (ps_em d) (ps_h d) (ps_u d) (ps_es d) (ps_insz d) (ps_g d) (ps_rdi d) LBn A.

Section HCW.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Hypothesis HH8 : asan_rt_hyps8 H.

(* [comment removed for export] *)
Lemma same_block : forall s LB m p1 p2 A n1 n2,
  as_RHEAP H s LB m -> In (p1, A, n1) LB -> In (p2, A, n2) LB -> 0 < n1 -> 0 < n2 -> (p1, A, n1) = (p2, A, n2).
Proof.
  intros s LB m p1 p2 A n1 n2 HP I1 I2 P1 P2. destruct (bptr_eq_dec p1 p2) as [E | D].
  - exact (nodup_blk_eq _ _ _ (ah_nodup H HH _ _ _ HP) I1 I2 E).
  - exfalso. destruct (ah_disj H HH _ _ _ _ _ HP I1 I2 D) as [K | K]; cbn in K; lia.
Qed.

(* [comment removed for export] *)
Lemma lb_remove_app : forall L1 x L2,
  List.NoDup (map blk_id (L1 ++ x :: L2)) -> as_lb_remove H (blk_id x) (L1 ++ x :: L2) = L1 ++ L2.
Proof.
  pose proof (ah_lb_remove H HH) as (R1 & R2 & R3).
  induction L1 as [|b L1 IH]; intros x L2 ND.
  - cbn in ND |- *. destruct x as [[p A] n]. cbn. apply R1. inversion ND; subst. exact H2.
  - cbn in ND |- *. inversion ND as [|y l NI ND']; subst.
    rewrite R2; [rewrite (IH x L2 ND'); reflexivity|].
    intros E. apply NI. rewrite E. rewrite map_app. apply in_or_app. right. left. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma prep_grow_facts : forall FB, fb_begin FB <= fb_in FB <= fb_out FB -> fb_out FB <= fb_last FB <= fb_end FB ->
  fb_prep_inplace FB (read_size_val FB) || fb_prep_slide FB (read_size_val FB) = false ->
  read_size_val FB = 512 /\ fb_cap FB - fb_size FB < 512 /\ fb_newsize FB (read_size_val FB) = Z.max (2 * fb_size FB) (fb_size FB + 512).
Proof.
  intros FB S1 S2 C. apply Bool.orb_false_iff in C. destruct C as [C1 C2]. apply Z.leb_gt in C1. apply Z.leb_gt in C2.
  unfold read_size_val, fb_newsize, fb_cap, fb_size in *.
  assert (K : fb_end FB - fb_begin FB - (fb_out FB - fb_in FB) < 512) by lia.
  split; [lia|]. split; [lia|]. replace (Z.min (Z.max 512 (fb_end FB - fb_begin FB - (fb_out FB - fb_in FB))) 65536) with 512 by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma dbp_charge : forall (C : rsc) MA (w : rsw),
  rs_static H C -> RWp H C MA w ->
  (w_FB w <> FB_empty -> 0 < fb_begin (w_FB w) /\ 0 < fb_cap (w_FB w)) -> zlength (w_fds w) = fb_size (w_FB w) ->
  fb_begin (w_FB w) <= fb_in (w_FB w) <= fb_out (w_FB w) -> fb_out (w_FB w) <= fb_last (w_FB w) <= fb_end (w_FB w) ->
  let n := read_size_val (w_FB w) in let dA := dbp_dA (w_FB w) n in
  0 <= dA /\ ps_A (w_d w) + dA <= MA /\ fbp_cost H (w_FB w) n true <= as_Cm H (ps_A (w_d w) + dA) - as_Cm H (ps_A (w_d w)).
Proof.
  intros C MA w STC RP OLDSH OLDSZ SH1 SH2. cbv zeta.
  destruct C as [bs fb P E ioc N lo B0 shi SP stb implb A LBin LF pad7 pad2 j13 j32a j8a j32b j8b mb m00 mo0 gp tp F fc MXc CXc].
  destruct w as [d PB FBB FB fds Fs sds nr]. destruct d as [c S L1 ns ls em h u es insz g rdi LBn Ag].
  unfold RWp, rs_static in *. cbn_w_all. cbn [ps_c ps_S ps_L ps_ns ps_ls ps_em ps_h ps_u ps_es ps_insz ps_g ps_rdi ps_LBn ps_A] in *.
  destruct STC as (AOP & AOE & P8 & E8 & BS8 & FB8 & SEPPE & SEPBF & CEIL & NR & IOC & (p7 & INS) & RBS & INA & SEPAS & LFL4 & LFL1 & TP & MXL & CXL).
  destruct RP as (PCOK & OWN & MOWN & DFB & HST & U01 & CAP & LES & INZ & LEN1 & HDJ & HL8 & SK62 & AOWN & PERM & FOK & FRL & FRB & FRT & FRM & FRF & DJL & DJB & DJT & DJM
                  & OFFP & OFFE & STRM & SZS & NRK & CPM & BY & CN & IZ & AG0 & AL).
  pose proof (ah_costs H HH) as (Cm0 & CmM & Cf0 & CfM & CmS & CfS). pose proof (read_size_val_range FB) as RSV.
  assert (BRNN : 0 <= body_res es insz (zlength fds + zlength sds)) by (unfold body_res; unfold zlength in *; clear - CAP LES INZ; lia).
  pose proof PCOK as (_ & _ & _ & _ & _ & Hl & _). pose proof (pot_if_range (pc_state c)) as (PR34 & _).
  assert (CP0 : 0 <= fb_cap FB) by (unfold fb_cap; clear - SH1 SH2; lia).
  unfold dbp_dA, fbp_cost. destruct (fb_prep_inplace FB (read_size_val FB) || fb_prep_slide FB (read_size_val FB)) eqn:COND.
  - pose proof (fb_res_nonneg N (fb_cap FB) NR ltac:(clear - CP0 CPM; lia)) as F0.
    split; [clear; lia|]. split; [clear - AL BRNN Hl PR34 F0; lia|]. rewrite Z.add_0_r. clear. lia.
  - destruct (prep_grow_facts FB SH1 SH2 COND) as (N512 & GROW & ENS).
    destruct (fb_res_step N (fb_cap FB) (fb_size FB) NR ltac:(unfold fb_cap, fb_size; clear - SH1 SH2; lia) ltac:(clear - OLDSZ SZS; unfold zlength in *; lia) CPM GROW)
      as (STEP & CLE & CLT & CPOS'). rewrite <- ENS in STEP, CLE, CLT, CPOS'.
    pose proof (fb_res_nonneg N (fb_newsize FB (read_size_val FB)) NR ltac:(clear - CPOS' CLE; lia)) as F0.
    destruct (fbv_eq_dec FB FB_empty) as [EFB|NE].
    + assert (EB : fb_begin FB = 0) by (rewrite EFB; reflexivity). assert (EC : fb_cap FB = 0) by (rewrite EFB; reflexivity).
      rewrite EB. rewrite EC in STEP, AL |- *. cbn [Z.eqb] in STEP |- *.
      split; [clear - CPOS'; lia|]. split; [clear - AL BRNN Hl PR34 F0 STEP; lia|].
      pose proof (CmS Ag (fb_newsize FB (read_size_val FB)) AG0 ltac:(clear - CPOS'; lia)) as K. clear - K. lia.
    + destruct (OLDSH NE) as [BP CP].
      replace (fb_begin FB =? 0) with false by (symmetry; apply Z.eqb_neq; clear - BP; lia).
      replace (fb_cap FB =? 0) with false in STEP by (symmetry; apply Z.eqb_neq; clear - CP; lia).
      split; [unfold AWILDB; clear - CPOS' CP; lia|]. split; [clear - AL BRNN Hl PR34 F0 STEP; lia|].
      pose proof (hyps8_realloc_round H HH HH8 Ag (fb_newsize FB (read_size_val FB)) (fb_cap FB) AG0 ltac:(clear - CPOS'; lia) ltac:(clear - CP; lia)) as K8. clear - K8. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma RWp_dbp_post : forall (C : rsc) MA (w : rsw) s0 (s' : as_St H) (LB' : list block) (FB' : fbv) (m m' : mem),
  rs_static H C -> RWp H C MA w ->
  let P := c_P C in let d := w_d w in let LB := ps_LBn d ++ c_LBin C in let n := read_size_val (w_FB w) in
  as_RHEAP H s0 LB m -> PutUw P (c_mb C) d m -> HdrOwnA LB m (ps_h d) -> aceil <= c_SP C ->
  as_RHEAP H s' LB' m' ->
  AFlatBuf LB' m' (c_fb C) FB' (w_fds w) -> fb_last FB' = fb_out FB' + n ->
  fb_prepare_rel H LB (w_FB w) n LB' FB' ->
  (w_FB w <> FB_empty -> 0 < fb_begin (w_FB w) /\ 0 < fb_cap (w_FB w)) -> zlength (w_fds w) = fb_size (w_FB w) ->
  fb_begin (w_FB w) <= fb_in (w_FB w) <= fb_out (w_FB w) -> fb_out (w_FB w) <= fb_last (w_FB w) <= fb_end (w_FB w) ->
  exists LBn' pf',
       LB' = LBn' ++ c_LBin C
    /\ RWp H C MA (mkW (pst_lbnA d LBn' (ps_A d + dbp_dA (w_FB w) n)) (w_PB w) [(pf', fb_begin FB', fb_cap FB')] FB' (w_fds w) (w_Fs w) (w_sds w) (w_nr w))
    /\ (forall b, In b LB -> In b LB' \/ blk_addr b = fb_begin (w_FB w))
    /\ c_stb C <> fb_begin (w_FB w)
    /\ (1 <= c_N C -> c_A C <> fb_begin (w_FB w))
    /\ (w_FB w <> FB_empty -> forall e dd, ps_em d !! e = Some dd -> e + esize dd <= fb_begin (w_FB w) \/ fb_end (w_FB w) <= e)
    /\ (w_FB w <> FB_empty -> forall x sz, In (x, sz) (ps_es d) -> x + mb_block_size sz <= fb_begin (w_FB w) \/ fb_end (w_FB w) <= x)
    /\ (w_FB w <> FB_empty -> hv_tl (ps_h d) <> 0 -> hv_tp (ps_h d) <> fb_begin (w_FB w))
    /\ (w_FB w <> FB_empty -> hv_ml (ps_h d) <> 0 -> hv_mp (ps_h d) <> fb_begin (w_FB w))
    /\ FB' <> FB_empty
    /\ (fb_end FB' <= c_stb C \/ c_stb C + SZ_SPCI_STATE <= fb_begin FB')
    /\ (w_Fs w = FB_empty \/ (fb_end FB' <= fb_begin (w_Fs w) \/ fb_end (w_Fs w) <= fb_begin FB'))
    /\ 0 <= dbp_dA (w_FB w) n
    /\ fbp_cost H (w_FB w) n true <= as_Cm H (ps_A d + dbp_dA (w_FB w) n) - as_Cm H (ps_A d).
Proof.
  intros C MA w s0 s' LB' FB' m m' STC RP. cbv zeta. intros HP UW HOWN CSP HP' FBU' LAST REL OLDSH OLDSZ SH1 SH2.
  destruct C as [bs fb P E ioc N lo B0 shi SP stb implb A LBin LF pad7 pad2 j13 j32a j8a j32b j8b mb m00 mo0 gp tp F fc MXc CXc].
  destruct w as [d PB FBB FB fds Fs sds nr]. destruct d as [c S L1 ns ls em h u es insz g rdi LBn Ag].
  unfold pst_lbnA, RWp, rs_static in *. cbn_w_all. cbn [ps_c ps_S ps_L ps_ns ps_ls ps_em ps_h ps_u ps_es ps_insz ps_g ps_rdi ps_LBn ps_A] in *.
  destruct STC as (AOP & AOE & P8 & E8 & BS8 & FB8 & SEPPE & SEPBF & CEIL & NR & IOC & (p7 & INS) & RBS & INA & SEPAS & LFL4 & LFL1 & TP & MXL & CXL).
  destruct RP as (PCOK & OWN & MOWN & DFB & HST & U01 & CAP & LES & INZ & LEN1 & HDJ & HL8 & SK62 & AOWN & PERM & FOK & FRL & FRB & FRT & FRM & FRF & DJL & DJB & DJT & DJM
                  & OFFP & OFFE & STRM & SZS & NRK & CPM & BY & CN & IZ & AG0 & AL).
  pose proof aceil_facts as (AF1 & AF2 & AF3).
  unfold PutUw in UW. cbn [ps_c ps_S ps_L ps_ns ps_ls ps_em ps_h ps_u ps_es ps_insz ps_g ps_rdi ps_LBn ps_A] in UW. destruct UW as (FC & _ & _ & MB & _).
  pose proof (AFlatBuf_shape _ _ _ _ _ FBU') as (FS1 & FS2 & FS3 & FS4 & FS5).
  pose proof (read_size_val_range FB) as RSV. set (n := read_size_val FB) in *.
  assert (NE' : FB' <> FB_empty) by (intros ->; cbn in LAST; lia).
  destruct FS5 as [K | (BP' & BAL' & BCP' & BAP' & pf0 & INf0)]; [exfalso; exact (NE' K)|].
  pose proof (rblock_bounds _ _ RBS) as (RB1 & RB2 & RB3 & RB4 & RB5 & RB6).
  (* [comment removed for export] *)
  assert (OLD : FB <> FB_empty -> exists pf, FBB = [(pf, fb_begin FB, fb_cap FB)] /\ In (pf, fb_begin FB, fb_cap FB) LBn).
  { intros NE. destruct FOK as [[K _] | (_ & pf & ->)]; [exfalso; exact (NE K)|].
    exists pf. split; [reflexivity|]. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_or_app. right. left. reflexivity. }
  (* [comment removed for export] *)
  assert (NXE : FB <> FB_empty -> forall e, e ∈ L1 -> e <> fb_begin FB).
  { intros NE e He. destruct (OLDSH NE) as [_ CP]. pose proof (DJL NE e He) as K. clear - CP K. unfold fb_cap in CP. lia. }
  assert (NXB : FB <> FB_empty -> forall x sz, In (x, sz) es -> x <> fb_begin FB).
  { intros NE x sz IN. destruct (OLDSH NE) as [_ CP]. destruct (mb_elem_facts _ _ _ _ _ _ MB IN) as (_ & S0 & _). pose proof (DJB NE x sz IN) as K. clear - CP S0 K. unfold fb_cap in CP. lia. }
  assert (NXT : FB <> FB_empty -> hv_tl h <> 0 -> hv_tp h <> fb_begin FB).
  { intros NE TL. destruct (OLDSH NE) as [_ CP]. destruct HOWN as (_ & _ & _ & TLR). pose proof (DJT NE TL) as K. clear - CP TLR TL K. unfold fb_cap in CP. lia. }
  assert (NXM : FB <> FB_empty -> hv_ml h <> 0 -> hv_mp h <> fb_begin FB).
  { intros NE ML. destruct (OLDSH NE) as [_ CP]. destruct HOWN as (_ & _ & MLR & _). pose proof (DJM NE ML) as K. clear - CP MLR ML K. unfold fb_cap in CP. lia. }
  pose proof (proj1 RBS) as SPOS.
  assert (NXS : stb <> fb_begin FB).
  { destruct (fbv_eq_dec FB FB_empty) as [-> | NE]; [cbn; clear - SPOS; lia|]. destruct (OLDSH NE) as [_ CP].
    pose proof (FRF NE stb SZ_SPCI_STATE ltac:(right; right; left; exists (p7, stb, SZ_SPCI_STATE); split; [exact INS | cbn; clear; lia]) ltac:(unfold SZ_SPCI_STATE; clear; lia)) as K.
    clear - K CP. unfold fb_cap, SZ_SPCI_STATE in *. lia. }
  assert (NXA : 1 <= N -> A <> fb_begin FB).
  { intros N1. destruct (INA N1) as [p9 IN9]. destruct (fbv_eq_dec FB FB_empty) as [-> | NE].
    - destruct (ah_blocks H HH _ _ _ _ HP ltac:(apply in_or_app; right; exact IN9)) as (Q1 & _). cbn in Q1. cbn. clear - Q1. lia.
    - destruct (OLDSH NE) as [_ CP].
      pose proof (FRF NE A N ltac:(right; right; left; exists (p9, A, N); split; [exact IN9 | cbn; clear; lia]) ltac:(clear - N1; lia)) as K. clear - K CP N1. unfold fb_cap in *. lia. }
  (* [comment removed for export] *)
  assert (EOFF : FB <> FB_empty -> forall e dd, em !! e = Some dd -> e + esize dd <= fb_begin FB \/ fb_end FB <= e).
  { intros NE. destruct (OLD NE) as (pf & EFBB & INn). intros e dd Le. destruct (OWN e dd Le) as (pe & INe & _). pose proof (esize_ge dd).
    pose proof FC as (_ & _ & _ & _ & _ & _ & _ & DOM & _).
    destruct (blocks_full_sep H HH _ _ _ _ _ _ _ _ _ 48 HP INe ltac:(apply in_or_app; left; exact INn) ltac:(lia)
                ltac:(destruct (DJL NE e ltac:(apply (proj2 (DOM e)); rewrite Le; eexists; reflexivity)); [left| right]; unfold fb_cap; lia)); unfold fb_cap in *; lia. }
  assert (BOFF : FB <> FB_empty -> forall x sz, In (x, sz) es -> x + mb_block_size sz <= fb_begin FB \/ fb_end FB <= x).
  { intros NE. destruct (OLD NE) as (pf & EFBB & INn). intros x sz IN. destruct (MOWN x sz IN) as (px & INx). destruct (mb_elem_facts _ _ _ _ _ _ MB IN) as (_ & S0 & S24 & _).
    destruct (blocks_full_sep H HH _ _ _ _ _ _ _ _ _ (24 + sz) HP INx ltac:(apply in_or_app; left; exact INn) ltac:(lia)
                ltac:(destruct (DJB NE x sz IN); [left| right]; unfold fb_cap; lia)); unfold fb_cap in *; lia. }
  assert (SUBin : forall b, In b LBin -> In b (LBn ++ LBin)) by (intros b Hb; apply in_or_app; right; exact Hb).
  pose proof FC as (_ & _ & _ & _ & _ & _ & _ & DOM & _).
  (* [comment removed for export] *)
  enough (K : exists LBn' pf', LB' = LBn' ++ LBin
      /\ (forall b, In b (LBn ++ LBin) -> In b LB' \/ blk_addr b = fb_begin FB)
      /\ Permutation LBn' (PB ++ [(pf', fb_begin FB', fb_cap FB')])
      /\ lb_bytes (LBn' ++ LBin) - fb_cap FB' = lb_bytes (LBn ++ LBin) - lb_bytes FBB
      /\ Z.of_nat (length (LBn' ++ LBin)) - 1 = Z.of_nat (length (LBn ++ LBin)) - Z.of_nat (length FBB)
      /\ blk_fresh H LBin SP (fb_begin FB') (fb_cap FB')
      /\ (forall e, e ∈ L1 -> e + 48 <= fb_begin FB' \/ fb_end FB' <= e)
      /\ (forall x sz, In (x, sz) es -> x + 24 + sz <= fb_begin FB' \/ fb_end FB' <= x)
      /\ (hv_tl h <> 0 -> hv_tp h + hv_tl h <= fb_begin FB' \/ fb_end FB' <= hv_tp h)
      /\ (hv_ml h <> 0 -> hv_mp h + hv_ml h <= fb_begin FB' \/ fb_end FB' <= hv_mp h)
      /\ fb_cap FB' <= CAPMAX N
      /\ 0 <= dbp_dA FB n /\ dbp_dA FB n + fb_res N (fb_cap FB') <= fb_res N (fb_cap FB)
      /\ fbp_cost H FB n true <= as_Cm H (Ag + dbp_dA FB n) - as_Cm H Ag).
  { destruct K as (LBn' & pf' & ELB & KEEP & PERM' & BYE & CNE & FRF' & DJL' & DJB' & DJT' & DJM' & CPM' & DA0 & DAR & COST).
    exists LBn', pf'. split; [exact ELB|].
    assert (KEEPx : forall b, In b (LBn ++ LBin) -> In b (LBn' ++ LBin) \/ blk_addr b = fb_begin FB) by (rewrite <- ELB; exact KEEP).
    split.
    { split; [exact PCOK|].
      split; [eapply AFieldsOwn_keep; [exact OWN | exact KEEPx | intros e dd Le EQ; destruct (fbv_eq_dec FB FB_empty) as [EFB | NE];
              [destruct (OWN e dd Le) as [pe [INe _]]; destruct (ah_blocks H HH _ _ _ _ HP INe) as (Q1 & _); cbn in Q1; rewrite EFB in EQ; cbn in EQ; lia
              | refine (NXE NE e _ EQ); apply (proj2 (DOM e)); rewrite Le; eexists; reflexivity]]|].
      split; [eapply AMBufOwn_keep; [exact MOWN | exact KEEPx | intros x sz IN EQ; destruct (fbv_eq_dec FB FB_empty) as [EFB | NE];
              [destruct (MOWN x sz IN) as [px INx]; destruct (ah_blocks H HH _ _ _ _ HP INx) as (Q1 & _); cbn in Q1; rewrite EFB in EQ; cbn in EQ; lia
              | exact (NXB NE x sz IN EQ)]]|].
      split; [exact DFB|]. split; [exact HST|]. split; [exact U01|]. split; [exact CAP|].
      split; [exact LES|]. split; [exact INZ|]. split; [exact LEN1|]. split; [exact HDJ|]. split; [exact HL8|]. split; [exact SK62|].
      split; [exact AOWN|]. split; [exact PERM'|].
      split; [right; split; [exact NE'|]; exists pf'; reflexivity|].
      split; [exact FRL|]. split; [exact FRB|]. split; [exact FRT|]. split; [exact FRM|].
      split; [intros _; exact FRF'|]. split; [intros _; exact DJL'|]. split; [intros _; exact DJB'|]. split; [intros _; exact DJT'|]. split; [intros _; exact DJM'|].
      split; [exact OFFP|]. split; [exact OFFE|].
      split; [exact STRM|]. split; [exact SZS|]. split; [exact NRK|]. split; [exact CPM'|].
      set (s34 := if pc_state c <=? 9 then 34 else 0) in *. set (s8 := if pc_state c <=? 1 then 8 else 0) in *. set (s2 := if pc_state c <=? 9 then 2 else 0) in *.
      cbn [lb_bytes fold_right length blk_size snd] in *.
      pose proof (fbb_ok_facts _ _ FOK) as (FBBb & FBBn & _).
      split; [clear - BY BYE FBBb; lia|]. split; [clear - CN CNE FBBn; lia|]. split; [exact IZ|].
      split; [clear - AG0 DA0; lia|]. clear - AL DAR. lia. }
    split; [exact KEEP|]. split; [exact NXS|]. split; [exact NXA|]. split; [exact EOFF|]. split; [exact BOFF|]. split; [exact NXT|]. split; [exact NXM|]. split; [exact NE'|].
    split.
    { destruct (FRF' stb SZ_SPCI_STATE ltac:(right; right; left; exists (p7, stb, SZ_SPCI_STATE); split; [exact INS | cbn; lia]) ltac:(unfold SZ_SPCI_STATE; lia)); unfold fb_cap in *; [right | left]; lia. }
    split.
    { destruct STRM as [[_ EFs] | (N1 & SA & SE)]; [left; exact EFs | right]. destruct (INA N1) as [p9 IN9]. rewrite SA, SE.
      destruct (FRF' A N ltac:(right; right; left; exists (p9, A, N); split; [exact IN9 | cbn; lia]) ltac:(lia)); unfold fb_cap in *; [right | left]; lia. }
    split; [exact DA0| exact COST]. }
  (* [comment removed for export] *)
  assert (NSZ : fb_newsize FB n <= CAPMAX N) by (unfold fb_newsize, CAPMAX; clear - OLDSZ SZS NR RSV; unfold zlength in *; lia).
  pose proof (ah_costs H HH) as (Cm0 & CmM & Cf0 & CfM & CmS & CfS).
  unfold fb_prepare_rel in REL. unfold dbp_dA, fbp_cost.
  destruct (fb_prep_inplace FB n || fb_prep_slide FB n) eqn:COND.
  - (* [comment removed for export] *)
    destruct REL as [EFB' ELB'].
    assert (NE : FB <> FB_empty).
    { intros EFB. rewrite EFB in COND. unfold fb_prep_inplace, fb_prep_slide, fb_cap, fb_size in COND. cbn in COND.
      apply Bool.orb_true_iff in COND. destruct COND as [K|K]; apply Z.leb_le in K; clear - K RSV; lia. }
    assert (SB : fb_begin FB' = fb_begin FB /\ fb_end FB' = fb_end FB /\ fb_cap FB' = fb_cap FB).
    { rewrite EFB'. unfold fb_prep_small, fb_cap. destruct (fb_prep_inplace FB n); cbn; clear; lia. }
    destruct SB as (SB1 & SB2 & SB3). destruct (OLD NE) as (pf & EFBB & INn). subst FBB.
    exists LBn, pf. rewrite SB1, SB2, SB3. cbn [lb_bytes fold_right length blk_size snd].
    split; [exact ELB'|]. split; [intros b Hb; left; rewrite ELB'; exact Hb|]. split; [exact PERM|].
    split; [lia|]. split; [lia|].
    split; [exact (FRF NE)|]. split; [exact (DJL NE)|]. split; [exact (DJB NE)|]. split; [exact (DJT NE)|]. split; [exact (DJM NE)|]. split; [exact CPM|].
    split; [clear; lia|]. split; [clear; lia|]. rewrite Z.add_0_r. clear. lia.
  - (* [comment removed for export] *)
    destruct REL as (p' & A' & RBA & EFB' & CASES).
    destruct (prep_grow_facts FB SH1 SH2 COND) as (N512 & GROW & ENS). fold n in N512, ENS. fold n in ENS.
    assert (SB : fb_begin FB' = A' /\ fb_end FB' = A' + fb_newsize FB n /\ fb_cap FB' = fb_newsize FB n).
    { rewrite EFB'. unfold fb_prep_grow, fb_cap. cbn. clear. lia. }
    destruct SB as (SB1 & SB2 & SB3). rewrite SB1, SB2, SB3.
    (* [comment removed for export] *)
    destruct (fb_res_step N (fb_cap FB) (fb_size FB) NR ltac:(unfold fb_cap, fb_size; clear - SH1 SH2; lia) ltac:(clear - OLDSZ SZS; unfold zlength in *; lia) CPM GROW)
      as (STEP & _ & CLT & CPOS').
    rewrite <- ENS in STEP, CLT, CPOS'.
    (* [comment removed for export] *)
    assert (FR2 : forall LBr a k, as_RHEAP H s' ((p', A', fb_newsize FB n) :: LBr) m' -> aclient_range H LBr SP a k -> 0 < k ->
                  a + k <= A' \/ A' + fb_newsize FB n <= a).
    { intros LBr a k HPr RR Hk. eapply (fresh_block_disjoint_client H HH); [exact HPr | exact RR | exact CSP | exact Hk]. }
    destruct CASES as [[EFB ELB'] | (p & INp & ELB')].
    + (* [comment removed for export] *)
      assert (EFBB : FBB = []) by (destruct FOK as [[_ K] | [K _]]; [exact K | exfalso; exact (K EFB)]).
      rewrite ELB' in HP'.
      exists ((p', A', fb_newsize FB n) :: LBn), p'. rewrite EFBB.
      split; [exact ELB'|]. split; [intros b Hb; left; rewrite ELB'; right; exact Hb|].
      split; [apply Permutation_cons_app; rewrite app_nil_r; rewrite EFBB, app_nil_r in PERM; exact PERM|].
      split. { clear. cbn [app]. rewrite ?lb_bytes_cons. cbn [lb_bytes fold_right blk_size snd]. lia. }
      split. { clear. cbn [app length]. lia. }
      split; [intros a k RR Hk; eapply FR2; [exact HP' | eapply aclient_range_LB_mono; [exact RR | exact SUBin] | exact Hk]|].
      split. { intros e He. destruct (proj1 (DOM e) He) as [dd Le]. destruct (OWN e dd Le) as [pe [INe _]]. pose proof (esize_ge dd).
               eapply FR2; [exact HP' | right; right; left; exists (pe, e, esize dd); split; [exact INe | cbn; clear - H0; lia] | clear; lia]. }
      split. { intros x sz IN. destruct (MOWN x sz IN) as [px INx]. destruct (mb_elem_facts _ _ _ _ _ _ MB IN) as (_ & S0 & S24 & _).
               destruct (FR2 _ x (24 + sz) HP' ltac:(right; right; left; exists (px, x, mb_block_size sz); split; [exact INx | cbn; clear - S24; lia]) ltac:(clear - S0; lia)) as [J|J]; clear - J; lia. }
      split. { intros TL. destruct HOWN as (_ & [[K0 _]|(TL1 & pt & bst & INt & _)] & _); [clear - K0 TL; lia|].
               eapply FR2; [exact HP' | right; right; left; exists (pt, hv_tp h, hv_tl h); split; [exact INt | cbn; clear; lia] | clear - TL1; lia]. }
      split. { intros ML. destruct HOWN as ([[K0 _]|(ML1 & pm & bsm & INm & _)] & _); [clear - K0 ML; lia|].
               eapply FR2; [exact HP' | right; right; left; exists (pm, hv_mp h, hv_ml h); split; [exact INm | cbn; clear; lia] | clear - ML1; lia]. }
      split; [exact NSZ|].
      rewrite EFB in STEP, CPOS' |- *. unfold FB_empty in STEP, CPOS' |- *. cbn [fb_begin fb_cap fb_end Z.sub Z.eqb] in STEP |- *.
      replace (fb_cap {| fb_begin := 0; fb_in := 0; fb_out := 0; fb_last := 0; fb_end := 0 |}) with 0 in STEP by reflexivity. cbn [Z.eqb] in STEP.
      split; [clear - CPOS'; lia|]. split; [exact STEP|].
      pose proof (CmS Ag (fb_newsize {| fb_begin := 0; fb_in := 0; fb_out := 0; fb_last := 0; fb_end := 0 |} n) AG0 ltac:(clear - CPOS'; lia)). clear - H0. lia.
    + (* [comment removed for export] *)
      assert (NE : FB <> FB_empty).
      { intros EFB. rewrite EFB in INp. destruct (ah_blocks H HH _ _ _ _ HP INp) as (Q1 & _). cbn in Q1. clear - Q1. lia. }
      destruct (OLDSH NE) as [BP CP]. destruct (OLD NE) as (pf & EFBB & INn). subst FBB.
      assert (Epf : p = pf).
      { pose proof (same_block _ _ _ p pf (fb_begin FB) (fb_cap FB) (fb_cap FB) HP INp ltac:(apply in_or_app; left; exact INn) CP CP) as EQ. injection EQ as E1. exact E1. }
      subst p. destruct (in_split _ _ INn) as (K1 & K2 & ELBn). subst LBn.
      pose proof (ah_nodup H HH _ _ _ HP) as ND. rewrite <- app_assoc in ND. cbn [app] in ND.
      pose proof (lb_remove_app K1 (pf, fb_begin FB, fb_cap FB) (K2 ++ LBin) ND) as EQR. cbn [blk_id fst] in EQR.
      rewrite <- app_assoc in ELB'. cbn [app] in ELB'.
      assert (ELB2 : LB' = (p', A', fb_newsize FB n) :: K1 ++ K2 ++ LBin) by (rewrite ELB'; f_equal; exact EQR). clear ELB'. rename ELB2 into ELB'.
      rewrite ELB' in HP'.
      exists ((p', A', fb_newsize FB n) :: K1 ++ K2), p'.
      split; [rewrite ELB'; cbn [app]; f_equal; first [apply app_assoc | symmetry; apply app_assoc]|].
      split. { intros b Hb. rewrite <- app_assoc in Hb. cbn [app] in Hb. destruct (in_app_keep _ _ _ _ Hb) as [-> | Hb']; [right; reflexivity | left]. rewrite ELB'. right. exact Hb'. }
      split. { apply Permutation_cons_app. rewrite app_nil_r. pose proof (@Permutation_app_inv _ K1 K2 PB [] _ PERM) as PERM2. rewrite app_nil_r in PERM2. exact PERM2. }
      split. { clear. cbn [app]. rewrite ?lb_bytes_cons, ?lb_bytes_app, ?lb_bytes_cons. cbn [lb_bytes fold_right blk_size snd]. lia. }
      split. { clear. cbn [app]. rewrite ?length_app. cbn [length]. rewrite ?length_app. cbn [length]. lia. }
      assert (SUBr : forall b, In b LBin -> In b (K1 ++ K2 ++ LBin)) by (intros b Hb; apply in_or_app; right; apply in_or_app; right; exact Hb).
      assert (KEEPr : forall b, In b ((K1 ++ (pf, fb_begin FB, fb_cap FB) :: K2) ++ LBin) -> blk_addr b <> fb_begin FB -> In b (K1 ++ K2 ++ LBin)).
      { intros b Hb NB. rewrite <- app_assoc in Hb. cbn [app] in Hb. destruct (in_app_keep _ _ _ _ Hb) as [-> | Hb']; [exfalso; exact (NB eq_refl) | exact Hb']. }
      split; [intros a k RR Hk; eapply FR2; [exact HP' | eapply aclient_range_LB_mono; [exact RR | exact SUBr] | exact Hk]|].
      split. { intros e He. destruct (proj1 (DOM e) He) as [dd Le]. destruct (OWN e dd Le) as [pe [INe _]]. pose proof (esize_ge dd).
               eapply FR2; [exact HP' | right; right; left; exists (pe, e, esize dd); split; [apply KEEPr; [exact INe | cbn; exact (NXE NE e He)] | cbn; clear - H0; lia] | clear; lia]. }
      split. { intros x sz IN. destruct (MOWN x sz IN) as [px INx]. destruct (mb_elem_facts _ _ _ _ _ _ MB IN) as (_ & S0 & S24 & _).
               destruct (FR2 _ x (24 + sz) HP' ltac:(right; right; left; exists (px, x, mb_block_size sz); split; [apply KEEPr; [exact INx | cbn; exact (NXB NE x sz IN)] | cbn; clear - S24; lia]) ltac:(clear - S0; lia)) as [J|J]; clear - J; lia. }
      split. { intros TL. destruct HOWN as (_ & [[K0 _]|(TL1 & pt & bst & INt & _)] & _); [clear - K0 TL; lia|].
               eapply FR2; [exact HP' | right; right; left; exists (pt, hv_tp h, hv_tl h); split; [apply KEEPr; [exact INt | cbn; exact (NXT NE TL)] | cbn; clear; lia] | clear - TL1; lia]. }
      split. { intros ML. destruct HOWN as ([[K0 _]|(ML1 & pm & bsm & INm & _)] & _); [clear - K0 ML; lia|].
               eapply FR2; [exact HP' | right; right; left; exists (pm, hv_mp h, hv_ml h); split; [apply KEEPr; [exact INm | cbn; exact (NXM NE ML)] | cbn; clear; lia] | clear - ML1; lia]. }
      split; [exact NSZ|].
      replace (fb_begin FB =? 0) with false in * by (symmetry; apply Z.eqb_neq; clear - BP; lia).
      replace (fb_cap FB =? 0) with false in STEP by (symmetry; apply Z.eqb_neq; clear - CP; lia).
      split; [unfold AWILDB; clear - CPOS' CP; lia|]. split; [exact STEP|].
      pose proof (hyps8_realloc_round H HH HH8 Ag (fb_newsize FB n) (fb_cap FB) AG0 ltac:(clear - CPOS'; lia) ltac:(clear - CP; lia)) as K8. clear - K8. lia.
Qed.
End HCW.
