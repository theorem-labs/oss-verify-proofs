(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import InitMem. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_kit Fz_cimg Fz_I1_defs Fz_I1_hash Fz_I1_getrn Fz_I1_split Fz_I1_rep Fz_I1_expand. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_cpy. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_M_malloc Fz_kit_ra Fz_M_realloc Fz_I1_insert Fz_I1_insert1 F_memset.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Printf_lib.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma chainv_own : forall DV m LBall L LBall' L' ns v, chainv DV m LBall L v ns ->
  (forall p A, In (p, A) ns -> cown LBall L p A 24 24 -> cown LBall' L' p A 24 24) -> chainv DV m LBall' L' v ns.
Proof.
  intros DV m LBall L LBall' L' ns. induction ns as [|[p A] ns IH]; intros v CV HO; cbn [chainv] in *; [exact CV|].
  destruct CV as (-> & O & RG & N & nx & CX & CV). split; [reflexivity|]. split; [apply HO; [left; reflexivity| exact O]|]. split; [exact RG|]. split; [exact N|].
  exists nx. split; [exact CX|]. apply IH; [exact CV|]. intros q Bq Hq. apply HO. right. exact Hq.
Qed.

Theorem lhi_double_spec : crypto_realloc_array_stmt -> lhi_double_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros CRA sp gp tp s7 s8 s9 s10 s11 z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 F fc m s LBall LB L f lh pl pb B nmb g bks data lo Bd
         Hf ROOM CST SP80 REP NMB SLO.
  pose proof CST as (HP & CO & (errv & _ & SPB & ST & LO & _ & MI & _) & _ & _ & CIMG & GLO).
  unfold LHI_STACK, CRE_STACK, RREALLOC_STACK, RMALLOC_STACK, GLOBALS_TOP, LHA_MAX in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
  rewrite unsigned_lit in ST, SPB by lia.
  destruct (lh_sep _ _ _ _ _ _ _ _ _ _ _ _ _ HP REP) as (S_LB & S_N & S_X & S_F).
  pose proof REP as (G & OL & RL & (x40 & x48 & err & pad & SCm) & OB & RB & LEN & CH & EMP & ND).
  pose proof (lh_geo_bounds g G) as GB.
  pose proof G as (G1 & G2 & G3 & G4 & G5 & G6). unfold LH_KMAX in G6.
  unfold lh_cells, ERR_FNS, lf_comp, lf_hash, lf_hashw, lf_compw, wz in SCm.
  set (na := g_na g) in *.
  (* [comment removed for export] *)
  destruct (cells_assemble (Z.to_nat na) m B ltac:(lia) ltac:(lia)) as (src & SRC).
  { intros i Hi. destruct (chain_chainv _ _ _ _ _ _ (CH (Z.of_nat i) ltac:(lia))) as (v & CV & _). exists (wz v). exact CV. }
  pose proof (rw_cells_CB_length usegs m B _ _ SRC) as LSRC.
  pose proof (munch_refl (@nil (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.
  assert (ES6 : bv_unsigned (Z_to_bv 64 na) ≪ 1 = 2 * na) by (rewrite unsigned_lit by lia; rewrite Z.shiftl_mul_pow2 by lia; lia).
  assert (EA1 : bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (2 * na)) ≪ 32)) ≫ 32 = 2 * na).
  { rewrite (unsigned_lit (2 * na)) by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite unsigned_lit by lia. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_mul. lia. }
  cprefix. do 8 step. step. rewrite ES6, EA1.
  chere. unfold crypto_realloc_array_stmt in CRA.
  eapply climpl_seq.
  { eapply CRA with (p := pb) (A := B) (n0 := 8 * na) (nm := nmb) (num := 2 * na) (sz := 8) (src := src) (lo := lo) (B := Bd);
      [exact Hf| | lia| lia| unfold MMAP_THRESHOLD; lia| exact OB| replace (Z.to_nat (8 * na)) with (8 * Z.to_nat na)%nat by lia; exact SRC| exact CST
      | rewrite unsigned_lit by lia; unfold CRE_STACK, RREALLOC_STACK, RMALLOC_STACK; lia| reflexivity| reflexivity| reflexivity].
    destruct (w_bounds (2 * na * 8) ltac:(lia)) as (W1 & W2 & _ & W3). eapply croom_weaken; [exact ROOM| lia| lia| lia]. }
  intros f1 L1 st1 ms1 (v & m1 & LBall1 & RET & FU1 & GR1 & CST1 & FRM1 & (q & A' & tail & -> & -> & RNG & BLK & ARMS)).
  destruct RET as (u0 & u1 & u2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & u3 & u4 & u5 & u6 & ->).
  cret_lit. rewrite unsigned_lit in * by lia.
  set (n' := 2 * na * 8) in *.
  set (LBall1 := (q, A', n') :: lb_remove pb LBall) in *.
  pose proof FRM1 as (CFR1 & [KP1 KP1'] & _).
  pose proof CST1 as (HP1 & CO1 & (errv1 & _ & _ & ST1 & _ & _ & MI1 & _) & _).
  rewrite unsigned_lit in ST1 by lia.
  pose proof RNG as (A'0 & _ & _ & A'C & A'IMG).
  destruct (cstate_nodup _ _ _ _ _ _ _ _ _ CST1) as [ND1 _].
  assert (INQ : In (q, A', n') LBall1) by (left; reflexivity).
  (* [comment removed for export] *)
  assert (KEPT : forall b0, In b0 LBall -> blk_id b0 <> pb -> In b0 LBall1 /\ blk_id b0 <> q).
  { intros b0 Hb0 NE. assert (X : In b0 (lb_remove pb LBall)) by (apply lb_remove_In; auto). split; [right; exact X|].
    intros E. unfold LBall1 in ND1. cbn [map] in ND1. apply NoDup_cons_iff in ND1. destruct ND1 as [NI _].
    change (blk_id (q, A', n')) with q in NI. rewrite <- E in NI. apply NI, in_map, X. }
  assert (PLPB : pl <> pb) by (intros E; apply NoDup_cons_iff in ND; destruct ND as [NI _]; apply NI; left; symmetry; exact E).
  assert (NODEPB : forall p0 X, In (p0, X) (concat bks) -> p0 <> pb).
  { intros p0 X Hin E. apply NoDup_cons_iff in ND. destruct ND as [_ ND']. apply NoDup_cons_iff in ND'. destruct ND' as [NI2 _].
    apply NI2. apply in_map_iff. exists (p0, X). split; [exact E| exact Hin]. }
  assert (INL : In (pl, lh, 104) LBall) by exact (proj1 OL).
  destruct (KEPT (pl, lh, 104) INL PLPB) as [INL1 PLQ]. unfold blk_id in PLQ; cbn [fst] in PLQ.
  assert (APL : lh + 104 <= A' \/ A' + n' <= lh) by (eapply (own_apart st1 LBall1 m1 pl lh 104 q A' n' HP1); [exact INL1| exact INQ| exact PLQ]).
  assert (NODE1 : forall p0 X, In (p0, X) (concat bks) -> In (p0, X, 24) LBall /\ cown LBall1 L1 p0 X 24 24 /\ (X + 24 <= A' \/ A' + n' <= X) /\ (X + 24 <= lh \/ lh + 104 <= X)
                                 /\ 0 < X /\ X + 24 <= alloc_ceiling).
  { intros p0 X Hin. pose proof (lh_rep_owned _ _ _ _ _ _ _ _ _ _ _ _ REP p0 X Hin) as [O1 O2].
    destruct (KEPT (p0, X, 24) O1 (NODEPB p0 X Hin)) as [I1 NQ]. unfold blk_id in NQ; cbn [fst] in NQ.
    split; [exact O1|]. split; [split; [exact I1| apply KP1'; [exact O2| intros E; exact (NODEPB p0 X Hin (eq_sym E))]]|].
    split; [eapply (own_apart st1 LBall1 m1 p0 X 24 q A' n' HP1); [exact I1| exact INQ| exact NQ]|].
    apply in_concat in Hin. destruct Hin as (nsx & Hns & Hin). destruct (In_nth _ _ [] Hns) as (jx & Hjx & Ejx). subst nsx.
    split; [exact (proj1 (S_N jx p0 X Hjx Hin))|].
    pose proof (CH (Z.of_nat jx) ltac:(lia)) as (c0 & SS & _). rewrite Nat2Z.id in SS. exact (lseg_ranges _ _ _ _ _ _ _ SS p0 X Hin). }
  assert (NMW : exists nmb2, In (q, nmb2) L1 /\ cgrow L L1 (wA nmb2 - wA nmb) (wB nmb2 - wB nmb) (wBig nmb2 - wBig nmb) /\ nmb <= nmb2 <= 16 * na).
  { clear - ARMS OB NMB GB. destruct ARMS as [(-> & _ & ->)|(i & HN & ->)].
    - exists nmb. split; [exact (proj2 OB)|]. split; [rewrite !Z.sub_diag; apply cgrow_refl| lia].
    - exists n'. split; [left; reflexivity|]. split; [| unfold n'; lia].
      eapply cgrow_weaken; [exact (cgrow_trans _ _ _ _ _ _ _ _ _ (cgrow_remove _ _ _ _ HN) (cgrow_cons _ q n'))| lia| lia| lia]. }
  destruct NMW as (nmb2 & INQL & GR2 & NMB2).
  pose proof (cfr_cells_block _ _ _ _ _ _ _ _ (pl, lh, 104) CFR1 SCm INL (fun E => PLPB (eq_sym E))
                ltac:(unfold blk_addr; cbn [fst snd]; lia) ltac:(unfold blk_addr, blk_size; cbn [fst snd cells_size csize]; lia)) as SC1.
  destruct (rw_cells_CB_split_at usegs m1 A' (Z.to_nat n') _ (Z.to_nat (8 * na)) ltac:(unfold n'; lia) BLK) as [NEWa NEWb].
  rewrite Z2Nat.id in NEWb by lia.
  replace (Z.to_nat n' - Z.to_nat (8 * na))%nat with (Z.to_nat (8 * na)) in NEWb by (unfold n'; lia).
  (* [comment removed for export] *)
  assert (OLDC : forall (i : nat) (w : word), (i < Z.to_nat na)%nat -> rw_cells usegs m (B + 8 * Z.of_nat i) [C8 w] -> rw_cells usegs m1 (A' + 8 * Z.of_nat i) [C8 w]).
  { intros i w Hi CW0. rewrite firstn_all2 in BLK by (unfold n'; lia). exact (cells_read_back m m1 B A' _ _ src tail i w SRC CW0 Hi BLK). }
  pose proof (munch_refl [(lh, lh + 8); (lh + 60, lh + 72); (A' + 8 * na, A' + 16 * na)]%Z m1) as MU1. pose proof (wmono_refl usegs m1) as WM1.
  cprefix. step. if_cases K3; zify_cond K3. { exfalso. rewrite ?unsigned_lit in K3 by lia. lia. }
  assert (EA2 : bv_unsigned (Z_to_bv 64 na) ≪ 3 = 8 * na) by (rewrite unsigned_lit by lia; rewrite Z.shiftl_mul_pow2 by lia; lia).
  step. step. cstep. step. rewrite ?EA2. if_cases KN; zify_cond KN. { exfalso. rewrite ?unsigned_lit, ?zb_lxor_ones in KN by lia. lia. }
  do 3 step.
  rewrite ?EA2.
  calle (eapply (memset_callZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (A' + 8 * na) 0 (8 * na))); try lia.
  lazymatch goal with H : rw_cells _ _ (A' + 8 * na) [CB _ (repeat _ _)] |- _ => rename H into ZB end.
  step. step. rewrite (Printf_lib.sx32_lit (g_nn g)) by lia. cstep. cstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mf end.
  chere. apply climpl_done. unfold lhi_double_post.
  do 19 eexists. exists mf, LBall1, q, A', nmb2.
  pose proof (agree_on_of_munch _ _ _ MU1 WM1) as AG1f.
  assert (CC2 : concat (bks ++ repeat [] (Z.to_nat na)) = concat bks) by (rewrite concat_app, concat_repeat_nil, app_nil_r; reflexivity).
  (* [comment removed for export] *)
  assert (AGN : agree_on (fun a => exists p0 X, In (p0, X) (concat bks) /\ X <= a < X + 24) m mf).
  { eapply agree_on_trans; [eapply agree_on_mono; [exact CFR1|]| eapply agree_on_mono; [exact AG1f|]].
    - intros a (p0 & X & Hin & Ha). destruct (NODE1 p0 X Hin) as (O1 & _). right; left. exists (p0, X, 24). split; [exact O1|].
      split; [intros E; exact (NODEPB p0 X Hin (eq_sym E))| unfold blk_addr, blk_size; cbn [fst snd]; lia].
    - intros a (p0 & X & Hin & Ha). destruct (NODE1 p0 X Hin) as (_ & _ & N1 & N2 & _). cbn [outside]. unfold n' in N1. lia. }
  split; [reflexivity|]. split; [exact FU1|].
  split. { eapply (cstate_seg _ _ _ _ _ m1 mf _ _ tp lo Bd (bv_unsigned sp + -80)); [exact CST1| exact MU1| exact WM1| eassumption| | lia| lia|
                                                                                      | rewrite unsigned_lit by lia; eassumption| rewrite unsigned_lit by lia; lia].
    - constructor; [| constructor; [| constructor; [| constructor]]].
      + apply (cwin_block _ _ _ (pl, lh, 104)); [exact INL1| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia.
      + apply (cwin_block _ _ _ (pl, lh, 104)); [exact INL1| |]; unfold blk_addr, blk_size; cbn [fst snd]; lia.
      + apply (cwin_block _ _ _ (q, A', n')); [exact INQ| |]; unfold blk_addr, blk_size, n'; cbn [fst snd]; lia.
    - cbn [disjoint_from]. unfold LX_FLAGS. pose proof (cstate_range _ _ _ _ _ _ _ _ _ _ _ _ CST1 INL1) as (_ & _ & _ & _ & X). unfold n' in *. lia. }
  split. { assert (FRW : cframe (fun x => x = pl \/ x = pb) [] (bv_unsigned sp + -80) s LBall L m st1 LBall1 L1 m1).
    { eapply cframe_call; [apply cframe_refl| exact FRM1| lia| intros a X; exact X|]. intros xq _ NT E. apply NT. right. symmetry. exact E. }
    eapply cframe_seg; [exact FRW| exact MU1| exact WM1| exact HP1| lia|].
    constructor; [| constructor; [| constructor; [| constructor]]].
    - apply (cseg_ok_block _ _ _ _ _ (pl, lh, 104)); [exact INL1| | |]; unfold blk_addr, blk_size; cbn [fst snd]; try lia.
      intros b0 _ NT E. apply NT. left. exact E.
    - apply (cseg_ok_block _ _ _ _ _ (pl, lh, 104)); [exact INL1| | |]; unfold blk_addr, blk_size; cbn [fst snd]; try lia.
      intros b0 _ NT E. apply NT. left. exact E.
    - apply (cseg_ok_block _ _ _ _ _ (q, A', n')); [exact INQ| | |]; unfold blk_addr, blk_size, n'; cbn [fst snd]; try lia.
      intros b0 Hb0 NT E. destruct (KEPT b0 Hb0 ltac:(intros X; apply NT; right; exact X)) as [_ NQ]. apply NQ. exact E. }
  split. { unfold lh_raw.
    split; [split; [exact INL1| apply KP1'; [exact (proj2 OL)| intros E; exact (PLPB (eq_sym E))]]|].
    split; [exact RL|].
    split; [split; [replace (8 * (2 * na)) with n' by (unfold n'; lia); exact INQ| exact INQL]|].
    split; [unfold n' in *; lia|].
    split; [rewrite length_app, repeat_length; lia|].
    split.
    - intros i Hi. destruct (Z_lt_le_dec i na) as [X|X].
      + rewrite app_nth1 by lia.
        destruct (chain_chainv _ _ _ _ _ _ (CH i ltac:(lia))) as (v & CV & CHV).
        eapply (chainv_chain _ _ _ _ _ _ v).
        * pose proof (OLDC (Z.to_nat i) (wz v) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; exact CV)) as C1. rewrite Z2Nat.id in C1 by lia.
          eapply rw_cells_agree; [exact AG1f| exact C1|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. intros a Ha. cbn [outside]. unfold n' in APL. lia.
        * eapply chainv_own; [eapply chainv_agree; [exact CHV|]|].
          -- eapply agree_on_mono; [exact AGN|]. intros a (p0 & X0 & Hin & Ha). exists p0, X0. split; [eapply in_nth_concat; exact Hin| exact Ha].
          -- intros p0 X0 Hin _. destruct (NODE1 p0 X0 ltac:(eapply in_nth_concat; exact Hin)) as (_ & O & _). exact O.
      + rewrite app_nth2 by lia. rewrite nth_repeat. exists (A' + 8 * i). split; [reflexivity|].
        change (0 mod 256) with 0 in ZB. replace (Z.to_nat (8 * na)) with (8 * Z.to_nat na)%nat in ZB by lia.
        pose proof (cells_zero mf (A' + 8 * na) (Z.to_nat na) (Z.to_nat (i - na)) ZB ltac:(lia)) as C0.
        replace (A' + 8 * na + 8 * Z.of_nat (Z.to_nat (i - na))) with (A' + 8 * i) in C0 by lia. unfold wz. exact C0.
    - rewrite CC2. apply NoDup_cons_iff in ND. destruct ND as [NI1 ND']. apply NoDup_cons_iff in ND'. destruct ND' as [NI2 ND2].
      constructor; [| constructor; [| exact ND2]].
      + intros [E|X]; [exact (PLQ (eq_sym E))| apply NI1; right; exact X].
      + intros X. apply in_map_iff in X. destruct X as ([p0 X0] & E & Hin). cbn [fst] in E. subst p0.
        destruct (NODE1 q X0 Hin) as (O1 & _). destruct (KEPT (q, X0, 24) O1 (NODEPB q X0 Hin)) as [_ NQ]. apply NQ. reflexivity. }
  split. { unfold lhs_cells. eassumption. }
  split; [exact GR2|]. split; [exact NMB2|].
  intros xq QIN NE E. assert (XB : In xq (map blk_id LBall)) by (destruct QIN as [X|X]; [exact X| exact (cl_own_ids _ _ _ _ CO X)]).
  apply in_map_iff in XB. destruct XB as (b0 & E0 & Hb0). destruct (KEPT b0 Hb0 ltac:(rewrite E0; exact NE)) as [_ NQ]. apply NQ. rewrite E0. exact E.
Qed.

(* [comment removed for export] *)
Theorem lh_insert_spec : crypto_realloc_array_stmt -> crypto_malloc_stmt -> lh_insert_stmt.
Proof. intros CRA CM. exact (lh_insert_of (lhi_double_spec CRA) CM). Qed.
End WithCeiling0.
