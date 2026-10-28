(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Ubs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn LhPure.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import InitMem. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_kit Fz_cimg Fz_I1_defs Fz_I1_hash Fz_I1_getrn.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)







(* [comment removed for export] *)
Lemma lseg_fp_end : forall m LBall L ns c0 c', lseg DVERR m LBall L c0 ns c' ->
  ForallOrdPairs apart24 (map snd ns) -> Forall (fun A => apartc A c0) (map snd ns) ->
  forall a, lseg_fp c0 ns a -> ~ (c' <= a < c' + 8).
Proof.
  intros m LBall L ns. induction ns as [|[p1 A1] ns IH]; intros c0 c' S FO FC a Ha; cbn [lseg_fp] in Ha; [destruct Ha|].
  cbn [lseg] in S. destruct S as (_ & _ & RG & _ & R). cbn [map snd] in FO, FC. inversion FO as [|x l FA FO']; subst. inversion FC as [|x l AC0 FC']; subst.
  (* [comment removed for export] *)
  assert (LOC : c' = A1 + 8 \/ exists A, In A (map snd ns) /\ c' = A + 8).
  { clear - R. revert R. generalize (A1 + 8). induction ns as [|[q Bq] ns IHn]; intros z R; cbn [lseg] in R; [left; symmetry; exact R|].
    destruct R as (_ & _ & _ & _ & R). destruct (IHn _ R) as [E|(A & HA & E)]; right; [exists Bq; split; [left; reflexivity| exact E]| exists A; split; [right; exact HA| exact E]]. }
  unfold apartc in AC0.
  destruct Ha as [Ha|[Ha|[Ha|Ha]]].
  - destruct LOC as [->|(A & HA & ->)]; [lia|]. pose proof (proj1 (Forall_forall _ _) FC' A HA) as X. unfold apartc in X. lia.
  - destruct LOC as [->|(A & HA & ->)]; [lia|]. pose proof (proj1 (Forall_forall _ _) FA A HA) as X. unfold apart24 in X. lia.
  - destruct LOC as [->|(A & HA & ->)]; [lia|]. pose proof (proj1 (Forall_forall _ _) FA A HA) as X. unfold apart24 in X. lia.
  - apply (IH (A1 + 8) c' R FO'); [| exact Ha].
    apply Forall_forall. intros A HA. pose proof (proj1 (Forall_forall _ _) FA A HA) as X. unfold apart24, apartc in *. lia.
Qed.

(* [comment removed for export] *)
Definition split_iter_post (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (c A nxt hm cn : Z) : machine_state -> Prop :=
  fun ms' => exists (a3' a4' : word) (c' : Z) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c') (Z_to_bv 64 cn) (Z_to_bv 64 nxt) a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 (if nxt =? 0 then 0xe9c70 else 0xe9d80)) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m'
    /\ ((c' = A + 8 /\ m' = m)
        \/ (c' = c /\ munch [(c, c + 8); (A + 8, A + 16); (cn, cn + 8)]%Z m m' /\ wmono usegs m m'
            /\ rw_cells usegs m' c [C8 (Z_to_bv 64 nxt)] /\ rw_cells usegs m' (A + 8) [C8 (Z_to_bv 64 hm)] /\ rw_cells usegs m' cn [C8 (Z_to_bv 64 A)])).

Lemma split_iter : forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (c A nxt hm cn : Z) (hN : word),
  rw_cells usegs m c [C8 (Z_to_bv 64 A)] -> rw_cells usegs m (A + 8) [C8 (Z_to_bv 64 nxt)] -> rw_cells usegs m (A + 16) [C8 hN] ->
  rw_cells usegs m cn [C8 (Z_to_bv 64 hm)] ->
  0 < A -> A + 24 <= alloc_ceiling -> 0 <= nxt < 2^63 ->
  (c + 8 <= A \/ A + 24 <= c) -> (cn + 8 <= A \/ A + 24 <= cn) -> (c + 8 <= cn \/ cn + 8 <= c) ->
  A mod 8 = 0 -> c mod 8 = 0 -> bv_unsigned s4 <> 0 -> mem_inv usegs m ->
  evt usegs (split_iter_post ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m c A nxt hm cn)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) (Z_to_bv 64 cn) (Z_to_bv 64 A) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xe9d80) fc None m (seg_rom usegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until hN. intros CC NX NH CN A0 AC NXR S1 S2 S3 AAL CAL S4 MI.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
  pose proof (rw_cells_bound _ _ _ _ CC) as CB. pose proof (rw_cells_bound _ _ _ _ CN) as CNB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in CB, CNB.
  pose proof (munch_refl [(c, c + 8); (A + 8, A + 16); (cn, cn + 8)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  (* [comment removed for export] *)
  step. step. ubs_if. step. ubs_if. do 3 step. step. if_cases K.
  - (* [comment removed for export] *)
    step. ubs_if. do 7 step.
    step. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
    + apply evt_done. do 2 eexists. exists c. eexists. split; [replace (nxt =? 0) with true by (symmetry; apply Z.eqb_eq; lia); reflexivity|].
      split; [eassumption|]. right. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. auto.
    + apply evt_done. do 2 eexists. exists c. eexists. split; [replace (nxt =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity|].
      split; [eassumption|]. right. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. auto.
  - (* [comment removed for export] *)
    step. ubs_if. do 3 step.
    step. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
    + apply evt_done. do 2 eexists. exists (A + 8), m. split; [replace (nxt =? 0) with true by (symmetry; apply Z.eqb_eq; lia); reflexivity|].
      split; [exact MI|]. left. auto.
    + apply evt_done. do 2 eexists. exists (A + 8), m. split; [replace (nxt =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity|].
      split; [exact MI|]. left. auto.
Qed.

(* [comment removed for export] *)

Definition split_post (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (LBall : list block) (L : @clist bptr) (cp cn : Z) (ALL : list (bptr * Z)) : machine_state -> Prop :=
  fun ms' => exists (a0' a2' a3' a4' : word) (m' : mem) (stay' moved' : list (bptr * Z)),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' (Z_to_bv 64 cn) a2' a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0xe9c70) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m'
    /\ chain DVERR m' LBall L cp stay' /\ chain DVERR m' LBall L cn moved'
    /\ Permutation (stay' ++ moved') ALL
    /\ agree_on (fun a => ~ split_W cp cn ALL a) m m' /\ wmono usegs m m'.

Lemma split_loop : forall (LBall : list block) (L : @clist bptr) (cp cn : Z) (ALL : list (bptr * Z))
    (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (rem stay moved : list (bptr * Z)) (c : Z) (pn : bptr) (A nxt hm : Z) (a3 a4 : word) (m : mem) (sH : PState) (mH : mem),
  Permutation (stay ++ (pn, A) :: rem ++ moved) ALL -> nsep ALL cp cn ->
  lseg DVERR m LBall L cp stay c -> rw_cells usegs m c [C8 (Z_to_bv 64 A)] ->
  cown LBall L pn A 24 24 -> (0 < A /\ A + 24 <= alloc_ceiling) -> node_cells DVERR m A ->
  rw_cells usegs m (A + 8) [C8 (Z_to_bv 64 nxt)] -> chainv DVERR m LBall L nxt rem ->
  rw_cells usegs m cn [C8 (Z_to_bv 64 hm)] -> chainv DVERR m LBall L hm moved ->
  c mod 8 = 0 -> bv_unsigned s4 <> 0 -> RHEAP sH LBall mH -> mem_inv usegs m ->
  evt usegs (split_post ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m LBall L cp cn ALL)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) (Z_to_bv 64 cn) (Z_to_bv 64 A) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xe9d80) fc None m (seg_rom usegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros LBall L cp cn ALL ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc rem.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
  induction rem as [|[q Bq] rem' IH]; intros stay moved c pn A nxt hm a3 a4 m sH mH PERM NSEP LSEG CC OWN RG NC NX CVR CN CVM CAL S4 RH MI.
  all: pose proof (nsep_perm _ _ _ _ NSEP (Permutation_sym PERM)) as (FO & BK & CPN).
  all: rewrite map_app in FO, BK; cbn [map snd] in FO, BK.
  all: destruct (fop_app_inv _ _ _ FO) as (FOS & FOR & XSA); inversion FOR as [|x l FA FO2]; subst x l.
  all: apply Forall_app in BK; destruct BK as [BKS BKR]; inversion BKR as [|x l [BKA1 BKA2] BKR2]; subst x l.
  all: pose proof NC as (d & hN & N1 & DVd & N2). all: pose proof (cown_al8 _ _ _ _ _ _ _ _ RH OWN) as (AAL & _).
  (* [comment removed for export] *)
  all: assert (CLOC : c = cp \/ exists X, In X (map snd stay) /\ c = X + 8).
  1,3: (clear - LSEG; revert LSEG; generalize cp; induction stay as [|[q0 B0] stay IHs]; intros z R; cbn [lseg] in R; [left; symmetry; exact R|];
        destruct R as (_ & _ & _ & _ & R); destruct (IHs _ R) as [E|(X & HX & E)]; right; [exists B0; split; [left; reflexivity| exact E]| exists X; split; [right; exact HX| exact E]]).
  all: assert (SCA : c + 8 <= A \/ A + 24 <= c) by (unfold apartc, apart24 in *; destruct CLOC as [->|(X & HX & ->)]; [lia|]; pose proof (XSA X A HX ltac:(left; reflexivity)); lia).
  all: assert (SCN : c + 8 <= cn \/ cn + 8 <= c) by (unfold apartc in *; destruct CLOC as [->|(X & HX & ->)]; [lia|]; pose proof (proj1 (Forall_forall _ _) BKS X HX) as [_ Y]; lia).
  all: unfold apartc in BKA1, BKA2.
  (* [comment removed for export] *)
  all: assert (OUTS : forall a, lseg_fp cp stay a -> outside [(c, c + 8); (A + 8, A + 16); (cn, cn + 8)]%Z a)
         by (intros a Ha; pose proof (lseg_fp_end _ _ _ _ _ _ LSEG FOS ltac:(eapply Forall_impl; [| exact BKS]; intros ? [? _]; assumption) a Ha) as NE;
             cbn [outside]; destruct (lseg_fp_where _ _ _ Ha) as [Y|(p0 & X & HX & Y)];
             [lia| apply (in_map snd) in HX; cbn [snd] in HX; pose proof (XSA X A HX ltac:(left; reflexivity)) as Z1;
                   pose proof (proj1 (Forall_forall _ _) BKS X HX) as [_ Z2]; unfold apart24, apartc in *; lia]).
  all: lazymatch type of FA with Forall _ ?others =>
         assert (OUTN : forall X, In X others -> forall a, X <= a < X + 24 -> outside [(c, c + 8); (A + 8, A + 16); (cn, cn + 8)]%Z a)
           by (intros X HX a Ha; pose proof (proj1 (Forall_forall _ _) FA X HX) as Z1; pose proof (proj1 (Forall_forall _ _) BKR2 X HX) as [Z2 Z3];
               cbn [outside]; unfold apart24, apartc in *; destruct CLOC as [->|(Y & HY & ->)]; [lia|]; pose proof (XSA Y X HY ltac:(right; exact HX)); lia) end.
  - (* [comment removed for export] *)
    cbn [chainv] in CVR. subst nxt.
    eapply evt_cut; [eapply (split_iter ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m c A 0 hm cn hN); try eassumption; lia|].
    intros ms1 (a3' & a4' & c' & m1 & -> & MI1 & ARM). change (0 =? 0) with true. cbv iota.
    apply evt_done. destruct ARM as [[-> ->]|(-> & MU1 & WM1 & CC1 & NX1 & CN1)].
    + exists (Z_to_bv 64 (A + 8)), (Z_to_bv 64 0), a3', a4', m, (stay ++ [(pn, A)]), moved.
      split; [reflexivity|]. split; [exact MI|].
      split. { exists (A + 8). split; [| exact NX]. eapply lseg_app; [exact LSEG|]. cbn [lseg]. auto 6. }
      split; [exact (chainv_chain _ _ _ _ _ _ _ CN CVM)|].
      split; [rewrite <- app_assoc; exact PERM|]. split; [apply agree_on_refl| apply wmono_refl].
    + pose proof (agree_on_of_munch _ _ _ MU1 WM1) as AG1.
      exists (Z_to_bv 64 c), (Z_to_bv 64 0), a3', a4', m1, stay, ((pn, A) :: moved).
      split; [reflexivity|]. split; [exact MI1|].
      split. { exists c. split; [| exact CC1]. eapply lseg_agree; [exact LSEG| | intros ? ? _ X; exact X]. eapply agree_on_mono; [exact AG1| exact OUTS]. }
      split. { eapply chainv_chain; [exact CN1|]. cbn [chainv]. split; [reflexivity|]. split; [exact OWN|]. split; [exact RG|].
        split. { exists d, hN. split; [| split; [exact DVd|]]; (eapply rw_cells_transport; [eassumption| exact MU1| exact WM1|]);
                 cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
        exists hm. split; [exact NX1|]. eapply chainv_agree; [exact CVM|]. eapply agree_on_mono; [exact AG1|].
        intros a (p0 & X & HX & Ha). apply (OUTN X); [apply (in_map snd) in HX; exact HX| exact Ha]. }
      split; [exact PERM|]. split; [| exact WM1].
      eapply agree_on_mono; [exact AG1|]. intros a NW. cbn [outside]. unfold split_W in NW.
      assert (INA : In (pn, A) ALL) by (eapply Permutation_in; [exact PERM| apply in_or_app; right; left; reflexivity]).
      split; [| split; [| split; [| exact I]]]; intros Hin; apply NW.
      * destruct CLOC as [->|(X & HX & ->)]; [left; exact Hin|]. right; right.
        apply in_map_iff in HX. destruct HX as ([p0 X0] & E & HX). cbn [snd] in E. subst X0. exists p0, X. split; [| lia].
        eapply Permutation_in; [exact PERM| apply in_or_app; left; exact HX].
      * right; right. exists pn, A. split; [exact INA| lia].
      * right; left. exact Hin.
  - (* [comment removed for export] *)
    cbn [chainv] in CVR. destruct CVR as (-> & OWNq & RGq & NCq & nx2 & NXq & CVR').
    assert (INQ : In Bq (Bq :: map snd (rem' ++ moved))) by (left; reflexivity).
    pose proof (proj1 (Forall_forall _ _) FA Bq INQ) as QA. pose proof (proj1 (Forall_forall _ _) BKR2 Bq INQ) as [QCP QCN].
    assert (QC : c + 8 <= Bq \/ Bq + 24 <= c) by (unfold apartc, apart24 in *; destruct CLOC as [->|(X & HX & ->)]; [lia|]; pose proof (XSA X Bq HX ltac:(right; exact INQ)); lia).
    unfold apart24, apartc in QA, QCP, QCN.
    eapply evt_cut; [eapply (split_iter ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m c A Bq hm cn hN); try eassumption; lia|].
    intros ms1 (a3' & a4' & c' & m1 & -> & MI1 & ARM). replace (Bq =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
    destruct ARM as [[-> ->]|(-> & MU1 & WM1 & CC1 & NX1 & CN1)].
    + (* [comment removed for export] *)
      eapply (IH (stay ++ [(pn, A)]) moved (A + 8) q Bq nx2 hm a3' a4' m sH mH); try eassumption.
      * rewrite <- app_assoc. exact PERM.
      * eapply lseg_app; [exact LSEG|]. cbn [lseg]. auto 6.
      * clear - AAL. Z.div_mod_to_equations. lia.
    + (* [comment removed for export] *)
      pose proof (agree_on_of_munch _ _ _ MU1 WM1) as AG1.
      assert (AGW : agree_on (fun a => ~ split_W cp cn ALL a) m m1).
      { eapply agree_on_mono; [exact AG1|]. intros a NW. cbn [outside]. unfold split_W in NW.
        assert (INA : In (pn, A) ALL) by (eapply Permutation_in; [exact PERM| apply in_or_app; right; left; reflexivity]).
        split; [| split; [| split; [| exact I]]]; intros Hin; apply NW.
        * destruct CLOC as [->|(X & HX & ->)]; [left; exact Hin|]. right; right.
          apply in_map_iff in HX. destruct HX as ([p0 X0] & E & HX). cbn [snd] in E. subst X0. exists p0, X. split; [| lia].
          eapply Permutation_in; [exact PERM| apply in_or_app; left; exact HX].
        * right; right. exists pn, A. split; [exact INA| lia].
        * right; left. exact Hin. }
      eapply evt_mono.
      { eapply (IH stay ((pn, A) :: moved) c q Bq nx2 A a3' a4' m1 sH mH); try eassumption.
        - eapply Permutation_trans; [| exact PERM]. apply Permutation_app_head. apply Permutation_sym.
          exact (Permutation_cons_app ((q, Bq) :: rem') moved (pn, A) (Permutation_refl _)).
        - eapply lseg_agree; [exact LSEG| | intros ? ? _ X; exact X]. eapply agree_on_mono; [exact AG1| exact OUTS].
        - destruct NCq as (dq & hq & Q1 & DVq & Q2). exists dq, hq. split; [| split; [exact DVq|]]; (eapply rw_cells_transport; [eassumption| exact MU1| exact WM1|]);
            cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
        - eapply rw_cells_transport; [exact NXq| exact MU1| exact WM1|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
        - eapply chainv_agree; [exact CVR'|]. eapply agree_on_mono; [exact AG1|].
          intros a (p0 & X & HX & Ha). apply (OUTN X); [| exact Ha]. right. apply in_map_iff. exists (p0, X). split; [reflexivity| apply in_or_app; left; exact HX].
        - cbn [chainv]. split; [reflexivity|]. split; [exact OWN|]. split; [exact RG|].
          split. { exists d, hN. split; [| split; [exact DVd|]]; (eapply rw_cells_transport; [eassumption| exact MU1| exact WM1|]);
                   cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
          exists hm. split; [exact NX1|]. eapply chainv_agree; [exact CVM|]. eapply agree_on_mono; [exact AG1|].
          intros a (p0 & X & HX & Ha). apply (OUTN X); [| exact Ha]. right. apply in_map_iff. exists (p0, X). split; [reflexivity| apply in_or_app; right; exact HX]. }
      intros ms' (b0 & b2 & b3 & b4 & mf & st' & mv' & -> & MIf & C1f & C2f & PMf & AGf & WMf).
      exists b0, b2, b3, b4, mf, st', mv'. split; [reflexivity|]. split; [exact MIf|]. split; [exact C1f|]. split; [exact C2f|]. split; [exact PMf|].
      split; [eapply agree_on_trans; eassumption| eapply wmono_trans; eassumption].
Qed.
End WithCeiling0.
