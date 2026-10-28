(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Ubs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import InitMem. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_kit Fz_cimg Fz_I1_defs Fz_I1_hash Fz_I1_getrn Fz_I1_split Fz_I1_rep. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Definition lhs_cells (B nn na p pmax items : Z) (x40 x48 err pad : word) : list cell :=
  [C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 954500); C8 (Z_to_bv 64 954384); C8 (Z_to_bv 64 0xe90d4); C8 (Z_to_bv 64 954612); C8 x40; C8 x48;
   C4 (Z_to_bv 64 nn); C4 (Z_to_bv 64 na); C4 (Z_to_bv 64 p); C4 (Z_to_bv 64 pmax); C8 (Z_to_bv 64 512); C8 (Z_to_bv 64 256); C8 (Z_to_bv 64 items); C4 err; C4 pad].

Definition lhi_split_post (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (LBall : list block) (L : @clist bptr) (lh B nn na p' pmax items : Z) (x40 x48 err pad : word) (cp cn : Z) (nsp : list (bptr * Z)) : machine_state -> Prop :=
  fun ms' => exists (a0' a1' a2' a3' a4' a5' a6' a7' s5' : word) (m' : mem) (stay' moved' : list (bptr * Z)),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0xe9c70) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m' /\ wmono usegs m m'
    /\ rw_cells usegs m' lh (lhs_cells B (nn + 1) na p' pmax items x40 x48 err pad)
    /\ chain DVERR m' LBall L cp stay' /\ chain DVERR m' LBall L cn moved'
    /\ Permutation (stay' ++ moved') nsp
    /\ agree_on (fun a => ~ ((lh + 56 <= a < lh + 68) \/ split_W cp cn nsp a)) m m'.

Lemma lhi_split : forall (ra sp gp tp t0 t1 t2 s0 a2 a3 a4 a5 a6 a7 s2 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (LBall : list block) (L : @clist bptr) (lh B nn na p p' pmax0 pmaxf na0 items : Z) (x40 x48 err pad : word) (nsp : list (bptr * Z)) (sH : PState) (mH : mem),
  rw_cells usegs m lh (lhs_cells B nn na p pmaxf items x40 x48 err pad) ->
  chain DVERR m LBall L (B + 8 * p) nsp -> chain DVERR m LBall L (B + 8 * nn) [] ->
  nsep nsp (B + 8 * p) (B + 8 * nn) ->
  nn = pmax0 + p -> 0 <= p < pmax0 -> 8 <= pmax0 -> nn < na -> na <= 16004 -> 0 < na0 < 2^31 -> 0 <= p' < 2^31 ->
  0 < lh -> lh + 104 <= alloc_ceiling -> 0 < B -> B + 8 * na <= alloc_ceiling -> B mod 8 = 0 -> RHEAP sH LBall mH ->
  (lh + 104 <= B \/ B + 8 * na <= lh) -> Forall (fun A => A + 24 <= lh \/ lh + 104 <= A) (map snd nsp) ->
  mem_inv usegs m ->
  evt usegs (lhi_split_post ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 lh) s2 (Z_to_bv 64 p) (Z_to_bv 64 na0) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m LBall L lh B nn na p' pmaxf items x40 x48 err pad
               (B + 8 * p) (B + 8 * nn) nsp)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 lh) (Z_to_bv 64 nn) (Z_to_bv 64 p') a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 p) (Z_to_bv 64 na0) (Z_to_bv 64 pmax0)
               s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xe9d14) fc None m (seg_rom usegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until mH. intros SC CHP CHN NSEP ENN PR PM NNA NAB NA0 PR' LH0 LHC B0 BC BAL RH SLB SLN MI.
  assert (CW : alloc_ceiling < 2^63) by (unfold ceil_window in *; lia).
  unfold lhs_cells in SC.
  remember (B + 8 * p) as cp eqn:ECP. remember (B + 8 * nn) as cn eqn:ECNN.
  pose proof CHN as (cn' & ECN & TERMN). cbn [lseg] in ECN. subst cn'.
  pose proof (chain_chainv _ _ _ _ _ _ CHP) as (hp0 & CPC & CVP).
  assert (E1 : B + bv_unsigned (Z_to_bv 64 p) ≪ 3 = cp) by (rewrite unsigned_lit by lia; rewrite Z.shiftl_mul_pow2 by lia; lia).
  assert (E2 : bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (pmax0 + p)) ≪ 32)) ≫ 29 = 8 * nn).
  { rewrite (unsigned_lit (pmax0 + p)) by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite unsigned_lit by lia. rewrite Z.shiftr_div_pow2 by lia.
    replace ((pmax0 + p) * 2 ^ 32) with ((8 * nn) * 2 ^ 29) by lia. apply Z.div_mul. lia. }
  pose proof (munch_refl [(lh + 56, lh + 68); (cn, cn + 8)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  do 4 step. rewrite E1. step. step. step. if_cases KO1; zify_cond KO1. { exfalso. rewrite ?unsigned_lit in KO1 by lia. lia. } zstep. zstep. zstep. replace (0 <? B) with true by (symmetry; apply Z.ltb_lt; lia). replace (cp <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z Z.lxor Pos.lxor]. zstep. th_if_lit.
  (* [comment removed for export] *)
  do 3 step. rewrite E2. step. rewrite ?(unsigned_lit (8 * nn)) by lia. replace (B + 8 * nn) with cn by lia. step. if_cases KO2; zify_cond KO2. { exfalso. rewrite ?unsigned_lit in KO2 by lia. lia. } zstep. zstep. replace (cn <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z Z.lxor Pos.lxor]. zstep. th_if_lit. step. ubs_if. step. step. ubs_if. step. cstep. step. ubs_if. step.
  destruct NSEP as (FOP & BKC & CPN).
  assert (NODES : forall X, In X (map snd nsp) -> (X + 24 <= lh \/ lh + 104 <= X) /\ apartc X cp /\ apartc X cn).
  { intros X HX. split; [exact (proj1 (Forall_forall _ _) SLN X HX)| exact (proj1 (Forall_forall _ _) BKC X HX)]. }
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mc end.
  pose proof (agree_on_of_munch _ _ _ MU WM) as AG0.
  assert (CVPc : chainv DVERR mc LBall L hp0 nsp).
  { eapply chainv_agree; [exact CVP|]. eapply agree_on_mono; [exact AG0|]. intros a (p0 & X & HX & Ha). apply (in_map snd) in HX. cbn [snd] in HX.
    destruct (NODES X HX) as (N1 & _ & N3). unfold apartc in N3. cbn [outside]. lia. }
  assert (AGP : agree_on (fun a => ~ ((lh + 56 <= a < lh + 68) \/ split_W cp cn nsp a)) m mc).
  { eapply agree_on_mono; [exact AG0|]. intros a NW. cbn [outside]. unfold split_W in NW. split; [tauto|]. split; [tauto| exact I]. }
  destruct nsp as [|[pn A] rest].
  - (* [comment removed for export] *)
    cbn [chainv] in CVP. subst hp0.
    step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
    apply evt_done. unfold lhi_split_post, lhs_cells. do 9 eexists. exists mc, [], []. split; [reflexivity|].
    split; [eassumption|]. split; [exact WM|]. split; [eassumption|].
    split; [exists cp; split; [reflexivity| exact CPC]|]. split; [exists cn; split; [reflexivity| eassumption]|]. split; [apply Permutation_refl| exact AGP].
  - cbn [chainv] in CVPc. destruct CVPc as (-> & OWN & RG & NC & nxt & NXC & CVR).
    step. if_cases K; zify_cond K. { exfalso. unfold wz in K. rewrite ?unsigned_lit in K by lia. lia. }
    eapply evt_cut.
    { eapply (split_loop LBall L cp cn ((pn, A) :: rest) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rest [] [] cp pn A nxt 0 _ _ mc sH mH);
        try eassumption; try reflexivity; try (rewrite ?unsigned_lit by lia; lia).
      - cbn [app]. rewrite app_nil_r. apply Permutation_refl.
      - split; [exact FOP|]. split; [exact BKC| exact CPN]. }
    intros ms' (b0 & b2 & b3 & b4 & mf & stay' & moved' & -> & MIf & C1 & C2 & PMf & AGf & WMf).
    apply evt_done. unfold lhi_split_post, lhs_cells. do 9 eexists. exists mf, stay', moved'. split; [reflexivity|].
    split; [exact MIf|]. split; [eapply wmono_trans; eassumption|].
    split. { eapply rw_cells_agree; [exact AGf| eassumption|]. intros a Ha NW. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Ha.
             unfold split_W in NW. destruct NW as [NW|[NW|(p0 & X & HX & NW)]]; [lia| lia|]. apply (in_map snd) in HX. cbn [snd] in HX. destruct (NODES X HX) as (N1 & _). lia. }
    split; [exact C1|]. split; [exact C2|]. split; [exact PMf|].
    eapply agree_on_trans; [exact AGP|]. eapply agree_on_mono; [exact AGf|]. intros a NW NW2. apply NW. right. exact NW2.
Qed.
End WithCeiling0.
