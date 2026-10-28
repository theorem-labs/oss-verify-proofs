(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith List Lia Bool Permutation.
From Stdlib Require Import Uint63.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Frame.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Common Require Import PropExec FastWord FastWordSem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Common.Ax Require Import ExTrie.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxStep HxStepSound HxRunSound HxHook HxHookSound HxToolkit HxGlue HxQuery HxLearn.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgHXU Require Import HxuImage HxuHeap HxuCallInit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgHXU Require HxuRun HxuFinal.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnModel.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnHeap BnRep.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Definition ERR_CLEAR_ERROR : Z := 0xe80ac.

Definition ECE_STACK : Z := 16384.

Definition stopC (pc : w64) : bool := w_eqb pc PC_ECE_RET.

Definition call_result : icache * rres := hx_run bgusegs stopC 13 IEmpty S0C.

Definition call_end (r : icache * rres) : sstate := res_state (snd r).
Notation SC_end := (call_end call_result).

Definition final_regsC : list (rix * hval) :=
  [(X1, VP TC_RA w_zero); (X2, VP 1%uint63 (W false CSTK)); (X3, VP TC_GP w_zero); (X4, VC TPVC);
   (X8, VP TC_S0 w_zero); (X9, VP (TC_S0 + 1)%uint63 w_zero); (X18, VP (TC_S0 + 2)%uint63 w_zero); (X19, VP (TC_S0 + 3)%uint63 w_zero);
   (X20, VP (TC_S0 + 4)%uint63 w_zero); (X21, VP (TC_S0 + 5)%uint63 w_zero); (X22, VP (TC_S0 + 6)%uint63 w_zero); (X23, VP (TC_S0 + 7)%uint63 w_zero);
   (X24, VP (TC_S0 + 8)%uint63 w_zero); (X25, VP (TC_S0 + 9)%uint63 w_zero); (X26, VP (TC_S0 + 10)%uint63 w_zero); (X27, VP (TC_S0 + 11)%uint63 w_zero)].

Definition final_regs_okC (S : sstate) : bool := forallb (fun rv => HxuRun.hval_eqb (rget S (fst rv)) (snd rv)) final_regsC.

Definition ES_ZS : list Z := repeat 0 704 ++ repeat 255 64 ++ repeat 0 136.

Definition Q_esC : HxuFinal.query := HxuFinal.Q T_ES 0 904 0 (kbs_bytes ES_ZS).

Definition call_ok (r : icache * rres) : bool :=
  match snd r with
  | RStop X => w_eqb (s_pc X) PC_ECE_RET && (match s_resv X with RNone => true | _ => false end) && final_regs_okC X && HxuFinal.q_ok X Q_esC
  | _ => false
  end.

Lemma call_ok_inv (r : icache * rres) : call_ok r = true ->
  exists ic S, r = (ic, RStop S) /\ s_pc S = PC_ECE_RET /\ s_resv S = RNone /\ final_regs_okC S = true /\ HxuFinal.q_ok S Q_esC = true.
Proof.
  destruct r as [ic [S|S|c S]]; cbn [call_ok snd]; try discriminate. intros H.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  exists ic, S. split; [reflexivity|]. split; [apply w_eqb_true_iff; exact H1|].
  split; [destruct (s_resv S); [reflexivity | discriminate | discriminate]|]. auto.
Qed.

Lemma call_result_unfold : call_result = hx_run bgusegs stopC 13 IEmpty S0C.
Proof. reflexivity. Qed.

Lemma call_checked : call_ok call_result = true.
Proof. vm_compute. reflexivity. Qed.

Lemma fetch_finalC : exists ic', hx_fetch bgusegs IEmpty PC_ECE_RET = Some (DJalr X0 X1 w_zero, ic').
Proof. eexists. vm_compute. reflexivity. Qed.

Definition wr_b (k : Z) (rg : region) : bool :=
  (k <? 28) &&
  (negb (rg_wr rg)
   || match rg_abs rg with
      | Some _ => false
      | None => ((k =? 13) && (to_Z (rg_size rg) =? 904)) || ((k =? 1) && (to_Z (rg_size rg) =? 16384))
      end).

Lemma MC_checked : mem_check wr_b MC = true.
Proof. vm_compute. reflexivity. Qed.

Lemma MC_get1 : mget MC 1%uint63 = Some cg_1.
Proof. vm_compute. reflexivity. Qed.

Local Ltac closed_side := first [ vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity | vm_compute; discriminate ].

Lemma cells_bytes_at (m : word -> option byte) (A : Z) (cs : list Cells.cell) : ro_cells bgusegs m A cs -> bytes_at bgusegs m A (cells_bytes cs).
Proof. intros [_ H]. exact H. Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma block_region_ok (rho : valuation) (t : int) (rg : region) (m : word -> option byte) (s : PState) (L : list block)
    (p : bptr) (A n : Z) (fs : list fact) :
  RHEAP s L m -> In (p, A, n) L -> rg_abs rg = None -> rho t = A -> to_Z (rg_size rg) = n -> to_Z (rg_al rg) = 4 ->
  n <= 8 * 2 ^ Z.of_nat (rg_d rg) -> Z.of_nat (rg_d rg) <= 59 ->
  Forall (fact_holds bgusegs rho m A) fs -> learn_check bgusegs rg fs 0 (Z.to_nat n) = true ->
  region_ok bgusegs rho t rg m.
Proof.
  intros HEAP Hin Ea Er Es Eal Hd1 Hd2 Hfs Hck.
  destruct (LH_block_range s L m (p, A, n) HEAP Hin) as (R1 & R2 & R3 & R4 & R5). cbn [blk_addr blk_size fst snd] in R1, R2, R3, R4, R5.
  assert (Eb : rbase rho t rg = A) by (unfold rbase; rewrite Ea; exact Er).
  apply (region_ok_learn bgusegs rho t rg m fs); rewrite ?Eb, ?Es, ?Eal; try assumption; try (unfold two63; lia).
  - intros i Hi. exact (proj2 (RHEAP_block_mapped s L m (p, A, n) HEAP Hin i Hi)).
  - intros _ i Hi. exact (proj1 (RHEAP_block_mapped s L m (p, A, n) HEAP Hin i Hi)).
Qed.

Section Handoff.
Variables (rho : valuation) (m : word -> option byte).
Variables (s : PState) (L OW : list block) (EA : err_addrs).
Hypothesis HEAP : RHEAP s L m.
Hypothesis INCL : forall b, In b OW -> In b L.
Hypothesis CS : crypto_statics m.
Hypothesis EI : err_inv m OW EA.
Hypothesis Hr10 : rho T_MK = ea_MK EA.
Hypothesis Hr11 : rho T_SA = ea_SA EA.
Hypothesis Hr12 : rho T_ND = ea_ND EA.
Hypothesis Hr13 : rho T_ES = ea_ES EA.

Local Ltac static_cells t rg G cs ks :=
  apply (static_region_ok bgusegs rho t rg m _ ks (cells_bytes cs) eq_refl eq_refl);
  [ closed_side
  | cbn [cells_bytes cbytes]; rewrite app_nil_r; repeat (apply Forall2_app); apply kbs_Z_intro; lia
  | exact (cells_bytes_at m _ _ G) | closed_side | closed_side ].

Lemma cg2_ok : region_ok bgusegs rho 2%uint63 cg_2 m.
Proof.
  destruct CS as (_ & G & _). unfold CR_GOT_FREE, CRYPTO_FREE in G.
  static_cells 2%uint63 cg_2 G [C8 (wz 0xe94dc)] (kbs_Z 8 0xe94dc).
Qed.

Lemma cg3_ok : region_ok bgusegs rho 3%uint63 cg_3 m.
Proof.
  destruct CS as (_ & _ & _ & _ & G & _). unfold CR_FREE_IMPL, CRYPTO_FREE in G.
  static_cells 3%uint63 cg_3 G [C8 (wz 0xe94dc)] (kbs_Z 8 0xe94dc).
Qed.

Lemma cg4_ok : region_ok bgusegs rho 4%uint63 cg_4 m.
Proof.
  destruct EI as [(_ & _ & _ & G & _) _]. unfold TL_MASTER_ONCE in G.
  static_cells 4%uint63 cg_4 G [C4 (wz 2); C4 (wz 2)] (kbs_Z 4 2 ++ kbs_Z 4 2).
Qed.

Lemma cg5_ok : region_ok bgusegs rho 5%uint63 cg_5 m.
Proof.
  destruct EI as [(G & _) _]. unfold OI_STOPPED in G.
  static_cells 5%uint63 cg_5 G [C1 (Z_to_bv 8 0)] (kbs_Z 1 0).
Qed.

Lemma cg6_ok : region_ok bgusegs rho 6%uint63 cg_6 m.
Proof.
  destruct EI as [(_ & _ & G & _) _]. unfold OI_BASE_ONCE in G.
  static_cells 6%uint63 cg_6 G [C4 (wz 2); C4 (wz 1)] (kbs_Z 4 2 ++ kbs_Z 4 1).
Qed.

Lemma cg7_ok : region_ok bgusegs rho 7%uint63 cg_7 m.
Proof.
  destruct EI as [(_ & G & _) _]. unfold OI_OPTSDONE in G.
  static_cells 7%uint63 cg_7 G [C8 (wz 2)] (kbs_Z 8 2).
Qed.

Lemma cg8_ok : region_ok bgusegs rho 8%uint63 cg_8 m.
Proof.
  destruct EI as [(_ & _ & _ & _ & G) _]. unfold TCB_TSD, TSD_MAIN in G.
  static_cells 8%uint63 cg_8 G [C8 (wz 0x352300)] (kbs_Z 8 0x352300).
Qed.

Lemma err_blocks :
  In (ea_pk EA, ea_MK EA, 72) L /\ In (ea_ps EA, ea_SA EA, 32) L /\ In (ea_pn EA, ea_ND EA, 128) L /\ In (ea_pe EA, ea_ES EA, 904) L.
Proof. destruct EI as [_ (B1 & B2 & B3 & B4 & _)]. repeat split; apply INCL; assumption. Qed.

Lemma blocks_apart (p p' : bptr) (A n A' n' : Z) : In (p, A, n) L -> In (p', A', n') L -> n <> n' -> A + n <= A' \/ A' + n' <= A.
Proof.
  intros H1 H2 Hne. apply (LH_disjoint s L m (p, A, n) (p', A', n') HEAP H1 H2). cbn [blk_id fst]. intros ->.
  destruct (RH_addr_unique L p' A n A' n' (LH_nodup s L m HEAP) H1 H2) as [_ E]. exact (Hne E).
Qed.

Lemma block_bounds (p : bptr) (A n : Z) : In (p, A, n) L -> 0 < A /\ A + n <= alloc_ceiling /\ (A + n <= 0x10000 \/ 0x353000 <= A).
Proof.
  intros H. destruct (LH_block_range s L m (p, A, n) HEAP H) as (R1 & _ & _ & R4 & R5). cbn [blk_addr blk_size fst snd] in R1, R4, R5. auto.
Qed.

Lemma cg9_ok : region_ok bgusegs rho 9%uint63 cg_9 m.
Proof.
  destruct err_blocks as (B1 & _). destruct (block_bounds _ _ _ B1) as (P1 & P2 & _).
  destruct EI as [_ (_ & _ & _ & _ & G & _)]. unfold TSD_MAIN in G. change (0x352300 + 16) with 0x352310 in G.
  apply (static_region_ok bgusegs rho 9%uint63 cg_9 m _ (kbs_ptr T_MK) (le8 (Z_to_bv 64 (ea_MK EA))) eq_refl eq_refl);
    [closed_side | apply kbs_ptr_intro; [exact Hr10 | lia] | | rewrite length_le8; reflexivity | closed_side].
  pose proof (cells_bytes_at m _ _ G) as X. cbn [cells_bytes cbytes] in X. rewrite app_nil_r in X. exact X.
Qed.

Lemma cg10_ok : region_ok bgusegs rho T_MK cg_10 m.
Proof.
  destruct err_blocks as (B1 & B2 & _). destruct (block_bounds _ _ _ B2) as (P1 & P2 & _).
  destruct EI as [_ (_ & _ & _ & _ & _ & G & _)].
  apply (block_region_ok rho T_MK cg_10 m s L (ea_pk EA) (ea_MK EA) 72 [(24, kbs_ptr T_SA)] HEAP B1 eq_refl Hr10 eq_refl eq_refl);
    [closed_side | closed_side | | closed_side].
  constructor; [|constructor]. exists (le8 (Z_to_bv 64 (ea_SA EA))). cbn [fst snd]. split; [apply kbs_ptr_intro; [exact Hr11 | lia]|].
  pose proof (cells_bytes_at m _ _ G) as X. cbn [cells_bytes cbytes] in X. rewrite app_nil_r in X. exact X.
Qed.

Lemma cg11_ok : region_ok bgusegs rho T_SA cg_11 m.
Proof.
  destruct err_blocks as (_ & B2 & B3 & _). destruct (block_bounds _ _ _ B3) as (P1 & P2 & _).
  destruct EI as [_ (_ & _ & _ & _ & _ & _ & (pad & G) & _)].
  apply (block_region_ok rho T_SA cg_11 m s L (ea_ps EA) (ea_SA EA) 32
           [(0, kbs_Z 4 1 ++ kbs_any 4 ++ kbs_Z 8 0 ++ kbs_Z 8 1 ++ kbs_ptr T_ND)] HEAP B2 eq_refl Hr11 eq_refl eq_refl);
    [closed_side | closed_side | | closed_side].
  constructor; [|constructor]. pose proof G as [(_ & Hpad & _) _]. cbn [cell_wf] in Hpad.
  exists (cells_bytes [C4 (wz 1); CB 4 pad; C8 (wz 0); C8 (wz 1); C8 (wz (ea_ND EA))]). cbn [fst snd]. rewrite Z.add_0_r.
  split; [|exact (cells_bytes_at m _ _ G)]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
  apply Forall2_app; [exact (kbs_Z_intro rho 4 1 ltac:(lia))|].
  apply Forall2_app; [rewrite <- Hpad; apply kbs_any_intro|].
  apply Forall2_app; [exact (kbs_Z_intro rho 8 0 ltac:(lia))|].
  apply Forall2_app; [exact (kbs_Z_intro rho 8 1 ltac:(lia))|].
  apply kbs_ptr_intro; [exact Hr12 | lia].
Qed.

Lemma cg12_ok : region_ok bgusegs rho T_ND cg_12 m.
Proof.
  destruct err_blocks as (_ & _ & B3 & B4). destruct (block_bounds _ _ _ B4) as (P1 & P2 & _).
  destruct EI as [_ (_ & _ & _ & _ & _ & _ & _ & G & _)].
  apply (block_region_ok rho T_ND cg_12 m s L (ea_pn EA) (ea_ND EA) 128 [(0, kbs_ptr T_ES)] HEAP B3 eq_refl Hr12 eq_refl eq_refl);
    [closed_side | closed_side | | closed_side].
  constructor; [|constructor]. exists (le8 (Z_to_bv 64 (ea_ES EA))). cbn [fst snd]. rewrite Z.add_0_r. split; [apply kbs_ptr_intro; [exact Hr13 | lia]|].
  pose proof (cells_bytes_at m _ _ G) as X. cbn [cells_bytes cbytes] in X. rewrite app_nil_r in X. exact X.
Qed.

Lemma ES_ZS_range : Forall (fun z => 0 <= z < 256) ES_ZS.
Proof. unfold ES_ZS. repeat (apply Forall_app; split); apply Forall_forall; intros z Hz; apply repeat_spec in Hz; subst z; lia. Qed.

Lemma cg13_ok : region_ok bgusegs rho T_ES cg_13 m.
Proof.
  destruct err_blocks as (_ & _ & _ & B4).
  destruct EI as [_ (_ & _ & _ & _ & _ & _ & _ & _ & G)].
  apply (block_region_ok rho T_ES cg_13 m s L (ea_pe EA) (ea_ES EA) 904 [(0, kbs_bytes ES_ZS)] HEAP B4 eq_refl Hr13 eq_refl eq_refl);
    [closed_side | closed_side | | closed_side].
  constructor; [|constructor]. exists (map (Z_to_bv 8) ES_ZS). cbn [fst snd]. rewrite Z.add_0_r. split; [exact (kbs_bytes_intro rho ES_ZS ES_ZS_range)|].
  pose proof (cells_bytes_at m _ _ (proj1 G)) as X. cbn [cells_bytes cbytes] in X. rewrite app_nil_r in X. exact X.
Qed.

Variables (lo sp0 : Z).
Hypothesis STKH : stk bgusegs m lo sp0.
Hypothesis Hrho1 : rho 1%uint63 = sp0 - ECE_STACK.
Hypothesis Hlo : lo <= sp0 - ECE_STACK.
Hypothesis Hlo0 : GLOBALS_TOP <= lo.
Hypothesis Hlo1 : alloc_ceiling <= lo.
Hypothesis Hsp63 : sp0 < 2 ^ 63.
Hypothesis Hsp16 : sp0 mod 16 = 0.

Lemma cg1_ok : region_ok bgusegs rho 1%uint63 cg_1 m.
Proof.
  unfold cg_1, ECE_STACK in *. unfold GLOBALS_TOP in Hlo0.
  apply region_ok_fresh; unfold rbase; cbn [rg_abs]; rewrite ?Hrho1; change (to_Z CSTK) with 16384.
  - lia.
  - unfold two63. lia.
  - lia.
  - apply Z.leb_le. reflexivity.
  - lia.
  - closed_side.
  - change (to_Z 4%uint63) with 4. change (2 ^ 4) with 16. rewrite <- (Z.mod_add _ 1024 16) by lia. replace (sp0 - 16384 + 1024 * 16) with sp0 by lia. exact Hsp16.
  - intros i Hi. destruct STKH as (_ & _ & Hs). destruct (Hs (sp0 - 16384 + i) ltac:(lia)) as [Hw Hb]. split; [exact Hb | intros _; exact Hw].
Qed.

Definition ivr (t : int) (rg : region) : Z * Z := (rbase rho t rg, rbase rho t rg + to_Z (rg_size rg)).

Local Ltac sep :=
  unfold ivr, rbase; cbn [rg_abs rg_size cg_1 cg_2 cg_3 cg_4 cg_5 cg_6 cg_7 cg_8 cg_9 cg_10 cg_11 cg_12 cg_13];
  rewrite ?Hr10, ?Hr11, ?Hr12, ?Hr13, ?Hrho1;
  repeat match goal with |- context [to_Z ?x] => is_ground x; let v := eval vm_compute in (to_Z x) in change (to_Z x) with v end;
  repeat (constructor; [cbn [fst snd]; lia|]); constructor.

Lemma rmemC : Rmem bgusegs rho MC m.
Proof.
  destruct err_blocks as (B1 & B2 & B3 & B4).
  destruct (block_bounds _ _ _ B1) as (K1 & K1' & K1''). destruct (block_bounds _ _ _ B2) as (K2 & K2' & K2'').
  destruct (block_bounds _ _ _ B3) as (K3 & K3' & K3''). destruct (block_bounds _ _ _ B4) as (K4 & K4' & K4'').
  pose proof (blocks_apart _ _ _ _ _ _ B1 B2 ltac:(lia)) as D12. pose proof (blocks_apart _ _ _ _ _ _ B1 B3 ltac:(lia)) as D13.
  pose proof (blocks_apart _ _ _ _ _ _ B1 B4 ltac:(lia)) as D14. pose proof (blocks_apart _ _ _ _ _ _ B2 B3 ltac:(lia)) as D23.
  pose proof (blocks_apart _ _ _ _ _ _ B2 B4 ltac:(lia)) as D24. pose proof (blocks_apart _ _ _ _ _ _ B3 B4 ltac:(lia)) as D34.
  unfold ECE_STACK, GLOBALS_TOP in *.
  pose proof (Rmem_empty bgusegs rho m) as R1. pose proof (dir_in_empty rho) as I1.
  assert (RI2 : Rmem bgusegs rho MC_2 m /\ dir_in rho MC_2 ([ivr 2%uint63 cg_2])).
  { unfold MC_2. apply (Rmem_add_sep bgusegs rho IEmpty 2%uint63 cg_2 m ([]) R1 I1); [vm_compute; reflexivity | vm_compute; reflexivity | exact cg2_ok | sep]. }
  destruct RI2 as [R2x I2x]. clear R1 I1.
  assert (RI3 : Rmem bgusegs rho MC_3 m /\ dir_in rho MC_3 (ivr 3%uint63 cg_3 :: [ivr 2%uint63 cg_2])).
  { unfold MC_3. apply (Rmem_add_sep bgusegs rho MC_2 3%uint63 cg_3 m ([ivr 2%uint63 cg_2]) R2x I2x); [vm_compute; reflexivity | vm_compute; reflexivity | exact cg3_ok | sep]. }
  destruct RI3 as [R3x I3x]. clear R2x I2x.
  assert (RI4 : Rmem bgusegs rho MC_4 m /\ dir_in rho MC_4 (ivr 4%uint63 cg_4 :: ivr 3%uint63 cg_3 :: [ivr 2%uint63 cg_2])).
  { unfold MC_4. apply (Rmem_add_sep bgusegs rho MC_3 4%uint63 cg_4 m (ivr 3%uint63 cg_3 :: [ivr 2%uint63 cg_2]) R3x I3x); [vm_compute; reflexivity | vm_compute; reflexivity | exact cg4_ok | sep]. }
  destruct RI4 as [R4x I4x]. clear R3x I3x.
  assert (RI5 : Rmem bgusegs rho MC_5 m /\ dir_in rho MC_5 (ivr 5%uint63 cg_5 :: ivr 4%uint63 cg_4 :: ivr 3%uint63 cg_3 :: [ivr 2%uint63 cg_2])).
  { unfold MC_5. apply (Rmem_add_sep bgusegs rho MC_4 5%uint63 cg_5 m (ivr 4%uint63 cg_4 :: ivr 3%uint63 cg_3 :: [ivr 2%uint63 cg_2]) R4x I4x); [vm_compute; reflexivity | vm_compute; reflexivity | exact cg5_ok | sep]. }
  destruct RI5 as [R5x I5x]. clear R4x I4x.
  assert (RI6 : Rmem bgusegs rho MC_6 m /\ dir_in rho MC_6 (ivr 6%uint63 cg_6 :: ivr 5%uint63 cg_5 :: ivr 4%uint63 cg_4 :: ivr 3%uint63 cg_3 :: [ivr 2%uint63 cg_2])).
  { unfold MC_6. apply (Rmem_add_sep bgusegs rho MC_5 6%uint63 cg_6 m (ivr 5%uint63 cg_5 :: ivr 4%uint63 cg_4 :: ivr 3%uint63 cg_3 :: [ivr 2%uint63 cg_2]) R5x I5x); [vm_compute; reflexivity | vm_compute; reflexivity | exact cg6_ok | sep]. }
  destruct RI6 as [R6x I6x]. clear R5x I5x.
  assert (RI7 : Rmem bgusegs rho MC_7 m /\ dir_in rho MC_7 (ivr 7%uint63 cg_7 :: ivr 6%uint63 cg_6 :: ivr 5%uint63 cg_5 :: ivr 4%uint63 cg_4 :: ivr 3%uint63 cg_3 :: [ivr 2%uint63 cg_2])).
  { unfold MC_7. apply (Rmem_add_sep bgusegs rho MC_6 7%uint63 cg_7 m (ivr 6%uint63 cg_6 :: ivr 5%uint63 cg_5 :: ivr 4%uint63 cg_4 :: ivr 3%uint63 cg_3 :: [ivr 2%uint63 cg_2]) R6x I6x); [vm_compute; reflexivity | vm_compute; reflexivity | exact cg7_ok | sep]. }
  destruct RI7 as [R7x I7x]. clear R6x I6x.
  assert (RI8 : Rmem bgusegs rho MC_8 m /\ dir_in rho MC_8 (ivr 8%uint63 cg_8 :: ivr 7%uint63 cg_7 :: ivr 6%uint63 cg_6 :: ivr 5%uint63 cg_5 :: ivr 4%uint63 cg_4 :: ivr 3%uint63 cg_3 :: [ivr 2%uint63 cg_2])).
  { unfold MC_8. apply (Rmem_add_sep bgusegs rho MC_7 8%uint63 cg_8 m (ivr 7%uint63 cg_7 :: ivr 6%uint63 cg_6 :: ivr 5%uint63 cg_5 :: ivr 4%uint63 cg_4 :: ivr 3%uint63 cg_3 :: [ivr 2%uint63 cg_2]) R7x I7x); [vm_compute; reflexivity | vm_compute; reflexivity | exact cg8_ok | sep]. }
  destruct RI8 as [R8x I8x]. clear R7x I7x.
  assert (RI9 : Rmem bgusegs rho MC_9 m /\ dir_in rho MC_9 (ivr 9%uint63 cg_9 :: ivr 8%uint63 cg_8 :: ivr 7%uint63 cg_7 :: ivr 6%uint63 cg_6 :: ivr 5%uint63 cg_5 :: ivr 4%uint63 cg_4 :: ivr 3%uint63 cg_3 :: [ivr 2%uint63 cg_2])).
  { unfold MC_9. apply (Rmem_add_sep bgusegs rho MC_8 9%uint63 cg_9 m (ivr 8%uint63 cg_8 :: ivr 7%uint63 cg_7 :: ivr 6%uint63 cg_6 :: ivr 5%uint63 cg_5 :: ivr 4%uint63 cg_4 :: ivr 3%uint63 cg_3 :: [ivr 2%uint63 cg_2]) R8x I8x); [vm_compute; reflexivity | vm_compute; reflexivity | exact cg9_ok | sep]. }
  destruct RI9 as [R9x I9x]. clear R8x I8x.
  assert (RI10 : Rmem bgusegs rho MC_10 m /\ dir_in rho MC_10 (ivr T_MK cg_10 :: ivr 9%uint63 cg_9 :: ivr 8%uint63 cg_8 :: ivr 7%uint63 cg_7 :: ivr 6%uint63 cg_6 :: ivr 5%uint63 cg_5 :: ivr 4%uint63 cg_4 :: ivr 3%uint63 cg_3 :: [ivr 2%uint63 cg_2])).
  { unfold MC_10. apply (Rmem_add_sep bgusegs rho MC_9 T_MK cg_10 m (ivr 9%uint63 cg_9 :: ivr 8%uint63 cg_8 :: ivr 7%uint63 cg_7 :: ivr 6%uint63 cg_6 :: ivr 5%uint63 cg_5 :: ivr 4%uint63 cg_4 :: ivr 3%uint63 cg_3 :: [ivr 2%uint63 cg_2]) R9x I9x); [vm_compute; reflexivity | vm_compute; reflexivity | exact cg10_ok | sep]. }
  destruct RI10 as [R10x I10x]. clear R9x I9x.
  assert (RI11 : Rmem bgusegs rho MC_11 m /\ dir_in rho MC_11 (ivr T_SA cg_11 :: ivr T_MK cg_10 :: ivr 9%uint63 cg_9 :: ivr 8%uint63 cg_8 :: ivr 7%uint63 cg_7 :: ivr 6%uint63 cg_6 :: ivr 5%uint63 cg_5 :: ivr 4%uint63 cg_4 :: ivr 3%uint63 cg_3 :: [ivr 2%uint63 cg_2])).
  { unfold MC_11. apply (Rmem_add_sep bgusegs rho MC_10 T_SA cg_11 m (ivr T_MK cg_10 :: ivr 9%uint63 cg_9 :: ivr 8%uint63 cg_8 :: ivr 7%uint63 cg_7 :: ivr 6%uint63 cg_6 :: ivr 5%uint63 cg_5 :: ivr 4%uint63 cg_4 :: ivr 3%uint63 cg_3 :: [ivr 2%uint63 cg_2]) R10x I10x); [vm_compute; reflexivity | vm_compute; reflexivity | exact cg11_ok | sep]. }
  destruct RI11 as [R11x I11x]. clear R10x I10x.
  assert (RI12 : Rmem bgusegs rho MC_12 m /\ dir_in rho MC_12 (ivr T_ND cg_12 :: ivr T_SA cg_11 :: ivr T_MK cg_10 :: ivr 9%uint63 cg_9 :: ivr 8%uint63 cg_8 :: ivr 7%uint63 cg_7 :: ivr 6%uint63 cg_6 :: ivr 5%uint63 cg_5 :: ivr 4%uint63 cg_4 :: ivr 3%uint63 cg_3 :: [ivr 2%uint63 cg_2])).
  { unfold MC_12. apply (Rmem_add_sep bgusegs rho MC_11 T_ND cg_12 m (ivr T_SA cg_11 :: ivr T_MK cg_10 :: ivr 9%uint63 cg_9 :: ivr 8%uint63 cg_8 :: ivr 7%uint63 cg_7 :: ivr 6%uint63 cg_6 :: ivr 5%uint63 cg_5 :: ivr 4%uint63 cg_4 :: ivr 3%uint63 cg_3 :: [ivr 2%uint63 cg_2]) R11x I11x); [vm_compute; reflexivity | vm_compute; reflexivity | exact cg12_ok | sep]. }
  destruct RI12 as [R12x I12x]. clear R11x I11x.
  assert (RI13 : Rmem bgusegs rho MC_13 m /\ dir_in rho MC_13 (ivr T_ES cg_13 :: ivr T_ND cg_12 :: ivr T_SA cg_11 :: ivr T_MK cg_10 :: ivr 9%uint63 cg_9 :: ivr 8%uint63 cg_8 :: ivr 7%uint63 cg_7 :: ivr 6%uint63 cg_6 :: ivr 5%uint63 cg_5 :: ivr 4%uint63 cg_4 :: ivr 3%uint63 cg_3 :: [ivr 2%uint63 cg_2])).
  { unfold MC_13. apply (Rmem_add_sep bgusegs rho MC_12 T_ES cg_13 m (ivr T_ND cg_12 :: ivr T_SA cg_11 :: ivr T_MK cg_10 :: ivr 9%uint63 cg_9 :: ivr 8%uint63 cg_8 :: ivr 7%uint63 cg_7 :: ivr 6%uint63 cg_6 :: ivr 5%uint63 cg_5 :: ivr 4%uint63 cg_4 :: ivr 3%uint63 cg_3 :: [ivr 2%uint63 cg_2]) R12x I12x); [vm_compute; reflexivity | vm_compute; reflexivity | exact cg13_ok | sep]. }
  destruct RI13 as [R13x I13x]. clear R12x I12x.
  unfold MC. apply (Rmem_add_sep bgusegs rho MC_13 1%uint63 cg_1 m (ivr T_ES cg_13 :: ivr T_ND cg_12 :: ivr T_SA cg_11 :: ivr T_MK cg_10 :: ivr 9%uint63 cg_9 :: ivr 8%uint63 cg_8 :: ivr 7%uint63 cg_7 :: ivr 6%uint63 cg_6 :: ivr 5%uint63 cg_5 :: ivr 4%uint63 cg_4 :: ivr 3%uint63 cg_3 :: [ivr 2%uint63 cg_2]) R13x I13x); [vm_compute; reflexivity | vm_compute; reflexivity | exact cg1_ok | sep].
Qed.

End Handoff.
End WithCeiling0.

Definition rho_call (sp0 MK SA ND ES : Z) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : valuation := fun t =>
  if (t =? 1)%uint63 then sp0 - ECE_STACK
  else if (t =? T_MK)%uint63 then MK else if (t =? T_SA)%uint63 then SA else if (t =? T_ND)%uint63 then ND else if (t =? T_ES)%uint63 then ES
  else if (t =? TC_RA)%uint63 then bv_unsigned ra else if (t =? TC_GP)%uint63 then bv_unsigned gp
  else if (t =? TC_S0)%uint63 then bv_unsigned s0 else if (t =? TC_S0 + 1)%uint63 then bv_unsigned s1
  else if (t =? TC_S0 + 2)%uint63 then bv_unsigned s2 else if (t =? TC_S0 + 3)%uint63 then bv_unsigned s3
  else if (t =? TC_S0 + 4)%uint63 then bv_unsigned s4 else if (t =? TC_S0 + 5)%uint63 then bv_unsigned s5
  else if (t =? TC_S0 + 6)%uint63 then bv_unsigned s6 else if (t =? TC_S0 + 7)%uint63 then bv_unsigned s7
  else if (t =? TC_S0 + 8)%uint63 then bv_unsigned s8 else if (t =? TC_S0 + 9)%uint63 then bv_unsigned s9
  else if (t =? TC_S0 + 10)%uint63 then bv_unsigned s10 else if (t =? TC_S0 + 11)%uint63 then bv_unsigned s11
  else 0.

Lemma Rregs_initC (rho : valuation) (MK SA ND ES : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (pc : word) (fc : bv 32) (rv : option word) :
  (forall t, to_Z t < to_Z NEXTC -> rho t = rho_call (bv_unsigned sp) MK SA ND ES ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t) ->
  tp = Z_to_bv 64 RMallocRep.RATP ->
  Rregs rho regsC (Core (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F pc fc rv).
Proof.
  intros Hrho -> r.
  assert (Esp : pword rho 1%uint63 (W false CSTK) = sp).
  { unfold pword. rewrite (Hrho 1%uint63) by (vm_compute; reflexivity).
    change (rho_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 1%uint63) with (bv_unsigned sp - ECE_STACK).
    change (wZ (W false CSTK)) with ECE_STACK. replace (bv_unsigned sp - ECE_STACK + ECE_STACK) with (bv_unsigned sp) by lia. apply Z_to_bv_bv_unsigned. }
  destruct (reg_cases r) as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
    subst r; try exact I; try reflexivity; try exact (eq_sym Esp);
    cbn [den]; symmetry; apply HxuMain.pword_scalar; rewrite Hrho by (vm_compute; reflexivity); reflexivity.
Qed.

Lemma final_regs_denC (rho : valuation) (S : sstate) (F : bvmap 5 word) (pc : word) (fc : bv 32) (rv : option word)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) :
  final_regs_okC S = true ->
  Rregs rho (s_regs S) (Core (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pc fc rv) ->
  x1 = pword rho TC_RA w_zero /\ x2 = pword rho 1%uint63 (W false CSTK) /\ x3 = pword rho TC_GP w_zero /\ x4 = wbv TPVC
  /\ x8 = pword rho TC_S0 w_zero /\ x9 = pword rho (TC_S0 + 1)%uint63 w_zero /\ x18 = pword rho (TC_S0 + 2)%uint63 w_zero
  /\ x19 = pword rho (TC_S0 + 3)%uint63 w_zero /\ x20 = pword rho (TC_S0 + 4)%uint63 w_zero /\ x21 = pword rho (TC_S0 + 5)%uint63 w_zero
  /\ x22 = pword rho (TC_S0 + 6)%uint63 w_zero /\ x23 = pword rho (TC_S0 + 7)%uint63 w_zero /\ x24 = pword rho (TC_S0 + 8)%uint63 w_zero
  /\ x25 = pword rho (TC_S0 + 9)%uint63 w_zero /\ x26 = pword rho (TC_S0 + 10)%uint63 w_zero /\ x27 = pword rho (TC_S0 + 11)%uint63 w_zero.
Proof.
  intros Hok HR. unfold final_regs_okC, final_regsC in Hok. cbn [forallb fst snd] in Hok.
  repeat (apply andb_prop in Hok as [?E Hok]). clear Hok.
  repeat match goal with E : HxuRun.hval_eqb (rget S ?X) ?v = true |- _ => apply HxuRun.hval_eqb_eq in E end.
  pose proof (HR (Z_to_bv 5 1)) as D1. pose proof (HR (Z_to_bv 5 2)) as D2. pose proof (HR (Z_to_bv 5 3)) as D3. pose proof (HR (Z_to_bv 5 4)) as D4.
  pose proof (HR (Z_to_bv 5 8)) as D8. pose proof (HR (Z_to_bv 5 9)) as D9. pose proof (HR (Z_to_bv 5 18)) as D18. pose proof (HR (Z_to_bv 5 19)) as D19.
  pose proof (HR (Z_to_bv 5 20)) as D20. pose proof (HR (Z_to_bv 5 21)) as D21. pose proof (HR (Z_to_bv 5 22)) as D22. pose proof (HR (Z_to_bv 5 23)) as D23.
  pose proof (HR (Z_to_bv 5 24)) as D24. pose proof (HR (Z_to_bv 5 25)) as D25. pose proof (HR (Z_to_bv 5 26)) as D26. pose proof (HR (Z_to_bv 5 27)) as D27.
  change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 1))) with (rget S X1) in D1. change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 2))) with (rget S X2) in D2.
  change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 3))) with (rget S X3) in D3. change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 4))) with (rget S X4) in D4.
  change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 8))) with (rget S X8) in D8. change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 9))) with (rget S X9) in D9.
  change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 18))) with (rget S X18) in D18. change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 19))) with (rget S X19) in D19.
  change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 20))) with (rget S X20) in D20. change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 21))) with (rget S X21) in D21.
  change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 22))) with (rget S X22) in D22. change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 23))) with (rget S X23) in D23.
  change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 24))) with (rget S X24) in D24. change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 25))) with (rget S X25) in D25.
  change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 26))) with (rget S X26) in D26. change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 27))) with (rget S X27) in D27.
  repeat match goal with E : rget S ?X = _, D : den rho (rget S ?X) _ |- _ => rewrite E in D; clear E end.
  cbn [den] in *. repeat split; assumption.
Qed.

Lemma stk_top_below (m : word -> option byte) (lo hi : Z) : mem_inv bgusegs m -> stk bgusegs m lo hi -> lo < hi -> hi <= UTOP.
Proof.
  intros MI (H0 & H1 & H) Hlt. destruct (H (hi - 1) ltac:(lia)) as [_ [b Hb]].
  pose proof (mrd_below bgusegs m _ _ MI Hb) as X. rewrite wa_unsigned in X by lia. lia.
Qed.

Section WithCeiling1. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Theorem ERR_clear_error_spec : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (s : PState) (L OW : list block) (EA : err_addrs),
  stk bgusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - ECE_STACK ->
  bv_unsigned sp mod 16 = 0 -> mem_inv bgusegs m -> tp = Z_to_bv 64 RMallocRep.RATP ->
  RHEAP s L m -> (forall b, In b OW -> In b L) ->
  crypto_statics m -> err_inv m OW EA ->
  evt bgusegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
               ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom bgusegs)
               /\ munch [(ea_ES EA, ea_ES EA + 904); (bv_unsigned sp - ECE_STACK, bv_unsigned sp)] m m'
               /\ wmono bgusegs m m' /\ mem_inv bgusegs m'
               /\ stk bgusegs m' lo (bv_unsigned sp)
               /\ rw_cells bgusegs m' (ea_ES EA) [CB 904 ES_CLEARED])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ERR_CLEAR_ERROR) fc None m (seg_rom bgusegs)).
Proof.
  intros until EA. intros Hstk Hlo1 Hlo2 Hlo3 Hsp16 Hmi Etp HEAP INCL CS EI.
  pose proof (stk_top_below m lo (bv_unsigned sp) Hmi Hstk ltac:(unfold ECE_STACK in Hlo3; lia)) as Hsp47. unfold UTOP in Hsp47.
  assert (Hsp63 : bv_unsigned sp < 2 ^ 63) by lia.
  set (rho0 := rho_call (bv_unsigned sp) (ea_MK EA) (ea_SA EA) (ea_ND EA) (ea_ES EA) ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  set (WIV := [(ea_ES EA, ea_ES EA + 904); (bv_unsigned sp - ECE_STACK, bv_unsigned sp)]).
  set (ms0 := MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 ERR_CLEAR_ERROR) fc None m (seg_rom bgusegs)).

  destruct (call_ok_inv call_result call_checked) as (icE & SE & Erun & Epc & Erv & Hregs & Hq).
  rewrite call_result_unfold in Erun.

  assert (HRn0 : Rn bgusegs rho0 S0C ms0).
  { intros rho2 Hag. cbn [S0C s_next] in Hag.
    assert (Hrho : forall t, to_Z t < to_Z NEXTC -> rho2 t = rho0 t) by exact Hag.
    unfold R, ms0. cbn [ms_svc_pending ms_pc_val ms_resv ms_mem MS S0C s_pc s_regs s_resv s_mem].
    split; [reflexivity|]. split; [reflexivity|]. split.
    { unfold core_of. cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv MS]. eapply Rregs_initC; [exact Hrho | exact Etp]. }
    split; [reflexivity|].
    eapply (rmemC rho2 m s L OW EA HEAP INCL CS EI); first [ exact Hstk | exact Hlo1 | exact Hlo2 | exact Hlo3 | exact Hsp63 | exact Hsp16
      | exact (Hrho T_MK ltac:(vm_compute; reflexivity)) | exact (Hrho T_SA ltac:(vm_compute; reflexivity))
      | exact (Hrho T_ND ltac:(vm_compute; reflexivity)) | exact (Hrho T_ES ltac:(vm_compute; reflexivity))
      | exact (Hrho 1%uint63 ltac:(vm_compute; reflexivity)) ]. }

  assert (HC0 : CInv bgusegs MC WIV m F fc S0C ms0).
  { unfold CInv, ms0. cbn [S0C s_mem ms_mem ms_fregs ms_fcsr ms_rom ms_regs MS].
    split; [apply same_dirs_refl|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact Hmi|].
    repeat (split; [reflexivity|]). do 31 eexists. reflexivity. }

  assert (W_ok : forall t rg, mget MC t = Some rg -> rg_wr rg = true -> inside WIV (rbase rho0 t rg) (to_Z (rg_size rg))).
  { intros t rg G Hw. pose proof (mem_check_ok wr_b MC MC_checked t rg G) as H. unfold wr_b in H. rewrite Hw in H. cbn [negb orb] in H.
    apply andb_prop in H as [_ H]. unfold rbase. destruct (rg_abs rg) as [a|]; [discriminate|].
    apply orb_prop in H as [H|H]; apply andb_prop in H as [E1 E2]; apply Z.eqb_eq in E1, E2; rewrite E2.
    - assert (t = T_ES) by (apply to_Z_inj; exact E1). subst t. change (rho0 T_ES) with (ea_ES EA). unfold WIV. cbn [inside]. left. lia.
    - assert (t = 1%uint63) by (apply to_Z_inj; exact E1). subst t. change (rho0 1%uint63) with (bv_unsigned sp - ECE_STACK).
      unfold WIV, ECE_STACK. cbn [inside]. right. left. lia. }
  destruct (hx_run_Rn_inv bgusegs stopC rho0 (CInv bgusegs MC WIV m F fc) (CInv_step bgusegs rho0 MC WIV m F fc W_ok) 13 IEmpty icE S0C (RStop SE) ms0
              (ic_ok_empty bgusegs) HRn0 HC0 Erun) as (_ & ms1 & Hms & HRn1 & HC1).
  cbn [res_state] in HRn1, HC1.

  pose proof (Rn_R bgusegs rho0 SE ms1 HRn1) as HR1. pose proof HR1 as (Hsvc & Hpc & HRg & Hrv & HRm).
  destruct fetch_finalC as [ic' Hfetch]. rewrite <- Epc in Hfetch.
  destruct (hx_ret_step bgusegs rho0 IEmpty ic' SE ms1 (ic_ok_empty bgusegs) HR1 Hfetch) as (ms2 & Hstep & Ems2).
  exists ms2. split; [exact (msteps_trans bgusegs _ _ _ Hms (msteps_one bgusegs _ _ Hstep))|].
  destruct HC1 as (Hd1 & MU & WM & MI1 & Hfr & Hfc & Hro & Hnf).
  rewrite Erv in Hrv. cbn [Rresv] in Hrv.
  destruct Hnf as (y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y18 & y19 & y20
                   & y21 & y22 & y23 & y24 & y25 & y26 & y27 & y28 & y29 & y30 & y31 & Eregs).
  unfold core_of in HRg, Ems2. rewrite Eregs in HRg, Ems2. rewrite Hfr, Hfc, Hro, Hrv in Ems2.
  destruct (final_regs_denC rho0 SE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hregs HRg)
    as (E1 & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27).
  rewrite (HxuMain.pword_scalar rho0 TC_RA ra) in E1 by reflexivity.
  rewrite (HxuMain.pword_scalar rho0 TC_GP gp) in E3 by reflexivity.
  rewrite (HxuMain.pword_scalar rho0 TC_S0 s0) in E8 by reflexivity.
  rewrite (HxuMain.pword_scalar rho0 (TC_S0 + 1)%uint63 s1) in E9 by reflexivity.
  rewrite (HxuMain.pword_scalar rho0 (TC_S0 + 2)%uint63 s2) in E18 by reflexivity.
  rewrite (HxuMain.pword_scalar rho0 (TC_S0 + 3)%uint63 s3) in E19 by reflexivity.
  rewrite (HxuMain.pword_scalar rho0 (TC_S0 + 4)%uint63 s4) in E20 by reflexivity.
  rewrite (HxuMain.pword_scalar rho0 (TC_S0 + 5)%uint63 s5) in E21 by reflexivity.
  rewrite (HxuMain.pword_scalar rho0 (TC_S0 + 6)%uint63 s6) in E22 by reflexivity.
  rewrite (HxuMain.pword_scalar rho0 (TC_S0 + 7)%uint63 s7) in E23 by reflexivity.
  rewrite (HxuMain.pword_scalar rho0 (TC_S0 + 8)%uint63 s8) in E24 by reflexivity.
  rewrite (HxuMain.pword_scalar rho0 (TC_S0 + 9)%uint63 s9) in E25 by reflexivity.
  rewrite (HxuMain.pword_scalar rho0 (TC_S0 + 10)%uint63 s10) in E26 by reflexivity.
  rewrite (HxuMain.pword_scalar rho0 (TC_S0 + 11)%uint63 s11) in E27 by reflexivity.
  assert (E2' : y2 = sp).
  { rewrite E2. unfold pword. change (rho0 1%uint63) with (bv_unsigned sp - ECE_STACK). change (wZ (W false CSTK)) with ECE_STACK.
    replace (bv_unsigned sp - ECE_STACK + ECE_STACK) with (bv_unsigned sp) by lia. apply Z_to_bv_bv_unsigned. }
  assert (E4' : y4 = tp) by (rewrite E4, Etp; reflexivity).
  subst y1 y2 y3 y4 y8 y9 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27.
  change (Sem.rget _ (Z_to_bv 5 1)) with ra in Ems2. rewrite E2', E4' in Ems2.

  set (m' := ms_mem ms1) in *.
  exists y5, y6, y7, y10, y11, y12, y13, y14, y15, y16, y17, y28, y29, y30, y31, m'.
  split; [exact Ems2|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI1|].
  destruct (err_blocks m L OW EA INCL EI) as (_ & _ & _ & B4).
  destruct (block_bounds m s L HEAP _ _ _ B4) as (K4 & K4' & _).
  split.
  -
    destruct Hstk as (S1 & S2 & S3). split; [exact S1|]. split; [exact S2|]. intros a Ha. destruct (S3 a Ha) as [Hwv (b & Hb)].
    split; [apply WM; exact Hwv|].
    destruct (Z_lt_le_dec a (bv_unsigned sp - ECE_STACK)) as [Lt|Ge].
    + exists b. unfold mrd in *. rewrite MU; [exact Hb|]. rewrite wa_unsigned by lia. unfold WIV, ECE_STACK in *. cbn [outside]. lia.
    + specialize (Hd1 1%uint63). rewrite MC_get1 in Hd1.
      destruct (mget (s_mem SE) 1%uint63) as [rg1|] eqn:Eg1; [|contradiction].
      pose proof (region_mapped bgusegs rho0 1%uint63 rg1 m' (proj1 HRm _ _ Eg1)) as Hmp.
      rewrite (rbase_same_dir rho0 1%uint63 cg_1 rg1 Hd1) in Hmp. destruct Hd1 as (_ & Es1 & _). rewrite Es1 in Hmp.
      unfold rbase in Hmp. cbn [rg_abs rg_size cg_1] in Hmp. change (rho0 1%uint63) with (bv_unsigned sp - ECE_STACK) in Hmp.
      change (to_Z CSTK) with ECE_STACK in Hmp.
      destruct (Hmp (a - (bv_unsigned sp - ECE_STACK)) ltac:(lia)) as [Hm' _].
      replace (bv_unsigned sp - ECE_STACK + (a - (bv_unsigned sp - ECE_STACK))) with a in Hm' by lia. exact Hm'.
  -
    pose proof (HxuFinal.q_rw_cells rho0 SE m' Q_esC [CB 904 ES_CLEARED] HRm Hq eq_refl) as X.
    change (rho0 (HxuFinal.q_tag Q_esC) + HxuFinal.q_off Q_esC) with (ea_ES EA + 0) in X. rewrite Z.add_0_r in X. apply X.
    + cbn [cells_wf cell_wf]. split; [reflexivity | exact I].
    + reflexivity.
    + intros bs H. rewrite (kbs_bytes_bytes rho0 _ bs H). reflexivity.
Qed.

End WithCeiling1.
