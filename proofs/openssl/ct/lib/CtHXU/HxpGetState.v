(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import PropExec MState Mem Cells Step Arr Frame Exec Image.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prog ApState ApOwner.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Common Require Import PropExec FastWord FastWordSem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Common.Ax Require Import ExTrie.
From OssFuzzTheorems.Proofs.openssl.ct.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxStep HxStepSound HxRunSound HxHook HxHookSound HxToolkit HxGlue HxQuery HxLearn HxImg.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpImage HxpHeap HxpFacts HxpGsInit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require HxpRun HxpMain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
Definition OSSL_ERR_GET_STATE_INT : Z := 0xe8a88.
(* [comment removed for export] *)
Definition GET_STATE_STACK : Z := 1024.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition stopG (pc : w64) : bool := w_eqb pc PC_GS_RET.

Definition gs_result (v od : int) : icache * rres := hx_run ctusegs stopG 13 IEmpty (S0G v od).

(* [comment removed for export] *)
Definition final_regsG : list (rix * hval) :=
  [(X1, VP TC_RA w_zero); (X2, VP T_GSTK (W false GSTK)); (X3, VP TC_GP w_zero); (X4, VC TPVG); (X10, VP T_ES w_zero);
   (X8, VP TC_S0 w_zero); (X9, VP (TC_S0 + 1)%uint63 w_zero); (X18, VP (TC_S0 + 2)%uint63 w_zero); (X19, VP (TC_S0 + 3)%uint63 w_zero);
   (X20, VP (TC_S0 + 4)%uint63 w_zero); (X21, VP (TC_S0 + 5)%uint63 w_zero); (X22, VP (TC_S0 + 6)%uint63 w_zero); (X23, VP (TC_S0 + 7)%uint63 w_zero);
   (X24, VP (TC_S0 + 8)%uint63 w_zero); (X25, VP (TC_S0 + 9)%uint63 w_zero); (X26, VP (TC_S0 + 10)%uint63 w_zero); (X27, VP (TC_S0 + 11)%uint63 w_zero)].

Definition final_regs_okG (S : sstate) : bool := forallb (fun rv => HxpRun.hval_eqb (rget S (fst rv)) (snd rv)) final_regsG.

(* [comment removed for export] *)
Definition errno_okG (S : sstate) : bool :=
  match mget (s_mem S) T_ERRNO with
  | Some rg => match rg_abs rg with Some a => (a =? A_ERRNO)%uint63 && (rg_size rg =? 4)%uint63 && rg_wr rg | None => false end
  | None => false
  end.

Definition gs_ok (r : icache * rres) : bool :=
  match snd r with
  | RStop X => w_eqb (s_pc X) PC_GS_RET && (match s_resv X with RNone => true | _ => false end) && final_regs_okG X && errno_okG X
  | _ => false
  end.

Lemma gs_ok_inv (r : icache * rres) : gs_ok r = true ->
  exists ic S, r = (ic, RStop S) /\ s_pc S = PC_GS_RET /\ s_resv S = RNone /\ final_regs_okG S = true /\ errno_okG S = true.
Proof.
  destruct r as [ic [S|S|c S]]; cbn [gs_ok snd]; try discriminate. intros H.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  exists ic, S. split; [reflexivity|]. split; [apply w_eqb_true_iff; exact H1|].
  split; [destruct (s_resv S); [reflexivity | discriminate | discriminate]|]. auto.
Qed.

(* [comment removed for export] *)
Lemma gs_checked_0_2 : gs_ok (gs_result 0 2) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gs_checked_1_2 : gs_ok (gs_result 1 2) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gs_checked_0_42 : gs_ok (gs_result 0 0x42) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gs_checked_1_42 : gs_ok (gs_result 1 0x42) = true. Proof. vm_compute. reflexivity. Qed.

Lemma gs_checked (v od : int) : (v = 0%uint63 \/ v = 1%uint63) -> (od = 2%uint63 \/ od = 0x42%uint63) -> gs_ok (gs_result v od) = true.
Proof. intros [-> | ->] [-> | ->]; [exact gs_checked_0_2 | exact gs_checked_0_42 | exact gs_checked_1_2 | exact gs_checked_1_42]. Qed.

(* [comment removed for export] *)
Lemma fetch_finalG : exists ic', hx_fetch ctusegs IEmpty PC_GS_RET = Some (DJalr X0 X1 w_zero, ic').
Proof. eexists. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition wr_bG (k : Z) (rg : region) : bool :=
  (k <? 29) &&
  (negb (rg_wr rg)
   || match rg_abs rg with
      | Some a => (k =? 2) && (a =? A_ERRNO)%uint63 && (to_Z (rg_size rg) =? 4)
      | None => (k =? 1) && (to_Z (rg_size rg) =? 1024)
      end).

Lemma MG_checked (od : int) : od = 2%uint63 \/ od = 0x42%uint63 -> mem_check wr_bG (MG od) = true.
Proof. intros [-> | ->]; vm_compute; reflexivity. Qed.

Lemma MG_get1 (od : int) : od = 2%uint63 \/ od = 0x42%uint63 -> mget (MG od) T_GSTK = Some gg_1.
Proof. intros [-> | ->]; vm_compute; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac closed_side := first [ vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity | vm_compute; discriminate ].

Lemma cells_bytes_at (m : word -> option byte) (A : Z) (cs : list Cells.cell) : ro_cells ctusegs m A cs -> bytes_at ctusegs m A (cells_bytes cs).
Proof. intros [_ H]. exact H. Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Lemma block_region_ok (rho : valuation) (t : int) (rg : region) (m : word -> option byte) (s : PState) (L : list block)
    (p : bptr) (A n : Z) (fs : list fact) :
  RHEAP s L m -> In (p, A, n) L -> rg_abs rg = None -> rho t = A -> to_Z (rg_size rg) = n -> to_Z (rg_al rg) = 4 ->
  n <= 8 * 2 ^ Z.of_nat (rg_d rg) -> Z.of_nat (rg_d rg) <= 59 ->
  Forall (fact_holds ctusegs rho m A) fs -> learn_check ctusegs rg fs 0 (Z.to_nat n) = true ->
  region_ok ctusegs rho t rg m.
Proof.
  intros HEAP Hin Ea Er Es Eal Hd1 Hd2 Hfs Hck. ceil_bounds.
  destruct (LH_block_range s L m (p, A, n) HEAP Hin) as (R1 & R2 & R3 & R4 & R5). cbn [blk_addr blk_size fst snd] in R1, R2, R3, R4, R5.
  assert (Eb : rbase rho t rg = A) by (unfold rbase; rewrite Ea; exact Er).
  apply (region_ok_learn ctusegs rho t rg m fs); rewrite ?Eb, ?Es, ?Eal; try assumption; try (unfold two63; lia).
  - intros i Hi. exact (proj2 (RHEAP_block_mapped s L m (p, A, n) HEAP Hin i Hi)).
  - intros _ i Hi. exact (proj1 (RHEAP_block_mapped s L m (p, A, n) HEAP Hin i Hi)).
Qed.

Section Handoff.
Variables (rho : valuation) (m : word -> option byte).
Variables (s : PState) (L OW : list block) (E : ap_env) (st : ap_st bptr) (bo : Z * Z) (od : int) (errv : word).
Hypothesis HEAP : RHEAP s L m.
Hypothesis INCL : forall b, In b OW -> In b L.
Hypothesis AS : ap_state st m OW E bo.
Hypothesis ERRNO : rw_cells ctusegs m LX_ERRNO [C4 errv].
Hypothesis Hod : rw_cells ctusegs m OI_OPTSDONE [C8 (wz (to_Z od))] /\ (od = 2%uint63 \/ od = 0x42%uint63).
Hypothesis Hr11 : rho T_MK = e_mk E.
Hypothesis Hr12 : rho T_SA = e_sa E.
Hypothesis Hr13 : rho T_ND = e_nd E.
Hypothesis Hr14 : rho T_ES = e_es E.

Lemma AS_fixed : ap_statics_fixed m E. Proof. destruct AS as (_ & _ & H & _). exact H. Qed.
Lemma AS_chain : tl_chain m E. Proof. destruct AS as (_ & _ & _ & _ & H & _). exact H. Qed.
Lemma AS_env : ap_env_ok E OW. Proof. destruct AS as (H & _). exact H. Qed.

(* [comment removed for export] *)
Local Ltac static_cells t rg G cs ks :=
  apply (static_region_ok ctusegs rho t rg m _ ks (cells_bytes cs) eq_refl eq_refl);
  [ closed_side
  | cbn [cells_bytes cbytes]; rewrite app_nil_r; repeat (apply Forall2_app); apply kbs_Z_intro; lia
  | exact (cells_bytes_at m _ _ G) | closed_side | closed_side ].

Lemma gg3_ok : region_ok ctusegs rho T_STOPPED gg_3 m.
Proof.
  destruct AS_fixed as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G & _). unfold OI_STOPPED in G.
  static_cells T_STOPPED gg_3 G [C1 (Z_to_bv 8 0)] (kbs_Z 1 0).
Qed.

Lemma gg4_ok : region_ok ctusegs rho T_BASEONCE gg_4 m.
Proof.
  destruct AS_fixed as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G & _). unfold OI_BASE_ONCE in G.
  static_cells T_BASEONCE gg_4 G [C4 (wz 2); C4 (wz 1)] (kbs_Z 4 2 ++ kbs_Z 4 1).
Qed.

Lemma gg5_ok : region_ok ctusegs rho T_OPTSDONE (gg_5 od) m.
Proof.
  destruct Hod as [[G _] Hod2]. unfold OI_OPTSDONE in G.
  assert (Eod : wZ (W false od) = to_Z od) by reflexivity.
  apply (static_region_ok ctusegs rho T_OPTSDONE (gg_5 od) m _ (kbs_Z 8 (to_Z od)) (cells_bytes [C8 (wz (to_Z od))]) eq_refl eq_refl);
  [ destruct Hod2 as [-> | ->]; closed_side
  | cbn [cells_bytes cbytes]; rewrite app_nil_r; unfold le8, word_to_le_bytes, wz;
    rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2 ^ 64); pose proof (to_Z_bounded od) as Bod; rewrite wB_eq in Bod; unfold two63 in Bod; lia);
    apply kbs_Z_intro; pose proof (to_Z_bounded od) as Bod; lia
  | exact (cells_bytes_at m _ _ G) | destruct Hod2 as [-> | ->]; closed_side | destruct Hod2 as [-> | ->]; closed_side ].
Qed.

Lemma gg6_ok : region_ok ctusegs rho T_MONCE gg_6 m.
Proof.
  destruct AS_fixed as (_ & _ & _ & G & _). unfold TL_MASTER_ONCE8 in G.
  static_cells T_MONCE gg_6 G [C4 (wz 1); C4 (wz 2)] (kbs_Z 4 1 ++ kbs_Z 4 2).
Qed.

Lemma gg7_ok : region_ok ctusegs rho T_MKEY gg_7 m.
Proof.
  destruct AS_fixed as (_ & _ & _ & _ & G & _). unfold TL_MASTER_KEY8, K_MASTER_KEY in G.
  static_cells T_MKEY gg_7 G [C4 (wz 2)] (kbs_Z 4 2).   (* [comment removed for export] *)
Qed.

Lemma gg8_ok : region_ok ctusegs rho T_OLOCK gg_8 m.
Proof.
  destruct AS_fixed as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [lk G] & _). unfold AP_OPTSDONE_LOCK in G.
  pose proof (cells_bytes_at m _ _ G) as Hb. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  apply region_ok_fresh; unfold rbase; cbn [rg_abs rg_size rg_al gg_8 A_OLOCK];
    repeat match goal with |- context [to_Z ?x] => is_ground x; let v := eval vm_compute in (to_Z x) in change (to_Z x) with v end;
    try (unfold two63; lia); try reflexivity; try (cbn; lia).
  intros i Hi. split; [|intros X; discriminate X].
    destruct (nth_error (le8 lk) (Z.to_nat i)) as [b|] eqn:En; [|apply nth_error_None in En; rewrite length_le8 in En; lia].
    exists b. rewrite <- En, <- (proj2 (proj2 Hb) (Z.to_nat i)) by (rewrite length_le8; lia). rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma gg9_ok : region_ok ctusegs rho T_TCBTSD gg_9 m.
Proof.
  destruct AS_fixed as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G & _). unfold TCB_TSD, TSD_MAIN in G.
  static_cells T_TCBTSD gg_9 G [C8 (wz 0x354590)] (kbs_Z 8 0x354590).
Qed.

(* [comment removed for export] *)
Lemma env_blocks_in :
  In (p_mk E, e_mk E, 72) L /\ In (p_sa E, e_sa E, 32) L /\ In (p_nd E, e_nd E, 128) L /\ In (p_es E, e_es E, 904) L.
Proof.
  destruct AS_env as (H & _). unfold env_blocks in H.
  pose proof (proj1 (Forall_forall _ _) H) as X. unfold BIO_SIZE, ES_SIZE, MUTEX_SIZE in X.
  repeat split; apply INCL; apply X; cbn [In]; tauto.
Qed.

Lemma block_bounds (p : bptr) (A n : Z) : In (p, A, n) L -> 0 < A /\ A + n <= alloc_ceiling /\ (A + n <= 0x10000 \/ 0x355000 <= A).
Proof.
  intros H. ceil_bounds. destruct (LH_block_range s L m (p, A, n) HEAP H) as (R1 & _ & _ & R4 & R5). cbn [blk_addr blk_size fst snd] in R1, R4, R5. auto.
Qed.

Lemma gg10_ok : region_ok ctusegs rho T_TSD3 gg_10 m.
Proof.
  ceil_bounds. destruct env_blocks_in as (B1 & _). destruct (block_bounds _ _ _ B1) as (P1 & P2 & _).
  destruct AS_fixed as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G & _). unfold TSD_MK_SLOT in G.
  apply (static_region_ok ctusegs rho T_TSD3 gg_10 m _ (kbs_ptr T_MK) (le8 (Z_to_bv 64 (e_mk E))) eq_refl eq_refl);
    [closed_side | apply kbs_ptr_intro; [exact Hr11 | lia] | | rewrite length_le8; reflexivity | closed_side].
  pose proof (cells_bytes_at m _ _ G) as X. cbn [cells_bytes cbytes] in X. rewrite app_nil_r in X. exact X.
Qed.

Lemma gg11_ok : region_ok ctusegs rho T_MK gg_11 m.
Proof.
  ceil_bounds. destruct env_blocks_in as (B1 & B2 & _). destruct (block_bounds _ _ _ B2) as (P1 & P2 & _).
  destruct AS_chain as (G & _ & _). unfold OFF_MK_SA in G.
  apply (block_region_ok rho T_MK gg_11 m s L (p_mk E) (e_mk E) 72 [(24, kbs_ptr T_SA)] HEAP B1 eq_refl Hr11 eq_refl eq_refl);
    [closed_side | closed_side | | closed_side].
  constructor; [|constructor]. exists (le8 (Z_to_bv 64 (e_sa E))). cbn [fst snd]. split; [apply kbs_ptr_intro; [exact Hr12 | lia]|].
  pose proof (cells_bytes_at m _ _ G) as X. cbn [cells_bytes cbytes] in X. rewrite app_nil_r in X. exact X.
Qed.

Lemma gg12_ok : region_ok ctusegs rho T_SA gg_12 m.
Proof.
  ceil_bounds. destruct env_blocks_in as (_ & B2 & B3 & _). destruct (block_bounds _ _ _ B3) as (P1 & P2 & _).
  destruct AS_chain as (_ & (pad & G) & _).
  apply (block_region_ok rho T_SA gg_12 m s L (p_sa E) (e_sa E) 32
           [(0, kbs_Z 4 1 ++ kbs_any 4 ++ kbs_Z 8 0 ++ kbs_Z 8 1 ++ kbs_ptr T_ND)] HEAP B2 eq_refl Hr12 eq_refl eq_refl);
    [closed_side | closed_side | | closed_side].
  constructor; [|constructor]. pose proof G as [(_ & Hpad & _) _]. cbn [cell_wf] in Hpad.
  exists (cells_bytes [C4 (wz 1); CB 4 pad; C8 (wz 0); C8 (wz 1); C8 (wz (e_nd E))]). cbn [fst snd]. rewrite Z.add_0_r.
  split; [|exact (cells_bytes_at m _ _ G)]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
  apply Forall2_app; [exact (kbs_Z_intro rho 4 1 ltac:(lia))|].
  apply Forall2_app; [rewrite <- Hpad; apply kbs_any_intro|].
  apply Forall2_app; [exact (kbs_Z_intro rho 8 0 ltac:(lia))|].
  apply Forall2_app; [exact (kbs_Z_intro rho 8 1 ltac:(lia))|].
  apply kbs_ptr_intro; [exact Hr13 | lia].
Qed.

Lemma gg13_ok : region_ok ctusegs rho T_ND gg_13 m.
Proof.
  ceil_bounds. destruct env_blocks_in as (_ & _ & B3 & B4). destruct (block_bounds _ _ _ B4) as (P1 & P2 & _).
  destruct AS_chain as (_ & _ & G).
  apply (block_region_ok rho T_ND gg_13 m s L (p_nd E) (e_nd E) 128 [(0, kbs_ptr T_ES)] HEAP B3 eq_refl Hr13 eq_refl eq_refl);
    [closed_side | closed_side | | closed_side].
  constructor; [|constructor]. exists (le8 (Z_to_bv 64 (e_es E))). cbn [fst snd]. rewrite Z.add_0_r. split; [apply kbs_ptr_intro; [exact Hr14 | lia]|].
  pose proof (cells_bytes_at m _ _ G) as X. cbn [cells_bytes cbytes] in X. rewrite app_nil_r in X. exact X.
Qed.

Lemma gg14_ok : region_ok ctusegs rho T_ES gg_14 m.
Proof.
  ceil_bounds. destruct env_blocks_in as (_ & _ & _ & B4).
  apply (block_region_ok rho T_ES gg_14 m s L (p_es E) (e_es E) 904 [] HEAP B4 eq_refl Hr14 eq_refl eq_refl);
    [closed_side | closed_side | constructor | closed_side].
Qed.

(* [comment removed for export] *)
Lemma gg2_ok : region_ok ctusegs rho T_ERRNO gg_2 m.
Proof.
  destruct ERRNO as [[_ Hb] Hw]. cbn [cells_bytes cbytes cells_size csize] in Hb, Hw. rewrite app_nil_r in Hb. unfold LX_ERRNO, RMallocRep.RATP in Hb, Hw.
  apply region_ok_fresh; unfold rbase; cbn [rg_abs rg_size rg_al gg_2 A_ERRNO];
    repeat match goal with |- context [to_Z ?x] => is_ground x; let v := eval vm_compute in (to_Z x) in change (to_Z x) with v end;
    try (unfold two63; lia); try reflexivity; try (cbn; lia).
  intros i Hi. split.
    + destruct (nth_error (le4 errv) (Z.to_nat i)) as [b|] eqn:En; [|apply nth_error_None in En; rewrite length_le4 in En; lia].
      exists b. rewrite <- En, <- (proj2 (proj2 Hb) (Z.to_nat i)) by (rewrite length_le4; lia). rewrite Z2Nat.id by lia. reflexivity.
    + intros _. exact (proj2 (proj2 Hw) i ltac:(lia)).
Qed.

Variables (lo sp0 : Z).
Hypothesis STKH : stk ctusegs m lo sp0.
Hypothesis Hrho1 : rho T_GSTK = sp0 - GET_STATE_STACK.
Hypothesis Hlo : lo <= sp0 - GET_STATE_STACK.
Hypothesis Hlo0 : GLOBALS_TOP <= lo.
Hypothesis Hlo1 : alloc_ceiling <= lo.
Hypothesis Hsp63 : sp0 < 2 ^ 63.
Hypothesis Hsp16 : sp0 mod 16 = 0.

Lemma gg1_ok : region_ok ctusegs rho T_GSTK gg_1 m.
Proof.
  unfold gg_1, GET_STATE_STACK in *. unfold GLOBALS_TOP in Hlo0.
  apply region_ok_fresh; unfold rbase; cbn [rg_abs]; rewrite ?Hrho1; change (to_Z GSTK) with 1024.
  - lia.
  - unfold two63. lia.
  - lia.
  - apply Z.leb_le. reflexivity.
  - lia.
  - closed_side.
  - change (to_Z 4%uint63) with 4. change (2 ^ 4) with 16. rewrite <- (Z.mod_add _ 64 16) by lia. replace (sp0 - 1024 + 64 * 16) with sp0 by lia. exact Hsp16.
  - intros i Hi. destruct STKH as (_ & _ & Hs). destruct (Hs (sp0 - 1024 + i) ltac:(lia)) as [Hw Hb]. split; [exact Hb | intros _; exact Hw].
Qed.

(* [comment removed for export] *)
Definition ivw (t : int) (rg : region) : Z * Z * bool := (rbase rho t rg, rbase rho t rg + to_Z (rg_size rg), rg_wr rg).

Local Ltac sepw :=
  unfold ivw, rbase; cbn [rg_abs rg_size rg_wr gg_1 gg_2 gg_3 gg_4 gg_5 gg_6 gg_7 gg_8 gg_9 gg_10 gg_11 gg_12 gg_13 gg_14 fst snd
                          A_ERRNO A_STOPPED A_BASEONCE A_OPTSDONE A_MONCE A_MKEY A_OLOCK A_TCBTSD A_TSD3];
  rewrite ?Hr11, ?Hr12, ?Hr13, ?Hr14, ?Hrho1;
  repeat match goal with |- context [to_Z ?x] => is_ground x; let v := eval vm_compute in (to_Z x) in change (to_Z x) with v end;
  repeat (constructor; [cbn [fst snd]; first [intros _; lia | intros [X|X]; [discriminate X | discriminate X]] |]); constructor.

Lemma rmemG : Rmem ctusegs rho (MG od) m.
Proof.
  ceil_bounds.
  destruct env_blocks_in as (B1 & B2 & B3 & B4).
  destruct (block_bounds _ _ _ B1) as (K1 & K1' & K1''). destruct (block_bounds _ _ _ B2) as (K2 & K2' & K2'').
  destruct (block_bounds _ _ _ B3) as (K3 & K3' & K3''). destruct (block_bounds _ _ _ B4) as (K4 & K4' & K4'').
  unfold GET_STATE_STACK, GLOBALS_TOP in *.
  pose proof (Rmem_empty ctusegs rho m) as R0. pose proof (dir_inw_empty rho) as I0.
  unfold MG.
  Local Ltac add R I t rg Hok :=
    let RI := fresh in
    pose proof (Rmem_add_sepw ctusegs rho _ t rg m _ R I ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Hok ltac:(sepw)) as RI;
    clear R I; destruct RI as [R I].
  add R0 I0 T_ERRNO gg_2 gg2_ok.
  add R0 I0 T_STOPPED gg_3 gg3_ok.
  add R0 I0 T_BASEONCE gg_4 gg4_ok.
  add R0 I0 T_OPTSDONE (gg_5 od) gg5_ok.
  add R0 I0 T_MONCE gg_6 gg6_ok.
  add R0 I0 T_MKEY gg_7 gg7_ok.
  add R0 I0 T_OLOCK gg_8 gg8_ok.
  add R0 I0 T_TCBTSD gg_9 gg9_ok.
  add R0 I0 T_TSD3 gg_10 gg10_ok.
  add R0 I0 T_MK gg_11 gg11_ok.
  add R0 I0 T_SA gg_12 gg12_ok.
  add R0 I0 T_ND gg_13 gg13_ok.
  add R0 I0 T_ES gg_14 gg14_ok.
  add R0 I0 T_GSTK gg_1 gg1_ok.
  exact R0.
Qed.

End Handoff.
End WithCeiling0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rho_gs (sp0 MK SA ND ES : Z) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : valuation := fun t =>
  if (t =? T_GSTK)%uint63 then sp0 - GET_STATE_STACK
  else if (t =? T_MK)%uint63 then MK else if (t =? T_SA)%uint63 then SA else if (t =? T_ND)%uint63 then ND else if (t =? T_ES)%uint63 then ES
  else if (t =? TC_RA)%uint63 then bv_unsigned ra else if (t =? TC_GP)%uint63 then bv_unsigned gp
  else if (t =? TC_S0)%uint63 then bv_unsigned s0 else if (t =? TC_S0 + 1)%uint63 then bv_unsigned s1
  else if (t =? TC_S0 + 2)%uint63 then bv_unsigned s2 else if (t =? TC_S0 + 3)%uint63 then bv_unsigned s3
  else if (t =? TC_S0 + 4)%uint63 then bv_unsigned s4 else if (t =? TC_S0 + 5)%uint63 then bv_unsigned s5
  else if (t =? TC_S0 + 6)%uint63 then bv_unsigned s6 else if (t =? TC_S0 + 7)%uint63 then bv_unsigned s7
  else if (t =? TC_S0 + 8)%uint63 then bv_unsigned s8 else if (t =? TC_S0 + 9)%uint63 then bv_unsigned s9
  else if (t =? TC_S0 + 10)%uint63 then bv_unsigned s10 else if (t =? TC_S0 + 11)%uint63 then bv_unsigned s11
  else 0.

Lemma Rregs_initG (rho : valuation) (v : int) (MK SA ND ES : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (pc : word) (fc : bv 32) (rv : option word) :
  (forall t, to_Z t < to_Z NEXTG -> rho t = rho_gs (bv_unsigned sp) MK SA ND ES ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t) ->
  tp = Z_to_bv 64 RMallocRep.RATP -> a0 = Z_to_bv 64 (to_Z v) ->
  Rregs rho (regsG v) (Core (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F pc fc rv).
Proof.
  intros Hrho -> -> r.
  assert (Esp : pword rho T_GSTK (W false GSTK) = sp).
  { unfold pword. rewrite (Hrho T_GSTK) by (vm_compute; reflexivity).
    change (rho_gs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ T_GSTK) with (bv_unsigned sp - GET_STATE_STACK).
    change (wZ (W false GSTK)) with GET_STATE_STACK. replace (bv_unsigned sp - GET_STATE_STACK + GET_STATE_STACK) with (bv_unsigned sp) by lia. apply Z_to_bv_bv_unsigned. }
  destruct (reg_cases r) as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
    subst r; try exact I; try reflexivity; try exact (eq_sym Esp);
    cbn [den]; symmetry; apply HxpMain.pword_scalar; rewrite Hrho by (vm_compute; reflexivity); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma final_regs_denG (rho : valuation) (S : sstate) (F : bvmap 5 word) (pc : word) (fc : bv 32) (rv : option word)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) :
  final_regs_okG S = true ->
  Rregs rho (s_regs S) (Core (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pc fc rv) ->
  x1 = pword rho TC_RA w_zero /\ x2 = pword rho T_GSTK (W false GSTK) /\ x3 = pword rho TC_GP w_zero /\ x4 = wbv TPVG /\ x10 = pword rho T_ES w_zero
  /\ x8 = pword rho TC_S0 w_zero /\ x9 = pword rho (TC_S0 + 1)%uint63 w_zero /\ x18 = pword rho (TC_S0 + 2)%uint63 w_zero
  /\ x19 = pword rho (TC_S0 + 3)%uint63 w_zero /\ x20 = pword rho (TC_S0 + 4)%uint63 w_zero /\ x21 = pword rho (TC_S0 + 5)%uint63 w_zero
  /\ x22 = pword rho (TC_S0 + 6)%uint63 w_zero /\ x23 = pword rho (TC_S0 + 7)%uint63 w_zero /\ x24 = pword rho (TC_S0 + 8)%uint63 w_zero
  /\ x25 = pword rho (TC_S0 + 9)%uint63 w_zero /\ x26 = pword rho (TC_S0 + 10)%uint63 w_zero /\ x27 = pword rho (TC_S0 + 11)%uint63 w_zero.
Proof.
  intros Hok HR. unfold final_regs_okG, final_regsG in Hok. cbn [forallb fst snd] in Hok.
  repeat (apply andb_prop in Hok as [?E Hok]). clear Hok.
  repeat match goal with E : HxpRun.hval_eqb (rget S ?X) ?v = true |- _ => apply HxpRun.hval_eqb_eq in E end.
  pose proof (HR (Z_to_bv 5 1)) as D1. pose proof (HR (Z_to_bv 5 2)) as D2. pose proof (HR (Z_to_bv 5 3)) as D3. pose proof (HR (Z_to_bv 5 4)) as D4.
  pose proof (HR (Z_to_bv 5 10)) as D10.
  pose proof (HR (Z_to_bv 5 8)) as D8. pose proof (HR (Z_to_bv 5 9)) as D9. pose proof (HR (Z_to_bv 5 18)) as D18. pose proof (HR (Z_to_bv 5 19)) as D19.
  pose proof (HR (Z_to_bv 5 20)) as D20. pose proof (HR (Z_to_bv 5 21)) as D21. pose proof (HR (Z_to_bv 5 22)) as D22. pose proof (HR (Z_to_bv 5 23)) as D23.
  pose proof (HR (Z_to_bv 5 24)) as D24. pose proof (HR (Z_to_bv 5 25)) as D25. pose proof (HR (Z_to_bv 5 26)) as D26. pose proof (HR (Z_to_bv 5 27)) as D27.
  change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 1))) with (rget S X1) in D1. change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 2))) with (rget S X2) in D2.
  change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 3))) with (rget S X3) in D3. change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 4))) with (rget S X4) in D4.
  change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 10))) with (rget S X10) in D10.
  change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 8))) with (rget S X8) in D8. change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 9))) with (rget S X9) in D9.
  change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 18))) with (rget S X18) in D18. change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 19))) with (rget S X19) in D19.
  change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 20))) with (rget S X20) in D20. change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 21))) with (rget S X21) in D21.
  change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 22))) with (rget S X22) in D22. change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 23))) with (rget S X23) in D23.
  change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 24))) with (rget S X24) in D24. change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 25))) with (rget S X25) in D25.
  change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 26))) with (rget S X26) in D26. change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 27))) with (rget S X27) in D27.
  repeat match goal with E : rget S ?X = _, D : den rho (rget S ?X) _ |- _ => rewrite E in D; clear E end.
  cbn [den] in *. repeat split; assumption.
Qed.

(* [comment removed for export] *)
Lemma stk_top_below (m : word -> option byte) (lo hi : Z) : mem_inv ctusegs m -> stk ctusegs m lo hi -> lo < hi -> hi <= UTOP.
Proof.
  intros MI (H0 & H1 & H) Hlt. destruct (H (hi - 1) ltac:(lia)) as [_ [b Hb]].
  pose proof (mrd_below ctusegs m _ _ MI Hb) as X. rewrite wa_unsigned in X by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma bytes_le_to_Z_bound : forall bs : list byte, 0 <= bytes_le_to_Z bs < 2 ^ (8 * Z.of_nat (length bs)).
Proof.
  induction bs as [|b bs IH]; cbn [bytes_le_to_Z length]; [lia|].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2 ^ Z.of_N 8) with (2 ^ 8) in Hb.
  replace (8 * Z.of_nat (S (length bs))) with (8 * Z.of_nat (length bs) + 8) by lia.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite (lor_add (bv_unsigned b) (bytes_le_to_Z bs) 8) by lia.
  rewrite Z.pow_add_r by lia. nia.
Qed.

Lemma le_bytes_roundtrip : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; cbn [Z_to_le_bytes bytes_le_to_Z length]; [reflexivity|].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2 ^ Z.of_N 8) with 256 in Hb.
  pose proof (bytes_le_to_Z_bound bs) as [R0 _].
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with (2 ^ 8).
    rewrite <- Z.land_ones by lia. apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, Z.lor_spec, Z.shiftl_spec by lia.
    destruct (Z.ltb_spec k 8) as [L|L].
    + rewrite Z.ones_spec_low by lia. rewrite (Z.testbit_neg_r _ (k - 8)) by lia. rewrite orb_false_r, andb_true_r. reflexivity.
    + rewrite Z.ones_spec_high by lia. rewrite andb_false_r.
      destruct (Z.eq_dec (bv_unsigned b) 0) as [->|Hn0]; [rewrite Z.bits_0; reflexivity|]. symmetry. apply Z.bits_above_log2; [lia|].
      apply (Z.lt_le_trans _ 8); [|lia]. apply Z.log2_lt_pow2; lia.
  - transitivity (Z_to_le_bytes (length bs) (bytes_le_to_Z bs)); [|exact IH]. f_equal.
    rewrite Z.shiftr_lor, Z.shiftr_shiftl_l, Z.sub_diag, Z.shiftl_0_r by lia.
    rewrite (Z.shiftr_div_pow2 (bv_unsigned b) 8) by lia. change (2 ^ 8) with 256. rewrite Z.div_small by lia. apply Z.lor_0_l.
Qed.

(* [comment removed for export] *)
Lemma rw_cell4_of_bytes (m : word -> option byte) (A : Z) (bs : list byte) :
  length bs = 4%nat -> bytes_at ctusegs m A bs -> wr_at ctusegs m A 4 -> exists v : word, rw_cells ctusegs m A [C4 v].
Proof.
  intros Hl Hb Hw. exists (Z_to_bv 64 (bytes_le_to_Z bs)).
  assert (E : le4 (Z_to_bv 64 (bytes_le_to_Z bs)) = bs).
  { unfold le4. rewrite Z_to_bv_unsigned.
    pose proof (bytes_le_to_Z_bound bs) as R. rewrite Hl in R. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R.
    rewrite bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2 ^ 64); lia).
    rewrite <- Hl. apply le_bytes_roundtrip. }
  split; [split; [cbn; auto | cbn [cells_bytes cbytes]; rewrite app_nil_r, E; exact Hb] | cbn [cells_size csize]; exact Hw].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeiling1. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Theorem ossl_err_get_state_int_spec : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (s : PState) (L OW : list block)
    (E : ap_env) (st : ap_st bptr) (bo : Z * Z) (errv : word) (v : Z),
  ap_state st m OW E bo -> RHEAP s L m -> (forall b, In b OW -> In b L) ->
  stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - GET_STATE_STACK ->
  bv_unsigned sp mod 16 = 0 -> rw_cells ctusegs m LX_ERRNO [C4 errv] -> mem_inv ctusegs m -> tp = wz RMallocRep.RATP ->
  (v = 0 \/ v = 1) -> a0 = wz v ->
  evt ctusegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' errv',
               ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz (e_es E)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom ctusegs)
               /\ munch [(bv_unsigned sp - GET_STATE_STACK, bv_unsigned sp); (LX_ERRNO, LX_ERRNO + 4)] m m'
               /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
               /\ stk ctusegs m' lo (bv_unsigned sp)
               /\ rw_cells ctusegs m' LX_ERRNO [C4 errv'])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 OSSL_ERR_GET_STATE_INT) fc None m (seg_rom ctusegs)).
Proof.
  intros until v. intros AS HEAP INCL Hstk Hlo1 Hlo2 Hlo3 Hsp16 ERRNO Hmi Etp Hv Ea0. ceil_bounds.
  pose proof (stk_top_below m lo (bv_unsigned sp) Hmi Hstk ltac:(unfold GET_STATE_STACK in Hlo3; lia)) as Hsp47. unfold UTOP in Hsp47.
  assert (Hsp63 : bv_unsigned sp < 2 ^ 63) by lia.
  (* [comment removed for export] *)
  assert (Hod : exists od : int, rw_cells ctusegs m OI_OPTSDONE [C8 (wz (to_Z od))] /\ (od = 2%uint63 \/ od = 0x42%uint63)).
  { destruct AS as (_ & _ & _ & Hcnf & _). destruct (as_cnf st) as [[[lk lh] bk]|]; cbn [ap_statics_cnf] in Hcnf.
    - exists 0x42%uint63. split; [exact (proj1 (proj2 Hcnf)) | right; reflexivity].
    - exists 2%uint63. split; [exact (proj1 (proj2 Hcnf)) | left; reflexivity]. }
  destruct Hod as (od & Hodc & Hod).
  set (vi := of_Z v). assert (Hvi : vi = 0%uint63 \/ vi = 1%uint63) by (destruct Hv as [-> | ->]; [left | right]; reflexivity).
  assert (Evi : to_Z vi = v) by (destruct Hv as [-> | ->]; reflexivity).
  set (rho0 := rho_gs (bv_unsigned sp) (e_mk E) (e_sa E) (e_nd E) (e_es E) ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  set (WIV := [(bv_unsigned sp - GET_STATE_STACK, bv_unsigned sp); (LX_ERRNO, LX_ERRNO + 4)]).
  set (ms0 := MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 OSSL_ERR_GET_STATE_INT) fc None m (seg_rom ctusegs)).
  (* [comment removed for export] *)
  destruct (gs_ok_inv (gs_result vi od) (gs_checked vi od Hvi Hod)) as (icE & SE & Erun & Epc & Erv & Hregs & Herr).
  unfold gs_result in Erun.
  (* [comment removed for export] *)
  assert (HRn0 : Rn ctusegs rho0 (S0G vi od) ms0).
  { intros rho2 Hag. cbn [S0G s_next] in Hag.
    assert (Hrho : forall t, to_Z t < to_Z NEXTG -> rho2 t = rho0 t) by exact Hag.
    unfold R, ms0. cbn [ms_svc_pending ms_pc_val ms_resv ms_mem MS S0G s_pc s_regs s_resv s_mem].
    split; [reflexivity|]. split; [reflexivity|]. split.
    { unfold core_of. cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv MS]. eapply Rregs_initG; [exact Hrho | exact Etp | rewrite Ea0, Evi; reflexivity]. }
    split; [reflexivity|].
    eapply (rmemG rho2 m s L OW E st bo od errv HEAP INCL AS ERRNO (conj Hodc Hod));
      first [ exact Hstk | exact Hlo1 | exact Hlo2 | exact Hlo3 | exact Hsp63 | exact Hsp16
            | exact (Hrho T_MK ltac:(vm_compute; reflexivity)) | exact (Hrho T_SA ltac:(vm_compute; reflexivity))
            | exact (Hrho T_ND ltac:(vm_compute; reflexivity)) | exact (Hrho T_ES ltac:(vm_compute; reflexivity))
            | exact (Hrho T_GSTK ltac:(vm_compute; reflexivity)) ]. }
  (* [comment removed for export] *)
  assert (HC0 : CInv ctusegs (MG od) WIV m F fc (S0G vi od) ms0).
  { unfold CInv, ms0. cbn [S0G s_mem ms_mem ms_fregs ms_fcsr ms_rom ms_regs MS].
    split; [apply same_dirs_refl|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact Hmi|].
    repeat (split; [reflexivity|]). do 31 eexists. reflexivity. }
  (* [comment removed for export] *)
  assert (W_ok : forall t rg, mget (MG od) t = Some rg -> rg_wr rg = true -> inside WIV (rbase rho0 t rg) (to_Z (rg_size rg))).
  { intros t rg G Hw. pose proof (mem_check_ok wr_bG (MG od) (MG_checked od Hod) t rg G) as HW. unfold wr_bG in HW. rewrite Hw in HW. cbn [negb orb] in HW.
    apply andb_prop in HW as [_ HW]. unfold rbase. destruct (rg_abs rg) as [a|].
    - apply andb_prop in HW as [HW E2]. apply andb_prop in HW as [E1 Ea]. apply Z.eqb_eq in E1, E2. apply Uint63.eqb_spec in Ea. rewrite E2, Ea.
      unfold WIV, LX_ERRNO, RMallocRep.RATP. cbn [inside]. right. left. change (to_Z A_ERRNO) with 0x333184. lia.
    - apply andb_prop in HW as [E1 E2]; apply Z.eqb_eq in E1, E2; rewrite E2.
      assert (t = T_GSTK) by (apply to_Z_inj; exact E1). subst t. change (rho0 T_GSTK) with (bv_unsigned sp - GET_STATE_STACK).
      unfold WIV, GET_STATE_STACK. cbn [inside]. left. lia. }
  destruct (hx_run_Rn_inv ctusegs stopG rho0 (CInv ctusegs (MG od) WIV m F fc) (CInv_step ctusegs rho0 (MG od) WIV m F fc W_ok) 13 IEmpty icE (S0G vi od) (RStop SE) ms0
              (ic_ok_empty ctusegs) HRn0 HC0 Erun) as (_ & ms1 & Hms & HRn1 & HC1).
  cbn [res_state] in HRn1, HC1.
  (* [comment removed for export] *)
  pose proof (Rn_R ctusegs rho0 SE ms1 HRn1) as HR1. pose proof HR1 as (Hsvc & Hpc & HRg & Hrv & HRm).
  destruct fetch_finalG as [ic' Hfetch]. rewrite <- Epc in Hfetch.
  destruct (hx_ret_step ctusegs rho0 IEmpty ic' SE ms1 (ic_ok_empty ctusegs) HR1 Hfetch) as (ms2 & Hstep & Ems2).
  exists ms2. split; [exact (msteps_trans ctusegs _ _ _ Hms (msteps_one ctusegs _ _ Hstep))|].
  destruct HC1 as (Hd1 & MU & WM & MI1 & Hfr & Hfc & Hro & Hnf).
  rewrite Erv in Hrv. cbn [Rresv] in Hrv.
  destruct Hnf as (y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y18 & y19 & y20
                   & y21 & y22 & y23 & y24 & y25 & y26 & y27 & y28 & y29 & y30 & y31 & Eregs).
  unfold core_of in HRg, Ems2. rewrite Eregs in HRg, Ems2. rewrite Hfr, Hfc, Hro, Hrv in Ems2.
  destruct (final_regs_denG rho0 SE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hregs HRg)
    as (E1 & E2 & E3 & E4 & E10 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27).
  rewrite (HxpMain.pword_scalar rho0 TC_RA ra) in E1 by reflexivity.
  rewrite (HxpMain.pword_scalar rho0 TC_GP gp) in E3 by reflexivity.
  rewrite (HxpMain.pword_scalar rho0 TC_S0 s0) in E8 by reflexivity.
  rewrite (HxpMain.pword_scalar rho0 (TC_S0 + 1)%uint63 s1) in E9 by reflexivity.
  rewrite (HxpMain.pword_scalar rho0 (TC_S0 + 2)%uint63 s2) in E18 by reflexivity.
  rewrite (HxpMain.pword_scalar rho0 (TC_S0 + 3)%uint63 s3) in E19 by reflexivity.
  rewrite (HxpMain.pword_scalar rho0 (TC_S0 + 4)%uint63 s4) in E20 by reflexivity.
  rewrite (HxpMain.pword_scalar rho0 (TC_S0 + 5)%uint63 s5) in E21 by reflexivity.
  rewrite (HxpMain.pword_scalar rho0 (TC_S0 + 6)%uint63 s6) in E22 by reflexivity.
  rewrite (HxpMain.pword_scalar rho0 (TC_S0 + 7)%uint63 s7) in E23 by reflexivity.
  rewrite (HxpMain.pword_scalar rho0 (TC_S0 + 8)%uint63 s8) in E24 by reflexivity.
  rewrite (HxpMain.pword_scalar rho0 (TC_S0 + 9)%uint63 s9) in E25 by reflexivity.
  rewrite (HxpMain.pword_scalar rho0 (TC_S0 + 10)%uint63 s10) in E26 by reflexivity.
  rewrite (HxpMain.pword_scalar rho0 (TC_S0 + 11)%uint63 s11) in E27 by reflexivity.
  assert (E2' : y2 = sp).
  { rewrite E2. unfold pword. change (rho0 T_GSTK) with (bv_unsigned sp - GET_STATE_STACK). change (wZ (W false GSTK)) with GET_STATE_STACK.
    replace (bv_unsigned sp - GET_STATE_STACK + GET_STATE_STACK) with (bv_unsigned sp) by lia. apply Z_to_bv_bv_unsigned. }
  assert (E4' : y4 = tp) by (rewrite E4, Etp; reflexivity).
  assert (E10' : y10 = wz (e_es E)).
  { rewrite E10. unfold pword. change (rho0 T_ES) with (e_es E). change (wZ w_zero) with 0. rewrite Z.add_0_r. reflexivity. }
  subst y1 y2 y3 y4 y8 y9 y10 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27.
  change (Sem.rget _ (Z_to_bv 5 1)) with ra in Ems2. rewrite E2', E4', E10' in Ems2.
  (* [comment removed for export] *)
  set (m' := ms_mem ms1) in *.
  (* [comment removed for export] *)
  assert (Herrno : exists errv', rw_cells ctusegs m' LX_ERRNO [C4 errv']).
  { unfold errno_okG in Herr. destruct (mget (s_mem SE) T_ERRNO) as [rge|] eqn:Ege; [|discriminate].
    destruct (rg_abs rge) as [ae|] eqn:Eae; [|discriminate]. apply andb_prop in Herr as [Herr Hwe]. apply andb_prop in Herr as [Ha Hsz].
    apply Uint63.eqb_spec in Ha. apply Uint63.eqb_spec in Hsz.
    pose proof (proj1 HRm T_ERRNO rge Ege) as Hok. pose proof Hok as (B0' & B1 & _ & _ & _ & _ & _ & Hby). unfold rbase in B0', B1, Hby. rewrite Eae, Ha, Hsz in Hby, B1.
    change (to_Z A_ERRNO) with LX_ERRNO in Hby. change (to_Z 4%uint63) with 4 in Hby.
    destruct (collect_bytes ctusegs m' 4 LX_ERRNO (fun _ _ => True) ltac:(unfold LX_ERRNO, RMallocRep.RATP; lia) ltac:(unfold LX_ERRNO, RMallocRep.RATP; lia)) as (bs & Hl & Hb & _).
    { intros i Hi. destruct (Hby i Hi) as (b & Eb & _). exists b. split; [exact Eb | exact I]. }
    apply (rw_cell4_of_bytes m' LX_ERRNO bs Hl Hb). split; [unfold LX_ERRNO, RMallocRep.RATP; lia|]. split; [unfold LX_ERRNO, RMallocRep.RATP; lia|].
    intros i Hi. destruct (Hby i Hi) as (b & _ & _ & W). exact (W Hwe). }
  destruct Herrno as [errv' Herrno].
  exists y5, y6, y7, y11, y12, y13, y14, y15, y16, y17, y28, y29, y30, y31, m', errv'.
  split; [exact Ems2|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI1|]. split; [|exact Herrno].
  (* [comment removed for export] *)
  destruct Hstk as (S1 & S2 & S3). split; [exact S1|]. split; [exact S2|]. intros a Ha. destruct (S3 a Ha) as [Hwv (b & Hb)].
  split; [apply WM; exact Hwv|].
  destruct (Z_lt_le_dec a (bv_unsigned sp - GET_STATE_STACK)) as [Lt|Ge].
  + exists b. unfold mrd in *. rewrite MU; [exact Hb|]. rewrite wa_unsigned by lia. unfold WIV, GET_STATE_STACK, LX_ERRNO, RMallocRep.RATP, GLOBALS_TOP in *. cbn [outside]. lia.
  + specialize (Hd1 T_GSTK). rewrite (MG_get1 od Hod) in Hd1.
    destruct (mget (s_mem SE) T_GSTK) as [rg1|] eqn:Eg1; [|contradiction].
    pose proof (region_mapped ctusegs rho0 T_GSTK rg1 m' (proj1 HRm _ _ Eg1)) as Hmp.
    rewrite (rbase_same_dir rho0 T_GSTK gg_1 rg1 Hd1) in Hmp. destruct Hd1 as (_ & Es1 & _). rewrite Es1 in Hmp.
    unfold rbase in Hmp. cbn [rg_abs rg_size gg_1] in Hmp. change (rho0 T_GSTK) with (bv_unsigned sp - GET_STATE_STACK) in Hmp.
    change (to_Z GSTK) with GET_STATE_STACK in Hmp.
    destruct (Hmp (a - (bv_unsigned sp - GET_STATE_STACK)) ltac:(lia)) as [Hm' _].
    replace (bv_unsigned sp - GET_STATE_STACK + (a - (bv_unsigned sp - GET_STATE_STACK))) with a in Hm' by lia. exact Hm'.
Qed.

End WithCeiling1.
