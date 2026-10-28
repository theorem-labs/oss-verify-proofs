(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AllocRepFacts AsDepotInv AW_MallocBase AllocWalkKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil}.

Lemma ienv_of_arep : forall s m, AREP s m -> IENV (wz ATP) ATSD (a_ctx s) (a_thr s) (a_sb s) (a_top s) (a_bot s) m.
Proof.
  intros s m R. destruct R as (OK & INST & FL & THR & _).
  destruct INST as (A1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & A9).
  destruct FL as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19 & F20 & F21 & F22 & F23 & F24 & F25 & F26 & F27).
  destruct THR as (T1 & T2 & T2b & T2c & T2d & _).
  apply (proj1 (rw_cells_app asegs _ _ [_] _)) in A1. destruct A1 as [A1 _].
  unfold AINST, OI_SPACEBEG, OI_MAXUSER, AFLAGS, ACFLAGS, ASHBASE_CELL, ASHADOW_BASE, AHIGHMEMEND, ACANPOISON, AINITED, ACTXSIZE, ATSDINIT,
         AALLOCFLAGS, AHOOKS, AREALMEMSET, AMEMSET, AGOT_LO, APAGESZ, ATLSSLOT, ATSD, ALSANDIS, AGOT2 in *.
  constructor; try assumption; unfold wz, ATP; rewrite ?unsigned_lit by lia; assumption.
Qed.

Lemma junk_stk' : forall m lo n, junk m lo n -> 0 <= lo -> lo + n <= 2^64 -> 0 <= n -> stk asegs m lo (lo + n).
Proof.
  intros m lo n J H1 H2 H3. destruct (Z.eq_dec n 0) as [->|NZ].
  - rewrite Z.add_0_r. apply stk_empty. lia.
  - apply J. lia.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_CB8_C8 : forall m A bs cs, rw_cells asegs m A (CB 8 bs :: cs) -> exists w, rw_cells asegs m A (C8 w :: cs).
Proof.
  intros m A bs cs R. assert (L : length bs = 8%nat) by (destruct R as [[[L _] _] _]; exact L).
  destruct (le8_surj bs L) as [w Hw]. exists w. destruct R as [[[_ W] B] R']. refine (conj (conj (conj I W) _) R').
  cbn [cells_bytes cbytes] in *. rewrite Hw. exact B.
Qed.

Section Hit.
  Variable s : ast.
  Variable m : mem.
  Hypothesis R : AREP s m.
  Let st := a_st s.

  (* [comment removed for export] *)
  Lemma hit_cells_of_arep : forall c, 1 <= c < kNumClasses -> pc_count (get_pc st c) <> 0 ->
    let pc := get_pc st c in let cp := hd 0 (pc_chunks pc) in
    let P := a_cache s + 80 * c in let AB := a_sb s + c * 2^32 + cp * 16 in let csz := class_size c in
    exists (j0 j1 j2 j3 : word),
       rw_cells asegs m P [C4 (wz (pc_count pc)); C4 (wz (max_count c))] /\ rw_cells asegs m (P + 8) [C8 (wz csz)]
    /\ u32arr asegs m (P + 16) (wlist (rev (pc_chunks pc))) /\ stk asegs m (P + 16 + 4 * pc_count pc) (P + 80)
    /\ rw_cells asegs m (a_thr s + 208 + 2560) [C8 j0; C8 j1; C8 j2; C8 j3]
    /\ stk asegs m AB (AB + csz) /\ u8arr asegs m (sh AB) (repeat (b8 0xfa) (Z.to_nat (csz / 8)))
    /\ stk asegs m (a_thr s + 2800) (a_thr s + 3168) /\ rw_cells asegs m (a_thr s + 3168) [C1 (b8 0)]
    /\ pc_count pc = zlen (pc_chunks pc) /\ 1 <= pc_count pc <= 16 /\ Forall (fun cp => 0 <= cp < 2^32) (pc_chunks pc)
    /\ a_sb s <= AB /\ AB + csz <= a_sb s + kSpaceSize /\ as_cache_inited st = true.
  Proof.
    intros c Hc CNT pc cp P AB csz.
    destruct R as (OK & INST & FL & THR & SEC & IA & CL & CH & BT & BG).
    assert (Hc' : 0 <= c < kNumClasses) by lia.
    destruct (CL c Hc') as (RG & PC & RSH & RJ).
    pose proof (WF_cache _ c (proj2 OK) Hc') as CO.
    pose proof (class_size_table_facts c ltac:(unfold kNumClasses in Hc; lia)) as CT.
    assert (INI : as_cache_inited st = true).
    { destruct (as_cache_inited st) eqn:E; [reflexivity|]. exfalso. pose proof (co_bound _ _ CO) as B. unfold st in E. rewrite E in B. exact (CNT B). }
    destruct PC as (P1 & P2 & U & J). subst pc cp P AB csz st. cbv zeta. rewrite INI in P1, P2. cbn [andb] in P1, P2.
    replace (negb (c =? 0)) with true in P1, P2 by (symmetry; apply Bool.negb_true_iff, Z.eqb_neq; lia).
    pose proof (co_count _ _ CO) as CC. pose proof (co_bound _ _ CO) as CB. rewrite INI in CB.
    assert (CNT0 : 0 <= pc_count (get_pc (a_st s) c)) by (rewrite CC; unfold zlen; lia).
    assert (CPS : Forall (fun cp => 0 <= cp < 2^32) (pc_chunks (get_pc (a_st s) c))).
    { apply Forall_forall. intros x Hx. destruct (co_elems _ _ CO x Hx) as (E1 & E2 & _).
      pose proof (WF_region _ c (proj2 OK) Hc') as RO. pose proof (ro_alloc_le _ _ RO) as AL. pose proof (ro_mapped_bound _ _ RO) as MB.
      rewrite Z.shiftl_mul_pow2 in E2 by (unfold kCompactPtrScale; lia).
      unfold kCompactPtrScale, kUserMapSize, kFreeArrayOffset in *. lia. }
    assert (IN : In (hd 0 (pc_chunks (get_pc (a_st s) c))) (pc_chunks (get_pc (a_st s) c))).
    { destruct (pc_chunks (get_pc (a_st s) c)) as [|x l] eqn:E; [| left; reflexivity]. exfalso. apply CNT. rewrite CC. reflexivity. }
    pose proof (carved_cache _ c _ (proj2 OK) Hc' IN) as CV.
    pose proof (carved_in_space s OK c _ CV) as (CS1 & CS2 & CS3).
    pose proof OK as OK'. destruct OK' as [PL _].
    pose proof PL as (S1 & S2 & S3 & P1' & P2' & P3 & T1 & T2 & T3 & _).
    apply akobj_env in T2; [| unfold kPageSize; clear; lia].   (* [comment removed for export] *)
    rewrite compact_to_addr_eq, region_beg_eq in *. unfold a_sb in *.
    (* [comment removed for export] *)
    destruct THR as (Tc & Ttid & Tthr & Tstk & T40 & Tsw & Ttq & Jtq & Jcs & Jst & Tunw).
    unfold a_cache, OT_CACHE, CACHE_STATS, OT_STATS, OT_UNWINDING, OT_TQ, PCLASS_SIZE in *.
    acb. unfold AHI_LO, kSpaceSize, kPageSize in *.
    pose proof (junk_stk' _ _ _ Jcs ltac:(lia) ltac:(lia) ltac:(lia)) as SCS.
    destruct (stk_cells _ _ _ SCS ltac:(lia)) as [js JS]. replace (a_thr s + 208 + 2560 + (2800 - 208 - 2560) - (a_thr s + 208 + 2560)) with 32 in JS by lia.
    change (Z.to_nat 32) with 32%nat in JS.
    apply (rw_cells_split_CB asegs _ _ [] 32 js [] [8;8;8;8]%nat) in JS; [| reflexivity]. cbn [mk_CB_cells app] in JS.
    destruct (rw_cells_CB8_C8 _ _ _ _ JS) as [w0 JS0].
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in JS0. destruct JS0 as [K0 JS1]. cbn [cells_size csize Nat.add] in JS1.
    destruct (rw_cells_CB8_C8 _ _ _ _ JS1) as [w1 JS1'].
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in JS1'. destruct JS1' as [K1 JS2]. cbn [cells_size csize Nat.add] in JS2.
    destruct (rw_cells_CB8_C8 _ _ _ _ JS2) as [w2 JS2'].
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in JS2'. destruct JS2' as [K2 JS3]. cbn [cells_size csize Nat.add] in JS3.
    destruct (rw_cells_CB8_C8 _ _ _ _ JS3) as [w3 K3].
    exists w0, w1, w2, w3.
    split; [exact P1|]. split; [exact P2|]. split; [exact U|].
    split. { replace (a_thr s + 208 + 80 * c + 80) with (a_thr s + 208 + 80 * c + 16 + 4 * pc_count (get_pc (a_st s) c) + (64 - 4 * pc_count (get_pc (a_st s) c))) by lia.
             apply junk_stk'; [exact J| unfold kNumClasses in *; lia| unfold kNumClasses in *; lia| lia]. }
    split. { apply (proj2 (rw_cells_app asegs _ _ [_] _)). split; [exact K0|]. cbn [cells_size csize Nat.add].
             apply (proj2 (rw_cells_app asegs _ _ [_] _)). split; [exact K1|]. cbn [cells_size csize Nat.add].
             apply (proj2 (rw_cells_app asegs _ _ [_] _)). split; [exact K2|]. cbn [cells_size csize Nat.add]. exact K3. }
    split. { pose proof (proj2 RJ _ IN) as JC. rewrite compact_to_addr_eq, region_beg_eq in JC. apply junk_stk'; [exact JC| lia| lia| lia]. }
    split. { destruct RSH as (_ & RS2 & _). destruct (RS2 _ IN) as (_ & _ & U8). rewrite compact_to_addr_eq, region_beg_eq in U8. exact U8. }
    split. { replace (a_thr s + 3168) with (a_thr s + 2800 + (3168 - 2800)) by lia. apply junk_stk'; [exact Jst| lia| lia| lia]. }
    split; [exact Tunw|].
    split; [exact CC|]. split; [lia|]. split; [exact CPS|]. split; [lia|]. split; [lia|]. exact INI.
  Qed.
End Hit.

End HCW.


