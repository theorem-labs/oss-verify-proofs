(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AllocRepFacts AllocRepFacts2
     AllocWalkKit AW_LargeAlloc1 AW_Efs AW_Populate AW_Gfa AW_InitCache AG_Malloc AG_Malloc2 AG_WFHit AG_RefillModel AS_Refill1 AG_Refill1 AllocRepX.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lia ::=
  dle_wrap ltac:(first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ]).

(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil}.

Lemma poisoned_app : forall m A k1 k2 v,
  poisoned m A k1 v -> poisoned m (A + 8 * Z.of_nat k1) k2 v -> poisoned m A (k1 + k2) v.
Proof.
  intros m A k1 k2 v P1 P2. unfold poisoned, poison_bytes in *. rewrite repeat_app. apply (proj2 (SHAD_app _ _ _ _)).
  rewrite repeat_length. split; assumption.
Qed.
Lemma poisoned_split : forall m A k1 k2 v,
  poisoned m A (k1 + k2) v -> poisoned m A k1 v /\ poisoned m (A + 8 * Z.of_nat k1) k2 v.
Proof.
  intros m A k1 k2 v PZ. unfold poisoned, poison_bytes in *. rewrite repeat_app in PZ. apply (proj1 (SHAD_app _ _ _ _)) in PZ.
  rewrite repeat_length in PZ. exact PZ.
Qed.
(* [comment removed for export] *)
Lemma poisoned_sub : forall m A k v B j, poisoned m A k v -> A <= B -> B mod 8 = 0 -> B + 8 * Z.of_nat j <= A + 8 * Z.of_nat k ->
  poisoned m B j v.
Proof.
  intros m A k v B j PZ LE B8 HI. pose proof (SHAD_aligned _ _ _ PZ) as [A0 A8].
  set (k1 := Z.to_nat ((B - A) / 8)).
  assert (E : k = (k1 + (j + (k - k1 - j)))%nat) by (subst k1; Z.div_mod_to_equations; lia).
  rewrite E in PZ. apply poisoned_split in PZ. destruct PZ as [_ PZ]. apply poisoned_split in PZ. destruct PZ as [PZ _].
  replace (A + 8 * Z.of_nat k1) with B in PZ; [exact PZ|]. subst k1. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma outside_icW_far : forall CA a, (a + 1 <= CA + 84 \/ CA + 2496 <= a) -> outside (icW CA) a.
Proof. intros CA a H. unfold icW. cbn. repeat split; lia. Qed.
Lemma outside_icW_count : forall CA c0 a, 0 <= c0 <= 31 -> CA + 80 * c0 <= a < CA + 80 * c0 + 4 -> outside (icW CA) a.
Proof. intros CA c0 a Hc H. unfold icW. cbn. repeat split; lia. Qed.
Lemma outside_icW_arr : forall CA c0 a, 0 <= c0 <= 31 -> CA + 80 * c0 + 16 <= a < CA + 80 * c0 + 80 -> outside (icW CA) a.
Proof. intros CA c0 a Hc H. unfold icW. cbn. repeat split; lia. Qed.

Lemma stk_of_u32arr : forall m A ws, u32arr asegs m A ws -> stk asegs m A (A + 4 * Z.of_nat (length ws)).
Proof.
  intros m A ws [B W].
  assert (U8 : u8arr asegs m A (u32s ws)). { split; [exact B|]. rewrite u32s_length, Nat2Z.inj_mul. exact W. }
  pose proof (rw_cells_of_u8arr asegs m A (u32s ws) U8) as RC.
  pose proof (stk_of_rw_cells asegs _ _ _ RC) as SK. cbn [cells_size csize] in SK. rewrite Nat.add_0_r, u32s_length, Nat2Z.inj_mul in SK. exact SK.
Qed.
Lemma junk_of_stk : forall m lo hi, stk asegs m lo hi -> junk m lo (hi - lo).
Proof. intros m lo hi SK POS. replace (lo + (hi - lo)) with hi by lia. exact SK. Qed.

Lemma junk_of_stk_eq : forall m lo hi n, stk asegs m lo hi -> hi = lo + n -> junk m lo n.
Proof. intros m lo hi n SK -> POS. exact SK. Qed.
Lemma junk_of_stk_range : forall m lo hi a n, stk asegs m lo hi -> lo <= a -> a + n <= hi -> junk m a n.
Proof. intros m lo hi a n SK H1 H2 POS. destruct (stk_split asegs _ _ a _ SK ltac:(hci; lia)) as [_ X]. destruct (stk_split asegs _ _ (a + n) _ X ltac:(hci; lia)) as [Y _]. exact Y. Qed.

(* [comment removed for export] *)
Lemma in_carve_cp : forall au csz nnew cp, au mod 16 = 0 -> csz mod 32 = 0 -> 0 <= au -> 0 < csz -> 0 <= nnew ->
  In cp (carve_asc au csz 0 (Z.to_nat nnew)) -> exists j, 0 <= j < nnew /\ cp * 16 = au + j * csz /\ 0 <= cp.
Proof.
  intros au csz nnew cp A16 C32 A0 CP NN Hin. apply in_carve_asc in Hin. destruct Hin as (j & Hj & E). rewrite Z2Nat.id in Hj by lia.
  exists j. rewrite Z.add_0_l in E.
  assert (M16 : (au + j * csz) mod 16 = 0) by (clear - A16 C32 Hj; try acb; Z.div_mod_to_equations; nia).
  assert (E' : cp = (au + j * csz) / 16) by (rewrite E; unfold kCompactPtrScale; rewrite Z.shiftr_div_pow2 by (clear; lia); reflexivity).
  clear - Hj M16 E' A0 CP; try acb. split; [lia|]. Z.div_mod_to_equations. nia.
Qed.
End HCW.

Section ArepAfterRefill.
  Context {HCEIL : HeapCeil}.
  Variables (s : ast) (m0 m2 : mem) (c : Z) (L2 S2 : list (word * word)) (AL2 lo spv : Z) (q0 q1 q2 q3 : word).
  Let st := a_st s.
  Let T := a_thr s.
  Let CA := a_cache s.
  Let sb := a_sb s.
  Let P := CA + 80 * c.
  Let RI := a_ri s + 128 * c.
  Let r := get_region st c.
  Let nf := rg_num_freed r. Let mfa := rg_mapped_free_array r. Let au := rg_allocated_user r. Let mu := rg_mapped_user r. Let fl := rg_free_array r.
  Let n := rf_n c. Let csz := class_size c.
  Let mu' := rf_mu' c nf au mu. Let nnew := rf_nnew c nf au mu. Let nf1 := rf_nf1 c nf au mu. Let mfa' := rf_mfa' c nf mfa au mu.
  Let au' := rf_au' c nf au mu. Let fl1 := rf_fl1 c nf au mu fl.
  Let st2 := refilled st c.
  Let s2 := mkAst st2 (a_thr s) (a_ctx s) (a_fsb s) L2 S2 (a_Zr s) AL2 (a_top s) (a_bot s).
  (* [comment removed for export] *)
  Let W : list ivl := (lo, spv) :: (T + 3168, T + 3169) :: rf_W lo spv P RI (FA s c) (RB s c) T CA nf mfa mu mfa' mu'.

  Hypothesis R0 : AREP s m0.
  Hypothesis HC : 1 <= c <= 30.
  Hypothesis EMPTY : pc_count (get_pc st c) = 0.
  Hypothesis ROOM : mu + 2 * kUserMapSize <= kFreeArrayOffset.
  Hypothesis LO : aceil <= lo.
  Hypothesis AG : agree_on (outside W) m0 m2.
  Hypothesis WM : wmono asegs m0 m2.
  (* [comment removed for export] *)
  Hypothesis PCN : rw_cells asegs m2 P [C4 (wz n)].
  Hypothesis FAM2 : forall c', 1 <= c' <= 31 -> rw_cells asegs m2 (CA + 80 * c' + 4) [C4 (wz (max_count c'))] /\ rw_cells asegs m2 (CA + 80 * c' + 8) [C8 (wz (class_size c'))].
  Hypothesis CHA : u32arr asegs m2 (P + 16) (wlist (rev (firstn (Z.to_nat n) fl1))).
  Hypothesis CHJ : stk asegs m2 (P + 16 + 4 * n) (P + 80).
  Hypothesis RI2 : rw_cells asegs m2 RI [C8 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz (nf1 - n)); C8 (wz mfa'); C8 (wz au'); C8 (wz 0); C8 (wz mu'); C8 (wz 0)].
  Hypothesis RIJ2 : stk asegs m2 (RI + 64) (RI + 68).
  Hypothesis EXH2 : rw_cells asegs m2 (RI + 68) [C1 (b8 0)].
  Hypothesis RST2 : stk asegs m2 (RI + 69) (RI + 128).
  Hypothesis FARR2 : u32arr asegs m2 (FA s c) (wlist (rev fl1)).
  Hypothesis FAJ2 : stk asegs m2 (FA s c + 4 * nf1) (FA s c + mfa').
  Hypothesis USJ2 : stk asegs m2 (RB s c + au) (RB s c + mu').
  Hypothesis POIu2 : poisoned m2 (RB s c + mu) (Z.to_nat ((mu' - mu) / 8)) 0xfa.
  Hypothesis POIf2 : poisoned m2 (FA s c + mfa) (Z.to_nat ((mfa' - mfa) / 8)) 0xfa.
  Hypothesis QST2 : rw_cells asegs m2 (T + 2768) [C8 q0; C8 q1; C8 q2; C8 q3].
  Hypothesis TST2 : stk asegs m2 (T + 2800) (T + 3168).
  Hypothesis UNW2 : rw_cells asegs m2 (T + 3168) [C1 (b8 0)].

  Let OK : ast_ok s. Proof. exact (proj1 R0). Qed.
  Let PL : placed_ok s. Proof. exact (proj1 OK). Qed.
  Let WFs : WF st. Proof. exact (proj2 OK). Qed.
  Let WF2 : WF st2. Proof. exact (WF_refill st c WFs HC EMPTY ROOM). Qed.
  Let OK2 : ast_ok s2. Proof. split; [exact PL| exact WF2]. Qed.
  Let RF := rf_facts st c WFs HC ROOM.
  Let PURE := refill_pure s m0 c R0 HC EMPTY.
  Let RGc := rfd_region_c st c WFs HC ROOM.
  Let RGo := rfd_region_o st c WFs HC ROOM.
  Let PCc := rfd_pc_c st c WFs HC ROOM.
  Let PCo := rfd_pc_o st c WFs HC ROOM.
  Let SAME := rfd_same st c.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Let B_pl : aceil <= lo /\ 4096 <= T /\ T + 4096 <= aceil /\ 0x10007fff8000 <= sb
             /\ sb + 137438953472 + 4096 <= aceil /\ 12599296 <= a_ctx s /\ a_ctx s + 160 <= aceil
             /\ 12599296 <= a_pa s /\ a_pa s + 8388608 <= aceil /\ 1 <= c <= 30.
  Proof.
    pose proof PL as (Y1 & Y2 & Y3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & _).
    apply akobj_env in T2; [| unfold kPageSize; clear; lia]. apply aapp_env in P2; [| unfold kPtrArrayReserve; clear; lia]. apply aapp_env in X2; [| clear; lia].
    acb. unfold AHI_LO, kSpaceSize, kPageSize, kPtrArrayReserve in *. subst T sb. unfold a_sb in *.
    clear - LO Y2 Y3 P2 P3 T2 T3 X2 X3 HC; try acb. repeat split; first [assumption | lia].
  Qed.
  Let BANDS : hidden ((T + 4096 <= 65536 \/ (12599296 <= T /\ T + 4096 <= 2147446784) \/ 17594333495296 <= T)
                   /\ (a_ctx s + 160 <= 2147446784 \/ 17594333495296 <= a_ctx s)
                   /\ (a_pa s + 8388608 <= 2147446784 \/ 17594333495296 <= a_pa s)).
  Proof.
    pose proof PL as (_ & _ & _ & _ & P2 & _ & _ & T2 & _ & _ & X2 & _).
    split. split; [exact (akobj_lit _ _ T2)|]. split; [exact (aapp_lit _ _ X2)|].
    pose proof (aapp_lit _ _ P2) as L; unfold kPtrArrayReserve in L; exact L.
  Qed.
  Tactic Notation "bands_as" simple_intropattern(p) := (let X := fresh "BX" in pose proof BANDS as X; destruct X as [p]).
  Let B_geo : P = T + 208 + 80 * c /\ CA = T + 208 /\ RI = sb + 137438953472 + 128 * c /\ RB s c = sb + c * 4294967296 /\ FA s c = RB s c + 3758096384.
  Proof.
    subst P CA RI T sb. unfold a_cache, a_ri, OT_CACHE, kSpaceSize, RB, FA, a_sb. rewrite free_array_base_eq, region_beg_eq. unfold kFreeArrayOffset.
    repeat split; reflexivity.
  Qed.
  Let B_dj : (T + 4096 <= sb \/ sb + 137438953472 + 4096 <= T) /\ (a_ctx s + 160 <= sb \/ sb + 137438953472 + 4096 <= a_ctx s)
             /\ (a_pa s + 8388608 <= sb \/ sb + 137438953472 + 4096 <= a_pa s)
             /\ (a_pa s + 8388608 <= T \/ T + 4096 <= a_pa s) /\ (T + 4096 <= a_ctx s \/ a_ctx s + 160 <= T).
  Proof.
    pose proof PL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D1 & D2 & D3 & D4 & D5 & _ & _ & _ & _ & _ & _ & _ & _ & TCX & _).
    unfold disj, kSpaceSize, kPageSize, kPtrArrayReserve in D1, D2, D3, D4, TCX. subst T sb. unfold a_sb in *. clear - D1 D2 D3 D4 TCX; try acb. repeat split; lia.
  Qed.
  Let B_ar : 0 <= nf /\ 4 * nf <= mfa /\ mfa <= mfa' <= 536870912 /\ 0 <= au <= mu /\ mu <= mu' <= mu + 262144 /\ mu' + 262144 <= 3758096384
             /\ 1 <= n <= 8 /\ n <= nf1 /\ 4 * nf1 <= mfa' /\ au <= au' <= mu' /\ 32 <= csz <= 65536.
  Proof.
    destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15).
    destruct PURE as (U1 & U2 & U3 & U4 & U5 & U6 & U7 & U8 & U9 & U10 & PCS).
    pose proof (class_size_table_facts c ltac:(hci; clear - HC; try acb; lia)) as (C1 & C2 & C3 & C4 & C5 & C6).
    unfold kUserMapSize, kFreeArrayOffset, kFreeArraySize in *.
    subst n csz nf mfa au mu nf1 mfa' au' mu' r st. unfold rf_n in *.
    clear - Q1 Q6 Q7 Q11 Q12 U1 U2 U4 ROOM C1 C3 C4 C5 HC; try acb. repeat split; lia.
  Qed.
  Let B_sh : 0x2008fff7000 <= sh (RB s c + mu) /\ sh (RB s c + mu) + (mu' - mu) / 8 <= (sh aceil)
             /\ 0x2008fff7000 <= sh (FA s c + mfa) /\ sh (FA s c + mfa) + (mfa' - mfa) / 8 <= (sh aceil).
  Proof. pose proof B_pl. pose proof B_geo. pose proof B_ar. clear - H H0 H1; try acb. unfold sh, ASHADOW_BASE. Z.div_mod_to_equations. lia. Qed.
  Let BND : (aceil <= lo /\ 4096 <= T /\ T + 4096 <= aceil /\ 0x10007fff8000 <= sb
             /\ sb + 137438953472 + 4096 <= aceil /\ 12599296 <= a_ctx s /\ a_ctx s + 160 <= aceil
             /\ 12599296 <= a_pa s /\ a_pa s + 8388608 <= aceil /\ 1 <= c <= 30)
         /\ (P = T + 208 + 80 * c /\ CA = T + 208 /\ RI = sb + 137438953472 + 128 * c /\ RB s c = sb + c * 4294967296 /\ FA s c = RB s c + 3758096384)
         /\ (0 <= nf /\ 4 * nf <= mfa /\ mfa <= mfa' <= 536870912 /\ 0 <= au <= mu /\ mu <= mu' <= mu + 262144 /\ mu' + 262144 <= 3758096384
             /\ 1 <= n <= 8 /\ n <= nf1 /\ 4 * nf1 <= mfa' /\ au <= au' <= mu' /\ 32 <= csz <= 65536)
         /\ (0x2008fff7000 <= sh (RB s c + mu) /\ sh (RB s c + mu) + (mu' - mu) / 8 <= (sh aceil)
             /\ 0x2008fff7000 <= sh (FA s c + mfa) /\ sh (FA s c + mfa) + (mfa' - mfa) / 8 <= (sh aceil)).
  Proof. exact (conj B_pl (conj B_geo (conj B_ar B_sh))). Qed.

  (* [comment removed for export] *)
  Let ALN : (RB s c + mu) mod 8 = 0 /\ 8 * ((mu' - mu) / 8) = mu' - mu /\ (FA s c + mfa) mod 8 = 0 /\ 8 * ((mfa' - mfa) / 8) = mfa' - mfa
            /\ mu mod 4096 = 0 /\ mu' mod 4096 = 0 /\ mfa mod 4096 = 0 /\ mfa' mod 4096 = 0 /\ sb mod 4096 = 0 /\ au mod 16 = 0 /\ au' mod 16 = 0.
  Proof.
    pose proof B_geo as (_ & _ & _ & ERB & EFA).
    destruct RF as (_ & _ & _ & _ & EAU & _ & _ & Q8 & Q9 & _ & _ & _ & Q13 & _). destruct PURE as (_ & _ & U3 & _ & _ & U6 & _).
    pose proof PL as (Y1 & _). pose proof (class_size_table_facts c ltac:(hci; clear - HC; try acb; lia)) as (C1 & C2 & C3 & _).
    pose proof (ro_alloc_mod _ _ (WF_region st c WFs ltac:(hci; unfold kNumClasses; clear - HC; try acb; lia)) ltac:(hci; clear - C3 HC; try acb; lia)) as AM.
    unfold kUserMapSize, kFreeArrayMapSize in *.
    subst n csz nf mfa au mu nf1 mfa' au' mu' r st sb. unfold a_sb in *.
    set (MU' := rf_mu' _ _ _ _) in *. set (MFA' := rf_mfa' _ _ _ _ _) in *. set (AU' := rf_au' _ _ _ _) in *. set (NNEW := rf_nnew _ _ _ _) in *.
    set (MU := rg_mapped_user _) in *. set (MFA := rg_mapped_free_array _) in *. set (AU := rg_allocated_user _) in *. set (SB := as_space_beg _) in *.
    set (CSZ := class_size c) in *.
    assert (A16 : AU mod 16 = 0) by (clear - AM C2 C3 HC; try acb; Z.div_mod_to_equations; nia).
    assert (A16' : AU' mod 16 = 0) by (rewrite EAU; clear - A16 C2; try acb; Z.div_mod_to_equations; nia).
    clear - ERB EFA Q8 Q13 U3 U6 Y1 A16 A16'; try acb. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  Ltac wsplit := unfold W, rf_W; cbn [outside];
    repeat lazymatch goal with
      | |- _ /\ _ => split
      | |- outside (icW _) _ => first [ apply outside_icW_far; lia | eapply outside_icW_count; [| eassumption]; lia | eapply outside_icW_arr; [| eassumption]; lia ]
      | |- True => exact I
      | |- ~ _ => lia
      end.

  (* [comment removed for export] *)
  Lemma Z_static : forall a, astatic a -> outside W a.
  Proof.
    intros a Ha. pose proof BND as B. bands_as (BT & _). clear - Ha B BT; try acb. unfold astatic in Ha.
    unfold AINST, OI_MISMATCH, AFLAGS, ACFLAGS, ASHBASE_CELL, AHIGHMEMEND, ACANPOISON, AINITED, AALLOCFLAGS, AIAINIT, AHOOKS, AREALMEMSET,
           AIAINST, AGOT_LO, APAGESZ, ASECNAME, APRIMNAME, ATLSSLOT, ATSD, ALSANDIS, AGOT2, ATP in Ha.
    assert (A23 : 65536 <= a < 12599296) by lia. clear Ha. wsplit.   (* [comment removed for export] *)
  Qed.
  Lemma Z_flags : forall a, aflags_range a -> outside W a.
  Proof.
    intros a Ha. pose proof BND as B. bands_as (BT & _). clear - Ha B BT; try acb. unfold aflags_range in Ha.
    unfold AFLAGS, ACFLAGS, ASHBASE_CELL, AHIGHMEMEND, ACANPOISON, AINITED, ACTXSIZE, ATSDINIT, AALLOCFLAGS, AIAINIT, AHOOKS, ADYING,
           AREALMEMSET, AIAINST, AGOT_LO, APAGESZ, ASECNAME, APRIMNAME, ATLSSLOT, ATSD, ALSANDIS, AGOT2, ATP in Ha.
    assert (A23 : 65536 <= a < 12599296) by lia. clear Ha. wsplit.   (* [comment removed for export] *)
  Qed.
  Lemma Z_T : forall a, T <= a < T + 208 -> outside W a.
  Proof. intros a Ha. pose proof BND as B. pose proof B_dj as (D & _). bands_as (BT & _). clear - Ha B D BT; try acb. wsplit. Qed.
  Lemma Z_CTX : forall a, a_ctx s + 8 <= a < a_ctx s + 160 -> outside W a.
  Proof. intros a Ha. pose proof BND as B. pose proof B_dj as (_ & D1 & _ & _ & D2). bands_as (_ & BC & _). clear - Ha B D1 D2 BC; try acb. wsplit. Qed.
  Lemma Z_PA : forall a, a_pa s <= a < a_pa s + kPtrArrayReserve -> outside W a.
  Proof. intros a Ha. pose proof BND as B. pose proof B_dj as (_ & _ & D1 & D2 & _). unfold kPtrArrayReserve in Ha. bands_as (_ & _ & BP). clear - Ha B D1 D2 BP; try acb. wsplit. Qed.
  (* [comment removed for export] *)
  Lemma Z_PCcnt : forall c0 a, 0 <= c0 < 32 -> c0 <> c -> CA + 80 * c0 <= a < CA + 80 * c0 + 4 -> outside W a.
  Proof. intros c0 a Hc0 NE Ha. pose proof BND as B. pose proof B_dj as (D & _). bands_as (BT & _). clear - Hc0 NE Ha B D BT; try acb. wsplit. Qed.
  Lemma Z_PCarr : forall c0 a, 0 <= c0 < 32 -> c0 <> c -> CA + 80 * c0 + 16 <= a < CA + 80 * c0 + 80 -> outside W a.
  Proof. intros c0 a Hc0 NE Ha. pose proof BND as B. pose proof B_dj as (D & _). bands_as (BT & _). clear - Hc0 NE Ha B D BT; try acb. wsplit. Qed.
  Lemma Z_PC0 : forall a, CA <= a < CA + 80 -> outside W a.
  Proof. intros a Ha. pose proof BND as B. pose proof B_dj as (D & _). bands_as (BT & _). clear - Ha B D BT; try acb. wsplit. Qed.
  (* [comment removed for export] *)
  Lemma Z_SPACE : forall a, sb <= a < sb + 137438953472 + 4096 ->
    (a + 1 <= RI \/ RI + 80 <= a) -> (a + 1 <= FA s c + 4 * nf \/ FA s c + mfa' <= a) -> (a + 1 <= RB s c + mu \/ RB s c + mu' <= a) -> outside W a.
  Proof. intros a Ha H1 H2 H3. pose proof BND as B. pose proof B_dj as (D & _). clear - Ha H1 H2 H3 B D; try acb. wsplit. Qed.
  Lemma Z_SEC : forall h a, In h (as_sec st) -> sc_map_beg h <= a < sc_map_beg h + sc_map_size h -> outside W a.
  Proof.
    intros h a Hh Ha. pose proof BND as B.
    pose proof PL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SEC & _).
    pose proof (SEC h Hh) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9). unfold disj, kSpaceSize, kPageSize, kPtrArrayReserve, AHI_LO in *.
    pose proof (aapp_lit _ _ Q2) as Q2l. apply aapp_env in Q2; [| clear - Q4; lia].   (* [comment removed for export] *)
    acb. fold sb T in Q5, Q7. clear - Ha B Q2 Q2l Q3 Q5 Q7; try acb. wsplit.
  Qed.
  (* [comment removed for export] *)
  Lemma Z_SH : forall lo' k a, 0 <= lo' -> lo' mod 8 = 0 -> 0 <= k -> lo' + 8 * k <= aceil ->
    (lo' + 8 * k <= RB s c + mu \/ RB s c + mu' <= lo') -> (lo' + 8 * k <= FA s c + mfa \/ FA s c + mfa' <= lo') ->
    sh lo' <= a < sh lo' + k -> outside W a.
  Proof.
    intros lo' k a H0 H8 Hk Hhi D1 D2 Ha. pose proof BND as B. destruct ALN as (M1 & M2 & M3 & M4 & _).
    assert (SS1 : sh lo' + k <= sh (RB s c + mu) \/ sh (RB s c + mu) + (mu' - mu) / 8 <= sh lo')
      by (clear - H8 M1 M2 Hk D1 B; try acb; apply sh_sep; try assumption; lia).
    assert (SS2 : sh lo' + k <= sh (FA s c + mfa) \/ sh (FA s c + mfa) + (mfa' - mfa) / 8 <= sh lo')
      by (clear - H8 M3 M4 Hk D2 B; try acb; apply sh_sep; try assumption; lia).
    assert (SB : 0x7fff8000 <= sh lo' /\ sh lo' + k <= 0x10007fef8000) by (clear - H0 Hk Hhi; try acb; acb; unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia).
    bands_as (BT & _). clear - Ha B SS1 SS2 SB BT; try acb. wsplit.
  Qed.
  (* [comment removed for export] *)
  Lemma carved_vs_W : forall c1 x, carved st c1 x ->
    sb <= x /\ x + class_size c1 <= sb + 137438953472 /\ 0 < class_size c1
    /\ (x + class_size c1 <= RB s c + au \/ RB s c + 4294967296 <= x \/ x + class_size c1 <= RB s c).
  Proof.
    intros c1 x CV. pose proof BND as B. pose proof (carved_in_space s OK c1 x CV) as (A1 & A2 & _). fold sb in A1, A2.
    destruct CV as (C1 & C2 & C3 & C4 & C5). unfold kNumClasses in C1.
    pose proof (class_size_table_facts c1 ltac:(hci; clear - C1; try acb; lia)) as (V1 & _).
    destruct (Z.eq_dec c1 c) as [->|NE].
    - fold st r au in C5. change (region_beg st c) with (RB s c) in C3, C5. unfold kSpaceSize in A2. clear - B A1 A2 C2 C3 C5 V1; try acb. lia.
    - pose proof (regions_disjoint st c1 c ltac:(hci; clear - C1; try acb; lia) ltac:(hci; clear - B; try acb; lia) NE) as D. change (region_beg st c) with (RB s c) in D.
      pose proof (ro_alloc_le _ _ (WF_region st c1 WFs ltac:(hci; unfold kNumClasses; clear - C1; try acb; lia))) as AL.
      pose proof (ro_mapped_bound _ _ (WF_region st c1 WFs ltac:(hci; unfold kNumClasses; clear - C1; try acb; lia))) as MB.
      unfold kUserMapSize, kFreeArrayOffset, kSpaceSize in *. clear - B A1 A2 C2 C3 C5 V1 D AL MB; try acb. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma Z_carved : forall c1 x a, carved st c1 x -> x <= a < x + class_size c1 -> outside W a.
  Proof.
    intros c1 x a CV Ha. pose proof BND as B. pose proof (carved_vs_W c1 x CV) as (A1 & A2 & A3 & A4).
    apply Z_SPACE; clear - Ha B A1 A2 A3 A4; try acb; lia.
  Qed.
  Lemma Z_carved_sh : forall c1 x lo' k a, carved st c1 x -> x <= lo' -> lo' + 8 * k <= x + class_size c1 -> lo' mod 8 = 0 -> 0 <= k ->
    sh lo' <= a < sh lo' + k -> outside W a.
  Proof.
    intros c1 x lo' k a CV G1 G2 G3 G4 Ha. pose proof BND as B. pose proof (carved_vs_W c1 x CV) as (A1 & A2 & A3 & A4).
    apply (Z_SH lo' k); try assumption; acb; clear - Ha B A1 A2 A3 A4 G1 G2 G4; try acb; lia.
  Qed.

  Let carved_of_elem_any : forall c0 cp, 0 <= c0 < 32 ->
    In cp (rg_free_array (get_region (a_st s) c0)) \/ In cp (pc_chunks (get_pc (a_st s) c0)) -> carved st c0 (compact_to_addr st c0 cp).
  Proof.
    intros c0 cp Hc0 [Hin|Hin]; [apply carved_free| apply carved_cache]; try exact WFs; try exact Hin; unfold kNumClasses; clear - Hc0; try acb; lia.
  Qed.
  Let AGp := AG.

  (* [comment removed for export] *)
  Lemma statics_after_refill : inst_rep s2 m2 /\ flags_rep s2 m2 /\ ia_rep s2 m2 /\ sec_rep s2 m2.
  Proof.
    pose proof R0 as RR. destruct RR as (_ & INST & FL & _ & SEC0 & IA & _).
    split.
    { change (inst_rep s2 m2) with (inst_rep s m2).
      apply (inst_rep_frame s m0 m2 (outside W) AGp WM); [| exact INST]. intros a Ha. apply Z_static. unfold astatic. left. exact Ha. }
    split.
    { change (flags_rep s2 m2) with (flags_rep s m2).
      apply (flags_rep_frame s m0 m2 (outside W) AGp WM); [| exact FL]. exact Z_flags. }
    split.
    { change (ia_rep s2 m2) with (ia_rep s m2).
      apply (ia_rep_frame s m0 m2 (outside W) AGp WM); [| exact IA]. intros a Ha. apply Z_static. unfold astatic. do 11 right. left. exact Ha. }
    change (sec_rep s2 m2) with (sec_rep s m2).
    apply (sec_rep_frame s m0 m2 (outside W) AGp WM OK); [| | exact SEC0].
    - intros a Ha. apply Z_PA. pose proof WFs as WW. destruct WW as (_ & _ & _ & _ & _ & _ & Wn & Wr & _). unfold kChunksBlockCount, kPtrArrayReserve in *.
      assert (0 <= zlen (as_sec st)) by (unfold zlen; clear; lia). change (a_st s) with st in Ha. clear - Ha Wn Wr H; try acb. lia.
    - intros h a Hh Ha. apply (Z_SEC h); [exact Hh|].
      pose proof PL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SEC & _).
      pose proof (SEC h Hh) as (_ & _ & _ & Q4 & _). unfold kPageSize in *. clear - Ha Q4; try acb. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma thread_after_refill : thread_rep s2 m2.
  Proof.
    pose proof BND as B. pose proof R0 as RR. destruct RR as (_ & _ & _ & THR & _).
    destruct THR as (T1 & T2 & T2b & T2c & T2d & T3 & T4 & J1 & J2 & J3 & T5).
    unfold thread_rep. change (a_ctx s2) with (a_ctx s). change (a_thr s2) with T. change (a_top s2) with (a_top s). change (a_bot s2) with (a_bot s).
    change (a_cache s2) with CA. change (as_tq (a_st s2)) with (as_tq st).
    fold T in T1, T2c, T2d, T3, T4, J1, J3, T5. fold CA in J2. unfold OT_SWITCHING, OT_TQ, OT_CACHE, OT_STATS, OT_UNWINDING, CACHE_STATS in *.
    Ltac trc H Z := eapply (rw_cells_transport_pt (outside W) m0 m2 AGp WM); [exact H|];
                    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ length repeat]; let Ha := fresh in intros ? Ha; apply Z; clear - Ha; try acb; lia.
    split; [trc T1 Z_T|]. split; [trc T2 Z_CTX|]. split; [trc T2b Z_CTX|]. split; [trc T2c Z_T|]. split; [trc T2d Z_T|].
    split; [trc T3 Z_T|]. split; [trc T4 Z_T|].
    split; [eapply (junk_transport_pt (outside W) m0 m2 AGp WM); [exact J1|]; let Ha := fresh in intros ? Ha; apply Z_T; clear - Ha; try acb; lia|].
    split.
    { intros _. pose proof (stk_of_rw_cells asegs _ _ _ QST2) as SQ. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in SQ.
      replace (CA + 2560) with (T + 2768) by (clear - B; try acb; lia). replace (T + 2768 + (2800 - 208 - 2560)) with (T + 2768 + 32) by (clear; lia). exact SQ. }
    split; [intros _; replace (T + 2800 + (3168 - 2800)) with (T + 3168) by (clear; lia); exact TST2|].
    exact UNW2.
  Qed.

  (* [comment removed for export] *)
  Lemma chunks_after_refill : forall x, In x (chunk_list st2) -> chunk_rep m2 x.
  Proof.
    intros x Hx. pose proof BND as B. pose proof R0 as RR. destruct RR as (_ & _ & _ & _ & _ & _ & _ & CHR & _).
    pose proof SAME as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S13 & _). unfold st2 in Hx. rewrite S13 in Hx. fold st in Hx.
    apply (chunk_rep_frame s m0 m2 (outside W) AGp WM OK x Hx); [| exact (CHR x Hx)].
    pose proof (record_ext s OK x Hx) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9).
    acb. unfold AIMG_TOP in X1.   (* [comment removed for export] *)
    pose proof (chunk_align s OK x Hx) as (A1 & A2 & A3 & A4 & A5).
    assert (NS : 8 * nsh (ch_used x) = round_up (ch_used x) 8 /\ ch_used x <= round_up (ch_used x) 8 /\ (round_up (ch_used x) 8) mod 8 = 0)
      by (unfold nsh, round_up; clear - X9; try acb; Z.div_mod_to_equations; lia).
    assert (RZ8 : 8 * (ch_rz x / 8) = ch_rz x) by (clear - A2; try acb; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    assert (APP : forall a, ch_lo x <= a < ch_end x -> outside W a).
    { intros a Ha. destruct (ch_primary x) eqn:PX.
      - pose proof (ext_facts s OK x Hx) as (_ & _ & _ & XP & _). destruct (XP PX) as (CV & EE & _).
        unfold ch_lo in Ha. rewrite PX in Ha. apply (Z_carved _ _ a CV). rewrite <- EE. exact Ha.
      - destruct (record_secondary_map s OK x Hx PX) as (h & Hh & E1 & E2 & _). apply (Z_SEC h); [exact Hh| clear - Ha E1 E2; try acb; lia]. }
    assert (SHW : forall lo' k a, ch_lo x <= lo' -> lo' + 8 * k <= ch_end x -> lo' mod 8 = 0 -> 0 <= k -> sh lo' <= a < sh lo' + k -> outside W a).
    { intros lo' k a G1 G2 G3 G4 Ga. destruct (ch_primary x) eqn:PX.
      - pose proof (ext_facts s OK x Hx) as (_ & _ & _ & XP & _). destruct (XP PX) as (CV & EE & _).
        unfold ch_lo in G1. rewrite PX in G1. apply (Z_carved_sh _ _ lo' k a CV); try assumption. rewrite <- EE. exact G2.
      - pose proof (record_vs_space s OK x Hx PX) as D. fold sb in D. unfold kSpaceSize, kPageSize in D.
        apply (Z_SH lo' k); try assumption; acb; clear - G1 G2 G3 G4 D B X1 X2; try acb; (first [clear - G1 X1 G2 X2 D B; lia | lia]). }
    intros a Ha. destruct Ha as [Ha|[Ha|[[Q Ha]|[Ha|[Ha|[[Q Ha]|[NP Ha]]]]]]].
    - apply APP. clear - Ha X3 X6 X7 X9 NS; try acb. lia.
    - apply APP. clear - Ha X3 X6 X8 X9; try acb. lia.
    - apply APP. clear - Ha X3 X6 X7 X8 NS; try acb. lia.
    - apply (SHW (ch_alloc_beg x) (ch_rz x / 8) a); clear - Ha X3 X6 X7 X8 X9 NS A1 RZ8; try acb; lia.
    - apply (SHW (ch_user_beg x + round_up (ch_used x) 8) ((ch_end x - (ch_user_beg x + round_up (ch_used x) 8)) / 8) a);
        clear - Ha X3 X6 X7 X8 X9 NS A3 A4; try acb; try lia; Z.div_mod_to_equations; lia.
    - apply (SHW (ch_user_beg x) (nsh (ch_used x)) a); clear - Ha X3 X6 X7 X8 X9 NS A3; try acb; try lia; unfold nsh; Z.div_mod_to_equations; lia.
    - unfold ch_lo in *. rewrite NP in *. apply (SHW (ch_alloc_beg x - kPageSize) 512 a); unfold kPageSize in *; clear - Ha X3 X6 X7 X8 X9 NS A1; try acb;
        try lia; Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma batches_after_refill : batches_rep m2 (qc_list (as_tq st2)) /\ batches_rep m2 (qc_list (as_gq st2)).
  Proof.
    change (as_tq st2) with (as_tq st). change (as_gq st2) with (as_gq st).
    pose proof R0 as RR. destruct RR as (_ & _ & _ & _ & _ & _ & _ & _ & BT & BG). pose proof BND as B.
    assert (BOK : forall b, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) ->
              0 <= qb_count b /\ 24 + 8 * qb_count b <= kBatchSize /\ qb_count b = zlen (qb_chunks b)).
    { intros b Hb. pose proof (WF_batch _ b WFs Hb) as (Q1 & Q2 & _). unfold kBatchSize, kBatchCount in *. clear - Q1 Q2; try acb. lia. }
    assert (HPB : forall b a, In b (qc_list (as_tq st) ++ qc_list (as_gq st)) ->
              (qb_addr b <= a < qb_addr b + kBatchSize \/ sh (qb_addr b) <= a < sh (qb_addr b) + kBatchSize / 8) -> outside W a).
    { intros b a Hb Hr. pose proof (batch_carved s OK b Hb) as (CV & _). change (class_size kBatchClass) with 8192 in *. unfold kBatchSize in Hr.
      destruct Hr as [Hr|Hr].
      - apply (Z_carved _ _ a CV). change (class_size kBatchClass) with 8192. exact Hr.
      - pose proof (batch_in_space s OK b Hb) as (_ & _ & M8).
        apply (Z_carved_sh _ _ (qb_addr b) 1024 a CV); change (class_size kBatchClass) with 8192; clear -Hr M8; lia. }
    split.
    - eapply (batches_rep_transport (outside W) m0 m2); [exact AGp| exact WM| | | exact BT].
      + intros b a Hb Hr. apply (HPB b a); [apply in_app_iff; left; exact Hb| exact Hr].
      + intros b Hb. apply BOK. apply in_app_iff. left. exact Hb.
    - eapply (batches_rep_transport (outside W) m0 m2); [exact AGp| exact WM| | | exact BG].
      + intros b a Hb Hr. apply (HPB b a); [apply in_app_iff; right; exact Hb| exact Hr].
      + intros b Hb. apply BOK. apply in_app_iff. right. exact Hb.
  Qed.

  (* [comment removed for export] *)
  Lemma regions_other_after_refill : forall c0, 0 <= c0 < kNumClasses -> c0 <> c ->
    region_rep s2 m2 c0 /\ pclass_rep s2 m2 c0 /\ region_shadow_rep s2 m2 c0 /\ region_junk_rep s2 m2 c0.
  Proof.
    intros c0 Hc0 NE. pose proof BND as B. destruct B as (B1 & (EP & ECA & ERI & ERB & EFA) & B3 & B4). pose proof R0 as RR. destruct RR as (_ & _ & _ & _ & _ & _ & CL & _).
    destruct (CL c0 Hc0) as (RG & PC & RSH & RJ). unfold kNumClasses in Hc0.
    pose proof (regions_disjoint st c0 c ltac:(hci; clear - Hc0; try acb; lia) ltac:(hci; clear - B1; try acb; lia) NE) as D. change (region_beg st c) with (RB s c) in D. change (region_beg st c0) with (RB s c0) in D.
    pose proof (WF_region st c0 WFs ltac:(hci; unfold kNumClasses; clear - Hc0; try acb; lia)) as RO0.
    pose proof (ro_alloc_nonneg _ _ RO0) as N1. pose proof (ro_alloc_le _ _ RO0) as N2. pose proof (ro_mapped_bound _ _ RO0) as N3.
    pose proof (ro_fa_le _ _ RO0) as N4. pose proof (ro_fa_bound _ _ RO0) as N5. pose proof (ro_numfreed _ _ RO0) as N6. unfold zlen in N6.
    assert (EFA0 : FA s c0 = RB s c0 + 3758096384) by (unfold FA, RB; rewrite free_array_base_eq; reflexivity).
    pose proof (region_in_space st c0 ltac:(hci; clear - Hc0; try acb; lia)) as RS0. change (region_beg st c0) with (RB s c0) in RS0. change (as_space_beg st) with sb in RS0.
    unfold kUserMapSize, kFreeArrayOffset, kFreeArraySize, kSpaceSize in *.
    assert (ZFA : forall a, FA s c0 <= a < FA s c0 + rg_mapped_free_array (get_region st c0) -> outside W a).
    { intros a Ha. apply Z_SPACE; clear - Ha B1 ERI ERB EFA B3 D N4 N5 N6 EFA0 RS0; try acb; lia. }
    assert (ZTL : forall a, RB s c0 + rg_allocated_user (get_region st c0) <= a < RB s c0 + rg_mapped_user (get_region st c0) -> outside W a).
    { intros a Ha. apply Z_SPACE; clear - Ha B1 ERI ERB EFA B3 D N1 N2 N3 RS0; try acb; lia. }
    assert (ZRI : forall a, a_ri s <= a < a_ri s + kPageSize -> (a + 1 <= RI \/ RI + 80 <= a) -> outside W a).
    { intros a Ha Hb. unfold a_ri, kSpaceSize, kPageSize in Ha. fold sb in Ha. apply Z_SPACE; clear - Ha Hb B1 ERI ERB EFA B3; try acb; lia. }
    split.
    { (* [comment removed for export] *)
      assert (X : region_rep s m2 c0).
      { destruct RG as (R1 & J1 & R2 & J2 & U & J3 & J4). fold st in R1, J1, R2, J2, U, J3, J4. unfold region_rep.
        Ltac trc2 H Z := first
          [ eapply (rw_cells_transport_pt (outside W) m0 m2 AGp WM); [exact H|]; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add length]
          | eapply (junk_transport_pt (outside W) m0 m2 AGp WM); [exact H|]
          | eapply (u32arr_transport_pt (outside W) m0 m2 AGp WM); [exact H|]; unfold wlist; rewrite ?length_map, ?length_rev ];
          let Ha := fresh in intros ? Ha; fold st in Ha; Z Ha.
        split; [trc2 R1 ltac:(fun Ha => apply ZRI; unfold a_ri, kSpaceSize, kPageSize, REGIONINFO_SIZE in *; clear - Ha B1 ERI Hc0 NE; try acb; lia)|].
        split; [trc2 J1 ltac:(fun Ha => apply ZRI; unfold a_ri, kSpaceSize, kPageSize, REGIONINFO_SIZE in *; clear - Ha B1 ERI Hc0 NE; try acb; lia)|].
        split; [trc2 R2 ltac:(fun Ha => apply ZRI; unfold a_ri, kSpaceSize, kPageSize, REGIONINFO_SIZE in *; clear - Ha B1 ERI Hc0 NE; try acb; lia)|].
        split; [trc2 J2 ltac:(fun Ha => apply ZRI; unfold a_ri, kSpaceSize, kPageSize, REGIONINFO_SIZE in *; clear - Ha B1 ERI Hc0 NE; try acb; lia)|].
        split; [trc2 U ltac:(fun Ha => apply ZFA; clear - Ha N4 N6; try acb; lia)|].
        split; [trc2 J3 ltac:(fun Ha => apply ZFA; clear - Ha N4 N6; try acb; lia)|].
        trc2 J4 ltac:(fun Ha => apply ZTL; clear - Ha; try acb; lia). }
      unfold region_rep in X |- *. change (a_st s2) with st2. unfold st2. rewrite (RGo c0) by (clear - Hc0 NE; try acb; lia). exact X. }
    split.
    { (* [comment removed for export] *)
      destruct PC as (Q1 & Q2 & QU & QJ). unfold pclass_rep. change (a_st s2) with st2. unfold st2. rewrite (PCo c0) by (clear - Hc0 NE; try acb; lia).
      change (as_cache_inited (refilled st c)) with true. change (a_cache s2) with CA. fold st in Q1, Q2, QU, QJ. fold CA in Q1, Q2, QU, QJ. unfold PCLASS_SIZE in *.
      pose proof (WF_cache st c0 WFs ltac:(hci; unfold kNumClasses; clear - Hc0; try acb; lia)) as CO0. pose proof (co_count _ _ CO0) as CC.
      pose proof (co_bound _ _ CO0) as CB. unfold zlen in CC.
      assert (CNT : 0 <= pc_count (get_pc st c0) <= 16).
      { pose proof (class_size_table_facts c0 ltac:(hci; clear - Hc0; try acb; lia)) as (_ & _ & _ & M & _). destruct (as_cache_inited st); clear - CC CB M; try acb; lia. }
      destruct (Z.eq_dec c0 0) as [->|NZ].
      - cbn [andb negb Z.eqb]. cbn [negb Z.eqb] in Q1, Q2. rewrite Bool.andb_false_r in Q1, Q2.
        rewrite Z.mul_0_r, Z.add_0_r in *.
        split; [eapply (rw_cells_transport_pt (outside W) m0 m2 AGp WM); [exact Q1|]; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]; intros a Ha; apply Z_PC0; clear - Ha; try acb; lia|].
        split; [eapply (rw_cells_transport_pt (outside W) m0 m2 AGp WM); [exact Q2|]; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]; intros a Ha; apply Z_PC0; clear - Ha; try acb; lia|].
        split; [eapply (u32arr_transport_pt (outside W) m0 m2 AGp WM); [exact QU|]; unfold wlist; rewrite length_map, length_rev; intros a Ha; apply Z_PC0; clear - Ha CC CNT; try acb; lia|].
        eapply (junk_transport_pt (outside W) m0 m2 AGp WM); [exact QJ|]. intros a Ha; apply Z_PC0; clear - Ha CNT; try acb; lia.
      - replace (negb (c0 =? 0)) with true by (symmetry; apply Bool.negb_true_iff, Z.eqb_neq; exact NZ). cbn [andb].
        destruct (FAM2 c0 ltac:(hci; clear - Hc0 NZ; try acb; lia)) as [F1 F2].
        apply (proj1 (rw_cells_app asegs _ _ [_] _)) in Q1. destruct Q1 as [Q1 _].
        split.
        { apply (proj2 (rw_cells_app asegs _ _ [_] _)). split.
          - eapply (rw_cells_transport_pt (outside W) m0 m2 AGp WM); [exact Q1|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add].
            intros a Ha. apply (Z_PCcnt c0); [clear - Hc0; try acb; lia| exact NE| clear - Ha; try acb; lia].
          - cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add length]. replace (CA + 80 * c0 + 4)%Z with (CA + 80 * c0 + Z.of_nat 4) in F1 by (clear; lia). exact F1. }
        split; [exact F2|].
        split; [eapply (u32arr_transport_pt (outside W) m0 m2 AGp WM); [exact QU|]; unfold wlist; rewrite length_map, length_rev; intros a Ha; apply (Z_PCarr c0); [clear - Hc0; try acb; lia| exact NE| clear - Ha CC CNT; try acb; lia]|].
        eapply (junk_transport_pt (outside W) m0 m2 AGp WM); [exact QJ|]. intros a Ha; apply (Z_PCarr c0); [clear - Hc0; try acb; lia| exact NE| clear - Ha CNT; try acb; lia]. }
    assert (ERB0 : RB s c0 = sb + c0 * 4294967296) by (unfold RB, sb, a_sb; rewrite region_beg_eq; reflexivity).
    pose proof (proj1 PL) as S64. fold sb in S64.
    pose proof (class_size_table_facts c0 ltac:(hci; clear - Hc0; try acb; lia)) as (C0 & C8 & _).
    split.
    { (* [comment removed for export] *)
      assert (X : region_shadow_rep s m2 c0).
      { apply (region_shadow_rep_frame s m0 m2 (outside W) AGp WM OK c0 ltac:(hci; unfold kNumClasses; clear - Hc0; try acb; lia)); [| | | exact RSH].
        - intros cp a Hin Ha. pose proof (carved_of_elem_any c0 cp Hc0 Hin) as CV.
          apply (Z_carved_sh _ _ (compact_to_addr st c0 cp) (class_size c0 / 8) a CV); try exact Ha.
          + clear; lia.
          + clear - C8; try acb; Z.div_mod_to_equations; lia.
          + rewrite compact_to_addr_eq. change (region_beg st c0) with (RB s c0). rewrite ERB0. clear - S64; try acb. Z.div_mod_to_equations. lia.
          + clear - C0; try acb; Z.div_mod_to_equations; lia.
        - intros a Ha. fold st in Ha.
          pose proof (ro_alloc_mod _ _ RO0) as AM. pose proof (ro_mapped_mod _ _ RO0) as MM. unfold kUserMapSize in MM.
          assert (AU8 : rg_allocated_user (get_region st c0) mod 8 = 0).
          { destruct (Z.eq_dec (class_size c0) 0) as [Z0|NZ0].
            * pose proof (ro_empty _ _ RO0 Z0) as E0. clear - E0 N1 N2; try acb. Z.div_mod_to_equations. lia.
            * specialize (AM NZ0). clear - AM C8 NZ0 N1 C0; try acb. Z.div_mod_to_equations. (first [clear - H9 H8 H4 H0 H AM C8; nia | nia]). }
          apply (Z_SH (RB s c0 + rg_allocated_user (get_region st c0)) ((rg_mapped_user (get_region st c0) - rg_allocated_user (get_region st c0)) / 8));
            try exact Ha; acb.
          + clear - N1 RS0 B1; try acb; lia.
          + rewrite ERB0. clear - S64 AU8; try acb. Z.div_mod_to_equations. lia.
          + clear - N1 N2; try acb; Z.div_mod_to_equations; lia.
          + clear - N1 N2 N3 RS0 B1; try acb; Z.div_mod_to_equations; lia.
          + clear - N1 N2 N3 D RS0 B3; try acb; Z.div_mod_to_equations; lia.
          + clear - N1 N2 N3 D RS0 B3 EFA; try acb; Z.div_mod_to_equations; lia.
        - intros a Ha. fold st in Ha. pose proof (ro_fa_mod _ _ RO0) as FM. unfold kFreeArrayMapSize in FM.
          apply (Z_SH (FA s c0) (rg_mapped_free_array (get_region st c0) / 8)); try exact Ha; acb.
          + clear - RS0 B1 EFA0; try acb; lia.
          + rewrite EFA0, ERB0. clear - S64; try acb. Z.div_mod_to_equations. lia.
          + clear - N4 N6; try acb; Z.div_mod_to_equations; lia.
          + clear - N4 N5 N6 RS0 B1 EFA0; try acb; Z.div_mod_to_equations; lia.
          + clear - N4 N5 N6 D RS0 B3 EFA0; try acb; Z.div_mod_to_equations; lia.
          + clear - N4 N5 N6 D RS0 B3 EFA EFA0; try acb; Z.div_mod_to_equations; lia. }
      unfold region_shadow_rep in X |- *. change (a_st s2) with st2. unfold st2. rewrite (RGo c0), (PCo c0) by (clear - Hc0 NE; try acb; lia).
      change (RB s2 c0) with (RB s c0). change (FA s2 c0) with (FA s c0).
      replace (compact_to_addr (refilled st c) c0) with (compact_to_addr st c0) by reflexivity. exact X. }
    (* [comment removed for export] *)
    assert (X : region_junk_rep s m2 c0).
    { apply (region_junk_rep_frame s m0 m2 (outside W) AGp WM c0 ltac:(hci; unfold kNumClasses; clear - Hc0; try acb; lia)); [| exact RJ].
      intros cp a Hin Ha. apply (Z_carved _ _ a (carved_of_elem_any c0 cp Hc0 Hin) Ha). }
    unfold region_junk_rep in X |- *. change (a_st s2) with st2. unfold st2. rewrite (RGo c0), (PCo c0) by (clear - Hc0 NE; try acb; lia).
    replace (compact_to_addr (refilled st c) c0) with (compact_to_addr st c0) by reflexivity. exact X.
  Qed.

  (* [comment removed for export] *)
  Lemma region_c_after_refill : region_rep s2 m2 c /\ pclass_rep s2 m2 c /\ region_shadow_rep s2 m2 c /\ region_junk_rep s2 m2 c.
  Proof.
    pose proof BND as B. destruct B as (B1 & (EP & ECA & ERI & ERB & EFA) & B3 & B4).
    pose proof ALN as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11).
    pose proof RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15).
    fold st in Q1, Q2, Q3, Q4, Q5, Q14, Q15. fold r in Q1, Q2, Q3, Q4, Q5, Q14, Q15.
    fold nf mfa au mu fl in Q1, Q2, Q3, Q4, Q5, Q14, Q15. fold n nnew nf1 mu' mfa' au' fl1 csz in Q1, Q2, Q3, Q4, Q5, Q14, Q15.
    pose proof R0 as RR. destruct RR as (_ & _ & _ & _ & _ & _ & CL & _). destruct (CL c ltac:(hci; unfold kNumClasses; clear - HC; try acb; lia)) as (RG & PC & RSH & RJ).
    pose proof (class_size_table_facts c ltac:(hci; clear - HC; try acb; lia)) as (_ & C32 & _). fold csz in C32.
    assert (LEN1 : length fl1 = Z.to_nat nf1) by (clear - Q2; try acb; unfold zlen in Q2; lia).
    assert (NK : (Z.to_nat n <= length fl1)%nat) by (rewrite LEN1; clear - Q1 B3; try acb; lia).
    assert (LSK : Z.of_nat (length (skipn (Z.to_nat n) fl1)) = nf1 - n) by (rewrite length_skipn, LEN1; clear - Q1 B3; try acb; lia).
    assert (LFN : Z.of_nat (length (firstn (Z.to_nat n) fl1)) = n) by (rewrite length_firstn, LEN1; clear - Q1 B3; try acb; lia).
    (* [comment removed for export] *)
    assert (ER2 : get_region st2 c = mkRegion mu' au' (nf1 - n) (skipn (Z.to_nat n) fl1) mfa') by (unfold st2; rewrite RGc; reflexivity).
    assert (EP2 : get_pc st2 c = mkPC n (firstn (Z.to_nat n) fl1)) by (unfold st2; rewrite PCc; reflexivity).
    (* [comment removed for export] *)
    assert (FSPLIT : u32arr asegs m2 (FA s c) (wlist (rev (skipn (Z.to_nat n) fl1))) /\ stk asegs m2 (FA s c + 4 * (nf1 - n)) (FA s c + 4 * nf1)).
    { pose proof FARR2 as U. rewrite <- (firstn_skipn (Z.to_nat n) fl1) in U at 1. rewrite rev_app_distr in U. unfold wlist in U |- *. rewrite map_app in U.
      apply (proj1 (u32arr_app _ _ _ _)) in U. destruct U as [U1 U2]. rewrite length_map, length_rev in U2. rewrite LSK in U2.
      split; [exact U1|]. pose proof (stk_of_u32arr _ _ _ U2) as SK. rewrite length_map, length_rev in SK. rewrite LFN in SK.
      replace (FA s c + 4 * (nf1 - n) + 4 * n) with (FA s c + 4 * nf1) in SK by (clear; lia). exact SK. }
    destruct FSPLIT as [FPRE FJ].
    (* [comment removed for export] *)
    destruct RSH as (H1 & H2 & H3 & H4). fold st r in H1, H3, H4. change (get_region st c) with r in H1, H3, H4. fold au mu mfa in H3, H4.
    assert (H3' : poisoned m2 (RB s c + au) (Z.to_nat ((mu - au) / 8)) kAsanHeapLeftRedzoneMagic).
    { eapply (poisoned_transport_pt (outside W) m0 m2 AGp WM); [exact H3|]. intros a Ha. rewrite Z2Nat.id in Ha by (clear - B3; try acb; Z.div_mod_to_equations; lia).
      apply (Z_SH (RB s c + au) ((mu - au) / 8)); try exact Ha; acb.
      + clear - B1 B3 ERB; try acb; lia.
      + rewrite ERB. clear - M9 M10; try acb. Z.div_mod_to_equations. lia.
      + clear - B3; try acb. Z.div_mod_to_equations. lia.
      + clear - B1 B3 ERB; try acb. Z.div_mod_to_equations. lia.
      + clear - B3; try acb. Z.div_mod_to_equations. lia.
      + clear - B3 EFA; try acb. Z.div_mod_to_equations. lia. }
    assert (H4' : poisoned m2 (FA s c) (Z.to_nat (mfa / 8)) kAsanHeapLeftRedzoneMagic).
    { eapply (poisoned_transport_pt (outside W) m0 m2 AGp WM); [exact H4|]. intros a Ha. rewrite Z2Nat.id in Ha by (clear - B3; try acb; Z.div_mod_to_equations; lia).
      apply (Z_SH (FA s c) (mfa / 8)); try exact Ha; acb.
      + clear - B1 B3 ERB EFA; try acb; lia.
      + rewrite EFA, ERB. clear - M9; try acb. Z.div_mod_to_equations. lia.
      + clear - B3; try acb. Z.div_mod_to_equations. lia.
      + clear - B1 B3 ERB EFA; try acb. Z.div_mod_to_equations. lia.
      + clear - B3 EFA; try acb. Z.div_mod_to_equations. lia.
      + clear - B3; try acb. Z.div_mod_to_equations. lia. }
    assert (PT : poisoned m2 (RB s c + au) (Z.to_nat ((mu' - au) / 8)) kAsanHeapLeftRedzoneMagic).
    { replace (Z.to_nat ((mu' - au) / 8)) with (Z.to_nat ((mu - au) / 8) + Z.to_nat ((mu' - mu) / 8))%nat by (clear - B3 M1 M2 M5 M10; try acb; Z.div_mod_to_equations; lia).
      apply poisoned_app; [exact H3'|]. replace (RB s c + au + 8 * Z.of_nat (Z.to_nat ((mu - au) / 8))) with (RB s c + mu) by (clear - B3 M5 M10; try acb; Z.div_mod_to_equations; lia).
      exact POIu2. }
    assert (PF : poisoned m2 (FA s c) (Z.to_nat (mfa' / 8)) kAsanHeapLeftRedzoneMagic).
    { replace (Z.to_nat (mfa' / 8)) with (Z.to_nat (mfa / 8) + Z.to_nat ((mfa' - mfa) / 8))%nat by (clear - B3 M7 M8; try acb; Z.div_mod_to_equations; lia).
      apply poisoned_app; [exact H4'|]. replace (FA s c + 8 * Z.of_nat (Z.to_nat (mfa / 8))) with (FA s c + mfa) by (clear - B3 M7; try acb; Z.div_mod_to_equations; lia).
      exact POIf2. }
    (* [comment removed for export] *)
    destruct RJ as [J1 J2]. fold st r in J1. change (get_region st c) with r in J1.
    assert (ELEM : forall cp, In cp fl1 ->
              poisoned m2 (compact_to_addr st c cp) (Z.to_nat (csz / 8)) kAsanHeapLeftRedzoneMagic /\ junk m2 (compact_to_addr st c cp) csz).
    { intros cp Hin. unfold fl1, rf_fl1 in Hin. fold nnew in Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
      - (* [comment removed for export] *)
        destruct (in_carve_cp au csz nnew cp M10 C32 ltac:(hci; clear - B3; try acb; lia) ltac:(hci; clear - B3; try acb; lia) Q3 Hin) as (j & Hj & Ecp & POS).
        assert (JA : 0 <= j * csz) by (apply Z.mul_nonneg_nonneg; clear - Hj B3; try acb; lia).
        assert (JB : (j + 1) * csz <= nnew * csz) by (apply Z.mul_le_mono_nonneg_r; clear - Hj B3; try acb; lia).
        assert (RANGE : au <= cp * 16 /\ cp * 16 + csz <= mu') by (rewrite Ecp; clear - JA JB B3 Q5 Hj; try acb; lia).
        rewrite compact_to_addr_eq. change (region_beg st c) with (RB s c). split.
        + apply (poisoned_sub _ _ _ _ _ _ PT); [clear - RANGE; try acb; lia| rewrite ERB; clear - M9; try acb; Z.div_mod_to_equations; lia|].
          clear - RANGE B3 M6 M10 C32; try acb. Z.div_mod_to_equations. lia.
        + apply junk_of_stk_range with (lo := RB s c + au) (hi := RB s c + mu'); [exact USJ2| clear - RANGE; try acb; lia| clear - RANGE; try acb; lia].
      - split.
        + eapply (poisoned_transport_pt (outside W) m0 m2 AGp WM); [exact (H1 cp Hin)|]. intros a Ha. rewrite Z2Nat.id in Ha by (clear - C32 B3; try acb; Z.div_mod_to_equations; lia).
          pose proof (carved_free st c cp WFs ltac:(hci; unfold kNumClasses; clear - HC; try acb; lia) Hin) as CV.
          apply (Z_carved_sh _ _ (compact_to_addr st c cp) (csz / 8) a CV); try (subst csz; clear - Ha C32; try acb; Z.div_mod_to_equations; lia).
          rewrite compact_to_addr_eq. change (region_beg st c) with (RB s c). rewrite ERB. clear - M9 C32; try acb. Z.div_mod_to_equations. lia.
        + eapply (junk_transport_pt (outside W) m0 m2 AGp WM); [exact (J1 cp Hin)|]. intros a Ha.
          exact (Z_carved _ _ a (carved_free st c cp WFs ltac:(hci; unfold kNumClasses; clear - HC; try acb; lia) Hin) Ha). }
    assert (INfl1 : forall cp, In cp (skipn (Z.to_nat n) fl1) \/ In cp (firstn (Z.to_nat n) fl1) -> In cp fl1).
    { intros cp H. rewrite <- (firstn_skipn (Z.to_nat n) fl1). apply in_app_iff. clear - H; try acb. tauto. }
    split.
    { (* [comment removed for export] *)
      unfold region_rep. change (a_st s2) with st2. rewrite ER2. cbn [rg_mapped_user rg_allocated_user rg_num_freed rg_free_array rg_mapped_free_array].
      change (a_ri s2) with (a_ri s). change (FA s2 c) with (FA s c). change (RB s2 c) with (RB s c). unfold REGIONINFO_SIZE. fold RI.
      split; [exact RI2|]. split; [apply junk_of_stk_eq with (hi := RI + 68); [exact RIJ2| clear; lia]|]. split; [exact EXH2|].
      split; [apply junk_of_stk_eq with (hi := RI + 128); [exact RST2| clear; lia]|].
      split; [exact FPRE|].
      split. { apply junk_of_stk_eq with (hi := FA s c + mfa'); [| clear; lia]. eapply stk_merge; [exact FJ| exact FAJ2| clear - B3; try acb; lia]. }
      apply junk_of_stk_eq with (hi := RB s c + mu'); [| clear; lia]. destruct (stk_split asegs _ _ (RB s c + au') _ USJ2 ltac:(hci; clear - B3; try acb; lia)) as [_ X]. exact X. }
    split.
    { (* [comment removed for export] *)
      unfold pclass_rep. change (a_st s2) with st2. rewrite EP2. cbn [pc_count pc_chunks]. change (as_cache_inited st2) with true. change (a_cache s2) with CA.
      replace (negb (c =? 0)) with true by (symmetry; apply Bool.negb_true_iff, Z.eqb_neq; clear - HC; try acb; lia). cbn [andb]. unfold PCLASS_SIZE. fold P.
      destruct (FAM2 c ltac:(hci; clear - HC; try acb; lia)) as [F1 F2]. change (CA + 80 * c) with P in F1, F2.
      split. { apply (proj2 (rw_cells_app asegs _ _ [_] _)). split; [exact PCN|]. cbn [cells_size csize Nat.add length]. replace (P + Z.of_nat 4) with (P + 4) by (clear; lia). exact F1. }
      split; [exact F2|]. split; [exact CHA|]. apply junk_of_stk_eq with (hi := P + 80); [exact CHJ| clear; lia]. }
    split.
    { (* [comment removed for export] *)
      unfold region_shadow_rep. change (a_st s2) with st2. rewrite ER2, EP2. cbn [rg_mapped_user rg_allocated_user rg_free_array rg_mapped_free_array pc_chunks].
      change (RB s2 c) with (RB s c). change (FA s2 c) with (FA s c). replace (compact_to_addr st2 c) with (compact_to_addr st c) by reflexivity. fold csz.
      split; [intros cp Hin; apply (proj1 (ELEM cp ltac:(hci; apply INfl1; left; exact Hin)))|].
      split; [intros cp Hin; apply (proj1 (ELEM cp ltac:(hci; apply INfl1; right; exact Hin)))|].
      split; [| exact PF].
      apply (poisoned_sub _ _ _ _ _ _ PT).
      + clear - B3; try acb; lia.
      + rewrite ERB. clear - M9 M11; try acb. Z.div_mod_to_equations. lia.
      + clear - B3 M6 M10 M11; try acb. Z.div_mod_to_equations. lia. }
    (* [comment removed for export] *)
    unfold region_junk_rep. change (a_st s2) with st2. rewrite ER2, EP2. cbn [rg_free_array pc_chunks].
    replace (compact_to_addr st2 c) with (compact_to_addr st c) by reflexivity. fold csz.
    split; [intros cp Hin; apply (proj2 (ELEM cp ltac:(hci; apply INfl1; left; exact Hin)))| intros cp Hin; apply (proj2 (ELEM cp ltac:(hci; apply INfl1; right; exact Hin)))].
  Qed.

  (* [comment removed for export] *)
  Theorem arep_after_refill : AREP s2 m2.
  Proof.
    destruct statics_after_refill as (I1 & I2 & I3 & I4). destruct batches_after_refill as [BT BG].
    split; [exact OK2|]. split; [exact I1|]. split; [exact I2|]. split; [exact thread_after_refill|]. split; [exact I4|]. split; [exact I3|].
    split.
    { intros c0 Hc0. destruct (Z.eq_dec c0 c) as [->|NE]; [exact region_c_after_refill| exact (regions_other_after_refill c0 Hc0 NE)]. }
    split; [exact chunks_after_refill|]. split; [exact BT| exact BG].
  Qed.

  (* [comment removed for export] *)
  Lemma flagsx_after_refill : flagsx_rep m0 -> flagsx_rep m2.
  Proof.
    intros (X1 & X2 & [g X3] & X4 & [b X5]). pose proof BND as B.
    assert (ZI : forall a, 65536 <= a < 12599296 -> outside W a) by (intros a Ha; bands_as (BT & _); clear - Ha B BT; try acb; wsplit).   (* [comment removed for export] *)
    unfold flagsx_rep, ALIBCPGSZ, AGOT_SSP, ASSPGUARD, ACFLAGS in *.
    Ltac trx H Z := eapply (rw_cells_transport_pt (outside W) m0 m2 AGp WM); [exact H|];
                  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add length]; let Ha := fresh in intros ? Ha; apply Z; clear - Ha; try acb; lia.
    split; [trx X1 ZI|]. split; [trx X2 ZI|]. split; [exists g; trx X3 ZI|]. split; [trx X4 ZI|]. exists b; trx X5 ZI.
  Qed.
End ArepAfterRefill.

