(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel Target Prog.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Definition SJ_OPDEL_SIZED : Z := 0x7b870.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma RHEAP_pull : forall s l1 b l2 m, RHEAP s (l1 ++ b :: l2) m -> RHEAP s (b :: l1 ++ l2) m.
Proof. intros s l1 b l2 m H. eapply RHEAP_perm; [exact H|]. symmetry. apply Permutation_middle. Qed.

Lemma LH_head_disj : forall s p A n LB m, RHEAP s ((p, A, n) :: LB) m ->
  forall a, in_block LB a -> ~ (A <= a < A + n).
Proof.
  intros s p A n LB m H a (b & Hb & Hr) Ha.
  pose proof (LH_nodup _ _ _ H) as ND. cbn [map blk_id fst snd] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI _].
  assert (NE : p <> blk_id b) by (intros E; apply NI; rewrite E; apply in_map; exact Hb).
  pose proof (LH_disjoint _ _ _ (p, A, n) b H ltac:(left; reflexivity) ltac:(right; exact Hb)) as DJ.
  cbn [blk_addr blk_size blk_id fst snd] in DJ. specialize (DJ NE). lia.
Qed.

Lemma LH_head_sep : forall s p A n LB m p' A' n', RHEAP s ((p, A, n) :: LB) m -> In (p', A', n') LB ->
  A + n <= A' \/ A' + n' <= A.
Proof.
  intros s p A n LB m p' A' n' H Hb.
  pose proof (LH_nodup _ _ _ H) as ND. cbn [map blk_id fst snd] in ND. apply NoDup_cons_iff in ND. destruct ND as [NI _].
  assert (NE : p <> p') by (intros E; apply NI; rewrite E; apply (in_map blk_id _ _ Hb)).
  pose proof (LH_disjoint _ _ _ (p, A, n) (p', A', n') H ltac:(left; reflexivity) ltac:(right; exact Hb)) as DJ.
  cbn [blk_addr blk_size blk_id fst snd] in DJ. specialize (DJ NE). lia.
Qed.

Lemma in_block_cons : forall b LB a, in_block LB a -> in_block (b :: LB) a.
Proof. intros b LB a (b' & Hb & Hr). exists b'. split; [right; exact Hb| exact Hr]. Qed.
Lemma in_block_incl : forall LB LB' a, (forall b, In b LB -> In b LB') -> in_block LB a -> in_block LB' a.
Proof. intros LB LB' a H (b & Hb & Hr). exists b. split; [apply H; exact Hb| exact Hr]. Qed.
Lemma in_block_hd : forall p A n LB a, A <= a < A + n -> in_block ((p, A, n) :: LB) a.
Proof. intros p A n LB a H. exists (p, A, n). split; [left; reflexivity| exact H]. Qed.

Lemma lx_pres_mono : forall LB SP X LB' SP' X' m m',
  lx_pres LB SP X m m' -> (forall a, 0 <= a < 2^64 -> lx_client LB' SP' X' a -> lx_client LB SP X a) -> lx_pres LB' SP' X' m m'.
Proof. intros LB SP X LB' SP' X' m m' H HC a Ha Hc. apply H; [exact Ha| apply HC; assumption]. Qed.

Lemma le4_of_bytes : forall b0 b1 b2 b3 : byte, exists w : word, le4 w = [b0; b1; b2; b3].
Proof.
  intros b0 b1 b2 b3.
  pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
  pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
  change (bv_modulus 8) with 256 in *.
  set (z := bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * bv_unsigned b3))).
  exists (Z_to_bv 64 z). unfold le4. rewrite unsigned_lit by (subst z; lia). cbn [Z_to_le_bytes].
  rewrite !Z.shiftr_div_pow2 by lia. change (2^8) with 256.
  assert (E1 : z / 256 = bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * bv_unsigned b3))
    by (symmetry; apply (Z.div_unique_pos z 256 _ (bv_unsigned b0)); subst z; lia).
  rewrite E1.
  assert (E2 : (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * bv_unsigned b3)) / 256 = bv_unsigned b2 + 256 * bv_unsigned b3)
    by (symmetry; apply (Z.div_unique_pos _ 256 _ (bv_unsigned b1)); lia).
  rewrite E2.
  assert (E3 : (bv_unsigned b2 + 256 * bv_unsigned b3) / 256 = bv_unsigned b3)
    by (symmetry; apply (Z.div_unique_pos _ 256 _ (bv_unsigned b2)); lia).
  rewrite E3.
  assert (BY : forall (b : byte) r, 0 <= bv_unsigned b < 256 -> Z_to_bv 8 (bv_unsigned b + 256 * r) = b).
  { intros b r Hb. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    replace (bv_unsigned b + 256 * r) with (bv_unsigned b + r * 256) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. exact Hb. }
  subst z. rewrite !BY by assumption. replace (bv_unsigned b3) with (bv_unsigned b3 + 256 * 0) by lia. rewrite BY by assumption. reflexivity.
Qed.

Lemma u32s_of_bytes : forall (k : nat) (bs : list byte), length bs = (4 * k)%nat -> exists ws, u32s ws = bs /\ length ws = k.
Proof.
  induction k as [|k IH]; intros bs L.
  - destruct bs; [|discriminate]. exists []. split; reflexivity.
  - destruct bs as [|b0 [|b1 [|b2 [|b3 r]]]]; cbn [length] in L; try lia.
    destruct (IH r ltac:(lia)) as (ws & E & LW). destruct (le4_of_bytes b0 b1 b2 b3) as (w & Ew).
    exists (w :: ws). split; [cbn [u32s]; rewrite Ew, E; reflexivity| cbn [length]; lia].
Qed.

Lemma u32arr_of_block : forall m A n (bs : list byte) (k : nat), rw_cells usegs m A [CB n bs] -> n = (4 * k)%nat ->
  exists ws, u32arr usegs m A ws /\ length ws = k.
Proof.
  intros m A n bs k H E. pose proof (u8arr_of_rw_cells usegs m A n bs H) as [HB HW].
  destruct H as [[[HL _] _] _]. cbn [cell_wf] in HL. destruct (u32s_of_bytes k bs ltac:(lia)) as (ws & Ews & LW).
  exists ws. split; [| exact LW]. split; [rewrite Ews; exact HB|]. rewrite LW. replace (4 * Z.of_nat k) with (Z.of_nat (length bs)) by lia. exact HW.
Qed.

Lemma rw_cells_C2_split : forall m A pre post,
  rw_cells usegs m A (pre ++ C2 (Z_to_bv 64 0) :: post) -> rw_cells usegs m A (pre ++ C1 (Z_to_bv 8 0) :: C1 (Z_to_bv 8 0) :: post).
Proof.
  intros m A pre post H. eapply rw_cells_recast; [exact H| | |].
  - destruct H as [[Hwf _] _]. apply cells_wf_app in Hwf. destruct Hwf as [W1 W2]. apply cells_wf_app. split; [exact W1|].
    cbn in W2 |- *. tauto.
  - rewrite !cells_bytes_app. f_equal.
  - rewrite !cells_size_app. f_equal.
Qed.

Definition impl_cells16 (vptr nsi : word) (p12 : list byte) (idx nxt : word) (p28 : list byte) (cap md : word) (b48 b49 : byte)
    (p50 : list byte) (oc ia bufv lenv docv : word) : list cell :=
  [C8 vptr; C4 nsi; CB 4 p12; C8 idx; C4 nxt; CB 4 p28; C8 cap; C8 md; C1 b48; C1 b49; CB 6 p50; C8 oc; C8 ia; C8 bufv; C8 lenv; C8 docv].

Lemma lx_pres_sub : forall LB q X LB1 q1 X1 m m',
  lx_pres LB1 q1 X1 m m' -> q1 <= q -> (forall b, In b LB -> In b LB1) ->
  (forall a, rin_ivs X1 a -> ~ rin_ivs X a -> a < q /\ ~ in_block LB a /\ ~ (0xd6000 <= a < 0x111000)) ->
  lx_pres LB q X m m'.
Proof.
  intros LB q X LB1 q1 X1 m m' H Hq HL HX. eapply lx_pres_mono; [exact H|].
  intros a Ha [HXa HC]. split.
  - intros HX1. destruct (HX a HX1 HXa) as (L1 & L2 & L3). destruct HC as [HC|[HC|[HC _]]]; [lia| exact (L2 HC)| exact (L3 HC)].
  - destruct HC as [HC|[HC|HC]]; [left; lia| right; left; eapply in_block_incl; [exact HL| exact HC]| right; right; exact HC].
Qed.

Lemma u32arr_agree : forall P m m' A ws,
  agree_on P m m' -> u32arr usegs m A ws -> (forall a, A <= a < A + 4 * Z.of_nat (length ws) -> P a) -> u32arr usegs m' A ws.
Proof.
  intros P m m' A ws HP [HB HW] HR. split.
  - eapply bytes_at_agree; [exact HP| exact HB|]. rewrite u32s_length. intros a Ha. apply HR. lia.
  - eapply wr_at_agree; [exact HP| exact HW| exact HR].
Qed.
Lemma u8arr_agree : forall P m m' A bs,
  agree_on P m m' -> u8arr usegs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> P a) -> u8arr usegs m' A bs.
Proof.
  intros P m m' A bs HP [HB HW] HR. split.
  - eapply bytes_at_agree; [exact HP| exact HB| exact HR].
  - eapply wr_at_agree; [exact HP| exact HW| exact HR].
Qed.

Definition p48_cells (nas : byte) (j57 : list byte) (lb lcap : word) : list cell :=
  [C8 (Z_to_bv 64 4294967295); C1 nas; CB 7 j57; C8 lb; C8 lcap].

Definition hpost (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (lo B : Z) (R : word -> PState -> mem -> Prop) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m' /\ stk usegs m' lo q
    /\ (exists errv' : word, rw_cells usegs m' LX_ERRNO [C4 errv'])
    /\ rauxv_ok m' B
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ R a0 s' m'.

Definition hpostF (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (s : PState) (lo B : Z) (R : word -> PState -> mem -> Prop) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom usegs)
    /\ frm0 fc'
    /\ mem_inv usegs m' /\ stk usegs m' lo q
    /\ (exists errv' : word, rw_cells usegs m' LX_ERRNO [C4 errv'])
    /\ rauxv_ok m' B
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ R a0 s' m'.

Lemma rw_cells_unmerge : forall m A pre mid post,
  rw_cells usegs m A (pre ++ CB (cells_size mid) (cells_bytes mid) :: post) -> cells_wf mid -> rw_cells usegs m A (pre ++ mid ++ post).
Proof.
  intros m A pre mid post H Hm. eapply rw_cells_recast; [exact H| | |].
  - destruct H as [[Hwf _] _]. apply cells_wf_app in Hwf. destruct Hwf as [W1 W2]. cbn [cells_wf] in W2. destruct W2 as [_ W3].
    apply cells_wf_app. split; [exact W1|]. apply cells_wf_app. split; [exact Hm| exact W3].
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. reflexivity.
  - rewrite !cells_size_app. cbn [cells_size csize]. reflexivity.
Qed.

Section Proofs.
  Hypothesis HF : rfree_stmt.
  Lemma opdel_sized_proof : opdel_stmt SJ_OPDEL_SIZED.
  Proof.
    unfold opdel_stmt, SJ_OPDEL_SIZED. intros until errv. intros HEAP IN AUX QB ST CEIL LO ERR MI Hq.
    unfold del. cbn [lib_free lops Target.ops lib_free_opt].
    unfold implM. iprefix. step. step. ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply (free_callZ HF) with (B := B) (lo := lo) (A := A) (n := n); eassumption.
  Qed.
End Proofs.
End WithCeiling0.

Ltac to_implM :=
  lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
    lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.

Ltac fix_lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) =>
           change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
           change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
           change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
       end).
Ltac hstep := step; fix_lit_store.

Definition keepP (P : Prop) : Prop := P.
Ltac hide H := lazymatch type of H with ?T => change (keepP T) in H end.
Ltac unhide H := unfold keepP in H.
