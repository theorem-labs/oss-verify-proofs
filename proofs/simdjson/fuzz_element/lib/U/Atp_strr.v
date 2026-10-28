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
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim STree Malloc Monad Stdio StrFun SjModel AtpModel Target Prog AtpImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_new_t2 Sj_h_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_num_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import F_memchr F_memcmp F_strlen F_memcpy F_memmove_t2 Atp_defs Atp_str.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition replace_post (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo S : Z) (lg : bool) (A cap sz : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(q - 80, q); (S, S + 24); (A, A + cap)] m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo q
    /\ lstr m' S lg A cap (sz - 1).

Lemma u8arr_split : forall m A (bs : list byte) k, u8arr usegs m A bs -> (k <= length bs)%nat ->
  u8arr usegs m A (firstn k bs) /\ u8arr usegs m (A + Z.of_nat k) (skipn k bs).
Proof.
  intros m A bs k [HB HW] Hk. rewrite <- (firstn_skipn k bs) in HB. apply bytes_at_app in HB. destruct HB as [B1 B2].
  rewrite firstn_length_le in B2 by lia. destruct (wr_at_split usegs m A _ (Z.of_nat k) HW ltac:(lia)) as [W1 W2].
  split; split; [exact B1| rewrite firstn_length_le by lia; exact W1| exact B2|].
  rewrite length_skipn. replace (Z.of_nat (length bs - k)) with (Z.of_nat (length bs) - Z.of_nat k) by lia. exact W2.
Qed.

Lemma long_word0 : forall cap, cap mod 2 = 0 -> Z.land (cap + 1) 1 = 1.
Proof. intros cap HE. rewrite land1_mod2. lia. Qed.

Lemma rw_CB_bytes : forall m A n (l : list byte), rw_cells usegs m A [CB n l] -> bytes_at usegs m A l /\ length l = n.
Proof.
  intros m A n l [[W B] _]. cbn [cells_wf cell_wf cells_bytes cbytes app] in W, B. rewrite app_nil_r in B. split; [exact B| tauto].
Qed.

Lemma nth_upd_same : forall (l : list byte) i (b d : byte), (i < length l)%nat -> nth i (upd l i b) d = b.
Proof.
  intros l i b d Hi. apply nth_error_nth. apply nth_error_upd_same. exact Hi.
Qed.

Lemma land1_lor_shiftl8 : forall x y, Z.land (Z.lor x (Z.shiftl y 8)) 1 = Z.land x 1.
Proof.
  intros x y. apply Z.bits_inj'. intros n Hn.
  rewrite !Z.land_spec, Z.lor_spec.
  destruct (Z.eq_dec n 0) as [->|NZ].
  - rewrite Z.shiftl_spec_low by lia. rewrite Bool.orb_false_r. reflexivity.
  - replace (Z.testbit 1 n) with false by (symmetry; apply (Z.bits_above_log2 1 n); [lia| cbn; lia]).
    rewrite !Bool.andb_false_r. reflexivity.
Qed.

Lemma le_word_bit0 : forall (b : byte) (l : list byte),
  Z.land (bv_unsigned (bv_extract 0 64 (le_bytes_to_word (b :: l)))) 1 = Z.land (bv_unsigned b) 1.
Proof.
  intros b l. rewrite bv_extract_unsigned, Z.shiftr_0_r.
  unfold le_bytes_to_word. rewrite Z_to_bv_unsigned. cbn [bytes_le_to_Z].
  unfold bv_wrap. change (bv_modulus 64) with (2^64)%Z.
  rewrite <- !(Z.land_ones _ 64) by lia.
  rewrite <- !Z.land_assoc. change (Z.land (Z.ones 64) (Z.land (Z.ones 64) 1)) with 1.
  apply land1_lor_shiftl8.
Qed.

Lemma short_hdr_read8 : forall m S (hb : byte) (bs : list byte),
  rw_cells usegs m S [C1 hb] -> u8arr usegs m (S + 1) bs -> (7 <= length bs)%nat ->
  ov_read_bytes usegs m (wa S) 8 = Some (hb :: firstn 7 bs).
Proof.
  intros m S hb bs [[_ HB] _] [BS _] HL. cbn [cells_bytes cbytes app] in HB.
  assert (X : bytes_at usegs m S (hb :: bs)).
  { apply (proj2 (bytes_at_app usegs m S [hb] bs)). split; [exact HB|]. cbn [length Z.of_nat Pos.of_succ_nat]. exact BS. }
  pose proof (bytes_at_read usegs m S _ 0 8 X ltac:(lia) ltac:(cbn [length]; lia)) as R.
  rewrite Z.add_0_r in R. rewrite R. reflexivity.
Qed.

Lemma lstr_frame : forall W m m' S (lg : bool) A cap sz,
  lstr m S lg A cap sz -> munch W m m' -> wmono usegs m m' -> disjoint_from W S 24 -> disjoint_from W A cap -> lstr m' S lg A cap sz.
Proof.
  intros W m m' S lg A cap sz (SZ0 & SZC & CAP & A0 & AC & (bs & BS & LBS & NUL) & REP) MU WM DS DA.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split.
  - exists bs. split; [| split; [exact LBS| exact NUL]]. eapply u8arr_transport; [exact BS| exact MU| exact WM| rewrite LBS; exact DA].
  - assert (DS' : forall n, 0 <= n <= 24 -> disjoint_from W S n).
    { intros n Hn. clear - DS Hn. induction W as [|[lo hi] W IH]; [exact I|]. destruct DS as [D1 D2]. split; [lia| exact (IH D2)]. }
    destruct lg; [destruct REP as [HDR EV]| destruct REP as (HDR & EA & ECAP)].
    + split; [| exact EV]. eapply rw_cells_transport; [exact HDR| exact MU| exact WM| apply DS'; cbn; lia].
    + split; [| split; [exact EA| exact ECAP]]. eapply rw_cells_transport; [exact HDR| exact MU| exact WM| apply DS'; cbn; lia].
Qed.

Lemma le1_smallZ : forall v, (0 <= v < 256)%Z -> le1 (Z_to_bv 64 v) = [Z_to_bv 8 v].
Proof. intros v Hv. unfold le1. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes]. reflexivity. Qed.

Definition shdr (m : mem) (S : Z) (lg : bool) (A cap sz : Z) : Prop :=
  if lg then rw_cells usegs m S [C8 (Z_to_bv 64 (cap + 1)); C8 (Z_to_bv 64 sz); C8 (Z_to_bv 64 A)] /\ cap mod 2 = 0
  else rw_cells usegs m S [C1 (Z_to_bv 8 (2 * sz))] /\ A = S + 1 /\ cap = 23.

Lemma replace4_mid : forall (ra gp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 xt6 xa1 xa3 xa4 a5 a6 a7 xs6 xs7 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : mem) (q lo S : Z) (lg : bool) (A cap sz pos lit c : Z)
    (l1 l4 : list byte) (b1 b0 : byte) (src : list byte),
  shdr m S lg A cap sz -> 0 <= pos -> pos + 2 <= sz -> sz < cap -> cap < 2^40 -> 0 < A -> A + cap < 2^63 ->
  rw_cells usegs m A [CB (Z.to_nat pos) l1] -> rw_cells usegs m (A + pos) [CB 1 [b1]] ->
  u8arr usegs m (A + pos + 1) (b0 :: src) -> Z.of_nat (length src) = sz - pos - 2 ->
  rw_cells usegs m (A + sz) [CB (Z.to_nat (cap - sz)) l4] -> wr_at usegs m A cap ->
  bytes_at usegs m lit [Z_to_bv 8 c] -> 0 < c < 256 -> 0 < lit -> lit + 16 <= lo -> (A + cap <= lit \/ lit + 16 <= A) ->
  q <= S -> S + 24 < 2^63 -> (lg = true -> A + cap <= lo) ->
  rw_cells usegs m (q + -80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk usegs m lo (q + -80) -> lo <= q - 80 -> mem_inv usegs m ->
  munch [(q - 80, q); (S, S + 24); (A, A + cap)] m0 m -> wmono usegs m0 m ->
  evt usegs (replace_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo S lg A cap sz m0)
    (MS (mkR t0 (Z_to_bv 64 (q + -80)) gp (Z_to_bv 64 RATP) t1 t2 t3
             (Z_to_bv 64 S) (Z_to_bv 64 1)
             (Z_to_bv 64 (sz - pos)) xa1 (Z_to_bv 64 2) xa3 xa4 a5 a6 a7
             (Z_to_bv 64 sz) (Z_to_bv 64 lit) (Z_to_bv 64 2) (Z_to_bv 64 pos) xs6 xs7 (Z_to_bv 64 A) s9 s10 s11 t4 t5 t6 xt6)
        F (Z_to_bv 64 0x7d388) fc None m (seg_rom usegs)).
Proof.
  intros until src. intros HDR POS PS SZC CAP A0 AC P1 P2 P3 LSRC P4 WR LIT1 CR L0 LLO LSEP QS S63 ASEP FR ST LO MI MU WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).

  assert (END : forall (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 xs6' xs7' x28 x29 x30 x31 x32 : word) (m2 : mem) (bsx : list byte),
    shdr m2 S lg A cap (sz - 1) -> u8arr usegs m2 A bsx -> Z.of_nat (length bsx) = cap ->
    rw_cells usegs m2 (q + -80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk usegs m2 lo (q + -80) -> mem_inv usegs m2 ->
    munch [(q - 80, q); (S, S + 24); (A, A + cap)] m0 m2 -> wmono usegs m0 m2 ->
    evt usegs (replace_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo S lg A cap sz m0)
      (MS (mkR x5 (Z_to_bv 64 (q + -80)) gp (Z_to_bv 64 RATP) x6 x7 x28
               (Z_to_bv 64 S) (Z_to_bv 64 1) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 (sz - 1)) (Z_to_bv 64 lit) (Z_to_bv 64 2) (Z_to_bv 64 pos) xs6' xs7' (Z_to_bv 64 A) s9 s10 s11 x29 x30 x31 x32)
          F (Z_to_bv 64 0x7d454) fc None m2 (seg_rom usegs))).
  { intros x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 xs6' xs7' x28 x29 x30 x31 x32 m2 bsx HDR2 DA LBS FR2 ST2 MI2 MU2 WM2.
    unfold shdr in HDR2.

    astep.
    pose proof (u8arr_store_ok usegs _ _ _ (sz - 1) (Z_to_bv 64 (A + (sz - 1))) DA ltac:(lia) ltac:(reflexivity)) as SOK.
    destruct lg; [destruct HDR2 as [HDR2 EV]; specialize (ASEP eq_refl)| destruct HDR2 as (HDR2 & EA & ECAP)].
    all: step; change (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0];
         change (write_to_mem m2 (Z_to_bv 64 (A + (sz - 1)))) with (write_to_mem m2 (wa (A + (sz - 1)))).
    all: pose proof (u8arr_write usegs _ _ _ (sz - 1) (Z_to_bv 8 0) DA ltac:(lia)) as DA2; clear DA; store_done; name_mem m3.

    all: step; do 10 step; step; release_frame FR2 ST2 q; step.
    all: apply evt_done; unfold replace_post; do 15 eexists; exists m3; split; [atp_st_eq_goal|].
    all: split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [assumption|].
    all: unfold lstr; split; [lia|]; split; [lia|]; split; [lia|]; split; [lia|]; split; [lia|].
    all: split; [exists (upd bsx (Z.to_nat (sz - 1)) (Z_to_bv 8 0)); split; [exact DA2|]; split; [rewrite upd_length; lia| apply nth_upd_same; lia]|].
    - split; [exact HDR2| exact EV].
    - split; [exact HDR2| split; [exact EA| exact ECAP]]. }

  pose proof (rw_CB_bytes _ _ _ _ P1) as [B1 L1].
  pose proof (rw_cells_bound _ _ _ _ P1) as PB1.

  unfold shdr in HDR. destruct lg; [destruct HDR as [HDR EV]; specialize (ASEP eq_refl)| destruct HDR as (HDR & EA & ECAP)].
  -

    step. if_cases KT; zify_cond KT.
    +
      assert (ESZ : sz = pos + 2) by lia.
      destruct src as [|? ?]; [| cbn [length] in LSRC; lia].
      step. if_false. astep. step. step. step.
      call memmove_far_callZ.
      1:{ exact LIT1. }
      1:{ reflexivity. }
      1:{ exact P2. }
      all: try lia. 1:{ assumption. }
      name_mem m2. rename PC into P2'. clear POST.

      lazymatch type of HDR with rw_cells _ ?mx _ _ => pose proof (rw_cells_C8_read1 mx _ _ _ HDR) as RD1 end.
      astep. rewrite zx8_lit by lia. astep. astep. rewrite long_byte0 by lia. astep. step. if_true.
      hstep. step. name_mem m3.
      lazymatch type of HDR with rw_cells _ _ _ [_; C8 (Z_to_bv 64 ?x); _] => replace x with (sz - 1) in HDR by lia end.
      pose proof (rw_CB_bytes _ _ _ _ P2') as [B2 _]. pose proof (rw_CB_bytes _ _ _ _ P4) as [B4 L4]. destruct P3 as [B3 _].
      lazymatch goal with H : bytes_at usegs m3 A l1 |- _ => rename H into B1' end.
      assert (DA : u8arr usegs m3 A (l1 ++ [Z_to_bv 8 c] ++ [b0] ++ l4)).
      { split.
        - apply (proj2 (bytes_at_app _ _ _ _ _)). split; [exact B1'|]. rewrite L1, Z2Nat.id by lia.
          apply (proj2 (bytes_at_app _ _ _ _ _)). split; [exact B2|]. cbn [length Z.of_nat Pos.of_succ_nat].
          apply (proj2 (bytes_at_app _ _ _ _ _)). split; [exact B3|]. cbn [length Z.of_nat Pos.of_succ_nat].
          replace (A + pos + 1 + 1) with (A + sz) by lia. exact B4.
        - rewrite !length_app, L1, L4. cbn [length].
          replace (Z.of_nat (Z.to_nat pos + (1 + (1 + Z.to_nat (cap - sz))))) with cap by lia. assumption. }
      eapply evt_eq; [| eapply (END _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 _ ltac:(unfold shdr; split; [exact HDR| exact EV]) DA)];
        [atp_st_eq| rewrite !length_app, L1, L4; cbn [length]; lia| assumption| assumption| assumption| assumption| assumption].
    +
      astep. astep. step. if_false. step. if_false. step. step. step. step.
      call memmove_far_callZ.
      1:{ exact LIT1. }
      1:{ reflexivity. }
      1:{ exact P2. }
      all: try lia. 1:{ assumption. }
      name_mem m2. rename PC into P2'. clear POST.

      astep. astep. step. step.
      eapply evt_cut.
      { eapply memmove_left1_spec with (D := A + pos + 1) (b0 := b0) (src := src);
          [atp_st_eq_leaf| atp_st_eq_leaf| f_equal; lia| exact P3| assumption| lia| lia]. }
      post_call usegs m2. name_mem m3. unfold left1_bytes in *.
      lazymatch goal with H : u8arr usegs m3 (A + pos + 1) _ |- _ => rename H into P3' end.

      lazymatch type of HDR with rw_cells _ ?mx _ _ => pose proof (rw_cells_C8_read1 mx _ _ _ HDR) as RD1 end.
      astep. rewrite zx8_lit by lia. astep. astep. rewrite long_byte0 by lia. astep. step. if_false.
      hstep. step. name_mem m4.
      lazymatch type of HDR with rw_cells _ _ _ [_; C8 (Z_to_bv 64 ?x); _] => replace x with (sz - 1) in HDR by lia end.
      pose proof (rw_CB_bytes _ _ _ _ P2') as [B2 _]. pose proof (rw_CB_bytes _ _ _ _ P4) as [B4 L4]. destruct P3' as [B3 _].
      lazymatch goal with H : bytes_at usegs m4 A l1 |- _ => rename H into B1' end.
      assert (DA : u8arr usegs m4 A (l1 ++ [Z_to_bv 8 c] ++ (src ++ [nth (length src) (b0 :: src) b0]) ++ l4)).
      { split.
        - apply (proj2 (bytes_at_app _ _ _ _ _)). split; [exact B1'|]. rewrite L1, Z2Nat.id by lia.
          apply (proj2 (bytes_at_app _ _ _ _ _)). split; [exact B2|]. cbn [length Z.of_nat Pos.of_succ_nat].
          apply (proj2 (bytes_at_app _ _ _ _ _)). split; [exact B3|]. rewrite length_app. cbn [length].
          replace (A + pos + 1 + Z.of_nat (length src + 1)) with (A + sz) by lia. exact B4.
        - rewrite !length_app, L1, L4. cbn [length].
          replace (Z.of_nat (Z.to_nat pos + (1 + (length src + 1 + Z.to_nat (cap - sz))))) with cap by lia. assumption. }
      eapply evt_eq; [| eapply (END _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 _ ltac:(unfold shdr; split; [exact HDR| exact EV]) DA)];
        [atp_st_eq| rewrite !length_app, L1, L4; cbn [length]; lia| assumption| assumption| assumption| assumption| assumption].
  -
    step. if_cases KT; zify_cond KT.
    + assert (ESZ : sz = pos + 2) by lia.
      destruct src as [|? ?]; [| cbn [length] in LSRC; lia].
      step. if_false. astep. step. step. step.
      call memmove_far_callZ.
      1:{ exact LIT1. }
      1:{ reflexivity. }
      1:{ exact P2. }
      all: try lia. 1:{ assumption. }
      name_mem m2. rename PC into P2'. clear POST.

      astep. astep. astep. rewrite short_byte0. astep. step. if_false.
      astep. step. rewrite le1_smallZ by lia. mem_after_store. name_mem m3.
      lazymatch type of HDR with rw_cells _ _ _ [C1 (Z_to_bv 8 ?x)] => replace x with (2 * (sz - 1)) in HDR by lia end.
      pose proof (rw_CB_bytes _ _ _ _ P2') as [B2 _]. pose proof (rw_CB_bytes _ _ _ _ P4) as [B4 L4]. destruct P3 as [B3 _].
      lazymatch goal with H : bytes_at usegs m3 A l1 |- _ => rename H into B1' end.
      assert (DA : u8arr usegs m3 A (l1 ++ [Z_to_bv 8 c] ++ [b0] ++ l4)).
      { split.
        - apply (proj2 (bytes_at_app _ _ _ _ _)). split; [exact B1'|]. rewrite L1, Z2Nat.id by lia.
          apply (proj2 (bytes_at_app _ _ _ _ _)). split; [exact B2|]. cbn [length Z.of_nat Pos.of_succ_nat].
          apply (proj2 (bytes_at_app _ _ _ _ _)). split; [exact B3|]. cbn [length Z.of_nat Pos.of_succ_nat].
          replace (A + pos + 1 + 1) with (A + sz) by lia. exact B4.
        - rewrite !length_app, L1, L4. cbn [length].
          replace (Z.of_nat (Z.to_nat pos + (1 + (1 + Z.to_nat (cap - sz))))) with cap by lia. assumption. }
      eapply evt_eq; [| eapply (END _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 _ ltac:(unfold shdr; split; [exact HDR| split; [exact EA| exact ECAP]]) DA)];
        [atp_st_eq| rewrite !length_app, L1, L4; cbn [length]; lia| assumption| assumption| assumption| assumption| assumption].
    + astep. astep. step. if_false. step. if_false. step. step. step. step.
      call memmove_far_callZ.
      1:{ exact LIT1. }
      1:{ reflexivity. }
      1:{ exact P2. }
      all: try lia. 1:{ assumption. }
      name_mem m2. rename PC into P2'. clear POST.
      astep. astep. step. step.
      eapply evt_cut.
      { eapply memmove_left1_spec with (D := A + pos + 1) (b0 := b0) (src := src);
          [atp_st_eq_leaf| atp_st_eq_leaf| f_equal; lia| exact P3| assumption| lia| lia]. }
      post_call usegs m2. name_mem m3. unfold left1_bytes in *.
      lazymatch goal with H : u8arr usegs m3 (A + pos + 1) _ |- _ => rename H into P3' end.

      astep. astep. astep. rewrite short_byte0. astep. step. if_true.
      astep. step. rewrite le1_smallZ by lia. mem_after_store. name_mem m4.
      lazymatch type of HDR with rw_cells _ _ _ [C1 (Z_to_bv 8 ?x)] => replace x with (2 * (sz - 1)) in HDR by lia end.
      pose proof (rw_CB_bytes _ _ _ _ P2') as [B2 _]. pose proof (rw_CB_bytes _ _ _ _ P4) as [B4 L4]. destruct P3' as [B3 _].
      lazymatch goal with H : bytes_at usegs m4 A l1 |- _ => rename H into B1' end.
      assert (DA : u8arr usegs m4 A (l1 ++ [Z_to_bv 8 c] ++ (src ++ [nth (length src) (b0 :: src) b0]) ++ l4)).
      { split.
        - apply (proj2 (bytes_at_app _ _ _ _ _)). split; [exact B1'|]. rewrite L1, Z2Nat.id by lia.
          apply (proj2 (bytes_at_app _ _ _ _ _)). split; [exact B2|]. cbn [length Z.of_nat Pos.of_succ_nat].
          apply (proj2 (bytes_at_app _ _ _ _ _)). split; [exact B3|]. rewrite length_app. cbn [length].
          replace (A + pos + 1 + Z.of_nat (length src + 1)) with (A + sz) by lia. exact B4.
        - rewrite !length_app, L1, L4. cbn [length].
          replace (Z.of_nat (Z.to_nat pos + (1 + (length src + 1 + Z.to_nat (cap - sz))))) with cap by lia. assumption. }
      eapply evt_eq; [| eapply (END _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 _ ltac:(unfold shdr; split; [exact HDR| split; [exact EA| exact ECAP]]) DA)];
        [atp_st_eq| rewrite !length_app, L1, L4; cbn [length]; lia| assumption| assumption| assumption| assumption| assumption].
Qed.

Lemma str_replace4_spec : forall (ra gp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : mem) (q lo S : Z) (lg : bool) (A cap sz pos lit c : Z),
  lstr m S lg A cap sz -> 0 <= pos -> pos + 2 <= sz ->
  bytes_at usegs m lit [Z_to_bv 8 c] -> 0 < c < 256 -> 0 < lit -> lit + 16 <= lo -> (A + cap <= lit \/ lit + 16 <= A) ->
  q <= S -> S + 24 < 2^63 -> (lg = true -> A + cap <= lo) ->
  stk usegs m lo q -> lo <= q - 80 -> mem_inv usegs m ->
  munch [(q - 80, q); (S, S + 24); (A, A + cap)] m0 m -> wmono usegs m0 m ->
  evt usegs (replace_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo S lg A cap sz m0)
    (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 pos) (Z_to_bv 64 2) (Z_to_bv 64 lit) (Z_to_bv 64 1) a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x7d2f8) fc None m (seg_rom usegs)).
Proof.
  intros until c. intros LS POS PS LIT1 CR L0 LLO LSEP QS S63 ASEP ST LO MI MU WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  destruct LS as (SZ0 & SZC & CAP & A0 & AC & (bs & BS & LBS & NUL) & REP).

  destruct lg; [destruct REP as [HDR EV]; specialize (ASEP eq_refl)| destruct REP as (HDR & EA & ECAP)].

  all: step; carve_frame 80%nat ST.
  all: apply (rw_cells_split_CB usegs _ _ [] 80 junk [] [8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity]; cbn [mk_CB_cells app] in FR.
  all: do 13 step; name_mem m1.

  all: pose proof (proj2 BS) as WR; rewrite <- (Z2Nat.id (Z.of_nat (length bs))) in WR by lia.
  all: replace (Z.to_nat (Z.of_nat (length bs))) with (length bs) in WR by lia; rewrite LBS in WR.
  all: pose proof BS as BS0.
  all: destruct (u8arr_split _ _ _ (Z.to_nat pos) BS ltac:(lia)) as [P1 P234].
  all: destruct (u8arr_split _ _ _ 1 P234 ltac:(rewrite length_skipn; lia)) as [P2 P34].
  all: destruct (u8arr_split _ _ _ (Z.to_nat (sz - pos - 1)) P34 ltac:(rewrite !length_skipn; lia)) as [P3 P4].
  all: rewrite skipn_skipn in P3; rewrite skipn_skipn in P4; rewrite skipn_skipn in P4; rewrite firstn_skipn_comm in P3.
  all: replace (Z.to_nat (sz - pos - 1) + (1 + Z.to_nat pos))%nat with (Z.to_nat sz) in P4 by lia.
  all: replace (1 + Z.to_nat pos + Z.to_nat (sz - pos - 1))%nat with (Z.to_nat sz) in P3 by lia.
  all: replace (A + Z.of_nat (Z.to_nat pos) + Z.of_nat 1) with (A + pos + 1) in P3, P4 by lia.
  all: replace (A + pos + 1 + Z.of_nat (Z.to_nat (sz - pos - 1))) with (A + sz) in P4 by lia.
  all: match type of P4 with u8arr _ _ _ (skipn ?k ?l) => replace k with (Z.to_nat sz) in P4 by lia end.
  all: set (mid := skipn (1 + Z.to_nat pos) (firstn (Z.to_nat sz) bs)) in P3.
  all: assert (LMID : length mid = Z.to_nat (sz - pos - 1)) by (subst mid; rewrite length_skipn, firstn_length_le by lia; lia).
  all: destruct mid as [|b0 src'] eqn:EMID; [cbn in LMID; lia|]; cbn [length] in LMID.
  all: replace (A + Z.of_nat (Z.to_nat pos)) with (A + pos) in P2 by lia.
  all: apply rw_cells_of_u8arr in P2; rewrite firstn_length_le in P2 by (rewrite length_skipn; lia).
  all: set (l2 := firstn 1 (skipn (Z.to_nat pos) bs)) in P2.
  all: assert (LL2 : length l2 = 1%nat) by (subst l2; rewrite firstn_length_le by (rewrite length_skipn; lia); reflexivity).
  all: destruct l2 as [|b1 [|? ?]] eqn:EL2; [cbn in LL2; lia| | cbn in LL2; lia].
  all: apply rw_cells_of_u8arr in P1; rewrite firstn_length_le in P1 by lia.
  all: apply rw_cells_of_u8arr in P4; rewrite length_skipn in P4; replace (length bs - Z.to_nat sz)%nat with (Z.to_nat (cap - sz)) in P4 by lia.
  all: clear P234 P34.
  -
    lazymatch type of HDR with rw_cells _ ?mx _ _ => pose proof (rw_cells_C8_read1 mx _ _ _ HDR) as RD0 end.
    astep. rewrite zx8_lit by lia. astep. rewrite long_byte0 by lia. step. step. if_false.
    step. step. step. if_lia. astep. step. step. if_lia. step. step. step. if_true.
    astep. rewrite long_capmask by lia. astep. astep. astep. step. if_lia.
    astep. rewrite long_word0 by lia. step. if_false. step. step. if_false.
    eapply evt_eq; [| eapply replace4_mid with (F := F) (fc := fc) (m0 := m0) (m := m1) (q := q) (lo := lo) (S := S) (lg := true) (A := A) (cap := cap) (sz := sz) (pos := pos) (lit := lit) (c := c) (b1 := b1) (b0 := b0) (src := src');
      [ unfold shdr; split; [exact HDR| exact EV] | lia| lia| lia| lia| lia| lia| exact P1| exact P2| exact P3| lia| exact P4| exact WR
      | exact LIT1| lia| lia| lia| lia| lia| lia| intros _; lia| exact FR| exact ST| lia| assumption
      | replace (q - 80) with (q + -80) by lia; exact MU| exact WM] ];
      [atp_st_eq].
  -
    astep. astep. rewrite short_byte0. step. step. if_true.
    astep. rewrite short_size by lia. step. if_lia. astep. step. step. if_lia. step.
    assert (L7 : (7 <= length bs)%nat) by lia. rewrite EA in BS0. pose proof (short_hdr_read8 _ _ _ _ HDR BS0 L7) as RD8.

    remember (Z_to_bv 8 (2 * sz) :: firstn 7 bs) as l8 eqn:El8 in RD8.
    step. step. if_false. astep. astep. astep. step. if_lia.
    astep. subst l8. rewrite le_word_bit0, a_u8_small, short_byte0 by lia. step. if_true.
    astep. step. if_true.
    eapply evt_eq; [| eapply replace4_mid with (F := F) (fc := fc) (m0 := m0) (m := m1) (q := q) (lo := lo) (S := S) (lg := false) (A := A) (cap := cap) (sz := sz) (pos := pos) (lit := lit) (c := c) (b1 := b1) (b0 := b0) (src := src');
      [ unfold shdr; split; [exact HDR| split; [exact EA| exact ECAP]] | lia| lia| lia| lia| lia| lia| exact P1| exact P2| exact P3| lia| exact P4| exact WR
      | exact LIT1| lia| lia| lia| lia| lia| lia| intros X; discriminate X| exact FR| exact ST| lia| assumption
      | replace (q - 80) with (q + -80) by lia; exact MU| exact WM] ];
      [atp_st_eq].
Qed.

Lemma str_replace_spec : forall (ra gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (q lo S : Z) (lg : bool) (A cap sz pos lit c : Z) (slack : list byte),
  lstr m S lg A cap sz -> 0 <= pos -> pos + 2 <= sz ->
  bytes_at usegs m lit (Z_to_bv 8 c :: Z_to_bv 8 0 :: slack) -> (- (lit + 2)) mod 8 <= Z.of_nat (length slack) -> Z.of_nat (length slack) <= 8 ->
  0 < c < 256 -> 0 < lit -> lit + 16 <= lo -> (A + cap <= lit \/ lit + 16 <= A) ->
  q <= S -> S + 24 < 2^63 -> (lg = true -> A + cap <= lo) ->
  stk usegs m lo q -> lo <= q - 80 -> mem_inv usegs m ->
  evt usegs (replace_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo S lg A cap sz m)
    (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 pos) (Z_to_bv 64 2) (Z_to_bv 64 lit) a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x7d698) fc None m (seg_rom usegs)).
Proof.
  intros until slack. intros LS POS PS LIT CPAD SL8 CR L0 LLO LSEP QS S63 ASEP ST LO MI.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(q - 48, q)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof LS as (SZ0 & SZC & CAP & A0 & AC & _ & _).

  step. carve_frame 48%nat ST.
  apply (rw_cells_split_CB usegs _ _ [] 48 junk [] [8;8;8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
  do 5 step. do 5 step. step.
  call strlen_spec.
  1:{ rewrite unsigned_lit by lia. change (Z_to_bv 8 c :: Z_to_bv 8 0 :: slack) with ([Z_to_bv 8 c] ++ Z_to_bv 8 0 :: slack) in LIT. exact LIT. }
  1:{ intros [X|[]]. apply (f_equal bv_unsigned) in X. rewrite !a_u8_small in X by lia. lia. }
  1:{ rewrite unsigned_lit by lia. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]. replace (lit + 1 + 1) with (lit + 2) by lia. exact CPAD. }
  1:{ assumption. }
  name_mem m2. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ].
  lazymatch goal with H : bytes_at usegs m2 _ ([Z_to_bv 8 c] ++ _) |- _ => rename H into LIT2 end.
  rewrite unsigned_lit in LIT2 by lia.
  assert (LIT1 : bytes_at usegs m2 lit [Z_to_bv 8 c]) by (apply (proj1 (bytes_at_app _ _ _ _ _)) in LIT2; tauto).

  do 5 step. do 5 step. release_frame FR ST q. step. step.
  assert (LS2 : lstr m2 S lg A cap sz).
  { eapply lstr_frame; [exact LS| exact MU| exact WM| cbn; lia| cbn]. split; [| exact I].
    destruct lg; [specialize (ASEP eq_refl); lia|].
    destruct LS as (_ & _ & _ & _ & _ & _ & (_ & EA & _)). lia. }
  assert (MU2 : munch [(q - 80, q); (S, S + 24); (A, A + cap)] m m2).
  { eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. intros xx Hxx. lia. }
  eapply evt_eq; [| eapply str_replace4_spec with (F := F) (fc := fc) (m0 := m) (m := m2) (q := q) (lo := lo) (S := S) (lg := lg) (A := A) (cap := cap) (sz := sz) (pos := pos) (lit := lit) (c := c);
    [ exact LS2| lia| lia| exact LIT1| lia| lia| lia| lia| lia| lia| exact ASEP| exact ST| lia| assumption| exact MU2| assumption] ]; [atp_st_eq].
Qed.

End WithCeiling0.
