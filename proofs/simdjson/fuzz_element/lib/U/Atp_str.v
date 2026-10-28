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
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import F_memchr F_memcmp F_strlen F_memcpy F_memmove_t2 Atp_defs.
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

Definition lstr (m : mem) (S : Z) (lg : bool) (A cap sz : Z) : Prop :=
  0 <= sz /\ sz < cap /\ cap < 2^40 /\ 0 < A /\ A + cap < 2^63 /\
  (exists bs : list byte, u8arr usegs m A bs /\ Z.of_nat (length bs) = cap /\ nth (Z.to_nat sz) bs (Z_to_bv 8 1) = Z_to_bv 8 0) /\
  if lg then rw_cells usegs m S [C8 (Z_to_bv 64 (cap + 1)); C8 (Z_to_bv 64 sz); C8 (Z_to_bv 64 A)] /\ cap mod 2 = 0
  else rw_cells usegs m S [C1 (Z_to_bv 8 (2 * sz))] /\ A = S + 1 /\ cap = 23.

Lemma rw_cells_C8_read1 : forall m A v rest,
  rw_cells usegs m A (C8 v :: rest) -> ov_read_bytes usegs m (wa A) 1 = Some [Z_to_bv 8 (bv_unsigned v)].
Proof.
  intros m A v rest [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb.
  pose proof (bytes_at_read usegs m A _ 0 1 Hb ltac:(lia)) as R.
  rewrite Z.add_0_r in R. rewrite R; [reflexivity|]. rewrite length_app, length_le8. cbn. lia.
Qed.

Lemma zxb_any : forall x, zxb (Z_to_bv 8 x) = Z_to_bv 64 (x mod 256).
Proof. intros x. unfold zxb. f_equal. Qed.
Lemma zx8_lit : forall x, 0 <= x < 2^64 -> zx8 (Z_to_bv 64 x) = Z_to_bv 64 (x mod 256).
Proof. intros x H. unfold zx8. f_equal. rewrite a_u64_small by lia. reflexivity. Qed.
Lemma land1_mod2 : forall x, Z.land x 1 = x mod 2.
Proof. intros x. pose proof (Z.land_ones x 1 ltac:(lia)) as H. change (Z.ones 1) with 1 in H. change (2 ^ 1) with 2 in H. exact H. Qed.
Lemma long_byte0 : forall cap, cap mod 2 = 0 -> Z.land ((cap + 1) mod 256) 1 = 1.
Proof. intros cap HE. rewrite land1_mod2. lia. Qed.
Lemma short_byte0 : forall sz, Z.land (2 * sz) 1 = 0.
Proof. intros sz. rewrite land1_mod2. lia. Qed.
Lemma short_size : forall sz, 0 <= sz -> Z.shiftr (2 * sz) 1 = sz.
Proof. intros sz H. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2. lia. Qed.
Lemma testbit_capmask : forall n, 0 <= n -> Z.testbit 18446744073709551614 n = ((1 <=? n) && (n <? 64))%bool.
Proof.
  intros n Hn. change 18446744073709551614 with (2 * Z.ones 63).
  destruct (Z.eq_dec n 0) as [->|NZ].
  - rewrite Z.testbit_even_0. reflexivity.
  - replace n with (Z.succ (n - 1)) at 1 by lia. rewrite Z.testbit_even_succ by lia.
    destruct (Z.lt_ge_cases (n - 1) 63).
    + rewrite Z.ones_spec_low by lia. symmetry. apply andb_true_intro. split; [apply Z.leb_le; lia| apply Z.ltb_lt; lia].
    + rewrite Z.ones_spec_high by lia. symmetry. apply Bool.andb_false_intro2. apply Z.ltb_ge. lia.
Qed.

Lemma long_capmask : forall cap, cap mod 2 = 0 -> 0 <= cap -> cap < 2^63 -> Z.land (cap + 1) 18446744073709551614 = cap.
Proof.
  intros cap HE H0 H1. set (h := cap / 2). assert (EC : cap = 2 * h) by (subst h; lia). rewrite EC.
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, testbit_capmask by lia.
  destruct (Z.eq_dec n 0) as [->|NZ].
  - rewrite Z.testbit_odd_0, Z.testbit_even_0. reflexivity.
  - replace n with (Z.succ (n - 1)) by lia. rewrite Z.testbit_odd_succ, Z.testbit_even_succ by lia.
    destruct (Z.lt_ge_cases (n - 1) 63).
    + replace ((1 <=? Z.succ (n - 1)) && (Z.succ (n - 1) <? 64))%bool with true
        by (symmetry; apply andb_true_intro; split; [apply Z.leb_le; lia| apply Z.ltb_lt; lia]). apply Bool.andb_true_r.
    + replace ((1 <=? Z.succ (n - 1)) && (Z.succ (n - 1) <? 64))%bool with false
        by (symmetry; apply Bool.andb_false_intro2; apply Z.ltb_ge; lia). rewrite Bool.andb_false_r.
      destruct (Z.eq_dec h 0) as [->|HZ]; [rewrite Z.bits_0; reflexivity|].
      symmetry. apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ 62); [| lia]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma find_or_found : forall y x, 0 < y -> Z.lor (Z.land (Z.b2z (0 <? y) + -1) 18446744073709551615) x = x.
Proof.
  intros y x Hy. replace (0 <? y) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z]. change (1 + -1) with 0.
  rewrite Z.land_0_l. apply Z.lor_0_l.
Qed.
Lemma find_or_npos : forall x, 0 <= x < 2^64 -> Z.lor (Z.land (Z.b2z (0 <? 0) + -1) 18446744073709551615) x = 18446744073709551615.
Proof.
  intros x Hx. cbn [Z.ltb Z.compare Z.b2z]. change (Z.land (0 + -1) 18446744073709551615) with 18446744073709551615.
  pose proof (Z.add_lor_land 18446744073709551615 x) as E.
  rewrite (Z.land_comm 18446744073709551615 x) in E. rewrite land64_mod, Z.mod_small in E by lia. lia.
Qed.

Lemma memmove_far_callZ : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (Dst Src N : Z) (src junk : list byte),
  bytes_at usegs m Src src -> length src = Z.to_nat N -> rw_cells usegs m Dst [CB (Z.to_nat N) junk] ->
  (Src + N <= Dst \/ Dst + N <= Src)%Z -> (1 <= N < 2^63)%Z -> (0 <= Src)%Z -> (Src + N < 2^63)%Z -> (0 <= Dst)%Z -> (Dst + N < 2^63)%Z -> mem_inv usegs m ->
  evt usegs (memcpy_postZ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Dst Src N src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xd0aec) fc None m (seg_rom usegs)).
Proof.
  intros until junk. intros BA LEN DC SEP HN HS HS2 HD HD2 MI.
  assert (ED : bv_unsigned (Z_to_bv 64 Dst) = Dst) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 Src) = Src) by (apply unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { eapply memmove_far_spec with (src := src) (junk := junk); rewrite ?ED, ?ES, ?EN; [exact BA| exact LEN| exact DC| exact SEP| lia| exact MI]. }
  intros ms' P. unfold memcpy_post, memcpy_postZ in *. rewrite ED, ES, EN in P. exact P.
Qed.

Definition find_post (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo S : Z) (lg : bool) (A cap sz pos : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem) (r : Z),
    ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(q - 16, q)] m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo q
    /\ lstr m' S lg A cap sz /\ (r = -1 \/ pos <= r < sz).

Lemma str_find_spec : forall (ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (q lo S : Z) (lg : bool) (A cap sz pos : Z),
  lstr m S lg A cap sz -> 0 <= pos < 2^62 -> q <= S -> S + 24 < 2^63 -> (lg = true -> A + cap <= lo) ->
  stk usegs m lo q -> lo <= q - 16 -> mem_inv usegs m ->
  evt usegs (find_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo S lg A cap sz pos m)
    (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 126) (Z_to_bv 64 pos) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x7dc00) fc None m (seg_rom usegs)).
Proof.
  intros until pos. intros LS POS QS S63 ASEP ST LO MI.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(q - 16, q)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  destruct LS as (SZ0 & SZC & CAP & A0 & AC & (bs & BS & LBS & NUL) & REP).

  assert (XNPOS : forall (xa3 xa4 : word),
    evt usegs (find_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo S lg A cap sz pos m)
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 126) (Z_to_bv 64 pos) xa3 xa4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x7dc14) fc None m (seg_rom usegs))).
  { intros xa3 xa4. astep. step. apply evt_done. unfold find_post. do 15 eexists. exists (-1). split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [| left; reflexivity].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exists bs; auto| exact REP]. }

  destruct lg.
  - destruct REP as [HDR EV]. specialize (ASEP eq_refl).
    pose proof (rw_cells_C8_read1 _ _ _ _ HDR) as RD0.
    astep. rewrite zx8_lit by lia. astep. rewrite long_byte0 by lia.
    step. if_false. astep. step. if_cases K; zify_cond K; try apply XNPOS; [idtac].

    step. carve_frame 16%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 16 junk [] [8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
    step. step. step. if_false. step. step. astep. astep. step. step.
    pose proof (bytes_at_skipn _ _ _ (Z.to_nat pos) (proj1 BS) ltac:(lia)) as BSP. rewrite Z2Nat.id in BSP by lia.
    call memchr_spec.
    1:{ rewrite unsigned_lit by lia. exact BSP. }
    1:{ rewrite !unsigned_lit by lia. unfold memchr_ok. change (126 mod 256) with 126.
        match goal with |- context [find_byte ?c ?l] => destruct (find_byte c l) end; rewrite length_skipn; [left|]; lia. }
    1:{ assumption. }
    rewrite !unsigned_lit by lia. change (126 mod 256) with 126. unfold memchr_res. name_mem m2.
    lazymatch goal with H : mem_inv usegs m2 |- _ => rename H into MI2 end.

    match goal with |- context [find_byte ?c ?l] => destruct (find_byte c l) as [ix|] eqn:FB end.
    + pose proof (find_byte_Some _ _ _ FB) as (Hl & _). rewrite length_firstn, length_skipn in Hl.
      astep. astep. astep. astep. step. step. step. release_frame FR ST q. step.
      rewrite find_or_found by lia.
      apply evt_done. unfold find_post. do 15 eexists. exists (pos + Z.of_nat ix). split.
      { atp_st_eq_goal. }
      split; [exact MU|]. split; [exact WM|]. split; [exact MI2|]. split; [exact ST|]. split; [| right; lia].
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exists bs; auto| split; [exact HDR| exact EV]].
    + astep. astep. astep. astep. step. step. step. release_frame FR ST q. step.
      rewrite find_or_npos by (rewrite land64_mod; lia).
      apply evt_done. unfold find_post. do 15 eexists. exists (-1). split.
      { atp_st_eq_goal. }
      split; [exact MU|]. split; [exact WM|]. split; [exact MI2|]. split; [exact ST|]. split; [| left; reflexivity].
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exists bs; auto| split; [exact HDR| exact EV]].
  - destruct REP as (HDR & EA & ECAP).
    astep. astep. rewrite short_byte0. step. if_true. astep. rewrite short_size by lia.
    step. if_cases K; zify_cond K; try apply XNPOS; [idtac].
    step. carve_frame 16%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 16 junk [] [8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
    step. step. step. if_true. astep. astep. astep. step. step.
    pose proof (bytes_at_skipn _ _ _ (Z.to_nat pos) (proj1 BS) ltac:(lia)) as BSP. rewrite Z2Nat.id in BSP by lia.
    rewrite <- EA.
    call memchr_spec.
    1:{ rewrite unsigned_lit by lia. exact BSP. }
    1:{ rewrite !unsigned_lit by lia. unfold memchr_ok. change (126 mod 256) with 126.
        match goal with |- context [find_byte ?c ?l] => destruct (find_byte c l) end; rewrite length_skipn; [left|]; lia. }
    1:{ assumption. }
    rewrite !unsigned_lit by lia. change (126 mod 256) with 126. unfold memchr_res. name_mem m2.
    lazymatch goal with H : mem_inv usegs m2 |- _ => rename H into MI2 end.
    match goal with |- context [find_byte ?c ?l] => destruct (find_byte c l) as [ix|] eqn:FB end.
    + pose proof (find_byte_Some _ _ _ FB) as (Hl & _). rewrite length_firstn, length_skipn in Hl.
      astep. astep. astep. astep. step. step. step. release_frame FR ST q. step.
      rewrite find_or_found by lia.
      apply evt_done. unfold find_post. do 15 eexists. exists (pos + Z.of_nat ix). split.
      { atp_st_eq_goal. }
      split; [exact MU|]. split; [exact WM|]. split; [exact MI2|]. split; [exact ST|]. split; [| right; lia].
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exists bs; auto| split; [exact HDR| auto]].
    + astep. astep. astep. astep. step. step. step. release_frame FR ST q. step.
      rewrite find_or_npos by (rewrite land64_mod; lia).
      apply evt_done. unfold find_post. do 15 eexists. exists (-1). split.
      { atp_st_eq_goal. }
      split; [exact MU|]. split; [exact WM|]. split; [exact MI2|]. split; [exact ST|]. split; [| left; reflexivity].
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exists bs; auto| split; [exact HDR| auto]].
Qed.

End WithCeiling0.
