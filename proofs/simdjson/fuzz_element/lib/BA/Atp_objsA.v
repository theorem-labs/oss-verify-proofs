(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_num_akit Sj_num_amem. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_defsA Atp_kitA Atp_objkA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition lstrA (m : mem) (S : Z) (lg : bool) (A cap sz : Z) : Prop :=
  0 <= sz /\ sz < cap /\ cap < 2^40 /\ 0 < A /\ A + cap < 2^47 /\
  (exists bs : list byte, u8arr asegs m A bs /\ Z.of_nat (length bs) = cap /\ nth (Z.to_nat sz) bs (Z_to_bv 8 1) = Z_to_bv 8 0) /\
  if lg then rw_cells asegs m S [C8 (Z_to_bv 64 (cap + 1)); C8 (Z_to_bv 64 sz); C8 (Z_to_bv 64 A)] /\ cap mod 2 = 0
  else rw_cells asegs m S [C1 (Z_to_bv 8 (2 * sz))] /\ A = S + 1 /\ cap = 23.

Definition lstr_cls (RT : rt_sig) (Σ : rts RT) (A n : Z) : Prop :=
  (exists f k, In (f, k) (rt_frames RT Σ) /\ f <= A /\ A + n <= f + fs_size k - 8) \/ (exists p k, In (p, k) (rt_live RT Σ) /\ p <= A /\ A + n <= p + k).

Lemma lstr_cls_rng : forall RT Σ A n, lstr_cls RT Σ A n -> rng_class RT Σ A n.
Proof. intros RT Σ A n [H|H]; [right; left; exact H| left; exact H]. Qed.
Lemma lstr_cls_client : forall RT Σ sp A n a, lstr_cls RT Σ A n -> A <= a < A + n -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp a.
Proof.
  intros RT Σ sp A n a [(f & k & Hin & H1 & H2)|(p & k & Hin & H1 & H2)] Ha.
  - right; right; right; left. exists f, k. split; [exact Hin| lia].
  - right; right; left. exists p, k. split; [exact Hin| lia].
Qed.
Lemma lstr_cls_sub : forall RT Σ A n A' n', lstr_cls RT Σ A n -> A <= A' -> A' + n' <= A + n -> lstr_cls RT Σ A' n'.
Proof.
  intros RT Σ A n A' n' [(f & k & Hin & H1 & H2)|(p & k & Hin & H1 & H2)] L1 L2; [left; exists f, k| right; exists p, k]; split; [exact Hin| lia| exact Hin| lia].
Qed.

Lemma rw_cells_C8_read1A : forall (m : mem) A v rest,
  rw_cells asegs m A (C8 v :: rest) -> ov_read_bytes asegs m (wa A) 1 = Some [Z_to_bv 8 (bv_unsigned v)].
Proof.
  intros m A v rest [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb.
  pose proof (bytes_at_read asegs m A _ 0 1 Hb ltac:(lia)) as R.
  rewrite Z.add_0_r in R. rewrite R; [reflexivity|]. rewrite length_app, length_le8. cbn. lia.
Qed.
Lemma u8_modA : forall x, bv_unsigned (Z_to_bv 8 x) = x mod 256.
Proof. intros x. rewrite Z_to_bv_unsigned. reflexivity. Qed.
Lemma land1_mod2A : forall x, Z.land x 1 = x mod 2.
Proof. intros x. pose proof (Z.land_ones x 1 ltac:(lia)) as H. change (Z.ones 1) with 1 in H. change (2 ^ 1) with 2 in H. exact H. Qed.
Lemma long_byte0A : forall cap, cap mod 2 = 0 -> Z.land ((cap + 1) mod 256) 1 = 1.
Proof. intros cap HE. rewrite land1_mod2A. lia. Qed.
Lemma short_byte0A : forall sz, Z.land (2 * sz) 1 = 0.
Proof. intros sz. rewrite land1_mod2A. lia. Qed.
Lemma short_sizeA : forall sz, 0 <= sz -> Z.shiftr (2 * sz) 1 = sz.
Proof. intros sz H. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2. lia. Qed.
Lemma find_or_foundA : forall y x, 0 < y -> Z.lor ((Z.b2z (0 <? y) + -1) mod 18446744073709551616) x = x.
Proof.
  intros y x Hy. replace (0 <? y) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z]. change ((1 + -1) mod 18446744073709551616) with 0.
  apply Z.lor_0_l.
Qed.
Lemma find_or_nposA : forall x, 0 <= x < 2^64 -> Z.lor ((Z.b2z (0 <? 0) + -1) mod 18446744073709551616) x = 18446744073709551615.
Proof.
  intros x Hx. cbn [Z.ltb Z.compare Z.b2z]. change ((0 + -1) mod 18446744073709551616) with 18446744073709551615.
  pose proof (Z.add_lor_land 18446744073709551615 x) as E.
  rewrite (Z.land_comm 18446744073709551615 x) in E. rewrite land64_mod, Z.mod_small in E by lia. lia.
Qed.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Lemma K_eqA : forall (K : machine_state -> Prop) (a b : machine_state), K a -> a = b -> K b.
Proof. intros K a b H <-. exact H. Qed.

Lemma sf_walk1 : forall (K : machine_state -> Prop) (sp lo S : Z) (lg : bool) (A cap sz pos : Z)
    (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  lstrA m S lg A cap sz -> 0 <= pos < sz -> 0 < S -> S + 24 < 2^47 -> (S + 24 <= sp - 16 \/ sp <= S) ->
  stk asegs m lo sp -> lo <= sp - 16 -> 0x6ca000 <= lo -> sp < 2^47 -> mem_inv asegs m ->
  (forall (m1 : mem) (xa3 xa4 : word), munch [(sp - 16, sp)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 -> stk asegs m1 lo (sp - 16) ->
     rw_cells asegs m1 (sp - 16) [C8 s0; C8 ra] ->
     K (MS (mkR (wz 0x108898) (wz (sp - 16)) gp tp t0 t1 t2 (wz A) s1 (wz (A + pos)) (wz 126) (wz (sz - pos)) xa3 xa4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz e_memchr) fc None m1 (seg_rom asegs))) ->
  evt asegs K (MS (mkR ra (wz sp) gp tp t0 t1 t2 s0 s1 (wz S) (wz 126) (wz pos) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (wz STR_FIND_A) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros LS POS S0 S47 SSEP ST LO GLO SPH MI HK.
  pose proof (munch_refl [(sp - 16, sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  destruct LS as (SZ0 & SZC & CAP & A0 & AC & (bs & BS & LBS & NUL) & REP).
  unfold STR_FIND_A, e_memchr in *.
  destruct lg.
  - destruct REP as [HDR EV].
    pose proof (rw_cells_C8_read1A _ _ _ _ HDR) as RD0.
    astep. rewrite u8_modA. astep. rewrite long_byte0A by lia.
    step. if_false. astep. step. if_lia.

    step. carve_frame 16%nat ST.
    apply (rw_cells_split_CB asegs _ _ [] 16 junk [] [8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
    step. step. step. if_false. step. step. astep. astep. step. step.
    name_mem m1. apply evt_done. eapply (HK m1); [exact MU| exact WM| assumption| assumption| ].
    replace (sp - 16) with (sp + -16) by lia. exact FR.
  - destruct REP as (HDR & EA & ECAP).
    astep. astep. rewrite short_byte0A. step. if_true. astep. rewrite short_sizeA by lia.
    step. if_lia.
    step. carve_frame 16%nat ST.
    apply (rw_cells_split_CB asegs _ _ [] 16 junk [] [8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
    step. step. step. if_true. astep. astep. astep. step. step.
    name_mem m1. apply evt_done. rewrite <- EA. eapply (HK m1); [exact MU| exact WM| assumption| assumption| ].
    replace (sp - 16) with (sp + -16) by lia. exact FR.
Qed.

Lemma sf_walk0 : forall (K : machine_state -> Prop) (sp S : Z) (lg : bool) (A cap sz pos : Z)
    (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  lstrA m S lg A cap sz -> sz <= pos < 2^62 -> 0 < S -> S + 24 < 2^47 -> mem_inv asegs m ->
  (forall (xa3 xa4 : word),
     K (MS (mkR ra (wz sp) gp tp t0 t1 t2 s0 s1 (wz 18446744073709551615) (wz 126) (wz pos) xa3 xa4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (ret_pc ra) fc None m (seg_rom asegs))) ->
  evt asegs K (MS (mkR ra (wz sp) gp tp t0 t1 t2 s0 s1 (wz S) (wz 126) (wz pos) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (wz STR_FIND_A) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros LS POS S0 S47 MI HK.
  destruct LS as (SZ0 & SZC & CAP & A0 & AC & (bs & BS & LBS & NUL) & REP).
  unfold STR_FIND_A in *.
  destruct lg.
  - destruct REP as [HDR EV].
    pose proof (rw_cells_C8_read1A _ _ _ _ HDR) as RD0.
    astep. rewrite u8_modA. astep. rewrite long_byte0A by lia.
    step. if_false. astep. step. if_lia.
    astep. step. apply evt_done. eapply (K_eqA K); [apply (HK (wz sz) (wz 1))| atp_st_eq].
  - destruct REP as (HDR & EA & ECAP).
    astep. astep. rewrite short_byte0A. step. if_true. astep. rewrite short_sizeA by lia.
    step. if_lia.
    astep. step. apply evt_done. eapply (K_eqA K); [apply (HK (wz sz) (wz 0))| atp_st_eq].
Qed.

Lemma sf_walk2 : forall (K : machine_state -> Prop) (sp lo A res : Z)
    (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  stk asegs m lo (sp - 16) -> lo <= sp - 16 -> sp < 2^47 -> 0x6ca000 <= lo -> rw_cells asegs m (sp - 16) [C8 s0; C8 ra] ->
  0 < A -> A < 2^47 -> (res = 0 \/ A <= res < 2^47) -> mem_inv asegs m ->
  (forall (xa1 : word), stk asegs m lo sp ->
     K (MS (mkR ra (wz sp) gp tp t0 t1 t2 s0 s1 (wz (if res =? 0 then 18446744073709551615 else res - A)) xa1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (ret_pc ra) fc None m (seg_rom asegs))) ->
  evt asegs K (MS (mkR (wz 0x108898) (wz (sp - 16)) gp tp t0 t1 t2 (wz A) s1 (wz res) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (wz 0x108898) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros ST LO SPH GLO FR A0 A47 RES MI HK.
  replace (sp - 16) with (sp + -16) in ST, FR |- * by lia.
  destruct RES as [->|RES].
  - astep. astep. astep. astep. step. step. step. release_frame FR ST sp. step.
    rewrite find_or_nposA by (Z.div_mod_to_equations; lia) || rewrite find_or_nposA by lia.
    apply evt_done. cbn [Z.eqb]. eapply (K_eqA K); [apply HK; exact ST| atp_st_eq].
  - astep. astep. astep. astep. step. step. step. release_frame FR ST sp. step.
    rewrite find_or_foundA by lia.
    apply evt_done. destruct (Z.eqb_spec res 0); [lia|]. eapply (K_eqA K); [apply HK; exact ST| atp_st_eq].
Qed.

Lemma testbit_capmaskA : forall n, 0 <= n -> Z.testbit 18446744073709551614 n = ((1 <=? n) && (n <? 64))%bool.
Proof.
  intros n Hn. change 18446744073709551614 with (2 * Z.ones 63).
  destruct (Z.eq_dec n 0) as [->|NZ].
  - rewrite Z.testbit_even_0. reflexivity.
  - replace n with (Z.succ (n - 1)) at 1 by lia. rewrite Z.testbit_even_succ by lia.
    destruct (Z.lt_ge_cases (n - 1) 63).
    + rewrite Z.ones_spec_low by lia. symmetry. apply andb_true_intro. split; [apply Z.leb_le; lia| apply Z.ltb_lt; lia].
    + rewrite Z.ones_spec_high by lia. symmetry. apply Bool.andb_false_intro2. apply Z.ltb_ge. lia.
Qed.
Lemma long_capmaskA : forall cap, cap mod 2 = 0 -> 0 <= cap -> cap < 2^63 -> Z.land (cap + 1) 18446744073709551614 = cap.
Proof.
  intros cap HE H0 H1. set (h := cap / 2). assert (EC : cap = 2 * h) by (subst h; lia). rewrite EC.
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, testbit_capmaskA by lia.
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
Lemma long_word0A : forall cap, cap mod 2 = 0 -> Z.land (cap + 1) 1 = 1.
Proof. intros cap HE. rewrite land1_mod2A. lia. Qed.
Lemma land1_lor_shiftl8A : forall x y, Z.land (Z.lor x (Z.shiftl y 8)) 1 = Z.land x 1.
Proof.
  intros x y. apply Z.bits_inj'. intros n Hn.
  rewrite !Z.land_spec, Z.lor_spec.
  destruct (Z.eq_dec n 0) as [->|NZ].
  - rewrite Z.shiftl_spec_low by lia. rewrite Bool.orb_false_r. reflexivity.
  - replace (Z.testbit 1 n) with false by (symmetry; apply (Z.bits_above_log2 1 n); [lia| cbn; lia]).
    rewrite !Bool.andb_false_r. reflexivity.
Qed.
Lemma le_word_bit0A : forall (b : byte) (l : list byte),
  Z.land (bv_unsigned (bv_extract 0 64 (le_bytes_to_word (b :: l)))) 1 = Z.land (bv_unsigned b) 1.
Proof.
  intros b l. rewrite bv_extract_unsigned, Z.shiftr_0_r.
  unfold le_bytes_to_word. rewrite Z_to_bv_unsigned. cbn [bytes_le_to_Z].
  unfold bv_wrap. change (bv_modulus 64) with (2^64)%Z.
  rewrite <- !(Z.land_ones _ 64) by lia.
  rewrite <- !Z.land_assoc. change (Z.land (Z.ones 64) (Z.land (Z.ones 64) 1)) with 1.
  apply land1_lor_shiftl8A.
Qed.

Lemma short_hdr_read8A : forall (m : mem) S (hb : byte) (bs : list byte),
  rw_cells asegs m S [C1 hb] -> u8arr asegs m (S + 1) bs -> (7 <= length bs)%nat ->
  ov_read_bytes asegs m (wa S) 8 = Some (hb :: firstn 7 bs).
Proof.
  intros m S hb bs [[_ HB] _] [BS _] HL. cbn [cells_bytes cbytes app] in HB.
  assert (X : bytes_at asegs m S (hb :: bs)).
  { apply (proj2 (bytes_at_app asegs m S [hb] bs)). split; [exact HB|]. cbn [length Z.of_nat Pos.of_succ_nat]. exact BS. }
  pose proof (bytes_at_read asegs m S _ 0 8 X ltac:(lia) ltac:(cbn [length]; lia)) as R.
  rewrite Z.add_0_r in R. rewrite R. reflexivity.
Qed.

Lemma rw_CB_bytesA : forall (m : mem) A n (l : list byte), rw_cells asegs m A [CB n l] -> bytes_at asegs m A l /\ length l = n.
Proof.
  intros m A n l [[W B] _]. cbn [cells_wf cell_wf cells_bytes cbytes app] in W, B. rewrite app_nil_r in B. split; [exact B| tauto].
Qed.
Lemma u8arr_splitA : forall (m : mem) A (bs : list byte) k, u8arr asegs m A bs -> (k <= length bs)%nat ->
  u8arr asegs m A (firstn k bs) /\ u8arr asegs m (A + Z.of_nat k) (skipn k bs).
Proof.
  intros m A bs k [HB HW] Hk. rewrite <- (firstn_skipn k bs) in HB. apply bytes_at_app in HB. destruct HB as [B1 B2].
  rewrite firstn_length_le in B2 by lia. destruct (wr_at_split asegs m A _ (Z.of_nat k) HW ltac:(lia)) as [W1 W2].
  split; split; [exact B1| rewrite firstn_length_le by lia; exact W1| exact B2|].
  rewrite length_skipn. replace (Z.of_nat (length bs - k)) with (Z.of_nat (length bs) - Z.of_nat k) by lia. exact W2.
Qed.
Lemma nth_upd_sameA : forall (l : list byte) i (b d : byte), (i < length l)%nat -> nth i (upd l i b) d = b.
Proof. intros l i b d Hi. apply nth_error_nth. apply nth_error_upd_same. exact Hi. Qed.

Lemma le1_smallA : forall v, (0 <= v < 256)%Z -> le1 (Z_to_bv 64 v) = [Z_to_bv 8 v].
Proof. intros v Hv. unfold le1. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes]. reflexivity. Qed.

Definition shdrA (m : mem) (S : Z) (lg : bool) (A cap sz : Z) : Prop :=
  if lg then rw_cells asegs m S [C8 (Z_to_bv 64 (cap + 1)); C8 (Z_to_bv 64 sz); C8 (Z_to_bv 64 A)] /\ cap mod 2 = 0
  else rw_cells asegs m S [C1 (Z_to_bv 8 (2 * sz))] /\ A = S + 1 /\ cap = 23.

Definition sr_frame (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 : word) : list cell := [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma sr_walk1 : forall (K : machine_state -> Prop) (sp lo lit : Z)
    (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  stk asegs m lo sp -> lo <= sp - 48 -> 0x6ca000 <= lo -> sp < 2^47 -> 0 <= lit < 2^47 -> mem_inv asegs m ->
  (forall (m1 : mem) (j : list byte), munch [(sp - 48, sp)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 -> stk asegs m1 lo (sp - 48) ->
     rw_cells asegs m1 (sp - 48) [CB 8 j; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
     K (MS (mkR (wz 0x108310) (wz (sp - 48)) gp tp t0 t1 t2 (wz lit) a2 (wz lit) a1 a2 (wz lit) a4 a5 a6 a7 a1 a0 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz e_strlen) fc None m1 (seg_rom asegs))) ->
  evt asegs K (MS (mkR ra (wz sp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 (wz lit) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (wz STR_REPLACE_A) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros ST LO GLO SPH LIT MI HK.
  pose proof (munch_refl [(sp - 48, sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold STR_REPLACE_A, e_strlen in *.
  step. carve_frame 48%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 48 junk [] [8;8;8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
  do 5 step. do 5 step. step.
  name_mem m1. apply evt_done. replace (sp + -48) with (sp - 48) in FR by lia. eapply (HK m1); [exact MU| exact WM| assumption| | exact FR].
  replace (sp - 48) with (sp + -48) by lia. assumption.
Qed.

Lemma sr_walk2 : forall (K : machine_state -> Prop) (sp lo S : Z) (lg : bool) (A cap sz pos lit : Z)
    (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (j : list byte) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  lstrA m S lg A cap sz -> 0 <= pos -> pos + 2 <= sz -> S + 24 <= lo -> A + cap <= lo -> 0 <= lit < 2^47 ->
  stk asegs m lo (sp - 48) -> lo <= sp - 80 -> 0x6ca000 <= lo -> sp < 2^47 -> mem_inv asegs m ->
  rw_cells asegs m (sp - 48) [CB 8 j; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  (forall (m1 : mem) (xa1 xa3 xa4 : word), munch [(sp - 80, sp)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 -> stk asegs m1 lo (sp - 80) ->
     rw_cells asegs m1 (sp - 80) (sr_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8) ->
     K (MS (mkR ra (wz (sp - 80)) gp tp t0 t1 t2 (wz S) (wz 1) (wz (sz - pos)) xa1 (wz 2) xa3 xa4 a5 a6 a7
               (wz sz) (wz lit) (wz 2) (wz pos) s6 s7 (wz A) s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x107fd0) fc None m1 (seg_rom asegs))) ->
  evt asegs K (MS (mkR (wz 0x108310) (wz (sp - 48)) gp tp t0 t1 t2 (wz lit) (wz 2) (wz 1) a1 a2 a3 a4 a5 a6 a7 (wz pos) (wz S) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (wz 0x108310) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros LS POS PS SLO ALO LIT ST LO GLO SPH MI FR HK.
  pose proof (munch_refl [(sp - 80, sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  destruct LS as (SZ0 & SZC & CAP & A0 & AC & (bs & BS & LBS & NUL) & REP).
  replace (sp - 48) with (sp + -48) in ST, FR |- * by lia.

  destruct lg; [destruct REP as [HDR EV]| destruct REP as (HDR & EA & ECAP)].

  all: do 5 step; do 5 step; release_frame FR ST sp; step; step.

  all: step; carve_frame 80%nat ST.
  all: apply (rw_cells_split_CB asegs _ _ [] 80 junk [] [8;8;8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity]; cbn [mk_CB_cells app] in FR.
  all: do 10 step; step; step; step.
  -
    pose proof (rw_cells_C8_read1A _ _ _ _ HDR) as RD0.
    astep. rewrite u8_modA. astep. rewrite long_byte0A by lia. step. step. if_false.
    step. step. step. if_lia. astep. step. step. if_lia. step. step. step. if_true.
    astep. rewrite long_capmaskA by lia. astep. astep. astep. step. if_lia.
    astep. rewrite long_word0A by lia. step. if_false. step. step. if_false.
    name_mem m1. apply evt_done. eapply (K_eqA K); [eapply (HK m1); [exact MU| exact WM| assumption| assumption| unfold sr_frame; replace (sp - 80) with (sp + -80) by lia; exact FR]| atp_st_eq].
  -
    astep. astep. rewrite short_byte0A. step. step. if_true.
    astep. rewrite short_sizeA by lia. step. if_lia. astep. step. step. if_lia. step.
    assert (L7 : (7 <= length bs)%nat) by lia. rewrite EA in BS. pose proof (short_hdr_read8A _ _ _ _ HDR BS L7) as RD8.
    remember (Z_to_bv 8 (2 * sz) :: firstn 7 bs) as l8 eqn:El8 in RD8.
    step. step. if_false. astep. astep. astep. step. if_lia.
    astep. subst l8. rewrite le_word_bit0A, a_u8_small, short_byte0A by lia. step. if_true.
    astep. step. if_true.
    name_mem m1. apply evt_done. rewrite <- EA.
    eapply (K_eqA K); [eapply (HK m1); [exact MU| exact WM| assumption| assumption| unfold sr_frame; replace (sp - 80) with (sp + -80) by lia; exact FR]| atp_st_eq].
Qed.

Lemma sr_walk2n : forall (K : machine_state -> Prop) (sp' S A sz pos lit : Z)
    (ra gp tp t0 t1 t2 xa1 xa3 xa4 a5 a6 a7 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  sz - pos = 2 -> 0 <= pos -> 0 < A -> A + sz < 2^47 -> mem_inv asegs m ->
  K (MS (mkR (wz 0x108080) (wz sp') gp tp t0 t1 t2 (wz S) (wz 1) (wz (A + pos)) (wz lit) (wz 1) xa3 xa4 a5 a6 a7
            (wz sz) (wz lit) (wz 2) (wz pos) s6 s7 (wz A) s9 s10 s11 t3 t4 t5 t6)
       F (wz e_memmove2) fc None m (seg_rom asegs)) ->
  evt asegs K (MS (mkR ra (wz sp') gp tp t0 t1 t2 (wz S) (wz 1) (wz (sz - pos)) xa1 (wz 2) xa3 xa4 a5 a6 a7
                      (wz sz) (wz lit) (wz 2) (wz pos) s6 s7 (wz A) s9 s10 s11 t3 t4 t5 t6)
                 F (wz 0x107fd0) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros NT POS A0 AH MI HK. unfold e_memmove2 in HK.
  step. if_lia. step. if_false. astep. step. step. step.
  apply evt_done. eapply (K_eqA K); [exact HK| atp_st_eq].
Qed.

Lemma sr_walk2t : forall (K : machine_state -> Prop) (sp' S A sz pos lit : Z)
    (ra gp tp t0 t1 t2 xa1 xa3 xa4 a5 a6 a7 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  2 < sz - pos -> 0 <= pos -> 0 < A -> A + sz < 2^47 -> mem_inv asegs m ->
  K (MS (mkR (wz 0x107ff4) (wz sp') gp tp t0 t1 t2 (wz S) (wz 1) (wz (A + pos)) (wz lit) (wz 1) xa3 xa4 a5 a6 a7
            (wz sz) (wz lit) (wz 2) (wz pos) (wz (sz - pos - 2)) (wz (A + pos)) (wz A) s9 s10 s11 t3 t4 t5 t6)
       F (wz e_memmove2) fc None m (seg_rom asegs)) ->
  evt asegs K (MS (mkR ra (wz sp') gp tp t0 t1 t2 (wz S) (wz 1) (wz (sz - pos)) xa1 (wz 2) xa3 xa4 a5 a6 a7
                      (wz sz) (wz lit) (wz 2) (wz pos) s6 s7 (wz A) s9 s10 s11 t3 t4 t5 t6)
                 F (wz 0x107fd0) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros TL POS A0 AH MI HK. unfold e_memmove2 in HK.
  step. if_lia. astep. astep. step. if_false. step. if_false. step. step. step. step.
  apply evt_done. eapply (K_eqA K); [exact HK| atp_st_eq].
Qed.

Lemma sr_walk3 : forall (K : machine_state -> Prop) (sp' S A sz pos lit : Z)
    (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  2 < sz - pos -> 0 <= pos -> 0 < A -> A + sz < 2^47 -> mem_inv asegs m ->
  K (MS (mkR (wz 0x108004) (wz sp') gp tp t0 t1 t2 (wz S) (wz 1) (wz (A + pos + 1)) (wz (A + pos + 2)) (wz (sz - pos - 2)) a3 a4 a5 a6 a7
            (wz sz) (wz lit) (wz 2) (wz pos) (wz (sz - pos - 2)) (wz (A + pos)) (wz A) s9 s10 s11 t3 t4 t5 t6)
       F (wz e_memmove2) fc None m (seg_rom asegs)) ->
  evt asegs K (MS (mkR (wz 0x107ff4) (wz sp') gp tp t0 t1 t2 (wz S) (wz 1) (wz (A + pos)) a1 a2 a3 a4 a5 a6 a7
                      (wz sz) (wz lit) (wz 2) (wz pos) (wz (sz - pos - 2)) (wz (A + pos)) (wz A) s9 s10 s11 t3 t4 t5 t6)
                 F (wz 0x107ff4) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros TL POS A0 AH MI HK. unfold e_memmove2 in HK.
  astep. astep. step. step.
  apply evt_done. eapply (K_eqA K); [exact HK| atp_st_eq].
Qed.

Lemma sr_walk4 : forall (K : machine_state -> Prop) (pc0 sp' S : Z) (lg : bool) (A cap sz pos lit : Z)
    (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  (pc0 = 0x108004 \/ pc0 = 0x108080) -> shdrA m S lg A cap sz -> 2 <= sz -> sz < cap -> cap < 2^40 -> 0 < S -> S + 24 < 2^47 -> mem_inv asegs m ->
  (forall (xa0 : word),
     K (MS (mkR (wz pc0) (wz sp') gp tp t0 t1 t2 (wz S) (wz 1) xa0 (wz 18446744073709551615) a2 a3 a4 a5 a6 a7
               (wz (sz - 1)) (wz lit) (wz 2) (wz pos) s6 s7 (wz A) s9 s10 s11 t3 t4 t5 t6)
          F (wz (if lg then 0x108018 else 0x108094)) fc None m (seg_rom asegs))) ->
  evt asegs K (MS (mkR (wz pc0) (wz sp') gp tp t0 t1 t2 (wz S) (wz 1) a0 a1 a2 a3 a4 a5 a6 a7
                      (wz sz) (wz lit) (wz 2) (wz pos) s6 s7 (wz A) s9 s10 s11 t3 t4 t5 t6)
                 F (wz pc0) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros PC HDR SZ2 SZC CAP S0 SH MI HK. unfold shdrA in HDR.
  destruct lg; [destruct HDR as [HDR EV]| destruct HDR as (HDR & EA & ECAP)].
  - pose proof (rw_cells_C8_read1A _ _ _ _ HDR) as RD1.
    destruct PC as [-> | ->].
    + astep. rewrite u8_modA. astep. astep. rewrite long_byte0A by lia. astep. step. if_false.
      apply evt_done. eapply (K_eqA K); [apply HK| atp_st_eq].
    + astep. rewrite u8_modA. astep. astep. rewrite long_byte0A by lia. astep. step. if_true.
      apply evt_done. eapply (K_eqA K); [apply HK| atp_st_eq].
  - destruct PC as [-> | ->].
    + astep. astep. astep. rewrite short_byte0A. astep. step. if_true.
      apply evt_done. eapply (K_eqA K); [apply HK| atp_st_eq].
    + astep. astep. astep. rewrite short_byte0A. astep. step. if_false.
      apply evt_done. eapply (K_eqA K); [apply HK| atp_st_eq].
Qed.

Lemma sr_walk5 : forall (K : machine_state -> Prop) (sp lo S : Z) (lg : bool) (A cap sz pos lit : Z)
    (rax gp tp t0 t1 t2 xa0 a2 a3 a4 a5 a6 a7 s6x s7x s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 : word) (bsx : list byte)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  shdrA m S lg A cap sz -> u8arr asegs m A bsx -> Z.of_nat (length bsx) = cap -> 2 <= sz -> sz < cap -> cap < 2^40 -> 0 < S -> S + 24 <= lo -> 0 < A -> A + cap <= lo ->
  (lg = false \/ S + 24 <= A \/ A + cap <= S) ->
  stk asegs m lo (sp - 80) -> lo <= sp - 80 -> 0x6ca000 <= lo -> sp < 2^47 -> rw_cells asegs m (sp - 80) (sr_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8) -> mem_inv asegs m ->
  (forall (m1 : mem), munch [(S, S + 24); (A + (sz - 1), A + sz)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 -> stk asegs m1 lo sp ->
     shdrA m1 S lg A cap (sz - 1) -> u8arr asegs m1 A (upd bsx (Z.to_nat (sz - 1)) (Z_to_bv 8 0)) ->
     K (MS (mkR ra (wz sp) gp tp t0 t1 t2 s0 s1 (wz S) (wz 18446744073709551615) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (ret_pc ra) fc None m1 (seg_rom asegs))) ->
  evt asegs K (MS (mkR rax (wz (sp - 80)) gp tp t0 t1 t2 (wz S) (wz 1) xa0 (wz 18446744073709551615) a2 a3 a4 a5 a6 a7
                      (wz (sz - 1)) (wz lit) (wz 2) (wz pos) s6x s7x (wz A) s9 s10 s11 t3 t4 t5 t6)
                 F (wz (if lg then 0x108018 else 0x108094)) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros HDR DA LBS SZ2 SZC CAP S0 SLO A0 ALO SEP ST LO GLO SPH FR MI HK. unfold shdrA in HDR. unfold sr_frame in FR.
  pose proof (munch_refl [(S, S + 24); (A + (sz - 1), A + sz)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  replace (sp - 80) with (sp + -80) in ST, FR |- * by lia.
  destruct lg; [destruct HDR as [HDR EV]| destruct HDR as (HDR & EA & ECAP)].
  -
    lstep. step. name_mem m1.
    lazymatch type of HDR with rw_cells _ _ _ [_; C8 (Z_to_bv 64 ?x); _] => replace x with (sz - 1) in HDR by lia end.

    astep.
    pose proof (u8arr_store_ok asegs _ _ _ (sz - 1) (Z_to_bv 64 (A + (sz - 1))) DA ltac:(lia) ltac:(reflexivity)) as SOK.
    step. change (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0]. change (write_to_mem m1 (Z_to_bv 64 (A + (sz - 1)))) with (write_to_mem m1 (wa (A + (sz - 1)))).
    pose proof (u8arr_write asegs _ _ _ (sz - 1) (Z_to_bv 8 0) DA ltac:(lia)) as DA2. clear DA. store_done. name_mem m2.

    step. do 10 step. step. release_frame FR ST sp. step.
    apply evt_done. eapply (K_eqA K); [eapply (HK m2); [exact MU| exact WM| assumption| assumption| unfold shdrA; split; [exact HDR| exact EV]| exact DA2]| atp_st_eq].
  -
    astep. step. rewrite le1_smallA by lia. mem_after_store. name_mem m1.
    lazymatch type of HDR with rw_cells _ _ _ [C1 (Z_to_bv 8 ?x)] => replace x with (2 * (sz - 1)) in HDR by lia end.
    astep.
    pose proof (u8arr_store_ok asegs _ _ _ (sz - 1) (Z_to_bv 64 (A + (sz - 1))) DA ltac:(lia) ltac:(reflexivity)) as SOK.
    step. change (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0]. change (write_to_mem m1 (Z_to_bv 64 (A + (sz - 1)))) with (write_to_mem m1 (wa (A + (sz - 1)))).
    pose proof (u8arr_write asegs _ _ _ (sz - 1) (Z_to_bv 8 0) DA ltac:(lia)) as DA2. clear DA. store_done. name_mem m2.
    step. do 10 step. step. release_frame FR ST sp. step.
    apply evt_done. eapply (K_eqA K); [eapply (HK m2); [exact MU| exact WM| assumption| assumption| unfold shdrA; split; [exact HDR| split; [exact EA| exact ECAP]]| exact DA2]| atp_st_eq].
Qed.

Lemma lstrA_agree : forall (m m' : mem) S lg A cap sz,
  lstrA m S lg A cap sz -> agree_on (fun x => S <= x < S + 24 \/ A <= x < A + cap) m m' -> lstrA m' S lg A cap sz.
Proof.
  intros m m' S lg A cap sz (SZ0 & SZC & CAP & A0 & AC & (bs & [BS BW] & LBS & NUL) & REP) AG.
  split; [exact SZ0|]. split; [exact SZC|]. split; [exact CAP|]. split; [exact A0|]. split; [exact AC|]. split.
  - exists bs. split; [| split; [exact LBS| exact NUL]]. split.
    + apply (bytes_at_agree asegs m m' _ _ BS). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta. lia.
    + apply (wr_at_agree_nw asegs m m' _ _ BW). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta. lia.
  - destruct lg; [destruct REP as [HDR EV]| destruct REP as (HDR & EA & ECAP)].
    + split; [| exact EV]. apply (rw_cells_agree_nw asegs m m' _ _ HDR). eapply agree_sub; [exact AG|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. lia.
    + split; [| split; [exact EA| exact ECAP]]. apply (rw_cells_agree_nw asegs m m' _ _ HDR). eapply agree_sub; [exact AG|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. lia.
Qed.

Section ObjS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis RC2 : rt_contracts2 RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.

Lemma lstr_cls_range : forall Σ m A n, ART RT Σ m -> lstr_cls RT Σ A n -> 0 <= n -> 0 < A /\ A + n <= rt_sp0 RT Σ - STACK_WIN.
Proof using AF.
  intros Σ m A n HA [(f & k & Hin & H1 & H2)|(p & k & Hin & H1 & H2)] Hn.
  - pose proof (af_frames_range RT AF Σ m f k HA Hin) as (R0 & R1 & _). lia.
  - pose proof (af_live_range RT AF Σ m p k HA Hin) as (R0 & R1 & _). lia.
Qed.

Lemma lstr_acc_agree : forall Σ (m m' : mem) A n, ART RT Σ m -> ART RT Σ m' -> lstr_cls RT Σ A n -> 0 <= n -> acc asegs m A n ->
  (forall f c, In (f, c) (rt_frames RT Σ) -> f <= A -> A + n <= f + fs_size c - 8 -> (f + fs_size c <= shad f \/ shad (f + fs_size c) <= f) ->
     forall a : word, shad f <= bv_unsigned a < shad (f + fs_size c) -> m' a = m a) ->
  acc asegs m' A n.
Proof using AF.
  intros Σ m m' A n HA HA' CLS Hn ACC AG.
  destruct CLS as [(f & c & Hin & H1 & H2)|(p & c & Hin & H1 & H2)].
  - intros i Hi. destruct (ACC i Hi) as (b & Hb & Hok). exists b. split; [| exact Hok].
    apply (bytes_at_agree asegs m m' _ _ Hb). intros a Ha. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in Ha.
    pose proof (fframe_ranges RT AF Σ m f c HA Hin) as (F0 & F1 & FSZ & SH0 & SH1).
    pose proof (proj2 (af_fshadow_apart RT AF Σ m f c HA Hin) f c Hin) as FSELF.
    assert (SA : shad f <= shad (A + i) /\ shad (A + i) < shad (f + fs_size c)).
    { unfold shad. pose proof (Z.div_le_mono f (A + i) 8 ltac:(lia) ltac:(lia)). assert ((A + i) / 8 < (f + fs_size c) / 8) by (Z.div_mod_to_equations; lia). lia. }
    apply (AG f c Hin H1 H2 FSELF). lia.
  - apply (acc_sub asegs m' p c A n); [exact (proj2 (af_acc_live RT AF Σ m' p c HA' Hin))| lia| lia].
Qed.

Lemma lstr_acc_pres : forall Σ (m m' : mem) sp A n (d k : Z), ART RT Σ m -> ART RT Σ m' -> lstr_cls RT Σ A n -> 0 <= n -> acc asegs m A n ->
  rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) sp d k m m' -> (k <= 0 \/ (A <= d /\ d + k <= A + n)) -> acc asegs m' A n.
Proof using AF.
  intros Σ m m' sp A n d k HA HA' CLS Hn ACC PRES ND.
  apply (lstr_acc_agree Σ m m' A n HA HA' CLS Hn ACC). intros f c Hin H1 H2 FSELF a Ha.
  apply PRES; [| destruct ND as [ND|[ND1 ND2]]; lia]. right; right; right; right. exists f, c. split; [exact Hin| lia].
Qed.

Theorem aevt_str_find : forall Σ K (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem)
    (sp S : Z) (lg : bool) (A cap sz pos lo : Z),
  lstrA m S lg A cap sz -> lstr_cls RT Σ A cap -> lstr_cls RT Σ S 24 -> acc asegs m A cap -> 0 <= pos < 2^62 ->
  ART RT Σ m -> mem_inv asegs m -> stk asegs m lo sp -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 16 <= sp -> sp + 16 <= USTACK_TOP -> sp mod 16 = 0 ->
  (forall (r : Z) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (m' : mem),
     (r = 18446744073709551615 \/ pos <= r < sz) ->
     lstrA m' S lg A cap sz -> acc asegs m' A cap -> ART RT Σ m' -> mem_inv asegs m' -> stk asegs m' lo sp -> wmono asegs m m' ->
     rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) sp 0 0 m m' ->
     aevt RT PMc Σ K (MS (mkR ra (wz sp) gp tp t0' t1' t2' s0 s1 (wz r) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                      F' (ret_pc ra) fc None m' (seg_rom asegs))) ->
  aevt RT PMc Σ K (MS (mkR ra (wz sp) gp tp t0 t1 t2 s0 s1 (wz S) (wz 126) (wz pos) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (wz STR_FIND_A) fc None m (seg_rom asegs)).
Proof using AF RC FDO MST.
  intros until lo. intros LS CLA CLSS ACC POS ART0 MI ST LOW LOR SPT SPA HK.
  pose proof LS as (SZ0 & SZC & CAP & A0 & AC & (bs & [BS BW] & LBS & NUL) & _).
  pose proof (lstr_cls_range Σ m A cap ART0 CLA ltac:(lia)) as [_ AHI]. pose proof (lstr_cls_range Σ m S 24 ART0 CLSS ltac:(lia)) as [S0 SHI].
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  destruct (Z.lt_ge_cases pos sz) as [PL|PG].
  2:{ apply (aevt_evt RT AF PMc MST). eapply (sf_walk0 _ sp S lg A cap sz pos); [exact LS| lia| lia| ul| exact MI|].
      intros xa3 xa4. apply (HK 18446744073709551615); [left; reflexivity| exact LS| exact ACC| exact ART0| exact MI| exact ST| apply wmono_refl| intros a _ _; reflexivity]. }
  apply (aevt_evt RT AF PMc MST). eapply (sf_walk1 _ sp lo S lg A cap sz pos); [exact LS| lia| lia| ul| left; ul| exact ST| ul| ul| ul| exact MI|].
  intros m1 xa3 xa4 MU1 WM1 MI1 ST1 FR1.
  assert (ART1 : ART RT Σ m1).
  { apply (art_client_write RT AF Σ m m1 lo ART0 LOW); [| exact WM1]. intros a Ha. apply MU1. cbn [outside]. split; [| exact I]. intros X. apply Ha. left. ul. }
  assert (AG1 : forall a : word, bv_unsigned a < lo -> m1 a = m a). { intros a Ha. apply MU1. cbn [outside]. split; [ul| exact I]. }
  assert (BS1 : bytes_at asegs m1 A bs). { apply (bytes_at_agree asegs m m1 _ _ BS). intros a Ha. apply AG1. lia. }
  assert (ACC1 : acc asegs m1 A cap).
  { intros i Hi. destruct (ACC i Hi) as (b & Hb & Hok). exists b. split; [| exact Hok]. apply (bytes_at_agree asegs m m1 _ _ Hb). intros a Ha.
    cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in Ha. apply AG1. unfold shad, SHB in Ha. ul. }
  assert (EU : bv_unsigned (wz (sp - 16)) = sp - 16) by (apply unsigned_lit; ul).
  eapply (aevt_memchrP RT RC PMc FDO MST Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 (A + pos) 126 (sz - pos) (skipn (Z.to_nat pos) bs) lo
            eq_refl eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(lia)).
  - replace (A + pos) with (A + Z.of_nat (Z.to_nat pos)) by lia. apply bytes_at_skipn; [exact BS1| lia].
  - unfold memchr_ok. destruct (find_byte 126 (firstn (Z.to_nat (sz - pos)) (skipn (Z.to_nat pos) bs))); rewrite length_skipn; [left|]; lia.
  - left. rewrite length_skipn. lia.
  - assert (CHK : 0 <= memchr_chk 126 (sz - pos) (skipn (Z.to_nat pos) bs) <= sz - pos).
    { unfold memchr_chk. destruct (find_byte 126 (firstn (Z.to_nat (sz - pos)) (skipn (Z.to_nat pos) bs))) as [i|] eqn:FB; [| lia].
      pose proof (find_byte_Some _ _ _ FB) as (Hl & _). rewrite length_firstn, length_skipn in Hl. lia. }
    split; [| left; lia]. intros _. split; [apply (acc_sub asegs m1 A cap); [exact ACC1| lia| lia]| apply lstr_cls_rng; apply (lstr_cls_sub RT Σ A cap); [exact CLA| lia| lia]].
  - exact ART1.
  - exact MI1.
  - unfold call_ok. rewrite EU. split; [exact ST1|]. split; [exact LOW|]. split; [ul|]. split; [ul| Z.div_mod_to_equations; lia].
  - intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m2 (ART2 & MI2 & WM2 & ST2) PRES2. rewrite EU in ST2, PRES2.
    assert (AG2 : forall a : word, sp - 16 <= bv_unsigned a < USTACK_TOP -> m2 a = m1 a) by (intros a Ha; apply PRES2; [left; exact Ha| lia]).
    assert (FR2 : rw_cells asegs m2 (sp - 16) [C8 s0; C8 ra]).
    { apply (rw_cells_agree_nw asegs m1 m2 _ _ FR1). intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply AG2. ul. }
    rewrite (ret_pc_even 0x108898) by lia.
    apply (aevt_evt RT AF PMc MST). eapply (sf_walk2 _ sp lo A); [exact ST2| ul| ul| ul| exact FR2| lia| lia| | exact MI2|].
    { unfold memchr_res. destruct (find_byte 126 (firstn (Z.to_nat (sz - pos)) (skipn (Z.to_nat pos) bs))) as [i|] eqn:FB; [| left; reflexivity].
      pose proof (find_byte_Some _ _ _ FB) as (Hl & _). rewrite length_firstn, length_skipn in Hl. right. lia. }
    intros xa1 ST3.
    assert (AGC : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) sp (bv_unsigned a) -> m2 a = m a).
    { intros a Ha. pose proof (aclient_split_c RT AF Σ m sp (bv_unsigned a) ART0 Ha) as SPL.
      rewrite (PRES2 a); [| apply (aclient_mono _ _ _ _ _ _ _ Ha); auto; lia| lia]. apply MU1. cbn [outside]. split; [ul| exact I]. }
    apply HK.
    + unfold memchr_res. destruct (find_byte 126 (firstn (Z.to_nat (sz - pos)) (skipn (Z.to_nat pos) bs))) as [i|] eqn:FB; [| left; reflexivity].
      pose proof (find_byte_Some _ _ _ FB) as (Hl & _). rewrite length_firstn, length_skipn in Hl. right.
      destruct (Z.eqb_spec (A + pos + Z.of_nat i) 0); lia.
    + apply (lstrA_agree m m2 _ _ _ _ _ LS). intros a [Ha|Ha]; apply AGC; [exact (lstr_cls_client RT Σ sp S 24 _ CLSS Ha)| exact (lstr_cls_client RT Σ sp A cap _ CLA Ha)].
    + exact (lstr_acc_pres Σ m1 m2 (sp - 16) A cap 0 0 ART1 ART2 CLA ltac:(lia) ACC1 PRES2 ltac:(left; lia)).
    + exact ART2.
    + exact MI2.
    + exact ST3.
    + exact (wmono_trans _ _ _ _ WM1 WM2).
    + intros a Ha _. exact (AGC a Ha).
Qed.

Definition litc (lit : Z) : Z := if lit =? 0x23800 then 126 else 47.

Lemma lit_bytesA : forall (m : mem) lit, (lit = 0x23800 \/ lit = 0x23820) -> mem_inv asegs m ->
  bytes_at asegs m lit ([Z_to_bv 8 (litc lit)] ++ Z_to_bv 8 0 :: repeat (Z_to_bv 8 0) 6).
Proof.
  intros m lit [-> | ->] MI; unfold litc; cbn [Z.eqb Pos.eqb repeat app].
  - assert (R : ro_cells asegs m 0x23800 [CB 8 [Z_to_bv 8 126; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]).
    { apply (ro_cells_image asegs m); [exact MI| vm_compute; reflexivity| lia| cbn; lia]. }
    destruct R as [_ B]. cbn [cells_bytes cbytes app] in B. exact B.
  - assert (R : ro_cells asegs m 0x23820 [CB 8 [Z_to_bv 8 47; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]).
    { apply (ro_cells_image asegs m); [exact MI| vm_compute; reflexivity| lia| cbn; lia]. }
    destruct R as [_ B]. cbn [cells_bytes cbytes app] in B. exact B.
Qed.

Lemma lit_accA : forall Σ m lit, ART RT Σ m -> (lit = 0x23800 \/ lit = 0x23820) -> acc asegs m lit 2.
Proof using AF.
  intros Σ m lit HA LIT. pose proof (af_acc_lits RT AF Σ m HA) as AL. rewrite Forall_forall in AL.
  destruct LIT as [-> | ->]; [exact (AL (0x23800, 2) ltac:(cbn; tauto))| exact (AL (0x23820, 2) ltac:(cbn; tauto))].
Qed.

Theorem aevt_str_replace : forall Σ K (ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem)
    (sp S : Z) (lg : bool) (A cap sz pos lit lo : Z),
  lstrA m S lg A cap sz -> lstr_cls RT Σ A cap -> lstr_cls RT Σ S 24 -> acc asegs m A cap ->
  (lg = false \/ S + 24 <= A \/ A + cap <= S) ->
  0 <= pos -> pos + 2 <= sz -> (lit = 0x23800 \/ lit = 0x23820) ->
  ART RT Σ m -> mem_inv asegs m -> stk asegs m lo sp -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 80 <= sp -> sp + 16 <= USTACK_TOP -> sp mod 16 = 0 ->
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (m' : mem),
     lstrA m' S lg A cap (sz - 1) -> acc asegs m' A cap -> ART RT Σ m' -> mem_inv asegs m' -> stk asegs m' lo sp -> wmono asegs m m' ->
     (forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) sp (bv_unsigned a) -> ~ (S <= bv_unsigned a < S + 24) -> ~ (A <= bv_unsigned a < A + cap) ->
        m' a = m a) ->
     aevt RT PMc Σ K (MS (mkR ra (wz sp) gp tp t0' t1' t2' s0 s1 (wz S) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                      F' (ret_pc ra) fc None m' (seg_rom asegs))) ->
  aevt RT PMc Σ K (MS (mkR ra (wz sp) gp tp t0 t1 t2 s0 s1 (wz S) (wz pos) (wz 2) (wz lit) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (wz STR_REPLACE_A) fc None m (seg_rom asegs)).
Proof using AF RC RC2 FDO MST.
  intros until lo. intros LS CLA CLSS ACC SEP POS PS LIT ART0 MI ST LOW LOR SPT SPA HK.
  pose proof LS as (SZ0 & SZC & CAP & A0 & AC & _ & _).
  pose proof (lstr_cls_range Σ m A cap ART0 CLA ltac:(lia)) as [_ AHI]. pose proof (lstr_cls_range Σ m S 24 ART0 CLSS ltac:(lia)) as [S0 SHI].
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  assert (LITR : 0x10000 <= lit /\ lit + 8 <= 0x6ca000) by (clear - LIT; destruct LIT; subst lit; lia).
  assert (LITC : 0 < litc lit < 256) by (unfold litc; destruct (lit =? 0x23800); lia).

  assert (CLo : forall sp' a, (S <= a < S + 24 \/ A <= a < A + cap) -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' a).
  { intros sp' a [Ha|Ha]; [exact (lstr_cls_client RT Σ sp' S 24 a CLSS Ha)| exact (lstr_cls_client RT Σ sp' A cap a CLA Ha)]. }
  assert (ACCLO : forall (mA mB : mem), acc asegs mA A cap -> (forall a : word, bv_unsigned a < lo -> mB a = mA a) -> acc asegs mB A cap).
  { intros mA mB HA AG i Hi. destruct (HA i Hi) as (b & Hb & Hok). exists b. split; [| exact Hok]. apply (bytes_at_agree asegs mA mB _ _ Hb). intros a Ha.
    cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in Ha. apply AG. unfold shad, SHB in Ha. ul. }

  apply (aevt_evt RT AF PMc MST). eapply (sr_walk1 _ sp lo lit); [exact ST| ul| ul| ul| lia| exact MI|].
  intros m1 j MU1 WM1 MI1 ST1 FR1.
  assert (AG1 : forall a : word, bv_unsigned a < lo -> m1 a = m a). { intros a Ha. apply MU1. cbn [outside]. split; [ul| exact I]. }
  assert (ART1 : ART RT Σ m1).
  { apply (art_client_write RT AF Σ m m1 lo ART0 LOW); [| exact WM1]. intros a Ha. apply MU1. cbn [outside]. split; [| exact I]. intros X. apply Ha. left. ul. }
  assert (LS1 : lstrA m1 S lg A cap sz). { apply (lstrA_agree m m1 _ _ _ _ _ LS). intros a Ha. apply AG1. lia. }
  pose proof (ACCLO m m1 ACC AG1) as ACC1.
  assert (EU1 : bv_unsigned (wz (sp - 48)) = sp - 48) by (apply unsigned_lit; ul).

  eapply (aevt_strlenP RT RC PMc FDO MST Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 lit [Z_to_bv 8 (litc lit)] (repeat (Z_to_bv 8 0) 6) lo
            eq_refl (lit_bytesA m1 lit LIT MI1)).
  - intros [X|[]]. apply (f_equal bv_unsigned) in X. rewrite !a_u8_small in X by lia. lia.
  - cbn. lia.
  - cbn [length Z.of_nat Pos.of_succ_nat Pos.succ repeat]. clear - LIT. destruct LIT; subst lit; cbn; lia.
  - ul.
  - left. rewrite repeat_length. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]. ul.
  - split; [| left; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; ul]. intros _. split; [exact (lit_accA Σ m1 lit ART1 LIT)| right; right; right; unfold SEGTOP_A; cbn; lia].
  - exact ART1.
  - exact MI1.
  - unfold call_ok. rewrite EU1. split; [exact ST1|]. split; [exact LOW|]. split; [ul|]. split; [ul| clear - SPA; Z.div_mod_to_equations; lia].
  - intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m2 (ART2 & MI2 & WM2 & ST2) PRES2. rewrite EU1 in ST2, PRES2.
    cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite (ret_pc_even 0x108310) by lia.
    assert (AG2 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) (sp - 48) (bv_unsigned a) -> m2 a = m1 a) by (intros a Ha; apply PRES2; [exact Ha| lia]).
    assert (FR2 : rw_cells asegs m2 (sp - 48) [CB 8 j; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { apply (rw_cells_agree_nw asegs m1 m2 _ _ FR1). intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply AG2. left. ul. }
    assert (LS2 : lstrA m2 S lg A cap sz). { apply (lstrA_agree m1 m2 _ _ _ _ _ LS1). intros a Ha. apply AG2. exact (CLo _ _ Ha). }
    pose proof (lstr_acc_pres Σ m1 m2 (sp - 48) A cap 0 0 ART1 ART2 CLA ltac:(lia) ACC1 PRES2 ltac:(left; lia)) as ACC2.

    apply (aevt_evt RT AF PMc MST). eapply (sr_walk2 _ sp lo S lg A cap sz pos lit); [exact LS2| exact POS| exact PS| ul| ul| lia| exact ST2| ul| ul| ul| exact MI2| exact FR2|].
    intros m3 xa1 xa3 xa4 MU3 WM3 MI3 ST3 FR3.
    assert (AG3 : forall a : word, bv_unsigned a < lo -> m3 a = m2 a). { intros a Ha. apply MU3. cbn [outside]. split; [ul| exact I]. }
    assert (ART3 : ART RT Σ m3).
    { apply (art_client_write RT AF Σ m2 m3 lo ART2 LOW); [| exact WM3]. intros a Ha. apply MU3. cbn [outside]. split; [| exact I]. intros X. apply Ha. left. ul. }
    assert (LS3 : lstrA m3 S lg A cap sz). { apply (lstrA_agree m2 m3 _ _ _ _ _ LS2). intros a Ha. apply AG3. lia. }
    pose proof (ACCLO m2 m3 ACC2 AG3) as ACC3.
    assert (EU3 : bv_unsigned (wz (sp - 80)) = sp - 80) by (apply unsigned_lit; ul).
    pose proof LS3 as (_ & _ & _ & _ & _ & (bs & [BS BW] & LBS & NUL) & REP). rewrite LBS in BW.
    assert (HDR3 : shdrA m3 S lg A cap sz) by exact REP.

    assert (HSEP : forall a, S <= a < (if lg then S + 24 else S + 1) -> ~ (A + pos <= a < A + sz)).
    { intros a Ha. destruct lg; [clear - Ha SEP POS PS SZC; destruct SEP as [X|[X|X]]; [discriminate X| lia| lia]|].
      destruct REP as (_ & EA & _). clear - Ha EA POS. lia. }
    assert (HDRX : forall mA mB, shdrA mA S lg A cap sz -> (forall a : word, S <= bv_unsigned a < (if lg then S + 24 else S + 1) -> mB a = mA a) -> shdrA mB S lg A cap sz).
    { intros mA mB H AG. unfold shdrA in *. destruct lg; [destruct H as [H EV]| destruct H as (H & EA & ECAP)];
        (split; [apply (rw_cells_agree_nw asegs mA mB _ _ H); intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply AG; lia| auto]). }

    assert (FIN : forall (pc0 : Z) (mx : mem) (bsx : list byte) (y0 y1 y2 b0 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 s6x s7x : word) (Fx : bvmap 5 word),
      (pc0 = 0x108004 \/ pc0 = 0x108080) ->
      ART RT Σ mx -> mem_inv asegs mx -> stk asegs mx lo (sp - 80) -> wmono asegs m mx ->
      rw_cells asegs mx (sp - 80) (sr_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8) -> shdrA mx S lg A cap sz ->
      u8arr asegs mx A bsx -> Z.of_nat (length bsx) = cap -> acc asegs mx A cap ->
      (forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) sp (bv_unsigned a) -> ~ (S <= bv_unsigned a < S + 24) -> ~ (A <= bv_unsigned a < A + cap) -> mx a = m a) ->
      aevt RT PMc Σ K (MS (mkR (wz pc0) (wz (sp - 80)) gp tp y0 y1 y2 (wz S) (wz 1) b0 b1 b2 b3 b4 b5 b6 b7
                            (wz sz) (wz lit) (wz 2) (wz pos) s6x s7x (wz A) s9 s10 s11 y3 y4 y5 y6) Fx (wz pc0) fc None mx (seg_rom asegs))).
    { intros pc0 mx bsx y0 y1 y2 b0 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 s6x s7x Fx PC ARTx MIx STx WMx FRx HDRx DAx LBSx ACCx AGx.
      apply (aevt_evt RT AF PMc MST). eapply (sr_walk4 _ pc0 (sp - 80) S lg A cap sz pos lit); [exact PC| exact HDRx| lia| lia| lia| lia| ul| exact MIx|].
      intros xa0.
      apply (aevt_evt RT AF PMc MST).
      eapply (sr_walk5 _ sp lo S lg A cap sz pos lit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ra s0 s1 s2 s3 s4 s5 s6 s7 s8 bsx);
        [exact HDRx| exact DAx| exact LBSx| lia| lia| lia| lia| ul| lia| ul| exact SEP| exact STx| ul| ul| ul| exact FRx| exact MIx|].
      intros m5 MU5 WM5 MI5 ST5 HDR5 DA5.
      assert (ART5 : ART RT Σ m5).
      { apply (art_client_write RT AF Σ mx m5 lo ARTx LOW); [| exact WM5]. intros a Ha. apply MU5. cbn [outside].
        split; [intros X; apply Ha; apply (CLo lo); left; exact X|]. split; [| exact I]. intros X; apply Ha; apply (CLo lo); right; lia. }
      apply HK.
      - split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [| exact HDR5].
        exists (upd bsx (Z.to_nat (sz - 1)) (Z_to_bv 8 0)). split; [exact DA5|]. split; [rewrite upd_length; exact LBSx| apply nth_upd_sameA; lia].
      - apply (lstr_acc_agree Σ mx m5 A cap ARTx ART5 CLA ltac:(lia) ACCx). intros f c Hin H1 H2 FSELF a Ha.
        pose proof (af_fshadow_apart RT AF Σ mx f c ARTx Hin) as [FSL FSF].
        apply MU5. cbn [outside]. split; [| split; [clear - Ha FSELF H1 H2 SZC PS POS; lia| exact I]].
        destruct CLSS as [(f' & k' & Hin' & Q1 & Q2)|(p' & k' & Hin' & Q1 & Q2)].
        + pose proof (FSF f' k' Hin') as Y. pose proof (proj1 (proj2 (proj2 (fframe_ranges RT AF Σ mx f' k' ARTx Hin')))) as FSZ'. clear - Ha Y Q1 Q2 FSZ'. lia.
        + pose proof (FSL p' k' Hin') as Y. clear - Ha Y Q1 Q2. lia.
      - exact ART5.
      - exact MI5.
      - exact ST5.
      - exact (wmono_trans _ _ _ _ WMx WM5).
      - intros a Ha N1 N2. rewrite <- (AGx a Ha N1 N2). apply MU5. cbn [outside]. clear - N1 N2 SZC PS POS. lia. }

    pose proof (proj1 (proj1 (bytes_at_app asegs m3 lit [Z_to_bv 8 (litc lit)] _) (lit_bytesA m3 lit LIT MI3))) as LITB3.
    assert (COK3 : call_ok RT Σ m3 (wz (sp - 80)) lo).
    { unfold call_ok. rewrite EU3. split; [exact ST3|]. split; [exact LOW|]. split; [ul|]. split; [ul| clear - SPA; Z.div_mod_to_equations; lia]. }
    assert (CSL : checked_src RT Σ m3 (wz (sp - 80)) lo lit (Z.of_nat (length [Z_to_bv 8 (litc lit)]))).
    { cbn [length Z.of_nat Pos.of_succ_nat]. split; [| left; ul]. intros _. split; [apply (acc_sub asegs m3 lit 2); [exact (lit_accA Σ m3 lit ART3 LIT)| lia| lia]|].
      right; right; right. unfold SEGTOP_A. lia. }
    assert (WRX : forall (mq : mem) d k, wr_at asegs mq A cap -> A <= d -> 0 <= k -> d + k <= A + cap -> wr_at asegs mq d k).
    { intros mq d k W D1 K0 D2. destruct (wr_at_split asegs mq A cap (d - A) W ltac:(lia)) as [_ W2]. replace (A + (d - A)) with d in W2 by lia.
      destruct (wr_at_split asegs mq d (cap - (d - A)) k W2 ltac:(lia)) as [W3 _]. exact W3. }
    assert (CDST : forall (mq : mem) d k, acc asegs mq A cap -> wr_at asegs mq A cap -> A <= d -> 0 <= k -> d + k <= A + cap -> checked_dst RT Σ mq (wz (sp - 80)) d k).
    { intros mq d k AC0 W D1 K0 D2. split; [| split; [intros i Hi; apply (CLo _ (d + i)); right; lia| exact (WRX mq d k W D1 K0 D2)]].
      intros _. split; [exact (acc_sub asegs mq A cap d k AC0 D1 D2)| apply lstr_cls_rng; exact (lstr_cls_sub RT Σ A cap d k CLA D1 D2)]. }
    destruct (Z.eq_dec (sz - pos) 2) as [NT|TL].
    +
      apply (aevt_evt RT AF PMc MST). eapply (sr_walk2n _ (sp - 80) S A sz pos lit); [exact NT| exact POS| lia| lia| exact MI3|].
      eapply (aevt_memmove2P RT PMc FDO MST RC2 Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 (A + pos) lit [Z_to_bv 8 (litc lit)] lo
                eq_refl eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(cbn; lia) LITB3 CSL (CDST m3 (A + pos) 1 ACC3 BW ltac:(lia) ltac:(lia) ltac:(lia)) ART3 MI3 COK3).
      intros y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 F4 m4 (ART4 & MI4 & WM4 & ST4) PRES4 BY4. rewrite EU3 in ST4, PRES4.
      cbn [length Z.of_nat Pos.of_succ_nat] in PRES4. rewrite (ret_pc_even 0x108080) by lia.
      assert (AG4 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) (sp - 80) (bv_unsigned a) -> ~ (A + pos <= bv_unsigned a < A + pos + 1) -> m4 a = m3 a).
      { intros a Ha Hn. exact (PRES4 a Ha Hn). }
      eapply (FIN 0x108080 m4 (firstn (Z.to_nat pos) bs ++ [Z_to_bv 8 (litc lit)] ++ skipn (Z.to_nat pos + 1) bs));
        [right; reflexivity| exact ART4| exact MI4| exact ST4| exact (wmono_trans _ _ _ _ (wmono_trans _ _ _ _ (wmono_trans _ _ _ _ WM1 WM2) WM3) WM4)| | | | | |].
      * apply (rw_cells_agree_nw asegs m3 m4 _ _ FR3). intros a Ha. unfold sr_frame in Ha. cbn [cells_size csize Nat.add] in Ha. apply AG4; [left; ul| ul].
      * apply (HDRX m3 m4 HDR3). intros a Ha. apply AG4; [apply (CLo _ _); left; destruct lg; lia| pose proof (HSEP _ Ha); lia].
      * split.
        -- apply (proj2 (bytes_at_app asegs m4 A _ _)). split.
           ++ apply (bytes_at_agree asegs m3 m4 _ _ (bytes_at_firstn m3 A bs (Z.to_nat pos) BS)). intros a Ha. rewrite firstn_length_le in Ha by lia.
              apply AG4; [apply (CLo _ _); right; lia| lia].
           ++ rewrite firstn_length_le by lia. rewrite Z2Nat.id by lia. apply (proj2 (bytes_at_app asegs m4 (A + pos) _ _)). split; [exact BY4|].
              lazymatch goal with |- bytes_at _ _ ?ad _ => replace ad with (A + Z.of_nat (Z.to_nat pos + 1)) by (cbn; lia) end.
              apply (bytes_at_agree asegs m3 m4 _ _ (bytes_at_skipn m3 A bs (Z.to_nat pos + 1) BS ltac:(lia))). intros a Ha. rewrite length_skipn in Ha.
              apply AG4; [apply (CLo _ _); right; lia| lia].
        -- rewrite !length_app, firstn_length_le, length_skipn by lia. cbn [length]. replace (Z.of_nat (Z.to_nat pos + (1 + (length bs - (Z.to_nat pos + 1))))) with cap by lia.
           exact (wr_at_transport asegs m3 m4 A cap BW WM4).
      * rewrite !length_app, firstn_length_le, length_skipn by lia. cbn [length]. lia.
      * exact (lstr_acc_pres Σ m3 m4 (sp - 80) A cap (A + pos) 1 ART3 ART4 CLA ltac:(lia) ACC3 PRES4 ltac:(right; lia)).
      * intros a Ha N1 N2. pose proof (aclient_split_c RT AF Σ m sp (bv_unsigned a) ART0 Ha) as SPL.
        rewrite (AG4 a); [| apply (aclient_mono _ _ _ _ _ _ _ Ha); auto; lia| lia].
        rewrite (MU3 a); [| cbn [outside]; split; [clear - SPL LOW LOR; ul| exact I]].
        rewrite (AG2 a); [| apply (aclient_mono _ _ _ _ _ _ _ Ha); auto; lia].
        apply MU1. cbn [outside]. split; [clear - SPL LOW LOR; ul| exact I].
    +
      assert (TL' : 2 < sz - pos) by lia.
      apply (aevt_evt RT AF PMc MST). eapply (sr_walk2t _ (sp - 80) S A sz pos lit); [exact TL'| exact POS| lia| lia| exact MI3|].
      eapply (aevt_memmove2P RT PMc FDO MST RC2 Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 (A + pos) lit [Z_to_bv 8 (litc lit)] lo
                eq_refl eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(cbn; lia) LITB3 CSL (CDST m3 (A + pos) 1 ACC3 BW ltac:(lia) ltac:(lia) ltac:(lia)) ART3 MI3 COK3).
      intros y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 F4 m4 (ART4 & MI4 & WM4 & ST4) PRES4 BY4. rewrite EU3 in ST4, PRES4.
      cbn [length Z.of_nat Pos.of_succ_nat] in PRES4. rewrite (ret_pc_even 0x107ff4) by lia.
      assert (AG4 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) (sp - 80) (bv_unsigned a) -> ~ (A + pos <= bv_unsigned a < A + pos + 1) -> m4 a = m3 a).
      { intros a Ha Hn. exact (PRES4 a Ha Hn). }
      pose proof (lstr_acc_pres Σ m3 m4 (sp - 80) A cap (A + pos) 1 ART3 ART4 CLA ltac:(lia) ACC3 PRES4 ltac:(right; lia)) as ACC4.
      pose proof (wr_at_transport asegs m3 m4 A cap BW WM4) as BW4.
      assert (COK4 : call_ok RT Σ m4 (wz (sp - 80)) lo).
      { unfold call_ok. rewrite EU3. split; [exact ST4|]. split; [exact LOW|]. split; [ul|]. split; [ul| clear - SPA; Z.div_mod_to_equations; lia]. }

      set (src := firstn (Z.to_nat (sz - pos - 2)) (skipn (Z.to_nat pos + 2) bs)).
      assert (LSRC : length src = Z.to_nat (sz - pos - 2)) by (subst src; rewrite firstn_length_le; [reflexivity| rewrite length_skipn; lia]).
      assert (SRC4 : bytes_at asegs m4 (A + pos + 2) src).
      { subst src. replace (A + pos + 2) with (A + Z.of_nat (Z.to_nat pos + 2)) by lia.
        apply (bytes_at_agree asegs m3 m4 _ _ (bytes_at_firstn m3 _ _ _ (bytes_at_skipn m3 A bs (Z.to_nat pos + 2) BS ltac:(lia)))). intros a Ha.
        rewrite firstn_length_le in Ha by (rewrite length_skipn; lia). apply AG4; [apply (CLo _ _); right; lia| lia]. }
      assert (CS5 : checked_src RT Σ m4 (wz (sp - 80)) lo (A + pos + 2) (Z.of_nat (length src))).
      { split; [| left; rewrite LSRC; ul]. intros _. rewrite LSRC, Z2Nat.id by lia.
        split; [apply (acc_sub asegs m4 A cap); [exact ACC4| lia| lia]| apply lstr_cls_rng; apply (lstr_cls_sub RT Σ A cap); [exact CLA| lia| lia]]. }
      assert (CD5 : checked_dst RT Σ m4 (wz (sp - 80)) (A + pos + 1) (Z.of_nat (length src))).
      { rewrite LSRC, Z2Nat.id by lia. exact (CDST m4 (A + pos + 1) (sz - pos - 2) ACC4 BW4 ltac:(lia) ltac:(lia) ltac:(lia)). }
      apply (aevt_evt RT AF PMc MST). eapply (sr_walk3 _ (sp - 80) S A sz pos lit); [exact TL'| exact POS| lia| lia| exact MI4|].
      eapply (aevt_memmove2P RT PMc FDO MST RC2 Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 (A + pos + 1) (A + pos + 2) src lo
                eq_refl eq_refl ltac:(rewrite LSRC, Z2Nat.id by lia; reflexivity) ltac:(lia) ltac:(lia) ltac:(rewrite LSRC; lia) SRC4 CS5 CD5 ART4 MI4 COK4).
      intros z0 z1 z2 e1 e2 e3 e4 e5 e6 e7 z3 z4 z5 z6 F5 m5 (ART5 & MI5 & WM5 & ST5) PRES5 BY5. rewrite EU3 in ST5, PRES5.
        rewrite LSRC, Z2Nat.id in PRES5 by lia. rewrite (ret_pc_even 0x108004) by lia.
        assert (AG5 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) (sp - 80) (bv_unsigned a) -> ~ (A + pos + 1 <= bv_unsigned a < A + pos + 1 + (sz - pos - 2)) ->
                        m5 a = m4 a).
        { intros a Ha Hn. exact (PRES5 a Ha Hn). }
        eapply (FIN 0x108004 m5 (firstn (Z.to_nat pos) bs ++ [Z_to_bv 8 (litc lit)] ++ src ++ skipn (Z.to_nat (sz - 1)) bs));
          [left; reflexivity| exact ART5| exact MI5| exact ST5
          | exact (wmono_trans _ _ _ _ (wmono_trans _ _ _ _ (wmono_trans _ _ _ _ (wmono_trans _ _ _ _ WM1 WM2) WM3) WM4) WM5)| | | | | |].
        -- apply (rw_cells_agree_nw asegs m3 m5 _ _ FR3). intros a Ha. unfold sr_frame in Ha. cbn [cells_size csize Nat.add] in Ha.
           rewrite (AG5 a); [| left; ul| ul]. apply AG4; [left; ul| ul].
        -- apply (HDRX m3 m5 HDR3). intros a Ha. pose proof (HSEP _ Ha) as NH.
           rewrite (AG5 a); [| apply (CLo _ _); left; destruct lg; lia| lia]. apply AG4; [apply (CLo _ _); left; destruct lg; lia| lia].
        -- split.
           ++ apply (proj2 (bytes_at_app asegs m5 A _ _)). split.
              ** apply (bytes_at_agree asegs m3 m5 _ _ (bytes_at_firstn m3 A bs (Z.to_nat pos) BS)). intros a Ha. rewrite firstn_length_le in Ha by lia.
                 rewrite (AG5 a); [| apply (CLo _ _); right; lia| lia]. apply AG4; [apply (CLo _ _); right; lia| lia].
              ** rewrite firstn_length_le by lia. rewrite Z2Nat.id by lia. apply (proj2 (bytes_at_app asegs m5 (A + pos) _ _)). split.
                 { apply (bytes_at_agree asegs m4 m5 _ _ BY4). intros a Ha. cbn [length Z.of_nat Pos.of_succ_nat] in Ha. apply AG5; [apply (CLo _ _); right; lia| lia]. }
                 lazymatch goal with |- bytes_at _ _ ?ad _ => replace ad with (A + pos + 1) by (cbn; lia) end.
                 apply (proj2 (bytes_at_app asegs m5 (A + pos + 1) _ _)). split; [exact BY5|]. rewrite LSRC, Z2Nat.id by lia.
                 replace (A + pos + 1 + (sz - pos - 2)) with (A + Z.of_nat (Z.to_nat (sz - 1))) by lia.
                 apply (bytes_at_agree asegs m3 m5 _ _ (bytes_at_skipn m3 A bs (Z.to_nat (sz - 1)) BS ltac:(lia))). intros a Ha. rewrite length_skipn in Ha.
                 rewrite (AG5 a); [| apply (CLo _ _); right; lia| lia]. apply AG4; [apply (CLo _ _); right; lia| lia].
           ++ rewrite !length_app, firstn_length_le, LSRC, length_skipn by lia. cbn [length].
              replace (Z.of_nat (Z.to_nat pos + (1 + (Z.to_nat (sz - pos - 2) + (length bs - Z.to_nat (sz - 1)))))) with cap by lia.
              exact (wr_at_transport asegs m4 m5 A cap BW4 WM5).
        -- rewrite !length_app, firstn_length_le, LSRC, length_skipn by lia. cbn [length]. lia.
        -- exact (lstr_acc_pres Σ m4 m5 (sp - 80) A cap (A + pos + 1) (sz - pos - 2) ART4 ART5 CLA ltac:(lia) ACC4 PRES5 ltac:(right; lia)).
        -- intros a Ha N1 N2. pose proof (aclient_split_c RT AF Σ m sp (bv_unsigned a) ART0 Ha) as SPL.
           rewrite (AG5 a); [| apply (aclient_mono _ _ _ _ _ _ _ Ha); auto; lia| lia].
           rewrite (AG4 a); [| apply (aclient_mono _ _ _ _ _ _ _ Ha); auto; lia| lia].
           rewrite (MU3 a); [| cbn [outside]; split; [clear - SPL LOW LOR; ul| exact I]].
           rewrite (AG2 a); [| apply (aclient_mono _ _ _ _ _ _ _ Ha); auto; lia].
           apply MU1. cbn [outside]. split; [clear - SPL LOW LOR; ul| exact I].
Qed.

End ObjS.
