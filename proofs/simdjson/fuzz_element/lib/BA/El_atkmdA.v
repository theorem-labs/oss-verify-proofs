From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_defsA Atp_kitA Atp_objkA El_callsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Ltac poff t :=
  lazymatch t with
  | Z_to_bv 64 ?n => let v := eval vm_compute in (n - 736088) in idtac "off" v
  | _ => idtac "pcterm" t
  end.
Ltac pgs_core :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) =>
    lazymatch pc with
    | if ?c then ?a else ?b => idtac "IF" c; poff a; poff b
    | _ => poff pc
    end
  | |- ?g => idtac "nogoal"
  end.
Ltac pg_core :=
  lazymatch goal with
  | |- evt _ _ (MS (TNode
      (TNode (TNode (TNode (TNode (TNode TEmpty (Some ?x31) TEmpty) (Some ?x15) TEmpty) (Some ?x7) (TNode TEmpty (Some ?x23) TEmpty))
                    (Some ?x3) (TNode (TNode TEmpty (Some ?x19) TEmpty) (Some ?x11) (TNode TEmpty (Some ?x27) TEmpty)))
             (Some ?x1)
             (TNode (TNode (TNode TEmpty (Some ?x17) TEmpty) (Some ?x9) (TNode TEmpty (Some ?x25) TEmpty))
                    (Some ?x5) (TNode (TNode TEmpty (Some ?x21) TEmpty) (Some ?x13) (TNode TEmpty (Some ?x29) TEmpty))))
      None
      (TNode (TNode (TNode (TNode TEmpty (Some ?x16) TEmpty) (Some ?x8) (TNode TEmpty (Some ?x24) TEmpty))
                    (Some ?x4) (TNode (TNode TEmpty (Some ?x20) TEmpty) (Some ?x12) (TNode TEmpty (Some ?x28) TEmpty)))
             (Some ?x2)
             (TNode (TNode (TNode TEmpty (Some ?x18) TEmpty) (Some ?x10) (TNode TEmpty (Some ?x26) TEmpty))
                    (Some ?x6) (TNode (TNode TEmpty (Some ?x22) TEmpty) (Some ?x14) (TNode TEmpty (Some ?x30) TEmpty)))))
      _ _ _ _ ?m _) =>
    idtac "  ra" x1 "| sp" x2 "| t0" x5 "| t1" x6 "| t2" x7;
    idtac "  s0" x8 "| s1" x9 "| a0" x10 "| a1" x11 "| a2" x12;
    idtac "  a3" x13 "| a4" x14 "| a5" x15 "| a6" x16 "| a7" x17;
    idtac "  s2" x18 "| s3" x19 "| s4" x20 "| s5" x21 "| s6" x22 "| s7" x23;
    idtac "  s8" x24 "| s9" x25 "| s10" x26 "| s11" x27 "| t3-6" x28 x29 x30 x31 "| mem" m
  | |- _ => idtac "  noregs"
  end.
Tactic Notation "pgs" string(tag) := idtac "PROBE" tag; pgs_core.
Tactic Notation "pg" string(tag) := idtac "PROBE" tag; pgs_core; pg_core.

Ltac pre_ok l := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?n) _ _ _ _) =>
  let b := eval vm_compute in (andb (andb (Z.leb 736088 n) (Z.ltb n 737124)) (negb (existsb (Z.eqb n) l))) in
  lazymatch b with true => idtac end end.
Ltac post_ok := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => idtac end.
Ltac run1 l := pre_ok l; astep; first [ post_ok | if_false; post_ok | if_true; post_ok ].
Ltac runl l := repeat (run1 l).
Ltac run := runl (@nil Z).
Tactic Notation "shz_at" constr(H) constr(x) := rewrite ?shr3_div; shz_pose H x; astep; shz_norm.

Definition atkm_W (q : Z) : list (Z * Z) := [(q + -128, q)].

Definition atkm_saved (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition atkm_frame (DOC out P : Z) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 (wz DOC); C8 (wz out); C8 (wz P)] ++ atkm_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11.

Lemma le8_nth7M : forall v, (0 <= v < 2^64)%Z -> nth 7 (le8 (Z_to_bv 64 v)) (Z_to_bv 8 0) = Z_to_bv 8 (ttype v).
Proof.
  intros v Hv. unfold le8, word_to_le_bytes. rewrite a_u64_small by lia.
  cbn [Z_to_le_bytes nth]. rewrite !Z.shiftr_shiftr by lia. cbn [Z.add Pos.add Pos.succ]. rewrite a_shr56. reflexivity.
Qed.
Lemma u64s_read7M : forall (ws : list word) (i : nat), (i < length ws)%nat ->
  firstn 1 (skipn (8 * i + 7) (u64s ws)) = [nth 7 (le8 (nth i ws (Z_to_bv 64 0))) (Z_to_bv 8 0)].
Proof.
  induction ws as [|w ws IH]; intros i Hi; cbn [length] in Hi; [lia|].
  destruct i as [|i].
  - cbn [Nat.mul Nat.add u64s nth]. rewrite skipn_app, length_le8. replace (7 - 8)%nat with 0%nat by lia. cbn [skipn].
    pose proof (length_le8 w) as L. remember (le8 w) as l eqn:El. clear El.
    destruct l as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 [|b8 r]]]]]]]]]; cbn [length] in L; try lia. reflexivity.
  - replace (8 * S i + 7)%nat with (8 + (8 * i + 7))%nat by lia. cbn [u64s nth]. rewrite skipn_app, length_le8.
    replace (8 + (8 * i + 7) - 8)%nat with (8 * i + 7)%nat by lia. rewrite skipn_all2 by (rewrite length_le8; lia). cbn [app].
    apply IH. lia.
Qed.
Lemma tape_read_typeM : forall m TAPE (tws : list Z) (i : Z),
  bytes_at asegs m TAPE (u64s (map (Z_to_bv 64) tws)) -> 0 <= i < Z.of_nat (length tws) -> 0 <= Tf tws i < 2^64 ->
  ov_read_bytes asegs m (wa (TAPE + 8 * i + 7)) 1 = Some [Z_to_bv 8 (ttype (Tf tws i))].
Proof.
  intros m TAPE tws i HB Hi HT.
  replace (TAPE + 8 * i + 7) with (TAPE + (8 * i + 7)) by lia.
  rewrite (bytes_at_read asegs m TAPE _ (8 * i + 7) 1 HB); [| lia| rewrite u64s_length, length_map; lia].
  f_equal. replace (Z.to_nat (8 * i + 7)) with (8 * Z.to_nat i + 7)%nat by lia.
  rewrite u64s_read7M by (rewrite length_map; lia).
  rewrite <- le8_nth7M by exact HT. do 3 f_equal.
  unfold Tf. rewrite (map_nth (Z_to_bv 64)). reflexivity.
Qed.
Lemma zx32_tnextM : forall w, (0 <= w < 2^64)%Z -> zx32 (Z_to_bv 64 w) = Z_to_bv 64 (tnext w).
Proof. intros w Hw. unfold zx32. f_equal. rewrite a_u64_small by lia. rewrite <- land32_tnext by lia. symmetry. change 4294967295 with (Z.ones 32). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma key_word_rangeM : forall (T S : Z -> Z) (sn i : Z), is_str T S sn i -> sn < 2^56 ->
  0 <= T i < 2^64 /\ Z.land (T i) 72057594037927935 = tval (T i) /\ ttype (T i) = t_str.
Proof.
  intros T S sn i (o & l & X & (Y1 & Y2 & Y3 & _)) Hsn. rewrite X.
  split; [apply tword_range; [unfold t_str; lia| lia]|].
  split; [| apply ttype_tword; lia].
  change 72057594037927935 with (Z.ones 56). rewrite Z.land_ones by (unfold tword, t_str; lia).
  unfold tval. reflexivity.
Qed.
Lemma shl8_shr8_tvalM : forall x, 0 <= x -> Z.shiftr (Z.land (Z.shiftl x 8) 18446744073709551615) 8 = tval x.
Proof. intros x Hx. rewrite zb_shl_shr_land by lia. unfold tval. change (2 ^ (64 - 8) - 1) with (Z.ones 56). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma shl_mod_smallM : forall b k, 0 <= b < 256 -> 0 <= k <= 24 -> (Z.shiftl b k) mod 18446744073709551616 = Z.shiftl b k.
Proof.
  intros b k Hb Hk. apply Z.mod_small. rewrite Z.shiftl_mul_pow2 by lia.
  assert (0 < 2 ^ k <= 2 ^ 24) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_le_mono_r; lia]). nia.
Qed.
Lemma land_shiftl_smallM : forall x y n, 0 <= n -> 0 <= x < 2^n -> Z.land (Z.shiftl y n) x = 0.
Proof.
  intros x y n Hn Hx. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i n) as [L|G].
  - rewrite Z.shiftl_spec_low by lia. reflexivity.
  - destruct (Z.eq_dec x 0) as [->|NZ]; [rewrite Z.bits_0; apply Bool.andb_false_r|].
    assert (LG : Z.log2 x < i).
    { apply (Z.lt_le_trans _ n); [| lia]. apply Z.log2_lt_pow2; lia. }
    rewrite (Z.bits_above_log2 x i) by lia. apply Bool.andb_false_r.
Qed.
Lemma lor_shiftl_smallM : forall x y n, 0 <= n -> 0 <= x < 2^n -> 0 <= y -> Z.lor (Z.shiftl y n) x = y * 2^n + x.
Proof.
  intros x y n Hn Hx Hy. rewrite <- Z.lxor_lor by (apply land_shiftl_smallM; lia).
  rewrite <- Z.add_nocarry_lxor by (apply land_shiftl_smallM; lia). rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.
Lemma le32_of_lbu4M : forall b0 b1 b2 b3, 0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
  Z.lor (Z.lor (Z.shiftl b3 24) (Z.shiftl b2 16)) (Z.lor (Z.shiftl b1 8) b0) = b0 + 2^8 * b1 + 2^16 * b2 + 2^24 * b3.
Proof.
  intros b0 b1 b2 b3 H0 H1 H2 H3.
  rewrite (lor_shiftl_smallM b0 b1 8) by lia.
  replace (Z.shiftl b3 24) with (Z.shiftl (Z.shiftl b3 8) 16) by (rewrite Z.shiftl_shiftl by lia; reflexivity).
  rewrite <- Z.shiftl_lor. rewrite (lor_shiftl_smallM b2 b3 8) by lia.
  rewrite (lor_shiftl_smallM (b1 * 2^8 + b0) (b3 * 2^8 + b2) 16); [lia| lia| |lia].
  change (2^16) with (2^8 * 2^8). lia.
Qed.
Lemma land64_shl_smallM : forall b k, 0 <= b < 256 -> 0 <= k <= 24 -> Z.land (Z.shiftl b k) 18446744073709551615 = Z.shiftl b k.
Proof.
  intros b k Hb Hk. rewrite land64_mod. apply Z.mod_small. rewrite Z.shiftl_mul_pow2 by lia.
  assert (0 < 2 ^ k <= 2 ^ 24) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_le_mono_r; lia]). nia.
Qed.

Section AtKmDefs.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.
  Variable d : nat.

  Lemma sbs_byteM : forall o, 0 <= o < ae_sn E -> 0 <= ae_S E o < 256.
  Proof using OK.
    intros o Ho. destruct OK as [_ SBS _ _ _ _ _ _ _ _ _]. unfold Tf. apply Forall_nth_Z; [exact SBS| lia].
  Qed.
End AtKmDefs.
