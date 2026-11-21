(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_ikit Z_infl_defs Z_infl_defs2 Z_infl_c_defs Z_infl_c_tab Zg_infl_defs.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface InflateState InflateArms Inflate RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateOkb RefInflateA_DIST1 RefInflateSafeH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

(* [comment removed for export] *)
Definition DECG (X : ictx) (s : inflate_state) (c : icall) (rw rb : iregs) (RES : ares Z) (rf : iregs) (p : codeptr) (index need : Z -> Z)
    (pcj : Z) (Q : iregs -> iscrh -> Prop) : machine_state -> Prop :=
  fun ms' =>
    (exists r1 q, RES = ARun (code_at s p (index (ir_hold r1))) (mkW s c r1)
                  /\ rf = r1
                  /\ need (code_at s p (index (ir_hold r1))) <= ir_bits r1
                  /\ 0 <= index (ir_hold r1) < ctab_size p
                  /\ REGS c r1 /\ pulled rb r1
                  /\ ILOOPh X (mkW s c rw) pcj q ms' /\ Q r1 q)
    \/ (exists r1, RES = ALeave (mkW s c r1) /\ pulled rb r1 /\ ILEAVE X (mkW s c r1) ms').

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma DC_found : forall k p index need s c r, need (code_at s p (index (ir_hold r))) <= ir_bits r ->
  DECODE_k k p index need (mkW s c r) = ARun (code_at s p (index (ir_hold r))) (mkW s c r).
Proof.
  intros k p index need s c r H. destruct k as [|k]; [apply RefInflateA_DIST1.DECODE_k_O|].
  rewrite RefInflateA_DIST1.DECODE_k_S. cbv zeta. rewrite (proj2 (Z.leb_le _ _) H). reflexivity.
Qed.
Lemma DC_dry : forall k p index need s c r, ir_bits r < need (code_at s p (index (ir_hold r))) -> ir_have r = 0 ->
  DECODE_k (S k) p index need (mkW s c r) = ALeave (mkW s c r).
Proof.
  intros k p index need s c r Hb Hh. rewrite RefInflateA_DIST1.DECODE_k_S. cbv zeta.
  rewrite (proj2 (Z.leb_gt _ _) Hb), (proj2 (Z.eqb_eq _ _) Hh). reflexivity.
Qed.
Lemma DC_pull : forall k p index need s c r, ir_bits r < need (code_at s p (index (ir_hold r))) -> ir_have r <> 0 ->
  DECODE_k (S k) p index need (mkW s c r) = DECODE_k k p index need (mkW s c (RefInflateArmLib.pullr c r)).
Proof.
  intros k p index need s c r Hb Hh. rewrite RefInflateA_DIST1.DECODE_k_S. cbv zeta.
  rewrite (proj2 (Z.leb_gt _ _) Hb), (proj2 (Z.eqb_neq _ _) Hh). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma CK_found : forall k c index need N tab r rf, dchk k c index need N tab r = Some rf ->
  need (tab (index (ir_hold r))) <= ir_bits r -> 0 <= index (ir_hold r) < N /\ rf = r.
Proof. intros. eapply dchk_found; eassumption. Qed.
Lemma CK_range : forall k c index need N tab r rf, dchk k c index need N tab r = Some rf ->
  0 <= index (ir_hold r) < N /\ 0 <= need (tab (index (ir_hold r))) <= 32.
Proof.
  intros k c index need N tab r rf H.
  destruct k as [|k']; cbn [dchk] in H;
    (destruct ((0 <=? index (ir_hold r)) && (index (ir_hold r) <? N) && (0 <=? need (tab (index (ir_hold r)))) && (need (tab (index (ir_hold r))) <=? 32)) eqn:Hc; [| discriminate H]);
    apply andb_prop in Hc as [Hc H4]; apply andb_prop in Hc as [Hc H3]; apply andb_prop in Hc as [H1 H2];
    apply Z.leb_le in H1; apply Z.ltb_lt in H2; apply Z.leb_le in H3; apply Z.leb_le in H4; lia.
Qed.
Lemma CK_dry : forall k c index need N tab r rf, dchk (S k) c index need N tab r = Some rf ->
  ir_bits r < need (tab (index (ir_hold r))) -> ir_have r = 0 -> rf = r.
Proof.
  intros k c index need N tab r rf H Hb Hh. destruct (dchk_step (S k) c index need N tab r rf H Hb) as (_ & _ & [[_ E]|[NE _]]); [exact E| contradiction].
Qed.
Lemma CK_pull : forall k c index need N tab r rf, dchk (S k) c index need N tab r = Some rf ->
  ir_bits r < need (tab (index (ir_hold r))) -> ir_have r <> 0 -> dchk k c index need N tab (RefInflateArmLib.pullr c r) = Some rf.
Proof.
  intros k c index need N tab r rf H Hb Hh. destruct (dchk_step (S k) c index need N tab r rf H Hb) as (_ & _ & [[E _]|[_ E]]); [contradiction| exact E].
Qed.
Lemma CK_short0 : forall c index need N tab r rf, dchk 0 c index need N tab r = Some rf ->
  ir_bits r < need (tab (index (ir_hold r))) -> False.
Proof. intros c index need N tab r rf H Hb. exact (proj2 (proj2 (dchk_step 0 c index need N tab r rf H Hb))). Qed.

(* [comment removed for export] *)
Lemma decG_r1_facts : forall c r r1, REGS c r1 -> pulled r r1 ->
  (0 <= ir_next r1 /\ 0 <= ir_have r1 < 2^32 /\ ir_next r1 + ir_have r1 = arr_len (ic_input c) /\ 0 <= ir_bits r1 <= 63 /\ 0 <= ir_hold r1 < 2 ^ ir_bits r1)
  /\ ir_in r1 = ir_in r /\ ir_out r1 = ir_out r /\ ir_ret r1 = ir_ret r /\ ir_put r1 = ir_put r /\ ir_left r1 = ir_left r.
Proof.
  intros c r r1 (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo) HP.
  destruct (pulled_eqs _ _ HP) as (E1 & E2 & E3 & E4 & E5). repeat split; try assumption; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition DREGSg (c : icall) (r : iregs) : Prop :=
  0 <= ir_next r /\ 0 <= ir_have r < 2^31 /\ ir_next r + ir_have r = arr_len (ic_input c) /\ 0 <= ir_bits r <= 63 /\ 0 <= ir_hold r < 2 ^ ir_bits r.
Lemma DREGSg_of_REGS : forall c r, REGS c r -> arr_len (ic_input c) < 2^31 -> DREGSg c r.
Proof. intros c r (Rn & Rh & Rnh & _ & _ & _ & [RB RH] & _) Hin. unfold DREGSg. repeat split; try lia. Qed.
Lemma dec_r1_factsg : forall c r r1, DREGSg c r -> (forall i, 0 <= arr_get (ic_input c) i < 256) ->
  (r1 = r \/ (r1 = RefInflateArmLib.pullr c r /\ 0 < ir_have r /\ ir_bits r <= 31)) ->
  DREGSg c r1 /\ ir_in r1 = ir_in r /\ ir_out r1 = ir_out r /\ ir_ret r1 = ir_ret r /\ ir_put r1 = ir_put r /\ ir_left r1 = ir_left r.
Proof.
  intros c r r1 (Rn & Rh & Rnh & RB & RH) Rin [->|(-> & H1 & HB)]; [repeat split; try reflexivity; try lia|].
  pose proof (Rin (ir_next r)) as RBy.
  destruct (RefInflateArmLib.pullr_facts c r ltac:(lia) ltac:(lia) RH RBy) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10).
  unfold DREGSg. rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9. rewrite <- E5.
  repeat split; try reflexivity; try lia.
Qed.
Lemma DREGSg_hold64 : forall c r, DREGSg c r -> 0 <= ir_hold r < 2^64.
Proof. intros c r (_ & _ & _ & RB & RH). split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. Qed.
Lemma DREGSg_drop : forall c r n, DREGSg c r -> 0 <= n <= ir_bits r -> DREGSg c (ddrop r n).
Proof.
  intros c r n (Rn & Rh & Rnh & RB & RH) Hn. unfold DREGSg, ddrop. destruct r; cbn in *. rewrite wrap32_id by lia.
  pose proof (hold_drop ir_hold ir_bits n Hn RH) as HD. rewrite Z.shiftr_div_pow2 by lia. repeat split; lia.
Qed.
(* [comment removed for export] *)
Lemma DREGSg_nb : forall c r r1 n, DREGSg c r -> (forall i, 0 <= arr_get (ic_input c) i < 256) -> n <= 32 ->
  ((r1 = r /\ n <= ir_bits r) \/ (r1 = RefInflateArmLib.pullr c r /\ 0 < ir_have r /\ ir_bits r < n <= ir_bits r + 8)) ->
  DREGSg c r1 /\ n <= ir_bits r1 /\ ir_in r1 = ir_in r /\ ir_out r1 = ir_out r /\ ir_ret r1 = ir_ret r /\ ir_put r1 = ir_put r /\ ir_left r1 = ir_left r.
Proof.
  intros c r r1 n DR Rin Hn [[-> H]|(-> & H1 & H2)].
  - repeat split; try reflexivity; try lia; apply DR.
  - pose proof DR as (Rn & Rh & Rnh & RB & RH).
    assert (A2 : ir_bits r <= 31) by lia.
    destruct (dec_r1_factsg c r (RefInflateArmLib.pullr c r) DR Rin (or_intror (conj eq_refl (conj H1 A2)))) as (DR1 & F).
    split; [exact DR1|]. split; [| exact F].
    unfold RefInflateArmLib.pullr. cbn [ir_bits]. rewrite wrap32_id by lia. lia.
Qed.
