From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldLemmas TWorldMem TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import WMem check_state_settle_c.
Import ListNotations.
Open Scope Z_scope.

Lemma css_eqb_s32 : forall a b, -2^31 <= a < 2^31 -> -2^31 <= b < 2^31 ->
  bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof.
  intros a b Ha Hb. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec a b) as [->|NE]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E. apply NE. Z.div_mod_to_equations. lia.
Qed.

Lemma css_lts0_s32 : forall a, -2^31 <= a < 2^31 -> bv_lts (Z_to_bv 64 0) (Z_to_bv 64 a) = (0 <? a).
Proof.
  intros a Ha. rewrite bv_lts_zero_l, unsigned_lit_wrap.
  destruct (Z.ltb_spec 0 a).
  - rewrite Z.mod_small by lia. destruct (Z.ltb_spec 0 a); destruct (Z.ltb_spec a (2^63)); try reflexivity; lia.
  - destruct (Z.eqb_spec a 0) as [->|NZ]; [reflexivity|].
    replace (a mod 2^64) with (a + 2^64).
    + destruct (Z.ltb_spec 0 (a + 2^64)); destruct (Z.ltb_spec (a + 2^64) (2^63)); try reflexivity; lia.
    + symmetry. rewrite <- (Z.mod_add a 1 (2^64)) by lia. apply Z.mod_small. lia.
Qed.

Lemma css_ltu_lit : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_ltu. rewrite !unsigned_lit by assumption. reflexivity. Qed.

Lemma css_eqb_lit : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof. intros a b Ha Hb. unfold bv_eqb. rewrite !unsigned_lit by assumption. reflexivity. Qed.

Lemma css_lxor_eqb0 : forall x y, (Z.lxor x y =? 0) = (x =? y).
Proof.
  intros x y. destruct (Z.eqb_spec x y) as [->|NE].
  - rewrite Z.lxor_nilpotent. reflexivity.
  - apply Z.eqb_neq. intros E. apply NE. apply Z.lxor_eq_0_iff. exact E.
Qed.

Lemma css_lor_eqb0 : forall x y, 0 <= x -> 0 <= y -> (Z.lor x y =? 0) = ((x =? 0) && (y =? 0)).
Proof.
  intros x y Hx Hy. destruct (Z.eqb_spec (Z.lor x y) 0) as [E|E].
  - apply Z.lor_eq_0_iff in E. destruct E as [-> ->]. reflexivity.
  - destruct (Z.eqb_spec x 0) as [->|]; destruct (Z.eqb_spec y 0) as [->|]; try reflexivity.
    exfalso. apply E. reflexivity.
Qed.

Lemma css_u_eqb : forall a b, -2^31 <= a < 2^31 -> -2^31 <= b < 2^31 ->
  (bv_unsigned (Z_to_bv 64 a) =? bv_unsigned (Z_to_bv 64 b)) = (a =? b).
Proof. intros a b Ha Hb. exact (css_eqb_s32 a b Ha Hb). Qed.

Lemma css_sltiu1 : forall x, 0 <= x < 2^64 -> v_sltiu (Z_to_bv 64 x) 1 = Z_to_bv 64 (Z.b2z (x =? 0)).
Proof.
  intros x Hx. unfold v_sltiu. rewrite unsigned_lit by exact Hx. change (bv_wrap 64 1) with 1.
  destruct (Z.ltb_spec x 1); destruct (Z.eqb_spec x 0); try reflexivity; lia.
Qed.

Lemma css_seqz_xor : forall a b, -2^31 <= a < 2^31 -> -2^31 <= b < 2^31 ->
  v_sltiu (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 a)) (bv_unsigned (Z_to_bv 64 b)))) 1 = Z_to_bv 64 (Z.b2z (a =? b)).
Proof.
  intros a b Ha Hb.
  rewrite css_sltiu1 by (apply zr_lxor; apply zr_word).
  rewrite css_lxor_eqb0, css_u_eqb by assumption. reflexivity.
Qed.

Lemma css_seqz_or_xor : forall a b c d, -2^31 <= a < 2^31 -> -2^31 <= b < 2^31 -> -2^31 <= c < 2^31 -> -2^31 <= d < 2^31 ->
  v_sltiu (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 a)) (bv_unsigned (Z_to_bv 64 b)))))
                             (bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 c)) (bv_unsigned (Z_to_bv 64 d))))))) 1
  = Z_to_bv 64 (Z.b2z ((a =? b) && (c =? d))).
Proof.
  intros a b c d Ha Hb Hc Hd.
  assert (X1 : inr64 (Z.lxor (bv_unsigned (Z_to_bv 64 a)) (bv_unsigned (Z_to_bv 64 b)))) by (apply zr_lxor; apply zr_word).
  assert (X2 : inr64 (Z.lxor (bv_unsigned (Z_to_bv 64 c)) (bv_unsigned (Z_to_bv 64 d)))) by (apply zr_lxor; apply zr_word).
  rewrite (unsigned_lit (Z.lxor (bv_unsigned (Z_to_bv 64 a)) (bv_unsigned (Z_to_bv 64 b)))) by exact X1.
  rewrite (unsigned_lit (Z.lxor (bv_unsigned (Z_to_bv 64 c)) (bv_unsigned (Z_to_bv 64 d)))) by exact X2.
  rewrite css_sltiu1 by (apply zr_lor; assumption).
  unfold inr64 in X1, X2.
  rewrite css_lor_eqb0 by lia.
  rewrite !css_lxor_eqb0, !css_u_eqb by assumption. reflexivity.
Qed.

Lemma css_snez_xor : forall a b, -2^31 <= a < 2^31 -> -2^31 <= b < 2^31 ->
  v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 a)) (bv_unsigned (Z_to_bv 64 b))))
  = Z_to_bv 64 (Z.b2z (negb (a =? b))).
Proof.
  intros a b Ha Hb.
  assert (X : inr64 (Z.lxor (bv_unsigned (Z_to_bv 64 a)) (bv_unsigned (Z_to_bv 64 b)))) by (apply zr_lxor; apply zr_word).
  pose proof (css_lxor_eqb0 (bv_unsigned (Z_to_bv 64 a)) (bv_unsigned (Z_to_bv 64 b))) as E.
  rewrite css_u_eqb in E by assumption.
  unfold v_sltu, c_ltu, bv_ltu. rewrite (unsigned_lit 0) by lia.
  rewrite (unsigned_lit (Z.lxor (bv_unsigned (Z_to_bv 64 a)) (bv_unsigned (Z_to_bv 64 b)))) by exact X.
  unfold inr64 in X.
  destruct (Z.eqb_spec a b) as [Eab|Eab].
  - subst b. rewrite Z.lxor_nilpotent. reflexivity.
  - try rewrite (proj2 (Z.eqb_neq a b) Eab) in E. apply Z.eqb_neq in E.
    replace (0 <? Z.lxor (bv_unsigned (Z_to_bv 64 a)) (bv_unsigned (Z_to_bv 64 b))) with true
      by (symmetry; apply Z.ltb_lt; lia).
    reflexivity.
Qed.

Lemma css_addiw_m1 : forall c : bool,
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (Z.b2z c)) + -1)) = Z_to_bv 64 (if c then 0 else -1).
Proof. intros [|]; reflexivity. Qed.

Lemma css_and_mask : forall c w : bool,
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (if c then 0 else -1))) (bv_unsigned (Z_to_bv 64 (Z.b2z w))))
  = Z_to_bv 64 (Z.b2z (w && negb c)).
Proof. intros [|] [|]; reflexivity. Qed.

Lemma css_and_b2z : forall x y : bool,
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.b2z x))) (bv_unsigned (Z_to_bv 64 (Z.b2z y))))
  = Z_to_bv 64 (Z.b2z (y && x)).
Proof. intros [|] [|]; reflexivity. Qed.

Lemma css_eqb_e : forall x (e : word), 0 <= x < 2^64 -> bv_eqb (Z_to_bv 64 x) e = (x =? bv_unsigned e).
Proof. intros x e Hx. unfold bv_eqb. rewrite unsigned_lit by exact Hx. reflexivity. Qed.

(* one turn of the model's loop over the first min(OW.n, TRANS_MAX) transitions (fuzz_transport.c:718-721) *)
Lemma css_loop_step : forall B i s w, 0 <= i -> i < OW_n B -> i < 16 ->
  state_settle_loop (Z.to_nat (16 - i)) B i s w =
  state_settle_loop (Z.to_nat (16 - (i + 1))) B (i + 1)
    (s && ((GOT_t_state B i =? OW_t_state B i) && (GOT_t_old B i =? OW_t_old B i)))
    (w && (GOT_t_reason B i =? OW_t_reason B i)).
Proof.
  intros B i s w H0 H1 H2.
  replace (Z.to_nat (16 - i)) with (S (Z.to_nat (16 - (i + 1)))) by lia.
  cbn [state_settle_loop].
  replace ((i <? OW_n B) && (i <? TRANS_MAX)) with true
    by (symmetry; apply andb_true_intro; split; apply Z.ltb_lt; unfold TRANS_MAX; lia).
  reflexivity.
Qed.

Lemma css_loop_stop : forall fuel B i s w, OW_n B <= i \/ 16 <= i -> state_settle_loop fuel B i s w = (s, w).
Proof.
  intros [|f] B i s w H; [reflexivity|]. cbn [state_settle_loop].
  replace ((i <? OW_n B) && (i <? TRANS_MAX)) with false; [reflexivity|].
  symmetry. apply andb_false_iff. unfold TRANS_MAX. destruct H; [left|right]; apply Z.ltb_ge; lia.
Qed.

Ltac css_uclean :=
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?e)] =>
      rewrite (unsigned_lit e) by (rewrite ?Z.shiftl_mul_pow2 by lia; lia)
  end;
  rewrite ?Z.shiftl_mul_pow2 by lia.


(* name the value an indexed 4-byte world load just put in a register: the kit's world hook leaves s32_at B at
   its own offset form; acc is the model's accessor for that field *)
Ltac css_ld acc :=
  lazymatch goal with
  | |- context [s32_at ?BB ?k] =>
      replace (s32_at BB k) with acc
        by (cbv [GOT_t_state OW_t_state GOT_t_old OW_t_old GOT_t_reason OW_t_reason
                 A_GOT_t_state A_OW_t_state A_GOT_t_old A_OW_t_old A_GOT_t_reason A_OW_t_reason OFF_GOT OFF_OW];
            f_equal; rewrite ?unsigned_lit by lia; rewrite ?Z.shiftl_mul_pow2 by lia; lia)
  end.

(* a bne / beq on two loaded int fields whose equality the model premise gives *)
Ltac br_eqt H :=
  lazymatch goal with
  | |- context [bv_eqb (Z_to_bv 64 ?x) (Z_to_bv 64 ?y)] =>
      rewrite (css_eqb_s32 x y) by (apply s32_range);
      replace (x =? y) with true by (symmetry; exact H); cbn [negb]
  end.

Theorem check_state_settle_holds : check_state_settle_contract.
Proof.
  unfold check_state_settle_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo B B'
    WM HM SPA ST LO OFF MI.
  unfold check_state_settle_FRAME in *. unfold w_off_stack in OFF.
  wk_facts.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WMo.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  unfold check_state_settle_m in HM.
  destruct (GOT_e2 B =? OW_e2 B) eqn:C1; cbn [negb orb] in HM; [|discriminate HM].
  destruct (GOT_e3 B =? OW_e3 B) eqn:C2; cbn [negb orb] in HM; [|discriminate HM].
  destruct (GOT_ndata B =? OW_ndata B) eqn:C3; cbn [negb orb] in HM; [|discriminate HM].
  destruct (GOT_desk B =? OW_desk B) eqn:C4; cbn [negb orb] in HM; [|discriminate HM].
  destruct (GOT_foreign B =? OW_foreign B) eqn:C5; cbn [negb orb] in HM; [|discriminate HM].
  destruct (state_settle_loop (Z.to_nat TRANS_MAX) B 0 ((GOT_n B =? OW_n B) && (S_state B =? M_state B)) true)
    as [same why] eqn:LP.
  destruct same; cbn [negb] in HM; [|discriminate HM].
  destruct why; cbn [negb] in HM; [|discriminate HM].
  injection HM as <-.
  lazymatch goal with |- evt _ ?Q _ => set (QQ := Q) end.
  carve_frame 16%nat ST.
  do 7 step. br_eqt C1.
  do 3 step. br_eqt C2.
  do 3 step. br_eqt C3.
  do 3 step. br_eqt C4.
  do 3 step. br_eqt C5.
  do 10 step.
  rewrite css_seqz_or_xor by (apply s32_range).
  change (s32_at B 65084) with (GOT_n B). change (s32_at B 65312) with (OW_n B).
  change (s32_at B 1760) with (S_state B). change (s32_at B 12) with (M_state B).
  assert (EE : check_state_settle_ENTRY = 91256) by reflexivity.
  assert (RN : -2^31 <= OW_n B < 2^31) by apply s32_range.
  (* the epilogue at 0x16564 *)
  assert (EPI : forall x10 x11 x12 x13 x14 x15 x16 : word,
    evt rsegs QQ (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 x14 x15 x16 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 (check_state_settle_ENTRY + 236)) fc None m0 (seg_rom rsegs))).
  { intros x10 x11 x12 x13 x14 x15 x16.
    step. step. step.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. unfold QQ. do 16 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WMo|]. split; [exact MI|]. split; [exact ST|]. split; [reflexivity|exact WM]. }
  (* the loop at 0x16514 over i < cnt = min(OW.n, 16) *)
  assert (LOOP : forall k i cnt (s w : bool) (e x14 x15 x16 : word),
    Z.of_nat k = cnt - i -> 0 <= i < cnt -> cnt = Z.min (OW_n B) 16 ->
    bv_unsigned e = 274988 + 12 * cnt ->
    state_settle_loop (Z.to_nat (16 - i)) B i s w = (true, true) ->
    evt rsegs QQ (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1
                          (Z_to_bv 64 (Z.b2z s)) (Z_to_bv 64 (Z.b2z w)) (Z_to_bv 64 (274988 + 12 * i)) e x14 x15 x16 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 (check_state_settle_ENTRY + 156)) fc None m0 (seg_rom rsegs))).
  { induction k as [|k IH]; intros i cnt s w e x14 x15 x16 Hk Hi Hc He HL; [lia|].
    rewrite css_loop_step in HL by lia.
    step. css_ld (GOT_t_state B i).
    step. css_ld (OW_t_state B i).
    step.
    rewrite css_eqb_s32 by (apply s32_range).
    assert (JN : forall (st : bool) (y15 : word),
      st = ((GOT_t_state B i =? OW_t_state B i) && (GOT_t_old B i =? OW_t_old B i)) ->
      evt rsegs QQ (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 s0 s1
                            (Z_to_bv 64 (Z.b2z s)) (Z_to_bv 64 (Z.b2z w)) (Z_to_bv 64 (274988 + 12 * i)) e
                            (Z_to_bv 64 (Z.b2z st)) y15 x16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 (check_state_settle_ENTRY + 192)) fc None m0 (seg_rom rsegs))).
    { intros st y15 Hst.
      step. css_ld (GOT_t_reason B i).
      step.
      css_ld (OW_t_reason B i).
      step. rewrite css_and_b2z.
      step. step.
      rewrite css_snez_xor by (apply s32_range).
      step. rewrite css_addiw_m1.
      step. step. rewrite css_and_mask, negb_involutive.
      step.
      rewrite css_eqb_e by lia. rewrite He.
      subst st.
      destruct (Z.eqb_spec (274988 + 12 * i + 12) (274988 + 12 * cnt)) as [EQ|NE]; cbn [negb].
      - rewrite css_loop_stop in HL by lia.
        injection HL as Hs Hw. rewrite Hs, Hw. cbn [Z.b2z].
        step. if_false. step. if_false.
        apply EPI.
      - replace (274988 + 12 * i + 12) with (274988 + 12 * (i + 1)) by lia.
        apply (IH (i + 1) cnt); try assumption; lia. }
    destruct (Z.eqb_spec (GOT_t_state B i) (OW_t_state B i)) as [Est|Est]; cbn [negb].
    - step. css_ld (GOT_t_old B i).
      step. css_ld (OW_t_old B i).
      step. step. rewrite css_seqz_xor by (apply s32_range).
      step.
      apply (JN (GOT_t_old B i =? OW_t_old B i)).
      first [ reflexivity | rewrite Est, Z.eqb_refl; reflexivity ].
    - step.
      apply (JN false).
      first [ reflexivity | rewrite (proj2 (Z.eqb_neq _ _) Est); reflexivity ]. }
  step.
  rewrite css_lts0_s32 by (apply s32_range).
  destruct (Z.ltb_spec 0 (OW_n B)) as [NP|NP]; cbn [negb].
  - step. step.
    rewrite css_ltu_lit by lia.
    destruct (Z.ltb_spec (OW_n B) 16) as [L16|L16]; cbn [negb].
    + do 6 step.
      apply (LOOP (Z.to_nat (OW_n B)) 0 (OW_n B) ((GOT_n B =? OW_n B) && (S_state B =? M_state B)) true).
      * lia.
      * lia.
      * lia.
      * css_uclean. lia.
      * exact LP.
    + step. do 6 step.
      apply (LOOP 16%nat 0 16 ((GOT_n B =? OW_n B) && (S_state B =? M_state B)) true).
      * lia.
      * lia.
      * lia.
      * css_uclean. lia.
      * exact LP.
  - rewrite css_loop_stop in LP by lia.
    injection LP as Hs0. rewrite Hs0. cbn [Z.b2z].
    step. if_true.
    apply EPI.
Qed.
