From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import StrFun CType.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import strncmp_c atoi_c sup_reply_code_c.
Import ListNotations.
Open Scope Z_scope.

Lemma u0 : bv_unsigned (Z_to_bv 8 0) = 0.
Proof. reflexivity. Qed.

Lemma walk_nul : forall k x r, ~ In (Z_to_bv 8 0) x -> (S k <= length r)%nat ->
  (forall b, In b (firstn (S k) r) -> bv_unsigned b <> 0) ->
  exists v, strncmp_walk (x ++ [Z_to_bv 8 0]) r k = Some v /\ -256 < v < 256 /\
    (v = 0 <-> firstn (S k) x = firstn (S k) r).
Proof.
  induction k as [|k IH]; intros x r NZ Lr Hr.
  all: destruct r as [|c r]; [cbn [length] in Lr; lia|].
  all: assert (Hc : bv_unsigned c <> 0) by (apply Hr; left; reflexivity).
  all: pose proof (byte_range c) as Rc.
  all: destruct x as [|a x].
  all: cbn [app strncmp_walk].
  1,3: rewrite u0, Z.eqb_refl; cbn [orb];
       eexists; split; [reflexivity|]; split; [lia|];
       cbn [firstn]; split; [intros H; exfalso; lia | intros H; discriminate H].
  all: assert (Ha : bv_unsigned a <> 0) by (intros E; apply NZ; left; apply bv_eq; rewrite E; reflexivity).
  all: pose proof (byte_range a) as Ra.
  all: rewrite (proj2 (Z.eqb_neq _ _) Ha), (proj2 (Z.eqb_neq _ _) Hc); cbn [orb Nat.eqb].
  - eexists; split; [reflexivity|]. split; [lia|]. cbn [firstn]. split.
    + intros E. f_equal. apply bv_eq. lia.
    + intros E. injection E as E. subst c. lia.
  - destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned c)) as [E|E]; cbn [negb].
    + assert (a = c) by (apply bv_eq; exact E). subst c.
      destruct (IH x r) as (v & Hw & Hv & Hiff).
      * intros Hin. apply NZ. right. exact Hin.
      * cbn [length] in Lr. lia.
      * intros b Hb. apply Hr. cbn [firstn]. right. exact Hb.
      * exists v. split; [exact Hw|]. split; [exact Hv|]. cbn [firstn]. split.
        -- intros H. rewrite (proj1 Hiff H). reflexivity.
        -- intros H. injection H as H. apply Hiff. exact H.
    + eexists; split; [reflexivity|]. split; [lia|]. cbn [firstn]. split.
      * intros H. exfalso. lia.
      * intros H. injection H as Hac Hrest. subst c. contradiction (E eq_refl).
Qed.

Lemma strncmp_resp : forall x, ~ In (Z_to_bv 8 0) x ->
  exists v, strncmp_model (x ++ [Z_to_bv 8 0]) resp_lit_bytes 5 = Some v /\ -256 < v < 256 /\
    (v = 0 <-> map bv_unsigned (firstn 5 x) = [114; 101; 115; 112; 32]).
Proof.
  intros x NZ. unfold strncmp_model. change (5 =? 0) with false. cbv iota. change (Z.to_nat (5 - 1)) with 4%nat.
  destruct (walk_nul 4 x resp_lit_bytes NZ) as (v & Hw & Hv & Hiff).
  - change (length resp_lit_bytes) with 6%nat. lia.
  - intros b Hb. unfold resp_lit_bytes in Hb. cbn [map firstn In] in Hb.
    repeat (destruct Hb as [<-|Hb]; [intros E; vm_compute in E; discriminate E|]). destruct Hb.
  - exists v. split; [exact Hw|]. split; [exact Hv|]. rewrite Hiff. split.
    + intros H. rewrite H. reflexivity.
    + intros H. apply map_unsigned_inj. rewrite H. reflexivity.
Qed.

Lemma digits_acc : forall s n, atoi_digits n s = atoi_acc n s.
Proof.
  induction s as [|c s IH]; intros n; [reflexivity|].
  cbn [atoi_digits atoi_acc]. unfold c_digit.
  destruct ((48 <=? bv_unsigned c) && (bv_unsigned c <=? 57)); [apply IH | reflexivity].
Qed.

Lemma atoi_musl_val : forall s, atoi_musl s = atoi_val s.
Proof.
  induction s as [|c s IH]; [reflexivity|].
  unfold atoi_val. cbn [atoi_musl skip_space]. unfold c_space.
  rewrite (orb_comm (bv_unsigned c =? 32)).
  destruct (((9 <=? bv_unsigned c) && (bv_unsigned c <=? 13)) || (bv_unsigned c =? 32)).
  - rewrite IH. reflexivity.
  - rewrite !digits_acc. reflexivity.
Qed.

Lemma eqb_lit_signed : forall x y, -2^63 <= x < 2^63 -> -2^63 <= y < 2^63 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = Z.eqb x y.
Proof.
  intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  change (2^64) with 18446744073709551616. change (2^63) with 9223372036854775808 in Hx, Hy.
  destruct (Z.eqb_spec x y) as [E|E]; [subst; apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E'. apply E. Z.div_mod_to_equations. lia.
Qed.

Theorem sup_reply_code_holds : strncmp_contract -> atoi_contract -> sup_reply_code_contract.
Proof.
  intros STRNCMP ATOI. unfold sup_reply_code_contract, SUP_REPLY_CODE, SUP_REPLY_CODE_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo x
    MI ST LO NZa HX NZ DX HP DP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  pose proof (zr_word a0) as Ra0. unfold inr64 in Ra0.
  assert (LRL : length resp_lit_bytes = 6%nat) by reflexivity.
  pose proof (bytes_at_bound _ _ _ _ HX) as BX. rewrite length_app in BX. cbn [length] in BX.
  destruct (strncmp_resp x NZ) as (v & Hv & Rv & Hiff).
  carve_frame 16%nat ST.
  do 9 step.
  eapply evt_cut.
  { eapply STRNCMP with (ls := x ++ [Z_to_bv 8 0]) (rs := resp_lit_bytes) (v := v).
    - exact HX.
    - rewrite unsigned_lit by lia. exact HP.
    - change (bv_unsigned (Z_to_bv 64 5)) with 5. exact Hv.
    - exact MI. }
  post_call rsegs m1.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m2 end.
  match goal with H : mem_inv rsegs m2 |- _ => rename H into MI2 end.
  step.
  rewrite (eqb_lit_signed v 0) by lia.
  destruct (Z.eqb_spec v 0) as [E0|E0]; cbn [negb].
  - pose proof (proj1 Hiff E0) as PRE.
    assert (L5 : length (firstn 5 x) = 5%nat)
      by (apply (f_equal (@length Z)) in PRE; rewrite length_map in PRE; exact PRE).
    assert (RC : reply_code x = atoi_val (skipn 5 x)).
    { unfold reply_code.
      destruct (list_eq_dec Z.eq_dec (map bv_unsigned (firstn 5 x)) [114; 101; 115; 112; 32]) as [_|NE];
        [apply atoi_musl_val | contradiction]. }
    assert (HY : bytes_at rsegs m2 (bv_unsigned a0 + 5) (skipn 5 x ++ [Z_to_bv 8 0])).
    { rewrite <- (firstn_skipn 5 x) in HX. rewrite <- app_assoc in HX. apply bytes_at_app in HX.
      destruct HX as [_ HY]. rewrite L5 in HY. exact HY. }
    do 5 step.
    release_frame FR ST (bv_unsigned sp).
    eapply evt_cut.
    { eapply ATOI with (A := bv_unsigned a0 + 5) (str := skipn 5 x); [exact HY | exact MI2]. }
    post_call rsegs m2.
    rewrite <- RC.
    finish.
  - assert (RC : reply_code x = -999).
    { unfold reply_code.
      destruct (list_eq_dec Z.eq_dec (map bv_unsigned (firstn 5 x)) [114; 101; 115; 112; 32]) as [E|_];
        [apply Hiff in E; contradiction | reflexivity]. }
    do 4 step.
    release_frame FR ST (bv_unsigned sp).
    step.
    rewrite <- RC.
    finish.
Qed.
