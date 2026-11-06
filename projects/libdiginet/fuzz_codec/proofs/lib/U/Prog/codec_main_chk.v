From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_agree.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells codec_main_inv codec_main_lib
  check_refusal_c check_range_c check_bytes_c.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(** ---- the 32 bytes of a command an encoder wrote ---- *)

(** cmd_out of a command, cut after bytes[24] and after len, display and the padding. *)
Lemma cmd_out_some : forall before w wk wd,
  cmd_out before (Some (w, wk, wd)) =
  (bz w ++ skipn (length w) (firstn 24 before)) ++
  ((bz [Z.of_nat (length w); wd] ++ firstn 2 (skipn 26 before)) ++ le4 (Z_to_bv 64 wk)).
Proof. intros before w wk wd. unfold cmd_out. rewrite <- !app_assoc. reflexivity. Qed.

Lemma cmd_pre_len : forall before w, length before = 32%nat -> (length w <= 24)%nat ->
  length (bz w ++ skipn (length w) (firstn 24 before)) = 24%nat.
Proof.
  intros before w HB HW. unfold bz. rewrite length_app, length_map, length_skipn, length_firstn, HB. lia.
Qed.

Lemma cmd_mid_len : forall before x y, length before = 32%nat ->
  length (bz [x; y] ++ firstn 2 (skipn 26 before)) = 4%nat.
Proof.
  intros before x y HB. unfold bz. rewrite length_app, length_firstn, length_skipn, HB. reflexivity.
Qed.

Lemma nth_app_off : forall (A B : list byte) (i n k : nat) d,
  length A = n -> i = (k + n)%nat -> nth i (A ++ B) d = nth k B d.
Proof.
  intros A B i n k d HA Hi. subst i n. rewrite app_nth2 by lia. f_equal. lia.
Qed.

Lemma skipn_app_off : forall (A B : list byte) (i n k : nat),
  length A = n -> i = (k + n)%nat -> skipn i (A ++ B) = skipn k B.
Proof.
  intros A B i n k HA Hi. subst i n. rewrite <- skipn_skipn, skipn_app_exact. reflexivity.
Qed.

Lemma b8_small : forall x, 0 <= x < 256 -> bv_unsigned (b8 x) = x.
Proof.
  intros x Hx. unfold b8. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  change (bv_modulus 8) with 256. exact Hx.
Qed.

Lemma fold_le_val : forall bs : list byte,
  fold_right (fun b acc => bv_unsigned b + 256 * acc) 0 bs = le_val (map bv_unsigned bs).
Proof.
  induction bs as [|b bs IH]; cbn [fold_right le_val map]; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma cmd_out_len : forall before w wk wd, length before = 32%nat -> (length w <= 24)%nat ->
  cmd_len (cmd_out before (Some (w, wk, wd))) = Z.of_nat (length w).
Proof.
  intros before w wk wd HB HW. unfold cmd_len. rewrite cmd_out_some.
  rewrite (nth_app_off _ _ 24%nat 24%nat 0%nat) by first [apply cmd_pre_len; assumption | reflexivity].
  cbn [bz map app nth]. apply b8_small. lia.
Qed.

Lemma cmd_out_display : forall before w wk wd, length before = 32%nat -> (length w <= 24)%nat ->
  0 <= wd < 256 -> cmd_display (cmd_out before (Some (w, wk, wd))) = wd.
Proof.
  intros before w wk wd HB HW HD. unfold cmd_display. rewrite cmd_out_some.
  rewrite (nth_app_off _ _ 25%nat 24%nat 1%nat) by first [apply cmd_pre_len; assumption | reflexivity].
  cbn [bz map app nth]. apply b8_small. exact HD.
Qed.

Lemma cmd_out_key : forall before w wk wd, length before = 32%nat -> (length w <= 24)%nat ->
  0 <= wk < 2 ^ 32 -> cmd_key (cmd_out before (Some (w, wk, wd))) = wk.
Proof.
  intros before w wk wd HB HW HK. unfold cmd_key. rewrite cmd_out_some.
  rewrite (skipn_app_off _ _ 28%nat 24%nat 4%nat) by first [apply cmd_pre_len; assumption | reflexivity].
  rewrite (skipn_app_off _ _ 4%nat 4%nat 0%nat) by first [apply cmd_mid_len; exact HB | reflexivity].
  change (skipn 0 (le4 (Z_to_bv 64 wk))) with (le4 (Z_to_bv 64 wk)).
  assert (E4 : firstn 4 (le4 (Z_to_bv 64 wk)) = le4 (Z_to_bv 64 wk))
    by (apply firstn_all2; rewrite length_le4; lia).
  rewrite E4.
  rewrite fold_le_val, <- bytes_le_to_Z_le_val, bytes_le_to_Z_le4.
  rewrite unsigned_lit by lia. apply Z.mod_small. exact HK.
Qed.

Lemma firstn_bz : forall w (l : list byte), firstn (length w) (bz w ++ l) = bz w.
Proof. intros w l. unfold bz. rewrite <- (length_map b8 w). apply firstn_app_exact. Qed.

Lemma cmd_out_firstn : forall before w wk wd,
  firstn (length w) (cmd_out before (Some (w, wk, wd))) = bz w.
Proof. intros before w wk wd. rewrite cmd_out_some, <- app_assoc. apply firstn_bz. Qed.

(** ---- the premises of the three checks, from the agreement lemmas ---- *)

(** k.desk is one of SPEC_DESK[0..2], so the record's desk is one the agreement lemmas cover. *)
Lemma od_of_ok : forall k, desk_at k -> od_ok (od_of k).
Proof.
  intros k HD. unfold od_ok, od_of.
  destruct HD as [(_ & E) | [(_ & E) | (_ & E)]]; rewrite E; unfold SDESK_C24, SDESK_PC; cbn.
  - left; reflexivity.
  - right; left; reflexivity.
  - right; right; reflexivity.
Qed.

(** check_refusal's premise from codec_agree.refusal; check_range's from enc_fail_none (as
    cmd_out_fail) and agree_all; check_bytes's from agree_all and owe_ok_wf. *)
Lemma chk_facts : forall k, chk_wf k ->
  ~ (k_kind k = 11 /\ k_b k = 0x70 /\ k_rc k = 0) /\
  (k_rc k <> 0 -> k_out k = k_before k) /\
  k_rc k = k_want_rc k /\
  (k_rc k = 0 ->
     k_want_len k = cmd_len (k_out k) /\
     k_want_len k <= 24 /\
     firstn (Z.to_nat (k_want_len k)) (k_out k) = firstn (Z.to_nat (k_want_len k)) (k_want k) /\
     cmd_key (k_out k) = k_want_key k /\
     cmd_display (k_out k) = k_want_display k).
Proof.
  intros k (HK & HD & _ & HB & HR & HRC & HO & HWRC & HWANT).
  pose proof (od_of_ok k HD) as HOD.
  assert (AG : fst (owe_k k) = fst (enc_k k) /\ (fst (enc_k k) = 0 -> snd (enc_k k) = Some (snd (owe_k k)))).
  { pose proof (agree_all (k_kind k) (od_of k) (k_a k) (k_b k) (k_c k) (k_delta k) (zb (k_bytes k)) (k_n k)
                  HK HOD HR) as G.
    revert G. unfold agrees, enc_k, owe_k.
    destruct (enc_of_call (k_kind k) (od_of k) (k_a k) (k_b k) (k_c k) (k_delta k) (zb (k_bytes k)) (k_n k))
      as [rc o].
    intros G. exact G. }
  pose proof (owe_ok_wf (k_kind k) (od_of k) (k_a k) (k_b k) (k_c k) (k_delta k) (zb (k_bytes k)) (k_n k)
                HK HOD HR) as OW.
  change (owe_spec (k_kind k) (od_of k) (k_a k) (k_b k) (k_c k) (k_delta k) (zb (k_bytes k)) (k_n k))
    with (owe_k k) in OW.
  destruct AG as [A1 A2].
  split; [| split; [| split]].
  - intros (H11 & Hb & H0). rewrite HRC in H0. unfold enc_k in H0. rewrite H11 in H0.
    exact (refusal (od_of k) (k_a k) (k_b k) (k_c k) (k_delta k) (zb (k_bytes k)) (k_n k) Hb H0).
  - intros Hne. rewrite HO. unfold enc_k. apply cmd_out_fail.
    unfold enc_k in HRC. rewrite <- HRC. exact Hne.
  - rewrite HRC, HWRC. symmetry. exact A1.
  - intros H0. rewrite HRC in H0.
    pose proof (A2 H0) as ES.
    assert (W0 : fst (owe_k k) = 0) by (rewrite A1; exact H0).
    specialize (HWANT W0). specialize (OW W0).
    assert (EO : k_out k = cmd_out (repeat (b8 0xa5) 32) (Some (snd (owe_k k))))
      by (rewrite HO, ES, HB; reflexivity).
    revert EO HWANT OW. destruct (snd (owe_k k)) as [[w wk] wd]. intros EO HWANT OW.
    destruct HWANT as (HF & HL & H24 & HKY & HDP).
    destruct OW as (OL & _ & OK & OD).
    assert (LB : length (repeat (b8 0xa5) 32) = 32%nat) by reflexivity.
    rewrite EO, HL, HKY, HDP, Nat2Z.id, HF.
    split; [symmetry; apply cmd_out_len; assumption |].
    split; [exact H24 |].
    split; [apply cmd_out_firstn |].
    split; [apply cmd_out_key; assumption |].
    apply cmd_out_display; [exact LB | exact OL | lia].
Qed.

(** ---- registers, alignment and the frame across a callee ---- *)

(** lw of k.rc: the sign-extended word of an int is the int. *)
Lemma sx32_s32 : forall r, - 2 ^ 31 <= r < 2 ^ 31 -> sx32 (Z_to_bv 64 r) = Z_to_bv 64 r.
Proof.
  intros r Hr. unfold sx32. f_equal. rewrite unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity.
  replace (bv_modulus 32) with (2 ^ 32) by reflexivity.
  Z.div_mod_to_equations. lia.
Qed.

Lemma unsigned_nz : forall r, - 2 ^ 31 <= r < 2 ^ 31 -> r <> 0 -> bv_unsigned (Z_to_bv 64 r) <> 0.
Proof. intros r Hr Hn. rewrite unsigned_lit_wrap. Z.div_mod_to_equations. lia. Qed.

(** &k = sp + 0x20 after the prologue: 8-aligned. *)
Lemma mod8_frame : forall x, x mod 16 = 0 -> (x + -384) mod 8 = 0.
Proof.
  intros x H. apply (proj1 (Z.mod_divide x 16 ltac:(lia))) in H. destruct H as [q ->].
  replace (q * 16 + -384) with ((2 * q - 48) * 8) by lia. apply Z.mod_mul. lia.
Qed.

(** ---- the segment ---- *)

(** 0x14a34 addi a0 = &k; jal check_refusal; addi a0 = &k; jal check_range; lw a0, k.rc;
    bnez a0 to the latch; addi a0 = &k; jal check_bytes; then the latch at 0x14a54. *)
Lemma codec_main_chk : seg_chk_stmt.
Proof.
  unfold seg_chk_stmt.
  intros [ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p F fc m lo data] n ENV CR CG CB NEXT.
  unfold chk_ok, latch_ok, env_ok in *. cenv_cbn.
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' t3' t4' t5' t6' k cur rem u0 pj tj plj c ops m1
         HWF HN HOPS HCUR HC0 HCN FR ST MU WM HMI.
  unfold check_refusal_contract, CHECK_REFUSAL in CR.
  unfold check_range_contract, CHECK_RANGE in CG.
  unfold check_bytes_contract, CHECK_BYTES in CB.
  pose proof ENV as (_ & _ & ST0 & HLO & HSP & _).
  pose proof ST0 as (Hlo0 & _ & _). clear ST0 ENV.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  assert (U416 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -416)) = bv_unsigned sp + -416)
    by (apply unsigned_lit; lia).
  assert (U384 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -384)) = bv_unsigned sp + -384)
    by (apply unsigned_lit; lia).
  assert (A8 : (bv_unsigned sp + -384) mod 8 = 0) by (apply mod8_frame; exact HSP).
  clear HSP.
  pose proof (chk_facts k HWF) as (REF & RNG1 & RNG2 & BYT).
  pose proof HWF as (_ & _ & KWF & _).
  pose proof KWF as (_ & _ & _ & _ & _ & _ & _ & _ & HRCr & _).
  clear HWF.
  pose proof FR as FD. unfold fr in FD. cbn [c_sp] in FD.
  destruct FD as (_ & _ & _ & FK & _).
  (* check_refusal *)
  zstep. zstep.
  eapply evt_cut; [ eapply CR with (k := k) | intros ms' (a0x & a1x & a2x & ->) ].
  { unfold check_refusal_pre. rewrite U384.
    split; [exact (proj1 FK) |]. split; [exact KWF |]. split; [exact A8 | exact REF]. }
  fix_ret. clear REF.
  (* check_range *)
  zstep. zstep.
  eapply evt_cut; [ eapply CG with (lo := lo) (k := k)
                  | intros ms' (t0x & t1x & t2x & a0x2 & a1x2 & a2x2 & a3x & a4x & a5x & a6x & a7x
                                & t3x & t4x & t5x & t6x & m2 & -> & MU2 & WM2 & MI2 & ST2) ].
  { unfold check_range_pre, CHECK_RANGE_DEPTH. rewrite U416, U384.
    split; [exact (proj1 FK) |]. split; [exact KWF |]. split; [exact A8 |].
    split; [lia |]. split; [exact HMI |]. split; [exact ST |]. split; [lia |].
    split; [exact RNG1 | exact RNG2]. }
  unfold CHECK_RANGE_DEPTH in MU2. rewrite U416 in MU2, ST2.
  fix_ret.
  pose proof (fr_munch _ _ _ _ _ _ _ _ _ _ _ FR MU2 WM2) as FR2.
  assert (MU2' : munch [(bv_unsigned sp - 640, bv_unsigned sp)] m m2)
    by (eapply munch_frame; [exact MU | exact MU2 | lia]).
  pose proof (wmono_trans rsegs _ _ _ WM WM2) as WM2'.
  clear FR FK ST MU WM MU2 WM2 HMI RNG1 RNG2.
  (* lw a0, k.rc; bnez a0 *)
  pose proof FR2 as FD. unfold fr in FD. cbn [c_sp] in FD.
  destruct FD as (_ & _ & _ & FK2 & _).
  unfold kcall_cells in FK2.
  zstep.
  rewrite (sx32_s32 (k_rc k)) by lia.
  zstep.
  destruct (Z.eq_dec (k_rc k) 0) as [H0 | Hne].
  2: {
    (* k.rc <> 0: straight to the latch *)
    pose proof (unsigned_nz (k_rc k) HRCr Hne) as UR.
    if_true.
    eapply NEXT; [ exact HN | exact HOPS | exact HCUR | exact HC0 | exact HCN | exact FR2 | exact ST2
                 | exact MU2' | exact WM2' | exact MI2 ]. }
  (* k.rc = 0: check_bytes *)
  rewrite H0. if_false.
  zstep. zstep.
  eapply evt_cut; [ eapply CB with (lo := lo) (k := k)
                  | intros ms' (t0y & t1y & t2y & a0y & a1y & a2y & a3y & a4y & a5y & a6y & a7y
                                & t3y & t4y & t5y & t6y & m3 & -> & MU3 & WM3 & MI3 & ST3) ].
  { unfold check_bytes_pre, CHECK_BYTES_DEPTH. rewrite U416, U384.
    destruct (BYT H0) as (B1 & B2 & B3 & B4 & B5).
    split; [exact (proj1 FK2) |]. split; [exact KWF |]. split; [exact A8 |].
    split; [lia |]. split; [exact MI2 |]. split; [exact ST2 |]. split; [lia |].
    split; [exact B1 |]. split; [exact B2 |]. split; [exact B3 |]. split; [exact B4 | exact B5]. }
  unfold CHECK_BYTES_DEPTH in MU3. rewrite U416 in MU3, ST3.
  fix_ret.
  pose proof (fr_munch _ _ _ _ _ _ _ _ _ _ _ FR2 MU3 WM3) as FR3.
  assert (MU3' : munch [(bv_unsigned sp - 640, bv_unsigned sp)] m m3)
    by (eapply munch_frame; [exact MU2' | exact MU3 | lia]).
  pose proof (wmono_trans rsegs _ _ _ WM2' WM3) as WM3'.
  eapply NEXT; [ exact HN | exact HOPS | exact HCUR | exact HC0 | exact HCN | exact FR3 | exact ST3
               | exact MU3' | exact WM3' | exact MI3 ].
Qed.
