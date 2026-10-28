(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Bytes PropExec.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim Monad SoftFloat FmtFp Stdio StrFun.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import SFW1_lemmas.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_memset F_memcpy F_memchr F_strnlen.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Stdio_base Printf_lib F_pop_arg.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Printf_model Printf_mlib Printf_zfacts.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import F_printf_iface.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.

Ltac showall := let x10 := getreg 10%Z in let x11 := getreg 11%Z in let x12 := getreg 12%Z in let x13 := getreg 13%Z in let x14 := getreg 14%Z in let x15 := getreg 15%Z in let x16 := getreg 16%Z in let x17 := getreg 17%Z in let x5 := getreg 5%Z in let x6 := getreg 6%Z in let x7 := getreg 7%Z in let x8 := getreg 8%Z in let x9 := getreg 9%Z in let x18 := getreg 18%Z in let x19 := getreg 19%Z in let x20 := getreg 20%Z in let x21 := getreg 21%Z in let x22 := getreg 22%Z in let x23 := getreg 23%Z in let x24 := getreg 24%Z in let x25 := getreg 25%Z in let x26 := getreg 26%Z in let x27 := getreg 27%Z in let x28 := getreg 28%Z in let x29 := getreg 29%Z in let x30 := getreg 30%Z in let x31 := getreg 31%Z in let x2 := getreg 2%Z in let x1 := getreg 1%Z in
    idtac "a0=" x10; idtac "a1=" x11; idtac "a2=" x12; idtac "a3=" x13; idtac "a4=" x14; idtac "a5=" x15; idtac "a6=" x16; idtac "a7=" x17; idtac "t0=" x5; idtac "t1=" x6; idtac "t2=" x7; idtac "s0=" x8; idtac "s1=" x9; idtac "s2=" x18; idtac "s3=" x19; idtac "s4=" x20; idtac "s5=" x21; idtac "s6=" x22; idtac "s7=" x23; idtac "s8=" x24; idtac "s9=" x25; idtac "s10=" x26; idtac "s11=" x27; idtac "t3=" x28; idtac "t4=" x29; idtac "t5=" x30; idtac "t6=" x31; idtac "sp=" x2; idtac "ra=" x1.
Ltac show_hyp H := let T := type of H in idtac H ":" T.
Ltac show_goal := match goal with |- ?G => idtac "GOAL:" G end.
Ltac dlia := first [lia | match goal with |- ?g => idtac "LIA FAILED:"; idtac g; fail 1 end].
Ltac zl := unfold zlength in *; cbn [length] in *; lia.
Ltac plia := unfold zlength, got_ssp, ssp_guard, PC_DEPTH, OUT_DEPTH, GLOBALS_TOP, FMT_FP_DEPTH, INT_MAX in *; lia.

Ltac hyp_cells :=
  lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
    match goal with H : rw_cells _ m A ?cs' |- _ =>
      replace cs with cs' by (repeat (reflexivity || lazymatch goal with |- @eq Z _ _ => fail | _ => f_equal end); lia); exact H end
  end.

Tactic Notation "callw" tactic3(tac) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ tac | post_call segs m ]
  end.
Ltac fix_stk := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
  match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end.
Tactic Notation "callx" tactic3(tac) := callw tac; try fix_stk.

Ltac fixK K := try (rewrite ?swrap32_small in K by lia); try (rewrite ?signed_of_Z in K by lia); try (rewrite ?Z.add_0_r in K).
Ltac brf K := if_cases K; zify_cond K; fixK K.
Ltac br K := brf K; try (exfalso; lia).

Ltac fixr := try (rewrite !swrap32_small by lia); try (rewrite !Z.add_0_r).

Ltac if_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let v := eval vm_compute in c in change c with v; cbv iota
  end.

Definition hide (P : Prop) := P.
Ltac stash H := lazymatch type of H with hide _ => idtac | ?T => change T with (hide T) in H end.
Ltac stash_mods := repeat match goal with H : context [Z.modulo _ _] |- _ =>
  lazymatch type of H with hide _ => fail | ?T => change T with (hide T) in H end end.
Ltac unstash := unfold hide in *.

Ltac ienter := lazymatch goal with |- Monad.implM _ _ _ _ _ => unfold Monad.implM; apply impl_from_evt | |- ITree.impl _ _ _ _ _ => apply impl_from_evt | _ => idtac end.
Ltac ileave := lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end;
               lazymatch goal with |- ITree.impl _ _ (?c ?s) (epost (fun p => ?Q (fst p) (snd p))) ?ms => change (Monad.implM rsegs c s Q ms) | _ => idtac end.

Lemma zb_length : forall l, length (zb l) = length l.
Proof. intros. unfold zb. apply length_map. Qed.
Lemma zb_app : forall a b, zb (a ++ b) = zb a ++ zb b.
Proof. intros. unfold zb. apply map_app. Qed.
Lemma nth_error_zb : forall l i c, nth_error l i = Some c -> nth_error (zb l) i = Some (Z_to_bv 8 c).
Proof. intros l i c H. unfold zb. rewrite nth_error_map, H. reflexivity. Qed.
Lemma znth_nth_error : forall l i, (0 <= i < zlength l)%Z -> nth_error l (Z.to_nat i) = Some (znth l i).
Proof.
  intros l i Hi. unfold znth. destruct (Z.ltb_spec0 i 0); [lia|].
  destruct (nth_error l (Z.to_nat i)) as [c|] eqn:E.
  - rewrite (nth_error_nth _ _ _ E). reflexivity.
  - apply nth_error_None in E. unfold zlength in Hi. lia.
Qed.
Lemma zbytes_read : forall m A l i a,
  bytes_at rsegs m A (zb l) -> (0 <= i < zlength l)%Z -> a = wa (A + i) ->
  ov_read_bytes rsegs m a 1 = Some [Z_to_bv 8 (znth l i)].
Proof.
  intros m A l i a HB Hi ->.
  eapply (u8ro_read rsegs m A (zb l) i); [exact HB | | lia | reflexivity].
  apply nth_error_zb. apply znth_nth_error. exact Hi.
Qed.
Lemma Forall_znth : forall (P : Z -> Prop) l i, Forall P l -> (0 <= i < zlength l)%Z -> P (znth l i).
Proof.
  intros P l i HF Hi. apply (proj1 (Forall_forall P l) HF). unfold znth. destruct (Z.ltb_spec0 i 0); [lia|].
  apply nth_In. unfold zlength in Hi. lia.
Qed.

Lemma land_lxor_distr : forall a b m, Z.land (Z.lxor a b) m = Z.lxor (Z.land a m) (Z.land b m).
Proof. intros. apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec, !Z.lxor_spec, !Z.land_spec. destruct (Z.testbit a n), (Z.testbit b n), (Z.testbit m n); reflexivity. Qed.

Section Sfx.
  Variable fmt : list Z.
  Definition sfx (k : Z) : list Z := skipn (Z.to_nat k) fmt.
  #[using="Type"] Lemma sfx_cons : forall k, (0 <= k < zlength fmt)%Z -> sfx k = znth fmt k :: sfx (k + 1).
  Proof.
    intros k Hk. unfold sfx. rewrite Z2Nat.inj_add, Nat.add_1_r by lia.
    pose proof (znth_nth_error fmt k Hk) as E.
    destruct (nth_error_split fmt (Z.to_nat k) _ E) as (pre & post & Efmt & Hlen).
    rewrite Efmt at 1 2. rewrite skipn_app, skipn_all2, Hlen, Nat.sub_diag by lia. cbn [skipn app].
    rewrite <- Efmt. f_equal. rewrite Efmt at 1. change (pre ++ znth fmt k :: post) with (pre ++ ([znth fmt k] ++ post)).
    rewrite app_assoc, skipn_app, skipn_all2 by (rewrite length_app; cbn; lia). rewrite length_app. cbn [length].
    replace (S (Z.to_nat k) - (length pre + 1))%nat with 0%nat by lia. reflexivity.
  Qed.
  #[using="Type"] Lemma sfx_nil : forall k, (zlength fmt <= k)%Z -> sfx k = [].
  Proof. intros k Hk. unfold sfx. apply skipn_all2. unfold zlength in Hk. lia. Qed.
  #[using="Type"] Lemma sfx_skipn : forall n k, (0 <= k)%Z -> skipn n (sfx k) = sfx (k + Z.of_nat n).
  Proof. intros n k Hk. unfold sfx. rewrite skipn_skipn. f_equal. lia. Qed.
  #[using="Type"] Lemma sfx_length : forall k, (0 <= k <= zlength fmt)%Z -> zlength (sfx k) = (zlength fmt - k)%Z.
  Proof. intros k Hk. unfold sfx, zlength in *. rewrite length_skipn. lia. Qed.
  #[using="Type"] Lemma sfx_cons_inv : forall k c s, (0 <= k)%Z -> sfx k = c :: s -> (k < zlength fmt)%Z /\ c = znth fmt k /\ s = sfx (k + 1).
  Proof.
    intros k c s Hk E. destruct (Z.lt_ge_cases k (zlength fmt)) as [Hlt|Hge].
    - rewrite sfx_cons in E by lia. injection E as <- <-. split; [exact Hlt| split; reflexivity].
    - rewrite sfx_nil in E by lia. discriminate.
  Qed.

  #[using="Type"] Lemma lit_run_firstn : forall s, lit_run s = firstn (length (lit_run s)) s.
  Proof. induction s as [|c s IH]; cbn; [reflexivity|]. destruct ((c =? 0) || (c =? 37))%Z; cbn; [reflexivity|]. f_equal. exact IH. Qed.
  #[using="Type"] Lemma lit_run_length : forall s, (length (lit_run s) <= length s)%nat.
  Proof. induction s as [|c s IH]; cbn; [lia|]. destruct ((c =? 0) || (c =? 37))%Z; cbn; lia. Qed.
  #[using="Type"] Lemma lit_run_in : forall s j c, nth_error (lit_run s) j = Some c -> c <> 0%Z /\ c <> 37%Z.
  Proof.
    induction s as [|c s IH]; intros j c' H; cbn in H. { destruct j; discriminate. }
    destruct (Z.eqb_spec c 0); [destruct j; discriminate|]. destruct (Z.eqb_spec c 37); [destruct j; discriminate|]. cbn in H.
    destruct j as [|j]; cbn in H. { injection H as <-. lia. } eapply IH. exact H.
  Qed.
  #[using="Type"] Lemma lit_run_stop : forall s c s', skipn (length (lit_run s)) s = c :: s' -> c = 0%Z \/ c = 37%Z.
  Proof.
    induction s as [|c s IH]; intros c' s' H; cbn in H; [discriminate|].
    destruct (Z.eqb_spec c 0); [cbn in H; injection H as <- _; lia|]. destruct (Z.eqb_spec c 37); [cbn in H; injection H as <- _; lia|].
    cbn in H. eapply IH. exact H.
  Qed.

  #[using="Type"] Lemma lit_run_sfx : forall i, (0 <= i)%Z -> let n := zlength (lit_run (sfx i)) in
    (i + n <= Z.max i (zlength fmt))%Z /\ skipn (length (lit_run (sfx i))) (sfx i) = sfx (i + n)
    /\ (forall j, 0 <= j < n -> znth fmt (i + j) <> 0 /\ znth fmt (i + j) <> 37)%Z
    /\ lit_run (sfx i) = firstn (Z.to_nat n) (sfx i).
  Proof.
    intros i Hi. cbv zeta. pose proof (lit_run_length (sfx i)) as L. unfold zlength.
    split. { unfold sfx in L |- *. rewrite length_skipn in L. lia. }
    split. { rewrite sfx_skipn by lia. reflexivity. }
    split.
    - intros j Hj.
      assert (E : nth_error (lit_run (sfx i)) (Z.to_nat j) = Some (znth fmt (i + j))).
      { rewrite lit_run_firstn. rewrite nth_error_firstn. destruct (Nat.ltb_spec0 (Z.to_nat j) (length (lit_run (sfx i)))); [|lia].
        unfold sfx. rewrite nth_error_skipn. replace (Z.to_nat i + Z.to_nat j)%nat with (Z.to_nat (i + j)) by lia.
        apply znth_nth_error. unfold sfx in *. rewrite length_skipn in L. unfold zlength. lia. }
      exact (lit_run_in _ _ _ E).
    - rewrite Nat2Z.id. apply lit_run_firstn.
  Qed.
End Sfx.

Lemma land_M64_id : forall x, (0 <= x < 2^64)%Z -> Z.land x 18446744073709551615 = x.
Proof. intros x Hx. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Lemma landM64_zero : forall p, (-2^63 <= p < 2^63)%Z -> (Z.land p 18446744073709551615 = 0 <-> p = 0)%Z.
Proof.
  intros p Hp. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
  split; intros H; [|subst p; reflexivity]. Z.div_mod_to_equations. nia.
Qed.
Lemma if_false_Z : forall a b : Z, (if false then a else b) = b. Proof. reflexivity. Qed.
Lemma if_true_Z : forall a b : Z, (if true then a else b) = a. Proof. reflexivity. Qed.

Lemma div10_magic : forall x, (0 <= x < 2^64)%Z ->
  Z.shiftr (Z.shiftr (x * 14757395258967641293) 64) 3 = (x / 10)%Z.
Proof.
  intros x Hx. rewrite !Z.shiftr_div_pow2 by lia. rewrite Z.div_div by lia. change (2^64 * 2^3)%Z with (2^67)%Z.
  pose proof (Z.div_mod x 10 ltac:(lia)) as E. pose proof (Z.mod_pos_bound x 10 ltac:(lia)) as R.
  pose proof (Z.div_pos x 10 ltac:(lia) ltac:(lia)) as Q0. pose proof (Z.div_lt_upper_bound x 10 (2^64) ltac:(lia) ltac:(lia)) as Q1.
  set (q := (x / 10)%Z) in *. set (s := (x mod 10)%Z) in *. clearbody q s. subst x.
  symmetry. apply (Z.div_unique_pos _ _ _ (2 * q + s * 14757395258967641293)%Z).
  - change (2^67)%Z with 147573952589676412928%Z. change (2^64)%Z with 18446744073709551616%Z in Q1. lia.
  - change (2^67)%Z with 147573952589676412928%Z. lia.
Qed.
Lemma lor48_digit : forall d, (0 <= d < 10)%Z -> Z.lor d 48 = (48 + d)%Z.
Proof.
  intros d Hd.
  assert (H : (d = 0 \/ d = 1 \/ d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6 \/ d = 7 \/ d = 8 \/ d = 9)%Z) by lia.
  destruct H as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]; reflexivity.
Qed.
Lemma le1_small : forall v, (0 <= v < 256)%Z -> le1 (Z_to_bv 64 v) = [Z_to_bv 8 v].
Proof. intros v Hv. unfold le1. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes]. reflexivity. Qed.

Lemma digits_aux_S : forall f b d y acc,
  digits_aux (S f) b d y acc = if y =? 0 then acc else digits_aux f b d (y / b) (d (y mod b) :: acc).
Proof. reflexivity. Qed.
Lemma digits_aux_acc : forall f b d y acc, digits_aux f b d y acc = digits_aux f b d y [] ++ acc.
Proof.
  induction f as [|f IH]; intros b d y acc; [reflexivity|]. rewrite !digits_aux_S.
  destruct (y =? 0)%Z; [reflexivity|]. rewrite (IH _ _ _ (d (y mod b)%Z :: acc)), (IH _ _ _ [d (y mod b)%Z]). rewrite <- app_assoc. reflexivity.
Qed.
Lemma digits_aux_fuel : forall b f d y acc, (1 < b)%Z -> (0 <= y < b ^ Z.of_nat f)%Z ->
  digits_aux f b d y acc = digits_aux (S f) b d y acc.
Proof.
  intros b. induction f as [|f IH]; intros d y acc Hb Hy.
  - rewrite digits_aux_S. rewrite Z.pow_0_r in Hy. replace y with 0%Z by lia. reflexivity.
  - rewrite !digits_aux_S. destruct (Z.eqb_spec y 0); [reflexivity|].
    apply IH; [lia|]. rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hy by lia. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. rewrite Z.mul_comm. lia.
Qed.
Lemma dec_digits_0 : dec_digits 0 = [].
Proof. reflexivity. Qed.
Lemma dec_digits_small : forall x, (1 <= x <= 9)%Z -> dec_digits x = [48 + x]%Z.
Proof.
  intros x Hx. unfold dec_digits. change 20%nat with (S (S 18)). rewrite !digits_aux_S.
  destruct (Z.eqb_spec x 0); [lia|]. rewrite Z.div_small by lia. cbn [Z.eqb]. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma dec_digits_step : forall x, (10 <= x < 2^64)%Z -> dec_digits x = dec_digits (x / 10) ++ [48 + x mod 10]%Z.
Proof.
  intros x Hx. unfold dec_digits at 1. change 20%nat with (S 19). rewrite digits_aux_S.
  destruct (Z.eqb_spec x 0); [lia|]. rewrite digits_aux_acc. apply (f_equal2 (@app Z)); [|reflexivity]. unfold dec_digits. apply digits_aux_fuel; [lia|].
  split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
  apply Z.lt_trans with (2^64)%Z; [lia|]. vm_compute. reflexivity.
Qed.
Lemma digits_aux_length : forall f b d y acc, (length (digits_aux f b d y acc) <= f + length acc)%nat.
Proof.
  induction f as [|f IH]; intros b d y acc; [cbn; lia|]. rewrite digits_aux_S.
  destruct (y =? 0)%Z; [cbn; lia|]. specialize (IH b d (y / b)%Z (d (y mod b)%Z :: acc)). cbn [length] in IH. lia.
Qed.
Lemma dec_digits_length : forall x, (length (dec_digits x) <= 20)%nat.
Proof. intros x. unfold dec_digits. pose proof (digits_aux_length 20 10 (fun v => 48 + v)%Z x []) as L. cbn [length Nat.add] in L. exact L. Qed.
Lemma dec_digits_range : forall x, Forall (fun c => 48 <= c < 58)%Z (dec_digits x).
Proof.
  intros x. unfold dec_digits.
  assert (G : forall f y acc, Forall (fun c => 48 <= c < 58)%Z acc -> Forall (fun c => 48 <= c < 58)%Z (digits_aux f 10 (fun v => 48 + v)%Z y acc)).
  { induction f as [|f IH]; intros y acc Ha; [exact Ha|]. rewrite digits_aux_S.
    destruct (Z.eqb_spec y 0); [exact Ha|]. apply IH. constructor; [|exact Ha]. pose proof (Z.mod_pos_bound y 10 ltac:(lia)). lia. }
  apply G. constructor.
Qed.

Lemma rw_CB_length : forall m A n (bs : list byte), rw_cells rsegs m A [CB n bs] -> length bs = n.
Proof. intros m A n bs [[[H _] _] _]. exact H. Qed.
Lemma upd_firstn_part : forall {X} (l : list X) i x n, (n <= i < length l)%nat -> firstn n (upd l i x) = firstn n l.
Proof.
  intros X l i x n H. rewrite upd_firstn_skipn by lia. rewrite firstn_app, firstn_firstn, length_firstn.
  replace (Nat.min n i) with n by lia. replace (n - Nat.min i (length l))%nat with 0%nat by lia. cbn. apply app_nil_r.
Qed.
Lemma upd_skipn_at : forall {X} (l : list X) i x, (i < length l)%nat -> skipn i (upd l i x) = x :: skipn (S i) l.
Proof.
  intros X l i x H. rewrite upd_firstn_skipn by lia. rewrite skipn_app, length_firstn.
  replace (Nat.min i (length l)) with i by lia. rewrite Nat.sub_diag, skipn_all2 by (rewrite length_firstn; lia). reflexivity.
Qed.

Lemma hex_digits_0 : forall l, hex_digits l 0 = [].
Proof. reflexivity. Qed.
Lemma hex_digits_step : forall l x, (0 < x < 2^64)%Z ->
  hex_digits l x = hex_digits l (x / 16) ++ [Z.lor (znth XDIGITS (x mod 16)) l].
Proof.
  intros l x Hx. unfold hex_digits at 1. change 16%nat with (S 15). rewrite digits_aux_S.
  destruct (Z.eqb_spec x 0); [lia|]. rewrite digits_aux_acc. apply (f_equal2 (@app Z)); [|reflexivity]. unfold hex_digits. apply digits_aux_fuel; [lia|].
  split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
  change (16 * 16 ^ Z.of_nat 15)%Z with (2^64)%Z. lia.
Qed.
Lemma hex_digits_length : forall l x, (length (hex_digits l x) <= 16)%nat.
Proof. intros l x. unfold hex_digits. pose proof (digits_aux_length 16 16 (fun v => Z.lor (znth XDIGITS v) l) x []) as L. cbn [length Nat.add] in L. exact L. Qed.
Lemma hexchar_ok0 : forall n, (0 <= n < 0 + Z.of_nat 16)%Z -> ((48 <=? Z.lor (znth XDIGITS n) 0) && (Z.lor (znth XDIGITS n) 0 <? 103))%Z = true.
Proof. apply Zrange_forallb. vm_compute. reflexivity. Qed.
Lemma hexchar_ok32 : forall n, (0 <= n < 0 + Z.of_nat 16)%Z -> ((48 <=? Z.lor (znth XDIGITS n) 32) && (Z.lor (znth XDIGITS n) 32 <? 103))%Z = true.
Proof. apply Zrange_forallb. vm_compute. reflexivity. Qed.
Lemma hexchar_range : forall l v, (l = 0 \/ l = 32)%Z -> (0 <= v < 16)%Z -> (48 <= Z.lor (znth XDIGITS v) l < 103)%Z.
Proof.
  intros l v [-> | ->] Hv.
  - pose proof (hexchar_ok0 v ltac:(cbn; lia)) as E. apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
  - pose proof (hexchar_ok32 v ltac:(cbn; lia)) as E. apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
Qed.
Lemma hex_digits_range : forall l x, (l = 0 \/ l = 32)%Z -> Forall (fun c => 48 <= c < 103)%Z (hex_digits l x).
Proof.
  intros l x Hl. unfold hex_digits.
  assert (G : forall f y acc, Forall (fun c => 48 <= c < 103)%Z acc -> Forall (fun c => 48 <= c < 103)%Z (digits_aux f 16 (fun v => Z.lor (znth XDIGITS v) l) y acc)).
  { induction f as [|f IH]; intros y acc Ha; [exact Ha|]. rewrite digits_aux_S.
    destruct (Z.eqb_spec y 0); [exact Ha|]. apply IH. constructor; [|exact Ha]. apply hexchar_range; [exact Hl|]. pose proof (Z.mod_pos_bound y 16 ltac:(lia)). lia. }
  apply G. constructor.
Qed.

Lemma ift : forall (X : Type) (a b : X), (if true then a else b) = a. Proof. reflexivity. Qed.
Lemma iff : forall (X : Type) (a b : X), (if false then a else b) = b. Proof. reflexivity. Qed.

Lemma lo64_range : forall y, (0 <= lo64 y < 2^64)%Z.
Proof. intros y. unfold lo64. rewrite wrap64_mod. apply Z.mod_pos_bound. lia. Qed.
Lemma hi64_range : forall y, (0 <= hi64 y < 2^64)%Z.
Proof. intros y. unfold hi64. rewrite wrap64_mod. apply Z.mod_pos_bound. lia. Qed.
Lemma lo64_hi64 : forall y, (0 <= y < 2^128)%Z -> (lo64 y + 2^64 * hi64 y)%Z = y.
Proof.
  intros y Hy. unfold lo64, hi64. rewrite !wrap64_mod. rewrite Z.shiftr_div_pow2 by lia.
  rewrite (Z.mod_small (y / 2^64)) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; [lia|]; change (2^64 * 2^64)%Z with (2^128)%Z; lia]).
  pose proof (Z.div_mod y (2^64) ltac:(lia)). lia.
Qed.

Section Ranges128.
  Local Open Scope Z_scope.
  #[using="Type"] Lemma mk128_range : forall hi lo, 0 <= hi < 2^64 -> 0 <= lo < 2^64 -> 0 <= mk128 hi lo < 2^128.
  Proof.
    intros hi lo Hh Hl. unfold mk128. apply Bytes.lor_lt_pow2; [|lia].
    rewrite Z.shiftl_mul_pow2 by lia. change (2^128) with (2^64 * 2^64). nia.
  Qed.
  #[using="Type"] Lemma shr64_range64 : forall a k, 0 <= a < 2^64 -> 0 <= k -> 0 <= Z.shiftr a k < 2^64.
  Proof. intros. apply PropExec.Z_shiftr_range; lia. Qed.
  #[using="Type"] Lemma sra63_range : forall x, 0 <= sra63 x < 2^64.
  Proof. intros x. unfold sra63, ONES64. destruct (is_neg64 x); cbn; lia. Qed.
  #[using="Type"] Lemma f128_of_d_range : forall d, 0 <= f128_of_d d < 2^128.
  Proof.
    intros d. unfold f128_of_d.
    set (aRep := lo64 d). set (aExp := Z.shiftr (shl64 aRep 1) 53). set (aSig := Z.shiftr (shl64 aRep 12) 12).
    set (signHi := shl64 (Z.shiftr aRep 63) 63).
    assert (RaRep : 0 <= aRep < 2^64) by (subst aRep; unfold lo64; apply wrap64_range).
    assert (RaSig : 0 <= aSig < 2^64) by (subst aSig; apply shr64_range64; [apply wrap64_range | lia]).
    assert (RsignHi : 0 <= signHi < 2^64) by (subst signHi; apply wrap64_range).
    assert (RINF : 0 <= INF_HI < 2^64) by (unfold INF_HI; lia).
    assert (RIMP : 0 <= IMPLICIT_HI < 2^64) by (unfold IMPLICIT_HI; lia).
    assert (G : forall e s, 0 <= e < 2^64 -> 0 <= s < 2^64 -> 0 <= Z.lor (Z.lor e s) signHi < 2^64).
    { intros e s He Hs. apply PropExec.Z_lor_range; [apply PropExec.Z_lor_range|]; lia. }
    cbv zeta.
    destruct (negb (aExp =? 0)).
    - destruct (negb (aExp =? 2047)); apply mk128_range; try apply wrap64_range;
        apply G; try apply wrap64_range; try (apply shr64_range64; lia). exact RINF.
    - destruct (aSig =? 0).
      + apply mk128_range; [|lia]. apply G; [apply wrap64_range | lia].
      + apply mk128_range.
        * apply G; [apply wrap64_range|]. apply PropExec.Z_lxor_range; [|exact RIMP].
          destruct (negb (is_neg64 _)); [apply wrap64_range|]. apply shr64_range64; [|apply Z.land_nonneg; lia].
          apply shr64_range64; lia.
        * apply Bytes.land_lt_pow2; [apply sra63_range|].
          pose proof (wrap64_range (Z.shiftl aSig (Z.land (add64 (clz64_mirror aSig) 49) 63))). unfold shl64. lia.
  Qed.
End Ranges128.

Lemma sx32_int : forall (slot : word) i, (-2^31 <= i < 2^31)%Z -> (bv_unsigned slot mod 2^32 = i mod 2^32)%Z ->
  sx32 slot = Z_to_bv 64 (i mod 2^64).
Proof.
  intros slot i Hi E. unfold sx32. rewrite Z_to_bv_mod64. apply Z_to_bv_eqm. f_equal.
  change (2^32)%Z with 4294967296%Z in E.
  rewrite swrap32_eq. rewrite <- Zplus_mod_idemp_l, E, Zplus_mod_idemp_l.
  rewrite Z.mod_small by lia. lia.
Qed.
Lemma zx32_uint : forall (slot : word) u, (bv_unsigned slot mod 2^32 = u)%Z -> zx32 slot = Z_to_bv 64 u.
Proof. intros slot u E. unfold zx32. rewrite E. reflexivity. Qed.

Lemma land_land_same : forall a m, Z.land (Z.land a m) m = Z.land a m.
Proof. intros. rewrite <- Z.land_assoc, Z.land_diag. reflexivity. Qed.

Lemma le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le8, word_to_le_bytes, le_bytes_to_word.
  pose proof (bytes_le_to_Z_range bs) as HR. rewrite HL in HR. change (2 ^ (8 * Z.of_nat 8))%Z with (2^64)%Z in HR.
  rewrite unsigned_lit by lia. rewrite <- HL. apply Z_to_le_bytes_to_Z.
Qed.
Lemma cb8_c8_in : forall m A pre post bs, rw_cells rsegs m A (pre ++ CB 8 bs :: post) -> rw_cells rsegs m A (pre ++ C8 (le_bytes_to_word bs) :: post).
Proof.
  intros m A pre post bs [[Hwf Hb] Hw].
  apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 H3]]. cbn in H2.
  split; [split|].
  - apply cells_wf_app. split; [exact H1|]. split; [exact I | exact H3].
  - rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in Hb |- *. rewrite le8_of_bytes by exact H2. exact Hb.
  - rewrite !cells_size_app in *. cbn [cells_size csize] in Hw |- *. exact Hw.
Qed.
Ltac c8ify H := lazymatch type of H with rw_cells _ ?m ?A ?cs =>
  let rec go pre l := lazymatch l with
     | CB 8 ?b :: ?post => apply (cb8_c8_in m A pre post b) in H; cbn [app] in H
     | ?c :: ?l' => go constr:(pre ++ [c]) l'
     | [] => idtac end in
  go constr:(@nil cell) cs end.

Lemma printf_loop_S : forall {St : Type} (OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z) fuel s args cnt,
  printf_loop OUT OUTFP (S fuel) s args cnt =
      match s with
      | [] => munr
      | c :: _ =>
        if (c =? 0)%Z then mret cnt else
        let lit := lit_run s in
        let l := zlength lit in
        let s1 := skipn (Datatypes.length lit) s in
        match s1 with
        | [] => munr
        | c1 :: s2 =>
          if ((c1 =? 37) && match s2 with [] => true | c2 :: _ => (c2 =? 37) end)%Z
          then munr
          else if (0 <? l)%Z then
            (if (INT_MAX - cnt <? l)%Z then munr
             else OUT lit ;;; printf_loop OUT OUTFP fuel s1 args (cnt + l))
          else
            match parse_dir s2, args with
            | Some (d, s3), a :: args' =>
                OUT [] ;;;
                cnt' <- conv OUT OUTFP cnt d a ;;
                printf_loop OUT OUTFP fuel s3 args' cnt'
            | _, _ => munr
            end
        end
      end.
Proof. reflexivity. Qed.
Lemma fp_calls_S : forall fuel s args,
  fp_calls (S fuel) s args =
    match s with
    | [] => []
    | c :: _ =>
      if (c =? 0)%Z then [] else
      let lit := lit_run s in
      let s1 := skipn (Datatypes.length lit) s in
      if (0 <? zlength lit)%Z then fp_calls fuel s1 args
      else match s1 with
           | _ :: s2 =>
             match parse_dir s2, args with
             | Some (d, s3), a :: args' =>
                 match a with
                 | PA_g dd =>
                     let fl := (if Z.land (d_fl d) LEFT_ADJ =? 0 then d_fl d else Z.land (d_fl d) (Z.lnot ZERO_PAD))%Z in
                     (f128_of_d dd, d_w d, d_p d, fl, d_t d) :: fp_calls fuel s3 args'
                 | _ => fp_calls fuel s3 args'
                 end
             | _, _ => []
             end
           | _ => []
           end
    end.
Proof. reflexivity. Qed.

Lemma In_firstn_w : forall {A} (x : A) n l, In x (firstn n l) -> In x l.
Proof. intros A x n l. revert n. induction l as [|y l IH]; intros [|n] H; cbn in H; try contradiction. destruct H as [->|H]; [left; reflexivity | right; eapply IH; exact H]. Qed.
Lemma In_skipn_w : forall {A} (x : A) n l, In x (skipn n l) -> In x l.
Proof. intros A x n l. revert n. induction l as [|y l IH]; intros [|n] H; cbn in H; try contradiction; [exact H|]. right. eapply IH. exact H. Qed.
Lemma Forall_sub : forall {A} (P : A -> Prop) (l : list A) n k, Forall P l -> Forall P (firstn n (skipn k l)).
Proof.
  intros A P l n k H. apply Forall_forall. intros x Hx. apply (proj1 (Forall_forall P l) H).
  eapply In_skipn_w. eapply In_firstn_w. exact Hx.
Qed.
Lemma zb_firstn : forall n l, zb (firstn n l) = firstn n (zb l).
Proof. intros. unfold zb. rewrite firstn_map. reflexivity. Qed.
Lemma zb_skipn : forall n l, zb (skipn n l) = skipn n (zb l).
Proof. intros. unfold zb. rewrite skipn_map. reflexivity. Qed.
Lemma bytes_at_sub : forall m A (l : list byte) k n,
  bytes_at rsegs m A l -> (k <= length l)%nat ->
  bytes_at rsegs m (A + Z.of_nat k) (firstn n (skipn k l)).
Proof.
  intros m A l k n H Hk.
  rewrite <- (firstn_skipn k l) in H. apply bytes_at_app in H. destruct H as [_ H]. rewrite length_firstn, Nat.min_l in H by lia.
  rewrite <- (firstn_skipn n (skipn k l)) in H. apply bytes_at_app in H. destruct H as [H _]. exact H.
Qed.

Lemma parse_dir_conv_type : forall s d rest, parse_dir s = Some (d, rest) -> conv_type (d_t d) = Some (d_ty d).
Proof.
  intros s d rest PD. destruct (parse_dir_shape _ _ _ PD) as (_ & SH). destruct (parse_flags s 0) as [fl0 s1'].
  destruct SH as (_ & c1 & s1b & _ & _ & s2 & _ & c2 & s2b & _ & PX).
  destruct PX as [(_ & _ & _ & Ht & _ & CT) | (_ & _ & c3 & s3b & _ & _ & s3 & _ & _ & CT)]; [rewrite Ht|]; exact CT.
Qed.

Lemma parse_dir_xp : forall s d rest, parse_dir s = Some (d, rest) ->
  ((d_xp d = false /\ d_p d = -1) \/ (d_xp d = true /\ 0 <= d_p d <= INT_MAX))%Z.
Proof.
  intros s d rest PD. destruct (parse_dir_shape _ _ _ PD) as (_ & SH). destruct (parse_flags s 0) as [fl0 s1'].
  destruct SH as (_ & c1 & s1b & _ & _ & s2 & _ & c2 & s2b & _ & PX).
  destruct PX as [(_ & Hp & Hx & _) | (_ & Hx & c3 & s3b & _ & _ & s3 & G & _)].
  - left. split; [exact Hx | exact Hp].
  - right. split; [exact Hx|]. eapply getint_some_range; [|exact G]. unfold INT_MAX. lia.
Qed.

Lemma c8_read4 : forall m A pre (w : word) post a,
  rw_cells rsegs m A (pre ++ C8 w :: post) -> a = wa (A + Z.of_nat (cells_size pre)) ->
  ov_read_bytes rsegs m a 4 = Some (le4 w).
Proof.
  intros m A pre w post a H ->.
  apply (proj1 (rw_cells_app rsegs m A pre (C8 w :: post))) in H. destruct H as [_ H].
  pose proof (rw_cells_bytes_at' _ _ _ _ H) as Hb. cbn [cells_bytes cbytes] in Hb.
  pose proof (bytes_at_ov_read rsegs m _ _ 0 4 Hb) as R. rewrite Z.add_0_r in R.
  rewrite R. 2:{ cbn [skipn]. rewrite length_app, length_le8. lia. }
  change (skipn 0 (le8 w ++ cells_bytes post)) with (le8 w ++ cells_bytes post).
  rewrite firstn_app, length_le8. change (4 - 8)%nat with 0%nat. rewrite firstn_O, app_nil_r, firstn4_le8. reflexivity.
Qed.

Lemma bytes_at_nil : forall m a, (0 <= a)%Z -> (a <= 2^64)%Z -> bytes_at rsegs m a [].
Proof. intros m a H0 H1. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia. Qed.

Section PrintfCore.
  Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
  Context {St : Type}.
  Variables (Fp B BS : Z) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
            (OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z).
  Hypothesis SFR : sink_frame_stmt Fp B BS SINK.
  Hypothesis SFL : sink_flags_stmt Fp SINK.
  Hypothesis TOK : topok_stmt TOPOK.
  Hypothesis HOUT : out_stmt Fp B BS SINK TOPOK OUT.
  Variables (ra : word) (q : Z) (gp tp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
            (F : bvmap 5 word) (fc0 : bv 32) (m0 : word -> option byte)
            (lo : Z) (canary : word) (A : Z) (fmt : list Z) (AP VA : Z) (slots : list word) (nla nlt : word).
  Hypothesis HF : Forall (fun c => 0 <= c < 256)%Z fmt.
  Hypothesis LO : (lo <= q - PC_DEPTH)%Z.
  Hypothesis GLO : (GLOBALS_TOP <= lo)%Z.
  Hypothesis QHI : (q <= 2^47)%Z.
  Hypothesis TQ : TOPOK q.
  Hypothesis FRM0 : frm0 fc0.

  Hypothesis HA : (A + zlength fmt <= 131072)%Z.

  Hypothesis SEP_F : ((172376 <= Fp /\ Fp + 232 <= 375432) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
  Hypothesis SEP_B : ((375440 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
  Hypothesis HAP : (q <= AP)%Z.
  Hypothesis HVA : (AP + 8 <= VA)%Z.
  Hypothesis A0 : (0 <= A)%Z.
  Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
  Hypothesis BS0 : (0 <= BS)%Z.

  Notation sfx := (sfx fmt).
  Definition ctx_all : unit :=
    let _ := (ra, q, gp, tp, s0e, s1e, s2e, s3e, s4e, s5e, s6e, s7e, s8e, s9e, s10e, s11e, F, fc0, m0,
              lo, canary, A, fmt, AP, VA, slots, nla, nlt) in tt.

  Definition W : list (Z * Z) := [(lo, q); (AP, AP + 8); (Fp, Fp + 232); (B, B + BS)]%Z.
  Notation qq := (q + -544)%Z.
  Notation SPv := (Z_to_bv 64 (q + -544)).
  Notation FPv := (Z_to_bv 64 Fp).

  Definition Fokd (F1 F2 : bvmap 5 word) : Prop := forall k : reg, bv_unsigned k <> 10%Z -> reg_get F2 k = reg_get F1 k.
  Definition Fok (Ft : bvmap 5 word) : Prop := forall k : reg, bv_unsigned k <> 10%Z -> reg_get Ft k = reg_get F k.
  #[using="Type"] Lemma Fok_refl : Fok F. Proof. intros k _. reflexivity. Qed.
  #[using="Type"] Lemma Fok_trans : forall F1 F2, Fok F1 -> (forall k : reg, bv_unsigned k <> 10%Z -> reg_get F2 k = reg_get F1 k) -> Fok F2.
  Proof. intros F1 F2 H1 H2 k Hk. rewrite (H2 k Hk). apply H1. exact Hk. Qed.

  Definition POST : Z -> St -> machine_state -> Prop :=
    fun r st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (apv : word) (m' : word -> option byte),
      ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0e s1e (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
               Ft (ret_pc ra) fc' None m' (seg_rom rsegs)
      /\ munch W m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m'
      /\ frm0 fc' /\ Fok Ft
      /\ stk rsegs m' lo q
      /\ SINK m' st'
      /\ ssp_cells m' canary
      /\ rw_cells rsegs m' AP [C8 apv]
      /\ (0 <= r <= INT_MAX)%Z.

  Definition hi_cells : list cell :=
    [C8 canary; C8 s11e; C8 s10e; C8 s9e; C8 s8e; C8 s7e; C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 ra].

  Definition lo_cells (pfx s2s za pl plp l10n alo ahi : word) (j128 : list byte) : list cell :=
    [C8 pfx; C8 s2s; C8 za; C8 pl; C8 plp; C8 (Z_to_bv 64 18446744072850558157); C8 (Z_to_bv 64 18446744073709486079);
     C8 nla; C8 nlt; C8 (Z_to_bv 64 AP); C8 (Z_to_bv 64 75913); C8 l10n; C8 (Z_to_bv 64 ssp_guard); C8 (Z_to_bv 64 214748364);
     C8 alo; C8 ahi; CB 24 j128].

  Definition finv (m : word -> option byte) : Prop :=
    mem_inv rsegs m /\ munch W m0 m /\ wmono rsegs m0 m
    /\ rw_cells rsegs m (q + -112) hi_cells
    /\ stk rsegs m lo (q + -544)
    /\ bytes_at rsegs m A (zb fmt)
    /\ va_area m VA slots
    /\ rw_cells rsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells rsegs m ssp_guard [C8 canary].

  Ltac hush := idtac.
  Ltac seps := idtac.
  Ltac seps_all := idtac.

  Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt).
  Ltac zst := hush; seps; zstep; try (fix_litstore; mem_after_store_opt); hush.

  Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
    let ST := fresh "ST" in let BY := fresh "BY" in let VAA := fresh "VAA" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
    destruct H as (MI & MU & WM & FRhi & ST & BY & VAA & SSP1 & SSP2); unfold W in MU; unfold hi_cells in FRhi;
    unfold got_ssp, ssp_guard in SSP1, SSP2; unfold va_area in VAA;
    unfold PC_DEPTH, GLOBALS_TOP in LO, GLO;
    try (let LT := fresh "LZB" in pose proof (zb_length fmt) as LT;
         lazymatch goal with _ : length (zb fmt) = length fmt, _ : length (zb fmt) = length fmt |- _ => clear LT | _ => idtac end);
    try (let LT := fresh "LU" in pose proof (u64s_length slots) as LT;
         lazymatch goal with _ : length (u64s slots) = _, _ : length (u64s slots) = _ |- _ => clear LT | _ => idtac end);
    unfold zlength in *; hush.
  Ltac hyp :=
    lazymatch goal with
    | |- rw_cells _ ?m ?A ?cs =>
        match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
    | |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
    end.
  Ltac mk_finv := unfold finv, W, hi_cells, got_ssp, ssp_guard, va_area;
    split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [first [hyp | hyp_cells] |]; split; [hyp|]; split; [hyp|]; split; hyp.

  Ltac at_pc p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q0) _ _ _ _) => constr_eq q0 p end.
  Ltac zsto p := repeat (tryif at_pc p then fail else
                   lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zs end).

  #[using="Type"] Lemma u8_lit : forall c, (0 <= c < 256)%Z -> bv_unsigned (Z_to_bv 8 c) = c.
  Proof. intros c Hc. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. apply Z.mod_small. cbn. lia. Qed.
  #[using="HF"] Lemma fmt_rng : forall i, (0 <= i < zlength fmt)%Z -> (0 <= znth fmt i < 256)%Z.
  Proof. intros i Hi. exact (Forall_znth _ fmt i HF Hi). Qed.

  Ltac fix_u8 i := cbv beta; rewrite (u8_lit (znth fmt i)) by (apply fmt_rng; unfold zlength in *; lia).

  Ltac rd_fmt idx :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
      match goal with BYH : bytes_at _ m A (zb fmt) |- _ =>
        let RD := fresh "RD" in let RG := fresh "RG" in
        pose proof (zbytes_read m A fmt idx _ BYH ltac:(unfold zlength in *; lia) eq_refl) as RD;
        pose proof (fmt_rng idx ltac:(unfold zlength in *; lia)) as RG;

        repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
          replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
      end end.

  #[using="Type"] Lemma states0_bytes : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x115a0 (zb STATES0).
  Proof.
    clear. intros m MI. apply ro_bytes_at. { exact MI. } { lia. } { cbn. lia. }
    apply ro_bytes_b_sound. vm_compute. reflexivity.
  Qed.

  #[using="Type"] Lemma states0_read : forall m t ty, mem_inv rsegs m -> conv_type t = Some ty ->
    ov_read_bytes rsegs m (wa (t + 71072 + -65)) 1 = Some [Z_to_bv 8 ty].
  Proof.
    clear. intros m t ty MI CT. pose proof (conv_type_range t ty CT) as R.
    rewrite <- (states0_conv t ty CT).
    eapply (zbytes_read m 0x115a0 STATES0 (t - 65)); [apply states0_bytes; exact MI | change (zlength STATES0) with 58%Z; lia | f_equal; lia].
  Qed.

  Definition PFXSTR : list Z := [45; 43; 32; 32; 32; 48; 88; 48; 120]%Z.
  #[using="Type"] Lemma pfx_bytes : forall m, mem_inv rsegs m -> bytes_at rsegs m 66205 (zb PFXSTR).
  Proof.
    clear. intros m MI. apply ro_bytes_at. { exact MI. } { lia. } { cbn. lia. }
    apply ro_bytes_b_sound. vm_compute. reflexivity.
  Qed.
  #[using="Type"] Lemma pfx_sub : forall m k n, mem_inv rsegs m -> (k + n <= 9)%nat ->
    bytes_at rsegs m (66205 + Z.of_nat k) (zb (firstn n (skipn k PFXSTR))).
  Proof.
    clear. intros m k n MI Hk. rewrite zb_firstn, zb_skipn. apply bytes_at_sub; [apply pfx_bytes; exact MI|]. cbn. lia.
  Qed.
  #[using="Type"] Lemma xdigits_bytes : forall m, mem_inv rsegs m -> bytes_at rsegs m 71536 (zb XDIGITS).
  Proof.
    clear. intros m MI. apply ro_bytes_at. { exact MI. } { lia. } { cbn. lia. }
    apply ro_bytes_b_sound. vm_compute. reflexivity.
  Qed.
  #[using="Type"] Lemma xdigits_read : forall m v, mem_inv rsegs m -> (0 <= v < 16)%Z ->
    ov_read_bytes rsegs m (wa (71536 + v)) 1 = Some [Z_to_bv 8 (znth XDIGITS v)].
  Proof.
    clear. intros m v MI Hv. eapply (zbytes_read m 71536 XDIGITS v); [apply xdigits_bytes; exact MI | change (zlength XDIGITS) with 16%Z; lia | reflexivity].
  Qed.

  Definition JT1 : list Z := [32; 166; 0; 0; 160; 166; 0; 0; 192; 167; 0; 0; 160; 166; 0; 0; 32; 166; 0; 0; 32; 166; 0; 0; 32; 166; 0; 0; 160; 166; 0; 0; 160; 166; 0; 0; 160; 166; 0; 0; 160; 166; 0; 0; 160; 166; 0; 0; 160; 166; 0; 0; 160; 166; 0; 0; 160; 166; 0; 0; 160; 166; 0; 0; 160; 166; 0; 0; 160; 166; 0; 0; 132; 168; 0; 0; 160; 166; 0; 0; 160; 166; 0; 0; 160; 166; 0; 0; 160; 166; 0; 0; 32; 168; 0; 0; 160; 166; 0; 0; 160; 166; 0; 0; 160; 166; 0; 0; 160; 166; 0; 0; 160; 166; 0; 0; 160; 166; 0; 0; 160; 166; 0; 0; 160; 166; 0; 0; 32; 166; 0; 0; 160; 166; 0; 0; 224; 167; 0; 0; 112; 166; 0; 0; 32; 166; 0; 0; 32; 166; 0; 0; 32; 166; 0; 0; 160; 166; 0; 0; 112; 166; 0; 0; 160; 166; 0; 0; 160; 166; 0; 0; 160; 166; 0; 0; 204; 166; 0; 0; 108; 167; 0; 0; 24; 167; 0; 0; 12; 168; 0; 0; 160; 166; 0; 0; 160; 166; 0; 0; 184; 166; 0; 0; 160; 166; 0; 0; 168; 167; 0; 0; 160; 166; 0; 0; 160; 166; 0; 0; 32; 168; 0; 0]%Z.
  #[using="Type"] Lemma jt1_bytes : forall m, mem_inv rsegs m -> bytes_at rsegs m 70572 (zb JT1).
  Proof.
    clear. intros m MI. apply ro_bytes_at. { exact MI. } { lia. } { cbn. lia. }
    apply ro_bytes_b_sound. vm_compute. reflexivity.
  Qed.
  #[using="Type"] Lemma jt1_read_lit : forall m (t : Z) bs, mem_inv rsegs m -> (65 <= t <= 120)%Z ->
    firstn 4 (skipn (Z.to_nat (4 * (t - 65))) (zb JT1)) = bs ->
    ov_read_bytes rsegs m (wa (70572 + 4 * (t - 65))) 4 = Some bs.
  Proof.
    clear. intros m t bs MI Ht <-.
    pose proof (bytes_at_ov_read rsegs m 70572 (zb JT1) (Z.to_nat (4 * (t - 65))) 4 (jt1_bytes m MI)) as R.
    rewrite Z2Nat.id in R by lia. apply R.
    rewrite zb_length. cbn [length JT1]. lia.
  Qed.
  #[using="Type"] Lemma jt1_read_s : forall m t, mem_inv rsegs m -> t = 115%Z -> ov_read_bytes rsegs m (wa (70572 + 4 * (t - 65))) 4 = Some [Z_to_bv 8 184; Z_to_bv 8 166; Z_to_bv 8 0; Z_to_bv 8 0].
  Proof. clear. intros m t MI ->. apply jt1_read_lit; [exact MI | lia | vm_compute; reflexivity]. Qed.
  #[using="Type"] Lemma jt1_read_d : forall m t, mem_inv rsegs m -> (t = 100 \/ t = 105)%Z -> ov_read_bytes rsegs m (wa (70572 + 4 * (t - 65))) 4 = Some [Z_to_bv 8 112; Z_to_bv 8 166; Z_to_bv 8 0; Z_to_bv 8 0].
  Proof. clear. intros m t MI [-> | ->]; (apply jt1_read_lit; [exact MI | lia | vm_compute; reflexivity]). Qed.
  #[using="Type"] Lemma jt1_read_u : forall m t, mem_inv rsegs m -> t = 117%Z -> ov_read_bytes rsegs m (wa (70572 + 4 * (t - 65))) 4 = Some [Z_to_bv 8 168; Z_to_bv 8 167; Z_to_bv 8 0; Z_to_bv 8 0].
  Proof. clear. intros m t MI ->. apply jt1_read_lit; [exact MI | lia | vm_compute; reflexivity]. Qed.
  #[using="Type"] Lemma jt1_read_x : forall m t, mem_inv rsegs m -> (t = 120 \/ t = 88)%Z -> ov_read_bytes rsegs m (wa (70572 + 4 * (t - 65))) 4 = Some [Z_to_bv 8 32; Z_to_bv 8 168; Z_to_bv 8 0; Z_to_bv 8 0].
  Proof. clear. intros m t MI [-> | ->]; (apply jt1_read_lit; [exact MI | lia | vm_compute; reflexivity]). Qed.
  #[using="Type"] Lemma jt1_read_fp : forall m t, mem_inv rsegs m -> conv_type t = Some T_DBL -> ov_read_bytes rsegs m (wa (70572 + 4 * (t - 65))) 4 = Some [Z_to_bv 8 32; Z_to_bv 8 166; Z_to_bv 8 0; Z_to_bv 8 0].
  Proof.
    clear. intros m t MI CT. unfold conv_type, T_PTR, T_INT, T_UINT, T_DBL in CT.
    repeat match type of CT with (if ?c then _ else _) = _ => destruct c eqn:?; [try discriminate CT|] end; try discriminate CT.
    repeat match goal with E : (_ || _) = true |- _ => apply orb_true_iff in E; destruct E as [E|E] | E : (_ =? _) = true |- _ => apply Z.eqb_eq in E end;
      subst; (apply jt1_read_lit; [exact MI | lia | vm_compute; reflexivity]).
  Qed.

  #[using="Type"] Lemma conv_type_cases : forall t ty, conv_type t = Some ty ->
    (ty = T_PTR /\ t = 115%Z) \/ (ty = T_INT /\ (t = 100 \/ t = 105)%Z) \/ (ty = T_UINT /\ (t = 117 \/ t = 120 \/ t = 88)%Z) \/ (ty = T_DBL).
  Proof.
    clear. intros t ty CT. unfold conv_type in CT.
    repeat match type of CT with (if ?c then _ else _) = _ => destruct c eqn:?; [injection CT as <-|] end; try discriminate CT;
    repeat match goal with E : (_ || _) = true |- _ => apply orb_true_iff in E; destruct E as [E|E] | E : (_ =? _) = true |- _ => apply Z.eqb_eq in E end;
      subst; auto 10.
  Qed.

  #[using="Type"] Lemma fl_shl50 : forall fl, (0 <= fl < 131072)%Z ->
    (Z.land (Z.shiftl fl 50) 18446744073709551615 < 9223372036854775808 <-> Z.land fl 8192 = 0)%Z.
  Proof.
    clear. intros fl Hfl. rewrite Z.shiftl_mul_pow2 by lia.
    change 8192%Z with (2^13)%Z. rewrite zb_land_pow2 by lia.
    change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
    split; intros H; Z.div_mod_to_equations; nia.
  Qed.
  #[using="Type"] Lemma nzmask_bits' : forall n, (0 <= n < 0 + Z.of_nat 64)%Z -> Bool.eqb (Z.testbit 18446744073709486079 n) (negb (Z.testbit 65536 n)) = true.
  Proof. clear. apply Zrange_forallb. vm_compute. reflexivity. Qed.
  #[using="Type"] Lemma nzmask_eq : forall fl, (0 <= fl < 131072)%Z -> Z.land fl 18446744073709486079 = Z.land fl (Z.lnot 65536).
  Proof.
    clear. intros fl Hfl. apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec, Z.lnot_spec by lia.
    destruct (Z.lt_ge_cases n 64).
    - pose proof (nzmask_bits' n ltac:(cbn; lia)) as E. destruct (Z.testbit 18446744073709486079 n), (Z.testbit 65536 n); cbn in E; try discriminate; reflexivity.
    - replace (Z.testbit fl n) with false; [reflexivity|]. symmetry.
      destruct (Z.eq_dec fl 0) as [->|]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|].
      apply Z.lt_le_trans with 17%Z; [apply Z.log2_lt_pow2; cbn in *; lia|lia].
  Qed.
  #[using="Type"] Lemma land_bound' : forall a m, (0 <= a)%Z -> (0 <= m)%Z -> (0 <= Z.land a m <= a)%Z.
  Proof.
    clear. intros a m Ha Hm. split; [apply Z.land_nonneg; left; exact Ha|].
    pose proof (Z.sub_land_same_l a m) as E.
    assert (0 <= Z.land a (Z.lnot m))%Z by (apply Z.land_nonneg; left; exact Ha). lia.
  Qed.

  #[using="Type"] Lemma sextw_small : forall p, (-2147483648 <= p < 2147483648)%Z -> bv_swrap 32 (Z.land p 18446744073709551615 + 0) = p.
  Proof.
    clear. intros p Hp. rewrite Z.add_0_r. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
    rewrite swrap32_eq.
    replace (p mod 2 ^ 64)%Z with (p + 2^64 * (- (p / 2^64)))%Z by (Z.div_mod_to_equations; lia).
    change (2^64)%Z with (4294967296 * 4294967296)%Z.
    set (kq := (- (p / (4294967296 * 4294967296)))%Z). clearbody kq. Z.div_mod_to_equations. nia.
  Qed.

  #[using="Type"] Lemma pad_test_xor : forall fl b, Z.land b 73728 = b ->
    (Z.land (Z.lxor fl b) 73728 =? 0)%Z = (Z.land fl 73728 =? b)%Z.
  Proof.
    clear. intros fl b Hb. rewrite land_lxor_distr, Hb.
    destruct (Z.eqb_spec (Z.lxor (Z.land fl 73728) b) 0) as [E|E]; destruct (Z.eqb_spec (Z.land fl 73728) b) as [E2|E2]; try reflexivity; exfalso.
    - apply E2. apply Z.lxor_eq. exact E.
    - apply E. rewrite E2. apply Z.lxor_nilpotent.
  Qed.

  Ltac the_mi k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.

  Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | zl | progress f_equal ].

  Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
  #[using="Type"] Lemma implM_eq_ms : forall {X} (c : M St X) s Q ms ms', ms = ms' -> implM rsegs c s Q ms' -> implM rsegs c s Q ms.
  Proof. intros X c s Q ms ms' -> H. exact H. Qed.
  Tactic Notation "jumpM" tactic3(tac) :=
    (lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
    eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].

  Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
  Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.

  #[using="SFR"] Lemma sink_store : forall m st a (bs : list byte),
    SINK m st -> (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2^64)%Z ->
    (a + Z.of_nat (length bs) <= Fp \/ Fp + 232 <= a)%Z -> (a + Z.of_nat (length bs) <= B \/ B + BS <= a)%Z ->
    SINK (write_to_mem m (wa a) bs) st.
  Proof.
    intros m st a bs HS Ha Hb D1 D2.
    apply (SFR [(a, a + Z.of_nat (length bs))]%Z m _ st HS).
    - apply munch_write; [apply munch_refl | lia | lia | cbn; lia].
    - apply wmono_write. apply wmono_refl.
    - constructor; [cbn; lia | constructor].
    - constructor; [cbn; lia | constructor].
  Qed.
  #[using="SFR"] Lemma sink_call : forall Wc m m' st,
    SINK m st -> munch Wc m m' -> wmono rsegs m m' ->
    Forall (fun iv => snd iv <= Fp \/ Fp + 232 <= fst iv)%Z Wc ->
    Forall (fun iv => snd iv <= B \/ B + BS <= fst iv)%Z Wc ->
    SINK m' st.
  Proof. intros Wc m m' st HS MU WM D1 D2. exact (SFR Wc m m' st HS MU WM D1 D2). Qed.

  #[using="fmt slots"] Lemma arg_ok_W : forall m m' w a, arg_ok Fp B BS m lo q AP w a -> munch W m m' -> arg_ok Fp B BS m' lo q AP w a.
  Proof.
    intros m m' w a H MU. destruct a as [s|i|u|d]; cbn in H |- *; try exact H.
    destruct H as (slack & BYs & Hs & LT23 & PAD & NZ & U47 & D1 & D2 & D3 & D4). exists slack.
    split; [|repeat (split; [assumption|]); assumption].
    eapply bytes_at_transport; [exact BYs | exact MU |].
    unfold W. cbn [disjoint_from]. rewrite length_app, zb_length. cbn [length]. unfold zlength in *. lia.
  Qed.
  #[using="fmt slots"] Lemma args_ok_W : forall m m' ws args, args_ok Fp B BS m lo q AP ws args -> munch W m m' -> args_ok Fp B BS m' lo q AP ws args.
  Proof.
    intros m m' ws args. revert ws. induction args as [|a args IH]; intros ws H MU; [destruct ws; exact I|].
    cbn [args_ok] in H |- *.
    destruct ws as [|w ws]; [exact H|]. destruct H as [H1 H2]. split; [eapply arg_ok_W; eauto | apply IH; assumption].
  Qed.

  Definition lo_cells14 (pfx s2s za pl plp l10n : word) : list cell :=
    [C8 pfx; C8 s2s; C8 za; C8 pl; C8 plp; C8 (Z_to_bv 64 18446744072850558157); C8 (Z_to_bv 64 18446744073709486079);
     C8 nla; C8 nlt; C8 (Z_to_bv 64 AP); C8 (Z_to_bv 64 75913); C8 l10n; C8 (Z_to_bv 64 ssp_guard); C8 (Z_to_bv 64 214748364)].
  #[using="Type"] Lemma lo_split : forall m pfx s2s za pl plp l10n alo ahi j128,
    rw_cells rsegs m (q + -544) (lo_cells pfx s2s za pl plp l10n alo ahi j128) ->
    rw_cells rsegs m (q + -544) (lo_cells14 pfx s2s za pl plp l10n) /\
    rw_cells rsegs m (q + -544 + 112) [C8 alo; C8 ahi] /\ rw_cells rsegs m (q + -544 + 128) [CB 24 j128].
  Proof.
    clear. intros. unfold lo_cells in H.
    apply (proj1 (rw_cells_app rsegs m _ [_;_;_;_;_;_;_;_;_;_;_;_;_;_] _)) in H. destruct H as [H1 H2]. cbn [cells_size csize Nat.add app] in H2.
    change (Z.of_nat 112) with 112%Z in H2.
    apply (proj1 (rw_cells_app rsegs m _ [_;_] _)) in H2. destruct H2 as [H2 H3]. cbn [cells_size csize Nat.add app] in H3.
    change (Z.of_nat 16) with 16%Z in H3.
    split; [exact H1|]. split; [exact H2|]. replace (q + -544 + 128)%Z with (q + -544 + 112 + 16)%Z by lia. exact H3.
  Qed.
  #[using="Type"] Lemma lo_join : forall m pfx s2s za pl plp l10n alo ahi j128,
    rw_cells rsegs m (q + -544) (lo_cells14 pfx s2s za pl plp l10n) ->
    rw_cells rsegs m (q + -544 + 112) [C8 alo; C8 ahi] -> rw_cells rsegs m (q + -544 + 128) [CB 24 j128] ->
    rw_cells rsegs m (q + -544) (lo_cells pfx s2s za pl plp l10n alo ahi j128).
  Proof.
    clear. intros. unfold lo_cells.
    apply (proj2 (rw_cells_app rsegs m _ [_;_;_;_;_;_;_;_;_;_;_;_;_;_] _)). split; [exact H|]. cbn [cells_size csize Nat.add app].
    change (Z.of_nat 112) with 112%Z.
    apply (proj2 (rw_cells_app rsegs m _ [_;_] _)). cbn [cells_size csize Nat.add app]. change (Z.of_nat 16) with 16%Z. split; [exact H0|].
    replace (q + -544 + 112 + 16)%Z with (q + -544 + 128)%Z by lia. exact H1.
  Qed.

  Ltac transport_chunks segs m a bs ::=
    repeat match goal with
    | H : bytes_at segs m ?A2 ?bs2 |- _ =>
        first [ apply (bytes_at_write_other segs m a bs A2 bs2) in H;
                [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
              | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
    | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
    | H : rw_cells segs m ?A2 ?cs2 |- _ =>
        first [ apply (rw_cells_frame segs m A2 cs2 a bs) in H;
                [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
              | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
    | H : ro_cells segs m ?A2 ?cs2 |- _ =>
        first [ apply (ro_cells_frame segs m A2 cs2 a bs) in H;
                [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
              | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
    | H : u8arr segs m ?A2 ?xs |- _ =>
        first [ apply (u8arr_frame segs m A2 xs a bs) in H;
                [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
              | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
    | H : u8ro segs m ?A2 ?xs |- _ =>
        first [ apply (u8ro_frame segs m A2 xs a bs) in H;
                [ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
              | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
    | H : SINK m ?st |- _ =>
        first [ apply (sink_store m st a bs) in H; [ | lia | simpl_sizes; slia | simpl_sizes; slia | simpl_sizes; slia ]
              | idtac "note: dropping SINK hypothesis (not provably disjoint from store):" H; clear H ]
    end.
  Ltac transport_after_call segs m m' MU WM ::=
    let W := lazymatch type of MU with munch ?W _ _ => W end in
    repeat match goal with
    | H : bytes_at segs m ?A2 ?bs2 |- _ =>
        first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
              | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
    | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
    | H : rw_cells segs m ?A2 ?cs2 |- _ =>
        first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
              | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
    | H : ro_cells segs m ?A2 ?cs2 |- _ =>
        first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
              | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
    | H : u8arr segs m ?A2 ?xs |- _ =>
        first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
              | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
    | H : u8ro segs m ?A2 ?xs |- _ =>
        first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
              | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
    | H : SINK m ?st |- _ =>
        first [ eapply (sink_call W m m' st) in H;
                [ | exact MU | exact WM
                | repeat (apply Forall_cons; [ cbn [fst snd]; slia | ]); apply Forall_nil
                | repeat (apply Forall_cons; [ cbn [fst snd]; slia | ]); apply Forall_nil ]
              | idtac "note: dropping SINK hypothesis (not provably disjoint from callee footprint):" H; clear H ]
    | H : stk segs m ?loq ?hiq |- _ =>
        first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; slia ]
              | clear H ]
    | H : munch ?Wq ?mq m |- _ =>
        first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ unfold sub_fp; cbn [outside]; intros; slia | exact MU ] ]
              | fail 100 "callee footprint not inside caller footprint" ]
    | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
    end.

  #[using="fmt LO GLO QHI HAP HVA"] Lemma pop_arg_callq : forall ra' t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (Ft : bvmap 5 word) fc (m : word -> option byte) (a0v k ty : Z) (slot x y : word),
    a0v = (q + -544 + 112)%Z ->
    rw_cells rsegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] ->
    va_area m VA slots -> nth_error slots (Z.to_nat k) = Some slot -> (0 <= k)%Z ->
    rw_cells rsegs m (q + -544 + 112) [C8 x; C8 y] ->
    stk rsegs m lo (q + -544) ->
    mem_inv rsegs m ->
    (ty = T_PTR \/ ty = T_INT \/ ty = T_UINT \/ ty = T_DBL)%Z ->
    evt rsegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Ft' m',
                 ms' = MS (mkR ra' SPv gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          Ft' (ret_pc ra') fc None m' (seg_rom rsegs)
                 /\ munch [(q + -544 - 16, q + -544); (AP, AP + 8); (q + -544 + 112, q + -544 + 112 + 16)]%Z m m'
                 /\ wmono rsegs m m' /\ mem_inv rsegs m'
                 /\ stk rsegs m' lo (q + -544)
                 /\ rw_cells rsegs m' AP [C8 (Z_to_bv 64 (VA + 8 * (k + 1)))]
                 /\ rw_cells rsegs m' (q + -544 + 112) [C8 (F_pop_arg.pop_arg_lo ty slot); C8 (F_pop_arg.pop_arg_hi ty slot y)]
                 /\ Fokd Ft Ft')
      (MS (mkR ra' SPv gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a0v) (Z_to_bv 64 ty) (Z_to_bv 64 AP) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Ft (Z_to_bv 64 0x1c2b4) fc None m (seg_rom rsegs)).
  Proof.
    clear SFR SFL TOK HOUT HF.
    intros until y. intros -> APC VAA NTH Hk ARGC ST MI TY. unfold PC_DEPTH, GLOBALS_TOP in *.
    pose proof (va_area_bound _ _ _ VAA) as VB. unfold zlength in *.
    destruct (stk_split _ _ _ (q + -544 - 16) _ ST ltac:(lia)) as [ST1 ST2].
    assert (Eq : bv_unsigned SPv = (q + -544)%Z) by (apply unsigned_lit; lia).
    assert (Ea : bv_unsigned (Z_to_bv 64 (q + -544 + 112)) = (q + -544 + 112)%Z) by (apply unsigned_lit; lia).
    assert (Ep : bv_unsigned (Z_to_bv 64 AP) = AP) by (apply unsigned_lit; lia).
    assert (IL : (Z.to_nat k < length slots)%nat) by (apply nth_error_Some; rewrite NTH; discriminate).
    eapply evt_mono.
    { eapply (pop_arg_spec ra' SPv gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (q + -544 + 112)) (Z_to_bv 64 ty) (Z_to_bv 64 AP) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Ft fc m VA slots k ty slot x y);
        rewrite ?Eq, ?Ea, ?Ep.
      all: first [exact ST2 | exact APC | exact VAA | exact NTH | exact ARGC | exact MI | exact TY | reflexivity | lia]. }
    cbv beta. intros ms' P. unfold pop_arg_post in P. rewrite !Eq, !Ea, !Ep in P.
    destruct P as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & Ft' & m' & -> & MU & WM & MI' & ST' & APC' & ARGC' & VAA' & HF).
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|].
    split.
    { eapply stk_merge; [ eapply stk_transport_disjoint; [exact ST1 | exact MU | exact WM | cbn [disjoint_from]; lia] | exact ST' | lia ]. }
    split; [exact APC'|]. split; [exact ARGC'|]. exact HF.
  Qed.

  #[using="LO GLO QHI"] Lemma strnlen_callq : forall ra' t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (Ft : bvmap 5 word) fc (m : word -> option byte) (P n : Z) (buf : list byte),
    stk rsegs m lo (q + -544) ->
    bytes_at rsegs m P buf ->
    memchr_ok P 0 n buf ->
    mem_inv rsegs m ->
    (P + Z.of_nat (length buf) <= lo \/ q <= P)%Z -> (0 < P < 2^64)%Z -> (0 <= n < 2^64)%Z ->
    evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
                 ms' = MS (mkR ra' SPv gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (strnlen_res n buf)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          Ft (ret_pc ra') fc None m' (seg_rom rsegs)
                 /\ munch [(q + -544 - 32, q + -544)]%Z m m'
                 /\ wmono rsegs m m' /\ mem_inv rsegs m'
                 /\ stk rsegs m' lo (q + -544)
                 /\ bytes_at rsegs m' P buf)
      (MS (mkR ra' SPv gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Ft (Z_to_bv 64 0x24b98) fc None m (seg_rom rsegs)).
  Proof.
    clear SFR SFL TOK HOUT HF.
    intros until buf. intros ST BUF OK MI SEP P0 Hn. unfold PC_DEPTH, GLOBALS_TOP in *.
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB.
    assert (Eq : bv_unsigned SPv = (q + -544)%Z) by (apply unsigned_lit; lia).
    assert (Ea : bv_unsigned (Z_to_bv 64 P) = P) by (apply unsigned_lit; lia).
    assert (En : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
    eapply evt_mono.
    { eapply (strnlen_spec ra' SPv gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Ft fc m buf lo);
        rewrite ?Eq, ?Ea, ?En.
      all: first [exact ST | exact BUF | exact OK | exact MI | lia]. }
    cbv beta. intros ms' PS. unfold strnlen_post in PS. rewrite !Eq, !Ea, !En in PS.
    destruct PS as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & ST' & BUF').
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|]. exact BUF'.
  Qed.

  #[using="Type"] Lemma zb_nonul : forall s, Forall (fun c => 0 < c < 256)%Z s -> ~ In (Z_to_bv 8 0) (zb s).
  Proof.
    clear. intros s HF IN. unfold zb in IN. apply in_map_iff in IN. destruct IN as (c & E & Hc).
    apply (proj1 (Forall_forall _ s) HF) in Hc.
    assert (E' : bv_unsigned (Z_to_bv 8 c) = bv_unsigned (Z_to_bv 8 0)) by (rewrite E; reflexivity).
    rewrite u8_lit in E' by lia. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z in E'. lia.
  Qed.

  Definition out_postq (ra' : word) (Ft : bvmap 5 word) (fc : bv 32) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (S : Z) (bs : list Z) (m : word -> option byte) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
      ms' = MS (mkR ra' SPv gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               Ft (ret_pc ra') fc None m' (seg_rom rsegs)
      /\ munch [(lo, q + -544); (Fp, Fp + 232); (B, B + BS)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (q + -544)
      /\ SINK m' st'
      /\ ssp_cells m' canary
      /\ bytes_at rsegs m' S (zb bs).
  Lemma out_callq : forall ra' t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (Ft : bvmap 5 word) fc (m : word -> option byte) (st : St) (S L : Z) (bs : list Z),
    SINK m st -> bytes_at rsegs m S (zb bs) -> Forall (fun c => 0 <= c < 256)%Z bs -> L = zlength bs ->
    stk rsegs m lo (q + -544) -> ssp_cells m canary -> mem_inv rsegs m ->
    (0 <= S)%Z -> (S + zlength bs <= q \/ S + zlength bs <= 2^47)%Z ->
    (S + zlength bs <= lo \/ q + -544 <= S)%Z -> (S + zlength bs <= Fp \/ Fp + 232 <= S)%Z -> (S + zlength bs <= B \/ B + BS <= S)%Z ->
    (zlength bs < 2^23)%Z ->
    implM rsegs (OUT bs) st (out_postq ra' Ft fc s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 S bs m)
      (MS (mkR ra' SPv gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 L) FPv a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Ft (Z_to_bv 64 0x1aef0) fc None m (seg_rom rsegs)).
  Proof using BS0 GLO HAP HOUT LO QHI SEP_B SEP_F TOK TQ fmt slots.
    clear SFR SFL HF.
    intros until bs. intros HS SRC RNG -> ST SSP MI HS0 HS1 D1 D2 D3 LB. unfold PC_DEPTH, GLOBALS_TOP in *.
    pose proof (bytes_at_bound _ _ _ _ SRC) as SB. rewrite zb_length in SB. unfold zlength in *.
    assert (Eq : bv_unsigned SPv = (q + -544)%Z) by (apply unsigned_lit; lia).
    assert (Es : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
    pose proof HOUT as HO. unfold out_stmt in HO.
    specialize (HO ra' SPv gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 (Z.of_nat (length bs))) FPv a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Ft fc m st bs lo canary).
    rewrite !Eq, !Es in HO.
    eapply implM_mono.
    { apply HO; try assumption; try reflexivity; unfold OUT_DEPTH, zlength; try lia.
      eapply TOK; [|exact TQ]. lia. }
    cbv beta. intros [] st' ms' P. unfold out_post, SR in P. rewrite !Eq in P. exact P.
  Qed.

  Definition fp_postq (ra' : word) (Ft : bvmap 5 word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (m : word -> option byte) : Z -> St -> machine_state -> Prop :=
    fun r st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
      ms' = MS (mkR ra' SPv gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               Ft' (ret_pc ra') fc' None m' (seg_rom rsegs)
      /\ munch [(lo, q + -544); (Fp, Fp + 232); (B, B + BS)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ frm0 fc' /\ Fokd Ft Ft'
      /\ stk rsegs m' lo (q + -544)
      /\ SINK m' st'
      /\ ssp_cells m' canary.
  #[using="TOK AP VA LO GLO QHI TQ SEP_F SEP_B HAP"] Lemma fp_callq : forall ra' t0 t1 t2 s0 s1 (a1 a2 a7 : word) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (Ft : bvmap 5 word) fc (m : word -> option byte) (st : St) (y w p fl t : Z),
    fpcall_stmt Fp B BS SINK TOPOK OUTFP (y, w, p, fl, t) ->
    SINK m st -> y = (bv_unsigned a1 + 2^64 * bv_unsigned a2)%Z -> bv_unsigned a7 <> 5%Z ->
    (-2^31 <= w <= 1)%Z -> (-2^31 <= p < 2^20)%Z -> (0 <= fl < 2^32)%Z -> (0 <= t < 256)%Z -> Z.lor t 32 <> 97%Z ->
    stk rsegs m lo (q + -544) -> ssp_cells m canary -> mem_inv rsegs m -> frm0 fc ->
    implM rsegs (OUTFP y w p fl t) st (fp_postq ra' Ft s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
      (MS (mkR ra' SPv gp tp t0 t1 t2 s0 s1 FPv a1 a2 (Z_to_bv 64 w) (Z_to_bv 64 p) (Z_to_bv 64 fl) (Z_to_bv 64 t) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Ft (Z_to_bv 64 0x1c4bc) fc None m (seg_rom rsegs)).
  Proof.
    clear SFR SFL HOUT HF.
    intros until t. intros FPC HS Hy H7 Hw Hp Hfl Ht Hta ST SSP MI FRM. unfold PC_DEPTH, GLOBALS_TOP in *.
    assert (Eq : bv_unsigned SPv = (q + -544)%Z) by (apply unsigned_lit; lia).
    cbn [fpcall_stmt] in FPC.
    specialize (FPC ra' SPv gp tp t0 t1 t2 s0 s1 FPv a1 a2 (Z_to_bv 64 w) (Z_to_bv 64 p) (Z_to_bv 64 fl) (Z_to_bv 64 t) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Ft fc m st lo canary).
    rewrite !Eq in FPC.
    eapply implM_mono.
    { apply FPC; try assumption; try reflexivity; unfold FMT_FP_DEPTH; try lia.
      eapply TOK; [|exact TQ]. lia. }
    cbv beta. intros r st' ms' P. unfold fpcall_post, SR in P. rewrite !Eq in P. exact P.
  Qed.

  #[using="Type"] Lemma conv_type_dbl : forall t, conv_type t = Some T_DBL -> (69 <= t <= 103)%Z /\ Z.lor t 32 <> 97%Z.
  Proof.
    clear. intros t CT. unfold conv_type, T_PTR, T_INT, T_UINT, T_DBL in CT.
    repeat match type of CT with (if ?c then _ else _) = _ => destruct c eqn:?; [try discriminate CT|] end; try discriminate CT.
    repeat match goal with E : (_ || _) = true |- _ => apply orb_true_iff in E; destruct E as [E|E] | E : (_ =? _) = true |- _ => apply Z.eqb_eq in E end;
      subst; (split; [lia | discriminate]).
  Qed.

  Ltac out_call :=
    ileave; eapply implM_bind;
    [ eapply out_callq;
      [ match goal with H : SINK _ _ |- _ => exact H end
      | | |
      | match goal with H : stk _ _ _ _ |- _ => exact H end
      | unfold ssp_cells, got_ssp, ssp_guard; split;
        [ match goal with H : rw_cells _ _ 172368 _ |- _ => exact H end
        | match goal with H : rw_cells _ _ 375432 _ |- _ => exact H end ]
      | match goal with H : mem_inv _ _ |- _ => exact H end
      | | | | | | ]
    | cbv beta ].

  Ltac out_ret m :=
    let st' := fresh "st" in intros [] st'; post_call rsegs m;
    try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
    ienter;
    try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
  Ltac fix_rsegs := idtac.

  Definition S_EXIT : Prop :=
    forall (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (r : Z)
           (pfx s2s za pl plp l10n alo ahi : word) (j128 digs pad : list byte) (apv : word),
      let _ := ctx_all in
      finv m ->
      rw_cells rsegs m (q + -544) (lo_cells pfx s2s za pl plp l10n alo ahi j128) ->
      rw_cells rsegs m (q + -392) [CB 24 digs] ->
      rw_cells rsegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells rsegs m AP [C8 apv] ->
      frm0 fc -> Fok Ft -> (0 <= r <= INT_MAX)%Z ->
      evt rsegs (POST r st)
        (MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 r) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x1c260) fc None m (seg_rom rsegs)).

  Definition S_SCAN : Prop :=
    forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (i n cnt' : Z) (Q : machine_state -> Prop),
      let _ := ctx_all in
      finv m ->
      (0 <= i)%Z -> (0 <= n)%Z -> (i + n < zlength fmt)%Z ->
      (forall j, 0 <= j < n -> znth fmt (i + j) <> 0 /\ znth fmt (i + j) <> 37)%Z ->
      (znth fmt (i + n) = 0 \/ (znth fmt (i + n) = 37 /\ i + n + 1 < zlength fmt /\ znth fmt (i + n + 1) <> 37))%Z ->
      (0 < n \/ znth fmt i = 37)%Z ->
      (0 <= cnt' <= INT_MAX)%Z -> (n <= INT_MAX - cnt')%Z ->
      (forall a1 a2 : word,
         evt rsegs Q
           (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (A + i + n)) a1 a2 x13 x14 x15 x16 x17
                    (Z_to_bv 64 (2147483647 - cnt')) (Z_to_bv 64 cnt') x20 (Z_to_bv 64 (A + i + n)) (Z_to_bv 64 n) (Z_to_bv 64 (A + i)) x24 x25 (Z_to_bv 64 n) x27 x28 x29 x30 x31)
               Ft (Z_to_bv 64 0x1b5ac) fc None m (seg_rom rsegs))) ->
      evt rsegs Q
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (znth fmt i)) x11 x12 x13 x14 x15 x16 x17
                 x18 (Z_to_bv 64 cnt') x20 x21 x22 (Z_to_bv 64 (A + i)) x24 x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x1b550) fc None m (seg_rom rsegs)).

  Definition S_FLAGS : Prop :=
    forall (x1 x6 x7 x10 x11 x12 x15 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
           (p k fl b : Z) (w3 : word) (FL : Z) (s1 : list Z),
      let _ := ctx_all in
      finv m -> (0 <= p)%Z -> (1 <= k)%Z -> (p + k <= zlength fmt)%Z ->
      bv_unsigned w3 = b -> (0 <= fl < 131072)%Z -> (0 <= b < 131072)%Z ->
      parse_flags (sfx (p + k)) (Z.lor fl b) = (FL, s1) -> s1 <> [] ->
      (forall (k' c' : Z) (a3 a4 a5 : word),
         (p + k <= k' < zlength fmt)%Z -> s1 = sfx k' -> c' = znth fmt k' -> flag_bit c' = None -> (0 <= FL < 131072)%Z ->
         evt rsegs Q
           (MS (mkR x1 SPv gp tp (Z_to_bv 64 75913) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 (Z_to_bv 64 c') (Z_to_bv 64 (A + k')) a3 a4 a5 (Z_to_bv 64 1) (Z_to_bv 64 32)
                    x18 x19 x20 x21 x22 x23 (Z_to_bv 64 FL) x25 x26 x27 x28 x29 x30 x31)
               Ft (Z_to_bv 64 0x1b664) fc None m (seg_rom rsegs))) ->
      evt rsegs Q
        (MS (mkR x1 SPv gp tp (Z_to_bv 64 75913) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 x11 x12 w3 (Z_to_bv 64 (A + p + k)) x15 (Z_to_bv 64 1) (Z_to_bv 64 32)
                 x18 x19 x20 x21 x22 x23 (Z_to_bv 64 fl) x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x1b640) fc None m (seg_rom rsegs)).

  Definition S_WLOOP : Prop :=
    forall (x1 x5 x6 x7 x10 x12 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
           (pos acc w : Z) (s2 : list Z) (pfx s2s za pl plp alo ahi : word) (j128 : list byte),
      let _ := ctx_all in
      finv m -> rw_cells rsegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
      (0 <= pos < zlength fmt)%Z -> (0 <= acc)%Z ->
      is_digit (znth fmt pos) = true -> getint (sfx pos) acc = Some (w, s2) -> s2 <> [] ->
      (forall (k2 : Z) (t0 t1 a1 a3 a4 a5 a6 a7 : word),
         (pos < k2 < zlength fmt)%Z -> s2 = sfx k2 -> is_digit (znth fmt k2) = false -> (0 <= w <= INT_MAX)%Z ->
         evt rsegs Q
           (MS (mkR x1 SPv gp tp t0 t1 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 a1 (Z_to_bv 64 (A + k2)) a3 a4 a5 a6 a7
                    x18 x19 x20 x21 (Z_to_bv 64 w) x23 x24 x25 x26 x27 x28 x29 x30 x31)
               Ft (Z_to_bv 64 0x1b794) fc None m (seg_rom rsegs))) ->
      evt rsegs Q
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 (Z_to_bv 64 (znth fmt pos + -48)) x12 (Z_to_bv 64 (A + pos)) x14 x15 x16 x17
                 x18 x19 x20 x21 (Z_to_bv 64 acc) x23 x24 x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x1b6f8) fc None m (seg_rom rsegs)).

  Definition S_WIDTH : Prop :=
    forall (x1 x5 x6 x7 x10 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
           (k1 w : Z) (s2 : list Z) (pfx s2s za pl plp alo ahi : word) (j128 : list byte),
      let _ := ctx_all in
      finv m -> rw_cells rsegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
      (0 <= k1 < zlength fmt)%Z ->
      getint (sfx k1) 0 = Some (w, s2) -> s2 <> [] ->
      (forall (k2 : Z) (t0 t1 a1 a3 a4 a5 a6 a7 : word),
         (k1 <= k2 < zlength fmt)%Z -> s2 = sfx k2 -> is_digit (znth fmt k2) = false -> (0 <= w <= INT_MAX)%Z ->
         evt rsegs Q
           (MS (mkR x1 SPv gp tp t0 t1 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 a1 (Z_to_bv 64 (A + k2)) a3 a4 a5 a6 a7
                    x18 x19 x20 x21 (Z_to_bv 64 w) x23 x24 x25 x26 x27 x28 x29 x30 x31)
               Ft (Z_to_bv 64 0x1b794) fc None m (seg_rom rsegs))) ->
      evt rsegs Q
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 (Z_to_bv 64 (znth fmt k1)) (Z_to_bv 64 (A + k1)) x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x1b6ac) fc None m (seg_rom rsegs)).

  Definition S_PLOOP : Prop :=
    forall (x1 x6 x7 x10 x13 x14 x15 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
           (pos acc p : Z) (s3 : list Z) (pfx s2s za pl plp alo ahi : word) (j128 : list byte),
      let _ := ctx_all in
      finv m -> rw_cells rsegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
      (0 <= pos < zlength fmt)%Z -> (0 <= acc)%Z ->
      is_digit (znth fmt pos) = true -> getint (sfx pos) acc = Some (p, s3) -> s3 <> [] ->
      (forall (k3 : Z) (a1 a3 a4 : word),
         (pos < k3 < zlength fmt)%Z -> s3 = sfx k3 -> is_digit (znth fmt k3) = false -> (0 <= p <= INT_MAX)%Z ->
         evt rsegs Q
           (MS (mkR x1 SPv gp tp (Z_to_bv 64 1) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 a1 (Z_to_bv 64 (A + k3)) a3 a4 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
                    x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
               Ft (Z_to_bv 64 0x1b8cc) fc None m (seg_rom rsegs))) ->
      evt rsegs Q
        (MS (mkR x1 SPv gp tp (Z_to_bv 64 1) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 (Z_to_bv 64 (znth fmt pos + -48)) (Z_to_bv 64 (A + pos)) x13 x14 x15 (Z_to_bv 64 10) (Z_to_bv 64 8)
                 x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 acc) x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x1b858) fc None m (seg_rom rsegs)).

  Definition S_PREC : Prop :=
    forall (x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
           (k2 k3 p : Z) (xp : bool) (pfx s2s za pl plp alo ahi : word) (j128 : list byte),
      let _ := ctx_all in
      finv m -> rw_cells rsegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
      (0 <= k2 < zlength fmt)%Z ->
      ( (znth fmt k2 <> 46 /\ p = -1 /\ xp = false /\ k3 = k2)
        \/ (znth fmt k2 = 46 /\ xp = true /\ k2 + 1 < zlength fmt /\ znth fmt (k2 + 1) <> 42
            /\ getint (sfx (k2 + 1)) 0 = Some (p, sfx k3) /\ k2 + 1 <= k3 < zlength fmt) )%Z ->
      (forall (a1 a3 a4 : word),
         (-1 <= p <= INT_MAX)%Z ->
         evt rsegs Q
           (MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 a1 (Z_to_bv 64 (A + k3)) a3 a4 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
                    x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
               Ft (Z_to_bv 64 0x1b8cc) fc None m (seg_rom rsegs))) ->
      evt rsegs Q
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 x11 (Z_to_bv 64 (A + k2)) x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x1b794) fc None m (seg_rom rsegs)).

  Definition S_STATE : Prop :=
    forall (x1 x5 x6 x7 x11 x13 x14 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
           (k3 ty : Z),
      let _ := ctx_all in
      finv m -> (0 <= k3 < zlength fmt)%Z -> conv_type (znth fmt k3) = Some ty ->
      (forall (a2 a3 : word),
         evt rsegs Q
           (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (-1)) (Z_to_bv 64 ty) a2 a3 x14 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
                    x18 x19 x20 (Z_to_bv 64 (A + k3 + 1)) x22 x23 x24 x25 x26 (Z_to_bv 64 0) x28 x29 x30 x31)
               Ft (Z_to_bv 64 0x1b94c) fc None m (seg_rom rsegs))) ->
      evt rsegs Q
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (-1)) x11 (Z_to_bv 64 (A + k3)) x13 x14 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x1b8cc) fc None m (seg_rom rsegs)).

  Definition S_DIR : Prop :=
    forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
           (i : Z) (d : dir) (rest : list Z) (pfx s2s za pl plp alo ahi : word) (j128 : list byte),
      let _ := ctx_all in
      finv m -> rw_cells rsegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
      (0 <= i)%Z -> (i + 1 <= zlength fmt)%Z ->
      parse_dir (sfx (i + 1)) = Some (d, rest) ->
      (forall (k4 : Z) (a2 a3 a4 t1 : word),
         (i + 1 < k4 <= zlength fmt)%Z -> rest = sfx k4 -> znth fmt (k4 - 1) = d_t d ->
         (0 <= d_fl d < 131072)%Z -> (0 <= d_w d <= INT_MAX)%Z -> (-1 <= d_p d <= INT_MAX)%Z ->
         evt rsegs Q
           (MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z (d_xp d))) t1 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
                    (Z_to_bv 64 (-1)) (Z_to_bv 64 (d_ty d)) a2 a3 a4 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
                    x18 x19 x20 (Z_to_bv 64 (A + k4)) (Z_to_bv 64 (d_w d)) x23 (Z_to_bv 64 (d_fl d)) (Z_to_bv 64 (d_p d)) x26 (Z_to_bv 64 0) x28 x29 x30 x31)
               Ft (Z_to_bv 64 0x1b94c) fc None m (seg_rom rsegs))) ->
      evt rsegs Q
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 x11 x12 x13 x14 x15 x16 x17
                 x18 x19 x20 (Z_to_bv 64 (A + i)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x1b5d0) fc None m (seg_rom rsegs)).

  Definition S_END : Prop :=
    forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (r : Z)
           (pfx s2s za pl plp l10n alo ahi : word) (j128 digs pad : list byte) (apv : word),
      let _ := ctx_all in
      finv m ->
      rw_cells rsegs m (q + -544) (lo_cells pfx s2s za pl plp l10n alo ahi j128) ->
      rw_cells rsegs m (q + -392) [CB 24 digs] ->
      rw_cells rsegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells rsegs m AP [C8 apv] ->
      frm0 fc -> Fok Ft -> (0 <= r <= INT_MAX)%Z ->
      evt rsegs (POST r st)
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 r) FPv x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x1c108) fc None m (seg_rom rsegs)).

  Definition S_HEAD (fuel : nat) : Prop :=
    forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i cnt l k : Z) (args : list parg)
           (pfx s2s za pl plp alo ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      finv m ->
      rw_cells rsegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
      rw_cells rsegs m (q + -392) [CB 24 digs] ->
      rw_cells rsegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells rsegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
      args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
      Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i) args) ->
      frm0 fc -> Fok Ft ->
      (0 <= i)%Z -> (0 <= cnt)%Z -> (0 <= l)%Z -> (cnt + l <= INT_MAX)%Z ->
      implM rsegs (printf_loop OUT OUTFP fuel (sfx i) args (cnt + l)) st POST
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 x11 x12 x13 x14 x15 x16 x17
                 x18 (Z_to_bv 64 cnt) FPv (Z_to_bv 64 (A + i)) x22 x23 x24 x25 (Z_to_bv 64 l) x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x1b534) fc None m (seg_rom rsegs)).

  Definition S_CONV : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (x1 x6 x7 x12 x13 x14 x23 x26 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (d : dir) (a : parg) (args : list parg)
           (pfx s2s za pl plp alo ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      finv m ->
      rw_cells rsegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
      rw_cells rsegs m (q + -392) [CB 24 digs] ->
      rw_cells rsegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells rsegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
      args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) (a :: args) ->
      match a with PA_g dd =>
        fpcall_stmt Fp B BS SINK TOPOK OUTFP
          (f128_of_d dd, d_w d, d_p d, (if Z.land (d_fl d) LEFT_ADJ =? 0 then d_fl d else Z.land (d_fl d) (Z.lnot ZERO_PAD))%Z, d_t d)
      | _ => True end ->
      Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
      frm0 fc -> Fok Ft ->
      (1 <= i4 <= zlength fmt)%Z -> znth fmt (i4 - 1) = d_t d -> conv_type (d_t d) = Some (d_ty d) ->
      (0 <= d_fl d < 131072)%Z -> (0 <= d_w d <= INT_MAX)%Z -> (-1 <= d_p d <= INT_MAX)%Z ->
      ((d_xp d = false /\ d_p d = -1) \/ (d_xp d = true /\ 0 <= d_p d <= INT_MAX))%Z ->
      (0 <= c <= INT_MAX)%Z ->
      implM rsegs (cnt' <- conv OUT OUTFP c d a ;; printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
        (MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z (d_xp d))) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
                 (Z_to_bv 64 (-1)) (Z_to_bv 64 (d_ty d)) x12 x13 x14 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
                 (Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 (d_w d)) x23 (Z_to_bv 64 (d_fl d)) (Z_to_bv 64 (d_p d)) x26 (Z_to_bv 64 0) x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x1b94c) fc None m (seg_rom rsegs)).

  Definition body_loc (BA n : Z) : Prop :=
    ((q + -392 <= BA /\ BA + n <= q + -368)
     \/ ((BA + n <= lo \/ q <= BA) /\ (BA + n <= Fp \/ Fp + 232 <= BA) /\ (BA + n <= B \/ B + BS <= BA)))%Z.

  Definition S_TAIL : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
           (fl w p : Z) (prefix body : list Z) (BA PFXA : Z)
           (s2s za plp alo ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      finv m ->
      rw_cells rsegs m (q + -544) (lo_cells (Z_to_bv 64 PFXA) s2s za (Z_to_bv 64 (zlength prefix)) plp (Z_to_bv 64 0) alo ahi j128) ->
      rw_cells rsegs m (q + -392) [CB 24 digs] ->
      rw_cells rsegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells rsegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
      args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
      Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
      frm0 fc -> Fok Ft ->
      bytes_at rsegs m BA (zb body) -> Forall (fun c => 0 <= c < 256)%Z body -> body_loc BA (zlength body) -> (BA + zlength body <= q \/ BA + zlength body <= 2^47)%Z -> (zlength body <= INT_MAX)%Z ->
      (zlength body < 2^23)%Z ->
      (forall m', mem_inv rsegs m' -> bytes_at rsegs m' PFXA (zb prefix)) -> Forall (fun c => 0 <= c < 256)%Z prefix ->
      (0 <= PFXA)%Z -> (PFXA + zlength prefix <= 131072)%Z -> (zlength prefix <= 2)%Z ->
      (0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (-1 <= p <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
      implM rsegs (cnt' <- conv_tail OUT c fl w p prefix body ;; printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
                 x10 (Z_to_bv 64 (BA + zlength body)) x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) (Z_to_bv 64 BA) (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x1bdd0) fc None m (seg_rom rsegs)).

  Definition tregs (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s8 s9 t3 t4 t5 t6 : word) (i4 c w BA wq pq : Z) : bvmap 5 word :=
    mkR xra SPv gp tp t0 t1 t2 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) a0 a1 a2 a3 a4 a5 a6 a7
        s2 (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) (Z_to_bv 64 BA) s8 s9 (Z_to_bv 64 wq) (Z_to_bv 64 pq) t3 t4 t5 t6.
  Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | zl | progress f_equal ].
  Definition tinv (m : word -> option byte) (st : St) (k i4 : Z) (args : list parg) (fuel : nat)
      (PFXA fl n pl pq BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte) : Prop :=
    finv m
    /\ rw_cells rsegs m (q + -544) (lo_cells (Z_to_bv 64 PFXA) (Z_to_bv 64 (Z.land fl 73728)) (Z_to_bv 64 n) (Z_to_bv 64 pl) (Z_to_bv 64 (pl + pq)) (Z_to_bv 64 0) alo ahi j128)
    /\ rw_cells rsegs m (q + -392) [CB 24 digs]
    /\ rw_cells rsegs m (q + -368) [CB 256 pad]
    /\ SINK m st /\ rw_cells rsegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] /\ (0 <= k)%Z
    /\ args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args
    /\ Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args)
    /\ bytes_at rsegs m BA (zb body) /\ Forall (fun c => 0 <= c < 256)%Z body /\ body_loc BA n /\ (BA + n <= q \/ BA + n <= 2^47)%Z /\ n = zlength body
    /\ (forall m', mem_inv rsegs m' -> bytes_at rsegs m' PFXA (zb prefix)) /\ Forall (fun c => 0 <= c < 256)%Z prefix
    /\ (0 <= PFXA)%Z /\ (PFXA + pl <= 131072)%Z /\ pl = zlength prefix /\ (pl <= 2)%Z
    /\ (0 <= i4 <= zlength fmt)%Z /\ (0 <= fl < 131072)%Z /\ (0 <= n <= INT_MAX)%Z /\ (n <= pq)%Z /\ (pl + pq <= INT_MAX)%Z
    /\ (n < 2^23)%Z.

  Ltac dest_tinv H body prefix :=
    let FI := fresh "FI" in
    destruct H as (FI & LOW & DIG & PAD & HS & APC & Hk & AOK & FPC & BODY & BRNG & BLOC & BHI & Hn & HPFX & PRNG & PF0 & PF1 & Hpl & PL2 & Hi4 & Hfl & HnI & Hnp & Hplp & Hn23);
    pose proof FI as FI'; dest_finv FI; unfold lo_cells, ssp_guard in LOW; unfold body_loc in BLOC; unfold INT_MAX in *;
    pose proof (zb_length body) as LB; pose proof (zb_length prefix) as LP;
    let BB := fresh "BB" in pose proof (bytes_at_bound _ _ _ _ BODY) as BB; rewrite LB in BB.

  Ltac mk_tinv :=
    lazymatch goal with |- tinv ?m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      unfold tinv, body_loc;
      split; [mk_finv|];
      split; [unfold lo_cells, ssp_guard; first [hyp | hyp_cells] |];
      split; [match goal with H : rw_cells _ m (q + -392)%Z _ |- _ => exact H end |];
      split; [match goal with H : rw_cells _ m (q + -368)%Z _ |- _ => exact H end |];
      split; [match goal with H : SINK m _ |- _ => exact H end |];
      split; [match goal with H : rw_cells _ m AP _ |- _ => exact H end |];
      split; [lia|];
      split; [assumption|];
      split; [assumption|];
      split; [match goal with H : bytes_at _ m _ (zb _) |- _ => exact H end |];
      repeat (split; [first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl] |]); first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl]
    end.

  Definition S_T6 : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 t3 t4 t5 t6 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (k i4 c w wq pq : Z) (args : list parg)
           (PFXA fl n pl BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      tinv m st k i4 args fuel PFXA fl n pl pq BA prefix body alo ahi j128 digs pad ->
      frm0 fc -> Fok Ft -> (0 <= c)%Z -> (0 <= w <= wq)%Z -> wq = Z.max w (pl + pq) -> (c + wq <= INT_MAX)%Z ->
      implM rsegs (mpad OUT 32 wq (pl + pq) (Z.lxor fl LEFT_ADJ) ;;; printf_loop OUT OUTFP fuel (sfx i4) args (c + wq)) st POST
        (MS (tregs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.land fl 73728)) s8 s9 t3 t4 t5 t6 i4 c w BA wq pq)
            Ft (Z_to_bv 64 0x1bfec) fc None m (seg_rom rsegs)).

  Definition S_T5 : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 t3 t4 t5 t6 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (k i4 c w wq pq : Z) (args : list parg)
           (PFXA fl n pl BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      tinv m st k i4 args fuel PFXA fl n pl pq BA prefix body alo ahi j128 digs pad ->
      frm0 fc -> Fok Ft -> (0 <= c)%Z -> (0 <= w <= wq)%Z -> wq = Z.max w (pl + pq) -> (c + wq <= INT_MAX)%Z ->
      implM rsegs (OUT body ;;; mpad OUT 32 wq (pl + pq) (Z.lxor fl LEFT_ADJ) ;;; printf_loop OUT OUTFP fuel (sfx i4) args (c + wq)) st POST
        (MS (tregs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.land fl 73728)) s8 s9 t3 t4 t5 t6 i4 c w BA wq pq)
            Ft (Z_to_bv 64 0x1bfd0) fc None m (seg_rom rsegs)).

  Definition S_T4 : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (k i4 c w wq pq : Z) (args : list parg)
           (PFXA fl n pl BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      tinv m st k i4 args fuel PFXA fl n pl pq BA prefix body alo ahi j128 digs pad ->
      frm0 fc -> Fok Ft -> (0 <= c)%Z -> (0 <= w <= wq)%Z -> wq = Z.max w (pl + pq) -> (c + wq <= INT_MAX)%Z ->
      implM rsegs (mpad OUT 48 pq n 0 ;;; OUT body ;;; mpad OUT 32 wq (pl + pq) (Z.lxor fl LEFT_ADJ) ;;; printf_loop OUT OUTFP fuel (sfx i4) args (c + wq)) st POST
        (MS (tregs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.land fl 73728)) s8 (Z_to_bv 64 pq) t3 t4 t5 t6 i4 c w BA wq pq)
            Ft (Z_to_bv 64 0x1bf4c) fc None m (seg_rom rsegs)).

  Definition S_T3 : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (k i4 c w wq pq : Z) (args : list parg)
           (PFXA fl n pl BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      tinv m st k i4 args fuel PFXA fl n pl pq BA prefix body alo ahi j128 digs pad ->
      frm0 fc -> Fok Ft -> (0 <= c)%Z -> (0 <= w <= wq)%Z -> wq = Z.max w (pl + pq) -> (c + wq <= INT_MAX)%Z ->
      implM rsegs (mpad OUT 48 wq (pl + pq) (Z.lxor fl ZERO_PAD) ;;; mpad OUT 48 pq n 0 ;;; OUT body ;;; mpad OUT 32 wq (pl + pq) (Z.lxor fl LEFT_ADJ) ;;; printf_loop OUT OUTFP fuel (sfx i4) args (c + wq)) st POST
        (MS (tregs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.land fl 73728)) s8 (Z_to_bv 64 pq) t3 t4 t5 t6 i4 c w BA wq pq)
            Ft (Z_to_bv 64 0x1bec4) fc None m (seg_rom rsegs)).

  Definition S_T2 : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (k i4 c w wq pq : Z) (args : list parg)
           (PFXA fl n pl BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      tinv m st k i4 args fuel PFXA fl n pl pq BA prefix body alo ahi j128 digs pad ->
      frm0 fc -> Fok Ft -> (0 <= c)%Z -> (0 <= w <= wq)%Z -> wq = Z.max w (pl + pq) -> (c + wq <= INT_MAX)%Z ->
      implM rsegs (OUT prefix ;;; mpad OUT 48 wq (pl + pq) (Z.lxor fl ZERO_PAD) ;;; mpad OUT 48 pq n 0 ;;; OUT body ;;; mpad OUT 32 wq (pl + pq) (Z.lxor fl LEFT_ADJ) ;;; printf_loop OUT OUTFP fuel (sfx i4) args (c + wq)) st POST
        (MS (tregs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.land fl 73728)) s8 (Z_to_bv 64 pq) t3 t4 t5 t6 i4 c w BA wq pq)
            Ft (Z_to_bv 64 0x1bea8) fc None m (seg_rom rsegs)).

  Definition S_T1 : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (k i4 c w wq pq : Z) (args : list parg)
           (PFXA fl n pl BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      tinv m st k i4 args fuel PFXA fl n pl pq BA prefix body alo ahi j128 digs pad ->
      frm0 fc -> Fok Ft -> (0 <= c)%Z -> (0 <= w <= wq)%Z -> wq = Z.max w (pl + pq) -> (c + wq <= INT_MAX)%Z ->
      Z.land fl 73728 = 0%Z ->
      implM rsegs (mpad OUT 32 wq (pl + pq) fl ;;; OUT prefix ;;; mpad OUT 48 wq (pl + pq) (Z.lxor fl ZERO_PAD) ;;; mpad OUT 48 pq n 0 ;;; OUT body ;;; mpad OUT 32 wq (pl + pq) (Z.lxor fl LEFT_ADJ) ;;; printf_loop OUT OUTFP fuel (sfx i4) args (c + wq)) st POST
        (MS (tregs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) s8 (Z_to_bv 64 pq) t3 t4 t5 t6 i4 c w BA wq pq)
            Ft (Z_to_bv 64 0x1be28) fc None m (seg_rom rsegs)).

  Definition S_INTC2 : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
           (fl w p argi : Z) (prefix body : list Z) (BA PFXA : Z)
           (s2s za plp ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      finv m ->
      rw_cells rsegs m (q + -544) (lo_cells (Z_to_bv 64 PFXA) s2s za (Z_to_bv 64 (zlength prefix)) plp (Z_to_bv 64 0) (Z_to_bv 64 argi) ahi j128) ->
      rw_cells rsegs m (q + -392) [CB 24 digs] ->
      rw_cells rsegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells rsegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
      args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
      Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
      frm0 fc -> Fok Ft ->
      bytes_at rsegs m BA (zb body) -> Forall (fun c => 0 <= c < 256)%Z body -> (BA + zlength body = q + -368)%Z -> (zlength body <= 24)%Z ->
      (forall m', mem_inv rsegs m' -> bytes_at rsegs m' PFXA (zb prefix)) -> Forall (fun c => 0 <= c < 256)%Z prefix ->
      (0 <= PFXA)%Z -> (PFXA + zlength prefix <= 131072)%Z -> (zlength prefix <= 2)%Z ->
      (0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (-1 <= p <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
      (0 <= argi < 2^64)%Z ->
      implM rsegs (cnt' <- (if ((argi =? 0) && (p =? 0))%Z then conv_tail OUT c fl w p prefix []
                            else conv_tail OUT c fl w (Z.max p (zlength body + (if (argi =? 0)%Z then 1 else 0))) prefix body) ;;
                   printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
                 x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) (Z_to_bv 64 BA) (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x1bd98) fc None m (seg_rom rsegs)).

  Definition S_INTC : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
           (fl w p : Z) (xp : bool) (argi : Z) (prefix body : list Z) (BA PFXA : Z)
           (s2s za plp ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      finv m ->
      rw_cells rsegs m (q + -544) (lo_cells (Z_to_bv 64 PFXA) s2s za (Z_to_bv 64 (zlength prefix)) plp (Z_to_bv 64 0) (Z_to_bv 64 argi) ahi j128) ->
      rw_cells rsegs m (q + -392) [CB 24 digs] ->
      rw_cells rsegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells rsegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
      args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
      Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
      frm0 fc -> Fok Ft ->
      bytes_at rsegs m BA (zb body) -> Forall (fun c => 0 <= c < 256)%Z body -> (BA + zlength body = q + -368)%Z -> (zlength body <= 24)%Z ->
      (forall m', mem_inv rsegs m' -> bytes_at rsegs m' PFXA (zb prefix)) -> Forall (fun c => 0 <= c < 256)%Z prefix ->
      (0 <= PFXA)%Z -> (PFXA + zlength prefix <= 131072)%Z -> (zlength prefix <= 2)%Z ->
      (0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
      ((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
      (0 <= argi < 2^64)%Z ->
      implM rsegs (cnt' <- conv_int OUT c fl w p xp argi prefix body ;; printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
        (MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
                 x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) (Z_to_bv 64 BA) (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x1bd80) fc None m (seg_rom rsegs)).

  Definition dloop_post (x1 x5 x6 x7 x8 x9 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (Ft : bvmap 5 word) (fc : bv 32) (x j : Z) (ds : list byte) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists (a2 a3 : word) (xq : Z) (W : list Z) (m' : word -> option byte),
      ms' = MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 xq) (Z_to_bv 64 (q + -392 + (j - zlength W))) a2 a3
                    (Z_to_bv 64 10) (Z_to_bv 64 18446744072850558157) (Z_to_bv 64 99) x17
                    x18 x19 x20 x21 x22 (Z_to_bv 64 (q + -392 + (j - zlength W))) x24 x25 x26 x27 x28 x29 x30 x31)
               Ft (Z_to_bv 64 0x1bd68) fc None m' (seg_rom rsegs)
      /\ munch [(q + -392, q + -368)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ rw_cells rsegs m' (q + -392) [CB 24 (firstn (Z.to_nat (j - zlength W)) ds ++ zb W ++ skipn (Z.to_nat j) ds)]
      /\ (1 <= xq <= 9)%Z /\ dec_digits x = (48 + xq)%Z :: W /\ (zlength W + 1 <= j)%Z.
  Definition S_DLOOP : Prop :=
    forall (x1 x5 x6 x7 x8 x9 x11 x12 x13 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (x j : Z) (ds : list byte),
      let _ := ctx_all in
      mem_inv rsegs m -> rw_cells rsegs m (q + -392) [CB 24 ds] ->
      (10 <= x < 2^64)%Z -> (zlength (dec_digits x) <= j <= 24)%Z -> x11 = Z_to_bv 64 (q + -392 + j) ->
      evt rsegs (dloop_post x1 x5 x6 x7 x8 x9 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc x j ds m)
        (MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 x) x11 x12 x13
                 (Z_to_bv 64 10) (Z_to_bv 64 18446744072850558157) (Z_to_bv 64 99) x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x1bd30) fc None m (seg_rom rsegs)).

  Definition S_FMTU2 : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (x1 x6 x7 x11 x12 x13 x14 x15 x16 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
           (fl w p : Z) (xp : bool) (x d jj : Z) (W prefix : list Z) (PFXA : Z)
           (pfx s2s za plp ahi : word) (j128 pre pad : list byte),
      let _ := ctx_all in
      finv m ->
      rw_cells rsegs m (q + -544) (lo_cells pfx s2s za (Z_to_bv 64 (zlength prefix)) plp (Z_to_bv 64 0) (Z_to_bv 64 x) ahi j128) ->
      rw_cells rsegs m (q + -392) [CB 24 (pre ++ zb W)] -> zlength pre = jj -> (1 <= jj)%Z ->
      ((d = 0 /\ W = [] /\ dec_digits x = []) \/ (1 <= d <= 9 /\ dec_digits x = (48 + d) :: W))%Z ->
      rw_cells rsegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells rsegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
      args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
      Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
      frm0 fc -> Fok Ft ->
      (forall m', mem_inv rsegs m' -> bytes_at rsegs m' PFXA (zb prefix)) -> Forall (fun c => 0 <= c < 256)%Z prefix ->
      (0 <= PFXA)%Z -> (PFXA + zlength prefix <= 131072)%Z -> (zlength prefix <= 2)%Z ->
      (0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
      ((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
      (0 <= x < 2^64)%Z ->
      implM rsegs (cnt' <- conv_int OUT c fl w p xp x prefix (dec_digits x) ;; printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
        (MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
                 (Z_to_bv 64 d) x11 x12 x13 x14 x15 x16 (Z_to_bv 64 PFXA)
                 (Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) (Z_to_bv 64 (q + -392 + jj)) (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x1bd68) fc None m (seg_rom rsegs)).

  Definition S_FMTU : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (x1 x6 x7 x11 x12 x13 x15 x16 x23 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
           (fl w p : Z) (xp : bool) (x : Z) (prefix : list Z) (PFXA : Z)
           (pfx s2s za plp ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      finv m ->
      rw_cells rsegs m (q + -544) (lo_cells pfx s2s za (Z_to_bv 64 (zlength prefix)) plp (Z_to_bv 64 0) (Z_to_bv 64 x) ahi j128) ->
      rw_cells rsegs m (q + -392) [CB 24 digs] ->
      rw_cells rsegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells rsegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
      args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
      Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
      frm0 fc -> Fok Ft ->
      (forall m', mem_inv rsegs m' -> bytes_at rsegs m' PFXA (zb prefix)) -> Forall (fun c => 0 <= c < 256)%Z prefix ->
      (0 <= PFXA)%Z -> (PFXA + zlength prefix <= 131072)%Z -> (zlength prefix <= 2)%Z ->
      (0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
      ((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
      (0 <= x < 2^64)%Z ->
      implM rsegs (cnt' <- conv_int OUT c fl w p xp x prefix (dec_digits x) ;; printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
        (MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
                 (Z_to_bv 64 x) x11 x12 x13 (Z_to_bv 64 10) x15 x16 (Z_to_bv 64 PFXA)
                 (Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) x23 (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x1bd20) fc None m (seg_rom rsegs)).

  Definition S_CV_D : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
           (fl w p : Z) (xp : bool) (i : Z)
           (pfx s2s za pl plp ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      finv m ->
      rw_cells rsegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) (Z_to_bv 64 (i mod 2^64)) ahi j128) ->
      rw_cells rsegs m (q + -392) [CB 24 digs] ->
      rw_cells rsegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells rsegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
      args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
      Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
      frm0 fc -> Fok Ft ->
      (0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
      ((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
      (-2^31 <= i < 2^31)%Z ->
      implM rsegs (cnt' <- (let '(argi, prefix) :=
                               (if INTMAX_MAX <? i mod 2^64 then ((- (i mod 2^64)) mod 2^64, [45])
                                else if negb (Z.land fl MARK_POS =? 0) then (i mod 2^64, [43])
                                else if negb (Z.land fl PAD_POS =? 0) then (i mod 2^64, [32])
                                else (i mod 2^64, []))%Z in
                            conv_int OUT c fl w p xp argi prefix (dec_digits argi)) ;;
                   printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
        (MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
                 x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) x23 (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x1ba1c) fc None m (seg_rom rsegs)).

  Definition S_CV_U : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
           (fl w p : Z) (xp : bool) (u : Z)
           (pfx s2s za pl plp ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      finv m ->
      rw_cells rsegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) (Z_to_bv 64 u) ahi j128) ->
      rw_cells rsegs m (q + -392) [CB 24 digs] ->
      rw_cells rsegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells rsegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
      args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
      Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
      frm0 fc -> Fok Ft ->
      (0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
      ((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
      (0 <= u < 2^32)%Z ->
      implM rsegs (cnt' <- conv_int OUT c fl w p xp u [] (dec_digits u) ;; printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
        (MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
                 x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) x23 (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x1bb54) fc None m (seg_rom rsegs)).

  Definition xloop_post (x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (Ft : bvmap 5 word) (fc : bv 32) (l x j : Z) (ds : list byte) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists (a2 a3 : word) (m' : word -> option byte),
      let H := hex_digits l x in
      ms' = MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 0) (Z_to_bv 64 l) a2 a3 x14 x15 x16 x17
                    x18 x19 x20 x21 x22 (Z_to_bv 64 (q + -392 + (j - zlength H))) x24 x25 x26 x27 x28 x29 x30 x31)
               Ft (Z_to_bv 64 0x1bc0c) fc None m' (seg_rom rsegs)
      /\ munch [(q + -392, q + -368)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ rw_cells rsegs m' (q + -392) [CB 24 (firstn (Z.to_nat (j - zlength H)) ds ++ zb H ++ skipn (Z.to_nat j) ds)]
      /\ (zlength H <= j)%Z.
  Definition S_XLOOP : Prop :=
    forall (x1 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (l x j : Z) (ds : list byte),
      let _ := ctx_all in
      mem_inv rsegs m -> rw_cells rsegs m (q + -392) [CB 24 ds] ->
      (0 < x < 2^64)%Z -> (l = 0 \/ l = 32)%Z -> (zlength (hex_digits l x) <= j <= 24)%Z -> x23 = Z_to_bv 64 (q + -392 + j) ->
      evt rsegs (xloop_post x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc l x j ds m)
        (MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 x) (Z_to_bv 64 l) x12 x13 x14 x15 x16 x17
                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x1bbe4) fc None m (seg_rom rsegs)).

  Definition S_CV_X : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (x1 x6 x7 x10 x11 x12 x13 x14 x15 x17 x23 x26 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
           (fl w p : Z) (xp : bool) (u t : Z)
           (pfx s2s za pl plp ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      finv m ->
      rw_cells rsegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) (Z_to_bv 64 u) ahi j128) ->
      rw_cells rsegs m (q + -392) [CB 24 digs] ->
      rw_cells rsegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells rsegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
      args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
      Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
      frm0 fc -> Fok Ft ->
      (0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
      ((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
      (0 <= u < 2^32)%Z -> (t = 120 \/ t = 88)%Z ->
      implM rsegs (cnt' <- conv_int OUT c fl w p xp u
                              (if negb (u =? 0) && negb (Z.land fl ALT_FORM =? 0) then (if t =? 120 then [48; 120] else [48; 88]) else [])%Z
                              (hex_digits (Z.land t 32) u) ;;
                   printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
        (MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
                 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 t) x17
                 (Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) x23 (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x1bbcc) fc None m (seg_rom rsegs)).

  Definition S_CV_S : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x27 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
           (fl w p fl10 : Z) (xp : bool) (P : Z) (s : list Z) (slack : list byte)
           (pfx s2s za pl plp ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      finv m ->
      rw_cells rsegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) (Z_to_bv 64 P) ahi j128) ->
      rw_cells rsegs m (q + -392) [CB 24 digs] ->
      rw_cells rsegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells rsegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
      args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
      Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
      frm0 fc -> Fok Ft ->
      (0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
      ((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
      bytes_at rsegs m P (zb s ++ Z_to_bv 8 0 :: slack) -> Forall (fun c => 0 < c < 256)%Z s ->
      (zlength s < 2^23)%Z ->
      ((- (P + zlength s + 1)) mod 8 <= zlength slack)%Z -> (0 < P)%Z -> (P + zlength s + 1 <= 2^47)%Z ->
      (P + zlength s + 1 + zlength slack <= lo \/ q <= P)%Z ->
      (P + zlength s + 1 + zlength slack <= Fp \/ Fp + 232 <= P)%Z ->
      (P + zlength s + 1 + zlength slack <= B \/ B + BS <= P)%Z ->
      (fl10 = Z.land fl (Z.lnot 65536))%Z ->
      implM rsegs (cnt' <- (if (p <? 0) && (INT_MAX <=? zlength s) then munr
                            else conv_tail OUT c (Z.land fl (Z.lnot ZERO_PAD)) w (if p <? 0 then zlength s else Z.min (zlength s) p) []
                                           (firstn (Z.to_nat (if p <? 0 then zlength s else Z.min (zlength s) p)) s))%Z ;;
                   printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
        (MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
                 x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) x23 (Z_to_bv 64 fl) (Z_to_bv 64 p) (Z_to_bv 64 fl10) x27 x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x1ba64) fc None m (seg_rom rsegs)).

  Definition S_CV_FP : Prop :=
    forall fuel, S_HEAD fuel ->
    forall (x1 x6 x7 x10 x11 x12 x13 x14 x15 x17 x23 x26 x28 x29 x30 x31 : word)
           (Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
           (fl w p : Z) (xp : bool) (y t : Z)
           (pfx s2s za pl plp : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      finv m ->
      rw_cells rsegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) (Z_to_bv 64 (lo64 y)) (Z_to_bv 64 (hi64 y)) j128) ->
      rw_cells rsegs m (q + -392) [CB 24 digs] ->
      rw_cells rsegs m (q + -368) [CB 256 pad] ->
      SINK m st -> rw_cells rsegs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
      args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
      fpcall_stmt Fp B BS SINK TOPOK OUTFP (y, w, p, fl, t) ->
      Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
      frm0 fc -> Fok Ft ->
      (0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
      ((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
      (0 <= y < 2^128)%Z -> conv_type t = Some T_DBL ->
      implM rsegs (cnt' <- (if xp && (p <? 0) then munr
                            else if (1 <? w) || (2^20 <=? p) then munr
                            else r <- OUTFP y w p fl t ;; if (r <? 0) || (INT_MAX - c <? r) then munr else mret (c + r))%Z ;;
                   printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
        (MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
                 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 t) x17
                 (Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) x23 (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 (Z_to_bv 64 0) x28 x29 x30 x31)
            Ft (Z_to_bv 64 0x1b9cc) fc None m (seg_rom rsegs)).

  Definition POST1 : Z -> machine_state -> Prop :=
    fun r ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
      ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0e s1e (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
               F (ret_pc ra) fc0 None m' (seg_rom rsegs)
      /\ munch [(lo, q)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo q
      /\ ssp_cells m' canary.

  Definition S_EXIT1 : Prop :=
    forall (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (r : Z)
           (pfx s2s za pl plp l10n alo ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      finv m -> munch [(lo, q)] m0 m ->
      rw_cells rsegs m (q + -544) (lo_cells pfx s2s za pl plp l10n alo ahi j128) ->
      rw_cells rsegs m (q + -392) [CB 24 digs] ->
      rw_cells rsegs m (q + -368) [CB 256 pad] ->
      (0 <= r < 2^64)%Z ->
      evt rsegs (POST1 r)
        (MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 r) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x1c260) fc0 None m (seg_rom rsegs)).

  Definition S_P1 : Prop :=
    forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x27 x28 x29 x30 x31 : word)
           (m : word -> option byte) (pfx s2s za pl plp alo ahi : word) (j128 digs pad : list byte),
      let _ := ctx_all in
      finv m -> munch [(lo, q)] m0 m ->
      rw_cells rsegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
      rw_cells rsegs m (q + -392) [CB 24 digs] ->
      rw_cells rsegs m (q + -368) [CB 256 pad] ->
      pass1_ok fmt = true ->
      evt rsegs (POST1 0)
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 x11 x12 x13 x14 x15 x16 x17
                 x18 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 A) x22 x23 x24 x25 (Z_to_bv 64 0) x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x1b534) fc0 None m (seg_rom rsegs)).

  Definition S_PRO : Prop :=
    forall (x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word) (f : Z) (Q : machine_state -> Prop),
      let _ := ctx_all in
      stk rsegs m0 lo q -> mem_inv rsegs m0 -> bytes_at rsegs m0 A (zb fmt) -> va_area m0 VA slots -> ssp_cells m0 canary ->
      (0 <= f < 2^64)%Z ->
      (forall (m : word -> option byte) (pfx s2s za pl plp alo ahi : word) (j128 digs pad : list byte) (a0 a1 a2 a3 : word),
         finv m -> munch [(q + -544, q)]%Z m0 m ->
         rw_cells rsegs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
         rw_cells rsegs m (q + -392) [CB 24 digs] ->
         rw_cells rsegs m (q + -368) [CB 256 pad] ->
         evt rsegs Q
           (MS (mkR ra SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) a0 a1 a2 a3 nlt x15 x16 x17
                    s2e (Z_to_bv 64 0) (Z_to_bv 64 f) (Z_to_bv 64 A) s6e s7e s8e s9e (Z_to_bv 64 0) s11e x28 x29 x30 x31)
               F (Z_to_bv 64 0x1b534) fc0 None m (seg_rom rsegs))) ->
      evt rsegs Q
        (MS (mkR ra (Z_to_bv 64 q) gp tp x5 x6 x7 s0e s1e (Z_to_bv 64 f) (Z_to_bv 64 A) (Z_to_bv 64 AP) nla nlt x15 x16 x17
                 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e x28 x29 x30 x31)
            F (Z_to_bv 64 0x1b484) fc0 None m0 (seg_rom rsegs)).

End PrintfCore.
