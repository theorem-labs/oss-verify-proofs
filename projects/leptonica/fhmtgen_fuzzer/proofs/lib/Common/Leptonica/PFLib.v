(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac RefMemcpyLib.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import Frame.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FR : Z := 3376.
Definition oL : Z := 2096.   (* [comment removed for export] *)
Definition oMSG : Z := 2080.
Definition oV : Z := 2400.   (* [comment removed for export] *)
Definition oCK : Z := 2168.  (* [comment removed for export] *)
Definition oF : Z := 2768.   (* [comment removed for export] *)
Definition oIB : Z := 2752.  (* [comment removed for export] *)
Definition oP : Z := 3312.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint segs_lo (segs : list Segment) : Z :=
  match segs with
  | [] => 2 ^ 64
  | s :: r => Z.min (Z.of_N (seg_base s)) (segs_lo r)
  end.
Fixpoint segs_hi (segs : list Segment) : Z :=
  match segs with
  | [] => 0
  | s :: r => Z.max (Z.of_N (seg_base s) + Z.of_N (seg_size s)) (segs_hi r)
  end.

Lemma find_segment_range : forall segs a n s,
  0 <= n -> find_segment segs a n = Some s -> segs_lo segs <= a /\ a + n <= segs_hi segs.
Proof.
  induction segs as [|s0 r IH]; intros a n s Hn H; cbn in H.
  - discriminate H.
  - cbn [segs_lo segs_hi].
    destruct (Z.leb (Z.of_N (seg_base s0)) a) eqn:E1;
    destruct (Z.leb (a + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E2; cbn [andb] in H.
    + apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
    + destruct (IH a n s Hn H). lia.
    + destruct (IH a n s Hn H). lia.
    + destruct (IH a n s Hn H). lia.
Qed.

Lemma seg_rom_range : forall segs (x : word) b,
  seg_rom segs x = Some b -> segs_lo segs <= bv_unsigned x /\ bv_unsigned x + 1 <= segs_hi segs.
Proof.
  intros segs x b H. unfold seg_rom, memory_read in H.
  destruct (find_segment segs (bv_unsigned x) (Z.of_N 1)) as [s|] eqn:E; [|discriminate H].
  exact (find_segment_range segs (bv_unsigned x) 1 s ltac:(lia) E).
Qed.

(* [comment removed for export] *)
Lemma rdn_defined : forall segs m (a : Z) (n : nat),
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat n -> m (Z_to_bv 64 (a + i)) <> None) ->
  exists bs, rdn segs m (Z_to_bv 64 a) n = Some bs /\ length bs = n.
Proof.
  intros segs m a n. revert a. induction n as [|n IH]; intros a Ha Hn Hd.
  - exists []. split; reflexivity.
  - cbn [rdn].
    destruct (m (Z_to_bv 64 a)) as [b|] eqn:E.
    2:{ exfalso. apply (Hd 0 ltac:(lia)). rewrite Z.add_0_r. exact E. }
    destruct (IH (a + 1) ltac:(lia) ltac:(lia)) as (bs & Hbs & Hl).
    { intros i Hi. replace (a + 1 + i) with (a + (1 + i)) by lia. apply Hd. lia. }
    replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)).
    2:{ apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
        assert (H1 : bv_unsigned (1 : word) = 1%Z) by reflexivity. rewrite H1.
        unfold bv_wrap. rewrite Zplus_mod_idemp_l. reflexivity. }
    rewrite Hbs. exists (b :: bs). split; [reflexivity | cbn; lia].
Qed.

(* [comment removed for export] *)
Lemma rdn1_rom : forall segs m (x : word) b,
  m x = None -> seg_rom segs x = Some b -> rdn segs m x 1 = Some [b].
Proof. intros segs m x b Hm Hr. cbn [rdn]. rewrite Hm, Hr. reflexivity. Qed.

(* [comment removed for export] *)
Definition defined (m : word -> option byte) (a : Z) (n : Z) : Prop :=
  forall i, 0 <= i < n -> m (Z_to_bv 64 (a + i)) <> None.

Lemma defined_grows : forall m m' a n, mem_grows m m' -> defined m a n -> defined m' a n.
Proof. intros m m' a n G D i Hi. apply G. apply D. exact Hi. Qed.

Lemma defined_0 : forall m a, defined m a 0.
Proof. intros m a i Hi. lia. Qed.

Lemma defined_wbytes : forall m (a : Z) bs,
  0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  defined (wbytes m (Z_to_bv 64 a) bs) a (Z.of_nat (length bs)).
Proof.
  intros m a bs Ha Hn i Hi E.
  pose proof (rdn_wbytes_hit [] bs m (Z_to_bv 64 a)) as H.
  rewrite u_Z2bv in H by lia. specialize (H Hn).
  pose proof (rdn_nth [] (wbytes m (Z_to_bv 64 a) bs) (length bs) (Z_to_bv 64 a) bs (Z.to_nat i) H ltac:(lia)) as B.
  replace (Z_to_bv 64 a + nat_to_word (Z.to_nat i))%bv with (Z_to_bv 64 (a + i)) in B.
  2:{ unfold nat_to_word. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
      unfold bv_wrap. rewrite <- Zplus_mod. f_equal. lia. }
  cbn [rdn] in B. rewrite E in B.
  destruct (seg_rom [] (Z_to_bv 64 (a + i))) eqn:S; [|discriminate B].
  unfold seg_rom, memory_read in S. cbn in S. discriminate S.
Qed.

Lemma defined_app : forall m a n1 n2,
  defined m a n1 -> defined m (a + n1) n2 -> 0 <= n1 -> defined m a (n1 + n2).
Proof.
  intros m a n1 n2 D1 D2 Hn i Hi.
  destruct (Z_lt_le_dec i n1).
  - apply D1. lia.
  - replace (a + i) with (a + n1 + (i - n1)) by lia. apply D2. lia.
Qed.

Lemma defined_mono : forall m a n n', defined m a n -> n' <= n -> defined m a n'.
Proof. intros m a n n' D H i Hi. apply D. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint ndig_f (fuel : nat) (x : Z) : Z :=
  match fuel with
  | O => 1
  | S f => if x <? 10 then 1 else 1 + ndig_f f (x / 10)
  end.
Definition ndig (x : Z) : Z := ndig_f 20 x.

Arguments ndig _ : simpl never.

Lemma ndig_f_ge1 : forall f x, 1 <= ndig_f f x.
Proof. induction f; intros; cbn; [lia|]. destruct (x <? 10); [lia|]. specialize (IHf (x/10)). lia. Qed.

Lemma ndig_f_bound : forall f k x, 1 <= k -> 0 <= x < 10 ^ k -> ndig_f f x <= k.
Proof.
  induction f as [|f IH]; intros k x Hk Hx; cbn [ndig_f]; [lia|].
  destruct (Z.ltb_spec x 10); [lia|].
  assert (Hk2 : 2 <= k).
  { destruct (Z_lt_le_dec k 2); [|lia]. exfalso. assert (k = 1) by lia. subst k. cbn in Hx. lia. }
  assert (Hp : 10 ^ k = 10 * 10 ^ (k - 1)).
  { replace k with (Z.succ (k - 1)) at 1 by lia. rewrite Z.pow_succ_r; lia. }
  assert (0 <= x / 10 < 10 ^ (k - 1)).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. lia. }
  specialize (IH (k - 1) (x / 10) ltac:(lia) H0). lia.
Qed.

Lemma ndig_f_small : forall f x, x < 10 -> ndig_f f x = 1.
Proof. intros f x Hx. destruct f; cbn; [reflexivity|]. destruct (Z.ltb_spec x 10); [reflexivity|lia]. Qed.

Lemma ndig_f_step : forall f x, 10 <= x -> ndig_f (S f) x = 1 + ndig_f f (x / 10).
Proof. intros f x Hx. cbn. destruct (Z.ltb_spec x 10); [lia|reflexivity]. Qed.

(* [comment removed for export] *)
Lemma ndig_f_stable : forall f x, 0 <= x < 10 ^ Z.of_nat f -> forall g, (f <= g)%nat -> ndig_f g x = ndig_f f x.
Proof.
  induction f as [|f IH]; intros x Hx g Hg.
  - cbn in Hx. rewrite !ndig_f_small by lia. reflexivity.
  - destruct g as [|g]; [lia|].
    destruct (Z_lt_le_dec x 10).
    + rewrite !ndig_f_small by lia. reflexivity.
    + rewrite !ndig_f_step by lia. f_equal. apply IH; [|lia].
      assert (Hp : 10 ^ Z.of_nat (S f) = 10 * 10 ^ Z.of_nat f).
      { replace (Z.of_nat (S f)) with (Z.succ (Z.of_nat f)) by lia. rewrite Z.pow_succ_r; lia. }
      split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
Qed.

Lemma ndig_range : forall x, 0 <= x < 2 ^ 64 -> 1 <= ndig x <= 20.
Proof.
  intros x Hx. unfold ndig. split; [apply ndig_f_ge1|].
  apply ndig_f_bound; [lia|]. cbn. lia.
Qed.

Lemma ndig_small : forall x, x < 10 -> ndig x = 1.
Proof. intros. apply ndig_f_small. assumption. Qed.

Lemma ndig_step : forall x, 10 <= x < 2 ^ 64 -> ndig x = 1 + ndig (x / 10).
Proof.
  intros x Hx. unfold ndig. rewrite (ndig_f_step 19) by lia.
  cut (ndig_f 20 (x/10) = ndig_f 19 (x/10)); [intros ->; reflexivity|].
  apply (ndig_f_stable 19 (x/10)); [|lia].
  split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. cbn. lia.
Qed.

Lemma ndig_ge2 : forall x, 10 <= x < 2 ^ 64 -> 2 <= ndig x.
Proof. intros x Hx. rewrite ndig_step by lia. pose proof (ndig_f_ge1 20 (x/10)). unfold ndig. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive fconv : Type := Cs | Cd | Cu | Czu.
Inductive fitem : Type := FLit (bs : list Z) | FConv (c : fconv).

Definition conv_bytes (c : fconv) : list Z :=
  match c with Cs => [37; 115] | Cd => [37; 100] | Cu => [37; 117] | Czu => [37; 122; 117] end.

(* [comment removed for export] *)
Fixpoint flat (its : list fitem) : list Z :=
  match its with
  | [] => [0]
  | FLit bs :: r => bs ++ flat r
  | FConv c :: r => conv_bytes c ++ flat r
  end.

Definition lit_byte (b : Z) : bool := (1 <=? b) && (b <=? 255) && negb (b =? 37).

(* [comment removed for export] *)
Fixpoint wf_items (its : list fitem) : bool :=
  match its with
  | [] => true
  | FLit bs :: r => negb (Nat.eqb (length bs) 0) && forallb lit_byte bs
                    && match r with FLit _ :: _ => false | _ => true end && wf_items r
  | FConv _ :: r => wf_items r
  end.

(* [comment removed for export] *)
Fixpoint convs (its : list fitem) : list fconv :=
  match its with
  | [] => []
  | FLit _ :: r => convs r
  | FConv c :: r => c :: convs r
  end.
Definition is_s (c : fconv) : bool := match c with Cs => true | _ => false end.
Fixpoint all_int (cs : list fconv) : bool :=
  match cs with [] => true | c :: r => negb (is_s c) && all_int r end.
(* [comment removed for export] *)
Fixpoint class_ok (nS : nat) (cs : list fconv) : bool :=
  match nS, cs with
  | O, _ => all_int cs
  | S n, c :: r => is_s c && class_ok n r
  | S _, [] => false
  end.
Definition fmt_class_ok (nS : nat) (its : list fitem) : bool :=
  wf_items its && class_ok nS (convs its) && (Nat.leb (length (convs its)) 7).

(* [comment removed for export] *)
Fixpoint lit_total (its : list fitem) : Z :=
  match its with
  | [] => 0
  | FLit bs :: r => Z.of_nat (length bs) + lit_total r
  | FConv _ :: r => lit_total r
  end.

(* [comment removed for export] *)
Fixpoint take_lit (bs : list Z) : list Z * list Z :=
  match bs with
  | b :: r => if lit_byte b then let (l, r') := take_lit r in (b :: l, r') else ([], bs)
  | [] => ([], [])
  end.

Definition parse_conv (r : list Z) : option (fconv * list Z) :=
  match r with
  | c :: r' =>
      if c =? 115 then Some (Cs, r')
      else if c =? 100 then Some (Cd, r')
      else if c =? 117 then Some (Cu, r')
      else if c =? 122 then match r' with d :: r'' => if d =? 117 then Some (Czu, r'') else None | [] => None end
      else None
  | [] => None
  end.

Fixpoint fmt_parse_f (fuel : nat) (bs : list Z) : option (list fitem) :=
  match fuel with
  | O => None
  | S f =>
    match bs with
    | [] => None
    | b :: r =>
        if b =? 0 then Some []
        else if b =? 37 then
          match parse_conv r with
          | Some (c, r') => option_map (cons (FConv c)) (fmt_parse_f f r')
          | None => None
          end
        else let (l, r0) := take_lit bs in
             match l with [] => None | _ => option_map (cons (FLit l)) (fmt_parse_f f r0) end
    end
  end.
Definition fmt_parse (bs : list Z) : option (list fitem) := fmt_parse_f (length bs) bs.

Lemma take_lit_spec : forall bs l r, take_lit bs = (l, r) ->
  bs = l ++ r /\ forallb lit_byte l = true /\ match r with b :: _ => lit_byte b = false | [] => True end.
Proof.
  induction bs as [|b bs IH]; intros l r H; cbn in H.
  - inversion H; subst. cbn. repeat split; reflexivity.
  - destruct (lit_byte b) eqn:E.
    + destruct (take_lit bs) as [l' r'] eqn:T. inversion H; subst.
      destruct (IH l' r eq_refl) as (A & B & C). subst bs. cbn. rewrite E, B. repeat split; auto.
    + inversion H; subst. cbn. repeat split; auto.
Qed.

Lemma parse_conv_spec : forall r c r', parse_conv r = Some (c, r') -> 37 :: r = conv_bytes c ++ r'.
Proof.
  intros r c r' H. destruct r as [|x r0]; cbn in H; [discriminate|].
  destruct (Z.eqb_spec x 115); [inversion H; subst; reflexivity|].
  destruct (Z.eqb_spec x 100); [inversion H; subst; reflexivity|].
  destruct (Z.eqb_spec x 117); [inversion H; subst; reflexivity|].
  destruct (Z.eqb_spec x 122); [|discriminate].
  destruct r0 as [|d r1]; [discriminate|].
  destruct (Z.eqb_spec d 117); [inversion H; subst; reflexivity|discriminate].
Qed.

(* [comment removed for export] *)
Lemma fmt_parse_f_sound : forall fuel bs its,
  fmt_parse_f fuel bs = Some its ->
  (exists rest, bs = flat its ++ rest) /\ wf_items its = true.
Proof.
  induction fuel as [|f IH]; intros bs its H; cbn [fmt_parse_f] in H; [discriminate|].
  destruct bs as [|b r]; [discriminate|].
  destruct (Z.eqb_spec b 0) as [->|Hb0].
  { inversion H; subst. split; [exists r; reflexivity | reflexivity]. }
  destruct (Z.eqb_spec b 37) as [->|Hb37].
  { destruct (parse_conv r) as [[c r']|] eqn:PC; [|discriminate].
    destruct (fmt_parse_f f r') as [its'|] eqn:P; [|discriminate]. cbn in H. inversion H; subst.
    destruct (IH _ _ P) as [[rest ->] W].
    split; [|exact W]. exists rest. cbn [flat]. rewrite <- app_assoc, <- (parse_conv_spec _ _ _ PC). reflexivity. }
  destruct (take_lit (b :: r)) as [l r0] eqn:T.
  pose proof (take_lit_spec _ _ _ T) as (A & B & C).
  destruct l as [|b' l']; [discriminate|].
  destruct (fmt_parse_f f r0) as [its'|] eqn:P; [|discriminate]. cbn in H. inversion H; subst.
  destruct (IH _ _ P) as [[rest E] W].
  split.
  - exists rest. rewrite A. cbn [flat]. rewrite E, <- app_assoc. reflexivity.
  - cbn [wf_items length]. rewrite B. cbn [negb Nat.eqb andb].
    rewrite W. destruct its' as [|[bs2|c2] ?]; try reflexivity.
    exfalso. cbn [flat] in E. subst r0.
    cbn [wf_items] in W. destruct bs2 as [|x xs]; [discriminate W|].
    cbn [app] in C. cbn [length Nat.eqb negb andb forallb] in W.
    rewrite C in W. cbn in W. discriminate W.
Qed.

Lemma fmt_parse_sound : forall bs its,
  fmt_parse bs = Some its -> (exists rest, bs = flat its ++ rest) /\ wf_items its = true.
Proof. intros bs its H. exact (fmt_parse_f_sound _ _ _ H). Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma runs_trans2 : forall segs (s0 : machine_state)
    (st1 : bvmap 5 word -> (word -> option byte) -> machine_state)
    (P1 : bvmap 5 word -> (word -> option byte) -> Prop)
    (st2 : bvmap 5 word -> (word -> option byte) -> machine_state)
    (P2 : bvmap 5 word -> (word -> option byte) -> Prop),
  (exists r1 m1, msteps segs s0 (st1 r1 m1) /\ P1 r1 m1) ->
  (forall r1 m1, P1 r1 m1 -> exists r2 m2, msteps segs (st1 r1 m1) (st2 r2 m2) /\ P2 r2 m2) ->
  exists r2 m2, msteps segs s0 (st2 r2 m2) /\ P2 r2 m2.
Proof.
  intros segs s0 st1 P1 st2 P2 (r1 & m1 & R1 & H1) K.
  destruct (K r1 m1 H1) as (r2 & m2 & R2 & H2).
  exists r2, m2. split; [eapply msteps_trans; eassumption | exact H2].
Qed.

(* [comment removed for export] *)
Lemma runs_trans1m : forall segs (s0 : machine_state)
    (st1 : bvmap 5 word -> machine_state)
    (P1 : bvmap 5 word -> Prop)
    (st2 : bvmap 5 word -> (word -> option byte) -> machine_state)
    (P2 : bvmap 5 word -> (word -> option byte) -> Prop),
  (exists r1, msteps segs s0 (st1 r1) /\ P1 r1) ->
  (forall r1, P1 r1 -> exists r2 m2, msteps segs (st1 r1) (st2 r2 m2) /\ P2 r2 m2) ->
  exists r2 m2, msteps segs s0 (st2 r2 m2) /\ P2 r2 m2.
Proof.
  intros segs s0 st1 P1 st2 P2 (r1 & R1 & H1) K.
  destruct (K r1 H1) as (r2 & m2 & R2 & H2).
  exists r2, m2. split; [eapply msteps_trans; eassumption | exact H2].
Qed.

(* [comment removed for export] *)
Lemma frame_mod_wb : forall m m1 rs (a : word) bs,
  frame_mod m m1 rs ->
  (forall x : word, in_rng x a (Z.of_nat (length bs)) -> ~ outside x rs) ->
  bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64 ->
  frame_mod m (wbytes m1 a bs) rs.
Proof.
  intros m m1 rs a bs [E G] Hin Hnw. split.
  - intros x Hx. rewrite wbytes_outside; [apply E, Hx| |exact Hnw].
    intros Hr. exact (Hin x Hr Hx).
  - eapply mem_grows_trans; [exact G | apply wbytes_grows].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation MAGIC10 := 14757395258967641293%Z (only parsing).

Lemma magic10_div : forall x, 0 <= x < 2^64 -> x * MAGIC10 / 2^64 / 8 = x / 10.
Proof.
  intros x Hx.
  rewrite Z.div_div by lia.
  change (2^64 * 8) with (2^67).
  pose proof (Z.div_mod x 10 ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound x 10 ltac:(lia)) as Hmb.
  set (q := x / 10) in *. set (r := x mod 10) in *.
  assert (Hq : 0 <= q <= 1844674407370955161).
  { subst q. split; [apply Z.div_pos; lia|].
    change 1844674407370955161 with (18446744073709551615 / 10). apply Z.div_le_mono; lia. }
  assert (Hxm : x * 14757395258967641293 = 2^67 * q + (2 * q + r * 14757395258967641293)).
  { rewrite Hdm. change (2^67) with 147573952589676412928. lia. }
  symmetry. apply (Z.div_unique_pos _ _ q (2 * q + r * 14757395258967641293)).
  - change (2^67) with 147573952589676412928. lia.
  - exact Hxm.
Qed.

(* [comment removed for export] *)
Lemma fmtu_q : forall x, 0 <= x < 2^64 ->
  v_srli (v_mulhu (Z_to_bv 64 x) (Z_to_bv 64 MAGIC10)) 3 = Z_to_bv 64 (x / 10).
Proof.
  intros x Hx. unfold v_srli, v_mulhu. rewrite !Z.shiftr_div_pow2 by lia.
  rewrite (u_Z2bv x) by lia.
  replace (bv_unsigned (Z_to_bv 64 MAGIC10)) with MAGIC10 by reflexivity.
  assert (Hm : 0 <= x * MAGIC10 / 2^64 < 2^64).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia. }
  rewrite u_Z2bv by lia. f_equal. change (2^3) with 8. apply magic10_div. lia.
Qed.

Lemma lor48_digit : forall d, 0 <= d < 10 -> Z.lor d 48 = 48 + d.
Proof.
  intros d Hd.
  assert (H : d = 0 \/ d = 1 \/ d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6 \/ d = 7 \/ d = 8 \/ d = 9) by lia.
  repeat (destruct H as [H0 | H]; [subst; reflexivity|]). subst; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma fmtu_r : forall x, 0 <= x < 2^64 ->
  v_ori (v_subw (Z_to_bv 64 x) (v_mul (Z_to_bv 64 (x / 10)) (Z_to_bv 64 10))) 48 = Z_to_bv 64 (48 + x mod 10).
Proof.
  intros x Hx. unfold v_ori, v_subw, v_mul.
  pose proof (Z.div_mod x 10 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound x 10 ltac:(lia)) as Hmb.
  assert (Hq : 0 <= x / 10 < 2^64) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite (u_Z2bv (x / 10)) by lia.
  replace (bv_unsigned (Z_to_bv 64 10)) with 10 by reflexivity.
  rewrite (u_Z2bv x) by lia. rewrite (u_Z2bv (x / 10 * 10)) by lia.
  replace (x - x / 10 * 10) with (x mod 10) by lia.
  replace (bv_swrap 32 (x mod 10)) with (x mod 10).
  2:{ symmetry. apply bv_swrap_small. change (bv_half_modulus 32) with 2147483648. lia. }
  rewrite u_Z2bv by lia. f_equal. change (bv_wrap 64 48) with 48. apply lor48_digit. lia.
Qed.

Lemma v_ori48 : forall y, 0 <= y < 10 -> v_ori (Z_to_bv 64 y) 48 = Z_to_bv 64 (48 + y).
Proof.
  intros y Hy. unfold v_ori. rewrite u_Z2bv by lia. f_equal. change (bv_wrap 64 48) with 48.
  apply lor48_digit. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma swrap32_id : forall z, - 2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof. intros z Hz. apply bv_swrap_small. change (bv_half_modulus 32) with (2^31). lia. Qed.

Lemma v_subw_Z : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> - 2^31 <= a - b < 2^31 ->
  v_subw (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof. intros a b Ha Hb Hd. unfold v_subw. rewrite !u_Z2bv by lia. rewrite swrap32_id by lia. reflexivity. Qed.

Lemma v_addw_Z : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> - 2^31 <= a + b < 2^31 ->
  v_addw (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof. intros a b Ha Hb Hd. unfold v_addw. rewrite !u_Z2bv by lia. rewrite swrap32_id by lia. reflexivity. Qed.

Lemma v_addiw_Z : forall a i, 0 <= a < 2^64 -> - 2^31 <= a + i < 2^31 ->
  v_addiw (Z_to_bv 64 a) i = Z_to_bv 64 (a + i).
Proof. intros a i Ha Hd. unfold v_addiw. rewrite !u_Z2bv by lia. rewrite swrap32_id by lia. reflexivity. Qed.

Lemma c_lts_Z : forall a b, 0 <= a < 2^63 -> 0 <= b < 2^63 ->
  c_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof.
  intros a b Ha Hb. rewrite c_lts_small by (rewrite u_Z2bv by lia; lia).
  unfold bv_ltu. rewrite !u_Z2bv by lia. reflexivity.
Qed.

Lemma c_ltu_Z : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 ->
  c_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros. unfold c_ltu, bv_ltu. rewrite !u_Z2bv by lia. reflexivity. Qed.

Lemma c_eq_Z : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 ->
  c_eq (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof. intros a b Ha Hb. unfold c_eq, bv_eqb. rewrite !u_Z2bv by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma u8_of_Z : forall b, 0 <= b < 256 -> bv_unsigned (Z_to_bv 8 b) = b.
Proof. intros b Hb. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rdn_of_bytes : forall segs m (k : nat) (a : Z) (g : Z -> byte),
  0 <= a -> a + Z.of_nat k <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat k -> rdn segs m (Z_to_bv 64 (a + i)) 1 = Some [g (a + i)]) ->
  rdn segs m (Z_to_bv 64 a) k = Some (map (fun i => g (a + Z.of_nat i)) (seq 0 k)).
Proof.
  intros segs m k. induction k as [|k IH]; intros a g Ha Hk Hb.
  - reflexivity.
  - cbn [rdn seq map]. rewrite Z.add_0_r.
    pose proof (Hb 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. cbn [rdn] in H0.
    destruct (match m (Z_to_bv 64 a) with Some b => Some b | None => seg_rom segs (Z_to_bv 64 a) end) as [b|];
      [|discriminate H0].
    injection H0 as ->.
    replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)).
    2:{ apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
        assert (H1 : bv_unsigned (1 : word) = 1) by reflexivity. rewrite H1.
        unfold bv_wrap. rewrite Zplus_mod_idemp_l. reflexivity. }
    rewrite (IH (a + 1) g ltac:(lia) ltac:(lia)).
    + rewrite <- seq_shift, map_map. f_equal. f_equal. apply map_ext. intros i. f_equal. lia.
    + intros i Hi. replace (a + 1 + i) with (a + (1 + i)) by lia. apply Hb. lia.
Qed.

Lemma rdn_of_bytes_len : forall k a (g : Z -> byte), length (map (fun i => g (a + Z.of_nat i)) (seq 0 k)) = k.
Proof. intros. rewrite length_map, length_seq. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition conv_c1 (c : fconv) : Z := match c with Cs => 115 | Cd => 100 | Cu => 117 | Czu => 122 end.
Definition conv_type (c : fconv) : Z := match c with Cs => 9 | Cd => 10 | Cu => 11 | Czu => 20 end.   (* [comment removed for export] *)
Definition conv_ps (c : fconv) : Z := match c with Czu => 6 | _ => 0 end.                            (* [comment removed for export] *)
Definition conv_len (c : fconv) : Z := match c with Czu => 3 | _ => 2 end.                           (* [comment removed for export] *)
Definition conv_last (c : fconv) : Z := match c with Cs => 115 | Cd => 100 | Cu => 117 | Czu => 117 end. (* [comment removed for export] *)

Lemma conv_bytes_len : forall c, Z.of_nat (length (conv_bytes c)) = conv_len c.
Proof. destruct c; reflexivity. Qed.
