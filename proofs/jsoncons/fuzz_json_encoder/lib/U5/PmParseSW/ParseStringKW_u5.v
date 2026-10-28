(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5 PmEncSpecs_u5 PmLibSpecsX_u5 PmLibSpecsW_u5 PmRef_u5 PmRefFacts_u5 PmRefFacts2_u5.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PSKW.
Import PML PMES PMR.
Abbreviation mem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition xstep (c : ctrl) (b : Z) : option (ctrl * list Z) :=
  let s := c_sst c in
  if s =? SS_TEXT then
    if is_ctl b then None
    else if (b =? 10) || (b =? 13) || (b =? 9) then None
    else if b =? 92 then Some (set_sst c SS_ESC, [])
    else if b =? 34 then None
    else Some (tok1 c b, [b])
  else if s =? SS_ESC then
    if (b =? 34) || (b =? 92) || (b =? 47) then Some (set_sst (tok1 c b) SS_TEXT, [b])
    else if b =? 98 then Some (set_sst (tok1 c 8) SS_TEXT, [8])
    else if b =? 102 then Some (set_sst (tok1 c 12) SS_TEXT, [12])
    else if b =? 110 then Some (set_sst (tok1 c 10) SS_TEXT, [10])
    else if b =? 114 then Some (set_sst (tok1 c 13) SS_TEXT, [13])
    else if b =? 116 then Some (set_sst (tok1 c 9) SS_TEXT, [9])
    else if b =? 117 then Some (set_sst (set_cp c 0) SS_U1, [])
    else None
  else if s =? SS_U1 then match hexval b with Some v => Some (set_sst (set_cp c v) SS_U2, []) | None => None end
  else if s =? SS_U2 then match hexval b with Some v => Some (set_sst (hexstep c false v) SS_U3, []) | None => None end
  else if s =? SS_U3 then match hexval b with Some v => Some (set_sst (hexstep c false v) SS_U4, []) | None => None end
  else if s =? SS_U4 then
    match hexval b with
    | Some v => let c1 := hexstep c false v in if is_high_surr (c_cp c1) then Some (set_sst c1 SS_SP1, []) else None
    | None => None end
  else if s =? SS_SP1 then (if b =? 92 then Some (set_sst (set_cp2 c 0) SS_SP2, []) else None)
  else if s =? SS_SP2 then (if b =? 117 then Some (set_sst c SS_U5, []) else None)
  else if s =? SS_U5 then match hexval b with Some v => Some (set_sst (set_cp2 c v) SS_U6, []) | None => None end
  else if s =? SS_U6 then match hexval b with Some v => Some (set_sst (hexstep c true v) SS_U7, []) | None => None end
  else if s =? SS_U7 then match hexval b with Some v => Some (set_sst (hexstep c true v) SS_U8, []) | None => None end
  else if s =? SS_U8 then
    match hexval b with
    | Some v => let c1 := hexstep c true v in let u := utf8_of (pair_cp (c_cp c1) (c_cp2 c1)) in Some (set_sst (tokn c1 u) SS_TEXT, u)
    | None => None end
  else None.
(* [comment removed for export] *)
Definition xfin (c : ctrl) (b : Z) (r : list Z) : res :=
  let s := c_sst c in let w := b :: r in
  if s =? SS_TEXT then
    if is_ctl b then err (set_sst c SS_TEXT) w E_ILLEGAL_CTL
    else if (b =? 10) || (b =? 13) || (b =? 9) then err c w E_CHAR_IN_STRING
    else end_string c w
  else if s =? SS_ESC then err (set_sst c SS_ESC) w E_ILLEGAL_ESC
  else if s =? SS_U1 then err c w E_INVALID_UESC
  else if s =? SS_U2 then err c w E_INVALID_UESC
  else if s =? SS_U3 then err c w E_INVALID_UESC
  else if s =? SS_U4 then
    match hexval b with
    | Some v => let c1 := hexstep c false v in ret (set_sst (tokn c1 (utf8_of (c_cp c1))) SS_TEXT) r
    | None => err c w E_INVALID_UESC end
  else if s =? SS_SP1 then err c w E_SURR_PAIR
  else if s =? SS_SP2 then err c w E_SURR_PAIR
  else if s =? SS_U5 then err c w E_INVALID_UESC
  else if s =? SS_U6 then err c w E_INVALID_UESC
  else if s =? SS_U7 then err c w E_INVALID_UESC
  else if s =? SS_U8 then err c w E_INVALID_UESC
  else err c w E_STUCK.
Lemma parse_string_cons : forall c b r,
  parse_string c (b :: r) = match xstep c b with Some (c', _) => parse_string c' r | None => xfin c b r end.
Proof.
  intros c b r. cbn [parse_string]. unfold xstep, xfin.
  destruct (c_sst c =? SS_TEXT).
  { destruct (is_ctl b); [reflexivity|]. destruct ((b =? 10) || (b =? 13) || (b =? 9))%bool; [reflexivity|]. destruct (b =? 92); [reflexivity|]. destruct (b =? 34); reflexivity. }
  destruct (c_sst c =? SS_ESC).
  { destruct ((b =? 34) || (b =? 92) || (b =? 47))%bool; [reflexivity|]. destruct (b =? 98); [reflexivity|]. destruct (b =? 102); [reflexivity|]. destruct (b =? 110); [reflexivity|].
    destruct (b =? 114); [reflexivity|]. destruct (b =? 116); [reflexivity|]. destruct (b =? 117); reflexivity. }
  destruct (c_sst c =? SS_U1) eqn:E1; [destruct (hexval b); reflexivity|].
  destruct (c_sst c =? SS_U2) eqn:E2; [destruct (hexval b); reflexivity|].
  destruct (c_sst c =? SS_U3) eqn:E3; [destruct (hexval b); reflexivity|].
  destruct (c_sst c =? SS_U4) eqn:E4; [destruct (hexval b); [|reflexivity]; destruct (is_high_surr _); reflexivity|].
  destruct (c_sst c =? SS_SP1) eqn:E5; [destruct (b =? 92); reflexivity|].
  destruct (c_sst c =? SS_SP2) eqn:E6; [destruct (b =? 117); reflexivity|].
  destruct (c_sst c =? SS_U5) eqn:E7; [destruct (hexval b); reflexivity|].
  destruct (c_sst c =? SS_U6) eqn:E8; [destruct (hexval b); reflexivity|].
  destruct (c_sst c =? SS_U7) eqn:E9; [destruct (hexval b); reflexivity|].
  destruct (c_sst c =? SS_U8) eqn:E10; [destruct (hexval b); reflexivity|]. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint xrun (c : ctrl) (bs : list Z) : option (ctrl * list Z) :=
  match bs with
  | [] => Some (c, [])
  | b :: r => match xstep c b with
              | Some (c1, o1) => match xrun c1 r with Some (c2, o2) => Some (c2, o1 ++ o2) | None => None end
              | None => None
              end
  end.
Lemma xrun_app : forall u v c, xrun c (u ++ v) = match xrun c u with Some (c1, o1) => match xrun c1 v with Some (c2, o2) => Some (c2, o1 ++ o2) | None => None end | None => None end.
Proof.
  induction u as [|b u IH]; intros v c; cbn [xrun app].
  - destruct (xrun c v) as [[c2 o2]|]; reflexivity.
  - destruct (xstep c b) as [[c1 o1]|]; [|reflexivity]. rewrite IH. destruct (xrun c1 u) as [[c2 o2]|]; [|reflexivity]. destruct (xrun c2 v) as [[c3 o3]|]; [|reflexivity].
    rewrite app_assoc. reflexivity.
Qed.
Lemma xrun_snoc : forall c u b c1 o1 c2 o2, xrun c u = Some (c1, o1) -> xstep c1 b = Some (c2, o2) -> xrun c (u ++ [b]) = Some (c2, o1 ++ o2).
Proof. intros c u b c1 o1 c2 o2 H1 H2. rewrite xrun_app, H1. cbn [xrun]. rewrite H2, app_nil_r. reflexivity. Qed.
Lemma firstn_succ : forall (l : list Z) n, (n < length l)%nat -> firstn (S n) l = firstn n l ++ [nth n l 0].
Proof. induction l as [|x l IH]; intros n Hn; [cbn in Hn; lia|]. destruct n as [|n]; [reflexivity|]. cbn [firstn nth app]. rewrite IH by (cbn in Hn; lia). reflexivity. Qed.
Lemma skipn_nth_cons : forall (n : nat) (w : list Z), (n < length w)%nat -> skipn n w = nth n w 0 :: skipn (S n) w.
Proof. induction n as [|n IH]; intros [|b r] H; cbn in H |- *; try lia; [reflexivity|]. apply IH. lia. Qed.
(* [comment removed for export] *)
Lemma xrun_parse : forall bs c r c1 o1, xrun c bs = Some (c1, o1) -> parse_string c (bs ++ r) = parse_string c1 r.
Proof.
  induction bs as [|b bs IH]; intros c r c1 o1 H; cbn [xrun app] in H |- *.
  - injection H as <- <-. reflexivity.
  - rewrite parse_string_cons. destruct (xstep c b) as [[c' o']|] eqn:Hs; [|discriminate H]. destruct (xrun c' bs) as [[c2 o2]|] eqn:Hr; [|discriminate H].
    injection H as <- <-. exact (IH _ _ _ _ Hr).
Qed.
(* [comment removed for export] *)
Definition core_eq (c1 c2 : ctrl) : Prop := c_st c1 = c_st c2 /\ c_more c1 = c_more c2 /\ c_done c1 = c_done c2 /\ c_level c1 = c_level c2 /\ c_stack c1 = c_stack c2 /\ c_nst c1 = c_nst c2.
Definition tok_ok (c : ctrl) (buf : list Z) : Prop := c_dlen c = Z.of_nat (length buf) /\ c_u8 c = u8_feeds u8_init buf.
Lemma u8_feeds_app : forall v l1 l2, u8_feeds v (l1 ++ l2) = u8_feeds (u8_feeds v l1) l2.
Proof. intros v l1; revert v; induction l1 as [|b r IH]; intros v l2; [reflexivity|]. cbn. apply IH. Qed.
Lemma tokn_tok : forall c buf u, tok_ok c buf -> tok_ok (tokn c u) (buf ++ u).
Proof. intros c buf u [H1 H2]. unfold tok_ok, tokn, set_tok. cbn. rewrite length_app, Nat2Z.inj_add, H1, H2, u8_feeds_app. split; reflexivity. Qed.
Lemma tok1_tok : forall c buf b, tok_ok c buf -> tok_ok (tok1 c b) (buf ++ [b]).
Proof. intros c buf b [H1 H2]. unfold tok_ok, tok1, set_tok. cbn. rewrite length_app, Nat2Z.inj_add, H1, H2, u8_feeds_app. cbn. split; [lia | reflexivity]. Qed.
Ltac xinv_fin H T2 :=
  injection H as <- <-; split;
  [ unfold core_eq; cbn; repeat split; reflexivity
  | intros [T1 T2]; unfold tok_ok; cbn -[u8_feeds u8_feed utf8_of pair_cp hexval is_high_surr Z.modulo Z.pow Z.mul Z.add Z.of_nat length app] in *;
    rewrite ?app_nil_r, ?length_app, ?Nat2Z.inj_add, ?u8_feeds_app, <- ?T2; cbn [length u8_feeds Z.of_nat Pos.of_succ_nat Pos.succ]; split; [lia | reflexivity] ].
Lemma xstep_inv : forall c b c1 o1 buf, xstep c b = Some (c1, o1) -> core_eq c c1 /\ (tok_ok c buf -> tok_ok c1 (buf ++ o1)).
Proof.
  intros c b c1 o1 buf H. unfold xstep, hexstep in H. destruct c as [st sst nst more done lvl stk cp cp2 dlen u8v]. cbn [c_sst c_cp c_cp2 set_cp set_cp2 set_sst] in H.
  destruct (sst =? SS_TEXT).
  { destruct (is_ctl b); [discriminate H|]. destruct ((b =? 10) || (b =? 13) || (b =? 9))%bool; [discriminate H|].
    destruct (b =? 92); [xinv_fin H T2|]. destruct (b =? 34); [discriminate H|]. xinv_fin H T2. }
  destruct (sst =? SS_ESC).
  { destruct ((b =? 34) || (b =? 92) || (b =? 47))%bool; [xinv_fin H T2|].
    do 6 (match type of H with (if ?x then _ else _) = _ => destruct x; [xinv_fin H T2|] end). discriminate H. }
  destruct (sst =? SS_U1); [destruct (hexval b); [xinv_fin H T2 | discriminate H]|].
  destruct (sst =? SS_U2); [destruct (hexval b); [xinv_fin H T2 | discriminate H]|].
  destruct (sst =? SS_U3); [destruct (hexval b); [xinv_fin H T2 | discriminate H]|].
  destruct (sst =? SS_U4); [destruct (hexval b); [destruct (is_high_surr _); [xinv_fin H T2 | discriminate H] | discriminate H]|].
  destruct (sst =? SS_SP1); [destruct (b =? 92); [xinv_fin H T2 | discriminate H]|].
  destruct (sst =? SS_SP2); [destruct (b =? 117); [xinv_fin H T2 | discriminate H]|].
  destruct (sst =? SS_U5); [destruct (hexval b); [xinv_fin H T2 | discriminate H]|].
  destruct (sst =? SS_U6); [destruct (hexval b); [xinv_fin H T2 | discriminate H]|].
  destruct (sst =? SS_U7); [destruct (hexval b); [xinv_fin H T2 | discriminate H]|].
  destruct (sst =? SS_U8); [|discriminate H]. destruct (hexval b); [|discriminate H]. xinv_fin H T2.
Qed.
Lemma core_eq_trans : forall a b c, core_eq a b -> core_eq b c -> core_eq a c.
Proof. intros a b c (A1 & A2 & A3 & A4 & A5 & A6) (B1 & B2 & B3 & B4 & B5 & B6). unfold core_eq. repeat split; congruence. Qed.
Lemma xrun_inv : forall bs c c1 o1 buf, xrun c bs = Some (c1, o1) -> core_eq c c1 /\ (tok_ok c buf -> tok_ok c1 (buf ++ o1)).
Proof.
  induction bs as [|b bs IH]; intros c c1 o1 buf H; cbn [xrun] in H.
  - injection H as <- <-. rewrite app_nil_r. split; [unfold core_eq; repeat split; reflexivity | intros T; exact T].
  - destruct (xstep c b) as [[c' o']|] eqn:Hs; [|discriminate H]. destruct (xrun c' bs) as [[c2 o2]|] eqn:Hr; [|discriminate H]. injection H as <- <-.
    destruct (xstep_inv c b c' o' buf Hs) as [C1 T1]. destruct (IH c' c2 o2 (buf ++ o') Hr) as [C2 T2].
    split; [exact (core_eq_trans _ _ _ C1 C2) | intros T; rewrite app_assoc; exact (T2 (T1 T))].
Qed.
(* [comment removed for export] *)
Definition inb (b : Z) : Prop := 0 <= b <= 255.
Lemma utf8_of_inb : forall cp, 0 <= cp -> Forall inb (utf8_of cp).
Proof.
  intros cp Hcp. unfold utf8_of.
  assert (L63 : forall x, 0 <= Z.land x 63 <= 63).
  { intros x. change 63 with (Z.ones 6). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound x (2 ^ 6) ltac:(lia)). change (Z.ones 6) with 63. lia. }
  assert (SH : forall x k hi, 0 <= x -> 0 < k -> x < hi * 2 ^ k -> 0 <= Z.shiftr x k < hi).
  { intros x k hi Hx Hk Hhi. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  destruct (is_surr cp); [constructor|].
  destruct (Z.ltb_spec cp 128) as [H1|H1]; [constructor; [unfold inb; lia | constructor]|].
  destruct (Z.ltb_spec cp 2048) as [H2|H2].
  { pose proof (SH cp 6 32 ltac:(lia) ltac:(lia) ltac:(lia)). pose proof (L63 cp). constructor; [unfold inb; lia|]. constructor; [unfold inb; lia | constructor]. }
  destruct (Z.ltb_spec cp 65536) as [H3|H3].
  { pose proof (SH cp 12 16 ltac:(lia) ltac:(lia) ltac:(lia)). pose proof (L63 (Z.shiftr cp 6)). pose proof (L63 cp).
    constructor; [unfold inb; lia|]. constructor; [unfold inb; lia|]. constructor; [unfold inb; lia | constructor]. }
  destruct (Z.leb_spec cp 1114111) as [H4|H4].
  { pose proof (SH cp 18 5 ltac:(lia) ltac:(lia) ltac:(lia)). pose proof (L63 (Z.shiftr cp 12)). pose proof (L63 (Z.shiftr cp 6)). pose proof (L63 cp).
    constructor; [unfold inb; lia|]. constructor; [unfold inb; lia|]. constructor; [unfold inb; lia|]. constructor; [unfold inb; lia | constructor]. }
  constructor; [unfold inb; lia|]. constructor; [unfold inb; lia|]. constructor; [unfold inb; lia | constructor].
Qed.
Lemma pair_cp_nonneg : forall a b, 0 <= pair_cp a b.
Proof. intros a b. unfold pair_cp. pose proof (proj2 (Z.land_nonneg a 1023) ltac:(right; lia)). pose proof (proj2 (Z.land_nonneg b 1023) ltac:(right; lia)). rewrite Z.shiftl_mul_pow2 by lia. nia. Qed.
Lemma hexstep_cp_nonneg : forall c v, 0 <= c_cp (hexstep c false v) < 2 ^ 32.
Proof. intros c v. unfold hexstep. cbn. apply Z.mod_pos_bound. lia. Qed.
Lemma xstep_inb : forall c b c1 o1, inb b -> xstep c b = Some (c1, o1) -> Forall inb o1.
Proof.
  intros c b c1 o1 Hb H. unfold xstep in H.
  destruct (c_sst c =? SS_TEXT).
  { destruct (is_ctl b); [discriminate H|]. destruct ((b =? 10) || (b =? 13) || (b =? 9))%bool; [discriminate H|]. destruct (b =? 92); [injection H as <- <-; constructor|].
    destruct (b =? 34); [discriminate H|]. injection H as <- <-. constructor; [exact Hb | constructor]. }
  destruct (c_sst c =? SS_ESC).
  { destruct ((b =? 34) || (b =? 92) || (b =? 47))%bool; [injection H as <- <-; constructor; [exact Hb | constructor]|].
    do 5 (match type of H with (if ?x then _ else _) = _ => destruct x; [injection H as <- <-; constructor; [unfold inb; lia | constructor]|] end).
    destruct (b =? 117); [injection H as <- <-; constructor | discriminate H]. }
  destruct (c_sst c =? SS_U1); [destruct (hexval b); [injection H as <- <-; constructor | discriminate H]|].
  destruct (c_sst c =? SS_U2); [destruct (hexval b); [injection H as <- <-; constructor | discriminate H]|].
  destruct (c_sst c =? SS_U3); [destruct (hexval b); [injection H as <- <-; constructor | discriminate H]|].
  destruct (c_sst c =? SS_U4); [destruct (hexval b); [destruct (is_high_surr _); [injection H as <- <-; constructor | discriminate H] | discriminate H]|].
  destruct (c_sst c =? SS_SP1); [destruct (b =? 92); [injection H as <- <-; constructor | discriminate H]|].
  destruct (c_sst c =? SS_SP2); [destruct (b =? 117); [injection H as <- <-; constructor | discriminate H]|].
  destruct (c_sst c =? SS_U5); [destruct (hexval b); [injection H as <- <-; constructor | discriminate H]|].
  destruct (c_sst c =? SS_U6); [destruct (hexval b); [injection H as <- <-; constructor | discriminate H]|].
  destruct (c_sst c =? SS_U7); [destruct (hexval b); [injection H as <- <-; constructor | discriminate H]|].
  destruct (c_sst c =? SS_U8); [|discriminate H]. destruct (hexval b); [|discriminate H]. injection H as <- <-. apply utf8_of_inb.
  apply pair_cp_nonneg.
Qed.

Lemma xrun_inb : forall bs c c1 o1, Forall inb bs -> xrun c bs = Some (c1, o1) -> Forall inb o1.
Proof.
  induction bs as [|b bs IH]; intros c c1 o1 HF H; cbn [xrun] in H.
  - injection H as <- <-. constructor.
  - inversion HF; subst. destruct (xstep c b) as [[c' o']|] eqn:Hs; [|discriminate H]. destruct (xrun c' bs) as [[c2 o2]|] eqn:Hr; [|discriminate H].
    injection H as <- <-. apply Forall_app. split; [exact (xstep_inb c b c' o' ltac:(assumption) Hs) | exact (IH c' c2 o2 ltac:(assumption) Hr)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition plain (b : Z) : bool := negb (is_ctl b) && negb ((b =? 10) || (b =? 13) || (b =? 9)) && negb (b =? 92) && negb (b =? 34).
Lemma xstep_plain : forall c b, c_sst c = SS_TEXT -> plain b = true -> xstep c b = Some (tok1 c b, [b]).
Proof.
  intros c b Hs Hp. unfold plain in Hp. apply andb_prop in Hp as [Hp H4]. apply andb_prop in Hp as [Hp H3]. apply andb_prop in Hp as [H1 H2].
  unfold xstep. rewrite Hs. cbn [Z.eqb SS_TEXT]. destruct (is_ctl b); [discriminate H1|]. destruct ((b =? 10) || (b =? 13) || (b =? 9))%bool; [discriminate H2|].
  destruct (b =? 92); [discriminate H3|]. destruct (b =? 34); [discriminate H4|]. reflexivity.
Qed.
Lemma xrun_plain : forall bs c, c_sst c = SS_TEXT -> forallb plain bs = true -> xrun c bs = Some (tokn c bs, bs).
Proof.
  induction bs as [|b bs IH]; intros c Hs Hp.
  - cbn. f_equal. f_equal. unfold tokn, set_tok. cbn. rewrite Z.add_0_r. destruct c; reflexivity.
  - cbn [forallb] in Hp. apply andb_prop in Hp as [H1 H2]. cbn [xrun]. rewrite (xstep_plain c b Hs H1).
    rewrite (IH (tok1 c b) ltac:(unfold tok1, set_tok; cbn; exact Hs) H2). f_equal. f_equal.
    unfold tokn, tok1, set_tok. cbn. f_equal. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma end_string_any : forall c w,
  q_code (end_string c w) = q_code (end_string c []) /\ q_c (end_string c w) = q_c (end_string c []) /\
  q_evs (end_string c w) = q_evs (end_string c []) /\ q_al (end_string c w) = q_al (end_string c []) /\
  (q_code (end_string c w) = 0 -> q_w (end_string c w) = tl w) /\ (q_code (end_string c w) <> 0 -> q_w (end_string c w) = w).
Proof.
  intros c w. unfold end_string. destruct (negb (u8_finish (c_u8 c) =? 0)) eqn:Hu.
  { cbn. repeat split; try reflexivity. intros H0. exfalso. unfold conv_errc in H0. repeat (destruct (_ =? _) in H0; [discriminate H0|]). discriminate H0. }
  destruct (top c =? ST_MEMBER_NAME); [cbn; repeat split; try reflexivity; intros H; exfalso; exact (H eq_refl)|].
  destruct ((top c =? ST_OBJECT) || (top c =? ST_ARRAY))%bool; [cbn; repeat split; try reflexivity; intros H; exfalso; exact (H eq_refl)|].
  destruct (top c =? ST_ROOT); [cbn; repeat split; try reflexivity; intros H; exfalso; exact (H eq_refl)|].
  cbn. repeat split; try reflexivity. intros H. discriminate H.
Qed.
Lemma of_text_self : forall c txt, c_dlen c = Z.of_nat (length txt) -> c_u8 c = u8_feeds u8_init (b256 txt) -> of_text c txt = c.
Proof. intros c txt H1 H2. unfold of_text, set_tok. destruct c; cbn in *. subst. reflexivity. Qed.
Lemma b256_id : forall l, Forall inb l -> b256 l = l.
Proof. intros l H. unfold b256. induction H as [|b l Hb _ IH]; [reflexivity|]. cbn [map]. rewrite IH. unfold inb in Hb. rewrite Z.mod_small by lia. reflexivity. Qed.
Lemma b256_app : forall l1 l2, b256 (l1 ++ l2) = b256 l1 ++ b256 l2.
Proof. intros. unfold b256. apply map_app. Qed.
Lemma b256_inb : forall l, Forall inb (b256 l).
Proof. intros l. unfold b256. apply Forall_forall. intros z Hz. apply in_map_iff in Hz as (b & <- & _). unfold inb. pose proof (Z.mod_pos_bound b 256). lia. Qed.
Lemma b256_idem : forall l, b256 (b256 l) = b256 l.
Proof. intros l. apply b256_id. apply b256_inb. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition w3s (cw : ctrl) (ww : list Z) (M' : mem) (P : Z) (ps ps' : pstate) (eg eg' : eghost) (code : Z) : Prop :=
  let rr := r_of ww (parse_string cw ww) in
  code = PMW.r_code rr /\
  g_es eg' = PMW.es_run (g_es eg) (PMW.r_evs rr) /\
  (exists pay, 0 <= pay <= PMW.r_allow rr /\ g_len eg' = g_len eg + PMW.ind_run (g_es eg) (PMW.r_evs rr) + pay) /\
  (code = 0 -> rm_match (PMW.r_ctrl rr) M' P ps' /\ PMW.r_used rr = winlen ps - winlen ps' /\ PMW.win_bytes M' ps' (PMW.w_after the_rm rr ww)).
Lemma w3s_fold : forall cw ww x M' P ps ps' eg eg' code,
  w3s cw ww M' P ps ps' eg eg' code ->
  let rr := PMW.rm_step the_rm PMW.FParseString cw (PMW.inp_win ps ww x) in
  code = PMW.r_code rr /\ g_es eg' = PMW.es_run (g_es eg) (PMW.r_evs rr) /\
  (exists pay, 0 <= pay <= PMW.r_allow rr /\ g_len eg' = g_len eg + PMW.ind_run (g_es eg) (PMW.r_evs rr) + pay) /\
  (code = 0 -> PMW.rm_match the_rm (PMW.r_ctrl rr) M' P ps' /\ PMW.r_used rr = winlen ps - winlen ps' /\ PMW.win_bytes M' ps' (PMW.w_after the_rm rr ww)).
Proof. intros. exact H. Qed.
(* [comment removed for export] *)
Lemma rm_match_string : forall c (M' : mem) P ps',
  rm_core c ps' -> ps_st ps' = ST_STRING -> c_sst c = ps_sst ps' -> tok_ok c (b256 (ps_buf ps')) ->
  (3 <= c_sst c <= 11 -> u32 M' (P + 148) (c_cp c)) -> (9 <= c_sst c <= 11 -> u32 M' (P + 152) (c_cp2 c)) ->
  (exists t, u8 M' (P + 220) t /\ 0 <= t <= 1) ->
  rm_match c M' P ps'.
Proof.
  intros c M' P ps' HC Hst Hs [T1 T2] Hcp Hcp2 Ht. split; [exact HC|]. split.
  - intros _. split; [exact Hs|]. split; [rewrite T1; unfold b256; rewrite length_map; reflexivity|]. split; [exact T2|]. split; [exact Hcp|]. split; [exact Hcp2 | exact Ht].
  - intros HN. exfalso. rewrite Hst in HN. discriminate HN.
Qed.
(* [comment removed for export] *)
Lemma w3_exh : forall cw c1 o1 ww (M' : mem) P ps ps' eg e,
  xrun cw ww = Some (c1, o1) ->
  rm_core c1 ps' -> ps_st ps' = ST_STRING -> c_sst c1 = ps_sst ps' -> tok_ok c1 (b256 (ps_buf ps')) ->
  (3 <= c_sst c1 <= 11 -> u32 M' (P + 148) (c_cp c1)) -> (9 <= c_sst c1 <= 11 -> u32 M' (P + 152) (c_cp2 c1)) ->
  (exists t, u8 M' (P + 220) t /\ 0 <= t <= 1) ->
  winlen ps = Z.of_nat (length ww) -> ps_win ps' = Some (e, e) ->
  w3s cw ww M' P ps ps' eg eg 0.
Proof.
  intros cw c1 o1 ww M' P ps ps' eg e HX HC Hst Hs HT Hcp Hcp2 Ht HW Hw'.
  assert (Hps : parse_string cw ww = ret c1 []) by (rewrite <- (app_nil_r ww) at 1; rewrite (xrun_parse ww cw [] c1 o1 HX); reflexivity).
  unfold w3s. rewrite Hps.
  unfold PMW.w_after. cbn [r_of ret PMW.r_code PMW.r_evs PMW.r_ctrl PMW.r_used PMW.r_allow q_c q_w q_evs q_code q_al length Z.of_nat PMW.es_run PMW.ind_run].
  rewrite Z.sub_0_r, Nat2Z.id, PMRF2.skipn_all.
  split; [reflexivity|]. split; [reflexivity|]. split; [exists 0; lia|]. intros _.
  split; [exact (rm_match_string c1 M' P ps' HC Hst Hs HT Hcp Hcp2 Ht)|].
  split; [unfold winlen at 2; rewrite Hw'; lia|]. unfold PMW.win_bytes. rewrite Hw'. split; [intros i Hi; cbn in Hi; lia|]. split; [cbn; lia | constructor].
Qed.
(* [comment removed for export] *)
Lemma parse_at : forall cw ww n c0 o0, (n < length ww)%nat -> xrun cw (firstn n ww) = Some (c0, o0) ->
  parse_string cw ww = match xstep c0 (nth n ww 0) with Some (c', _) => parse_string c' (skipn (S n) ww) | None => xfin c0 (nth n ww 0) (skipn (S n) ww) end.
Proof.
  intros cw ww n c0 o0 Hn HX. rewrite <- (firstn_skipn n ww) at 1. rewrite (xrun_parse _ cw _ c0 o0 HX). rewrite (skipn_nth_cons n ww Hn). apply parse_string_cons.
Qed.
(* [comment removed for export] *)
Lemma w3_ret : forall cw n ww c0 o0 c1 (M' : mem) P ps ps' eg p e,
  (n < length ww)%nat -> xrun cw (firstn n ww) = Some (c0, o0) -> xstep c0 (nth n ww 0) = None -> xfin c0 (nth n ww 0) (skipn (S n) ww) = ret c1 (skipn (S n) ww) ->
  rm_core c1 ps' -> ps_st ps' = ST_STRING -> c_sst c1 = ps_sst ps' -> tok_ok c1 (b256 (ps_buf ps')) -> c_sst c1 = SS_TEXT ->
  (exists t, u8 M' (P + 220) t /\ 0 <= t <= 1) ->
  ps_win ps = Some (p, e) -> Z.of_nat (length ww) = e - p -> ps_win ps' = Some (p + Z.of_nat (S n), e) -> PMW.win_bytes M' ps' (skipn (S n) ww) ->
  w3s cw ww M' P ps ps' eg eg 0.
Proof.
  intros cw n ww c0 o0 c1 M' P ps ps' eg p e Hn HX HS HF HC Hst Hs HT Htext Ht Hw HL Hw' HWB.
  assert (Hps : parse_string cw ww = ret c1 (skipn (S n) ww)) by (rewrite (parse_at cw ww n c0 o0 Hn HX), HS; exact HF).
  unfold w3s. rewrite Hps. unfold PMW.w_after. cbn [r_of ret PMW.r_code PMW.r_evs PMW.r_ctrl PMW.r_used PMW.r_allow q_c q_w q_evs q_code q_al PMW.es_run PMW.ind_run].
  rewrite length_skipn. replace (Z.of_nat (length ww) - Z.of_nat (length ww - S n)) with (Z.of_nat (S n)) by lia. rewrite Nat2Z.id.
  split; [reflexivity|]. split; [reflexivity|]. split; [exists 0; lia|]. intros _.
  split; [apply (rm_match_string c1 M' P ps' HC Hst Hs HT); [intros R; exfalso; rewrite Htext in R; unfold SS_TEXT in R; lia | intros R; exfalso; rewrite Htext in R; unfold SS_TEXT in R; lia | exact Ht]|].
  split; [unfold winlen; rewrite Hw, Hw'; lia | exact HWB].
Qed.
(* [comment removed for export] *)
Lemma w3_err : forall cw c1 w1 ww (M' : mem) P ps ps' eg code,
  parse_string cw ww = err c1 w1 code -> code <> 0 -> w3s cw ww M' P ps ps' eg eg code.
Proof.
  intros cw c1 w1 ww M' P ps ps' eg code Hps Hc. unfold w3s. rewrite Hps.
  cbn [r_of err PMW.r_code PMW.r_evs PMW.r_ctrl PMW.r_used PMW.r_allow q_c q_w q_evs q_code q_al PMW.es_run PMW.ind_run].
  split; [reflexivity|]. split; [reflexivity|]. split; [exists 0; lia|]. intros H0. exfalso. exact (Hc H0).
Qed.
(* [comment removed for export] *)
Lemma w3_end : forall cw ww (n : nat) c0 o0 (M' : mem) P ps ps' eg eg' code p e,
  (n < length ww)%nat -> xrun cw (firstn n ww) = Some (c0, o0) -> parse_string cw ww = end_string c0 (skipn n ww) ->
  let q := end_string c0 (skipn n ww) in
  code = q_code q -> g_es eg' = PMW.es_run (g_es eg) (q_evs q) ->
  (exists pay, 0 <= pay <= q_al q /\ g_len eg' = g_len eg + PMW.ind_run (g_es eg) (q_evs q) + pay) ->
  (code = 0 -> rm_core (q_c q) ps' /\ ps_st ps' <> ST_STRING /\ ps_st ps' <> ST_NUMBER) ->
  ps_win ps = Some (p, e) -> Z.of_nat (length ww) = e - p ->
  (code = 0 -> ps_win ps' = Some (p + Z.of_nat (S n), e) /\ PMW.win_bytes M' ps' (skipn (S n) ww)) ->
  w3s cw ww M' P ps ps' eg eg' code.
Proof.
  intros cw ww n c0 o0 M' P ps ps' eg eg' code p e Hn HX Hps q Hc Hes Hpay Hcore Hw HL HWB. unfold w3s. rewrite Hps. fold q.
  destruct (end_string_any c0 (skipn n ww)) as (_ & _ & _ & _ & Qw0 & _). fold q in Qw0.
  unfold PMW.w_after. cbn [r_of PMW.r_code PMW.r_evs PMW.r_ctrl PMW.r_used PMW.r_allow].
  split; [exact Hc|]. split; [exact Hes|]. split; [exact Hpay|]. intros H0. destruct (Hcore H0) as (HC & NS & NN). destruct (HWB H0) as [Hw' HWB'].
  rewrite (Qw0 ltac:(rewrite <- Hc; exact H0)). rewrite (skipn_nth_cons n ww Hn). cbn [tl]. rewrite length_skipn.
  replace (Z.of_nat (length ww) - Z.of_nat (length ww - S n)) with (Z.of_nat (S n)) by lia. rewrite Nat2Z.id.
  split; [split; [exact HC|]; split; intros X; exfalso; [exact (NS X) | exact (NN X)]|].
  split; [unfold winlen; rewrite Hw, Hw'; lia | exact HWB'].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hexv (cp d : Z) : Z := (cp * 16 + d) mod 2 ^ 32.
Inductive cpu := UKeep | USet (v : Z) | UHex (d : Z).
Inductive sres := SGo (s : Z) (u1 u2 : cpu) (out : list Z) | SErr (code : Z) | SEnd | SU4 (d : Z) | SU8 (d : Z) | SNone.
Definition appu (u : cpu) (old : Z) : Z := match u with UKeep => old | USet v => v | UHex d => hexv old d end.
Definition sdesc (sst b : Z) : sres :=
  if sst =? SS_TEXT then
    if is_ctl b then SErr E_ILLEGAL_CTL
    else if (b =? 10) || (b =? 13) || (b =? 9) then SErr E_CHAR_IN_STRING
    else if b =? 92 then SGo SS_ESC UKeep UKeep []
    else if b =? 34 then SEnd
    else SGo SS_TEXT UKeep UKeep [b]
  else if sst =? SS_ESC then
    if (b =? 34) || (b =? 92) || (b =? 47) then SGo SS_TEXT UKeep UKeep [b]
    else if b =? 98 then SGo SS_TEXT UKeep UKeep [8]
    else if b =? 102 then SGo SS_TEXT UKeep UKeep [12]
    else if b =? 110 then SGo SS_TEXT UKeep UKeep [10]
    else if b =? 114 then SGo SS_TEXT UKeep UKeep [13]
    else if b =? 116 then SGo SS_TEXT UKeep UKeep [9]
    else if b =? 117 then SGo SS_U1 (USet 0) UKeep []
    else SErr E_ILLEGAL_ESC
  else if sst =? SS_U1 then match hexval b with Some v => SGo SS_U2 (USet v) UKeep [] | None => SErr E_INVALID_UESC end
  else if sst =? SS_U2 then match hexval b with Some v => SGo SS_U3 (UHex v) UKeep [] | None => SErr E_INVALID_UESC end
  else if sst =? SS_U3 then match hexval b with Some v => SGo SS_U4 (UHex v) UKeep [] | None => SErr E_INVALID_UESC end
  else if sst =? SS_U4 then match hexval b with Some v => SU4 v | None => SErr E_INVALID_UESC end
  else if sst =? SS_SP1 then (if b =? 92 then SGo SS_SP2 UKeep (USet 0) [] else SErr E_SURR_PAIR)
  else if sst =? SS_SP2 then (if b =? 117 then SGo SS_U5 UKeep UKeep [] else SErr E_SURR_PAIR)
  else if sst =? SS_U5 then match hexval b with Some v => SGo SS_U6 UKeep (USet v) [] | None => SErr E_INVALID_UESC end
  else if sst =? SS_U6 then match hexval b with Some v => SGo SS_U7 UKeep (UHex v) [] | None => SErr E_INVALID_UESC end
  else if sst =? SS_U7 then match hexval b with Some v => SGo SS_U8 UKeep (UHex v) [] | None => SErr E_INVALID_UESC end
  else if sst =? SS_U8 then match hexval b with Some v => SU8 v | None => SErr E_INVALID_UESC end
  else SNone.
(* [comment removed for export] *)
Lemma sdesc_sound : forall c b,
  match sdesc (c_sst c) b with
  | SGo s' u1 u2 out => exists c1, xstep c b = Some (c1, out) /\ c_sst c1 = s' /\ c_cp c1 = appu u1 (c_cp c) /\ c_cp2 c1 = appu u2 (c_cp2 c)
  | SErr code => xstep c b = None /\ forall r, exists c', xfin c b r = err c' (b :: r) code
  | SEnd => xstep c b = None /\ forall r, xfin c b r = end_string c (b :: r)
  | SU4 d => let x := hexv (c_cp c) d in
      (is_high_surr x = true -> exists c1, xstep c b = Some (c1, []) /\ c_sst c1 = SS_SP1 /\ c_cp c1 = x /\ c_cp2 c1 = c_cp2 c) /\
      (is_high_surr x = false -> xstep c b = None /\
         forall r, exists c1, xfin c b r = ret c1 r /\ c_sst c1 = SS_TEXT /\ c_cp c1 = x /\ c_cp2 c1 = c_cp2 c /\ core_eq c c1 /\ (forall buf, tok_ok c buf -> tok_ok c1 (buf ++ utf8_of x)))
  | SU8 d => let x2 := hexv (c_cp2 c) d in
      exists c1, xstep c b = Some (c1, utf8_of (pair_cp (c_cp c) x2)) /\ c_sst c1 = SS_TEXT /\ c_cp c1 = c_cp c /\ c_cp2 c1 = x2
  | SNone => True
  end.
Proof.
  intros c b. unfold sdesc, xstep, xfin, hexstep, hexv. destruct c as [st sst nst more done lvl stk cp cp2 dlen u8v]. cbn [c_sst c_cp c_cp2 set_sst set_cp set_cp2 tok1 tokn set_tok].
  Ltac go := eexists; split; [reflexivity|]; cbn; repeat split; reflexivity.
  destruct (Z.eqb_spec sst SS_TEXT) as [->|NT].
  { destruct (is_ctl b); [split; [reflexivity | intros r; eexists; reflexivity]|]. destruct ((b =? 10) || (b =? 13) || (b =? 9))%bool; [split; [reflexivity | intros r; eexists; reflexivity]|].
    destruct (b =? 92); [go|]. destruct (b =? 34); [split; [reflexivity | intros r; reflexivity]|]. go. }
  destruct (sst =? SS_ESC).
  { destruct ((b =? 34) || (b =? 92) || (b =? 47))%bool; [go|].
    do 6 (match goal with |- context [if ?x then _ else _] => destruct x; [go|] end). split; [reflexivity | intros r; eexists; reflexivity]. }
  destruct (sst =? SS_U1); [destruct (hexval b); [go | split; [reflexivity | intros r; eexists; reflexivity]]|].
  destruct (sst =? SS_U2); [destruct (hexval b); [go | split; [reflexivity | intros r; eexists; reflexivity]]|].
  destruct (sst =? SS_U3); [destruct (hexval b); [go | split; [reflexivity | intros r; eexists; reflexivity]]|].
  destruct (sst =? SS_U4).
  { destruct (hexval b) as [v|]; [|split; [reflexivity | intros r; eexists; reflexivity]]. cbv zeta. split; intros Hh; rewrite Hh.
    - go.
    - split; [reflexivity|]. intros r. eexists. split; [reflexivity|]. cbn. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [unfold core_eq; cbn; repeat split; reflexivity|].
      intros buf [T1 T2]. unfold tok_ok in *. cbn in *. rewrite length_app, Nat2Z.inj_add, T1, T2, u8_feeds_app. split; reflexivity. }
  destruct (sst =? SS_SP1); [destruct (b =? 92); [go | split; [reflexivity | intros r; eexists; reflexivity]]|].
  destruct (sst =? SS_SP2); [destruct (b =? 117); [go | split; [reflexivity | intros r; eexists; reflexivity]]|].
  destruct (sst =? SS_U5); [destruct (hexval b); [go | split; [reflexivity | intros r; eexists; reflexivity]]|].
  destruct (sst =? SS_U6); [destruct (hexval b); [go | split; [reflexivity | intros r; eexists; reflexivity]]|].
  destruct (sst =? SS_U7); [destruct (hexval b); [go | split; [reflexivity | intros r; eexists; reflexivity]]|].
  destruct (sst =? SS_U8); [|exact I]. destruct (hexval b); [|split; [reflexivity | intros r; eexists; reflexivity]]. cbv zeta. go.
Qed.
(* [comment removed for export] *)
Lemma sdesc_go_inv : forall c b c1 out buf, xstep c b = Some (c1, out) -> core_eq c c1 /\ (tok_ok c buf -> tok_ok c1 (buf ++ out)).
Proof. intros. eapply xstep_inv. exact H. Qed.
End PSKW.
