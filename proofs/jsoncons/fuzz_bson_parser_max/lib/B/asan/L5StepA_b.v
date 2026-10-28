(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA HeapIfaceABx
     AsanAcct AsanAcctShape AxSymExec3 AxSymExec3Sound AsanPlanSoundSums SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5SA.
Import L5A. Import L5CA.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac keep_arith := lazymatch goal with |- _ => L5FastLia.prune_arith end.
Ltac clear_disj_but H := repeat match goal with H' : _ \/ _ |- _ => tryif constr_eq H' H then fail else clear H' end.
Ltac alia0 := first [ lia | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Ltac alia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia | alia0 ].
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac feed_concl T := lazymatch T with ?A -> ?B => feed_concl B | _ => T end.
Ltac feed P tac :=
  let T := type of P in
  lazymatch T with
  | ?A0 -> _ =>
      let C := feed_concl T in
      let Q := fresh "SC" in
      assert (Q : C) by (apply P; clear P; first [ tac | lazymatch goal with |- ?A => fail 1 "feed: cannot prove premise" A end ]);   (* [comment removed for export] *)
      move Q after P; clear P; rename Q into P
  | _ => idtac
  end.
(* [comment removed for export] *)
Ltac greg :=
  lazymatch goal with |- getr ?R ?x = ?rhs =>
    match goal with H : getr R ?y = ?rhs' |- _ =>
      first [ constr_eq x y | replace x with y by (apply bv_eq; vm_compute; reflexivity) ];
      first [ exact H
            | lazymatch rhs with Z_to_bv 64 ?z => lazymatch rhs' with Z_to_bv 64 ?z' => replace z with z' by (clear; lia); exact H end end ]
    end
  end.
(* [comment removed for export] *)
Ltac gmem :=
  lazymatch goal with
  | |- L5.u64_at ?sg ?M ?a ?v => match goal with H : L5.u64_at sg M ?b ?v' |- _ => first [constr_eq a b | replace a with b by (clear; lia)]; first [exact H | replace v with v' by (clear; lia); exact H] end
  | |- L5.u32_at ?sg ?M ?a ?v => match goal with H : L5.u32_at sg M ?b ?v' |- _ => first [constr_eq a b | replace a with b by (clear; lia)]; first [exact H | replace v with v' by (clear; lia); exact H] end
  | |- L5.u8_at ?sg ?M ?a ?v => match goal with H : L5.u8_at sg M ?b ?v' |- _ => first [constr_eq a b | replace a with b by (clear; lia)]; first [exact H | replace v with v' by (clear; lia); exact H] end
  | |- L5.defined ?M ?a ?n => match goal with H : L5.defined M ?b ?m |- _ => apply (L5.defined_sub M b m a n H); clear; lia end
  | |- L5.writable ?sg ?M ?a ?n => match goal with H : L5.writable sg M ?b ?m |- _ => apply (L5.writable_sub sg M b m a n H); clear; lia end
  | |- L5KA.zeros_at ?M ?a ?n => match goal with H : L5KA.zeros_at M ?b ?m |- _ => apply (L5KA.zeros_at_sub M b m a n H); clear; lia end
  | |- L5.img_clear ?M _ _ => match goal with H : L5.img_clear M _ _ |- _ => exact H end
  end.
(* [comment removed for export] *)
Ltac arith_shape :=
  lazymatch goal with
  | |- (_ <= _)%Z => idtac | |- (_ < _)%Z => idtac | |- (_ <= _ <= _)%Z => idtac | |- (_ <= _ < _)%Z => idtac | |- (_ < _ <= _)%Z => idtac | |- (_ < _ < _)%Z => idtac
  | |- @eq Z _ _ => idtac | |- (_ \/ _) => idtac | |- (~ _)%type => idtac | |- (_ /\ _) => idtac
  | |- le _ _ => idtac | |- lt _ _ => idtac | |- @eq nat _ _ => idtac
  end.
Ltac arith_goal := first [ arith_shape | red; arith_shape ].
(* [comment removed for export] *)
Ltac sc0 := first [ assumption | greg | gmem | arith_goal; first [assumption | alia] ].
(* [comment removed for export] *)
Ltac xfer AG C :=
  first [ eapply L5C.u64_at_agree; [intros ? ?; apply AG; alia | alia | alia | exact C]
        | eapply L5C.u8_at_agree; [intros ? ?; apply AG; alia | alia | alia | exact C]
        | eapply L5KA.zeros_at_agree1; [intros ? ?; apply AG; alia | exact C]
        | eapply L5C.defined_agree; [intros ? ?; apply AG; alia | exact C] ].
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)).

Lemma r1 : (1%bv : bv 5) = Z_to_bv 5 (Z.of_nat 1). Proof. apply bv_eq; reflexivity. Qed.
Lemma r2 : (2%bv : bv 5) = Z_to_bv 5 (Z.of_nat 2). Proof. apply bv_eq; reflexivity. Qed.
Lemma r4 : (4%bv : bv 5) = Z_to_bv 5 (Z.of_nat 4). Proof. apply bv_eq; reflexivity. Qed.
Lemma r10 : (10%bv : bv 5) = Z_to_bv 5 (Z.of_nat 10). Proof. apply bv_eq; reflexivity. Qed.
Lemma r11 : (11%bv : bv 5) = Z_to_bv 5 (Z.of_nat 11). Proof. apply bv_eq; reflexivity. Qed.
Lemma r12 : (12%bv : bv 5) = Z_to_bv 5 (Z.of_nat 12). Proof. apply bv_eq; reflexivity. Qed.

Lemma rng_dec a lo hi : {lo <= a < hi} + {~ (lo <= a < hi)}.
Proof. destruct (Z_lt_le_dec a lo); [right; lia|]. destruct (Z_lt_le_dec a hi); [left; lia | right; lia]. Qed.

(* [comment removed for export] *)
Definition cs_all : list nat := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Lemma preserved_by_index (R R' : bvmap 5 word) : (forall k, In k cs_all -> getr R' (reg k) = getr R (reg k)) -> regs_preserved R R'.
Proof.
  intros KR x Hx. rewrite <- (AX2S.ridx_roundtrip x). apply KR.
  unfold callee_saved_idx in Hx. unfold AX2.ridx. set (z := bv_unsigned x) in *. cbn in Hx.
  repeat (destruct Hx as [Hx|Hx]; [rewrite <- Hx; cbn; tauto|]). destruct Hx.
Qed.
Lemma cs_of_preserved (R R' : bvmap 5 word) k : regs_preserved R R' -> In k cs_all -> getr R' (reg k) = getr R (reg k).
Proof.
  intros RP Hk. apply RP. unfold callee_saved_idx. cbn in Hk.
  repeat (destruct Hk as [<-|Hk]; [cbn; tauto|]). destruct Hk.
Qed.
Lemma regs_preserved_trans R1 R2 R3 : regs_preserved R1 R2 -> regs_preserved R2 R3 -> regs_preserved R1 R3.
Proof. intros A B x Hx. rewrite (B x Hx). apply A. exact Hx. Qed.

(* [comment removed for export] *)
Ltac rk :=
  first [ reflexivity | greg
        | match goal with K : forall x, In x _ -> getr ?Rb (reg x) = getr ?Ra (reg x) |- getr ?Rb' (Z_to_bv 5 (Z.of_nat ?k)) = _ =>
            constr_eq Rb Rb'; rewrite (K k) by (apply L5K.in_b; vm_compute; reflexivity); rk end
        | match goal with RP : regs_preserved ?Ra ?Rb |- getr ?Rb' (Z_to_bv 5 (Z.of_nat ?k)) = _ =>
            constr_eq Rb Rb'; rewrite (cs_of_preserved Ra Rb k RP) by (apply L5K.in_b; vm_compute; reflexivity); rk end ].
Ltac sc := first [ assumption | rk | gmem | arith_goal; first [assumption | alia] ].

(* [comment removed for export] *)
Lemma u64_of_zeros_at M a : L5KA.zeros_at M a 8 -> 0 <= a -> a + 8 <= 2 ^ 64 -> L5.u64_at RSEGS M a 0.
Proof.
  intros Z8 Ha Hn. unfold L5.u64_at. change (word_to_le_bytes 8 (Z_to_bv 64 0)) with (repeat (Z_to_bv 8 0 : byte) 8).
  apply APSX.rdn_overlay_all. rewrite L5.unsigned_lit by lia. cbn. lia.
  intros i Hi. rewrite L5.unsigned_lit by lia. apply Z8. cbn in Hi. lia.
Qed.
(* [comment removed for export] *)
Lemma reserve_flags fb : 0 <= fb < 256 -> Z.lor (Z.land (4 * (fb / 4) + 1) 253) (Z.land fb 2) = Z.lor fb 1.
Proof.
  intros H.
  assert (E : forallb (fun k => Z.eqb (Z.lor (Z.land (4 * (Z.of_nat k / 4) + 1) 253) (Z.land (Z.of_nat k) 2)) (Z.lor (Z.of_nat k) 1)) (seq 0 256) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in E. specialize (E (Z.to_nat fb) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in E by lia. apply Z.eqb_eq. exact E.
Qed.
Lemma lor1_facts fb : 0 <= fb < 256 -> 0 <= Z.lor fb 1 < 256 /\ Z.testbit (Z.lor fb 1) 0 = true.
Proof.
  intros H. split.
  - assert (E : forallb (fun k => Z.ltb (Z.lor (Z.of_nat k) 1) 256 && Z.leb 0 (Z.lor (Z.of_nat k) 1))%bool (seq 0 256) = true) by (vm_compute; reflexivity).
    rewrite forallb_forall in E. specialize (E (Z.to_nat fb) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in E by lia. apply andb_prop in E. destruct E as [E1 E2].
    apply Z.ltb_lt in E1. apply Z.leb_le in E2. lia.
  - rewrite Z.lor_spec. rewrite Bool.orb_true_iff. right. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rdn_overlay_list M : forall (bs : list byte) (a : Z),
  0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall i, (i < length bs)%nat -> M (Z_to_bv 64 (a + Z.of_nat i)) = nth_error bs i) ->
  rdn RSEGS M (Z_to_bv 64 a) (length bs) = Some bs.
Proof.
  induction bs as [|b bs IH]; intros a Ha Hn Hall. reflexivity.
  cbn [rdn length]. pose proof (Hall 0%nat ltac:(cbn; lia)) as H0. rewrite Z.add_0_r in H0. cbn [nth_error] in H0. rewrite H0.
  cbn [length] in Hn.
  replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)).
  2:{ apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). change (bv_unsigned 1) with (1 mod 2 ^ 64).
      rewrite <- Z.add_mod by lia. reflexivity. }
  rewrite (IH (a + 1)). reflexivity. lia. lia. intros i Hi. replace (a + 1 + Z.of_nat i) with (a + Z.of_nat (Datatypes.S i)) by lia. apply (Hall (Datatypes.S i)). cbn; lia.
Qed.
(* [comment removed for export] *)
Definition limb_bytes (ws : list Z) : list byte := flat_map (fun w => word_to_le_bytes 8 (Z_to_bv 64 w)) ws.
Lemma limb_bytes_length ws : length (limb_bytes ws) = (8 * length ws)%nat.
Proof. induction ws as [|w ws IH]. reflexivity. cbn [limb_bytes flat_map]. rewrite length_app, length_N_to_le_bytes. unfold limb_bytes in IH. rewrite IH. cbn [length]. lia. Qed.
Lemma rdn_of_limbs_at M : forall ws q, L5.limbs_at RSEGS M q ws -> 0 <= q -> q + 8 * Z.of_nat (length ws) <= 2 ^ 64 ->
  rdn RSEGS M (Z_to_bv 64 q) (8 * length ws)%nat = Some (limb_bytes ws).
Proof.
  induction ws as [|w ws IH]; intros q HL Hq Hn. reflexivity.
  cbn [length] in Hn. replace (8 * length (w :: ws))%nat with (8 + 8 * length ws)%nat by (cbn [length]; lia).
  change (limb_bytes (w :: ws)) with (word_to_le_bytes 8 (Z_to_bv 64 w) ++ limb_bytes ws).
  apply SeqExec.rdn_app.
  - pose proof (HL 0%nat ltac:(cbn; lia)) as H0. cbn [nth] in H0. unfold L5.u64_at in H0. rewrite Z.add_0_r in H0. exact H0.
  - unfold nat_to_word.
    replace (Z_to_bv 64 q + Z_to_bv 64 (Z.of_nat 8))%bv with (Z_to_bv 64 (q + 8)).
    2: { apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
         rewrite <- Z.add_mod by lia. reflexivity. }
    apply IH. intros i Hi. replace (q + 8 + 8 * Z.of_nat i) with (q + 8 * Z.of_nat (Datatypes.S i)) by lia.
    change (nth i ws 0) with (nth (Datatypes.S i) (w :: ws) 0). apply HL. cbn; lia. lia. lia.
Qed.
Lemma limbs_at_of_bytes M : forall (ws : list Z) (dst : Z),
  0 <= dst -> dst + 8 * Z.of_nat (length ws) <= 2 ^ 64 ->
  (forall i, (i < 8 * length ws)%nat -> M (Z_to_bv 64 (dst + Z.of_nat i)) = nth_error (limb_bytes ws) i) ->
  L5.limbs_at RSEGS M dst ws.
Proof.
  induction ws as [|w ws IH]; intros dst Hd Hn Hall i Hi. cbn in Hi; lia.
  cbn [length] in Hn, Hi.
  change (limb_bytes (w :: ws)) with (word_to_le_bytes 8 (Z_to_bv 64 w) ++ limb_bytes ws) in Hall.
  destruct i as [|i].
  - cbn [nth]. unfold L5.u64_at. rewrite Z.mul_0_r, Z.add_0_r. rewrite <- (length_N_to_le_bytes 8 (Z_to_bv 64 w)) at 1.
    apply rdn_overlay_list. exact Hd. rewrite length_N_to_le_bytes. lia.
    intros k Hk. rewrite length_N_to_le_bytes in Hk. rewrite (Hall k ltac:(cbn [length]; lia)). rewrite nth_error_app1. reflexivity. rewrite length_N_to_le_bytes. exact Hk.
  - cbn [nth]. replace (dst + 8 * Z.of_nat (Datatypes.S i)) with (dst + 8 + 8 * Z.of_nat i) by lia. apply IH. lia. lia. 2: cbn in Hi |- *; lia.
    intros k Hk. replace (dst + 8 + Z.of_nat k) with (dst + Z.of_nat (8 + k)) by lia. rewrite (Hall (8 + k)%nat ltac:(cbn [length]; lia)).
    rewrite nth_error_app2. rewrite length_N_to_le_bytes. f_equal. lia. rewrite length_N_to_le_bytes. lia.
Qed.
(* [comment removed for export] *)
Lemma defined_word M a : L5.defined M a 8 -> 0 <= a -> a + 8 <= 2 ^ 64 -> exists w, 0 <= w < 2 ^ 64 /\ L5.u64_at RSEGS M a w.
Proof.
  intros D Ha Hb.
  set (f := fun x : Z => match M (Z_to_bv 64 x) with Some b => b | None => Z_to_bv 8 0 end).
  set (bs := map (fun k => f (a + Z.of_nat k)) (seq 0 8)).
  exists (bytes_le_to_Z bs).
  assert (L: length bs = 8%nat) by reflexivity.
  pose proof (AX2S.bytes_le_to_Z_bound bs) as B. rewrite L in B. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in B. split. exact B.
  unfold L5.u64_at. rewrite (APSX.word_to_le_bytes_of_bytes_n 8 bs L ltac:(lia)). rewrite <- L at 1.
  apply rdn_overlay_list. exact Ha. rewrite L; exact Hb. intros i Hi. rewrite L in Hi. unfold bs.
  rewrite nth_error_map. rewrite (nth_error_nth' _ 0%nat) by (rewrite length_seq; exact Hi). rewrite seq_nth by exact Hi. cbn [option_map Nat.add]. unfold f.
  destruct (M (Z_to_bv 64 (a + Z.of_nat i))) eqn:E. reflexivity. exfalso. apply (D (Z.of_nat i)). lia. exact E.
Qed.
Lemma limbs_of_defined M q : forall (k : nat), L5.defined M q (8 * Z.of_nat k) -> 0 <= q -> q + 8 * Z.of_nat k <= 2 ^ 64 ->
  exists ws, length ws = k /\ Forall (fun w => 0 <= w < 2 ^ 64) ws /\ L5.limbs_at RSEGS M q ws.
Proof.
  induction k as [|k IH]; intros D Hq Hk.
  - exists []. split. reflexivity. split. constructor. apply L5C.limbs_at_nil.
  - destruct (IH ltac:(eapply L5.defined_sub; [exact D|lia|lia]) Hq ltac:(lia)) as (ws & Lw & Rw & LA).
    destruct (defined_word M (q + 8 * Z.of_nat k) ltac:(eapply L5.defined_sub; [exact D|lia|lia]) ltac:(lia) ltac:(lia)) as (w & Rg & Uw).
    exists (ws ++ [w]). split. rewrite length_app; cbn; lia. split. apply Forall_app; split; [exact Rw|constructor; [lia|constructor]].
    apply L5C.limbs_at_app. exact LA. intros i Hi. cbn in Hi. destruct i; [|lia]. cbn [nth]. rewrite Lw.
    replace (q + 8 * Z.of_nat k + 8 * Z.of_nat 0) with (q + 8 * Z.of_nat k) by lia. exact Uw.
Qed.
(* [comment removed for export] *)
Lemma kland_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof. intros Ha Hm. pose proof (L5K.land_le_r a m Ha ltac:(lia)). pose proof (Z.land_nonneg a m). lia. Qed.
Lemma klor_byte a b : 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
  intros Ha Hb. split. apply Z.lor_nonneg; lia.
  destruct (Z.eq_dec a 0) as [->|Na]. rewrite Z.lor_0_l. lia. destruct (Z.eq_dec b 0) as [->|Nb]. rewrite Z.lor_0_r. lia.
  apply (Z.log2_lt_cancel). rewrite Z.log2_lor by lia.
  apply Z.max_lub_lt; apply Z.log2_lt_pow2; try lia; change (2 ^ Z.log2 256) with 256; lia.
Qed.
Lemma signcopy_facts f0 fb' : 0 <= f0 < 256 -> 0 <= fb' < 256 ->
  0 <= Z.lor (Z.land f0 253) (Z.land fb' 2) < 256 /\ Z.testbit (Z.lor (Z.land f0 253) (Z.land fb' 2)) 0 = Z.testbit f0 0.
Proof.
  intros H0 H1. split.
  - apply klor_byte; apply kland_byte; lia.
  - rewrite Z.lor_spec, !Z.land_spec. change (Z.testbit 253 0) with true. change (Z.testbit 2 0) with false. rewrite Bool.andb_true_r, Bool.andb_false_r, Bool.orb_false_r. reflexivity.
Qed.

Section SCFG_1.
Context {SCFG_P : ScfgP}.

Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : asan_iface_okB L ar C SCFG HI.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Lemma aclient_mono {BS ST} LB FF sp scr sp' scr' a :
  aclient_g BS ST L ar LB FF sp scr a -> (forall x, sp' - scr' <= x < sp' -> sp - scr <= x < sp) -> aclient_g BS ST L ar LB FF sp' scr' a.
Proof.
  intros Hc Hs. destruct Hc as [Hc|[Hc|Hc]]. left; exact Hc. right; left. split. lia. intros X. apply (proj2 Hc). apply Hs. exact X. right; right; exact Hc.
Qed.
Lemma aclient_00 {BS ST} LB FF sp scr a : aclient_g BS ST L ar LB FF sp scr a -> aclient_g BS ST L ar LB FF 0 0 a.
Proof. intros Hc. eapply aclient_mono. exact Hc. intros x Hx. lia. Qed.
Lemma aclient_cons {BS ST} LB FF f sp scr a : aclient_g BS ST L ar LB FF sp scr a -> aclient_g BS ST L ar LB (f :: FF) sp scr a.
Proof.
  intros Hc. destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]].
  - left; exact Hc. - right; left; exact Hc. - right; right; left; exact Hc.
  - right; right; right; left. destruct Hc as (g & Hg & X). exists g. split. right; exact Hg. exact X.
  - right; right; right; right; left; exact Hc.
  - right; right; right; right; right; left. destruct Hc as (g & Hg & X). exists g. split. right; exact Hg. exact X.
  - right; right; right; right; right; right. exact Hc.
Qed.
Lemma aclient_consb {BS ST} LB FF b sp scr a : aclient_g BS ST L ar LB FF sp scr a -> aclient_g BS ST L ar (b :: LB) FF sp scr a.
Proof.
  intros Hc. destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]].
  - left. destruct Hc as (g & Hg & X). exists g. split. right; exact Hg. exact X.
  - right; left; exact Hc. - right; right; left; exact Hc.
  - right; right; right; left; exact Hc.
  - right; right; right; right; left; exact Hc.
  - right; right; right; right; right; left; exact Hc.
  - right; right; right; right; right; right. destruct Hc as (g & Hg & X). exists g. split. right; exact Hg. exact X.
Qed.
Lemma aclient_app {BS ST} LB FF FX sp scr a : aclient_g BS ST L ar LB FF sp scr a -> aclient_g BS ST L ar LB (FX ++ FF) sp scr a.
Proof. intros Hc. induction FX as [|f FX IH]. exact Hc. cbn [app]. apply aclient_cons. exact IH. Qed.
Lemma aclient_appb {BS ST} LB BX FF sp scr a : aclient_g BS ST L ar LB FF sp scr a -> aclient_g BS ST L ar (BX ++ LB) FF sp scr a.
Proof. intros Hc. induction BX as [|b BX IH]. exact Hc. cbn [app]. apply aclient_consb. exact IH. Qed.
Lemma aclient_consb_inv LB FF b sp scr a :
  aclient L ar (b :: LB) FF sp scr a -> aclient L ar LB FF sp scr a \/ (fst b <= a < fst b + snd b) \/ in_shadow_of (fst b) (snd b) a.
Proof.
  intros Hc. destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]].
  - destruct Hc as (g & [<-|Hg] & X). right; left; exact X. left; left. exists g. split. exact Hg. exact X.
  - left; right; left; exact Hc. - left; right; right; left; exact Hc. - left; right; right; right; left; exact Hc.
  - left; right; right; right; right; left; exact Hc. - left; right; right; right; right; right; left; exact Hc.
  - destruct Hc as (g & [<-|Hg] & X). right; right; exact X. left; right; right; right; right; right; right. exists g. split. exact Hg. exact X.
Qed.
Lemma aobj_cons FF f o sz : aobj FF o sz -> aobj (f :: FF) o sz.
Proof. intros (g & Hg & X). exists g. split. right; exact Hg. exact X. Qed.
Lemma fframes_apart_incl a n FF FF' : fframes_apart a n FF -> incl FF' FF -> fframes_apart a n FF'.
Proof. intros H I f Hf. apply H. apply I. exact Hf. Qed.
Lemma fframes_apart_tl a n f FF : fframes_apart a n (f :: FF) -> fframes_apart a n FF.
Proof. intros H g Hg. apply H. right. exact Hg. Qed.
(* [comment removed for export] *)
Lemma aclient_cases LB FF LK cr A M V sp scr a :
  ri_inv HI LB FF LK cr A M V -> 0x7fff80000000 <= ar_sptop ar <= 2 ^ 47 ->
  aclient L ar LB FF sp scr a -> (ahl_ceil ar <= a /\ ~ (sp - scr <= a < sp)) \/ a < ahl_ceil ar.
Proof.
  intros HH SPT Hc. pose proof (aiob_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _).
  destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]].
  - right. destruct Hc as (b & Hb & X). pose proof (proj1 (WB b Hb)) as (_ & _ & _ & _ & Y & _). lia.
  - left. split. lia. exact (proj2 Hc).
  - right. rewrite (aly_img_hi L C LY) in Hc. lia.
  - right. destruct Hc as (f & Hf & X). pose proof (WF f Hf) as (_ & Y & _). lia.
  - right. unfold in_shadow_of, S, SB in Hc. lia.
  - right. destruct Hc as (f & Hf & X). pose proof (WF f Hf) as (Y1 & Y & _). unfold in_shadow_of, S, SB in X. unfold app_mem in FSAPP. lia.
  - right. destruct Hc as (b & Hb & X). pose proof (proj1 (WB b Hb)) as (Y0 & _ & _ & _ & Y & _). unfold in_shadow_of, S, SB in X. lia.
Qed.
(* [comment removed for export] *)
Lemma fresh_frame_not_client LB FF LK cr A M V sp scr F B a :
  ri_inv HI LB FF LK cr A M V -> 0x7fff80000000 <= ar_sptop ar <= 2 ^ 47 ->
  0x696000 <= F -> F + B <= ahl_ceil ar -> app_mem F B -> F mod 8 = 0 -> 0 < B -> B mod 8 = 0 ->
  fframes_apart F B FF -> (forall b, In b LB -> F + B <= fst b \/ fst b + snd b <= F) ->
  (F <= a < F + B \/ S F <= a <= S (F + B - 1)) -> ~ aclient L ar LB FF sp scr a.
Proof.
  intros HH SPT F1 F2 F3 F4 F5 F6 FA FB Ha Hc. pose proof (aiob_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _).
  unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in F3. unfold S, SB in Ha.
  destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]].
  - destruct Hc as (b & Hb & X). pose proof (proj1 (WB b Hb)) as (Y0 & _ & _ & _ & Y & Y2). unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Y2. specialize (FB b Hb). lia.
  - lia.
  - rewrite (aly_img_hi L C LY) in Hc. lia.
  - destruct Hc as (f & Hf & X). pose proof (WF f Hf) as (Y1 & Y & _). specialize (FA f Hf). unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in FSAPP. lia.
  - unfold in_shadow_of, S, SB in Hc. lia.
  - destruct Hc as (f & Hf & X). pose proof (WF f Hf) as (Y1 & Y & Y3 & Y4 & _). specialize (FA f Hf). unfold in_shadow_of, S, SB in X.
    assert (Y5 : ff_addr f mod 8 = 0 /\ ff_bytes (ff_class f) mod 8 = 0 /\ 0 < ff_bytes (ff_class f)).
    { destruct Y4 as [E|[E|[E|[]]]]; rewrite <- E in Y3 |- *;
      [change (ff_bytes 1) with (16 * 8) in Y3 |- * | change (ff_bytes 2) with (32 * 8) in Y3 |- * | change (ff_bytes 3) with (64 * 8) in Y3 |- *];
      (split; [|split; [apply Z_mod_mult|lia]]); apply Z.mod_divide in Y3; try lia; destruct Y3 as [k Hk]; rewrite Hk; rewrite Z.mul_assoc; apply Z_mod_mult. }
    destruct Y5 as (Y5 & Y6 & Y7). unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in FSAPP. lia.
  - destruct Hc as (b & Hb & X). pose proof (proj1 (WB b Hb)) as (Y0 & _ & Y1 & _ & Y & Y2). specialize (FB b Hb). unfold in_shadow_of, S, SB in X.
    unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Y2. assert (Y5 : fst b mod 8 = 0) by (clear - Y1; apply Z.mod_divide in Y1; [|lia]; destruct Y1 as [k ->]; replace (k * 16) with ((2 * k) * 8) by lia; apply Z_mod_mult). lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma aclientw_not_bshadow LB FF LK cr A M V sp scr a :
  ri_inv HI LB FF LK cr A M V -> aclientw L ar LB FF sp scr a -> ~ block_shadow LB a.
Proof.
  intros HH Hc (b' & Hb' & X'). pose proof (aiob_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & (_ & _ & SPT & SP16) & _).
  destruct (WB b' Hb') as ((Q0 & _ & Q16 & Q3 & Q4 & Q5) & _ & _ & _ & _ & QFA & _). unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Q5.
  unfold in_shadow_of, S, SB in X'. unfold app_mem, FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in FSAPP.
  destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]].
  - destruct Hc as (b & Hb & X). pose proof (proj1 (WB b Hb)) as (Y0 & _ & _ & _ & Y & Y2). unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Y2. lia.
  - lia.
  - rewrite (aly_img_hi L C LY) in Hc. lia.
  - destruct Hc as (f & Hf & X). pose proof (WF f Hf) as (Y1 & Y & _). unfold FS_BYTES in Y. lia.
  - unfold in_shadow_of, S, SB in Hc. lia.
  - destruct Hc as (f & Hf & X). pose proof (WF f Hf) as (Y1 & Y & Y3 & Y4 & _). specialize (QFA f ltac:(apply in_or_app; left; exact Hf)). unfold in_shadow_of, S, SB in X.
    assert (Y5 : ff_addr f mod 8 = 0 /\ ff_bytes (ff_class f) mod 8 = 0 /\ 0 < ff_bytes (ff_class f)).
    { destruct Y4 as [E|[E|[E|[]]]]; rewrite <- E in Y3 |- *;
      [change (ff_bytes 1) with (16 * 8) in Y3 |- * | change (ff_bytes 2) with (32 * 8) in Y3 |- * | change (ff_bytes 3) with (64 * 8) in Y3 |- *];
      (split; [|split; [apply Z_mod_mult|lia]]); apply Z.mod_divide in Y3; try lia; destruct Y3 as [k Hk]; rewrite Hk; rewrite Z.mul_assoc; apply Z_mod_mult. }
    destruct Y5 as (Y5 & Y6 & Y7). lia.
  - destruct Hc as (b & _ & []).
Qed.
(* [comment removed for export] *)
Lemma aclientw_of_client LB FF LK cr A M V sp scr a :
  ri_inv HI LB FF LK cr A M V -> aclient L ar LB FF sp scr a -> ~ (0x10000 <= a < 0x696000) -> (a < 0x7fff8000 \/ 0x10007fff8000 <= a) -> aclientw L ar LB FF sp scr a.
Proof.
  intros HH Hc NI NS. pose proof (aiob_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
  destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]]; unfold aclientw, aclient_g.
  - left. exact Hc.
  - right; left. exact Hc.
  - exfalso. rewrite (aly_img_lo L C LY), (aly_img_hi L C LY) in Hc. apply NI. exact (proj1 Hc).
  - right; right; right; left. exact Hc.
  - right; right; right; right; left. exact Hc.
  - right; right; right; right; right; left. exact Hc.
  - exfalso. destruct Hc as (b & Hb & X). destruct (WB b Hb) as ((Q0 & _ & _ & Q3 & _ & (_ & _ & Q4)) & _). unfold in_shadow_of, S, SB in X.
    clear - X Q0 Q3 Q4 NS. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


(* [comment removed for export] *)
Lemma stack_client {BS ST} LB FF sp scr a : ahl_ceil ar <= a < 2 ^ 47 -> ~ (sp - scr <= a < sp) -> aclient_g BS ST L ar LB FF sp scr a.
Proof. intros H1 H2. right; left. split. exact H1. exact H2. Qed.
(* [comment removed for export] *)
Lemma stk_shadow_client {BS ST} LB FF sp scr a : in_shadow_of (ahl_ceil ar) (ar_sptop ar - ahl_ceil ar) a -> ar_sptop ar <= 2 ^ 47 -> aclient_g BS ST L ar LB FF sp scr a.
Proof.
  intros [H1 H2] HT. right; right; right; right; left. split. exact H1. eapply Z.le_trans. exact H2. unfold S.
  apply Z.add_le_mono_r. apply Z.div_le_mono. reflexivity. Lia.lia.
Qed.
Lemma block_client {BS ST} LB FF sp scr q n a : In (q, n) LB -> q <= a < q + n -> aclient_g BS ST L ar LB FF sp scr a.
Proof. intros Hin Ha. left. exists (q, n). split. exact Hin. exact Ha. Qed.
Lemma obj_client {BS ST} LB FF sp scr o sz a : aobj FF o sz -> o <= a < o + sz -> aclient_g BS ST L ar LB FF sp scr a.
Proof.
  intros (f & Hf & H1 & H2 & _) Ha. right; right; right; left. exists f. split. exact Hf. lia.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fframe_client {BS ST} LB FF sp scr F k rs a : In (F, k, rs) FF -> (F <= a < F + ff_bytes k - 8 /\ ~ (F + 24 <= a < F + 32)) -> aclient_g BS ST L ar LB FF sp scr a.
Proof. intros Hf Ha. right; right; right; left. exists (F, k, rs). split. exact Hf. cbn [ff_addr ff_class fst snd]. exact Ha. Qed.
Lemma fframe_shadow_client {BS ST} LB FF sp scr F k rs a : In (F, k, rs) FF -> in_shadow_of F (ff_bytes k) a -> aclient_g BS ST L ar LB FF sp scr a.
Proof. intros Hf Ha. right; right; right; right; right; left. exists (F, k, rs). split. exact Hf. exact Ha. Qed.

(* [comment removed for export] *)
Lemma client_apart LB FF sp scr a n b m :
  (forall i, 0 <= i < n -> aclient L ar LB FF sp scr (a + i)) -> (forall i, 0 <= i < m -> ~ aclient L ar LB FF sp scr (b + i)) ->
  0 < n -> 0 < m -> a + n <= b \/ b + m <= a.
Proof.
  intros HC HN Hn Hm. destruct (Z_lt_le_dec b (a + n)) as [X|X]; [|left; exact X]. destruct (Z_lt_le_dec a (b + m)) as [Y|Y]; [|right; exact Y].
  exfalso. apply (HN (Z.max a b - b)). lia. replace (b + (Z.max a b - b)) with (a + (Z.max a b - a)) by lia. apply HC. lia.
Qed.

(* [comment removed for export] *)
Lemma ff_count_app k l1 l2 : ff_count k (l1 ++ l2) = (ff_count k l1 + ff_count k l2)%nat.
Proof. unfold ff_count. rewrite list_basics.list.filter_app, length_app. reflexivity. Qed.
Lemma ff_count_cons k f l : (ff_count k (f :: l) <= Datatypes.S (ff_count k l))%nat.
Proof. unfold ff_count. rewrite list_basics.list.filter_cons. destruct (decide _); cbn [length]; lia. Qed.
Lemma ff_count_incl k l l' : incl l l' -> NoDup l -> (ff_count k l <= ff_count k l')%nat.
Proof.
  intros I ND. unfold ff_count. apply NoDup_incl_length.
  - apply NoDup_ListNoDup. apply list_relations.list.NoDup_filter. exact ND.
  - intros x Hx. apply list_elem_of_In in Hx. apply list_elem_of_In. apply list_basics.list.list_elem_of_filter in Hx. destruct Hx as [Px Hx].
    apply list_basics.list.list_elem_of_filter. split. exact Px. apply list_elem_of_In. apply I. apply list_elem_of_In. exact Hx.
Qed.
Lemma nodup_of_map_app_r (l1 l2 : list fframe) : NoDup (map ff_addr (l1 ++ l2)) -> NoDup l2.
Proof. intros ND. rewrite map_app in ND. apply list_relations.list.NoDup_app in ND. destruct ND as (_ & _ & ND). apply (list_monad.list.NoDup_fmap_1 ff_addr). exact ND. Qed.
Lemma ffr_push FF LK LK' (f : fframe) d d' :
  ffr FF LK d -> incl LK' LK -> NoDup (map ff_addr ((f :: FF) ++ LK')) -> d' + 1 <= d -> 0 <= d' -> ffr (f :: FF) LK' d'.
Proof.
  unfold ffr. intros R I ND Hd Hd'. rewrite ff_count_app in R. change ((f :: FF) ++ LK') with (f :: (FF ++ LK')).
  pose proof (ff_count_cons 1 f (FF ++ LK')) as C1. rewrite ff_count_app in C1.
  pose proof (ff_count_incl 1 LK' LK I (nodup_of_map_app_r (f :: FF) LK' ND)) as C2. lia.
Qed.
Lemma ffr_pop FF LK (f : fframe) d : ffr (f :: FF) LK d -> ffr FF LK d.
Proof. unfold ffr. change ((f :: FF) ++ LK) with (f :: (FF ++ LK)). intros H. unfold ff_count in *. rewrite list_basics.list.filter_cons in H. destruct (decide _); cbn [length] in H; lia. Qed.
Lemma ffr_le FF LK d d' : ffr FF LK d -> d' <= d -> ffr FF LK d'.
Proof. unfold ffr. lia. Qed.
Lemma ffrs_push FF sp sp' F k rs : ffrs FF sp -> sp' + 32 <= rs -> sp' <= sp -> ffrs ((F, k, rs) :: FF) sp'.
Proof. intros H Hr Hs f [<-|Hf]. cbn [ff_rs snd]. exact Hr. specialize (H f Hf). lia. Qed.
Lemma ffrs_le FF sp sp' : ffrs FF sp -> sp' <= sp -> ffrs FF sp'.
Proof. intros H Hs f Hf. specialize (H f Hf). lia. Qed.

(* [comment removed for export] *)
Lemma fl_range LB FF LK cr A M V fl :
  ri_inv HI LB FF LK cr A M V -> ar_fs ar <= fl < ar_fs ar + FS_BYTES -> 0x696000 <= fl /\ fl + 1 <= ahl_ceil ar /\ fl + 1 <= 2 ^ 47.
Proof.
  intros HH FLP. pose proof (aiob_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & FSAPP & FSCEIL & FSIMG & _ & _ & _ & _ & TOP & _).
  unfold app_mem, FS_BYTES in *. rewrite (aly_img_lo L C LY), (aly_img_hi L C LY) in FSIMG. lia.
Qed.
Lemma fl_writable LB FF LK cr A M V fl :
  ri_inv HI LB FF LK cr A M V -> ar_fs ar <= fl < ar_fs ar + FS_BYTES -> L5.defined M fl 1 /\ L5.writable RSEGS M fl 1.
Proof.
  intros HH FLP. pose proof (fl_range LB FF LK cr A M V fl HH FLP) as FR.
  pose proof (aiob_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as WF. repeat lazymatch type of WF with _ /\ _ => apply proj2 in WF end.
  assert (D : L5.defined M fl 1). { intros i Hi. replace (fl + i) with (ar_fs ar + (fl + i - ar_fs ar)) by lia. apply WF. unfold FS_BYTES in *. lia. }
  split. exact D. apply (L5C.writable_of_defined RSEGS). exact D. lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma vis_pack LB FF LK cr A M model :
  ri_inv HI LB FF LK cr A M (vml_of model) ->
  let H := ahid A model in
  H_off_segments RSEGS H
  /\ (forall a n, ahl_ceil ar <= a -> a + n <= 2 ^ 64 -> avis H a n)
  /\ (forall a n, 0 <= a -> a + n <= 0x696000 -> avis H a n)
  /\ (forall a n, ar_fs ar <= a -> a + n <= ar_fs ar + FS_BYTES -> avis H a n)
  /\ (forall q m a n, In (q, m) LB -> q <= a -> a + n <= q + m -> avis H a n)
  /\ (forall q m a n, In (q, m) LB -> (forall i, 0 <= i < n -> in_shadow_of q m (a + i)) -> avis H a n)
  /\ (forall a n, (forall i, 0 <= i < n -> in_shadow_of (ar_fs ar) FS_BYTES (a + i)) -> avis H a n)
  /\ (forall a n, (forall i, 0 <= i < n -> in_shadow_of (ahl_ceil ar) (ar_sptop ar - ahl_ceil ar) (a + i)) -> avis H a n).
Proof.
  intros HH. pose proof (aiob_lazy _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (AWF & LZ).
  pose proof (aiob_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & FSSH & STSH & _).
  unfold app_mem in FSAPP. unfold FS_BYTES in FSAPP, FSCEIL.
  cbn zeta. split.
  { apply (L5LZ.H_off_segments_ahid RSEGS A model 0x696000 segs_below). intros w Hw. pose proof (LZ w Hw) as (X & _). rewrite (aly_img_hi L C LY) in X. exact X. }
  split. { intros a n Ha Hn. apply (avis_of_not_lazy A model (fun x => x < ahl_ceil ar)). intros w Hw. exact (proj1 (proj2 (LZ w Hw))). intros j Hj. lia. lia. lia. }
  split. { intros a n Ha Hn. apply (avis_of_not_lazy A model (fun x => 0x696000 <= x)). intros w Hw. pose proof (proj1 (LZ w Hw)) as X. rewrite (aly_img_hi L C LY) in X. exact X. intros j Hj. lia. lia. lia. }
  split. { intros a n Ha Hn. unfold app_mem, FS_BYTES in *.
           apply (avis_of_not_lazy A model (fun x => ~ (ar_fs ar <= x < ar_fs ar + 11571200))). intros w Hw. exact (proj2 (proj2 (proj2 (LZ w Hw)))).
           intros j Hj X. apply X. lia. lia. lia. }
  split. { intros q m a n Hin Ha Hn. pose proof (proj1 (WB (q, m) Hin)) as (B0 & _ & _ & _ & B4 & B5). cbn [fst snd] in *. unfold app_mem in B5.
           apply (avis_of_not_lazy A model (fun x => ~ in_block LB x)). intros w Hw. exact (proj1 (proj2 (proj2 (LZ w Hw)))).
           intros j Hj X. apply X. exists (q, m). split. exact Hin. cbn [fst snd]. lia. lia. lia. }
  split. { intros q m a n Hin Hs. apply (avis_of_shadow_allowed A model q m). exact (proj1 (proj2 (proj2 (proj2 (WB (q, m) Hin))))). exact Hs. }
  split. { intros a n Hs. apply (avis_of_shadow_allowed A model (ar_fs ar) FS_BYTES). exact FSSH. exact Hs. }
  intros a n Hs. apply (avis_of_shadow_allowed A model (ahl_ceil ar) (ar_sptop ar - ahl_ceil ar)). exact STSH. exact Hs.
Qed.

Lemma fl_vis LB FF LK cr A M model fl :
  ri_inv HI LB FF LK cr A M (vml_of model) -> ar_fs ar <= fl < ar_fs ar + FS_BYTES -> avis (ahid A model) fl 1.
Proof. intros HH FLP. pose proof (vis_pack LB FF LK cr A M model HH) as (_ & _ & _ & VFS & _). apply VFS; lia. Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma aobj_facts LB FF LK cr A M model o sz sp scr :
  ri_inv HI LB FF LK cr A M (vml_of model) -> aobj FF o sz -> 0 < sz -> sz mod 8 = 0 ->
  let H := ahid A model in
  (0x696000 <= o /\ o + sz <= ahl_ceil ar /\ o + sz <= 2 ^ 47 /\ o mod 8 = 0 /\ (o / 8) * 8 = o)
  /\ (0x7fff7000 + 17592186048512 <= o \/ o + sz <= 0x7fff7000)
  /\ L5.defined M o sz /\ avis H o sz /\ avis H (o / 8 + SB) (sz / 8)
  /\ (forall i, 0 <= i < sz -> aclient L ar LB FF sp scr (o + i))
  /\ (forall i, 0 <= i < sz / 8 -> aclient L ar LB FF sp scr (o / 8 + SB + i)).
Proof.
  intros HH (f & Hf & O1 & O2 & O8) Hsz Hsz8 H.
  pose proof (aiob_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & FSSH & _ & _ & _ & TOP & _).
  pose proof (vis_pack LB FF LK cr A M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  pose proof (WF f Hf) as (Y1 & Y2 & Y3 & Y4 & Y5 & _).
  rewrite (aly_img_lo L C LY), (aly_img_hi L C LY) in FSIMG. unfold app_mem, FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in *.
  assert (HB : 0 < ff_bytes (ff_class f) <= 512). { clear - Y4. destruct Y4 as [E|[E|[E|[]]]]; rewrite <- E; [change (ff_bytes 1) with 128 | change (ff_bytes 2) with 256 | change (ff_bytes 3) with 512]; lia. }
  apply Z.mod_divide in O8; [|lia]. destruct O8 as [q Eq].
  apply Z.mod_divide in Hsz8; [|lia]. destruct Hsz8 as [m Em].
  split. { subst o sz. rewrite Z_div_mult by lia. repeat split; first [apply Z_mod_mult | lia]. }
  split. lia.
  split. { intros i Hi. replace (o + i) with (ff_addr f + (o + i - ff_addr f)) by lia. apply Y5. lia. }
  split. { apply VFS. lia. lia. }
  split. { apply VFSSH. intros i Hi. unfold in_shadow_of, S. subst o sz. rewrite Z_div_mult in Hi |- * by lia. clear - Hi Y1 Y2 O1 O2 HB. lia. }
  split. { intros i Hi. right; right; right; left. exists f. split. exact Hf. lia. }
  intros i Hi. right; right; right; right; right; left. exists f. split. exact Hf. unfold in_shadow_of, S. subst o sz. rewrite Z_div_mult in Hi |- * by lia. clear - Hi O1 O2 HB. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma app_rng_fs LB FF LK cr A M V p m : ri_inv HI LB FF LK cr A M V -> ar_fs ar <= p -> p + m <= ar_fs ar + FS_BYTES -> app_rng ar p m.
Proof.
  intros HH H1 H2. pose proof (aiob_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & FSAPP & FSCEIL & _).
  unfold app_mem in FSAPP. split. clear - FSAPP H1; lia. split. clear - FSAPP H1 H2; lia. clear - FSCEIL H2; lia.
Qed.
Lemma app_rng_aobj LB FF LK cr A M V o sz p m : ri_inv HI LB FF LK cr A M V -> aobj FF o sz -> o <= p -> p + m <= o + sz -> app_rng ar p m.
Proof.
  intros HH (f & Hf & O1 & O2 & _) H1 H2. pose proof (aiob_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & WF & _).
  destruct (WF f Hf) as (Y1 & Y2 & _). apply (app_rng_fs LB FF LK cr A M V p m HH). clear - Y1 O1 H1; lia. clear - Y2 O2 H2; lia.
Qed.
Lemma app_rng_block LB FF LK cr A M V q n p m : ri_inv HI LB FF LK cr A M V -> In (q, n) LB -> q <= p -> p + m <= q + n -> app_rng ar p m.
Proof.
  intros HH Hin H1 H2. pose proof (aiob_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
  destruct (WB (q, n) Hin) as ((Q0 & _ & _ & _ & Q4 & (_ & Q5 & _)) & _). cbn [fst snd] in *. split. clear - Q0 H1; lia. split. clear - Q5 H1 H2; lia. clear - Q4 H2; lia.
Qed.
Lemma app_rng_img p m : 0x7fff80000000 <= ar_sptop ar -> 0 <= p -> p + m <= 0x696000 -> app_rng ar p m.       (* [comment removed for export] *)
Proof. intros SPT H0 H. unfold app_rng, BIGSHADOW_LO. split. exact H0. split. left; clear - H; lia. clear - SPT H; lia. Qed.
Lemma app_rng_stack p m : 0x7fff80000000 <= ar_sptop ar -> ahl_ceil ar <= p -> p + m <= ar_sptop ar -> app_rng ar p m.
Proof. intros SPT H1 H2. unfold app_rng, BIGSHADOW_HI. split. clear - SPT H1; lia. split. right; clear - SPT H1; lia. left; exact H2. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma apiece LB FF LK cr A M model (fx fx1 : FPState) R (pc : Z) R1 (pc1 : Z) (M1v : word -> option byte) (W : Z -> Prop) K :
  ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model ->
  msteps RSEGS (st fx R pc (mrestrict (ahid A model) M)) (st fx1 R1 pc1 M1v) ->
  mem_grows (mrestrict (ahid A model) M) M1v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M1v (Z_to_bv 64 a) = mrestrict (ahid A model) M (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> W a -> aclientw L ar LB FF 0 0 a /\ ~ (0x10000 <= a < 0x696000)) ->       (* [comment removed for export] *)
  (forall M1 model1,
      ri_inv HI LB FF LK cr A M1 (vml_of model1) -> amodel_ok A model1 -> model_rt model model1 -> ahid A model1 = ahid A model ->
      mrestrict (ahid A model) M1 = M1v -> mem_grows M M1 ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
      (forall a : word, ahid A model a = false -> M1 a = M1v a) ->
      srealizes RSEGS SCFG (cfg (fx:=fx1) R1 pc1 M1 model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) R pc M model) K.
Proof.
  intros HH [Hh MI] MS MG FZ WC KONT.
  pose proof (aiob_lazy _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (AWF & LZ).
  pose proof (vis_pack LB FF LK cr A M model HH) as (HOFF & _).
  set (H := ahid A model) in *.
  unfold cfg. eapply (L5LZ.cps_of_msteps_lazy RSEGS H A fx fx1 R _ M R1 _ M1v model K HOFF wx_nowrap (L5LZ.lazy_cover_ahid A model) AWF MI Hh MS).
  intros model1 MI1 SBM1 HC1.
  set (M1 := munrestrict H M M1v).
  assert (M1vis : mrestrict H M1 = M1v). { apply L5LZ.mrestrict_of_munrestrict. exact HC1. }
  assert (FRM1 : forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha Hn. unfold M1, munrestrict. destruct (H (Z_to_bv 64 a)) eqn:E. reflexivity. rewrite (FZ a Ha Hn). unfold mrestrict. rewrite E. reflexivity. }
  assert (MGM1 : mem_grows M M1).
  { intros x Hx. unfold M1, munrestrict. destruct (H x) eqn:E. exact Hx. apply MG. unfold mrestrict. rewrite E. exact Hx. }
  assert (VML : vml_of model1 = vml_of model). { unfold vml_of. rewrite (L5LZ.sbm_vmmaps _ _ SBM1), (L5LZ.sbm_lazy _ _ SBM1). reflexivity. }
  apply (KONT M1 model1).
  - rewrite VML. apply (aiob_frame _ _ _ _ _ HIok LB FF LK cr A M M1 _ HH).
    + intros a Ha Hp. apply FRM1. exact Ha. intros CW. destruct (WC a Ha CW) as [C1 C2]. destruct Hp as [Hp|[Hp|Hp]].
      * exact (Hp (aclientw_client _ _ _ _ _ _ _ C1)). * apply C2. exact (aly_ro_img L C LY a Hp).
      * exact (aclientw_not_bshadow LB FF LK cr A M _ 0 0 a HH C1 Hp).
    + exact MGM1.
  - split. exact (eq_trans (L5LZ.sbm_halted _ _ SBM1) Hh). exact MI1.
  - apply L5LZ.sbm_model_rt. exact SBM1.
  - apply L5LZ.sbm_ahid. exact SBM1.
  - exact M1vis.
  - exact MGM1.
  - exact FRM1.
  - intros a Ha. unfold M1. apply L5LZ.munrestrict_visible. exact Ha.
Qed.

(* [comment removed for export] *)
Lemma apiece_ro LB FF LK cr A M model (fx fx1 : FPState) R (pc : Z) R1 (pc1 : Z) (M1v : word -> option byte) K :
  ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model ->
  msteps RSEGS (st fx R pc (mrestrict (ahid A model) M)) (st fx1 R1 pc1 M1v) ->
  mem_grows (mrestrict (ahid A model) M) M1v ->
  (forall a, 0 <= a < 2 ^ 64 -> M1v (Z_to_bv 64 a) = mrestrict (ahid A model) M (Z_to_bv 64 a)) ->
  (forall M1 model1,
      ri_inv HI LB FF LK cr A M1 (vml_of model1) -> amodel_ok A model1 -> model_rt model model1 -> ahid A model1 = ahid A model ->
      mrestrict (ahid A model) M1 = M1v -> mem_grows M M1 ->
      (forall a, 0 <= a < 2 ^ 64 -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
      srealizes RSEGS SCFG (cfg (fx:=fx1) R1 pc1 M1 model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) R pc M model) K.
Proof.
  intros HH AM MS MG FZ KONT. apply (apiece LB FF LK cr A M model fx fx1 R pc R1 pc1 M1v (fun _ => False) K HH AM MS MG).
  - intros a Ha _. apply FZ. exact Ha.
  - intros a _ [].
  - intros M1 model1 X1 X2 X3 X4 X5 X6 X7 _. apply (KONT M1 model1 X1 X2 X3 X4 X5 X6). intros a Ha. apply X7. exact Ha. intros [].
Qed.

(* [comment removed for export] *)
Lemma mem_eq_of_agree (M M' : word -> option byte) : (forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> M' = M.
Proof.
  intros E. apply functional_extensionality. intros w. rewrite <- (Z_to_bv_bv_unsigned 64 w) at 1. rewrite <- (Z_to_bv_bv_unsigned 64 w) at 2.
  apply E. pose proof (bv_unsigned_in_range _ w) as X. change (bv_modulus 64) with (2 ^ 64) in X. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma astack_ok_of_astk M M1 sp scr fr scr' :
  astk ar M sp scr -> mem_grows M M1 -> 0 <= fr -> 0 <= scr' -> fr + scr' <= scr -> (sp - fr) mod 16 = 0 ->
  astack_ok L ar M1 scr' (sp - fr).
Proof.
  intros (A16 & SLO & SHI & SPT & DSCR & DUP) MG Hfr Hscr Hle AL.
  split. exact AL. split. lia. split. lia. split. exact SPT. split.
  - intros d m Hd Hm. rewrite (aly_segs L C LY). apply (L5C.writable_of_defined RSEGS M1 (sp - fr - scr') scr'). eapply L5.defined_grows. exact MG.
    eapply L5.defined_sub. exact DSCR. lia. lia. lia. lia. exact Hd. exact Hm.
  - eapply L5.defined_grows. exact MG. intros j Hj. destruct (Z_lt_le_dec j fr).
    + replace (sp - fr + j) with (sp - scr + (scr - fr + j)) by lia. apply DSCR. lia.
    + replace (sp - fr + j) with (sp + (j - fr)) by lia. apply DUP. lia.
Qed.

Lemma astk_sub M M1 sp scr fr scr' :
  astk ar M sp scr -> mem_grows M M1 -> 0 <= fr -> 0 <= scr' -> fr + scr' <= scr -> (sp - fr) mod 16 = 0 -> astk ar M1 (sp - fr) scr'.
Proof.
  intros (A16 & SLO & SHI & SPT & DSCR & DUP) MG Hfr Hscr Hle AL.
  split. exact AL. split. lia. split. lia. split. exact SPT. split.
  - eapply L5.defined_grows. exact MG. eapply L5.defined_sub. exact DSCR. lia. lia.
  - eapply L5.defined_grows. exact MG. intros j Hj. destruct (Z_lt_le_dec j fr).
    + replace (sp - fr + j) with (sp - scr + (scr - fr + j)) by lia. apply DSCR. lia.
    + replace (sp - fr + j) with (sp + (j - fr)) by lia. apply DUP. lia.
Qed.

Lemma astk_grows M M1 sp scr : astk ar M sp scr -> mem_grows M M1 -> astk ar M1 sp scr.
Proof.
  intros (A16 & SLO & SHI & SPT & DSCR & DUP) MG. split. exact A16. split. exact SLO. split. exact SHI. split. exact SPT.
  split; eapply L5.defined_grows; eauto.
Qed.

(* [comment removed for export] *)
Lemma astk_after_rt LB FF LK cr A M M1 M2 V sp scr sp' scr' :
  ri_inv HI LB FF LK cr A M V ->
  astk ar M sp scr -> mem_grows M M1 -> aheap_pres L ar LB FF sp' scr' M1 M2 ->
  sp - scr <= sp' - scr' -> sp' <= sp -> 0 <= scr -> astk ar M2 sp scr.
Proof.
  intros HH (A16 & SLO & SHI & SPT & DSCR & DUP) MG [PRES SDEF] H1 H2 H0.
  pose proof (aiob_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TOP & _).
  assert (D : forall x, (sp - scr <= x < sp \/ sp <= x < ar_stack_top ar) -> M2 (Z_to_bv 64 x) <> None).
  { intros x Hx2. destruct (rng_dec x (sp' - scr') sp') as [I|O].
    - apply SDEF. exact I.
    - rewrite PRES. apply MG. destruct (Z_lt_le_dec x sp).
      + replace x with (sp - scr + (x - (sp - scr))) by lia. apply DSCR. lia.
      + replace x with (sp + (x - sp)) by lia. apply DUP. lia.
      + lia. + apply stack_client. lia. exact O. }
  split. exact A16. split. lia. split. lia. split. exact SPT. split.
  - intros j Hj. apply D. lia.
  - intros j Hj. apply D. lia.
Qed.

(* [comment removed for export] *)
Lemma astk_after LB FF LK cr A M M1 M2 V sp scr sp' scr' W :
  ri_inv HI LB FF LK cr A M V ->
  astk ar M sp scr -> mem_grows M M1 -> ahpres L ar LB FF sp' scr' W M1 M2 ->
  sp - scr <= sp' - scr' -> sp' <= sp -> 0 <= scr -> astk ar M2 sp scr.
Proof.
  intros HH (A16 & SLO & SHI & SPT & DSCR & DUP) MG (PRES & SDEF & DK) H1 H2 H0.
  pose proof (aiob_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TOP & _).
  assert (D : forall x, (sp - scr <= x < sp \/ sp <= x < ar_stack_top ar) -> M2 (Z_to_bv 64 x) <> None).
  { intros x Hx2. destruct (rng_dec x (sp' - scr') sp') as [I|O].
    - replace x with (sp' - scr' + (x - (sp' - scr'))) by lia. apply SDEF. lia.
    - apply DK. lia. apply stack_client. lia. exact O. apply MG. destruct (Z_lt_le_dec x sp).
      + replace x with (sp - scr + (x - (sp - scr))) by lia. apply DSCR. lia.
      + replace x with (sp + (x - sp)) by lia. apply DUP. lia. }
  split. exact A16. split. lia. split. lia. split. exact SPT. split.
  - intros j Hj. apply D. lia.
  - intros j Hj. apply D. lia.
Qed.

Lemma astk_writable M sp scr a n : astk ar M sp scr -> sp - scr <= a -> a + n <= sp -> 0 <= n -> L5.writable RSEGS M a n.
Proof.
  intros (A16 & SLO & SHI & SPT & DSCR & DUP) H1 H2 Hn. apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact DSCR. lia. lia. lia. lia.
Qed.
Lemma astk_defined M sp scr a n : astk ar M sp scr -> sp - scr <= a -> a + n <= sp -> L5.defined M a n.
Proof. intros (A16 & SLO & SHI & SPT & DSCR & DUP) H1 H2. eapply L5.defined_sub. exact DSCR. lia. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma retire_frame LB FF LK cr A M2 M3 V F k rs fl :
  ri_inv HI LB ((F, k, rs) :: FF) LK cr A M2 V ->
  cell_is RSEGS M2 (F + ff_bytes k - 8) 8 fl -> ~ aclient L ar LB ((F, k, rs) :: FF) 0 0 fl ->
  (forall a, 0 <= a < 2 ^ 64 -> a <> fl -> M3 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a) \/ aclientw L ar LB ((F, k, rs) :: FF) 0 0 a) ->
  L5.u8_at RSEGS M3 fl 0 -> mem_grows M2 M3 ->
  ri_inv HI LB FF LK cr A M3 V.
Proof.
  intros HH FLC FLNC DIFF FL0 MG.
  assert (EQFF : ff_remove F ((F, k, rs) :: FF) = FF). { cbn [ff_remove ff_addr fst snd]. rewrite Z.eqb_refl. reflexivity. }
  rewrite <- EQFF.
  apply (aiob_release _ _ _ _ _ HIok LB ((F, k, rs) :: FF) LK cr A M2 M3 V F k rs fl HH (or_introl eq_refl)).
  - rewrite (aly_segs L C LY). exact FLC.
  - exact DIFF.
  - rewrite (aly_segs L C LY). exact FL0.
  - exact MG.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma sm_facts LB FF LK' cr A M2 model2 F k rs fl :
  let B := ff_bytes k in let H2 := ahid A model2 in let MV2 := mrestrict H2 M2 in
  ri_inv HI LB ((F, k, rs) :: FF) LK' cr A M2 (vml_of model2) -> In k [1; 2; 3] ->
  ar_fs ar <= F -> F + B <= ar_fs ar + FS_BYTES -> F mod B = 0 -> app_mem F B -> F + B <= ahl_ceil ar ->
  defined M2 F B -> cell_is RSEGS M2 (F + B - 8) 8 fl -> ar_fs ar <= fl < ar_fs ar + FS_BYTES -> ~ aclient L ar LB ((F, k, rs) :: FF) 0 0 fl ->
  (F + B <= fl \/ fl + 1 <= F) ->                                  (* [comment removed for export] *)
  shadow_zero M2 F (B / 8) ->
  (4096 <= F /\ F + B <= 2 ^ 47 /\ 0x696000 <= F /\ F + B <= ahl_ceil ar /\ 64 <= B <= 512) /\ (F + B <= fl \/ fl + 1 <= F)
  /\ F mod 32 = 0 /\ (F / 8) * 8 = F /\ B mod 64 = 0
  /\ L5.defined MV2 F B /\ L5.writable RSEGS MV2 F B
  /\ (0x7fff7000 + 17592186048512 <= F \/ F + B <= 0x7fff7000)
  /\ L5.writable RSEGS MV2 (F / 8 + SB) (B / 8) /\ L5KA.zeros_at MV2 (F / 8 + SB) (B / 8)
  /\ L5.u64_at RSEGS MV2 (F + B - 8) fl
  /\ (4096 <= fl /\ fl + 1 <= 2 ^ 47 /\ 0x696000 <= fl /\ fl + 1 <= ahl_ceil ar)
  /\ L5.writable RSEGS MV2 fl 1
  /\ (0x7fff7000 + 17592186048512 <= fl \/ fl + 1 <= 0x7fff7000)
  /\ avis H2 F B /\ avis H2 (F / 8 + SB) (B / 8) /\ avis H2 fl 1.
Proof.
  intros B H2 MV2 HH2 Hk FS1 FS2 FAL FAPP FCEIL FDEF FLC FLP FLNC FLA FSH.
  pose proof (aiob_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH2) as (WB & WF & FSAPP & FSCEIL & FSIMG & FSSH & _ & _ & _ & TOP & _).
  pose proof (vis_pack _ _ _ _ _ _ _ HH2) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  rewrite (aly_img_lo L C LY), (aly_img_hi L C LY) in FSIMG.
  assert (HB : 64 <= B <= 512 /\ B mod 64 = 0 /\ exists q, F = q * 64).
  { subst B. destruct Hk as [<-|[<-|[<-|[]]]]; cbn -[Z.le Z.add Z.mul Z.modulo]; 
    [change (ff_bytes 1) with 128 in FAL |- * | change (ff_bytes 2) with 256 in FAL |- * | change (ff_bytes 3) with 512 in FAL |- *];
    (split; [lia|]); (split; [reflexivity|]); apply Z.mod_divide in FAL; try lia; destruct FAL as [q Hq];
    [exists (q * 2) | exists (q * 4) | exists (q * 8)]; lia. }
  destruct HB as (BR & B64 & q & EF).
  unfold app_mem, FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in *.
  pose proof (fl_range _ _ _ _ _ _ _ fl HH2 FLP) as FLR. pose proof (fl_writable _ _ _ _ _ _ _ fl HH2 FLP) as [FLD FLW]. pose proof (fl_vis _ _ _ _ _ _ _ fl HH2 FLP) as FLV.
  assert (VF : avis H2 F B). { apply VFS. lia. lia. }
  assert (VSH : avis H2 (F / 8 + SB) (B / 8)).
  { apply VFSSH. intros i Hi. unfold in_shadow_of, S. clear - Hi EF FS1 FS2 BR B64. subst F. lia. }
  split. lia.
  split. exact FLA.
  split. { subst F. replace (q * 64) with ((q * 2) * 32) by lia. apply Z_mod_mult. } split. { clear - EF. subst F. lia. } split. exact B64.
  split. { apply (proj2 (defined_vis H2 M2 F B VF)). exact FDEF. }
  split. { apply (proj2 (writable_vis H2 M2 F B VF ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact FDEF. lia. lia. }
  split. lia.
  assert (ZSH : L5KA.zeros_at M2 (F / 8 + SB) (B / 8)). { intros i Hi. unfold shadow_zero, byte_at, S in FSH. apply FSH. exact Hi. }
  split. { apply (proj2 (writable_vis H2 M2 _ _ VSH ltac:(unfold SB; lia) ltac:(unfold SB; lia))). apply (L5C.writable_of_defined RSEGS). apply L5KA.zeros_at_defined. exact ZSH. unfold SB; lia. unfold SB; lia. }
  split. { apply (proj2 (zeros_at_vis H2 M2 _ _ VSH)). exact ZSH. }
  split. { apply (proj2 (u64_at_vis H2 M2 (F + B - 8) fl ltac:(eapply avis_sub; [exact VF|lia|lia]) ltac:(lia) ltac:(lia))). exact FLC. }
  split. lia.
  split. { apply (proj2 (writable_vis H2 M2 fl 1 FLV ltac:(lia) ltac:(lia))). exact FLW. }
  split. lia.
  split. exact VF. split. exact VSH. exact FLV.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma sm_apart LB FF LK' cr A M2 V F k rs fl sp scr a n :
  ri_inv HI LB ((F, k, rs) :: FF) LK' cr A M2 V -> 0x7fff80000000 <= ar_sptop ar <= 2 ^ 47 -> In k [1; 2; 3] ->
  0x696000 <= F -> F + ff_bytes k <= ahl_ceil ar -> app_mem F (ff_bytes k) -> F mod ff_bytes k = 0 ->
  fframes_apart F (ff_bytes k) (FF ++ LK') -> (forall b, In b LB -> F + ff_bytes k <= fst b \/ fst b + snd b <= F) ->
  ~ aclient L ar LB ((F, k, rs) :: FF) 0 0 fl ->
  (forall i, 0 <= i < n -> aclient L ar LB FF sp scr (a + i)) -> 0 < n ->
  (a + n <= F \/ F + ff_bytes k <= a) /\ (a + n <= F / 8 + SB \/ F / 8 + SB + ff_bytes k / 8 <= a) /\ (a + n <= fl \/ fl + 1 <= a).
Proof.
  intros HH2 SPT Hk F1 F2 F3 F4 FA FB FLNC CA Hn.
  assert (HB : 0 < ff_bytes k /\ ff_bytes k mod 8 = 0 /\ F mod 8 = 0 /\ (F / 8) * 8 = F).
  { Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    destruct Hk as [<-|[<-|[<-|[]]]]; [change (ff_bytes 1) with 128 in F4 |- * | change (ff_bytes 2) with 256 in F4 |- * | change (ff_bytes 3) with 512 in F4 |- *];
    (split; [lia|]); (split; [reflexivity|]); apply Z.mod_divide in F4; try lia; destruct F4 as [q ->]; split; clear; lia. }
  destruct HB as (B0 & B8 & F8 & FQ).
  assert (HHF : ri_inv HI LB FF LK' cr A M2 V -> True) by (intros; exact I). clear HHF.
  assert (NC : forall x, (F <= x < F + ff_bytes k \/ S F <= x <= S (F + ff_bytes k - 1)) -> ~ aclient L ar LB FF sp scr x).
  { intros x Hx. pose proof (aiob_perm _ _ _ _ _ HIok) as _.
    (* [comment removed for export] *)
    intros Hc. pose proof (aiob_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH2) as (WB & WF & FSAPP & FSCEIL & _).
    unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in F3, FSAPP. unfold S, SB in Hx.
    destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]].
    - destruct Hc as (b & Hb & X). pose proof (proj1 (WB b Hb)) as (Y0 & _ & _ & _ & Y & Y2). unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Y2. specialize (FB b Hb). lia.
    - lia.
    - rewrite (aly_img_hi L C LY) in Hc. lia.
    - destruct Hc as (f & Hf & X). pose proof (WF f (or_intror Hf)) as (Y1 & Y & _). specialize (FA f (in_or_app _ _ _ (or_introl Hf))). lia.
    - unfold in_shadow_of, S, SB in Hc. lia.
    - destruct Hc as (f & Hf & X). pose proof (WF f (or_intror Hf)) as (Y1 & Y & Y3 & Y4 & _). specialize (FA f (in_or_app _ _ _ (or_introl Hf))). unfold in_shadow_of, S, SB in X.
      assert (Y5 : ff_addr f mod 8 = 0 /\ ff_bytes (ff_class f) mod 8 = 0 /\ 0 < ff_bytes (ff_class f)).
      { destruct Y4 as [E|[E|[E|[]]]]; rewrite <- E in Y3 |- *;
        [change (ff_bytes 1) with (16 * 8) in Y3 |- * | change (ff_bytes 2) with (32 * 8) in Y3 |- * | change (ff_bytes 3) with (64 * 8) in Y3 |- *];
        (split; [|split; [apply Z_mod_mult|lia]]); apply Z.mod_divide in Y3; try lia; destruct Y3 as [kk Hk']; rewrite Hk'; rewrite Z.mul_assoc; apply Z_mod_mult. }
      destruct Y5 as (Y5 & Y6 & Y7). Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
    - destruct Hc as (b & Hb & X). pose proof (proj1 (WB b Hb)) as (Y0 & _ & Y1 & _ & Y & Y2). specialize (FB b Hb). unfold in_shadow_of, S, SB in X.
      unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Y2. assert (Y5 : fst b mod 8 = 0) by (clear - Y1; apply Z.mod_divide in Y1; [|lia]; destruct Y1 as [kk ->]; replace (kk * 16) with ((2 * kk) * 8) by lia; apply Z_mod_mult). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  split. { apply (client_apart LB FF sp scr a n F (ff_bytes k) CA). intros i Hi. apply NC. left. lia. exact Hn. exact B0. }
  split. { apply (client_apart LB FF sp scr a n (F / 8 + SB) (ff_bytes k / 8) CA). intros i Hi. apply NC. right. unfold S.
           assert ((F + ff_bytes k - 1) / 8 = F / 8 + ff_bytes k / 8 - 1).
           { apply Z.mod_divide in B8. destruct B8 as [m Hm]. rewrite Hm. rewrite <- FQ. rewrite Z_div_mult by lia.
             replace (F / 8 * 8 + m * 8 - 1) with ((F / 8 + m - 1) * 8 + 7) by lia. rewrite Z.div_add_l by lia. change (7 / 8) with 0. lia. lia. }
           lia. exact Hn. apply Z.div_str_pos. lia. }
  apply (client_apart LB FF sp scr a n fl 1 CA). intros i Hi X. apply FLNC. apply aclient_cons. replace (fl + i) with fl in X by lia. eapply aclient_00. exact X. exact Hn. lia.
Qed.

(* [comment removed for export] *)
Lemma flagptr_now LB FF LK cr A M V LB' FF' LK' cr' A' M' model' F k rs rs' fl :
  ri_inv HI LB FF LK cr A M V -> ri_inv HI LB' FF' LK' cr' A' M' (vml_of model') ->
  In (F, k, rs) FF -> In (F, k, rs') FF' -> In k [1; 2; 3] ->
  cell_is RSEGS M (F + ff_bytes k - 8) 8 fl ->
  cell_is RSEGS M' (F + ff_bytes k - 8) 8 fl /\ L5.u64_at RSEGS (mrestrict (ahid A' model') M') (F + ff_bytes k - 8) fl.
Proof.
  intros HH HH' IN IN' Hk FLC.
  pose proof (aiob_flagptr _ _ _ _ _ HIok LB FF LK cr A M V LB' FF' LK' cr' A' M' _ F k rs rs' fl HH HH' IN IN') as X.
  rewrite (aly_segs L C LY) in X. specialize (X FLC). split. exact X.
  pose proof (aiob_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH') as (_ & WF & FSAPP & _).
  pose proof (WF _ IN') as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2.
  pose proof (vis_pack _ _ _ _ _ _ _ HH') as (_ & _ & _ & VFS & _).
  assert (BR : 64 <= ff_bytes k <= 512) by (destruct Hk as [<-|[<-|[<-|[]]]]; vm_compute; split; discriminate).
  unfold app_mem, FS_BYTES in *.
  apply (proj2 (u64_at_vis (ahid A' model') M' (F + ff_bytes k - 8) fl ltac:(apply VFS; lia) ltac:(lia) ltac:(lia))). exact X.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ek (LB : list (Z * Z)) (FF : list fframe) (sp scr : Z) (W : list L5.range) (M M' : word -> option byte) : Prop :=
  forall a, akept L ar LB FF sp scr W a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Definition dk (LB : list (Z * Z)) (FF : list fframe) (sp scr : Z) (M M' : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp scr a -> M (Z_to_bv 64 a) <> None -> M' (Z_to_bv 64 a) <> None.
Lemma ahpres_of LB FF sp scr W M M' : ek LB FF sp scr W M M' -> L5.defined M' (sp - scr) scr -> dk LB FF sp scr M M' -> ahpres L ar LB FF sp scr W M M'.
Proof. intros E D K. split. exact E. split. exact D. exact K. Qed.
Lemma ek_trans LB FF sp scr W M1 M2 M3 : ek LB FF sp scr W M1 M2 -> ek LB FF sp scr W M2 M3 -> ek LB FF sp scr W M1 M3.
Proof. intros A B a Ha. rewrite (B a Ha). apply A. exact Ha. Qed.
Lemma ek_mono LB FF sp scr sp' scr' W W' M M' :
  ek LB FF sp' scr' W' M M' -> (forall x, sp' - scr' <= x < sp' -> sp - scr <= x < sp) -> (forall a, L5.outside W a -> L5.outside W' a) -> ek LB FF sp scr W M M'.
Proof. intros E Hs HW a (Ha & Hc & Ho). apply E. split. exact Ha. split. eapply aclient_mono. exact Hc. exact Hs. apply HW. exact Ho. Qed.
Lemma ek_tl LB b FF sp scr W M M' : ek (b :: LB) FF sp scr W M M' -> ek LB FF sp scr W M M'.
Proof. intros E a (Ha & Hc & Ho). apply E. split. exact Ha. split. apply aclient_consb. exact Hc. exact Ho. Qed.
Lemma dk_tl LB b FF sp scr M M' : dk (b :: LB) FF sp scr M M' -> dk LB FF sp scr M M'.
Proof. intros D a Ha Hc HM. apply D. exact Ha. apply aclient_consb. exact Hc. exact HM. Qed.
Lemma ek_W LB FF sp scr W W' M M' : ek LB FF sp scr W' M M' -> (forall a, L5.outside W a -> L5.outside W' a) -> ek LB FF sp scr W M M'.
Proof. intros E HW a (Ha & Hc & Ho). apply E. split. exact Ha. split. exact Hc. apply HW. exact Ho. Qed.
Lemma dk_trans LB FF sp scr M1 M2 M3 : dk LB FF sp scr M1 M2 -> dk LB FF sp scr M2 M3 -> dk LB FF sp scr M1 M3.
Proof. intros A B a Ha Hc D. apply B. exact Ha. exact Hc. apply A. exact Ha. exact Hc. exact D. Qed.
Lemma dk_grows LB FF sp scr M M' : mem_grows M M' -> dk LB FF sp scr M M'.
Proof. intros G a _ _ D. apply G. exact D. Qed.
(* [comment removed for export] *)
Lemma ek_piece LB FF sp scr W M M' (P : Z -> Prop) :
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp scr a -> L5.outside W a -> ~ P a) -> ek LB FF sp scr W M M'.
Proof. intros E X a (Ha & Hc & Ho). apply E. exact Ha. apply X. exact Ha. exact Hc. exact Ho. Qed.
(* [comment removed for export] *)
Lemma ek_rt LB FF FX sp scr sp' scr' W M M' :
  aheap_pres L ar LB (FX ++ FF) sp' scr' M M' -> sp - scr <= sp' - scr' -> sp' <= sp -> ek LB FF sp scr W M M'.
Proof.
  intros [P _] H1 H2 a (Ha & Hc & _). apply P. exact Ha. apply aclient_app. eapply aclient_mono. exact Hc. intros x Hx. lia.
Qed.
Lemma aclient_narrow {BS ST} LB FF sp scr sp' scr' a :
  aclient_g BS ST L ar LB FF sp scr a -> ~ (sp' - scr' <= a < sp') -> aclient_g BS ST L ar LB FF sp' scr' a.
Proof. intros Hc O. destruct Hc as [Hc|[Hc|Hc]]. left; exact Hc. right; left. split. exact (proj1 Hc). exact O. right; right; exact Hc. Qed.
Lemma dk_rt LB FF FX sp scr sp' scr' M M' :
  aheap_pres L ar LB (FX ++ FF) sp' scr' M M' -> sp - scr <= sp' - scr' -> sp' <= sp -> dk LB FF sp scr M M'.
Proof.
  intros [P D] H1 H2 a Ha Hc HM. destruct (rng_dec a (sp' - scr') sp') as [I|O]. apply D. exact I.
  rewrite P. exact HM. exact Ha. apply aclient_app. exact (aclient_narrow _ _ _ _ _ _ _ Hc O).
Qed.
(* [comment removed for export] *)
Lemma ek_callee LB BX FF FX sp scr sp' scr' W W' M M' :
  ahpres L ar (BX ++ LB) (FX ++ FF) sp' scr' W' M M' -> sp - scr <= sp' - scr' -> sp' <= sp ->
  (forall a, aclient L ar LB FF sp scr a -> L5.outside W a -> L5.outside W' a) -> ek LB FF sp scr W M M'.
Proof.
  intros (P & _ & _) H1 H2 HW a (Ha & Hc & Ho). apply P. split. exact Ha. split.
  apply aclient_appb. apply aclient_app. eapply aclient_mono. exact Hc. intros x Hx. lia.
  apply HW. exact Hc. exact Ho.
Qed.
Lemma dk_callee LB BX FF FX sp scr sp' scr' W' M M' :
  ahpres L ar (BX ++ LB) (FX ++ FF) sp' scr' W' M M' -> sp - scr <= sp' - scr' -> sp' <= sp -> dk LB FF sp scr M M'.
Proof.
  intros (P & D & K) H1 H2 a Ha Hc HM. destruct (rng_dec a (sp' - scr') sp') as [I|O]. replace a with (sp' - scr' + (a - (sp' - scr'))) by lia. apply D. lia.
  apply K. exact Ha. 2: exact HM. apply aclient_appb. apply aclient_app. exact (aclient_narrow _ _ _ _ _ _ _ Hc O).
Qed.

(* [comment removed for export] *)
Lemma apiece_retire LB FF LK cr A M model (fx fx1 : FPState) R (pc : Z) R1 (pc1 : Z) (M1v : word -> option byte) (W : Z -> Prop) F k rs fl K :
  ri_inv HI LB ((F, k, rs) :: FF) LK cr A M (vml_of model) -> amodel_ok A model ->
  cell_is RSEGS M (F + ff_bytes k - 8) 8 fl -> ~ aclient L ar LB ((F, k, rs) :: FF) 0 0 fl -> avis (ahid A model) fl 1 -> 0 <= fl /\ fl + 1 <= 2 ^ 64 ->
  msteps RSEGS (st fx R pc (mrestrict (ahid A model) M)) (st fx1 R1 pc1 M1v) ->
  mem_grows (mrestrict (ahid A model) M) M1v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M1v (Z_to_bv 64 a) = mrestrict (ahid A model) M (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> W a -> a = fl \/ aclientw L ar LB ((F, k, rs) :: FF) 0 0 a) -> (forall a, W a \/ ~ W a) ->
  L5.u8_at RSEGS M1v fl 0 ->
  (forall M1 model1,
      ri_inv HI LB FF LK cr A M1 (vml_of model1) -> amodel_ok A model1 -> model_rt model model1 -> ahid A model1 = ahid A model ->
      mrestrict (ahid A model) M1 = M1v -> mem_grows M M1 ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
      (forall a : word, ahid A model a = false -> M1 a = M1v a) ->
      srealizes RSEGS SCFG (cfg (fx:=fx1) R1 pc1 M1 model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) R pc M model) K.
Proof.
  intros HH [Hh MI] FLC FLNC FLV FLR MS MG FZ WC WD FL0 KONT.
  pose proof (aiob_lazy _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (AWF & LZ).
  pose proof (vis_pack LB _ LK cr A M model HH) as (HOFF & _).
  set (H := ahid A model) in *.
  unfold cfg. eapply (L5LZ.cps_of_msteps_lazy RSEGS H A fx fx1 R _ M R1 _ M1v model K HOFF wx_nowrap (L5LZ.lazy_cover_ahid A model) AWF MI Hh MS).
  intros model1 MI1 SBM1 HC1.
  set (M1 := munrestrict H M M1v).
  assert (M1vis : mrestrict H M1 = M1v). { apply L5LZ.mrestrict_of_munrestrict. exact HC1. }
  assert (FRM1 : forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha Hn. unfold M1, munrestrict. destruct (H (Z_to_bv 64 a)) eqn:E. reflexivity. rewrite (FZ a Ha Hn). unfold mrestrict. rewrite E. reflexivity. }
  assert (MGM1 : mem_grows M M1).
  { intros x Hx. unfold M1, munrestrict. destruct (H x) eqn:E. exact Hx. apply MG. unfold mrestrict. rewrite E. exact Hx. }
  assert (VML : vml_of model1 = vml_of model). { unfold vml_of. rewrite (L5LZ.sbm_vmmaps _ _ SBM1), (L5LZ.sbm_lazy _ _ SBM1). reflexivity. }
  apply (KONT M1 model1).
  - rewrite VML. apply (retire_frame LB FF LK cr A M M1 _ F k rs fl HH FLC FLNC).
    + intros a Ha Hne. destruct (H (Z_to_bv 64 a)) eqn:E.
      * left. unfold M1, munrestrict. rewrite E. reflexivity.
      * assert (EM : M1 (Z_to_bv 64 a) = M1v (Z_to_bv 64 a)). { unfold M1, munrestrict. rewrite E. reflexivity. }
        destruct (WD a) as [HW|HW].
        -- destruct (WC a Ha HW) as [X|X]. exfalso; exact (Hne X). right; exact X.
        -- left. rewrite EM, (FZ a Ha HW). unfold mrestrict. rewrite E. reflexivity.
    + apply (proj1 (u8_at_vis H M1 fl 0 FLV ltac:(lia) ltac:(lia))). rewrite M1vis. exact FL0.
    + exact MGM1.
  - split. exact (eq_trans (L5LZ.sbm_halted _ _ SBM1) Hh). exact MI1.
  - apply L5LZ.sbm_model_rt. exact SBM1.
  - apply L5LZ.sbm_ahid. exact SBM1.
  - exact M1vis.
  - exact MGM1.
  - exact FRM1.
  - intros a Ha. unfold M1. apply L5LZ.munrestrict_visible. exact Ha.
Qed.

(* [comment removed for export] *)
Lemma astk_after_eq LB FF LK cr A M M1 M2 V sp scr sp' scr' :
  ri_inv HI LB FF LK cr A M V -> astk ar M sp scr -> mem_grows M M1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ahl_ceil ar <= a < 2 ^ 47 -> ~ (sp' - scr' <= a < sp') -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  (forall a, sp' - scr' <= a < sp' -> M2 (Z_to_bv 64 a) <> None) ->
  sp - scr <= sp' - scr' -> sp' <= sp -> 0 <= scr -> astk ar M2 sp scr.
Proof.
  intros HH (A16 & SLO & SHI & SPT & DSCR & DUP) MG PRES SDEF H1 H2 H0.
  pose proof (aiob_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TOP & _).
  assert (D : forall x, (sp - scr <= x < sp \/ sp <= x < ar_stack_top ar) -> M2 (Z_to_bv 64 x) <> None).
  { intros x Hx2. destruct (rng_dec x (sp' - scr') sp') as [I|O].
    - apply SDEF. exact I.
    - rewrite PRES. apply MG. destruct (Z_lt_le_dec x sp).
      + replace x with (sp - scr + (x - (sp - scr))) by lia. apply DSCR. lia.
      + replace x with (sp + (x - sp)) by lia. apply DUP. lia.
      + lia. + lia. + exact O. }
  split. exact A16. split. lia. split. lia. split. exact SPT. split.
  - intros j Hj. apply D. lia.
  - intros j Hj. apply D. lia.
Qed.
(* [comment removed for export] *)
Lemma ek_mem LB FF sp scr sp' scr' (D : Z -> Prop) W M M' :
  (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp' scr' a -> ~ D a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  sp - scr <= sp' - scr' -> sp' <= sp -> (forall a, aclient L ar LB FF sp scr a -> L5.outside W a -> ~ D a) -> ek LB FF sp scr W M M'.
Proof.
  intros P H1 H2 HW a (Ha & Hc & Ho). apply P. exact Ha. eapply aclient_mono. exact Hc. intros x Hx. lia. apply HW. exact Hc. exact Ho.
Qed.
Lemma dk_mem LB FF sp scr sp' scr' (D : Z -> Prop) M M' :
  (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp' scr' a -> ~ D a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  (forall a, sp' - scr' <= a < sp' -> M' (Z_to_bv 64 a) <> None) -> (forall a, D a -> M' (Z_to_bv 64 a) <> None) -> (forall a, D a \/ ~ D a) ->
  sp - scr <= sp' - scr' -> sp' <= sp -> dk LB FF sp scr M M'.
Proof.
  intros P SD DD Ddec H1 H2 a Ha Hc HM. destruct (Ddec a) as [X|X]. apply DD. exact X.
  destruct (rng_dec a (sp' - scr') sp') as [I|O]. apply SD. exact I.
  rewrite P. exact HM. exact Ha. exact (aclient_narrow _ _ _ _ _ _ _ Hc O). exact X.
Qed.
(* [comment removed for export] *)
Lemma fresh_block_not_client LB FF LK cr A M V sp scr q n a :
  ri_inv HI LB FF LK cr A M V -> 0x7fff80000000 <= ar_sptop ar <= 2 ^ 47 ->
  ablock_range L ar q n -> blocks_apart q n LB -> fframes_apart q n FF -> q <= a < q + n -> ~ aclient L ar LB FF sp scr a.
Proof.
  intros HH SPT (B0 & B1 & B2 & B3 & B4 & B5) BA FA Ha Hc.
  pose proof (aiob_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _).
  rewrite (aly_img_lo L C LY), (aly_img_hi L C LY) in B1. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in B5.
  destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]].
  - destruct Hc as (b & Hb & X). specialize (BA b Hb). lia.
  - lia.
  - rewrite (aly_img_lo L C LY), (aly_img_hi L C LY) in Hc. lia.
  - destruct Hc as (f & Hf & X). specialize (FA f Hf). lia.
  - unfold in_shadow_of, S, SB in Hc. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
  - destruct Hc as (f & Hf & X). pose proof (WF f Hf) as (Y1 & Y & _). unfold in_shadow_of, S, SB in X. unfold app_mem, FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in FSAPP. lia.
  - destruct Hc as (b & Hb & X). pose proof (proj1 (WB b Hb)) as (Y0 & _ & _ & _ & Y & Y2). unfold in_shadow_of, S, SB in X. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Y2. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

End WithIface.
End SCFG_1.
End L5SA.
