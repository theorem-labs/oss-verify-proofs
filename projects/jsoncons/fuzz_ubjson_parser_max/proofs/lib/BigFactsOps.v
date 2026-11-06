(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import BigModel BigFactsBase.
Import ListNotations.
Unset Lia Cache. Unset Nra Cache. Unset Nia Cache.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__BigFactsOps () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BigFactsBase."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BigFactsOps."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BigFactsOps.ShlFacts."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BigModel."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BigModel.W."; "Stdlib.Arith.PeanoNat.Nat."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."], [["0B"; "1O"; "1S"; "1app"; "1bool"; "1cons"; "1false"; "1length"; "1list"; "1nat"; "1nil"; "1true"; "1tt"; "1unit"; "2True"; "2and"]; ["2eq"; "2ex"; "2iff"; "2not"; "2or"; "3add"; "3mul"; "3sub"; "4le"; "4lt"; "5firstn"; "5skipn"; "6Z"; "0K"; "0N"; "0P"]; ["7val"; "7wordZ"; "7words_ok"; "8BB"; "9shlG"; "8cmp3"; "8mspec"; "8nallocs"; "8okN"; "8reduced"; "8reduced_ws"; "8wf"; ":ECatch"; ":EFree"; ":EThrow"; ":NORM_FUEL"]; [";M"; ";l_bit"; ";land"; ";shl"; ";shr"; ":add_carry_loop"; ":alloc"; ":capacity"; ":compare"; ":compare_loop"; ":copy"; ":destroy"; ":emit"; ":event"; ":exn"; ":norm_count"]; [":nth_w"; ":reduce"; ":reduce_loop"; ":reserve"; ":resize"; ":round_up"; ":s_alloc"; ":s_blk"; ":s_cap"; ":s_neg"; ":s_words"; ":set_neg"; ":set_words"; ":shl_loop"; ":shr_bits"; ":shr_loop"]; [":site"; ":size"; ":sto"; ":sto_empty"; ":sto_of_word"; ":upd"; ":words"; ":zeros"; "<div"; "<modulo"; "=last"; "=removelast"; ">add"; ">div"; ">eqb"; ">land"]; [">le"; ">lor"; ">lt"; ">ltb"; ">modulo"; ">mul"; ">of_nat"; ">pow"; ">sub"; ">testbit"; "0a"; "0b"; "0blk"; "0carry"; "0d"; "0e"]; ["0f"; "0fuel"; "0hi"; "0i"; "0j"; "0k"; "0k1"; "0lo"; "0m"; "0mask"; "0n"; "0orig"; "0r"; "0s"; "0s'"; "0src"]; ["0v"; "0w"; "0ws"; "0ws'"; "0x"; "0x'"; "0xs"; "0y"; "0ys"]]).
Definition wf (s : sto) : Prop :=
words_ok (s_words s) /\ (size s <= capacity s)%nat /\ (s_alloc s = false -> s_cap s = inlined_capacity).
Definition reduced_ws (ws : words) : Prop := ws = [] \/ last ws 0 <> 0.
Definition reduced (s : sto) : Prop := reduced_ws (s_words s).
Lemma wf_empty : ltac2:(TCodec.tc2 tcn__BigFactsOps "3&Q;&RC%211").
Proof. unfold wf, sto_empty, size, capacity, inlined_capacity; simpl. split. constructor. split. lia. auto. Qed.
Lemma wf_of_word : ltac2:(TCodec.tc2 tcn__BigFactsOps ";'L&Q1r1%211&Q;&RDr2%211%411p061pX4:1").
Proof. intros w. unfold wf, sto_of_word, size, capacity, inlined_capacity; simpl. intros. destruct (Z.eqb_spec w 0); simpl.
split. constructor. split. lia. auto. split. constructor. auto. constructor. split. lia. auto. Qed.
Lemma reduced_empty : ltac2:(TCodec.tc2 tcn__BigFactsOps "3&Q9&RC%211"). Proof. left; reflexivity. Qed.
Lemma reduced_of_word : ltac2:(TCodec.tc2 tcn__BigFactsOps "7'L&Q9&RDr1%211%411pX461").
Proof. intros w. unfold reduced, reduced_ws, sto_of_word; simpl. destruct (Z.eqb_spec w 0); simpl; auto. Qed.
Lemma val_of_word : ltac2:(TCodec.tc2 tcn__BigFactsOps ";'L'@&Q0&R:&RDr1%211%411%611%83914pX4:1").
Proof. intros w. unfold sto_of_word. cbn [s_words]. destruct (Z.eqb_spec w 0). subst; reflexivity. rewrite val_cons, val_nil. lia. Qed.
Lemma size_of_word w : size (sto_of_word w) = if w =? 0 then 0%nat else 1%nat.
Proof. unfold sto_of_word, size; simpl. destruct (w =? 0); reflexivity. Qed.
Lemma wf_set_neg : ltac2:(TCodec.tc2 tcn__BigFactsOps "<'RB'4&Q;r2%211&R;r3%2214%611p051pVH91pWL;1").
Proof. intros s b. unfold wf, set_neg, size, capacity; simpl; tauto. Qed.
Lemma wf_set_words : ltac2:(TCodec.tc2 tcn__BigFactsOps "I'RB&RF&Q;r2%211&Q2%113'H&7'Lr3%3221&QGr4%211%8241&R<r5%2215%A11p051p0?1p0B1pX6F1pWLH1").
Proof. intros s ws. unfold wf, set_words, size, capacity; simpl. intuition. Qed.
Lemma reduced_set_neg : ltac2:(TCodec.tc2 tcn__BigFactsOps "<'RB'4&Q9r2%211&R;r3%2214%611p051pVH91pWL;1"). Proof. intros s b. unfold reduced; simpl; auto. Qed.
Lemma last_nth : ltac2:(TCodec.tc2 tcn__BigFactsOps "H'8'L%211&C'@r1(:%116%43631%611&RJr2z%33<21&R0&G&7%12@6u1%4221%6291%A3D81p0=1pX6E1").
Proof. intros ws. induction ws as [|a ws IH]; intros. congruence. destruct ws as [|b ws']. reflexivity.
simpl length. replace (S (S (length ws')) - 1)%nat with (S (length ws')) by lia.
unfold nth_w. simpl nth. change (last (b::ws') 0 = nth_w (b::ws') (length ws')). rewrite IH by congruence. simpl length. f_equal. lia. Qed.
Lemma reduced_ws_top : ltac2:(TCodec.tc2 tcn__BigFactsOps "J&RF&Q:r1%211&C'@r2(:'L%211%53:41%711&R0r3&G&7%1283u1%4221%7261z%@3=21%B11p0<1p0E1pX6I1").
Proof. intros ws. intros [->|H] Hn. congruence. rewrite <- last_nth; auto. Qed.
Lemma reduced_ws_intro : ltac2:(TCodec.tc2 tcn__BigFactsOps "J'8'L%211&C'@r1(:%116%43631%611&R0r2&G&7%12=3u1%4221%7261z%?3B21%A11p0<1&Q:%11<p031pX6G1").
Proof. intros ws. intros. destruct ws. left; auto. right. rewrite last_nth. apply H. congruence. congruence. Qed.
Lemma reduced_val_lower : ltac2:(TCodec.tc2 tcn__BigFactsOps "Q2&RF&Q2r1%211&Q:r2%211&C'@r3(:'L%211%53=41%711&S0&S7&Q@&S8&S6&7r4%22;1%411+1%7221%:291&Q0%117%>231p0@1p0I1p0M1pX6Q11").
Proof. intros ws. intros. rewrite val_removelast by auto. pose proof (reduced_ws_top ws H0 H1). rewrite <- last_nth in H2 by auto.
assert (wordZ (last ws 0)). { rewrite last_nth by auto. apply words_ok_nth; auto. }
assert (words_ok (removelast ws)). { rewrite (app_removelast_last 0 H1) in H. apply words_ok_app_inv in H. tauto. }
pose proof (val_nonneg _ H4). unfold wordZ in H3. pose proof (Z.pow_pos_nonneg W.M (Z.of_nat (length ws) - 1) M_pos). nia. Qed.
Lemma reduced_val_zero : ltac2:(TCodec.tc2 tcn__BigFactsOps "F&RF&Q2r1%211&Q:r2%211'@'L&Q0r3%211z%63521r4(:%118%:3A31p051p0=1p0A1pX6E1").
Proof. intros ws. intros. destruct (list_eq_dec Z.eq_dec ws []); auto. exfalso.
pose proof (reduced_val_lower ws H H0 n). assert (0 < W.M ^ (Z.of_nat (length ws) - 1)). { apply Z.pow_pos_nonneg. apply M_pos. destruct ws. congruence. simpl length. lia. } lia. Qed.
Lemma size_le_of_val : ltac2:(TCodec.tc2 tcn__BigFactsOps "M&RF'9&Q2r2%211&Q:r3%211&S2&Q0r4%211&S7&Q@&S6%119%4231%9261'H&7'Lr5%3221%521=p071p0B1p0F1pW<J1pX6L1").
Proof. intros ws k. intros. destruct (list_eq_dec Z.eq_dec ws []). subst; simpl; lia.
pose proof (reduced_val_lower ws H H0 n).
destruct (Nat.le_gt_cases (length ws) k); auto. exfalso.
assert (W.M ^ Z.of_nat k <= W.M ^ (Z.of_nat (length ws) - 1)). { apply Z.pow_le_mono_r. apply M_pos. lia. } lia. Qed.
Lemma size_ge_of_val : ltac2:(TCodec.tc2 tcn__BigFactsOps "I&RF'9&Q2r2%211&S0&S7&Q@&S6%116%4231&Q0r3%211%9241&I&7'Lr4%3221%5281p071p0B1pW<F1pX6H1").
Proof. intros ws k. intros. pose proof (val_bound ws H). destruct (Nat.lt_ge_cases k (length ws)); auto. exfalso.
assert (W.M ^ Z.of_nat (length ws) <= W.M ^ Z.of_nat k). { apply Z.pow_le_mono_r. apply M_pos. lia. } lia. Qed.
Lemma top_word_of_val : ltac2:(TCodec.tc2 tcn__BigFactsOps "QC&RF'9'L&Q2r3%211&Q:r4%211'?&S0+1%2218&S2&Q@%22;1%7241&S5&S7&S6r5%211%4281%62@1&Q0r6%211%A241&RL%12FB%=218%B251%G251'@&7r7%22Q21(2%11=%63Q631&R0%126@%93Q81F%Q2241p0<1p0M1p0Q61p0Q:1pVNQ>1pW<Q@1pX6QB1").
Proof. intros ws k d. intros Hw Hr Hd [Hlo Hhi]. pose proof (Z.pow_pos_nonneg W.M (Z.of_nat k) M_pos) as Pk.
assert (L1: (k < length ws)%nat). { apply size_ge_of_val; auto. nia. }
assert (L2: (length ws <= S k)%nat). { apply size_le_of_val; auto. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. pose proof M_pos. nia. }
assert (L: length ws = S k) by lia. split; auto.
pose proof (val_single_nth ws k L1) as E.
assert (Sk: skipn (S k) ws = []). { apply length_zero_iff_nil. rewrite length_skipn. lia. }
rewrite Sk, val_nil, Z.mul_0_r, Z.add_0_r in E.
pose proof (val_bound (firstn k ws) (words_ok_firstn k ws Hw)) as B0. rewrite length_firstn, Nat.min_l in B0 by lia.
pose proof (words_ok_nth ws k Hw) as Wk. unfold wordZ in Wk.
set (w := nth_w ws k) in *. set (V0 := val (firstn k ws)) in *. set (P := W.M ^ Z.of_nat k) in *.
assert (~ w <= d - 1). { intro. assert (P * w <= P * (d - 1)) by nia. nia. }
assert (~ d + 1 <= w). { intro. assert (P * (d + 1) <= P * w) by nia. nia. }
lia. Qed.
Definition ev_ok (B : Z) (e : event) : Prop :=
match e with EAlloc _ b _ => 0 <= b <= B | _ => True end.
Fixpoint nallocs (l : list event) : nat :=
match l with [] => O | EAlloc _ _ _ :: t => S (nallocs t) | _ :: t => nallocs t end.
Lemma nallocs_app : ltac2:(TCodec.tc2 tcn__BigFactsOps "B'8'QM%211'@'9&Q7&3r2r1%33821%511&E%715%815%3221%<3;51pVH>1pVF?1").
Proof. intros a b. induction a as [|e a IH]; simpl; auto. destruct e; simpl; rewrite IH; auto. Qed.
Definition post {A} (m : M A) (s0 : st) (P : A -> Prop) (K : nat) (B : Z) : Prop :=
P (fst (m s0)) /\
exists l, st_evs (snd (m s0)) = rev l ++ st_evs s0 /\ Forall (ev_ok B) l /\ (nallocs l <= K)%nat
/\ (st_next s0 <= st_next (snd (m s0)))%nat.
Definition mspec {A} (m : M A) (P : A -> Prop) (K : nat) (B : Z) : Prop := forall s0, post m s0 P K B.
Lemma mspec_ret {A} (a : A) (P : A -> Prop) K B : P a -> mspec (ret a) P K B.
Proof. intros H s0. unfold post, ret; simpl. split; auto. exists []. simpl. repeat split; auto; try lia. Qed.
Lemma mspec_emit_free : ltac2:(TCodec.tc2 tcn__BigFactsOps "H'9'L'=!pX:21r3(<%211&Q6&QL(Q=r6r5%3221%511r4r2%95?32<1p0;1p2B1pQLD1pR0A1pWFE1pVJG1").
Proof. intros blk n P K B. intros H s0. unfold post, emit; simpl. split; auto. exists [EFree blk n]. simpl. repeat split; auto; try lia. all: try (constructor; simpl; auto; lia). Qed.
Lemma mspec_emit_throw : ltac2:(TCodec.tc2 tcn__BigFactsOps "G'QN'=!pX:21'9'Lr3(<%211&Q6&QL(Q>r5%211%411r4r2%85@32;1p0:1p2>1pQL@1pR0B1pW0F1").
Proof. intros e P K B. intros H s0. unfold post, emit; simpl. split; auto. exists [EThrow e]. simpl. repeat split; auto; try lia. all: try (constructor; simpl; auto; lia). Qed.
Lemma mspec_emit_catch : ltac2:(TCodec.tc2 tcn__BigFactsOps "C'=!pX:21'9'Lr3(<%211&Q6&QL(Q<%211r4r2%65>3291p081p2<1pQL>1pR0@1").
Proof. intros P K B. intros H s0. unfold post, emit; simpl. split; auto. exists [ECatch]. simpl. repeat split; auto; try lia. all: try (constructor; simpl; auto; lia). Qed.
Lemma mspec_alloc : ltac2:(TCodec.tc2 tcn__BigFactsOps "H'L'R@'?&S0zr3%3221r1%5231%7231&Q6'9&QFr4%2219'>q051u1r2%9585321p0;1p2E1pX4E1pWFG1").
Proof. intros n w B. intros H s0. unfold post, alloc, bind, fresh, emit, ret; simpl. split; auto.
exists [EAlloc (st_next s0) n w]. simpl. repeat split; auto; try lia. all: try (constructor; simpl; auto; lia). Qed.
Lemma mspec_bind {A B'} (m : M A) (k : A -> M B') P Q K1 K2 B :
mspec m P K1 B -> (forall a, P a -> mspec (k a) Q K2 B) -> mspec (bind m k) Q (K1 + K2) B.
Proof. intros Hm Hk s0. unfold post, bind. specialize (Hm s0). unfold post in Hm.
destruct (m s0) as [a s1]. simpl in Hm. destruct Hm as [Pa (l1 & E1 & F1 & N1 & X1)].
specialize (Hk a Pa s1). unfold post in Hk. destruct (k a s1) as [b s2]. simpl in *.
destruct Hk as [Qb (l2 & E2 & F2 & N2 & X2)]. split; auto. exists (l1 ++ l2).
rewrite E2, E1, rev_app_distr, <- app_assoc. repeat split; auto. apply Forall_app; auto. rewrite nallocs_app; lia. lia. Qed.
Lemma mspec_weaken {A} (m : M A) (P Q : A -> Prop) K K' B B' :
mspec m P K B -> (forall a, P a -> Q a) -> (K <= K')%nat -> B <= B' -> mspec m Q K' B'.
Proof. intros Hm HPQ HK HB s0. specialize (Hm s0). unfold post in *. destruct (m s0) as [a s1]; simpl in *.
destruct Hm as [Pa (l & E & F & N & X)]. split; auto. exists l; repeat split; auto.
eapply Forall_impl. 2: exact F. intros e. destruct e; simpl; auto; lia. lia. Qed.
Lemma mspec_if {A} (b : bool) (m1 m2 : M A) P K B :
(b = true -> mspec m1 P K B) -> (b = false -> mspec m2 P K B) -> mspec (if b then m1 else m2) P K B.
Proof. destruct b; auto. Qed.
Lemma mspec_conj {A} (m : M A) (P Q : A -> Prop) K B :
mspec m P K B -> (forall s0, Q (fst (m s0))) -> mspec m (fun a => P a /\ Q a) K B.
Proof. intros Hm HQ s0. specialize (Hm s0). specialize (HQ s0). unfold post in *. destruct (m s0); simpl in *. tauto. Qed.
Lemma mspec_bind' {A B'} (m : M A) (k : A -> M B') P Q K1 K B :
mspec m P K1 B -> (forall a, P a -> mspec (k a) Q (K - K1) B) -> (K1 <= K)%nat -> mspec (bind m k) Q K B.
Proof. intros. replace K with (K1 + (K - K1))%nat by lia. eapply mspec_bind; eauto. Qed.
Ltac mstep L := eapply mspec_bind'; [ apply L | intros | simpl; lia ].
Lemma round_up_gt : ltac2:(TCodec.tc2 tcn__BigFactsOps "7'9&Ir1&R5%112%4231pWF61").
Proof. intros n. unfold round_up. pose proof (Nat.mod_upper_bound n 8). lia. Qed.
Lemma round_up_le : ltac2:(TCodec.tc2 tcn__BigFactsOps ":'9'H&R5r1%211&Eu8%2241%7241pWF91").
Proof. intros n. unfold round_up. lia. Qed.
Lemma round_up_mult8 : ltac2:(TCodec.tc2 tcn__BigFactsOps ";'9'@&RI&R5r1%211u8%5221(1%83921pWF:1").
Proof. intros n. unfold round_up. rewrite (Nat.div_mod_eq n 8) at 1. pose proof (Nat.mod_upper_bound n 8).
replace (8 * (n / 8) + n mod 8 + (8 - n mod 8))%nat with ((n / 8 + 1) * 8)%nat by lia. apply Nat.Div0.mod_mul. Qed.
Lemma round_up_eq : ltac2:(TCodec.tc2 tcn__BigFactsOps "?'9'@&R5r1%211&Fu8&E&RH%1263u1%4221%7261%<3=91pWF>1").
Proof. intros n. unfold round_up. pose proof (Nat.div_mod_eq n 8). pose proof (Nat.mod_upper_bound n 8). lia. Qed.
Lemma round_up_mono : ltac2:(TCodec.tc2 tcn__BigFactsOps "='9'Hr2r1%3221&R5r3%211%316%8221p061pVH;1pVF<1").
Proof. intros a b. intros. rewrite !round_up_eq. pose proof (Nat.Div0.div_le_mono a b 8 H). lia. Qed.
Definition BB (N : nat) : Z := 8 * Z.of_nat (round_up N).
Definition okN (N : nat) (s : sto) : Prop := wf s /\ (capacity s <= round_up N)%nat.
Lemma okN_wf : ltac2:(TCodec.tc2 tcn__BigFactsOps ";'9'RB&Q8r2r1%3221&Q;%114p031pWL81pQN:1"). Proof. intros N s. intros [H _]; auto. Qed.
Lemma okN_size : ltac2:(TCodec.tc2 tcn__BigFactsOps "@'9'RB&Q8r2r1%3221'H&RA%115&R5r3%211%6241p081pWL=1pQN?1").
Proof. intros N s. intros [[_ [H _]] H']. lia. Qed.
Lemma okN_words : ltac2:(TCodec.tc2 tcn__BigFactsOps "='9'RB&Q8r2r1%3221&Q2&R:%115%311p051pWL:1pQN<1"). Proof. intros N s. intros [[H _] _]; auto. Qed.
Lemma okN_empty : ltac2:(TCodec.tc2 tcn__BigFactsOps "6'9&Q8r1&RC%3221pQN51").
Proof. intros N. split. apply wf_empty. unfold capacity, sto_empty, inlined_capacity; simpl. rewrite round_up_eq. lia. Qed.
Lemma okN_of_word : ltac2:(TCodec.tc2 tcn__BigFactsOps ">'9'L&Q1r1%211&Q8r3&RDr2%211%5241p071pX4;1pQN=1").
Proof. intros N w. intros. split. apply wf_of_word; auto. unfold capacity, sto_of_word, inlined_capacity; simpl. rewrite round_up_eq. lia. Qed.
Lemma okN_set_neg : ltac2:(TCodec.tc2 tcn__BigFactsOps "?'9'RB'4&Q8r3r2%3221r4&R;%1254%7231p051pVH:1pWL<1pQN>1").
Proof. intros N s b. intros [H1 H2]. split. apply wf_set_neg; auto. unfold capacity, set_neg in *; simpl in *; auto. Qed.
Lemma okN_set_words : ltac2:(TCodec.tc2 tcn__BigFactsOps "L'9'RB&RF&Q8r3r2%3221&Q2%113'H&7'L%2218&QGr4%211%7241r6&R<r5%2216%B241p061p0?1p0B1pX6G1pWLI1pQNK1").
Proof. intros N s ws. intros [H1 H2] Hw Hl. split. apply wf_set_words; auto. unfold capacity, set_words in *; simpl in *; auto. Qed.
Lemma capacity_set_words : ltac2:(TCodec.tc2 tcn__BigFactsOps ">'RB&RF'@'9&QG&R<r2r1%3221%511%614%93821pX6;1pWL=1"). Proof. intros s ws. reflexivity. Qed.
Lemma capacity_set_neg : ltac2:(TCodec.tc2 tcn__BigFactsOps ">'RB'4'@'9&QG&R;r2r1%3221%511%614%93821pVH;1pWL=1"). Proof. intros s b. reflexivity. Qed.
Lemma size_set_words : ltac2:(TCodec.tc2 tcn__BigFactsOps "@'RB&RF'@'9&RA&R<r2r1%3221%511&7'L%2215%;3:41pX6=1pWL?1"). Proof. intros s ws. reflexivity. Qed.
Lemma size_set_neg : ltac2:(TCodec.tc2 tcn__BigFactsOps ">'RB'4'@'9&RA&R;r2r1%3221%511%614%93821pVH;1pWL=1"). Proof. intros s b. reflexivity. Qed.
Lemma reserve_mspec : ltac2:(TCodec.tc2 tcn__BigFactsOps "Q?'9'RB&Q8r3r2%3221'Hr4%2241&Q6&R3%1248'?r6r1%=221'@&RF&R:%115r5%311%63531'4&R9%11;%216%;3421&QG%11?%H2G1%31;%J213%E231%F271%G2=1%H2E1qWNQ41u1&Q3%11D%Q05Q8N431p0Q21p0Q61pWFQ<1pWLQ<1pQNQ>1").
Proof. intros N s n.
intros Hok Hn. unfold reserve. destruct (Nat.ltb_spec (capacity s) n).
2:{ apply mspec_ret. repeat split; auto; try lia. all: destruct Hok as [[? [? ?]] ?]; auto. }
eapply mspec_bind'. apply mspec_alloc. unfold BB. split. lia. apply Z.mul_le_mono_nonneg_l. lia. apply Nat2Z.inj_le. apply round_up_mono; auto.
2: lia. intros blk _. simpl.
eapply mspec_bind' with (P := fun _ => True) (K1 := 0%nat). destruct (s_alloc s). apply mspec_emit_free; auto. apply mspec_ret; auto. 2: lia.
intros u _. apply mspec_ret. destruct Hok as [[Hw [Hsz Hcap]] Hc].
unfold okN, wf, capacity, size in *; simpl in *. pose proof (round_up_gt n). pose proof (round_up_mono n N Hn).
repeat split; auto; try lia. all: try (intros; congruence).
Qed.
Lemma resize_words_eq n (ws : words) :
(if (n <=? length ws)%nat then firstn n ws else ws ++ zeros (n - length ws)) = firstn n ws ++ zeros (n - length ws).
Proof. destruct (Nat.leb_spec n (length ws)).
replace (n - length ws)%nat with 0%nat by lia. cbn. rewrite app_nil_r. reflexivity.
rewrite firstn_all2 by lia. reflexivity. Qed.
Lemma resize_mspec : ltac2:(TCodec.tc2 tcn__BigFactsOps "QK'9'RB&Q8r3r2%3221'Hr4%2241&Q6&R4%1248'?r6r1%=221'@&RF&R:%115&3'L&Jr5%611%334B1&RG&G&RA%116%32G1%511%<3;71%A3@>1%61D%C3Q31L'4&R9%11H%21@%H3421&QG%11C%21M%Q6221%Q1251%Q22;1%Q32>1%Q42Q11qWNQ@1u1&Q3%11M%Q<5QDQ:431p0Q>1p0QB1pWFQH1pWLQH1pQNQJ1").
Proof. intros N s n.
intros Hok Hn. unfold resize. eapply mspec_bind'. apply reserve_mspec; eauto. 2: lia.
intros s1 (Hok1 & Hw1 & Hneg1 & Hc1 & Hc2). unfold size. rewrite resize_words_eq. rewrite Hw1.
assert (Hlen: length (firstn n (s_words s) ++ zeros (n - length (s_words s))) = n).
{ rewrite length_app, length_firstn, zeros_length. lia. }
apply mspec_ret. split. apply okN_set_words; auto. apply words_ok_app. apply words_ok_firstn. apply (okN_words N); auto. apply words_ok_zeros.
rewrite Hlen; lia.
cbn [s_words set_words s_neg]. repeat split; auto.
Qed.
Lemma removelast_firstn : ltac2:(TCodec.tc2 tcn__BigFactsOps "A&RF'@'8'L%211&RKr1%2241&J&G&7%1285u1%4221%63;18%>3;81pX6@1").
Proof. intros ws. induction ws as [|a ws IH]. reflexivity. destruct ws as [|b ws']. reflexivity.
simpl length. change (removelast (a :: b :: ws')) with (a :: removelast (b :: ws')). rewrite IH.
simpl length. replace (S (S (length ws')) - 1)%nat with (S (S (length ws') - 1))%nat by lia. reflexivity. Qed.
Lemma reduce_loop_prefix : ltac2:(TCodec.tc2 tcn__BigFactsOps "I'9'8'L%211'A'?'Hr1&7r2%2281%5241'@&RF&R2r3%2217&J%13@;9%73631%?291qWBE1%B2F1pX6D1pW4H1").
Proof. intros fuel ws. revert ws; induction fuel as [|f IH]; intros ws; simpl.
exists (length ws). split. lia. rewrite firstn_all; auto.
destruct ws as [|w t]. exists 0%nat. simpl. split; auto.
destruct (Z.eqb_spec (last (w :: t) 0) 0).
- destruct (IH (removelast (w :: t))) as (m & Hm & E). rewrite E. rewrite removelast_firstn in *.
rewrite length_firstn in Hm. exists m. split. simpl length in *. lia. rewrite firstn_firstn. f_equal. simpl length in *. lia.
- exists (length (w :: t)). split. lia. rewrite firstn_all. reflexivity. Qed.
Lemma reduce_loop_val : ltac2:(TCodec.tc2 tcn__BigFactsOps ">'9&RF'@'L&Q0&R2r2r1%3221%511%613%93821pX6;1pW4=1").
Proof. intros fuel ws. revert ws; induction fuel as [|f IH]; intros ws; simpl. auto.
destruct ws as [|w t]. auto. destruct (Z.eqb_spec (last (w :: t) 0) 0).
rewrite IH. rewrite (val_removelast (w :: t)) by congruence. rewrite e. lia. auto. Qed.
Lemma reduce_loop_reduced : ltac2:(TCodec.tc2 tcn__BigFactsOps "B'9'8'L%211'H&7r1%2251r2%5221&Q:&R2r3%2215%411p061pX6=1pW4A1").
Proof. intros fuel ws. revert ws; induction fuel as [|f IH]; intros ws Hl; simpl.
destruct ws. left; auto. simpl in Hl; lia.
destruct ws as [|w t]. left; auto. destruct (Z.eqb_spec (last (w :: t) 0) 0).
apply IH. rewrite removelast_firstn, length_firstn. simpl length in *. lia.
right. auto. Qed.
Lemma reduce_loop_id : ltac2:(TCodec.tc2 tcn__BigFactsOps ">'9&RF&Q:r1%211'@&R2r3r2%3221%53912p071pX6;1pW4=1").
Proof. intros fuel ws. intros [->|H]; destruct fuel; simpl; auto. destruct ws; auto. destruct (Z.eqb_spec (last (z :: ws) 0) 0); auto. congruence. Qed.
Lemma reduce_loop_length : ltac2:(TCodec.tc2 tcn__BigFactsOps ">'9&RF'H&7'L&R2r2r1%3221%6251%7263%9221pX6;1pW4=1").
Proof. intros fuel ws. destruct (reduce_loop_prefix fuel ws) as (m & Hm & E). rewrite E, length_firstn. lia. Qed.
Lemma reduce_loop_words_ok : ltac2:(TCodec.tc2 tcn__BigFactsOps "='9&RF&Q2r1%211&R2r3r2%3221%711p061pX6:1pW4<1").
Proof. intros fuel ws. destruct (reduce_loop_prefix fuel ws) as (m & Hm & E). rewrite E. apply words_ok_firstn. Qed.
Lemma reduce_loop_nth : ltac2:(TCodec.tc2 tcn__BigFactsOps "G'9&RF&Ir1&7'L&R2r3r2%3221%6251%9281'@&R0r4%9218%3218%42:9%63=21p081pW8D1pX6D1pW4F1").
Proof. intros fuel ws i. destruct (reduce_loop_prefix fuel ws) as (m & Hm & E). rewrite E. rewrite length_firstn. intros.
unfold nth_w. rewrite <- (firstn_skipn m ws) at 2. rewrite app_nth1. auto. rewrite length_firstn. lia. Qed.
Lemma reduce_words : ltac2:(TCodec.tc2 tcn__BigFactsOps "?'RB'@&RF&R:&R1r1%211%411&R2&RA%115%816%4221%<3;61pWL>1"). Proof. intros s. reflexivity. Qed.
Lemma reduce_alloc : ltac2:(TCodec.tc2 tcn__BigFactsOps ";'RB'@'4&R6&R1r1%211%411%513%83721pWL:1"). Proof. intros s. reflexivity. Qed.
Lemma reduce_cap : ltac2:(TCodec.tc2 tcn__BigFactsOps ";'RB'@'9&R8&R1r1%211%411%513%83721pWL:1"). Proof. intros s. reflexivity. Qed.
Lemma reduce_blk : ltac2:(TCodec.tc2 tcn__BigFactsOps ";'RB'@'9&R7&R1r1%211%411%513%83721pWL:1"). Proof. intros s. reflexivity. Qed.
Lemma capacity_reduce : ltac2:(TCodec.tc2 tcn__BigFactsOps ";'RB'@'9&QG&R1r1%211%411%513%83721pWL:1"). Proof. intros s. reflexivity. Qed.
Lemma reduce_neg s : s_neg (reduce s) = if (size (reduce s) =? 0)%nat then false else s_neg s.
Proof. reflexivity. Qed.
Lemma reduce_val : ltac2:(TCodec.tc2 tcn__BigFactsOps ">'RB'@'L&Q0&R:&R1r1%211%411%611%614%811%;3:31pWL=1").
Proof. intros s. rewrite reduce_words. apply reduce_loop_val. Qed.
Lemma reduce_reduced : ltac2:(TCodec.tc2 tcn__BigFactsOps "7'RB&Q9&R1r1%211%411pWL61").
Proof. intros s. unfold reduced. rewrite reduce_words. apply reduce_loop_reduced. unfold size; lia. Qed.
Lemma reduce_size_le : ltac2:(TCodec.tc2 tcn__BigFactsOps ":'RB'H&RA&R1r1%211%411%513%7221pWL91").
Proof. intros s. unfold size at 1. rewrite reduce_words. apply reduce_loop_length. Qed.
Lemma reduce_okN : ltac2:(TCodec.tc2 tcn__BigFactsOps "='9'RB&Q8r2r1%3221r3&R1%115%7231p051pWL:1pQN<1").
Proof. intros N s. intros [[Hw [Hs Hc]] Hcap]. pose proof (reduce_size_le s). split. split. rewrite reduce_words. apply reduce_loop_words_ok; auto.
rewrite capacity_reduce. split. lia. rewrite reduce_alloc, reduce_cap. auto. rewrite capacity_reduce. auto. Qed.
Lemma reduce_id : ltac2:(TCodec.tc2 tcn__BigFactsOps "I'RB&Q9r1%211'D'@'4&R9r2%211(6%63521&I(1&RA%117%4231%=261&R1r3%211%@3E12p051p0D1pWLH1").
Proof. intros s. intros Hr Hn. unfold reduce. rewrite (reduce_loop_id _ _ Hr). destruct s as [al ng ws cp bk]; simpl in *.
f_equal. unfold size in Hn; simpl in Hn. destruct (Nat.eqb_spec (length ws) 0); auto. destruct Hn; auto. lia. Qed.
Lemma reduce_nil_iff : ltac2:(TCodec.tc2 tcn__BigFactsOps "I'RB&Q2&R:r1%211%411&B'@&RF&R1r2%211%:11(:'L%211%93841&Q0%@18%211z%>3721%@261p0B1pWLH1").
Proof. intros s. intros Hw. split. intros E. rewrite <- reduce_val, E. reflexivity.
intros V. apply reduced_val_zero. rewrite reduce_words. apply reduce_loop_words_ok; auto. apply reduce_reduced. rewrite reduce_val; auto. Qed.
Lemma copy_mspec : ltac2:(TCodec.tc2 tcn__BigFactsOps "Q<'9'RB&Q8r2r1%3221&Q6&QJ%115'?r4%9217'@&RF&R:%11;r3%311%63531'4&R9%11A%216%;3421&R6%11E%21:%?3821&QG%11I%21>%C3O21%G251%H2:1%I2@1%J2H1qWNQ31u1&Q3%11G%Q25Q7Q0431p0Q41pX0Q91pQNQ;1").
Proof. intros N src.
intros Hok. unfold copy. destruct (s_alloc src) eqn:A.
- eapply mspec_bind'. apply mspec_alloc. destruct Hok as [[Hw [Hs Hc]] Hcap]. unfold capacity in Hcap. rewrite A in Hcap. unfold BB. split. lia. nia.
2: lia. intros blk _. apply mspec_ret. destruct Hok as [[Hw [Hs Hc]] Hcap]. unfold okN, wf, capacity, size in *; simpl in *. rewrite A in *.
repeat split; auto; try (intros; congruence).
- apply mspec_ret. destruct Hok as [[Hw [Hs Hc]] Hcap]. unfold okN, wf, capacity, size in *; simpl in *. rewrite A in *.
repeat split; auto; try lia. all: try (rewrite (Hc eq_refl) in Hs; auto).
Qed.
Lemma assign_mspec N dst src : okN N dst -> okN N src -> (size src <= N)%nat ->
mspec (assign dst src) (fun s' => okN N s' /\ s_words s' = s_words src /\ size s' = size src
/\ s_neg s' = (if (0 <? size src)%nat then s_neg src else s_neg dst)
/\ (capacity dst <= capacity s')%nat) 1 (BB N).
Proof.
intros Hd Hs Hn. unfold assign. eapply mspec_bind'. apply resize_mspec; eauto. 2: lia.
intros s1 (Hok1 & Hw1 & Hsz1 & Hneg1 & Hc1). apply mspec_ret. destruct (Nat.ltb_spec 0 (size src)).
- pose proof (okN_words N src Hs) as Hws. destruct Hok1 as [[Hw [Hsz Hc]] Hcap]. clear Hd Hs.
unfold okN, wf, size, capacity in *. cbn [s_words s_neg s_alloc s_cap] in *. repeat split; auto; try lia.
- assert (E: s_words src = []). { destruct (s_words src) eqn:E; auto. unfold size in H; rewrite E in H; simpl in H; lia. }
assert (E1: s_words s1 = []). { apply length_zero_iff_nil. unfold size in *. lia. }
split. auto. rewrite E1, E. unfold size. rewrite E1, E. repeat split; auto.
Qed.
Lemma destroy_mspec : ltac2:(TCodec.tc2 tcn__BigFactsOps "C'RB'=!p021'Lr2(<%211&Q6&QKr4%211r3(1%65=3219p081p2<1pR0>1pWLB1").
Proof. intros s P B. intros. unfold destroy. destruct (s_alloc s). apply mspec_emit_free; auto. apply mspec_ret; auto. Qed.
Lemma firstn_S_nth : ltac2:(TCodec.tc2 tcn__BigFactsOps "N&RF'9&Ir1&7'Lr2%3221%6251'@'8%116&J(2%118r3%43;21&3%63=<3(5&R0%126?(:%11B%53C31%83D71%A3?:1p0C1pW8K1pX6M1").
Proof. intros ws i. revert i; induction ws as [|w ws IH]; intros [|i] H; simpl in *; try lia; auto.
unfold nth_w. simpl. f_equal. specialize (IH i). unfold nth_w in IH. rewrite <- IH by lia. reflexivity. Qed.
Lemma val_firstn_S : ltac2:(TCodec.tc2 tcn__BigFactsOps "Q2&RF'9&Ir1&7'Lr2%3221%6251'@&Q0&J(2%117r3%43:21%611&RL%73=<4%911&S5&R0%128@&S7&Q@&S6%11D%4231%8261%<2:1%E3I>1p0G1pW8O1pX6Q11").
Proof. intros ws i. intros. rewrite firstn_S_nth by auto. rewrite val_app, val_cons, val_nil, length_firstn, Nat.min_l by lia. lia. Qed.
Lemma firstn_upd_le : ltac2:(TCodec.tc2 tcn__BigFactsOps "G&RF'9'L'Hr2r3%3221'@'8%117&J&REr5r4%3321:%53=:1%63>;4%:3821p0<1pX2A1pW:C1pW8D1pX6F1").
Proof. intros ws i j v. revert i j; induction ws as [|w ws IH]; intros [|i] [|j] H; simpl; auto; try lia. rewrite IH; auto; lia. Qed.
Lemma val_firstn_all : ltac2:(TCodec.tc2 tcn__BigFactsOps "=&RF'@'L&Q0&J&7r1%2251%43612%611%714%:3921pX6<1").
Proof. intros ws. rewrite firstn_all; auto. Qed.
Lemma mul_loop_inv y orig : wordZ y -> words_ok orig ->
forall f i dig carry ws,
words_ok ws -> wordZ carry -> length ws = length orig -> (i + f < length orig)%nat ->
(forall k, (i <= k)%nat -> nth_w ws k = nth_w orig k) -> dig = nth_w orig i ->
val (firstn i ws) + carry * W.M ^ Z.of_nat i = y * val (firstn i orig) ->
let (ws', c') := mul_loop f i dig carry y ws in
words_ok ws' /\ wordZ c' /\ length ws' = length orig /\
(forall k, (i + f <= k)%nat -> nth_w ws' k = nth_w orig k) /\
val (firstn (i + f) ws') + c' * W.M ^ Z.of_nat (i + f) = y * val (firstn (i + f) orig).
Proof.
intros Hy Ho. induction f as [|f IH]; intros i dig carry ws Hw Hc Hl Hf Hk Hd Hv.
- simpl. rewrite Nat.add_0_r. repeat split; auto; unfold wordZ in *; try lia.
- cbn [mul_loop]. pose proof (words_ok_nth orig i Ho) as Hdig. rewrite <- Hd in Hdig.
pose proof (DDproduct_correct dig y Hdig Hy) as HP. pose proof (DDproduct_hi_bound dig y Hdig Hy) as Hhb.
destruct (DDproduct dig y) as [hi lo]. simpl in Hhb. destruct HP as (Whi & Wlo & EP).
set (wi := W.add lo carry). set (ws1 := upd ws i wi).
pose proof (add_carry lo carry Wlo Hc) as AC. fold wi in AC.
set (c1 := W.b2z (W.ltu wi lo)) in *.
assert (Hc1: 0 <= c1 <= 1) by (apply b2z_range).
assert (Ecarry: W.add hi c1 = hi + c1). { apply add_small; auto. unfold wordZ; rewrite M_val; lia. unfold wordZ in *; lia. }
specialize (IH (S i) (nth_w ws1 (S i)) (W.add hi c1) ws1).
replace (i + S f)%nat with (S i + f)%nat by lia.
destruct (mul_loop f (S i) (nth_w ws1 (S i)) (W.add hi c1) y ws1) as [ws' c'].
apply IH; clear IH.
+ unfold ws1. apply upd_words_ok; auto. apply add_range.
+ rewrite Ecarry. unfold wordZ in *; lia.
+ unfold ws1. rewrite upd_length; auto.
+ lia.
+ intros k Hk2. unfold ws1. rewrite upd_nth_other by lia. apply Hk. lia.
+ unfold ws1. rewrite upd_nth_other by lia. apply Hk. lia.
+ rewrite val_firstn_S. 2: unfold ws1; rewrite upd_length; lia.
rewrite val_firstn_S by lia. unfold ws1 at 1. rewrite firstn_upd_le by lia. unfold ws1. rewrite upd_nth_same by lia.
rewrite Ecarry. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
rewrite <- Hd. nia.
Qed.
Lemma mul_word_mspec N s y : okN N s -> wordZ y -> (S (size s) <= N)%nat ->
mspec (mul_word s y)
(fun s' => okN N s' /\ reduced s' /\ val (s_words s') = val (s_words s) * y /\ (size s' <= S (size s))%nat
/\ s_neg s' = (if (size s' =? 0)%nat then false else s_neg s) /\ (capacity s <= capacity s')%nat)
1 (BB N).
Proof.
intros Hok Hy Hn. unfold mul_word. eapply mspec_bind'. apply resize_mspec; eauto. 2: lia.
intros s1 (Hok1 & Hw1 & Hsz1 & Hneg1 & Hc1).
assert (Horig: s_words s1 = s_words s ++ [0]).
{ rewrite Hw1. unfold size. rewrite firstn_all2 by lia. replace (S (length (s_words s)) - length (s_words s))%nat with 1%nat by lia. reflexivity. }
pose proof (okN_words N s1 Hok1) as Wo. pose proof (okN_words N s Hok) as Ws.
set (orig := s_words s1) in *. set (len0 := size s) in *.
assert (Hlen: length orig = S len0). { subst orig len0. unfold size in Hsz1. exact Hsz1. }
assert (Hdig: nth_w (s_words s) 0 = nth_w orig 0).
{ rewrite Horig. destruct (s_words s). reflexivity. reflexivity. }
pose proof (mul_loop_inv y orig Hy Wo len0 0 (nth_w (s_words s) 0) 0 orig Wo) as INV.
destruct (mul_loop len0 0 (nth_w (s_words s) 0) 0 y orig) as [ws' c'] eqn:EL.
assert (INV' : words_ok ws' /\ wordZ c' /\ length ws' = length orig /\
(forall k, (len0 <= k)%nat -> nth_w ws' k = nth_w orig k) /\
val (firstn len0 ws') + c' * W.M ^ Z.of_nat len0 = y * val (firstn len0 orig)).
{ apply INV; auto. unfold wordZ; rewrite M_val; lia. lia. simpl. lia. }
clear INV. destruct INV' as (W' & Wc' & L' & K' & V').
apply mspec_ret.
assert (Vfin: val (upd ws' len0 c') = val (s_words s) * y).
{ rewrite val_upd by lia. rewrite (K' len0) by lia.
assert (Ho0: nth_w orig len0 = 0). { rewrite Horig. rewrite nth_w_app_r. unfold len0, size. rewrite Nat.sub_diag. reflexivity. unfold len0, size; lia. }
rewrite Ho0. pose proof (val_single_nth ws' len0) as VS. rewrite VS by lia. rewrite (K' len0) by lia. rewrite Ho0.
assert (SK: skipn (S len0) ws' = []). { apply length_zero_iff_nil. rewrite length_skipn. lia. }
rewrite SK, val_nil.
assert (Fo: firstn len0 orig = s_words s). { rewrite Horig. rewrite firstn_app. unfold len0, size. rewrite Nat.sub_diag, firstn_O, firstn_all, app_nil_r. reflexivity. }
rewrite Fo in V'. nia. }
assert (Hok2: okN N (set_words s1 (upd ws' len0 c'))).
{ apply okN_set_words; auto. apply upd_words_ok; auto. rewrite upd_length, L', Hlen. destruct Hok1 as [[_ [Hs _]] _]. unfold size in Hs. rewrite <- Hsz1. exact Hs. }
split. apply reduce_okN; auto.
split. apply reduce_reduced.
split. rewrite reduce_val. cbn [s_words set_words]. exact Vfin.
split. pose proof (reduce_size_le (set_words s1 (upd ws' len0 c'))) as RS. rewrite size_set_words, upd_length, L', Hlen in RS. exact RS.
split. rewrite reduce_neg. cbn [s_neg set_words]. rewrite Hneg1. reflexivity.
rewrite capacity_reduce, capacity_set_words. exact Hc1.
Qed.
Lemma skipn_nth_ext : ltac2:(TCodec.tc2 tcn__BigFactsOps "Q1&RF'9'@&7'Lr3%3221r2%5241%73831'Hr1%2271&R0r6%2218r5%421:%@3>31p071pW<C1'8%11B&K%13DC8r4%33FE1%I3531p081p0D1pW8M1pVHO1pVFQ01").
Proof. intros a b i. intros Hl Hk. apply (nth_ext _ _ 0 0). rewrite !length_skipn; lia.
intros n Hn. rewrite !nth_skipn. apply Hk. lia. Qed.
Lemma add_carry_loop_inv : ltac2:(TCodec.tc2 tcn__BigFactsOps "S:'L&RF'9&Q2r2%211'@&7r3%2291%43816&R0r4&Gu1%2271%5241z%<3B21'H%1268&E%12>:r9%B3F21%F1A%C2J>r<%F3J21'?&S0r6%22?1+1%4231%6231&Cr7%Q03Q61E%311&Ir?%22C1p041r:r1%K221%Q42HQ;rB%Q621Q=%Q<3QB31p051pW<QB1&RL&Q0&Jr8%23QI=1%411&S5&S7&Q@&S6%11C%4231%62Q:1%=281rA%=3R4H1%?11%A21F%R13R751&QEr;%25Q?17NQC%R81N%R52R<O%R73R;1M%H1Q1rC%J11rD%M221%R=3RC51%QG271%QH2:1tX8RE<1p0@1p0Q41p0Q>1p0QG1p0QO1p0R31p0R91p0R61pX6RN1pVLS01pW8RO1pW2S01p0R?1p0RB1p0RK1p0S11pWFS51pWHS71pX@S91").
Proof. intros y orig n.
intros Ho Hlo Htop Hn1. induction f as [|f IH]; intros i carry ws Hif Hi Hw Hl Hc Hcn Hk Hv; cbn [add_carry_loop].
- assert (carry = 0). { destruct (Z.eq_dec carry 0); auto. specialize (Hcn n0). lia. } subst carry.
assert (i = n) by lia. subst i. repeat split; auto.
rewrite !firstn_all2 in Hv by lia. lia.
- destruct (Nat.ltb_spec i n); cbn [andb].
2:{ exfalso. lia. }
destruct (Z.eqb_spec carry 0); cbn [negb].
+ subst carry. repeat split; auto.
rewrite (val_firstn_skipn i ws), (val_firstn_skipn i orig). rewrite !length_firstn, Hl, Hlo.
rewrite (skipn_nth_ext ws orig i) by (auto; lia). lia.
+ assert (carry = 1) by lia. subst carry.
pose proof (words_ok_nth ws i Hw) as Wi.
assert (W1: wordZ 1) by (unfold wordZ; rewrite M_val; lia).
pose proof (add_carry' (nth_w ws i) 1 Wi W1) as AC.
set (d := W.add (nth_w ws i) 1) in *. set (c' := W.b2z (W.ltu d 1)) in *.
pose proof (b2z_range (W.ltu d 1)) as Rc'. fold c' in Rc'.
apply IH; clear IH.
* lia. * lia.
* apply upd_words_ok; auto. apply add_range.
* rewrite upd_length; auto.
* lia.
* intros Hc'. destruct (Nat.eq_dec (S i) n); try lia. exfalso.
assert (Hz: nth_w ws i = 0). { rewrite Hk by lia. replace i with (n - 1)%nat by lia. exact Htop. }
rewrite Hz in AC. unfold c' in *. unfold W.b2z, W.ltu in *. destruct (Z.ltb_spec d 1); try lia.
pose proof (add_range (nth_w ws i) 1). fold d in H1. unfold wordZ in H1. rewrite M_val in *. lia.
* intros k Hk2. rewrite upd_nth_other by lia. apply Hk; lia.
* rewrite val_firstn_S by (rewrite upd_length; lia). rewrite firstn_upd_le by lia. rewrite upd_nth_same by lia.
rewrite val_firstn_S by lia. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
rewrite <- (Hk i) by lia. nia.
Qed.
Lemma add_word_mspec N s y : okN N s -> wordZ y -> (S (size s) <= N)%nat ->
mspec (add_word s y)
(fun s' => okN N s' /\ reduced s' /\ val (s_words s') = val (s_words s) + y /\ (size s' <= S (size s))%nat
/\ s_neg s' = (if (size s' =? 0)%nat then false else s_neg s) /\ (capacity s <= capacity s')%nat)
1 (BB N).
Proof.
intros Hok Hy Hn. unfold add_word. eapply mspec_bind'. apply resize_mspec; eauto. 2: lia.
intros s1 (Hok1 & Hw1 & Hsz1 & Hneg1 & Hc1).
assert (Horig: s_words s1 = s_words s ++ [0]).
{ rewrite Hw1. unfold size. rewrite firstn_all2 by lia. replace (S (length (s_words s)) - length (s_words s))%nat with 1%nat by lia. reflexivity. }
pose proof (okN_words N s1 Hok1) as Wo. pose proof (okN_words N s Hok) as Ws.
set (orig := s_words s1) in *. set (n := size s1) in *.
assert (Hlen: length orig = n) by reflexivity.
assert (Htop: nth_w orig (n - 1) = 0).
{ unfold n, size. fold orig. rewrite Horig, length_app. simpl length. rewrite nth_w_app_r by lia.
replace (length (s_words s) + 1 - 1 - length (s_words s))%nat with 0%nat by lia. reflexivity. }
pose proof (words_ok_nth orig 0 Wo) as W0.
assert (E0: W.add (nth_w orig 0) 0 = nth_w orig 0). { rewrite add_small. lia. auto. unfold wordZ; rewrite M_val; lia. unfold wordZ in *; lia. }
rewrite E0. replace (W.ltu (nth_w orig 0) 0) with false.
2:{ unfold W.ltu. destruct (Z.ltb_spec (nth_w orig 0) 0); auto. unfold wordZ in W0; lia. }
cbn [W.b2z].
pose proof (add_carry (nth_w orig 0) y W0 Hy) as AC.
set (w0 := W.add (nth_w orig 0) y) in *.
set (c := if W.ltu w0 (nth_w orig 0) then 1 else 0).
assert (Ec: c = W.b2z (W.ltu w0 (nth_w orig 0))) by reflexivity.
pose proof (b2z_range (W.ltu w0 (nth_w orig 0))) as Rc. rewrite <- Ec in Rc, AC.
pose proof (add_carry_loop_inv y orig n Wo Hlen Htop ltac:(lia) (n - 1) 1 c (upd orig 0 w0)) as INV.
assert (INV': let ws' := add_carry_loop (n - 1) 1 n c (upd orig 0 w0) in words_ok ws' /\ length ws' = n /\ val ws' = val orig + y).
{ apply INV; clear INV; try lia.
- apply upd_words_ok; auto. apply add_range.
- rewrite upd_length; auto.
- intros Hc0. destruct (Nat.eq_dec n 1); try lia. exfalso.
assert (Hz: nth_w orig 0 = 0). { replace 0%nat with (n - 1)%nat by lia. exact Htop. }
pose proof (add_range (nth_w orig 0) y) as AR. fold w0 in AR. unfold wordZ in AR.
rewrite Hz in AC. unfold c in Hc0, AC. unfold W.ltu in *. rewrite Hz in *. destruct (Z.ltb_spec w0 0); try lia.
- intros k Hk. rewrite upd_nth_other by lia. auto.
- rewrite val_firstn_S by (rewrite upd_length; lia). rewrite val_firstn_S by lia. cbn [firstn]. rewrite val_nil, upd_nth_same by lia.
simpl Z.of_nat. rewrite Z.pow_0_r, Z.pow_1_r. lia. }
clear INV. cbv zeta in INV'. destruct INV' as (W' & L' & V').
set (ws2 := add_carry_loop (n - 1) 1 n c (upd orig 0 w0)) in *.
assert (Hok2: okN N (set_words s1 ws2)).
{ apply okN_set_words; auto. rewrite L'. destruct Hok1 as [[_ [Hs _]] _]. exact Hs. }
apply mspec_ret.
split. apply reduce_okN; auto.
split. apply reduce_reduced.
split. rewrite reduce_val. cbn [s_words set_words]. rewrite V'. fold orig. rewrite Horig, val_app, val_cons, val_nil. lia.
split. pose proof (reduce_size_le (set_words s1 ws2)) as RS. rewrite size_set_words, L' in RS. lia.
split. rewrite reduce_neg. cbn [s_neg set_words]. rewrite Hneg1. reflexivity.
rewrite capacity_reduce, capacity_set_words. exact Hc1.
Qed.
Lemma land_high_low : ltac2:(TCodec.tc2 tcn__BigFactsOps "L'L&S0zr3%3221'?&S2&S7+2r5%3221%5281%7281'@&RO&S5r6%:291%3291r4%6221%83E1Cp0:1p0C1p0D1pVHI1pVFJ1pW<K1").
Proof. intros k a b.
intros Hk Ha Hb. apply Z.bits_inj_0. intros n.
destruct (Z_lt_le_dec n 0). rewrite Z.testbit_neg_r; auto.
rewrite Z.land_spec. destruct (Z_lt_le_dec n k).
- rewrite Z.mul_pow2_bits_low; auto.
- destruct (Z.eq_dec b 0). subst. rewrite Z.bits_0. apply andb_false_r.
rewrite (Z.bits_above_log2 b). apply andb_false_r. lia. apply Z.lt_le_trans with k. apply Z.log2_lt_pow2; lia. lia.
Qed.
Lemma lor_high_low : ltac2:(TCodec.tc2 tcn__BigFactsOps "N'L&S0zr3%3221'?&S2&S7+2r5%3221%5281%7281'@&S1&S5r6%:291%3291r4%6221&RL%1243%:3G31p0<1p0E1p0F1pVHK1pVFL1pW<M1").
Proof. intros k a b. intros. rewrite <- Z.lxor_lor by (apply land_high_low; auto). symmetry. apply Z.add_nocarry_lxor. apply land_high_low; auto. Qed.
Lemma testbit_high : ltac2:(TCodec.tc2 tcn__BigFactsOps "Q1'L&S0zr1%3221'?r3%6251&S2&S7+2&RLr2+1%3221%6251%82:1%<2:1&B'@'4&S9r4%221A(;%63521%A2@D%J215%:231p0<1p0J1pWFO1pX@Q01").
Proof. intros y n.
intros Hn Hy. rewrite Z.testbit_true by auto.
assert (Hq: 0 <= y / 2 ^ n < 2). { split. apply Z.div_pos. lia. apply Z.pow_pos_nonneg; lia.
apply Z.div_lt_upper_bound. apply Z.pow_pos_nonneg; lia. rewrite Z.pow_add_r in Hy by lia. change (2^1) with 2 in Hy. lia. }
pose proof (Z.pow_pos_nonneg 2 n).
split; intros H1.
- assert (y / 2 ^ n = 1). { rewrite Z.mod_small in H1 by lia. auto. }
pose proof (Z.mul_div_le y (2^n)). lia.
- rewrite Z.mod_small by lia. pose proof (Z.div_le_lower_bound y (2^n) 1). lia.
Qed.
Lemma land_l_bit : ltac2:(TCodec.tc2 tcn__BigFactsOps "F'L&Q1r1%211'@'4&RN&QBr2&QA%3221z%6221&S3&S7+2+QO%3221%52:1%?3>71p0A1pX@E1").
Proof. intros y.
intros Hy. unfold W.land. rewrite l_bit_val. change 9223372036854775808 with (2^63).
unfold wordZ in Hy. rewrite M_val in Hy. change 18446744073709551616 with (2^(63+1)) in Hy.
pose proof (testbit_high y 63 ltac:(lia) Hy) as TB.
assert (E: Z.land y (2^63) = if Z.testbit y 63 then 2^63 else 0).
{ apply Z.bits_inj'. intros m Hm. rewrite Z.land_spec, Z.pow2_bits_eqb by lia.
destruct (Z.eqb_spec 63 m). subst. destruct (Z.testbit y 63). rewrite Z.pow2_bits_true by lia. reflexivity. rewrite Z.bits_0. reflexivity.
rewrite andb_false_r. destruct (Z.testbit y 63). rewrite Z.pow2_bits_false by lia. reflexivity. rewrite Z.bits_0. reflexivity. }
rewrite E. destruct (Z.testbit y 63).
- destruct TB as [TB1 _]. specialize (TB1 eq_refl). pose proof (Z.pow_pos_nonneg 2 63).
destruct (Z.ltb_spec y (2^63)); destruct (Z.eqb_spec (2^63) 0); auto; lia.
- rewrite Z.eqb_refl. destruct (Z.ltb_spec y (2^63)); auto. exfalso. destruct TB as [_ TB2]. specialize (TB2 ltac:(lia)). congruence.
Qed.
Lemma norm_count_spec : ltac2:(TCodec.tc2 tcn__BigFactsOps "QI'9'L&Q1r2%211&C'@r3z%33821%511&S0&S7+2+QO%3221&S5r4&S6r5%211%9281%6251%<281%=2@7&QOr7r6%33219'?r1%D241&RLr8%@11%3281%I261%8261&S8%129<%L2K1%I2?1%O2K1&S2+R0%Q12Q01%3251%B251%C2;1tX<Q@E1p0J1p0L1p0Q:1p0QA1pX:QE1pX@QF1pW2QH1").
Proof.
induction f as [|f IH]; intros y x Hy Hnz Hf Hx; cbn [norm_count].
- simpl in Hf. replace (x - x) with 0 by lia. rewrite Z.pow_0_r. unfold wordZ in Hy; rewrite M_val in Hy. change 18446744073709551616 with (2^64) in Hy. lia.
- rewrite land_l_bit by auto. destruct (Z.ltb_spec y (2^63)).
+ assert (Hs: W.shl y 1 = y * 2). { unfold W.shl. change (2^1) with 2. apply wrap_id. unfold wordZ; rewrite M_val. change 18446744073709551616 with (2^64). lia. }
rewrite Hs. specialize (IH (y * 2) (x + 1)).
assert (wordZ (y * 2)). { unfold wordZ; rewrite M_val; change 18446744073709551616 with (2^64); unfold wordZ in Hy; lia. }
assert (2 ^ 63 <= y * 2 * 2 ^ Z.of_nat f). { rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hf by lia. lia. }
specialize (IH H0 ltac:(lia) H1 ltac:(lia)). cbv zeta in IH.
set (x' := norm_count f (y * 2) (x + 1)) in *.
replace (x' - x) with (1 + (x' - (x + 1))) by lia. rewrite Z.pow_add_r by lia. change (2^1) with 2. rewrite Nat2Z.inj_succ. lia.
+ replace (x - x) with 0 by lia. rewrite Z.pow_0_r. unfold wordZ in Hy; rewrite M_val in Hy. change 18446744073709551616 with (2^64) in Hy. lia.
Qed.
Corollary norm_count_64 : ltac2:(TCodec.tc2 tcn__BigFactsOps "Q6'L&Q1r1%211&C'@r2z%33821%511&QO&Q?r3%33216'?&S0%129>+QO%32@1%5231&S7+2%2215&S5r4%524G%3221%<251&S2+R0%:291%3251%B251%C2>1tX:Q2E1p0J1p0Q11pX@Q51").
Proof. intros y.
intros Hy Hnz. unfold NORM_FUEL. pose proof (norm_count_spec 64 y 0 Hy Hnz) as H.
assert (H0: 2 ^ 63 <= y * 2 ^ Z.of_nat 64). { simpl Z.of_nat. unfold wordZ in Hy. assert (1 <= y) by lia.
assert (2^63 <= 2^64) by (apply Z.pow_le_mono_r; lia). nia. }
specialize (H H0 ltac:(lia)). cbv zeta in H. rewrite Z.sub_0_r in H. simpl Z.of_nat in H.
cbv zeta. set (x := norm_count 64 y 0) in *. destruct H as [H1 H2].
assert (x <> 64). { intro e. rewrite e in H2. unfold wordZ in Hy. assert (1 <= y) by lia. pose proof (Z.pow_pos_nonneg 2 64). nia. }
split. lia. exact H2.
Qed.
Section ShlFacts.
Variable k : Z.
Hypothesis Hk : 0 < k < 64.
Let k1 := 64 - k.
Let mask := W.sub (W.shl 1 k) 1.
Lemma pow_k_pos : ltac2:(TCodec.tc2 tcn__BigFactsOps "7&S2z&S7+2vSE%3221%6251"). Proof. apply Z.pow_pos_nonneg; lia. Qed.
Lemma pow_k1_pos : ltac2:(TCodec.tc2 tcn__BigFactsOps "7&S2z&S7+2vSF%3221%6251"). Proof. apply Z.pow_pos_nonneg; lia. Qed.
Lemma M_split : ltac2:(TCodec.tc2 tcn__BigFactsOps "<'@'L&Q@&S5&S7+2vSF%3221vSE%5241%7231%;3:91").
Proof. rewrite M_val. change 18446744073709551616 with (2^64). rewrite <- Z.pow_add_r by lia. f_equal. lia. Qed.
Lemma pow_k_lt_M : ltac2:(TCodec.tc2 tcn__BigFactsOps "7&S2&S7+2vSE%3221&Q@%6221").
Proof. rewrite M_val. change 18446744073709551616 with (2^64). apply Z.pow_lt_mono_r; lia. Qed.
Lemma mask_eq : ltac2:(TCodec.tc2 tcn__BigFactsOps ";'@'LvSI&S8&S7+2vSE%3221+1%6221%:3981").
Proof. unfold mask. unfold W.shl. rewrite Z.mul_1_l. rewrite wrap_id. 2:{ unfold wordZ. pose proof pow_k_pos. pose proof pow_k_lt_M. lia. }
apply sub_small. unfold wordZ; pose proof pow_k_pos; pose proof pow_k_lt_M; lia. unfold wordZ; rewrite M_val; lia. pose proof pow_k_pos; lia. Qed.
Lemma shl_decomp : ltac2:(TCodec.tc2 tcn__BigFactsOps "Q6'L&Q1r1%211'?'@&QCr2vSE%3221&S5&S4&S7+2vSF%3221%5291%5249%8221%>3C:1%:2=3&RL&Q@&RM%12A9%?231%52A1%F3K71&S0z%2216&S2%128?%M231%N271%O2@1p0Q11pVFQ51").
Proof. intros a.
intros Ha. unfold W.shl, W.wrap. rewrite M_split. pose proof pow_k_pos. pose proof pow_k1_pos.
rewrite Z.mul_mod_distr_r by lia.
split. reflexivity. split. rewrite (Z_div_mod_eq_full a (2 ^ k1)) at 1. nia.
split. apply Z.div_pos; unfold wordZ in Ha; lia. apply Z.div_lt_upper_bound. lia. rewrite <- M_split. unfold wordZ in Ha; lia.
Qed.
Lemma hi_part : ltac2:(TCodec.tc2 tcn__BigFactsOps "D'L&Q1r1%211'@&QB&QDr2vSF%3221vSI%6221&RM&S7+2%2217%4291%=3A61p0?1pVHC1").
Proof. intros b.
intros Hb. rewrite mask_eq. unfold W.land, W.shr. replace (2 ^ k - 1) with (Z.ones k) by (unfold Z.ones; rewrite Z.shiftl_1_l; lia).
rewrite Z.land_ones by lia. apply Z.mod_small. destruct (shl_decomp b Hb) as (_ & _ & H). exact H.
Qed.
Definition shlG (orig : words) (j : nat) : Z :=
let wi := W.shl (nth_w orig j) k in
if (0 <? j)%nat then W.lor wi (W.land (W.shr (nth_w orig (j - 1)) k1) mask) else wi.
Lemma shlG_val orig j : words_ok orig ->
shlG orig j = W.shl (nth_w orig j) k + (if (0 <? j)%nat then nth_w orig (j - 1) / 2 ^ k1 else 0)
/\ wordZ (shlG orig j).
Proof.
intros Ho. unfold shlG. pose proof (words_ok_nth orig j Ho) as Wj. pose proof (words_ok_nth orig (j-1) Ho) as Wj1.
destruct (shl_decomp _ Wj) as (E1 & E2 & R1). destruct (shl_decomp _ Wj1) as (_ & _ & R2).
destruct (Nat.ltb_spec 0 j).
- rewrite hi_part by auto. unfold W.lor. rewrite E1. rewrite lor_high_low; try lia. 2:{ apply Z.mod_pos_bound. apply pow_k1_pos. }
split. reflexivity. unfold wordZ. rewrite M_split. pose proof (Z.mod_pos_bound (nth_w orig j) (2^k1) pow_k1_pos). nia.
- split. lia. apply shl_range.
Qed.
Lemma shl_loop_pointwise : ltac2:(TCodec.tc2 tcn__BigFactsOps "QM&RF&Q2r1%211'9'8'L%211'@&7%1248r4%3261%53931'Hr3r5%82;1%4231&I%12B4&R0r2%2271r8%4213%B3D31p071pW:H1&R=vSEvSFvSI%45A321F'?%J2M;%L3Q0J1r7%H21Q4%B2HA%C23B%Q13Q321p041pW:Q71%I2Q:7&Q4r:%221I%Q83Q:91p051pW:Q>1%A281%B2@1tWJQED1p0J1p0Q51p0Q;1pX6QB1pW2QF1p0QH1pWHQL1").
Proof. intros orig.
intros Ho. induction f as [|i IH]; intros ws Hl Hf Hagree; cbn [shl_loop].
- repeat split; auto. intros; lia.
- set (wi := if (0 <? i)%nat then W.lor (W.shl (nth_w ws i) k) (W.land (W.shr (nth_w ws (i - 1)) k1) mask) else W.shl (nth_w ws i) k).
assert (Ewi: wi = shlG orig i). { unfold wi, shlG. rewrite !Hagree by lia. reflexivity. }
specialize (IH (upd ws i wi)). cbv zeta in IH.
destruct IH as (L & A & B). rewrite upd_length; auto. lia. intros j Hj. rewrite upd_nth_other by lia. apply Hagree; lia.
repeat split. exact L.
+ intros j Hj. rewrite A by lia. rewrite upd_nth_other by lia. reflexivity.
+ intros j Hj. destruct (Nat.eq_dec j i). subst j. rewrite A by lia. rewrite upd_nth_same by lia. exact Ewi. apply B. lia.
Qed.
Lemma shl_val_prefix : ltac2:(TCodec.tc2 tcn__BigFactsOps "R5&RF'8'L%211&Q2r2%211'@'9&7%1285r3%32:1%63531&Ir1r5%82?1%4231&R0%124?&Q4r6%221B%A3F41p071pW:B1'?'Hu1%221?%F2M9%42A1%6231&Q0&J%13Q2O>%311&S8&S5&S7+2vSE%3221r7%:3Q;Q81%<11%8241&Q@&S6%11Q=%;231&RM&G%12QAI%Q42;1vSF%A2@1%6231%D281%F2=1%QF3QKH1p0M1pWBQG1p0Q61p0QD1p0QL1pWJR01pWHR41").
Proof. intros orig r.
intros Ho Hl Hr. induction m as [|m IH]; intros Hm. lia.
destruct (Nat.eq_dec m 0).
- subst m. rewrite !val_firstn_S by lia. cbn [firstn]. rewrite !val_nil. simpl Z.of_nat. rewrite Z.pow_0_r, Z.pow_1_r. simpl Nat.sub.
rewrite Hr by lia. destruct (shlG_val orig 0 Ho) as [E _]. rewrite E. cbn [Nat.ltb Nat.leb].
destruct (shl_decomp (nth_w orig 0) (words_ok_nth orig 0 Ho)) as (_ & E2 & _). lia.
- rewrite !val_firstn_S by lia. rewrite IH by lia. rewrite Hr by lia.
destruct (shlG_val orig m Ho) as [E _]. rewrite E. destruct (Nat.ltb_spec 0 m). 2: lia.
destruct (shl_decomp (nth_w orig m) (words_ok_nth orig m Ho)) as (_ & E2 & _).
rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. replace (S m - 1)%nat with m by lia.
nia.
Qed.
End ShlFacts.
Ltac splits := repeat match goal with |- _ /\ _ => split end.
Lemma shl_bits_mspec N s k : okN N s -> 0 <= k < 64 -> (S (size s) <= N)%nat ->
mspec (shl_bits s k)
(fun s' => okN N s' /\ reduced s' /\ val (s_words s') = val (s_words s) * 2 ^ k /\ (size s' <= S (size s))%nat
/\ s_neg s' = (if (size s' =? 0)%nat then false else s_neg s) /\ (capacity s <= capacity s')%nat)
2 (BB N).
Proof.
intros Hok Hk Hn. unfold shl_bits.
replace (Z.to_nat (k / 64)) with 0%nat by (rewrite Z.div_small by lia; reflexivity). cbn [Nat.eqb negb].
eapply mspec_bind' with (K1 := 0%nat). apply mspec_ret with (P := fun x => x = (s, k, size s)). reflexivity. 2: lia.
intros sq ->. destruct (Z.eqb_spec k 0).
- subst k. cbn [negb]. eapply mspec_bind' with (K1 := 0%nat). apply mspec_ret with (P := fun x => x = s); reflexivity. 2: lia.
intros s1 ->. apply mspec_ret. rewrite Z.pow_0_r, Z.mul_1_r. pose proof (reduce_size_le s).
splits. apply reduce_okN; auto. apply reduce_reduced. apply reduce_val. lia. apply reduce_neg. rewrite capacity_reduce; lia.
- cbn [negb]. eapply mspec_bind' with (K1 := 1%nat). 3: lia. 2:{ intros s2 Hs2. apply mspec_ret. exact Hs2. }
eapply mspec_bind' with (K1 := 1%nat). apply resize_mspec; eauto. 2: lia.
intros s1 (Hok1 & Hw1 & Hsz1 & Hneg1 & Hc1).
assert (Horig: s_words s1 = s_words s ++ [0]).
{ rewrite Hw1. unfold size. rewrite firstn_all2 by lia. replace (S (length (s_words s)) - length (s_words s))%nat with 1%nat by lia. reflexivity. }
pose proof (okN_words N s1 Hok1) as Wo.
assert (Lo: length (s_words s1) = size s1) by reflexivity.
rewrite Horig in Wo, Lo |- *. set (orig := s_words s ++ [0]) in *.
assert (Ln: length orig = S (length (s_words s))). { subst orig. rewrite length_app. simpl. lia. }
assert (Hk' : 0 < k < 64) by lia.
pose proof (shl_loop_pointwise k orig Wo (size s1) orig eq_refl ltac:(lia) ltac:(auto)) as PW. cbv zeta in PW.
destruct PW as (L & A & B).
set (r := shl_loop (size s1) k (64 - k) (W.sub (W.shl 1 k) 1) orig) in *.
assert (B' : forall j0, (j0 < length orig)%nat -> nth_w r j0 = shlG k orig j0). { intros j0 Hj0. apply B. lia. }
assert (Wr: words_ok r).
{ unfold words_ok. apply Forall_forall. intros x Hx. apply In_nth with (d := 0) in Hx. destruct Hx as (j & Hj & <-).
fold (nth_w r j). rewrite B' by lia. apply (shlG_val k Hk' orig j Wo). }
assert (Vr: val r = val (s_words s) * 2 ^ k).
{ pose proof (shl_val_prefix k Hk' orig r Wo L B' (length orig) ltac:(lia)) as VP.
rewrite (firstn_all2 r) in VP by lia. rewrite (firstn_all2 orig) in VP by lia. rewrite VP.
replace (nth_w orig (length orig - 1)) with 0.
2:{ rewrite Ln. subst orig. rewrite nth_w_app_r by (simpl; lia). replace (S (length (s_words s)) - 1 - length (s_words s))%nat with 0%nat by lia. reflexivity. }
rewrite Z.div_0_l by (apply Z.pow_nonzero; lia). subst orig; rewrite val_app, val_cons, val_nil. lia. }
apply mspec_ret.
assert (Hok2: okN N (set_words s1 r)). { apply okN_set_words; auto. rewrite L, Lo. destruct Hok1 as [[_ [Hs _]] _]. exact Hs. }
pose proof (reduce_size_le (set_words s1 r)) as RS. rewrite size_set_words, L in RS.
splits. apply reduce_okN; auto. apply reduce_reduced. rewrite reduce_val. exact Vr.
lia.
rewrite reduce_neg. cbn [s_neg set_words]. rewrite Hneg1. reflexivity.
rewrite capacity_reduce, capacity_set_words. exact Hc1.
Qed.
Lemma shr_loop_length : ltac2:(TCodec.tc2 tcn__BigFactsOps "H'9'L&RF'@&7&R?r7r6r5r4r3r2r1%877654321%:2=1%;2>3%=3@21pX6?1pWDA1pW>B1pW<C1pWFE1pW8F1pW2G1").
Proof. intros f i n k k1 mask ws. revert i ws; induction f; intros; cbn [shr_loop]; auto. rewrite IHf, upd_length; auto. Qed.
Lemma shr_loop_words_ok : ltac2:(TCodec.tc2 tcn__BigFactsOps "L'9'L&RF&S0zr4%3221&Q2r2%211&R?r9r8r7r6r5r3%7765432<1%;11p0:1p0>1pX6C1pWDE1pW>F1pW<G1pWFI1pW8J1pW2K1").
Proof. intros f i n k k1 mask ws. revert i ws; induction f; intros; cbn [shr_loop]; auto. apply IHf; auto. apply upd_words_ok; auto.
destruct (Nat.ltb i n). apply lor_range. apply shr_range; auto. apply words_ok_nth; auto. apply shl_range. apply shr_range; auto. apply words_ok_nth; auto. Qed.
Lemma shr_bits_mspec : ltac2:(TCodec.tc2 tcn__BigFactsOps "Q>'9'RB'L&Q8r3r2%3221'?&S2z%2215+R0%4271%6231&Q6&R>r4%221=r6r1%A221&Q9%113'H&RA%116r5%311%5231&QG%114%21<%9221%J251%K2<1%L2?1qWNQ31u1&Q3%11=%J5Q7G431p0L1p0Q41pW<Q91pWLQ;1pQNQ=1").
Proof. intros N s k.
intros Hok Hk. unfold shr_bits.
replace (Z.to_nat (k / 64)) with 0%nat by (rewrite Z.div_small by lia; reflexivity). cbn [Nat.ltb Nat.leb andb].
destruct (size s) as [|n0] eqn:Hsz; cbn [Nat.leb].
- eapply mspec_weaken. apply resize_mspec; eauto. lia. 2: lia. 2: lia.
intros s1 (Hok1 & Hw1 & Hsz1 & _ & Hc1). assert (s_words s1 = []) by (apply length_zero_iff_nil; auto).
splits; auto. unfold reduced; rewrite H; left; auto. lia.
- eapply mspec_bind' with (K1 := 0%nat). apply mspec_ret with (P := fun x => x = (s, k)); reflexivity. 2: lia.
intros sk ->. apply mspec_ret.
set (r := shr_loop _ _ _ _ _ _ _).
assert (Lr: length r = size s). { subst r. rewrite shr_loop_length. reflexivity. }
assert (Hok2: okN N (set_words s r)). { apply okN_set_words; auto. apply shr_loop_words_ok. lia. apply (okN_words N); auto.
rewrite Lr. destruct Hok as [[_ [Hs _]] _]; auto. }
pose proof (reduce_size_le (set_words s r)) as RS. rewrite size_set_words, Lr in RS.
splits. apply reduce_okN; auto. apply reduce_reduced. lia. rewrite capacity_reduce, capacity_set_words. lia.
Qed.
Definition cmp3 (a b : Z) : Z := match a ?= b with Lt => -1 | Eq => 0 | Gt => 1 end.
Lemma compare_loop_spec : ltac2:(TCodec.tc2 tcn__BigFactsOps "Q3&RF&Q2r2%211'9'Hr1&7'Lr5%3221%6251%72:2'@&QIr3r7r6%43321&Q5&Q0&J%13>76%311%33@97%511%7231%>3C91p0@1p0B1pWFJ1p0L1p0M1pXBQ11pX>Q21").
Proof. intros xs ys.
intros Wx Wy. induction n as [|i IH]; intros Hx Hy; cbn [compare_loop].
- cbn. reflexivity.
- rewrite !val_firstn_S by lia.
pose proof (val_bound (firstn i xs) (words_ok_firstn i xs Wx)) as Bx. pose proof (val_bound (firstn i ys) (words_ok_firstn i ys Wy)) as By.
rewrite !length_firstn, !Nat.min_l in Bx, By by lia.
pose proof (words_ok_nth xs i Wx) as Wxi. pose proof (words_ok_nth ys i Wy) as Wyi. unfold wordZ in *.
set (P := W.M ^ Z.of_nat i) in *. set (a := nth_w xs i) in *. set (b := nth_w ys i) in *.
destruct (Z.ltb_spec b a).
+ unfold cmp3. assert (a * P >= (b + 1) * P) by nia. rewrite (proj2 (Z.compare_gt_iff _ _)). reflexivity. nia.
+ destruct (Z.ltb_spec a b).
* unfold cmp3. assert ((a + 1) * P <= b * P) by nia. rewrite (proj2 (Z.compare_lt_iff _ _)). reflexivity. nia.
* assert (a = b) by lia. rewrite IH by lia. rewrite H1. unfold cmp3.
destruct (Z.compare_spec (val (firstn i xs)) (val (firstn i ys)));
[ rewrite (proj2 (Z.compare_eq_iff _ _)) by lia | rewrite (proj2 (Z.compare_lt_iff _ _)) by lia | rewrite (proj2 (Z.compare_gt_iff _ _)) by lia ]; reflexivity.
Qed.
Lemma cmp3_lt : ltac2:(TCodec.tc2 tcn__BigFactsOps ">'L&S2r2r1%3221'@&Q5r3%2216-1%53:21p071pVH<1pVF=1").
Proof. intros a b. intros. unfold cmp3. rewrite (proj2 (Z.compare_lt_iff _ _)); auto. Qed.
Lemma cmp3_gt : ltac2:(TCodec.tc2 tcn__BigFactsOps ">'L&S2r1r2%3221'@&Q5r3%2215+1%53:21p071pVH<1pVF=1").
Proof. intros a b. intros. unfold cmp3. rewrite (proj2 (Z.compare_gt_iff _ _)); auto; lia. Qed.
Lemma cmp3_eq : ltac2:(TCodec.tc2 tcn__BigFactsOps "='L'@r2r1%33421&Q5r3%2215z%83921p061pVH;1pVF<1").
Proof. intros a b. intros. unfold cmp3. rewrite (proj2 (Z.compare_eq_iff _ _)); auto. Qed.
Lemma compare_nonneg : ltac2:(TCodec.tc2 tcn__BigFactsOps "Q5'RB&Q2&R:r2%211%411&Q9r4%211'@'4&R9r6%211(6%63521'L&QHr8r7%3221&Q5&Q0%E15%211%G16%411%6231%C3<81p0>1p0?1p0G1p0H1p0L1p0M1pX@Q31pX:Q41").
Proof. intros x y.
intros Wx Wy Rx Ry Nx Ny. unfold compare. rewrite Nx, Ny. cbn [Bool.eqb negb].
assert (Sx: size x = length (s_words x)) by reflexivity. assert (Sy: size y = length (s_words y)) by reflexivity.
pose proof (val_bound _ Wx) as Bx. pose proof (val_bound _ Wy) as By.
assert (Zx: size x = 0%nat -> val (s_words x) = 0). { intros E. rewrite Sx in E. apply length_zero_iff_nil in E. rewrite E. reflexivity. }
assert (Zy: size y = 0%nat -> val (s_words y) = 0). { intros E. rewrite Sy in E. apply length_zero_iff_nil in E. rewrite E. reflexivity. }
assert (Lx: size x <> 0%nat -> W.M ^ (Z.of_nat (size x) - 1) <= val (s_words x)).
{ intros E. rewrite Sx. apply reduced_val_lower; auto. intro E'. rewrite Sx, E' in E. simpl in E. lia. }
assert (Ly: size y <> 0%nat -> W.M ^ (Z.of_nat (size y) - 1) <= val (s_words y)).
{ intros E. rewrite Sy. apply reduced_val_lower; auto. intro E'. rewrite Sy, E' in E. simpl in E. lia. }
rewrite <- Sx in Bx. rewrite <- Sy in By.
destruct (Nat.eqb_spec (size x) 0) as [Ex|Ex]; destruct (Nat.eqb_spec (size y) 0) as [Ey|Ey]; cbn [andb].
- rewrite Zx, Zy by auto. reflexivity.
- destruct (Nat.ltb_spec (size x) (size y)); try lia. rewrite Zx by auto. symmetry. apply cmp3_lt.
specialize (Ly Ey). pose proof (Z.pow_pos_nonneg W.M (Z.of_nat (size y) - 1) M_pos). lia.
- destruct (Nat.ltb_spec (size x) (size y)); try lia. destruct (Nat.ltb_spec (size y) (size x)); try lia.
rewrite Zy by auto. symmetry. apply cmp3_gt.
specialize (Lx Ex). pose proof (Z.pow_pos_nonneg W.M (Z.of_nat (size x) - 1) M_pos). lia.
- destruct (Nat.ltb_spec (size x) (size y)).
+ symmetry. apply cmp3_lt. specialize (Ly Ey).
assert (W.M ^ Z.of_nat (size x) <= W.M ^ (Z.of_nat (size y) - 1)). { apply Z.pow_le_mono_r. apply M_pos. lia. } lia.
+ destruct (Nat.ltb_spec (size y) (size x)).
* symmetry. apply cmp3_gt. specialize (Lx Ex).
assert (W.M ^ Z.of_nat (size y) <= W.M ^ (Z.of_nat (size x) - 1)). { apply Z.pow_le_mono_r. apply M_pos. lia. } lia.
* assert (E: size x = size y) by lia. rewrite compare_loop_spec by (auto; lia).
rewrite Sx, firstn_all. rewrite Sx, E, Sy, firstn_all in *. reflexivity.
Qed.
Lemma cmp3_lt_iff : ltac2:(TCodec.tc2 tcn__BigFactsOps ">'L'@'4&S3&Q5r2r1%3221z%6221%7254%:3921pVH<1pVF=1").
Proof. intros a b. unfold cmp3. destruct (Z.compare_spec a b); destruct (Z.ltb_spec a b); simpl; auto; lia. Qed.
Lemma cmp3_nonneg_iff : ltac2:(TCodec.tc2 tcn__BigFactsOps "B'L&B'@'4&S3&Q5r2r1%3221z%6221(6%:3921&S0%1278%>231pVH@1pVFA1").
Proof. intros a b. rewrite cmp3_lt_iff. destruct (Z.ltb_spec a b); split; intros; auto; try lia; try congruence. Qed.
Lemma top_word_range : ltac2:(TCodec.tc2 tcn__BigFactsOps "QH&RF'9'L&Q2r4%211&Q:r5%211&S0+1%2217%3258&Q@%5271'?&S5r7&S7&S6r8%211%4291%7261&Q0r9%211%B241&S2r6%>218%3251%A251'@&7r:%22Q21(2%11=%63Q631&R0%126@%Q12F1%?22J%M221%N261p0>1p0Q11p0Q41p0Q61p0Q:1p0Q>1pW6QB1pW@QC1pW<QE1pX6QG1").
Proof. intros ws k lo hi. intros Hw Hr Hlo Hlh Hhi [H1 H2]. pose proof (Z.pow_pos_nonneg W.M (Z.of_nat k) M_pos) as Pk.
assert (L1: (k < length ws)%nat). { apply size_ge_of_val; auto. nia. }
assert (L2: (length ws <= S k)%nat). { apply size_le_of_val; auto. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. nia. }
assert (L: length ws = S k) by lia. split; auto.
pose proof (val_single_nth ws k L1) as E.
assert (Sk: skipn (S k) ws = []). { apply length_zero_iff_nil. rewrite length_skipn. lia. }
rewrite Sk, val_nil, Z.mul_0_r, Z.add_0_r in E.
pose proof (val_bound (firstn k ws) (words_ok_firstn k ws Hw)) as B0. rewrite length_firstn, Nat.min_l in B0 by lia.
pose proof (words_ok_nth ws k Hw) as Wk. unfold wordZ in Wk.
set (w := nth_w ws k) in *. set (V0 := val (firstn k ws)) in *. set (P := W.M ^ Z.of_nat k) in *.
assert (~ w <= lo - 1). { intro. assert (P * w <= P * (lo - 1)) by nia. nia. }
assert (~ hi <= w). { intro. assert (P * hi <= P * w) by nia. nia. }
lia. Qed.
