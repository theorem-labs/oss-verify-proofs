(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec CatExec AxSymExec3 AxSymExec3Sound MemSplit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegTmpl SegGhost SegVC SegLin.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import SjVCPre.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SWARZ SLOWG NRMG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.

Module SNV.
Local Notation u := bv_unsigned.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint kdigestX (allkn kn : list kentry) : list VP.zf :=
  match kn with
  | [] => []
  | KRange e lo hi :: rest =>
      if (negb (VP.atoms_var (snd (lin_of e))) && fact_nowrap allkn e hi)%bool then VP.ZFrng (lin_of e) lo hi :: kdigestX allkn rest
      else kdigestX allkn rest
  | _ :: rest => kdigestX allkn rest
  end.

Lemma kdigestX_sound : forall segs E M allkn kn, know_ok segs E M allkn -> know_ok segs E M kn -> Forall (VP.zf_den E) (kdigestX allkn kn).
Proof.
  intros segs E M allkn kn HA. induction kn as [|K rest IH]; intros HK; cbn [kdigestX]; [constructor|].
  apply Forall_cons_iff in HK as [HK1 HR]. specialize (IH HR).
  destruct K as [a w v|a n|a n k|lo hi|e m|e lo hi|a n|a1 n1 a2 n2|a n c|a n]; try exact IH.
  destruct (negb (VP.atoms_var (snd (lin_of e))) && fact_nowrap allkn e hi)%bool eqn:C; [|exact IH].
  apply andb_prop in C as [_ C]. constructor; [|exact IH]. cbn [VP.zf_den]. cbn [kentry_ok] in HK1.
  pose proof (fact_nowrap_sound segs E M allkn e lo hi HA C HK1) as Q. rewrite VP.pden_ok, <- Q. exact HK1.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma u_ext1 : forall E x, u (edenot E (EExt false 0 1 x)) = u (edenot E x) mod 256.
Proof.
  intros E x. cbn [edenot]. unfold ext_val, ext_Z. cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r.
  change (2 ^ (8 * 1)) with 256. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  apply Z.mod_small. pose proof (Z.mod_pos_bound (u (edenot E x)) 256 ltac:(lia)). lia.
Qed.

Lemma rr1 : forall segs m E a k v, sc_denot segs m E (SCReadBase (SA a k) 1 false (EVar v)) ->
  SNG.bat segs m (u (adenot E (SA a k))) (u (ev E v)) /\ 0 <= u (ev E v) < 256.
Proof.
  intros segs m E a k v (bs & Hr & Hv). cbn [edenot] in Hv.
  pose proof (rdn_length segs m 1 _ bs Hr) as Hl. destruct bs as [|c [|c' r]]; try discriminate Hl.
  pose proof (SV.rd1_rdn segs m _ c Hr) as Hc.
  assert (U : u (ev E v) = u c).
  { rewrite <- Hv. cbn [extz bytes_le_to_Z]. rewrite Z.shiftl_0_l, Z.lor_0_r. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. pose proof (bv_unsigned_in_range 8 c) as R. unfold bv_modulus in R.
    cbn in R. lia. }
  pose proof (bv_unsigned_in_range 8 c) as R. unfold bv_modulus in R. cbn in R.
  split; [|lia]. exists c. split; [|symmetry; exact U].
  unfold SNG.rb. rewrite Z_to_bv_bv_unsigned. exact Hc.
Qed.

Lemma u_ext1_v : forall E v, u (ev E v) < 256 -> u (edenot E (EExt false 0 1 (EVar v))) = u (ev E v).
Proof. intros E v H. rewrite u_ext1. cbn [edenot]. apply Z.mod_small. pose proof (bv_unsigned_in_range 64 (ev E v)). lia. Qed.

(* [comment removed for export] *)
Lemma u_adenot : forall E b k, u (adenot E (SA b k)) = (u (edenot E b) + k) mod 2 ^ 64.
Proof. intros E b k. unfold adenot. cbn [a_base a_off]. unfold v_addi. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). reflexivity. Qed.

(* [comment removed for export] *)
Fixpoint krng_of (kn : list kentry) (e : expr) : option (Z * Z) :=
  match kn with
  | [] => None
  | KRange e' lo hi :: r => if expr_eqb e e' then Some (lo, hi) else krng_of r e
  | _ :: r => krng_of r e
  end.
Lemma krng_of_in : forall kn e lo hi, krng_of kn e = Some (lo, hi) -> In (KRange e lo hi) kn.
Proof.
  induction kn as [|K r IH]; intros e lo hi H; cbn [krng_of] in H; [discriminate|].
  destruct K; try (right; exact (IH _ _ _ H)).
  destruct (expr_eqb e e0) eqn:Q; [|right; exact (IH _ _ _ H)]. apply expr_eqb_eq in Q. subst. injection H as <- <-. left. reflexivity.
Qed.
Lemma u_lin_fact : forall segs E M kn e lo hi l, know_ok segs E M kn -> krng_of kn e = Some (lo, hi) -> fact_nowrap kn e hi = true ->
  lin_of e = l -> u (edenot E e) = VP.pden E l.
Proof.
  intros segs E M kn e lo hi l HK Hf Hn <-. pose proof (krng_of_in kn e lo hi Hf) as Hin.
  pose proof (proj1 (Forall_forall _ _) HK _ Hin) as HK1. cbn [kentry_ok] in HK1.
  rewrite VP.pden_ok. exact (fact_nowrap_sound segs E M kn e lo hi HK Hn HK1).
Qed.

(* [comment removed for export] *)
Lemma u_lin_mod : forall E e l, lin_of e = l -> u (edenot E e) = (VP.pden E l) mod 2 ^ 64.
Proof.
  intros E e l <-. rewrite VP.pden_ok. pose proof (lin_of_sound E e) as [q Hq]. unfold lden, uE in Hq.
  pose proof (bv_unsigned_in_range 64 (edenot E e)) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with (2 ^ 64) in R.
  apply Z.mod_unique with q; [left; lia | lia].
Qed.

(* [comment removed for export] *)
Lemma tgt_transfer : forall segs E m kn lg id args, know_ok segs E m kn -> log_flat E lg ->
  SG.log_apart kn lg (SNG.sng_gfp id args) = true ->
  SNG.sng_gp segs id (map (edenot E) args) m -> SNG.sng_gp segs id (map (edenot E) args) (mem_denot E m lg).
Proof.
  intros segs E m kn lg id args HK HL HA H. apply (SNG.sng_frame segs id args E m); [|exact H].
  intros x Hx. exact (SG.mem_denot_apart segs E kn m lg _ x HK HL HA Hx).
Qed.

(* [comment removed for export] *)
Lemma zrun_step : forall segs m a n k b, 0 <= n -> SNG.zdot segs m a n -> k = SNG.cnt0 segs m a (Z.to_nat n) ->
  SNG.bat segs m (a + n) b -> (b = 48 \/ b = 46) ->
  SNG.zdot segs m a (n + 1) /\ k + (if Z.eqb b 48 then 1 else 0) = SNG.cnt0 segs m a (Z.to_nat (n + 1)).
Proof.
  intros segs m a n k b Hn Hz Hk Hb Hd. split; [exact (SNG.zdot_app1 segs m a n b Hn Hz Hb Hd)|].
  replace (Z.to_nat (n + 1)) with (S (Z.to_nat n)) by lia. rewrite SNG.cnt0_S, Z2Nat.id by lia. rewrite <- Hk.
  destruct (Z.eqb_spec b 48) as [->|Hne].
  - rewrite (SNG.is0_48 segs m (a + n) Hb). reflexivity.
  - rewrite (SNG.is0_not48 segs m (a + n) b Hb Hne). lia.
Qed.

Lemma cnt0_zero : forall segs m a, SNG.cnt0 segs m a (Z.to_nat 0) = 0.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma digs_at : forall segs m a n x v, SNG.digs segs m a n -> a <= x < a + n -> SNG.bat segs m x v -> 48 <= v <= 57.
Proof.
  intros segs m a n x v H Hx Hv. destruct (H (x - a) ltac:(lia)) as (b & Hb & Hd). replace (a + (x - a)) with x in Hb by lia.
  rewrite (SNG.bat_fun segs m x v b Hv Hb). exact Hd.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma u_lit_small : forall E z, 0 <= z < 2 ^ 64 -> u (edenot E (ELit z)) = z.
Proof. intros E z H. cbn [edenot]. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. exact H. Qed.
Lemma u_and_lit : forall E a c, u (edenot E (EAlu ALU_AND a (ELit c))) = Z.land (u (edenot E a)) (c mod 2 ^ 64).
Proof.
  intros E a c. cbn [edenot]. unfold alu64, alu. rewrite bv_and_unsigned, Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). reflexivity.
Qed.
Lemma u_and255 : forall E a, u (edenot E (EAlu ALU_AND a (ELit 255))) = u (edenot E a) mod 256.
Proof. intros E a. rewrite u_and_lit. change (255 mod 2 ^ 64) with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma u_or : forall E a b, u (edenot E (EAlu ALU_OR a b)) = Z.lor (u (edenot E a)) (u (edenot E b)).
Proof. intros E a b. cbn [edenot]. unfold alu64, alu. rewrite bv_or_unsigned. reflexivity. Qed.
Lemma u_aluw_add_low : forall E a b, u (edenot E (EAluw ALU_ADD a b)) mod 2 ^ 32 = (u (edenot E a) + u (edenot E b)) mod 2 ^ 32.
Proof.
  intros E a b. cbn [edenot]. rewrite sext32_unsigned.
  change (alu32 ALU_ADD (low32 (edenot E a)) (low32 (edenot E b))) with (bv_add (low32 (edenot E a)) (low32 (edenot E b))).
  rewrite bv_add_unsigned, !low32_unsigned.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
  change (2 ^ Z.of_N 32) with 4294967296. change (2 ^ 32) with 4294967296. change (4294967296 / 2) with 2147483648.
  set (x := u (edenot E a)). set (y := u (edenot E b)).
  rewrite <- (Znumtheory.Zmod_div_mod 4294967296 18446744073709551616) by (lia || (exists 4294967296; lia)).
  rewrite Zminus_mod_idemp_l. replace ((x mod 4294967296 + y mod 4294967296) mod 4294967296 + 2147483648 - 2147483648)
    with ((x mod 4294967296 + y mod 4294967296) mod 4294967296) by lia.
  rewrite Z.mod_mod by lia. rewrite <- Zplus_mod. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma swar8_bridge : forall v0 v1 v2 v3 v4 v5 v6 v7 V,
  V = v0 + 256 * v1 + 65536 * v2 + 16777216 * v3 + 4294967296 * v4 + 1099511627776 * v5 + 281474976710656 * v6 + 72057594037927936 * v7 ->
  0 <= v0 < 256 -> 0 <= v1 < 256 -> 0 <= v2 < 256 -> 0 <= v3 < 256 -> 0 <= v4 < 256 -> 0 <= v5 < 256 -> 0 <= v6 < 256 -> 0 <= v7 < 256 ->
  Z.land (Z.lor ((V + 5063812098665367110) mod 2 ^ 64) ((V + -3472328296227680304) mod 2 ^ 64)) (9259542123273814144 mod 2 ^ 64) = 0 ->
  48 <= v0 <= 57 /\ 48 <= v1 <= 57 /\ 48 <= v2 <= 57 /\ 48 <= v3 <= 57 /\ 48 <= v4 <= 57 /\ 48 <= v5 <= 57 /\ 48 <= v6 <= 57 /\ 48 <= v7 <= 57.
Proof.
  intros v0 v1 v2 v3 v4 v5 v6 v7 V HV H0 H1 H2 H3 H4 H5 H6 H7 HC.
  assert (F : Forall (fun b => 48 <= b <= 57) [v0; v1; v2; v3; v4; v5; v6; v7]).
  { apply SWZ.swar_digits; [repeat constructor; lia|].
    replace (SWZ.lev [v0; v1; v2; v3; v4; v5; v6; v7]) with V by (cbn [SWZ.lev]; lia).
    replace (SWZ.rep 70 (length [v0; v1; v2; v3; v4; v5; v6; v7])) with 5063812098665367110 by reflexivity.
    replace (SWZ.rep 48 (length [v0; v1; v2; v3; v4; v5; v6; v7])) with 3472328296227680304 by reflexivity.
    replace (SWZ.rep 128 (length [v0; v1; v2; v3; v4; v5; v6; v7])) with (9259542123273814144 mod 2 ^ 64) by reflexivity.
    replace (8 * Z.of_nat (length [v0; v1; v2; v3; v4; v5; v6; v7])) with 64 by reflexivity.
    replace (V - 3472328296227680304) with (V + -3472328296227680304) by lia. exact HC. }
  repeat (apply Forall_cons_iff in F as [? F]). repeat split; lia.
Qed.

Lemma land_low32 : forall A B M, Z.land (Z.lor A B) M = 0 -> 0 <= A -> 0 <= B ->
  Z.land (Z.lor (A mod 2 ^ 32) (B mod 2 ^ 32)) (M mod 2 ^ 32) = 0.
Proof.
  intros A B M H HA HB. change (2 ^ 32) with (2 ^ Z.of_nat 32).
  rewrite <- !Z.land_ones by lia. rewrite <- Z.land_lor_distr_l.
  rewrite (Z.land_comm M (Z.ones (Z.of_nat 32))), Z.land_assoc, <- (Z.land_assoc (Z.lor A B)), Z.land_diag.
  rewrite <- Z.land_assoc, (Z.land_comm (Z.ones _) M), Z.land_assoc, H. reflexivity.
Qed.

Lemma swar4_bridge : forall v0 v1 v2 v3 V A B,
  V = v0 + 256 * v1 + 65536 * v2 + 16777216 * v3 ->
  0 <= v0 < 256 -> 0 <= v1 < 256 -> 0 <= v2 < 256 -> 0 <= v3 < 256 -> 0 <= A -> 0 <= B ->
  A mod 2 ^ 32 = (V + 1179010630) mod 2 ^ 32 -> B mod 2 ^ 32 = (V + 18446744072901087184) mod 2 ^ 32 ->
  Z.land (Z.lor A B) (18446744071570489472 mod 2 ^ 64) = 0 ->
  48 <= v0 <= 57 /\ 48 <= v1 <= 57 /\ 48 <= v2 <= 57 /\ 48 <= v3 <= 57.
Proof.
  intros v0 v1 v2 v3 V A B HV H0 H1 H2 H3 HA HB EA EB HC.
  pose proof (land_low32 A B _ HC HA HB) as HL. rewrite EA, EB in HL.
  assert (F : Forall (fun b => 48 <= b <= 57) [v0; v1; v2; v3]).
  { apply SWZ.swar_digits; [repeat constructor; lia|].
    replace (SWZ.lev [v0; v1; v2; v3]) with V by (cbn [SWZ.lev]; lia).
    replace (SWZ.rep 70 (length [v0; v1; v2; v3])) with 1179010630 by reflexivity.
    replace (SWZ.rep 48 (length [v0; v1; v2; v3])) with 808464432 by reflexivity.
    replace (SWZ.rep 128 (length [v0; v1; v2; v3])) with ((18446744071570489472 mod 2 ^ 64) mod 2 ^ 32) by reflexivity.
    replace (8 * Z.of_nat (length [v0; v1; v2; v3])) with 32 by reflexivity.
    replace ((V - 808464432) mod 2 ^ 32) with ((V + 18446744072901087184) mod 2 ^ 32).
    - exact HL.
    - rewrite <- (Z_mod_plus_full (V - 808464432) 4294967296 (2 ^ 32)). f_equal. lia. }
  repeat (apply Forall_cons_iff in F as [? F]). repeat split; lia.
Qed.

(* [comment removed for export] *)
Lemma mod_shift : forall X X' d C, X' = X + d -> X mod 2 ^ 64 = C -> 0 <= C + d < 2 ^ 64 -> X' mod 2 ^ 64 = C + d.
Proof. intros X X' d C -> H R. rewrite <- Zplus_mod_idemp_l, H. apply Z.mod_small. exact R. Qed.

(* [comment removed for export] *)
Lemma slt_lit_false : forall segs m E a c, 0 <= c < 2 ^ 63 -> sc_denot segs m E (SCBr false BC_LT a (ELit c)) ->
  c <= u (edenot E a) < 2 ^ 63.
Proof.
  intros segs m E a c Hc H. cbn [sc_denot branch_taken] in H. unfold bv_lts in H.
  apply Z.ltb_ge in H. cbn [edenot] in H. rewrite (bv_signed_small (Z_to_bv 64 c)) in H by (rewrite Z_to_bv_unsigned; unfold bv_wrap;
    change (bv_modulus 64) with (2 ^ 64); rewrite Z.mod_small; lia).
  rewrite Z_to_bv_unsigned in H. unfold bv_wrap in H. change (bv_modulus 64) with (2 ^ 64) in H. rewrite Z.mod_small in H by lia.
  pose proof (bv_unsigned_in_range 64 (edenot E a)) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with (2 ^ 64) in R.
  destruct (Z.lt_ge_cases (u (edenot E a)) (2 ^ 63)) as [Hl|Hg].
  - rewrite bv_signed_small in H by exact Hl. lia.
  - exfalso. rewrite bv_signed_hi in H by exact Hg. lia.
Qed.

(* [comment removed for export] *)
Lemma scbr_u : forall segs m E t c a b, sc_denot segs m E (SCBr t c a b) ->
  match c with
  | BC_LTU => if t then u (edenot E a) < u (edenot E b) else u (edenot E b) <= u (edenot E a)
  | BC_GEU => if t then u (edenot E b) <= u (edenot E a) else u (edenot E a) < u (edenot E b)
  | BC_EQ => if t then u (edenot E a) = u (edenot E b) else u (edenot E a) <> u (edenot E b)
  | BC_NE => if t then u (edenot E a) <> u (edenot E b) else u (edenot E a) = u (edenot E b)
  | _ => True
  end.
Proof.
  intros segs m E t c a b H. cbn [sc_denot branch_taken] in H. unfold bv_ltu, bv_eqb in H.
  destruct c, t; cbn iota beta; try exact I.
  - apply Z.eqb_eq in H. exact H.
  - apply Z.eqb_neq in H. exact H.
  - apply negb_true_iff, Z.eqb_neq in H. exact H.
  - apply negb_false_iff, Z.eqb_eq in H. exact H.
  - apply Z.ltb_lt in H. exact H.
  - apply Z.ltb_ge in H. exact H.
  - apply negb_true_iff, Z.ltb_ge in H. exact H.
  - apply negb_false_iff, Z.ltb_lt in H. exact H.
Qed.

(* [comment removed for export] *)
Lemma cnt0_rng' : forall segs m a n, 0 <= n -> 0 <= SNG.cnt0 segs m a (Z.to_nat n) <= n.
Proof. intros segs m a n H. pose proof (SNG.cnt0_rng segs m a (Z.to_nat n)). lia. Qed.

(* [comment removed for export] *)
Lemma swar4_bridge_ext : forall v0 v1 v2 v3 H S A B,
  S = v0 + 256 * v1 + 65536 * v2 + 16777216 * v3 + 4294967296 * H ->
  0 <= v0 < 256 -> 0 <= v1 < 256 -> 0 <= v2 < 256 -> 0 <= v3 < 256 -> 0 <= A -> 0 <= B ->
  A mod 2 ^ 32 = (S + 1179010630) mod 2 ^ 32 -> B mod 2 ^ 32 = (S + 18446744072901087184) mod 2 ^ 32 ->
  Z.land (Z.lor A B) (18446744071570489472 mod 2 ^ 64) = 0 ->
  48 <= v0 <= 57 /\ 48 <= v1 <= 57 /\ 48 <= v2 <= 57 /\ 48 <= v3 <= 57.
Proof.
  intros v0 v1 v2 v3 H S A B HS H0 H1 H2 H3 HA HB EA EB HC.
  apply (swar4_bridge v0 v1 v2 v3 (v0 + 256 * v1 + 65536 * v2 + 16777216 * v3) A B eq_refl H0 H1 H2 H3 HA HB); [ | | exact HC].
  - rewrite EA, HS. rewrite <- (Z_mod_plus_full (v0 + 256 * v1 + 65536 * v2 + 16777216 * v3 + 1179010630) H (2 ^ 32)). f_equal. lia.
  - rewrite EB, HS. rewrite <- (Z_mod_plus_full (v0 + 256 * v1 + 65536 * v2 + 16777216 * v3 + 18446744072901087184) H (2 ^ 32)). f_equal. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac sn_forall H :=
  repeat match type of H with
  | Forall _ (_ :: _) => apply Forall_cons_iff in H; let X := fresh "G" in destruct H as [X H]
  | Forall _ [] => clear H
  end.

Ltac sn_hyps := repeat match goal with H : _ /\ _ |- _ => destruct H end.

(* [comment removed for export] *)
Ltac sn_lin1 segs E m HK e :=
  let l := eval vm_compute in (lin_of e) in
  first [ lazymatch e with EAlu ALU_AND ?a (ELit 255) => rewrite (u_and255 E a) in * end
        | lazymatch e with EAlu ALU_AND ?a (ELit ?c) => rewrite (u_and_lit E a c) in * end
        | lazymatch e with EAlu ALU_OR ?a ?b => rewrite (u_or E a b) in * end
        | lazymatch e with EAluw _ _ _ => fail end
        | rewrite (VP.u_lin' segs E m _ e l HK ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) in *
        | lazymatch type of HK with know_ok _ _ _ ?kn =>
            let r := eval vm_compute in (krng_of kn e) in
            lazymatch r with Some (?lo, ?hi) =>
              rewrite (u_lin_fact segs E m _ e lo hi l HK ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                         ltac:(vm_compute; reflexivity)) in * end end
        | rewrite (u_lin_mod E e l ltac:(vm_compute; reflexivity)) in * ].
Ltac sn_lin segs E m HK :=
  repeat match goal with
  | H : context [bv_unsigned (edenot E (ELit ?z))] |- _ => rewrite (u_lit_small E z ltac:(lia)) in H
  | |- context [bv_unsigned (edenot E (ELit ?z))] => rewrite (u_lit_small E z ltac:(lia))
  | H : context [bv_unsigned (edenot E ?e)] |- _ =>
      lazymatch e with EVar _ => fail | ELit _ => fail | EExt _ _ _ _ => fail | EAluw _ _ _ => fail | _ => idtac end;
      sn_lin1 segs E m HK e
  | |- context [bv_unsigned (edenot E ?e)] =>
      lazymatch e with EVar _ => fail | ELit _ => fail | EExt _ _ _ _ => fail | EAluw _ _ _ => fail | _ => idtac end;
      sn_lin1 segs E m HK e
  end;
  cbn [VP.pden VP.psum VP.pterm fst snd Z.eqb Pos.eqb lin_of ladd lscale lscale_terms lins snorm] in *;
  unfold uE in *; rewrite ?VP.edenot_EVar in *.

(* [comment removed for export] *)
Ltac sn_pre :=
  unfold SG.vc_holds; cbn [SG.vc_kn SG.vc_path SG.vc_log SG.vc_src SG.vc_tgt SG.vc_facts];
  let E := fresh "E" in let m := fresh "m" in let HK := fresh "HK" in let HP := fresh "HP" in let HL := fresh "HL" in
  let HS := fresh "HS" in
  intros E m HK HP HL HS;
  lazymatch type of HK with know_ok ?segs _ _ ?kn =>
    let lx := eval vm_compute in (kdigestX kn kn) in
    let ZX := fresh "ZX" in
    assert (ZX : Forall (VP.zf_den E) lx)
      by (replace lx with (kdigestX kn kn) by (vm_compute; reflexivity); exact (kdigestX_sound segs E m kn kn HK HK));
    VP.vp_forall ZX;
    VP.vp_digest segs E m HK HP;
    (* [comment removed for export] *)
    repeat match goal with
      | P : sc_denot _ m E (SCReadBase (SA ?a ?k) 1 false (EVar ?v)) |- _ =>
          let B := fresh "B" in let R := fresh "R" in destruct (rr1 segs m E a k v P) as [B R]; clear P;
          rewrite u_adenot in B;
          try rewrite (u_ext1_v E v ltac:(lia)) in *
      end;
    (* [comment removed for export] *)
    repeat match goal with
      | P : sc_denot ?segs m E (SCBr false BC_LT ?a (ELit ?c)) |- _ =>
          let Q := fresh "Q" in pose proof (slt_lit_false segs m E a c ltac:(lia) P) as Q; clear P
      end;
    (* [comment removed for export] *)
    repeat match goal with
      | P : sc_denot ?segs m E (SCBr ?t ?c ?a ?b) |- _ =>
          lazymatch c with BC_LT => fail | BC_GE => fail | _ => idtac end;
          let Q := fresh "Q" in pose proof (scbr_u segs m E t c a b P) as Q; cbn beta iota in Q; clear P
      end;
    unfold SG.gholds in HS; sn_forall HS;
    cbn [SNU.snu_gp SNG.sng_gp map ST.g_id ST.g_args] in *;   (* [comment removed for export] *)
    unfold SNG.g_dig, SNG.g_dot, SNG.g_frac, SNG.g_zrun, SNG.g_nzd, SNG.g_z0 in *;
    sn_lin segs E m HK
  end.

Lemma digs_app_eq : forall segs m a a0 n N k, a = a0 -> N = n + k -> 0 <= n -> SNG.digs segs m a0 n -> SNG.digs segs m (a0 + n) k ->
  SNG.digs segs m a N.
Proof. intros segs m a a0 n N k -> -> Hn H1 H2. exact (SNG.digs_app segs m a0 n k Hn H1 H2). Qed.
Lemma digs_lit_eq : forall segs m a N k, N = k -> SNG.digs segs m a k -> SNG.digs segs m a N.
Proof. intros segs m a N k -> H. exact H. Qed.

Lemma bat_eq : forall segs m x y b, SNG.bat segs m x b -> x = y -> SNG.bat segs m y b.
Proof. intros segs m x y b H <-. exact H. Qed.

(* [comment removed for export] *)
Ltac sn_goal :=
  lazymatch goal with |- SG.gholds _ _ _ _ /\ know_ok _ _ _ _ =>
    split; [unfold SG.gholds; repeat (apply Forall_cons; [|]); try apply Forall_nil | ]
  end;
  cbn [ST.g_id ST.g_args] in *; cbn [SNU.snu_gp] in *;
  (* [comment removed for export] *)
  repeat match goal with
  | HK : know_ok ?segs ?E ?m _, HL : log_flat ?E ?lg |- SNG.sng_gp ?segs ?id (map (edenot ?E) ?args) (mem_denot ?E ?m (?x :: ?r)) =>
      apply (tgt_transfer segs E m _ (x :: r) id args HK HL); [vm_compute; reflexivity | ]
  end;
  cbn [SNG.sng_gp map ST.g_id ST.g_args mem_denot] in *;
  unfold SNG.g_dig, SNG.g_dot, SNG.g_frac, SNG.g_zrun, SNG.g_nzd, SNG.g_z0 in *;
  try (lazymatch goal with |- know_ok _ _ _ _ => unfold know_ok; repeat (apply Forall_cons; [|]); try apply Forall_nil end);
  cbn [kentry_ok] in *;
  try (lazymatch goal with |- _ \/ _ => unfold estart, elenZ; cbn [a_base a_off] end).

(* [comment removed for export] *)
Ltac sn_bats :=
  repeat match goal with
  | B : SNG.bat _ _ ((?x + 0) mod 2 ^ 64) _ |- _ => rewrite Z.add_0_r in B
  | B : SNG.bat _ _ ?a _ |- _ =>
      match a with context [?x mod 2 ^ 64] =>
        lazymatch x with context [_ mod _] => fail | _ => idtac end;
        rewrite (Z.mod_small x (2 ^ 64)) in B by lia end
  end.

(* [comment removed for export] *)
Ltac find_byte segs m x j k := match goal with B : SNG.bat segs m ?y ?v |- _ => assert (y = x + j) as _ by ring; k v end.

(* [comment removed for export] *)
Ltac sn_swar8 segs m x :=
  find_byte segs m x 0 ltac:(fun v0 => find_byte segs m x 1 ltac:(fun v1 => find_byte segs m x 2 ltac:(fun v2 =>
  find_byte segs m x 3 ltac:(fun v3 => find_byte segs m x 4 ltac:(fun v4 => find_byte segs m x 5 ltac:(fun v5 =>
  find_byte segs m x 6 ltac:(fun v6 => find_byte segs m x 7 ltac:(fun v7 =>
    match goal with Hc : Z.land (Z.lor ((?S + 5063812098665367110) mod 2 ^ 64) _) _ = 0 |- _ =>
      let SW := fresh "SW" in
      pose proof (swar8_bridge v0 v1 v2 v3 v4 v5 v6 v7 S ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                    ltac:(lia) ltac:(lia) ltac:(lia) Hc) as SW; sn_hyps end)))))))).
Ltac sn_swar4_with segs m x v0 v1 v2 v3 h :=
    match goal with
    | Hc : Z.land (Z.lor ?A ?B) (18446744071570489472 mod 2 ^ 64) = 0,
      WA : ?A mod 2 ^ 32 = (?S + 1179010630) mod 2 ^ 32, WB : ?B mod 2 ^ 32 = (?S + 18446744072901087184) mod 2 ^ 32 |- _ =>
      let SW := fresh "SW" in
      pose proof (swar4_bridge_ext v0 v1 v2 v3 h S A B ltac:(ring) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                    ltac:(lia) ltac:(lia) WA WB Hc) as SW; sn_hyps end.
Ltac sn_swar4 segs m x :=
  find_byte segs m x 0 ltac:(fun v0 => find_byte segs m x 1 ltac:(fun v1 => find_byte segs m x 2 ltac:(fun v2 =>
  find_byte segs m x 3 ltac:(fun v3 =>
    first [ sn_swar4_with segs m x v0 v1 v2 v3 0
          | find_byte segs m x 4 ltac:(fun v4 => find_byte segs m x 5 ltac:(fun v5 => find_byte segs m x 6 ltac:(fun v6 =>
            find_byte segs m x 7 ltac:(fun v7 =>
              sn_swar4_with segs m x v0 v1 v2 v3 (v4 + 256 * v5 + 65536 * v6 + 16777216 * v7))))) ])))).

(* [comment removed for export] *)
Ltac sn_digs_lit :=
  lazymatch goal with |- SNG.digs ?segs ?m ?x ?k =>
    let j := fresh "j" in let Hj := fresh "Hj" in intros j Hj;
    let k' := eval vm_compute in k in
    try lazymatch k' with 8 => sn_swar8 segs m x | 4 => sn_swar4 segs m x
                        | 12 => (try sn_swar8 segs m x); sn_swar4 segs m (x + 8) end;
    let rec cases n := lazymatch n with
      | 0 => lia
      | _ => let n1 := eval vm_compute in (n - 1) in
             destruct (Z.eq_dec j n1) as [->|?]; [ | cases n1 ] end in
    cases k';
    lazymatch goal with |- exists b, SNG.bat _ _ ?xa b /\ _ =>
    match goal with B : SNG.bat _ _ ?y ?b |- _ =>
      assert (y = xa) as _ by ring;
      exists b; split; [apply (bat_eq segs m y); [exact B | ring] | unfold SNG.isdig; first [split; assumption | lia]] end end
  end.

(* [comment removed for export] *)

Ltac sn_digit_facts :=
  repeat match goal with
  | B : SNG.bat ?segs ?m ?x ?v, D : SNG.digs ?segs ?m ?a ?n |- _ =>
      lazymatch goal with _ : 48 <= v <= 57 |- _ => fail | _ => idtac end;
      let Hd := fresh "Hd" in assert (Hd : 48 <= v <= 57) by (apply (digs_at segs m a n x v D); [lia | exact B])
  end.

Ltac sn_mods :=
  repeat match goal with
  | H : Z.land _ _ = _ |- _ => fail
  | H : context [?x mod 2 ^ 64] |- _ => lazymatch type of H with Z.land _ _ = _ => fail | _ => idtac end;
      rewrite (Z.mod_small x (2 ^ 64)) in H by lia
  | |- context [?x mod 2 ^ 64] => rewrite (Z.mod_small x (2 ^ 64)) by lia
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac sn_bat_goal :=
  lazymatch goal with |- SNG.bat ?segs ?m ?x ?b =>
    first [ match goal with B : SNG.bat segs m ?y ?c |- _ =>
              assert (y = x) as _ by ring; replace b with c by lia; apply (bat_eq segs m y x c B); ring end
          | match goal with B : SNG.bat segs m ?y ?c |- _ =>
              replace b with c by lia; apply (bat_eq segs m y x c B); lia end ] end.

(* [comment removed for export] *)
Ltac sn_with_k N n kont :=
  let rec go ks eqt := lazymatch ks with
    | nil => fail
    | cons ?k ?r => tryif (assert (N = n + k) as _ by eqt) then kont k else go r eqt end in
  let ks := constr:([0; 1; 4; 8; 12; 2; 3; 5; 6; 7; 9; 10; 11]) in
  tryif (go ks ltac:(ring)) then idtac else go ks ltac:(lia).

Ltac sn_digs_goal :=
  lazymatch goal with |- SNG.digs ?segs ?m ?a ?N =>
    tryif (lazymatch goal with H : SNG.digs segs m a _ |- _ => idtac end) then
      lazymatch goal with H : SNG.digs segs m a ?n |- _ =>
        sn_with_k N n ltac:(fun k => apply (digs_app_eq segs m a a n N k eq_refl ltac:(first [ring | lia]) ltac:(lia) H); sn_digs_lit)
      end
    else sn_with_k N 0 ltac:(fun k => apply (digs_lit_eq segs m a N k ltac:(first [ring | lia])); sn_digs_lit)
  end.

Ltac sn_zdot_goal :=
  lazymatch goal with |- SNG.zdot ?segs ?m ?a ?N =>
    first [ replace N with 0 by lia; apply SNG.zdot_0
          | match goal with H : SNG.zdot segs m a ?n |- _ =>
              first [ replace N with n by lia; exact H
                    | replace N with (n + 1) by lia;
                      match goal with B : SNG.bat segs m ?y ?c |- _ =>
                        apply (SNG.zdot_app1 segs m a n c); [lia | exact H | apply (bat_eq segs m y); [exact B | lia] | lia] end ] end ]
  end.

Ltac sn_cnt_goal :=
  lazymatch goal with |- ?k = SNG.cnt0 ?segs ?m ?a (Z.to_nat ?N) =>
    repeat match goal with H : _ = SNG.cnt0 segs m a (Z.to_nat ?n) |- _ =>
      lazymatch goal with _ : 0 <= SNG.cnt0 segs m a (Z.to_nat n) <= n |- _ => fail | _ => idtac end;
      pose proof (cnt0_rng' segs m a n ltac:(lia)) end;
    first [ replace N with 0 by lia; change (SNG.cnt0 segs m a (Z.to_nat 0)) with 0; lia
          | match goal with H : ?k0 = SNG.cnt0 segs m a (Z.to_nat ?n) |- _ =>
              first [ replace N with n by lia; lia
                    | replace N with (n + 1) by lia;
                      match goal with Z : SNG.zdot segs m a n, B : SNG.bat segs m ?y ?c |- _ =>
                        let S := fresh "S" in
                        assert (B' : SNG.bat segs m (a + n) c) by (apply (bat_eq segs m y); [exact B | lia]);
                        destruct (zrun_step segs m a n k0 c ltac:(lia) Z H B' ltac:(lia)) as [_ S];
                        destruct (Z.eqb_spec c 48); lia end ] end ]
  end.

Lemma zeros_cong : forall segs m a a0 n n0, a = a0 -> n = n0 -> SNG.zeros segs m a0 n0 -> SNG.zeros segs m a n.
Proof. intros segs m a a0 n n0 -> -> H. exact H. Qed.

Ltac sn_z0_goal :=
  lazymatch goal with |- _ = 0 -> SNG.zeros ?segs ?m ?a ?n =>
    let Hi := fresh "Hi" in intros Hi; sn_digit_facts; sn_mods;
    first [ apply (zeros_cong segs m a a n 0 ltac:(lia) ltac:(lia)); apply SNG.zeros_0
          | match goal with H : _ = 0 -> SNG.zeros segs m ?a0 ?n0 |- _ =>
              first [ apply (zeros_cong segs m a a0 n n0 ltac:(lia) ltac:(lia)); apply H; lia
                    | apply (zeros_cong segs m a a0 n (n0 + 1) ltac:(lia) ltac:(lia));
                      apply (SNG.zeros_app1 segs m a0 n0); [lia | apply H; lia | sn_bat_goal ] ] end ]
  end.

(* [comment removed for export] *)
Ltac sn_nz :=
  lazymatch goal with |- 1 <= ?X =>
    first [ lia | (sn_digit_facts; sn_mods; lia)
          | sn_digit_facts;
            match goal with N : (exists j, 0 <= j < ?il /\ exists b, SNG.bat ?segs ?m (?ip + j) b /\ 49 <= b <= 57) \/
                                (exists j, 0 <= j < ?fl /\ exists b, SNG.bat ?segs ?m (?fp + j) b /\ 49 <= b <= 57) |- _ =>
              let Z1 := fresh "Z1" in let Z2 := fresh "Z2" in
              assert (Z1 : X = 0 -> SNG.zeros segs m ip il) by sn_z0_goal;
              assert (Z2 : X = 0 -> SNG.zeros segs m fp fl) by sn_z0_goal;
              pose proof (SNG.z0_final segs m ip il fp fl X N Z1 Z2); lia end ]
  end.

(* [comment removed for export] *)
Ltac sn_nzd_goal :=
  lazymatch goal with |- (exists j, 0 <= j < ?il /\ exists b, SNG.bat ?segs ?m (?ip + j) b /\ 49 <= b <= 57) \/
                         (exists j, 0 <= j < ?fl /\ exists b, SNG.bat ?segs ?m (?fp + j) b /\ 49 <= b <= 57) =>
    match goal with Ck0 : _ = SNG.cnt0 segs m ?ipz0 (Z.to_nat ?n0) |- _ => pose proof (cnt0_rng' segs m ipz0 n0 ltac:(lia)) end;
    match goal with
    | Zd : SNG.zdot segs m ?ipz ?n, Ck : ?k = SNG.cnt0 segs m ?ipz (Z.to_nat ?n),
      D1 : SNG.digs segs m ?ip1 ?il1, D2 : SNG.digs segs m ?fp2 ?fl2, Fr : (?flx = 0 \/ _) |- _ =>
        first [
          (* [comment removed for export] *)
          match goal with B : SNG.bat segs m ?z ?v |- _ =>
            apply (SNG.nzd_intro' segs m ip il fp fl (ipz + n) k); [lia | lia | lia
              | apply (digs_lit_eq segs m ip il il1 ltac:(lia)); replace ip with ip1 by lia; exact D1
              | apply (digs_lit_eq segs m fp fl fl2 ltac:(lia)); replace fp with fp2 by lia; exact D2
              | destruct Fr as [Fr|Fr]; [left; lia | right; sn_hyps; repeat split; first [lia | sn_bat_goal]]
              | lia | replace (ipz + n - ip) with n by lia; replace ip with ipz by lia; exact Zd
              | replace (ipz + n - ip) with n by lia; replace ip with ipz by lia; lia
              | left; exists v; split; [apply (bat_eq segs m z); [exact B | lia] | lia] | lia ] end
        | (* [comment removed for export] *)
          match goal with B : SNG.bat segs m ?y ?c |- _ =>
            let S1 := fresh "S1" in let S2 := fresh "S2" in
            assert (B' : SNG.bat segs m (ipz + n) c) by (apply (bat_eq segs m y); [exact B | lia]);
            destruct (zrun_step segs m ipz n k c ltac:(lia) Zd Ck B' ltac:(lia)) as [S1 S2];
            apply (SNG.nzd_intro' segs m ip il fp fl (ipz + (n + 1)) (k + (if Z.eqb c 48 then 1 else 0))); [lia | lia | lia
              | apply (digs_lit_eq segs m ip il il1 ltac:(lia)); replace ip with ip1 by lia; exact D1
              | apply (digs_lit_eq segs m fp fl fl2 ltac:(lia)); replace fp with fp2 by lia; exact D2
              | destruct Fr as [Fr|Fr]; [left; lia | right; sn_hyps; repeat split; first [lia | sn_bat_goal]]
              | lia | replace (ipz + (n + 1) - ip) with (n + 1) by lia; replace ip with ipz by lia; exact S1
              | replace (ipz + (n + 1) - ip) with (n + 1) by lia; replace ip with ipz by lia; symmetry; exact S2
              | right; lia | destruct (Z.eqb_spec c 48); lia ] end ]
    end
  end.

(* [comment removed for export] *)
Ltac sn_clear :=
  repeat match goal with
  | H : know_ok _ _ _ _ |- _ => clear H
  | H : log_flat _ _ |- _ => clear H
  | H : sc_denot _ _ _ _ |- _ => clear H
  end.
(* [comment removed for export] *)
Ltac sn_hmods :=
  repeat match goal with
  | H : SNG.digs _ _ ?a (?x mod 2 ^ 64) |- _ => rewrite (Z.mod_small x (2 ^ 64)) in H by lia
  | H : SNG.digs _ _ (?x mod 2 ^ 64) _ |- _ => rewrite (Z.mod_small x (2 ^ 64)) in H by lia
  | H : SNG.zdot _ _ ?a (?x mod 2 ^ 64) |- _ => rewrite (Z.mod_small x (2 ^ 64)) in H by lia
  | H : SNG.zdot _ _ (?x mod 2 ^ 64) _ |- _ => rewrite (Z.mod_small x (2 ^ 64)) in H by lia
  | H : _ -> SNG.zeros _ _ ?a (?x mod 2 ^ 64) |- _ => rewrite (Z.mod_small x (2 ^ 64)) in H by lia
  | H : _ -> SNG.zeros _ _ (?x mod 2 ^ 64) _ |- _ => rewrite (Z.mod_small x (2 ^ 64)) in H by lia
  end.
(* [comment removed for export] *)
Ltac sn_gmods := repeat match goal with |- context [?x mod 2 ^ 64] => rewrite (Z.mod_small x (2 ^ 64)) by lia end.

(* [comment removed for export] *)
Ltac sn_aluw :=
  repeat match goal with
  | H : context [bv_unsigned (edenot ?E (EAluw ALU_ADD ?a ?b))] |- _ =>
      lazymatch goal with _ : bv_unsigned (edenot E (EAluw ALU_ADD a b)) mod 2 ^ 32 = _ |- _ => fail | _ => idtac end;
      let W := fresh "W" in pose proof (u_aluw_add_low E a b) as W;
      let W2 := fresh "W" in pose proof (bv_unsigned_in_range 64 (edenot E (EAluw ALU_ADD a b))) as W2;
      unfold bv_modulus in W2; change (2 ^ Z.of_N 64) with (2 ^ 64) in W2
  end.

Ltac sn_ext :=
  repeat match goal with
  | H : context [bv_unsigned (edenot ?E (EExt false 0 1 (EVar ?v)))] |- _ => rewrite (u_ext1_v E v ltac:(lia)) in H
  | |- context [bv_unsigned (edenot ?E (EExt false 0 1 (EVar ?v)))] => rewrite (u_ext1_v E v ltac:(lia))
  end.

Ltac sn_clear_bytes := repeat match goal with H : SNG.bat _ _ _ _ |- _ => clear H | H : context [Z.land _ _] |- _ => clear H end.

Ltac sn_leaf :=
  lazymatch goal with
  | |- SNG.digs _ _ _ _ => sn_digs_goal
  | |- SNG.bat _ _ _ _ => sn_bat_goal
  | |- SNG.zdot _ _ _ _ => sn_zdot_goal
  | |- _ = SNG.cnt0 _ _ _ _ => sn_cnt_goal
  | |- _ = 0 -> SNG.zeros _ _ _ _ => sn_z0_goal
  | |- 1 <= _ => sn_nz
  | |- (exists j, _) \/ (exists j, _) => first [ sn_nzd_goal | (exfalso; lia) ]
  | |- _ = 0 \/ _ => first [ left; lia | right; repeat split; first [lia | sn_bat_goal] ]
  | |- _ \/ _ => first [ lia | (sn_clear_bytes; unfold VP.disj in *; lia) ]
  | |- Forall _ [] => constructor
  | |- _ => first [ lia | (sn_digit_facts; sn_mods; lia) ]
  end.

Ltac sn_solve :=
  sn_pre; sn_goal;
  lazymatch goal with HK : know_ok ?segs ?E ?m _ |- _ => sn_lin segs E m HK; sn_aluw; sn_lin segs E m HK end;
  sn_ext; sn_bats; sn_hyps; sn_clear; sn_hmods; sn_gmods;
  repeat split; solve [sn_leaf].

End SNV.
