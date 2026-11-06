(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_H.v; 751 of its 834 lines of code are new or changed and 1060 lines of the source are left out. *)
(* Segment J of LLVMFuzzerTestOneInput's ASan walk (fuzz_identity.asan 0x81974 .. 0x81e60), cut into pieces that
   separate lanes prove. This file holds what the pieces share and their exact statements:
   - the plain-model lemmas (JModel), the U-level lemmas and tactics of the walk;
   - the segment's bookkeeping: jc (what every state of the segment carries besides ecommon), jcut (a state of the
     segment at a slot), WJ (the bytes the segment may write) and jcut_mk (a step from one jcut to the next);
   - the cut points and their facts Pj1 .. Pj4, and the statements of the pieces:
       piece  from                         to                            file                 statement
       L0     0x81974 (inv_I_end)          0x819e0 (Pe0)                 _J.v (jL0)
       B      0x819e0 (Pe0)                0x81a30 (Pj1) or 0x82090      _J.v
       C      0x81a30 Pj1 (BASE + 0x1324)  0x81ab4 Pj2 (BASE + 0x13a8)   _JC.v (j_C)          j_C_stmt
       D      0x81ab4 Pj2                  0x81c34 Pj3 (BASE + 0x1528)   _JD.v (j_D)          j_D_stmt
       E      0x81c34 Pj3                  0x81e18 Pj4 (BASE + 0x170c)   _JE.v (j_E)          j_E_stmt
       F      0x81e18 Pj4                  0x81e60 inv_J_end             _JF.v (j_F)          j_F_stmt
     C: the stem (id.model_name when has_model_name and its first byte is not 0, else switch.table[fam - 1] for
        fam in 1..3, else "REAC"), n4 = ld = 0, w4's shadow, put_dec(w4, &n4, in, 2) at 0x81a9c and
        put_dec(w4, &n4, out, 2) at 0x81ab0.
     D: w4[n4] = 0, the stem copy loop (j_stem_loop), the bcmp of exp_nm + ln - 4 with w4 at 0x81b70 (ln >= 4),
        '-' and the four bytes of w4 appended (0x81b84 .. 0x81bf8), exp_nm[ln] = 0.
     E: the exp_nm -> exp_dp copy loop (j_dp_loop), " (" (0x81cbc .. 0x81ce0), put_dec(exp_dp, &ld, in, 1) at
        0x81cfc, " in / " (0x81d00 .. 0x81d50), put_dec(exp_dp, &ld, out, 1) at 0x81d88, " out)"
        (0x81d8c .. 0x81de0), exp_dp[ld] = 0.
     F: fits (ln < cap_name, memchr(exp_nm, '-', ln) at 0x81e2c, lt < cap_tok, ld < cap_disp) and the two aborts
        `fits && r != 0`, `!fits && r != -1`, which the plain model refutes (n_r = 0 exactly when wok and fits).
     A piece's lane takes any of the contract's Section hypotheses (LLVMFuzzerTestOneInput.v) by their exact names
     and types, and nothing else; a lane that needs one more fact at its start has it added here.
   - the two copy loops, stated for their own lanes (proved in _Jstem.v and _Jdp.v):
   1. j_stem_loop_stmt, the stem copy loop, 0x81b00 (BASE + 0x13f4) .. 0x81b60 (BASE + 0x1454):
        0x81b00 the shadow test of a1 = nm + i        0x81b10 a4 := a2 + s9 = stem + 1 + i
        0x81b14 sb a3,4(a0): the byte s[i] at nm + i  0x81b18 the shadow test of a4
        0x81b28 a3 := stem[1 + i]                     0x81b2c a1++, a0++, s9++
        0x81b38 bnez a3: the next byte, else 0x81b60
      It copies the NUL-terminated stem s into exp_nm and leaves |s| in s9 (x25).
      The two slow paths 0x81b40 and 0x81b4c are the partial-granule tests of the shadow; the one at
      0x81b5c (`jal errpath_load1`, an __asan_report_load1 block) is unreachable under the premises.
   2. j_dp_loop_stmt, the exp_nm -> exp_dp copy loop, 0x81c48 (BASE + 0x153c) .. 0x81ca0 (BASE + 0x1594):
        0x81c48 a1 := s8 + a2 = dp + ld + j           0x81c4c the shadow test of a1
        0x81c5c sb a4,0(a1): the byte s[j] at dp + ld + j
        0x81c60 the shadow test of a0 = nm + 1 + j    0x81c70 a4 := exp_nm[1 + j]
        0x81c74 a0++, a3++, a2++                      0x81c80 bnez a4: the next byte, else 0x81ca0
      It copies the NUL-terminated string s at exp_nm into exp_dp at offset ld, and leaves ld + |s| in a2. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI08 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentFrame IdentCJ IdentRo
IdentProgSig YC1g YC1h YC45 YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Rt Require Import MemchrDef.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require put_dec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec put_dec_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* YC4b turns lia's division and modulo handling off; the address arithmetic here needs it. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the plain model, as the walk reads it ------------------------------------------------------------------ *)
Module JModel.
Import RcIdentModel SlotModel IdentSpec.
Definition digit (b : byte) : bool := (48 <=? bz b) && (bz b <=? 57).
Lemma DEC_digits : forall x m, 0 <= x <= 40 -> (m = 1 \/ m = 2) -> forallb digit (DEC x m) = true.
Proof.
intros x m Hx Hm.
assert (H1 : z_all (fun x => forallb digit (DEC x 1) && forallb digit (DEC x 2)) 41 0 = true) by (vm_compute; reflexivity).
pose proof (z_all_spec _ 41 0 H1 x ltac:(lia)) as H. cbv beta in H. apply andb_true_iff in H as [A1 A2].
destruct Hm as [-> | ->]; assumption.
Qed.
Lemma digit_nz : forall b, digit b = true -> bz b <> 0.
Proof. intros b H. unfold digit in H. apply andb_true_iff in H as [H _]. apply Z.leb_le in H. lia. Qed.
Lemma has_dash_len : forall l, has_dash l = true -> (1 <= length l)%nat.
Proof. intros [|b l] H; [discriminate | cbn; lia]. Qed.
Lemma tok_go_len : forall l d,
  length (tok_go d l) = (length l - (if negb d && has_dash l then 1 else 0))%nat.
Proof.
induction l as [|b l IH]; intros d; [cbn; destruct d; reflexivity|].
cbn [tok_go has_dash existsb length].
destruct d; cbn [negb andb].
- cbn [length]. rewrite IH. cbn [negb andb]. lia.
- destruct (bz b =? 45) eqn:E; cbn [orb].
  + rewrite IH. cbn [negb andb]. destruct (has_dash l); lia.
  + cbn [length]. rewrite IH. cbn [negb andb]. fold (has_dash l).
    destruct (has_dash l) eqn:Hd; [pose proof (has_dash_len l Hd); lia | lia].
Qed.
Lemma n_r_zero : forall inp, n_r inp = 0 -> n_wok inp = true /\ n_fits inp = true.
Proof.
intros inp H. unfold n_r in H. destruct (n_wok inp), (n_fits inp); cbn in H; try discriminate; split; reflexivity.
Qed.
Lemma n_r_cases : forall inp, n_r inp = 0 \/ n_r inp = -1.
Proof. intros inp. unfold n_r. destruct (n_wok inp && n_fits inp); [left | right]; reflexivity. Qed.
Lemma jbytes_lens : forall inp, n_r inp = 0 ->
  Z.of_nat (length (n_EXP_NM inp ++ [zb 0])) <= t_cap_name inp /\
  Z.of_nat (length (n_TK inp ++ [zb 0])) <= t_cap_tok inp /\
  Z.of_nat (length (n_EXP_DP inp ++ [zb 0])) <= t_cap_disp inp.
Proof.
intros inp H. destruct (n_r_zero inp H) as [_ Hf]. unfold n_fits in Hf.
apply andb_true_iff in Hf as [Hf H3]. apply andb_true_iff in Hf as [H1 H2].
apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. apply Z.ltb_lt in H3.
unfold n_ln, n_lt, n_ld in H1, H2, H3.
assert (LT : length (n_TK inp) = (length (n_EXP_NM inp) - (if has_dash (n_EXP_NM inp) then 1 else 0))%nat)
  by (unfold n_TK, TOK; rewrite tok_go_len; reflexivity).
rewrite !length_app. cbn [length]. rewrite LT.
pose proof (has_dash_len (n_EXP_NM inp)) as HL.
unfold n_ln in H2.
revert H2 HL. destruct (has_dash (n_EXP_NM inp)); intros H2 HL; [specialize (HL eq_refl)|]; lia.
Qed.
Lemma okw_zero : okw 0 = true.
Proof. reflexivity. Qed.
Lemma okw_even_ok : forall v, 2 <= v <= 40 -> Z.odd v = false -> okw v = true.
Proof.
intros v H1 H2. unfold okw. apply orb_true_iff. right. apply andb_true_iff. split.
- apply andb_true_iff. split; [apply Z.leb_le; lia | apply Z.leb_le; lia].
- rewrite <- Z.negb_odd, H2. reflexivity.
Qed.
Lemma okw_big : forall v, 40 < v -> okw v = false.
Proof.
intros v H. unfold okw. apply orb_false_iff. split; [apply Z.eqb_neq; lia|].
apply andb_false_iff. left. apply andb_false_iff. right. apply Z.leb_gt. lia.
Qed.
Lemma okw_one : okw 1 = false.
Proof. reflexivity. Qed.
Lemma okw_odd : forall v, Z.odd v = true -> okw v = false.
Proof.
intros v H. unfold okw. apply orb_false_iff. split.
- apply Z.eqb_neq. intros ->. discriminate H.
- apply andb_false_iff. right. rewrite <- Z.negb_odd, H. reflexivity.
Qed.
Lemma wok_true : forall inp, okw (t_in inp) = true -> okw (t_out inp) = true ->
  (t_in inp <> 0 \/ t_out inp <> 0) -> n_wok inp = true.
Proof.
intros inp H1 H2 H3. unfold n_wok. rewrite H1, H2. cbn [andb].
apply negb_true_iff. apply andb_false_iff.
destruct H3 as [H|H]; [left | right]; apply Z.eqb_neq; exact H.
Qed.
Lemma wok_false_in : forall inp, okw (t_in inp) = false -> n_wok inp = false.
Proof. intros inp H. unfold n_wok. rewrite H. reflexivity. Qed.
Lemma wok_false_out : forall inp, okw (t_out inp) = false -> n_wok inp = false.
Proof. intros inp H. unfold n_wok. rewrite H, andb_false_r. reflexivity. Qed.
Lemma wok_false_00 : forall inp, t_in inp = 0 -> t_out inp = 0 -> n_wok inp = false.
Proof.
intros inp H1 H2. unfold n_wok. rewrite H1, H2. cbn [Z.eqb andb negb]. apply andb_false_r.
Qed.
Lemma tin_range : forall inp, 0 <= t_in inp < 256.
Proof. intros. apply inb_range. Qed.
Lemma tout_range : forall inp, 0 <= t_out inp < 256.
Proof. intros. apply inb_range. Qed.
End JModel.

(* ---- the symbolic values the walk reads off its states ------------------------------------------------------ *)
Lemma jU_off : forall E n v c, ew E n = w64 v -> U E (SOff n c) = (v + c) mod M64.
Proof.
intros E n v c H. rewrite U_SOff, H. unfold w64. rewrite Z_to_bv_unsigned.
unfold zcanon, M64, bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Zplus_mod_idemp_l.
Qed.
Lemma jU_lit : forall E z, U E (SLit z) = z mod M64.
Proof. intros E z. rewrite U_SLit. reflexivity. Qed.
Lemma jsv_U : forall E e, sv_denot E e = w64 (U E e).
Proof. intros E e. unfold U, w64. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma jland1 : forall x, 0 <= x -> Z.land x 1 = x mod 2.
Proof. intros x Hx. exact (Z.land_ones x 1 ltac:(lia)). Qed.
Lemma jU_and1 : forall E n v, ew E n = w64 v -> 0 <= v < M64 ->
  U E (SAlu ALU_AND (SOff n 0) (SLit 1)) = (if Z.odd v then 1 else 0).
Proof.
intros E n v H Hv. rewrite U_SAlu. cbn [zalu_raw].
rewrite (jU_off E n v 0 H), jU_lit, Z.add_0_r, (Z.mod_small v) by (unfold M64 in *; lia).
change (1 mod M64) with 1. rewrite jland1 by lia.
rewrite Zmod_odd. destruct (Z.odd v); reflexivity.
Qed.
Lemma jlor_lt : forall a b, 0 <= a < 256 -> 0 <= b < 256 -> 0 <= Z.lor a b < 256.
Proof.
intros a b Ha Hb.
assert (Hn : 0 <= Z.lor a b) by (apply Z.lor_nonneg; lia).
split; [exact Hn|].
destruct (Z.eq_dec (Z.lor a b) 0) as [E0|Hne]; [lia|].
assert (H0 : 0 < Z.lor a b) by lia.
assert (Hla : Z.log2 a < 8).
{ destruct (Z.eq_dec a 0) as [->|Hn2]; [cbn; lia|].
  apply (proj1 (Z.log2_lt_pow2 a 8 ltac:(lia))). change (2 ^ 8) with 256. lia. }
assert (Hlb : Z.log2 b < 8).
{ destruct (Z.eq_dec b 0) as [->|Hn2]; [cbn; lia|].
  apply (proj1 (Z.log2_lt_pow2 b 8 ltac:(lia))). change (2 ^ 8) with 256. lia. }
assert (Hlt : Z.lor a b < 2 ^ 8).
{ apply (proj2 (Z.log2_lt_pow2 (Z.lor a b) 8 H0)). rewrite Z.log2_lor by lia. apply Z.max_lub_lt; assumption. }
change (2 ^ 8) with 256 in Hlt. lia.
Qed.
Lemma jU_sltu_or : forall E m n a b, ew E m = w64 a -> ew E n = w64 b -> 0 <= a < 256 -> 0 <= b < 256 ->
  U E (SAlu ALU_SLTU (SLit 0) (SAlu ALU_OR (SOff m 0) (SOff n 0))) = (if Z.eqb a 0 && Z.eqb b 0 then 0 else 1).
Proof.
intros E m n a b Ha Hb Ra Rb. pose proof (jlor_lt a b Ra Rb) as Hlor.
assert (Hor : U E (SAlu ALU_OR (SOff m 0) (SOff n 0)) = Z.lor a b).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite (jU_off E m a 0 Ha), (jU_off E n b 0 Hb), !Z.add_0_r.
  rewrite (Z.mod_small a), (Z.mod_small b) by (unfold M64; lia).
  apply zcanon_id. unfold M64. lia. }
rewrite U_SAlu. cbn [zalu_raw]. rewrite jU_lit, Hor. change (0 mod M64) with 0.
destruct (Z.eqb_spec a 0) as [->|Hna]; destruct (Z.eqb_spec b 0) as [->|Hnb]; cbn [andb].
- rewrite Z.lor_0_l. reflexivity.
- rewrite Z.lor_0_l. rewrite (proj2 (Z.ltb_lt 0 b)) by lia. reflexivity.
- rewrite Z.lor_0_r. rewrite (proj2 (Z.ltb_lt 0 a)) by lia. reflexivity.
- assert (H0 : 0 < Z.lor a b).
  { destruct (Z.eq_dec (Z.lor a b) 0) as [E0|Ne]; [apply Z.lor_eq_0_iff in E0; lia | lia]. }
  rewrite (proj2 (Z.ltb_lt 0 (Z.lor a b))) by lia. reflexivity.
Qed.
(* The branch conditions of the tree, as arithmetic: the U-form of the test, with the walk's own values for
   the operands (A..G) put in. *)
Ltac jbr1 A B C D F G :=
  repeat match goal with
  | H : branch_taken BC_EQ _ _ = true |- _ =>
      rewrite branch_eq_U, ?A, ?B, ?C, ?D, ?F, ?G, ?jU_lit in H; try (unfold M64 in H); apply Z.eqb_eq in H
  | H : branch_taken BC_EQ _ _ = false |- _ =>
      rewrite branch_eq_U, ?A, ?B, ?C, ?D, ?F, ?G, ?jU_lit in H; try (unfold M64 in H); apply Z.eqb_neq in H
  | H : branch_taken BC_NE _ _ = true |- _ =>
      rewrite branch_ne_U, ?A, ?B, ?C, ?D, ?F, ?G, ?jU_lit in H; try (unfold M64 in H);
      apply negb_true_iff, Z.eqb_neq in H
  | H : branch_taken BC_NE _ _ = false |- _ =>
      rewrite branch_ne_U, ?A, ?B, ?C, ?D, ?F, ?G, ?jU_lit in H; try (unfold M64 in H);
      apply negb_false_iff, Z.eqb_eq in H
  | H : branch_taken BC_LTU _ _ = true |- _ =>
      rewrite branch_ltu_U, ?A, ?B, ?C, ?D, ?F, ?G, ?jU_lit in H; try (unfold M64 in H); apply Z.ltb_lt in H
  | H : branch_taken BC_LTU _ _ = false |- _ =>
      rewrite branch_ltu_U, ?A, ?B, ?C, ?D, ?F, ?G, ?jU_lit in H; try (unfold M64 in H); apply Z.ltb_ge in H
  | H : branch_taken BC_GEU _ _ = true |- _ =>
      rewrite branch_geu_U, ?A, ?B, ?C, ?D, ?F, ?G, ?jU_lit in H; try (unfold M64 in H);
      apply negb_true_iff, Z.ltb_ge in H
  | H : branch_taken BC_GEU _ _ = false |- _ =>
      rewrite branch_geu_U, ?A, ?B, ?C, ?D, ?F, ?G, ?jU_lit in H; try (unfold M64 in H);
      apply negb_false_iff, Z.ltb_lt in H
  end.
(* The parity of a width, from the branch on its lowest bit. *)
Ltac jodd_t x H :=
  match goal with Hh : context[if Z.odd x then _ else _] |- _ =>
    assert (H : Z.odd x = true) by
      (revert Hh; destruct (Z.odd x); intros Hh'; cbn in Hh'; [reflexivity | exfalso; clear - Hh'; lia])
  end.
Ltac jeven_t x H :=
  match goal with Hh : context[if Z.odd x then _ else _] |- _ =>
    assert (H : Z.odd x = false) by
      (revert Hh; destruct (Z.odd x); intros Hh'; cbn in Hh'; [exfalso; clear - Hh'; lia | reflexivity])
  end.
(* The memory of a state reached by runs whose regions are all read-only is the memory it started from. *)
Ltac jkeepgoal :=
  repeat match goal with
  | HFr : frame_of ?E ?rs (mrestrict (w_H ?W) ?m) (mrestrict (w_H ?W) ?m2)
    |- aview ?segs (w_H ?W) ?m2 ?a = aview ?segs (w_H ?W) ?mold ?a =>
      rewrite (kept_of_frame E rs (w_H W) m m2 (fun _ : Z => False) HFr
                 ltac:(intros bb wl wh aa Hin Hr; cbn in Hin;
                       repeat (destruct Hin as [Eqw|Hin]; [injection Eqw as <- <- <-; cbn [base_val] in Hr; lia|]);
                       destruct Hin)
                 a ltac:(assumption) ltac:(intros []))
  end; reflexivity.
(* lia on the arithmetic facts only: every hypothesis that is not an arithmetic fact about the plain model's
   numbers is cleared first, in a sub-proof (a lia over a walk's whole context was measured at 570 s). *)
Ltac jlia :=
  match goal with |- ?G =>
    let H := fresh "J" in
    assert (H : G) by (
      repeat match goal with
      | X : ?T |- _ =>
          lazymatch type of T with
          | Prop => lazymatch T with
                    | context [U _ _] => clear X
                    | context [getr _ _] => clear X
                    | context [ew _ _] => clear X
                    | context [sv_denot _ _] => clear X
                    | _ \/ _ => clear X
                    | context [SlotModel.t_in _] => fail
                    | context [SlotModel.t_out _] => fail
                    | _ => clear X
                    end
          end
      end; lia);
    exact H
  end.

(* ---- memory transfer helpers --------------------------------------------------------------------------------- *)
Section h.
Variable segs : list Segment.
Lemma j_garr8_moved : forall H H' (m m' : word -> option byte) a l,
  (forall k, 0 <= k < Z.of_nat (length l) -> aview segs H' m' (a + k) = aview segs H m (a + k)) ->
  garr8 segs (mrestrict H m) a l -> garr8 segs (mrestrict H' m') a l.
Proof.
intros H H' m m' a l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_moved segs H H' m m' (a + Z.of_nat j) (a + Z.of_nat j) 1 (nth j l 0)); [|exact Hv].
intros k Hk1. replace (a + Z.of_nat j + k) with (a + (Z.of_nat j + k)) by lia. apply Hk. lia.
Qed.
End h.
Lemma j_zero_shadow_moved : forall (rd rd' : reader) Bs a n,
  (forall i, 0 <= i < n / 8 -> rd' (shadow_of_addr Bs a + i) = rd (shadow_of_addr Bs a + i)) ->
  zero_shadow rd Bs a n -> zero_shadow rd' Bs a n.
Proof. intros rd rd' Bs a n Hk Hz i Hi. rewrite (Hk i Hi). exact (Hz i Hi). Qed.
Lemma j_block_shadow_moved : forall (rd rd' : reader) Bs a n,
  (forall i, 0 <= i < (n + 7) / 8 -> rd' (shadow_of_addr Bs a + i) = rd (shadow_of_addr Bs a + i)) ->
  block_shadow rd Bs a n -> block_shadow rd' Bs a n.
Proof.
intros rd rd' Bs a n Hk (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
intros i Hi. rewrite (Hk i Hi). exact (H3 i Hi).
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation bz := RcIdentModel.bz.
#[local] Notation nthb := RcIdentModel.nthb.
#[local] Notation zb := RcIdentModel.zb.
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
(* The Section of LLVMFuzzerTestOneInput.v / _inv.v, in the same order. *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
#[local] Notation ACUT := (acut B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation ECOMMON := (ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation HBLOCKS := (hblocks B).

(* ---- what the segment takes, each as the contract's Section states it (LLVMFuzzerTestOneInput.v) ----------- *)
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis HMT0 : forall s s' : astate, mo_le MT s s' 0.
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Hypothesis HRO : forall rdr, arodata_okS SEGS B RLO RHI rdr -> arodata_okP SEGS pa_relro_lo pa_relro_hi B rdr.
Variable G : list (Z * Z).
Hypothesis GM : globs_marked SEGS B G.
Hypothesis G_IN : In (VAL (A_OBJ 9), 7) G.
Hypothesis G_OUT : In (VAL (A_OBJ 10), 6) G.
Hypothesis G_REAC : In (VAL (A_OBJ 8), 5) G.
Hypothesis HIMG : forall (W : world SEGS) mem,
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> llvmf_img B G W mem.
Hypothesis PSIG : ident_prog_sig_ok (PI := PI).
Hypothesis HPD : put_dec.tput_dec_spec B.
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA IS___interceptor_trampoline_bcmp).
Hypothesis AMEMCHR : amemchr_realizes SEGS B (SIGMA IS___interceptor_trampoline_memchr).
Hypothesis AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
  ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  m_fds md' = m_fds md /\ m_fs md' = m_fs md.

(* The bytes a loop may write: the caller's journal allows them and they are there. *)
Definition jcut_wr (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (lyc : alayout) (Sc : astate) (own : list (Z * Z)) (W : world SEGS) (memL : word -> option byte)
  (q n : Z) : Prop :=
  forall a, q <= a < q + n ->
    awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memL a.

(* ---- 1. the stem copy loop ------------------------------------------------------------------------------- *)
Definition j_stem_loop_stmt : Prop :=
forall (STK sp0 : Z) (FP own : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
  (mem0 : word -> option byte) (md0 : Model) (lyc : alayout) (Sc : astate) (W : world SEGS) (k : Z)
  (nmA stemA : Z) (s : list byte) (i : nat)
  (regsL : bvmap 5 word) (memL : word -> option byte) (mdL : Model),
(* the caller's journal at the loop's head *)
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memL mdL k ->
(* the registers the loop carries *)
getr regsL 3 = w64 (as_gp B) -> getr regsL 4 = w64 (as_tp B) ->
getr regsL 17 = w64 SHADOW_OFF ->
getr regsL 11 = w64 (nmA + Z.of_nat i) ->
getr regsL 10 = w64 (nmA + Z.of_nat i - 4) ->
getr regsL 12 = w64 (stemA + 1) ->
getr regsL 25 = w64 (Z.of_nat i) ->
getr regsL 13 = w64 (bz (nthb s i)) ->
(* the stem: NUL-terminated, no NUL inside, at most 16 bytes *)
(i < length s)%nat -> (length s <= 16)%nat ->
(forall j, (j < length s)%nat -> bz (nthb s j) <> 0) ->
garr8 SEGS (mrestrict (w_H W) memL) stemA (map bv_unsigned (s ++ [zb 0])) ->
range_addressable (aview SEGS (w_H W) memL) SHADOW_OFF stemA (Z.of_nat (length s) + 1) ->
(forall x, stemA + Z.of_nat (length s) < x < stemA + Z.of_nat (length s) - (stemA + Z.of_nat (length s)) mod 8 + 8 ->
   aview SEGS (w_H W) memL x <> None) ->
(* the destination: 32 bytes of the caller's side frame, shadow zero, writable *)
zero_shadow (aview SEGS (w_H W) memL) SHADOW_OFF nmA 32 ->
jcut_wr STK sp0 FP ly S lyc Sc own W memL nmA 32 ->
(* what the loop has copied so far *)
(forall j, (j < i)%nat -> aview SEGS (w_H W) memL (nmA + Z.of_nat j) = Some (bz (nthb s j))) ->
(* where the two ranges lie: both are bytes of the application's own memory, so apart from the shadow band
   (in_app of the caller's side frame gives it through YG0f's in_app_addr; measured:
   without it the destination could be the shadow of the source, and the loop's next shadow test would fail) *)
in_app nmA 32 -> in_app stemA (Z.of_nat (length s) + 1) ->
4096 <= nmA -> nmA + 32 <= alloc_ceiling -> nmA mod 8 = 0 ->
4096 <= stemA -> stemA + Z.of_nat (length s) + 1 <= alloc_ceiling ->
(stemA + Z.of_nat (length s) + 1 <= nmA \/ nmA + 32 <= stemA) ->
SRr SEGS W (cfg_at SEGS (BASE + 0x13f4) regsL memL mdL)
(fun W' c' => W' = W /\ exists regsF memF mdF,
  c' = cfg_at SEGS (BASE + 0x1454) regsF memF mdF /\
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memF mdF k /\
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 17; 18; 19; 20; 21; 22; 23; 24; 26; 27]%bv ->
     getr regsF r = getr regsL r) /\
  getr regsF 25 = w64 (Z.of_nat (length s)) /\
  getr regsF 10 = w64 (nmA + Z.of_nat (length s) - 4) /\
  (forall j, (j < length s)%nat -> aview SEGS (w_H W) memF (nmA + Z.of_nat j) = Some (bz (nthb s j))) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (nmA <= a < nmA + Z.of_nat (length s)) ->
     aview SEGS (w_H W) memF a = aview SEGS (w_H W) memL a) /\
  (forall a, apresent (w_H W) memL a -> apresent (w_H W) memF a)).

(* ---- 2. the exp_nm -> exp_dp copy loop -------------------------------------------------------------------- *)
Definition j_dp_loop_stmt : Prop :=
forall (STK sp0 : Z) (FP own : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
  (mem0 : word -> option byte) (md0 : Model) (lyc : alayout) (Sc : astate) (W : world SEGS) (k : Z)
  (nmA dpA ld0 : Z) (s : list byte) (j : nat)
  (regsL : bvmap 5 word) (memL : word -> option byte) (mdL : Model),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memL mdL k ->
getr regsL 3 = w64 (as_gp B) -> getr regsL 4 = w64 (as_tp B) ->
getr regsL 17 = w64 SHADOW_OFF ->
getr regsL 10 = w64 (nmA + 1 + Z.of_nat j) ->
getr regsL 13 = w64 (nmA + 1 + Z.of_nat j) ->
getr regsL 12 = w64 (ld0 + Z.of_nat j) ->
getr regsL 14 = w64 (bz (nthb s j)) ->
getr regsL 24 = w64 dpA ->
(* the string at exp_nm: NUL-terminated, no NUL inside, at most 21 bytes; it fits in exp_dp at ld0 *)
(j < length s)%nat -> (length s <= 21)%nat ->
(forall m, (m < length s)%nat -> bz (nthb s m) <> 0) ->
garr8 SEGS (mrestrict (w_H W) memL) nmA (map bv_unsigned (s ++ [zb 0])) ->
0 <= ld0 -> ld0 + Z.of_nat (length s) <= 63 ->
zero_shadow (aview SEGS (w_H W) memL) SHADOW_OFF nmA 32 ->
zero_shadow (aview SEGS (w_H W) memL) SHADOW_OFF dpA 64 ->
jcut_wr STK sp0 FP ly S lyc Sc own W memL dpA 64 ->
(forall m, (m < j)%nat -> aview SEGS (w_H W) memL (dpA + ld0 + Z.of_nat m) = Some (bz (nthb s m))) ->
in_app nmA 32 -> in_app dpA 64 ->
4096 <= nmA -> nmA + 32 <= alloc_ceiling -> nmA mod 8 = 0 ->
4096 <= dpA -> dpA + 64 <= alloc_ceiling -> dpA mod 8 = 0 ->
(nmA + 32 <= dpA \/ dpA + 64 <= nmA) ->
SRr SEGS W (cfg_at SEGS (BASE + 0x153c) regsL memL mdL)
(fun W' c' => W' = W /\ exists regsF memF mdF,
  c' = cfg_at SEGS (BASE + 0x1594) regsF memF mdF /\
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memF mdF k /\
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
     getr regsF r = getr regsL r) /\
  getr regsF 12 = w64 (ld0 + Z.of_nat (length s)) /\
  (forall m, (m < length s)%nat -> aview SEGS (w_H W) memF (dpA + ld0 + Z.of_nat m) = Some (bz (nthb s m))) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (dpA + ld0 <= a < dpA + ld0 + Z.of_nat (length s)) ->
     aview SEGS (w_H W) memF a = aview SEGS (w_H W) memL a) /\
  (forall a, apresent (w_H W) memL a -> apresent (w_H W) memF a)).

(* ---- the segment's own bookkeeping ---------------------------------------------------------------------------- *)
Definition jhs (g : ectx) (nm tk dp : Z) : list (Z * Z) :=
  [(nm, Z.max (SlotModel.t_cap_name (e_pl g)) 1); (tk, Z.max (SlotModel.t_cap_tok (e_pl g)) 1);
   (dp, Z.max (SlotModel.t_cap_disp (e_pl g)) 1)].
(* The bytes the segment may change: the machine stack below the machine frame (the callees' windows), the two
   counter slots mf+200 / mf+208, exp_nm .. w4 in the side frame, and the shadow bytes of exp_nm, exp_dp, w4. *)
Definition WJ (g : ectx) (pos mf a : Z) : Prop :=
  (alloc_ceiling <= a < mf) \/ (mf + 200 <= a < mf + 216) \/
  (SFa g pos + 528 <= a < SFa g pos + 696) \/ (shadow_addr (SFa g pos) + 66 <= a < shadow_addr (SFa g pos) + 87).
Definition jkeep (g : ectx) (pos mf : Z) (W2 : world SEGS) (mem2 : word -> option byte)
  (W3 : world SEGS) (mem3 : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ WJ g pos mf a -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) mem2 a.
(* Where everything lies; fixed for the whole segment. *)
Definition jlay (g : ectx) (pos mf nm tk dp : Z) : Prop :=
  alloc_ceiling + ASTACK <= mf /\ e_sp0 g <= 2 ^ 47 /\ e_sp0 g mod 16 = 0 /\
  4096 <= SFa g pos /\ SFa g pos + 1024 <= alloc_ceiling /\ in_app (SFa g pos) 1024 /\ SFa g pos mod 64 = 0 /\
  (forall p n, In (p, n) (jhs g nm tk dp) ->
     4096 <= p /\ p + req_size n <= alloc_ceiling /\ in_app p (req_size n) /\
     (p + req_size n <= SFa g pos \/ SFa g pos + 1024 <= p)) /\
  (e_pl g = [] \/ (4096 <= e_p g /\ e_p g + Z.of_nat (length (e_pl g)) <= alloc_ceiling /\
     in_app (e_p g) (Z.of_nat (length (e_pl g))) /\
     (e_p g + Z.of_nat (length (e_pl g)) <= SFa g pos \/ SFa g pos + 1024 <= e_p g))).
Definition jbytes (g : ectx) (nm tk dp : Z) (W2 : world SEGS) (mem2 : word -> option byte) : Prop :=
  SlotModel.n_r (e_pl g) = 0 ->
  bytes_at8 W2 mem2 nm (SlotModel.n_EXP_NM (e_pl g) ++ [RcIdentModel.zb 0]) /\
  bytes_at8 W2 mem2 tk (SlotModel.n_TK (e_pl g) ++ [RcIdentModel.zb 0]) /\
  bytes_at8 W2 mem2 dp (SlotModel.n_EXP_DP (e_pl g) ++ [RcIdentModel.zb 0]).
(* What every state of the segment carries besides ecommon. *)
Definition jc (g : ectx) (pos mf nm tk dp : Z) (ly2 : alayout) (S2 : astate) (W2 : world SEGS)
  (regs2 : bvmap 5 word) (mem2 : word -> option byte) : Prop :=
  jlay g pos mf nm tk dp /\
  id_at g pos (m_nrec g) W2 mem2 /\ mf_id3 g pos mf W2 mem2 /\ HBLOCKS g ly2 S2 (jhs g nm tk dp) /\
  getr regs2 20 = w64 (SlotModel.t_cap_tok (e_pl g)) /\ getr regs2 21 = w64 tk /\ getr regs2 22 = w64 dp /\
  val_mem SEGS (rd W2 mem2) (mf + 184) 8 nm /\
  val_mem SEGS (rd W2 mem2) (mf + 152) 8 (SlotModel.t_cap_name (e_pl g)) /\
  val_mem SEGS (rd W2 mem2) (mf + 144) 8 (SlotModel.t_cap_disp (e_pl g)) /\
  val_mem SEGS (rd W2 mem2) (mf + 160) 8 (SlotModel.t_in (e_pl g)) /\
  val_mem SEGS (rd W2 mem2) (mf + 168) 8 (SlotModel.t_out (e_pl g)) /\
  val_mem SEGS (rd W2 mem2) (mf + 136) 8 (SlotModel.t_row (e_pl g)) /\
  jbytes g nm tk dp W2 mem2.
(* A state of the segment at slot pc with the extra facts P. *)
Definition jcut (g : ectx) (pos mf nm tk dp : Z) (pc : Z)
  (P : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  : world SEGS -> config -> Prop :=
  ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 7) pc
    (fun ly2 S2 W2 regs2 mem2 md2 => jc g pos mf nm tk dp ly2 S2 W2 regs2 mem2 /\ P ly2 S2 W2 regs2 mem2 md2).

(* Every byte the boundaries speak of lies outside WJ. *)
Lemma jnwj : forall g pos mf nm tk dp a, jlay g pos mf nm tk dp -> e_sp0 g - 336 <= mf <= e_sp0 g - 320 ->
  ((mf <= a < mf + 200) \/ (mf + 216 <= a < 2 ^ 64) \/
   (SFa g pos <= a < SFa g pos + 528) \/ (SFa g pos + 696 <= a < SFa g pos + 1024) \/
   (shadow_addr (SFa g pos) <= a < shadow_addr (SFa g pos) + 66) \/
   (shadow_addr (SFa g pos) + 87 <= a < shadow_addr (SFa g pos) + 128) \/
   (exists p n, In (p, n) (jhs g nm tk dp) /\ p <= a < p + req_size n) \/
   (e_pl g <> [] /\ e_p g <= a < e_p g + Z.of_nat (length (e_pl g)))) ->
  ~ WJ g pos mf a.
Proof.
intros g pos mf nm tk dp a (Hmf0 & Hsp47 & Hsp16 & HSF0 & HSF1 & HSFapp & HSF64 & Hhs & Hinp) Hmf Ha HW.
pose proof asan_consts as (C1 & _).
unfold WJ, shadow_addr, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF, ASTACK in *.
destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[(p & n & Hin & Ha)|(Hne & Ha)]]]]]]].
- clear - Ha HW Hmf0 HSF1 HSF0 C1. lia.
- clear - Ha HW Hmf0 HSF1 HSF0 C1. lia.
- clear - Ha HW Hmf0 HSF1 HSF0 HSFapp C1. lia.
- clear - Ha HW Hmf0 HSF1 HSF0 HSFapp C1. lia.
- clear - Ha HW Hmf0 HSF1 HSF0 HSFapp C1. lia.
- clear - Ha HW Hmf0 HSF1 HSF0 HSFapp C1. lia.
- destruct (Hhs p n Hin) as (P0 & P1 & P2 & P3). clear - Ha HW Hmf0 HSF1 HSF0 HSFapp C1 P0 P1 P2 P3. lia.
- destruct Hinp as [E | (P0 & P1 & P2 & P3)]; [exact (Hne E)|].
  clear - Ha HW Hmf0 HSF1 HSF0 HSFapp C1 P0 P1 P2 P3. lia.
Qed.
Lemma jvm : forall g pos mf W2 mem2 W3 mem3 a n v, jkeep g pos mf W2 mem2 W3 mem3 ->
  (forall k, 0 <= k < Z.of_nat n -> 0 <= a + k < 2 ^ 64 /\ ~ WJ g pos mf (a + k)) ->
  val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W3 mem3) a n v.
Proof.
intros g pos mf W2 mem2 W3 mem3 a n v HK Hn Hv.
apply (val_mem_moved SEGS (w_H W2) (w_H W3) mem2 mem3 a a n v); [|exact Hv].
intros k Hk. destruct (Hn k Hk) as [H1 H2]. exact (HK _ H1 H2).
Qed.
Lemma jga : forall g pos mf W2 mem2 W3 mem3 a l, jkeep g pos mf W2 mem2 W3 mem3 ->
  (forall k, 0 <= k < Z.of_nat (length l) -> 0 <= a + k < 2 ^ 64 /\ ~ WJ g pos mf (a + k)) ->
  garr8 SEGS (rd W2 mem2) a l -> garr8 SEGS (rd W3 mem3) a l.
Proof.
intros g pos mf W2 mem2 W3 mem3 a l HK Hn Hg.
apply (j_garr8_moved SEGS (w_H W2) (w_H W3) mem2 mem3 a l); [|exact Hg].
intros k Hk. destruct (Hn k Hk) as [H1 H2]. exact (HK _ H1 H2).
Qed.


(* The bytes the cuts read outside WJ, by class: at or above mf (the machine frame and the entry's saved words),
   a live block, the side frame, its shadow. A call's tcj_kept keeps each class (IdentCJ.v). *)
Definition jcls (g : ectx) (pos mf : Z) (ly2 : alayout) (S2 : astate) (a : Z) : Prop :=
  mf <= a \/ (exists b m, In (b, m) (ablocks B ly2 S2) /\ b <= a < b + req_size m) \/
  (SFa g pos <= a < SFa g pos + 1024) \/ (shadow_addr (SFa g pos) <= a < shadow_addr (SFa g pos) + 128).
Definition jkeep4 (g : ectx) (pos mf : Z) (ly2 : alayout) (S2 : astate) (W2 : world SEGS)
  (mem2 : word -> option byte) (W3 : world SEGS) (mem3 : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ WJ g pos mf a -> jcls g pos mf ly2 S2 a ->
    aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) mem2 a.
Lemma jkeep4_of : forall g pos mf ly2 S2 W2 mem2 W3 mem3,
  jkeep g pos mf W2 mem2 W3 mem3 -> jkeep4 g pos mf ly2 S2 W2 mem2 W3 mem3.
Proof. intros g pos mf ly2 S2 W2 mem2 W3 mem3 HK a Ha HW _. exact (HK a Ha HW). Qed.
Lemma jvm4 : forall g pos mf ly2 S2 W2 mem2 W3 mem3 a n v, jkeep4 g pos mf ly2 S2 W2 mem2 W3 mem3 ->
  (forall k, 0 <= k < Z.of_nat n -> 0 <= a + k < 2 ^ 64 /\ ~ WJ g pos mf (a + k) /\ jcls g pos mf ly2 S2 (a + k)) ->
  val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W3 mem3) a n v.
Proof.
intros g pos mf ly2 S2 W2 mem2 W3 mem3 a n v HK Hn Hv.
apply (val_mem_moved SEGS (w_H W2) (w_H W3) mem2 mem3 a a n v); [|exact Hv].
intros k Hk. destruct (Hn k Hk) as (H1 & H2 & H3). exact (HK _ H1 H2 H3).
Qed.
Lemma jga4 : forall g pos mf ly2 S2 W2 mem2 W3 mem3 a l, jkeep4 g pos mf ly2 S2 W2 mem2 W3 mem3 ->
  (forall k, 0 <= k < Z.of_nat (length l) -> 0 <= a + k < 2 ^ 64 /\ ~ WJ g pos mf (a + k) /\
     jcls g pos mf ly2 S2 (a + k)) ->
  garr8 SEGS (rd W2 mem2) a l -> garr8 SEGS (rd W3 mem3) a l.
Proof.
intros g pos mf ly2 S2 W2 mem2 W3 mem3 a l HK Hn Hg.
apply (j_garr8_moved SEGS (w_H W2) (w_H W3) mem2 mem3 a l); [|exact Hg].
intros k Hk. destruct (Hn k Hk) as (H1 & H2 & H3). exact (HK _ H1 H2 H3).
Qed.

(* The state after a step of the segment is a jcut again: ecommon and jc hold of every state whose memory agrees
   with the step's start outside WJ at the bytes the cuts read (jkeep4: at or above mf, the live blocks, the side
   frame and its shadow; what tcj_kept keeps across a call, JPieceC measured), whose journal is the entry's with
   the same count, and whose registers 2, 8, 9, 3, 4, 19 (ecommon) and 20, 21, 22 (jc) are the start's. *)
Lemma jcut_mk4 : forall g pos mf nm tk dp pc
  (P : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3,
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W2 mem2 md2 (4 * Z.of_nat (m_nrec g) + 7) ->
  frames S2 = [(4, pos)] -> 0 <= 4 * Z.of_nat (m_nrec g) + 7 <= EV_LLVMF ->
  mo_le MT (e_S g) S2 ((4 * Z.of_nat (m_nrec g) + 7) * (mo_malloc MT 256 + mo_free MT)) ->
  mo_ok MT S2 ((EV_LLVMF - (4 * Z.of_nat (m_nrec g) + 7)) * (mo_malloc MT 256 + mo_free MT)) ->
  ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 -> jc g pos mf nm tk dp ly2 S2 W2 regs2 mem2 ->
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly3 S3 W3 mem3 md3 (4 * Z.of_nat (m_nrec g) + 7) ->
  frames S3 = [(4, pos)] -> Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) ->
  jkeep4 g pos mf ly2 S2 W2 mem2 W3 mem3 ->
  (forall r : bv 5, In r [2; 8; 9; 3; 4; 19; 20; 21; 22]%bv -> getr regs3 r = getr regs2 r) ->
  (forall fd, fd_lookup (m_fds md3) fd = fd_lookup (m_fds md2) fd) -> m_fs md3 = m_fs md2 ->
  P ly3 S3 W3 regs3 mem3 md3 ->
  jcut g pos mf nm tk dp pc P W3 (cfg_at SEGS pc regs3 mem3 md3).
Proof.
intros g pos mf nm tk dp pc P ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3
  HJ2 Hfr2 HK MLE MOK HC HJC HJ3 Hfr3 Hperm KP RS Hfd Hfs HP.
destruct HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & Rs3 & V80 & V192 & V176 & Vra & Vs0 &
  V24 & V32 & V40 & V48 & V56 & V64 & V72 & V80b & V88 & V96 & V104 & Vmf24 & Vflag & HPRE & Hfds & Hfss & Hinb).
destruct HJC as (Hlay & (Hidb & Hidz & Hidk) & Hid3 & (Hhb1 & Hhb2) & R20 & R21 & R22 &
  V184 & V152 & V144 & V160 & V168 & V136 & Hjb).
pose proof Hlay as (Hmf0 & Hsp47 & Hsp16 & HSF0 & HSF1 & HSFapp & HSF64 & Hhs & Hinp).
assert (NW : forall a, ((mf <= a < mf + 200) \/ (mf + 216 <= a < 2 ^ 64) \/
   (SFa g pos <= a < SFa g pos + 528) \/ (SFa g pos + 696 <= a < SFa g pos + 1024) \/
   (shadow_addr (SFa g pos) <= a < shadow_addr (SFa g pos) + 66) \/
   (shadow_addr (SFa g pos) + 87 <= a < shadow_addr (SFa g pos) + 128) \/
   (exists p n, In (p, n) (jhs g nm tk dp) /\ p <= a < p + req_size n) \/
   (e_pl g <> [] /\ e_p g <= a < e_p g + Z.of_nat (length (e_pl g)))) -> ~ WJ g pos mf a)
  by (intros a Ha; exact (jnwj g pos mf nm tk dp a Hlay Hmfb Ha)).
pose proof asan_consts as (C1 & _).
assert (BLK : forall p n, In (p, n) (jhs g nm tk dp) -> In (p, n) (ablocks B ly2 S2))
  by (intros p n Hin; apply (Permutation_in _ (Permutation_sym Hhb1)); apply in_or_app; left; exact Hin).
assert (VH : forall off v, 0 <= off -> off + 8 <= 200 \/ 216 <= off -> mf + off + 8 <= 2 ^ 64 ->
  val_mem SEGS (rd W2 mem2) (mf + off) 8 v -> val_mem SEGS (rd W3 mem3) (mf + off) 8 v).
{ intros off v H0 H1 H2 Hv. apply (jvm4 g pos mf ly2 S2 W2 mem2 W3 mem3 _ 8 v KP); [|exact Hv].
  intros k Hk. cbn in Hk. split; [clear - H0 H2 Hk Hmf0 C1; unfold ASTACK in *; lia|].
  split; [apply NW; clear - H0 H1 H2 Hk; lia | left; clear - H0 Hk; lia]. }
assert (Hsp0 : e_sp0 g - 336 <= mf <= e_sp0 g - 320) by exact Hmfb.
assert (VS : forall off v, 8 <= off <= 104 ->
  val_mem SEGS (rd W2 mem2) (e_sp0 g - off) 8 v -> val_mem SEGS (rd W3 mem3) (e_sp0 g - off) 8 v).
{ intros off v H0 Hv. replace (e_sp0 g - off) with (mf + (e_sp0 g - off - mf)) in * by lia.
  apply VH; [clear - H0 Hsp0; lia | clear - H0 Hsp0; lia | clear - H0 Hsp0 Hsp47; lia | exact Hv]. }
assert (VF : forall off n v, 0 <= off -> off + Z.of_nat n <= 528 \/ 696 <= off -> off + Z.of_nat n <= 1024 ->
  val_mem SEGS (rd W2 mem2) (SFa g pos + off) n v -> val_mem SEGS (rd W3 mem3) (SFa g pos + off) n v).
{ intros off n v H0 H1 H2 Hv. apply (jvm4 g pos mf ly2 S2 W2 mem2 W3 mem3 _ n v KP); [|exact Hv].
  intros k Hk. split; [clear - H0 H2 Hk HSF0 HSF1 C1; lia|].
  split; [apply NW; clear - H0 H1 H2 Hk; lia | right; right; left; clear - H0 H2 Hk; lia]. }
assert (GF : forall off l, 0 <= off -> off + Z.of_nat (length l) <= 528 -> 
  garr8 SEGS (rd W2 mem2) (SFa g pos + off) l -> garr8 SEGS (rd W3 mem3) (SFa g pos + off) l).
{ intros off l H0 H1 Hg. apply (jga4 g pos mf ly2 S2 W2 mem2 W3 mem3 _ l KP); [|exact Hg].
  intros k Hk. split; [clear - H0 H1 Hk HSF0 HSF1 C1; lia|].
  split; [apply NW; clear - H0 H1 Hk; lia | right; right; left; clear - H0 H1 Hk; lia]. }
assert (SHK : forall i, 0 <= i < 66 \/ 87 <= i < 128 ->
  aview SEGS (w_H W3) mem3 (shadow_addr (SFa g pos) + i) = aview SEGS (w_H W2) mem2 (shadow_addr (SFa g pos) + i)).
{ intros i Hi. apply KP; [| apply NW; clear - Hi; lia | right; right; right; clear - Hi; lia].
  unfold shadow_addr, SHADOW_OFF. clear - Hi HSF0 HSF1 C1. lia. }
unfold jcut, acut. exists ly3, S3, regs3, mem3, md3.
split; [reflexivity|]. split; [exact HJ3|]. split; [exact Hfr3|]. split; [exact HK|].
split.
{ eapply (mo_le_mono MT MTL); [exact (mo_le_trans MT MTL _ _ _ _ _ MLE (HMT0 S2 S3))|]. clear. lia. }
split.
{ apply (mo_ok_step MT MTL S2 S3 0); [|exact (HMT0 S2 S3)]. rewrite Z.add_0_l. exact MOK. }
split.
{ unfold ecommon.
  rewrite !(RS 2%bv), !(RS 9%bv), !(RS 8%bv), !(RS 3%bv), !(RS 4%bv), !(RS 19%bv) by (cbn; tauto).
  refine (conj Rsp (conj Rs1 (conj Rs0 (conj Hmfb (conj Hmf32 (conj Rgp (conj Rtp (conj Rs3 _)))))))).
  split; [apply VH; [lia | lia | clear - Hsp0 Hsp47; lia | exact V80]|].
  split; [apply VH; [lia | lia | clear - Hsp0 Hsp47; lia | exact V192]|].
  split; [apply VH; [lia | lia | clear - Hsp0 Hsp47; lia | exact V176]|].
  split; [apply VS; [lia | exact Vra]|]. split; [apply VS; [lia | exact Vs0]|].
  split; [apply VS; [lia | exact V24]|]. split; [apply VS; [lia | exact V32]|].
  split; [apply VS; [lia | exact V40]|]. split; [apply VS; [lia | exact V48]|].
  split; [apply VS; [lia | exact V56]|]. split; [apply VS; [lia | exact V64]|].
  split; [apply VS; [lia | exact V72]|]. split; [apply VS; [lia | exact V80b]|].
  split; [apply VS; [lia | exact V88]|]. split; [apply VS; [lia | exact V96]|].
  split; [apply VS; [lia | exact V104]|].
  split; [apply VH; [lia | lia | clear - Hsp0 Hsp47; lia | exact Vmf24]|].
  split; [apply VF; [lia | cbn; lia | cbn; lia | exact Vflag]|].
  split; [exact HPRE|].
  split; [intros fd; rewrite Hfd; apply Hfds|].
  split; [rewrite Hfs; exact Hfss|].
  unfold bytes_at8 in *. apply (jga4 g pos mf ly2 S2 W2 mem2 W3 mem3 _ _ KP); [|exact Hinb].
  intros k Hk. rewrite length_map in Hk.
  destruct Hinp as [E | (P0 & P1 & P2 & P3)]; [rewrite E in Hk; cbn in Hk; lia|].
  pose proof HPRE as HPRE'. unfold e_pre, tLLVMFuzzerTestOneInput_pre in HPRE'.
  destruct HPRE' as (_ & _ & _ & _ & Hinp' & Hlen & _).
  split; [clear - Hk P0 P1 C1; lia|]. split.
  { apply NW. right; right; right; right; right; right; right.
    split; [intros E; rewrite E in Hk; cbn in Hk; lia | lia]. }
  right; left. destruct Hinp' as [[Hn0 _] | [Hn Hpin]]; [clear - Hn0 Hlen Hk; lia|].
  exists (e_p g), (e_n g). split.
  { apply (Permutation_in _ (Permutation_sym Hhb1)). apply in_or_app. right. exact Hpin. }
  assert (Rq : req_size (e_n g) = e_n g) by (unfold req_size; destruct (Z.eqb_spec (e_n g) 0); lia).
  rewrite Rq. clear - Hk Hlen. lia. }
split; [|exact HP].
unfold jc. refine (conj Hlay _).
split.
{ unfold id_at, bytes_at8, sh_zero, sh_blk in *. refine (conj _ (conj _ _)).
  - apply GF; [unfold V_id; lia | rewrite length_map; unfold m_id; rewrite SlotModel.rec_id_length;
      unfold V_id, RcIdentModel.ID_SIZE; lia | exact Hidb].
  - apply (j_zero_shadow_moved (aview SEGS (w_H W2) mem2)); [|exact Hidz].
    intros i Hi. unfold shadow_of_addr. unfold V_id, N_id in *.
    replace (SHADOW_OFF + (SFa g pos + 352) / 8 + i) with (shadow_addr (SFa g pos) + (44 + i))
      by (unfold shadow_addr; clear - HSF64 Hi; lia).
    apply SHK. clear - Hi. lia.
  - apply (j_block_shadow_moved (aview SEGS (w_H W2) mem2)); [|exact Hidk].
    intros i Hi. unfold shadow_of_addr. unfold V_id, N_id in *.
    replace (SHADOW_OFF + (SFa g pos + 352) / 8 + i) with (shadow_addr (SFa g pos) + (44 + i))
      by (unfold shadow_addr; clear - HSF64 Hi; lia).
    apply SHK. clear - Hi. lia. }
split; [unfold mf_id3 in *; apply VH; [lia | lia | clear - Hsp0 Hsp47; lia | exact Hid3]|].
split; [split; [eapply Permutation_trans; [exact Hperm | exact Hhb1] | exact Hhb2]|].
rewrite !(RS 20%bv), !(RS 21%bv), !(RS 22%bv) by (cbn; tauto).
refine (conj R20 (conj R21 (conj R22 _))).
split; [apply VH; [lia | lia | clear - Hsp0 Hsp47; lia | exact V184]|].
split; [apply VH; [lia | lia | clear - Hsp0 Hsp47; lia | exact V152]|].
split; [apply VH; [lia | lia | clear - Hsp0 Hsp47; lia | exact V144]|].
split; [apply VH; [lia | lia | clear - Hsp0 Hsp47; lia | exact V160]|].
split; [apply VH; [lia | lia | clear - Hsp0 Hsp47; lia | exact V168]|].
split; [apply VH; [lia | lia | clear - Hsp0 Hsp47; lia | exact V136]|].
intros Hr0. destruct (Hjb Hr0) as (B1 & B2 & B3).
destruct (JModel.jbytes_lens (e_pl g) Hr0) as (L1 & L2 & L3).
assert (HB : forall p n l, In (p, n) (jhs g nm tk dp) -> Z.of_nat (length l) <= n ->
  bytes_at8 W2 mem2 p l -> bytes_at8 W3 mem3 p l).
{ intros p n l Hin Hl Hb. unfold bytes_at8 in *. apply (jga4 g pos mf ly2 S2 W2 mem2 W3 mem3 _ _ KP); [|exact Hb].
  intros k Hk. rewrite length_map in Hk. destruct (Hhs p n Hin) as (P0 & P1 & _).
  pose proof (req_size_pos n) as Rq. unfold req_size in *.
  destruct (Z.eqb_spec n 0); [clear - Hk Hl e; lia|].
  split; [clear - Hk Hl P0 P1 C1 Rq; lia|]. split.
  { apply NW. right; right; right; right; right; right; left.
    exists p, n. split; [exact Hin|]. unfold req_size. destruct (Z.eqb_spec n 0); [contradiction | lia]. }
  right; left. exists p, n. split; [exact (BLK p n Hin)|].
  unfold req_size. destruct (Z.eqb_spec n 0); [contradiction | lia]. }
unfold jhs in HB.
refine (conj _ (conj _ _)).
- apply (HB nm (Z.max (SlotModel.t_cap_name (e_pl g)) 1)); [left; reflexivity | lia | exact B1].
- apply (HB tk (Z.max (SlotModel.t_cap_tok (e_pl g)) 1)); [right; left; reflexivity | lia | exact B2].
- apply (HB dp (Z.max (SlotModel.t_cap_disp (e_pl g)) 1)); [right; right; left; reflexivity | lia | exact B3].
Qed.

(* jcut_mk4 with the keep premise at every byte outside WJ. *)
Lemma jcut_mk : forall g pos mf nm tk dp pc
  (P : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3,
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W2 mem2 md2 (4 * Z.of_nat (m_nrec g) + 7) ->
  frames S2 = [(4, pos)] -> 0 <= 4 * Z.of_nat (m_nrec g) + 7 <= EV_LLVMF ->
  mo_le MT (e_S g) S2 ((4 * Z.of_nat (m_nrec g) + 7) * (mo_malloc MT 256 + mo_free MT)) ->
  mo_ok MT S2 ((EV_LLVMF - (4 * Z.of_nat (m_nrec g) + 7)) * (mo_malloc MT 256 + mo_free MT)) ->
  ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 -> jc g pos mf nm tk dp ly2 S2 W2 regs2 mem2 ->
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly3 S3 W3 mem3 md3 (4 * Z.of_nat (m_nrec g) + 7) ->
  frames S3 = [(4, pos)] -> Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) ->
  jkeep g pos mf W2 mem2 W3 mem3 ->
  (forall r : bv 5, In r [2; 8; 9; 3; 4; 19; 20; 21; 22]%bv -> getr regs3 r = getr regs2 r) ->
  (forall fd, fd_lookup (m_fds md3) fd = fd_lookup (m_fds md2) fd) -> m_fs md3 = m_fs md2 ->
  P ly3 S3 W3 regs3 mem3 md3 ->
  jcut g pos mf nm tk dp pc P W3 (cfg_at SEGS pc regs3 mem3 md3).
Proof.
intros g pos mf nm tk dp pc P ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3
  HJ2 Hfr2 HK MLE MOK HC HJC HJ3 Hfr3 Hperm KP.
exact (jcut_mk4 g pos mf nm tk dp pc P ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3
  HJ2 Hfr2 HK MLE MOK HC HJC HJ3 Hfr3 Hperm (jkeep4_of g pos mf ly2 S2 W2 mem2 W3 mem3 KP)).
Qed.

(* jlay, from the first state of the segment. *)
Lemma jlay_of : forall g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2,
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W2 mem2 md2 (4 * Z.of_nat (m_nrec g) + 7) ->
  frames S2 = [(4, pos)] -> ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 -> HBLOCKS g ly2 S2 (jhs g nm tk dp) ->
  jlay g pos mf nm tk dp.
Proof.
intros g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 HJ Hfrs HC (Hperm & _).
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _).
assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (F1 & F2 & F3).
destruct (frame_al64 SEGS B ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (F64 & _ & _).
change (fs_frame_bytes 4) with 1024 in *. rewrite EFa in *.
destruct HC as (_ & _ & _ & Hmfb & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & _ & _ & HPRE & _ & _ & _).
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
unfold e_pre, tLLVMFuzzerTestOneInput_pre in HPRE.
destruct HPRE as (_ & _ & _ & _ & Hinp & Hlen & _).
assert (HBL : forall p n, In (p, n) (ablocks B ly2 S2) ->
  4096 <= p /\ p + req_size n <= alloc_ceiling /\ in_app p (req_size n) /\
  (p + req_size n <= SFa g pos \/ SFa g pos + 1024 <= p)).
{ intros p n Hin. destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR2 Hin) as (_ & P4096 & Pceil & Papp & _).
  pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem2 md2 p n 4 pos HAR2 Hin Hin4) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 4) with 1024 in Hd. rewrite EFa in Hd.
  refine (conj P4096 (conj Pceil (conj Papp _))). lia. }
unfold jlay. split; [unfold e_sp0 in *; unfold ASTACK in *; lia|].
split; [unfold e_sp0 in *; lia|]. split; [unfold e_sp0 in *; exact Hsp0al|].
refine (conj F1 (conj F2 (conj F3 (conj F64 _)))).
split.
- intros p n Hin. apply HBL. apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. left. exact Hin.
- destruct Hinp as [[Hn0 _] | [Hn Hpin]].
  + left. destruct (e_pl g); [reflexivity | cbn in Hlen; lia].
  + right. destruct (HBL (e_p g) (e_n g)) as (P0 & P1 & P2 & P3).
    { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. exact Hpin. }
    assert (Rq : req_size (e_n g) = e_n g) by (unfold req_size; destruct (Z.eqb_spec (e_n g) 0); lia).
    rewrite Rq in *. rewrite <- Hlen. exact (conj P0 (conj P1 (conj P2 P3))).
Qed.

(* A cut with a weaker boundary fact: acut is monotone in its P, given ecommon. *)
Lemma jacut_mono : forall g pos mf k pc
  (P Q : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  (forall ly2 S2 W2 regs2 mem2 md2, ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 ->
     P ly2 S2 W2 regs2 mem2 md2 -> Q ly2 S2 W2 regs2 mem2 md2) ->
  forall W2 c2, ACUT g pos mf k pc P W2 c2 -> ACUT g pos mf k pc Q W2 c2.
Proof.
intros g pos mf k pc P Q HPQ W2 c2 (ly2 & S2 & regs2 & mem2 & md2 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & HP).
exists ly2, S2, regs2, mem2, md2.
refine (conj E1 (conj E2 (conj E3 (conj E4 (conj E5 (conj E6 (conj E7 _))))))).
exact (HPQ _ _ _ _ _ _ E7 HP).
Qed.

(* The end of a run of the segment that allocates nothing (jkeep4: the keep at the bytes the cuts read): the state the symbolic run stopped in (at slot pc) is
   a jcut, given what the run kept (KEEP: memory outside WJ; the registers ecommon and jc speak of) and the
   boundary's own facts P of the final registers and memory. *)
Lemma jcut_close4 : forall g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 E ss ms md extra pc
  (P : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W2 mem2 md2 (4 * Z.of_nat (m_nrec g) + 7) ->
  frames S2 = [(4, pos)] -> 0 <= 4 * Z.of_nat (m_nrec g) + 7 <= EV_LLVMF ->
  mo_le MT (e_S g) S2 ((4 * Z.of_nat (m_nrec g) + 7) * (mo_malloc MT 256 + mo_free MT)) ->
  mo_ok MT S2 ((EV_LLVMF - (4 * Z.of_nat (m_nrec g) + 7)) * (mo_malloc MT 256 + mo_free MT)) ->
  ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 -> jc g pos mf nm tk dp ly2 S2 W2 regs2 mem2 ->
  st_ok_pi SEGS VAL E ss (restrict (w_H W2) ms) -> ss_pc ss = pc -> ss_resv ss = None ->
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W2 (ms_mem ms) md (4 * Z.of_nat (m_nrec g) + 7) ->
  jkeep4 g pos mf ly2 S2 W2 mem2 W2 (ms_mem ms) ->
  env_agree 32 (Ereg regs2 extra) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0))
    [2; 8; 9; 3; 4; 19; 20; 21; 22]%bv = true ->
  P ly2 S2 W2 (ms_regs ms) (ms_mem ms) md ->
  SRr SEGS W2 (mkCfg ms md) (jcut g pos mf nm tk dp (BASE + pc) P).
Proof.
intros g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 E ss ms md extra pc P HJ2 Hfr2 HK MLE MOK HC HJC
  HS Hpc Hrv HJ3 KEEP HAE Hkept HP.
pose proof (st_ok_pi_restrict_mkst (w_H W2) E ss ms HS Hrv) as Hms. rewrite Hpc in Hms.
pose proof (regs_kept_of_st_ok_pi E ss (restrict (w_H W2) ms) regs2 extra _ HS HAE Hkept) as RK.
cbn [ms_regs restrict] in RK.
apply SRr_ret. rewrite Hms.
destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as [D1 D2].
destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as [D3 D4].
apply (jcut_mk4 g pos mf nm tk dp (BASE + pc) P ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) md
  HJ2 Hfr2 HK MLE MOK HC HJC HJ3 Hfr2 (Permutation_refl _) KEEP).
- intros r Hr. apply RK. exact Hr.
- intros fd. rewrite D3, D1. reflexivity.
- rewrite D4, D2. reflexivity.
- exact HP.
Qed.

(* The end of a run of the segment that allocates nothing: the state the symbolic run stopped in (at slot pc) is
   a jcut, given what the run kept (KEEP: memory outside WJ; the registers ecommon and jc speak of) and the
   boundary's own facts P of the final registers and memory. *)
Lemma jcut_close : forall g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 E ss ms md extra pc
  (P : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W2 mem2 md2 (4 * Z.of_nat (m_nrec g) + 7) ->
  frames S2 = [(4, pos)] -> 0 <= 4 * Z.of_nat (m_nrec g) + 7 <= EV_LLVMF ->
  mo_le MT (e_S g) S2 ((4 * Z.of_nat (m_nrec g) + 7) * (mo_malloc MT 256 + mo_free MT)) ->
  mo_ok MT S2 ((EV_LLVMF - (4 * Z.of_nat (m_nrec g) + 7)) * (mo_malloc MT 256 + mo_free MT)) ->
  ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 -> jc g pos mf nm tk dp ly2 S2 W2 regs2 mem2 ->
  st_ok_pi SEGS VAL E ss (restrict (w_H W2) ms) -> ss_pc ss = pc -> ss_resv ss = None ->
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W2 (ms_mem ms) md (4 * Z.of_nat (m_nrec g) + 7) ->
  jkeep g pos mf W2 mem2 W2 (ms_mem ms) ->
  env_agree 32 (Ereg regs2 extra) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0))
    [2; 8; 9; 3; 4; 19; 20; 21; 22]%bv = true ->
  P ly2 S2 W2 (ms_regs ms) (ms_mem ms) md ->
  SRr SEGS W2 (mkCfg ms md) (jcut g pos mf nm tk dp (BASE + pc) P).
Proof.
intros g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 E ss ms md extra pc P HJ2 Hfr2 HK MLE MOK HC HJC
  HS Hpc Hrv HJ3 KEEP.
exact (jcut_close4 g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 E ss ms md extra pc P HJ2 Hfr2 HK MLE MOK HC HJC
  HS Hpc Hrv HJ3 (jkeep4_of g pos mf ly2 S2 W2 mem2 W2 (ms_mem ms) KEEP)).
Qed.

(* ---- the cut points of segment J ---------------------------------------------------------------------------- *)
(* The stem at stemA: what the stem copy loop (j_stem_loop_stmt) asks of it, and that segment J writes none of its
   bytes. *)
Definition jstem_at (g : ectx) (pos mf : Z) (W2 : world SEGS) (mem2 : word -> option byte) (stemA : Z) : Prop :=
  (length (SlotModel.n_stem (e_pl g)) <= 16)%nat /\
  (forall j, (j < length (SlotModel.n_stem (e_pl g)))%nat -> bz (nthb (SlotModel.n_stem (e_pl g)) j) <> 0) /\
  bytes_at8 W2 mem2 stemA (SlotModel.n_stem (e_pl g) ++ [zb 0]) /\
  range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF stemA
    (Z.of_nat (length (SlotModel.n_stem (e_pl g))) + 1) /\
  (forall x, stemA + Z.of_nat (length (SlotModel.n_stem (e_pl g))) < x <
     stemA + Z.of_nat (length (SlotModel.n_stem (e_pl g))) -
       (stemA + Z.of_nat (length (SlotModel.n_stem (e_pl g)))) mod 8 + 8 ->
     aview SEGS (w_H W2) mem2 x <> None) /\
  in_app stemA (Z.of_nat (length (SlotModel.n_stem (e_pl g))) + 1) /\
  4096 <= stemA /\ stemA + Z.of_nat (length (SlotModel.n_stem (e_pl g))) + 1 <= alloc_ceiling /\
  (forall a, stemA <= a < stemA + Z.of_nat (length (SlotModel.n_stem (e_pl g))) + 1 -> ~ WJ g pos mf a).

(* 0x81a30 (BASE + 0x1324), after the wok test at 0x81a2c: s10 = exp_nm, s8 = exp_dp (0x819ec, 0x819f0), their
   shadow zero (0x819f4 .. 0x81a20); a2 = SF, a3 = the shadow base, a4 = said = id.model_name (0x81984 ..
   0x8198c); s7 = has_model_name, s9 = fam (seg_I). *)
Definition Pj1 (g : ectx) (pos : Z) (ly2 : alayout) (S2 : astate) (W2 : world SEGS) (regs2 : bvmap 5 word)
  (mem2 : word -> option byte) (md2 : Model) : Prop :=
  SlotModel.n_wok (e_pl g) = true /\
  getr regs2 27 = w64 (SlotModel.n_r (e_pl g)) /\
  getr regs2 26 = w64 (SFa g pos + V_nm) /\ getr regs2 24 = w64 (SFa g pos + V_dp) /\
  getr regs2 12 = w64 (SFa g pos) /\ getr regs2 13 = w64 SHADOW_OFF /\
  getr regs2 14 = w64 (SFa g pos + V_id + 3) /\
  getr regs2 23 = w64 (RcIdentModel.has_model_name (m_id g (m_nrec g))) /\
  getr regs2 25 = w64 (SlotModel.n_fam (e_pl g)) /\
  sh_zero W2 mem2 (SFa g pos + V_nm) N_nm /\ sh_zero W2 mem2 (SFa g pos + V_dp) N_dp.

(* 0x81ab4 (BASE + 0x13a8), after put_dec(w4, &n4, out, 2) returns: s2 = w4, s7 = the stem, w4 = DEC(in,2)
   DEC(out,2), n4 = 4 (mf+208), ld = 0 (mf+200), the shadow of exp_nm, exp_dp and w4 zero. *)
Definition Pj2 (g : ectx) (pos mf : Z) (ly2 : alayout) (S2 : astate) (W2 : world SEGS) (regs2 : bvmap 5 word)
  (mem2 : word -> option byte) (md2 : Model) : Prop :=
  SlotModel.n_wok (e_pl g) = true /\
  getr regs2 27 = w64 (SlotModel.n_r (e_pl g)) /\
  getr regs2 26 = w64 (SFa g pos + V_nm) /\ getr regs2 24 = w64 (SFa g pos + V_dp) /\
  getr regs2 18 = w64 (SFa g pos + V_w4) /\
  (exists stemA, getr regs2 23 = w64 stemA /\ jstem_at g pos mf W2 mem2 stemA) /\
  bytes_at8 W2 mem2 (SFa g pos + V_w4) (SlotModel.n_W4 (e_pl g)) /\
  val_mem SEGS (rd W2 mem2) (mf + M_n1) 8 4 /\ val_mem SEGS (rd W2 mem2) (mf + M_n2) 8 0 /\
  sh_zero W2 mem2 (SFa g pos + V_nm) N_nm /\ sh_zero W2 mem2 (SFa g pos + V_dp) N_dp /\
  sh_zero W2 mem2 (SFa g pos + V_w4) N_w4.

(* 0x81c34 (BASE + 0x1528), after exp_nm[ln] = 0 (0x81c30): s9 = ln, a7 = the shadow base, exp_nm built, ld = 0. *)
Definition Pj3 (g : ectx) (pos mf : Z) (ly2 : alayout) (S2 : astate) (W2 : world SEGS) (regs2 : bvmap 5 word)
  (mem2 : word -> option byte) (md2 : Model) : Prop :=
  SlotModel.n_wok (e_pl g) = true /\
  getr regs2 27 = w64 (SlotModel.n_r (e_pl g)) /\
  getr regs2 26 = w64 (SFa g pos + V_nm) /\ getr regs2 24 = w64 (SFa g pos + V_dp) /\
  getr regs2 25 = w64 (SlotModel.n_ln (e_pl g)) /\ getr regs2 17 = w64 SHADOW_OFF /\
  (length (SlotModel.n_EXP_NM (e_pl g)) <= 21)%nat /\
  bytes_at8 W2 mem2 (SFa g pos + V_nm) (SlotModel.n_EXP_NM (e_pl g) ++ [zb 0]) /\
  val_mem SEGS (rd W2 mem2) (mf + M_n2) 8 0 /\
  sh_zero W2 mem2 (SFa g pos + V_nm) N_nm /\ sh_zero W2 mem2 (SFa g pos + V_dp) N_dp.

(* 0x81e18 (BASE + 0x170c), after exp_dp[ld] = 0 (0x81e14): s9 = ln, s2 = ld, exp_nm and exp_dp built. *)
Definition Pj4 (g : ectx) (pos mf : Z) (ly2 : alayout) (S2 : astate) (W2 : world SEGS) (regs2 : bvmap 5 word)
  (mem2 : word -> option byte) (md2 : Model) : Prop :=
  SlotModel.n_wok (e_pl g) = true /\
  getr regs2 27 = w64 (SlotModel.n_r (e_pl g)) /\
  getr regs2 26 = w64 (SFa g pos + V_nm) /\ getr regs2 24 = w64 (SFa g pos + V_dp) /\
  getr regs2 25 = w64 (SlotModel.n_ln (e_pl g)) /\ getr regs2 18 = w64 (SlotModel.n_ld (e_pl g)) /\
  (length (SlotModel.n_EXP_NM (e_pl g)) <= 21)%nat /\
  bytes_at8 W2 mem2 (SFa g pos + V_nm) (SlotModel.n_EXP_NM (e_pl g) ++ [zb 0]) /\
  bytes_at8 W2 mem2 (SFa g pos + V_dp) (SlotModel.n_EXP_DP (e_pl g) ++ [zb 0]) /\
  sh_zero W2 mem2 (SFa g pos + V_nm) N_nm /\ sh_zero W2 mem2 (SFa g pos + V_dp) N_dp.

#[local] Notation INV_J := (inv_J_end B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).

(* ---- the pieces ---------------------------------------------------------------------------------------------- *)
Definition j_C_stmt : Prop :=
  forall g pos mf nm tk dp W2 c2, jcut g pos mf nm tk dp (BASE + 0x1324) (Pj1 g pos) W2 c2 ->
  SRr SEGS W2 c2 (jcut g pos mf nm tk dp (BASE + 0x13a8) (Pj2 g pos mf)).
Definition j_D_stmt : Prop :=
  forall g pos mf nm tk dp W2 c2, jcut g pos mf nm tk dp (BASE + 0x13a8) (Pj2 g pos mf) W2 c2 ->
  SRr SEGS W2 c2 (jcut g pos mf nm tk dp (BASE + 0x1528) (Pj3 g pos mf)).
Definition j_E_stmt : Prop :=
  forall g pos mf nm tk dp W2 c2, jcut g pos mf nm tk dp (BASE + 0x1528) (Pj3 g pos mf) W2 c2 ->
  SRr SEGS W2 c2 (jcut g pos mf nm tk dp (BASE + 0x170c) (Pj4 g pos mf)).
Definition j_F_stmt : Prop :=
  forall g pos mf nm tk dp W2 c2, jcut g pos mf nm tk dp (BASE + 0x170c) (Pj4 g pos mf) W2 c2 ->
  SRr SEGS W2 c2 (INV_J g pos mf nm tk dp).

End c.
End b.
End a.
