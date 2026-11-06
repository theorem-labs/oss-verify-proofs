(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7 Q5Rg Qfw3_c1 QWxq_c1 Qc3B QlEo_c1 Lib.GwApply QsjA QZAi Ql2m QqdR QYTG Lib.SepCache QnDM_c1 QVbl QQLG Q91D QQRC G.T_shp G.T_pe Qbz7 QFau Q8l1 Lib.CodeAt Lib.StepGen Lib.StepGenX Lib.StepGenX2 Lib.GwCallee Lib.GwFold.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg Qfw3_c1.Mq2 QWxq_c1.Mq0 Qc3B QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0.

Import QZAi.Mq1 Ql2m.Mq3 QZAi QqdR QYTG.Mq2.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QnDM_c1.
Import QVbl.Mq4.
Import QVbl.Mq3.
Import QQLG.Mq8.
Import Q91D.Mq6.
Import QQLG.Mq7.
Import Q91D.Mq2.
Import QQRC.Mq0.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_shp.F_fmt_fp.
Import Q91D.Mq3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.
Import Qbz7.
Import QFau.
Import Q8l1.Mq1.

Import ListNotations.
Import QlEo_c1.Mq0.Exc. Unset Keyed Unification. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Local Notation PA_g := G.T_printf.PA_g.
Local Notation d_fl := G.T_printf.d_fl.
Local Notation d_w := G.T_printf.d_w.
Local Notation d_p := G.T_printf.d_p.
Local Notation d_xp := G.T_printf.d_xp.
Local Notation d_t := G.T_printf.d_t.

Ltac showall := let x10 := getreg 10%Z in let x11 := getreg 11%Z in let x12 := getreg 12%Z in let x13 := getreg 13%Z in let x14 := getreg 14%Z in let x15 := getreg 15%Z in let x16 := getreg 16%Z in let x17 := getreg 17%Z in let x5 := getreg 5%Z in let x6 := getreg 6%Z in let x7 := getreg 7%Z in let x8 := getreg 8%Z in let x9 := getreg 9%Z in let x18 := getreg 18%Z in let x19 := getreg 19%Z in let x20 := getreg 20%Z in let x21 := getreg 21%Z in let x22 := getreg 22%Z in let x23 := getreg 23%Z in let x24 := getreg 24%Z in let x25 := getreg 25%Z in let x26 := getreg 26%Z in let x27 := getreg 27%Z in let x28 := getreg 28%Z in let x29 := getreg 29%Z in let x30 := getreg 30%Z in let x31 := getreg 31%Z in let x2 := getreg 2%Z in let x1 := getreg 1%Z in
idtac "a0=" x10; idtac "a1=" x11; idtac "a2=" x12; idtac "a3=" x13; idtac "a4=" x14; idtac "a5=" x15; idtac "a6=" x16; idtac "a7=" x17; idtac "t0=" x5; idtac "t1=" x6; idtac "t2=" x7; idtac "s0=" x8; idtac "s1=" x9; idtac "s2=" x18; idtac "s3=" x19; idtac "s4=" x20; idtac "s5=" x21; idtac "s6=" x22; idtac "s7=" x23; idtac "s8=" x24; idtac "s9=" x25; idtac "s10=" x26; idtac "s11=" x27; idtac "t3=" x28; idtac "t4=" x29; idtac "t5=" x30; idtac "t6=" x31; idtac "sp=" x2; idtac "ra=" x1.
Ltac show_hyp H := let T := type of H in idtac H ":" T.
Ltac show_goal := match goal with |- ?G => idtac "GOAL:" G end.
Ltac dlia := first [lia | match goal with |- ?g => idtac "LIA FAILED:"; idtac g; fail 1 end].
Ltac zl := unfold zlength in *; cbn [length] in *; lia.

Ltac hyp_cells :=
lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ m A ?cs' |- _ =>
replace cs with cs' by (repeat (reflexivity || lazymatch goal with |- @eq Z _ _ => fail | _ => f_equal end); lia); exact H end
end.
Ltac fix_stk := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with H : stk _ m _ _ |- _ => let n := fresh "ST" in rename H into n end end.

Ltac fixK K := try (rewrite ?swrap32_small in K by lia); try (rewrite ?signed_of_Z in K by lia); try (rewrite ?Z.add_0_r in K).
Ltac brf K := if_cases K; zify_cond K; fixK K.
Ltac br K := brf K; try (exfalso; lia).

Ltac fixr := try (rewrite !swrap32_small by lia); try (rewrite !Z.add_0_r).

Ltac if_lit :=
lazymatch goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
let v := eval vm_compute in c in change c with v; cbv iota
end. Ltac mkr__if_lit_3 := lazymatch goal with
| |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
let v := eval vm_compute in c in change c with v; cbv iota
end.

Definition hide (P : Prop) := P.
Ltac stash H := lazymatch type of H with hide _ => idtac | ?T => change T with (hide T) in H end.
Ltac stash_mods := repeat match goal with H : context [Z.modulo _ _] |- _ =>
lazymatch type of H with hide _ => fail | ?T => change T with (hide T) in H end end.
Ltac unstash := unfold hide in *.

Ltac ienter := lazymatch goal with |- Ql2m.Mq3.implM _ _ _ _ _ => unfold Ql2m.Mq3.implM; apply impl_from_evt | |- QlEo_c1.Mq0.impl _ _ _ _ _ => apply impl_from_evt | _ => idtac end.

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
Lemma Forall_znth : forall (P : Z -> Prop) l i, Forall P l -> (0 <= i < zlength l)%Z -> P (znth l i).
Proof.
intros P l i HF Hi. apply (proj1 (Forall_forall P l) HF). unfold znth. destruct (Z.ltb_spec0 i 0); [lia|].
apply nth_In. unfold zlength in Hi. lia.
Qed.

Lemma land_lxor_distr : forall a b m, Z.land (Z.lxor a b) m = Z.lxor (Z.land a m) (Z.land b m).
Proof. intros. apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec, !Z.lxor_spec, !Z.land_spec. destruct (Z.testbit a n), (Z.testbit b n), (Z.testbit m n); reflexivity. Qed.

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

Lemma parse_dir_conv_type : forall s d rest, parse_dir s = Some (d, rest) -> dir_ty_ok d.
Proof. exact parse_dir_ty_ok. Qed.

Lemma parse_dir_xp : forall s d rest, parse_dir s = Some (d, rest) ->
((d_xp d = false /\ d_p d = -1) \/ (d_xp d = true /\ 0 <= d_p d <= INT_MAX))%Z.
Proof.
intros s d rest PD. destruct (parse_dir_shape _ _ _ PD) as (_ & SH). destruct (parse_flags s 0) as [fl0 s1'].
destruct SH as (_ & c1 & s1b & _ & _ & s2 & _ & c2 & s2b & _ & PX).
destruct PX as [(_ & Hp & Hx & _) | (_ & Hx & c3 & s3b & _ & _ & s3 & G & _)].
- left. split; [exact Hx | exact Hp].
- right. split; [exact Hx|]. eapply getint_some_range; [|exact G]. unfold INT_MAX. lia.
Qed.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 : Z).
Variables (G_102fd G_107e0 G_11778 G_118c0 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard : Z).
Variables (e_fwritex e_2596c e_memchr : Z).
Variables (jt_11778_o1504 jt_11778_o1432 jt_11778_o1800 jt_11778_o1744 jt_11778_o1864 jt_11778_o1352 : Z).
Hypothesis CODE : code_at segs base (printf_core_code w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 3632.
Hypothesis RNG_GLOBALS_TOP : gw_br GLOBALS_TOP 8.
Hypothesis LAY_lo_GLOBALS_TOP : gw_le 65536 GLOBALS_TOP.
Hypothesis LAY_ssp_guard_GLOBALS_TOP : gw_le (ssp_guard + 8) GLOBALS_TOP.
Hypothesis RNG_G_118c0 : gw_br G_118c0 116.
Hypothesis ROM_G_118c0 : ro_bytes segs G_118c0 [Z_to_bv 8 25; Z_to_bv 8 0; Z_to_bv 8 11; Z_to_bv 8 0; Z_to_bv 8 25; Z_to_bv 8 25; Z_to_bv 8 25; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 5; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 11; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 25; Z_to_bv 8 0; Z_to_bv 8 10; Z_to_bv 8 10; Z_to_bv 8 25; Z_to_bv 8 25; Z_to_bv 8 25; Z_to_bv 8 3; Z_to_bv 8 10; Z_to_bv 8 7; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 27; Z_to_bv 8 9; Z_to_bv 8 11; Z_to_bv 8 24; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 6; Z_to_bv 8 11; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 11; Z_to_bv 8 0; Z_to_bv 8 6; Z_to_bv 8 25; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 25; Z_to_bv 8 25; Z_to_bv 8 25; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 14; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 25; Z_to_bv 8 0; Z_to_bv 8 11; Z_to_bv 8 13; Z_to_bv 8 25; Z_to_bv 8 25; Z_to_bv 8 25; Z_to_bv 8 0; Z_to_bv 8 13; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 2; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 14; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 0; Z_to_bv 8 14; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 14; Z_to_bv 8 0; Z_to_bv 8 0].
Hypothesis RNG_G_102fd : gw_br G_102fd 12.
Hypothesis ROM_G_102fd : ro_bytes segs G_102fd [Z_to_bv 8 45; Z_to_bv 8 43; Z_to_bv 8 32; Z_to_bv 8 32; Z_to_bv 8 32; Z_to_bv 8 48; Z_to_bv 8 88; Z_to_bv 8 48; Z_to_bv 8 120; Z_to_bv 8 0; Z_to_bv 8 125; Z_to_bv 8 0].
Hypothesis RNG_G_107e0 : gw_br G_107e0 16.
Hypothesis ROM_G_107e0 : ro_bytes segs G_107e0 [Z_to_bv 8 48; Z_to_bv 8 49; Z_to_bv 8 50; Z_to_bv 8 51; Z_to_bv 8 52; Z_to_bv 8 53; Z_to_bv 8 54; Z_to_bv 8 55; Z_to_bv 8 56; Z_to_bv 8 57; Z_to_bv 8 65; Z_to_bv 8 66; Z_to_bv 8 67; Z_to_bv 8 68; Z_to_bv 8 69; Z_to_bv 8 70].
Hypothesis RNG_G_11778 : gw_br G_11778 224.
Hypothesis ROM_jt_11778_50 : ro_bytes segs (G_11778 + 200) (le4 (Z_to_bv 64 jt_11778_o1504)).
Hypothesis ROM_jt_11778_35 : ro_bytes segs (G_11778 + 140) (le4 (Z_to_bv 64 jt_11778_o1432)).
Hypothesis ROM_jt_11778_40 : ro_bytes segs (G_11778 + 160) (le4 (Z_to_bv 64 jt_11778_o1432)).
Hypothesis ROM_jt_11778_34 : ro_bytes segs (G_11778 + 136) (le4 (Z_to_bv 64 jt_11778_o1800)).
Hypothesis ROM_jt_11778_52 : ro_bytes segs (G_11778 + 208) (le4 (Z_to_bv 64 jt_11778_o1744)).
Hypothesis ROM_jt_11778_55 : ro_bytes segs (G_11778 + 220) (le4 (Z_to_bv 64 jt_11778_o1864)).
Hypothesis ROM_jt_11778_23 : ro_bytes segs (G_11778 + 92) (le4 (Z_to_bv 64 jt_11778_o1864)).
Hypothesis ROM_jt_11778_36 : ro_bytes segs (G_11778 + 144) (le4 (Z_to_bv 64 jt_11778_o1352)).
Hypothesis ROM_jt_11778_37 : ro_bytes segs (G_11778 + 148) (le4 (Z_to_bv 64 jt_11778_o1352)).
Hypothesis ROM_jt_11778_38 : ro_bytes segs (G_11778 + 152) (le4 (Z_to_bv 64 jt_11778_o1352)).
Hypothesis ROM_jt_11778_4 : ro_bytes segs (G_11778 + 16) (le4 (Z_to_bv 64 jt_11778_o1352)).
Hypothesis ROM_jt_11778_5 : ro_bytes segs (G_11778 + 20) (le4 (Z_to_bv 64 jt_11778_o1352)).
Hypothesis ROM_jt_11778_6 : ro_bytes segs (G_11778 + 24) (le4 (Z_to_bv 64 jt_11778_o1352)).

Local Definition gw_tbl_0 := tt.

Definition strnlen_post : ltac:(gw_rebind_ty (@Q91D.Mq6.strnlen_post segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@Q91D.Mq6.strnlen_post segs) constr:(gw_tbl_0)).
Local Definition gw_tbl_1 := (gw_ent (@Q91D.Mq6.strnlen_post segs) strnlen_post gw_tbl_0).
Definition va_area : ltac:(gw_rebind_ty (@Q91D.Mq3.va_area segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q91D.Mq3.va_area segs) constr:(gw_tbl_1)).
Local Definition gw_tbl_2 := (gw_ent (@Q8l1.Mq1.va_area segs) va_area (gw_ent (@Q91D.Mq3.va_area segs) va_area gw_tbl_1)).
Definition pop_arg_post : ltac:(gw_rebind_ty (@Q91D.Mq3.pop_arg_post segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q91D.Mq3.pop_arg_post segs) constr:(gw_tbl_2)).
Local Definition gw_tbl_3 := (gw_ent (@Q91D.Mq3.pop_arg_post segs) pop_arg_post gw_tbl_2).
Definition wfile : ltac:(gw_rebind_ty (@QQLG.Mq7.wfile segs) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@QQLG.Mq7.wfile segs) constr:(gw_tbl_3)).
Local Definition gw_tbl_4 := (gw_ent (@Q8l1.Mq1.wfile segs) wfile (gw_ent (@Q91D.Mq2.wfile segs) wfile (gw_ent (@QQLG.Mq7.wfile segs) wfile gw_tbl_3))).
Definition ssp_cells : ltac:(gw_rebind_ty (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_4)).
Local Definition gw_tbl_5 := (gw_ent (@Q8l1.Mq1.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) ssp_cells gw_tbl_4)).
Definition sink_frame_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.sink_frame_stmt segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.sink_frame_stmt segs) constr:(gw_tbl_5)).
Local Definition gw_tbl_6 := (gw_ent (@Q8l1.Mq1.sink_frame_stmt segs) sink_frame_stmt gw_tbl_5).
#[global] Arguments sink_frame_stmt {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope.
Definition sink_flags_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.sink_flags_stmt segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.sink_flags_stmt segs) constr:(gw_tbl_6)).
Local Definition gw_tbl_7 := (gw_ent (@Q8l1.Mq1.sink_flags_stmt segs) sink_flags_stmt gw_tbl_6).
#[global] Arguments sink_flags_stmt {St}%_type_scope Fp%_Z_scope SINK%_function_scope.
Definition out_post : ltac:(gw_rebind_ty (@Q8l1.Mq1.out_post segs got_ssp ssp_guard) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.out_post segs got_ssp ssp_guard) constr:(gw_tbl_7)).
Local Definition gw_tbl_8 := (gw_ent (@Q8l1.Mq1.out_post segs got_ssp ssp_guard) out_post gw_tbl_7).
#[global] Arguments out_post {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope ra%_bv_scope sp%_bv_scope gp%_bv_scope tp%_bv_scope s0%_bv_scope s1%_bv_scope s2%_bv_scope s3%_bv_scope s4%_bv_scope s5%_bv_scope s6%_bv_scope s7%_bv_scope s8%_bv_scope s9%_bv_scope s10%_bv_scope s11%_bv_scope F fc%_bv_scope S%_Z_scope bs%_list_scope lo%_Z_scope canary%_bv_scope m%_function_scope _ _ _.
Definition out_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) constr:(gw_tbl_8)).
Local Definition gw_tbl_9 := (gw_ent (@Q8l1.Mq1.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt gw_tbl_8).
#[global] Arguments out_stmt {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope.
Definition fpcall_post : ltac:(gw_rebind_ty (@Q8l1.Mq1.fpcall_post segs got_ssp ssp_guard) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.fpcall_post segs got_ssp ssp_guard) constr:(gw_tbl_9)).
Local Definition gw_tbl_10 := (gw_ent (@Q8l1.Mq1.fpcall_post segs got_ssp ssp_guard) fpcall_post gw_tbl_9).
#[global] Arguments fpcall_post {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope ra%_bv_scope sp%_bv_scope gp%_bv_scope tp%_bv_scope s0%_bv_scope s1%_bv_scope s2%_bv_scope s3%_bv_scope s4%_bv_scope s5%_bv_scope s6%_bv_scope s7%_bv_scope s8%_bv_scope s9%_bv_scope s10%_bv_scope s11%_bv_scope F lo%_Z_scope canary%_bv_scope m%_function_scope _%_Z_scope _ _.
Definition fpcall_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_10)).
Local Definition gw_tbl_11 := (gw_ent (@Q8l1.Mq1.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt gw_tbl_10).
#[global] Arguments fpcall_stmt {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUTFP%_function_scope c.
Definition arg_ok : ltac:(gw_rebind_ty (@Q8l1.Mq1.arg_ok segs) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.arg_ok segs) constr:(gw_tbl_11)).
Local Definition gw_tbl_12 := (gw_ent (@Q8l1.Mq1.arg_ok segs) arg_ok gw_tbl_11).
Definition args_ok : ltac:(gw_rebind_ty (@Q8l1.Mq1.args_ok segs) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.args_ok segs) constr:(gw_tbl_12)).
Local Definition gw_tbl_13 := (gw_ent (@Q8l1.Mq1.args_ok segs) args_ok gw_tbl_12).

Hypothesis strnlen_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Q91D.Mq6.gw_all) (@Q91D.Mq6.strnlen_spec) e_2596c)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_13))) in exact T).

Hypothesis va_area_bound : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Q91D.Mq3.gw_all) (@Q91D.Mq3.va_area_bound) (base + 3632)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_13))) in let T := gw_fold_pcs T base (3632)%Z [0]%Z in exact T).
Hypothesis pop_arg_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Q91D.Mq3.gw_all) (@Q91D.Mq3.pop_arg_spec) (base + 3632)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_13))) in let T := gw_fold_pcs T base (3632)%Z [0]%Z in exact T).

Notation parg := G.T_printf.parg.
Notation PA_g := G.T_printf.PA_g.
Notation dir := G.T_printf.dir.
Notation d_fl := G.T_printf.d_fl.
Notation d_w := G.T_printf.d_w.
Notation d_p := G.T_printf.d_p.
Notation d_xp := G.T_printf.d_xp.
Notation d_t := G.T_printf.d_t.
Notation d_ty := G.T_printf.d_ty.

#[using="G_102fd G_107e0 G_11778 G_118c0 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard e_fwritex e_2596c e_memchr CODE BASE4 BASER RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_ssp_guard_GLOBALS_TOP RNG_G_118c0 ROM_G_118c0 RNG_G_102fd ROM_G_102fd RNG_G_107e0 ROM_G_107e0 RNG_G_11778 ROM_jt_11778_50 ROM_jt_11778_35 ROM_jt_11778_40 ROM_jt_11778_34 ROM_jt_11778_52 ROM_jt_11778_55 ROM_jt_11778_23 ROM_jt_11778_36 ROM_jt_11778_37 ROM_jt_11778_38 ROM_jt_11778_4 ROM_jt_11778_5 ROM_jt_11778_6 strnlen_spec va_area_bound pop_arg_spec"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := clear - hs segs base w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 G_102fd G_107e0 G_11778 G_118c0 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard e_fwritex e_2596c e_memchr CODE BASE4 BASER RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_ssp_guard_GLOBALS_TOP RNG_G_118c0 ROM_G_118c0 RNG_G_102fd ROM_G_102fd RNG_G_107e0 ROM_G_107e0 RNG_G_11778 ROM_jt_11778_50 ROM_jt_11778_35 ROM_jt_11778_40 ROM_jt_11778_34 ROM_jt_11778_52 ROM_jt_11778_55 ROM_jt_11778_23 ROM_jt_11778_36 ROM_jt_11778_37 ROM_jt_11778_38 ROM_jt_11778_4 ROM_jt_11778_5 ROM_jt_11778_6 strnlen_spec va_area_bound pop_arg_spec.

#[using="RNG_G_11778"] Lemma gw_jt_rd_G_11778 : forall m k jt, mem_inv segs m -> (0 <= k /\ k + 4 <= 224)%Z -> ro_bytes segs (G_11778 + k) (le4 (Z_to_bv 64 jt)) ->
ov_read_bytes segs m (Z_to_bv 64 (k + G_11778)) 4 = Some (le4 (Z_to_bv 64 jt)).
Proof. clear - RNG_G_11778 segs G_11778. intros m k jt MI Hk ROM. pose proof RNG_G_11778 as R; unfold gw_br in R.
assert (RN : gw_br (G_11778 + k) 4) by (unfold gw_br; lia).
pose proof (ro_bytes_read segs m (G_11778 + k) 4 _ 0 4 MI ROM RN eq_refl) as RD.
rewrite Z.add_0_r in RD. replace (k + G_11778)%Z with (G_11778 + k)%Z by lia. exact RD. Qed.
#[using="RNG_G_11778"] Lemma gw_jt_rdw_G_11778 : forall m k jt, mem_inv segs m -> (0 <= k /\ k + 4 <= 224)%Z -> ro_bytes segs (G_11778 + k) (le4 (Z_to_bv 64 jt)) ->
ov_read_bytes segs m (Z_to_bv 64 (G_11778 + k)) 4 = Some (le4 (Z_to_bv 64 jt)).
Proof. clear - RNG_G_11778 segs G_11778. intros m k jt MI Hk ROM. pose proof (gw_jt_rd_G_11778 m k jt MI Hk ROM) as RD. replace (G_11778 + k)%Z with (k + G_11778)%Z by lia. exact RD. Qed.

Tactic Notation "callw" tactic3(tac) :=
lazymatch goal with
| |- evt ?segs_ _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ tac | post_call segs_ m ]
end.
Tactic Notation "callx" tactic3(tac) := callw tac; try fix_stk.
#[using="Type"] Lemma zbytes_read : forall m A l i a,
bytes_at segs m A (zb l) -> (0 <= i < zlength l)%Z -> a = wa (A + i) ->
ov_read_bytes segs m a 1 = Some [Z_to_bv 8 (znth l i)].
Proof. clear - segs.
intros m A l i a HB Hi ->.
eapply (u8ro_read segs m A (zb l) i); [exact HB | | lia | reflexivity].
apply nth_error_zb. apply znth_nth_error. exact Hi.
Qed.

Section Sfx.
Variable fmt : list Z.
Definition sfx (k : Z) : list Z := skipn (Z.to_nat k) fmt.
#[using="Type"] Lemma sfx_cons : forall k, (0 <= k < zlength fmt)%Z -> sfx k = znth fmt k :: sfx (k + 1).
Proof. clear - fmt.
intros k Hk. unfold sfx. rewrite Z2Nat.inj_add, Nat.add_1_r by lia.
pose proof (znth_nth_error fmt k Hk) as E.
destruct (nth_error_split fmt (Z.to_nat k) _ E) as (pre & post & Efmt & Hlen).
rewrite Efmt at 1 2. rewrite skipn_app, skipn_all2, Hlen, Nat.sub_diag by lia. cbn [skipn app].
rewrite <- Efmt. f_equal. rewrite Efmt at 1. change (pre ++ znth fmt k :: post) with (pre ++ ([znth fmt k] ++ post)).
rewrite app_assoc, skipn_app, skipn_all2 by (rewrite length_app; cbn; lia). rewrite length_app. cbn [length].
replace (S (Z.to_nat k) - (length pre + 1))%nat with 0%nat by lia. reflexivity.
Qed.
#[using="Type"] Lemma sfx_nil : forall k, (zlength fmt <= k)%Z -> sfx k = [].
Proof. clear - fmt. intros k Hk. unfold sfx. apply skipn_all2. unfold zlength in Hk. lia. Qed.
#[using="Type"] Lemma sfx_skipn : forall n k, (0 <= k)%Z -> skipn n (sfx k) = sfx (k + Z.of_nat n).
Proof. clear - fmt. intros n k Hk. unfold sfx. rewrite skipn_skipn. f_equal. lia. Qed.
#[using="Type"] Lemma sfx_length : forall k, (0 <= k <= zlength fmt)%Z -> zlength (sfx k) = (zlength fmt - k)%Z.
Proof. clear - fmt. intros k Hk. unfold sfx, zlength in *. rewrite length_skipn. lia. Qed.
#[using="Type"] Lemma sfx_cons_inv : forall k c s, (0 <= k)%Z -> sfx k = c :: s -> (k < zlength fmt)%Z /\ c = znth fmt k /\ s = sfx (k + 1).
Proof. clear - fmt.
intros k c s Hk E. destruct (Z.lt_ge_cases k (zlength fmt)) as [Hlt|Hge].
- rewrite sfx_cons in E by lia. injection E as <- <-. split; [exact Hlt| split; reflexivity].
- rewrite sfx_nil in E by lia. discriminate.
Qed.

#[using="Type"] Lemma lit_run_firstn : forall s, lit_run s = firstn (length (lit_run s)) s.
Proof. clear - fmt. induction s as [|c s IH]; cbn; [reflexivity|]. destruct ((c =? 0) || (c =? 37))%Z; cbn; [reflexivity|]. f_equal. exact IH. Qed.
#[using="Type"] Lemma lit_run_length : forall s, (length (lit_run s) <= length s)%nat.
Proof. clear - fmt. induction s as [|c s IH]; cbn; [lia|]. destruct ((c =? 0) || (c =? 37))%Z; cbn; lia. Qed.
#[using="Type"] Lemma lit_run_in : forall s j c, nth_error (lit_run s) j = Some c -> c <> 0%Z /\ c <> 37%Z.
Proof. clear - fmt.
induction s as [|c s IH]; intros j c' H; cbn in H. { destruct j; discriminate. }
destruct (Z.eqb_spec c 0); [destruct j; discriminate|]. destruct (Z.eqb_spec c 37); [destruct j; discriminate|]. cbn in H.
destruct j as [|j]; cbn in H. { injection H as <-. lia. } eapply IH. exact H.
Qed.
#[using="Type"] Lemma lit_run_stop : forall s c s', skipn (length (lit_run s)) s = c :: s' -> c = 0%Z \/ c = 37%Z.
Proof. clear - fmt.
induction s as [|c s IH]; intros c' s' H; cbn in H; [discriminate|].
destruct (Z.eqb_spec c 0); [cbn in H; injection H as <- _; lia|]. destruct (Z.eqb_spec c 37); [cbn in H; injection H as <- _; lia|].
cbn in H. eapply IH. exact H.
Qed.

#[using="Type"] Lemma lit_run_sfx : forall i, (0 <= i)%Z -> let n := zlength (lit_run (sfx i)) in
(i + n <= Z.max i (zlength fmt))%Z /\ skipn (length (lit_run (sfx i))) (sfx i) = sfx (i + n)
/\ (forall j, 0 <= j < n -> znth fmt (i + j) <> 0 /\ znth fmt (i + j) <> 37)%Z
/\ lit_run (sfx i) = firstn (Z.to_nat n) (sfx i).
Proof. clear - fmt.
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

#[using="Type"] Lemma rw_CB_length : forall m A n (bs : list byte), rw_cells segs m A [CB n bs] -> length bs = n.
Proof. clear - segs. intros m A n bs [[[H _] _] _]. exact H. Qed.

Section Ranges128.
Local Open Scope Z_scope.
#[using="Type"] Lemma mk128_range : forall hi lo, 0 <= hi < 2^64 -> 0 <= lo < 2^64 -> 0 <= mk128 hi lo < 2^128.
Proof.
intros hi lo Hh Hl. unfold mk128. apply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.lor_lt_pow2; [|lia].
rewrite Z.shiftl_mul_pow2 by lia. change (2^128) with (2^64 * 2^64). nia.
Qed.
#[using="Type"] Lemma shr64_range64 : forall a k, 0 <= a < 2^64 -> 0 <= k -> 0 <= Z.shiftr a k < 2^64.
Proof. intros. apply QsjA.Z_shiftr_range; lia. Qed.
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
{ intros e s He Hs. apply QsjA.Z_lor_range; [apply QsjA.Z_lor_range|]; lia. }
cbv zeta.
destruct (negb (aExp =? 0)).
- destruct (negb (aExp =? 2047)); apply mk128_range; try apply wrap64_range;
apply G; try apply wrap64_range; try (apply shr64_range64; lia). exact RINF.
- destruct (aSig =? 0).
+ apply mk128_range; [|lia]. apply G; [apply wrap64_range | lia].
+ apply mk128_range.
* apply G; [apply wrap64_range|]. apply QsjA.Z_lxor_range; [|exact RIMP].
destruct (negb (is_neg64 _)); [apply wrap64_range|]. apply shr64_range64; [|apply Z.land_nonneg; lia].
apply shr64_range64; lia.
* apply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.land_lt_pow2; [apply sra63_range|].
pose proof (wrap64_range (Z.shiftl aSig (Z.land (add64 (clz64_mirror aSig) 49) 63))). unfold shl64. lia.
Qed.
End Ranges128.
#[using="Type"] Lemma cb8_c8_in : forall m A pre post bs, rw_cells segs m A (pre ++ CB 8 bs :: post) -> rw_cells segs m A (pre ++ C8 (le_bytes_to_word bs) :: post).
Proof. clear - segs.
intros m A pre post bs [[Hwf Hb] Hw].
apply cells_wf_app in Hwf. destruct Hwf as [H1 [H2 H3]]. cbn in H2.
split; [split|].
- apply cells_wf_app. split; [exact H1|]. split; [exact I | exact H3].
- rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in Hb |- *. rewrite le8_of_bytes by exact H2. exact Hb.
- rewrite !cells_size_app in *. cbn [cells_size csize] in Hw |- *. exact Hw.
Qed.
#[using="Type"] Lemma bytes_at_sub : forall m A (l : list byte) k n,
bytes_at segs m A l -> (k <= length l)%nat ->
bytes_at segs m (A + Z.of_nat k) (firstn n (skipn k l)).
Proof. clear - segs.
intros m A l k n H Hk.
rewrite <- (firstn_skipn k l) in H. apply bytes_at_app in H. destruct H as [_ H]. rewrite length_firstn, Nat.min_l in H by lia.
rewrite <- (firstn_skipn n (skipn k l)) in H. apply bytes_at_app in H. destruct H as [H _]. exact H.
Qed.

#[using="Type"] Lemma c8_read4 : forall m A pre (w : word) post a,
rw_cells segs m A (pre ++ C8 w :: post) -> a = wa (A + Z.of_nat (cells_size pre)) ->
ov_read_bytes segs m a 4 = Some (le4 w).
Proof. clear - segs.
intros m A pre w post a H ->.
apply (proj1 (rw_cells_app segs m A pre (C8 w :: post))) in H. destruct H as [_ H].
pose proof (rw_cells_bytes_at' _ _ _ _ H) as Hb. cbn [cells_bytes cbytes] in Hb.
pose proof (bytes_at_ov_read segs m _ _ 0 4 Hb) as R. rewrite Z.add_0_r in R.
rewrite R. 2:{ cbn [skipn]. rewrite length_app, length_le8. lia. }
change (skipn 0 (le8 w ++ cells_bytes post)) with (le8 w ++ cells_bytes post).
rewrite firstn_app, length_le8. change (4 - 8)%nat with 0%nat. rewrite firstn_O, app_nil_r, firstn4_le8. reflexivity.
Qed.

#[using="Type"] Lemma bytes_at_nil : forall m a, (0 <= a)%Z -> (a <= 2^64)%Z -> bytes_at segs m a [].
Proof. clear - segs. intros m a H0 H1. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia. Qed.

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
Hypothesis QHI : (q < 2^63)%Z.
Hypothesis TQ : TOPOK q.
Hypothesis FRM0 : frm0 fc0.

Hypothesis HA : (A + zlength fmt <= STATIC_SPLIT)%Z.

Hypothesis SEP_F : (((got_ssp + 8)%Z <= Fp /\ Fp + 232 <= ssp_guard) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
Hypothesis SEP_B : (((ssp_guard + 8)%Z <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
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

Notation SPv := (Z_to_bv 64 (q + -544)).
Notation FPv := (Z_to_bv 64 Fp).

Definition Fokd (F1 F2 : bvmap 5 word) : Prop := forall k : reg, bv_unsigned k <> 10%Z -> reg_get F2 k = reg_get F1 k.
Definition Fok (Ft : bvmap 5 word) : Prop := forall k : reg, bv_unsigned k <> 10%Z -> reg_get Ft k = reg_get F k.
#[using="Type"] Lemma Fok_refl : Fok F. Proof. clear - St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0. first [clear SFR | gw_hide SFR | idtac]; first [clear SFL | gw_hide SFL | idtac]; first [clear TOK | gw_hide TOK | idtac]; first [clear HOUT | gw_hide HOUT | idtac]; first [clear HF | gw_hide HF | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear GLO | gw_hide GLO | idtac]; first [clear QHI | gw_hide QHI | idtac]; first [clear TQ | gw_hide TQ | idtac]; first [clear FRM0 | gw_hide FRM0 | idtac]; first [clear HA | gw_hide HA | idtac]; first [clear SEP_F | gw_hide SEP_F | idtac]; first [clear SEP_B | gw_hide SEP_B | idtac]; first [clear HAP | gw_hide HAP | idtac]; first [clear HVA | gw_hide HVA | idtac]; first [clear A0 | gw_hide A0 | idtac]; first [clear VAHI | gw_hide VAHI | idtac]; first [clear BS0 | gw_hide BS0 | idtac]. intros k _. reflexivity. Qed.
#[using="Type"] Lemma Fok_trans : forall F1 F2, Fok F1 -> (forall k : reg, bv_unsigned k <> 10%Z -> reg_get F2 k = reg_get F1 k) -> Fok F2.
Proof. clear - St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0. first [clear SFR | gw_hide SFR | idtac]; first [clear SFL | gw_hide SFL | idtac]; first [clear TOK | gw_hide TOK | idtac]; first [clear HOUT | gw_hide HOUT | idtac]; first [clear HF | gw_hide HF | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear GLO | gw_hide GLO | idtac]; first [clear QHI | gw_hide QHI | idtac]; first [clear TQ | gw_hide TQ | idtac]; first [clear FRM0 | gw_hide FRM0 | idtac]; first [clear HA | gw_hide HA | idtac]; first [clear SEP_F | gw_hide SEP_F | idtac]; first [clear SEP_B | gw_hide SEP_B | idtac]; first [clear HAP | gw_hide HAP | idtac]; first [clear HVA | gw_hide HVA | idtac]; first [clear A0 | gw_hide A0 | idtac]; first [clear VAHI | gw_hide VAHI | idtac]; first [clear BS0 | gw_hide BS0 | idtac]. intros F1 F2 H1 H2 k Hk. rewrite (H2 k Hk). apply H1. exact Hk. Qed.

Definition POST : Z -> St -> machine_state -> Prop :=
fun r st' ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (apv : word) (m' : word -> option byte),
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0e s1e (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
Ft (ret_pc ra) fc' None m' (seg_rom segs)
/\ munch W m0 m' /\ wmono segs m0 m' /\ mem_inv segs m'
/\ frm0 fc' /\ Fok Ft
/\ stk segs m' lo q
/\ SINK m' st'
/\ ssp_cells m' canary
/\ rw_cells segs m' AP [C8 apv]
/\ (0 <= r <= INT_MAX)%Z.

Definition hi_cells : list cell :=
[C8 canary; C8 s11e; C8 s10e; C8 s9e; C8 s8e; C8 s7e; C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 ra].

Definition lo_cells (pfx s2s za pl plp l10n alo ahi : word) (j128 : list byte) : list cell :=
[C8 pfx; C8 s2s; C8 za; C8 pl; C8 plp; C8 (Z_to_bv 64 18446744072850558157); C8 (Z_to_bv 64 18446744073709486079);
C8 nla; C8 nlt; C8 (Z_to_bv 64 AP); C8 (Z_to_bv 64 75913); C8 l10n; C8 (Z_to_bv 64 ssp_guard); C8 (Z_to_bv 64 214748364);
C8 alo; C8 ahi; CB 24 j128].

Definition finv (m : word -> option byte) : Prop :=
mem_inv segs m /\ munch W m0 m /\ wmono segs m0 m
/\ rw_cells segs m (q + -112) hi_cells
/\ stk segs m lo (q + -544)
/\ bytes_at segs m A (zb fmt)
/\ va_area m VA slots
/\ rw_cells segs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells segs m ssp_guard [C8 canary].

#[using="Type"] Lemma u8_lit : forall c, (0 <= c < 256)%Z -> bv_unsigned (Z_to_bv 8 c) = c.
Proof. clear - St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0. first [clear SFR | gw_hide SFR | idtac]; first [clear SFL | gw_hide SFL | idtac]; first [clear TOK | gw_hide TOK | idtac]; first [clear HOUT | gw_hide HOUT | idtac]; first [clear HF | gw_hide HF | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear GLO | gw_hide GLO | idtac]; first [clear QHI | gw_hide QHI | idtac]; first [clear TQ | gw_hide TQ | idtac]; first [clear FRM0 | gw_hide FRM0 | idtac]; first [clear HA | gw_hide HA | idtac]; first [clear SEP_F | gw_hide SEP_F | idtac]; first [clear SEP_B | gw_hide SEP_B | idtac]; first [clear HAP | gw_hide HAP | idtac]; first [clear HVA | gw_hide HVA | idtac]; first [clear A0 | gw_hide A0 | idtac]; first [clear VAHI | gw_hide VAHI | idtac]; first [clear BS0 | gw_hide BS0 | idtac]. intros c Hc. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. apply Z.mod_small. cbn. lia. Qed.
#[using="HF"] Lemma fmt_rng : forall i, (0 <= i < zlength fmt)%Z -> (0 <= znth fmt i < 256)%Z.
Proof. clear - HF St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0. first [clear SFR | gw_hide SFR | idtac]; first [clear SFL | gw_hide SFL | idtac]; first [clear TOK | gw_hide TOK | idtac]; first [clear HOUT | gw_hide HOUT | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear GLO | gw_hide GLO | idtac]; first [clear QHI | gw_hide QHI | idtac]; first [clear TQ | gw_hide TQ | idtac]; first [clear FRM0 | gw_hide FRM0 | idtac]; first [clear HA | gw_hide HA | idtac]; first [clear SEP_F | gw_hide SEP_F | idtac]; first [clear SEP_B | gw_hide SEP_B | idtac]; first [clear HAP | gw_hide HAP | idtac]; first [clear HVA | gw_hide HVA | idtac]; first [clear A0 | gw_hide A0 | idtac]; first [clear VAHI | gw_hide VAHI | idtac]; first [clear BS0 | gw_hide BS0 | idtac]. intros i Hi. exact (Forall_znth _ fmt i HF Hi). Qed.

#[using="RNG_G_118c0 ROM_G_118c0"] Lemma states0_bytes : forall m, mem_inv segs m -> bytes_at segs m G_118c0 (zb STATES0).
Proof. clear - RNG_G_118c0 ROM_G_118c0 segs G_118c0 St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0. first [clear SFR | gw_hide SFR | idtac]; first [clear SFL | gw_hide SFL | idtac]; first [clear TOK | gw_hide TOK | idtac]; first [clear HOUT | gw_hide HOUT | idtac]; first [clear HF | gw_hide HF | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear GLO | gw_hide GLO | idtac]; first [clear QHI | gw_hide QHI | idtac]; first [clear TQ | gw_hide TQ | idtac]; first [clear FRM0 | gw_hide FRM0 | idtac]; first [clear HA | gw_hide HA | idtac]; first [clear SEP_F | gw_hide SEP_F | idtac]; first [clear SEP_B | gw_hide SEP_B | idtac]; first [clear HAP | gw_hide HAP | idtac]; first [clear HVA | gw_hide HVA | idtac]; first [clear A0 | gw_hide A0 | idtac]; first [clear VAHI | gw_hide VAHI | idtac]; first [clear BS0 | gw_hide BS0 | idtac].
intros m MI. pose proof RNG_G_118c0 as R; unfold gw_br in R.
lazymatch type of ROM_G_118c0 with ro_bytes _ _ ?L =>
assert (H : bytes_at segs m G_118c0 L) by (apply ro_bytes_at; [exact MI | lia | cbn; lia | exact ROM_G_118c0]);
change L with (zb STATES0 ++ skipn (length STATES0) L) in H
end.
apply bytes_at_app in H. exact (proj1 H).
Qed.

#[using="RNG_G_118c0 ROM_G_118c0"] Lemma states0_read : forall m t ty, mem_inv segs m -> conv_type t = Some ty ->
ov_read_bytes segs m (wa (t + G_118c0 + -65)) 1 = Some [Z_to_bv 8 ty].
Proof. clear - RNG_G_118c0 ROM_G_118c0 segs G_118c0 St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0. first [clear SFR | gw_hide SFR | idtac]; first [clear SFL | gw_hide SFL | idtac]; first [clear TOK | gw_hide TOK | idtac]; first [clear HOUT | gw_hide HOUT | idtac]; first [clear HF | gw_hide HF | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear GLO | gw_hide GLO | idtac]; first [clear QHI | gw_hide QHI | idtac]; first [clear TQ | gw_hide TQ | idtac]; first [clear FRM0 | gw_hide FRM0 | idtac]; first [clear HA | gw_hide HA | idtac]; first [clear SEP_F | gw_hide SEP_F | idtac]; first [clear SEP_B | gw_hide SEP_B | idtac]; first [clear HAP | gw_hide HAP | idtac]; first [clear HVA | gw_hide HVA | idtac]; first [clear A0 | gw_hide A0 | idtac]; first [clear VAHI | gw_hide VAHI | idtac]; first [clear BS0 | gw_hide BS0 | idtac].
clear - RNG_G_118c0 ROM_G_118c0 segs G_118c0. intros m t ty MI CT. pose proof (conv_type_range t ty CT) as R.
rewrite <- (states0_conv t ty CT).
eapply (zbytes_read m G_118c0 STATES0 (t - 65)); [apply states0_bytes; exact MI | change (zlength STATES0) with 58%Z; lia | f_equal; lia].
Qed.

#[using="RNG_G_118c0 ROM_G_118c0"] Lemma states01_bytes : forall m, mem_inv segs m -> bytes_at segs m G_118c0 (zb (STATES0 ++ STATES1)).
Proof. clear - RNG_G_118c0 ROM_G_118c0 segs G_118c0 St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0. first [clear SFR | gw_hide SFR | idtac]; first [clear SFL | gw_hide SFL | idtac]; first [clear TOK | gw_hide TOK | idtac]; first [clear HOUT | gw_hide HOUT | idtac]; first [clear HF | gw_hide HF | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear GLO | gw_hide GLO | idtac]; first [clear QHI | gw_hide QHI | idtac]; first [clear TQ | gw_hide TQ | idtac]; first [clear FRM0 | gw_hide FRM0 | idtac]; first [clear HA | gw_hide HA | idtac]; first [clear SEP_F | gw_hide SEP_F | idtac]; first [clear SEP_B | gw_hide SEP_B | idtac]; first [clear HAP | gw_hide HAP | idtac]; first [clear HVA | gw_hide HVA | idtac]; first [clear A0 | gw_hide A0 | idtac]; first [clear VAHI | gw_hide VAHI | idtac]; first [clear BS0 | gw_hide BS0 | idtac].
intros m MI. pose proof RNG_G_118c0 as R; unfold gw_br in R.
lazymatch type of ROM_G_118c0 with ro_bytes _ _ ?L =>
assert (H : bytes_at segs m G_118c0 L) by (apply ro_bytes_at; [exact MI | lia | cbn; lia | exact ROM_G_118c0]);
change L with (zb (STATES0 ++ STATES1) ++ skipn (length (STATES0 ++ STATES1)) L) in H
end.
apply bytes_at_app in H. exact (proj1 H).
Qed.
#[using="RNG_G_118c0 ROM_G_118c0"] Lemma states0_read_l : forall m, mem_inv segs m -> ov_read_bytes segs m (wa (108 + G_118c0 + -65)) 1 = Some [Z_to_bv 8 1].
Proof. clear - RNG_G_118c0 ROM_G_118c0 segs G_118c0 St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0. first [clear SFR | gw_hide SFR | idtac]; first [clear SFL | gw_hide SFL | idtac]; first [clear TOK | gw_hide TOK | idtac]; first [clear HOUT | gw_hide HOUT | idtac]; first [clear HF | gw_hide HF | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear GLO | gw_hide GLO | idtac]; first [clear QHI | gw_hide QHI | idtac]; first [clear TQ | gw_hide TQ | idtac]; first [clear FRM0 | gw_hide FRM0 | idtac]; first [clear HA | gw_hide HA | idtac]; first [clear SEP_F | gw_hide SEP_F | idtac]; first [clear SEP_B | gw_hide SEP_B | idtac]; first [clear HAP | gw_hide HAP | idtac]; first [clear HVA | gw_hide HVA | idtac]; first [clear A0 | gw_hide A0 | idtac]; first [clear VAHI | gw_hide VAHI | idtac]; first [clear BS0 | gw_hide BS0 | idtac].
clear - RNG_G_118c0 ROM_G_118c0 segs G_118c0. intros m MI.
eapply (zbytes_read m G_118c0 (STATES0 ++ STATES1) (108 - 65)); [apply states01_bytes; exact MI | change (zlength (STATES0 ++ STATES1)) with 116%Z; lia | f_equal; lia].
Qed.
#[using="RNG_G_118c0 ROM_G_118c0"] Lemma states1_read : forall m t ty, mem_inv segs m -> conv_type_l t = Some ty ->
ov_read_bytes segs m (wa (t + (G_118c0 + 58)%Z + -65)) 1 = Some [Z_to_bv 8 ty].
Proof. clear - RNG_G_118c0 ROM_G_118c0 segs G_118c0 St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0. first [clear SFR | gw_hide SFR | idtac]; first [clear SFL | gw_hide SFL | idtac]; first [clear TOK | gw_hide TOK | idtac]; first [clear HOUT | gw_hide HOUT | idtac]; first [clear HF | gw_hide HF | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear GLO | gw_hide GLO | idtac]; first [clear QHI | gw_hide QHI | idtac]; first [clear TQ | gw_hide TQ | idtac]; first [clear FRM0 | gw_hide FRM0 | idtac]; first [clear HA | gw_hide HA | idtac]; first [clear SEP_F | gw_hide SEP_F | idtac]; first [clear SEP_B | gw_hide SEP_B | idtac]; first [clear HAP | gw_hide HAP | idtac]; first [clear HVA | gw_hide HVA | idtac]; first [clear A0 | gw_hide A0 | idtac]; first [clear VAHI | gw_hide VAHI | idtac]; first [clear BS0 | gw_hide BS0 | idtac].
clear - RNG_G_118c0 ROM_G_118c0 segs G_118c0. intros m t ty MI CT.
replace ty with (znth (STATES0 ++ STATES1) (58 + (t - 65))).
2:{ destruct (conv_type_l_ty _ _ CT) as [[-> [-> | ->]] | [-> ->]]; reflexivity. }
eapply (zbytes_read m G_118c0 (STATES0 ++ STATES1) (58 + (t - 65))); [apply states01_bytes; exact MI | | f_equal; lia].
change (zlength (STATES0 ++ STATES1)) with 116%Z. destruct (conv_type_l_ty _ _ CT) as [[_ [-> | ->]] | [_ ->]]; lia.
Qed.

Definition PFXSTR : list Z := [45; 43; 32; 32; 32; 48; 88; 48; 120]%Z.
#[using="RNG_G_102fd ROM_G_102fd"] Lemma pfx_bytes : forall m, mem_inv segs m -> bytes_at segs m G_102fd (zb PFXSTR).
Proof. clear - RNG_G_102fd ROM_G_102fd segs G_102fd St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0. first [clear SFR | gw_hide SFR | idtac]; first [clear SFL | gw_hide SFL | idtac]; first [clear TOK | gw_hide TOK | idtac]; first [clear HOUT | gw_hide HOUT | idtac]; first [clear HF | gw_hide HF | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear GLO | gw_hide GLO | idtac]; first [clear QHI | gw_hide QHI | idtac]; first [clear TQ | gw_hide TQ | idtac]; first [clear FRM0 | gw_hide FRM0 | idtac]; first [clear HA | gw_hide HA | idtac]; first [clear SEP_F | gw_hide SEP_F | idtac]; first [clear SEP_B | gw_hide SEP_B | idtac]; first [clear HAP | gw_hide HAP | idtac]; first [clear HVA | gw_hide HVA | idtac]; first [clear A0 | gw_hide A0 | idtac]; first [clear VAHI | gw_hide VAHI | idtac]; first [clear BS0 | gw_hide BS0 | idtac].
intros m MI. pose proof RNG_G_102fd as R; unfold gw_br in R.
lazymatch type of ROM_G_102fd with ro_bytes _ _ ?L =>
assert (H : bytes_at segs m G_102fd L) by (apply ro_bytes_at; [exact MI | lia | cbn; lia | exact ROM_G_102fd]);
change L with (zb PFXSTR ++ skipn (length PFXSTR) L) in H
end.
apply bytes_at_app in H. exact (proj1 H).
Qed.
#[using="RNG_G_102fd ROM_G_102fd"] Lemma pfx_sub : forall m k n, mem_inv segs m -> (k + n <= 9)%nat ->
bytes_at segs m (G_102fd + Z.of_nat k) (zb (firstn n (skipn k PFXSTR))).
Proof. clear - RNG_G_102fd ROM_G_102fd segs G_102fd St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0. first [clear SFR | gw_hide SFR | idtac]; first [clear SFL | gw_hide SFL | idtac]; first [clear TOK | gw_hide TOK | idtac]; first [clear HOUT | gw_hide HOUT | idtac]; first [clear HF | gw_hide HF | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear GLO | gw_hide GLO | idtac]; first [clear QHI | gw_hide QHI | idtac]; first [clear TQ | gw_hide TQ | idtac]; first [clear FRM0 | gw_hide FRM0 | idtac]; first [clear HA | gw_hide HA | idtac]; first [clear SEP_F | gw_hide SEP_F | idtac]; first [clear SEP_B | gw_hide SEP_B | idtac]; first [clear HAP | gw_hide HAP | idtac]; first [clear HVA | gw_hide HVA | idtac]; first [clear A0 | gw_hide A0 | idtac]; first [clear VAHI | gw_hide VAHI | idtac]; first [clear BS0 | gw_hide BS0 | idtac].
clear - RNG_G_102fd ROM_G_102fd segs G_102fd. intros m k n MI Hk. rewrite zb_firstn, zb_skipn. apply bytes_at_sub; [apply pfx_bytes; exact MI|]. cbn. lia.
Qed.

#[using="RNG_G_107e0 ROM_G_107e0"] Lemma xdigits_bytes : forall m, mem_inv segs m -> bytes_at segs m G_107e0 (zb XDIGITS).
Proof. clear - RNG_G_107e0 ROM_G_107e0 segs G_107e0 St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0. first [clear SFR | gw_hide SFR | idtac]; first [clear SFL | gw_hide SFL | idtac]; first [clear TOK | gw_hide TOK | idtac]; first [clear HOUT | gw_hide HOUT | idtac]; first [clear HF | gw_hide HF | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear GLO | gw_hide GLO | idtac]; first [clear QHI | gw_hide QHI | idtac]; first [clear TQ | gw_hide TQ | idtac]; first [clear FRM0 | gw_hide FRM0 | idtac]; first [clear HA | gw_hide HA | idtac]; first [clear SEP_F | gw_hide SEP_F | idtac]; first [clear SEP_B | gw_hide SEP_B | idtac]; first [clear HAP | gw_hide HAP | idtac]; first [clear HVA | gw_hide HVA | idtac]; first [clear A0 | gw_hide A0 | idtac]; first [clear VAHI | gw_hide VAHI | idtac]; first [clear BS0 | gw_hide BS0 | idtac].
intros m MI. pose proof RNG_G_107e0 as R; unfold gw_br in R.
lazymatch type of ROM_G_107e0 with ro_bytes _ _ ?L =>
assert (H : bytes_at segs m G_107e0 L) by (apply ro_bytes_at; [exact MI | lia | cbn; lia | exact ROM_G_107e0]);
change L with (zb XDIGITS ++ skipn (length XDIGITS) L) in H
end.
apply bytes_at_app in H. exact (proj1 H).
Qed.
#[using="RNG_G_107e0 ROM_G_107e0"] Lemma xdigits_read : forall m v, mem_inv segs m -> (0 <= v < 16)%Z ->
ov_read_bytes segs m (wa (G_107e0 + v)) 1 = Some [Z_to_bv 8 (znth XDIGITS v)].
Proof. clear - RNG_G_107e0 ROM_G_107e0 segs G_107e0 St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0. first [clear SFR | gw_hide SFR | idtac]; first [clear SFL | gw_hide SFL | idtac]; first [clear TOK | gw_hide TOK | idtac]; first [clear HOUT | gw_hide HOUT | idtac]; first [clear HF | gw_hide HF | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear GLO | gw_hide GLO | idtac]; first [clear QHI | gw_hide QHI | idtac]; first [clear TQ | gw_hide TQ | idtac]; first [clear FRM0 | gw_hide FRM0 | idtac]; first [clear HA | gw_hide HA | idtac]; first [clear SEP_F | gw_hide SEP_F | idtac]; first [clear SEP_B | gw_hide SEP_B | idtac]; first [clear HAP | gw_hide HAP | idtac]; first [clear HVA | gw_hide HVA | idtac]; first [clear A0 | gw_hide A0 | idtac]; first [clear VAHI | gw_hide VAHI | idtac]; first [clear BS0 | gw_hide BS0 | idtac].
clear - RNG_G_107e0 ROM_G_107e0 segs G_107e0. intros m v MI Hv. eapply (zbytes_read m G_107e0 XDIGITS v); [apply xdigits_bytes; exact MI | change (zlength XDIGITS) with 16%Z; lia | reflexivity].
Qed.

Lemma jt1_read_s : forall m t, mem_inv segs m -> t = 115%Z -> ov_read_bytes segs m (wa (G_11778 + 4 * (t - 65))) 4 = Some (le4 (Z_to_bv 64 jt_11778_o1504)).
Proof. intros m t MI ->. exact (gw_jt_rdw_G_11778 m 200%Z jt_11778_o1504 MI ltac:(lia) ROM_jt_11778_50). Qed.
Lemma jt1_read_d : forall m t, mem_inv segs m -> (t = 100 \/ t = 105)%Z -> ov_read_bytes segs m (wa (G_11778 + 4 * (t - 65))) 4 = Some (le4 (Z_to_bv 64 jt_11778_o1432)).
Proof. intros m t MI [-> | ->]; [exact (gw_jt_rdw_G_11778 m 140%Z jt_11778_o1432 MI ltac:(lia) ROM_jt_11778_35) | exact (gw_jt_rdw_G_11778 m 160%Z jt_11778_o1432 MI ltac:(lia) ROM_jt_11778_40)]. Qed.
Lemma jt1_read_u : forall m t, mem_inv segs m -> t = 117%Z -> ov_read_bytes segs m (wa (G_11778 + 4 * (t - 65))) 4 = Some (le4 (Z_to_bv 64 jt_11778_o1744)).
Proof. intros m t MI ->. exact (gw_jt_rdw_G_11778 m 208%Z jt_11778_o1744 MI ltac:(lia) ROM_jt_11778_52). Qed.
Lemma jt1_read_x : forall m t, mem_inv segs m -> (t = 120 \/ t = 88)%Z -> ov_read_bytes segs m (wa (G_11778 + 4 * (t - 65))) 4 = Some (le4 (Z_to_bv 64 jt_11778_o1864)).
Proof. intros m t MI [-> | ->]; [exact (gw_jt_rdw_G_11778 m 220%Z jt_11778_o1864 MI ltac:(lia) ROM_jt_11778_55) | exact (gw_jt_rdw_G_11778 m 92%Z jt_11778_o1864 MI ltac:(lia) ROM_jt_11778_23)]. Qed.
Lemma jt1_read_fp : forall m t, mem_inv segs m -> conv_type t = Some T_DBL -> ov_read_bytes segs m (wa (G_11778 + 4 * (t - 65))) 4 = Some (le4 (Z_to_bv 64 jt_11778_o1352)).
Proof.
intros m t MI CT. unfold conv_type, T_PTR, T_INT, T_UINT, T_DBL in CT.
repeat match type of CT with (if ?c then _ else _) = _ => destruct c eqn:?; [try discriminate CT|] end; try discriminate CT.
repeat match goal with E : (_ || _) = true |- _ => apply orb_true_iff in E; destruct E as [E|E] | E : (_ =? _) = true |- _ => apply Z.eqb_eq in E end;
subst; [exact (gw_jt_rdw_G_11778 m 144%Z jt_11778_o1352 MI ltac:(lia) ROM_jt_11778_36) | exact (gw_jt_rdw_G_11778 m 148%Z jt_11778_o1352 MI ltac:(lia) ROM_jt_11778_37) | exact (gw_jt_rdw_G_11778 m 152%Z jt_11778_o1352 MI ltac:(lia) ROM_jt_11778_38) | exact (gw_jt_rdw_G_11778 m 16%Z jt_11778_o1352 MI ltac:(lia) ROM_jt_11778_4) | exact (gw_jt_rdw_G_11778 m 20%Z jt_11778_o1352 MI ltac:(lia) ROM_jt_11778_5) | exact (gw_jt_rdw_G_11778 m 24%Z jt_11778_o1352 MI ltac:(lia) ROM_jt_11778_6)].
Qed.
Lemma jt1_read_c : forall m t, mem_inv segs m -> t = 99%Z -> ov_read_bytes segs m (wa (G_11778 + 4 * (t - 65))) 4 = Some (le4 (Z_to_bv 64 jt_11778_o1800)).
Proof. intros m t MI ->. exact (gw_jt_rdw_G_11778 m 136%Z jt_11778_o1800 MI ltac:(lia) ROM_jt_11778_34). Qed.

#[using="Type"] Lemma conv_type_cases : forall t ty, conv_type t = Some ty ->
(ty = T_PTR /\ t = 115%Z) \/ (ty = T_INT /\ (t = 100 \/ t = 105)%Z) \/ (ty = T_UINT /\ (t = 117 \/ t = 120 \/ t = 88)%Z) \/ (ty = T_DBL)
\/ (ty = T_INT /\ t = 99%Z).
Proof. clear - St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0. first [clear SFR | gw_hide SFR | idtac]; first [clear SFL | gw_hide SFL | idtac]; first [clear TOK | gw_hide TOK | idtac]; first [clear HOUT | gw_hide HOUT | idtac]; first [clear HF | gw_hide HF | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear GLO | gw_hide GLO | idtac]; first [clear QHI | gw_hide QHI | idtac]; first [clear TQ | gw_hide TQ | idtac]; first [clear FRM0 | gw_hide FRM0 | idtac]; first [clear HA | gw_hide HA | idtac]; first [clear SEP_F | gw_hide SEP_F | idtac]; first [clear SEP_B | gw_hide SEP_B | idtac]; first [clear HAP | gw_hide HAP | idtac]; first [clear HVA | gw_hide HVA | idtac]; first [clear A0 | gw_hide A0 | idtac]; first [clear VAHI | gw_hide VAHI | idtac]; first [clear BS0 | gw_hide BS0 | idtac].
clear. intros t ty CT. unfold conv_type in CT.
repeat match type of CT with (if ?c then _ else _) = _ => destruct c eqn:?; [injection CT as <-|] end; try discriminate CT;
repeat match goal with E : (_ || _) = true |- _ => apply orb_true_iff in E; destruct E as [E|E] | E : (_ =? _) = true |- _ => apply Z.eqb_eq in E end;
subst; auto 10.
Qed.

#[using="Type"] Lemma fl_shl50 : forall fl, (0 <= fl < 131072)%Z ->
(Z.land (Z.shiftl fl 50) 18446744073709551615 < 9223372036854775808 <-> Z.land fl 8192 = 0)%Z.
Proof. clear - St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0. first [clear SFR | gw_hide SFR | idtac]; first [clear SFL | gw_hide SFL | idtac]; first [clear TOK | gw_hide TOK | idtac]; first [clear HOUT | gw_hide HOUT | idtac]; first [clear HF | gw_hide HF | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear GLO | gw_hide GLO | idtac]; first [clear QHI | gw_hide QHI | idtac]; first [clear TQ | gw_hide TQ | idtac]; first [clear FRM0 | gw_hide FRM0 | idtac]; first [clear HA | gw_hide HA | idtac]; first [clear SEP_F | gw_hide SEP_F | idtac]; first [clear SEP_B | gw_hide SEP_B | idtac]; first [clear HAP | gw_hide HAP | idtac]; first [clear HVA | gw_hide HVA | idtac]; first [clear A0 | gw_hide A0 | idtac]; first [clear VAHI | gw_hide VAHI | idtac]; first [clear BS0 | gw_hide BS0 | idtac].
clear. intros fl Hfl. rewrite Z.shiftl_mul_pow2 by lia.
change 8192%Z with (2^13)%Z. rewrite zb_land_pow2 by lia.
change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
split; intros H; Z.div_mod_to_equations; nia.
Qed.
#[using="Type"] Lemma nzmask_bits' : forall n, (0 <= n < 0 + Z.of_nat 64)%Z -> Bool.eqb (Z.testbit 18446744073709486079 n) (negb (Z.testbit 65536 n)) = true.
Proof. clear - St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0. first [clear SFR | gw_hide SFR | idtac]; first [clear SFL | gw_hide SFL | idtac]; first [clear TOK | gw_hide TOK | idtac]; first [clear HOUT | gw_hide HOUT | idtac]; first [clear HF | gw_hide HF | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear GLO | gw_hide GLO | idtac]; first [clear QHI | gw_hide QHI | idtac]; first [clear TQ | gw_hide TQ | idtac]; first [clear FRM0 | gw_hide FRM0 | idtac]; first [clear HA | gw_hide HA | idtac]; first [clear SEP_F | gw_hide SEP_F | idtac]; first [clear SEP_B | gw_hide SEP_B | idtac]; first [clear HAP | gw_hide HAP | idtac]; first [clear HVA | gw_hide HVA | idtac]; first [clear A0 | gw_hide A0 | idtac]; first [clear VAHI | gw_hide VAHI | idtac]; first [clear BS0 | gw_hide BS0 | idtac]. clear. apply Zrange_forallb. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma nzmask_eq : forall fl, (0 <= fl < 131072)%Z -> Z.land fl 18446744073709486079 = Z.land fl (Z.lnot 65536).
Proof. clear - St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0. first [clear SFR | gw_hide SFR | idtac]; first [clear SFL | gw_hide SFL | idtac]; first [clear TOK | gw_hide TOK | idtac]; first [clear HOUT | gw_hide HOUT | idtac]; first [clear HF | gw_hide HF | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear GLO | gw_hide GLO | idtac]; first [clear QHI | gw_hide QHI | idtac]; first [clear TQ | gw_hide TQ | idtac]; first [clear FRM0 | gw_hide FRM0 | idtac]; first [clear HA | gw_hide HA | idtac]; first [clear SEP_F | gw_hide SEP_F | idtac]; first [clear SEP_B | gw_hide SEP_B | idtac]; first [clear HAP | gw_hide HAP | idtac]; first [clear HVA | gw_hide HVA | idtac]; first [clear A0 | gw_hide A0 | idtac]; first [clear VAHI | gw_hide VAHI | idtac]; first [clear BS0 | gw_hide BS0 | idtac].
clear. intros fl Hfl. apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec, Z.lnot_spec by lia.
destruct (Z.lt_ge_cases n 64).
- pose proof (nzmask_bits' n ltac:(cbn; lia)) as E. destruct (Z.testbit 18446744073709486079 n), (Z.testbit 65536 n); cbn in E; try discriminate; reflexivity.
- replace (Z.testbit fl n) with false; [reflexivity|]. symmetry.
destruct (Z.eq_dec fl 0) as [->|]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|].
apply Z.lt_le_trans with 17%Z; [apply Z.log2_lt_pow2; cbn in *; lia|lia].
Qed.
#[using="Type"] Lemma land_bound' : forall a m, (0 <= a)%Z -> (0 <= m)%Z -> (0 <= Z.land a m <= a)%Z.
Proof. clear - St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0. first [clear SFR | gw_hide SFR | idtac]; first [clear SFL | gw_hide SFL | idtac]; first [clear TOK | gw_hide TOK | idtac]; first [clear HOUT | gw_hide HOUT | idtac]; first [clear HF | gw_hide HF | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear GLO | gw_hide GLO | idtac]; first [clear QHI | gw_hide QHI | idtac]; first [clear TQ | gw_hide TQ | idtac]; first [clear FRM0 | gw_hide FRM0 | idtac]; first [clear HA | gw_hide HA | idtac]; first [clear SEP_F | gw_hide SEP_F | idtac]; first [clear SEP_B | gw_hide SEP_B | idtac]; first [clear HAP | gw_hide HAP | idtac]; first [clear HVA | gw_hide HVA | idtac]; first [clear A0 | gw_hide A0 | idtac]; first [clear VAHI | gw_hide VAHI | idtac]; first [clear BS0 | gw_hide BS0 | idtac].
clear. intros a m Ha Hm. split; [apply Z.land_nonneg; left; exact Ha|].
pose proof (Z.sub_land_same_l a m) as E.
assert (0 <= Z.land a (Z.lnot m))%Z by (apply Z.land_nonneg; left; exact Ha). lia.
Qed.

#[using="Type"] Lemma sextw_small : forall p, (-2147483648 <= p < 2147483648)%Z -> bv_swrap 32 (Z.land p 18446744073709551615 + 0) = p.
Proof. clear - St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0. first [clear SFR | gw_hide SFR | idtac]; first [clear SFL | gw_hide SFL | idtac]; first [clear TOK | gw_hide TOK | idtac]; first [clear HOUT | gw_hide HOUT | idtac]; first [clear HF | gw_hide HF | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear GLO | gw_hide GLO | idtac]; first [clear QHI | gw_hide QHI | idtac]; first [clear TQ | gw_hide TQ | idtac]; first [clear FRM0 | gw_hide FRM0 | idtac]; first [clear HA | gw_hide HA | idtac]; first [clear SEP_F | gw_hide SEP_F | idtac]; first [clear SEP_B | gw_hide SEP_B | idtac]; first [clear HAP | gw_hide HAP | idtac]; first [clear HVA | gw_hide HVA | idtac]; first [clear A0 | gw_hide A0 | idtac]; first [clear VAHI | gw_hide VAHI | idtac]; first [clear BS0 | gw_hide BS0 | idtac].
clear. intros p Hp. rewrite Z.add_0_r. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
rewrite swrap32_eq.
replace (p mod 2 ^ 64)%Z with (p + 2^64 * (- (p / 2^64)))%Z by (Z.div_mod_to_equations; lia).
change (2^64)%Z with (4294967296 * 4294967296)%Z.
set (kq := (- (p / (4294967296 * 4294967296)))%Z). clearbody kq. Z.div_mod_to_equations. nia.
Qed.

#[using="Type"] Lemma pad_test_xor : forall fl b, Z.land b 73728 = b ->
(Z.land (Z.lxor fl b) 73728 =? 0)%Z = (Z.land fl 73728 =? b)%Z.
Proof. clear - St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0. first [clear SFR | gw_hide SFR | idtac]; first [clear SFL | gw_hide SFL | idtac]; first [clear TOK | gw_hide TOK | idtac]; first [clear HOUT | gw_hide HOUT | idtac]; first [clear HF | gw_hide HF | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear GLO | gw_hide GLO | idtac]; first [clear QHI | gw_hide QHI | idtac]; first [clear TQ | gw_hide TQ | idtac]; first [clear FRM0 | gw_hide FRM0 | idtac]; first [clear HA | gw_hide HA | idtac]; first [clear SEP_F | gw_hide SEP_F | idtac]; first [clear SEP_B | gw_hide SEP_B | idtac]; first [clear HAP | gw_hide HAP | idtac]; first [clear HVA | gw_hide HVA | idtac]; first [clear A0 | gw_hide A0 | idtac]; first [clear VAHI | gw_hide VAHI | idtac]; first [clear BS0 | gw_hide BS0 | idtac].
clear. intros fl b Hb. rewrite land_lxor_distr, Hb.
destruct (Z.eqb_spec (Z.lxor (Z.land fl 73728) b) 0) as [E|E]; destruct (Z.eqb_spec (Z.land fl 73728) b) as [E2|E2]; try reflexivity; exfalso.
- apply E2. apply Z.lxor_eq. exact E.
- apply E. rewrite E2. apply Z.lxor_nilpotent.
Qed.

Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | zl | progress f_equal ].

#[using="Type"] Lemma implM_eq_ms : forall {X} (c : M St X) s Q ms ms', ms = ms' -> implM segs c s Q ms' -> implM segs c s Q ms.
Proof. clear - segs St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0. first [clear SFR | gw_hide SFR | idtac]; first [clear SFL | gw_hide SFL | idtac]; first [clear TOK | gw_hide TOK | idtac]; first [clear HOUT | gw_hide HOUT | idtac]; first [clear HF | gw_hide HF | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear GLO | gw_hide GLO | idtac]; first [clear QHI | gw_hide QHI | idtac]; first [clear TQ | gw_hide TQ | idtac]; first [clear FRM0 | gw_hide FRM0 | idtac]; first [clear HA | gw_hide HA | idtac]; first [clear SEP_F | gw_hide SEP_F | idtac]; first [clear SEP_B | gw_hide SEP_B | idtac]; first [clear HAP | gw_hide HAP | idtac]; first [clear HVA | gw_hide HVA | idtac]; first [clear A0 | gw_hide A0 | idtac]; first [clear VAHI | gw_hide VAHI | idtac]; first [clear BS0 | gw_hide BS0 | idtac]. intros X c s Q ms ms' -> H. exact H. Qed.

#[using="segs SFR"] Lemma sink_store : forall m st a (bs : list byte),
SINK m st -> (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2^64)%Z ->
(a + Z.of_nat (length bs) <= Fp \/ Fp + 232 <= a)%Z -> (a + Z.of_nat (length bs) <= B \/ B + BS <= a)%Z ->
SINK (write_to_mem m (wa a) bs) st.
Proof. clear - segs SFR St Fp B BS SINK TOPOK OUT OUTFP SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0. first [clear SFL | gw_hide SFL | idtac]; first [clear TOK | gw_hide TOK | idtac]; first [clear HOUT | gw_hide HOUT | idtac]; first [clear HF | gw_hide HF | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear GLO | gw_hide GLO | idtac]; first [clear QHI | gw_hide QHI | idtac]; first [clear TQ | gw_hide TQ | idtac]; first [clear FRM0 | gw_hide FRM0 | idtac]; first [clear HA | gw_hide HA | idtac]; first [clear SEP_F | gw_hide SEP_F | idtac]; first [clear SEP_B | gw_hide SEP_B | idtac]; first [clear HAP | gw_hide HAP | idtac]; first [clear HVA | gw_hide HVA | idtac]; first [clear A0 | gw_hide A0 | idtac]; first [clear VAHI | gw_hide VAHI | idtac]; first [clear BS0 | gw_hide BS0 | idtac].
intros m st a bs HS Ha Hb D1 D2.
apply (SFR [(a, a + Z.of_nat (length bs))]%Z m _ st HS).
- apply munch_write; [apply munch_refl | lia | lia | cbn; lia].
- apply wmono_write. apply wmono_refl.
- constructor; [cbn; lia | constructor].
- constructor; [cbn; lia | constructor].
Qed.
#[using="SFR"] Lemma sink_call : forall Wc m m' st,
SINK m st -> munch Wc m m' -> wmono segs m m' ->
Forall (fun iv => snd iv <= Fp \/ Fp + 232 <= fst iv)%Z Wc ->
Forall (fun iv => snd iv <= B \/ B + BS <= fst iv)%Z Wc ->
SINK m' st.
Proof. clear - SFR segs St Fp B BS SINK TOPOK OUT OUTFP SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0. first [clear SFL | gw_hide SFL | idtac]; first [clear TOK | gw_hide TOK | idtac]; first [clear HOUT | gw_hide HOUT | idtac]; first [clear HF | gw_hide HF | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear GLO | gw_hide GLO | idtac]; first [clear QHI | gw_hide QHI | idtac]; first [clear TQ | gw_hide TQ | idtac]; first [clear FRM0 | gw_hide FRM0 | idtac]; first [clear HA | gw_hide HA | idtac]; first [clear SEP_F | gw_hide SEP_F | idtac]; first [clear SEP_B | gw_hide SEP_B | idtac]; first [clear HAP | gw_hide HAP | idtac]; first [clear HVA | gw_hide HVA | idtac]; first [clear A0 | gw_hide A0 | idtac]; first [clear VAHI | gw_hide VAHI | idtac]; first [clear BS0 | gw_hide BS0 | idtac]. intros Wc m m' st HS MU WM D1 D2. exact (SFR Wc m m' st HS MU WM D1 D2). Qed.

#[using="fmt slots"] Lemma arg_ok_W : forall m m' w a, arg_ok Fp B BS m lo q AP w a -> munch W m m' -> arg_ok Fp B BS m' lo q AP w a.
Proof. clear - fmt slots St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A AP VA nla nlt HF LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0. first [clear SFR | gw_hide SFR | idtac]; first [clear SFL | gw_hide SFL | idtac]; first [clear TOK | gw_hide TOK | idtac]; first [clear HOUT | gw_hide HOUT | idtac]; first [clear HF | gw_hide HF | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear GLO | gw_hide GLO | idtac]; first [clear QHI | gw_hide QHI | idtac]; first [clear TQ | gw_hide TQ | idtac]; first [clear FRM0 | gw_hide FRM0 | idtac]; first [clear HA | gw_hide HA | idtac]; first [clear SEP_F | gw_hide SEP_F | idtac]; first [clear SEP_B | gw_hide SEP_B | idtac]; first [clear HAP | gw_hide HAP | idtac]; first [clear HVA | gw_hide HVA | idtac]; first [clear A0 | gw_hide A0 | idtac]; first [clear VAHI | gw_hide VAHI | idtac]; first [clear BS0 | gw_hide BS0 | idtac].
intros m m' w a H MU. destruct a as [s|i|u|d|li|lu]; cbn in H |- *; try exact H.
destruct H as (slack & BYs & Hs & PAD & NZ & D1 & D2 & D3 & D4). exists slack.
split; [|repeat (split; [assumption|]); assumption].
eapply bytes_at_transport; [exact BYs | exact MU |].
unfold W. cbn [disjoint_from]. rewrite length_app, zb_length. cbn [length]. unfold zlength in *. lia.
Qed.
#[using="fmt slots"] Lemma args_ok_W : forall m m' ws args, args_ok Fp B BS m lo q AP ws args -> munch W m m' -> args_ok Fp B BS m' lo q AP ws args.
Proof. clear - fmt slots St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A AP VA nla nlt HF LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0. first [clear SFR | gw_hide SFR | idtac]; first [clear SFL | gw_hide SFL | idtac]; first [clear TOK | gw_hide TOK | idtac]; first [clear HOUT | gw_hide HOUT | idtac]; first [clear HF | gw_hide HF | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear GLO | gw_hide GLO | idtac]; first [clear QHI | gw_hide QHI | idtac]; first [clear TQ | gw_hide TQ | idtac]; first [clear FRM0 | gw_hide FRM0 | idtac]; first [clear HA | gw_hide HA | idtac]; first [clear SEP_F | gw_hide SEP_F | idtac]; first [clear SEP_B | gw_hide SEP_B | idtac]; first [clear HAP | gw_hide HAP | idtac]; first [clear HVA | gw_hide HVA | idtac]; first [clear A0 | gw_hide A0 | idtac]; first [clear VAHI | gw_hide VAHI | idtac]; first [clear BS0 | gw_hide BS0 | idtac].
intros m m' ws args. revert ws. induction args as [|a args IH]; intros ws H MU; [destruct ws; exact I|].
cbn [args_ok] in H |- *.
destruct ws as [|w ws]; [exact H|]. destruct H as [H1 H2]. split; [eapply arg_ok_W; eauto | apply IH; assumption].
Qed.

Definition lo_cells14 (pfx s2s za pl plp l10n : word) : list cell :=
[C8 pfx; C8 s2s; C8 za; C8 pl; C8 plp; C8 (Z_to_bv 64 18446744072850558157); C8 (Z_to_bv 64 18446744073709486079);
C8 nla; C8 nlt; C8 (Z_to_bv 64 AP); C8 (Z_to_bv 64 75913); C8 l10n; C8 (Z_to_bv 64 ssp_guard); C8 (Z_to_bv 64 214748364)].
#[using="Type"] Lemma lo_split : forall m pfx s2s za pl plp l10n alo ahi j128,
rw_cells segs m (q + -544) (lo_cells pfx s2s za pl plp l10n alo ahi j128) ->
rw_cells segs m (q + -544) (lo_cells14 pfx s2s za pl plp l10n) /\
rw_cells segs m (q + -544 + 112) [C8 alo; C8 ahi] /\ rw_cells segs m (q + -544 + 128) [CB 24 j128].
Proof. clear - segs St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0. first [clear SFR | gw_hide SFR | idtac]; first [clear SFL | gw_hide SFL | idtac]; first [clear TOK | gw_hide TOK | idtac]; first [clear HOUT | gw_hide HOUT | idtac]; first [clear HF | gw_hide HF | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear GLO | gw_hide GLO | idtac]; first [clear QHI | gw_hide QHI | idtac]; first [clear TQ | gw_hide TQ | idtac]; first [clear FRM0 | gw_hide FRM0 | idtac]; first [clear HA | gw_hide HA | idtac]; first [clear SEP_F | gw_hide SEP_F | idtac]; first [clear SEP_B | gw_hide SEP_B | idtac]; first [clear HAP | gw_hide HAP | idtac]; first [clear HVA | gw_hide HVA | idtac]; first [clear A0 | gw_hide A0 | idtac]; first [clear VAHI | gw_hide VAHI | idtac]; first [clear BS0 | gw_hide BS0 | idtac].
clear - segs. intros. unfold lo_cells in H.
apply (proj1 (rw_cells_app segs m _ [_;_;_;_;_;_;_;_;_;_;_;_;_;_] _)) in H. destruct H as [H1 H2]. cbn [cells_size csize Nat.add app] in H2.
change (Z.of_nat 112) with 112%Z in H2.
apply (proj1 (rw_cells_app segs m _ [_;_] _)) in H2. destruct H2 as [H2 H3]. cbn [cells_size csize Nat.add app] in H3.
change (Z.of_nat 16) with 16%Z in H3.
split; [exact H1|]. split; [exact H2|]. replace (q + -544 + 128)%Z with (q + -544 + 112 + 16)%Z by lia. exact H3.
Qed.
#[using="Type"] Lemma lo_join : forall m pfx s2s za pl plp l10n alo ahi j128,
rw_cells segs m (q + -544) (lo_cells14 pfx s2s za pl plp l10n) ->
rw_cells segs m (q + -544 + 112) [C8 alo; C8 ahi] -> rw_cells segs m (q + -544 + 128) [CB 24 j128] ->
rw_cells segs m (q + -544) (lo_cells pfx s2s za pl plp l10n alo ahi j128).
Proof. clear - segs St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0. first [clear SFR | gw_hide SFR | idtac]; first [clear SFL | gw_hide SFL | idtac]; first [clear TOK | gw_hide TOK | idtac]; first [clear HOUT | gw_hide HOUT | idtac]; first [clear HF | gw_hide HF | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear GLO | gw_hide GLO | idtac]; first [clear QHI | gw_hide QHI | idtac]; first [clear TQ | gw_hide TQ | idtac]; first [clear FRM0 | gw_hide FRM0 | idtac]; first [clear HA | gw_hide HA | idtac]; first [clear SEP_F | gw_hide SEP_F | idtac]; first [clear SEP_B | gw_hide SEP_B | idtac]; first [clear HAP | gw_hide HAP | idtac]; first [clear HVA | gw_hide HVA | idtac]; first [clear A0 | gw_hide A0 | idtac]; first [clear VAHI | gw_hide VAHI | idtac]; first [clear BS0 | gw_hide BS0 | idtac].
clear - segs. intros. unfold lo_cells.
apply (proj2 (rw_cells_app segs m _ [_;_;_;_;_;_;_;_;_;_;_;_;_;_] _)). split; [exact H|]. cbn [cells_size csize Nat.add app].
change (Z.of_nat 112) with 112%Z.
apply (proj2 (rw_cells_app segs m _ [_;_] _)). cbn [cells_size csize Nat.add app]. change (Z.of_nat 16) with 16%Z. split; [exact H0|].
replace (q + -544 + 112 + 16)%Z with (q + -544 + 128)%Z by lia. exact H1.
Qed.

Ltac transport_chunks segs_ m a bs ::=
repeat match goal with
| H : bytes_at segs_ m ?A2 ?bs2 |- _ =>
first [ apply (bytes_at_write_other segs_ m a bs A2 bs2) in H;
[ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : wr_at segs_ m ?A2 ?n2 |- _ => apply (wr_at_write segs_ m A2 n2 (wa a) bs) in H
| H : rw_cells segs_ m ?A2 ?cs2 |- _ =>
first [ apply (rw_cells_frame segs_ m A2 cs2 a bs) in H;
[ | lia | simpl_sizes; slia | simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : ro_cells segs_ m ?A2 ?cs2 |- _ =>
first [ apply (ro_cells_frame segs_ m A2 cs2 a bs) in H;
[ | lia | simpl_sizes; slia | simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : u8arr segs_ m ?A2 ?xs |- _ =>
first [ apply (u8arr_frame segs_ m A2 xs a bs) in H;
[ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : u8ro segs_ m ?A2 ?xs |- _ =>
first [ apply (u8ro_frame segs_ m A2 xs a bs) in H;
[ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : SINK m ?st |- _ =>
first [ apply (sink_store m st a bs) in H; [ | lia | simpl_sizes; slia | simpl_sizes; slia | simpl_sizes; slia ]
| idtac "note: dropping SINK hypothesis (not provably disjoint from store):" H; clear H ]
end.
Ltac transport_after_call segs_ m m' MU WM ::=
let W := lazymatch type of MU with munch ?W _ _ => W end in
repeat match goal with
| H : bytes_at segs_ m ?A2 ?bs2 |- _ =>
first [ apply (bytes_at_transport segs_ W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : wr_at segs_ m ?A2 ?n2 |- _ => apply (wr_at_transport segs_ m m' A2 n2) in H; [ | exact WM ]
| H : rw_cells segs_ m ?A2 ?cs2 |- _ =>
first [ apply (rw_cells_transport segs_ W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : ro_cells segs_ m ?A2 ?cs2 |- _ =>
first [ apply (ro_cells_transport segs_ W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : u8arr segs_ m ?A2 ?xs |- _ =>
first [ apply (u8arr_transport segs_ W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : u8ro segs_ m ?A2 ?xs |- _ =>
first [ apply (u8ro_transport segs_ W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : SINK m ?st |- _ =>
first [ eapply (sink_call W m m' st) in H;
[ | exact MU | exact WM
| repeat (apply Forall_cons; [ cbn [fst snd]; slia | ]); apply Forall_nil
| repeat (apply Forall_cons; [ cbn [fst snd]; slia | ]); apply Forall_nil ]
| idtac "note: dropping SINK hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : stk segs_ m ?loq ?hiq |- _ =>
first [ apply (stk_transport_disjoint segs_ W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; slia ]
| clear H ]
| H : munch ?Wq ?mq m |- _ =>
first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ unfold sub_fp; cbn [outside]; intros; slia | exact MU ] ]
| fail 100 "callee footprint not inside caller footprint" ]
| H : wmono segs_ ?mq m |- _ => apply (wmono_trans segs_ mq m m') in H; [ | exact WM ]
end.

#[using="GLOBALS_TOP RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP va_area_bound pop_arg_spec fmt LO GLO QHI HAP HVA"] Lemma pop_arg_callq : forall ra' t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(Ft : bvmap 5 word) fc (m : word -> option byte) (a0v k ty : Z) (slot x y : word),
a0v = (q + -544 + 112)%Z ->
rw_cells segs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] ->
va_area m VA slots -> nth_error slots (Z.to_nat k) = Some slot -> (0 <= k)%Z ->
rw_cells segs m (q + -544 + 112) [C8 x; C8 y] ->
stk segs m lo (q + -544) ->
mem_inv segs m ->
(ty = T_PTR \/ ty = T_INT \/ ty = T_UINT \/ ty = T_DBL \/ ty = T_LONG \/ ty = T_ULONG)%Z ->
evt segs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Ft' m',
ms' = MS (mkR ra' SPv gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
Ft' (ret_pc ra') fc None m' (seg_rom segs)
/\ munch [(q + -544 - 16, q + -544); (AP, AP + 8); (q + -544 + 112, q + -544 + 112 + 16)]%Z m m'
/\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' lo (q + -544)
/\ rw_cells segs m' AP [C8 (Z_to_bv 64 (VA + 8 * (k + 1)))]
/\ rw_cells segs m' (q + -544 + 112) [C8 (Q91D.Mq3.pop_arg_lo ty slot); C8 (Q91D.Mq3.pop_arg_hi ty slot y)]
/\ Fokd Ft Ft')
(MS (mkR ra' SPv gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a0v) (Z_to_bv 64 ty) (Z_to_bv 64 AP) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (Z_to_bv 64 (base + 3632)) fc None m (seg_rom segs)).
Proof. clear - GLOBALS_TOP RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP va_area_bound pop_arg_spec fmt LO GLO QHI HAP HVA segs base St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A AP VA slots nla nlt HF TQ FRM0 HA SEP_F SEP_B A0 VAHI BS0. try gw_hide SFR; try gw_hide SFL; try gw_hide TOK; try gw_hide HOUT; try gw_hide HF; first [clear TQ | gw_hide TQ | idtac]; first [clear FRM0 | gw_hide FRM0 | idtac]; first [clear HA | gw_hide HA | idtac]; first [clear SEP_F | gw_hide SEP_F | idtac]; first [clear SEP_B | gw_hide SEP_B | idtac]; first [clear A0 | gw_hide A0 | idtac]; first [clear VAHI | gw_hide VAHI | idtac]; first [clear BS0 | gw_hide BS0 | idtac].
clear SFR SFL TOK HOUT HF.
intros until y. intros -> APC VAA NTH Hk ARGC ST MI TY. gw_expose GLOBALS_TOP; unfold PC_DEPTH in *.
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

#[using="GLOBALS_TOP RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP strnlen_spec LO GLO QHI"] Lemma strnlen_callq : forall ra' t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(Ft : bvmap 5 word) fc (m : word -> option byte) (P n : Z) (buf : list byte),
stk segs m lo (q + -544) ->
bytes_at segs m P buf ->
memchr_ok P 0 n buf ->
mem_inv segs m ->
(P + Z.of_nat (length buf) <= lo \/ q <= P)%Z -> (0 < P < 2^64)%Z -> (0 <= n < 2^64)%Z ->
evt segs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
ms' = MS (mkR ra' SPv gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (strnlen_res n buf)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
Ft (ret_pc ra') fc None m' (seg_rom segs)
/\ munch [(q + -544 - 32, q + -544)]%Z m m'
/\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' lo (q + -544)
/\ bytes_at segs m' P buf)
(MS (mkR ra' SPv gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (Z_to_bv 64 (e_2596c + 0x0)) fc None m (seg_rom segs)).
Proof. clear - GLOBALS_TOP RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP strnlen_spec LO GLO QHI segs e_2596c St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0. try gw_hide SFR; try gw_hide SFL; try gw_hide TOK; try gw_hide HOUT; try gw_hide HF; first [clear TQ | gw_hide TQ | idtac]; first [clear FRM0 | gw_hide FRM0 | idtac]; first [clear HA | gw_hide HA | idtac]; first [clear SEP_F | gw_hide SEP_F | idtac]; first [clear SEP_B | gw_hide SEP_B | idtac]; first [clear HAP | gw_hide HAP | idtac]; first [clear HVA | gw_hide HVA | idtac]; first [clear A0 | gw_hide A0 | idtac]; first [clear VAHI | gw_hide VAHI | idtac]; first [clear BS0 | gw_hide BS0 | idtac].
clear SFR SFL TOK HOUT HF.
intros until buf. intros ST BUF OK MI SEP P0 Hn. gw_expose GLOBALS_TOP; unfold PC_DEPTH in *.
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
Proof. clear - St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0. first [clear SFR | gw_hide SFR | idtac]; first [clear SFL | gw_hide SFL | idtac]; first [clear TOK | gw_hide TOK | idtac]; first [clear HOUT | gw_hide HOUT | idtac]; try gw_hide HF; first [clear LO | gw_hide LO | idtac]; first [clear GLO | gw_hide GLO | idtac]; first [clear QHI | gw_hide QHI | idtac]; first [clear TQ | gw_hide TQ | idtac]; first [clear FRM0 | gw_hide FRM0 | idtac]; first [clear HA | gw_hide HA | idtac]; first [clear SEP_F | gw_hide SEP_F | idtac]; first [clear SEP_B | gw_hide SEP_B | idtac]; first [clear HAP | gw_hide HAP | idtac]; first [clear HVA | gw_hide HVA | idtac]; first [clear A0 | gw_hide A0 | idtac]; first [clear VAHI | gw_hide VAHI | idtac]; first [clear BS0 | gw_hide BS0 | idtac].
clear. intros s HF IN. unfold zb in IN. apply in_map_iff in IN. destruct IN as (c & E & Hc).
apply (proj1 (Forall_forall _ s) HF) in Hc.
assert (E' : bv_unsigned (Z_to_bv 8 c) = bv_unsigned (Z_to_bv 8 0)) by (rewrite E; reflexivity).
rewrite u8_lit in E' by lia. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z in E'. lia.
Qed.

Definition out_postq (ra' : word) (Ft : bvmap 5 word) (fc : bv 32) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(S : Z) (bs : list Z) (m : word -> option byte) : unit -> St -> machine_state -> Prop :=
fun _ st' ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
ms' = MS (mkR ra' SPv gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (ret_pc ra') fc None m' (seg_rom segs)
/\ munch [(lo, q + -544); (Fp, Fp + 232); (B, B + BS)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' lo (q + -544)
/\ SINK m' st'
/\ ssp_cells m' canary
/\ bytes_at segs m' S (zb bs).
#[using="GLOBALS_TOP RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_ssp_guard_GLOBALS_TOP BS0 GLO HAP HOUT LO QHI SEP_B SEP_F TOK TQ fmt slots"] Lemma out_callq : forall ra' t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(Ft : bvmap 5 word) fc (m : word -> option byte) (st : St) (S L : Z) (bs : list Z),
SINK m st -> bytes_at segs m S (zb bs) -> Forall (fun c => 0 <= c < 256)%Z bs -> L = zlength bs ->
stk segs m lo (q + -544) -> ssp_cells m canary -> mem_inv segs m ->
(0 <= S)%Z -> (S < 2^64)%Z ->
(S + zlength bs <= lo \/ q + -544 <= S)%Z -> (S + zlength bs <= Fp \/ Fp + 232 <= S)%Z -> (S + zlength bs <= B \/ B + BS <= S)%Z ->
(zlength bs < 2^31)%Z ->
implM segs (OUT bs) st (out_postq ra' Ft fc s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 S bs m)
(MS (mkR ra' SPv gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 L) FPv a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (Z_to_bv 64 (e_fwritex + 0x0)) fc None m (seg_rom segs)).
Proof. clear - GLOBALS_TOP RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_ssp_guard_GLOBALS_TOP BS0 GLO HAP HOUT LO QHI SEP_B SEP_F TOK TQ fmt slots segs e_fwritex St Fp B BS SINK TOPOK OUT OUTFP SFR SFL ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A AP VA nla nlt HF FRM0 HA HVA A0 VAHI. try clear VA. try clear AP. try clear TOPOK.
clear SFR SFL HF.
intros until bs. intros HS SRC RNG -> ST SSP MI HS0 HS1 D1 D2 D3 LB. gw_expose GLOBALS_TOP; unfold PC_DEPTH in *.
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
Ft' (ret_pc ra') fc' None m' (seg_rom segs)
/\ munch [(lo, q + -544); (Fp, Fp + 232); (B, B + BS)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ frm0 fc' /\ Fokd Ft Ft'
/\ stk segs m' lo (q + -544)
/\ SINK m' st'
/\ ssp_cells m' canary.
#[using="RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_ssp_guard_GLOBALS_TOP TOK AP VA LO GLO QHI TQ SEP_F SEP_B HAP"] Lemma fp_callq : forall ra' t0 t1 t2 s0 s1 (a1 a2 a7 : word) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(Ft : bvmap 5 word) fc (m : word -> option byte) (st : St) (y w p fl t : Z),
fpcall_stmt Fp B BS SINK TOPOK OUTFP (y, w, p, fl, t) ->
SINK m st -> y = (bv_unsigned a1 + 2^64 * bv_unsigned a2)%Z -> bv_unsigned a7 <> 5%Z ->
(-2^31 <= w <= 1)%Z -> (-2^31 <= p < 2^20)%Z -> (0 <= fl < 2^32)%Z -> (0 <= t < 256)%Z -> Z.lor t 32 <> 97%Z ->
stk segs m lo (q + -544) -> ssp_cells m canary -> mem_inv segs m -> frm0 fc ->
implM segs (OUTFP y w p fl t) st (fp_postq ra' Ft s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
(MS (mkR ra' SPv gp tp t0 t1 t2 s0 s1 FPv a1 a2 (Z_to_bv 64 w) (Z_to_bv 64 p) (Z_to_bv 64 fl) (Z_to_bv 64 t) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (Z_to_bv 64 (base + 4152)) fc None m (seg_rom segs)).
Proof. clear - RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_ssp_guard_GLOBALS_TOP TOK AP VA LO GLO QHI TQ SEP_F SEP_B HAP segs base St Fp B BS SINK TOPOK OUT OUTFP SFR SFL HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt slots nla nlt HF FRM0 HA HVA A0 VAHI BS0. try gw_hide SFR; try gw_hide SFL; try gw_hide HOUT; try gw_hide HF; first [clear FRM0 | gw_hide FRM0 | idtac]; first [clear HA | gw_hide HA | idtac]; first [clear HVA | gw_hide HVA | idtac]; first [clear A0 | gw_hide A0 | idtac]; first [clear VAHI | gw_hide VAHI | idtac]; first [clear BS0 | gw_hide BS0 | idtac].
clear SFR SFL HOUT HF.
intros until t. intros FPC HS Hy H7 Hw Hp Hfl Ht Hta ST SSP MI FRM. gw_expose GLOBALS_TOP; unfold PC_DEPTH in *.
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
Proof. clear - St Fp B BS SINK TOPOK OUT OUTFP SFR SFL TOK HOUT ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt HF LO GLO QHI TQ FRM0 HA SEP_F SEP_B HAP HVA A0 VAHI BS0. first [clear SFR | gw_hide SFR | idtac]; first [clear SFL | gw_hide SFL | idtac]; first [clear TOK | gw_hide TOK | idtac]; first [clear HOUT | gw_hide HOUT | idtac]; first [clear HF | gw_hide HF | idtac]; first [clear LO | gw_hide LO | idtac]; first [clear GLO | gw_hide GLO | idtac]; first [clear QHI | gw_hide QHI | idtac]; first [clear TQ | gw_hide TQ | idtac]; first [clear FRM0 | gw_hide FRM0 | idtac]; first [clear HA | gw_hide HA | idtac]; first [clear SEP_F | gw_hide SEP_F | idtac]; first [clear SEP_B | gw_hide SEP_B | idtac]; first [clear HAP | gw_hide HAP | idtac]; first [clear HVA | gw_hide HVA | idtac]; first [clear A0 | gw_hide A0 | idtac]; first [clear VAHI | gw_hide VAHI | idtac]; first [clear BS0 | gw_hide BS0 | idtac].
clear. intros t CT. unfold conv_type, T_PTR, T_INT, T_UINT, T_DBL in CT.
repeat match type of CT with (if ?c then _ else _) = _ => destruct c eqn:?; [try discriminate CT|] end; try discriminate CT.
repeat match goal with E : (_ || _) = true |- _ => apply orb_true_iff in E; destruct E as [E|E] | E : (_ =? _) = true |- _ => apply Z.eqb_eq in E end;
subst; (split; [lia | discriminate]).
Qed.

Definition S_EXIT : Prop :=
forall (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (r : Z)
(pfx s2s za pl plp l10n alo ahi : word) (j128 digs pad : list byte) (apv : word),
let _ := ctx_all in
finv m ->
rw_cells segs m (q + -544) (lo_cells pfx s2s za pl plp l10n alo ahi j128) ->
rw_cells segs m (q + -392) [CB 24 digs] ->
rw_cells segs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells segs m AP [C8 apv] ->
frm0 fc -> Fok Ft -> (0 <= r <= INT_MAX)%Z ->
evt segs (POST r st)
(MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 r) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0xddc)) fc None m (seg_rom segs)).

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
evt segs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (A + i + n)) a1 a2 x13 x14 x15 x16 x17
(Z_to_bv 64 (2147483647 - cnt')) (Z_to_bv 64 cnt') x20 (Z_to_bv 64 (A + i + n)) (Z_to_bv 64 n) (Z_to_bv 64 (A + i)) x24 x25 (Z_to_bv 64 n) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x128)) fc None m (seg_rom segs))) ->
evt segs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (znth fmt i)) x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 cnt') x20 x21 x22 (Z_to_bv 64 (A + i)) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0xcc)) fc None m (seg_rom segs)).

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
evt segs Q
(MS (mkR x1 SPv gp tp (Z_to_bv 64 75913) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 (Z_to_bv 64 c') (Z_to_bv 64 (A + k')) a3 a4 a5 (Z_to_bv 64 1) (Z_to_bv 64 32)
x18 x19 x20 x21 x22 x23 (Z_to_bv 64 FL) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x1e0)) fc None m (seg_rom segs))) ->
evt segs Q
(MS (mkR x1 SPv gp tp (Z_to_bv 64 75913) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 x11 x12 w3 (Z_to_bv 64 (A + p + k)) x15 (Z_to_bv 64 1) (Z_to_bv 64 32)
x18 x19 x20 x21 x22 x23 (Z_to_bv 64 fl) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x1bc)) fc None m (seg_rom segs)).

Definition S_WLOOP : Prop :=
forall (x1 x5 x6 x7 x10 x12 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
(pos acc w : Z) (s2 : list Z) (pfx s2s za pl plp alo ahi : word) (j128 : list byte),
let _ := ctx_all in
finv m -> rw_cells segs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
(0 <= pos < zlength fmt)%Z -> (0 <= acc)%Z ->
is_digit (znth fmt pos) = true -> getint (sfx pos) acc = Some (w, s2) -> s2 <> [] ->
(forall (k2 : Z) (t0 t1 a1 a3 a4 a5 a6 a7 : word),
(pos < k2 < zlength fmt)%Z -> s2 = sfx k2 -> is_digit (znth fmt k2) = false -> (0 <= w <= INT_MAX)%Z ->
evt segs Q
(MS (mkR x1 SPv gp tp t0 t1 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 a1 (Z_to_bv 64 (A + k2)) a3 a4 a5 a6 a7
x18 x19 x20 x21 (Z_to_bv 64 w) x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x310)) fc None m (seg_rom segs))) ->
evt segs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 (Z_to_bv 64 (znth fmt pos + -48)) x12 (Z_to_bv 64 (A + pos)) x14 x15 x16 x17
x18 x19 x20 x21 (Z_to_bv 64 acc) x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x274)) fc None m (seg_rom segs)).

Definition S_WIDTH : Prop :=
forall (x1 x5 x6 x7 x10 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
(k1 w : Z) (s2 : list Z) (pfx s2s za pl plp alo ahi : word) (j128 : list byte),
let _ := ctx_all in
finv m -> rw_cells segs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
(0 <= k1 < zlength fmt)%Z ->
getint (sfx k1) 0 = Some (w, s2) -> s2 <> [] ->
(forall (k2 : Z) (t0 t1 a1 a3 a4 a5 a6 a7 : word),
(k1 <= k2 < zlength fmt)%Z -> s2 = sfx k2 -> is_digit (znth fmt k2) = false -> (0 <= w <= INT_MAX)%Z ->
evt segs Q
(MS (mkR x1 SPv gp tp t0 t1 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 a1 (Z_to_bv 64 (A + k2)) a3 a4 a5 a6 a7
x18 x19 x20 x21 (Z_to_bv 64 w) x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x310)) fc None m (seg_rom segs))) ->
evt segs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 (Z_to_bv 64 (znth fmt k1)) (Z_to_bv 64 (A + k1)) x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x228)) fc None m (seg_rom segs)).

Definition S_PLOOP : Prop :=
forall (x1 x6 x7 x10 x13 x14 x15 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
(pos acc p : Z) (s3 : list Z) (pfx s2s za pl plp alo ahi : word) (j128 : list byte),
let _ := ctx_all in
finv m -> rw_cells segs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
(0 <= pos < zlength fmt)%Z -> (0 <= acc)%Z ->
is_digit (znth fmt pos) = true -> getint (sfx pos) acc = Some (p, s3) -> s3 <> [] ->
(forall (k3 : Z) (a1 a3 a4 : word),
(pos < k3 < zlength fmt)%Z -> s3 = sfx k3 -> is_digit (znth fmt k3) = false -> (0 <= p <= INT_MAX)%Z ->
evt segs Q
(MS (mkR x1 SPv gp tp (Z_to_bv 64 1) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 a1 (Z_to_bv 64 (A + k3)) a3 a4 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x448)) fc None m (seg_rom segs))) ->
evt segs Q
(MS (mkR x1 SPv gp tp (Z_to_bv 64 1) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 (Z_to_bv 64 (znth fmt pos + -48)) (Z_to_bv 64 (A + pos)) x13 x14 x15 (Z_to_bv 64 10) (Z_to_bv 64 8)
x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 acc) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x3d4)) fc None m (seg_rom segs)).

Definition S_PREC : Prop :=
forall (x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
(k2 k3 p : Z) (xp : bool) (pfx s2s za pl plp alo ahi : word) (j128 : list byte),
let _ := ctx_all in
finv m -> rw_cells segs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
(0 <= k2 < zlength fmt)%Z ->
( (znth fmt k2 <> 46 /\ p = -1 /\ xp = false /\ k3 = k2)
\/ (znth fmt k2 = 46 /\ xp = true /\ k2 + 1 < zlength fmt /\ znth fmt (k2 + 1) <> 42
/\ getint (sfx (k2 + 1)) 0 = Some (p, sfx k3) /\ k2 + 1 <= k3 < zlength fmt) )%Z ->
(forall (a1 a3 a4 : word),
(-1 <= p <= INT_MAX)%Z ->
evt segs Q
(MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 a1 (Z_to_bv 64 (A + k3)) a3 a4 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x448)) fc None m (seg_rom segs))) ->
evt segs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 x11 (Z_to_bv 64 (A + k2)) x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x310)) fc None m (seg_rom segs)).

Definition S_STATE : Prop :=
forall (x1 x5 x6 x7 x11 x13 x14 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
(k3 ty : Z),
let _ := ctx_all in
finv m -> (0 <= k3 < zlength fmt)%Z -> conv_type (znth fmt k3) = Some ty ->
(forall (a2 a3 : word),
evt segs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (-1)) (Z_to_bv 64 ty) a2 a3 x14 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
x18 x19 x20 (Z_to_bv 64 (A + k3 + 1)) x22 x23 x24 x25 x26 (Z_to_bv 64 0) x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x4c8)) fc None m (seg_rom segs))) ->
evt segs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (-1)) x11 (Z_to_bv 64 (A + k3)) x13 x14 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x448)) fc None m (seg_rom segs)).

Definition S_STATEL : Prop :=
forall (x1 x5 x6 x7 x11 x13 x14 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
(k3 ty : Z),
let _ := ctx_all in
finv m -> (0 <= k3)%Z -> (k3 + 1 < zlength fmt)%Z -> znth fmt k3 = 108%Z -> conv_type_l (znth fmt (k3 + 1)) = Some ty ->
(forall (a2 a3 : word),
evt segs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (-1)) (Z_to_bv 64 ty) a2 a3 x14 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
x18 x19 x20 (Z_to_bv 64 (A + k3 + 2)) x22 x23 x24 x25 x26 (Z_to_bv 64 1) x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x4c8)) fc None m (seg_rom segs))) ->
evt segs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (-1)) x11 (Z_to_bv 64 (A + k3)) x13 x14 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x448)) fc None m (seg_rom segs)).

Definition S_DIR : Prop :=
forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
(i : Z) (d : dir) (rest : list Z) (pfx s2s za pl plp alo ahi : word) (j128 : list byte),
let _ := ctx_all in
finv m -> rw_cells segs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
(0 <= i)%Z -> (i + 1 <= zlength fmt)%Z ->
parse_dir (sfx (i + 1)) = Some (d, rest) ->
(forall (k4 : Z) (a2 a3 a4 t1 : word),
(i + 1 < k4 <= zlength fmt)%Z -> rest = sfx k4 -> znth fmt (k4 - 1) = d_t d ->
(0 <= d_fl d < 131072)%Z -> (0 <= d_w d <= INT_MAX)%Z -> (-1 <= d_p d <= INT_MAX)%Z ->
evt segs Q
(MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z (d_xp d))) t1 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
(Z_to_bv 64 (-1)) (Z_to_bv 64 (d_ty d)) a2 a3 a4 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
x18 x19 x20 (Z_to_bv 64 (A + k4)) (Z_to_bv 64 (d_w d)) x23 (Z_to_bv 64 (d_fl d)) (Z_to_bv 64 (d_p d)) x26 (Z_to_bv 64 (d_ps d)) x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x4c8)) fc None m (seg_rom segs))) ->
evt segs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 (Z_to_bv 64 (A + i)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x14c)) fc None m (seg_rom segs)).

Definition S_END : Prop :=
forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (r : Z)
(pfx s2s za pl plp l10n alo ahi : word) (j128 digs pad : list byte) (apv : word),
let _ := ctx_all in
finv m ->
rw_cells segs m (q + -544) (lo_cells pfx s2s za pl plp l10n alo ahi j128) ->
rw_cells segs m (q + -392) [CB 24 digs] ->
rw_cells segs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells segs m AP [C8 apv] ->
frm0 fc -> Fok Ft -> (0 <= r <= INT_MAX)%Z ->
evt segs (POST r st)
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 r) FPv x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0xc84)) fc None m (seg_rom segs)).

Definition S_HEAD (fuel : nat) : Prop :=
forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i cnt l k : Z) (args : list parg)
(pfx s2s za pl plp alo ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m ->
rw_cells segs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
rw_cells segs m (q + -392) [CB 24 digs] ->
rw_cells segs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells segs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i) args) ->
frm0 fc -> Fok Ft ->
(0 <= i)%Z -> (0 <= cnt)%Z -> (0 <= l)%Z -> (cnt + l <= INT_MAX)%Z ->
implM segs (printf_loop OUT OUTFP fuel (sfx i) args (cnt + l)) st POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 cnt) FPv (Z_to_bv 64 (A + i)) x22 x23 x24 x25 (Z_to_bv 64 l) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0xb0)) fc None m (seg_rom segs)).

Definition S_CONV : Prop :=
forall fuel, S_HEAD fuel ->
forall (x1 x6 x7 x12 x13 x14 x23 x26 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (d : dir) (a : parg) (args : list parg)
(pfx s2s za pl plp alo ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m ->
rw_cells segs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
rw_cells segs m (q + -392) [CB 24 digs] ->
rw_cells segs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells segs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) (a :: args) ->
match a with PA_g dd =>
fpcall_stmt Fp B BS SINK TOPOK OUTFP
(f128_of_d dd, d_w d, d_p d, (if Z.land (d_fl d) LEFT_ADJ =? 0 then d_fl d else Z.land (d_fl d) (Z.lnot ZERO_PAD))%Z, d_t d)
| _ => True end ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
frm0 fc -> Fok Ft ->
(1 <= i4 <= zlength fmt)%Z -> znth fmt (i4 - 1) = d_t d -> dir_ty_ok d ->
(0 <= d_fl d < 131072)%Z -> (0 <= d_w d <= INT_MAX)%Z -> (-1 <= d_p d <= INT_MAX)%Z ->
((d_xp d = false /\ d_p d = -1) \/ (d_xp d = true /\ 0 <= d_p d <= INT_MAX))%Z ->
(0 <= c <= INT_MAX)%Z ->
implM segs (cnt' <- conv OUT OUTFP c d a ;; printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
(MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z (d_xp d))) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
(Z_to_bv 64 (-1)) (Z_to_bv 64 (d_ty d)) x12 x13 x14 (Z_to_bv 64 (-58)) (Z_to_bv 64 58) (Z_to_bv 64 8)
(Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 (d_w d)) x23 (Z_to_bv 64 (d_fl d)) (Z_to_bv 64 (d_p d)) x26 (Z_to_bv 64 (d_ps d)) x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x4c8)) fc None m (seg_rom segs)).

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
rw_cells segs m (q + -544) (lo_cells (Z_to_bv 64 PFXA) s2s za (Z_to_bv 64 (zlength prefix)) plp (Z_to_bv 64 0) alo ahi j128) ->
rw_cells segs m (q + -392) [CB 24 digs] ->
rw_cells segs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells segs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
frm0 fc -> Fok Ft ->
bytes_at segs m BA (zb body) -> Forall (fun c => 0 <= c < 256)%Z body -> body_loc BA (zlength body) -> (BA + zlength body < 2^64)%Z -> (zlength body <= INT_MAX)%Z ->
(forall m', mem_inv segs m' -> bytes_at segs m' PFXA (zb prefix)) -> Forall (fun c => 0 <= c < 256)%Z prefix ->
(0 <= PFXA)%Z -> (PFXA + zlength prefix <= STATIC_SPLIT)%Z -> (zlength prefix <= 2)%Z ->
(0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (-1 <= p <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
implM segs (cnt' <- conv_tail OUT c fl w p prefix body ;; printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
x10 (Z_to_bv 64 (BA + zlength body)) x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) (Z_to_bv 64 BA) (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x94c)) fc None m (seg_rom segs)).

Definition tregs (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s8 s9 t3 t4 t5 t6 : word) (i4 c w BA wq pq : Z) : bvmap 5 word :=
mkR xra SPv gp tp t0 t1 t2 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) a0 a1 a2 a3 a4 a5 a6 a7
s2 (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) (Z_to_bv 64 BA) s8 s9 (Z_to_bv 64 wq) (Z_to_bv 64 pq) t3 t4 t5 t6.
Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | zl | progress f_equal ].
Definition tinv (m : word -> option byte) (st : St) (k i4 : Z) (args : list parg) (fuel : nat)
(PFXA fl n pl pq BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte) : Prop :=
finv m
/\ rw_cells segs m (q + -544) (lo_cells (Z_to_bv 64 PFXA) (Z_to_bv 64 (Z.land fl 73728)) (Z_to_bv 64 n) (Z_to_bv 64 pl) (Z_to_bv 64 (pl + pq)) (Z_to_bv 64 0) alo ahi j128)
/\ rw_cells segs m (q + -392) [CB 24 digs]
/\ rw_cells segs m (q + -368) [CB 256 pad]
/\ SINK m st /\ rw_cells segs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] /\ (0 <= k)%Z
/\ args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args
/\ Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args)
/\ bytes_at segs m BA (zb body) /\ Forall (fun c => 0 <= c < 256)%Z body /\ body_loc BA n /\ (BA + n < 2^64)%Z /\ n = zlength body
/\ (forall m', mem_inv segs m' -> bytes_at segs m' PFXA (zb prefix)) /\ Forall (fun c => 0 <= c < 256)%Z prefix
/\ (0 <= PFXA)%Z /\ (PFXA + pl <= STATIC_SPLIT)%Z /\ pl = zlength prefix /\ (pl <= 2)%Z
/\ (0 <= i4 <= zlength fmt)%Z /\ (0 <= fl < 131072)%Z /\ (0 <= n <= INT_MAX)%Z /\ (n <= pq)%Z /\ (pl + pq <= INT_MAX)%Z.

Definition S_T6 : Prop :=
forall fuel, S_HEAD fuel ->
forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 t3 t4 t5 t6 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (k i4 c w wq pq : Z) (args : list parg)
(PFXA fl n pl BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
tinv m st k i4 args fuel PFXA fl n pl pq BA prefix body alo ahi j128 digs pad ->
frm0 fc -> Fok Ft -> (0 <= c)%Z -> (0 <= w <= wq)%Z -> wq = Z.max w (pl + pq) -> (c + wq <= INT_MAX)%Z ->
implM segs (mpad OUT 32 wq (pl + pq) (Z.lxor fl LEFT_ADJ) ;;; printf_loop OUT OUTFP fuel (sfx i4) args (c + wq)) st POST
(MS (tregs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.land fl 73728)) s8 s9 t3 t4 t5 t6 i4 c w BA wq pq)
Ft (Z_to_bv 64 (base + 0xb68)) fc None m (seg_rom segs)).

Definition S_T5 : Prop :=
forall fuel, S_HEAD fuel ->
forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 t3 t4 t5 t6 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (k i4 c w wq pq : Z) (args : list parg)
(PFXA fl n pl BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
tinv m st k i4 args fuel PFXA fl n pl pq BA prefix body alo ahi j128 digs pad ->
frm0 fc -> Fok Ft -> (0 <= c)%Z -> (0 <= w <= wq)%Z -> wq = Z.max w (pl + pq) -> (c + wq <= INT_MAX)%Z ->
implM segs (OUT body ;;; mpad OUT 32 wq (pl + pq) (Z.lxor fl LEFT_ADJ) ;;; printf_loop OUT OUTFP fuel (sfx i4) args (c + wq)) st POST
(MS (tregs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.land fl 73728)) s8 s9 t3 t4 t5 t6 i4 c w BA wq pq)
Ft (Z_to_bv 64 (base + 0xb4c)) fc None m (seg_rom segs)).

Definition S_T4 : Prop :=
forall fuel, S_HEAD fuel ->
forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (k i4 c w wq pq : Z) (args : list parg)
(PFXA fl n pl BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
tinv m st k i4 args fuel PFXA fl n pl pq BA prefix body alo ahi j128 digs pad ->
frm0 fc -> Fok Ft -> (0 <= c)%Z -> (0 <= w <= wq)%Z -> wq = Z.max w (pl + pq) -> (c + wq <= INT_MAX)%Z ->
implM segs (mpad OUT 48 pq n 0 ;;; OUT body ;;; mpad OUT 32 wq (pl + pq) (Z.lxor fl LEFT_ADJ) ;;; printf_loop OUT OUTFP fuel (sfx i4) args (c + wq)) st POST
(MS (tregs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.land fl 73728)) s8 (Z_to_bv 64 pq) t3 t4 t5 t6 i4 c w BA wq pq)
Ft (Z_to_bv 64 (base + 0xac8)) fc None m (seg_rom segs)).

Definition S_T3 : Prop :=
forall fuel, S_HEAD fuel ->
forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (k i4 c w wq pq : Z) (args : list parg)
(PFXA fl n pl BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
tinv m st k i4 args fuel PFXA fl n pl pq BA prefix body alo ahi j128 digs pad ->
frm0 fc -> Fok Ft -> (0 <= c)%Z -> (0 <= w <= wq)%Z -> wq = Z.max w (pl + pq) -> (c + wq <= INT_MAX)%Z ->
implM segs (mpad OUT 48 wq (pl + pq) (Z.lxor fl ZERO_PAD) ;;; mpad OUT 48 pq n 0 ;;; OUT body ;;; mpad OUT 32 wq (pl + pq) (Z.lxor fl LEFT_ADJ) ;;; printf_loop OUT OUTFP fuel (sfx i4) args (c + wq)) st POST
(MS (tregs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.land fl 73728)) s8 (Z_to_bv 64 pq) t3 t4 t5 t6 i4 c w BA wq pq)
Ft (Z_to_bv 64 (base + 0xa40)) fc None m (seg_rom segs)).

Definition S_T2 : Prop :=
forall fuel, S_HEAD fuel ->
forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (k i4 c w wq pq : Z) (args : list parg)
(PFXA fl n pl BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
tinv m st k i4 args fuel PFXA fl n pl pq BA prefix body alo ahi j128 digs pad ->
frm0 fc -> Fok Ft -> (0 <= c)%Z -> (0 <= w <= wq)%Z -> wq = Z.max w (pl + pq) -> (c + wq <= INT_MAX)%Z ->
implM segs (OUT prefix ;;; mpad OUT 48 wq (pl + pq) (Z.lxor fl ZERO_PAD) ;;; mpad OUT 48 pq n 0 ;;; OUT body ;;; mpad OUT 32 wq (pl + pq) (Z.lxor fl LEFT_ADJ) ;;; printf_loop OUT OUTFP fuel (sfx i4) args (c + wq)) st POST
(MS (tregs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.land fl 73728)) s8 (Z_to_bv 64 pq) t3 t4 t5 t6 i4 c w BA wq pq)
Ft (Z_to_bv 64 (base + 0xa24)) fc None m (seg_rom segs)).

Definition S_T1 : Prop :=
forall fuel, S_HEAD fuel ->
forall (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (k i4 c w wq pq : Z) (args : list parg)
(PFXA fl n pl BA : Z) (prefix body : list Z) (alo ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
tinv m st k i4 args fuel PFXA fl n pl pq BA prefix body alo ahi j128 digs pad ->
frm0 fc -> Fok Ft -> (0 <= c)%Z -> (0 <= w <= wq)%Z -> wq = Z.max w (pl + pq) -> (c + wq <= INT_MAX)%Z ->
Z.land fl 73728 = 0%Z ->
implM segs (mpad OUT 32 wq (pl + pq) fl ;;; OUT prefix ;;; mpad OUT 48 wq (pl + pq) (Z.lxor fl ZERO_PAD) ;;; mpad OUT 48 pq n 0 ;;; OUT body ;;; mpad OUT 32 wq (pl + pq) (Z.lxor fl LEFT_ADJ) ;;; printf_loop OUT OUTFP fuel (sfx i4) args (c + wq)) st POST
(MS (tregs xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) s8 (Z_to_bv 64 pq) t3 t4 t5 t6 i4 c w BA wq pq)
Ft (Z_to_bv 64 (base + 0x9a4)) fc None m (seg_rom segs)).

Definition S_INTC2 : Prop :=
forall fuel, S_HEAD fuel ->
forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
(fl w p argi : Z) (prefix body : list Z) (BA PFXA : Z)
(s2s za plp ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m ->
rw_cells segs m (q + -544) (lo_cells (Z_to_bv 64 PFXA) s2s za (Z_to_bv 64 (zlength prefix)) plp (Z_to_bv 64 0) (Z_to_bv 64 argi) ahi j128) ->
rw_cells segs m (q + -392) [CB 24 digs] ->
rw_cells segs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells segs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
frm0 fc -> Fok Ft ->
bytes_at segs m BA (zb body) -> Forall (fun c => 0 <= c < 256)%Z body -> (BA + zlength body = q + -368)%Z -> (zlength body <= 24)%Z ->
(forall m', mem_inv segs m' -> bytes_at segs m' PFXA (zb prefix)) -> Forall (fun c => 0 <= c < 256)%Z prefix ->
(0 <= PFXA)%Z -> (PFXA + zlength prefix <= STATIC_SPLIT)%Z -> (zlength prefix <= 2)%Z ->
(0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (-1 <= p <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
(0 <= argi < 2^64)%Z ->
implM segs (cnt' <- (if ((argi =? 0) && (p =? 0))%Z then conv_tail OUT c fl w p prefix []
else conv_tail OUT c fl w (Z.max p (zlength body + (if (argi =? 0)%Z then 1 else 0))) prefix body) ;;
printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) (Z_to_bv 64 BA) (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x914)) fc None m (seg_rom segs)).

Definition S_INTC : Prop :=
forall fuel, S_HEAD fuel ->
forall (x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
(fl w p : Z) (xp : bool) (argi : Z) (prefix body : list Z) (BA PFXA : Z)
(s2s za plp ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m ->
rw_cells segs m (q + -544) (lo_cells (Z_to_bv 64 PFXA) s2s za (Z_to_bv 64 (zlength prefix)) plp (Z_to_bv 64 0) (Z_to_bv 64 argi) ahi j128) ->
rw_cells segs m (q + -392) [CB 24 digs] ->
rw_cells segs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells segs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
frm0 fc -> Fok Ft ->
bytes_at segs m BA (zb body) -> Forall (fun c => 0 <= c < 256)%Z body -> (BA + zlength body = q + -368)%Z -> (zlength body <= 24)%Z ->
(forall m', mem_inv segs m' -> bytes_at segs m' PFXA (zb prefix)) -> Forall (fun c => 0 <= c < 256)%Z prefix ->
(0 <= PFXA)%Z -> (PFXA + zlength prefix <= STATIC_SPLIT)%Z -> (zlength prefix <= 2)%Z ->
(0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
(0 <= argi < 2^64)%Z ->
implM segs (cnt' <- conv_int OUT c fl w p xp argi prefix body ;; printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
(MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) (Z_to_bv 64 BA) (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x8fc)) fc None m (seg_rom segs)).

Definition dloop_post (x1 x5 x6 x7 x8 x9 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (x j : Z) (ds : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists (a2 a3 : word) (xq : Z) (W : list Z) (m' : word -> option byte),
ms' = MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 xq) (Z_to_bv 64 (q + -392 + (j - zlength W))) a2 a3
(Z_to_bv 64 10) (Z_to_bv 64 18446744072850558157) (Z_to_bv 64 99) x17
x18 x19 x20 x21 x22 (Z_to_bv 64 (q + -392 + (j - zlength W))) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x8e4)) fc None m' (seg_rom segs)
/\ munch [(q + -392, q + -368)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ rw_cells segs m' (q + -392) [CB 24 (firstn (Z.to_nat (j - zlength W)) ds ++ zb W ++ skipn (Z.to_nat j) ds)]
/\ (1 <= xq <= 9)%Z /\ dec_digits x = (48 + xq)%Z :: W /\ (zlength W + 1 <= j)%Z.
Definition S_DLOOP : Prop :=
forall (x1 x5 x6 x7 x8 x9 x11 x12 x13 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (x j : Z) (ds : list byte),
let _ := ctx_all in
mem_inv segs m -> rw_cells segs m (q + -392) [CB 24 ds] ->
(10 <= x < 2^64)%Z -> (zlength (dec_digits x) <= j <= 24)%Z -> x11 = Z_to_bv 64 (q + -392 + j) ->
evt segs (dloop_post x1 x5 x6 x7 x8 x9 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc x j ds m)
(MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 x) x11 x12 x13
(Z_to_bv 64 10) (Z_to_bv 64 18446744072850558157) (Z_to_bv 64 99) x17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x8ac)) fc None m (seg_rom segs)).

Definition S_FMTU2 : Prop :=
forall fuel, S_HEAD fuel ->
forall (x1 x6 x7 x11 x12 x13 x14 x15 x16 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
(fl w p : Z) (xp : bool) (x d jj : Z) (W prefix : list Z) (PFXA : Z)
(pfx s2s za plp ahi : word) (j128 pre pad : list byte),
let _ := ctx_all in
finv m ->
rw_cells segs m (q + -544) (lo_cells pfx s2s za (Z_to_bv 64 (zlength prefix)) plp (Z_to_bv 64 0) (Z_to_bv 64 x) ahi j128) ->
rw_cells segs m (q + -392) [CB 24 (pre ++ zb W)] -> zlength pre = jj -> (1 <= jj)%Z ->
((d = 0 /\ W = [] /\ dec_digits x = []) \/ (1 <= d <= 9 /\ dec_digits x = (48 + d) :: W))%Z ->
rw_cells segs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells segs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
frm0 fc -> Fok Ft ->
(forall m', mem_inv segs m' -> bytes_at segs m' PFXA (zb prefix)) -> Forall (fun c => 0 <= c < 256)%Z prefix ->
(0 <= PFXA)%Z -> (PFXA + zlength prefix <= STATIC_SPLIT)%Z -> (zlength prefix <= 2)%Z ->
(0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
(0 <= x < 2^64)%Z ->
implM segs (cnt' <- conv_int OUT c fl w p xp x prefix (dec_digits x) ;; printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
(MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
(Z_to_bv 64 d) x11 x12 x13 x14 x15 x16 (Z_to_bv 64 PFXA)
(Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) (Z_to_bv 64 (q + -392 + jj)) (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x8e4)) fc None m (seg_rom segs)).

Definition S_FMTU : Prop :=
forall fuel, S_HEAD fuel ->
forall (x1 x6 x7 x11 x12 x13 x15 x16 x23 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
(fl w p : Z) (xp : bool) (x : Z) (prefix : list Z) (PFXA : Z)
(pfx s2s za plp ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m ->
rw_cells segs m (q + -544) (lo_cells pfx s2s za (Z_to_bv 64 (zlength prefix)) plp (Z_to_bv 64 0) (Z_to_bv 64 x) ahi j128) ->
rw_cells segs m (q + -392) [CB 24 digs] ->
rw_cells segs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells segs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
frm0 fc -> Fok Ft ->
(forall m', mem_inv segs m' -> bytes_at segs m' PFXA (zb prefix)) -> Forall (fun c => 0 <= c < 256)%Z prefix ->
(0 <= PFXA)%Z -> (PFXA + zlength prefix <= STATIC_SPLIT)%Z -> (zlength prefix <= 2)%Z ->
(0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
(0 <= x < 2^64)%Z ->
implM segs (cnt' <- conv_int OUT c fl w p xp x prefix (dec_digits x) ;; printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
(MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
(Z_to_bv 64 x) x11 x12 x13 (Z_to_bv 64 10) x15 x16 (Z_to_bv 64 PFXA)
(Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) x23 (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x89c)) fc None m (seg_rom segs)).

Definition S_CV_D : Prop :=
forall fuel, S_HEAD fuel ->
forall (x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
(fl w p : Z) (xp : bool) (i : Z)
(pfx s2s za pl plp ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m ->
rw_cells segs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) (Z_to_bv 64 (i mod 2^64)) ahi j128) ->
rw_cells segs m (q + -392) [CB 24 digs] ->
rw_cells segs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells segs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
frm0 fc -> Fok Ft ->
(0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
(-2^63 <= i < 2^63)%Z ->
implM segs (cnt' <- (let '(argi, prefix) :=
(if INTMAX_MAX <? i mod 2^64 then ((- (i mod 2^64)) mod 2^64, [45])
else if negb (Z.land fl MARK_POS =? 0) then (i mod 2^64, [43])
else if negb (Z.land fl PAD_POS =? 0) then (i mod 2^64, [32])
else (i mod 2^64, []))%Z in
conv_int OUT c fl w p xp argi prefix (dec_digits argi)) ;;
printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
(MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) x23 (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x598)) fc None m (seg_rom segs)).

Definition S_CV_U : Prop :=
forall fuel, S_HEAD fuel ->
forall (x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
(fl w p : Z) (xp : bool) (u : Z)
(pfx s2s za pl plp ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m ->
rw_cells segs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) (Z_to_bv 64 u) ahi j128) ->
rw_cells segs m (q + -392) [CB 24 digs] ->
rw_cells segs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells segs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
frm0 fc -> Fok Ft ->
(0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
(0 <= u < 2^64)%Z ->
implM segs (cnt' <- conv_int OUT c fl w p xp u [] (dec_digits u) ;; printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
(MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) x23 (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x6d0)) fc None m (seg_rom segs)).

Definition S_CV_C : Prop :=
forall fuel, S_HEAD fuel ->
forall (x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
(fl flc w p : Z) (xp : bool) (i : Z)
(pfx s2s za pl plp ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m ->
rw_cells segs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) (Z_to_bv 64 (i mod 2^64)) ahi j128) ->
rw_cells segs m (q + -392) [CB 24 digs] ->
rw_cells segs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells segs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
frm0 fc -> Fok Ft ->
(0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
flc = Z.land fl (Z.lnot ZERO_PAD) ->
implM segs (cnt' <- conv_tail OUT c (Z.land fl (Z.lnot ZERO_PAD)) w 1 [] [i mod 256] ;; printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
(MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) x23 (Z_to_bv 64 fl) (Z_to_bv 64 p) (Z_to_bv 64 flc) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x708)) fc None m (seg_rom segs)).

Definition xloop_post (x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (l x j : Z) (ds : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists (a2 a3 : word) (m' : word -> option byte),
let H := hex_digits l x in
ms' = MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 0) (Z_to_bv 64 l) a2 a3 x14 x15 x16 x17
x18 x19 x20 x21 x22 (Z_to_bv 64 (q + -392 + (j - zlength H))) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x788)) fc None m' (seg_rom segs)
/\ munch [(q + -392, q + -368)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ rw_cells segs m' (q + -392) [CB 24 (firstn (Z.to_nat (j - zlength H)) ds ++ zb H ++ skipn (Z.to_nat j) ds)]
/\ (zlength H <= j)%Z.
Definition S_XLOOP : Prop :=
forall (x1 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (l x j : Z) (ds : list byte),
let _ := ctx_all in
mem_inv segs m -> rw_cells segs m (q + -392) [CB 24 ds] ->
(0 < x < 2^64)%Z -> (l = 0 \/ l = 32)%Z -> (zlength (hex_digits l x) <= j <= 24)%Z -> x23 = Z_to_bv 64 (q + -392 + j) ->
evt segs (xloop_post x1 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc l x j ds m)
(MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 x) (Z_to_bv 64 l) x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x760)) fc None m (seg_rom segs)).

Definition S_CV_X : Prop :=
forall fuel, S_HEAD fuel ->
forall (x1 x6 x7 x10 x11 x12 x13 x14 x15 x17 x23 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
(fl w p : Z) (xp : bool) (u t : Z)
(pfx s2s za pl plp ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m ->
rw_cells segs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) (Z_to_bv 64 u) ahi j128) ->
rw_cells segs m (q + -392) [CB 24 digs] ->
rw_cells segs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells segs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
frm0 fc -> Fok Ft ->
(0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
(0 <= u < 2^32)%Z -> (t = 120 \/ t = 88)%Z ->
implM segs (cnt' <- conv_int OUT c fl w p xp u
(if negb (u =? 0) && negb (Z.land fl ALT_FORM =? 0) then (if t =? 120 then [48; 120] else [48; 88]) else [])%Z
(hex_digits (Z.land t 32) u) ;;
printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
(MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
x10 x11 x12 x13 x14 x15 (Z_to_bv 64 t) x17
(Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) x23 (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x748)) fc None m (seg_rom segs)).

Definition S_CV_S : Prop :=
forall fuel, S_HEAD fuel ->
forall (x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
(fl w p fl10 : Z) (xp : bool) (P : Z) (s : list Z) (slack : list byte)
(pfx s2s za pl plp ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m ->
rw_cells segs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) (Z_to_bv 64 P) ahi j128) ->
rw_cells segs m (q + -392) [CB 24 digs] ->
rw_cells segs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells segs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
frm0 fc -> Fok Ft ->
(0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
bytes_at segs m P (zb s ++ Z_to_bv 8 0 :: slack) -> Forall (fun c => 0 < c < 256)%Z s ->
((- (P + zlength s + 1)) mod 8 <= zlength slack)%Z -> (0 < P)%Z ->
(P + zlength s + 1 + zlength slack <= lo \/ q <= P)%Z ->
(P + zlength s + 1 + zlength slack <= Fp \/ Fp + 232 <= P)%Z ->
(P + zlength s + 1 + zlength slack <= B \/ B + BS <= P)%Z ->
(fl10 = Z.land fl (Z.lnot 65536))%Z ->
implM segs (cnt' <- (if (p <? 0) && (INT_MAX <=? zlength s) then munr
else conv_tail OUT c (Z.land fl (Z.lnot ZERO_PAD)) w (if p <? 0 then zlength s else Z.min (zlength s) p) []
(firstn (Z.to_nat (if p <? 0 then zlength s else Z.min (zlength s) p)) s))%Z ;;
printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
(MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) x23 (Z_to_bv 64 fl) (Z_to_bv 64 p) (Z_to_bv 64 fl10) x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x5e0)) fc None m (seg_rom segs)).

Definition S_CV_FP : Prop :=
forall fuel, S_HEAD fuel ->
forall (x1 x6 x7 x10 x11 x12 x13 x14 x15 x17 x23 x26 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (i4 k c : Z) (args : list parg)
(fl w p : Z) (xp : bool) (y t : Z)
(pfx s2s za pl plp : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m ->
rw_cells segs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) (Z_to_bv 64 (lo64 y)) (Z_to_bv 64 (hi64 y)) j128) ->
rw_cells segs m (q + -392) [CB 24 digs] ->
rw_cells segs m (q + -368) [CB 256 pad] ->
SINK m st -> rw_cells segs m AP [C8 (Z_to_bv 64 (VA + 8 * k))] -> (0 <= k)%Z ->
args_ok Fp B BS m0 lo q AP (skipn (Z.to_nat k) slots) args ->
fpcall_stmt Fp B BS SINK TOPOK OUTFP (y, w, p, fl, t) ->
Forall (fpcall_stmt Fp B BS SINK TOPOK OUTFP) (fp_calls fuel (sfx i4) args) ->
frm0 fc -> Fok Ft ->
(0 <= i4 <= zlength fmt)%Z -> (0 <= fl < 131072)%Z -> (0 <= w <= INT_MAX)%Z -> (0 <= c <= INT_MAX)%Z ->
((xp = false /\ p = -1) \/ (xp = true /\ 0 <= p <= INT_MAX))%Z ->
(0 <= y < 2^128)%Z -> conv_type t = Some T_DBL ->
implM segs (cnt' <- (if xp && (p <? 0) then munr
else if (1 <? w) || (2^20 <=? p) then munr
else r <- OUTFP y w p fl t ;; if (r <? 0) || (INT_MAX - c <? r) then munr else mret (c + r))%Z ;;
printf_loop OUT OUTFP fuel (sfx i4) args cnt') st POST
(MS (mkR x1 SPv gp tp (Z_to_bv 64 (Z.b2z xp)) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647)
x10 x11 x12 x13 x14 x15 (Z_to_bv 64 t) x17
(Z_to_bv 64 (2147483647 - c)) (Z_to_bv 64 c) FPv (Z_to_bv 64 (A + i4)) (Z_to_bv 64 w) x23 (Z_to_bv 64 fl) (Z_to_bv 64 p) x26 (Z_to_bv 64 0) x28 x29 x30 x31)
Ft (Z_to_bv 64 (base + 0x548)) fc None m (seg_rom segs)).

Definition POST1 : Z -> machine_state -> Prop :=
fun r ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0e s1e (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
F (ret_pc ra) fc0 None m' (seg_rom segs)
/\ munch [(lo, q)] m0 m' /\ wmono segs m0 m' /\ mem_inv segs m'
/\ stk segs m' lo q
/\ ssp_cells m' canary.

Definition S_EXIT1 : Prop :=
forall (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(m : word -> option byte) (r : Z)
(pfx s2s za pl plp l10n alo ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m -> munch [(lo, q)] m0 m ->
rw_cells segs m (q + -544) (lo_cells pfx s2s za pl plp l10n alo ahi j128) ->
rw_cells segs m (q + -392) [CB 24 digs] ->
rw_cells segs m (q + -368) [CB 256 pad] ->
(0 <= r < 2^64)%Z ->
evt segs (POST1 r)
(MS (mkR x1 SPv gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 r) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 (base + 0xddc)) fc0 None m (seg_rom segs)).

Definition S_P1 : Prop :=
forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x24 x25 x27 x28 x29 x30 x31 : word)
(m : word -> option byte) (pfx s2s za pl plp alo ahi : word) (j128 digs pad : list byte),
let _ := ctx_all in
finv m -> munch [(lo, q)] m0 m ->
rw_cells segs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
rw_cells segs m (q + -392) [CB 24 digs] ->
rw_cells segs m (q + -368) [CB 256 pad] ->
pass1_ok fmt = true ->
evt segs (POST1 0)
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) x10 x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 A) x22 x23 x24 x25 (Z_to_bv 64 0) x27 x28 x29 x30 x31)
F (Z_to_bv 64 (base + 0xb0)) fc0 None m (seg_rom segs)).

Definition S_PRO : Prop :=
forall (x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 : word) (f : Z) (Q : machine_state -> Prop),
let _ := ctx_all in
stk segs m0 lo q -> mem_inv segs m0 -> bytes_at segs m0 A (zb fmt) -> va_area m0 VA slots -> ssp_cells m0 canary ->
(0 <= f < 2^64)%Z ->
(forall (m : word -> option byte) (pfx s2s za pl plp alo ahi : word) (j128 digs pad : list byte) (a0 a1 a2 a3 : word),
finv m -> munch [(q + -544, q)]%Z m0 m ->
rw_cells segs m (q + -544) (lo_cells pfx s2s za pl plp (Z_to_bv 64 0) alo ahi j128) ->
rw_cells segs m (q + -392) [CB 24 digs] ->
rw_cells segs m (q + -368) [CB 256 pad] ->
evt segs Q
(MS (mkR ra SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) a0 a1 a2 a3 nlt x15 x16 x17
s2e (Z_to_bv 64 0) (Z_to_bv 64 f) (Z_to_bv 64 A) s6e s7e s8e s9e (Z_to_bv 64 0) s11e x28 x29 x30 x31)
F (Z_to_bv 64 (base + 0xb0)) fc0 None m (seg_rom segs))) ->
evt segs Q
(MS (mkR ra (Z_to_bv 64 q) gp tp x5 x6 x7 s0e s1e (Z_to_bv 64 f) (Z_to_bv 64 A) (Z_to_bv 64 AP) nla nlt x15 x16 x17
s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e x28 x29 x30 x31)
F (Z_to_bv 64 (base + 0x0)) fc0 None m0 (seg_rom segs)).

End PrintfCore.

End G.
End Mq0.

Module Mq1.

Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0.
Import QZAi.Mq1 Ql2m.Mq3 QZAi QqdR QYTG.Mq2.
Import QnDM_c1.
Import QVbl.Mq4.
Import QVbl.Mq3.
Import QQLG.Mq7.
Import Q91D.Mq2.
Import QQRC.Mq0.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_shp.F_fmt_fp.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.
Import Qbz7.
Import Q8l1.Mq1.

Import ListNotations.
Import QlEo_c1.Mq0.Exc. Unset Keyed Unification. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Open Scope mspec_scope.

Lemma zb_length : forall l, length (zb l) = length l.
Proof. intros. unfold zb. apply length_map. Qed.
Lemma zb_app : forall a b, zb (a ++ b) = zb a ++ zb b.
Proof. intros. unfold zb. apply map_app. Qed.

Lemma Forall_disjoint_from : forall (W : list (Z * Z)) A N a n,
Forall (fun iv => snd iv <= A \/ A + N <= fst iv) W -> A <= a -> a + n <= A + N -> 0 <= n -> disjoint_from W a n.
Proof.
intros W A N a n H Ha Hn Hn0. induction H as [|[lo hi] W' Hiv _ IH]; cbn; [exact I|]. cbn in Hiv. split; [lia | exact IH].
Qed.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment) (base : Z).
Variables (w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907 : Z).
Variables (got_ssp GLOBALS_TOP ssp_guard : Z).
Variables (e_fwritex e_memcpy : Z).
Hypothesis CODE : code_at segs base (printf_core_code w_22 w_25 w_81 w_281 w_282 w_332 w_333 w_360 w_362 w_371 w_372 w_378 w_379 w_381 w_383 w_389 w_395 w_396 w_412 w_413 w_426 w_427 w_438 w_439 w_453 w_454 w_467 w_468 w_473 w_474 w_530 w_533 w_534 w_543 w_545 w_627 w_639 w_648 w_655 w_668 w_680 w_689 w_701 w_713 w_722 w_729 w_742 w_754 w_762 w_798 w_883 w_907).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 3632.
Hypothesis RNG_got_ssp : gw_br got_ssp 8.
Hypothesis RNG_ssp_guard : gw_br ssp_guard 8.
Hypothesis RNG_GLOBALS_TOP : gw_br GLOBALS_TOP 8.
Hypothesis LAY_lo_GLOBALS_TOP : gw_le 65536 GLOBALS_TOP.
Hypothesis LAY_got_ssp_ssp_guard : gw_le (got_ssp + 8) ssp_guard.
Hypothesis LAY_ssp_guard_GLOBALS_TOP : gw_le (ssp_guard + 8) GLOBALS_TOP.

Local Definition gw_tbl_0 := tt.

Definition wfile : ltac:(gw_rebind_ty (@QQLG.Mq7.wfile segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QQLG.Mq7.wfile segs) constr:(gw_tbl_0)).
Local Definition gw_tbl_1 := (gw_ent (@Q8l1.Mq1.wfile segs) wfile (gw_ent (@Q91D.Mq2.wfile segs) wfile (gw_ent (@QQLG.Mq7.wfile segs) wfile gw_tbl_0))).
Definition fwritex_post : ltac:(gw_rebind_ty (@QQLG.Mq7.fwritex_post segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@QQLG.Mq7.fwritex_post segs) constr:(gw_tbl_1)).
Local Definition gw_tbl_2 := (gw_ent (@QQLG.Mq7.fwritex_post segs) fwritex_post gw_tbl_1).
Definition ssp_cells : ltac:(gw_rebind_ty (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_2)).
Local Definition gw_tbl_3 := (gw_ent (@Q8l1.Mq1.ssp_cells segs got_ssp ssp_guard) ssp_cells (gw_ent (@Q91D.Mq2.ssp_cells segs got_ssp ssp_guard) ssp_cells gw_tbl_2)).
Definition va_area : ltac:(gw_rebind_ty (@Q91D.Mq3.va_area segs) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q91D.Mq3.va_area segs) constr:(gw_tbl_3)).
Local Definition gw_tbl_4 := (gw_ent (@Q91D.Mq3.va_area segs) va_area (gw_ent (@Q8l1.Mq1.va_area segs) va_area gw_tbl_3)).
Definition sink_frame_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.sink_frame_stmt segs) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.sink_frame_stmt segs) constr:(gw_tbl_4)).
Local Definition gw_tbl_5 := (gw_ent (@Q8l1.Mq1.sink_frame_stmt segs) sink_frame_stmt gw_tbl_4).
#[global] Arguments sink_frame_stmt {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope.
Definition sink_flags_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.sink_flags_stmt segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.sink_flags_stmt segs) constr:(gw_tbl_5)).
Local Definition gw_tbl_6 := (gw_ent (@Q8l1.Mq1.sink_flags_stmt segs) sink_flags_stmt gw_tbl_5).
#[global] Arguments sink_flags_stmt {St}%_type_scope Fp%_Z_scope SINK%_function_scope.
Definition out_post : ltac:(gw_rebind_ty (@Q8l1.Mq1.out_post segs got_ssp ssp_guard) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.out_post segs got_ssp ssp_guard) constr:(gw_tbl_6)).
Local Definition gw_tbl_7 := (gw_ent (@Q8l1.Mq1.out_post segs got_ssp ssp_guard) out_post gw_tbl_6).
#[global] Arguments out_post {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope ra%_bv_scope sp%_bv_scope gp%_bv_scope tp%_bv_scope s0%_bv_scope s1%_bv_scope s2%_bv_scope s3%_bv_scope s4%_bv_scope s5%_bv_scope s6%_bv_scope s7%_bv_scope s8%_bv_scope s9%_bv_scope s10%_bv_scope s11%_bv_scope F fc%_bv_scope S%_Z_scope bs%_list_scope lo%_Z_scope canary%_bv_scope m%_function_scope _ _ _.
Definition out_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) constr:(gw_tbl_7)).
Local Definition gw_tbl_8 := (gw_ent (@Q8l1.Mq1.out_stmt segs got_ssp GLOBALS_TOP ssp_guard e_fwritex) out_stmt gw_tbl_7).
#[global] Arguments out_stmt {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUT%_function_scope.
Definition fpcall_post : ltac:(gw_rebind_ty (@Q8l1.Mq1.fpcall_post segs got_ssp ssp_guard) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.fpcall_post segs got_ssp ssp_guard) constr:(gw_tbl_8)).
Local Definition gw_tbl_9 := (gw_ent (@Q8l1.Mq1.fpcall_post segs got_ssp ssp_guard) fpcall_post gw_tbl_8).
#[global] Arguments fpcall_post {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope ra%_bv_scope sp%_bv_scope gp%_bv_scope tp%_bv_scope s0%_bv_scope s1%_bv_scope s2%_bv_scope s3%_bv_scope s4%_bv_scope s5%_bv_scope s6%_bv_scope s7%_bv_scope s8%_bv_scope s9%_bv_scope s10%_bv_scope s11%_bv_scope F lo%_Z_scope canary%_bv_scope m%_function_scope _%_Z_scope _ _.
Definition fpcall_stmt : ltac:(gw_rebind_ty (@Q8l1.Mq1.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) constr:(gw_tbl_9)).
Local Definition gw_tbl_10 := (gw_ent (@Q8l1.Mq1.fpcall_stmt segs base got_ssp GLOBALS_TOP ssp_guard) fpcall_stmt gw_tbl_9).
#[global] Arguments fpcall_stmt {St}%_type_scope Fp%_Z_scope B%_Z_scope BS%_Z_scope SINK%_function_scope TOPOK%_function_scope OUTFP%_function_scope c.
Definition SINK_sn : ltac:(gw_rebind_ty (@Q8l1.Mq1.SINK_sn segs) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8l1.Mq1.SINK_sn segs) constr:(gw_tbl_10)).
Local Definition gw_tbl_11 := (gw_ent (@Q8l1.Mq1.SINK_sn segs) SINK_sn gw_tbl_10).

Hypothesis fwritex_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QQLG.Mq7.gw_all) (@QQLG.Mq7.fwritex_spec) e_fwritex)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_11))) in exact T).

#[using="got_ssp GLOBALS_TOP ssp_guard e_fwritex e_memcpy CODE BASE4 BASER RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP fwritex_spec"] Lemma gw_all : True. Proof. exact I. Qed.

#[using="Type"] Lemma bytes_at_func : forall m a (bs1 bs2 : list byte), bytes_at segs m a bs1 -> bytes_at segs m a bs2 -> length bs1 = length bs2 -> bs1 = bs2.
Proof. clear - segs.
intros m a bs1 bs2 (_ & _ & H1) (_ & _ & H2) L.
apply nth_error_ext. intros i. destruct (Nat.lt_ge_cases i (length bs1)) as [Hi|Hi].
- rewrite <- H1 by exact Hi. rewrite <- H2 by lia. reflexivity.
- rewrite (proj2 (nth_error_None bs1 i)) by lia. rewrite (proj2 (nth_error_None bs2 i)) by lia. reflexivity.
Qed.
#[using="Type"] Lemma C8_func : forall m a (v w : word), rw_cells segs m a [C8 v] -> rw_cells segs m a [C8 w] -> v = w.
Proof. clear - segs.
intros m a v w [[_ H1] _] [[_ H2] _]. cbn [cells_bytes cbytes] in H1, H2. rewrite app_nil_r in H1, H2.
pose proof (bytes_at_func _ _ _ _ H1 H2 ltac:(rewrite !length_le8; reflexivity)) as E.
rewrite <- (le_bytes_to_word_le8 v), <- (le_bytes_to_word_le8 w), E. reflexivity.
Qed.

Section SnProofs.
Variables (Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (frest : list cell) (B TOP : Z).
Let SINK := SINK_sn Fp fl0 j1 j2 lbfw frest B TOP.

#[using="Type"] Lemma sn_sink_frame : sink_frame_stmt Fp B 80 SINK.
Proof. clear - Fp fl0 j1 j2 lbfw frest B TOP SINK.
unfold sink_frame_stmt. intros W m m' o (junk & WF & FR & FRL & LEN & SEPB & T1 & T2) MU WM D1 D2.
exists junk. split; [|split; [|split; [exact FRL | split; [exact LEN | split; [exact SEPB | split; assumption]]]]].
- destruct WF as (FC & BUF & FL & LBF & Bpos & Bhi & SEPfb).
pose proof (zb_length o) as LZ. unfold zlength, SN_CAP in LEN.
split; [|split; [|repeat split; assumption]].
+ eapply rw_cells_transport; [exact FC | exact MU | exact WM |].
eapply Forall_disjoint_from; [exact D1 | lia | cbn [cells_size FILE_cells csize Nat.add]; lia | cbn [cells_size FILE_cells csize Nat.add]; lia].
+ eapply rw_cells_transport; [exact BUF | exact MU | exact WM |].
eapply Forall_disjoint_from; [exact D2 | lia | cbn [cells_size csize Nat.add]; rewrite LZ; lia | cbn [cells_size csize Nat.add]; lia].
- eapply rw_cells_transport; [exact FR | exact MU | exact WM |].
eapply Forall_disjoint_from; [exact D1 | lia | lia | lia].
Qed.

#[using="Type"] Lemma sn_sink_flags : sink_flags_stmt Fp SINK.
Proof. clear - Fp fl0 j1 j2 lbfw frest B TOP SINK.
unfold sink_flags_stmt. intros m o (junk & (FC & BUF & FL & _) & _).
exists fl0. split; [|exact FL].
apply (proj1 (rw_cells_app segs m Fp [CB 1 [fl0]] _)) in FC. exact (proj1 FC).
Qed.

#[using="Type"] Lemma sn_topok : topok_stmt (TOPOK_sn TOP).
Proof. clear - Fp fl0 j1 j2 lbfw frest B TOP SINK. unfold topok_stmt, TOPOK_sn. intros. lia. Qed.

#[using="RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP fwritex_spec"] Lemma sn_out : out_stmt Fp B 80 SINK (TOPOK_sn TOP) OUT_sn.
Proof. clear - RNG_got_ssp RNG_ssp_guard RNG_GLOBALS_TOP LAY_lo_GLOBALS_TOP LAY_got_ssp_ssp_guard LAY_ssp_guard_GLOBALS_TOP fwritex_spec Fp fl0 j1 j2 lbfw frest B TOP SINK.
unfold out_stmt. intros until canary. intros HS SRC RNG LB Ha1 Ha2 ST LO GLO SPHI TQ SSP MI D1 D2 D3 D4 D5. rename st into o.
destruct HS as (junk & WF & FR & FRL & LEN & SEPB & T1 & T2). unfold TOPOK_sn in TQ. gw_expose GLOBALS_TOP; unfold OUT_DEPTH, SN_CAP in *.
pose proof WF as WF'. destruct WF' as (FC & BUF & FL & LBF & Bpos & Bhi & SEPfb).
pose proof (zb_length o) as LZo. pose proof (zb_length bs) as LZb. rewrite LZo in *. unfold zlength in *.
pose proof (rw_cells_bound _ _ _ _ FC) as FB. cbn [cells_size FILE_cells csize Nat.add] in FB.
pose proof (bytes_at_bound _ _ _ _ SRC) as SB. rewrite LZb in SB.
assert (EFp : bv_unsigned a2 = Fp) by (subst a2; apply unsigned_lit; lia).
unfold OUT_sn. apply implM_get_l. unfold zlength, SN_CAP.
destruct (Z.leb_spec0 (Z.of_nat (length o) + Z.of_nat (length bs)) 80) as [FIT|NOFIT]; [|apply implM_unr].
apply implM_put.
destruct (stk_split _ _ _ (bv_unsigned sp - 64) _ ST ltac:(lia)) as [ST1 ST2].
eapply evt_mono.
{ eapply (fwritex_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m fl0 j1 j2 lbfw B (zb o) junk (zb bs));
rewrite ?EFp, ?LZo, ?LZb.
- exact WF. - exact SRC. - subst a1. rewrite unsigned_lit by lia. reflexivity. - lia. - exact ST2. - exact MI.
- lia. - lia. - lia. - lia. - lia. - lia. }
cbv beta. intros ms' P. unfold fwritex_post in P. rewrite ?EFp, ?LZo, ?LZb in P.
destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & m' & -> & MU & WM & MI' & ST' & WF2 & SRC').
unfold out_post, SR. eexists x5, x6, x7, _, b1, b2, b3, b4, b5, b6, b7, x28, x29, x30, x31, m'.
split; [reflexivity|].
split. { eapply munch_weaken; [|exact MU]. unfold sub_fp; try unfold SR; cbn [outside]; intros; lia. }
split; [exact WM|]. split; [exact MI'|].
split. { eapply stk_merge; [ eapply stk_transport_disjoint; [exact ST1 | exact MU | exact WM | cbn [disjoint_from]; lia] | exact ST' | lia ]. }
split. { exists (skipn (length bs) junk). split; [rewrite zb_app; exact WF2|].
split. { eapply rw_cells_transport; [exact FR | exact MU | exact WM | cbn [disjoint_from]; lia]. }
split; [exact FRL|]. unfold zlength, SN_CAP. rewrite length_app, length_skipn. split; [lia|]. split; [lia|]. split; assumption. }
split. { destruct SSP as [S1 S2]. gw_expose got_ssp; gw_expose ssp_guard; unfold ssp_cells in *. split.
- eapply rw_cells_transport; [exact S1 | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; lia].
- eapply rw_cells_transport; [exact S2 | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
exact SRC'.
Qed.

#[using="Type"] Lemma sn_fpcall : forall y w p fl t, fmt_fp_facts y fl p t ->
fpcall_stmt Fp B 80 SINK (TOPOK_sn TOP) OUTFP_sn (y, w, p, fl, t).
Proof. clear - Fp fl0 j1 j2 lbfw frest B TOP SINK. intros y w p fl t H. destruct H. Qed.
End SnProofs.

End G.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfYR QfcC QDUx Q9Ay Qy5Y Qy8Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg.
Import QZAi.Mq1 QZAi QfYR QfcC.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QnDM_c1 QDUx Q9Ay Qy5Y.
Import QVbl.Mq3.
Import QQLG.Mq8.
Import Qy8Z.Mq0.
Export Q8l1.Mq3.

Import ListNotations. Unset Keyed Unification.
Open Scope Z_scope.
Open Scope bv_scope.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Open Scope Z_scope.
Open Scope bv_scope.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_71 w_72 w_98 : Z).
Variables (got_ssp STRING_READ ssp_guard : Z).
Hypothesis CODE : code_at segs base (shgetc_code w_71 w_72 w_98).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 544.

Local Definition gw_tbl_0 := tt.

Definition ss_cells : ltac:(gw_rebind_ty (@QQRC.Mq3.ss_cells STRING_READ) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QQRC.Mq3.ss_cells STRING_READ) constr:(gw_tbl_0)).
Local Definition gw_tbl_1 := (gw_ent (@Q8l1.Mq3.ss_cells STRING_READ) ss_cells (gw_ent (@QQRC.Mq3.ss_cells STRING_READ) ss_cells gw_tbl_0)).
Definition SHGETC := (base + 56)%Z.
Local Definition gw_tbl_2 := (gw_ent (@QQRC.Mq3.SHGETC base) SHGETC gw_tbl_1).
Definition UFLOW := (base + 256)%Z.
Local Definition gw_tbl_3 := (gw_ent (@QQRC.Mq3.UFLOW base) UFLOW gw_tbl_2).
Definition ssp_cells : ltac:(gw_rebind_ty (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) constr:(gw_tbl_3)).
Local Definition gw_tbl_4 := (gw_ent (@QQRC.Mq3.ssp_cells segs got_ssp ssp_guard) ssp_cells gw_tbl_3).
Definition ssJ : ltac:(gw_rebind_ty (@QQRC.Mq3.ssJ STRING_READ) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@QQRC.Mq3.ssJ STRING_READ) constr:(gw_tbl_4)).
Local Definition gw_tbl_5 := (gw_ent (@QQRC.Mq3.ssJ STRING_READ) ssJ gw_tbl_4).

#[using="got_ssp STRING_READ ssp_guard CODE BASE4 BASER"] Lemma gw_all : True. Proof. exact I. Qed.

Definition uflow_res (txt : list Z) (off p : Z) : Z := if (off <? p)%Z then znth txt off else -1.

Definition uflow_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Fp T p off : Z) (txt : list Z) (shend : Z) (shl shc canary : word) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (uflow_res txt off p)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(q - 128, q); (Fp, Fp + 232)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' (q - 128) (q)
/\ rw_cells segs m' Fp (ss_cells T (T + off + sread_len off p) (T + p) (Z_to_bv 64 M64) (T + p) shend shl shc)
/\ bytes_at segs m' T (zbytes txt)
/\ ssp_cells m' canary.

Definition uflow_stmt : Prop :=
forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T p off rpos rend shend : Z) (txt pre post : list Z) (mode shl shc canary : word),
rw_cells segs m Fp (ss_cells T rpos rend mode (T + off) shend shl shc) ->
(mode = Z_to_bv 64 0 \/ mode = Z_to_bv 64 M64) ->
rtext T txt pre post -> p = zlength pre -> (0 <= off <= p)%Z ->
bytes_at segs m T (zbytes txt) -> ssp_cells m canary ->
(4096 <= T)%Z -> (T + 2^41 <= 2^63)%Z -> (0 <= rpos < 2^64)%Z -> (0 <= rend < 2^64)%Z -> (0 <= shend < 2^64)%Z ->
(Fp + 232 <= T \/ T + zlength txt <= Fp)%Z ->
stk segs m (q - 128) (q) -> (4096 <= q - 128)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
(T + zlength txt <= q - 128 \/ q <= T)%Z ->
(ssp_guard + 8 <= q - 128)%Z ->
(T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z -> (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z ->
(0 <= q)%Z -> (q < 2^63)%Z ->
mem_inv segs m ->
evt segs (uflow_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T p off txt shend shl shc canary m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 UFLOW) fc None m (seg_rom segs)).

Definition shgetc_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Fp T p : Z) (f : shfile) (txt : list Z) (canary : word) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fst (sh_getc f))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(q - 160, q); (Fp, Fp + 232)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' (q - 160) q
/\ rw_cells segs m' Fp (rf_cells T p true (snd (sh_getc f)) ssJ)
/\ bytes_at segs m' T (zbytes txt)
/\ ssp_cells m' canary.

Definition shgetc_stmt : Prop :=
forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T p : Z) (w : bool) (f : shfile) (txt pre post : list Z) (canary : word),
rw_cells segs m Fp (rf_cells T p w f ssJ) ->
sh_stdio f = true -> sh_n f = p -> sh_buf f = txt ->
sh_rpos f = (if w then p else 0%Z) -> (w = false -> sh_cnt0 f = 0%Z /\ sh_shlim_neg f = false) -> (0 <= sh_cnt0 f <= sh_rpos f)%Z ->
rtext T txt pre post -> p = zlength pre -> bytes_at segs m T (zbytes txt) -> ssp_cells m canary ->
(4096 <= T)%Z -> (T + 2^41 <= 2^63)%Z -> (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z ->
stk segs m (q - 160) q -> (4096 <= q - 160)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
(T + zlength txt <= q - 160 \/ q <= T)%Z ->
(ssp_guard + 8 <= q - 160)%Z ->
(T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z -> (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z ->
(0 <= q)%Z -> (q < 2^63)%Z ->
mem_inv segs m ->
evt segs (shgetc_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T p f txt canary m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 SHGETC) fc None m (seg_rom segs)).

End G.
End Mq2.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Q2qa Q4J3 QytA Qnxq QJE4 QWTl QPjm QUZl Q7S0 QGeV QLsg QkQT QlkP QM7w Q8QT QCa8 QDXD QkTt Q6q3 G.GwFamMalloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.

Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 QDUx.Mqb Qy5Y.Mq6 QPjm.Mq3 Q4J3.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg Qy5Y.Mq7 QkQT QlkP QWTl.Mq0 QM7w QDUx.Mq0 Q9Ay.Mq3 Q9Ay.Mq4 Q9Ay.Mq5 Q9Ay.Mq6 Q9Ay.Mq7 Q9Ay.Mq8 QJE4.Mq3.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QCa8.Mq4.
Import QDXD.Mq2.
Import QkTt.Mq3.
Import QkTt.Mq4.
Import Q8QT.Mq2.
Import QDXD.Mq1.
Import Qy8Z.Mqa.
Import QkTt.Mq5.
Import QCa8.Mq3.
Import Qy8Z.Mq8.
Import Q8l1.Mq8.
Import Qy8Z.Mq9.
Import QQRC.Mq9.
Import Qy8Z.Mq1.
Import QQRC.Mq4.
Import QQRC.Mqc.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.
Open Scope Z_scope.

Definition alloc_slot_code (w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 : Z) : list Z :=
[0xf7010113; 0x08113423; 0x08813023; 0x06913c23; 0x07213823; 0x07313423; 0x07413023; 0x05513c23; 0x05613823; 0x05713423; 0x05813023; 0x03913c23; 0x00058913; 0x00050413; w_14; w_15; 0x000a3503; 0x00341b93; w_18; w_19; 0x02a13823; 0x017b0bb3; 0x058bb603; 0x058b8a93; 0x18060063; 0x01862583; 0x00058663; 0x00060513; 0x1300006f; 0x01c62583; 0x00863503; 0x00058663; 0x00aab023; 0x0440006f; 0x02c50463; 0x00063583; 0x00a5b423; 0x00063503; 0x00863583; 0x00a5b023; 0x000ab503; 0x00c51a63; 0x00863503; 0x0080006f; 0x00000513; 0x00aab023; 0x00063023; 0x00063423; 0x000ab503; 0x10050e63; 0x01c52683; 0x02053583; 0x0205f613; 0x00200713; 0x00060e63; 0x00b715bb; 0xfff5859b; 0x00b69863; 0x00853503; 0x00aab023; 0x01c52683; 0x01053583; 0x0085c603; 0x00c7173b; 0xfff7071b; 0x00d776b3; 0x00069a63; 0x00853683; 0x3ca68263; 0x00dab023; 0x00068513; 0x01852583; 0x00058463; 0x00000023; 0x01053583; 0x0085c583; 0x00200613; 0x00b615bb; 0x01c50613; 0x40b006bb; 0x00062703; 0x00d777b3; 0x1606282f; 0x00e81663; 0x1ef628af; 0xfe089ae3; 0x0008081b; 0xfee812e3; 0xfff5859b; 0x00b775b3; 0x00b52c23; 0x00059463; 0x00000023; 0x02052603; 0x03461613; 0x03a65613; 0xff960613; 0x01f00693; 0x00c6ec63; 0x00cb0633; 0x37864683; 0x00068663; 0xfff68693; 0x36d60c23; 0x40b0063b; 0x00c5f633; 0x40c586bb; 0x00d52c23; 0x02060863; 0x40b0053b; 0x00a5f533; 0x077cb5b7; 0x53158593; 0x02b50533; w_114; 0x01b5551b; w_116; 0x00a58533; 0x00054503; 0x6840006f; 0x00141993; w_121; w_122; 0x013c8533; 0x00055c03; 0xfc4ff0ef; 0x00050493; 0xfff00513; 0x66048063; 0x1d8bb503; w_130; w_131; 0x00800613; 0x004c1c13; 0x02864a63; 0x00898633; w_136; w_137; 0x00c68633; 0x00064983; 0x00299693; 0x06d57863; 0x00164983; 0x00299693; 0x06d57263; 0x00264983; 0x05c0006f; 0x00347613; w_148; w_149; 0x00c68633; 0x00064683; 0x0016f613; 0x02061063; 0x0026961b; 0x02c57063; 0x0016d61b; 0x0026f713; 0x00060693; 0xfe0706e3; 0x0100006f; 0x00068613; 0x0080006f; 0x00068613; 0x00060993; 0x02cc0633; 0x01465693; 0x0019d61b; 0xfe0698e3; 0x010c0613; 0x00100713; 0x0015d693; 0x00e99863; 0x00c6b733; 0x00200793; 0x40e789bb; 0x033c0733; 0x01070793; 0x04f6f463; 0xff94079b; 0x01f00693; 0x0cf6ec63; 0x00fb07b3; 0x3787c883; 0x3587c283; 0x0648b693; 0x0016c693; 0x28028863; 0x398b4803; 0x405802b3; 0x00900313; 0x28534263; 0x06300813; 0x2708e863; 0x09600893; 0x26c0006f; 0x00c70593; 0x09d00513; 0x00475713; 0x0aa5ec63; 0x00170513; 0x077cb637; 0x0025569b; 0x00a6e6b3; 0x0015551b; 0x00a6e6b3; 0x0026d69b; 0x00a6e533; 0x00455693; 0x00a6e533; 0x00855693; 0x00a6e533; 0x02151693; 0x0316d693; 0x00a6e533; 0x00150693; 0xfff54513; 0x00a6f533; w_218; 0x53160613; w_220; 0x02c50533; 0x01b5551b; 0x00a68533; 0x00054503; 0x00251513; 0x07c54513; 0x07900613; 0x40a60633; 0x00161613; 0x00cc8633; 0x00065603; 0x00c76a63; 0x07a00613; 0x0100006f; 0x00000693; 0x1cc0006f; 0x07800613; 0x40a60633; 0x00161513; 0x00ac8533; 0x00055503; 0x00a73533; 0x00154713; 0x00e66733; 0x0007091b; 0x00090513; 0xc25ff0ef; 0x06054c63; 0x00050593; 0x00391513; 0x00191913; 0x00ab0533; 0x012c8933; 0x00095603; 0x05853503; 0x014b2683; 0x00461613; 0xffc60613; 0x498000ef; 0x0204b583; 0x03459593; 0x0345d593; 0x02b4b023; 0xffd54603; 0x0019859b; 0x01f67613; 0x0c060613; 0xfec50ea3; 0x00c50613; 0x00060023; 0xfff58593; 0x01860633; 0xfe059ae3; 0xfff98593; 0x00098c93; 0x00058613; 0x2b40006f; 0x02013423; 0x00013423; 0x00013823; 0x00013c23; 0x02013023; 0x01013503; 0x00a4b423; 0x02813503; 0x02a4b023; 0x02013503; 0x00a4bc23; 0x01813503; 0x00a4b823; 0x00813503; 0x00a4b023; 0x0084b503; 0x00050463; 0x00000023; 0x0004b583; 0xfff00513; 0x00058463; 0x00000023; 0x018b3583; 0x0a058663; 0x00b4b423; 0x0005b583; 0x00b4b023; 0x0095b423; 0x0084bb03; 0x009b3023; 0x3900006f; 0x01f67793; 0x02053683; w_311; 0x00278813; w_313; 0x0056d893; 0x07e8f893; 0x01170733; 0x00075883; 0x00178713; 0x00479793; 0x03078293; 0x00489793; 0x031288b3; 0x030782b3; 0x00f8881b; 0x0102829b; 0x000018b7; 0x00584333; 0x00f282bb; 0x0017071b; 0x00f8083b; 0xff1348e3; 0x01f6f693; 0x00168693; 0x00d76463; 0x00068713; 0xfff70713; 0x01f77713; 0x0e067613; 0x00c76633; 0x00c58423; 0x01852583; 0xbc0596e3; 0xbcdff06f; 0x0094b023; 0x0094b423; 0x018b0b13; 0x009b3023; 0x2f00006f; 0x00188893; 0x37178c23; 0x398b4803; 0x0ff00793; 0x00f81e63; 0x340b3c23; 0x360b3023; 0x360b3423; 0x360b3823; 0x00100813; 0x0080006f; 0x00180813; 0x01f00793; 0x390b0c23; 0x0087ca63; 0x00147793; 0x00079663; 0x1e0bb783; 0x00a78533; 0x0029979b; 0x06f57663; 0x06069463; 0x00347793; 0x00100893; 0x00359813; 0x01179863; 0x00e87663; 0x00200c93; 0x0500006f; 0x00200893; 0x01179a63; 0x00259893; 0x00e8f663; 0x00300c93; 0x0380006f; 0x00e838b3; 0x0017b293; 0x0112f8b3; 0x00089663; 0x00098c93; 0x0080006f; 0x00300c93; 0x00079c63; 0x00e86a63; 0x00159793; 0x00e7f463; 0x00500993; 0x00098c93; 0x039c07b3; 0xff000713; 0x40f70833; 0xfff58713; 0x00e87833; 0x010787b3; 0x01078993; 0x04069063; 0x00700693; 0x0396ec63; 0xfec00693; 0x412686b3; 0x00d776b3; 0x00d906b3; 0x01468693; 0x00c6f863; 0x00100c93; 0x00068993; 0x0140006f; 0x00259593; 0x00b6e663; 0x001c959b; 0xfeb564e3; 0x00300613; 0x02200693; 0xfff00713; 0xfff00913; 0x00000513; 0x00098593; 0x00000793; w_427; 0x13250463; 0xfffff5b7; 0x0204b603; 0x00b9f6b3; 0x000015b7; 0xff05859b; 0x0385d5b3; 0x014b2703; 0x03461613; 0x03465613; 0x00d66633; 0x00170713; 0x02c4b023; 0x00eb2a23; 0x000c8613; 0x00bce463; 0x00058613; 0xfff60593; 0x00b63633; 0xfff60613; 0x00b67633; 0xfffc8593; 0x1d8bb683; 0x019686b3; 0x00200713; 0x1cdbbc23; 0x00c716bb; 0xfff68693; 0x00d4ac23; 0x0184a683; 0x00b7173b; 0xfff6c693; 0x00d706b3; 0x00d4ae23; 0x00a4b823; 0x00953023; 0x0104b503; 0x00854683; 0x01f67613; 0x01f5f593; 0x0e06f693; 0x00c6e633; 0x00c50423; 0x0204b503; 0xfffff637; 0x03a41413; 0x03445413; 0x00c57533; 0x00b465b3; 0x00a5e533; 0x02050513; 0x02a4b023; 0x0184a503; 0xfff50513; 0x00a4ac23; 0x0084b503; 0x00050463; 0x00000023; 0x0004b503; 0x00050463; 0x00000023; 0x000ab503; 0x00050e63; 0x00a4b423; 0x00053503; 0x00a4b023; 0x00953423; 0x0084ba83; 0x00c0006f; 0x0094b023; 0x0094b423; 0x00000513; 0x009ab023; 0x08c0006f; 0x02013423; 0x00013423; 0x00013823; 0x00013c23; 0x02013023; 0x01013503; 0x00a4b423; 0x02813503; 0x02a4b023; 0x02013503; 0x00a4bc23; 0x01813503; 0x00a4b823; 0x00813503; 0x00a4b023; 0x0084b503; 0x00050463; 0x00000023; 0x0004b503; 0x00050463; 0x00000023; 0x018b3503; 0x00050e63; 0x00a4b423; 0x00053503; 0x00a4b023; 0x00953423; 0x0084bb03; 0x0100006f; 0x0094b023; 0x0094b423; 0x018b0b13; 0x009b3023; 0xfff00513; 0x000a3583; 0x03013603; 0x02c59c63; 0x08813083; 0x08013403; 0x07813483; 0x07013903; 0x06813983; 0x06013a03; 0x05813a83; 0x05013b03; 0x04813b83; 0x04013c03; 0x03813c83; 0x09010113; 0x00008067; w_552]%Z.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment) (base : Z).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (rvm_wait_entry : Z).
Variables (w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 : Z).
Variables (hi_14 hi_18 hi_114 hi_121 hi_130 hi_136 hi_148 hi_218 hi_311 : bv 20).
Variables (lo_15 lo_19 lo_116 lo_122 lo_131 lo_137 lo_149 lo_220 lo_313 : bv 12).
Variables (joff_427 joff_552 : bv 21).
Variables (e_197bc : Z).
Hypothesis CODE : code_at segs base (alloc_slot_code w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 2212.
Hypothesis D_14 : decode_any (Z_to_bv 32 w_14) = Some (Auipc 10 hi_14, 4%Z).
Hypothesis E_14 : is_ecall (Z_to_bv 32 w_14) = false.
Hypothesis D_15 : decode_any (Z_to_bv 32 w_15) = Some (Load SZ8 true 20 10 lo_15, 4%Z).
Hypothesis E_15 : is_ecall (Z_to_bv 32 w_15) = false.
Hypothesis D_18 : decode_any (Z_to_bv 32 w_18) = Some (Auipc 11 hi_18, 4%Z).
Hypothesis E_18 : is_ecall (Z_to_bv 32 w_18) = false.
Hypothesis D_19 : decode_any (Z_to_bv 32 w_19) = Some (OpImm ALU_ADD 22 11 lo_19, 4%Z).
Hypothesis E_19 : is_ecall (Z_to_bv 32 w_19) = false.
Hypothesis D_114 : decode_any (Z_to_bv 32 w_114) = Some (Auipc 11 hi_114, 4%Z).
Hypothesis E_114 : is_ecall (Z_to_bv 32 w_114) = false.
Hypothesis D_116 : decode_any (Z_to_bv 32 w_116) = Some (OpImm ALU_ADD 11 11 lo_116, 4%Z).
Hypothesis E_116 : is_ecall (Z_to_bv 32 w_116) = false.
Hypothesis D_121 : decode_any (Z_to_bv 32 w_121) = Some (Auipc 10 hi_121, 4%Z).
Hypothesis E_121 : is_ecall (Z_to_bv 32 w_121) = false.
Hypothesis D_122 : decode_any (Z_to_bv 32 w_122) = Some (OpImm ALU_ADD 25 10 lo_122, 4%Z).
Hypothesis E_122 : is_ecall (Z_to_bv 32 w_122) = false.
Hypothesis D_130 : decode_any (Z_to_bv 32 w_130) = Some (Auipc 11 hi_130, 4%Z).
Hypothesis E_130 : is_ecall (Z_to_bv 32 w_130) = false.
Hypothesis D_131 : decode_any (Z_to_bv 32 w_131) = Some (Load SZ8 true 11 11 lo_131, 4%Z).
Hypothesis E_131 : is_ecall (Z_to_bv 32 w_131) = false.
Hypothesis D_136 : decode_any (Z_to_bv 32 w_136) = Some (Auipc 13 hi_136, 4%Z).
Hypothesis E_136 : is_ecall (Z_to_bv 32 w_136) = false.
Hypothesis D_137 : decode_any (Z_to_bv 32 w_137) = Some (OpImm ALU_ADD 13 13 lo_137, 4%Z).
Hypothesis E_137 : is_ecall (Z_to_bv 32 w_137) = false.
Hypothesis D_148 : decode_any (Z_to_bv 32 w_148) = Some (Auipc 13 hi_148, 4%Z).
Hypothesis E_148 : is_ecall (Z_to_bv 32 w_148) = false.
Hypothesis D_149 : decode_any (Z_to_bv 32 w_149) = Some (OpImm ALU_ADD 13 13 lo_149, 4%Z).
Hypothesis E_149 : is_ecall (Z_to_bv 32 w_149) = false.
Hypothesis D_218 : decode_any (Z_to_bv 32 w_218) = Some (Auipc 13 hi_218, 4%Z).
Hypothesis E_218 : is_ecall (Z_to_bv 32 w_218) = false.
Hypothesis D_220 : decode_any (Z_to_bv 32 w_220) = Some (OpImm ALU_ADD 13 13 lo_220, 4%Z).
Hypothesis E_220 : is_ecall (Z_to_bv 32 w_220) = false.
Hypothesis D_311 : decode_any (Z_to_bv 32 w_311) = Some (Auipc 14 hi_311, 4%Z).
Hypothesis E_311 : is_ecall (Z_to_bv 32 w_311) = false.
Hypothesis D_313 : decode_any (Z_to_bv 32 w_313) = Some (OpImm ALU_ADD 14 14 lo_313, 4%Z).
Hypothesis E_313 : is_ecall (Z_to_bv 32 w_313) = false.
Hypothesis D_427 : decode_any (Z_to_bv 32 w_427) = Some (Jal 1 joff_427, 4%Z).
Hypothesis E_427 : is_ecall (Z_to_bv 32 w_427) = false.
Hypothesis D_552 : decode_any (Z_to_bv 32 w_552) = Some (Jal 1 joff_552, 4%Z).
Hypothesis E_552 : is_ecall (Z_to_bv 32 w_552) = false.
Hypothesis ANCH_15 : gw_anch (Z.shiftl (bv_signed hi_14) 12 + (base + 56) + bv_signed lo_15)%Z RGOT_SSP.
Hypothesis ANCH_19 : gw_anch (Z.shiftl (bv_signed hi_18) 12 + (base + 72) + bv_signed lo_19)%Z (RATP + 131960).
Hypothesis ANCH_116 : gw_anch (Z.shiftl (bv_signed hi_114) 12 + (base + 456) + bv_signed lo_116)%Z RDEBRUIJN.
Hypothesis ANCH_122 : gw_anch (Z.shiftl (bv_signed hi_121) 12 + (base + 484) + bv_signed lo_122)%Z (RDEBRUIJN + 32).
Hypothesis ANCH_131 : gw_anch (Z.shiftl (bv_signed hi_130) 12 + (base + 520) + bv_signed lo_131)%Z (RATP + 131776).
Hypothesis ANCH_137 : gw_anch (Z.shiftl (bv_signed hi_136) 12 + (base + 544) + bv_signed lo_137)%Z (RDEBRUIJN + 128).
Hypothesis ANCH_149 : gw_anch (Z.shiftl (bv_signed hi_148) 12 + (base + 592) + bv_signed lo_149)%Z (RDEBRUIJN + 155).
Hypothesis ANCH_220 : gw_anch (Z.shiftl (bv_signed hi_218) 12 + (base + 872) + bv_signed lo_220)%Z RDEBRUIJN.
Hypothesis ANCH_313 : gw_anch (Z.shiftl (bv_signed hi_311) 12 + (base + 1244) + bv_signed lo_313)%Z (RDEBRUIJN + 32).
Hypothesis LINK_427 : gw_anch (base + 1708 + bv_signed joff_427)%Z (rvm_wait_entry + 4)%Z.
Hypothesis LINK_552 : gw_anch (base + 2208 + bv_signed joff_552)%Z (e_197bc + 0)%Z.
Hypothesis RNG_RATP : gw_br RATP 1896.
Hypothesis LAY_lo_RATP : gw_le (gw_RDATA2_LO + 164) RATP.
Hypothesis LAY_hi_RATP : gw_le ((RATP + 132896)) RIMG_HI.
Hypothesis AL_RATP : gw_al RATP 8.
Hypothesis RNG_RDEBRUIJN : gw_br RDEBRUIJN 159.
Hypothesis LAY_lo_RDEBRUIJN : gw_le (0x10000 + 0) RDEBRUIJN.
Hypothesis LAY_hi_RDEBRUIJN : gw_le ((RDEBRUIJN + 159)) gw_RTEXT_LO.
Hypothesis AL_RDEBRUIJN : gw_al RDEBRUIJN 8.
Hypothesis RNG_RGOT_SSP : gw_br RGOT_SSP 8.
Hypothesis LAY_lo_RGOT_SSP : gw_le (RDATA_LO + 0) RGOT_SSP.
Hypothesis LAY_hi_RGOT_SSP : gw_le ((RGOT_SSP + 8)) gw_RDATA2_LO.
Hypothesis AL_RGOT_SSP : gw_al RGOT_SSP 8.
Hypothesis LAY_win_0 : gw_win (0x10000 + 1) gw_RTEXT_LO.
Hypothesis LAY_win_1 : gw_win (gw_RTEXT_LO + 1) RDATA_LO.
Hypothesis LAY_win_2 : gw_win (RDATA_LO + 1) gw_RDATA2_LO.
Hypothesis LAY_win_3 : gw_win (gw_RDATA2_LO + 1) RIMG_HI.
Hypothesis LAY_win_4 : gw_win RIMG_HI 0x1000000.
Hypothesis AL_win_RIMG_HI : gw_winal RIMG_HI 4096.
Hypothesis AL_win_RDATA_LO : gw_winal RDATA_LO 4096.
Hypothesis AL_win_gw_RTEXT_LO : gw_winal gw_RTEXT_LO 4096.
Hypothesis AL_win_gw_RDATA2_LO : gw_winal gw_RDATA2_LO 4096.
Hypothesis ROM_RSIZE_CLASSES : QZDE.ro_bytes segs (RDEBRUIJN + 32) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RSIZE_CLASSES.
Hypothesis ROM_RDEBRUIJN : QZDE.ro_bytes segs RDEBRUIJN OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RDEBRUIJN.
Hypothesis ROM_RSMALL_CNT : QZDE.ro_bytes segs (RDEBRUIJN + 128) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RSMALL_CNT.
Hypothesis ROM_RMED_CNT : QZDE.ro_bytes segs (RDEBRUIJN + 155) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RMED_CNT.
Hypothesis ROM_reservedZ : QGeV.reservedZ segs = ref_reserved.
Hypothesis LAY_ref_reserved : ref_reserved = (cons (0x10000, gw_RTEXT_LO - 0x10000) (cons (gw_RTEXT_LO, RDATA_LO - gw_RTEXT_LO) (cons (RDATA_LO, gw_RDATA2_LO - RDATA_LO) (cons (gw_RDATA2_LO, RIMG_HI - gw_RDATA2_LO) nil))))%Z.
Hypothesis AL_rvm_wait_entry : gw_al rvm_wait_entry 4.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@QQRC.Mqc.rarea_rep segs) (@rarea_rep) (gw_ent (@QQRC.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mqa.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QQRC.Mq9.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq9.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8l1.Mq8.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_0))))))))))))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QQRC.Mqc.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QQRC.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mqa.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QQRC.Mq9.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq9.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8l1.Mq8.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_1))))))))))))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@QQRC.Mqc.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QQRC.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mqa.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QQRC.Mq9.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq9.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8l1.Mq8.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_2))))))))))))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@QQRC.Mqc.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QQRC.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mqa.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QQRC.Mq9.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq9.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8l1.Mq8.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_3))))))))))))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@QQRC.Mqc.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QQRC.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mqa.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QQRC.Mq9.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq9.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8l1.Mq8.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_4))))))))))))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@QQRC.Mqc.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QQRC.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mqa.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QQRC.Mq9.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq9.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8l1.Mq8.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_5))))))))))))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@QQRC.Mqc.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QQRC.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mqa.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QQRC.Mq9.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq9.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8l1.Mq8.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_6))))))))))))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@QQRC.Mqc.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QQRC.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mqa.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QQRC.Mq9.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq9.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8l1.Mq8.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_7))))))))))))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@QQRC.Mqc.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QQRC.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mqa.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QQRC.Mq9.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq9.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8l1.Mq8.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_8))))))))))))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@QQRC.Mqc.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QQRC.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mqa.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QQRC.Mq9.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq9.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8l1.Mq8.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_9))))))))))))))).

Hypothesis rdbi_range : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Qy8Z.Mq8.gw_all) (@Qy8Z.Mq8.rdbi_range) (base + -880)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_10))) in let T := gw_fold_pcs T base (-880)%Z [0; 116; 472; 500; 524]%Z in exact T).
Hypothesis rdebruijn_read : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Qy8Z.Mq8.gw_all) (@Qy8Z.Mq8.rdebruijn_read) (base + -880)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_10))) in let T := gw_fold_pcs T base (-880)%Z [0; 116; 472; 500; 524]%Z in exact T).

Hypothesis mul_srliw27_sxv : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Q8l1.Mq8.gw_all) (@Q8l1.Mq8.mul_srliw27_sxv) (base + -880)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_10))) in let T := gw_fold_pcs T base (-880)%Z [0; 116; 472; 500; 524; 664; 676; 696; 708; 712; 768; 784; 804; 816; 876]%Z in exact T).

Definition rmrep_meta_chunk : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_meta_chunk) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_meta_chunk)).
Definition rmrep_transport_high : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_transport_high) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_transport_high)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.

Definition rmrep_put_meta_frame : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_put_meta_frame) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_put_meta_frame)).

Definition rmeta_chunk_facts : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq5.rmeta_chunk_facts) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq5.rmeta_chunk_facts)).

Ltac mem_after_store ::=
lazymatch goal with
| |- evt ?segs_ ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
let c' := cell_of_bytes bs in
let n := eval cbv in (csize c') in
lazymatch goal with
| H : rw_cells segs_ m A ?cs0 |- _ =>
split_for_access H segs_ m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
let HB := fresh "HB" in
pose proof (rw_cells_bound segs_ m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
try lazymatch goal with
| HI : mem_inv segs_ m |- _ =>
apply (mem_inv_store_cbytes segs_ m (wa (A + Z.of_nat kn)) c') in HI;
[ | exact I | apply (rw_cells_store_ok segs_ m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
end;
change bs with (cbytes c');
let H' := fresh "CH" in
pose proof (rw_cells_write segs_ m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
clear H;
cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
transport_chunks segs_ m (A + Z.of_nat kn)%Z (cbytes c');
footprint_after_store segs_ m (A + Z.of_nat kn)%Z (cbytes c');
let m' := fresh "m" in
let E := fresh "EQ" m' in
remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:E;
clear HB; try rename H' into H
end
end
end.
Ltac mem_after_store ::=
lazymatch goal with
| |- evt ?segs_ ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
let c' := cell_of_bytes bs in
let n := eval cbv in (csize c') in
lazymatch goal with
| H : rw_cells segs_ m A ?cs0 |- _ =>
split_for_access H segs_ m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
let HB := fresh "HB" in
pose proof (rw_cells_bound segs_ m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
try lazymatch goal with
| HI : mem_inv segs_ m |- _ =>
apply (mem_inv_store_cbytes segs_ m (wa (A + Z.of_nat kn)) c') in HI;
[ | exact I | apply (rw_cells_store_ok segs_ m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
end;
change bs with (cbytes c');
let H' := fresh "CH" in
pose proof (rw_cells_write segs_ m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
clear H;
cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
transport_chunks segs_ m (A + Z.of_nat kn)%Z (cbytes c');
footprint_after_store segs_ m (A + Z.of_nat kn)%Z (cbytes c');
let m' := fresh "m" in
remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm;
clear Heqm; clear HB; try clear m; try rename H' into H
end
end
end.
#[using="RDEBRUIJN RGOT_SSP e_197bc rvm_wait_entry RATP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_14 E_14 D_15 E_15 D_18 E_18 D_19 E_19 D_114 E_114 D_116 E_116 D_121 E_121 D_122 E_122 D_130 E_130 D_131 E_131 D_136 E_136 D_137 E_137 D_148 E_148 D_149 E_149 D_218 E_218 D_220 E_220 D_311 E_311 D_313 E_313 D_427 E_427 D_552 E_552 ANCH_15 ANCH_19 ANCH_116 ANCH_122 ANCH_131 ANCH_137 ANCH_149 ANCH_220 ANCH_313 LINK_427 LINK_552 RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rvm_wait_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ rdbi_range rdebruijn_read mul_srliw27_sxv"] Lemma gw_all : True. Proof. exact I. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1.

Definition rta_frame (junk : list byte) (s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) : list cell :=
[CB 48 junk; C8 rc_canary; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].

#[using="RIMG_HI gw_RDATA2_LO w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_4"] Lemma ras_ret : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
(s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) F fc (m0 m : word -> option byte) (W : list (Z * Z)) (junk : list byte) (st' : mstate) (lo : Z),
rmrep st' m -> mem_inv segs m ->
rw_cells segs m (bv_unsigned sp + -144) (rta_frame junk s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav) ->
stk segs m lo (bv_unsigned sp + -144) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 144 ->
munch ((bv_unsigned sp - 144, bv_unsigned sp) :: W)%Z m0 m -> wmono segs m0 m ->
evt segs (fun ms' => exists (a1' a2' : word) m',
ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v a0 a1' a2' a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10 s11 t3 t4 t5 t6)
F (ret_pc rav) fc None m' (seg_rom segs)
/\ munch ((bv_unsigned sp - 144, bv_unsigned sp) :: W)%Z m0 m' /\ wmono segs m0 m' /\ mem_inv segs m'
/\ stk segs m' lo (bv_unsigned sp) /\ rmrep st' m')
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 (RATP + 131696)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x860)) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI gw_RDATA2_LO w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 CODE LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_4 segs base RATP. gw_expose_fam RATP.
intros until lo. intros MR' MI FR ST LO LOLE MU WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof MR' as (_ & _ & (_ & _ & _ & _ & GUARD) & _).
(gw_expose_fam RATP; unfold alloc_ceiling, rta_frame in *).
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MUs. pose proof (wmono_refl segs m) as WMs.

st1. st1. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }

st1. st1. st1. st1. st1. st1. st1. st1. st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR2 : rmrep st' mX)
by (eapply rmrep_transport_high; [gw_exact MR' | gw_exact MUs | gw_exact WMs | intros l h [E|[]]; inversion E; subst; unfold alloc_ceiling; lia]) end.
clear MUs WMs.
release_frame FR ST (bv_unsigned sp).
apply evt_done. do 3 eexists. split; [reflexivity|].
split; [gw_exact MU|]. split; [gw_exact WM|]. split; [assumption|]. split; [gw_exact ST|]. gw_exact MR2.
Qed.

Section FIN.
Variables (st : mstate) (m : mem) (g : aptr) (mask : Z) (lo : Z).
Let G := conc st g.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis MASK : 0 < mask < 2^32.
Hypothesis CLO : alloc_ceiling <= lo.

#[using="RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 hi_114 lo_116 CODE D_114 E_114 D_116 E_116 ANCH_116 RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RDEBRUIJN LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved rdbi_range rdebruijn_read mul_srliw27_sxv MR MSL MASK CLO"] Lemma rfin_walk :
forall (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 gw : word)
(s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) F fc junk,
bv_unsigned gw = G ->
rw_cells segs m (bv_unsigned sp + -144) (rta_frame junk s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav) ->
stk segs m lo (bv_unsigned sp + -144) -> lo <= bv_unsigned sp - 144 -> mem_inv segs m ->
evt segs (fun ms' => exists (a1' a2' a3' : word) m' k,
0 <= k < 32 /\ lowbit mask = 2 ^ k /\
ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (wz k) a1' a2' a3' a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10 s11 t3 t4 t5 t6)
F (ret_pc rav) fc None m' (seg_rom segs)
/\ munch [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' lo (bv_unsigned sp)
/\ rmrep (upd_meta g (m_set_avail (mask - lowbit mask)) st) m')
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 s1 gw (wz (sxv mask)) a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 (RATP + 131696)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x1a0)) fc None m (seg_rom segs)).
Proof. clear - RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_14 w_15 w_18 w_19 w_114 w_116 w_121 w_122 w_130 w_131 w_136 w_137 w_148 w_149 w_218 w_220 w_311 w_313 w_427 w_552 hi_114 lo_116 CODE D_114 E_114 D_116 E_116 ANCH_116 RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RDEBRUIJN LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved rdbi_range rdebruijn_read mul_srliw27_sxv MR MSL MASK CLO segs base RATP st m g mask lo G. gw_expose_fam RATP; gw_expose_fam RDEBRUIJN. try gw_hide G; try gw_hide lo; try gw_hide mask; try gw_hide g; try gw_hide m; try gw_hide st.
intros until junk. intros HG FR ST LO MI.
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40)]%Z m) as MU. pose proof (wmono_refl segs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_chunk_facts st m g MR MSL) as (CH & Gpos & GC & GI1 & GI2 & _). fold G in CH, Gpos, GC, GI1, GI2.
unfold meta_cells in CH. rewrite <- HG in CH.
destruct (lowbit_facts mask ltac:(lia)) as (k & Hk & LB).
assert (P2 : 0 < 2 ^ k <= mask).
{ destruct (lowbit_nonzero mask ltac:(lia)) as (k' & Hk' & E & L). rewrite LB in E.
apply Z.pow_inj_r in E; [|lia|lia|lia]. subst k'. split; [apply Z.pow_pos_nonneg; lia| gw_exact L]. }
assert (P32 : 2 ^ k < 2 ^ 32) by (apply Z.pow_lt_mono_r; lia).
pose proof (sxv_range mask) as RA. pose proof (sxv_range (2 ^ k)) as RK.
(gw_expose_fam RATP; unfold alloc_ceiling, rta_frame in *).

step. step. rewrite (Z.land_comm (bv_unsigned (wz (sxv mask)))). rewrite (negw_and_lowbit mask) by lia. rewrite LB.

step. rewrite (wz_unsigned (sxv mask)), (wz_unsigned (sxv (2 ^ k))) by assumption. rewrite (swrap_word (sxv mask - sxv (2 ^ k))).

pose proof (munch_refl [(G, G + 40)]%Z m) as MUg. pose proof (wmono_refl segs m) as WMg.
step.
lazymatch goal with H : rw_cells segs ?mc (bv_unsigned gw) ?cs |- _ =>
apply (rw_cells_congr segs mc (bv_unsigned gw) cs
(meta_cells st (m_set_avail (mask - lowbit mask) (get_meta_rec st g)))) in H;
[| unfold meta_cells; cbn [cells_bytes cbytes m_prev m_next m_mem m_avail m_freed m_set_avail]; rewrite LB, (le4_avail_sub mask (2 ^ k)) by lia; reflexivity
| reflexivity | cbn; tauto ];
rewrite HG in H;
pose proof (rmrep_put_meta_frame st m mc g _ MR MSL MUg WMg H) as MR1; rewrite <- upd_meta_put in MR1; clear H MUg WMg
end.

step. if_cases K0; zify_cond K0.
{ exfalso. rewrite ?wz_unsigned in K0 by assumption. pose proof (proj1 (sxv_zero (2 ^ k) ltac:(lia)) K0). lia. }
clear K0.

step. step. rewrite (Z.land_comm (bv_unsigned (wz (sxv mask)))). rewrite (negw_and_lowbit mask) by lia. rewrite LB.
step. step. change 125613361 with rDB32.
step. step. step. rewrite (mul_srliw27_sxv k) by lia.
pose proof (rdbi_range k) as DR.
step. step. rewrite ?(unsigned_lit (rdbi k)) by lia.
lazymatch goal with HI : mem_inv segs ?mc |- _ => pose proof (rdebruijn_read mc k HI ltac:(lia)) as DBR; gw_expose_fam RDEBRUIJN end.
step. rewrite ?zxb_b8, ?(wz_unsigned k) by lia. clear DBR.

step.
rewrite ?LB in MR1.
eapply evt_mono.
{ eapply (ras_ret sp gp tp t0 t1 t2 s0 s1 _ _ _ _ a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 _ s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav F fc m _ _ junk _ lo);
[gw_exact MR1 | assumption | gw_exact FR | gw_exact ST | unfold alloc_ceiling; lia | lia | gw_exact MU | gw_exact WM]. }
cbv beta. intros ms' (a1' & a2' & m' & -> & MU' & WM' & MI' & ST' & MR').
do 4 eexists. exists k. split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
split; [gw_exact MU'|]. split; [gw_exact WM'|]. split; [gw_exact MI'|]. split; [gw_exact ST'|]. gw_exact MR'.
Qed.
End FIN.

End RC__1.

End G.
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0.

Import Q2qa.Mq1 QytA Q4J3.Mq4 QPjm.Mq0 Q4J3.Mq2 Qy5Y.Mq6 QPjm.Mq3 QJE4.Mq0 QJE4.Mq1 QWTl.Mq1 Q9Ay.Mq9.
Import QZAi.Mq2 QUZl Q7S0.Mq0 QGeV.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QDXD.Mq2.
Import QkTt.Mq4.
Import Q8QT.Mq2.
Import Qy8Z.Mq9.
Import QQRC.Mq5.
Import Qy8Z.Mq2.
Import Q8l1.Mq5.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Open Scope bv_scope.
Open Scope Z_scope.

Definition errno_loc_code : list Z :=
[0x00020513; 0xf5c50513; 0x00008067]%Z.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment) (base : Z).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (rerrno_loc_entry rvm_wait_entry : Z).
Variables (w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 : Z).
Variables (hi_7 hi_10 hi_14 : bv 20).
Variables (lo_8 lo_12 lo_15 : bv 12).
Variables (joff_30 joff_98 joff_120 joff_173 joff_175 joff_181 : bv 21).
Variables (e_197bc e_24f80 : Z).
Hypothesis CODE : code_at segs base (alloc_meta_code w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 728.
Let rmmap_entry := (rvm_wait_entry + 4)%Z.
Let rmprotect_entry := (rvm_wait_entry + 240)%Z.
Hypothesis D_7 : decode_any (Z_to_bv 32 w_7) = Some (Auipc 10 hi_7, 4%Z).
Hypothesis E_7 : is_ecall (Z_to_bv 32 w_7) = false.
Hypothesis D_8 : decode_any (Z_to_bv 32 w_8) = Some (Load SZ8 true 18 10 lo_8, 4%Z).
Hypothesis E_8 : is_ecall (Z_to_bv 32 w_8) = false.
Hypothesis D_10 : decode_any (Z_to_bv 32 w_10) = Some (Auipc 11 hi_10, 4%Z).
Hypothesis E_10 : is_ecall (Z_to_bv 32 w_10) = false.
Hypothesis D_12 : decode_any (Z_to_bv 32 w_12) = Some (OpImm ALU_ADD 19 11 lo_12, 4%Z).
Hypothesis E_12 : is_ecall (Z_to_bv 32 w_12) = false.
Hypothesis D_14 : decode_any (Z_to_bv 32 w_14) = Some (Auipc 11 hi_14, 4%Z).
Hypothesis E_14 : is_ecall (Z_to_bv 32 w_14) = false.
Hypothesis D_15 : decode_any (Z_to_bv 32 w_15) = Some (OpImm ALU_ADD 8 11 lo_15, 4%Z).
Hypothesis E_15 : is_ecall (Z_to_bv 32 w_15) = false.
Hypothesis D_30 : decode_any (Z_to_bv 32 w_30) = Some (Jal 1 joff_30, 4%Z).
Hypothesis E_30 : is_ecall (Z_to_bv 32 w_30) = false.
Hypothesis D_98 : decode_any (Z_to_bv 32 w_98) = Some (Jal 1 joff_98, 4%Z).
Hypothesis E_98 : is_ecall (Z_to_bv 32 w_98) = false.
Hypothesis D_120 : decode_any (Z_to_bv 32 w_120) = Some (Jal 1 joff_120, 4%Z).
Hypothesis E_120 : is_ecall (Z_to_bv 32 w_120) = false.
Hypothesis D_173 : decode_any (Z_to_bv 32 w_173) = Some (Jal 1 joff_173, 4%Z).
Hypothesis E_173 : is_ecall (Z_to_bv 32 w_173) = false.
Hypothesis D_175 : decode_any (Z_to_bv 32 w_175) = Some (Jal 1 joff_175, 4%Z).
Hypothesis E_175 : is_ecall (Z_to_bv 32 w_175) = false.
Hypothesis D_181 : decode_any (Z_to_bv 32 w_181) = Some (Jal 1 joff_181, 4%Z).
Hypothesis E_181 : is_ecall (Z_to_bv 32 w_181) = false.
Hypothesis ANCH_8 : gw_anch (Z.shiftl (bv_signed hi_7) 12 + (base + 28) + bv_signed lo_8)%Z RGOT_SSP.
Hypothesis ANCH_12 : gw_anch (Z.shiftl (bv_signed hi_10) 12 + (base + 40) + bv_signed lo_12)%Z (RATP + 131960).
Hypothesis ANCH_15 : gw_anch (Z.shiftl (bv_signed hi_14) 12 + (base + 56) + bv_signed lo_15)%Z (RATP + 131728).
Hypothesis LINK_30 : gw_anch (base + 120 + bv_signed joff_30)%Z (e_24f80 + 0)%Z.
Hypothesis LINK_98 : gw_anch (base + 392 + bv_signed joff_98)%Z (rvm_wait_entry + 4)%Z.
Hypothesis LINK_120 : gw_anch (base + 480 + bv_signed joff_120)%Z (rvm_wait_entry + 4)%Z.
Hypothesis LINK_173 : gw_anch (base + 692 + bv_signed joff_173)%Z (rvm_wait_entry + 240)%Z.
Hypothesis LINK_175 : gw_anch (base + 700 + bv_signed joff_175)%Z (rerrno_loc_entry + 0)%Z.
Hypothesis LINK_181 : gw_anch (base + 724 + bv_signed joff_181)%Z (e_197bc + 0)%Z.
Hypothesis CODE_rerrno_loc_entry : code_at segs rerrno_loc_entry errno_loc_code.
Hypothesis AL_rerrno_loc_entry_b4 : gw_b4 rerrno_loc_entry.
Hypothesis RNG_rerrno_loc_entry_code : gw_br rerrno_loc_entry 12.
Hypothesis RNG_RATP : gw_br RATP 1896.
Hypothesis LAY_lo_RATP : gw_le (gw_RDATA2_LO + 164) RATP.
Hypothesis LAY_hi_RATP : gw_le ((RATP + 132896)) RIMG_HI.
Hypothesis AL_RATP : gw_al RATP 8.
Hypothesis RNG_RDEBRUIJN : gw_br RDEBRUIJN 159.
Hypothesis LAY_lo_RDEBRUIJN : gw_le (0x10000 + 0) RDEBRUIJN.
Hypothesis LAY_hi_RDEBRUIJN : gw_le ((RDEBRUIJN + 159)) gw_RTEXT_LO.
Hypothesis AL_RDEBRUIJN : gw_al RDEBRUIJN 8.
Hypothesis RNG_RGOT_SSP : gw_br RGOT_SSP 8.
Hypothesis LAY_lo_RGOT_SSP : gw_le (RDATA_LO + 0) RGOT_SSP.
Hypothesis LAY_hi_RGOT_SSP : gw_le ((RGOT_SSP + 8)) gw_RDATA2_LO.
Hypothesis AL_RGOT_SSP : gw_al RGOT_SSP 8.
Hypothesis LAY_win_0 : gw_win (0x10000 + 1) gw_RTEXT_LO.
Hypothesis LAY_win_1 : gw_win (gw_RTEXT_LO + 1) RDATA_LO.
Hypothesis LAY_win_2 : gw_win (RDATA_LO + 1) gw_RDATA2_LO.
Hypothesis LAY_win_3 : gw_win (gw_RDATA2_LO + 1) RIMG_HI.
Hypothesis LAY_win_4 : gw_win RIMG_HI 0x1000000.
Hypothesis AL_win_RIMG_HI : gw_winal RIMG_HI 4096.
Hypothesis AL_win_RDATA_LO : gw_winal RDATA_LO 4096.
Hypothesis AL_win_gw_RTEXT_LO : gw_winal gw_RTEXT_LO 4096.
Hypothesis AL_win_gw_RDATA2_LO : gw_winal gw_RDATA2_LO 4096.
Hypothesis ROM_RSIZE_CLASSES : QZDE.ro_bytes segs (RDEBRUIJN + 32) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RSIZE_CLASSES.
Hypothesis ROM_RDEBRUIJN : QZDE.ro_bytes segs RDEBRUIJN OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RDEBRUIJN.
Hypothesis ROM_RSMALL_CNT : QZDE.ro_bytes segs (RDEBRUIJN + 128) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RSMALL_CNT.
Hypothesis ROM_RMED_CNT : QZDE.ro_bytes segs (RDEBRUIJN + 155) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RMED_CNT.
Hypothesis ROM_reservedZ : QGeV.reservedZ segs = ref_reserved.
Hypothesis LAY_ref_reserved : ref_reserved = (cons (0x10000, gw_RTEXT_LO - 0x10000) (cons (gw_RTEXT_LO, RDATA_LO - gw_RTEXT_LO) (cons (RDATA_LO, gw_RDATA2_LO - RDATA_LO) (cons (gw_RDATA2_LO, RIMG_HI - gw_RDATA2_LO) nil))))%Z.
Hypothesis AL_rerrno_loc_entry : gw_al rerrno_loc_entry 4.
Hypothesis AL_rvm_wait_entry : gw_al rvm_wait_entry 4.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Definition ram_fp : ltac:(gw_rebind_ty (@QQRC.Mq5.ram_fp RATP) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QQRC.Mq5.ram_fp RATP) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@Q8l1.Mq5.ram_fp RATP) (@ram_fp) (gw_ent (@QQRC.Mq5.ram_fp RATP) (@ram_fp) gw_tbl_0)).
Definition rpres_except : ltac:(gw_rebind_ty (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@Q8l1.Mq5.rpres_except segs) (@rpres_except) (gw_ent (@QQRC.Mq5.rpres_except segs) (@rpres_except) (gw_ent (@QDXD.Mq2.rpres_except segs) (@rpres_except) (gw_ent (@QCa8.Mq5.rpres_except segs) (@rpres_except) (gw_ent (@Qy8Z.Mq9.rpres_except segs) (@rpres_except) gw_tbl_1))))).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@Q8l1.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QQRC.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq9.rarea_rep segs) (@rarea_rep) gw_tbl_2)))))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@Q8l1.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QQRC.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq9.rmrep_areas segs) (@rmrep_areas) gw_tbl_3)))))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@Q8l1.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QQRC.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq9.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_4)))))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@Q8l1.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QQRC.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq9.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_5)))))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@Q8l1.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QQRC.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq9.rgroup_rep segs) (@rgroup_rep) gw_tbl_6)))))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@Q8l1.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QQRC.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq9.rmrep_groups segs) (@rmrep_groups) gw_tbl_7)))))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@Q8l1.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QQRC.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq9.rshadow_rep segs) (@rshadow_rep) gw_tbl_8)))))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@Q8l1.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QQRC.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq9.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_9)))))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@Q8l1.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QQRC.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq9.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_10)))))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_11)).
Notation gw_tbl_12 := (gw_ent (@Q8l1.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QQRC.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq9.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_11)))))))).
Definition ram_ret_post : ltac:(gw_rebind_ty (@QQRC.Mq5.ram_ret_post segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@QQRC.Mq5.ram_ret_post segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_12)).
Notation gw_tbl_13 := (gw_ent (@Q8l1.Mq5.ram_ret_post segs RATP RGOT_SSP ref_reserved RC__) (@ram_ret_post) (gw_ent (@QQRC.Mq5.ram_ret_post segs RATP RGOT_SSP ref_reserved RC__) (@ram_ret_post) gw_tbl_12)).
Definition ram_frame : ltac:(gw_rebind_ty (@QQRC.Mq5.ram_frame RC__) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@QQRC.Mq5.ram_frame RC__) constr:(gw_tbl_13)).
Notation gw_tbl_14 := (gw_ent (@Q8l1.Mq5.ram_frame RC__) (@ram_frame) (gw_ent (@QQRC.Mq5.ram_frame RC__) (@ram_frame) gw_tbl_13)).

Definition rmrep_meta_chunk : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_meta_chunk) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_meta_chunk)).
Definition rmrep_transport_high : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_transport_high) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_transport_high)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.
Definition rpres_except_trans : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_trans) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_trans)).
Definition rpres_except_mono : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_mono) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_mono)).

Definition rmrep_put_meta_frame : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_put_meta_frame) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_put_meta_frame)).
Definition rpres_except_of_munch_cov : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rpres_except_of_munch_cov) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rpres_except_of_munch_cov)).
Definition rmrep_ctx_frameW : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_ctx_frameW) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_ctx_frameW)).

Definition ram_fp_stack : ltac:(gw_ctx_fold_ty2 (@QQRC.Mq5.ram_fp_stack) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QQRC.Mq5.ram_fp_stack)).
Definition ram_fp_ctx : ltac:(gw_ctx_fold_ty2 (@QQRC.Mq5.ram_fp_ctx) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QQRC.Mq5.ram_fp_ctx)).

#[using="RGOT_SSP rerrno_loc_entry e_197bc rvm_wait_entry rmmap_entry rmprotect_entry e_24f80 RATP RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_7 E_7 D_8 E_8 D_10 E_10 D_12 E_12 D_14 E_14 D_15 E_15 D_30 E_30 D_98 E_98 D_120 E_120 D_173 E_173 D_175 E_175 D_181 E_181 ANCH_8 ANCH_12 ANCH_15 LINK_30 LINK_98 LINK_120 LINK_173 LINK_175 LINK_181 CODE_rerrno_loc_entry AL_rerrno_loc_entry_b4 RNG_rerrno_loc_entry_code RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rerrno_loc_entry AL_rvm_wait_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ rmmap_entry rmprotect_entry"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := first [clear - hs segs base w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 hi_7 hi_10 hi_14 lo_8 lo_12 lo_15 joff_30 joff_98 joff_120 joff_173 joff_175 joff_181 RGOT_SSP rerrno_loc_entry e_197bc rvm_wait_entry rmmap_entry rmprotect_entry e_24f80 RATP RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_7 E_7 D_8 E_8 D_10 E_10 D_12 E_12 D_14 E_14 D_15 E_15 D_30 E_30 D_98 E_98 D_120 E_120 D_173 E_173 D_175 E_175 D_181 E_181 ANCH_8 ANCH_12 ANCH_15 LINK_30 LINK_98 LINK_120 LINK_173 LINK_175 LINK_181 CODE_rerrno_loc_entry AL_rerrno_loc_entry_b4 RNG_rerrno_loc_entry_code RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rerrno_loc_entry AL_rvm_wait_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ | clear - hs segs base w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 hi_7 hi_10 hi_14 lo_8 lo_12 lo_15 joff_30 joff_98 joff_120 joff_173 joff_175 joff_181 RGOT_SSP rerrno_loc_entry e_197bc rvm_wait_entry rmmap_entry rmprotect_entry e_24f80 RATP RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_7 E_7 D_8 E_8 D_10 E_10 D_12 E_12 D_14 E_14 D_15 E_15 D_30 E_30 D_98 E_98 D_120 E_120 D_173 E_173 D_175 E_175 D_181 E_181 ANCH_8 ANCH_12 ANCH_15 LINK_30 LINK_98 LINK_120 LINK_173 LINK_175 LINK_181 CODE_rerrno_loc_entry AL_rerrno_loc_entry_b4 RNG_rerrno_loc_entry_code RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rerrno_loc_entry AL_rvm_wait_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay].

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1.

#[using="rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 CODE rmmap_entry rmprotect_entry"] Lemma ram_disp_dead : forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
(m : word -> option byte) (st : mstate),
rmrep st m -> c_avail_meta_area_count (ctx st) = 0 -> c_brk (ctx st) = BrkDead ->
evt segs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (2^64 - 1)) (Z_to_bv 64 0) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 (RATP + 131960)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x1b8)) fc None m (seg_rom segs))
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 (RATP + 131960)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x108)) fc None m (seg_rom segs)).
Proof. clear - rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 CODE rmmap_entry rmprotect_entry segs base RATP. gw_expose_fam RATP.
intros until st. intros MR CNT BRK.
pose proof MR as (WF & (C1 & _ & _ & _ & _ & C6) & _). unfold ctx_head_cells in C1. rewrite CNT in C1.
unfold ctx_tail_cells, brk_word in C6. rewrite BRK in C6.
unfold pw in C1. cbn [oconc] in C1. unfold wz in C1, C6.
gw_expose_fam RATP. change ((RATP + 132880)) with (RATP + 132880) in C6.

st1. st1. rewrite bv_eqb_refl. cbn [negb]. cbv iota.

st1. st1. st1.
change (bv_eqb (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (-1))) with true. cbv iota.

st1. rewrite bv_eqb_refl. cbv iota.
apply evt_done. reflexivity.
Qed.

#[using="w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 joff_120 CODE D_120 E_120 LINK_120 rmmap_entry rmprotect_entry"] Lemma ram_to_mmap : forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
(m : word -> option byte) (st : mstate),
rmrep st m -> 0 <= c_meta_alloc_shift (ctx st) <= 40 ->
let n := Z.shiftl 2 (c_meta_alloc_shift (ctx st)) in
evt segs (fun ms' => ms' = MS (mkR (Z_to_bv 64 (base + 0x1e4)) sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 n)
(Z_to_bv 64 0) (Z_to_bv 64 (n * 4096)) (Z_to_bv 64 0) (Z_to_bv 64 34) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) a6 a7
(Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 (RATP + 131960)) (Z_to_bv 64 (-1)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmmap_entry) fc None m (seg_rom segs))
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 (RATP + 131960)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x1b8)) fc None m (seg_rom segs)).
Proof. clear - w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 joff_120 CODE D_120 E_120 LINK_120 rmmap_entry rmprotect_entry segs base RATP. gw_expose_fam RATP.
intros until st. intros MR SH n.
pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
gw_expose_fam RATP.

st1. st1. st1.
rewrite (Z.mod_small (c_meta_alloc_shift (ctx st)) 64) by lia.
assert (NR : 0 < Z.shiftl 2 (c_meta_alloc_shift (ctx st)) <= 2^41).
{ rewrite Z.shiftl_mul_pow2 by lia. split; [apply Z.mul_pos_pos; [lia| apply Z.pow_pos_nonneg; lia]|].
change (2^41) with (2 * 2^40). apply Z.mul_le_mono_nonneg_l; [lia|]. apply Z.pow_le_mono_r; lia. }

st1. st1. st1. st1. st1. st1. st1. st1.
apply evt_done. unfold rmmap_entry. subst n. reflexivity.
Qed.

#[using="RIMG_HI gw_RDATA2_LO rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 CODE LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_4 rmmap_entry rmprotect_entry"] Lemma ram_mm_fail : forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
(m0 m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate),
rmrep st m -> mem_inv segs m ->
rpres_except (ram_fp st lo (bv_unsigned sp)) m0 m -> wmono segs m0 m ->
rw_cells segs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
stk segs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
evt segs (ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo st m0 st (Z_to_bv 64 0))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 (RATP + 131960)) (Z_to_bv 64 (-1)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x1e4)) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI gw_RDATA2_LO rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 CODE LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_4 rmmap_entry rmprotect_entry segs base RATP. gw_expose_fam RATP.
intros until st. intros MR MI PE0 WM0 FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl segs m) as WM.
pose proof MR as (_ & _ & (_ & _ & _ & _ & GUARD) & _).
(gw_expose_fam RATP; unfold alloc_ceiling, ram_frame in *).

st1. rewrite bv_eqb_refl. cbv iota. st1. st1. st1. st1. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }

st1. st1. st1. st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRX : rmrep st mX) end.
{ eapply rmrep_transport_high; [gw_exact MR| gw_exact MU| gw_exact WM|]. intros l h [E|[]]; inversion E; subst; unfold alloc_ceiling; lia. }
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold ram_ret_post. do 15 eexists. split; [reflexivity|].
split.
{ eapply rpres_except_trans; [gw_exact PE0|].
apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [gw_exact MU|gw_exact WM|].
cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply ram_fp_stack. lia. }
split; [eapply wmono_trans; [gw_exact WM0| gw_exact WM]|]. split; [assumption|]. split; [gw_exact ST|]. gw_exact MRX.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved rmmap_entry rmprotect_entry"] Lemma ram_mm_ok : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
(m0 m : word -> option byte) (junk : list byte) (lo x n : Z) (st0 st : mstate) (rid : N) (r : region),
rmrep st m -> mem_inv segs m -> (forall a, ram_fp st0 lo (bv_unsigned sp) a -> ram_fp st lo (bv_unsigned sp) a) ->
(s_regions st) !! rid = Some r -> r_base r = x -> x mod 4096 = 0 -> 0 < x -> x + 8192 <= alloc_ceiling -> 1 <= n < 2^62 ->
0 <= c_meta_alloc_shift (ctx st) < 2^62 ->
rpres_except (ram_fp st0 lo (bv_unsigned sp)) m0 m -> wmono segs m0 m ->
rw_cells segs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
stk segs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
evt segs (fun ms' => exists m',
ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (x + 4096)) (Z_to_bv 64 0)
(Z_to_bv 64 (c_meta_alloc_shift (ctx st) + 1)) (Z_to_bv 64 (n - 1)) a3 a4 a5 a6 a7
(Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 (RATP + 131960)) (Z_to_bv 64 (-1)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x2a8)) fc None m' (seg_rom segs)
/\ rpres_except (ram_fp st lo (bv_unsigned sp)) m0 m' /\ wmono segs m0 m' /\ mem_inv segs m'
/\ rw_cells segs m' (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw)
/\ stk segs m' lo (bv_unsigned sp + -64)
/\ rmrep (mm_ok_st st rid n) m')
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 n) (Z_to_bv 64 x) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 (RATP + 131960)) (Z_to_bv 64 (-1)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x1e4)) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved rmmap_entry rmprotect_entry segs base RATP. gw_expose_fam RATP.
intros until r. intros MR MI FP0 Hr RB XAL X0 XC NR SH PE0 WM0 FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); ((RATP + 131968), (RATP + 132896))]%Z m) as MU. pose proof (wmono_refl segs m) as WM.
pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
assert (AL : Z.land (x + 4096) 4095 = 0).
{ change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096. clear - XAL X0 RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved rmmap_entry rmprotect_entry segs base RATP. Z.div_mod_to_equations. lia. }
assert (AL' : Z.land 4095 (x + 4096) = 0) by (rewrite Z.land_comm; gw_exact AL).
change (x mod 4096 = 0) with (pgal x) in XAL.
(gw_expose_fam RATP; unfold alloc_ceiling, ram_frame in *).

st1.
assert (CF : bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 (-1)) = false)
by (unfold bv_eqb; rewrite (unsigned_lit x) by lia; change (bv_unsigned (Z_to_bv 64 (-1))) with (2^64 - 1)%Z; apply Z.eqb_neq; lia).
rewrite CF; clear CF.

st1. st1. st1. st1. st1. st1.
replace ((n + -1) * 1) with (n - 1) by lia.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [((RATP + 132008), (RATP + 132024)); ((RATP + 132040), (RATP + 132048))]%Z mX) as MUc; pose proof (wmono_refl segs mX) as WMc end.
gw_expose_fam RATP.

st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR2 : rmrep (mm_ok_st st rid n) mX) end.
{ eapply (rmrep_ctx_frameW st _ _ _ _ MR MUc WMc); try reflexivity.
- intros lo' hi' [E|[E|[]]]; inversion E; subst; gw_expose_fam RATP; lia.
- left. (gw_expose_fam RATP; unfold ctx_head_cells). cbn [ctx mm_ok_st upd_ctx s_ctx set_meta_alloc_shift set_avail_meta_area_count set_avail_meta_areas c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
change (pw (mm_ok_st st rid n) ?q) with (pw st q). unfold pw. cbn [oconc]. change (conc (mm_ok_st st rid n) ?q) with (conc st q).
rewrite (conc_region' st (rid, 4096) r Hr). cbn [snd]. rewrite RB. unfold wz.
lazymatch goal with H : rw_cells segs ?mX (RATP + 131968) _ |- _ => exact H end.
- right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; gw_expose_fam RATP; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; gw_expose_fam RATP; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; gw_expose_fam RATP; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; gw_expose_fam RATP; lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; gw_expose_fam RATP; lia. }
clear MUc WMc.

st1. st1. rewrite ?AL, ?AL'. st1. rewrite bv_eqb_refl. cbv iota.
apply evt_done. eexists. split; [reflexivity|].
split.
{ eapply rpres_except_trans; [eapply rpres_except_mono; [gw_exact PE0| gw_exact FP0]|].
apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [gw_exact MU|gw_exact WM|].
cbn [ivs_covered]. split; [|split; [|exact I]].
- intros y Hy. apply ram_fp_stack. lia.
- intros y Hy. apply ram_fp_ctx. gw_expose_fam RATP. lia. }
split; [first [gw_exact WM0 | eapply wmono_trans; [gw_exact WM0| gw_exact WM]]|]. split; [assumption|]. split; [gw_exact FR|]. split; [gw_exact ST|]. gw_exact MR2.
Qed.

End RC__1.

End G.
End Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXxF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.

Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq QJE4.Mq4 Qy5Y.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg QDUx.Mq8 Q9Ay.Mqa QXxF.Mq3 QDUx.Mq9.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QCa8.Mq4.
Import QDXD.Mq2.
Import QkTt.Mq3.
Import QDXD.Mq1.
Import QkTt.Mq5.
Import Qy8Z.Mq7.
Import Qy8Z.Mq1.
Import Qy8Z.Mq8.
Import QQRC.Mq8.
Import Q8l1.Mq8.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.
Open Scope Z_scope.

Definition errno_loc_code : list Z :=
[0x00020513; 0xf5c50513; 0x00008067]%Z.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment) (base : Z).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (rerrno_loc_entry rvm_wait_entry rlock_entry runlock_entry : Z).
Variables (w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 : Z).
Variables (hi_26 hi_40 hi_43 hi_57 hi_85 hi_125 hi_128 hi_147 hi_216 : bv 20).
Variables (lo_27 lo_41 lo_44 lo_59 lo_90 lo_126 lo_129 lo_148 lo_217 : bv 12).
Variables (joff_11 joff_37 joff_45 joff_130 joff_149 joff_152 joff_203 joff_218 : bv 21).
Hypothesis CODE : code_at segs base (malloc_code w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 880.
Let rmalloc_entry := (base + 0)%Z.
Let ralloc_slot_entry := (base + 880)%Z.
Let rmmap_entry := (rvm_wait_entry + 4)%Z.
Let rmunmap_entry := (rvm_wait_entry + 524)%Z.
Hypothesis D_11 : decode_any (Z_to_bv 32 w_11) = Some (Jal 1 joff_11, 4%Z).
Hypothesis E_11 : is_ecall (Z_to_bv 32 w_11) = false.
Hypothesis D_26 : decode_any (Z_to_bv 32 w_26) = Some (Auipc 11 hi_26, 4%Z).
Hypothesis E_26 : is_ecall (Z_to_bv 32 w_26) = false.
Hypothesis D_27 : decode_any (Z_to_bv 32 w_27) = Some (OpImm ALU_ADD 9 11 lo_27, 4%Z).
Hypothesis E_27 : is_ecall (Z_to_bv 32 w_27) = false.
Hypothesis D_37 : decode_any (Z_to_bv 32 w_37) = Some (Jal 1 joff_37, 4%Z).
Hypothesis E_37 : is_ecall (Z_to_bv 32 w_37) = false.
Hypothesis D_40 : decode_any (Z_to_bv 32 w_40) = Some (Auipc 10 hi_40, 4%Z).
Hypothesis E_40 : is_ecall (Z_to_bv 32 w_40) = false.
Hypothesis D_41 : decode_any (Z_to_bv 32 w_41) = Some (Load SZ1 false 10 10 lo_41, 4%Z).
Hypothesis E_41 : is_ecall (Z_to_bv 32 w_41) = false.
Hypothesis D_43 : decode_any (Z_to_bv 32 w_43) = Some (Auipc 10 hi_43, 4%Z).
Hypothesis E_43 : is_ecall (Z_to_bv 32 w_43) = false.
Hypothesis D_44 : decode_any (Z_to_bv 32 w_44) = Some (OpImm ALU_ADD 10 10 lo_44, 4%Z).
Hypothesis E_44 : is_ecall (Z_to_bv 32 w_44) = false.
Hypothesis D_45 : decode_any (Z_to_bv 32 w_45) = Some (Jal 1 joff_45, 4%Z).
Hypothesis E_45 : is_ecall (Z_to_bv 32 w_45) = false.
Hypothesis D_57 : decode_any (Z_to_bv 32 w_57) = Some (Auipc 12 hi_57, 4%Z).
Hypothesis E_57 : is_ecall (Z_to_bv 32 w_57) = false.
Hypothesis D_59 : decode_any (Z_to_bv 32 w_59) = Some (OpImm ALU_ADD 19 12 lo_59, 4%Z).
Hypothesis E_59 : is_ecall (Z_to_bv 32 w_59) = false.
Hypothesis D_85 : decode_any (Z_to_bv 32 w_85) = Some (Auipc 12 hi_85, 4%Z).
Hypothesis E_85 : is_ecall (Z_to_bv 32 w_85) = false.
Hypothesis D_90 : decode_any (Z_to_bv 32 w_90) = Some (OpImm ALU_ADD 11 12 lo_90, 4%Z).
Hypothesis E_90 : is_ecall (Z_to_bv 32 w_90) = false.
Hypothesis D_125 : decode_any (Z_to_bv 32 w_125) = Some (Auipc 10 hi_125, 4%Z).
Hypothesis E_125 : is_ecall (Z_to_bv 32 w_125) = false.
Hypothesis D_126 : decode_any (Z_to_bv 32 w_126) = Some (Load SZ1 false 10 10 lo_126, 4%Z).
Hypothesis E_126 : is_ecall (Z_to_bv 32 w_126) = false.
Hypothesis D_128 : decode_any (Z_to_bv 32 w_128) = Some (Auipc 10 hi_128, 4%Z).
Hypothesis E_128 : is_ecall (Z_to_bv 32 w_128) = false.
Hypothesis D_129 : decode_any (Z_to_bv 32 w_129) = Some (OpImm ALU_ADD 10 10 lo_129, 4%Z).
Hypothesis E_129 : is_ecall (Z_to_bv 32 w_129) = false.
Hypothesis D_130 : decode_any (Z_to_bv 32 w_130) = Some (Jal 1 joff_130, 4%Z).
Hypothesis E_130 : is_ecall (Z_to_bv 32 w_130) = false.
Hypothesis D_147 : decode_any (Z_to_bv 32 w_147) = Some (Auipc 10 hi_147, 4%Z).
Hypothesis E_147 : is_ecall (Z_to_bv 32 w_147) = false.
Hypothesis D_148 : decode_any (Z_to_bv 32 w_148) = Some (OpImm ALU_ADD 10 10 lo_148, 4%Z).
Hypothesis E_148 : is_ecall (Z_to_bv 32 w_148) = false.
Hypothesis D_149 : decode_any (Z_to_bv 32 w_149) = Some (Jal 1 joff_149, 4%Z).
Hypothesis E_149 : is_ecall (Z_to_bv 32 w_149) = false.
Hypothesis D_152 : decode_any (Z_to_bv 32 w_152) = Some (Jal 1 joff_152, 4%Z).
Hypothesis E_152 : is_ecall (Z_to_bv 32 w_152) = false.
Hypothesis D_203 : decode_any (Z_to_bv 32 w_203) = Some (Jal 1 joff_203, 4%Z).
Hypothesis E_203 : is_ecall (Z_to_bv 32 w_203) = false.
Hypothesis D_216 : decode_any (Z_to_bv 32 w_216) = Some (Auipc 10 hi_216, 4%Z).
Hypothesis E_216 : is_ecall (Z_to_bv 32 w_216) = false.
Hypothesis D_217 : decode_any (Z_to_bv 32 w_217) = Some (OpImm ALU_ADD 10 10 lo_217, 4%Z).
Hypothesis E_217 : is_ecall (Z_to_bv 32 w_217) = false.
Hypothesis D_218 : decode_any (Z_to_bv 32 w_218) = Some (Jal 1 joff_218, 4%Z).
Hypothesis E_218 : is_ecall (Z_to_bv 32 w_218) = false.
Hypothesis ANCH_27 : gw_anch (Z.shiftl (bv_signed hi_26) 12 + (base + 104) + bv_signed lo_27)%Z (RATP + 131960).
Hypothesis ANCH_41 : gw_anch (Z.shiftl (bv_signed hi_40) 12 + (base + 160) + bv_signed lo_41)%Z (RATP + 131731).
Hypothesis ANCH_44 : gw_anch (Z.shiftl (bv_signed hi_43) 12 + (base + 172) + bv_signed lo_44)%Z (RATP + 131960).
Hypothesis ANCH_59 : gw_anch (Z.shiftl (bv_signed hi_57) 12 + (base + 228) + bv_signed lo_59)%Z RDEBRUIJN.
Hypothesis ANCH_90 : gw_anch (Z.shiftl (bv_signed hi_85) 12 + (base + 340) + bv_signed lo_90)%Z (RDEBRUIJN + 32).
Hypothesis ANCH_126 : gw_anch (Z.shiftl (bv_signed hi_125) 12 + (base + 500) + bv_signed lo_126)%Z (RATP + 131731).
Hypothesis ANCH_129 : gw_anch (Z.shiftl (bv_signed hi_128) 12 + (base + 512) + bv_signed lo_129)%Z (RATP + 131960).
Hypothesis ANCH_148 : gw_anch (Z.shiftl (bv_signed hi_147) 12 + (base + 588) + bv_signed lo_148)%Z (RATP + 131960).
Hypothesis ANCH_217 : gw_anch (Z.shiftl (bv_signed hi_216) 12 + (base + 864) + bv_signed lo_217)%Z (RATP + 131960).
Hypothesis LINK_11 : gw_anch (base + 44 + bv_signed joff_11)%Z (rerrno_loc_entry + 0)%Z.
Hypothesis LINK_37 : gw_anch (base + 148 + bv_signed joff_37)%Z (rmmap_entry + 0)%Z.
Hypothesis LINK_45 : gw_anch (base + 180 + bv_signed joff_45)%Z (rlock_entry + 0)%Z.
Hypothesis LINK_130 : gw_anch (base + 520 + bv_signed joff_130)%Z (rlock_entry + 0)%Z.
Hypothesis LINK_149 : gw_anch (base + 596 + bv_signed joff_149)%Z (runlock_entry + 0)%Z.
Hypothesis LINK_152 : gw_anch (base + 608 + bv_signed joff_152)%Z (rmunmap_entry + 0)%Z.
Hypothesis LINK_203 : gw_anch (base + 812 + bv_signed joff_203)%Z (runlock_entry + 0)%Z.
Hypothesis LINK_218 : gw_anch (base + 872 + bv_signed joff_218)%Z (runlock_entry + 0)%Z.
Hypothesis CODE_rerrno_loc_entry : code_at segs rerrno_loc_entry errno_loc_code.
Hypothesis AL_rerrno_loc_entry_b4 : gw_b4 rerrno_loc_entry.
Hypothesis RNG_rerrno_loc_entry_code : gw_br rerrno_loc_entry 12.
Hypothesis RNG_RATP : gw_br RATP 1896.
Hypothesis LAY_lo_RATP : gw_le (gw_RDATA2_LO + 164) RATP.
Hypothesis LAY_hi_RATP : gw_le ((RATP + 132896)) RIMG_HI.
Hypothesis AL_RATP : gw_al RATP 8.
Hypothesis RNG_RDEBRUIJN : gw_br RDEBRUIJN 159.
Hypothesis LAY_lo_RDEBRUIJN : gw_le (0x10000 + 0) RDEBRUIJN.
Hypothesis LAY_hi_RDEBRUIJN : gw_le ((RDEBRUIJN + 159)) gw_RTEXT_LO.
Hypothesis AL_RDEBRUIJN : gw_al RDEBRUIJN 8.
Hypothesis RNG_RGOT_SSP : gw_br RGOT_SSP 8.
Hypothesis LAY_lo_RGOT_SSP : gw_le (RDATA_LO + 0) RGOT_SSP.
Hypothesis LAY_hi_RGOT_SSP : gw_le ((RGOT_SSP + 8)) gw_RDATA2_LO.
Hypothesis AL_RGOT_SSP : gw_al RGOT_SSP 8.
Hypothesis LAY_win_0 : gw_win (0x10000 + 1) gw_RTEXT_LO.
Hypothesis LAY_win_1 : gw_win (gw_RTEXT_LO + 1) RDATA_LO.
Hypothesis LAY_win_2 : gw_win (RDATA_LO + 1) gw_RDATA2_LO.
Hypothesis LAY_win_3 : gw_win (gw_RDATA2_LO + 1) RIMG_HI.
Hypothesis LAY_win_4 : gw_win RIMG_HI 0x1000000.
Hypothesis AL_win_RIMG_HI : gw_winal RIMG_HI 4096.
Hypothesis AL_win_RDATA_LO : gw_winal RDATA_LO 4096.
Hypothesis AL_win_gw_RTEXT_LO : gw_winal gw_RTEXT_LO 4096.
Hypothesis AL_win_gw_RDATA2_LO : gw_winal gw_RDATA2_LO 4096.
Hypothesis ROM_RSIZE_CLASSES : QZDE.ro_bytes segs (RDEBRUIJN + 32) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RSIZE_CLASSES.
Hypothesis ROM_RDEBRUIJN : QZDE.ro_bytes segs RDEBRUIJN OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RDEBRUIJN.
Hypothesis ROM_RSMALL_CNT : QZDE.ro_bytes segs (RDEBRUIJN + 128) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RSMALL_CNT.
Hypothesis ROM_RMED_CNT : QZDE.ro_bytes segs (RDEBRUIJN + 155) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RMED_CNT.
Hypothesis ROM_reservedZ : QGeV.reservedZ segs = ref_reserved.
Hypothesis LAY_ref_reserved : ref_reserved = (cons (0x10000, gw_RTEXT_LO - 0x10000) (cons (gw_RTEXT_LO, RDATA_LO - gw_RTEXT_LO) (cons (RDATA_LO, gw_RDATA2_LO - RDATA_LO) (cons (gw_RDATA2_LO, RIMG_HI - gw_RDATA2_LO) nil))))%Z.
Hypothesis AL_rerrno_loc_entry : gw_al rerrno_loc_entry 4.
Hypothesis AL_rvm_wait_entry : gw_al rvm_wait_entry 4.
Hypothesis AL_rlock_entry : gw_al rlock_entry 4.
Hypothesis AL_runlock_entry : gw_al runlock_entry 4.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Definition rrepfoot : ltac:(gw_rebind_ty (@QDXD.Mq2.rrepfoot RATP RGOT_SSP) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QDXD.Mq2.rrepfoot RATP RGOT_SSP) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@QkTt.Mq3.rrepfoot RATP RGOT_SSP) (@rrepfoot) (gw_ent (@QDXD.Mq2.rrepfoot RATP RGOT_SSP) (@rrepfoot) gw_tbl_0)).
Definition rentry_post : ltac:(gw_rebind_ty (@Qy8Z.Mq8.rentry_post segs base RATP RDEBRUIJN) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Qy8Z.Mq8.rentry_post segs base RATP RDEBRUIJN) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@Qy8Z.Mq8.rentry_post segs base RATP RDEBRUIJN) (@rentry_post) gw_tbl_1).
Definition rentry_big_post : ltac:(gw_rebind_ty (@Qy8Z.Mq8.rentry_big_post segs base RATP) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Qy8Z.Mq8.rentry_big_post segs base RATP) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@Qy8Z.Mq8.rentry_big_post segs base RATP) (@rentry_big_post) gw_tbl_2).
Definition rentry_ovf_post : ltac:(gw_rebind_ty (@Qy8Z.Mq8.rentry_ovf_post segs) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Qy8Z.Mq8.rentry_ovf_post segs) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@Qy8Z.Mq8.rentry_ovf_post segs) (@rentry_ovf_post) gw_tbl_3).
Definition runlock_post : ltac:(gw_rebind_ty (@QCa8.Mq4.runlock_post segs) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@QCa8.Mq4.runlock_post segs) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@Q8l1.Mq8.runlock_post segs) (@runlock_post) (gw_ent (@Qy8Z.Mq7.runlock_post segs) (@runlock_post) (gw_ent (@QCa8.Mq4.runlock_post segs) (@runlock_post) gw_tbl_4))).
Definition rauxv_ok : ltac:(gw_rebind_ty (@QCa8.Mq5.rauxv_ok segs RATP RC__) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rauxv_ok segs RATP RC__) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@Q8l1.Mq8.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QQRC.Mq8.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@Qy8Z.Mq1.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QDXD.Mq1.rauxv_ok segs RATP RC__) (@rauxv_ok) (gw_ent (@QCa8.Mq5.rauxv_ok segs RATP RC__) (@rauxv_ok) gw_tbl_5))))).
Definition ralloc_fp : ltac:(gw_rebind_ty (@QCa8.Mq5.ralloc_fp RATP) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@QCa8.Mq5.ralloc_fp RATP) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@Q8l1.Mq8.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@QQRC.Mq8.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@Qy8Z.Mq1.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@QkTt.Mq5.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@QCa8.Mq5.ralloc_fp RATP) (@ralloc_fp) gw_tbl_6))))).
Definition rmalloc_fp : ltac:(gw_rebind_ty (@QkTt.Mq5.rmalloc_fp RATP RC__) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@QkTt.Mq5.rmalloc_fp RATP RC__) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@Q8l1.Mq8.rmalloc_fp RATP RC__) (@rmalloc_fp) (gw_ent (@QQRC.Mq8.rmalloc_fp RATP RC__) (@rmalloc_fp) (gw_ent (@Qy8Z.Mq1.rmalloc_fp RATP RC__) (@rmalloc_fp) (gw_ent (@QkTt.Mq5.rmalloc_fp RATP RC__) (@rmalloc_fp) gw_tbl_7)))).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@Q8l1.Mq8.rarea_rep segs) (@rarea_rep) (gw_ent (@QQRC.Mq8.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq7.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_8))))))))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@Q8l1.Mq8.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QQRC.Mq8.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq7.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_9))))))))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@Q8l1.Mq8.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QQRC.Mq8.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq7.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_10))))))))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_11)).
Notation gw_tbl_12 := (gw_ent (@Q8l1.Mq8.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QQRC.Mq8.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq7.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_11))))))))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_12)).
Notation gw_tbl_13 := (gw_ent (@Q8l1.Mq8.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QQRC.Mq8.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq7.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_12))))))))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_13)).
Notation gw_tbl_14 := (gw_ent (@Q8l1.Mq8.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QQRC.Mq8.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq7.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_13))))))))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_14)).
Notation gw_tbl_15 := (gw_ent (@Q8l1.Mq8.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QQRC.Mq8.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq7.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_14))))))))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_15)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_15)).
Notation gw_tbl_16 := (gw_ent (@Q8l1.Mq8.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QQRC.Mq8.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq7.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_15))))))))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_16)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_16)).
Notation gw_tbl_17 := (gw_ent (@Q8l1.Mq8.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QQRC.Mq8.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq7.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_16))))))))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_17)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_17)).
Notation gw_tbl_18 := (gw_ent (@Q8l1.Mq8.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QQRC.Mq8.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq7.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_17))))))))))).
Definition rpres_except : ltac:(gw_rebind_ty (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_18)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_18)).
Notation gw_tbl_19 := (gw_ent (@Q8l1.Mq8.rpres_except segs) (@rpres_except) (gw_ent (@QQRC.Mq8.rpres_except segs) (@rpres_except) (gw_ent (@Qy8Z.Mq1.rpres_except segs) (@rpres_except) (gw_ent (@Qy8Z.Mq7.rpres_except segs) (@rpres_except) (gw_ent (@QkTt.Mq5.rpres_except segs) (@rpres_except) (gw_ent (@QDXD.Mq1.rpres_except segs) (@rpres_except) (gw_ent (@QkTt.Mq3.rpres_except segs) (@rpres_except) (gw_ent (@QDXD.Mq2.rpres_except segs) (@rpres_except) (gw_ent (@QCa8.Mq5.rpres_except segs) (@rpres_except) gw_tbl_18))))))))).
Definition ras_post : ltac:(gw_rebind_ty (@Qy8Z.Mq1.ras_post segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_19)) := ltac:(gw_rebind_tm (@Qy8Z.Mq1.ras_post segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_19)).
Notation gw_tbl_20 := (gw_ent (@Q8l1.Mq8.ras_post segs RATP RGOT_SSP ref_reserved RC__) (@ras_post) (gw_ent (@Qy8Z.Mq1.ras_post segs RATP RGOT_SSP ref_reserved RC__) (@ras_post) gw_tbl_19)).
Definition rimplT : ltac:(gw_rebind_ty (@QCa8.Mq5.rimplT segs RC__) constr:(gw_tbl_20)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rimplT segs RC__) constr:(gw_tbl_20)).
#[global] Arguments rimplT {R}%_type_scope o t s Q%_function_scope ms.
Notation gw_tbl_21 := (gw_ent (@Q8l1.Mq8.rimplT segs RC__) (@rimplT) (gw_ent (@QQRC.Mq8.rimplT segs RC__) (@rimplT) (gw_ent (@Qy8Z.Mq1.rimplT segs RC__) (@rimplT) (gw_ent (@Qy8Z.Mq7.rimplT segs RC__) (@rimplT) (gw_ent (@QkTt.Mq3.rimplT segs RC__) (@rimplT) (gw_ent (@QCa8.Mq5.rimplT segs RC__) (@rimplT) gw_tbl_20)))))).
Definition ralloc_slot_stmt : ltac:(gw_rebind_ty (@Qy8Z.Mq1.ralloc_slot_stmt segs RATP RGOT_SSP ref_reserved ralloc_slot_entry RC__) constr:(gw_tbl_21)) := ltac:(gw_rebind_tm (@Qy8Z.Mq1.ralloc_slot_stmt segs RATP RGOT_SSP ref_reserved ralloc_slot_entry RC__) constr:(gw_tbl_21)).
Notation gw_tbl_22 := (gw_ent (@Q8l1.Mq8.ralloc_slot_stmt segs base RATP RGOT_SSP ref_reserved RC__) (@ralloc_slot_stmt) (gw_ent (@Qy8Z.Mq1.ralloc_slot_stmt segs RATP RGOT_SSP ref_reserved ralloc_slot_entry RC__) (@ralloc_slot_stmt) gw_tbl_21)).
Definition renf_hyp : ltac:(gw_rebind_ty (@QQRC.Mq8.renf_hyp segs base RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_22)) := ltac:(gw_rebind_tm (@QQRC.Mq8.renf_hyp segs base RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_22)).
#[global] Arguments renf_hyp {R}%_type_scope K%_function_scope o m0 st s Q%_function_scope ra%_bv_scope sp%_bv_scope gp%_bv_scope tp%_bv_scope s5%_bv_scope s6%_bv_scope s7%_bv_scope s8%_bv_scope s9%_bv_scope s10%_bv_scope s11%_bv_scope s0v%_bv_scope s1v%_bv_scope s2v%_bv_scope s3v%_bv_scope s4v%_bv_scope F fc%_bv_scope n%_Z_scope lo%_Z_scope.
Notation gw_tbl_23 := (gw_ent (@Q8l1.Mq8.renf_hyp segs base RATP RGOT_SSP ref_reserved RC__) (@renf_hyp) (gw_ent (@QQRC.Mq8.renf_hyp segs base RATP RGOT_SSP ref_reserved RC__) (@renf_hyp) gw_tbl_22)).
Definition rfail_hyp : ltac:(gw_rebind_ty (@QQRC.Mq8.rfail_hyp segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_23)) := ltac:(gw_rebind_tm (@QQRC.Mq8.rfail_hyp segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_23)).
#[global] Arguments rfail_hyp {R}%_type_scope K%_function_scope o m0 st s Q%_function_scope ra%_bv_scope sp%_bv_scope gp%_bv_scope tp%_bv_scope s5%_bv_scope s6%_bv_scope s7%_bv_scope s8%_bv_scope s9%_bv_scope s10%_bv_scope s11%_bv_scope s0v%_bv_scope s1v%_bv_scope s2v%_bv_scope s3v%_bv_scope s4v%_bv_scope F fc%_bv_scope lo%_Z_scope.
Notation gw_tbl_24 := (gw_ent (@Q8l1.Mq8.rfail_hyp segs RATP RGOT_SSP ref_reserved RC__) (@rfail_hyp) (gw_ent (@QQRC.Mq8.rfail_hyp segs RATP RGOT_SSP ref_reserved RC__) (@rfail_hyp) gw_tbl_23)).
Hypothesis runlock_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QCa8.Mq4.gw_all) (@QCa8.Mq4.runlock_spec) (base + -1984)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_24))) in let T := gw_fold_pcs T base (-1984)%Z [0; 244]%Z in exact T).

Definition rreserved_disjoint : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rreserved_disjoint) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rreserved_disjoint)).
Definition rarea_conc : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rarea_conc) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rarea_conc)).
Definition rgroup_conc : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rgroup_conc) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rgroup_conc)).
Definition rmrep_transport_high : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_transport_high) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_transport_high)).
Definition rmrep_set_tick : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_set_tick) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_set_tick)).

Definition rimplT_ret : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_ret) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_ret)).
#[global] Arguments rimplT_ret {R}%_type_scope o r s Q%_function_scope ms _.
Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.
Definition rauxv_ok_frame : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rauxv_ok_frame) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rauxv_ok_frame)).
Definition rpres_except_of_munch : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_of_munch) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_of_munch)).
Ltac riprefixT := apply rimplT_from_evt.

Definition rmrep_transport_unowned : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_transport_unowned) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_transport_unowned)).

Definition rregion_facts : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq5.rregion_facts) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq5.rregion_facts)).
Notation RMFACTS := (@MFACTS_g ref_reserved).

Definition rmalloc_entry_walk : ltac:(gw_ctx_fold_ty2 (@Qy8Z.Mq8.rmalloc_entry_walk) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@Qy8Z.Mq8.rmalloc_entry_walk)).
Definition rentry_big_walk : ltac:(gw_ctx_fold_ty2 (@Qy8Z.Mq8.rentry_big_walk) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@Qy8Z.Mq8.rentry_big_walk)).
Definition rentry_ovf_walk : ltac:(gw_ctx_fold_ty2 (@Qy8Z.Mq8.rentry_ovf_walk) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@Qy8Z.Mq8.rentry_ovf_walk)).

Definition rmalloc_small_implT : ltac:(gw_ctx_fold_ty2 (@Q8l1.Mq8.rmalloc_small_implT) constr:(gw_tbl_24)) := ltac:(gw_ctx_fold_tm2 (@Q8l1.Mq8.rmalloc_small_implT)).
#[global] Arguments rmalloc_small_implT {R}%_type_scope K%_function_scope bail o m0 st LB%_list_scope s Q%_function_scope ra%_bv_scope sp%_bv_scope gp%_bv_scope tp%_bv_scope s5%_bv_scope s6%_bv_scope s7%_bv_scope s8%_bv_scope s9%_bv_scope s10%_bv_scope s11%_bv_scope s0v%_bv_scope s1v%_bv_scope s2v%_bv_scope s3v%_bv_scope s4v%_bv_scope F fc%_bv_scope n%_Z_scope lo%_Z_scope t%_N_scope as_pre%_function_scope as_inv%_function_scope RAS HENF HFAIL MF MR0 TP CLO LO N0 NT BL m1 errv%_bv_scope t0%_bv_scope t1%_bv_scope t2%_bv_scope a0%_bv_scope a1%_bv_scope a2%_bv_scope a3%_bv_scope a4%_bv_scope a5%_bv_scope a6%_bv_scope a7%_bv_scope s2r%_bv_scope t3%_bv_scope t4%_bv_scope t5%_bv_scope t6%_bv_scope ra'%_bv_scope sc%_Z_scope _ _ _ _%_function_scope _ _ _ _ _ _ _ _ _.
Ltac mem_after_store ::=
lazymatch goal with
| |- evt ?segs_ ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
let c' := cell_of_bytes bs in
let n := eval cbv in (csize c') in
lazymatch goal with
| H : rw_cells segs_ m A ?cs0 |- _ =>
split_for_access H segs_ m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
let HB := fresh "HB" in
pose proof (rw_cells_bound segs_ m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
try lazymatch goal with
| HI : mem_inv segs_ m |- _ =>
apply (mem_inv_store_cbytes segs_ m (wa (A + Z.of_nat kn)) c') in HI;
[ | exact I | apply (rw_cells_store_ok segs_ m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
end;
change bs with (cbytes c');
let H' := fresh "CH" in
pose proof (rw_cells_write segs_ m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
clear H;
cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
transport_chunks segs_ m (A + Z.of_nat kn)%Z (cbytes c');
footprint_after_store segs_ m (A + Z.of_nat kn)%Z (cbytes c');
let m' := fresh "m" in
let E := fresh "EQ" m' in
remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:E;
clear HB; try rename H' into H
end
end
end.
Ltac mem_after_store ::=
lazymatch goal with
| |- evt ?segs_ ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
let c' := cell_of_bytes bs in
let n := eval cbv in (csize c') in
lazymatch goal with
| H : rw_cells segs_ m A ?cs0 |- _ =>
split_for_access H segs_ m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
let HB := fresh "HB" in
pose proof (rw_cells_bound segs_ m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
try lazymatch goal with
| HI : mem_inv segs_ m |- _ =>
apply (mem_inv_store_cbytes segs_ m (wa (A + Z.of_nat kn)) c') in HI;
[ | exact I | apply (rw_cells_store_ok segs_ m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
end;
change bs with (cbytes c');
let H' := fresh "CH" in
pose proof (rw_cells_write segs_ m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
clear H;
cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
transport_chunks segs_ m (A + Z.of_nat kn)%Z (cbytes c');
footprint_after_store segs_ m (A + Z.of_nat kn)%Z (cbytes c');
let m' := fresh "m" in
remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm;
clear Heqm; clear HB; try clear m; try rename H' into H
end
end
end.

#[using="RDEBRUIJN rerrno_loc_entry rmmap_entry rmunmap_entry rlock_entry runlock_entry RATP RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved rvm_wait_entry CODE BASE4 BASER D_11 E_11 D_26 E_26 D_27 E_27 D_37 E_37 D_40 E_40 D_41 E_41 D_43 E_43 D_44 E_44 D_45 E_45 D_57 E_57 D_59 E_59 D_85 E_85 D_90 E_90 D_125 E_125 D_126 E_126 D_128 E_128 D_129 E_129 D_130 E_130 D_147 E_147 D_148 E_148 D_149 E_149 D_152 E_152 D_203 E_203 D_216 E_216 D_217 E_217 D_218 E_218 ANCH_27 ANCH_41 ANCH_44 ANCH_59 ANCH_90 ANCH_126 ANCH_129 ANCH_148 ANCH_217 LINK_11 LINK_37 LINK_45 LINK_130 LINK_149 LINK_152 LINK_203 LINK_218 CODE_rerrno_loc_entry AL_rerrno_loc_entry_b4 RNG_rerrno_loc_entry_code RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rerrno_loc_entry AL_rvm_wait_entry AL_rlock_entry AL_runlock_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ rmalloc_entry ralloc_slot_entry rmmap_entry rmunmap_entry runlock_spec"] Lemma gw_all : True. Proof. exact I. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Notation RAREACH := (AREACH_from ref_reserved rc_secret).
Section RC__1.

Definition rcoreQ (o m0 : mem) (st : mstate) (s : PState)
(ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z)
(res : mstate * option (aptr * Z)) (s' : PState) (ms' : machine_state) : Prop :=
match res with
| (st2, Some (g, idx)) =>
exists (b : aptr) (r : region) (m1 : mem) (errv : word) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 ra' : word),
ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 (RATP + 131960))
a0 a1 a2 a3 a4 a5 a6 a7 (pw st2 (Some g)) (wz idx) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x324)) fc None m1 (seg_rom segs)
/\ rmrep st2 m1 /\ ticks_ok st2 /\ unk_agree st2 o m1 /\ mem_inv segs m1
/\ stk segs m1 lo (bv_unsigned sp + -48)
/\ rw_cells segs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra]
/\ rw_cells segs m1 (errno_addr tp) [C4 errv] /\ rauxv_ok m1 (bv_unsigned sp)
/\ rpres_except (rmalloc_fp st st2 lo (bv_unsigned sp)) m0 m1
/\ (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx - 4 <= a
< r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx + get_stride (get_meta_rec st2 g) - 4 ->
rmalloc_fp st st2 lo (bv_unsigned sp) a)
/\ 0 <= c_mmap_counter (ctx st2) < 2^32
/\ slot_ok st2 g b r idx n
/\ (expo_cond st n -> rdv pans_mem o st2 (fst b, snd b + (16 + get_stride (get_meta_rec st2 g) * idx) + -3) = 0)
/\ mrel st st2 /\ brk_link_ps st2 s' /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
| (st2, None) =>
exists (m1 : mem) (errv : word) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0v s1v (wz 0) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m1 (seg_rom segs)
/\ rmrep st2 m1 /\ ticks_ok st2 /\ mem_inv segs m1 /\ stk segs m1 lo (bv_unsigned sp)
/\ rw_cells segs m1 (errno_addr tp) [C4 errv] /\ rauxv_ok m1 (bv_unsigned sp)
/\ rpres_except (rmalloc_fp st st2 lo (bv_unsigned sp)) m0 m1
/\ mrel st st2 /\ brk_link_ps st2 s' /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
/\ errv = Z_to_bv 64 12
end.

#[using="Type"] Lemma renf_hyp_ret o m0 st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo :
renf_hyp (fun st1 r => ret (st1, r)) o m0 st s (rcoreQ o m0 st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo)
ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo.
Proof. clear - o m0 st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo RATP. gw_expose_fam RATP.
intros st2 g b r idx m1 s' errv t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 ra'; intros.
apply rimplT_ret. apply evt_done. cbn [rcoreQ].
exists b, r, m1, errv. do 17 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
Qed.

#[using="Type"] Lemma rfail_hyp_ret o m0 st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo :
rfail_hyp (fun st1 r => ret (st1, r)) o m0 st s (rcoreQ o m0 st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo)
ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc lo.
Proof. clear - o m0 st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo RATP. gw_expose_fam RATP.
intros st2 m1 s' errv t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6; intros.
apply rimplT_ret. apply evt_done. cbn [rcoreQ].
exists m1, errv. do 14 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
Qed.

Definition rbig_stmt : Prop :=
forall (o m0 : mem) (st : mstate) (LB : list block) (s : PState)
(ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (t : N)
(m1 : mem) (errv : word) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2r s3r s4r t3 t4 t5 t6 ra' : word),
let st1 := set_tick t st in
RAREACH st LB -> RMFACTS st LB -> rmrep st m0 -> tp = Z_to_bv 64 RATP ->
alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 - RAM_STACK -> MMAP_THRESHOLD <= n < 2^63 - 4097 -> brk_link_ps st s ->
rmrep st1 m1 -> ticks_ok st1 -> unk_agree st1 o m1 -> mem_inv segs m1 ->
stk segs m1 lo (bv_unsigned sp + -48) ->
rw_cells segs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
rw_cells segs m1 (errno_addr tp) [C4 errv] -> rauxv_ok m1 (bv_unsigned sp) ->
rpres_except (rmalloc_fp st st1 lo (bv_unsigned sp)) m0 m1 ->
rimplT o (malloc_core full_lay st1 n) s (rcoreQ o m0 st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo)
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 (RATP + 131960)) (Z_to_bv 64 131052) a1 a2 a3 a4 a5 a6 a7
s2r s3r s4r s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x74)) fc None m1 (seg_rom segs)).

#[using="base RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved rmalloc_entry ralloc_slot_entry rmmap_entry rmunmap_entry"] Lemma rrepfoot_low_core stY a : rregions_wf stY -> rrepfoot stY a -> a < alloc_ceiling /\ ~ ((RATP + -164) <= a < (RATP + -164 + 4)).
Proof. clear - base RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved rmalloc_entry ralloc_slot_entry rmmap_entry rmunmap_entry RATP stY a RGOT_SSP. gw_expose_fam RATP; gw_expose_fam RGOT_SSP.
intros WF H. pose proof WF as (_ & WR & _ & WA & WG). unfold alloc_ceiling.
destruct H as [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]]; (gw_expose_fam RATP; gw_expose_fam RGOT_SSP); try lia.
- destruct C as (ak & ar & Hak & Hin). destruct (rarea_conc stY ak ar WF Hak) as (rra & Hra & Ca & Sa0 & Sa1 & SaL & NKa & RB0 & RBAL & RBC).
destruct (WR _ _ Hra) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as (D1 & _ & D23 & D2). unfold alloc_ceiling in RBC. lia.
- destruct C as (b & gh & Hb & Hin). destruct (rgroup_conc stY b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & Al & RB0 & RBC).
destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as (D1 & _ & D23 & D2). unfold alloc_ceiling in RBC. lia.
- destruct C as (rid & rg & v & Hrg & Krg & Hin & _). destruct (WR _ _ Hrg) as (_ & _ & _ & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (D1 & _ & D23 & D2). unfold alloc_ceiling in RBC. lia.
Qed.

Section CORE.
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis RAS : ralloc_slot_stmt as_pre as_inv.
Hypothesis AS_PRE : forall st LB t sc n, RAREACH st LB -> RMFACTS st LB -> (s_tick st < t)%N -> 0 <= sc < 48 -> 0 <= n < 2^32 ->
n + 4 <= 16 * size_class sc -> as_pre st (set_tick t st) sc n FUEL.
Hypothesis RBIG : rbig_stmt.

#[using="RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rerrno_loc_entry rvm_wait_entry runlock_entry w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 hi_26 hi_57 hi_85 hi_125 hi_216 lo_27 lo_59 lo_90 lo_126 lo_217 joff_11 joff_218 CODE BASE4 BASER D_11 E_11 D_26 E_26 D_27 E_27 D_57 E_57 D_59 E_59 D_85 E_85 D_90 E_90 D_125 E_125 D_126 E_126 D_216 E_216 D_217 E_217 D_218 E_218 ANCH_27 ANCH_59 ANCH_90 ANCH_126 ANCH_217 LINK_11 LINK_218 CODE_rerrno_loc_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_reservedZ LAY_ref_reserved runlock_spec rmalloc_entry ralloc_slot_entry rmmap_entry rmunmap_entry as_pre as_inv RAS AS_PRE RBIG"] Lemma rmalloc_core_implT :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(m : mem) (st : mstate) (LB : list block) (s : PState) (n lo : Z) (errv : word) (t : N),
RAREACH st LB -> RMFACTS st LB -> rmrep st m -> brk_link_ps st s ->
rauxv_ok m (bv_unsigned sp) ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 8192 ->
rw_cells segs m (errno_addr tp) [C4 errv] -> mem_inv segs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 n -> 0 <= n < 2^64 -> (s_tick st < t)%N ->
rimplT m (malloc_core full_lay (set_tick t st) n) s
(rcoreQ m m st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom segs)).
Proof. clear - RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rerrno_loc_entry rvm_wait_entry runlock_entry w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 hi_26 hi_57 hi_85 hi_125 hi_216 lo_27 lo_59 lo_90 lo_126 lo_217 joff_11 joff_218 CODE BASE4 BASER D_11 E_11 D_26 E_26 D_27 E_27 D_57 E_57 D_59 E_59 D_85 E_85 D_90 E_90 D_125 E_125 D_126 E_126 D_216 E_216 D_217 E_217 D_218 E_218 ANCH_27 ANCH_59 ANCH_90 ANCH_126 ANCH_217 LINK_11 LINK_218 CODE_rerrno_loc_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_reservedZ LAY_ref_reserved runlock_spec rmalloc_entry ralloc_slot_entry rmmap_entry rmunmap_entry as_pre as_inv RAS AS_PRE RBIG segs RATP. gw_expose_fam RATP.
intros until t. intros AR MF MR BL AUX ST CLO LO ERR MI TP HA N TT.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (RAS_STACK_ge 0) as ASG.
assert (RB0 : forall rid r1, (s_regions st) !! rid = Some r1 -> 0 <= r_base r1 /\ r_base r1 + round_up_pg (r_len r1) <= alloc_ceiling).
{ intros rid r1 H1. pose proof (rregion_facts st m rid r1 MR H1) as (X1 & _ & X2 & _). unfold alloc_ceiling in X2. lia. }
pose proof MR as (WF0 & CX0 & GL0 & _). destruct GL0 as (_ & NL & _).
assert (PREP : forall m1, munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m1 -> wmono segs m m1 ->
rmrep (set_tick t st) m1 /\ ticks_ok (set_tick t st) /\ unk_agree (set_tick t st) m m1
/\ rw_cells segs m1 (errno_addr tp) [C4 errv] /\ rauxv_ok m1 (bv_unsigned sp)
/\ rpres_except (rmalloc_fp st (set_tick t st) lo (bv_unsigned sp)) m m1).
{ intros m1 MU WM. unfold alloc_ceiling in CLO.
split. { apply rmrep_set_tick. eapply rmrep_transport_high; [gw_exact MR| gw_exact MU| gw_exact WM| intros lo' hi' [E|[]]; inversion E; unfold alloc_ceiling; lia]. }
split. { apply ticks_ok_set_tick; [lia|]. exact (mf_ticks _ _ MF). }
split. { eapply unk_agree_munch; [| gw_exact MU| |].
- eapply unk_agree_ext; [apply unk_agree_refl| reflexivity| intros; reflexivity| reflexivity].
- intros rid r1 H1 K1. pose proof (RB0 rid r1 H1). cbn. lia.
- intros rid r1 H1. pose proof (RB0 rid r1 H1). lia. }
split. { eapply rw_cells_transport; [gw_exact ERR| gw_exact MU| gw_exact WM|]. subst tp. gw_expose_fam RATP. rewrite unsigned_lit by lia. cbn. lia. }
split. { eapply rauxv_ok_frame; [gw_exact AUX| gw_exact MU| gw_exact WM|]. gw_expose_fam RATP. constructor; [cbn; lia| constructor]. }
eapply rpres_except_of_munch; [gw_exact MU| gw_exact WM|]. intros a Ha NC. cbn. split; [|exact I]. intros HX. apply NC. left. left. lia. }
assert (ETP : bv_unsigned tp + -164 = (RATP + -164)) by (rewrite TP; gw_expose_fam RATP; rewrite unsigned_lit by lia; first [reflexivity | lia]).
destruct (Z.le_gt_cases (2^63 - 4097) n) as [OV|NOV].
{
unfold malloc_core.
replace (size_overflows n) with true by (symmetry; unfold size_overflows; apply Z.leb_le; lia).
riprefixT. eapply evt_cut.
{ eapply (rentry_ovf_walk ra sp gp tp); [gw_exact HA| lia| gw_exact ST| unfold alloc_ceiling in CLO; lia| lia| gw_exact MI| gw_exact ERR| gw_exact TP]. }
intros ms' (a1' & m1 & -> & ST1 & MU & WM & MI1 & ERR1).
apply evt_done. apply rimplT_ret. apply evt_done. cbn [rcoreQ].
exists m1, (Z_to_bv 64 12). do 14 eexists. split; [reflexivity|].
split. { apply rmrep_set_tick. eapply (rmrep_transport_unowned st m m1 _ MR MU WM).
intros lo' hi' a Hin Ha RF. destruct (rrepfoot_low_core st a WF0 RF) as [A1 A2].
rewrite ETP in Hin. unfold alloc_ceiling in *. destruct Hin as [E|[E|[]]]; inversion E; subst; lia. }
split. { apply ticks_ok_set_tick; [lia|]. exact (mf_ticks _ _ MF). }
split; [gw_exact MI1|]. split; [gw_exact ST1|]. split; [gw_exact ERR1|].
split. { eapply rauxv_ok_frame; [gw_exact AUX| gw_exact MU| gw_exact WM|]. gw_expose_fam RATP. rewrite ETP. constructor; [cbn; unfold alloc_ceiling in CLO; lia|]. constructor; [cbn; unfold alloc_ceiling in CLO; lia| constructor]. }
split. { eapply rpres_except_of_munch; [gw_exact MU| gw_exact WM|]. intros a Ha NC. cbn. rewrite ETP. unfold alloc_ceiling in CLO. split; [|split; [|exact I]]; intros HX; apply NC; left; [left; lia| right; left]. rewrite unsigned_lit by lia. lia. }
split; [apply mrel_same; reflexivity|]. split; [gw_exact BL|]. repeat split; reflexivity. }
destruct (Z.le_gt_cases MMAP_THRESHOLD n) as [TH|TH].
-
riprefixT. eapply evt_cut.
{ eapply (rentry_big_walk ra sp gp tp); [gw_exact HA| unfold MMAP_THRESHOLD in *; lia| gw_exact ST| unfold alloc_ceiling in CLO; lia| lia| gw_exact MI]. }
intros ms' (a1' & m1 & -> & FR & ST1 & MU & WM & MI1).
destruct (PREP m1 MU WM) as (MR1 & TK1 & UA1 & ERR1 & AUX1 & PE1).
apply evt_done.
eapply (RBIG m m st LB s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo t); try eassumption.
+ unfold RAM_STACK. lia.
+ lia.
-
assert (N32 : 0 <= n < 2^32) by (unfold MMAP_THRESHOLD in TH; lia). clear N. rename N32 into N.
unfold malloc_core.
replace (size_overflows n) with false by (symmetry; unfold size_overflows; apply Z.leb_gt; lia).
replace (MMAP_THRESHOLD <=? n) with false by (symmetry; apply Z.leb_gt; lia).
riprefixT. eapply evt_cut.
{ eapply (rmalloc_entry_walk ra sp gp tp); [gw_exact HA| unfold MMAP_THRESHOLD in *; lia| gw_exact ST| unfold alloc_ceiling in CLO; lia| lia| gw_exact MI| gw_exact NL]. }
intros ms' (a0' & a1' & a2' & a3' & m1 & -> & FR & ST1 & MU & WM & MI1).
destruct (PREP m1 MU WM) as (MR1 & TK1 & UA1 & ERR1 & AUX1 & PE1).
pose proof (size_to_class_props n ltac:(lia)) as (SCR & SFIT & _).
apply evt_done.
eapply (rmalloc_small_implT (fun st1 r => ret (st1, r)) (ret (set_tick t st, None)) m m st LB s _ ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo t as_pre as_inv RAS).
all: try eassumption.
+ apply renf_hyp_ret.
+ apply rfail_hyp_ret.
+ unfold RAS_STACK. lia.
+ reflexivity.
+ intros sc' Hsc' Hfit'. eapply AS_PRE; [gw_exact AR| gw_exact MF| gw_exact TT| gw_exact Hsc'| lia| gw_exact Hfit'].
Qed.
End CORE.

End RC__1.

End G.
End Mq5.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.

Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq4 Q4J3.Mq2 QWTl.Mq4 QDUx.Mqb.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QDXD.Mq2.
Import QkTt.Mq4.
Import Qy8Z.Mq9.
Import Q8l1.Mq9.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Open Scope bv_scope.
Open Scope Z_scope.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment) (base : Z).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (w_6 w_7 w_26 w_27 w_31 w_32 w_93 w_94 w_245 : Z).
Variables (hi_6 hi_26 hi_31 hi_93 : bv 20).
Variables (lo_7 lo_27 lo_32 lo_94 : bv 12).
Variables (joff_245 : bv 21).
Variables (e_197bc : Z).
Hypothesis CODE : code_at segs base (ntf_code w_6 w_7 w_26 w_27 w_31 w_32 w_93 w_94 w_245).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 984.
Hypothesis D_6 : decode_any (Z_to_bv 32 w_6) = Some (Auipc 12 hi_6, 4%Z).
Hypothesis E_6 : is_ecall (Z_to_bv 32 w_6) = false.
Hypothesis D_7 : decode_any (Z_to_bv 32 w_7) = Some (Load SZ8 true 9 12 lo_7, 4%Z).
Hypothesis E_7 : is_ecall (Z_to_bv 32 w_7) = false.
Hypothesis D_26 : decode_any (Z_to_bv 32 w_26) = Some (Auipc 16 hi_26, 4%Z).
Hypothesis E_26 : is_ecall (Z_to_bv 32 w_26) = false.
Hypothesis D_27 : decode_any (Z_to_bv 32 w_27) = Some (OpImm ALU_ADD 18 16 lo_27, 4%Z).
Hypothesis E_27 : is_ecall (Z_to_bv 32 w_27) = false.
Hypothesis D_31 : decode_any (Z_to_bv 32 w_31) = Some (Auipc 16 hi_31, 4%Z).
Hypothesis E_31 : is_ecall (Z_to_bv 32 w_31) = false.
Hypothesis D_32 : decode_any (Z_to_bv 32 w_32) = Some (OpImm ALU_ADD 16 16 lo_32, 4%Z).
Hypothesis E_32 : is_ecall (Z_to_bv 32 w_32) = false.
Hypothesis D_93 : decode_any (Z_to_bv 32 w_93) = Some (Auipc 13 hi_93, 4%Z).
Hypothesis E_93 : is_ecall (Z_to_bv 32 w_93) = false.
Hypothesis D_94 : decode_any (Z_to_bv 32 w_94) = Some (OpImm ALU_ADD 13 13 lo_94, 4%Z).
Hypothesis E_94 : is_ecall (Z_to_bv 32 w_94) = false.
Hypothesis D_245 : decode_any (Z_to_bv 32 w_245) = Some (Jal 1 joff_245, 4%Z).
Hypothesis E_245 : is_ecall (Z_to_bv 32 w_245) = false.
Hypothesis ANCH_7 : gw_anch (Z.shiftl (bv_signed hi_6) 12 + (base + 24) + bv_signed lo_7)%Z RGOT_SSP.
Hypothesis ANCH_27 : gw_anch (Z.shiftl (bv_signed hi_26) 12 + (base + 104) + bv_signed lo_27)%Z (RATP + 131968).
Hypothesis ANCH_32 : gw_anch (Z.shiftl (bv_signed hi_31) 12 + (base + 124) + bv_signed lo_32)%Z (RDEBRUIJN + 32).
Hypothesis ANCH_94 : gw_anch (Z.shiftl (bv_signed hi_93) 12 + (base + 372) + bv_signed lo_94)%Z (RATP + 131968).
Hypothesis LINK_245 : gw_anch (base + 980 + bv_signed joff_245)%Z (e_197bc + 0)%Z.
Hypothesis RNG_RATP : gw_br RATP 1896.
Hypothesis LAY_lo_RATP : gw_le (gw_RDATA2_LO + 164) RATP.
Hypothesis LAY_hi_RATP : gw_le ((RATP + 132896)) RIMG_HI.
Hypothesis AL_RATP : gw_al RATP 8.
Hypothesis RNG_RDEBRUIJN : gw_br RDEBRUIJN 159.
Hypothesis LAY_lo_RDEBRUIJN : gw_le (0x10000 + 0) RDEBRUIJN.
Hypothesis LAY_hi_RDEBRUIJN : gw_le ((RDEBRUIJN + 159)) gw_RTEXT_LO.
Hypothesis AL_RDEBRUIJN : gw_al RDEBRUIJN 8.
Hypothesis RNG_RGOT_SSP : gw_br RGOT_SSP 8.
Hypothesis LAY_lo_RGOT_SSP : gw_le (RDATA_LO + 0) RGOT_SSP.
Hypothesis LAY_hi_RGOT_SSP : gw_le ((RGOT_SSP + 8)) gw_RDATA2_LO.
Hypothesis AL_RGOT_SSP : gw_al RGOT_SSP 8.
Hypothesis LAY_win_0 : gw_win (0x10000 + 1) gw_RTEXT_LO.
Hypothesis LAY_win_1 : gw_win (gw_RTEXT_LO + 1) RDATA_LO.
Hypothesis LAY_win_2 : gw_win (RDATA_LO + 1) gw_RDATA2_LO.
Hypothesis LAY_win_3 : gw_win (gw_RDATA2_LO + 1) RIMG_HI.
Hypothesis LAY_win_4 : gw_win RIMG_HI 0x1000000.
Hypothesis AL_win_RIMG_HI : gw_winal RIMG_HI 4096.
Hypothesis AL_win_RDATA_LO : gw_winal RDATA_LO 4096.
Hypothesis AL_win_gw_RTEXT_LO : gw_winal gw_RTEXT_LO 4096.
Hypothesis AL_win_gw_RDATA2_LO : gw_winal gw_RDATA2_LO 4096.
Hypothesis ROM_RSIZE_CLASSES : QZDE.ro_bytes segs (RDEBRUIJN + 32) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RSIZE_CLASSES.
Hypothesis ROM_RDEBRUIJN : QZDE.ro_bytes segs RDEBRUIJN OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RDEBRUIJN.
Hypothesis ROM_RSMALL_CNT : QZDE.ro_bytes segs (RDEBRUIJN + 128) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RSMALL_CNT.
Hypothesis ROM_RMED_CNT : QZDE.ro_bytes segs (RDEBRUIJN + 155) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RMED_CNT.
Hypothesis ROM_reservedZ : QGeV.reservedZ segs = ref_reserved.
Hypothesis LAY_ref_reserved : ref_reserved = (cons (0x10000, gw_RTEXT_LO - 0x10000) (cons (gw_RTEXT_LO, RDATA_LO - gw_RTEXT_LO) (cons (RDATA_LO, gw_RDATA2_LO - RDATA_LO) (cons (gw_RDATA2_LO, RIMG_HI - gw_RDATA2_LO) nil))))%Z.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Definition rfree_fp : ltac:(gw_rebind_ty (@QDXD.Mq2.rfree_fp RATP) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QDXD.Mq2.rfree_fp RATP) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@Q8l1.Mq9.rfree_fp RATP) (@rfree_fp) (gw_ent (@Qy8Z.Mq9.rfree_fp RATP) (@rfree_fp) (gw_ent (@QDXD.Mq2.rfree_fp RATP) (@rfree_fp) gw_tbl_0))).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@Q8l1.Mq9.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq9.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_1)))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@Q8l1.Mq9.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq9.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_2)))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@Q8l1.Mq9.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq9.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_3)))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@Q8l1.Mq9.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq9.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_4)))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@Q8l1.Mq9.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq9.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_5)))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@Q8l1.Mq9.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq9.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_6)))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@Q8l1.Mq9.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq9.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_7)))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@Q8l1.Mq9.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq9.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_8)))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@Q8l1.Mq9.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq9.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_9)))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@Q8l1.Mq9.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq9.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_10)))))).
Definition rpres_except : ltac:(gw_rebind_ty (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_11)).
Notation gw_tbl_12 := (gw_ent (@Q8l1.Mq9.rpres_except segs) (@rpres_except) (gw_ent (@Qy8Z.Mq9.rpres_except segs) (@rpres_except) (gw_ent (@QDXD.Mq2.rpres_except segs) (@rpres_except) (gw_ent (@QCa8.Mq5.rpres_except segs) (@rpres_except) gw_tbl_11)))).

Definition rmrep_meta_chunk : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_meta_chunk) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_meta_chunk)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.
Definition rpres_except_refl : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_refl) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_refl)).

Definition rmrep_put_meta_frame : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_put_meta_frame) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_put_meta_frame)).
Definition rmrep_usage_read : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_usage_read) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_usage_read)).
Definition rmeta_slot_bounds : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmeta_slot_bounds) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmeta_slot_bounds)).
Definition rfree_fp_stack : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rfree_fp_stack) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rfree_fp_stack)).
Definition rfree_fp_ctx : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rfree_fp_ctx) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rfree_fp_ctx)).
Definition rpres_except_of_munch_cov : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rpres_except_of_munch_cov) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rpres_except_of_munch_cov)).

Definition rmrep_set_usage : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq4.rmrep_set_usage) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq4.rmrep_set_usage)).

Ltac rmeta_chunk MR MSq CH :=
pose proof (rmrep_meta_chunk _ _ _ MR MSq) as CH;
rewrite ?meta_cells_put_meta in CH; unfold meta_cells in CH;
rewrite ?get_meta_rec_put_same in CH;
rewrite ?conc_put_meta, ?pw_put_meta in CH;
cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen meta_word meta0
m_set_prev m_set_next m_set_mem m_set_avail m_set_freed Z.mul Z.add] in CH;
rewrite ?meta_word_meta0 in CH; unfold pw in CH; cbn [oconc] in CH; unfold wz in CH.

Ltac rraw_store_finish A bs' FR ST MU WM SOK :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); (gw_expose_fam RATP; unfold wa); f_equal; lia);
let L := fresh "LEN" in
assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
apply (rw_cells_frame segs mX _ _ A bs') in FR; [| gw_expose_fam RATP; lia | rewrite <- L; gw_expose_fam RATP; lia | rewrite <- L; gw_expose_fam RATP; cbn [cells_size csize Nat.add]; lia];
apply (stk_write segs mX _ _ A bs') in ST; [| gw_expose_fam RATP; lia | rewrite <- L; gw_expose_fam RATP; lia];
apply (munch_write _ _ mX A bs') in MU; [| gw_expose_fam RATP; lia | rewrite <- L; gw_expose_fam RATP; lia | rewrite <- L; gw_expose_fam RATP; cbn [inside]; lia];
apply (wmono_write segs _ mX (wa A) bs') in WM;
lazymatch goal with HI : mem_inv segs mX |- _ =>
apply (mem_inv_store segs mX (wa A) bs') in HI;
[| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by ((gw_expose_fam RATP; unfold wa); f_equal; lia); exact SOK ] ]
end;
clear L SOK;
let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
end.

#[using="RGOT_SSP e_197bc RATP RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_6 E_6 D_7 E_7 D_26 E_26 D_27 E_27 D_31 E_31 D_32 E_32 D_93 E_93 D_94 E_94 D_245 E_245 ANCH_7 ANCH_27 ANCH_32 ANCH_94 LINK_245 RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__"] Lemma gw_all : True. Proof. exact I. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1.

#[using="Type"] Lemma testbit_false_ge a n : 0 <= a < 2^n -> 0 <= n -> forall k, n <= k -> Z.testbit a k = false.
Proof. clear - a n.
intros Ha Hn k Hk. destruct (Z.eq_dec a 0) as [->|NE]; [apply Z.bits_0|].
apply Z.bits_above_log2; [lia|].
assert (Z.log2 a < n) by (apply Z.log2_lt_pow2; lia). lia.
Qed.

#[using="Type"] Lemma lor_lxor_ones64 a b : 0 <= a < 2^64 -> 0 <= b < 2^64 ->
Z.lor (Z.lxor a 18446744073709551615) (Z.lxor b 18446744073709551615) = Z.lxor (Z.land a b) 18446744073709551615.
Proof. clear - a b.
intros Ha Hb. change 18446744073709551615 with (Z.ones 64).
apply Z.bits_inj'. intros n Hn. rewrite Z.lor_spec, !Z.lxor_spec, Z.land_spec.
destruct (Z.lt_ge_cases n 64) as [L|G].
- rewrite Z.ones_spec_low by lia. destruct (Z.testbit a n), (Z.testbit b n); reflexivity.
- rewrite Z.ones_spec_high by lia. rewrite (testbit_false_ge a 64), (testbit_false_ge b 64) by lia. reflexivity.
Qed.

#[using="Type"] Lemma usage_sub_word u w : 0 <= u < 2^64 -> 0 <= w < 2^64 ->
Z_to_bv 64 (u + Z.lor (bv_unsigned (Z_to_bv 64 (Z.lxor w 18446744073709551615))) 18446744073709551584)
= wz (u - (Z.land w 31 + 1)).
Proof. clear - u w.
intros Hu Hw.
assert (HX : 0 <= Z.lxor w 18446744073709551615 < 2^64) by (rewrite zb_lxor_ones by lia; lia).
rewrite unsigned_lit by lia.
change 18446744073709551584 with (Z.lxor 31 18446744073709551615).
rewrite lor_lxor_ones64 by lia.
assert (HL : 0 <= Z.land w 31 < 32).
{ split; [apply Z.land_nonneg; lia|]. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
rewrite zb_lxor_ones by lia. unfold wz.
rewrite <- (Z_to_bv_mod64 (u + _)), <- (Z_to_bv_mod64 (u - _)). f_equal.
replace (u + (18446744073709551615 - Z.land w 31)) with ((u - (Z.land w 31 + 1)) + 1 * 2^64) by lia.
rewrite Z.mod_add by lia. reflexivity.
Qed.

Definition rfg_post (ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (st : mstate) (m : word -> option byte) (st' : mstate) (g : aptr) (sc W : Z) (fr : list cell) : machine_state -> Prop :=
fun ms' => exists a3 a4 m',
ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 sc) (wz W) a3 a4 a5 a6 a7 (Z_to_bv 64 (RATP + 131968)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x25c)) fc None m' (seg_rom segs)
/\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' lo (bv_unsigned sp + -96)
/\ rw_cells segs m' (bv_unsigned sp + -96) fr
/\ rmrep st' m'.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_6 w_7 w_26 w_27 w_31 w_32 w_93 w_94 w_245 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 LAY_ref_reserved"] Lemma rntf_fg : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
(m : word -> option byte) (fr : list cell) st (g : aptr) (lo : Z),
let mr := get_meta_rec st g in
rmrep st m -> mem_inv segs m -> meta_slot st g ->
mw_ok mr ->
(m_sizeclass mr < 48 -> 0 <= usage st (m_sizeclass mr) < 2^64) ->
rw_cells segs m (bv_unsigned sp + -96) fr -> cells_size fr = 96%nat ->
stk segs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
evt segs (rfg_post ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 F fc lo st m
(fg_usage_st st g) g (m_sizeclass mr) (meta_word mr) fr)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (RATP + 131968)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x228)) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_6 w_7 w_26 w_27 w_31 w_32 w_93 w_94 w_245 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 LAY_ref_reserved segs base RATP. gw_expose_fam RATP.
intros until lo. intros mr MR MI MSL MW UR FR FRL ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st m g MR MSL) as GB.
pose proof (meta_word_range mr MW) as MWR.
pose proof MW as (LI & FB & SCR & ML).
pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
(gw_expose_fam RATP; unfold alloc_ceiling in *).
assert (MW2 : Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (meta_word mr) 52))) 58 = m_sizeclass mr).
{ rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. unfold meta_word.
replace ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr) * 2 ^ 52)
with ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) * 2^52 + m_maplen mr * 2^64) by lia.
rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
replace ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) * 2 ^ 52) with ((m_last_idx mr + 32 * m_freeable mr) * 2^52 + m_sizeclass mr * 2^58) by lia.
rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
rmeta_chunk MR MSL CH. fold mr in CH.
st1. st1. st1. rewrite MW2. st1. st1. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
-
clear CH.
unfold fg_usage_st. fold mr. replace (m_sizeclass mr <? 48) with false by (symmetry; apply Z.ltb_ge; lia).
apply evt_done. unfold rfg_post. do 3 eexists. split; [cbv delta [mkR]; gw_expose_fam RATP; reflexivity|].
split; [apply rpres_except_refl|]. split; [apply wmono_refl|]. split; [gw_exact MI|]. split; [gw_exact ST|]. split; [gw_exact FR|gw_exact MR].
- unfold fg_usage_st. fold mr. replace (m_sizeclass mr <? 48) with true by (symmetry; apply Z.ltb_lt; lia).
specialize (UR ltac:(lia)).
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); ((RATP + 131968), (RATP + 132896))]%Z m) as MU.
pose proof (wmono_refl segs m) as WM.
pose proof (rmrep_usage_read st m (m_sizeclass mr) (wa ((RATP + 132432) + 8 * m_sizeclass mr)) MR ltac:(lia) eq_refl) as RDU. gw_expose_fam RATP.
st1. rewrite ?(unsigned_lit (m_sizeclass mr)), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
st1.
replace (wa ((RATP + 132432) + 8 * m_sizeclass mr)) with (Z_to_bv 64 ((RATP + 131968) + m_sizeclass mr * 8 + 464)) in RDU by (unfold wa; f_equal; lia).
st1. clear RDU.

st1. st1. st1.
rewrite (usage_sub_word (usage st (m_sizeclass mr)) (meta_word mr)) by lia. rewrite (meta_word_last_idx mr MW).

pose proof MR as (_ & (_ & _ & USG & _) & _).
pose proof (u64arr_store_ok segs _ _ (usages st) (m_sizeclass mr) (Z_to_bv 64 ((RATP + 131968) + m_sizeclass mr * 8 + 464)) USG
ltac:(rewrite usages_length; lia) ltac:((gw_expose_fam RATP; unfold wa); f_equal; lia)) as SOK.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_usage st mX (m_sizeclass mr) (usage st (m_sizeclass mr) - (m_last_idx mr + 1)) MR ltac:(lia)) as MR2; gw_expose_fam RATP end.
clear USG.
rraw_store_finish ((RATP + 132432) + 8 * m_sizeclass mr) (le8 (wz (usage st (m_sizeclass mr) - (m_last_idx mr + 1)))) FR ST MU WM SOK.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (CH' : rw_cells segs mX (conc st g) (meta_cells st mr)) end.
{ pose proof (rmrep_meta_chunk _ _ _ MR2 (meta_slot_set_usage _ _ _ _ MSL)) as X.
rewrite conc_set_usage, rec_set_usage in X. fold mr in X.
replace (meta_cells (set_usage (m_sizeclass mr) (usage st (m_sizeclass mr) - (m_last_idx mr + 1)) st) mr) with (meta_cells st mr) in X; [gw_exact X|].
unfold meta_cells, pw. rewrite !oconc_set_usage. reflexivity. }
clear CH. unfold meta_cells in CH'.
st1. clear CH'.
apply evt_done. unfold rfg_post. do 3 eexists. split; [cbv delta [mkR]; gw_expose_fam RATP; reflexivity|].
split.
{ apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [gw_exact MU|gw_exact WM|].
cbn [ivs_covered]. repeat split; intros x Hx.
+ apply rfree_fp_stack. lia.
+ apply rfree_fp_ctx. gw_expose_fam RATP. lia. }
split; [gw_exact WM|]. split; [assumption|]. split; [gw_exact ST|]. split; [gw_exact FR|gw_exact MR2].
Qed.

End RC__1.

End G.
End Mq6.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.

Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq4 Q4J3.Mq2 Q9Ay.Mqb QDUx.Mqb.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QDXD.Mq2.
Import QkTt.Mq4.
Import Qy8Z.Mq3.
Import Qy8Z.Mq9.
Import Q8l1.Mq9.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.
Open Scope bv_scope.
Open Scope Z_scope.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment) (base : Z).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (w_6 w_7 w_26 w_27 w_31 w_32 w_93 w_94 w_245 : Z).
Variables (hi_6 hi_26 hi_31 hi_93 : bv 20).
Variables (lo_7 lo_27 lo_32 lo_94 : bv 12).
Variables (joff_245 : bv 21).
Variables (e_197bc : Z).
Hypothesis CODE : code_at segs base (ntf_code w_6 w_7 w_26 w_27 w_31 w_32 w_93 w_94 w_245).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 984.
Hypothesis D_6 : decode_any (Z_to_bv 32 w_6) = Some (Auipc 12 hi_6, 4%Z).
Hypothesis E_6 : is_ecall (Z_to_bv 32 w_6) = false.
Hypothesis D_7 : decode_any (Z_to_bv 32 w_7) = Some (Load SZ8 true 9 12 lo_7, 4%Z).
Hypothesis E_7 : is_ecall (Z_to_bv 32 w_7) = false.
Hypothesis D_26 : decode_any (Z_to_bv 32 w_26) = Some (Auipc 16 hi_26, 4%Z).
Hypothesis E_26 : is_ecall (Z_to_bv 32 w_26) = false.
Hypothesis D_27 : decode_any (Z_to_bv 32 w_27) = Some (OpImm ALU_ADD 18 16 lo_27, 4%Z).
Hypothesis E_27 : is_ecall (Z_to_bv 32 w_27) = false.
Hypothesis D_31 : decode_any (Z_to_bv 32 w_31) = Some (Auipc 16 hi_31, 4%Z).
Hypothesis E_31 : is_ecall (Z_to_bv 32 w_31) = false.
Hypothesis D_32 : decode_any (Z_to_bv 32 w_32) = Some (OpImm ALU_ADD 16 16 lo_32, 4%Z).
Hypothesis E_32 : is_ecall (Z_to_bv 32 w_32) = false.
Hypothesis D_93 : decode_any (Z_to_bv 32 w_93) = Some (Auipc 13 hi_93, 4%Z).
Hypothesis E_93 : is_ecall (Z_to_bv 32 w_93) = false.
Hypothesis D_94 : decode_any (Z_to_bv 32 w_94) = Some (OpImm ALU_ADD 13 13 lo_94, 4%Z).
Hypothesis E_94 : is_ecall (Z_to_bv 32 w_94) = false.
Hypothesis D_245 : decode_any (Z_to_bv 32 w_245) = Some (Jal 1 joff_245, 4%Z).
Hypothesis E_245 : is_ecall (Z_to_bv 32 w_245) = false.
Hypothesis ANCH_7 : gw_anch (Z.shiftl (bv_signed hi_6) 12 + (base + 24) + bv_signed lo_7)%Z RGOT_SSP.
Hypothesis ANCH_27 : gw_anch (Z.shiftl (bv_signed hi_26) 12 + (base + 104) + bv_signed lo_27)%Z (RATP + 131968).
Hypothesis ANCH_32 : gw_anch (Z.shiftl (bv_signed hi_31) 12 + (base + 124) + bv_signed lo_32)%Z (RDEBRUIJN + 32).
Hypothesis ANCH_94 : gw_anch (Z.shiftl (bv_signed hi_93) 12 + (base + 372) + bv_signed lo_94)%Z (RATP + 131968).
Hypothesis LINK_245 : gw_anch (base + 980 + bv_signed joff_245)%Z (e_197bc + 0)%Z.
Hypothesis RNG_RATP : gw_br RATP 1896.
Hypothesis LAY_lo_RATP : gw_le (gw_RDATA2_LO + 164) RATP.
Hypothesis LAY_hi_RATP : gw_le ((RATP + 132896)) RIMG_HI.
Hypothesis AL_RATP : gw_al RATP 8.
Hypothesis RNG_RDEBRUIJN : gw_br RDEBRUIJN 159.
Hypothesis LAY_lo_RDEBRUIJN : gw_le (0x10000 + 0) RDEBRUIJN.
Hypothesis LAY_hi_RDEBRUIJN : gw_le ((RDEBRUIJN + 159)) gw_RTEXT_LO.
Hypothesis AL_RDEBRUIJN : gw_al RDEBRUIJN 8.
Hypothesis RNG_RGOT_SSP : gw_br RGOT_SSP 8.
Hypothesis LAY_lo_RGOT_SSP : gw_le (RDATA_LO + 0) RGOT_SSP.
Hypothesis LAY_hi_RGOT_SSP : gw_le ((RGOT_SSP + 8)) gw_RDATA2_LO.
Hypothesis AL_RGOT_SSP : gw_al RGOT_SSP 8.
Hypothesis LAY_win_0 : gw_win (0x10000 + 1) gw_RTEXT_LO.
Hypothesis LAY_win_1 : gw_win (gw_RTEXT_LO + 1) RDATA_LO.
Hypothesis LAY_win_2 : gw_win (RDATA_LO + 1) gw_RDATA2_LO.
Hypothesis LAY_win_3 : gw_win (gw_RDATA2_LO + 1) RIMG_HI.
Hypothesis LAY_win_4 : gw_win RIMG_HI 0x1000000.
Hypothesis AL_win_RIMG_HI : gw_winal RIMG_HI 4096.
Hypothesis AL_win_RDATA_LO : gw_winal RDATA_LO 4096.
Hypothesis AL_win_gw_RTEXT_LO : gw_winal gw_RTEXT_LO 4096.
Hypothesis AL_win_gw_RDATA2_LO : gw_winal gw_RDATA2_LO 4096.
Hypothesis ROM_RSIZE_CLASSES : QZDE.ro_bytes segs (RDEBRUIJN + 32) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RSIZE_CLASSES.
Hypothesis ROM_RDEBRUIJN : QZDE.ro_bytes segs RDEBRUIJN OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RDEBRUIJN.
Hypothesis ROM_RSMALL_CNT : QZDE.ro_bytes segs (RDEBRUIJN + 128) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RSMALL_CNT.
Hypothesis ROM_RMED_CNT : QZDE.ro_bytes segs (RDEBRUIJN + 155) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RMED_CNT.
Hypothesis ROM_reservedZ : QGeV.reservedZ segs = ref_reserved.
Hypothesis LAY_ref_reserved : ref_reserved = (cons (0x10000, gw_RTEXT_LO - 0x10000) (cons (gw_RTEXT_LO, RDATA_LO - gw_RTEXT_LO) (cons (RDATA_LO, gw_RDATA2_LO - RDATA_LO) (cons (gw_RDATA2_LO, RIMG_HI - gw_RDATA2_LO) nil))))%Z.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Definition rntf_frame : ltac:(gw_rebind_ty (@Qy8Z.Mq9.rntf_frame RC__) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@Qy8Z.Mq9.rntf_frame RC__) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@Qy8Z.Mq9.rntf_frame RC__) (@rntf_frame) gw_tbl_0).
Definition rfree_fp : ltac:(gw_rebind_ty (@QDXD.Mq2.rfree_fp RATP) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@QDXD.Mq2.rfree_fp RATP) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@Q8l1.Mq9.rfree_fp RATP) (@rfree_fp) (gw_ent (@Qy8Z.Mq9.rfree_fp RATP) (@rfree_fp) (gw_ent (@QDXD.Mq2.rfree_fp RATP) (@rfree_fp) (gw_ent (@Qy8Z.Mq3.rfree_fp RATP) (@rfree_fp) gw_tbl_1)))).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@Q8l1.Mq9.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq9.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq3.rarea_rep segs) (@rarea_rep) gw_tbl_2))))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@Q8l1.Mq9.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq9.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq3.rmrep_areas segs) (@rmrep_areas) gw_tbl_3))))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@Q8l1.Mq9.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq9.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_4))))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@Q8l1.Mq9.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq9.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_5))))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@Q8l1.Mq9.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq9.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq3.rgroup_rep segs) (@rgroup_rep) gw_tbl_6))))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@Q8l1.Mq9.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq9.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq3.rmrep_groups segs) (@rmrep_groups) gw_tbl_7))))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@Q8l1.Mq9.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq9.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq3.rshadow_rep segs) (@rshadow_rep) gw_tbl_8))))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@Q8l1.Mq9.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq9.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq3.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_9))))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@Q8l1.Mq9.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq9.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_10))))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_11)).
Notation gw_tbl_12 := (gw_ent (@Q8l1.Mq9.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq9.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_11))))))).
Definition rpres_except : ltac:(gw_rebind_ty (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_12)).
Notation gw_tbl_13 := (gw_ent (@Q8l1.Mq9.rpres_except segs) (@rpres_except) (gw_ent (@Qy8Z.Mq9.rpres_except segs) (@rpres_except) (gw_ent (@QDXD.Mq2.rpres_except segs) (@rpres_except) (gw_ent (@QCa8.Mq5.rpres_except segs) (@rpres_except) (gw_ent (@Qy8Z.Mq3.rpres_except segs) (@rpres_except) gw_tbl_12))))).
Definition rntf_ret_post : ltac:(gw_rebind_ty (@QDXD.Mq2.rntf_ret_post segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@QDXD.Mq2.rntf_ret_post segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_13)).
Notation gw_tbl_14 := (gw_ent (@Qy8Z.Mq9.rntf_ret_post segs RATP RGOT_SSP ref_reserved RC__) (@rntf_ret_post) (gw_ent (@QDXD.Mq2.rntf_ret_post segs RATP RGOT_SSP ref_reserved RC__) (@rntf_ret_post) gw_tbl_13)).

Hypothesis meta_word_pg : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Qy8Z.Mq3.gw_all) (@Qy8Z.Mq3.meta_word_pg) (base + -732)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_14))) in let T := gw_fold_pcs T base (-732)%Z [0; 36; 80; 108; 180; 260]%Z in exact T).

Definition rmrep_meta_chunk : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_meta_chunk) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_meta_chunk)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.
Definition rpres_except_trans : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_trans) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_trans)).
Definition rpres_except_mono : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_mono) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_mono)).

Definition rmrep_put_meta_frame : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_put_meta_frame) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_put_meta_frame)).
Definition rmrep_seq_read : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_seq_read) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_seq_read)).
Definition rmeta_slot_bounds : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmeta_slot_bounds) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmeta_slot_bounds)).
Definition rfree_fp_stack : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rfree_fp_stack) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rfree_fp_stack)).
Definition rfree_fp_ctx : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rfree_fp_ctx) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rfree_fp_ctx)).
Definition rfree_fp_mono : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rfree_fp_mono) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rfree_fp_mono)).
Definition rpres_except_of_munch_cov : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rpres_except_of_munch_cov) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rpres_except_of_munch_cov)).
Definition rmrep_ctx_frameW : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_ctx_frameW) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_ctx_frameW)).

Definition rmrep_set_seq : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq4.rmrep_set_seq) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq4.rmrep_set_seq)).
Definition rmrep_set_unmap_seq : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq4.rmrep_set_unmap_seq) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq4.rmrep_set_unmap_seq)).

Definition rntf_fm : ltac:(gw_ctx_fold_ty2 (@Qy8Z.Mq9.rntf_fm) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@Qy8Z.Mq9.rntf_fm)).
Ltac rmeta_chunk MR MSq CH :=
pose proof (rmrep_meta_chunk _ _ _ MR MSq) as CH;
rewrite ?meta_cells_put_meta in CH; unfold meta_cells in CH;
rewrite ?get_meta_rec_put_same in CH;
rewrite ?conc_put_meta, ?pw_put_meta in CH;
cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen meta_word meta0
m_set_prev m_set_next m_set_mem m_set_avail m_set_freed Z.mul Z.add] in CH;
rewrite ?meta_word_meta0 in CH; unfold pw in CH; cbn [oconc] in CH; unfold wz in CH.

Ltac rraw_store_finish A bs' FR ST MU WM SOK :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); (gw_expose_fam RATP; unfold wa); f_equal; lia);
let L := fresh "LEN" in
assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
apply (rw_cells_frame segs mX _ _ A bs') in FR; [| gw_expose_fam RATP; lia | rewrite <- L; gw_expose_fam RATP; lia | rewrite <- L; gw_expose_fam RATP; cbn [cells_size csize Nat.add]; lia];
apply (stk_write segs mX _ _ A bs') in ST; [| gw_expose_fam RATP; lia | rewrite <- L; gw_expose_fam RATP; lia];
apply (munch_write _ _ mX A bs') in MU; [| gw_expose_fam RATP; lia | rewrite <- L; gw_expose_fam RATP; lia | rewrite <- L; gw_expose_fam RATP; cbn [inside]; lia];
apply (wmono_write segs _ mX (wa A) bs') in WM;
lazymatch goal with HI : mem_inv segs mX |- _ =>
apply (mem_inv_store segs mX (wa A) bs') in HI;
[| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by ((gw_expose_fam RATP; unfold wa); f_equal; lia); exact SOK ] ]
end;
clear L SOK;
let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
end.

#[using="RGOT_SSP e_197bc RATP RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_6 E_6 D_7 E_7 D_26 E_26 D_27 E_27 D_31 E_31 D_32 E_32 D_93 E_93 D_94 E_94 D_245 E_245 ANCH_7 ANCH_27 ANCH_32 ANCH_94 LINK_245 RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ meta_word_pg"] Lemma gw_all : True. Proof. exact I. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_6 w_7 w_26 w_27 w_31 w_32 w_93 w_94 w_245 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved meta_word_pg"] Lemma rntf_seq : forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
(m0 m : word -> option byte) (junk : list byte) (raw s0o s1o s2o s3o : word) st0 st (g p : aptr) (sc ns lo : Z),
let mr := get_meta_rec st g in
rmrep st m -> mem_inv segs m -> meta_slot st g -> mw_ok mr ->
sc = m_sizeclass mr -> m_mem mr = Some p -> 0 <= ns < 256 ->
fm_facts st g ->
s1 = Z_to_bv 64 (RATP + 131696) ->
s_regions st = s_regions st0 -> s_shadow st = s_shadow st0 -> s_groups st = s_groups st0 ->
munch [(bv_unsigned sp - 96, bv_unsigned sp); ((RATP + 131968), (RATP + 132896))] m0 m -> wmono segs m0 m ->
rw_cells segs m (bv_unsigned sp + -96) (rntf_frame junk s3o s2o s1o s0o raw) ->
stk segs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
evt segs (rntf_ret_post raw sp gp tp s0o s1o s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st0 m0
(fm_st (seq_st ns sc st) g) (Z_to_bv 64 (conc st p)) (Z_to_bv 64 (m_maplen mr * 4096)))
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 sc) (Z_to_bv 64 ns) a3 a4 a5 a6 a7 (Z_to_bv 64 (RATP + 131968)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x2bc)) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_6 w_7 w_26 w_27 w_31 w_32 w_93 w_94 w_245 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved meta_word_pg segs base RATP. gw_expose_fam RATP.
intros until lo. intros mr MR MI MSL MW HSC Hmem NS FMF S1 ER ES EG MU WM FR ST LO LOLE. subst mr.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st m g MR MSL) as GB.
pose proof (meta_word_range _ MW) as MWR. pose proof MW as (LI & FB & SCR & ML).
pose proof FR as [[[LJ _] _] _]. cbn in LJ.
(gw_expose_fam RATP; unfold alloc_ceiling, rntf_frame in *).

st1. rewrite ?(unsigned_lit sc) by lia. st1.

pose proof MR as (_ & (_ & _ & _ & _ & _ & C6) & _).
pose proof (rw_cells_store_ok_at segs m _ _ 0 (C1 (b8 (c_seq (ctx st)))) 1 (Z_to_bv 64 ((RATP + 132880))) C6 eq_refl eq_refl
ltac:(unfold wa; f_equal; lia)) as SOK.
clear C6.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_seq st mX ns MR NS) as MR1; gw_expose_fam RATP end.
rraw_store_finish ((RATP + 132880)) [b8 ns] FR ST MU WM SOK.
set (st1 := upd_ctx (set_seq ns) st) in MR1.

st1.
assert (JOIN : forall m2 (a1' : word),
rmrep (seq_st ns sc st) m2 -> mem_inv segs m2 ->
munch [(bv_unsigned sp - 96, bv_unsigned sp); ((RATP + 131968), (RATP + 132896))] m0 m2 -> wmono segs m0 m2 ->
stk segs m2 lo (bv_unsigned sp + -96) -> rw_cells segs m2 (bv_unsigned sp + -96) [CB 48 junk; C8 rc_canary; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 raw] ->
evt segs (rntf_ret_post raw sp gp tp s0o s1o s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st0 m0
(fm_st (seq_st ns sc st) g) (Z_to_bv 64 (conc st p)) (Z_to_bv 64 (m_maplen (get_meta_rec st g) * 4096)))
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) a1' (Z_to_bv 64 ns) (Z_to_bv 64 31) a4 a5 a6 a7 (Z_to_bv 64 (RATP + 131968)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x2d4)) fc None m2 (seg_rom segs))).
{ intros m2 a1' MR2 MI2 MU2 WM2 ST2 FR2.
assert (MS2 : meta_slot (seq_st ns sc st) g) by (unfold seq_st; rewrite record_seq_eq; destruct (sc_in_seq_range sc); gw_exact MSL).
rmeta_chunk MR2 MS2 CH.
assert (Hc2 : forall q, conc (seq_st ns sc st) q = conc st q) by (intros; unfold seq_st; rewrite record_seq_eq; destruct (sc_in_seq_range sc); reflexivity).
assert (Hr2 : forall q, get_meta_rec (seq_st ns sc st) q = get_meta_rec st q) by (intros; unfold seq_st; rewrite record_seq_eq; destruct (sc_in_seq_range sc); reflexivity).
assert (Ho2 : forall q, oconc (seq_st ns sc st) q = oconc st q) by (intros [q|]; [apply Hc2|reflexivity]).
rewrite !Hc2, !Hr2, !Ho2 in CH. rewrite Hmem in CH. cbn [oconc] in CH.

st1. st1. st1. st1. clear CH.
rewrite ?(unsigned_lit (meta_word _)) by lia. rewrite land_pgmask by lia. rewrite (meta_word_pg _ MW).
replace (4096 * m_maplen (get_meta_rec st g)) with (m_maplen (get_meta_rec st g) * 4096) by lia.
replace (Z_to_bv 64 (conc st g)) with (Z_to_bv 64 (conc (seq_st ns sc st) g)) by (f_equal; apply Hc2).
eapply evt_mono.
{ eapply (rntf_fm ra sp gp tp t0 t1 t2 s0 s1 _ _ _ a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m2 junk raw s0o s1o s2o s3o (seq_st ns sc st) g lo);
first [gw_exact MR2 | gw_exact MI2 | gw_exact MS2 | gw_exact S1 | gw_exact FR2 | gw_exact ST2 | unfold alloc_ceiling; lia | lia | idtac].
unfold seq_st. rewrite record_seq_eq. destruct (sc_in_seq_range sc); repeat apply fm_facts_ctx; try reflexivity; gw_exact FMF. }
intros ms' PO. unfold rntf_ret_post in PO |- *.
destruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & m' & -> & PE & WM' & MI' & ST' & MR').
do 14 eexists. split; [reflexivity|].
split.
{ eapply rpres_except_trans.
- apply (rpres_except_of_munch_cov (rfree_fp st0 lo (bv_unsigned sp))) in MU2; [gw_exact MU2|gw_exact WM2|].
cbn [ivs_covered]. repeat split; intros x Hx; [apply rfree_fp_stack; lia | apply rfree_fp_ctx; gw_expose_fam RATP; lia].
- eapply rpres_except_mono; [gw_exact PE|]. intros a Ha.
eapply (rfree_fp_mono st0 (seq_st ns sc st) lo (bv_unsigned sp) (bv_unsigned sp) a); try gw_exact Ha; try lia;
unfold seq_st; rewrite record_seq_eq; destruct (sc_in_seq_range sc); cbn; rewrite <- ?ER, <- ?ES, <- ?EG; try reflexivity; auto. }
split; [eapply wmono_trans; [gw_exact WM2|gw_exact WM']|]. split; [gw_exact MI'|]. split; [gw_exact ST'|gw_exact MR']. }
if_cases K; zify_cond K.
-
assert (NR : sc_in_seq_range sc = false) by (apply (proj1 (seq_range_test sc ltac:(lia))); gw_exact K).
eapply JOIN; try eassumption. unfold seq_st. rewrite record_seq_eq, NR. gw_exact MR1.
- assert (SR : sc_in_seq_range sc = true).
{ destruct (sc_in_seq_range sc) eqn:E; [reflexivity|]. exfalso. apply (proj2 (seq_range_test sc ltac:(lia))) in E. lia. }
assert (SR' : 7 <= sc < 39).
{ unfold sc_in_seq_range in SR. apply andb_true_iff in SR. destruct SR as [Sa Sb]. apply Z.leb_le in Sa. apply Z.ltb_lt in Sb. lia. }

st1.
pose proof MR1 as (_ & (_ & _ & _ & US & _) & _).
pose proof (u8arr_store_ok segs _ _ (unmap_seqs st1) (sc - 7) (Z_to_bv 64 ((RATP + 131968) + (sc + -7) + 848)) US
ltac:(rewrite unmap_seqs_length; lia) ltac:((gw_expose_fam RATP; unfold wa); f_equal; lia)) as SOK.
clear US.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_unmap_seq st1 mX (sc - 7) ns MR1 ltac:(lia)) as MR2; gw_expose_fam RATP end.
rraw_store_finish ((RATP + 132816) + (sc - 7)) [b8 ns] FR ST MU WM SOK.
eapply JOIN; try eassumption.
unfold seq_st. rewrite record_seq_eq, SR. unfold st1 in MR2.
match type of MR2 with rmrep ?S _ => replace (upd_ctx _ (upd_ctx (set_seq ns) st)) with S; [gw_exact MR2|] end.
unfold upd_ctx. cbn. reflexivity.
Qed.

#[using="Type"] Lemma zeros32_cells : cells_bytes [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] = zeros 32.
Proof. clear - segs. vm_compute. reflexivity. Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_6 w_7 w_26 w_27 w_31 w_32 w_93 w_94 w_245 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved meta_word_pg"] Lemma rntf_top : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
(m0 m : word -> option byte) (junk : list byte) (raw s0o s1o s2o s3o : word) st0 st (g p : aptr) (sc lo : Z),
let mr := get_meta_rec st g in
rmrep st m -> mem_inv segs m -> meta_slot st g -> mw_ok mr ->
sc = m_sizeclass mr -> m_mem mr = Some p -> m_maplen mr <> 0 ->
0 <= c_seq (ctx st) < 256 ->
fm_facts st g ->
s1 = Z_to_bv 64 (RATP + 131696) ->
s_regions st = s_regions st0 -> s_shadow st = s_shadow st0 -> s_groups st = s_groups st0 ->
munch [(bv_unsigned sp - 96, bv_unsigned sp); ((RATP + 131968), (RATP + 132896))] m0 m -> wmono segs m0 m ->
rw_cells segs m (bv_unsigned sp + -96) (rntf_frame junk s3o s2o s1o s0o raw) ->
stk segs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
evt segs (rntf_ret_post raw sp gp tp s0o s1o s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st0 m0
(fm_st (record_seq sc (step_seq st)) g) (Z_to_bv 64 (conc st p)) (Z_to_bv 64 (m_maplen mr * 4096)))
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 sc) (wz (meta_word mr)) a3 a4 a5 a6 a7 (Z_to_bv 64 (RATP + 131968)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x25c)) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_6 w_7 w_26 w_27 w_31 w_32 w_93 w_94 w_245 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved meta_word_pg segs base RATP. gw_expose_fam RATP.
intros until lo. intros mr MR MI MSL MW HSC Hmem HML SEQ FMF S1 ER ES EG MU WM FR ST LO LOLE. subst mr.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (meta_word_range _ MW) as MWR. pose proof MW as (LI & FB & SCR & ML).
pose proof (meta_word_maplen _ MW) as M12.
pose proof FR as [[[LJ _] _] _]. cbn in LJ.
(gw_expose_fam RATP; unfold alloc_ceiling, rntf_frame in *).

st1. rewrite M12. st1. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. 2:{ exfalso. lia. } clear K.

pose proof (rmrep_seq_read st m (wa ((RATP + 132880))) MR eq_refl) as RDS. (gw_expose_fam RATP; unfold wa in RDS).
st1. clear RDS. st1.

st1. if_cases K; zify_cond K; rewrite ?wz_unsigned in K by lia.
-
st1.
replace (record_seq sc (step_seq st)) with (seq_st (c_seq (ctx st) + 1) sc st).
2:{ unfold seq_st. rewrite (step_seq_eq st). replace (c_seq (ctx st) =? 255) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
eapply (rntf_seq ra sp gp tp t0 t1 t2 s0 s1 _ a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m junk raw s0o s1o s2o s3o st0 st g p sc (c_seq (ctx st) + 1) lo);
first [gw_exact MR | gw_exact MI | gw_exact MSL | gw_exact MW | gw_exact HSC | gw_exact Hmem | gw_exact FMF | gw_exact S1 | gw_exact ER | gw_exact ES | gw_exact EG | gw_exact MU | gw_exact WM | gw_exact FR | gw_exact ST | unfold alloc_ceiling; lia].
-
pose proof MR as (_ & (_ & _ & _ & US & _) & _).
pose proof (rw_cells_of_u8arr segs m _ _ US) as UB. rewrite unmap_seqs_length in UB. clear US. gw_expose_fam RATP.
replace ((RATP + 132816)) with (RATP + 132816) in UB by first [reflexivity | (cbn; lia)].
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [((RATP + 132816), (RATP + 132848))]%Z mX) as MUz; pose proof (wmono_refl segs mX) as WMz end.
st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (UA' : u8arr segs mX ((RATP + 132816)) (zeros 32))
by (apply (u8arr_of_rw_cells segs mX _ 32); gw_expose_fam RATP; eapply rw_cells_congr; [| | | gw_exact UB]; [gw_exact zeros32_cells| reflexivity| cbn; tauto]) end.
clear UB.
set (stz := upd_ctx (fun c => set_unmap_seq_map ∅ c) st).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRz : rmrep stz mX) end.
{ eapply (rmrep_ctx_frameW st stz m _ _ MR MUz WMz); try reflexivity.
- intros lo' hi' [E|[]]; inversion E; subst. gw_expose_fam RATP. lia.
- right. split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; gw_expose_fam RATP; lia].
- right. split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; gw_expose_fam RATP; lia].
- right. split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; gw_expose_fam RATP; lia].
- left. unfold stz. rewrite unmap_seqs_empty. gw_exact UA'.
- right. split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; gw_expose_fam RATP; lia].
- right. split; [| intros lo' hi' [E|[]]; inversion E; subst; gw_expose_fam RATP; lia].
unfold ctx_tail_cells, brk_word, ctx, stz. cbn [s_ctx upd_ctx c_seq c_brk set_unmap_seq_map]. reflexivity. }

st1. st1.
replace (record_seq sc (step_seq st)) with (seq_st 1 sc stz).
2:{ unfold seq_st, stz. rewrite (step_seq_eq st). fold (ctx st). replace (c_seq (ctx st) =? 255) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity. }
replace (Z_to_bv 64 (conc st g)) with (Z_to_bv 64 (conc stz g)) by first [reflexivity | (cbn; lia)].
replace (conc st p) with (conc stz p) by first [reflexivity | (cbn; lia)].
change (get_meta_rec st g) with (get_meta_rec stz g).
eapply (rntf_seq ra sp gp tp t0 t1 t2 s0 s1 _ a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 _ junk raw s0o s1o s2o s3o st0 stz g p sc 1 lo);
first [gw_exact MRz | assumption | gw_exact MSL | gw_exact MW | gw_exact HSC | gw_exact Hmem | gw_exact S1 | gw_exact ER | gw_exact ES | gw_exact EG | gw_exact FR | gw_exact ST | unfold alloc_ceiling; lia
| apply fm_facts_ctx; [reflexivity| gw_exact FMF] ].
Qed.

End RC__1.

End G.
End Mq7.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.

Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq4 Q4J3.Mq2 QDUx.Mqb QPjm.Mq3.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QDXD.Mq2.
Import QkTt.Mq4.
Import QCa8.Mq4.
Import Qy8Z.Mq9.
Import Q8l1.Mq9.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.
Open Scope bv_scope.
Open Scope Z_scope.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment) (base : Z).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (w_6 w_7 w_26 w_27 w_31 w_32 w_93 w_94 w_245 : Z).
Variables (hi_6 hi_26 hi_31 hi_93 : bv 20).
Variables (lo_7 lo_27 lo_32 lo_94 : bv 12).
Variables (joff_245 : bv 21).
Variables (e_197bc : Z).
Hypothesis CODE : code_at segs base (ntf_code w_6 w_7 w_26 w_27 w_31 w_32 w_93 w_94 w_245).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 984.
Hypothesis D_6 : decode_any (Z_to_bv 32 w_6) = Some (Auipc 12 hi_6, 4%Z).
Hypothesis E_6 : is_ecall (Z_to_bv 32 w_6) = false.
Hypothesis D_7 : decode_any (Z_to_bv 32 w_7) = Some (Load SZ8 true 9 12 lo_7, 4%Z).
Hypothesis E_7 : is_ecall (Z_to_bv 32 w_7) = false.
Hypothesis D_26 : decode_any (Z_to_bv 32 w_26) = Some (Auipc 16 hi_26, 4%Z).
Hypothesis E_26 : is_ecall (Z_to_bv 32 w_26) = false.
Hypothesis D_27 : decode_any (Z_to_bv 32 w_27) = Some (OpImm ALU_ADD 18 16 lo_27, 4%Z).
Hypothesis E_27 : is_ecall (Z_to_bv 32 w_27) = false.
Hypothesis D_31 : decode_any (Z_to_bv 32 w_31) = Some (Auipc 16 hi_31, 4%Z).
Hypothesis E_31 : is_ecall (Z_to_bv 32 w_31) = false.
Hypothesis D_32 : decode_any (Z_to_bv 32 w_32) = Some (OpImm ALU_ADD 16 16 lo_32, 4%Z).
Hypothesis E_32 : is_ecall (Z_to_bv 32 w_32) = false.
Hypothesis D_93 : decode_any (Z_to_bv 32 w_93) = Some (Auipc 13 hi_93, 4%Z).
Hypothesis E_93 : is_ecall (Z_to_bv 32 w_93) = false.
Hypothesis D_94 : decode_any (Z_to_bv 32 w_94) = Some (OpImm ALU_ADD 13 13 lo_94, 4%Z).
Hypothesis E_94 : is_ecall (Z_to_bv 32 w_94) = false.
Hypothesis D_245 : decode_any (Z_to_bv 32 w_245) = Some (Jal 1 joff_245, 4%Z).
Hypothesis E_245 : is_ecall (Z_to_bv 32 w_245) = false.
Hypothesis ANCH_7 : gw_anch (Z.shiftl (bv_signed hi_6) 12 + (base + 24) + bv_signed lo_7)%Z RGOT_SSP.
Hypothesis ANCH_27 : gw_anch (Z.shiftl (bv_signed hi_26) 12 + (base + 104) + bv_signed lo_27)%Z (RATP + 131968).
Hypothesis ANCH_32 : gw_anch (Z.shiftl (bv_signed hi_31) 12 + (base + 124) + bv_signed lo_32)%Z (RDEBRUIJN + 32).
Hypothesis ANCH_94 : gw_anch (Z.shiftl (bv_signed hi_93) 12 + (base + 372) + bv_signed lo_94)%Z (RATP + 131968).
Hypothesis LINK_245 : gw_anch (base + 980 + bv_signed joff_245)%Z (e_197bc + 0)%Z.
Hypothesis RNG_RATP : gw_br RATP 1896.
Hypothesis LAY_lo_RATP : gw_le (gw_RDATA2_LO + 164) RATP.
Hypothesis LAY_hi_RATP : gw_le ((RATP + 132896)) RIMG_HI.
Hypothesis AL_RATP : gw_al RATP 8.
Hypothesis RNG_RDEBRUIJN : gw_br RDEBRUIJN 159.
Hypothesis LAY_lo_RDEBRUIJN : gw_le (0x10000 + 0) RDEBRUIJN.
Hypothesis LAY_hi_RDEBRUIJN : gw_le ((RDEBRUIJN + 159)) gw_RTEXT_LO.
Hypothesis AL_RDEBRUIJN : gw_al RDEBRUIJN 8.
Hypothesis RNG_RGOT_SSP : gw_br RGOT_SSP 8.
Hypothesis LAY_lo_RGOT_SSP : gw_le (RDATA_LO + 0) RGOT_SSP.
Hypothesis LAY_hi_RGOT_SSP : gw_le ((RGOT_SSP + 8)) gw_RDATA2_LO.
Hypothesis AL_RGOT_SSP : gw_al RGOT_SSP 8.
Hypothesis LAY_win_0 : gw_win (0x10000 + 1) gw_RTEXT_LO.
Hypothesis LAY_win_1 : gw_win (gw_RTEXT_LO + 1) RDATA_LO.
Hypothesis LAY_win_2 : gw_win (RDATA_LO + 1) gw_RDATA2_LO.
Hypothesis LAY_win_3 : gw_win (gw_RDATA2_LO + 1) RIMG_HI.
Hypothesis LAY_win_4 : gw_win RIMG_HI 0x1000000.
Hypothesis AL_win_RIMG_HI : gw_winal RIMG_HI 4096.
Hypothesis AL_win_RDATA_LO : gw_winal RDATA_LO 4096.
Hypothesis AL_win_gw_RTEXT_LO : gw_winal gw_RTEXT_LO 4096.
Hypothesis AL_win_gw_RDATA2_LO : gw_winal gw_RDATA2_LO 4096.
Hypothesis ROM_RSIZE_CLASSES : QZDE.ro_bytes segs (RDEBRUIJN + 32) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RSIZE_CLASSES.
Hypothesis ROM_RDEBRUIJN : QZDE.ro_bytes segs RDEBRUIJN OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RDEBRUIJN.
Hypothesis ROM_RSMALL_CNT : QZDE.ro_bytes segs (RDEBRUIJN + 128) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RSMALL_CNT.
Hypothesis ROM_RMED_CNT : QZDE.ro_bytes segs (RDEBRUIJN + 155) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RMED_CNT.
Hypothesis ROM_reservedZ : QGeV.reservedZ segs = ref_reserved.
Hypothesis LAY_ref_reserved : ref_reserved = (cons (0x10000, gw_RTEXT_LO - 0x10000) (cons (gw_RTEXT_LO, RDATA_LO - gw_RTEXT_LO) (cons (RDATA_LO, gw_RDATA2_LO - RDATA_LO) (cons (gw_RDATA2_LO, RIMG_HI - gw_RDATA2_LO) nil))))%Z.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Definition rget_meta_post : ltac:(gw_rebind_ty (@QCa8.Mq4.rget_meta_post segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QCa8.Mq4.rget_meta_post segs) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@QCa8.Mq4.rget_meta_post segs) (@rget_meta_post) gw_tbl_0).
Definition rntf_frame : ltac:(gw_rebind_ty (@Qy8Z.Mq9.rntf_frame RC__) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Qy8Z.Mq9.rntf_frame RC__) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@Qy8Z.Mq9.rntf_frame RC__) (@rntf_frame) gw_tbl_1).
Definition rfree_fp : ltac:(gw_rebind_ty (@QDXD.Mq2.rfree_fp RATP) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@QDXD.Mq2.rfree_fp RATP) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@Q8l1.Mq9.rfree_fp RATP) (@rfree_fp) (gw_ent (@Qy8Z.Mq9.rfree_fp RATP) (@rfree_fp) (gw_ent (@QDXD.Mq2.rfree_fp RATP) (@rfree_fp) gw_tbl_2))).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@Q8l1.Mq9.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq9.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_3))))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@Q8l1.Mq9.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq9.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_4))))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@Q8l1.Mq9.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq9.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_5))))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@Q8l1.Mq9.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq9.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_6))))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@Q8l1.Mq9.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq9.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_7))))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@Q8l1.Mq9.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq9.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_8))))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@Q8l1.Mq9.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq9.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_9))))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@Q8l1.Mq9.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq9.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_10))))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_11)).
Notation gw_tbl_12 := (gw_ent (@Q8l1.Mq9.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq9.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_11))))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_12)).
Notation gw_tbl_13 := (gw_ent (@Q8l1.Mq9.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq9.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_12))))))).
Definition rpres_except : ltac:(gw_rebind_ty (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_13)).
Notation gw_tbl_14 := (gw_ent (@Q8l1.Mq9.rpres_except segs) (@rpres_except) (gw_ent (@Qy8Z.Mq9.rpres_except segs) (@rpres_except) (gw_ent (@QDXD.Mq2.rpres_except segs) (@rpres_except) (gw_ent (@QCa8.Mq5.rpres_except segs) (@rpres_except) gw_tbl_13)))).
Definition rntf_ret_post : ltac:(gw_rebind_ty (@QDXD.Mq2.rntf_ret_post segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@QDXD.Mq2.rntf_ret_post segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_14)).
Notation gw_tbl_15 := (gw_ent (@Qy8Z.Mq9.rntf_ret_post segs RATP RGOT_SSP ref_reserved RC__) (@rntf_ret_post) (gw_ent (@QDXD.Mq2.rntf_ret_post segs RATP RGOT_SSP ref_reserved RC__) (@rntf_ret_post) gw_tbl_14)).

Hypothesis rget_meta_walk : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QCa8.Mq4.gw_all) (@QCa8.Mq4.rget_meta_walk) (base + -272)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_15))) in let T := gw_fold_pcs T base (-272)%Z [0; 244]%Z in exact T).

Definition rsize_classes_read : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rsize_classes_read) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rsize_classes_read)).
Definition rmrep_meta_chunk : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_meta_chunk) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_meta_chunk)).
Definition rmrep_group_read : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_group_read) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_group_read)).
Definition rmrep_area_check_read : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_area_check_read) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_area_check_read)).
Definition rmrep_ctx_secret_read : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_ctx_secret_read) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_ctx_secret_read)).
Definition rreserved_disjoint : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rreserved_disjoint) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rreserved_disjoint)).
Definition rgroup_conc : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rgroup_conc) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rgroup_conc)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.

Definition rmrep_put_meta_frame : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_put_meta_frame) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_put_meta_frame)).
Definition rmeta_slot_bounds : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmeta_slot_bounds) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmeta_slot_bounds)).
Definition rfree_fp_stack : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rfree_fp_stack) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rfree_fp_stack)).
Definition rfree_fp_group : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rfree_fp_group) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rfree_fp_group)).
Definition rpres_except_of_munch_cov : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rpres_except_of_munch_cov) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rpres_except_of_munch_cov)).

Definition rmrep_group_hdr_zero : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq4.rmrep_group_hdr_zero) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq4.rmrep_group_hdr_zero)).
Definition rmrep_grp_del_eq : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq4.rmrep_grp_del_eq) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq4.rmrep_grp_del_eq)).

Definition rntf_fm : ltac:(gw_ctx_fold_ty2 (@Qy8Z.Mq9.rntf_fm) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm2 (@Qy8Z.Mq9.rntf_fm)).
Ltac rmeta_chunk MR MSq CH :=
pose proof (rmrep_meta_chunk _ _ _ MR MSq) as CH;
rewrite ?meta_cells_put_meta in CH; unfold meta_cells in CH;
rewrite ?get_meta_rec_put_same in CH;
rewrite ?conc_put_meta, ?pw_put_meta in CH;
cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen meta_word meta0
m_set_prev m_set_next m_set_mem m_set_avail m_set_freed Z.mul Z.add] in CH;
rewrite ?meta_word_meta0 in CH; unfold pw in CH; cbn [oconc] in CH; unfold wz in CH.

Ltac rraw_store_finish A bs' FR ST MU WM SOK :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); (gw_expose_fam RATP; unfold wa); f_equal; lia);
let L := fresh "LEN" in
assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
apply (rw_cells_frame segs mX _ _ A bs') in FR; [| gw_expose_fam RATP; lia | rewrite <- L; gw_expose_fam RATP; lia | rewrite <- L; gw_expose_fam RATP; cbn [cells_size csize Nat.add]; lia];
apply (stk_write segs mX _ _ A bs') in ST; [| gw_expose_fam RATP; lia | rewrite <- L; gw_expose_fam RATP; lia];
apply (munch_write _ _ mX A bs') in MU; [| gw_expose_fam RATP; lia | rewrite <- L; gw_expose_fam RATP; lia | rewrite <- L; gw_expose_fam RATP; cbn [inside]; lia];
apply (wmono_write segs _ mX (wa A) bs') in WM;
lazymatch goal with HI : mem_inv segs mX |- _ =>
apply (mem_inv_store segs mX (wa A) bs') in HI;
[| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by ((gw_expose_fam RATP; unfold wa); f_equal; lia); exact SOK ] ]
end;
clear L SOK;
let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
end.

#[using="RGOT_SSP e_197bc RATP RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_6 E_6 D_7 E_7 D_26 E_26 D_27 E_27 D_31 E_31 D_32 E_32 D_93 E_93 D_94 E_94 D_245 E_245 ANCH_7 ANCH_27 ANCH_32 ANCH_94 LINK_245 RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ rget_meta_walk"] Lemma gw_all : True. Proof. exact I. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1.

Definition rnest_call_post (sp gp tp s1 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (st : mstate) (m : word -> option byte) (st' : mstate) (g p : aptr) (G1 idx : Z) (fr : list cell) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR (Z_to_bv 64 (base + 0x288)) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 (conc st p)) s1 (Z_to_bv 64 G1) (Z_to_bv 64 idx) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (RATP + 131968)) (Z_to_bv 64 (conc st g)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x0)) fc None m' (seg_rom segs)
/\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' lo (bv_unsigned sp + -96)
/\ rw_cells segs m' (bv_unsigned sp + -96) fr
/\ rmrep st' m'.

#[using="RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_6 w_7 w_26 w_27 w_31 w_32 w_93 w_94 w_245 CODE BASE4 BASER RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RDEBRUIJN LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 ROM_RSIZE_CLASSES ROM_reservedZ LAY_ref_reserved rget_meta_walk"] Lemma rntf_nest_call : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
(m : word -> option byte) (fr : list cell) st (g p base1 g1 : aptr) (ghp gh1 : ghdr) (ar1 : area) (b3 lo8 hi8 off16 lo : Z),
let mr := get_meta_rec st g in
let mr1 := get_meta_rec st g1 in
let idx1 := Z.land b3 31 in
rmrep st m -> mem_inv segs m -> meta_slot st g -> mw_ok mr -> m_maplen mr = 0 -> m_mem mr = Some p ->
(s_groups st) !! p = Some ghp ->
(forall o, 0 <= o < 12 -> exists h, cell_read (get_shadow st (fst p)) (snd p + o) = Unknown h) ->
bytes_at segs m (conc st p - 4) [b8 0; b8 b3; b8 lo8; b8 hi8] ->
0 <= b3 < 256 -> 0 <= lo8 < 256 -> 0 <= hi8 < 256 -> off16 = lo8 + 256 * hi8 ->
base1 = aadd p (- (UNIT * off16) - UNIT) ->
(s_groups st) !! base1 = Some gh1 -> g_meta gh1 = Some g1 -> meta_slot st g1 -> m_mem mr1 = Some base1 ->
0 <= m_avail mr1 < 2^32 -> 0 <= m_freed mr1 < 2^32 -> 0 <= m_last_idx mr1 < 32 -> 0 <= m_freeable mr1 < 2 ->
0 <= m_sizeclass mr1 < 64 -> 0 <= m_maplen mr1 < 2^40 ->
(s_areas st) !! (area_of g1) = Some ar1 -> a_check ar1 = c_secret (ctx st) -> 0 <= c_secret (ctx st) < 2^64 ->
idx1 <= m_last_idx mr1 -> Z.testbit (m_avail mr1) idx1 = false -> Z.testbit (m_freed mr1) idx1 = false ->
(m_sizeclass mr1 < 48 -> size_class (m_sizeclass mr1) * idx1 <= off16 < size_class (m_sizeclass mr1) * (idx1 + 1)) ->
(48 <= m_sizeclass mr1 -> m_sizeclass mr1 = 63) ->
(m_maplen mr1 <> 0 -> off16 <= m_maplen mr1 * 256 - 1) ->
rw_cells segs m (bv_unsigned sp + -96) fr -> cells_size fr = 96%nat ->
stk segs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
evt segs (rnest_call_post sp gp tp s1 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st m (grp_del st g p) g p (conc st g1) idx1 fr)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) a1 (wz (meta_word mr)) a3 a4 a5 a6 a7 (Z_to_bv 64 (RATP + 131968)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x25c)) fc None m (seg_rom segs)).
Proof. clear - RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_6 w_7 w_26 w_27 w_31 w_32 w_93 w_94 w_245 CODE BASE4 BASER RNG_RATP LAY_lo_RATP LAY_hi_RATP RNG_RDEBRUIJN LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 ROM_RSIZE_CLASSES ROM_reservedZ LAY_ref_reserved rget_meta_walk segs base RATP. gw_expose_fam RATP.
intros until lo. intros mr mr1 idx1 MR MI MSL MW HML Hmem Hp UNK HDR B3 LO8 HI8 O16 Hb1 Hgh1 Hg1 MS1 Hmem1
AV1 FR1 LI1 FB1 SC1 ML1 Har1 Hchk SEC Hidx Hav Hfr Hsc Hsc63 Hml FR FRL ST LO LOLE. subst mr mr1.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (meta_word_range _ MW) as MWR. pose proof MW as (LI & FB & SCR & ML).
pose proof (meta_word_maplen _ MW) as M12.
pose proof (rmeta_slot_bounds st m g MR MSL) as GB. pose proof (rmeta_slot_bounds st m g1 MR MS1) as G1B.
pose proof FR as [[WFfr _] _]. pose proof (cells_bytes_length _ WFfr) as LFR. rewrite FRL in LFR.
pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DISJ & WA & WG).
destruct (rgroup_conc st p ghp WF Hp) as (r & Hr & Cp & Kr & Sp0 & Sp1 & SpA & RB0 & RBC).
destruct (WR _ r Hr) as (_ & RBAL & _ & _ & RFr). pose proof (round_up_pg_ge (r_len r)) as RU.
pose proof (rreserved_disjoint _ _ RFr) as (Dr1 & Dr2 & Dr3 & Dr4).

destruct (WG base1 gh1 Hgh1) as (rb & Hrb & _ & Bb0 & Bb1 & BbA). rewrite Hb1 in Hrb. cbn [aadd fst] in Hrb. rewrite Hr in Hrb. inversion Hrb; subst rb. clear Hrb.
assert (HBc : conc st base1 = conc st p - 16 * off16 - 16).
{ rewrite Hb1. rewrite conc_aadd by (cbn; rewrite Hr; eauto). unfold UNIT. lia. }
rewrite Hb1 in Bb0. cbn [aadd snd] in Bb0.
pose proof MS1 as (a & ara & k & Ha & Hkk & Eg).
destruct (WA a ara Ha) as (rg & Hrg & Sa0 & Sa1 & AAL & ANG & ALR).
destruct (WR (fst a) rg Hrg) as (RgB0 & RgBAL & _ & RgBC & RFa).
assert (HG : conc st g1 = r_base rg + snd a + (AREA_HDR + META_SIZE * k)).
{ rewrite Eg, conc_aadd by (rewrite Hrg; eauto). rewrite (conc_region' st a rg Hrg). reflexivity. }
assert (Hao : area_of g1 = a).
{ rewrite Eg. unfold AREA_HDR, META_SIZE. apply area_of_slot; [gw_exact AAL | unfold NSLOTS in Hkk; lia]. }
assert (HGm : conc st g1 mod 4096 = AREA_HDR + META_SIZE * k).
{ rewrite HG. apply page_off_mod; [gw_exact RgBAL | gw_exact AAL | unfold AREA_HDR, META_SIZE, NSLOTS in *; lia]. }
assert (P16m : conc st p mod 16 = 0) by (rewrite Cp; apply base16_mod; assumption).
(gw_expose_fam RATP; unfold alloc_ceiling, AREA_HDR, META_SIZE, NSLOTS in *).
assert (HAeq : r_base rg + snd a = conc st g1 - conc st g1 mod 4096) by lia.

change (frozen (conc st p mod 16 = 0)) in P16m.
change (frozen (r_base rg + snd a = conc st g1 - conc st g1 mod 4096)) in HAeq.
clear HGm AAL RBAL RgBAL SpA BbA.
destruct GB as (GB0 & GB1 & GB2 & _). destruct G1B as (G1B0 & G1B1 & G1B2 & _).
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st p, conc st p + 8)]%Z m) as MU.
pose proof (wmono_refl segs m) as WM.

st1. rewrite ?(unsigned_lit (meta_word _)) by lia. rewrite M12, HML. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. } clear K.

rmeta_chunk MR MSL CH. rewrite Hmem in CH. cbn [oconc] in CH.
st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (rmrep_group_read st mX base1 gh1 MR Hgh1) as [RG _];
pose proof (rmrep_meta_chunk st mX g1 MR MS1) as MM;
pose proof (rmrep_area_check_read st mX (area_of g1) ar1 MR Har1) as RA;
pose proof (rmrep_ctx_secret_read st mX MR) as RC;
pose proof (bytes_at_read segs mX _ _ 0 1 HDR ltac:(lia) ltac:(cbn; lia)) as R4;
pose proof (bytes_at_read segs mX _ _ 1 1 HDR ltac:(lia) ltac:(cbn; lia)) as R3;
pose proof (bytes_at_read segs mX _ _ 2 2 HDR ltac:(lia) ltac:(cbn; lia)) as R2
end.
rewrite Hg1 in RG. unfold pw in RG. cbn [oconc] in RG.
unfold meta_cells in MM. rewrite Hmem1 in MM. unfold pw in MM. cbn [oconc] in MM. unfold meta_word in MM.
rewrite Hchk in RA. rewrite Hao, (conc_region' st a rg Hrg) in RA. gw_expose_fam RATP.
change (firstn 1 (skipn (Z.to_nat 0) [b8 0; b8 b3; b8 lo8; b8 hi8])) with [b8 0] in R4.
change (firstn 1 (skipn (Z.to_nat 1) [b8 0; b8 b3; b8 lo8; b8 hi8])) with [b8 b3] in R3.
change (firstn 2 (skipn (Z.to_nat 2) [b8 0; b8 b3; b8 lo8; b8 hi8])) with [b8 lo8; b8 hi8] in R2.
replace (conc st p - 4 + 0) with (conc st p - 4) in R4 by lia.
replace (conc st p - 4 + 1) with (conc st p - 3) in R3 by lia.
replace (conc st p - 4 + 2) with (conc st p - 2) in R2 by lia.
rewrite <- (le2_lohi lo8 hi8) in R2 by lia. rewrite <- O16 in R2.

st1.
eapply evt_cut.
{ eapply (rget_meta_walk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
(conc st p) (conc st g1) (conc st base1) (r_base rg + snd a) b3 off16
(m_avail (get_meta_rec st g1)) (m_freed (get_meta_rec st g1)) (m_last_idx (get_meta_rec st g1)) (m_freeable (get_meta_rec st g1))
(m_sizeclass (get_meta_rec st g1)) (m_maplen (get_meta_rec st g1)) (c_secret (ctx st))).
all: lazymatch goal with
| |- ov_read_bytes _ _ (wa (_ - 4)) 1 = _ => gw_exact R4
| |- ov_read_bytes _ _ (wa (_ - 3)) 1 = _ => gw_exact R3
| |- ov_read_bytes _ _ (wa (_ - 2)) 2 = _ => gw_exact R2
| |- ov_read_bytes _ _ (wa (conc _ _)) 8 = _ => gw_exact RG
| |- ov_read_bytes _ _ (wa (RATP + 131968)) 8 = _ => gw_exact RC
| |- ov_read_bytes _ _ (wa (RATP + 131968)) 8 = _ => gw_exact RC
| |- ov_read_bytes _ _ (wa (r_base _ + snd _)) 8 = _ => gw_exact RA
| |- rw_cells _ _ (conc _ _) _ => gw_exact MM
| |- _ -> ov_read_bytes _ _ _ 2 = _ => intros Hlt; apply rsize_classes_read; [assumption | lia]
| |- _ => idtac
end.
all: first [ gw_exact P16m | gw_exact HAeq | gw_exact Hidx | gw_exact Hav | gw_exact Hfr | gw_exact Hsc | gw_exact Hsc63 | gw_exact Hml
| lia | unfold wz; rewrite ?unsigned_lit by lia; lia | unfold UNIT in *; lia ]. }
intros ms' (ga2 & ga3 & ga4 & ga5 & ->).
try g_ret_pc_any.

st1.
unfold wa in R3. unfold wz. replace (conc st p - 3) with (conc st p + -3) in R3 by lia.
st1.

clear CH MM RG RA RC R4 R2.
pose proof MR as (_ & _ & _ & _ & GR0 & _). destruct (GR0 p ghp Hp) as (w8 & RWp & _). clear GR0.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (rw_cells_store_ok_at segs mX _ _ 0 (C8 (pw st (g_meta ghp))) 8 (Z_to_bv 64 (conc st p)) RWp eq_refl eq_refl ltac:(unfold wa; f_equal; lia)) as SOK end.
clear RWp.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_group_hdr_zero st mX p ghp (le8 (Z_to_bv 64 0)) ltac:(eassumption) Hp UNK (length_le8 _)) as MR2
end.
rraw_store_finish (conc st p) (le8 (Z_to_bv 64 0)) FR ST MU WM SOK.
apply (rmrep_grp_del_eq st _ g p) in MR2.

st1. st1.
apply evt_done. unfold rnest_call_post. do 14 eexists.
split. { unfold idx1. rewrite ?zxb_b8 by lia. unfold wz. rewrite ?(wz_unsigned b3), ?(unsigned_lit b3) by lia.
cbv delta [mkR]. gw_expose_fam RATP. reflexivity. }
split.
{ apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [gw_exact MU|gw_exact WM|].
cbn [ivs_covered]. repeat split; intros x Hx.
+ apply rfree_fp_stack. lia.
+ eapply rfree_fp_group; [gw_exact Hp | lia]. }
split; [gw_exact WM|]. split; [assumption|]. split; [gw_exact ST|]. split; [gw_exact FR| gw_exact MR2].
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_6 w_7 w_26 w_27 w_31 w_32 w_93 w_94 w_245 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved"] Lemma rntf_nest_ret : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
(m : word -> option byte) (junk : list byte) (raw s0o s1o s2o s3o : word) (st0 st : mstate) (g : aptr) (lo : Z),
rmrep st m -> mem_inv segs m -> meta_slot st g -> fm_facts st g ->
conc st g = conc st0 g ->
s1 = Z_to_bv 64 (RATP + 131696) ->
rw_cells segs m (bv_unsigned sp + -96) (rntf_frame junk s3o s2o s1o s0o raw) ->
stk segs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
evt segs (rntf_ret_post raw sp gp tp s0o s1o s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st m (fm_st st g) a0 a1)
(MS (mkR (Z_to_bv 64 (base + 0x288)) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (RATP + 131968)) (Z_to_bv 64 (conc st0 g)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x288)) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_6 w_7 w_26 w_27 w_31 w_32 w_93 w_94 w_245 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved segs base RATP. gw_expose_fam RATP.
intros until lo. intros MR MI MSL FMF Hcg S1 FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
unfold alloc_ceiling in *.
st1. st1. st1.
rewrite <- Hcg.
eapply (rntf_fm _ sp gp tp _ _ _ s0 s1 a1 a0 _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m junk raw s0o s1o s2o s3o st g lo);
first [gw_exact MR | assumption | gw_exact MSL | gw_exact FMF | gw_exact S1 | gw_exact FR | gw_exact ST | unfold alloc_ceiling; lia].
Qed.

End RC__1.

End G.
End Mq8.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QytA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QytA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8QT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8QT.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCa8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCa8.Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDXD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDXD.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkTt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkTt.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8QT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8QT.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy8Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy8Z.Mq9.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQRC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQRC.Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy8Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy8Z.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8l1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8l1.Mq5.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require Import CodeAt StepGen StepGenX StepGenX2 GwCallee GwApply GwFold.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G Require Import GwFamMalloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Open Scope bv_scope.
Open Scope Z_scope.

Definition errno_loc_code : list Z :=
[0x00020513; 0xf5c50513; 0x00008067]%Z.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment) (base : Z).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (rerrno_loc_entry rvm_wait_entry : Z).
Variables (w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 : Z).
Variables (hi_7 hi_10 hi_14 : bv 20).
Variables (lo_8 lo_12 lo_15 : bv 12).
Variables (joff_30 joff_98 joff_120 joff_173 joff_175 joff_181 : bv 21).
Variables (e_197bc e_24f80 : Z).
Hypothesis CODE : code_at segs base (alloc_meta_code w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 728.
Let rmmap_entry := (rvm_wait_entry + 4)%Z.
Let rmprotect_entry := (rvm_wait_entry + 240)%Z.
Hypothesis D_7 : decode_any (Z_to_bv 32 w_7) = Some (Auipc 10 hi_7, 4%Z).
Hypothesis E_7 : is_ecall (Z_to_bv 32 w_7) = false.
Hypothesis D_8 : decode_any (Z_to_bv 32 w_8) = Some (Load SZ8 true 18 10 lo_8, 4%Z).
Hypothesis E_8 : is_ecall (Z_to_bv 32 w_8) = false.
Hypothesis D_10 : decode_any (Z_to_bv 32 w_10) = Some (Auipc 11 hi_10, 4%Z).
Hypothesis E_10 : is_ecall (Z_to_bv 32 w_10) = false.
Hypothesis D_12 : decode_any (Z_to_bv 32 w_12) = Some (OpImm ALU_ADD 19 11 lo_12, 4%Z).
Hypothesis E_12 : is_ecall (Z_to_bv 32 w_12) = false.
Hypothesis D_14 : decode_any (Z_to_bv 32 w_14) = Some (Auipc 11 hi_14, 4%Z).
Hypothesis E_14 : is_ecall (Z_to_bv 32 w_14) = false.
Hypothesis D_15 : decode_any (Z_to_bv 32 w_15) = Some (OpImm ALU_ADD 8 11 lo_15, 4%Z).
Hypothesis E_15 : is_ecall (Z_to_bv 32 w_15) = false.
Hypothesis D_30 : decode_any (Z_to_bv 32 w_30) = Some (Jal 1 joff_30, 4%Z).
Hypothesis E_30 : is_ecall (Z_to_bv 32 w_30) = false.
Hypothesis D_98 : decode_any (Z_to_bv 32 w_98) = Some (Jal 1 joff_98, 4%Z).
Hypothesis E_98 : is_ecall (Z_to_bv 32 w_98) = false.
Hypothesis D_120 : decode_any (Z_to_bv 32 w_120) = Some (Jal 1 joff_120, 4%Z).
Hypothesis E_120 : is_ecall (Z_to_bv 32 w_120) = false.
Hypothesis D_173 : decode_any (Z_to_bv 32 w_173) = Some (Jal 1 joff_173, 4%Z).
Hypothesis E_173 : is_ecall (Z_to_bv 32 w_173) = false.
Hypothesis D_175 : decode_any (Z_to_bv 32 w_175) = Some (Jal 1 joff_175, 4%Z).
Hypothesis E_175 : is_ecall (Z_to_bv 32 w_175) = false.
Hypothesis D_181 : decode_any (Z_to_bv 32 w_181) = Some (Jal 1 joff_181, 4%Z).
Hypothesis E_181 : is_ecall (Z_to_bv 32 w_181) = false.
Hypothesis ANCH_8 : gw_anch (Z.shiftl (bv_signed hi_7) 12 + (base + 28) + bv_signed lo_8)%Z RGOT_SSP.
Hypothesis ANCH_12 : gw_anch (Z.shiftl (bv_signed hi_10) 12 + (base + 40) + bv_signed lo_12)%Z (RATP + 131960).
Hypothesis ANCH_15 : gw_anch (Z.shiftl (bv_signed hi_14) 12 + (base + 56) + bv_signed lo_15)%Z (RATP + 131728).
Hypothesis LINK_30 : gw_anch (base + 120 + bv_signed joff_30)%Z (e_24f80 + 0)%Z.
Hypothesis LINK_98 : gw_anch (base + 392 + bv_signed joff_98)%Z (rvm_wait_entry + 4)%Z.
Hypothesis LINK_120 : gw_anch (base + 480 + bv_signed joff_120)%Z (rvm_wait_entry + 4)%Z.
Hypothesis LINK_173 : gw_anch (base + 692 + bv_signed joff_173)%Z (rvm_wait_entry + 240)%Z.
Hypothesis LINK_175 : gw_anch (base + 700 + bv_signed joff_175)%Z (rerrno_loc_entry + 0)%Z.
Hypothesis LINK_181 : gw_anch (base + 724 + bv_signed joff_181)%Z (e_197bc + 0)%Z.
Hypothesis CODE_rerrno_loc_entry : code_at segs rerrno_loc_entry errno_loc_code.
Hypothesis AL_rerrno_loc_entry_b4 : gw_b4 rerrno_loc_entry.
Hypothesis RNG_rerrno_loc_entry_code : gw_br rerrno_loc_entry 12.
Hypothesis RNG_RATP : gw_br RATP 1896.
Hypothesis LAY_lo_RATP : gw_le (gw_RDATA2_LO + 164) RATP.
Hypothesis LAY_hi_RATP : gw_le ((RATP + 132896)) RIMG_HI.
Hypothesis AL_RATP : gw_al RATP 8.
Hypothesis RNG_RDEBRUIJN : gw_br RDEBRUIJN 159.
Hypothesis LAY_lo_RDEBRUIJN : gw_le (0x10000 + 0) RDEBRUIJN.
Hypothesis LAY_hi_RDEBRUIJN : gw_le ((RDEBRUIJN + 159)) gw_RTEXT_LO.
Hypothesis AL_RDEBRUIJN : gw_al RDEBRUIJN 8.
Hypothesis RNG_RGOT_SSP : gw_br RGOT_SSP 8.
Hypothesis LAY_lo_RGOT_SSP : gw_le (RDATA_LO + 0) RGOT_SSP.
Hypothesis LAY_hi_RGOT_SSP : gw_le ((RGOT_SSP + 8)) gw_RDATA2_LO.
Hypothesis AL_RGOT_SSP : gw_al RGOT_SSP 8.
Hypothesis LAY_win_0 : gw_win (0x10000 + 1) gw_RTEXT_LO.
Hypothesis LAY_win_1 : gw_win (gw_RTEXT_LO + 1) RDATA_LO.
Hypothesis LAY_win_2 : gw_win (RDATA_LO + 1) gw_RDATA2_LO.
Hypothesis LAY_win_3 : gw_win (gw_RDATA2_LO + 1) RIMG_HI.
Hypothesis LAY_win_4 : gw_win RIMG_HI 0x1000000.
Hypothesis AL_win_RIMG_HI : gw_winal RIMG_HI 4096.
Hypothesis AL_win_RDATA_LO : gw_winal RDATA_LO 4096.
Hypothesis AL_win_gw_RTEXT_LO : gw_winal gw_RTEXT_LO 4096.
Hypothesis AL_win_gw_RDATA2_LO : gw_winal gw_RDATA2_LO 4096.
Hypothesis ROM_RSIZE_CLASSES : QZDE.ro_bytes segs (RDEBRUIJN + 32) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RSIZE_CLASSES.
Hypothesis ROM_RDEBRUIJN : QZDE.ro_bytes segs RDEBRUIJN OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RDEBRUIJN.
Hypothesis ROM_RSMALL_CNT : QZDE.ro_bytes segs (RDEBRUIJN + 128) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RSMALL_CNT.
Hypothesis ROM_RMED_CNT : QZDE.ro_bytes segs (RDEBRUIJN + 155) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RMED_CNT.
Hypothesis ROM_reservedZ : QGeV.reservedZ segs = ref_reserved.
Hypothesis LAY_ref_reserved : ref_reserved = (cons (0x10000, gw_RTEXT_LO - 0x10000) (cons (gw_RTEXT_LO, RDATA_LO - gw_RTEXT_LO) (cons (RDATA_LO, gw_RDATA2_LO - RDATA_LO) (cons (gw_RDATA2_LO, RIMG_HI - gw_RDATA2_LO) nil))))%Z.
Hypothesis AL_rerrno_loc_entry : gw_al rerrno_loc_entry 4.
Hypothesis AL_rvm_wait_entry : gw_al rvm_wait_entry 4.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Definition ram_fp : ltac:(gw_rebind_ty (@QQRC.Mq5.ram_fp RATP) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QQRC.Mq5.ram_fp RATP) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@Q8l1.Mq5.ram_fp RATP) (@ram_fp) (gw_ent (@QQRC.Mq5.ram_fp RATP) (@ram_fp) gw_tbl_0)).
Definition rpres_except : ltac:(gw_rebind_ty (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@Q8l1.Mq5.rpres_except segs) (@rpres_except) (gw_ent (@QQRC.Mq5.rpres_except segs) (@rpres_except) (gw_ent (@QDXD.Mq2.rpres_except segs) (@rpres_except) (gw_ent (@QCa8.Mq5.rpres_except segs) (@rpres_except) (gw_ent (@Qy8Z.Mq9.rpres_except segs) (@rpres_except) gw_tbl_1))))).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@Q8l1.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QQRC.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@Qy8Z.Mq9.rarea_rep segs) (@rarea_rep) gw_tbl_2)))))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@Q8l1.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QQRC.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Qy8Z.Mq9.rmrep_areas segs) (@rmrep_areas) gw_tbl_3)))))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@Q8l1.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QQRC.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Qy8Z.Mq9.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_4)))))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@Q8l1.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QQRC.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Qy8Z.Mq9.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_5)))))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@Q8l1.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QQRC.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Qy8Z.Mq9.rgroup_rep segs) (@rgroup_rep) gw_tbl_6)))))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@Q8l1.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QQRC.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Qy8Z.Mq9.rmrep_groups segs) (@rmrep_groups) gw_tbl_7)))))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@Q8l1.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QQRC.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Qy8Z.Mq9.rshadow_rep segs) (@rshadow_rep) gw_tbl_8)))))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@Q8l1.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QQRC.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Qy8Z.Mq9.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_9)))))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@Q8l1.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QQRC.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Qy8Z.Mq9.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_10)))))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_11)).
Notation gw_tbl_12 := (gw_ent (@Q8l1.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QQRC.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Qy8Z.Mq9.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_11)))))))).
Definition ram_ret_post : ltac:(gw_rebind_ty (@QQRC.Mq5.ram_ret_post segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@QQRC.Mq5.ram_ret_post segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_12)).
Notation gw_tbl_13 := (gw_ent (@Q8l1.Mq5.ram_ret_post segs RATP RGOT_SSP ref_reserved RC__) (@ram_ret_post) (gw_ent (@QQRC.Mq5.ram_ret_post segs RATP RGOT_SSP ref_reserved RC__) (@ram_ret_post) gw_tbl_12)).
Definition ram_frame : ltac:(gw_rebind_ty (@QQRC.Mq5.ram_frame RC__) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@QQRC.Mq5.ram_frame RC__) constr:(gw_tbl_13)).
Notation gw_tbl_14 := (gw_ent (@Q8l1.Mq5.ram_frame RC__) (@ram_frame) (gw_ent (@QQRC.Mq5.ram_frame RC__) (@ram_frame) gw_tbl_13)).

Definition rmrep_meta_chunk : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_meta_chunk) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_meta_chunk)).
Definition rmrep_transport_high : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_transport_high) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_transport_high)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.
Definition rpres_except_trans : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_trans) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_trans)).

Definition rmrep_put_meta_frame : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_put_meta_frame) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_put_meta_frame)).
Definition rpres_except_of_munch_cov : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rpres_except_of_munch_cov) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rpres_except_of_munch_cov)).

Definition ram_fp_stack : ltac:(gw_ctx_fold_ty2 (@QQRC.Mq5.ram_fp_stack) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QQRC.Mq5.ram_fp_stack)).

#[using="RGOT_SSP rerrno_loc_entry e_197bc rvm_wait_entry rmmap_entry rmprotect_entry e_24f80 RATP RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_7 E_7 D_8 E_8 D_10 E_10 D_12 E_12 D_14 E_14 D_15 E_15 D_30 E_30 D_98 E_98 D_120 E_120 D_173 E_173 D_175 E_175 D_181 E_181 ANCH_8 ANCH_12 ANCH_15 LINK_30 LINK_98 LINK_120 LINK_173 LINK_175 LINK_181 CODE_rerrno_loc_entry AL_rerrno_loc_entry_b4 RNG_rerrno_loc_entry_code RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rerrno_loc_entry AL_rvm_wait_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ rmmap_entry rmprotect_entry"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := first [clear - hs segs base w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 hi_7 hi_10 hi_14 lo_8 lo_12 lo_15 joff_30 joff_98 joff_120 joff_173 joff_175 joff_181 RGOT_SSP rerrno_loc_entry e_197bc rvm_wait_entry rmmap_entry rmprotect_entry e_24f80 RATP RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_7 E_7 D_8 E_8 D_10 E_10 D_12 E_12 D_14 E_14 D_15 E_15 D_30 E_30 D_98 E_98 D_120 E_120 D_173 E_173 D_175 E_175 D_181 E_181 ANCH_8 ANCH_12 ANCH_15 LINK_30 LINK_98 LINK_120 LINK_173 LINK_175 LINK_181 CODE_rerrno_loc_entry AL_rerrno_loc_entry_b4 RNG_rerrno_loc_entry_code RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rerrno_loc_entry AL_rvm_wait_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ | clear - hs segs base w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 hi_7 hi_10 hi_14 lo_8 lo_12 lo_15 joff_30 joff_98 joff_120 joff_173 joff_175 joff_181 RGOT_SSP rerrno_loc_entry e_197bc rvm_wait_entry rmmap_entry rmprotect_entry e_24f80 RATP RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_7 E_7 D_8 E_8 D_10 E_10 D_12 E_12 D_14 E_14 D_15 E_15 D_30 E_30 D_98 E_98 D_120 E_120 D_173 E_173 D_175 E_175 D_181 E_181 ANCH_8 ANCH_12 ANCH_15 LINK_30 LINK_98 LINK_120 LINK_173 LINK_175 LINK_181 CODE_rerrno_loc_entry AL_rerrno_loc_entry_b4 RNG_rerrno_loc_entry_code RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rerrno_loc_entry AL_rvm_wait_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay].

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1.

#[using="rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 CODE rmmap_entry rmprotect_entry"] Lemma ram_disp_fin : forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
(m : word -> option byte) (st : mstate) (p : aptr) (r : region),
rmrep st m -> c_avail_meta_area_count (ctx st) <> 0 -> 0 <= c_avail_meta_area_count (ctx st) < 2^64 ->
c_avail_meta_areas (ctx st) = Some p -> (s_regions st) !! (fst p) = Some r -> pgal (snd p) -> 0 <= snd p -> snd p + 4096 <= round_up_pg (r_len r) ->
evt segs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (conc st p)) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 (RATP + 131960)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x2a8)) fc None m (seg_rom segs))
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 (RATP + 131960)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x108)) fc None m (seg_rom segs)).
Proof. clear - rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 CODE rmmap_entry rmprotect_entry segs base RATP. gw_expose_fam RATP.
intros until r. intros MR CNT CR AMA Hr SAL S0 S1.
pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. rewrite AMA in C1.
unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
pose proof WF as (_ & WR & _). destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & _). unfold alloc_ceiling in RBC.
pose proof (conc_region' st p r Hr) as Cp. pose proof (round_up_pg_ge (r_len r)) as RU.
assert (AL : Z.land (conc st p) 4095 = 0).
{ rewrite Cp. unfold pgal in SAL. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096.
clear - RBAL SAL S0 RB0 rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 CODE rmmap_entry rmprotect_entry segs base RATP. Z.div_mod_to_equations. lia. }
assert (AL' : Z.land 4095 (conc st p) = 0) by (rewrite Z.land_comm; gw_exact AL).
assert (PB : 0 <= conc st p < 2^64) by lia.
clear RBAL RU RBC RL0 WR.
gw_expose_fam RATP.

st1. st1.
assert (CF : negb (bv_eqb (Z_to_bv 64 (c_avail_meta_area_count (ctx st))) (Z_to_bv 64 0)) = true)
by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Bool.negb_true_iff; apply Z.eqb_neq; gw_exact CNT).
rewrite CF.

st1. apply Bool.negb_true_iff in CF. rewrite CF. clear CF.
st1. st1.

st1. st1. rewrite ?AL, ?AL'. st1.
change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true. cbv iota.
apply evt_done. reflexivity.
Qed.

#[using="w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 joff_173 CODE D_173 E_173 LINK_173 rmprotect_entry"] Lemma ram_to_mprotect : forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
(m : word -> option byte) (P : Z),
evt segs (fun ms' => ms' = MS (mkR (Z_to_bv 64 (base + 0x2b8)) sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 P)
(Z_to_bv 64 P) (Z_to_bv 64 4096) (Z_to_bv 64 3) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmprotect_entry) fc None m (seg_rom segs))
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x2a8)) fc None m (seg_rom segs)).
Proof. clear - w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 joff_173 CODE D_173 E_173 LINK_173 rmprotect_entry segs base.
intros.

st1. st1. st1. st1.
apply evt_done. unfold rmprotect_entry. reflexivity.
Qed.

#[using="w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 CODE"] Lemma ram_mp_ok0 : forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
(m : word -> option byte),
evt segs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x218)) fc None m (seg_rom segs))
(MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x2b8)) fc None m (seg_rom segs)).
Proof. clear - w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 CODE segs base.
intros.
st1. rewrite bv_eqb_refl. cbv iota.
apply evt_done. reflexivity.
Qed.

#[using="RIMG_HI gw_RDATA2_LO rerrno_loc_entry rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 joff_175 CODE BASE4 BASER D_175 E_175 LINK_175 CODE_rerrno_loc_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_4 rmmap_entry rmprotect_entry"] Lemma ram_mp_fail : forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
(m0 m : word -> option byte) (junk : list byte) (lo e : Z) (st : mstate),
rmrep st m -> mem_inv segs m -> tp = Z_to_bv 64 RATP ->
rw_cells segs m (errno_addr tp) [C4 (Z_to_bv 64 e)] -> 1 <= e <= 4095 -> e <> 38 ->
rpres_except (ram_fp st lo (bv_unsigned sp)) m0 m -> wmono segs m0 m ->
rw_cells segs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
stk segs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
evt segs (fun ms' => ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo st m0 st (Z_to_bv 64 0) ms'
/\ rw_cells segs (ms_mem ms') (errno_addr tp) [C4 (Z_to_bv 64 e)])
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (RATP + 131696)) (Z_to_bv 64 (RATP + 131960)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x2b8)) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI gw_RDATA2_LO rerrno_loc_entry rvm_wait_entry w_7 w_8 w_10 w_12 w_14 w_15 w_30 w_98 w_120 w_173 w_175 w_181 joff_175 CODE BASE4 BASER D_175 E_175 LINK_175 CODE_rerrno_loc_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_4 rmmap_entry rmprotect_entry segs base RATP. gw_expose_fam RATP.
intros until st. intros MR MI TP ERR ER E38 PE0 WM0 FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl segs m) as WM.
pose proof MR as (_ & _ & (_ & _ & _ & _ & GUARD) & _).
subst tp. rewrite (unsigned_lit RATP) in * by lia. change (RATP + -164) with (RATP + -164) in *.
change (Z_to_bv 64 e) with (wz e) in ERR.
(gw_expose_fam RATP; unfold alloc_ceiling, ram_frame in *).

st1. change (bv_eqb (Z_to_bv 64 (-1)) (Z_to_bv 64 0)) with false. cbv iota.

st1. st1. st1. st1.

st1. rewrite sx32_wz by lia. st1. st1.
assert (CF : bv_eqb (wz e) (Z_to_bv 64 38) = false)
by (unfold bv_eqb, wz; rewrite !unsigned_lit by lia; apply Z.eqb_neq; gw_exact E38).
rewrite CF; clear CF.

st1. st1. st1. st1. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }

st1. st1. st1. st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRX : rmrep st mX) end.
{ eapply rmrep_transport_high; [gw_exact MR| gw_exact MU| gw_exact WM|]. intros l h [E|[]]; inversion E; subst; unfold alloc_ceiling; lia. }
release_frame FR ST (bv_unsigned sp).
apply evt_done. split.
- unfold ram_ret_post. do 15 eexists. split; [reflexivity|].
split.
{ eapply rpres_except_trans; [gw_exact PE0|].
apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [gw_exact MU|gw_exact WM|].
cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply ram_fp_stack. lia. }
split; [eapply wmono_trans; [gw_exact WM0| gw_exact WM]|]. split; [assumption|]. split; [gw_exact ST|]. gw_exact MRX.
- cbn [ms_mem]. change (wz e) with (Z_to_bv 64 e) in ERR. gw_exact ERR.
Qed.

End RC__1.

End G.
