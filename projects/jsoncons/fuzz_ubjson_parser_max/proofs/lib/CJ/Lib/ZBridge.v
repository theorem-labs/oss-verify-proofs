(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import PropExec MState Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Lib_ZBridge () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.ZBridge."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.NArith.BinNat.N."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1andb"; "1bool"; "1false"; "1negb"; "1true"; "2and"; "2eq"; "2iff"; "2not"; "3N"; "3Z"; "4bv_eqb"; "4bv_lts"; "4bv_ltu"; "5inr64"; "6v_slt"]; ["6v_slti"; "6v_sltiu"; "6v_sltu"; "7le"; "8add"; "8b2z"; "8div"; "8eqb"; "8land"; "8le"; "8leb"; "8lor"; "8lt"; "8ltb"; "8lxor"; "8modulo"]; ["8mul"; "8pow"; "8shiftl"; "8shiftr"; "8sub"; "0a"; "0b"; "0e"; "0e1"; "0e2"; "0imm"; "0k"; "0m"; "0n"; "0p"; "9Z_to_bv"]; ["9bv"; "9bv_unsigned"; "9bv_wrap"; "0x"; "0y"; "0z"]]).
Definition inr64 (e : Z) : Prop := (0 <= e < 2^64)%Z.
Lemma zr_word : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge "9'Q@yR0%211&>&QAr1%2251%411pS861").
Proof. intros x. pose proof (bv_unsigned_in_range 64 x). unfold bv_modulus in *. exact H. Qed.
Lemma zr_bv : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge "@'9'Q@r1%211&Cr2yR0%3221&>&QAr3%2216%411p061pS8;1pRL?1").
Proof.
intros n x Hn. pose proof (bv_unsigned_in_range n x) as H. unfold bv_modulus, inr64 in *.
split; [lia|]. apply Z.lt_le_trans with (2 ^ Z.of_N n)%Z; [lia|]. apply Z.pow_le_mono_r; lia.
Qed.
Lemma zr_lit : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge "B':'5&Izr1%3221&L&Q1+2+R0%3221%5271%;271&>r2%211p041pS<A1").
Proof. intros; assumption. Qed.
Lemma zr_mod64 : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge ";':&>&Or1&Q1+2+R0%3221%6251%811pR@:1").
Proof. intros. unfold inr64. apply Z.mod_pos_bound. lia. Qed.
Lemma zr_mod : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge "E':'5&Izr1%3221+R0%5231%7231&>&Or3&Q1+2r2%3221%6251%811p0:1pRHC1pR@D1").
Proof.
intros e k Hk. unfold inr64. pose proof (Z.mod_pos_bound e (2^k) ltac:(apply Z.pow_pos_nonneg; lia)).
split; [lia|]. apply Z.lt_le_trans with (2^k)%Z; [lia|]. apply Z.pow_le_mono_r; lia.
Qed.
Lemma zr_mod_any : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge "F':'5&Lzr1%3221&I&Q1+2+R0%3221%5271%;271&>&Or3r2%3221%511p071pRND1pR@E1").
Proof. intros e p Hp. unfold inr64. pose proof (Z.mod_pos_bound e p ltac:(lia)). lia. Qed.
Lemma zr_land_l : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge "@':&>r2%211&Iz%2214&Hr4r3%3221%:11p061p0:1pR>>1pR<?1").
Proof.
intros a b [Ha Ha'] Hb. unfold inr64. pose proof (Z.land_nonneg a b) as Hn.
split; [lia|].
destruct (Z.eq_dec (Z.land a b) 0) as [->|Hnz]; [lia|].
destruct (Z.eq_dec a 0) as [->|Haz]. { rewrite Z.land_0_l. lia. }
apply Z.log2_lt_pow2; [lia|].
pose proof (Z.log2_land a b ltac:(lia) Hb).
assert (Z.log2 a < 64)%Z by (apply Z.log2_lt_pow2; lia). lia.
Qed.
Lemma zr_land_r : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge "@':&Izr2%3221&>%113&Hr4r3%3221%611p061p091pR>>1pR<?1").
Proof. intros. rewrite Z.land_comm. apply zr_land_l; assumption. Qed.
Lemma land_mask_mod : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge "I':'5&Izr1%3221&L&Q1+2+R0%3221%5271%;271'6&Hr3r2%3221&O%1249%6214%83E41p0:1pRJG1pR@H1").
Proof.
intros e m Hm. apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
destruct (Z.lt_ge_cases i 64).
- rewrite Z.mod_pow2_bits_low by lia. reflexivity.
- replace (Z.testbit m i) with false. { rewrite !andb_false_r. reflexivity. }
symmetry. destruct (Z.eq_dec m 0) as [->|]; [apply Z.bits_0|].
apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64%Z; [apply Z.log2_lt_pow2; lia|lia].
Qed.
Lemma zr_land_lit : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge "F':'5&Izr1%3221&L&Q1+2+R0%3221%5271%;271&>&Hr3r2%3221%511p071pRJD1pR@E1").
Proof.
intros e m Hm. rewrite land_mask_mod by exact Hm. apply zr_land_r; [|exact Hm].
apply Z.mod_pos_bound. lia.
Qed.
Lemma zr_lor : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge "=':&>r2%211&Kr4r3%3221%711p061p071pR>;1pR<<1").
Proof. intros a b Ha Hb. unfold inr64 in *. apply Z_lor_range; lia. Qed.
Lemma zr_lxor : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge "=':&>r2%211&Nr4r3%3221%711p061p071pR>;1pR<<1").
Proof. intros a b Ha Hb. unfold inr64 in *. apply Z_lxor_range; lia. Qed.
Lemma zr_shiftr : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge "@':&>r2%211&Iz%2214&Q3r4r3%3221%:11p061p0:1pRH>1pR<?1").
Proof. intros a k Ha Hk. unfold inr64 in *. apply Z_shiftr_range; lia. Qed.
Lemma zr_div : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge "@':&>r2%211&Lz%2214&Fr4r3%3221%:11p061p0:1pRH>1pR<?1").
Proof.
intros a k [Ha Ha'] Hk. unfold inr64. split. { apply Z.div_pos; lia. }
apply Z.le_lt_trans with a; [|lia]. apply Z.div_le_upper_bound; [lia|]. nia.
Qed.
Lemma zr_b2z : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge "7'1&>&Er1%211%411pR>61").
Proof. intros [|]; cbv; split; congruence. Qed.
Lemma zr_ite : forall (b : bool) x y, inr64 x -> inr64 y -> inr64 (if b then x else y).
Proof. intros [|]; auto. Qed.
Lemma inr64_unsigned_lit : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge ">':&>r1%211'6&QAyR0&Q?r2%2231%5241%73;13p091pR@=1").
Proof. intros e H. apply unsigned_lit. exact H. Qed.
Ltac is_Zlit_zb a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
Ltac slim := repeat match goal with x := _ : Z |- _ => clearbody x end.
Ltac flia := first [ assumption | slim; lia | lia ].
Ltac zrange :=
lazymatch goal with
| |- inr64 ?e =>
lazymatch e with
| bv_unsigned _ => first [ apply zr_word | apply zr_bv; vm_compute; congruence ]
| Z.land _ ?mk => first [ is_Zlit_zb mk; apply zr_land_lit; flia
| apply zr_land_l; [zrange | zrange_nonneg] | apply zr_land_r; [zrange_nonneg | zrange] ]
| Z.lor _ _ => apply zr_lor; [zrange | zrange]
| Z.lxor _ _ => apply zr_lxor; [zrange | zrange]
| Z.shiftr _ _ => apply zr_shiftr; [zrange | flia]
| Z.modulo _ (2^64)%Z => apply zr_mod64
| Z.modulo _ _ => first [ apply zr_mod_any; flia | apply zr_mod; flia ]
| Z.div _ _ => apply zr_div; [zrange | flia]
| Z.b2z _ => apply zr_b2z
| (if _ then _ else _) => apply zr_ite; [zrange | zrange]
| _ => first [ apply zr_lit; flia
| is_var e; progress (unfold e); zrange ]
end
| |- (0 <= ?e < _)%Z => change (inr64 e); zrange
end
with zrange_nonneg :=
lazymatch goal with
| |- (0 <= ?e)%Z =>
first [ apply (proj1 (A:=(0 <= e)%Z) (B:=(e < 2^64)%Z)); change (inr64 e); zrange
| apply Z.land_nonneg; left; zrange_nonneg
| apply Z.lor_nonneg; split; zrange_nonneg
| apply Z.lxor_nonneg; split; zrange_nonneg
| apply Z.shiftr_nonneg; zrange_nonneg
| apply Z.shiftl_nonneg; zrange_nonneg
| flia
| is_var e; progress (unfold e); zrange_nonneg ]
end.
Lemma Z_to_bv_mod64 : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge "A':'6'Q@yR0%211&Q?&Or1&Q1+2+R0%3221%6251%82:1%92;7%>3;21pR@@1").
Proof.
intros e. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64)%Z.
apply Z.mod_mod. lia.
Qed.
Lemma zb_land_pow2_small : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge "H':'5&Izr2%3221&L&Q1+2r1%3221%5271%;271'6&Hr4r3%:291%4231%63C1@p0?1p091pRHF1pS:G1").
Proof.
intros y k Hy Hk. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
destruct (Z.eq_dec i k) as [->|Hne].
- rewrite Z.pow2_bits_true by lia. rewrite andb_true_r.
apply Z.testbit_false; [lia|]. rewrite Z.div_small by lia. reflexivity.
- rewrite Z.pow2_bits_eqb by lia. replace (k =? i)%Z with false by (symmetry; apply Z.eqb_neq; lia). apply andb_false_r.
Qed.
Lemma zb_lxor_pow2_small : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge "J':'5&Izr2%3221&L&Q1+2r1%3221%5271%;271'6&Nr4r3%:291%4231&D%1253%83E31p0A1p0;1pRHH1pS:I1").
Proof. intros. symmetry. apply Z.add_nocarry_lxor. apply zb_land_pow2_small; assumption. Qed.
Lemma zb_lxor_sign : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge "J':'5&Izr1%3221&L&Q1+2+R0%3221%5271%;271'6&Nr2+QO%:291%4231&O&D%1264%321<%:3G51p0<1pS8I1").
Proof.
intros x Hx. destruct (Z.lt_ge_cases x (2^63)).
- rewrite zb_lxor_pow2_small by lia. rewrite Z.mod_small by lia. reflexivity.
- set (y := (x - 2^63)%Z). replace x with (y + 2^63)%Z by lia.
rewrite <- (zb_lxor_pow2_small y 63) at 1 by lia. rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r.
replace (y + 2^63 + 2^63)%Z with (y + 1 * 2^64)%Z by lia. rewrite Z.mod_add, Z.mod_small by lia. reflexivity.
Qed.
Lemma zb_signed : forall x : word,
bv_signed x = (if bv_unsigned x <? 2^63 then bv_unsigned x else bv_unsigned x - 2^64)%Z.
Proof.
intros x. pose proof (bv_unsigned_in_range 64 x) as Hr. unfold bv_modulus in Hr.
unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 64)%Z with (2^64)%Z in *. change (2^64 / 2)%Z with (2^63)%Z.
destruct (Z.ltb_spec0 (bv_unsigned x) (2^63)).
- rewrite Z.mod_small by lia. lia.
- rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma bv_eqb_Z : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge "A'Q@yR0%211'6'1&;r2r1%33721&G&QA%12:5%22;5%4221%;3:61pS:=1pS8>1").
Proof. reflexivity. Qed.
Lemma bv_ltu_Z : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge "A'Q@yR0%211'6'1&=r2r1%33721&M&QA%12:5%22;5%4221%;3:61pS:=1pS8>1").
Proof. reflexivity. Qed.
Lemma bv_lts_lxor : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge "H'Q@yR0%211'6'1&<r2r1%33721&M&N&QA%12;6&Q1+2+QO%3221%7251%72A;%9213%;231%B3A=1pS:D1pS8E1").
Proof.
intros x y. unfold bv_lts. rewrite !zb_signed.
pose proof (bv_unsigned_in_range 64 x) as Hx. pose proof (bv_unsigned_in_range 64 y) as Hy. unfold bv_modulus in *.
change (2 ^ Z.of_N 64)%Z with (2^64)%Z in *.
rewrite !zb_lxor_sign by lia.
destruct (Z.ltb_spec0 (bv_unsigned x) (2^63)); destruct (Z.ltb_spec0 (bv_unsigned y) (2^63)).
- rewrite !Z.mod_small by lia. apply eq_true_iff_eq. rewrite !Z.ltb_lt. lia.
- rewrite (Z.mod_small (bv_unsigned x + _)) by lia.
rewrite <- (Z.mod_add (bv_unsigned y + _) (-1)), Z.mod_small by lia. apply eq_true_iff_eq. rewrite !Z.ltb_lt. lia.
- rewrite (Z.mod_small (bv_unsigned y + _)) by lia.
rewrite <- (Z.mod_add (bv_unsigned x + _) (-1)), Z.mod_small by lia. apply eq_true_iff_eq. rewrite !Z.ltb_lt. lia.
- rewrite <- (Z.mod_add (bv_unsigned x + _) (-1)), Z.mod_small by lia.
rewrite <- (Z.mod_add (bv_unsigned y + _) (-1)), Z.mod_small by lia. apply eq_true_iff_eq. rewrite !Z.ltb_lt. lia.
Qed.
Lemma bv_lts_zero_r : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge "E'Q@yR0%211'6'1&<r1&Q?z%2281%53941&J&Q1+2+QO%3221&QA%12@;%7231%@3?91pS8B1").
Proof.
intros x. unfold bv_lts. rewrite (zb_signed x). change (bv_signed (Z_to_bv 64 0)) with 0%Z.
pose proof (bv_unsigned_in_range 64 x) as Hx. unfold bv_modulus in Hx. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Hx.
destruct (Z.ltb_spec0 (bv_unsigned x) (2^63)); apply eq_true_iff_eq; rewrite Z.ltb_lt, Z.leb_le; lia.
Qed.
Lemma bv_lts_zero_l : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge "H'Q@yR0%211'6'1&<&Q?z%2271r1%53921&0&M&QA%12=5%3281&Q1+2+QO%3221%8261%:261%C3B<1pS8E1").
Proof.
intros x. unfold bv_lts. rewrite (zb_signed x). change (bv_signed (Z_to_bv 64 0)) with 0%Z.
pose proof (bv_unsigned_in_range 64 x) as Hx. unfold bv_modulus in Hx. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Hx.
destruct (Z.ltb_spec0 (bv_unsigned x) (2^63)); apply eq_true_iff_eq; rewrite andb_true_iff, !Z.ltb_lt; lia.
Qed.
Lemma v_sltu_b2z : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge "D'Q@yR0%211'6&Br2r1%3221&Q?&E&M&QA%12;7%22<7%4221%611%82?1%>3?:1pS:@1pS8A1").
Proof. intros. unfold v_sltu, c_ltu, bv_ltu. destruct (Z.ltb _ _); reflexivity. Qed.
Lemma v_slt_b2z : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge "K'Q@yR0%211'6&?r2r1%3221&Q?&E&M&N&QA%12<8&Q1+2+QO%3221%7251%72B=%9213%;231%=11%?2F1%E3FA1pS:G1pS8H1").
Proof. intros. unfold v_slt, c_lts. rewrite bv_lts_lxor. destruct (Z.ltb _ _); reflexivity. Qed.
Lemma v_sltiu_b2z : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge "F'Q@yR0%211':'6&Ar2r1%3221&Q?&E&M&QA%12<7&QB%12>8%5231%711%92A1%?3A;1pRFA1pS8C1").
Proof. intros. unfold v_sltiu. destruct (Z.ltb _ _); reflexivity. Qed.
Lemma v_slti_b2z : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge "L'Q@yR0%211':'6&@r2r1%3221&Q?&E&M&N&QA%12=8&Q1+2+QO%3221%7251&D%12>3%;231%=11%?2G1%E3GA1pRFG1pS8I1").
Proof.
intros. unfold v_slti, zsig. rewrite zb_signed.
pose proof (bv_unsigned_in_range 64 x) as Hx. unfold bv_modulus in Hx. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Hx.
rewrite zb_lxor_sign by lia.
destruct (Z.ltb_spec0 (bv_unsigned x) (2^63)).
- rewrite Z.mod_small by lia.
destruct (Z.ltb_spec0 (bv_unsigned x) imm); destruct (Z.ltb_spec0 (bv_unsigned x + 2^63) (imm + 2^63)); try reflexivity; exfalso; lia.
- rewrite <- (Z.mod_add _ (-1)), Z.mod_small by lia.
destruct (Z.ltb_spec0 (bv_unsigned x - 2^64) imm); destruct (Z.ltb_spec0 (bv_unsigned x + 2^63 + -1 * 2^64) (imm + 2^63)); try reflexivity; exfalso; lia.
Qed.
Lemma zb_b2z_if : forall b, Z.b2z b = (if b then 1 else 0)%Z.
Proof. intros [|]; reflexivity. Qed.
Lemma zb_b2z_nonzero : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge "?'1&7&8'6':&Er1%211z%63521%811(4%93<61%<231pR>>1").
Proof. intros [|]; cbv; split; congruence. Qed.
Lemma zb_b2z_zero : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge "='1&7'6':&Er1%211z%63521(2%83:51%:231pR><1").
Proof. intros [|]; cbv; split; congruence. Qed.
Lemma zb_b2z_eqb0 : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge "<'1'6&G&Er1%211z%5221&3%115%93:31pR>;1").
Proof. intros [|]; reflexivity. Qed.
Lemma zb_b2z_range : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge "<'1'5&Iz&Er1%211%5241+1%7231%9231pR>;1").
Proof. intros [|]; cbv; split; congruence. Qed.
Lemma zb_land_mask : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge "F':&Izr1%3221'6&Hr3&Q4&Q1+2r2%3221+1%6221%9281&O%12:5%=3B31p0?1pRHD1pS8E1").
Proof. intros. rewrite <- Z.land_ones by lia. unfold Z.ones. rewrite Z.shiftl_1_l. f_equal. Qed.
Lemma zb_land_mask_l : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge "F':&Izr1%3221'6&H&Q4&Q1+2r2%3221+1%6221r3%9221&O%1236%=3B31p0?1pRHD1pS8E1").
Proof. intros. rewrite Z.land_comm. apply zb_land_mask. assumption. Qed.
Lemma zb_shiftl_mul : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge "C':&Izr1%3221'6&Q2r3r2%3221&Q0&Q1+2%2215%4271%:3?61p0<1pRHA1pS8B1").
Proof. intros. apply Z.shiftl_mul_pow2. assumption. Qed.
Lemma zb_shiftr_div : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge "C':&Izr1%3221'6&Q3r3r2%3221&F&Q1+2%2215%4271%:3?61p0<1pRHA1pS8B1").
Proof. intros. apply Z.shiftr_div_pow2. assumption. Qed.
Lemma zb_shl_shr : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge "Q0':&Izr2%3221'5&L%1254+R0%3261%5231'6&Q3&O&Q2r4r3%3221&Q1+2%221<%8241%:216&Q4%12@8%7261%=2;1%@3K51p0B1p0I1pRHN1pS8O1").
Proof.
intros x k Hx Hk. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
replace (2^64)%Z with (2^(64-k) * 2^k)%Z by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
rewrite Z.mul_mod_distr_r by lia. apply Z.div_mul. lia.
Qed.
Lemma zb_shr_shl : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge "H':&Izr2%3221'6&Q2&Q3r4r3%3221%5212&Q4&O&Q1+2%2217%4291%62:1%>3C81p0@1p0A1pRHF1pS8G1").
Proof.
intros x k Hx Hk. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
pose proof (Z.div_mod x (2^k) ltac:(lia)). lia.
Qed.
Lemma zb_lor_eq0 : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge "@':&7'6&Kr2r1%3221z%63821'5%83:63%93;64%3221%<251pR>>1pR<?1").
Proof. intros. apply Z.lor_eq_0_iff. Qed.
Lemma zb_lor_eqb0 : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge "F':&Izr2%3221'6'1&G&Kr4r3%3221%521:&0%725<%825=%3221%<3;51p0>1p0?1pR>D1pR<E1").
Proof.
intros a b Ha Hb. apply eq_true_iff_eq. rewrite andb_true_iff, !Z.eqb_eq. apply Z.lor_eq_0_iff.
Qed.
Lemma zb_lxor_eq0 : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge "=':&7'6&Nr2r1%3221z%63821%73954%9221pR>;1pR<<1").
Proof. intros. apply Z.lxor_eq_0_iff. Qed.
Lemma zb_lxor_eqb0 : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge ">':'6'1&G&Nr2r1%3221z%6221%7254%:3921pR><1pR<=1").
Proof.
intros. apply eq_true_iff_eq. rewrite !Z.eqb_eq. apply Z.lxor_eq_0_iff.
Qed.
Lemma zb_land_lor_distr_l : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge "@':'6&H&Kr3r2%3221r1%6221%7252%8253%8221%;3<41pRJ=1pR>>1pR<?1").
Proof. intros. apply Z.land_lor_distr_l. Qed.
Lemma zb_lxor_ones : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge "G':'5&Izr1%3221&L&Q1+2+R0%3221%5271%;271'6&Nr2+_oooooooooooO%3221&Q4%1234%73D31p091pS8F1").
Proof.
intros x Hx. change 18446744073709551615%Z with (Z.ones 64).
pose proof (Z.add_lnot_diag x).
assert (E : Z.lxor x (Z.ones 64) = ((Z.lnot x) mod 2^64)%Z).
{ rewrite <- Z.land_ones by lia. apply Z.bits_inj'. intros i Hi.
rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia.
destruct (Z.lt_ge_cases i 64).
- rewrite Z.ones_spec_low by lia. rewrite xorb_true_r, andb_true_r. reflexivity.
- rewrite Z.ones_spec_high by lia. rewrite xorb_false_r, andb_false_r.
destruct (Z.eq_dec x 0) as [->|]; [apply Z.bits_0|].
apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64%Z; [apply Z.log2_lt_pow2; lia|lia]. }
rewrite E. unfold Z.ones. rewrite Z.shiftl_1_l. change (Z.pred (2^64)) with (2^64 - 1)%Z.
replace (Z.lnot x) with (-x - 1)%Z by lia.
rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Ltac mlia := Z.div_mod_to_equations; lia.
Ltac zb_fold_lits :=
repeat match goal with
| |- context [Z.shiftr ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.shiftr a b) in change (Z.shiftr a b) with v
| |- context [Z.shiftl ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.shiftl a b) in change (Z.shiftl a b) with v
| |- context [Z.land ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.land a b) in change (Z.land a b) with v
| |- context [Z.lor ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.lor a b) in change (Z.lor a b) with v
| |- context [Z.lxor ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.lxor a b) in change (Z.lxor a b) with v
| |- context [Z.modulo ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.modulo a b) in change (Z.modulo a b) with v
| |- context [Z.pow ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.pow a b) in change (Z.pow a b) with v
| |- context [Z.sub ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.sub a b) in change (Z.sub a b) with v
| |- context [bv_wrap ?n ?z] => is_Zlit_zb z; let v := eval vm_compute in (bv_wrap n z) in
replace (bv_wrap n z) with v by (vm_compute; reflexivity)
| |- context [Z_to_bv 64 ?z] => is_Zlit_zb z;
lazymatch eval vm_compute in (Z.leb 18446744073709551616 z) with true => idtac end;
let v := eval vm_compute in (z mod 18446744073709551616)%Z in
replace (Z_to_bv 64 z) with (Z_to_bv 64 v) by (apply bv_eq; vm_compute; reflexivity)
end.
Lemma unsigned_lit_land : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge "=':'6&QAyR0&Q?r1%2231%5241&H+_oooooooooooO%2251%:3;41pR@<1").
Proof. intros. rewrite unsigned_lit_wrap. change 18446744073709551615%Z with (Z.ones 64). symmetry. apply Z.land_ones. lia. Qed.
Lemma Z_to_bv_land64 : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge ">':'6'Q@yR0%211&Q?&Hr1+_oooooooooooO%3221%5271%6284%;3821pR@=1").
Proof. intros. rewrite <- unsigned_lit_land. apply Z_to_bv_bv_unsigned. Qed.
Lemma zb_shl_shr_land : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge "Q2':&Izr2%3221'5&L%1254+R0%3261%5231'6&Q3&H&Q2r4r3%3221+_oooooooooooO%6221%8214&Q4&Q1+2%32@8%3221+1%6221%?2=1%B3M91p0D1p0K1pRHQ01pS8Q11").
Proof.
intros x k Hx Hk. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
rewrite zb_shl_shr, <- zb_land_mask by lia. reflexivity.
Qed.
Ltac zs_wrap e := rewrite (unsigned_lit_wrap e).
Ltac zs_wrap_in e H := rewrite (unsigned_lit_wrap e) in H.
Ltac zs_idioms :=
match goal with
| |- context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e)
| |- context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e)
| |- context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] =>
rewrite (zb_shl_shr x k) by (first [lia | zrange_nonneg])
end.
Ltac zs_idioms_in H :=
match type of H with
| context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e) in H
| context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e) in H
| context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] =>
rewrite (zb_shl_shr x k) in H by (first [lia | zrange_nonneg])
end.
Ltac zs_wrap_land e := rewrite (unsigned_lit_land e).
Ltac zs_wrap_land_in e H := rewrite (unsigned_lit_land e) in H.
Ltac zs_idioms_land :=
match goal with
| |- context [Z.shiftr (Z.land (Z.shiftl ?x ?k) 18446744073709551615) ?k] =>
rewrite (zb_shl_shr_land x k) by (first [lia | zrange_nonneg])
end.
Ltac zs_idioms_land_in H :=
match type of H with
| context [Z.shiftr (Z.land (Z.shiftl ?x ?k) 18446744073709551615) ?k] =>
rewrite (zb_shl_shr_land x k) in H by (first [lia | zrange_nonneg])
end.
Ltac zsimp_slt :=
(lazymatch goal with |- context [v_sltu] => rewrite ?v_sltu_b2z | _ => idtac end);
(lazymatch goal with |- context [v_slt] => rewrite ?v_slt_b2z | _ => idtac end);
(lazymatch goal with |- context [v_sltiu] => rewrite ?v_sltiu_b2z | _ => idtac end);
(lazymatch goal with |- context [v_slti] => rewrite ?v_slti_b2z | _ => idtac end).
Ltac zsimp :=
zsimp_slt;
cbv delta [zxb];
zb_fold_lits;
repeat match goal with
| |- context [bv_unsigned (Z_to_bv 64 ?e)] =>
first [ rewrite (inr64_unsigned_lit e) by zrange
| zs_wrap e ]
| |- _ => progress zs_idioms
end; zb_fold_lits.
Ltac zb_fold_lits_in H :=
repeat match type of H with
| context [Z.shiftr ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.shiftr a b) in change (Z.shiftr a b) with v in H
| context [Z.shiftl ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.shiftl a b) in change (Z.shiftl a b) with v in H
| context [Z.land ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.land a b) in change (Z.land a b) with v in H
| context [Z.lor ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.lor a b) in change (Z.lor a b) with v in H
| context [Z.lxor ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.lxor a b) in change (Z.lxor a b) with v in H
| context [Z.pow ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.pow a b) in change (Z.pow a b) with v in H
| context [Z.sub ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.sub a b) in change (Z.sub a b) with v in H
| context [bv_wrap ?n ?z] => is_Zlit_zb z; let v := eval vm_compute in (bv_wrap n z) in
replace (bv_wrap n z) with v in H by (vm_compute; reflexivity)
end.
Ltac zsimp_in H :=
rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z in H;
cbv delta [zxb] in H;
zb_fold_lits_in H;
repeat match type of H with
| context [bv_unsigned (Z_to_bv 64 ?e)] =>
first [ rewrite (inr64_unsigned_lit e) in H by zrange
| zs_wrap_in e H ]
| _ => progress (zs_idioms_in H)
end; zb_fold_lits_in H.
Ltac decide_tests :=
repeat match goal with
| |- context [Z.eqb ?x ?y] =>
first [ rewrite (proj2 (Z.eqb_eq x y)) by mlia | rewrite (proj2 (Z.eqb_neq x y)) by mlia ]
| |- context [Z.ltb ?x ?y] =>
first [ rewrite (proj2 (Z.ltb_lt x y)) by mlia | rewrite (proj2 (Z.ltb_ge x y)) by mlia ]
| |- context [Z.leb ?x ?y] =>
first [ rewrite (proj2 (Z.leb_le x y)) by mlia | rewrite (proj2 (Z.leb_gt x y)) by mlia ]
end; cbn [andb orb negb].
Lemma b2z_word_nez : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge "@'1'6&3&;yR0&Q?&Er1%211%4251z%6271%93831%;11%=3>17pR>?1").
Proof. intros [|]; reflexivity. Qed.
Lemma b2z_word_eqz : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge "@'1'6&;yR0&Q?&Er1%211%4251z%6271%93831&3%117%=3>31pR>?1").
Proof. intros [|]; reflexivity. Qed.
Ltac zr_pose e := let H := fresh "R" in assert (H : inr64 e) by zrange; unfold inr64 in H.
Ltac zb_masks :=
repeat match goal with
| |- context [Z.land ?x ?m] =>
is_Zlit_zb m;
let k := eval vm_compute in (Z.log2 (m + 1)) in
let m' := eval vm_compute in (2 ^ k - 1)%Z in
constr_eq m m';
let p := eval vm_compute in (2 ^ k)%Z in
replace (Z.land x m) with (x mod p)%Z by (symmetry; change m with (2^k - 1)%Z; change p with (2^k)%Z; apply zb_land_mask; lia)
| H : context [Z.land ?x ?m] |- _ =>
is_Zlit_zb m;
let k := eval vm_compute in (Z.log2 (m + 1)) in
let m' := eval vm_compute in (2 ^ k - 1)%Z in
constr_eq m m';
let p := eval vm_compute in (2 ^ k)%Z in
replace (Z.land x m) with (x mod p)%Z in H by (symmetry; change m with (2^k - 1)%Z; change p with (2^k)%Z; apply zb_land_mask; lia)
end.
Ltac pose_word_ranges :=
repeat match goal with
| |- context [bv_unsigned ?x] =>
lazymatch goal with
| _ : (0 <= bv_unsigned x < _)%Z |- _ => fail
| _ => pose proof (zr_word x : (0 <= bv_unsigned x < 2^64)%Z)
end
| _ : context [bv_unsigned ?x] |- _ =>
lazymatch goal with
| _ : (0 <= bv_unsigned x < _)%Z |- _ => fail
| _ => pose proof (zr_word x : (0 <= bv_unsigned x < 2^64)%Z)
end
end.
Ltac zb_bits_norm :=
intros;
rewrite ?Z.land_lor_distr_l in *;
rewrite ?Z.lor_eq_0_iff in *;
rewrite ?zb_lxor_eq0 in *;
zb_masks;
rewrite ?Z.shiftr_div_pow2 in * by lia;
zb_fold_lits.
Ltac blia := zb_bits_norm; pose_word_ranges; mlia.
Ltac decide_tests_b :=
repeat match goal with
| |- context [Z.eqb ?x ?y] =>
first [ rewrite (proj2 (Z.eqb_eq x y)) by blia | rewrite (proj2 (Z.eqb_neq x y)) by blia ]
| |- context [Z.ltb ?x ?y] =>
first [ rewrite (proj2 (Z.ltb_lt x y)) by blia | rewrite (proj2 (Z.ltb_ge x y)) by blia ]
| |- context [Z.leb ?x ?y] =>
first [ rewrite (proj2 (Z.leb_le x y)) by blia | rewrite (proj2 (Z.leb_gt x y)) by blia ]
end; cbn [andb orb negb].
Lemma zb_negb_eqb0 : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge "A':&Izr1%3221'6'1&3&Gr2%2218%411&M%12;4%93831p0;1pS8@1").
Proof. intros x Hx. destruct (Z.eqb_spec x 0); destruct (Z.ltb_spec0 0 x); cbn; try reflexivity; exfalso; lia. Qed.
Lemma Z_to_bv_eqm : ltac2:(TCodec.tc2 tcn__CJ_Lib_ZBridge "G':'6&Or2&Q1+2+R0%3221%6251r1%8213%:3;31'Q@yR0%211&Q?r3%2241%325?%B3521p091pRDE1pRBF1").
Proof. intros e1 e2 H. rewrite <- (Z_to_bv_mod64 e1), <- (Z_to_bv_mod64 e2), H. reflexivity. Qed.
Ltac word_eq_tac :=
first [ exact eq_refl
| f_equal; lia
| apply Z_to_bv_eqm; Z.div_mod_to_equations; lia
| apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia ].
