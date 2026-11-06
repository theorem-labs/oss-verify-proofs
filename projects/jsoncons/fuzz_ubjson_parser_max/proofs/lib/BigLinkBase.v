(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Instr Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec AxSymExec3.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BigModel BigFactsBase BigFactsDigits.
Import -(notations) BigModel BigFactsBase BigFactsDigits.
Import ListNotations.
Import AX2.
Unset Lia Cache. Unset Nra Cache. Unset Nia Cache.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__BigLinkBase () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Sem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3.AX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BigFactsBase."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BigLinkBase.BL."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BigModel."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BigModel.W."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0B"; "1Some"; "1bool"; "1fst"; "1nat"; "1option"; "1snd"; "1true"; "2and"; "2eq"; "2iff"; "3lt"; "4Z"; "0E"; "5aluop"]; ["5mulop"; "6alu64"; "6mul_div"; "7edenot"; "7env"; "7evars_lt"; "7expr"; "8wordZ"; "9MM"; "9inrange"; "9uv"; "9za"; "9zalu"; "9zb"; "9zcomp"; "9zden"]; ["9zeval"; "9zmd"; ":DDproduct"; ";M"; ";add"; ";b2z"; ";ltu"; ";mul"; "<add"; "<div"; "<le"; "<lt"; "<ltb"; "<modulo"; "<mul"; "<sub"]; ["0V"; "0V'"; "0a"; "0b"; "0e"; "0n"; "0op"; "=Z_to_bv"; "=bv"; "=bv_unsigned"; "0t"; "0w"; "0x"; "0z"]]).
Module BL.
Definition MM : Z := 2 ^ 64.
Lemma MM_WM : ltac2:(TCodec.tc2 tcn__BigLinkBase "5':'=&H&Q3%43321"). Proof. rewrite M_val. reflexivity. Qed.
Lemma MM_val : ltac2:(TCodec.tc2 tcn__BigLinkBase "5':'=&H+`PPPPPPPPPPP0%43321"). Proof. reflexivity. Qed.
Definition zalu (op : aluop) (a b : Z) : option Z :=
match op with
| ALU_ADD => Some ((a + b) mod MM)
| ALU_SUB => Some ((a - b) mod MM)
| ALU_SLL => Some ((a * 2 ^ (b mod 64)) mod MM)
| ALU_SRL => Some (a / 2 ^ (b mod 64))
| ALU_SLTU => Some (if a <? b then 1 else 0)
| ALU_AND => Some (Z.land a b)
| ALU_OR => Some (Z.lor a b)
| ALU_XOR => Some (Z.lxor a b)
| ALU_SLT | ALU_SRA => None
end.
Definition zmd (op : mulop) (a b : Z) : option Z :=
match op with
| M_MUL => Some ((a * b) mod MM)
| M_MULHU => Some ((a * b) / MM)
| M_DIVU => Some (if b =? 0 then MM - 1 else a / b)
| M_REMU => Some (if b =? 0 then a else a mod b)
| _ => None
end.
Fixpoint zeval (V : nat -> Z) (e : expr) : option Z :=
match e with
| ELit z => Some (z mod MM)
| EVar n => Some (V n)
| EAlu op a b => match zeval V a, zeval V b with Some x, Some y => zalu op x y | _, _ => None end
| EMd op a b => match zeval V a, zeval V b with Some x, Some y => zmd op x y | _, _ => None end
| _ => None
end.
Definition uv (E : env) (n : nat) : Z := bv_unsigned (ev E n).
Definition inrange (z : Z) : Prop := 0 <= z < MM.
Lemma bvu_range : ltac2:(TCodec.tc2 tcn__BigLinkBase "9'QHyR0%211&I&QIr1%2251%411pSH61").
Proof. intros w. unfold inrange, MM. pose proof (bv_unsigned_in_range 64 w). unfold bv_modulus in H. exact H. Qed.
Lemma zalu_sound : ltac2:(TCodec.tc2 tcn__BigLinkBase "N'?'QHyR0%211'=':'6%113&Lr4&QIr3%22:1r2%42<1%73631(2r1%22>1%>3<41&Ar5%231=;%=2E1%C3D1;p061pSLF1pS8H1pS6I1pS>M1").
Proof. intros op a b z.
pose proof (bvu_range a) as Ra. pose proof (bvu_range b) as Rb. unfold inrange in *.
unfold alu64, alu, zalu. destruct op; intros H; inversion H; subst; clear H.
- rewrite bv_add_unsigned. reflexivity.
- rewrite bv_sub_unsigned. reflexivity.
- rewrite bv_shiftl_unsigned. unfold bv_wrap. rewrite bv_and_unsigned, Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with MM. rewrite (Z.mod_small 63) by (unfold MM; lia).
rewrite Z.shiftl_mul_pow2. 2: apply Z.land_nonneg; lia. change 63 with (Z.ones 6). rewrite Z.land_ones by lia. reflexivity.
- unfold bv_ltu. destruct (Z.ltb _ _); rewrite Z_to_bv_unsigned; reflexivity.
- rewrite bv_xor_unsigned. reflexivity.
- rewrite bv_shiftr_unsigned, bv_and_unsigned, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with MM.
rewrite (Z.mod_small 63) by (unfold MM; lia). rewrite Z.shiftr_div_pow2. 2: apply Z.land_nonneg; lia.
change 63 with (Z.ones 6). rewrite Z.land_ones by lia. reflexivity.
- rewrite bv_or_unsigned. reflexivity.
- rewrite bv_and_unsigned. reflexivity.
Qed.
Lemma zmd_sound : ltac2:(TCodec.tc2 tcn__BigLinkBase "N'@'QHyR0%211'=':'6%113&Q1r4&QIr3%22:1r2%42<1%73631(2r1%22>1%>3<41&Br5%24D1=;%=2E1%C3D1;p061pSLF1pS8H1pS6I1pS>M1").
Proof. intros op a b z.
pose proof (bvu_range a) as Ra. pose proof (bvu_range b) as Rb. unfold inrange in *.
unfold mul_div, zmd. destruct op; intros H; inversion H; subst; clear H.
- rewrite bv_mul_unsigned. reflexivity.
- unfold bv_mulhuu. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with MM.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ Z.of_N 64) with MM. apply Z.mod_small. split.
apply Z.div_pos; unfold MM; lia. apply Z.div_lt_upper_bound. unfold MM; lia. unfold MM in *; nia.
- destruct (Z.eqb_spec (bv_unsigned b) 0). rewrite Z_to_bv_unsigned. reflexivity. rewrite bv_divu_unsigned. reflexivity.
- destruct (Z.eqb_spec (bv_unsigned b) 0). reflexivity. rewrite bv_modu_unsigned. reflexivity.
Qed.
Theorem zeval_sound : ltac2:(TCodec.tc2 tcn__BigLinkBase "K'D'F'=':'6%113&Q0&Jr3%211r2%5221(2r1%22<1%<3:41&QIyR0&Cr4%221<%5241%C3D1<p081pSLF1pS:H1pNJ1").
Proof. intros E e.
induction e; intros zz H; cbn [zeval edenot] in H; try discriminate.
- inversion H. cbn [edenot]. rewrite Z_to_bv_unsigned. reflexivity.
- inversion H. cbn [edenot]. reflexivity.
- destruct (zeval (uv E) e1) as [x|] eqn:E1; try discriminate. destruct (zeval (uv E) e2) as [y|] eqn:E2; try discriminate.
cbn [edenot]. rewrite <- (IHe1 x eq_refl), <- (IHe2 y eq_refl) in H. apply zalu_sound; auto.
- destruct (zeval (uv E) e1) as [x|] eqn:E1; try discriminate. destruct (zeval (uv E) e2) as [y|] eqn:E2; try discriminate.
cbn [edenot]. rewrite <- (IHe1 x eq_refl), <- (IHe2 y eq_refl) in H. apply zmd_sound; auto.
Qed.
Corollary zeval_word : ltac2:(TCodec.tc2 tcn__BigLinkBase "M'D'F'=':'6%113&Q0&Jr3%211r2%5221(2r1%22<1%<3:41'QHyR0%211&Cr4%221=&QG%126=%E3631p0:1pSLH1pS:J1pNL1").
Proof. intros E e z.
intros H. apply bv_eq. rewrite (zeval_sound E e z H). rewrite Z_to_bv_unsigned.
pose proof (bvu_range (edenot E e)) as R. rewrite (zeval_sound E e z H) in R. unfold inrange in R.
unfold bv_wrap. change (bv_modulus 64) with MM. rewrite Z.mod_small; auto.
Qed.
Inductive za : Type :=
| ZV (n : nat) | ZL (z : Z)
| ZAddM (a b : za) | ZSubM (a b : za) | ZMulM (a b : za) | ZMulHU (a b : za)
| ZDivC (a : za) (c : Z)
| ZShlC (a : za) (c : Z)
| ZSrl (a b : za) | ZSll (a b : za)
| ZLtu (a b : za) | ZAnd (a b : za) | ZOr (a b : za) | ZXor (a b : za)
| ZDivU (a b : za) | ZRemU (a b : za).
Fixpoint zden (V : nat -> Z) (t : za) : Z :=
match t with
| ZV n => V n
| ZL z => z
| ZAddM a b => (zden V a + zden V b) mod MM
| ZSubM a b => (zden V a - zden V b) mod MM
| ZMulM a b => (zden V a * zden V b) mod MM
| ZMulHU a b => (zden V a * zden V b) / MM
| ZDivC a c => zden V a / c
| ZShlC a c => (zden V a * c) mod MM
| ZSrl a b => zden V a / 2 ^ (zden V b mod 64)
| ZSll a b => (zden V a * 2 ^ (zden V b mod 64)) mod MM
| ZLtu a b => (if zden V a <? zden V b then 1 else 0)
| ZAnd a b => Z.land (zden V a) (zden V b)
| ZOr a b => Z.lor (zden V a) (zden V b)
| ZXor a b => Z.lxor (zden V a) (zden V b)
| ZDivU a b => (if zden V b =? 0 then MM - 1 else zden V a / zden V b)
| ZRemU a b => (if zden V b =? 0 then zden V a else zden V a mod zden V b)
end.
Fixpoint zcomp (e : expr) : option za :=
match e with
| ELit z => Some (ZL (z mod MM))
| EVar n => Some (ZV n)
| EAlu op a b =>
match zcomp a, zcomp b with
| Some x, Some y =>
match op with
| ALU_ADD => Some (ZAddM x y)
| ALU_SUB => Some (ZSubM x y)
| ALU_SLL => Some (match y with ZL k => ZShlC x (2 ^ (k mod 64)) | _ => ZSll x y end)
| ALU_SRL => Some (match y with ZL k => ZDivC x (2 ^ (k mod 64)) | _ => ZSrl x y end)
| ALU_SLTU => Some (ZLtu x y)
| ALU_AND => Some (ZAnd x y)
| ALU_OR => Some (ZOr x y)
| ALU_XOR => Some (ZXor x y)
| _ => None
end
| _, _ => None
end
| EMd op a b =>
match zcomp a, zcomp b with
| Some x, Some y =>
match op with
| M_MUL => Some (ZMulM x y)
| M_MULHU => Some (ZMulHU x y)
| M_DIVU => Some (ZDivU x y)
| M_REMU => Some (ZRemU x y)
| _ => None
end
| _, _ => None
end
| _ => None
end.
Definition zc (e : expr) : za := match zcomp e with Some t => t | None => ZL 0 end.
Lemma zcomp_zeval : ltac2:(TCodec.tc2 tcn__BigLinkBase "L'5'=p021'F'K':'6%113&Nr2%211(2r1%2291%93741%91>&Q0r4r3%3221&O%124<%;2E1%B3841p0:1pSFE1pS:G1pS2I1").
Proof. intros V e.
induction e; intros t H; cbn [zcomp] in H; try discriminate.
- inversion H. reflexivity.
- inversion H. reflexivity.
- destruct (zcomp e1) as [x|] eqn:E1; try discriminate. destruct (zcomp e2) as [y|] eqn:E2; try discriminate.
cbn [zeval]. rewrite (IHe1 x eq_refl), (IHe2 y eq_refl).
destruct op; inversion H; subst; cbn [zalu zden]; try reflexivity.
+ destruct y; reflexivity.
+ destruct y; reflexivity.
- destruct (zcomp e1) as [x|] eqn:E1; try discriminate. destruct (zcomp e2) as [y|] eqn:E2; try discriminate.
cbn [zeval]. rewrite (IHe1 x eq_refl), (IHe2 y eq_refl).
destruct op; inversion H; subst; cbn [zmd zden]; reflexivity.
Qed.
Theorem zcomp_sound : ltac2:(TCodec.tc2 tcn__BigLinkBase "N'D'F'K':'6%113&Nr2%211(2r1%2291%93741'=&QIyR0&Cr4r3%3221%6251&O&J%116%321A%F3<51p0>1pSFI1pS:K1pNM1").
Proof. intros E e t. intros H. apply zeval_sound. apply zcomp_zeval; auto. Qed.
Lemma zden_agree : ltac2:(TCodec.tc2 tcn__BigLinkBase "Q<'5'=pSJ21'F'K&<r1r6%3221':r2%411r5%113%53=31p071pS<@1'3&Er3%22=1(8%=3521'6%11D&Nr4%211(2%12I:%E3631&Or7%2217%32K8%J3Q221p061p0?1p0F1pSFQ31pS:Q51pS4Q71pS2Q81pS8Q;1").
Proof. intros b V V' e t.
intros HV Hv Ht. pose proof (zcomp_zeval V e t Ht) as A. pose proof (zcomp_zeval V' e t Ht) as B.
assert (zeval V e = zeval V' e).
{ clear A B t Ht. induction e; cbn [evars_lt zeval] in *; auto;
repeat match goal with | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H end;
try (rewrite IHe1, IHe2 by assumption; reflexivity).
apply Nat.ltb_lt in Hv. rewrite HV; auto. }
rewrite H in A. rewrite A in B. inversion B. reflexivity.
Qed.
Lemma zeval_agree : ltac2:(TCodec.tc2 tcn__BigLinkBase "Q2'5'=pSJ21'F&<r1r5%3221':r2%411r4%113%53<31p071pS<?1'3&E%12<9(8%<3421'6%11E&Q0r3%22C1%32?2%C3521p081p0>1pS:K1pS4M1pS2N1pS8Q11").
Proof. intros b V V' e.
intros HV. induction e; cbn [evars_lt zeval]; intros H; auto;
repeat match goal with | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H end;
try (rewrite IHe1, IHe2 by assumption; reflexivity).
apply Nat.ltb_lt in H. rewrite HV; auto.
Qed.
Definition zb (b : bool) : Z := if b then 1 else 0.
Lemma carry_ltu_l : ltac2:(TCodec.tc2 tcn__BigLinkBase "G'=&Ir2%211':&M&Q<&Q=&Q8r4r3%3221&H%6221%8215%:11&Q9%1265%>3B31p0@1p0A1pS8E1pS6F1").
Proof. intros a b.
unfold inrange, zb, MM. intros Ha Hb.
destruct (Z_lt_le_dec (a + b) (2^64)).
- rewrite Z.mod_small, Z.div_small by lia. destruct (Z.ltb_spec (a + b) a); lia.
- replace ((a + b) mod 2^64) with (a + b - 2^64). 2:{ apply Z.mod_unique with 1; lia. }
replace ((a + b) / 2^64) with 1. 2:{ apply Z.div_unique with (a + b - 2^64); lia. }
destruct (Z.ltb_spec (a + b - 2^64) a); lia.
Qed.
Lemma carry_ltu_r : ltac2:(TCodec.tc2 tcn__BigLinkBase "G'=&Ir2%211':&M&Q<&Q=&Q8r4r3%3221&H%6221%8214%:11&Q9%1265%>3B31p0@1p0A1pS8E1pS6F1").
Proof. intros a b. intros. rewrite Z.add_comm. apply carry_ltu_l; auto. Qed.
Lemma mod_inrange : ltac2:(TCodec.tc2 tcn__BigLinkBase "8'=&I&Q=r1&H%3221%511pS671").
Proof. intros a. unfold inrange. apply Z.mod_pos_bound. reflexivity. Qed.
Lemma esub_val : ltac2:(TCodec.tc2 tcn__BigLinkBase "O'='9&Q;zr2%3221&Q:r1%2241%8241&H%9271':&Q=&Q8&Q>&Q?+1%2281r4%5221%821;r3%9221%;21>%9236%>3J21p0@1p0C1pS8M1pS6N1").
Proof. intros a b.
intros Ha Hb. unfold MM in *.
replace ((2 ^ 64 - 1) * a) with ((2^64 - a) + (a - 1) * 2 ^ 64) by lia.
rewrite Z_mod_plus_full. rewrite (Z.mod_small (2^64 - a)) by lia.
replace (2 ^ 64 - a + b) with ((b - a) + 1 * 2 ^ 64) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma esub_val' : ltac2:(TCodec.tc2 tcn__BigLinkBase "O'='9&Q;zr2%3221&Q:r1%2241%8241&H%9271':&Q=&Q8r3&Q>&Q?+1%2291r4%5221%921<%9281%;21>%82:5%>3J21p0@1p0C1pS8M1pS6N1").
Proof. intros a b. intros. rewrite Z.add_comm. apply esub_val; auto. Qed.
Lemma W_add_eq : ltac2:(TCodec.tc2 tcn__BigLinkBase ">'=':&Q4r2r1%3221&Q=&Q8%1254&H%4221%:3;61pS8<1pS6=1"). Proof. intros a b. unfold W.add, W.wrap. rewrite MM_WM. reflexivity. Qed.
Lemma W_mul_eq : ltac2:(TCodec.tc2 tcn__BigLinkBase ">'=':&Q7r2r1%3221&Q=&Q>%1254&H%4221%:3;61pS8<1pS6=1"). Proof. intros a b. unfold W.mul, W.wrap. rewrite MM_WM. reflexivity. Qed.
Lemma W_b2z_ltu : ltac2:(TCodec.tc2 tcn__BigLinkBase "?'=':&Q5&Q6r2r1%3221%511&M&Q<%1265%311%;3<51pS8=1pS6>1"). Proof. intros a b. reflexivity. Qed.
Lemma wordZ_inrange : ltac2:(TCodec.tc2 tcn__BigLinkBase "9'=&;&Gr1%211&I%113%6231pS681"). Proof. intros a. unfold wordZ, inrange. rewrite MM_WM. tauto. Qed.
Lemma DDproduct_closed : ltac2:(TCodec.tc2 tcn__BigLinkBase "L'=&Ir2%211'9':&4&Q2r4r3%3221%53;;1&Q9&Q>%1265&H%4221%<3A61&7%13CC9&Q=%1276%A3F31%C261p0E1p0F1p4J1p2K1").
Proof. intros A B.
intros HA HB. apply wordZ_inrange in HA. apply wordZ_inrange in HB.
pose proof (DDproduct_correct A B HA HB) as H. destruct (DDproduct A B) as [hi lo]. cbn [fst snd] in *.
destruct H as (Wh & Wl & E). unfold wordZ, inrange in *. rewrite MM_val. rewrite M_val in *. split.
- apply Z.div_unique with lo; lia.
- apply Z.mod_unique with hi; lia.
Qed.
End BL.
Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.
