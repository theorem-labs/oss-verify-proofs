(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac RefMemcpyLib MemSplit As0StepLib Ja0MemIsZero.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ja0RegionPoisoned () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0RegionPoisoned."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0RegionPoisoned.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0RegionPoisoned.FPX_1.RIP."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefMemcpyLib."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1bool"; "1cons"; "1list"; "1nat"; "1nil"; "1option"; "1true"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "2or"; "3Z"; "0L"]; ["4store_ok"; "4word_to_le_bytes"; "5bvmap"; "0M"; "0M'"; "6wbytes"; "7msteps"; "8ret_ok"; ";M7"; ";c1_post"; ";c2_post"; ";c3_post"; ";c4_post"; ";frame_only"; ";reload_ok"; ":RIPL"]; [":in_app"; ":keeps_but"; ":rt_layout_globs"; "9HIGHEND"; "9SB"; "<getr"; "<mkst"; "<rdn"; "<regupd"; "<v_lb"; "=callee_saved"; "=keeps_cs"; ">mem_grows"; "?loaded_segments"; "@In"; "Aadd"]; ["Adiv"; "Aland"; "Ale"; "Alt"; "Amodulo"; "Aof_nat"; "Apow"; "Asub"; "0a"; "0fx"; "0j"; "0k"; "0kL"; "0mem0"; "0n"; "0p"]; ["0r1"; "0r2"; "0r3"; "0ra"; "0rd"; "0regs"; "0regs'"; "0regs0"; "0ret"; "0rg"; "0rom"; "0s"; "0sp"; "BBV"; "BZ_to_bv"; "Bbv"]; ["Bbv_signed"; "Bbv_unsigned"; "0v"; "0x"; "0z"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc. Local Ltac lia := L5FastLia.plia.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
Definition SB : Z := 0x7fff8000.
Definition LOWEND : Z := 0x7fff7fff.
Definition HIGHBEG : Z := 0x10007fff8000.
Definition HIGHEND : Z := 0x7fffffffffff.
Section FPX_1. Context {fx : PropExec.FPState}.
Definition rt_layout_globs (M : word -> option byte) : Prop :=
rdn ASEGS M (0x132638 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x13acf8)) /\
rdn ASEGS M (0x13acf8 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 SB)) /\
rdn ASEGS M (0x132640 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x13b9e8)) /\
rdn ASEGS M (0x13b9e8 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) /\
rdn ASEGS M (0x132648 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x13b9f0)) /\
rdn ASEGS M (0x13b9f0 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) /\
rdn ASEGS M (0x132650 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x13b9e0)) /\
rdn ASEGS M (0x13b9e0 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 HIGHEND)).
Definition in_app (p : Z) : Prop := (0 <= p <= LOWEND)%Z \/ (HIGHBEG <= p <= HIGHEND)%Z.
#[local] Ltac rwH :=
repeat match goal with
| H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
end.
#[local] Ltac unorm :=
repeat match goal with
| |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
lazymatch z with context [Z_to_bv 64 _] => fail | _ => rewrite (u_Z2bv z) by lia end
end.
#[local] Ltac cond :=
rwH; unfold at_, v_addi, v_add, c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; lia.
#[local] Ltac wval :=
gres; rwH; unfold at_, v_addi, v_add, v_sub, v_srli; imm_norm; unorm; rewrite ?Z.shiftr_div_pow2 by lia;
try change (2 ^ 3)%Z with 8%Z; first [reflexivity | f_equal; lia].
Section SE.
Local Abbreviation SEC_T_memtoshadow_run := (ltac2:(TCodec.tc2 tcn__Ja0RegionPoisoned "R@&By5'R?yR0%211%5241'6y8%611%311p061'>&Q2r4%211&Q0r2%211':&Q5r7(R=+:(8%33G21%6251&R>r3%22I1%;3I41r8+1%;3O19%>231r5%A3O21&Gr6%211';'9'F&Q=&Q6vQIr;+_YfL%J3Q<1H/01Q<r:r9%8576321r1%:591G43%=3<31%Q423O&Q?&Q@+8%22Q71&Q4%5221%Q42QK1%Q=3QK81&Q;%12D=%J231%K2=1qT>QO1%N2R01p0Q01p0Q41p0Q;1p0QH1p0QL1pT0R01pTBR81pTFR31pQ8R41pT<R:1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_memtoshadow_run) 0%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_memtoshadow_run) 1%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_memtoshadow_run) 2%nat 0%nat).
Variable ret : ltac:(sec_ty2 constr:(SEC_T_memtoshadow_run) 3%nat 0%nat).
Variable p : ltac:(sec_ty2 constr:(SEC_T_memtoshadow_run) 4%nat 0%nat).
Lemma memtoshadow_run : ltac:(sec_stmt2 constr:(SEC_T_memtoshadow_run) 5%nat 0%nat).
Proof using Type regs M rom ret p.
intros (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8) Hp H10 H1 Hret.
unfold in_app, LOWEND, HIGHBEG, HIGHEND in Hp. unfold SB in *.
pose proof (Z.div_mod p 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as Hmd.
destruct Hp as [Hlow|Hhigh].
- eexists. split.
+ stepn (ltac:(oF' 0x7a6dc%Z)) (ltac:(oD' 0x7a6dc%Z)).
mld (ltac:(oF' 0x7a6e0%Z)) (ltac:(oD' 0x7a6e0%Z)) (0x132638 : word) G1.
mld (ltac:(oF' 0x7a6e4%Z)) (ltac:(oD' 0x7a6e4%Z)) (0x13acf8 : word) G2.
stepn (ltac:(oF' 0x7a6e8%Z)) (ltac:(oD' 0x7a6e8%Z)).
stepn (ltac:(oF' 0x7a6ec%Z)) (ltac:(oD' 0x7a6ec%Z)).
stepn (ltac:(oF' 0x7a6f0%Z)) (ltac:(oD' 0x7a6f0%Z)).
stepn (ltac:(oF' 0x7a6f4%Z)) (ltac:(oD' 0x7a6f4%Z)).
stepb_tk (ltac:(oF' 0x7a6f8%Z)) (ltac:(oD' 0x7a6f8%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x7a73c%Z)) (ltac:(oD' 0x7a73c%Z)) (Z_to_bv 64 (p / 8)) ltac:(wval).
stepiv (ltac:(oF' 0x7a740%Z)) (ltac:(oD' 0x7a740%Z)) (Z_to_bv 64 (p / 8 + 0x7fff8000)) ltac:(wval).
stepret (ltac:(oF' 0x7a744%Z)) (ltac:(oD' 0x7a744%Z)) ret ltac:(rwH; reflexivity).
apply mst_refl.
+ split; [gres; reflexivity | solve_keeps_cs].
- eexists. split.
+ stepn (ltac:(oF' 0x7a6dc%Z)) (ltac:(oD' 0x7a6dc%Z)).
mld (ltac:(oF' 0x7a6e0%Z)) (ltac:(oD' 0x7a6e0%Z)) (0x132638 : word) G1.
mld (ltac:(oF' 0x7a6e4%Z)) (ltac:(oD' 0x7a6e4%Z)) (0x13acf8 : word) G2.
stepn (ltac:(oF' 0x7a6e8%Z)) (ltac:(oD' 0x7a6e8%Z)).
stepn (ltac:(oF' 0x7a6ec%Z)) (ltac:(oD' 0x7a6ec%Z)).
stepn (ltac:(oF' 0x7a6f0%Z)) (ltac:(oD' 0x7a6f0%Z)).
stepn (ltac:(oF' 0x7a6f4%Z)) (ltac:(oD' 0x7a6f4%Z)).
stepb_ft (ltac:(oF' 0x7a6f8%Z)) (ltac:(oD' 0x7a6f8%Z)) ltac:(cond).
stepn (ltac:(oF' 0x7a6fc%Z)) (ltac:(oD' 0x7a6fc%Z)).
mld (ltac:(oF' 0x7a700%Z)) (ltac:(oD' 0x7a700%Z)) (0x132640 : word) G3.
stepn (ltac:(oF' 0x7a704%Z)) (ltac:(oD' 0x7a704%Z)).
mld (ltac:(oF' 0x7a708%Z)) (ltac:(oD' 0x7a708%Z)) (0x132648 : word) G5.
mld (ltac:(oF' 0x7a70c%Z)) (ltac:(oD' 0x7a70c%Z)) (0x13b9e8 : word) G4.
mld (ltac:(oF' 0x7a710%Z)) (ltac:(oD' 0x7a710%Z)) (0x13b9f0 : word) G6.
stepn (ltac:(oF' 0x7a714%Z)) (ltac:(oD' 0x7a714%Z)).
stepb_tk (ltac:(oF' 0x7a718%Z)) (ltac:(oD' 0x7a718%Z)) ltac:(cond).
stepn (ltac:(oF' 0x7a720%Z)) (ltac:(oD' 0x7a720%Z)).
mld (ltac:(oF' 0x7a724%Z)) (ltac:(oD' 0x7a724%Z)) (0x132650 : word) G7.
mld (ltac:(oF' 0x7a728%Z)) (ltac:(oD' 0x7a728%Z)) (0x13b9e0 : word) G8.
stepn (ltac:(oF' 0x7a72c%Z)) (ltac:(oD' 0x7a72c%Z)).
stepn (ltac:(oF' 0x7a730%Z)) (ltac:(oD' 0x7a730%Z)).
stepb_ft (ltac:(oF' 0x7a734%Z)) (ltac:(oD' 0x7a734%Z)) ltac:(cond).
stepb_ft (ltac:(oF' 0x7a738%Z)) (ltac:(oD' 0x7a738%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x7a73c%Z)) (ltac:(oD' 0x7a73c%Z)) (Z_to_bv 64 (p / 8)) ltac:(wval).
stepiv (ltac:(oF' 0x7a740%Z)) (ltac:(oD' 0x7a740%Z)) (Z_to_bv 64 (p / 8 + 0x7fff8000)) ltac:(wval).
stepret (ltac:(oF' 0x7a744%Z)) (ltac:(oD' 0x7a744%Z)) ret ltac:(rwH; reflexivity).
apply mst_refl.
+ split; [gres; reflexivity | solve_keeps_cs].
Qed.
End SE.
Definition keeps_but (L : list reg) (regs regs' : bvmap 5 word) : Prop :=
forall r : reg, In r callee_saved -> ~ In r L -> getr regs' r = getr regs r.
#[using="Type"] Lemma keeps_but_refl : ltac2:(TCodec.tc2 tcn__Ja0RegionPoisoned "?'3'R?y5%211%411&ByR0%611%3261&Q1r2r1%33211pT<51pQ0:1"). Proof. intros L regs r _ _. reflexivity. Qed.
#[using="Type"] Lemma keeps_but_trans : ltac2:(TCodec.tc2 tcn__Ja0RegionPoisoned "H'3'R?y5%211%411&ByR0%611%3261&Q1r4r3r2%43321r5%63143r6%83136p031p061pT6<1pT4=1pT2>1pQ0C1").
Proof. intros L r1 r2 r3 A B r Hr HL. rewrite (B r Hr HL). apply A; assumption. Qed.
#[using="Type"] Lemma keeps_but_upd : ltac2:(TCodec.tc2 tcn__Ja0RegionPoisoned "Q2'3'R?y5%211%411&ByR0%611%3261&Q1r5r4r3%43321'=&Q>r6%23>51&<&Q:%53A81%311%8251r7&Q8%13?>=%A33:1p051p0?1pU6F1pT:K1pT>G1pT<H1pQ0M1").
Proof.
intros L regs regs' rd v K Hrd r Hr HL. rewrite getr_other; [apply K; assumption|].
intros ->. destruct Hrd as [Hrd|Hrd]; [exact (HL Hrd) | exact (Hrd Hr)].
Qed.
#[using="Type"] Lemma keeps_but_cs : ltac2:(TCodec.tc2 tcn__Ja0RegionPoisoned "E'3'R?y5%211%411&ByR0%611%3261&Q;r2r1%3221&Q1r4r3%33216p051pT>:1pT<;1pQ0@1").
Proof. intros L regs regs' K r Hr _. apply K, Hr. Qed.
Ltac solve_keeps_but :=
repeat (apply keeps_but_upd; [| first [left; cbv; tauto | right; not_kept] ]);
first [apply keeps_but_refl | assumption | apply keeps_but_cs; assumption].
#[using="Type"] Lemma v_lb_k : ltac2:(TCodec.tc2 tcn__Ja0RegionPoisoned "G'>'9&QBzr1%3221+7%5231%7231':'R?yR0%211&Q9&R>y8r2%3221%511%5283%;3821p0=1pSHF1").
Proof.
intros k Hk7. unfold v_lb. f_equal. rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap.
change (bv_half_modulus 8) with 128%Z. change (bv_modulus 8) with 256%Z. rewrite Z.mod_small; lia.
Qed.
#[using="Type"] Lemma signed64_small : ltac2:(TCodec.tc2 tcn__Ja0RegionPoisoned "G'>'9&QBzr1%3221&QC&QF+2+QO%3221%5271%;271':&R@yR0&R>r2%2231%5241%73D13p091pU:F1").
Proof.
intros z Hz. rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap.
change (bv_half_modulus 64) with (2 ^ 63)%Z. change (bv_modulus 64) with (2 ^ 64)%Z. rewrite Z.mod_small; lia.
Qed.
#[using="Type"] Lemma land7_mod8 : ltac2:(TCodec.tc2 tcn__Ja0RegionPoisoned ";'>':&QAr1+7%3221&QD+8%2251%83941pSB:1").
Proof. intros a. change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
#[local] Definition RIPL : list reg := [1; 2; 8; 9; 18; 19; 20; 21]%bv.
Section RIP.
Variable mem0 : word -> option byte.
Variable rom : word -> option byte.
Variables sp ra : word.
Variables p n s : Z.
Hypothesis Hs_def : bv_unsigned sp = s.
Hypothesis Hn : (0 < n <= 2 ^ 40)%Z.
Hypothesis Happ : (0 <= p /\ p + n + 8 <= LOWEND)%Z \/ (HIGHBEG <= p /\ p + n + 8 <= HIGHEND)%Z.
Hypothesis Hs : (0x1000000 <= s - 72)%Z /\ (s < 2 ^ 64)%Z.
Hypothesis Hshs : (SB + (p + n - 1) / 8 < s - 72)%Z.
Hypothesis Hok : store_ok ASEGS mem0 (Z_to_bv 64 (s - 72)) 72%nat = true.
Hypothesis Hret : ret_ok ra.
Hypothesis HG : rt_layout_globs mem0.
Variable kL : Z.
Hypothesis HZ : forall x : word, (SB + p / 8 <= bv_unsigned x < SB + (p + n - 1) / 8)%Z -> mem0 x = Some (Z_to_bv 8 0).
Hypothesis HL : mem0 (Z_to_bv 64 (SB + (p + n - 1) / 8)) = Some (Z_to_bv 8 kL).
Hypothesis HkL : kL = 0%Z \/ ((p + n - 1) mod 8 < kL <= 7)%Z.
#[local] Notation A k := (Z_to_bv 64 (s - k)) (only parsing).
#[local] Notation W M k v := (wbytes M (Z_to_bv 64 (s - k)) (word_to_le_bytes 8 v)) (only parsing).
#[using="Hs_def"] Lemma sp_s : ltac2:(TCodec.tc2 tcn__Ja0RegionPoisoned "9':'R?yR0%211vR<&R>vR;%2251%83541"). Proof. rewrite <- Hs_def. symmetry. apply Z_to_bv_bv_unsigned. Qed.
#[using="Hn Happ"] Lemma p_facts : ltac2:(TCodec.tc2 tcn__Ja0RegionPoisoned "H'9&QBzvQO%3221&Q?vQN%2241&Q3%8221&Q@+8%2291%<2;1&QG+1%2291%7216%A261%B22;%D221%E281%F2=1%G2C1").
Proof.
unfold LOWEND, HIGHBEG, HIGHEND in *. destruct Happ as [[H1 H2]|[H1 H2]];
(repeat split; [lia | lia | apply Z.div_pos; lia | apply Z.div_le_mono; lia | apply Z.div_le_upper_bound; lia]).
Qed.
Definition frame_only (M : word -> option byte) : Prop :=
forall x : word, (bv_unsigned x < s - 72 \/ s <= bv_unsigned x)%Z -> M x = mem0 x.
#[using="Type"] Lemma frame_only_refl : ltac2:(TCodec.tc2 tcn__Ja0RegionPoisoned "3&MvQM%211"). Proof. intros x _. reflexivity. Qed.
#[using="p n Hn Hs"] Lemma frame_only_w : ltac2:(TCodec.tc2 tcn__Ja0RegionPoisoned "Q5'R?yR0%211'6y8%511%311p051'>&Mr3%211'9&QB+8%2215+R8%4271%6231&Er5&R>&QGvR;r4%3221%52I1&Au8%221C%;3:41%F11p0>1p0F1pU6Q01pSHK1pQ8M1").
Proof.
intros M k v HF Hk x Hx. pose proof (u64_range x).
destruct Hx as [Hx|Hx].
- rewrite wbytes_below; [apply HF; lia | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | unorm; lia].
- rewrite wbytes_above; [apply HF; lia | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia].
Qed.
#[using="p n Hs HG"] Lemma frame_only_globs : ltac2:(TCodec.tc2 tcn__Ja0RegionPoisoned "@'R?yR0%211'6y8%511%311p051&Mr1%211&Q2r2%211p041pQ881").
Proof.
intros M HF. destruct HG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
assert (EQ : forall (a : word) k, (bv_unsigned a + Z.of_nat k <= 0x1000000)%Z -> rdn ASEGS M a k = rdn ASEGS mem0 a k).
{ intros a k Ha. apply rdn_ext; [lia|]. intros x Hx. apply HF. lia. }
unfold rt_layout_globs. rewrite !EQ by (cbn [Z.of_nat Pos.to_nat]; imm_norm; lia). repeat split; assumption.
Qed.
#[using="Hshs HZ"] Lemma frame_only_zero : ltac2:(TCodec.tc2 tcn__Ja0RegionPoisoned "Q?'R?yR0%211'6y8%511%311p051&Mr2%211'9&QB&Q?&Q4&Q@vQO+8%3221%6251&RA%12D<%:231&QC&QGvQN%=2:1+1%4221%>21<%A2@1%82:1%E2:1':r4r3%211(0&R>z%22Q41%42Q41%93Q461p0;1p0Q21pU8Q;1pQ8Q71").
Proof. intros M x HF Hx. rewrite HF by lia. apply HZ. exact Hx. Qed.
#[using="Hn Happ Hshs HL"] Lemma frame_only_last : ltac2:(TCodec.tc2 tcn__Ja0RegionPoisoned "Q3'R?yR0%211'6y8%511%311p051&Mr1%211':r2&R>&Q?&Q4&Q@&QGvQOvQN%6221+1%5221+8%8221%;2:1%=2I1%?11(0vQL%A2J1%32J1%E3J51p0G1pQ8K1").
Proof.
intros M HF. pose proof p_facts as (Pp & Ppn & Pp8 & Pmono & Phi). unfold SB, HIGHEND in *.
rewrite HF by (unorm; lia). exact HL.
Qed.
#[using="p n Hn Hs Hok"] Lemma frame_only_store_ok : ltac2:(TCodec.tc2 tcn__Ja0RegionPoisoned "Q:'R?yR0%211'6y8%511%311p051'>'4&Q<vQMr3%3221'9&QB&QEr2%211%4217+R8%6291%8231':'1&@&Q=r5&R>&QGvR;r4%3221%52Q01%94871F(7%=3<21p0?1p0I1pSFN1pSHQ01pQ8Q21").
Proof.
intros M k j HGr Hk. apply (store_ok_mono _ _ mem0 M _ HGr).
apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (s - 72)) _ 72%nat); [unorm; cbn [Z.of_nat Pos.to_nat]; lia | exact Hok | unorm; lia | unorm; cbn [Z.of_nat Pos.to_nat]; lia].
Qed.
#[local] Ltac grows := first [apply mem_grows_refl | eapply mem_grows_trans; [ | apply wbytes_grows ]; grows].
#[local] Ltac fsok := apply frame_only_store_ok; [grows | cbn [Z.of_nat Pos.to_nat]; lia].
#[local] Ltac fonly := repeat (apply frame_only_w; [|lia]); apply frame_only_refl.
Definition M7 (rg : bvmap 5 word) : word -> option byte :=
wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem0
(Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ra))
(Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr rg 8)))
(Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr rg 9)))
(Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr rg 18)))
(Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr rg 19)))
(Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr rg 20)))
(Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (getr rg 21)).
#[using="p n Hn Hs"] Lemma M7_frame_only : ltac2:(TCodec.tc2 tcn__Ja0RegionPoisoned "<&By5'R?yR0%211%5241&M&Hr1%211%411pTD61"). Proof. intros rg. unfold M7. fonly. Qed.
Definition c1_post (regs rg : bvmap 5 word) : Prop :=
getr rg 9 = Z_to_bv 64 n /\ getr rg 8 = Z_to_bv 64 p /\ getr rg 21 = Z_to_bv 64 0x13acf8 /\ getr rg 11 = Z_to_bv 64 SB
/\ getr rg 12 = Z_to_bv 64 LOWEND /\ getr rg 2 = Z_to_bv 64 (s - 64) /\ getr rg 1 = ra.
Section SE.
Local Abbreviation SEC_T_c1_run := (ltac2:(TCodec.tc2 tcn__Ja0RegionPoisoned "R7&By5'R?yR0%211%5241':&Q5r1(R=+:(8%33;21%6251&R>vQO%22=1%;3=41r2+;%;3C19%>231vQN%92D1%B3D31r3+2%B3J1@%E231vR<%H3J21r4+1%H3Q01F%K231vR3%N3Q021';'9'F&Q=&Q6vQIr6+_Zk8%Q43Q:1Q2/01Q:vQMvR:%8576321+_Zm@%Q:3Q@1Q8/01Q@&H%11;%>5=Q?317%A3@71&I%12?QB&Q1&O%231BQE%H241%I271qT>QK1%L2QL1p0N1p0Q51p0Q<1p0QD1pT<R11")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_c1_run) 0%nat 0%nat).
Lemma c1_run : ltac:(sec_stmt2 constr:(SEC_T_c1_run) 1%nat 0%nat).
Proof using Hs_def Hn Happ Hs Hok HG kL HkL regs.
intros H10 H11 H2 H1.
rewrite sp_s in H2. pose proof p_facts as (Pp & Ppn & Pp8 & Pmono & Phi). unfold HIGHEND in *.
pose proof (frame_only_globs (M7 regs) (M7_frame_only regs)) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
unfold M7 in *.
eexists. split.
- stepiv (ltac:(oF' 0x7ab68%Z)) (ltac:(oD' 0x7ab68%Z)) (Z_to_bv 64 (s - 64)) ltac:(wval).
stepsd (ltac:(oF' 0x7ab6c%Z)) (ltac:(oD' 0x7ab6c%Z)) (Z_to_bv 64 (s - 8)) ra ltac:(fsok).
stepsd (ltac:(oF' 0x7ab70%Z)) (ltac:(oD' 0x7ab70%Z)) (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(fsok).
stepsd (ltac:(oF' 0x7ab74%Z)) (ltac:(oD' 0x7ab74%Z)) (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(fsok).
stepsd (ltac:(oF' 0x7ab78%Z)) (ltac:(oD' 0x7ab78%Z)) (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(fsok).
stepsd (ltac:(oF' 0x7ab7c%Z)) (ltac:(oD' 0x7ab7c%Z)) (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(fsok).
stepsd (ltac:(oF' 0x7ab80%Z)) (ltac:(oD' 0x7ab80%Z)) (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(fsok).
stepsd (ltac:(oF' 0x7ab84%Z)) (ltac:(oD' 0x7ab84%Z)) (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(fsok).
stepb_ft (ltac:(oF' 0x7ab88%Z)) (ltac:(oD' 0x7ab88%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x7ab8c%Z)) (ltac:(oD' 0x7ab8c%Z)) (Z_to_bv 64 n) ltac:(wval).
stepiv (ltac:(oF' 0x7ab90%Z)) (ltac:(oD' 0x7ab90%Z)) (Z_to_bv 64 p) ltac:(wval).
stepn (ltac:(oF' 0x7ab94%Z)) (ltac:(oD' 0x7ab94%Z)).
mld (ltac:(oF' 0x7ab98%Z)) (ltac:(oD' 0x7ab98%Z)) (0x132638 : word) G1.
mld (ltac:(oF' 0x7ab9c%Z)) (ltac:(oD' 0x7ab9c%Z)) (0x13acf8 : word) G2.
stepn (ltac:(oF' 0x7aba0%Z)) (ltac:(oD' 0x7aba0%Z)).
stepn (ltac:(oF' 0x7aba4%Z)) (ltac:(oD' 0x7aba4%Z)).
stepn (ltac:(oF' 0x7aba8%Z)) (ltac:(oD' 0x7aba8%Z)).
stepn (ltac:(oF' 0x7abac%Z)) (ltac:(oD' 0x7abac%Z)).
apply mst_refl.
- unfold c1_post, SB, LOWEND. split; [repeat split; gres; rwH; try reflexivity | solve_keeps_but].
Qed.
End SE.
Definition c2_post (rg : bvmap 5 word) : Prop :=
getr rg 18 = Z_to_bv 64 (p + n) /\ getr rg 9 = Z_to_bv 64 n /\ getr rg 8 = Z_to_bv 64 p /\ getr rg 21 = Z_to_bv 64 0x13acf8
/\ getr rg 11 = Z_to_bv 64 SB /\ getr rg 2 = Z_to_bv 64 (s - 64) /\ getr rg 1 = ra.
Section SE.
Local Abbreviation SEC_T_c2_run := (ltac2:(TCodec.tc2 tcn__Ja0RegionPoisoned "Q<&By5'R?yR0%211%5241&Ir2r1%3221';'9'F&Q=&Q6vQIr3(R=+_Zm@(8%33A21/01A&Hr4%211vR:%<5;:521+_[QL%;3I19/01I%@5?F165%C3B51&J%11I&Q1&O%231DL%J241%K271qT>Q21%N2Q31p0Q01pT<Q51pT@Q61")) (only parsing).
Variable regs0 : ltac:(sec_ty2 constr:(SEC_T_c2_run) 0%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_c2_run) 1%nat 0%nat).
Lemma c2_run : ltac:(sec_stmt2 constr:(SEC_T_c2_run) 2%nat 0%nat).
Proof using sp Hn Happ Hs HG kL HkL regs0 regs.
intros (H9 & H8 & H21 & H11 & H12 & H2 & H1).
pose proof p_facts as (Pp & Ppn & Pp8 & Pmono & Phi).
pose proof (frame_only_globs (M7 regs0) (M7_frame_only regs0)) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
unfold SB, LOWEND, HIGHBEG, HIGHEND in *.
destruct Happ as [[Hl1 Hl2]|[Hh1 Hh2]].
- eexists. split.
+ stepb_tk (ltac:(oF' 0x7abb0%Z)) (ltac:(oD' 0x7abb0%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x7abf4%Z)) (ltac:(oD' 0x7abf4%Z)) (Z_to_bv 64 (p + n)) ltac:(wval).
stepb_tk (ltac:(oF' 0x7abf8%Z)) (ltac:(oD' 0x7abf8%Z)) ltac:(cond).
apply mst_refl.
+ unfold c2_post, SB. split; [repeat split; gres; rwH; reflexivity | solve_keeps_but].
- eexists. split.
+ stepb_ft (ltac:(oF' 0x7abb0%Z)) (ltac:(oD' 0x7abb0%Z)) ltac:(cond).
stepn (ltac:(oF' 0x7abb4%Z)) (ltac:(oD' 0x7abb4%Z)). mld (ltac:(oF' 0x7abb8%Z)) (ltac:(oD' 0x7abb8%Z)) (0x132640 : word) G3.
stepn (ltac:(oF' 0x7abbc%Z)) (ltac:(oD' 0x7abbc%Z)). mld (ltac:(oF' 0x7abc0%Z)) (ltac:(oD' 0x7abc0%Z)) (0x132648 : word) G5.
mld (ltac:(oF' 0x7abc4%Z)) (ltac:(oD' 0x7abc4%Z)) (0x13b9e8 : word) G4. mld (ltac:(oF' 0x7abc8%Z)) (ltac:(oD' 0x7abc8%Z)) (0x13b9f0 : word) G6.
stepn (ltac:(oF' 0x7abcc%Z)) (ltac:(oD' 0x7abcc%Z)).
stepb_tk (ltac:(oF' 0x7abd0%Z)) (ltac:(oD' 0x7abd0%Z)) ltac:(cond).
stepn (ltac:(oF' 0x7abd8%Z)) (ltac:(oD' 0x7abd8%Z)). mld (ltac:(oF' 0x7abdc%Z)) (ltac:(oD' 0x7abdc%Z)) (0x132650 : word) G7. mld (ltac:(oF' 0x7abe0%Z)) (ltac:(oD' 0x7abe0%Z)) (0x13b9e0 : word) G8.
stepn (ltac:(oF' 0x7abe4%Z)) (ltac:(oD' 0x7abe4%Z)). stepn (ltac:(oF' 0x7abe8%Z)) (ltac:(oD' 0x7abe8%Z)).
stepb_ft (ltac:(oF' 0x7abec%Z)) (ltac:(oD' 0x7abec%Z)) ltac:(cond).
stepb_ft (ltac:(oF' 0x7abf0%Z)) (ltac:(oD' 0x7abf0%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x7abf4%Z)) (ltac:(oD' 0x7abf4%Z)) (Z_to_bv 64 (p + n)) ltac:(wval).
stepb_ft (ltac:(oF' 0x7abf8%Z)) (ltac:(oD' 0x7abf8%Z)) ltac:(cond).
stepn (ltac:(oF' 0x7abfc%Z)) (ltac:(oD' 0x7abfc%Z)). mld (ltac:(oF' 0x7ac00%Z)) (ltac:(oD' 0x7ac00%Z)) (0x132640 : word) G3.
stepn (ltac:(oF' 0x7ac04%Z)) (ltac:(oD' 0x7ac04%Z)). mld (ltac:(oF' 0x7ac08%Z)) (ltac:(oD' 0x7ac08%Z)) (0x132648 : word) G5.
mld (ltac:(oF' 0x7ac0c%Z)) (ltac:(oD' 0x7ac0c%Z)) (0x13b9e8 : word) G4. mld (ltac:(oF' 0x7ac10%Z)) (ltac:(oD' 0x7ac10%Z)) (0x13b9f0 : word) G6.
stepn (ltac:(oF' 0x7ac14%Z)) (ltac:(oD' 0x7ac14%Z)).
stepb_tk (ltac:(oF' 0x7ac18%Z)) (ltac:(oD' 0x7ac18%Z)) ltac:(cond).
stepn (ltac:(oF' 0x7ac20%Z)) (ltac:(oD' 0x7ac20%Z)). mld (ltac:(oF' 0x7ac24%Z)) (ltac:(oD' 0x7ac24%Z)) (0x132650 : word) G7. mld (ltac:(oF' 0x7ac28%Z)) (ltac:(oD' 0x7ac28%Z)) (0x13b9e0 : word) G8.
stepn (ltac:(oF' 0x7ac2c%Z)) (ltac:(oD' 0x7ac2c%Z)). stepn (ltac:(oF' 0x7ac30%Z)) (ltac:(oD' 0x7ac30%Z)).
stepb_ft (ltac:(oF' 0x7ac34%Z)) (ltac:(oD' 0x7ac34%Z)) ltac:(cond).
stepb_ft (ltac:(oF' 0x7ac38%Z)) (ltac:(oD' 0x7ac38%Z)) ltac:(cond).
apply mst_refl.
+ unfold c2_post, SB. split; [repeat split; gres; rwH; reflexivity | solve_keeps_but].
Qed.
End SE.
#[local] Notation AB := (p + 7 - (p + 7) mod 8)%Z (only parsing).
#[local] Notation AE := (p + n - (p + n) mod 8)%Z (only parsing).
Definition c3_post (rg : bvmap 5 word) : Prop :=
getr rg 19 = Z_to_bv 64 ((p + 7 - (p + 7) mod 8) / 8 + SB) /\ getr rg 10 = Z_to_bv 64 ((p + n - (p + n) mod 8) / 8 + SB)
/\ getr rg 20 = Z_to_bv 64 (p + n - (p + n) mod 8)
/\ getr rg 18 = Z_to_bv 64 (p + n) /\ getr rg 9 = Z_to_bv 64 n /\ getr rg 8 = Z_to_bv 64 p /\ getr rg 21 = Z_to_bv 64 0x13acf8
/\ getr rg 2 = Z_to_bv 64 (s - 64).
#[using="Type"] Lemma ret_ok_lit1 : ltac2:(TCodec.tc2 tcn__Ja0RegionPoisoned ":&G(R=yR0+_[R@(8%43321'R?%115/031%911"). Proof. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma ret_ok_lit2 : ltac2:(TCodec.tc2 tcn__Ja0RegionPoisoned ":&G(R=yR0+_[RL(8%43321'R?%115/031%911"). Proof. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
Section SE.
Local Abbreviation SEC_T_c3_run := (ltac2:(TCodec.tc2 tcn__Ja0RegionPoisoned "Q;&By5'R?yR0%211%5241&Jr1%211';'9'F&Q=&Q6vQIr3(R=+_[QL(8%33@21/01@&Hr4%211vR:%<5;:521+_[RL%;3H19/01H%@5?F165%C3B51&K%11I&Q1&O%231DL%J241%K271qT>Q11%N2Q21p0Q01pT<Q41pT@Q51")) (only parsing).
Variable regs0 : ltac:(sec_ty2 constr:(SEC_T_c3_run) 0%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_c3_run) 1%nat 0%nat).
Lemma c3_run : ltac:(sec_stmt2 constr:(SEC_T_c3_run) 2%nat 0%nat).
Proof using sp Hn Happ Hs HG kL HkL regs0 regs.
intros (H18 & H9 & H8 & H21 & H11 & H2 & H1).
pose proof p_facts as (Pp & Ppn & Pp8 & Pmono & Phi).
pose proof (frame_only_globs (M7 regs0) (M7_frame_only regs0)) as HGM.
pose proof (Z.mod_pos_bound (p + 7) 8 ltac:(lia)) as Hm1. pose proof (Z.mod_pos_bound (p + n) 8 ltac:(lia)) as Hm2.
pose proof (Z.mod_le (p + n) 8 ltac:(lia) ltac:(lia)) as Hm3. pose proof (Z.mod_le (p + 7) 8 ltac:(lia) ltac:(lia)) as Hm4.
assert (Hab_app : in_app AB) by (unfold in_app, LOWEND, HIGHBEG, HIGHEND in *; destruct Happ as [[? ?]|[? ?]]; [left|right]; lia).
assert (Hae_app : in_app AE).
{ unfold in_app, LOWEND, HIGHBEG, HIGHEND in *. destruct Happ as [[? ?]|[? ?]]; [left; lia|right].
pose proof (Z.div_mod (p + n) 8 ltac:(lia)) as Hdm. set (q := ((p + n) / 8)%Z) in *. assert (2199291686912 <= q)%Z by lia. lia. }
unfold SB, LOWEND, HIGHBEG, HIGHEND in *.
assert (HAB8 : (0 <= AB / 8 <= 17592186044416)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (HAE8 : (0 <= AE / 8 <= 17592186044416)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x7a6dc : word) (M7 regs0) rom)
(fun rg => getr rg 10 = Z_to_bv 64 AB /\ getr rg 1 = (0x7ac50 : word) /\ getr rg 20 = Z_to_bv 64 AE
/\ getr rg 18 = Z_to_bv 64 (p + n) /\ getr rg 9 = Z_to_bv 64 n /\ getr rg 8 = Z_to_bv 64 p
/\ getr rg 21 = Z_to_bv 64 0x13acf8 /\ getr rg 2 = Z_to_bv 64 (s - 64) /\ keeps_but RIPL regs rg)).
{ eexists. split.
- stepb_ft (ltac:(oF' 0x7ac3c%Z)) (ltac:(oD' 0x7ac3c%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x7ac40%Z)) (ltac:(oD' 0x7ac40%Z)) (Z_to_bv 64 (p + 7)) ltac:(wval).
stepiv (ltac:(oF' 0x7ac44%Z)) (ltac:(oD' 0x7ac44%Z)) (Z_to_bv 64 AB)
ltac:(gres; unfold v_andi; imm_norm; replace (bv_wrap 64 (-8)) with (2 ^ 64 - 8)%Z by reflexivity; unorm; rewrite land_down8 by lia; reflexivity).
stepiv (ltac:(oF' 0x7ac48%Z)) (ltac:(oD' 0x7ac48%Z)) (Z_to_bv 64 AE)
ltac:(gres; rwH; unfold v_andi; imm_norm; replace (bv_wrap 64 (-8)) with (2 ^ 64 - 8)%Z by reflexivity; unorm; rewrite land_down8 by lia; reflexivity).
stepn (ltac:(oF' 0x7ac4c%Z)) (ltac:(oD' 0x7ac4c%Z)).
apply mst_refl.
- repeat split; gres; rwH; try reflexivity; try (apply bv_eq; reflexivity). solve_keeps_but. }
cbv beta. intros r1 (R10 & R1 & R20 & R18 & R9 & R8 & R21 & R2 & K1).
destruct (memtoshadow_run r1 (M7 regs0) rom (0x7ac50 : word) AB HGM Hab_app R10 R1 ret_ok_lit1) as (r2 & RUN2 & Q10 & K2). unfold SB in Q10.
eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x7a6dc : word) (M7 regs0) rom)
(fun rg => getr rg 10 = Z_to_bv 64 AE /\ getr rg 1 = (0x7ac5c : word) /\ getr rg 19 = Z_to_bv 64 (AB / 8 + 2147450880)
/\ getr rg 20 = Z_to_bv 64 AE /\ getr rg 18 = Z_to_bv 64 (p + n) /\ getr rg 9 = Z_to_bv 64 n /\ getr rg 8 = Z_to_bv 64 p
/\ getr rg 21 = Z_to_bv 64 0x13acf8 /\ getr rg 2 = Z_to_bv 64 (s - 64) /\ keeps_but RIPL regs rg)).
{ assert (S20 : getr r2 20 = Z_to_bv 64 AE) by (rewrite (K2 20%bv) by (cbv; tauto); exact R20).
eexists. split.
- eapply msteps_trans; [exact RUN2|].
stepiv (ltac:(oF' 0x7ac50%Z)) (ltac:(oD' 0x7ac50%Z)) (Z_to_bv 64 (AB / 8 + 2147450880)) ltac:(gres; rewrite Q10; unfold v_addi; imm_norm; unorm; f_equal; lia).
stepiv (ltac:(oF' 0x7ac54%Z)) (ltac:(oD' 0x7ac54%Z)) (Z_to_bv 64 AE) ltac:(gres; rewrite S20; unfold v_addi; imm_norm; unorm; f_equal; lia).
stepn (ltac:(oF' 0x7ac58%Z)) (ltac:(oD' 0x7ac58%Z)).
apply mst_refl.
- repeat split; gres; try reflexivity; try (apply bv_eq; reflexivity);
try (rewrite (K2 _) by (cbv; tauto); assumption).
eapply keeps_but_trans; [exact K1|]. solve_keeps_but. }
cbv beta. intros r3 (T10 & T1 & T19 & T20 & T18 & T9 & T8 & T21 & T2 & K3).
destruct (memtoshadow_run r3 (M7 regs0) rom (0x7ac5c : word) AE HGM Hae_app T10 T1 ret_ok_lit2) as (r4 & RUN4 & U10 & K4). unfold SB in U10.
exists r4. split; [exact RUN4|]. split.
- unfold c3_post, SB. repeat split; try (rewrite (K4 _) by (cbv; tauto); assumption). exact U10.
- eapply keeps_but_trans; [exact K3|]. apply keeps_but_cs. exact K4.
Qed.
End SE.
#[using="Hn Happ Hs Hshs HZ"] Lemma rdn1_M7 : ltac2:(TCodec.tc2 tcn__Ja0RegionPoisoned "QI&By5'R?yR0%211%5241'>'9&QB&Q?&Q4&Q@vQO+8%3221%6251r1%9221&QC&QGvQN%<291+1%4221%=21;%@2?1%82:1%D2:1':'6'3y8%N11%311%511&Q7&Q=&Hr3%211&R>r2%22Q71u1%948521(0(2z%82A1(5%11B%53C31%72C1%I3C91p0K1pU:QA1pT@QC1").
Proof.
intros regs0 z Hz. pose proof p_facts as (Pp & Ppn & Pp8 & Pmono & Phi). unfold SB, HIGHEND in *.
cbn [rdn]. rewrite (frame_only_zero (M7 regs0) (Z_to_bv 64 z) (M7_frame_only regs0)) by (unfold SB; unorm; lia). reflexivity.
Qed.
#[using="Hn Happ Hs Hshs HL"] Lemma rdn1_M7_last : ltac2:(TCodec.tc2 tcn__Ja0RegionPoisoned "QB&By5'R?yR0%211%5241'>':r1&Q?&Q4&Q@&QGvQOvQN%6221+1%5221+8%8221%;2:1%>3?=1'6'3y8%G11%311%511&Q7&Q=&Hr3%211&R>r2%22Q01u1%948521(0(2vQL%82A1(5%11B%53C31%72C1%Q73C91p0J1pU:Q:1pT@Q<1").
Proof.
intros regs0 z ->. cbn [rdn]. rewrite (frame_only_last (M7 regs0) (M7_frame_only regs0)). reflexivity.
Qed.
#[local] Ltac maddr z := match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 z) by (symmetry; wval) end.
#[local] Ltac mlb0 F D z :=
chain_step; [reflexivity
| eapply step_lb; [exact F | reflexivity | exact D | maddr z; apply rdn1_M7; unfold SB; lia]
| step_simpl; vnorm].
#[local] Ltac mlbk F D z :=
chain_step; [reflexivity
| eapply step_lb; [exact F | reflexivity | exact D | maddr z; apply rdn1_M7_last; unfold SB; lia]
| step_simpl; vnorm; rewrite (v_lb_k kL ltac:(lia))].
Definition c4_post (rg : bvmap 5 word) : Prop :=
getr rg 19 = Z_to_bv 64 ((p + 7 - (p + 7) mod 8) / 8 + SB) /\ getr rg 10 = Z_to_bv 64 ((p + n - (p + n) mod 8) / 8 + SB)
/\ getr rg 2 = Z_to_bv 64 (s - 64).
#[local] Ltac conds :=
rwH; unfold c_lts, bv_lts, v_andi; imm_norm; unorm; rewrite ?land7_mod8; unorm; rewrite !signed64_small by lia;
first [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Section SE.
Local Abbreviation SEC_T_c4_run := (ltac2:(TCodec.tc2 tcn__Ja0RegionPoisoned "Q;&By5'R?yR0%211%5241&Kr1%211';'9'F&Q=&Q6vQIr3(R=+_[RL(8%33@21/01@&Hr4%211vR:%<5;:521+_[V<%;3H19/01H%@5?F165%C3B51&L%11I&Q1&O%231DL%J241%K271qT>Q11%N2Q21p0Q01pT<Q41pT@Q51")) (only parsing).
Variable regs0 : ltac:(sec_ty2 constr:(SEC_T_c4_run) 0%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_c4_run) 1%nat 0%nat).
Lemma c4_run : ltac:(sec_stmt2 constr:(SEC_T_c4_run) 2%nat 0%nat).
Proof using sp Hn Happ Hs Hshs HG kL HZ HL HkL regs0 regs.
intros (H19 & H10 & H20 & H18 & H9 & H8 & H21 & H2).
pose proof p_facts as (Pp & Ppn & Pp8 & Pmono & Phi).
pose proof (frame_only_globs (M7 regs0) (M7_frame_only regs0)) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
pose proof (Z.div_mod p 8 ltac:(lia)) as Dp. pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as Mp.
pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)) as Dq. pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)) as Mq.
unfold SB, LOWEND, HIGHBEG, HIGHEND in *.
destruct (Z.lt_ge_cases (p / 8) ((p + n - 1) / 8)) as [Hlt|Hge].
-
destruct HkL as [Hk0|Hk7].
+ eexists. split.
* mld (ltac:(oF' 0x7ac5c%Z)) (ltac:(oD' 0x7ac5c%Z)) (0x13acf8 : word) G2.
stepiv (ltac:(oF' 0x7ac60%Z)) (ltac:(oD' 0x7ac60%Z)) (Z_to_bv 64 (p / 8)) ltac:(wval).
stepiv (ltac:(oF' 0x7ac64%Z)) (ltac:(oD' 0x7ac64%Z)) (Z_to_bv 64 (2147450880 + p / 8)) ltac:(wval).
mlb0 (ltac:(oF' 0x7ac68%Z)) (ltac:(oD' 0x7ac68%Z)) (2147450880 + p / 8)%Z.
stepb_tk (ltac:(oF' 0x7ac6c%Z)) (ltac:(oD' 0x7ac6c%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x7ac78%Z)) (ltac:(oD' 0x7ac78%Z)) (Z_to_bv 64 (p + n - 1)) ltac:(wval).
stepiv (ltac:(oF' 0x7ac7c%Z)) (ltac:(oD' 0x7ac7c%Z)) (Z_to_bv 64 ((p + n - 1) / 8)) ltac:(wval).
stepiv (ltac:(oF' 0x7ac80%Z)) (ltac:(oD' 0x7ac80%Z)) (Z_to_bv 64 (2147450880 + (p + n - 1) / 8)) ltac:(wval).
mlbk (ltac:(oF' 0x7ac84%Z)) (ltac:(oD' 0x7ac84%Z)) (2147450880 + (p + n - 1) / 8)%Z.
stepb_tk (ltac:(oF' 0x7ac88%Z)) (ltac:(oD' 0x7ac88%Z)) ltac:(cond).
apply mst_refl.
* unfold c4_post, SB. split; [repeat split; gres; rwH; reflexivity | solve_keeps_but].
+ eexists. split.
* mld (ltac:(oF' 0x7ac5c%Z)) (ltac:(oD' 0x7ac5c%Z)) (0x13acf8 : word) G2.
stepiv (ltac:(oF' 0x7ac60%Z)) (ltac:(oD' 0x7ac60%Z)) (Z_to_bv 64 (p / 8)) ltac:(wval).
stepiv (ltac:(oF' 0x7ac64%Z)) (ltac:(oD' 0x7ac64%Z)) (Z_to_bv 64 (2147450880 + p / 8)) ltac:(wval).
mlb0 (ltac:(oF' 0x7ac68%Z)) (ltac:(oD' 0x7ac68%Z)) (2147450880 + p / 8)%Z.
stepb_tk (ltac:(oF' 0x7ac6c%Z)) (ltac:(oD' 0x7ac6c%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x7ac78%Z)) (ltac:(oD' 0x7ac78%Z)) (Z_to_bv 64 (p + n - 1)) ltac:(wval).
stepiv (ltac:(oF' 0x7ac7c%Z)) (ltac:(oD' 0x7ac7c%Z)) (Z_to_bv 64 ((p + n - 1) / 8)) ltac:(wval).
stepiv (ltac:(oF' 0x7ac80%Z)) (ltac:(oD' 0x7ac80%Z)) (Z_to_bv 64 (2147450880 + (p + n - 1) / 8)) ltac:(wval).
mlbk (ltac:(oF' 0x7ac84%Z)) (ltac:(oD' 0x7ac84%Z)) (2147450880 + (p + n - 1) / 8)%Z.
stepb_ft (ltac:(oF' 0x7ac88%Z)) (ltac:(oD' 0x7ac88%Z)) ltac:(cond).
stepn (ltac:(oF' 0x7ac8c%Z)) (ltac:(oD' 0x7ac8c%Z)).
stepb_tk (ltac:(oF' 0x7ac90%Z)) (ltac:(oD' 0x7ac90%Z)) ltac:(conds).
apply mst_refl.
* unfold c4_post, SB. split; [repeat split; gres; rwH; reflexivity | solve_keeps_but].
-
assert (Heq : (p / 8 = (p + n - 1) / 8)%Z) by lia.
destruct HkL as [Hk0|Hk7].
+ eexists. split.
* mld (ltac:(oF' 0x7ac5c%Z)) (ltac:(oD' 0x7ac5c%Z)) (0x13acf8 : word) G2.
stepiv (ltac:(oF' 0x7ac60%Z)) (ltac:(oD' 0x7ac60%Z)) (Z_to_bv 64 (p / 8)) ltac:(wval).
stepiv (ltac:(oF' 0x7ac64%Z)) (ltac:(oD' 0x7ac64%Z)) (Z_to_bv 64 (2147450880 + (p + n - 1) / 8)) ltac:(wval).
mlbk (ltac:(oF' 0x7ac68%Z)) (ltac:(oD' 0x7ac68%Z)) (2147450880 + (p + n - 1) / 8)%Z.
stepb_tk (ltac:(oF' 0x7ac6c%Z)) (ltac:(oD' 0x7ac6c%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x7ac78%Z)) (ltac:(oD' 0x7ac78%Z)) (Z_to_bv 64 (p + n - 1)) ltac:(wval).
stepiv (ltac:(oF' 0x7ac7c%Z)) (ltac:(oD' 0x7ac7c%Z)) (Z_to_bv 64 ((p + n - 1) / 8)) ltac:(wval).
stepiv (ltac:(oF' 0x7ac80%Z)) (ltac:(oD' 0x7ac80%Z)) (Z_to_bv 64 (2147450880 + (p + n - 1) / 8)) ltac:(wval).
mlbk (ltac:(oF' 0x7ac84%Z)) (ltac:(oD' 0x7ac84%Z)) (2147450880 + (p + n - 1) / 8)%Z.
stepb_tk (ltac:(oF' 0x7ac88%Z)) (ltac:(oD' 0x7ac88%Z)) ltac:(cond).
apply mst_refl.
* unfold c4_post, SB. split; [repeat split; gres; rwH; try reflexivity; f_equal; lia | solve_keeps_but].
+ eexists. split.
* mld (ltac:(oF' 0x7ac5c%Z)) (ltac:(oD' 0x7ac5c%Z)) (0x13acf8 : word) G2.
stepiv (ltac:(oF' 0x7ac60%Z)) (ltac:(oD' 0x7ac60%Z)) (Z_to_bv 64 (p / 8)) ltac:(wval).
stepiv (ltac:(oF' 0x7ac64%Z)) (ltac:(oD' 0x7ac64%Z)) (Z_to_bv 64 (2147450880 + (p + n - 1) / 8)) ltac:(wval).
mlbk (ltac:(oF' 0x7ac68%Z)) (ltac:(oD' 0x7ac68%Z)) (2147450880 + (p + n - 1) / 8)%Z.
stepb_ft (ltac:(oF' 0x7ac6c%Z)) (ltac:(oD' 0x7ac6c%Z)) ltac:(cond).
stepn (ltac:(oF' 0x7ac70%Z)) (ltac:(oD' 0x7ac70%Z)).
stepb_ft (ltac:(oF' 0x7ac74%Z)) (ltac:(oD' 0x7ac74%Z)) ltac:(conds).
stepiv (ltac:(oF' 0x7ac78%Z)) (ltac:(oD' 0x7ac78%Z)) (Z_to_bv 64 (p + n - 1)) ltac:(wval).
stepiv (ltac:(oF' 0x7ac7c%Z)) (ltac:(oD' 0x7ac7c%Z)) (Z_to_bv 64 ((p + n - 1) / 8)) ltac:(wval).
stepiv (ltac:(oF' 0x7ac80%Z)) (ltac:(oD' 0x7ac80%Z)) (Z_to_bv 64 (2147450880 + (p + n - 1) / 8)) ltac:(wval).
mlbk (ltac:(oF' 0x7ac84%Z)) (ltac:(oD' 0x7ac84%Z)) (2147450880 + (p + n - 1) / 8)%Z.
stepb_ft (ltac:(oF' 0x7ac88%Z)) (ltac:(oD' 0x7ac88%Z)) ltac:(cond).
stepn (ltac:(oF' 0x7ac8c%Z)) (ltac:(oD' 0x7ac8c%Z)).
stepb_tk (ltac:(oF' 0x7ac90%Z)) (ltac:(oD' 0x7ac90%Z)) ltac:(conds).
apply mst_refl.
* unfold c4_post, SB. split; [repeat split; gres; rwH; try reflexivity; f_equal; lia | solve_keeps_but].
Qed.
End SE.
Definition reload_ok (regs0 : bvmap 5 word) (M : word -> option byte) : Prop :=
frame_only M /\
rdn ASEGS M (Z_to_bv 64 (s - 8)) 8%nat = Some (word_to_le_bytes 8 ra) /\
rdn ASEGS M (Z_to_bv 64 (s - 16)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 8)) /\
rdn ASEGS M (Z_to_bv 64 (s - 24)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 9)) /\
rdn ASEGS M (Z_to_bv 64 (s - 32)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 18)) /\
rdn ASEGS M (Z_to_bv 64 (s - 40)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 19)) /\
rdn ASEGS M (Z_to_bv 64 (s - 48)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 20)) /\
rdn ASEGS M (Z_to_bv 64 (s - 56)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 21)).
#[local] Ltac peel :=
rewrite rdn_wbytes_out;
[ | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | cbn [Z.of_nat Pos.to_nat]; unorm; lia
| rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia ].
#[local] Ltac slot := repeat peel; apply rdn_wbytes_hit8; unorm; lia.
Section SE.
Local Abbreviation SEC_T_M7_reload := (ltac2:(TCodec.tc2 tcn__Ja0RegionPoisoned "<&By5'R?yR0%211%5241&Nr1&H%112%4231pT@61")) (only parsing).
Variable regs0 : ltac:(sec_ty2 constr:(SEC_T_M7_reload) 0%nat 0%nat).
Lemma M7_reload : ltac:(sec_stmt2 constr:(SEC_T_M7_reload) 1%nat 0%nat).
Proof using p n Hn Hs regs0.
split; [apply M7_frame_only|]. unfold M7. repeat split; slot.
Qed.
End SE.
#[using="p n Hn Hs"] Lemma W72_reload : ltac2:(TCodec.tc2 tcn__Ja0RegionPoisoned "Q0&By5'R?yR0%211%5241'6y8%611%311p061&Nr3r2%3221r4&E&R>&QGvR;+R8%3221%52C1&Au8%221<%:3>41%@2<1p0>1pU6I1pQ8D1pT@J1").
Proof.
intros regs0 M v (HF & R1 & R2 & R3 & R4 & R5 & R6 & R7). split; [apply frame_only_w; [exact HF | lia]|].
repeat split; (peel; assumption).
Qed.
Section SE.
Local Abbreviation SEC_T_c5_run := (ltac2:(TCodec.tc2 tcn__Ja0RegionPoisoned "R4&By5'R?yR0%211%5241&Lr1%211';'6y8%:11%311p0:1'9'F&Q=&Q6vQIr4(R=+_[V<(8%33E21/01E&Hr5%211vR:%<5;:521r2+_[W0%<3N1:/01N%A5@41L6%D3C61&N%12;O':&Q5+2%E3Q91C%32<1&R>&QGvR;+R0%3221%52Q>1%;3Q>71&Q1&O%231Q1F&Q<vQM%221QA%Q:241%Q;281%Q<2E1%Q=2H1qQ:Q?1%QE2Q@1qT>QJ1%QG2QK1p0QI1pT<QM1pT@QN1")) (only parsing).
Variable regs0 : ltac:(sec_ty2 constr:(SEC_T_c5_run) 0%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_c5_run) 1%nat 0%nat).
Lemma c5_run : ltac:(sec_stmt2 constr:(SEC_T_c5_run) 2%nat 0%nat).
Proof using sp Hn Happ Hs Hshs Hok kL HZ HL HkL regs0 regs.
intros (H19 & H10 & H2).
pose proof p_facts as (Pp & Ppn & Pp8 & Pmono & Phi).
pose proof (Z.mod_pos_bound (p + 7) 8 ltac:(lia)) as Hm1. pose proof (Z.mod_pos_bound (p + n) 8 ltac:(lia)) as Hm2.
pose proof (Z.mod_le (p + n) 8 ltac:(lia) ltac:(lia)) as Hm3. pose proof (Z.mod_le (p + 7) 8 ltac:(lia) ltac:(lia)) as Hm4.
unfold SB, LOWEND, HIGHBEG, HIGHEND in *.
assert (HAB8 : (p / 8 <= AB / 8 <= 17592186044416)%Z) by (split; [apply Z.div_le_mono; lia | apply Z.div_le_upper_bound; lia]).
assert (HAE8 : (0 <= AE / 8 <= (p + n) / 8)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_le_mono; lia]).
assert (Hpn8 : ((p + n) / 8 <= (p + n - 1) / 8 + 1)%Z).
{ pose proof (Z.div_mod (p + n) 8 ltac:(lia)). pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)). lia. }
assert (HAE8' : (AE / 8 - 1 <= (p + n - 1) / 8)%Z).
{ pose proof (Z.div_mod AE 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound AE 8 ltac:(lia)).
pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)). lia. }
pose proof (Z.div_mod p 8 ltac:(lia)) as Dp. pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as Mp.
pose proof (Z.div_mod (p + n) 8 ltac:(lia)) as Dpn.
set (sb := (2147450880 + AB / 8)%Z) in *. set (se := (2147450880 + AE / 8)%Z) in *.
assert (E19 : getr regs 19 = Z_to_bv 64 sb) by (rewrite H19; f_equal; lia).
assert (E10 : getr regs 10 = Z_to_bv 64 se) by (rewrite H10; f_equal; lia).
destruct (Z.le_gt_cases se sb) as [Hskip|Hgo].
- exists regs, (M7 regs0). split; [|split; [apply M7_reload | split; [exact H2 | split; [apply keeps_but_refl | unfold M7; grows]]]].
stepb_tk (ltac:(oF' 0x7accc%Z)) (ltac:(oD' 0x7accc%Z)) ltac:(rewrite E19, E10; unfold c_ltu, bv_ltu; unorm; apply Z.ltb_ge; lia).
apply mst_refl.
-
assert (S1 : exists r1, msteps ASEGS (mkst regs (0x7accc : word) (M7 regs0) rom) (mkst r1 (0x8b054 : word) (M7 regs0) rom)
/\ (getr r1 10 = Z_to_bv 64 sb /\ getr r1 11 = Z_to_bv 64 (se - sb) /\ getr r1 2 = Z_to_bv 64 (s - 64) /\ getr r1 1 = (0x7acdc : word)
/\ keeps_but RIPL regs r1)).
{ eexists. split.
- stepb_ft (ltac:(oF' 0x7accc%Z)) (ltac:(oD' 0x7accc%Z)) ltac:(rewrite E19, E10; unfold c_ltu, bv_ltu; unorm; apply Z.ltb_lt; lia).
stepiv (ltac:(oF' 0x7acd0%Z)) (ltac:(oD' 0x7acd0%Z)) (Z_to_bv 64 (se - sb)) ltac:(gres; rewrite E19, E10; unfold v_sub; unorm; f_equal; lia).
stepiv (ltac:(oF' 0x7acd4%Z)) (ltac:(oD' 0x7acd4%Z)) (Z_to_bv 64 sb) ltac:(gres; rewrite E19; unfold v_addi; imm_norm; unorm; f_equal; lia).
stepn (ltac:(oF' 0x7acd8%Z)) (ltac:(oD' 0x7acd8%Z)).
apply mst_refl.
- repeat split; gres; rwH; try reflexivity; try (apply bv_eq; reflexivity). solve_keeps_but. }
destruct S1 as (r1 & RUN1 & Q10 & Q11 & Q2 & Q1 & K1).
assert (Hret2 : ret_ok (0x7acdc : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
pose proof (mem_is_zero_run (M7 regs0) (Z_to_bv 64 sb) (Z_to_bv 64 (s - 64)) (0x7acdc : word) (se - sb) sb (s - 64) se
(sb + 7 - (sb + 7) mod 8) (se - se mod 8) rom) as MZ.
specialize (MZ ltac:(unorm; reflexivity) ltac:(unorm; reflexivity) ltac:(lia) eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
specialize (MZ ltac:(replace (s - 64 - 8)%Z with (s - 72)%Z by lia; apply frame_only_store_ok; [unfold M7; grows | cbn; lia]) Hret2).
assert (HZI : forall x : word, (sb <= bv_unsigned x < sb + (se - sb))%Z -> M7 regs0 x = Some (Z_to_bv 8 0)).
{ intros x Hx. destruct (Z.lt_ge_cases (bv_unsigned x) (2147450880 + (p + n - 1) / 8)) as [Hxl|Hxh].
- apply (frame_only_zero (M7 regs0) x (M7_frame_only regs0)). unfold SB. lia.
-
assert (Ex : x = Z_to_bv 64 (SB + (p + n - 1) / 8)) by (apply bv_eq; unfold SB; unorm; lia).
pose proof (Z.div_mod AE 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound AE 8 ltac:(lia)).
pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)).
assert (kL = 0)%Z as Hk0 by lia.
rewrite Ex, (frame_only_last (M7 regs0) (M7_frame_only regs0)), Hk0. reflexivity. }
specialize (MZ HZI).
destruct (MZ r1 Q10 Q11 Q2 Q1) as (r2 & RUN2 & V10 & V2 & V1 & K2).
replace (s - 64 - 8)%Z with (s - 72)%Z in RUN2 by lia.
eexists. exists (wbytes (M7 regs0) (Z_to_bv 64 (s - 72)) (word_to_le_bytes 8 (0x7acdc : word))). split; [|split; [apply W72_reload, M7_reload|]].
+ eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
stepb_ft (ltac:(oF' 0x7acdc%Z)) (ltac:(oD' 0x7acdc%Z)) ltac:(rewrite V10; unfold c_eq, bv_eqb; unorm; apply Z.eqb_neq; lia).
apply mst_refl.
+ split; [gres; exact V2|]. split; [|unfold M7; grows].
eapply keeps_but_trans; [exact K1|]. apply keeps_but_cs. exact K2.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_c6_run := (ltac2:(TCodec.tc2 tcn__Ja0RegionPoisoned "S=&By5'R?yR0%211%5241'6y8%611%311p061&Nr3r1%3221':&Q5(R=+2(8%33C21%5291&R>&QGvR;+R0%3221%52H1%=3H71';'9'F&Q=&Q6vQIr5+_[W0%D3Q21B/01Q2r4vR:%8576321vR3%:59N143%=3<31+:%M3Q=1K%O2Q21z%K2Q>1%Q33Q>31%Q32Q6OvR<%Q63QA21+1%Q63QF1Q4%Q82Q;1%Q:3QE1?+8%Q:3QJ1Q8%Q<2Q?1r6%Q>213%Q@3QK31+9%Q@3R01Q>%QB2QE1%QC262%QE3R021+B%QE3R51QC%QG2QJ1%QH2;2%QJ3R521+C%QJ3R:1QH%QL2QO1%QM2@2%QO3R:21+D%QO3R?1QM%R12R41%R22E2%R43R?21+E%R43RD1R2%R62R91%R72J2%R93RD21&Q1&O%231QHR>%QN241%QO2:1%R02@1%R12F1%R22L1%R32Q21%R42Q91%R52Q>1%R62QB1%R72QI1qT>S11%R:2S21p0R<1p0RK1pQ8S01pT<S61pT@S71")) (only parsing).
Variable regs0 : ltac:(sec_ty2 constr:(SEC_T_c6_run) 0%nat 0%nat).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_c6_run) 1%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_c6_run) 2%nat 0%nat).
Lemma c6_run : ltac:(sec_stmt2 constr:(SEC_T_c6_run) 3%nat 0%nat).
Proof using p n Hs_def Hn Happ Hs Hret kL HkL regs0 regs M.
intros (HF & R1 & R2 & R3 & R4 & R5 & R6 & R7) H2.
eexists. split.
- stepn (ltac:(oF' 0x7ace0%Z)) (ltac:(oD' 0x7ace0%Z)).
stepn (ltac:(oF' 0x7ace4%Z)) (ltac:(oD' 0x7ace4%Z)).
stepld (ltac:(oF' 0x7ace8%Z)) (ltac:(oD' 0x7ace8%Z)) ra ltac:(maddr (s - 8)%Z; exact R1).
stepld (ltac:(oF' 0x7acec%Z)) (ltac:(oD' 0x7acec%Z)) (getr regs0 8) ltac:(maddr (s - 16)%Z; exact R2).
stepld (ltac:(oF' 0x7acf0%Z)) (ltac:(oD' 0x7acf0%Z)) (getr regs0 9) ltac:(maddr (s - 24)%Z; exact R3).
stepld (ltac:(oF' 0x7acf4%Z)) (ltac:(oD' 0x7acf4%Z)) (getr regs0 18) ltac:(maddr (s - 32)%Z; exact R4).
stepld (ltac:(oF' 0x7acf8%Z)) (ltac:(oD' 0x7acf8%Z)) (getr regs0 19) ltac:(maddr (s - 40)%Z; exact R5).
stepld (ltac:(oF' 0x7acfc%Z)) (ltac:(oD' 0x7acfc%Z)) (getr regs0 20) ltac:(maddr (s - 48)%Z; exact R6).
stepld (ltac:(oF' 0x7ad00%Z)) (ltac:(oD' 0x7ad00%Z)) (getr regs0 21) ltac:(maddr (s - 56)%Z; exact R7).
stepiv (ltac:(oF' 0x7ad04%Z)) (ltac:(oD' 0x7ad04%Z)) (Z_to_bv 64 s) ltac:(wval).
stepret (ltac:(oF' 0x7ad08%Z)) (ltac:(oD' 0x7ad08%Z)) ra ltac:(rwH; reflexivity).
apply mst_refl.
- repeat split; gres; try reflexivity; [symmetry; apply sp_s | solve_keeps_but].
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_region_is_poisoned_run := (ltac2:(TCodec.tc2 tcn__Ja0RegionPoisoned "RF&By5'R?yR0%211%5241':&Q5r1(R=+:(8%33;21%6251&R>vQO%22=1%;3=41r2+;%;3C19%>231vQN%92D1%B3D31r3+2%B3J1@%E231vR<%H3J21r4+1%H3Q01F%K231vR3%N3Q021';'6y8%Q611%311p0Q61'9'F&Q=&Q6vQIr7+_Zk8%Q93Q?1Q7/01Q?vQMvR:%8576321%958Q5DQ?2%<3;21%QB2Q7Q=z%Q=2QH1%QF3QH31%QF2Q;Q2%QH3QJ1Q1%QH2Q=N%QJ3QL1M&Q;%12BQ@&M%11QL&Q<%12BQN%L231%M261%N291%O2<1%Q02?1%Q12D1qQ:Q31%Q92Q41qT>R:1%Q;2R;1p0Q=1p0QD1p0QK1p0R31pT<R@1")) (only parsing).
Variable regs : ltac:(sec_ty2 constr:(SEC_T_region_is_poisoned_run) 0%nat 0%nat).
Theorem region_is_poisoned_run : ltac:(sec_stmt2 constr:(SEC_T_region_is_poisoned_run) 1%nat 0%nat).
Proof using Hs_def Hn Happ Hs Hshs Hok Hret HG kL HZ HL HkL regs.
intros H10 H11 H2 H1.
destruct (c1_run regs H10 H11 H2 H1) as (r1 & RUN1 & P1 & K1).
destruct (c2_run regs r1 P1) as (r2 & RUN2 & P2 & K2).
destruct (c3_run regs r2 P2) as (r3 & RUN3 & P3 & K3).
destruct (c4_run regs r3 P3) as (r4 & RUN4 & P4 & K4).
destruct (c5_run regs r4 P4) as (r5 & M5 & RUN5 & RL5 & S5 & K5 & G5).
destruct (c6_run regs r5 M5 RL5 S5) as (r6 & RUN6 & Q10 & Q2 & Q1 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & K6).
exists r6, M5. split.
- eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|].
eapply msteps_trans; [exact RUN4|]. eapply msteps_trans; [exact RUN5|]. exact RUN6.
- assert (KB : keeps_but RIPL regs r6).
{ eapply keeps_but_trans; [exact K1|]. eapply keeps_but_trans; [exact K2|]. eapply keeps_but_trans; [exact K3|].
eapply keeps_but_trans; [exact K4|]. eapply keeps_but_trans; [exact K5|]. exact K6. }
repeat split; try assumption.
+ intros r Hr. destruct (decide (r = 1%bv)) as [->|N1]; [rewrite Q1, H1; reflexivity|].
destruct (decide (r = 2%bv)) as [->|N2]; [rewrite Q2, H2; reflexivity|].
destruct (decide (r = 8%bv)) as [->|N8]; [exact Q8|]. destruct (decide (r = 9%bv)) as [->|N9]; [exact Q9|].
destruct (decide (r = 18%bv)) as [->|N18]; [exact Q18|]. destruct (decide (r = 19%bv)) as [->|N19]; [exact Q19|].
destruct (decide (r = 20%bv)) as [->|N20]; [exact Q20|]. destruct (decide (r = 21%bv)) as [->|N21]; [exact Q21|].
apply KB; [exact Hr|]. cbv. intuition congruence.
+ exact (proj1 RL5).
Qed.
End SE.
End RIP.
End FPX_1.
