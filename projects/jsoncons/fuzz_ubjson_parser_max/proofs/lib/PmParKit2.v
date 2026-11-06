(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
PmLayout PmModel PmModelFacts PmStatics PmSpecs PmStep PmKeep PmFrame PmParSpecs PmParKit.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmParKit2 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Core.L5C."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmParKit.PMPK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmParKit2.PMPK2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecs.PMSP."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1app"; "1cons"; "1fst"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1snd"; "2and"; "2eq"; "2iff"; "2not"; "2or"; "3lt"]; ["4Forall"; "4nth"; "5Z"; "0L"; "0M"; "0M'"; "6credit"; "6heap_layout"; "6hl_b_overhead"; "6hl_k_per_malloc"; "7agree_on"; "8u64_at"; "8u8_at"; "9CHUNK"; "9PST"; "9VLong"]; ["9mode_bottom"; "9mode_flag"; "9p_b"; "9p_depth"; "9p_done"; "9p_k"; "9p_more"; "9p_src"; "9p_stk"; "9p_tb"; "9p_tg"; "9parser_at"; "9pot_parser"; "9ps_mode"; "9pst"; "9pstate"]; ["9pstate_at"; "9pstate_ok"; "9sr_qc"; "9stack_shape"; "9strm"; "9tb_ok"; "9top_flag"; "9unread"; "9vec_at"; "9vstr"; ":dkr"; ";lp_W"; ";lp_X"; ";lp_mu"; ";lp_w"; "<T3"]; ["<T4"; "<cr0"; "<credit_keep"; "<push_rel"; "=add"; "=le"; "=lt"; "=mul"; "=of_nat"; "=opp"; "=pow"; "=sub"; "0b"; "0c"; "0cr"; "0cr1"]; ["0d"; "0i"; "0k"; "0l1"; "0l2"; "0m"; "0n"; "0ois"; "0op"; "0p"; "0p'"; "0p1"; "0pre"; "0q"; "0s"; "0s'"]; ["0s1"; "0s2"; "0s3"; "0segs"; "0sm"; "0sm'"; "0sm1"; "0sm2"; "0sm3"; ">bv"; "0stk"; "0top"; "0v"]]).
Module PMPK2.
Definition lp_w (p : PM.pstate) : Z :=
if (Z.eqb (PM.ps_mode p) 3 || Z.eqb (PM.ps_mode p) 9 || Z.eqb (PM.ps_mode p) 10)%bool then - 1 - PM.ps_idx p
else if (Z.eqb (PM.ps_mode p) 0 || Z.eqb (PM.ps_mode p) 1)%bool then 0
else PM.ps_len p - PM.ps_idx p.
Definition lp_W (stk : list PM.pstate) : Z := fold_right (fun p w => lp_w p + w) 0 stk.
Definition lp_X (stk : list PM.pstate) : Z := (lp_W stk + 2 ^ 35) * 4096 + 2 * Z.of_nat (length stk) + PM.top_flag stk.
Definition lp_mu (s : PM.pst) (sm : PM.strm) : Z := PM.unread (PM.p_src s) sm * 2 ^ 50 + lp_X (PM.p_stk s).
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmParKit2 "G'Q?&QAr1%211':&R5&R;&R9&R:+2+H%3221%511+1%8221&QNr2%211%=241%>228%@221p0B1pUDF1")) (only parsing).
Variable p : ltac:(sec_ty2 constr:(SECT) 0%nat 0%nat).
Lemma lp_w_bound : ltac:(sec_stmt2 constr:(SECT) 1%nat 0%nat).
Proof.
unfold PM.pstate_ok, lp_w, PM.MAX_ITEMS, PM.mode_counted, PM.mode_indef, PM.mode_bottom.
intros (_ & [(Hm & H1 & H2)|[(Hm & H1 & H2)|(Hm & H1 & H2)]]).
- destruct Hm as [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ]; cbn; lia.
- destruct Hm as [ -> | [ -> | -> ] ]; cbn; lia.
- destruct Hm as [ -> | -> ]; cbn; lia.
Qed.
End S.
Lemma lp_W_app : ltac2:(TCodec.tc2 tcn__PmParKit2 "B'5'Q?%211';'B&QK&1r2r1%33821%511&R4%715%815%3221%<3;51pU:>1pU8?1").
Proof. intros l1 l2. induction l1 as [|x l1 IH]; cbn; [reflexivity|]. unfold lp_W in IH |- *. cbn in IH |- *. rewrite IH. lia. Qed.
Lemma lp_W_one : ltac2:(TCodec.tc2 tcn__PmParKit2 ">'Q?';'B&QK(2r1(7%117%43831%611&QN%116%;3:31pUD=1").
Proof. intros p. unfold lp_W. cbn. lia. Qed.
Lemma lp_W_bound : ltac2:(TCodec.tc2 tcn__PmParKit2 "Q1'5'Q?%211'@&QAr1%33521':&R5&R7&R;&R9&R:+2+H%3221%511+1%8221&R8&4r2%22E1%411%?261&QK%115%C231%C2=5%E231%G231p0I1pVFN1").
Proof. intros stk.
induction 1 as [|x l Hx Hl IH]; [cbn; lia|].
pose proof (lp_w_bound x Hx). unfold lp_W in IH |- *. cbn [fold_right length]. rewrite Nat2Z.inj_succ. lia.
Qed.
Lemma mode_flag_01 : ltac2:(TCodec.tc2 tcn__PmParKit2 "<'B':&R5z&Q1r1%211%5241+1%7231%9231pU<;1").
Proof. intros m. unfold PM.mode_flag. destruct (_ || _ || _ || _)%bool; lia. Qed.
Lemma top_flag_01 : ltac2:(TCodec.tc2 tcn__PmParKit2 ">'5'Q?%211':&R5z&QFr1%211%5241+1%7231%9231pVF;1").
Proof. intros stk. unfold PM.top_flag. apply mode_flag_01. Qed.
Lemma shape_forall : ltac2:(TCodec.tc2 tcn__PmParKit2 "<'5'Q?%211&QCr1%211'@&QAr2%33821p051pVF91").
Proof. intros stk.
intros (_ & _ & _ & _ & H). apply Forall_nth. intros i d Hi.
rewrite (nth_indep stk d PM.ps_root Hi). apply H. exact Hi.
Qed.
Lemma lp_X_bound : ltac2:(TCodec.tc2 tcn__PmParKit2 "F'5'Q?%211&QCr1%211':&R5z&QLr2%211%5241&R6&R:+2+QB%3221%5271%=271p0?1pVFC1").
Proof. intros stk.
intros SH. pose proof (lp_W_bound stk (shape_forall stk SH)) as B. pose proof SH as (_ & L2 & _).
unfold PM.MAX_DEPTH in L2. pose proof (top_flag_01 stk). unfold lp_X. nia.
Qed.
Lemma lp_mu_lt_U : ltac2:(TCodec.tc2 tcn__PmParKit2 "Q7'Q>'QD&QC&Q8r4%211%411r3%511%711&R5z&QG&Q7%11:%3218%6251&R6r5%611%821@r7%911r6%<221%8251&QM%1249r8%3218%=231p061p0@1p0H1p0L1pV<Q21pV0Q41pV:Q41pUNQ61").
Proof. intros s sm s' sm'.
intros S1 S2 U0 U1. pose proof (lp_X_bound _ S1). pose proof (lp_X_bound _ S2). unfold lp_mu. nia.
Qed.
Lemma lp_mu_pop : ltac2:(TCodec.tc2 tcn__PmParKit2 "QB'Q>'QD'Q?';'5%113&Q8r5%211&1r3%511(2r1(7%11=%43>31%83?61%?3=:1'B&QNr2%211z%E3521&R5&QG&Q7%11Er4%4221r7%511r6%8221%:251&R6&QM%125Or8%3219%5231p071p0C1p0J1pVHQ;1pV<Q=1pV0Q?1pV:Q?1pUNQA1").
Proof. intros s sm s' sm' top.
intros E W0 U1. unfold lp_mu, lp_X. rewrite E, lp_W_app, lp_W_one, W0, length_app. cbn [length].
pose proof (top_flag_01 (PM.p_stk s' ++ [top])). pose proof (top_flag_01 (PM.p_stk s')). rewrite Nat2Z.inj_add. cbn [Z.of_nat Pos.of_succ_nat]. nia.
Qed.
Lemma lp_mu_pushv : ltac2:(TCodec.tc2 tcn__PmParKit2 "QF'Q>'QD&QC&Q8r6%211%411r3%511%711&R6&QL%117r8%;11%411%6241&R5&QG&Q7r7%211%421Br9%511%721<%9241z%91Hr5%<221%>241&R3r:%241E;>&QM%12=Gr=r<%4221%N241p071p0@1p0<1p0B1p0M1p0Q51p0Q91pVBQ?1pV6QA1pV@QA1pV4QC1pV>QC1pV2QE1").
Proof. intros s1 sm1 s2 sm2 s3 sm3.
intros S1 S3 X21 U21 U30 U32 [E|(c & E & OK & I0 & NB & CT)].
- unfold lp_mu. rewrite E. nia.
- destruct (Z_lt_le_dec (PM.unread (PM.p_src s3) sm3) (PM.unread (PM.p_src s2) sm2)) as [LT|GE].
+ apply (lp_mu_lt_U s1 sm1 s3 sm3 S1 S3 U30). lia.
+ assert (NC : ~ PM.mode_counted (PM.ps_mode c)) by (intros X; specialize (CT X); lia).
assert (WC : lp_w c = - 1).
{ pose proof OK as (_ & [(Hm & _)|[(Hm & _)|(Hm & _)]]); [contradiction| |contradiction].
unfold lp_w, PM.mode_indef in *. rewrite I0. destruct Hm as [ -> | [ -> | -> ] ]; cbn; lia. }
unfold lp_mu, lp_X in *. rewrite E, lp_W_app, lp_W_one, WC, length_app in *. cbn [length] in *. rewrite Nat2Z.inj_add in *.
pose proof (top_flag_01 (PM.p_stk s2 ++ [c])). pose proof (top_flag_01 (PM.p_stk s2)). cbn [Z.of_nat Pos.of_succ_nat] in *. nia.
Qed.
Lemma lp_X_set_top : ltac2:(TCodec.tc2 tcn__PmParKit2 "Q9'5'Q?%211';'B&QL&1r3(2r1(7%11:%43;31%73<61%911&R;&R4r2%:3A17%=3B<1%?11&R7+TP0&QN%11?%218%;221%6251%<281&Q1&Q=%11F%311%A251%41A%611%E231%Q23Q1G1pUFQ51pUDQ61pUJQ61").
Proof. intros pre p p'.
unfold lp_X, PM.top_flag. rewrite !lp_W_app, !lp_W_one, !length_app, !last_last. cbn [length]. lia.
Qed.
Lemma nth_app_last : ltac2:(TCodec.tc2 tcn__PmParKit2 "Q4'5'Q?%211'6&?r2&4&1r4(2r3(7%11;%43<31%73=61%92>1%<2;1&=';r5%>2C1%33B;1%511&Ar6%@3H6=%C3I21%44JC1A%54KD4B%;3L21p081p0?1pU2O1pU4N1pUDQ11pUJQ11").
Proof. intros pre p i d. intros H N. rewrite length_app in H. cbn in H. rewrite app_nth1 by lia. reflexivity. Qed.
Lemma nth_app_at : ltac2:(TCodec.tc2 tcn__PmParKit2 "E'5'Q?%211';&A&4r3%2261&1(2r2(7%11;%43<31%63=81r1%<4?921%>3@17pU2A1pUDB1pUJB1").
Proof. intros pre p d. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity. Qed.
Lemma stack_shape_set_top : ltac2:(TCodec.tc2 tcn__PmParKit2 "Q2'5'Q?%211&QC&1r3(2r2(7%118%43931%73:61%911&QA%117&<&Q0&Q=r4%211%411%41@%611%8231r6%C3H7@%F3I21%H11p051p0?1p0B1pUFN1pUDO1pUJO1").
Proof. intros pre p p'.
intros (H1 & H2 & H3 & H4 & H5) OK' EB. unfold PM.stack_shape. rewrite !length_app in *. cbn [length] in *.
split; [lia|]. split; [exact H2|].
split.
{ destruct pre as [|x pre]; cbn in *; [apply EB; exact H3| exact H3]. }
split.
{ intros i Hi. destruct (Nat.eq_dec i (length pre)) as [->|N].
- rewrite nth_app_at. intros B. apply EB in B. specialize (H4 (length pre) ltac:(lia)). rewrite nth_app_at in H4. exact (H4 B).
- rewrite nth_app_last by (try rewrite length_app; cbn; lia). specialize (H4 i ltac:(lia)). rewrite nth_app_last in H4 by (try rewrite length_app; cbn; lia). exact H4. }
intros i Hi. destruct (Nat.eq_dec i (length pre)) as [->|N].
- rewrite nth_app_at. exact OK'.
- rewrite nth_app_last by (try rewrite length_app; cbn; lia). specialize (H5 i ltac:(lia)). rewrite nth_app_last in H5 by (try rewrite length_app; cbn; lia). exact H5.
Qed.
Lemma top_of_shape : ltac2:(TCodec.tc2 tcn__PmParKit2 "Q2'5'Q?%211&QC&1r2(2r1(7%118%43931%73:61%911':&QA%11:'>';r3%23A1:&Q0&Q=%11A%311%;251&=%117%214%?221%=251%A2?1p0C1pUDO1pUJO1").
Proof. intros pre p.
intros (H1 & H2 & H3 & H4 & H5). rewrite length_app in *. cbn [length] in *.
split; [specialize (H5 (length pre) ltac:(lia)); rewrite nth_app_at in H5; exact H5|].
destruct pre as [|x pre]; [left; split; [reflexivity| exact H3]|].
right. split; [discriminate|]. specialize (H4 (length (x :: pre)) ltac:(cbn; lia)). rewrite nth_app_at in H4. exact H4.
Qed.
Section Kit.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Variable A : pm_addrs.
Abbreviation T3 := PMSP.T3.
Abbreviation T4 := PMSP.T4.
Section Upd.
Variables M M' : word -> option byte.
Abbreviation ag := (L5C.agree_on M M').
Local Ltac u64x AG H := apply (L5C.u64_at_agree segs M M'); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia|exact H].
Local Ltac u32x AG H := apply (PMF.u32_at_agree segs M M'); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia|exact H].
Local Ltac u8x AG H := apply (L5C.u8_at_agree segs M M'); [eapply L5C.agree_on_sub; [exact AG|lia|lia]|lia|lia|exact H].
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmParKit2 "S4'B'5'Q?%211&QHvS3&QO&R0vDr6r5r4&1r3(2r2(7%11?%43@31%73A61%@8?>=<;:91&R5zr7%3221&R4r8+H%3221&R:+2+R0%3221%<251%=2<8r9&R7+Q0%928<%3221%?251%D219&JvEr;%34Q521B&R8&4%12Q>=%311%>2=1%94Q;871r<r:%72QD1%911%D2C1%Q0251%Q121E&R;%O2N@%I2H1%3216%421J%F4QHE61&QJr=%D2R1G%F11%Q12Q01%Q=241%64QOL1Q2&Q@r>%K2R8F%M11%Q82Q71%QD241%64R9Q31Ir@r?%R33R?Q5R0%R63R@@1%R?8R>R=R<Q843:1p061p0>1p0F1p0Q41p0Q;1p0Q@1p0QH1p0QJ1p0R41p0R91pUFRL1pUDRM1pUJRM1pU6S11pTJS21pVJS31")) (only parsing).
Variable v : ltac:(sec_ty2 constr:(SECT) 0%nat 0%nat).
Variable b : ltac:(sec_ty2 constr:(SECT) 1%nat 0%nat).
Variable k : ltac:(sec_ty2 constr:(SECT) 2%nat 0%nat).
Variable pre : ltac:(sec_ty2 constr:(SECT) 3%nat 0%nat).
Variable p : ltac:(sec_ty2 constr:(SECT) 4%nat 0%nat).
Variable p' : ltac:(sec_ty2 constr:(SECT) 5%nat 0%nat).
Lemma vec_at_set_top : ltac:(sec_stmt2 constr:(SECT) 6%nat 0%nat).
Proof.
intros (V0 & V8 & V16 & Hk & Hlen & Hal & DB & _ & _ & EL) Hv Hv' Hb Hb' AG0 AGL AGH DKT PT.
unfold PM.vec_at. rewrite !length_app in *. cbn [length] in *. rewrite !Nat2Z.inj_add in *. cbn [Z.of_nat Pos.of_succ_nat] in *.
split; [u64x AG0 V0|]. split; [u64x AG0 V8|]. split; [u64x AG0 V16|].
split; [exact Hk|]. split; [exact Hlen|]. split; [exact Hal|].
split.
{ intros i Hi. destruct (Z_lt_le_dec i (32 * Z.of_nat (length pre))) as [X|X]; [rewrite AGL by lia; apply DB; lia|].
destruct (Z_lt_le_dec i (32 * Z.of_nat (length pre) + 32)) as [Y|Y].
- replace (b + i) with (b + 32 * Z.of_nat (length pre) + (i - 32 * Z.of_nat (length pre))) by lia.
apply DKT; [lia|]. replace (b + 32 * Z.of_nat (length pre) + (i - 32 * Z.of_nat (length pre))) with (b + i) by lia. apply DB; lia.
- rewrite AGH by lia. apply DB; lia. }
split; [exact I|]. split; [exact I|].
intros i Hi.
destruct (Nat.eq_dec i (length pre)) as [->|N]; [rewrite nth_app_at; exact PT|].
rewrite nth_app_last by (try rewrite length_app; cbn; lia).
specialize (EL i ltac:(lia)). rewrite nth_app_last in EL by (try rewrite length_app; cbn; lia).
apply (PMF.pstate_at_agree segs M M'); [lia|lia| |exact EL].
apply (L5C.agree_on_sub M M' b (32 * Z.of_nat (length pre))); [exact AGL|lia|lia].
Qed.
End S.
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmParKit2 "TI'B'Q>'5'Q?%211&Q;vS3v0&QO&R0vDr6r5r4%9887654321';&Q8%115&1(2r3(7%11C%43D31%63E;1%:3E81&R5zr8%3221&R4r9+\0%3221&R:+2+R0%3221%<251&JvEr:%34Q021:&QJ&QB&Q7%11?%311&M%64Q7921&Q2%11:%J2I1r;%411&R7+Q0&Q5%115%I2H1%5241%O271%Q421Ir<%>11&R8&4%12R0>%311%>2=1%O4QLN61r=%F11%72R6:%911%D2C1%Q>241%Q?21E&R;%F18%Q>2Q=1%J2I1%4217%521K%Q=4R:Q<71r>%Q411%E2RD@%G11%Q22Q11%QL241%Q@4RAQC1Q3&Q@r?%Q<11%M2RL:%O11%Q:2Q91%R4241%74RMQK1Q4'QI&Q9rC%211(Or2r1%33RG21%RM3851%R24S3R54S0p021pULS?1pU>S@1pTLSA1rB(N&Q6rA%211&Q4%113&Q3%115%R>16%G17&Q:%119%R=1:%R71;r@%S?3SOQ=S<%SA3T021%A9><:986541%T08SOSNSMSLRMOC1p0E1p0Q41p0Q=1p0QE1p0R41p0R=1p0RH1p0RL1p0S41p0S91p0SC1p0SH1p0T41pUFT@1pUDTA1pUJTA1pUNTE1pU@TG1pUBTH1")) (only parsing).
Variable op : ltac:(sec_ty2 constr:(SECT) 0%nat 0%nat).
Variable ois : ltac:(sec_ty2 constr:(SECT) 1%nat 0%nat).
Variable s : ltac:(sec_ty2 constr:(SECT) 2%nat 0%nat).
Variable pre : ltac:(sec_ty2 constr:(SECT) 3%nat 0%nat).
Variable p : ltac:(sec_ty2 constr:(SECT) 4%nat 0%nat).
Variable p' : ltac:(sec_ty2 constr:(SECT) 5%nat 0%nat).
Lemma parser_top_upd : ltac:(sec_stmt2 constr:(SECT) 6%nat 0%nat).
Proof.
intros (H0 & D & _ & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & _ & TB & VEC & B1 & B2 & B3) ES Ho Ho' AG DKC Hb Hb' AGL AGH DKT PT AGT.
destruct SRC as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & G1 & G2 & G3 & G4 & DC & _ & _).
rewrite ES in VEC.
unfold PM.parser_at. cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk].
split; [u64x AG H0|].
split; [intros i Hi; rewrite AG by lia; apply D; lia|].
split; [exact I|]. split; [u8x AG H8|]. split; [u8x AG H9|]. split; [u32x AG H12|]. split; [u8x AG H16|]. split; [u32x AG H20|].
split. { apply (PMF.nullis_at_agree segs A M M'); [lia| lia| eapply L5C.agree_on_sub; [exact AG|lia|lia]| exact NI]. }
split.
{ split; [u64x AG F1|]. split; [u64x AG F2|].
split. { apply (L5C.defined_agree M M'); [eapply L5C.agree_on_sub; [exact AG|lia|lia]| exact F3]. }
split; [u64x AG F4|]. split; [u64x AG F5|]. split; [u64x AG F6|]. split; [u64x AG F7|].
split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
split; [apply (PMPK.defined_dkr M M' _ _ DKC DC)|]. split; exact I. }
split; [u32x AG H320|]. split; [u64x AG H328|]. split; [exact I|].
split. { apply (PMPK.vstr_at_keep segs M M'); [lia| lia| eapply L5C.agree_on_sub; [exact AG|lia|lia]| exact AGT| exact TB]. }
split. { apply (vec_at_set_top (op + 360) (PM.p_b s) (PM.p_k s) pre p p' VEC); [lia|lia|exact Hb|exact Hb'| eapply L5C.agree_on_sub; [exact AG|lia|lia]| exact AGL| exact AGH| exact DKT| exact PT]. }
split; [exact B1|]. split; [exact B2| exact B3].
Qed.
End S.
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmParKit2 "T6'B'Q>&Q;vS3v0&QO&R0vDr3r2r1%9887654321&R5zr4%3221&R4r5+\0%3221&R:+2+R0%3221%<251&JvEr6+8%44F321r7+:%@221+[6%94K821r8+[H%E221%=4O<1:&QJr9%I21=%34Q3@1Er:+[@%M221%74Q7D1B&Lr;%Q121E%34Q?H1Q5r<+9%Q5221+1%84QDM21&Kr=%Q:21>&Q2%11<%54QJQ331&QB&Q7%11=%311&M%L4QLQ921%91;%QI2QH1r>%<11&R7+Q0&Q5%115%QH2QG1%5241%QN271%R321QHr?%F11%812%QO2QN1%<2;1%QL4R>QK41';'QI&Q9rC%211(O%13RDRCRB%73631%QG4RGR4RER@p021pULS01pU>S11pTLS21rB(N&Q3rA%211%Q912%A13&Q:%115%QA16%Q317(7'Q?%211%=9S4QK:986541%S@8S?S>S=S<RHI?1p0A1p0O1p0Q61p0QA1p0QD1p0QK1p0R21p0R81p0R=1p0RB1p0RG1p0RL1p0S21p0S81p0SB1p0SG1pUNT21pU@T41pUBT51")) (only parsing).
Variable op : ltac:(sec_ty2 constr:(SECT) 0%nat 0%nat).
Variable ois : ltac:(sec_ty2 constr:(SECT) 1%nat 0%nat).
Variable s : ltac:(sec_ty2 constr:(SECT) 2%nat 0%nat).
Lemma parser_accept_upd : ltac:(sec_stmt2 constr:(SECT) 3%nat 0%nat).
Proof.
intros (H0 & D & _ & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & _ & TB & VEC & B1 & B2 & B3) Ho Ho' AG1 AG2 AG3 DK8 DK368 C8 C9 C368 DKC Hb Hb' AGV AGT.
destruct SRC as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & G1 & G2 & G3 & G4 & DC & _ & _).
unfold PM.parser_at. cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk].
assert (AG4 : forall a n, op + 10 <= a -> a + n <= op + 368 -> ag a n) by (intros a n X1 X2; eapply L5C.agree_on_sub; [exact AG2|lia|lia]).
split; [u64x AG1 H0|].
split. { intros i Hi. destruct (Z_lt_le_dec i 8) as [X|X]; [rewrite AG1 by lia; apply D; lia|].
destruct (Z_lt_le_dec i 10) as [Y|Y]; [apply DK8; [lia| apply D; lia]|].
destruct (Z_lt_le_dec i 368) as [Y2|Y2]; [rewrite AG2 by lia; apply D; lia|].
destruct (Z_lt_le_dec i 376) as [Y3|Y3]; [apply DK368; [lia| apply D; lia]| rewrite AG3 by lia; apply D; lia]. }
split; [exact I|]. split; [exact C8|]. split; [exact C9|].
split; [apply (PMF.u32_at_agree segs M M'); [apply AG4; lia|lia|lia|exact H12]|].
split; [apply (L5C.u8_at_agree segs M M'); [apply AG4; lia|lia|lia|exact H16]|].
split; [apply (PMF.u32_at_agree segs M M'); [apply AG4; lia|lia|lia|exact H20]|].
split. { apply (PMF.nullis_at_agree segs A M M'); [lia| lia| apply AG4; lia| exact NI]. }
split.
{ split; [u64x AG2 F1|]. split; [u64x AG2 F2|].
split. { apply (L5C.defined_agree M M'); [apply AG4; lia| exact F3]. }
split; [u64x AG2 F4|]. split; [u64x AG2 F5|]. split; [u64x AG2 F6|]. split; [u64x AG2 F7|].
split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
split; [apply (PMPK.defined_dkr M M' _ _ DKC DC)|]. split; exact I. }
split; [apply (PMF.u32_at_agree segs M M'); [apply AG4; lia|lia|lia|exact H320]|]. split; [u64x AG2 H328|]. split; [exact I|].
split. { apply (PMPK.vstr_at_keep segs M M'); [lia| lia| apply AG4; lia| exact AGT| exact TB]. }
split.
{ destruct VEC as (V0 & V8 & V16 & Hk & Hlen & Hal & DB & _ & _ & EL).
split; [u64x AG2 V0|]. split; [replace (op + 360 + 8) with (op + 368) by lia; match goal with |- L5.u64_at _ _ _ ?x => replace x with (PM.p_b s) by (cbn; lia) end; exact C368|].
split; [u64x AG3 V16|]. split; [exact Hk|]. split; [cbn [length Z.of_nat]; pose proof (PM.pow2_pos (PM.p_k s) ltac:(lia)); lia|].
split; [exact Hal|]. split; [apply (L5C.defined_agree M M' _ _ AGV DB)|]. split; [exact I|]. split; [exact I|].
intros i Hi. cbn in Hi. lia. }
split; [left; reflexivity|]. split; [right; reflexivity| exact B3].
Qed.
End S.
End Upd.
Section S.
Local Abbreviation SECT := (ltac2:(TCodec.tc2 tcn__PmParKit2 "QJ'G'S9yR0%211'8y8%511%311p051'B'Q>&Q;vS3v0&QO&R0r4r3r2r1%9887654321&QE&Q9%115&Q:%117%5231&R5z&Ir7%211%5241&Hr8%211%9281':&3&Q<r9r5%3221%53Q2Q21%A2@1&9%13Q5Q54%D2C1%;241p0=1p0B1p0I1p0Q01pUNQ;1pU@Q=1pUBQ>1pQ:Q@1pQ8QI1")) (only parsing).
Variables (L : heap_layout).
Variable M : ltac:(sec_ty2 constr:(SECT) 1%nat 0%nat).
Variable op : ltac:(sec_ty2 constr:(SECT) 2%nat 0%nat).
Variable ois : ltac:(sec_ty2 constr:(SECT) 3%nat 0%nat).
Variable s : ltac:(sec_ty2 constr:(SECT) 4%nat 0%nat).
Lemma pot_parser_nonneg : ltac:(sec_stmt2 constr:(SECT) 5%nat 0%nat).
Proof.
intros PA (T0 & T1 & T2) K0 B0.
pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TB & VEC & _).
pose proof VEC as (_ & _ & _ & Hk & _).
unfold PM.pot_parser, PM.credit_add, PM.pot_stack, PM.pot_text. cbn [fst snd].
assert (P2 : 2 ^ (PM.p_k s + 1) <= 2 ^ 12) by (apply Z.pow_le_mono_r; lia).
assert (CAP : PM.vs_cap (PM.p_tb s) <= 2 ^ 27 - 1).
{ destruct (PM.p_tb s) as [n|c n q]; cbn [PM.vs_cap]; [lia|]. destruct TB as (_ & _ & _ & _ & _ & _ & (_ & C2) & _). lia. }
split; nia.
Qed.
End S.
Lemma credit_keep_final : ltac2:(TCodec.tc2 tcn__PmParKit2 "L&F&R2r4r3r2r1%544321&R5z&3'B%23117%5241&9%1344;%8271r7r6r5&R1%C44321p061p0:1p0A1pUHH1pUDI1pU0J1pTNK1").
Proof. intros cr cr1 p p1. unfold PMSP.credit_keep, PMSP.cr0. cbn [fst snd]. lia. Qed.
End Kit.
End PMPK2.
