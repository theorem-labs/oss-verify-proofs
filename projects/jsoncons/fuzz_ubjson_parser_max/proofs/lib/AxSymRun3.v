(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AxSymExec3 AxSymExec3Sound.
Import ListNotations.
Open Scope bv_scope.
Import AX2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import AX2S.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__AxSymRun3 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.StackLayout."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "LinuxProcessSemantics.Riscv.Sem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3.AX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3Sound.AX2S."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymRun3.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1O"; "1Some"; "1app"; "1bool"; "1cons"; "1false"; "1length"; "1list"; "1nat"; "1negb"; "1nil"; "1option"; "1pair"; "1prod"; "1true"]; ["2I"; "2and"; "2eq"; "2ex"; "2iff"; "2not"; "3le"; "4nth"; "5Z"; "0E"; "0E'"; "0E''"; "0K"; "6PhdrInfo"; "6Segment"; "7store_ok"]; ["7word_to_le_bytes"; "8EntryDraw"; "9stack_max_size"; ":BC_EQ"; ":BC_GEU"; ":BC_LTU"; ":BC_NE"; ";bvmap"; ";bvmap_empty"; "<branch_taken"; "0R"; "=ELit"; "=Env"; "=KAlign"; "=KBlob"; "=KImg"]; ["=KRange"; "=KWord"; "=KWr"; "=KZero"; "=SA"; "=SSR"; "=adenot"; "=carry"; "=eb"; "=edenot"; "=env"; "=expr"; "=ext_val"; "=itab"; "=itab_sound"; "=kentry"]; ["=ridx"; "=s_know"; "=s_log"; "=s_next"; "=s_pc"; "=s_regs"; "=saddr"; "=scripts"; "=sentry"; "=sidecond"; "=sr_get"; "=sr_upd"; "=sym_exec"; "=sym_execTX"; "=sym_state"; ">eagree"]; [">flat"; ">kentry_ok"; ">know_ok"; ">log_flat"; ">mem_denot"; ">regs_ok"; ">scs_denot"; ">st_ok"; "?env_agree"; "?expr_vars_lt"; "?kn_vars_lt"; "?log_vars_lt"; "?saddr_vars_lt"; "?sr_init"; "?sr_vars_lt"; "?stk_ok"]; ["?vals_ev"; "@msteps"; "Agetr"; "Amkst"; "Ardn"; "Aregupd"; "Av_addi"; "Awrap_mem"; "Bmem_grows"; "Cadd"; "Ceqb"; "Cle"; "Clt"; "Cltb"; "Cmodulo"; "Cmul"]; ["Cof_nat"; "Copp"; "Cpow"; "Csub"; "Cto_nat"; "0a"; "0argv"; "0b"; "0base"; "0bs"; "0e"; "0ebs"; "0envp"; "0extra"; "0fuel"; "0fx"]; ["0hi"; "0hints"; "0hs'"; "0hw"; "0i"; "0k"; "0kn"; "0kn'"; "0len"; "0lo"; "0log"; "0m"; "0mem"; "0mem'"; "0n"; "0nx"]; ["0off"; "0pc"; "0ph"; "0r"; "0rd"; "0rdraw"; "0regs"; "0rest"; "0rom"; "0scr"; "0scr'"; "0scs"; "0segs"; "0sp"; "0sr"; "0ss'"]; ["DBV"; "DZ_to_bv"; "Dbv"; "Dbv_unsigned"; "0stops"; "0t"; "0uid"; "0v"; "0vals"; "0w"; "0x"; "0z"]]).
Section FPX_1. Context {fx : FPState}.
Definition vals_ev (vals : list word) : nat -> word :=
fun n => nth n vals (Z_to_bv 64 0).
Fixpoint expr_vars_lt (b : nat) (e : expr) : bool :=
match e with
| ELit _ => true
| EVar n => Nat.ltb n b
| EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => expr_vars_lt b x && expr_vars_lt b y
| EExt _ _ _ x => expr_vars_lt b x
| EBlob _ _ _ _ => true
end.
Definition saddr_vars_lt (b : nat) (a : saddr) : bool := expr_vars_lt b (a_base a).
Fixpoint sr_vars_lt (b : nat) (sr : list expr) : bool :=
match sr with [] => true | e :: r => expr_vars_lt b e && sr_vars_lt b r end.
Definition kentry_vars_lt (b : nat) (K : kentry) : bool :=
match K with
| KWord a _ v => saddr_vars_lt b a && expr_vars_lt b v
| KZero a n => saddr_vars_lt b a && expr_vars_lt b n
| KBlob a n _ => saddr_vars_lt b a && expr_vars_lt b n
| KImg _ _ => true
| KAlign e _ => expr_vars_lt b e
| KRange e _ _ => expr_vars_lt b e
| KWr a n => saddr_vars_lt b a && expr_vars_lt b n
| KDisj a1 n1 a2 n2 => saddr_vars_lt b a1 && expr_vars_lt b n1 && saddr_vars_lt b a2 && expr_vars_lt b n2
| KFill a n _ => saddr_vars_lt b a && expr_vars_lt b n
| KUnk a n => saddr_vars_lt b a && expr_vars_lt b n
end.
Fixpoint kn_vars_lt (b : nat) (kn : list kentry) : bool :=
match kn with [] => true | K :: r => kentry_vars_lt b K && kn_vars_lt b r end.
Fixpoint log_vars_lt (b : nat) (log : list sentry) : bool :=
match log with
| [] => true
| SE a _ v :: r => saddr_vars_lt b a && expr_vars_lt b v && log_vars_lt b r
end.
Definition env_agree (b : nat) (E E' : env) : Prop :=
(forall n, (n < b)%nat -> ev E n = ev E' n) /\ eb E = eb E'.
Lemma edenot_agree : ltac2:(TCodec.tc2 tcn__AxSymRun3 "L'9'QJ'QK&RHr4r3r2%43321'B'4&RIr5%2216(?%63521'U2yR0%211&QI%128>%22@?%=3421p081p0@1pWFF1pQFH1pQDI1pW@K1").
Proof.
intros b E E' e [Hv Hb]. induction e; cbn [expr_vars_lt edenot]; intros H;
repeat match goal with
| H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
end;
try reflexivity;
try (rewrite IHe1, IHe2 by assumption; reflexivity);
try (rewrite IHe by assumption; reflexivity).
- apply Nat.ltb_lt in H. apply Hv. exact H.
- rewrite Hb. reflexivity.
Qed.
Lemma adenot_agree : ltac2:(TCodec.tc2 tcn__AxSymRun3 "L'9'QJ'R6&RHr4r3r2%43321'B'4&RLr5%2216(?%63521'U2yR0%211&QF%128>%22@?%=3421p081p0@1pW<F1pQFH1pQDI1pW@K1").
Proof.
intros b E E' a Ha H. unfold adenot. rewrite (edenot_agree b E E' _ Ha H). reflexivity.
Qed.
Lemma regs_ok_agree : ltac2:(TCodec.tc2 tcn__AxSymRun3 "Q2'9'QJ'8'QK%211&Q7y5'U2yR0%211%5241&RHr5r4r3%43321'B'4&RNr6%2216(?%63521&RE%135;:%236=<p021p051p0=1pY>C1pYNJ1pQFN1pQDO1pW@Q11").
Proof.
intros b E E' sr regs Ha Hsr HR r. rewrite (HR r).
unfold sr_get. destruct (bv_eqb r 0); [reflexivity|].
assert (Hnth : forall i, expr_vars_lt b (nth i sr (ELit 0)) = true).
{ clear HR r. induction sr as [|e t IH]; intros i.
- destruct i; reflexivity.
- cbn [sr_vars_lt] in Hsr. apply andb_prop in Hsr as [He Ht].
destruct i; [exact He | apply IH; exact Ht]. }
apply (edenot_agree b); [exact Ha | apply Hnth].
Qed.
Lemma mem_denot_agree : ltac2:(TCodec.tc2 tcn__AxSymRun3 "Q5'9'QJ'U2yR0%211'<y8%511%311p051'8'R8%211&RHr5r4r3%43321'B'4&RKr6r2%3221(?%73621&RD%136<;%23>=<%;3D21p051p0>1pXFD1pWBH1pQFQ11pQDQ21pW@Q41").
Proof.
intros b E E' base log Ha. induction log as [|[a w v] r IH]; cbn [log_vars_lt mem_denot]; intros H.
- reflexivity.
- apply andb_prop in H as [H1 H3]. apply andb_prop in H1 as [H1 H2].
rewrite IH by exact H3. rewrite (adenot_agree b E E' a Ha H1), (edenot_agree b E E' v Ha H2).
reflexivity.
Qed.
Lemma flat_agree : ltac2:(TCodec.tc2 tcn__AxSymRun3 "L'9'QJ'R6'H&RHr5r4r3%43321'B'4&RLr6%2216(?%63521&D&R@%136<;%23>=<%4221p061p0>1pXND1pW<F1pQFH1pQDI1pW@K1").
Proof.
intros b E E' a n Ha H. unfold flat, estart.
rewrite (edenot_agree b E E' (a_base a) Ha H). tauto.
Qed.
Lemma log_flat_agree : ltac2:(TCodec.tc2 tcn__AxSymRun3 "K'9'QJ'8'R8%211&RHr4r3r2%43321'B'4&RKr5%2216(?%63521&RC%125;%226=p021p051p0=1pXFC1pQFG1pQDH1pW@J1").
Proof.
intros b E E' log Ha. induction log as [|[a w v] r IH]; cbn [log_vars_lt log_flat]; intros H Hl.
- exact I.
- apply andb_prop in H as [H1 H3]. apply andb_prop in H1 as [H1 H2].
destruct Hl as (Hw & Hf & Hr). split; [exact Hw|]. split.
+ apply (flat_agree b E E' a _ Ha H1). exact Hf.
+ apply IH; assumption.
Qed.
Lemma know_ok_agree : ltac2:(TCodec.tc2 tcn__AxSymRun3 "Q:'8'N%211'9'QJ'U2yR0%211'<y8%511%311p051'QO%>11&RHr5r4r3%43321'B'4&RJr6r2%3221(?%73621&RBr8%2417=<r9%4419@?p031p071p0@1pX>F1pWBI1pQFQ21pQDQ31pW@Q51pYJQ71").
Proof.
intros segs b E E' base kn Ha. induction kn as [|K r IH]; cbn [kn_vars_lt]; intros H Hk.
- constructor.
- apply andb_prop in H as [HK Hr]. apply Forall_cons_iff in Hk as [Hk1 Hk2].
constructor; [| apply IH; assumption].
destruct Ha as [Hv Hb].
destruct K as [a w v|a n|a n k|lo hi|ae am|re rlo rhi|wa wn|da1 dn1 da2 dn2|a n fc|a n]; cbn [kentry_vars_lt kentry_ok] in *;
[ | | | | rewrite <- (edenot_agree b E E' ae (conj Hv Hb) HK); exact Hk1
| rewrite <- (edenot_agree b E E' re (conj Hv Hb) HK); exact Hk1
| apply andb_prop in HK as [HK1 HK2]; unfold flat, estart, elenZ in *;
rewrite <- (edenot_agree b E E' (a_base wa) (conj Hv Hb) HK1), <- (edenot_agree b E E' wn (conj Hv Hb) HK2); exact Hk1
| apply andb_prop in HK as [HK HK4]; apply andb_prop in HK as [HK HK3]; apply andb_prop in HK as [HK1 HK2];
unfold estart, elenZ in *;
rewrite <- (edenot_agree b E E' (a_base da1) (conj Hv Hb) HK1), <- (edenot_agree b E E' dn1 (conj Hv Hb) HK2),
<- (edenot_agree b E E' (a_base da2) (conj Hv Hb) HK3), <- (edenot_agree b E E' dn2 (conj Hv Hb) HK4); exact Hk1
| | ].
+ apply andb_prop in HK as [H1 H2].
rewrite <- (adenot_agree b E E' a (conj Hv Hb) H1), <- (edenot_agree b E E' v (conj Hv Hb) H2).
destruct Hk1 as (A & B & C). split; [exact A|]. split; [|exact C].
apply (flat_agree b E E' a _ (conj Hv Hb) H1). exact B.
+ apply andb_prop in HK as [H1 H2]. unfold elenZ, estart in *.
rewrite <- (edenot_agree b E E' n (conj Hv Hb) H2), <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1).
destruct Hk1 as [A B]. split; [|exact B].
unfold flat, estart in *. rewrite <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1). exact A.
+ apply andb_prop in HK as [H1 H2]. unfold elenZ, estart in *. rewrite <- Hb.
rewrite <- (edenot_agree b E E' n (conj Hv Hb) H2), <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1).
destruct Hk1 as (A & B & C). split; [|split; [exact B | exact C]].
unfold flat, estart in *. rewrite <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1). exact A.
+ exact Hk1.
+
apply andb_prop in HK as [H1 H2]. unfold elenZ, estart in *.
rewrite <- (edenot_agree b E E' n (conj Hv Hb) H2), <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1).
destruct Hk1 as [A B]. split; [|exact B].
unfold flat, estart in *. rewrite <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1). exact A.
+
apply andb_prop in HK as [H1 H2]. unfold elenZ, estart in *.
rewrite <- (edenot_agree b E E' n (conj Hv Hb) H2), <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1).
destruct Hk1 as [A B]. split; [|exact B].
unfold flat, estart in *. rewrite <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1). exact A.
Qed.
Lemma vals_app_agree : ltac2:(TCodec.tc2 tcn__AxSymRun3 "L'8'U2yR0%211%411'9y8%611%811p041&RH&7r3%22:1(Q<&S0%114r1%4221&3r2%23B91%711%9216%>3;61pWH@1pWLF1pZBG1").
Proof.
intros vals extra ebs. split; [|reflexivity]. intros n Hn. cbn [ev]. unfold vals_ev.
rewrite app_nth1 by exact Hn. reflexivity.
Qed.
Section Run.
Variable segs : list Segment.
Lemma st_ok_entry : ltac2:(TCodec.tc2 tcn__AxSymRun3 "QJ'QJ'U2yR0%211'<y8%511%311p051'H'8'QK%211'QO%411'9&Q7y5%221?&REr8r4r1%43321&RBvTLr9%342176&RGvSOr:(QEr7r6(;'R8%211r5(0'R6%211%:69854D1&S3r3&U1%12Q;=%45A31DJ%C7BFAEK61p0E1p0J1pY>Q01pY0Q41pX>Q61pYNQ91pY4Q=1pYBQ?1pWBQ@1pQDQI1").
Proof.
intros E base rom pc sr kn nx regs HR HK. exists regs. cbn [s_pc s_log s_regs s_know mem_denot].
split; [reflexivity|]. split; [exact HR|]. split; [exact I | exact HK].
Qed.
Theorem run_sound : ltac2:(TCodec.tc2 tcn__AxSymRun3 "S<'9'8'H%211'R7'QK%511'QO%711'R>'R9%:11'QJ'U2yR0%211'<y8%511%311p051&Q7y5%2218'B'>%12A?%221G&R<vTLr>(?r=r<(QEr;r:(;'R8%211r9r8(0'R6%211%;6:96541%91Q4%C7BA@?>21(=r7r6%34Q:Q821r5%54KQA21%N3K71&REr2%235F1&RB%14N97H&RF%14Q0;<E'C'A&R5%11Q0r1%<3K21&RC&R2%11Q5%32O1'S1&S3vSO&U1r@%22QO1%554L1Q5M&R4%11Q?%62R31&RD%13Q;Q:=%;5:B31Q3%=3QH71%G2?1%H2D1qRFR11%K2R21p0M1p0Q01p0Q31p0Q71pY>R71pYBR;1pWBR<1pQDRE1pYFRN1pYHRH1pZ0RK1pY0S51pX>RN1pYNS11pY4S61pYDS51pZ:S71pWNS;1").
Proof.
intros fuel stops scr pc sr kn nx ss' scs scr' E base rom regs Hex HR HK Hsc.
eapply sym_exec_ex; [exact Hex | exact Hsc | apply st_ok_entry; assumption].
Qed.
Lemma eagree_env_agree : ltac2:(TCodec.tc2 tcn__AxSymRun3 ">'9'QJ&D&R?r3r2r1%43321&RH%13543%8231pQF:1pQD;1pW@=1").
Proof. intros b E E'. unfold eagree, env_agree. tauto. Qed.
Lemma st_okX_entry : ltac2:(TCodec.tc2 tcn__AxSymRun3 "R<'QJ'U2yR0%211'<y8%511%311p051'H'8'QK%211'QO%411'9&Q7y5%221?&REr8r4r1%43321&RBvTLr9%342176'B'4&RNr6%22;1(?%63521&RJr5%2216%:3915&R?r7r=%3321D&RGvSOr2r<(QEr;r:(;'R8%211(0'R6%211%96874NQ41&S3&U1%12QI;%35@D1C>%B7AQ4@D?51p0D1pQFQO1p0J1p0O1p0Q71p0Q<1pY>QB1pY0QF1pX>QH1pYNQK1pY4QO1pYBR11pWBR21pQDR;1").
Proof.
intros E base rom pc sr kn nx regs HR HK Hsr Hkn E' Ha. apply eagree_env_agree in Ha.
apply st_ok_entry.
- eapply regs_ok_agree; [exact Ha | exact Hsr | exact HR].
- eapply know_ok_agree; [exact Ha | exact Hkn | exact HK].
Qed.
Theorem runTX_sound : ltac2:(TCodec.tc2 tcn__AxSymRun3 "T6&QM'9'8'H%211'QK%411'QO%611'QJ'U2yR0%211'<y8%511%311p051&Q7y5%2218&QNvTLr<%3221&REr5r8r2%43321&RBr6%24:165'B'4&RNr:%22:1(?%63521&RJr9%2216%:3915'R>&R=rAr@r?r>(QEr=(;'R8%211r;(0'R6%211%968Q454G1%?7Q6>=<F;1'C'A&RH%13=Q9Q4'F&R3r3%211%42B1&R5%114r1%Q@3Q=21&RC&R2%119%32QA1&R1%11<%QB4QJQDI1'S1&S3vSO&U1%12R:Q6%453Q=1OQB&R4%11E%52R>1&RD%13QOQ4?%:59D31QH%<3R771r4%M11%Q131MH&RG%;1R8%?2RH1%I1R:%;37QB1%D5CQ331R?%67DRAR;QDR@R=1p081pQHS01%Q<2=1%Q=2K1%Q>2O1%Q?2Q41%Q@2Q91%QA2Q?1qRFRL1%QD2RM1qQFS91%QF2S:1tZ0R8QH1p0R:1p0R?1p0RG1p0RK1p0S11pY>S61pYBS:1pWBS;1pQDSD1pY0SM1pX>SG1pYNSJ1pY4SN1pZ:SN1pWNT21pQJT31pZ<T51").
Proof.
intros t K fuel stops pc sr kn nx E base rom regs Ht HR HK Hsr Hkn.
destruct (sym_execTX_ex segs t K fuel true stops (SS pc sr [] kn nx) E base rom _ Ht
(st_okX_entry E base rom pc sr kn nx regs HR HK Hsr Hkn)) as (E' & R & Ha & Hle & HR' & Hlf & HK' & Hms & HALL).
exists E', R. split; [apply eagree_env_agree; exact Ha|]. split; [exact Hle|].
split; [exact HR'|]. split; [exact Hlf|]. split; [exact HK'|]. split; [exact Hms|].
intros E'' Ha''. apply HALL. apply eagree_env_agree. exact Ha''.
Qed.
Theorem carry_after : ltac2:(TCodec.tc2 tcn__AxSymRun3 "QM'QJ'U2yR0%211'<y8%511%311p051'8'R8%211'QO%411'4%611'R9%811'B'>%1273%2216&QGr6r5r4%43321(=r3r2%34A=21r1%54<A21%?3<71&RCr9r7%3221&RBvTLr:%342165&RFr;%24541Dr<&RD%13247%:4931<p051p091p0>1p0C1pX6Q61pYHQ51pX@Q:1pX4Q91pX>Q<1pXFQ?1pWBQC1pQDQL1").
Proof. intros. eapply carry_sound; eauto. Qed.
Lemma reg_val : ltac2:(TCodec.tc2 tcn__AxSymRun3 "N'QJ'8'QK%211&Q7y5'U2yR0%211%5241%415&REr4r3r2%43321'B&S2%1254&QIr5&R:%12:8%4231%83@61p0:1pY8@1pRFB1pYNI1pQDM1").
Proof. intros E sr R r HR. apply HR. Qed.
Lemma regs_ok_set : ltac2:(TCodec.tc2 tcn__AxSymRun3 "Q?'QJ'8'QK%211&Q7y5'U2yR0%211%5241%415&REr6r5r4%43321&E'B(U0z(@%33@21%53<81%711&QIr8r3%3221%;3D1>r9&R;&R0%11D%3381C&S5r7%231HG%J3841p0:1p0@1p0I1pWFQ71pZ@Q21pY:Q11pRFQ31pYNQ:1pQDQ>1").
Proof.
intros E sr R rd v e HR Hrd He.
pose proof (regs_ok_upd E sr R rd v e HR He) as H.
assert (Hb : bv_eqb rd 0 = false).
{ unfold bv_eqb. apply Z.eqb_neq. intros Hc. apply Hrd. apply bv_eq. exact Hc. }
rewrite Hb in H. exact H.
Qed.
End Run.
Definition sr_init : list expr :=
[ELit 0; ELit 0; EVar 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0;
ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0;
ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0;
ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0].
Lemma regs_ok_init : ltac2:(TCodec.tc2 tcn__AxSymRun3 "Q8'U2yR0%211'8%112'9y8%711%511p041&RE(Q<&S0(5r3r2%33>21%511r1%8221&RM&S5&Q8y5%221F(U0+:(@%33521&U1z%22N1%;3841+2%93;17%>331E%J3A@1pWHL1pY@Q21pYLQ51").
Proof.
intros sp rest ebs r.
unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
- assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. reflexivity.
- pose proof (ridx_range r) as Hlt.
rewrite <- (ridx_roundtrip r). rewrite <- (ridx_roundtrip r) in Hr0.
set (n := ridx r) in *. clearbody n.
do 32 (destruct n as [|n]; [vm_compute in Hr0 |- *; first [discriminate | reflexivity] |]).
exfalso. lia.
Qed.
Definition stk_ok (segs : list Segment) (mem : word -> option byte) (sp : word) (K : Z) : Prop :=
forall (a : word) (n : nat),
(bv_unsigned sp - K <= bv_unsigned a)%Z ->
(bv_unsigned a + Z.of_nat n <= bv_unsigned sp)%Z ->
store_ok segs mem a n = true.
Lemma stk_ok_vaddi : ltac2:(TCodec.tc2 tcn__AxSymRun3 "QE'8'N%211'U2yR0%211'<y8%511%311p051'H'9&ROr6r5r4r3%544321&S;&U3%12A6%3261&SA%119%6219&S9&S@%11<%32>1z%<221'B'4&Or:r9&S6r8%221I%64541I(?%:3921p0<1p0C1p0G1p0L1pXNQ31pY2Q51pQJQ61pYLQ=1pXJQ91pYJQB1").
Proof.
intros segs mem sp K off n Hs HK H1 H2. pose proof (u64_range sp).
apply Hs; unfold v_addi; rewrite u_small by lia; lia.
Qed.
Lemma stk_ok_lit : ltac2:(TCodec.tc2 tcn__AxSymRun3 "QE'8'N%211'U2yR0%211'<y8%511%311p051'H'9&ROr6r5r4r3%544321&S;&SC&U3%12B7%3217%5217&S9&S@%11:%32<1%82I?%;221z%=21A'B'4&Or:r9&U1%12Q3I%54431I(?%93821p0;1p0>1p0E1p0L1pXNQ31pZHQ51pQJQ61pYLQ=1pXJQ91pYJQB1").
Proof.
intros segs mem sp K z n Hs H1 H2 H3. pose proof (u64_range sp).
apply Hs; rewrite u_small by lia; lia.
Qed.
Lemma stk_ok_grows : ltac2:(TCodec.tc2 tcn__AxSymRun3 "N'8'N%211'U2yR0%211'<y8%511%311p051'H&ROr5r4r2r1%544321&S8%1265r7r3%:42981p041p071pQJ>1pYLE1pXLA1pXJB1pYJK1").
Proof.
intros segs mem mem' sp K Hs Hg a n H1 H2. eapply store_ok_mono; [exact Hg | apply Hs; assumption].
Qed.
Lemma stk_ok_mem_denot : ltac2:(TCodec.tc2 tcn__AxSymRun3 "Q2'8'N%211'QJ'U2yR0%211'<y8%511%311p051'R8%=11'H&ROr6r4r2r1%544321r7&RDr5%23817r3%;45218p071pQJ>1pYLG1pXFA1pXJD1pQDM1pYJO1").
Proof. intros. eapply stk_ok_grows; [eassumption | apply mem_denot_grows]. Qed.
Lemma stk_ok_init : ltac2:(TCodec.tc2 tcn__AxSymRun3 "Q1'8'N%211'M'U2yR0%211y8%411%911%:11'Q1&ROr8&S7r7r6r5r4r3r2r1%877654321&Q2%<4;281pY<>1pX8D1pZ>E1pWJB1pW>C1pYLH1pY6L1pYJN1").
Proof.
intros segs ph sp argv envp uid hw rdraw a n H1 H2.
apply store_ok_wrap_window; assumption.
Qed.
Lemma kwr_of_stk_ok : ltac2:(TCodec.tc2 tcn__AxSymRun3 "QG'8'N%211'QJ'U2yR0%211'<y8%511%311p051'QK'H'B&QIr5r3%3221r2%63>21&ROr7%241764'A&S;z%221:&U3r4%22I1%62>1%8251&RAr9r8(QB(QDr6&SA%11;%4231(Q;%11>%8231%<4;:G1p0>1p0H1p0L1pQJQ41pYLQ<1pWFQ71pXJQ91pQDQB1pYJQD1").
Proof.
intros segs E mem e sp K He Hs HK. cbn [kentry_ok]. unfold flat, estart, elenZ. cbn [a_base a_off edenot]. rewrite He.
pose proof (u64_range sp). rewrite u_small by lia. split; [lia|].
intros d m Hd Hm. apply Hs; rewrite u_small by lia; lia.
Qed.
Lemma kword_intro : ltac2:(TCodec.tc2 tcn__AxSymRun3 "RK'8'N%211'QJ'U2yR0%211'<y8%511%311p051'QK'H'9'B&QIr8r6%3221r5%63?21r9r3%8221r2%;3D21'Fu1%2219u8%42=1&S;z&S9&U3%12O>%321D%6251r:%52Q31%721C&S@%11J%:231&SB+2+R0%3221%A251%QB1Q9%Q<11&S4r?r=&U1r;%F2QD1%H21C%42QF1%84761Q6(2&Q0r7%22Q:1%42?1%QC3?61&RAr@r>(QA(QD%12B@%331Q2QC%746E51p091p0K1p0Q71p0Q?1p0QB1p0QF1p0QL1pZFR<1pZ@R71pZDR61pY2R81pW<R@1pWFR;1pXJR=1pQDRF1pYJRH1").
Proof.
intros segs E mem e a off w v x He Hv Hw1 Hw H1 H2 Hr. cbn [kentry_ok]. unfold flat, estart, adenot, v_addi.
cbn [a_base a_off]. rewrite He, Hv. split; [exact Hw|]. split; [lia | exact Hr].
Qed.
Lemma krange_intro : ltac2:(TCodec.tc2 tcn__AxSymRun3 "Q9'8'N%211'QJ'U2yR0%211'<y8%511%311p051'QK'H'A&S;r2&U3&QIr5r3%3221%52A1%8271r1%:231%<231&RAr7r6(Q@r4%231<@%6454>1p081pX2F1pXDG1pWFI1pXJK1pQDQ41pYJQ61").
Proof. intros. cbn [kentry_ok]. lia. Qed.
Lemma kalign_intro : ltac2:(TCodec.tc2 tcn__AxSymRun3 "Q;'8'N%211'QJ'U2yR0%211'<y8%511%311p051'QK'H&S<zr1%3221'B&S>&U3&QIr5r3%3221%52D1r2%8221%:3?1=&RAr7r6(Q=r4%221;%6454=1p081p0D1pXHI1pWFK1pXJM1pQDQ61pYJQ81").
Proof. intros. cbn [kentry_ok]. auto. Qed.
Lemma kimg_intro : ltac2:(TCodec.tc2 tcn__AxSymRun3 "QF'8'N%211'QJ'U2yR0%211'<y8%511%311pZF51'H&S;zr2%3221&SB+2+R0%3221%8261'Ar5r1%<221&S<r4%2241%7241'Br7&U1%12LB%311(0%11K%73K31p091pX:K1&RAr8r6(Q?%12EA%544>31p071p0J1p0Q01pX2Q51pXDQ61pXJQ81pQDQA1pYJQC1").
Proof. intros. cbn [kentry_ok]. auto. Qed.
Lemma kzero_intro : ltac2:(TCodec.tc2 tcn__AxSymRun3 "RH'8'N%211'QJ'U2yR0%211'<y8%511%311pZF51'QK'H'B&QIr7r5%3221r4%63>21&U3r8r3%9221%42D1r2%=3>21&S;z&S9r6%;2K1%321@%6251&S<%127A%@2Q0?%821F%921F&SB+2+R0%3221%@251'Ar1%C2B1%=22Q0%4221r=&U1r;%Q02Q@1r:%I221%J21N%62QD1%811(2%92QDO%22QD1%Q@3QD41p0>1pX:QC1&RAr>r<(QC(QDr9%22C1%421QB%847G61p0:1p0O1p0Q81p0Q;1p0QC1p0QK1pXBR31pXNR51pY2R51pW<R=1pWFR81pXJR:1pQDRC1pYJRE1").
Proof.
intros segs E mem e a off n len He Hn H1 H2 H3 Hz. cbn [kentry_ok]. unfold flat, elenZ, estart.
cbn [a_base a_off]. rewrite He, Hn. split; [lia | exact Hz].
Qed.
Lemma kblob_intro : ltac2:(TCodec.tc2 tcn__AxSymRun3 "S>'8'N%211'QJ'U2yR0%211'<y8%511%311pZF51'QK'H'9%?16'B&QIr8r6%3221r5%63@21&QHr9r3%3221r2%<3=21&U3r:%>21:%32K1&S@&7%12J:%311%E3H51&S;z&S9%<2Q4Gr7%3221%6251&S<%A2Q9F%721M&SB+2+R0%3221%7251%H2Q@G%>21N%E2Q>Q4%G11%A231%D217'Ar1%G2F1%L2QEQ<%N11%C241%6241r?&U1r=%Q82R01r<%O221%Q021Q=%62R41%811(2&G&SD%11QC%<2R7Q8%44R72QH1%62R81%R23R881p0B1pX:R71&RAr@r>(Q>(QDr;%22G1%431QNR4%847K61p0:1p0Q51p0Q<1p0QE1p0QM1p0R71p0R>1pWDRF1pX<RH1pXNRK1pY2RK1pW<S31pWFRN1pXJS01pQDS91pYJS;1").
Proof.
intros segs E mem e a off n k bs He Hb Hn H1 H1' H2 Hz. cbn [kentry_ok]. unfold flat, elenZ, estart.
cbn [a_base a_off]. rewrite He, Hn, Hb. split; [lia|]. split; [reflexivity | exact Hz].
Qed.
Lemma wrap_mem_none_low : ltac2:(TCodec.tc2 tcn__AxSymRun3 "QC'M'U2yR0%211'8y8%511%311%411'Q1'H&S;zr1%3221&S<r2&SC&U3r8%22B1&Q2%5221%8271'B'<%11D&S7r:r9r7r6r5r4&U1r3%22Q21%:898B76541(0%11Q1%@3>31p0B1p0L1pX:Q11pY<Q31pX8Q:1pZ>Q;1pWJQ71pW>Q81pYLQ>1pY6QB1").
Proof.
intros ph sp argv envp uid hw rdraw i H0 Hi. unfold wrap_mem.
pose proof (u64_range sp) as Hsp.
assert (Hu : bv_unsigned (Z_to_bv 64 i) = i) by (apply u_small; unfold stack_max_size in Hi; lia).
unfold stack_to_mem. rewrite Hu.
replace (Z.leb (bv_unsigned sp) i) with false by (symmetry; apply Z.leb_gt; unfold stack_max_size in Hi; lia).
replace (Z.leb (bv_unsigned sp - stack_max_size) i) with false by (symmetry; apply Z.leb_gt; lia).
reflexivity.
Qed.
Lemma ext_val_zx_id : ltac2:(TCodec.tc2 tcn__AxSymRun3 "L'9'U2yR0%211&S<&U3r1%2251&SB+2&S?+8&S@r2%211%5241%8271%=2:1'B&QL(6(1r3%44321:%63E1;p081pZ@G1pXNK1").
Proof.
intros n v Hv. unfold ext_val, ext_Z. pose proof (u64_range v).
change (2 ^ (8 * Z.of_nat 0))%Z with 1%Z. rewrite Z.div_1_r, Z.mod_small by lia.
apply Z_to_bv_bv_unsigned.
Qed.
Lemma ext_val_sx_id : ltac2:(TCodec.tc2 tcn__AxSymRun3 "Q3'9'U2yR0%211'Fu1r2%3221&S<&U3%1284&SB+2&SC&S?+8&S@r3%211%5241+1%8221%;2:1%?2=1'B&QL(?(1r4%44321<%63K1=p081p0I1pZ@N1pXNQ21").
Proof.
intros n v Hn Hv. unfold ext_val, ext_Z. pose proof (u64_range v).
assert (Hp : (2 ^ (8 * Z.of_nat n - 1) * 2 = 2 ^ (8 * Z.of_nat n))%Z).
{ rewrite Z.mul_comm, <- Z.pow_succ_r by lia. f_equal. lia. }
change (2 ^ (8 * Z.of_nat 0))%Z with 1%Z. rewrite Z.div_1_r, Z.mod_small by lia.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
replace (Z.of_N (8 * N.of_nat n)) with (8 * Z.of_nat n)%Z by lia.
rewrite <- Hp. rewrite Z.div_mul by lia.
rewrite Z.mod_small by lia. replace (bv_unsigned v + 2 ^ (8 * Z.of_nat n - 1) - 2 ^ (8 * Z.of_nat n - 1))%Z
with (bv_unsigned v) by lia.
apply Z_to_bv_bv_unsigned.
Qed.
Lemma branch_eq_lit : ltac2:(TCodec.tc2 tcn__AxSymRun3 "Q1'U2yR0%211'H'A&S;zr1%3221&S<&SB+2+R0%3221%5271%;271'B'4&Q9(Q3r3&U1r2%22F1%63541&S:&U3%12J7%3216%=3<51p0?1pZHL1pZ@N1").
Proof.
intros v z Hz. cbn [branch_taken]. unfold bv_eqb. rewrite u_small by lia. reflexivity.
Qed.
Lemma branch_ne_lit : ltac2:(TCodec.tc2 tcn__AxSymRun3 "Q3'U2yR0%211'H'A&S;zr1%3221&S<&SB+2+R0%3221%5271%;271'B'4&Q9(Q6r3&U1r2%22F1%63541&:&S:&U3%12K8%3217%511%?3>71p0A1pZHN1pZ@Q01").
Proof.
intros v z Hz. cbn [branch_taken]. unfold bv_eqb. rewrite u_small by lia. reflexivity.
Qed.
Lemma branch_ltu_lit_r : ltac2:(TCodec.tc2 tcn__AxSymRun3 "Q1'U2yR0%211'H'A&S;zr1%3221&S<&SB+2+R0%3221%5271%;271'B'4&Q9(Q5r3&U1r2%22F1%63541&S=&U3%12J7%3216%=3<51p0?1pZHL1pZ@N1").
Proof.
intros v z Hz. cbn [branch_taken]. unfold bv_ltu. rewrite u_small by lia. reflexivity.
Qed.
Lemma branch_ltu_lit_l : ltac2:(TCodec.tc2 tcn__AxSymRun3 "Q1'U2yR0%211'H'A&S;zr1%3221&S<&SB+2+R0%3221%5271%;271'B'4&Q9(Q5&U1r2%22E1r3%63521&S=&U3%12J4%3271%=3<51p0?1pZHL1pZ@N1").
Proof.
intros v z Hz. cbn [branch_taken]. unfold bv_ltu. rewrite u_small by lia. reflexivity.
Qed.
Lemma branch_geu_lit_r : ltac2:(TCodec.tc2 tcn__AxSymRun3 "Q3'U2yR0%211'H'A&S;zr1%3221&S<&SB+2+R0%3221%5271%;271'B'4&Q9(Q4r3&U1r2%22F1%63541&:&S=&U3%12K8%3217%511%?3>71p0A1pZHN1pZ@Q01").
Proof.
intros v z Hz. cbn [branch_taken]. unfold bv_ltu. rewrite u_small by lia. reflexivity.
Qed.
Lemma branch_geu_lit_l : ltac2:(TCodec.tc2 tcn__AxSymRun3 "Q3'U2yR0%211'H'A&S;zr1%3221&S<&SB+2+R0%3221%5271%;271'B'4&Q9(Q4&U1r2%22E1r3%63521&:&S=&U3%12K5%3281%511%?3>71p0A1pZHN1pZ@Q01").
Proof.
intros v z Hz. cbn [branch_taken]. unfold bv_ltu. rewrite u_small by lia. reflexivity.
Qed.
End FPX_1.
Ltac split_scs :=
lazymatch goal with
| |- scs_denot _ _ _ [] => constructor
| |- scs_denot _ _ _ (_ :: _) => constructor; [| split_scs]
| |- Forall _ [] => constructor
| |- Forall _ (_ :: _) => constructor; [| split_scs]
end.
Ltac ground_mod :=
repeat match goal with
| |- context [ (?a mod ?b)%Z ] =>
lazymatch a with
| context [bv_unsigned _] => fail
| _ => lazymatch b with
| context [bv_unsigned _] => fail
| _ => let v := eval vm_compute in (a mod b)%Z in change ((a mod b)%Z) with v
end
end
end.
Ltac sc_unfold :=
unfold sc_denot, flat, estart, elenZ, adenot;
cbn [a_base a_off edenot ev eb vals_ev nth];
rewrite ?Z_to_bv_unsigned, ?bv_wrap64_mod; ground_mod.
Ltac lit_u :=
repeat match goal with
| |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
lazymatch z with
| context [bv_unsigned _] => fail
| _ => rewrite (u_small z) by (cbn; lia)
end
end.
Ltac sc_store :=
match goal with
| Hs : stk_ok _ _ _ _ |- store_ok _ _ (v_addi _ _) _ = true =>
apply (stk_ok_vaddi _ _ _ _ _ _ Hs); lia
| Hs : stk_ok _ _ _ _ |- store_ok _ _ (Z_to_bv 64 _) _ = true =>
apply (stk_ok_lit _ _ _ _ _ _ Hs); lia
end.
Ltac sc_auto extra :=
sc_unfold;
first [ lia
| sc_store
| extra
| match goal with |- _ /\ _ => repeat split; first [lia | sc_store | extra] end
| idtac ].
Ltac sym_run_tac segs fuel stops scr nx HR HK R' HR' Hlf Hms extra :=
lazymatch type of HR with
| regs_ok ?E ?sr ?regs =>
lazymatch type of HK with
| know_ok _ _ ?base ?kn =>
lazymatch goal with
| |- context [mkst regs (Z_to_bv 64 ?pc) base ?rom] =>
let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr [] kn nx) []) in
lazymatch r with
| (?ss', ?scs, ?scr') =>
let Hsc := fresh "Hsc" in
assert (Hsc : scs_denot segs base E scs);
[ split_scs; sc_auto extra
| destruct (run_sound segs fuel stops scr pc sr kn nx ss' scs scr' E base rom regs
(eq_refl _) HR HK Hsc) as (R' & HR' & Hlf & Hms);
clear Hsc ]
end
end
end
end.
