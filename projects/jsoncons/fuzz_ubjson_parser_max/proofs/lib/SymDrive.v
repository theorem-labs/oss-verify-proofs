(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg DivergeSim SpinAlg SpinAlgX SymExec Frame RefMemcpyLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SymExec2 SymExec2Sound SymRun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__SymDrive () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymDrive.FPX_1.Drive."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymRun."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1O"; "1Some"; "1app"; "1bool"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1true"; "2I"; "2and"]; ["2eq"; "2ex"; "2not"; "3le"; "3lt"; "4nth"; "5Z"; "0E"; "6bytes_le_to_Z"; "7word_to_le_bytes"; "8mkCfg"; "9Model"; "9m_halted"; "9m_vm_lazy"; ":bvmap"; "0M"]; ["0M'"; "0R"; "0R'"; ";getr"; ";mkst"; ";rdn"; ";regupd"; ";v_addi"; "<TSet"; "=srealizes"; ">junk_vals"; ">kblob_find"; ">kread"; ">sr_after_call_j"; "?ELit"; "?Env"]; ["?KBlob"; "?SA"; "?SS"; "?adenot"; "?carry"; "?eb"; "?edenot"; "?env"; "?expr"; "?kentry"; "?ridx"; "?s_log"; "?s_pc"; "?s_regs"; "?scripts"; "?sentry"]; ["?sidecond"; "?sr_upd"; "?sym_exec"; "?sym_state"; "@flat"; "@kentry_ok"; "@know_ok"; "@mem_denot"; "@regs_ok"; "@scs_denot"; "Aexpr_vars_lt"; "Akn_vars_lt"; "Asr_vars_lt"; "Avals_ev"; "BIn"; "Cadd"]; ["Cle"; "Clt"; "Cof_nat"; "Cpow"; "0T"; "0b"; "0bk"; "0bs"; "0e"; "0ebs"; "0fuel"; "0fx"; "0hs2"; "0i"; "0k"; "0kept"]; ["0kn"; "0kn'"; "0len"; "0model"; "0n"; "0nx"; "0pc"; "0rom"; "0scfg"; "0scr"; "0scr'"; "0scs"; "0scs2"; "0segs"; "0sr"; "0ss'"]; ["DBV"; "DZ_to_bv"; "Dbv"; "0stops"; "0v"; "0vals"; "0x"]]).
Section FPX_1. Context {fx : PropExec.FPState}.
Definition blobs_ev (bl : list (list byte)) : nat -> list byte := fun n => nth n bl [].
Section Drive.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.
Theorem rz_run : ltac2:(TCodec.tc2 tcn__SymDrive "TH'8'7'F%211'QN'QH%511'QI%711'R3'R0%:11'4%<11'QG'SByR0%211':y8%511%311p051&Ny5%2218'K&Q8'@'<%12EC%221K&R2vS=rC(=rBrA(QBr@r?(9'QO%211r>r=%8576321%61Q5%@7?>=<;21(;r<r;%34Q;Q921r:%54HQB21%K3H71%K2Q@Q=%L21Q<&QD&QK%11?%D1QA%432F1r9%?4QHQE;1r8%A4:QE21%Q73:51&R8r5%235Q11&R6%14Q797Q3&R9%14Q9;EQ2%24Q:FHN%QJ1QK&L%11=(0%11QO%QE3531%QE2R1R1%RB11&M%11F%Q=14%QK3421&QMrF%211r2%H3QE21rD%G4QMQI31r3&R7rH%Q711%33QOQN1%R83R>51'Q9vS8(J&Q4vRK&SA&QLrI%211%42RN1r4%857Q;21R;%:21R9%=4RA<1R6p0?1p0F1p0I1pR2S01pR6RN1%>2S8<%A5@R71R=R<%C21R7%F4RJE1R6p051p0Q61p0Q=1p0QD1p0QF1p0QI1p0QL1p0R01p0R=1pU:S:1pV8S<1pR4S>1pV@SB1pR0SC1pQ@SL1pUJSN1pVJT11pV4T51pVFT:1pVHT41pW0T71pV<TA1pV2T:1pVNT=1pV>TB1pVDTA1pW8TC1pUFTG1").
Proof.
intros fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R model T
Hex Hc HR HK Hsc Hsc2 Hh Hlazy Hcont.
destruct (run_sound segs fuel stops scr pc sr kn nx ss' scs scr' E M rom R Hex HR HK Hsc)
as (R' & HR' & Hlf & Hms).
eapply srz_msteps; [exact Hh | exact Hlazy | exact Hms |].
apply (Hcont R' _ HR'); [|reflexivity].
eapply carry_after; eassumption.
Qed.
Definition kread (kn : list kentry) (b : expr) (k : Z) (n : nat) : option expr :=
match know_lookup segs kn b k n false [] [] with
| LHit v [] _ => Some v
| _ => None
end.
Lemma kread_sound : ltac2:(TCodec.tc2 tcn__SymDrive "RF'QG'SByR0%211':y8%511%311p051'7'QI%211'QH'F'8&R6vS=r7r6r5%544321'@%B1:&Q<r4r3%348721(2r2%22A1%93841'Cu1%2219u8%42@1&R4r;(QAr8%221G&RB%11H%73631'A%Q41Q7'?%Q;12&Q5r<&QCr=r:r9%@221%5241%84Q871Ar1%O2=1%Q63<31&6%12QG4%Q93Q@1G&SA&H%118%32R01&QF%12AQC%Q@3R231%H281%I2<1qU@K1%M2L1p0O1p0Q81p0Q;1p0Q?1p0QJ1pW:R31pV:R21pUNR41pU<R61pV2R81pR0R<1pQ@RE1").
Proof.
intros E M kn b k n v Hkn Hr Hn1 Hn8 Hfl. unfold kread in Hr.
pose proof (know_lookup_sound segs E M kn b k n false [] [] Hkn Hn1 Hn8) as Hs.
destruct (know_lookup segs kn b k n false [] []) as [v' scs h|scs h|]; try discriminate.
destruct scs; [|discriminate]. injection Hr as ->.
destruct (Hs ltac:(constructor) Hfl) as (bs & A & B & C). exists bs. unfold extz in C. auto.
Qed.
Lemma word_to_le_bytes_of_lez : ltac2:(TCodec.tc2 tcn__SymDrive "M'8'7'SBy8%211%411'@&6r1%2251r2%53;21'Cr3u8%3221&Ir4&SAyR0&H%118%4231%7261%B3C1;p0:1p0?1pU@F1pV:L1").
Proof.
intros n bs Hl Hn. unfold word_to_le_bytes.
pose proof (bytes_le_to_Z_bound bs) as Hb. rewrite Hl in Hb.
assert (Hlt : (2 ^ (8 * Z.of_nat n) <= 2 ^ 64)%Z) by (apply Z.pow_le_mono_r; lia).
rewrite Z_to_bv_unsigned, bv_wrap64_mod, Z.mod_small by lia.
rewrite <- Hl. apply Z_to_le_bytes_lez.
Qed.
Lemma kread_rdn : ltac2:(TCodec.tc2 tcn__SymDrive "R7'QG'SByR0%211':y8%511%311p051'7'QI%211'QH'F'8&R6vS=r7r6r5%544321'@%B1:&Q<r4r3%348721(2r2%22A1%93841'Cu1%2219u8%42@1&R4r;(QAr8%221G&RB%11H%73631%Q31Q6%Q911&Q5&QCr<r9%<21;%4231%64Q4?1Q3&I&QF%127Q5%32Q71%N2=1%Q53=61p0@1p0I1p0L1p0Q01p0Q;1pW:QD1pV:QC1pUNQE1pU<QG1pV2QI1pR0QM1pQ@R61").
Proof.
intros E M kn b k n v Hkn Hr Hn1 Hn8 Hfl.
destruct (kread_sound E M kn b k n v Hkn Hr Hn1 Hn8 Hfl) as (bs & A & B & C).
rewrite A, <- C, word_to_le_bytes_of_lez by assumption. reflexivity.
Qed.
Fixpoint kblob_find (kn : list kentry) (b : expr) (k : Z) : option (expr * nat) :=
match kn with
| [] => None
| KBlob (SA kb kk) len bk :: rest =>
if (expr_eqb b kb && Z.eqb k kk)%bool then Some (len, bk) else kblob_find rest b k
| _ :: rest => kblob_find rest b k
end.
Lemma kblob_find_sound : ltac2:(TCodec.tc2 tcn__SymDrive "QD'QG'SByR0%211':y8%511%311p051'7'QI%211'QH'F'8&R6vS=r7r6r5%544321'@'<%12;9%D11&Q;r4%23981(2(;r3r2%34DB21%52:1%=3:71&R5r9r8(Q@(QA%12FE%331?;%74J651p091p0H1pU>O1pV6Q21pUNQ21pU<Q41pV2Q61pR0Q:1pQ@QC1").
Proof.
intros E M kn b k len bk Hkn. induction kn as [|K rest IH]; cbn [kblob_find]; intros H; [discriminate|].
apply Forall_cons_iff in Hkn as [HK Hrest].
destruct K as [| |[kb kk] len' bk'| | | | |]; try (apply IH; assumption).
destruct (expr_eqb b kb && Z.eqb k kk)%bool eqn:Heq; [|apply IH; assumption].
apply andb_prop in Heq as [H1 H2]. apply expr_eqb_eq in H1. apply Z.eqb_eq in H2. subst.
injection H as <- <-. exact HK.
Qed.
Lemma kblob_rdn : ltac2:(TCodec.tc2 tcn__SymDrive "QL'QG'SByR0%211':y8%511%311p051'7'QI%211'QH'F'8&R6vS=r7r6r5%544321'@'<%12;9%D11&Q;r4%23981(2(;r3r2%34DB21%52:1%=3:71%J1M%Q011&Q5r8&QCr9(QA%12HG%4231&6&QE%126@%32Q91%;4Q0:51%E2>3%M3>21p0A1p0Q01pU>Q71pV6Q:1pUNQ:1pU<Q<1pV2Q>1pR0QB1pQ@QK1").
Proof.
intros E M kn b k len bk Hkn Hf.
pose proof (kblob_find_sound E M kn b k len bk Hkn Hf) as HK. cbn [kentry_ok] in HK.
destruct HK as (Hfl & Hlen & Hb).
apply rdn_pointwise.
- reflexivity.
- rewrite (flat_u E _ _ Hfl). destruct Hfl as (?&?&?&?). lia.
- intros j Hj. rewrite (flat_u E _ _ Hfl). rewrite Hb by lia. rewrite Nat2Z.id. reflexivity.
Qed.
Lemma env_ext_regs : ltac2:(TCodec.tc2 tcn__SymDrive "QC'7'SByR0%211%411'8y8%611%811p041'QH%;11&Ny5%221;'@'4&R<&6r5%22A1r2%5221(=%93821&R8(Q?&R=r6%211r4%5221r3%8321<&3r7(5(9%11Q3%33Q4;1%63Q551%>11%@21G%B31=;p0;1p0E1pR4Q01pVNQ41pUDQ71pW>Q>1pW<Q>1").
Proof. intros. eapply regs_ok_agree; [apply vals_app_agree | eassumption | eassumption]. Qed.
Lemma env_ext_know : ltac2:(TCodec.tc2 tcn__SymDrive "QE'7'SByR0%211%411'8y8%611%811p041':%114p091'QI%>11'@'4&R;&6r5%22A1r1%5221(=%93821&R6vS=(Q?&R=r6%211r4%5221r3r2%:49321&3r7(5(9%11Q5%33Q6<1%63Q751%?11%A21I%D4C1><p0;1p0G1pV2Q21pR0Q51pUDQ91pW>Q@1pW<Q@1").
Proof. intros. eapply know_ok_agree; [apply vals_app_agree | eassumption | eassumption]. Qed.
Lemma vals_ev_last : ltac2:(TCodec.tc2 tcn__SymDrive "E'7'SByR0%211%411'@&R=&3r2(5r1(9%119%43:31%73;61&6%12=8%;231%=3?18pW>@1pW<@1").
Proof. intros. unfold vals_ev. rewrite nth_middle || (rewrite app_nth2, Nat.sub_diag by lia; reflexivity). reflexivity. Qed.
Lemma v_addi_pc4 : ltac2:(TCodec.tc2 tcn__SymDrive "N'F&R@zr1%3221&RA&R?r2+4%3221&RC+2+R0%3221%9251'@'SByR0%211&Q7&SAr3%2251%421?%B23@%5281%;3831p0=1p0H1pV>M1").
Proof. intros pc H0 H1. unfold v_addi. rewrite u_small by lia. reflexivity. Qed.
Lemma regs_set_a0 : ltac2:(TCodec.tc2 tcn__SymDrive "Q8'QG'7'QH%211&Ny5'SByR0%211%5241&R8r5r4r3%43321'@&QFr6r2%3221%53<17r7&R1&QJ(S@+:(>%33F21%511%73<1@&Q6%13D4C%F3;31p0=1p0D1pUBQ11pW:L1pR4L1pVNQ31pQ@Q71").
Proof. intros. apply regs_ok_set; [assumption | discriminate | assumption]. Qed.
Definition junk_vals (R' : bvmap 5 word) : list word :=
map (fun i => getr R' (Z_to_bv 5 (Z.of_nat i))) (seq 0 32).
Definition sr_after_call_j (sr : list expr) (kept : list nat) (jbase : nat) : list expr :=
map (fun i => if existsb (Nat.eqb i) kept then nth i sr (ELit 0) else EVar (jbase + i))
(seq 0 32).
Lemma nth_map_seq_gen : forall {A} (f : nat -> A) len s n d, (n < len)%nat ->
nth n (map f (seq s len)) d = f (s + n)%nat.
Proof.
intros A f len. induction len as [|len IH]; intros s n d H; [lia|].
cbn [seq map]. destruct n as [|n].
- cbn [nth]. rewrite Nat.add_0_r. reflexivity.
- cbn [nth]. rewrite IH by lia. f_equal. lia.
Qed.
Lemma nth_map_seq : forall {A} (f : nat -> A) n len d, (n < len)%nat ->
nth n (map f (seq 0 len)) d = f n.
Proof. intros. rewrite nth_map_seq_gen by assumption. reflexivity. Qed.
Lemma sr_vars_lt_nth : ltac2:(TCodec.tc2 tcn__SymDrive "I'8'7'QH%211'@'4&R<r3r2%3221(=%73621&R:r4&E(Q>z%211%44@:;1%7261%@3?1:p0:1pV:F1pVND1pU<H1").
Proof.
intros b sr. induction sr as [|e t IH]; intros n H; [destruct n; reflexivity|].
cbn [sr_vars_lt] in H. apply andb_prop in H as [He Ht]. destruct n; [exact He | apply IH; exact Ht].
Qed.
Lemma regs_after_call : ltac2:(TCodec.tc2 tcn__SymDrive "R@'7'SByR0%211%411'8y8%611%811p041'QH%;11&Ny5%221;%?1:'@'4&R<&6r6%22B1r4%5221(=%93821&R8(Q?&R=r7%211%421;r5%7321;&R>r1%23O1>'?&Dr2uQ0%3221&Q3&SA&RB%116%32Q11%52K1%62C2%Q13Q>21%=291p0?1pULQ?1&B(1%E3QB1Q1%311&3r:&Q:%11Q8%43QJ31%Q211r9%Q5221&Q=r8%Q@2R09%332Q41%Q;351QAp0>1p0C1p0Q71p0Q@1pV0QK1pR6QM1pR4QN1pVNR21pUDR51pW<R;1").
Proof.
intros vals ebs sr R R' kept Hlt HR Hkept H0 r.
pose proof (ridx_range r) as Hr.
unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
- assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. reflexivity.
- unfold sr_after_call_j. rewrite nth_map_seq by exact Hr.
destruct (existsb (Nat.eqb (ridx r)) kept) eqn:Hex.
+ apply existsb_exists in Hex as (i & Hin & Heqi). apply Nat.eqb_eq in Heqi. subst i.
destruct (Hkept _ Hin) as [_ Hg]. rewrite ridx_roundtrip in Hg. rewrite Hg.
pose proof (HR r) as Hv. unfold sr_get in Hv. rewrite Hr0 in Hv. rewrite Hv.
eapply edenot_agree; [apply vals_app_agree|]. apply sr_vars_lt_nth. exact Hlt.
+ cbn [edenot ev]. unfold vals_ev. rewrite app_nth2 by lia.
replace (length vals + ridx r - length vals)%nat with (ridx r) by lia.
unfold junk_vals. rewrite nth_map_seq by exact Hr. rewrite ridx_roundtrip. reflexivity.
Qed.
End Drive.
End FPX_1.
