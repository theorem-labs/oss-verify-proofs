(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg DivergeSim SpinAlg SpinAlgX
SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX MemSplit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__SymDriveH4 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "LinuxProcessSemantics.Riscv.Sem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymDriveH4.FPX_2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1O"; "1Some"; "1bool"; "1false"; "1length"; "1list"; "1nat"; "1option"; "1true"; "2I"; "2and"; "2eq"; "2not"; "3Z"; "0E"; "0K"]; ["4Segment"; "5ALU_ADD"; "6sext"; "7alu32"; "7low32"; "0M"; "0M'"; "8wbytes"; "9rdn"; ":mem_grows"; ";kentry_out_b"; ";kn_cut"; ";log_out_b"; ";win_ok"; ";win_out_b"; "<EAluw"]; ["<EExt"; "<ELit"; "<KRange"; "<edenot"; "<env"; "<ev"; "<expr"; "<kentry"; "<sentry"; "=elenZ"; "=kentry_ok"; "=know_ok"; "=mem_denot"; ">nth_error"; "?add"; "?le"]; ["?lt"; "?of_nat"; "?pow"; "0a"; "0b"; "0bs"; "0e"; "0hi"; "0i"; "0ihi"; "0k"; "0kn"; "0lo"; "0log"; "0n"; "0segs"]; ["0spi"; "@BV"; "@Z_to_bv"; "@bv"; "@bv_unsigned"; "0x"; "0y"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}.
Lemma low32_zero_sext : ltac2:(TCodec.tc2 tcn__SymDriveH4 "C';'R3yQ0%211&D&R2yR0z%3221%511&By<(R1(9%23371%>14/021%736?1%B3?91").
Proof. apply bv_eq. reflexivity. Qed.
Lemma edenot_addw0_r : ltac2:(TCodec.tc2 tcn__SymDriveH4 "O'Q4'Q6&Q@&R4yR0&Q3r2r1%3221%6251&QB+2+O%3221%<251';'R3%11=r3(O(A(Q1z%211%534B1%D271%E28D%<3:21p0>1pS8L1pNN1").
Proof.
intros E a Ha. cbn [edenot]. rewrite low32_zero_sext, w_addiw.
change (bv_signed (0 : bv 12)) with 0%Z. apply v_addiw_id. exact Ha.
Qed.
Lemma alu32_add_comm : ltac2:(TCodec.tc2 tcn__SymDriveH4 "='R3yQ0%211';&C(Ar2r1%43321%53423%73821pT>91pT<:1").
Proof.
intros x y. change (x + y = y + x). apply bv_eq.
rewrite !bv_add_unsigned. f_equal. lia.
Qed.
Lemma edenot_addw0_l : ltac2:(TCodec.tc2 tcn__SymDriveH4 "O'Q4'Q6&Q@&R4yR0&Q3r2r1%3221%6251&QB+2+O%3221%<251';'R3%11=r3(O(A(Q1z%211%5341B%D271%E28D%<3:21p0>1pS8L1pNN1").
Proof.
intros E a Ha. cbn [edenot]. rewrite alu32_add_comm.
pose proof (edenot_addw0_r E a Ha) as H. cbn [edenot] in H. exact H.
Qed.
Lemma edenot_exts4 : ltac2:(TCodec.tc2 tcn__SymDriveH4 "N'Q4'Q6&Q@&R4yR0&Q3r2r1%3221%6251&QB+2+O%3221%<251';'R3%11=r3(Q0(8(0u4%44321A%C261%D27C%;3921p0=1pS8K1pNM1").
Proof.
intros E a Ha. cbn [edenot]. apply ext_val_sx_id; [lia|].
change (2 ^ (8 * Z.of_nat 4 - 1))%Z with (2 ^ 31)%Z. exact Ha.
Qed.
Lemma edenot_extu4 : ltac2:(TCodec.tc2 tcn__SymDriveH4 "N'Q4'Q6&Q@&R4yR0&Q3r2r1%3221%6251&QB+2+Q0%3221%<251';'R3%11=r3(Q0(3(0u4%44321A%C261%D27C%;3921p0=1pS8K1pNM1").
Proof.
intros E a Ha. cbn [edenot]. apply ext_val_zx_id.
change (2 ^ (8 * Z.of_nat 4))%Z with (2 ^ 32)%Z. exact Ha.
Qed.
End FPX_1.
Ltac intisms E e Hsmall :=
repeat first [ rewrite (edenot_addw0_r E e Hsmall)
| rewrite (edenot_addw0_l E e Hsmall)
| rewrite (edenot_exts4 E e Hsmall) ].
Section FPX_2. Context {fx : PropExec.FPState}.
Definition win_out_b (spi : nat) (lo hi ihi : Z) (b : expr) (k n : Z) : bool :=
match b with
| EVar i => Nat.eqb i spi && (Z.leb (k + n) lo || Z.leb hi k)
&& Z.leb (- 2 ^ 40) k && Z.leb (k + n) (2 ^ 40) && Z.leb 0 n
| ELit z => Z.eqb z 0 && Z.leb 0 k && Z.leb 0 n && Z.leb (k + n) ihi
| _ => false
end.
Definition win_ok (E : env) (spi : nat) (lo hi ihi : Z) : Prop :=
(2 ^ 41 <= bv_unsigned (ev E spi))%Z /\ (bv_unsigned (ev E spi) + 2 ^ 41 <= 2 ^ 64)%Z
/\ (lo <= hi)%Z /\ (- 2 ^ 40 <= lo)%Z /\ (hi <= 2 ^ 40)%Z
/\ (0 <= ihi)%Z /\ (ihi <= bv_unsigned (ev E spi) + lo)%Z.
Lemma win_out_sound : ltac2:(TCodec.tc2 tcn__SymDriveH4 "RA'Q4'6'='Q6';'2&Nr7r6r5r4r3r2r1%877654321(8%<3;21&Mr9r8%3521=<;':&Q?z&Q>&R4yR0&Q3r:%221D%5241%721E%:291&Q@&QB+2+R0%3221%5271%?28L%B213%D231%D2CO'R3%11Br;%C21Q6%F2E1%H21Q7%H2GQ4%L221%K23Q9%C231%Q0231&<&Q5r<%221<%Q12Q01%Q321O%Q32Q2Q@%Q7221%Q624Q<%N231%Q;231%;11p0=1pT<G1%Q?2J1%Q@2L1%QA2Q61p0QC1p0QH1pSNR71pSFR81pS:R81pSDR:1pS@R;1pSJR<1pT2R>1pNR@1").
Proof.
intros E spi lo hi ihi b k n Hb (W1 & W2 & W3 & W4 & W5 & W6 & W7).
destruct b as [z|i| | | | | |]; cbn [win_out_b] in Hb; try discriminate.
- repeat (apply andb_prop in Hb; destruct Hb as [Hb ?]).
apply Z.eqb_eq in Hb. subst z.
repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H end.
cbn [edenot]. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
repeat split; try lia.
- repeat (apply andb_prop in Hb; destruct Hb as [Hb ?]).
apply Nat.eqb_eq in Hb. subst i.
repeat match goal with
| H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H
| H : (_ || _)%bool = true |- _ => apply orb_prop in H
end.
cbn [edenot]. repeat split; try lia.
Qed.
Definition entry_out_b (spi : nat) (lo hi ihi : Z) (e : sentry) : bool :=
match e with
| SE (SA b k) w _ => win_out_b spi lo hi ihi b k (Z.of_nat w)
end.
Definition log_out_b (spi : nat) (lo hi ihi : Z) (log : list sentry) : bool :=
forallb (entry_out_b spi lo hi ihi) log.
Lemma mem_denot_out : ltac2:(TCodec.tc2 tcn__SymDriveH4 "QL'Q4'R3yR0%211'7y8%511%311p051'5'Q8%211'6'=';'2&Lr5r4r3r2r6%6554321(8%:3921&Mr9%2516:98':&Q?&Q>&R4&Q5r:r7%3221%52Q21%721@%72Q4C%:221&Q@%;25H%2241%?241&Q<r;%241=DL%>1M%Q23Q921p061p0G1p0K1pT<QA1pSDQ81pS@Q91pSJQ:1pT2Q<1pSLQ>1pQ<QB1pNQK1").
Proof.
intros E M log spi lo hi ihi x Hb Hw Hx.
induction log as [|[[b k] w v] rest IH]; [reflexivity|].
cbn [log_out_b forallb] in Hb. apply andb_prop in Hb as [He Hrest].
cbn [entry_out_b] in He.
destruct (win_out_sound E spi lo hi ihi b k (Z.of_nat w) He Hw) as (A & B & C & D).
cbn [mem_denot]. rewrite wbytes_outside.
- apply IH. exact Hrest.
- rewrite length_N_to_le_bytes. unfold adenot, v_addi. cbn [a_base a_off]. rewrite u_small by lia. lia.
- rewrite length_N_to_le_bytes. unfold adenot, v_addi. cbn [a_base a_off]. rewrite u_small by lia.
pose proof (u64_range x).
destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned (edenot E b) + k)) as [L|G]; [left; lia|].
destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned (edenot E b) + k + Z.of_nat w)) as [L2|G2]; [|right; lia].
exfalso. apply (D x); lia.
Qed.
Lemma rdn_mem_denot_out : ltac2:(TCodec.tc2 tcn__SymDriveH4 "R;'5'@%211'Q4'R3yR0%211'7y8%511%311p051'Q8%=11'6'=';'2&Lr6r5r4r3r7%6554321(8%:3921&Mr:%2516:98&Q?&Q>&R4&Q5r;r8%3221%52Q01%721?%72Q2B%:221%92Q4E&QA%11F%=231r<r9%>221%@2Q;1%B21J%D261%QC1Q:%Q=11&Hr>&Q<r=%231<G%5441Q7Q6%645>Q8Q7%Q<3821p0;1p0F1p0Q21p0Q61pSNQC1pS8QL1pSDQD1pS@QE1pSJQF1pT2QH1pSLQJ1pQ<QM1pNR61pT0R81").
Proof.
intros segs E M log spi lo hi ihi a n Hb Hw H1 H2.
destruct Hw as (W1 & W2 & W3 & W4 & W5 & W6 & W7).
apply rdn_agree. intros j Hj. pose proof (u64_range a).
apply (mem_denot_out E M log spi lo hi ihi); [exact Hb | repeat split; assumption |].
rewrite u_small by lia. lia.
Qed.
Definition kentry_out_b (spi : nat) (lo hi ihi : Z) (K : kentry) : bool :=
match K with
| KWord (SA b k) w _ => win_out_b spi lo hi ihi b k (Z.of_nat w)
| KZero (SA b k) (ELit n) => Z.ltb n (2 ^ 64) && win_out_b spi lo hi ihi b k n
| KBlob (SA b k) (ELit n) _ => Z.ltb n (2 ^ 64) && win_out_b spi lo hi ihi b k n
| KImg l h => Z.leb h ihi
| KAlign _ _ => true
| KRange _ _ _ => true
| KDisj _ _ _ _ => true
| KWr _ _ => true
| _ => false
end.
Definition kn_cut (spi : nat) (lo hi ihi : Z) (kn : list kentry) : list kentry :=
List.filter (kentry_out_b spi lo hi ihi) kn.
Lemma elenZ_lit_small : ltac2:(TCodec.tc2 tcn__SymDriveH4 "I'Q4'=':&Q?zr1%3221&Q@&QB+2+R0%3221%5271%;271';&Q9r3(Q1r2%211%5241%73D13p091pSNF1pNH1").
Proof. intros E n Hn. unfold elenZ. cbn [edenot]. apply u_small. lia. Qed.
Lemma kentry_cut_sound : ltac2:(TCodec.tc2 tcn__SymDriveH4 "R='5'@%211'Q4'R3yR0%211'7y8%511%311pT<51'6'='Q7&Mr8r5r4r3r2%6554321&<':&Q?&Q>&R4&Q5r:r7%3221%52J1r6%8221r1%92N1%<231&Q@%=27E%2241%A241%C11';r9%11H%A1I%43Q421p061pT<Q:1&I%127Q2&Q:r<r;%3421JQ4'2&J%15>Q9LIQ8(8%A3421r>r=%;4219Np041p0:1p0?1p0B1p0Q>1pQ0QF1pSDQH1pS@QI1pSJQJ1pT2QL1pQ>QN1pQ<QO1pNR81pT0R:1").
Proof.
intros segs E M M' spi lo hi ihi K Hw Hag Hg HK Hb.
pose proof Hw as Hw'. destruct Hw' as (W1 & W2 & W3 & W4 & W5 & W6 & W7).
destruct K as [[b k] w v|[b k] n|[b k] n bk|l h|e m|e l h|a n|a1 n1 a2 n2]; cbn [kentry_out_b] in Hb;
cbn [kentry_ok] in HK |- *; try exact HK.
-
destruct HK as (Hw8 & Hfl & Hr). split; [exact Hw8|]. split; [exact Hfl|].
destruct (win_out_sound E spi lo hi ihi b k (Z.of_nat w) Hb Hw) as (A & B & C & D).
rewrite <- Hr. apply rdn_agree. intros j Hj. apply Hag.
pose proof (flat_u E _ _ Hfl) as Hu. unfold estart in Hu. cbn [a_base a_off] in Hu.
rewrite Hu. apply D. rewrite u_small by lia. lia.
-
destruct n as [n| | | | | | |]; try discriminate. apply andb_prop in Hb as [Hn Hb]. apply Z.ltb_lt in Hn.
destruct HK as (Hfl & Hz).
assert (Hn0 : (0 <= n)%Z).
{ destruct b as [z|i| | | | | |]; cbn [win_out_b] in Hb; try discriminate;
repeat (apply andb_prop in Hb; destruct Hb as [Hb ?]);
repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H end; lia. }
rewrite elenZ_lit_small in Hfl, Hz |- * by lia.
split; [exact Hfl|]. intros i Hi.
destruct (win_out_sound E spi lo hi ihi b k n Hb Hw) as (A & B & C & D).
rewrite Hag; [apply Hz; exact Hi|]. unfold estart. cbn [a_base a_off].
apply D. rewrite u_small by lia. lia.
-
destruct n as [n| | | | | | |]; try discriminate. apply andb_prop in Hb as [Hn Hb]. apply Z.ltb_lt in Hn.
destruct HK as (Hfl & Hlen & Hz).
assert (Hn0 : (0 <= n)%Z).
{ destruct b as [z|i| | | | | |]; cbn [win_out_b] in Hb; try discriminate;
repeat (apply andb_prop in Hb; destruct Hb as [Hb ?]);
repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H end; lia. }
rewrite elenZ_lit_small in Hfl, Hlen, Hz |- * by lia.
split; [exact Hfl|]. split; [exact Hlen|]. intros i Hi.
destruct (win_out_sound E spi lo hi ihi b k n Hb Hw) as (A & B & C & D).
rewrite Hag; [apply Hz; exact Hi|]. unfold estart. cbn [a_base a_off].
apply D. rewrite u_small by lia. lia.
-
apply Z.leb_le in Hb. destruct HK as (H0 & H64 & Hnone).
split; [exact H0|]. split; [exact H64|]. intros i Hi.
rewrite Hag; [apply Hnone; exact Hi|]. rewrite u_small by lia. lia.
-
destruct HK as [Hfl Hst]. split; [exact Hfl|]. intros d m Hd Hm.
eapply store_ok_mono; [exact Hg|]. apply Hst; assumption.
Qed.
Theorem know_cut_sound : ltac2:(TCodec.tc2 tcn__SymDriveH4 "R9'5'@%211'Q4'R3yR0%211'7y8%511%311pT<51'6'='Q7%?11&Mr8r5r4r3r2%6554321&<':&Q?&Q>&R4&Q5r:r7%3221%52K1r6%8221r1%92O1%<231&Q@%=27E%2241%A241%C11';r9%11H%A1I%43Q521p061pT<Q;1&I%127Q2&Q;r<r;%3421JQ4r=&K%15>Q9LIQ8%7436N1p051p0:1p0=1p0Q91pSHQA1pSDQD1pS@QE1pSJQF1pT2QH1pQ>QJ1pQ<QK1pNR41pT0R61").
Proof.
intros segs E M M' spi lo hi ihi kn Hw Hag Hg HK. unfold know_ok in *.
induction kn as [|K rest IH]; [constructor|].
apply Forall_cons_iff in HK as [HK1 HK2].
change (kn_cut spi lo hi ihi (K :: rest))
with (if kentry_out_b spi lo hi ihi K then K :: kn_cut spi lo hi ihi rest else kn_cut spi lo hi ihi rest).
destruct (kentry_out_b spi lo hi ihi K) eqn:Hb.
- constructor; [|apply IH; exact HK2]. eapply kentry_cut_sound; eauto.
- apply IH. exact HK2.
Qed.
Lemma wbytes_agree_out : ltac2:(TCodec.tc2 tcn__SymDriveH4 "R@'R3yR0%211'7y8%511%311p051'5%114'Q4'6'=&Q?&Q>&R4&Q5r4r3%3221%52C1r2%8221r6%92G1%<231r7%<2J1&QA&4%12I7%311%B251r5%B21A%D2Q21%F21?%H251%F2?5%H2Q61%J21F&QB+2+R0%3221%Q0251&<':r8%Q121G%Q32QA1%Q521Lr1%Q62QD1%Q9231&Q@%Q:26G%2241%;241%=11';&Gr<r;r:%44321Q<%41Q=%73QM21p091pT<R31p0I1p0Q21p0Q?1pS@QM1pSJQN1pT2R01pNR21pS<R41pS8R<1pQ<R81").
Proof.
intros M a bs E spi lo hi H1 H2 H3 x Hx. pose proof (u64_range x).
apply wbytes_outside; [lia|].
destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned a)) as [L|G]; [left; exact L | right].
destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned a + Z.of_nat (length bs))) as [L2|G2]; [|exact G2].
exfalso. apply Hx. lia.
Qed.
Lemma krange_of_know : ltac2:(TCodec.tc2 tcn__SymDriveH4 "QG'5'@%211'Q4'R3yR0%211'7y8%511%311p051'Q7%=11'6'Q6'=&Q;r8r7r6r5%544321';%A1<&Q=%13>65(1(Q2r4r3r2%43321%62E1%;3:81':&Q?&R4&Q3r9%221C%42Q41%62=1%722=%9221p0;1p0H1pS@O1pSJQ01pS>Q21pSBQ41pSHQ61pQ<Q91pNQB1pT0QD1").
Proof.
intros segs E M kn i e lo hi HK Hn.
pose proof (know_nth segs E M kn i _ HK Hn) as H. cbn [kentry_ok] in H. lia.
Qed.
End FPX_2.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
