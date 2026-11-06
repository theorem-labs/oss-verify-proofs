(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StreamExec FileSim ShapeAlg DivergeSim SpinAlg SpinAlgX StoreOk.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__AgentLib () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AgentLib.FPX_3."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.FileSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "Stdlib.Lists.List."; "Stdlib.NArith.BinNat.N."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0A'"; "0B"; "0B'"; "1None"; "1Some"; "1app"; "1bool"; "1cons"; "1false"; "1fst"; "1length"; "1list"; "1nat"; "1negb"; "1nil"]; ["1option"; "1pair"; "1prod"; "1true"; "2and"; "2eq"; "2ex"; "3N"; "3Z"; "4len_word"; "5Segment"; "6store_ok"; "6wview"; "7SpuriousCfg"; "7config"; "8FdEntry"]; ["8errno_ret"; "8event"; "8fd_insert"; "8fd_lookup"; "8read_bytes_map"; "8readable_bytes"; "8readable_bytes_aux"; "9bv_eqb"; ":zall"; ";mrb"; "<c_eq"; "<c_lts"; "<c_ltu"; "<rdn"; "<v_add"; "<v_addi"]; ["<v_sub"; "=TSet"; "=t_alt2"; "=t_emit"; "=t_eq"; ">srealizes"; "?filter"; "@to_nat"; "Aadd"; "Aeqb"; "Ale"; "Alt"; "Altb"; "Amodulo"; "Aof_N"; "Aof_nat"]; ["Aopp"; "Apow"; "Asub"; "0T"; "0T'"; "0a"; "0b"; "0bs"; "0c"; "0e"; "0e'"; "0f"; "0fd"; "0fds"; "0i"; "0m"]; ["0mem"; "0n"; "0p"; "0r"; "0scfg"; "0segs"; "BZ_to_bv"; "Bbv"; "Bbv_signed"; "Bbv_unsigned"; "0w"; "0x"; "0z"]]).
Section FPX_1. Context {fx : PropExec.FPState}.
Lemma t_emit_app : ltac2:(TCodec.tc2 tcn__AgentLib "B'<'Q1%211&QA&QD&QC&6r3r2%33821r1%6221%7242%8261%:231pT8<1pT>>1pT<?1").
Proof.
intros a b T tr. unfold t_emit. split.
- intros [Hp | (tr' & -> & HT)].
+ apply is_prefix_app_split in Hp as [Hp | (b' & -> & Hp)].
* left. exact Hp.
* right. exists b'. split; [reflexivity | left; exact Hp].
+ right. exists (b ++ tr'). split; [rewrite app_assoc; reflexivity|].
right. exists tr'. auto.
- intros [Hp | (tr' & -> & [Hp | (tr'' & -> & HT)])].
+ left. apply is_prefix_app_r. exact Hp.
+ left. apply is_prefix_app_mono. exact Hp.
+ right. exists tr''. rewrite app_assoc. auto.
Qed.
Lemma t_emit_congr : ltac2:(TCodec.tc2 tcn__AgentLib "B'<'Q1%211&QA&QDr2r1%3221&QCr4r3%3221%4237%9221p071pT:<1pT8=1pTD?1").
Proof.
intros e T T' H tr. unfold t_emit. split.
- intros [Hp | (tr' & -> & HT)]; [left; exact Hp | right; exists tr'; split; [reflexivity | apply H; exact HT]].
- intros [Hp | (tr' & -> & HT)]; [left; exact Hp | right; exists tr'; split; [reflexivity | apply H; exact HT]].
Qed.
Lemma t_alt2_congr : ltac2:(TCodec.tc2 tcn__AgentLib "C&QA&QDr4r3%3221r2%5231&QBr6%2217r5%4218%;231p071p0:1p8?1p6@1p4A1p2B1").
Proof. intros A A' B B' HA HB tr. unfold t_alt2. rewrite (HA tr), (HB tr). reflexivity. Qed.
Lemma t_emit_nil_l : ltac2:(TCodec.tc2 tcn__AgentLib "=&QAr1(?'Q1%211%411&QD&QCr2%2251%4212p061pT8<1").
Proof. exact t_emit_nil_eq. Qed.
Lemma rz_eq : ltac2:(TCodec.tc2 tcn__AgentLib "H'<'J%211'M'N&QA&QDr1r2%3221'QEr6r5r4%443216r7%641543p031p091pT:>1pT8?1pTBA1pU:C1pU<E1").
Proof. intros segs scfg c T T' Heq H. eapply srz_conseq; [exact H | exact Heq]. Qed.
Lemma t_emit_app3 : ltac2:(TCodec.tc2 tcn__AgentLib "F'<'Q1%211&QA&QD&QCr4r3r2r1%5221%6241%7261&6%13=76%23>91%;217%=251pT8?1pTBA1pT>B1pT<C1").
Proof.
intros a b c T. apply t_eq_sym.
eapply t_eq_trans; [apply t_emit_app|].
apply t_emit_congr. apply t_emit_app.
Qed.
Lemma map_app3 {A B} (f : A -> B) (a b c : list A) :
map f (a ++ b ++ c) = map f a ++ map f b ++ map f c.
Proof. rewrite !map_app. reflexivity. Qed.
Lemma readable_bytes_aux_of_rdn : ltac2:(TCodec.tc2 tcn__AgentLib "Q5'<'J%211'RGyR0%211'@y8%511%311p051'=%<14'E%812&Q=r5r4r2r3%544321(5r1%22;1%;3:41&Q6&Q9r6%221<%431:<%A3B1<p071pT@D1pT<L1pU4G1pU2I1pU<Q21").
Proof.
intros segs mem n; induction n as [|n IH]; intros a bs H.
- cbn in H. injection H; intros <-. reflexivity.
- destruct bs as [|b rest].
+ exfalso. pose proof (rdn_length segs mem (S n) a [] H) as HL. cbn in HL. lia.
+ cbn [readable_bytes_aux].
rewrite (mrb_first segs mem a n b rest H).
rewrite (IH (a + 1) rest (rdn_tail segs mem a n b rest H)). reflexivity.
Qed.
Lemma readable_bytes_of_rdn : ltac2:(TCodec.tc2 tcn__AgentLib "QB'<'J%211'RGyR0%211'@y8%511%311p051'=%<14'E%812&Q=r5r4r2r3%544321(5r1%22;1%;3:41&QK&QO%11:&R1+2+R0%3221%7251&Q5&Q9r7r6%3221&RF%=1G%22Q41%834H1%M3N1Gp0;1p0D1pT@Q11pT<Q91pU4Q41pU2Q61pU<Q?1").
Proof.
intros segs mem n a bs H Hn. rewrite readable_bytes_eq. unfold word_to_nat.
rewrite Z_to_bv_small by (unfold bv_modulus; lia). rewrite Nat2Z.id.
apply readable_bytes_aux_of_rdn. exact H.
Qed.
Lemma len_word_of_nat : ltac2:(TCodec.tc2 tcn__AgentLib "C'<'RGy8%211%411'EyR0%611&Ir1%2271&RF&QO&;%12;5%311%52:1%<3:71pT@>1").
Proof. reflexivity. Qed.
Lemma read_bytes_map_of_store_ok : ltac2:(TCodec.tc2 tcn__AgentLib "QF'<'J%211'RGyR0%211'@y8%511%311p051'='E'7&Kr4r3r2r1%544321(C%93821&QK&QO%117&R1+2+R0%3221%7251'F%O1G%J11&Q4&Lr7r6%3221r5&RF%A1I%22Q51%93541(5%12=J%Q13=31qUF?1%A2@1p0C1p0L1pU4Q71pT<Q>1pU2Q:1pU<QC1").
Proof.
intros segs mem a n H Hn. rewrite read_bytes_map_eq. unfold word_to_nat.
rewrite Z_to_bv_small by (unfold bv_modulus; lia). rewrite Nat2Z.id.
apply store_ok_read_aux. exact H.
Qed.
Lemma fd_insert_head_same : ltac2:(TCodec.tc2 tcn__AgentLib "I'<'B'RGyR0%211'O%5221%711'E&Q2(8(Ar3r2%34:921r4%63:21r1%93261%:3472%<3=21pTF@1pTDA1pTJC1pTLA1").
Proof.
intros fds fd e e'. unfold fd_insert. cbn [List.filter fst].
rewrite bv_eqb_refl. cbn [negb]. reflexivity.
Qed.
Lemma filter_fd_id : ltac2:(TCodec.tc2 tcn__AgentLib "Q0'<'B'RGyR0%211'O%5221%711'E'@%115&Q3r2r1%3221(4%11;%93731&QF&>&Q7&:%13BA9r3%43E21%611qU6D1%93E14%D3E15p0<1pTJJ1pTLH1").
Proof.
induction fds as [|[k e] r IH]; intros fd H; [reflexivity|].
cbn [List.filter fst fd_lookup] in *.
destruct (bv_eqb k fd) eqn:E; [discriminate|]. cbn [negb].
rewrite (IH fd H). reflexivity.
Qed.
Lemma fd_insert_fresh_eq : ltac2:(TCodec.tc2 tcn__AgentLib "N'<'B'RGyR0%211'O%5221%711'E'@%115&Q3r3r2%3221(4%11;%93731&Q2r4%23187(8(A%14CB;:%33B15%A3B51p091pTDF1pTJH1pTLF1").
Proof. intros fds fd e H. unfold fd_insert. rewrite (filter_fd_id fds fd H). reflexivity. Qed.
Lemma u64_lit : ltac2:(TCodec.tc2 tcn__AgentLib "G'H'D&QJzr1%3221&QK&R1+2+R0%3221%5271%;271'E&RIyR0&RFr2%2231%5241%73D13p091pUJF1").
Proof. intros z Hz. apply Z_to_bv_small. unfold bv_modulus. lia. Qed.
Lemma v_add_lit : ltac2:(TCodec.tc2 tcn__AgentLib "Q1'H&QJzr2%3221&QK&QHr4r3%3221&R1+2+R0%3221%9251'E'RGyR0%211&Q>&RFr5%2251%326@%5221%C24B%6291%<3931p0>1p0I1p0J1pT>O1pT<Q01").
Proof.
intros a b Ha Hb Hab. unfold v_add. rewrite !u64_lit by lia. reflexivity.
Qed.
Lemma v_sub_lit : ltac2:(TCodec.tc2 tcn__AgentLib "Q2'H'D&QJzr1%3221r2%5231%7231&QKr3&R1+2+R0%3221%6251'E'RGyR0%211&Q@&RFr4%2251%326>%5221&R2%125A%72:1%=3:41p0?1p0G1pT>Q01pT<Q11").
Proof.
intros a b Hab Ha. unfold v_sub. rewrite !u64_lit by lia. reflexivity.
Qed.
Lemma v_addi_lit : ltac2:(TCodec.tc2 tcn__AgentLib "M'H'D&QJzr2%3221&QK&R1+2+R0%3221%5271%;271'E'RGyR0%211&Q?&RFr3%2251%421A&QH%124C%6291%<3941p0>1pTNK1pT<L1").
Proof. intros a i Ha. unfold v_addi. rewrite u64_lit by lia. reflexivity. Qed.
Lemma Z_to_bv_64_mod : ltac2:(TCodec.tc2 tcn__AgentLib "A'H'E'RGyR0%211&RFr1%2241&QM&R1+2+R0%3221%5271%92;1%>3;81pUJ@1").
Proof.
intro z. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma c_ltu_lit : ltac2:(TCodec.tc2 tcn__AgentLib "N'H'D&QJzr2%3221&QK&R1+2+R0%3221%5271%;271'E'7&Q<&RFyR0r4%3221r3%5241%7231&QL%1264%<3;31p0>1p0?1pT>L1pT<M1").
Proof. intros a b Ha Hb. unfold c_ltu, bv_ltu. rewrite !u64_lit by lia. reflexivity. Qed.
Lemma c_eq_lit : ltac2:(TCodec.tc2 tcn__AgentLib "N'H'D&QJzr2%3221&QK&R1+2+R0%3221%5271%;271'E'7&Q:&RFyR0r4%3221r3%5241%7231&QI%1264%<3;31p0>1p0?1pT>L1pT<M1").
Proof. intros a b Ha Hb. unfold c_eq, bv_eqb. rewrite !u64_lit by lia. reflexivity. Qed.
Lemma bv_signed_small : ltac2:(TCodec.tc2 tcn__AgentLib "G'H'D&QJzr1%3221&QK&R1+2+QO%3221%5271%;271'E&RHyR0&RFr2%2231%5241%73D13p091pUJF1").
Proof.
intros z Hz. rewrite Z_to_bv_signed. unfold bv_swrap.
unfold bv_wrap, bv_half_modulus, bv_modulus.
replace (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z by reflexivity.
replace (2 ^ 64 `div` 2)%Z with (2 ^ 63)%Z by reflexivity.
rewrite Z.mod_small by lia. lia.
Qed.
Lemma bv_signed_neg : ltac2:(TCodec.tc2 tcn__AgentLib "I'H'D&QKzr1%3221&QJ&R1+2+QO%3221%5271%;271'E&RHyR0&RF&R0r2%211%4251%7261%93F13p0;1pTDH1").
Proof.
intros e He. rewrite Z_to_bv_signed. unfold bv_swrap.
unfold bv_wrap, bv_half_modulus, bv_modulus.
replace (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z by reflexivity.
replace (2 ^ 64 `div` 2)%Z with (2 ^ 63)%Z by reflexivity.
rewrite Z.mod_small by lia. lia.
Qed.
Lemma c_lts_zero_nonneg : ltac2:(TCodec.tc2 tcn__AgentLib "J'H'D&QJzr1%3221&QK&R1+2+QO%3221%5271%;271'E'7&Q;&RFyR0r2%3221%423A%6221(9%:3921p0<1pUJI1").
Proof.
intros z Hz. unfold c_lts, bv_lts. rewrite !bv_signed_small by lia. apply Z.ltb_ge. lia.
Qed.
Lemma c_lts_zero_errno : ltac2:(TCodec.tc2 tcn__AgentLib "L'H'D&QKzr1%3221&QJ&R1+2+QO%3221%5271%;271'E'7&Q;&RFyR0&R0r2%211%5241%625C%8221(C%<3;21p0>1pTDK1").
Proof.
intros e He. unfold c_lts, bv_lts. rewrite bv_signed_neg by lia.
rewrite bv_signed_small by lia. apply Z.ltb_lt. lia.
Qed.
Lemma errno_ret_lit : ltac2:(TCodec.tc2 tcn__AgentLib ">'H'E'RGyR0%211&Q0r1%211&RF&R0%114%3281%;3851pTD=1").
Proof. reflexivity. Qed.
End FPX_1.
Ltac show_goal_marker := match goal with |- ?g => idtac "=====GOAL=====" g end.
Section FPX_2. Context {fx : PropExec.FPState}.
Lemma rdn_addr_eq : ltac2:(TCodec.tc2 tcn__AgentLib "Q3'<'J%211'RGyR0%211'@y8%511%311p051'=%<14%711'Er4r3%33<21&Q=r7r6%342165r2%93:21r8%74165:%<3=1:p041p0;1pU8@1pU4C1pT>J1pT<K1pU0G1pU<Q01").
Proof. intros segs m a b n r -> H. exact H. Qed.
End FPX_2.
Ltac rdn_at b :=
apply (rdn_addr_eq _ _ _ b);
[ first [ f_equal; lia
| lazymatch goal with |- ?g => StepTac.check_closed_term g end;
apply bv_eq; vm_compute; reflexivity ]
| ].
Section FPX_3. Context {fx : PropExec.FPState}.
Fixpoint zall (n : nat) (f : Z -> bool) (z : Z) : bool :=
match n with
| O => true
| S n' => if f z then zall n' f (z + 1)%Z else false
end.
Lemma zall_spec : ltac2:(TCodec.tc2 tcn__AgentLib "O'='H'7p021'E&Q8r3r2r1%43321(C%73921'D&QJ%1286&QK&QH&QOr5%211%42>1%62=1%:281%51@%D3F1>p031pUHI1p0@1pUJK1pTHJ1pU4N1").
Proof.
induction n as [|n IH]; intros f z H x Hx; [lia|].
cbn [zall] in H. destruct (f z) eqn:E; [|discriminate].
destruct (Z.eq_dec x z) as [->|Hne]; [exact E|].
apply (IH f (z + 1)%Z H). lia.
Qed.
Lemma zallN_spec : ltac2:(TCodec.tc2 tcn__AgentLib "N'G'H'7p021'E&Q8&QGr2%211r1z%63321(C%93;21'D&QJ%1267&QK&QNr4%211%42<1%8261%41@%D3F1<p031pUHI1p0>1pTHI1pU4M1").
Proof. intros n f H x Hx. apply (zall_spec (N.to_nat n) f 0%Z H). rewrite N_nat_Z. lia. Qed.
End FPX_3.
Ltac rdn_at_hyp Hb :=
lazymatch type of Hb with
| rdn _ _ ?b _ = _ => rdn_at b; exact Hb
end.
