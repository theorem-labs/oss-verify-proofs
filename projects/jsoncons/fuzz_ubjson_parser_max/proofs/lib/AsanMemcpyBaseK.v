(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__AsanMemcpyBaseK () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.Riscv.DecodeC."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanMemcpyBaseK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanMemcpyBaseK.MC."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefMemcpyLib."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1Some"; "1app"; "1bool"; "1cons"; "1false"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1true"; "2and"; "2eq"; "2or"]; ["3sub"; "4le"; "5firstn"; "5skipn"; "6Z"; "7MachineOk"; "7fetch_word"; "7is_ecall"; "7machine_result"; "7machine_state"; "7step"; "7store_ok"; "7word_to_le_bytes"; "8decode_any"; "9SZ1"; "9SZ4"]; ["9Store"; "9instr"; ":bvmap"; "<b_"; "<memk"; "<sb_"; ";asanreflect_fx"; "=wbytes"; ">at_"; "?getr"; "?mkst"; "?rdn"; "?v_addi"; "?v_andi"; "?v_or"; "?v_slli"]; ["?v_srli"; "?v_srliw"; "@LBv"; "@LWv"; "Aloaded_segments"; "Badd"; "Bland"; "Ble"; "Blt"; "Bmodulo"; "Bmul"; "Bof_nat"; "Bpow"; "Bsub"; "0a"; "0b"]; ["0bs"; "0d"; "0dst"; "0imm"; "0j"; "0j1"; "0j2"; "0k"; "0k0"; "0l"; "0m"; "0mem0"; "0n"; "0pc"; "0q"; "0regs"]; ["0rom"; "0rs1"; "0rs2"; "0src"; "CZ_to_bv"; "Cbv"; "Cbv_signed"; "Cbv_unsigned"; "0v"; "0w"; "0x"]]).
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
Abbreviation ASEGS0 := Asan.M.loaded_segments.
Record mcH (mem0 : word -> option byte) (dst src : word) (n : Z) (bs : list byte) : Prop := MCH {
Hn : (0 <= n < 2 ^ 64)%Z;
Hlen : length bs = Z.to_nat n;
Hsrc : rdn ASEGS0 mem0 src (length bs) = Some bs;
Hdst : store_ok ASEGS0 mem0 dst (length bs) = true;
Hdisj : (bv_unsigned dst + n <= bv_unsigned src \/ bv_unsigned src + n <= bv_unsigned dst)%Z;
Hnws : (bv_unsigned src + n < 2 ^ 64)%Z;
Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z }.
Section MC.
Variable mem0 : word -> option byte.
Variables dst src : word.
Variable n : Z.
Variable bs : list byte.
Hypothesis HOK : mcH mem0 dst src n bs.
Let Hn := Hn _ _ _ _ _ HOK.
Let Hlen := Hlen _ _ _ _ _ HOK.
Let Hsrc := Hsrc _ _ _ _ _ HOK.
Let Hdst := Hdst _ _ _ _ _ HOK.
Let Hdisj := Hdisj _ _ _ _ _ HOK.
Let Hnws := Hnws _ _ _ _ _ HOK.
Let Hnwd := Hnwd _ _ _ _ _ HOK.
Definition memk (k : Z) : word -> option byte := wbytes mem0 dst (firstn (Z.to_nat k) bs).
Definition sb_ (j : Z) (m : nat) : list byte := sub bs (Z.to_nat j) m.
Definition b_ (j : Z) : byte := nth (Z.to_nat j) bs (Z_to_bv 8 0).
Lemma lenZ : ltac2:(TCodec.tc2 tcn__AsanMemcpyBaseK "<'>'D&QK&5'REy8%211vR0%5221%711vR<%;3:21").
Proof. rewrite Hlen. lia. Qed.
Lemma memk_0 : ltac2:(TCodec.tc2 tcn__AsanMemcpyBaseK ">'>'REyR0%211'9y8%511%311p051&Q4z%211vR;%=3521").
Proof. reflexivity. Qed.
Lemma memk_n : ltac2:(TCodec.tc2 tcn__AsanMemcpyBaseK "B'>'REyR0%211'9y8%511%311p051&Q4vR<%211&Q7vR;vR2vR0%43321%A3961").
Proof. unfold memk. rewrite <- Hlen, firstn_all. reflexivity. Qed.
Lemma sb_len : ltac2:(TCodec.tc2 tcn__AsanMemcpyBaseK "K'D'7&QGzr2%3221&QEr3&QK%115%4231vR<%:221'>&5'REy8%211&Q5r4%221=%7241%93E1?p0;1p0C1pTFH1pT:J1").
Proof. intros j m Hj Hm. unfold sb_. apply sub_length. rewrite Hlen. lia. Qed.
Lemma rd_src : ltac2:(TCodec.tc2 tcn__AsanMemcpyBaseK "Q='D'7'=&QGzr3%3221vR<%5231%7231&QEr4&QK%118%4231%<218'>'9'6'REy8%211%411%611&Q;&QD&Q4r6%211&Q8vRCr5%3221%94851F(0&Q5%125I%32?1%F3?51p0H1p0Q21p0Q01pTFQ91pT:Q;1pT@Q<1").
Proof.
intros k j m Hk Hj Hm. unfold memk, sb_.
pose proof (u64_range src). pose proof (u64_range dst).
destruct m as [|m'].
{ cbn. unfold sub. cbn. reflexivity. }
rewrite rdn_wbytes_out.
- replace (at_ src j) with (at_ src (Z.of_nat (Z.to_nat j))) by (f_equal; lia).
apply (rdn_sub ASEGS0 mem0 (length bs)); [exact Hsrc | rewrite Hlen; lia].
- rewrite length_firstn, Hlen, at_u; lia.
- rewrite at_u; lia.
- rewrite length_firstn, Hlen. lia.
Qed.
Lemma rd_src1 : ltac2:(TCodec.tc2 tcn__AsanMemcpyBaseK "Q?'D'=&QGzr2%3221vR<%5231%7231&QEr3+1%3221%;217'>'9'6'REy8%211%411%611&Q;&QD&Q4r5%211&Q8vRCr4%3221u1%:49621(0(3&Q3%117(8%11C%53D31%72D1%K3D91p0M1p0Q61p0Q41pT:Q=1pT@Q>1").
Proof.
intros k j Hk Hj H1. rewrite (rd_src k j 1) by lia. unfold sb_, b_.
rewrite sub_nth; [reflexivity | rewrite Hlen; lia].
Qed.
Lemma wr_dst : ltac2:(TCodec.tc2 tcn__AsanMemcpyBaseK "Q0'D'7&QGzr2%3221&QEr3&QK%115%4231vR<%:221'>'2&K&QD&Q4r5%211&Q8vR2r4%3221%94851A(<%=3<21p0?1p0G1pTFL1pT:N1pT@O1").
Proof.
intros k j m Hj Hm. unfold memk.
apply (store_ok_at ASEGS0 mem0 dst (length bs)); try assumption; rewrite ?lenZ; lia.
Qed.
Lemma memk_extend : ltac2:(TCodec.tc2 tcn__AsanMemcpyBaseK "Q?'D'6'REy8%211%411'7&QGzr3%3221&QEr4&QKr2%211%5241vR<%;221'>&Q5r5%221=%43B;1yR0%G11'9%11Gp031&Q7&Q4r6%211&Q8vR2%2214%7341?%H1I%K271%911%E3<41p0B1p0H1p0Q11pTFQ61pTDQ81pT@Q>1").
Proof.
intros k l m Hk Hm ->. unfold memk, sb_.
replace (at_ dst k) with (at_ dst (Z.of_nat (Z.to_nat k))) by (f_equal; lia).
rewrite wbytes_extend' by (rewrite Hlen; lia). f_equal. f_equal. lia.
Qed.
Lemma memk_extend1 : ltac2:(TCodec.tc2 tcn__AsanMemcpyBaseK "Q<'D'REy8%211&QGzr2%3221&QEr3+1%3221vR<%9221'>&Q3r4%211%43?91yR0%C11'9%11Cp031&Q7&Q4r5%211&Q8vR2%2214(3(8%11N%33OB1%;3851%L2:J%<11%H3?31p0E1p0K1p0Q21pT0Q71pT@Q;1").
Proof.
intros k b Hk H1 ->.
replace (k + 1)%Z with (k + Z.of_nat 1)%Z by lia.
rewrite <- (memk_extend k (sb_ k 1) 1); try lia; [|reflexivity].
unfold sb_, b_. rewrite sub_nth by (rewrite Hlen; lia). reflexivity.
Qed.
Lemma sb4_split : ltac2:(TCodec.tc2 tcn__AsanMemcpyBaseK "Q2'D'7&QGzr2%3221'Au4%2241'>'6'REy8%211%411&Q5r4%221:&1r3%5241&QE&QK%114%3281&@%12C7%<231%:3?81%D3?<1p0F1p0J1pTNO1pT:Q11").
Proof.
intros j q Hj Hq. unfold sb_.
replace 4%nat with (q + (4 - q))%nat at 1 by lia. rewrite sub_split. f_equal. f_equal. lia.
Qed.
Lemma skipn_sb : ltac2:(TCodec.tc2 tcn__AsanMemcpyBaseK "N'D'7&QGzr3%3221'>'6'REy8%211%411&C&Q5r4r2%3221%537=1&QE&QK%11@%3271&@%128C%;231%C3>81p0E1pTFJ1pTNK1pT:M1").
Proof.
intros j q m Hj. unfold sb_, sub. rewrite skipn_firstn_comm, <- skipn_add. f_equal. f_equal. lia.
Qed.
Lemma firstn_sb : ltac2:(TCodec.tc2 tcn__AsanMemcpyBaseK "H'D'7'Ar2r1%3221'>'6'REy8%211%411&Br3&Q5r4%221=%53741%4235%=3821p0?1pTFD1pTNE1pT:G1").
Proof. intros j q m Hq. unfold sb_, sub. rewrite firstn_firstn. f_equal. lia. Qed.
Lemma merge_sb : ltac2:(TCodec.tc2 tcn__AsanMemcpyBaseK "R2'D'7'REyR0%211&QGzr3%3221&QEr4+8%3221vR<%9221'='Au1%2218u3%42:1%6231'>&Q>&Q?&QC&Q5r6+4%D221u4%5221%711&QM+Q0&QJ&QKr5%211%42L1%7261%A291&QA%A2@=%C11%3216%G251%I3Q;Q51'6y8%Q@11%311&L%12G@r7%C1L%Q?221%O21K%Q43751p0<1p0Q71p0Q?1p0QF1pUBQK1pTNQO1pT:R11").
Proof.
intros j q v Hj H8 Hq Hv.
rewrite (sw_bytes_merge (sb_ j 4) (sb_ (j + 4) 4) q v); try (apply sb_len; lia); try assumption.
rewrite skipn_sb, firstn_sb by lia.
rewrite (sb4_split (j + Z.of_nat q) (4 - q)) by lia.
f_equal. f_equal; lia.
Qed.
Lemma merge_sb' : ltac2:(TCodec.tc2 tcn__AsanMemcpyBaseK "R2'D'7'REyR0%211&QGzr3%3221&QEr4+8%3221vR<%9221'='Au1%2218u3%42:1%6231'>&Q>&QA&QC&Q5r6u4%3221%511&QJ&QKr5%211%42H1%<261&Q?+4%N2<1%>21<%@11&QM+Q0%2219%8241%G2:1%I3Q;Q51'6y8%Q@11%311&L%12IDr7%G1L%Q?221%O21M%Q43751p0<1p0Q71p0Q?1p0QF1pUBQK1pTNQO1pT:R11").
Proof.
intros j q v Hj H8 Hq ->. apply merge_sb; try lia. unfold v_or. f_equal. apply Z.lor_comm.
Qed.
Lemma mc_lbu : forall regs pc rom w rd rs (imm : bv 12) k j0 j,
fetch_word ASEGS0 pc = Some w -> is_ecall w = false ->
decode_any w = Some (Load SZ1 false rd rs imm, 4%Z) ->
getr regs rs = at_ src j0 -> (j0 + bv_signed imm = j)%Z ->
(0 <= k <= n)%Z -> (0 <= j)%Z -> (j + 1 <= n)%Z ->
RiscvSemantics.step ASEGS0 (mkst regs pc (memk k) rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (LBv (b_ j))) (v_addi pc 4) (memk k) rom).
Proof.
intros regs pc rom w rd rs imm k j0 j Hf He Hd Hrs Hj Hk Hj0 Hj1.
eapply step_lbu; [exact Hf | exact He | exact Hd |].
rewrite Hrs, at_addi, Hj. apply rd_src1; lia.
Qed.
Lemma mc_lw : forall regs pc rom w rd rs (imm : bv 12) k j0 j,
fetch_word ASEGS0 pc = Some w -> is_ecall w = false ->
decode_any w = Some (Load SZ4 true rd rs imm, 4%Z) ->
getr regs rs = at_ src j0 -> (j0 + bv_signed imm = j)%Z ->
(0 <= k <= n)%Z -> (0 <= j)%Z -> (j + 4 <= n)%Z ->
RiscvSemantics.step ASEGS0 (mkst regs pc (memk k) rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (LWv (sb_ j 4))) (v_addi pc 4) (memk k) rom).
Proof.
intros regs pc rom w rd rs imm k j0 j Hf He Hd Hrs Hj Hk Hj0 Hj4.
eapply step_lw; [exact Hf | exact He | exact Hd | |].
- rewrite Hrs, at_addi, Hj. apply (rd_src k j 4); lia.
- symmetry. apply u_lez4. apply sb_len; lia.
Qed.
Lemma mc_sb : ltac2:(TCodec.tc2 tcn__AsanMemcpyBaseK "SI&Q2y5'REyR0%211%5241'9y8%611%311p061yQ0%:11%;1<y<%=11'D'>%<16&F&QDr9%3221(0r7%22=1%93841'2&Gr8%211(4%?3521';'Q1%221C%N11&M%11A(:(Q0(Nr6%342>C1+4%64;M21%G2;1%N3;91&Q9r=%221M&Q8vR2r5%3221%Q63QC51&QE&RF%12Q<M%32A1%Q;3Q<1Q4r?r:%?221%Q?3QL1F&RD&RG%12R0Q;%32QM1&Q3%11QA%QF3QO31&QGz%221<r;+1%E221vR<%7221'H'I%211&J&Q:&Q6rCrB&Q4r<%211rA%8576521%:2R91(E&Q<%129QD%Q928E%:11%?5>=318%62C1%RD3C81p0G1p0M1p0Q11p0Q91p0Q>1p0QD1p0QM1p0R=1p0RD1pUBS;1pTBS01pT@S11pT8S31pU6S61pU4S71pUDS91pU2S<1pTLSC1pU0SC1").
Proof.
intros regs pc rom w rs1 rs2 imm k k0 v Hf He Hd Hrs1 Hk Hrs2 Hb Hk0 Hk1.
rewrite <- (memk_extend1 k (b_ k)) by (lia || reflexivity).
eapply MmapSim.step_sb_at; [exact Hf | exact He | exact Hd | | exact Hrs2 | exact Hb |].
- rewrite Hrs1, at_addi, Hk. reflexivity.
- apply wr_dst; lia.
Qed.
Lemma mc_sw : ltac2:(TCodec.tc2 tcn__AsanMemcpyBaseK "SI&Q2y5'REyR0%211%5241'9y8%611%311p061yQ0%:11%;1<y<%=11'D'>%<16&F&QDr9%3221(0r7%22=1%93841'2&Gr8%211(4%?3521';'Q1%221C%N11&M%11A(:(Q0(Or6%342>C1+4%64;M21%G2;1%N3;91&Q9r=%221M&Q8vR2r5%3221%Q63QC51&QE&RF%12Q<M%32A1%Q;3Q<1Q4r?r:%?221%Q?3QL1F'6%11QJ&Lu4%221Q=&Q5%12QB3%QG3631&QGz%221=r;%E21Q1vR<%6221'H'I%211&J&Q:&Q6rCrB&Q4r<%211rA%8576521%:2R91(E&Q<%129QD%Q928QE%:11%?5>=318%62C1%RD3C81p0G1p0L1p0Q01p0Q91p0Q>1p0QD1p0QM1p0R=1p0RD1pUBS;1pTBS01pT@S11pT8S31pU6S61pU4S71pUDS91pU2S<1pTLSC1pU0SC1").
Proof.
intros regs pc rom w rs1 rs2 imm k k0 v Hf He Hd Hrs1 Hk Hrs2 Hb Hk0 Hk4.
replace (k + 4)%Z with (k + Z.of_nat 4)%Z by lia.
rewrite <- (memk_extend k (sb_ k 4) 4) by (lia || reflexivity).
rewrite <- Hb.
eapply step_sw_at; [exact Hf | exact He | exact Hd | | exact Hrs2 |].
- rewrite Hrs1, at_addi, Hk. reflexivity.
- apply wr_dst; lia.
Qed.
Lemma sw_val_plain : ltac2:(TCodec.tc2 tcn__AsanMemcpyBaseK "M'D&QGzr1%3221&QEr2+4%3221vR<%9221'>'6'REy8%211%411&Lu4&QC&Q5r3%2214%411%7261%>3913p0@1p0G1pT@L1").
Proof. intros k Hk H4. apply sw_bytes_LWv. apply sb_len; lia. Qed.
Lemma sb_val_plain : ltac2:(TCodec.tc2 tcn__AsanMemcpyBaseK "A'D'>'REy8%211&RD&RGyR0&QB&Q3r1%211%411%7261%92;1%>3;14pT@@1").
Proof. intros k. apply sb_byte_LBv. Qed.
Lemma sb_val_srli : ltac2:(TCodec.tc2 tcn__AsanMemcpyBaseK "Q?'D'7&QGzr2%3221&QEr3+4%3221vR<%9221'Au3%2271'>'REy8%211&RD&RGyR0&Q@&QC&Q5r5u4%3221%511&QJ+8&QKr4%211%5241%=271%@2?1%B2D1&Q3%Q12>6%211%J3G41p0L1p0Q01p0Q71pTNQ<1pT:Q>1").
Proof.
intros j q Hj H4 Hq. rewrite sb_byte_srli_LWv; [| apply sb_len; lia | exact Hq].
unfold sb_, b_, sub.
rewrite nth_firstn. replace (q <? 4)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
rewrite nth_skipn. f_equal. lia.
Qed.
Lemma sb_val_word0 : ltac2:(TCodec.tc2 tcn__AsanMemcpyBaseK "Q0'D&QGzr1%3221&QEr2+4%3221vR<%9221'>'REy8%211&RD&RGyR0&QC&Q5r3u4%3221%511%8271%:2<1&Q3%117%A3>31p0C1p0J1pT:O1").
Proof.
intros j Hj H4.
pose proof (sb_val_srli j 0 Hj H4 ltac:(lia)) as E.
rewrite Z.add_0_r in E. rewrite <- E. f_equal. f_equal.
unfold v_srli. rewrite Z.mul_0_r, Z.shiftr_0_r. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma merge_s16 : ltac2:(TCodec.tc2 tcn__AsanMemcpyBaseK "QJ'REyR0%211'D'>r4&Q>&Q?&QC&Q5r2u4%3221%511+@%8221&QAr3%9217%;11%4216%?261%B3DA1&QE+4%22D1%F3G91r5+2%6221%J3K=1&QGzr6%3221r7+8%>221vR<%8221'6y8%Q:11%311&Lr9%22Q31%Q62>Q4%Q<3521p0:1p0@1p0E1p0J1p0O1pT@QC1pT>QD1pT<QE1pUBQG1").
Proof.
intros v j1 j2 k -> -> -> Hj H8.
replace (j1 + 2)%Z with (j1 + Z.of_nat 2)%Z by lia. apply merge_sb; try lia. reflexivity.
Qed.
Lemma merge_s8 : ltac2:(TCodec.tc2 tcn__AsanMemcpyBaseK "QJ'REyR0%211'D'>r4&Q>&Q?&QC&Q5r2u4%3221%511+H%8221&QAr3%9217%;11+8%5221%@271%C3EB1&QE+4%22E1%G3H:1r5+1%6221%K3L>1&QGzr6%3221r7%=21AvR<%7221'6y8%Q:11%311&Lr9%22Q31%Q62=Q4%Q<3521p0:1p0?1p0D1p0I1p0N1pT@QC1pT>QD1pT<QE1pUBQG1").
Proof.
intros v j1 j2 k -> -> -> Hj H8.
replace (j1 + 1)%Z with (j1 + Z.of_nat 1)%Z by lia. apply merge_sb; try lia. reflexivity.
Qed.
Lemma merge_s24 : ltac2:(TCodec.tc2 tcn__AsanMemcpyBaseK "QJ'REyR0%211'D'>r4&Q>&Q?&QC&Q5r2u4%3221%511+8%8221&QAr3%9217%;11+H%5221%@271%C3EB1&QE+4%22E1%G3H:1r5+3%6221%K3L>1&QGzr6%3221r7%=21GvR<%7221'6y8%Q:11%311&Lr9%22Q31%Q62=Q4%Q<3521p0:1p0?1p0D1p0I1p0N1pT@QC1pT>QD1pT<QE1pUBQG1").
Proof.
intros v j1 j2 k -> -> -> Hj H8.
replace (j1 + 3)%Z with (j1 + Z.of_nat 3)%Z by lia. apply merge_sb; try lia. reflexivity.
Qed.
Lemma sb_val_srli8 : ltac2:(TCodec.tc2 tcn__AsanMemcpyBaseK "Q9'D&QGzr2%3221&QEr3+4%3221vR<%9221'>r4+1%9221%43?91'REy8%211&RD&RGyR0&Q@&QC&Q5r5u4%3221%511+8%8221%;2:1%=2?1&Q3%11F%H3A31p0E1p0K1p0Q21pT@Q71pT:Q81").
Proof.
intros j k Hj H4 ->. replace (j + 1)%Z with (j + Z.of_nat 1)%Z by lia.
rewrite <- (sb_val_srli j 1) by lia. reflexivity.
Qed.
Lemma sb_val_srli16 : ltac2:(TCodec.tc2 tcn__AsanMemcpyBaseK "Q9'D&QGzr2%3221&QEr3+4%3221vR<%9221'>r4+2%9221%43?91'REy8%211&RD&RGyR0&Q@&QC&Q5r5u4%3221%511+@%8221%;2:1%=2?1&Q3%11F%H3A31p0E1p0K1p0Q21pT@Q71pT:Q81").
Proof.
intros j k Hj H4 ->. replace (j + 2)%Z with (j + Z.of_nat 2)%Z by lia.
rewrite <- (sb_val_srli j 2) by lia. reflexivity.
Qed.
Lemma sb_val_word0' : ltac2:(TCodec.tc2 tcn__AsanMemcpyBaseK "Q4'D&QGzr2%3221&QEr3+4%3221vR<%9221'>r4%23=71'REy8%211&RD&RGyR0&QC&Q5r5u4%3221%511%8271%:2<1&Q3%11A%C3>31p0B1p0F1p0M1pT@Q21pT:Q31").
Proof. intros j k Hj H4 ->. apply sb_val_word0; lia. Qed.
End MC.
Ltac rwH :=
repeat match goal with
| H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
end.
Ltac unorm :=
repeat match goal with
| |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
lazymatch z with context [Z_to_bv 64 _] => fail | _ => rewrite (u_Z2bv z) by lia end
end.
Ltac mnorm := gres; imm_norm; rewrite ?v_addi_0; rwH; rewrite ?at_addi; vals_lit.
Ltac cond_lia :=
rwH; unfold c_ltu, c_eq, bv_ltu, bv_eqb; imm_norm; unorm;
first [ apply Z.ltb_lt | apply Z.ltb_ge | apply Z.eqb_eq | apply Z.eqb_neq ]; lia.
Lemma u_andi : ltac2:(TCodec.tc2 tcn__AsanMemcpyBaseK "N'REyR0%211'D'=&QGzr1%3221&QH&QL+2+R0%3221%5271%;271'>&RG&Q=r3r2%3221%52E1&QF%72G5%2215%:3G41p0<1pT8I1pUFK1").
Proof.
intros x imm Hi. unfold v_andi. rewrite Z_to_bv_unsigned.
replace (bv_wrap 64 imm) with imm by (symmetry; apply bv_wrap_small; change (bv_modulus 64) with (2^64)%Z; lia).
apply bv_wrap_small. change (bv_modulus 64) with (2^64)%Z. apply Z_land_range; [apply u64_range|lia].
Qed.
Lemma land_3 : ltac2:(TCodec.tc2 tcn__AsanMemcpyBaseK "@'D&QGzr1%3221'>&QFr2+3%3221&QI+4%2251%83=41p0:1pSN?1").
Proof. intros a Ha. change 3%Z with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land_1 : ltac2:(TCodec.tc2 tcn__AsanMemcpyBaseK "@'D&QGzr1%3221'>&QFr2+1%3221&QI+2%2251%83=41p0:1pSN?1").
Proof. intros a Ha. change 1%Z with (Z.ones 1). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma bits_lt32 : ltac2:(TCodec.tc2 tcn__AsanMemcpyBaseK "QD'D'=&QGzr1%3221&QH+Q0%2241%8241'?'>&QFr2+@%3221%53@1=%63A23%8221+8%8271%:3E1B%;3F23%=221+4%=2<1%?3J1G%@3K23%B221+2%B2A1%D3O1L%E3Q023%G221+1%G2F1%I3Q41Q1%J3Q523%L221&QE%12ID%221@%321<%4218%Q13Q<O1%Q<271%Q=2=1%Q>2C1%Q?2I1%Q@2O1p0Q91pTFQC1").
Proof.
intros m Hm.
assert (E : exists k : nat, m = Z.of_nat k /\ (k < 32)%nat).
{ exists (Z.to_nat m). split; lia. }
destruct E as (k & -> & Hk).
do 32 (destruct k as [|k]; [vm_compute; intuition lia|]). lia.
Qed.
Lemma at_mod4 : ltac2:(TCodec.tc2 tcn__AsanMemcpyBaseK "Q4'REyR0%211'D'=&QGz&QE&RGr2%2291r1%5221%8271&QH&QL+2+R0%3221%5271%@271'>&QI&Q8r3%221@%B2I1+4%6221%E2L5%G21E%9214%;3M41p0=1pT4O1pSNQ11").
Proof. intros a d H. rewrite at_u by lia. reflexivity. Qed.
