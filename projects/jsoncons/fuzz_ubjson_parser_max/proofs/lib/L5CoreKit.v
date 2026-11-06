(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface AllocSim
AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlanSoundSums L5Defs L5Core.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__L5CoreKit () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanSoundSums.APSX."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5CoreKit.L5K."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.Arith.PeanoNat.Nat."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1O"; "1Some"; "1bool"; "1length"; "1list"; "1nat"; "1option"; "1prod"; "1true"; "2I"; "2and"; "2eq"; "2not"; "2or"; "3mul"; "4repeat"]; ["4seq"; "5Z"; "0L"; "0LB"; "6Segment"; "7bvmap"; "0M"; "0P"; "0R"; "0R'"; "8kept_ok"; "9wbytes"; ":client_addr"; ":heap_layout"; ":regs_preserved"; ";ret_ok"]; ["<CS"; "<limb_bytes"; "=limbs_at"; "=ra_ok"; "=u64_at"; ">getr"; ">rdn"; "?eqb"; "@In"; "@existsb"; "@forallb"; "@incl"; "Aadd"; "Ale"; "Alt"; "Amul"]; ["Aof_nat"; "Apow"; "Asub"; "0a"; "0b"; "0dst"; "0fb"; "0i"; "0j"; "0k"; "0ks"; "0ks'"; "0l"; "0n"; "0q"; "0r"]; ["0scr"; "0scr'"; "0segs"; "0sp"; "0sp'"; "BBV"; "BZ_to_bv"; "Bbv"; "0ws"]]).
Local Ltac lia := L5FastLia.plia.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto0.
Module L5K.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Definition CS : list nat := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Lemma regs_preserved_by_index : ltac2:(TCodec.tc2 tcn__L5CoreKit "N&Ey5'R7yR0%211%5241'5&Q8r1&Q0%33421';&Q5r3&R6&Q@r2%211%42A1%7261r4%9213%;3B31p0=1pS@B1&N%12=:p031pQDG1pQBH1").
Proof. intros R R'.
intros K r Hr. rewrite <- (ridx_roundtrip r). apply K.
unfold callee_saved_idx in Hr. unfold ridx. set (z := bv_unsigned r) in *. cbn in Hr.
repeat (destruct Hr as [Hr|Hr]; [rewrite <- Hr; cbn; tauto|]). destruct Hr.
Qed.
Lemma regs_preserved_index : ltac2:(TCodec.tc2 tcn__L5CoreKit "N&Ey5'R7yR0%211%5241'5&Nr3r2%3221&Q8&Q0%23741';&Q5r4&R6&Q@%11;%32C1%6251r5%8213%:3D31p0<1p0@1pS@E1pQDG1pQBH1").
Proof. intros R R' i.
intros P Hi. apply P. unfold callee_saved_idx. cbn in Hi.
repeat (destruct Hi as [<-|Hi]; [cbn; tauto|]). destruct Hi.
Qed.
Lemma client_inner : ltac2:(TCodec.tc2 tcn__L5CoreKit "Q1'M'4'7'A%2211%411&Lr7r6r5r4r1%6554321&Q=&QB%1276r3%3271%5231%62:<r:r9%@521>=<p041p061p0=1pS8G1pT4H1pT:I1pT2J1pT8K1pQ8J1pQ6Q01").
Proof. intros L LB sp scr sp' scr' a.
intros CA H1 H2. destruct CA as [IB|[[S1 S2]|IM]]. left; exact IB. right; left; split; [exact S1|lia]. right; right; exact IM.
Qed.
Lemma kept_ok_index : ltac2:(TCodec.tc2 tcn__L5CoreKit "N&Ey5'R7yR0%211%5241'5&Jr3r2%3221&Q8&Q0%23741';&Q5r4&R6&Q@%11;%32C1%6251r5%8213%:3D31p0<1p0@1pS@E1pQDG1pQBH1").
Proof. intros R R' i.
intros K Hi. apply K.
- intros E. apply (f_equal bv_unsigned) in E. rewrite Z_to_bv_unsigned in E. unfold bv_wrap in E. change (bv_modulus 5) with 32 in E.
change (bv_unsigned (0%bv : bv 5)) with 0 in E. cbn in Hi. repeat (destruct Hi as [<-|Hi]; [vm_compute in E; discriminate|]). destruct Hi.
- unfold ridx. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. unfold APC.caller_saved.
cbn in Hi. repeat (destruct Hi as [<-|Hi]; [vm_compute; intros HH; repeat (destruct HH as [HH|HH]; [discriminate|]); exact HH|]). destruct Hi.
Qed.
Lemma kept_sub : ltac2:(TCodec.tc2 tcn__L5CoreKit "Q<&Ey5'R7yR0%211%5241'4'5%211&Q8r1r3%33521';&Q5r5&R6&Q@r2%211%42C1%7261r6%9213%;3D31p0=1pS@C1&Q;%13E:Ar4%E3GD1r7%B21<r8%D21>%F3O31p061pS@N1p0:1p0=1pSHQ01pSFQ11pQDQ51pQBQ61").
Proof. intros R R' ks ks'. intros K Hi i Hin. apply K. apply Hi. exact Hin. Qed.
Lemma ret_ok_lit : ltac2:(TCodec.tc2 tcn__L5CoreKit "<'A&Q3r1%211&O&R6yR0r2%3221%511p071pT0;1").
Proof. intros r.
intros [Hr He]. apply Hoare.ret_ok_even. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small r (2 ^ 64)) by lia. exact He.
Qed.
Lemma lit_neq : ltac2:(TCodec.tc2 tcn__L5CoreKit "Q1'A':&Q=zr2%3221&Q>&QA+2+R0%3221%5271%;271&<';r4r3%33A21%511'R7yR0%211&R6r5%2241%325:%<3521%>11p0:1p0A1p0B1pS:O1pS8Q01").
Proof. intros a b.
intros Ha Hb Hne E. apply Hne. apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E.
change (bv_modulus 64) with (2 ^ 64) in E. rewrite !Z.mod_small in E by lia. exact E.
Qed.
Lemma In_of_mem : ltac2:(TCodec.tc2 tcn__L5CoreKit "C'5'4%112';'2&Q9&Q7r2%211r1%53:21(8%93821&Q8r3%23?18p041pSJ?1pSBB1").
Proof. intros j l. intros H. apply existsb_exists in H as (x & Hx & E). apply Nat.eqb_eq in E. subst x. exact Hx. Qed.
Ltac inlist H := cbn in H; repeat (destruct H as [<-|H]; [apply In_of_mem; reflexivity|]); destruct H.
Lemma u64_zero_of_fill : ltac2:(TCodec.tc2 tcn__L5CoreKit "QG'4'D%211'R7yR0%211'6y8%511%311p051'A'5&Q=zr3%3221&Q<r4&Q@%115%4231&QA+2+R0%3221%=251+8%;2:1r5%;11%B231&Q4r9&Kr8&R6r7%22Q21&?%42Q1Jr6%33Q221%93851%K27?%=4<21Op0?1p0O1p0F1p0Q11pSBQ71pSDQ71pS<Q91pQ>Q;1pT6QD1").
Proof. intros segs M dst k j.
intros Hd Hk Hj Hjk. unfold L5.u64_at. change (word_to_le_bytes 8 (Z_to_bv 64 0)) with (repeat (Z_to_bv 8 0 : byte) 8).
apply APSX.rdn_overlay_all. { rewrite L5.unsigned_lit by lia. cbn. lia. }
intros i Hi. rewrite L5.unsigned_lit by lia.
replace (dst + j + i) with (bv_unsigned (Z_to_bv 64 dst) + Z.of_nat (Z.to_nat (j + i))) by (rewrite L5.unsigned_lit by lia; lia).
rewrite AX2S.wbytes_nth. f_equal. apply nth_repeat. rewrite L5.unsigned_lit by lia. rewrite repeat_length. lia. rewrite repeat_length. cbn in Hi. lia.
Qed.
Lemma wbytes_fill_out : ltac2:(TCodec.tc2 tcn__L5CoreKit "R7'4'D%211'R7yR0%211'6y8%511%311p051'A'5':&Q=zr4%3221&Q>&QA+2+R0%3221%5271%;271&Q<r5&Q@%11<%4231%@218'=r6%617%9221r8%F221r7%;11%>241%J218%:251';%Q;1Q3%Q611&Q6r;&Kr:&R6r9%22Q?1&?%42Q>Q6%23Q>1C%83741%72QDC%<4;21I%=4<:2J%A3?21p0C1p0O1p0Q61p0Q11p0Q81pSLQE1pS8QG1pSDQG1pS<QI1pQ>QK1pT6R41").
Proof. intros segs M dst k a n.
intros Hd Hk Ha Hn Hap. apply rdn_wbytes_out; rewrite ?L5.unsigned_lit by lia; rewrite ?repeat_length; lia.
Qed.
Definition limb_bytes (ws : list Z) : list byte := flat_map (fun w => word_to_le_bytes 8 (Z_to_bv 64 w)) ws.
Lemma limb_bytes_length : ltac2:(TCodec.tc2 tcn__L5CoreKit "C'4'A%211';'5&3'R7y8%211&Q1r1%211%7241&>u8%:2>5%3221%>3=51pTB@1").
Proof. intros ws. induction ws as [|w ws IH]. reflexivity. cbn [limb_bytes flat_map]. rewrite length_app, length_N_to_le_bytes. unfold limb_bytes in IH. rewrite IH. cbn [length]. lia. Qed.
Lemma rdn_of_limbs_at : ltac2:(TCodec.tc2 tcn__L5CoreKit "QN'4'D%211'R7yR0%211'6y8%511%311p051'A%<11&Q2r4r3r1r2%544321&Q=z%2214&Q<&Q?+8&Q@&3%12@=%311%6251%82?1&QA+2+R0%3221%@251';%Q51M%Q011&Q6r7r6&R6%12Q7M&>u8r5%E2Q41%4231%:49861(1&Q1%116%32@1%B3@51p0D1p0Q31p0Q71pSNQ?1pTBQ?1pQ>QB1pT6QK1").
Proof. intros segs M.
induction ws as [|w ws IH]; intros q HL Hq Hn. reflexivity.
cbn [length] in Hn. replace (8 * length (w :: ws))%nat with (8 + 8 * length ws)%nat by (cbn [length]; lia).
change (limb_bytes (w :: ws)) with (word_to_le_bytes 8 (Z_to_bv 64 w) ++ limb_bytes ws).
apply SeqExec.rdn_app.
- pose proof (HL 0%nat ltac:(cbn; lia)) as H0. cbn [nth] in H0. unfold L5.u64_at in H0. rewrite Z.add_0_r in H0. exact H0.
- unfold nat_to_word.
replace (Z_to_bv 64 q + Z_to_bv 64 (Z.of_nat 8))%bv with (Z_to_bv 64 (q + 8)).
2: { apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite <- Z.add_mod by lia. reflexivity. }
apply IH. intros i Hi. replace (q + 8 + 8 * Z.of_nat i) with (q + 8 * Z.of_nat (S i)) by lia.
change (nth i ws 0) with (nth (S i) (w :: ws) 0). apply HL. cbn; lia. lia. lia.
Qed.
Lemma limbs_at_of_wbytes : ltac2:(TCodec.tc2 tcn__L5CoreKit "QC'4'D%211'A%411'R7yR0%211'6y8%511%311p051&Q=zr1%3221&Q>&Q<r2&Q?+8&Q@&3r4%22F1%411%7261%:291&QA+2+R0%3221%@251&Q2r6&K&R6r3%22Q11&Q1r5%211%73C41%:49163p0<1p0N1pS<Q<1pQ>Q41pTBQ=1pT6Q@1").
Proof. intros segs.
induction ws as [|w ws IH]; intros M dst Hd Hn. apply L5C.limbs_at_nil.
cbn [length] in Hn.
change (limb_bytes (w :: ws)) with (word_to_le_bytes 8 (Z_to_bv 64 w) ++ limb_bytes ws).
rewrite AllocSim.wbytes_app. rewrite length_N_to_le_bytes. unfold nat_to_word.
replace (Z_to_bv 64 dst + Z_to_bv 64 (Z.of_nat 8))%bv with (Z_to_bv 64 (dst + 8)).
2: { apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite <- Z.add_mod by lia. reflexivity. }
intros i Hi. destruct i as [|i].
- cbn [nth]. unfold L5.u64_at. rewrite Z.add_0_r.
rewrite rdn_wbytes_out. 2: { left. rewrite !L5.unsigned_lit by lia. cbn. lia. } 2: { rewrite L5.unsigned_lit by lia. cbn. lia. }
2: { rewrite L5.unsigned_lit by lia. rewrite limb_bytes_length. lia. }
rewrite <- (length_N_to_le_bytes 8 (Z_to_bv 64 w)) at 1. apply SeqExec.rdn_wbytes_hit. rewrite L5.unsigned_lit by lia. rewrite length_N_to_le_bytes. lia.
- cbn [nth]. replace (dst + 8 * Z.of_nat (S i)) with (dst + 8 + 8 * Z.of_nat i) by lia. apply IH. lia. lia. cbn in Hi. lia.
Qed.
Lemma wbytes_limbs_out : ltac2:(TCodec.tc2 tcn__L5CoreKit "RA'4'D%211'R7yR0%211'6y8%511%311p051'A%<11'5':&Q=zr4%3221&Q>&QA+2+R0%3221%5271%;271&Q<r5&Q?+8&Q@&3%12E?%311%6251%9281%E21=%71D%<2;1%H21@'=r6%<1?%A221r8%N221r7%@2Q41%B11%E2D1%H261%Q421:%<271';%QF1Q>%QA11&Q6r;&Kr:&R6r9%22QJ1&Q1%11D%73631%62QND%;4:21J%<4;92K%@3>21p0B1p0Q01p0Q?1p0Q51p0QA1pSLQN1pS8R11pTBR11pS<R31pQ>R51pT6R>1").
Proof. intros segs M dst ws a n.
intros Hd Hn Ha Han Hap. apply rdn_wbytes_out; rewrite ?L5.unsigned_lit by lia; rewrite ?limb_bytes_length; lia.
Qed.
Lemma wbytes_limbs_out1 : ltac2:(TCodec.tc2 tcn__L5CoreKit "R1'R7yR0%211'6y8%511%311p051'A'4%112':&Q=zr3%3221&Q>&QA+2+R0%3221%5271%;271&Q<r4&Q?+8&Q@&3%12E?%311%6251%9281%E21=&<r6%H21<r5%:2N1%<11%?2>1%B261%J2B1%Q0271%:11';&Kr8&R6r7%22QA1&Q1%11A%52QD@%847421%812%;3QB21p0=1p0Q41p0J1p0Q61pS8QE1pTBQD1pS<QG1pQ>QI1").
Proof. intros M dst ws a.
intros Hd Hn Ha Hna. apply AX2S.wbytes_out; rewrite ?L5.unsigned_lit, ?limb_bytes_length by lia; lia.
Qed.
Lemma byte_cases : ltac2:(TCodec.tc2 tcn__L5CoreKit "Q2'A'2p021';&Q:'5r2&Q@r1%211%411qS@61&@(0uX0%3221%<3;51(8%?3A21':&Q=z%221>&Q>+X0%22A1%7241r4%11F%J3L1<p041pS>O1p0>1pQ@O1").
Proof. intros P.
intros H fb Hfb. rewrite forallb_forall in H. replace fb with (Z.of_nat (Z.to_nat fb)) by lia. apply H. apply in_seq. lia.
Qed.
Lemma rl1 : ltac2:(TCodec.tc2 tcn__L5CoreKit "?';'R7y5%211(R5+1(9%33521/015&R6&Q@u1%211%42;1%>3;61"). Proof. apply bv_eq. reflexivity. Qed.
Lemma rl2 : ltac2:(TCodec.tc2 tcn__L5CoreKit "?';'R7y5%211(R5+2(9%33521/015&R6&Q@u2%211%42;1%>3;61"). Proof. apply bv_eq. reflexivity. Qed.
Lemma rl3 : ltac2:(TCodec.tc2 tcn__L5CoreKit "?';'R7y5%211(R5+3(9%33521/015&R6&Q@u3%211%42;1%>3;61"). Proof. apply bv_eq. reflexivity. Qed.
Lemma rl4 : ltac2:(TCodec.tc2 tcn__L5CoreKit "?';'R7y5%211(R5+4(9%33521/015&R6&Q@u4%211%42;1%>3;61"). Proof. apply bv_eq. reflexivity. Qed.
Lemma rl5 : ltac2:(TCodec.tc2 tcn__L5CoreKit "?';'R7y5%211(R5+5(9%33521/015&R6&Q@u5%211%42;1%>3;61"). Proof. apply bv_eq. reflexivity. Qed.
Lemma rl6 : ltac2:(TCodec.tc2 tcn__L5CoreKit "?';'R7y5%211(R5+6(9%33521/015&R6&Q@u6%211%42;1%>3;61"). Proof. apply bv_eq. reflexivity. Qed.
Lemma rl7 : ltac2:(TCodec.tc2 tcn__L5CoreKit "?';'R7y5%211(R5+7(9%33521/015&R6&Q@u7%211%42;1%>3;61"). Proof. apply bv_eq. reflexivity. Qed.
Lemma rl8 : ltac2:(TCodec.tc2 tcn__L5CoreKit "?';'R7y5%211(R5+8(9%33521/015&R6&Q@u8%211%42;1%>3;61"). Proof. apply bv_eq. reflexivity. Qed.
Lemma rl9 : ltac2:(TCodec.tc2 tcn__L5CoreKit "?';'R7y5%211(R5+9(9%33521/015&R6&Q@u9%211%42;1%>3;61"). Proof. apply bv_eq. reflexivity. Qed.
Lemma rl10 : ltac2:(TCodec.tc2 tcn__L5CoreKit "?';'R7y5%211(R5+:(9%33521/015&R6&Q@u:%211%42;1%>3;61"). Proof. apply bv_eq. reflexivity. Qed.
Lemma rl11 : ltac2:(TCodec.tc2 tcn__L5CoreKit "?';'R7y5%211(R5+;(9%33521/015&R6&Q@u;%211%42;1%>3;61"). Proof. apply bv_eq. reflexivity. Qed.
Lemma rl12 : ltac2:(TCodec.tc2 tcn__L5CoreKit "?';'R7y5%211(R5+<(9%33521/015&R6&Q@u<%211%42;1%>3;61"). Proof. apply bv_eq. reflexivity. Qed.
Lemma rl13 : ltac2:(TCodec.tc2 tcn__L5CoreKit "?';'R7y5%211(R5+=(9%33521/015&R6&Q@u=%211%42;1%>3;61"). Proof. apply bv_eq. reflexivity. Qed.
Lemma rl14 : ltac2:(TCodec.tc2 tcn__L5CoreKit "?';'R7y5%211(R5+>(9%33521/015&R6&Q@u>%211%42;1%>3;61"). Proof. apply bv_eq. reflexivity. Qed.
Lemma rl15 : ltac2:(TCodec.tc2 tcn__L5CoreKit "?';'R7y5%211(R5+?(9%33521/015&R6&Q@u?%211%42;1%>3;61"). Proof. apply bv_eq. reflexivity. Qed.
Lemma rl16 : ltac2:(TCodec.tc2 tcn__L5CoreKit "?';'R7y5%211(R5+@(9%33521/015&R6&Q@u@%211%42;1%>3;61"). Proof. apply bv_eq. reflexivity. Qed.
Lemma rl17 : ltac2:(TCodec.tc2 tcn__L5CoreKit "?';'R7y5%211(R5+A(9%33521/015&R6&Q@uA%211%42;1%>3;61"). Proof. apply bv_eq. reflexivity. Qed.
Lemma rl18 : ltac2:(TCodec.tc2 tcn__L5CoreKit "?';'R7y5%211(R5+B(9%33521/015&R6&Q@uB%211%42;1%>3;61"). Proof. apply bv_eq. reflexivity. Qed.
Lemma rl19 : ltac2:(TCodec.tc2 tcn__L5CoreKit "?';'R7y5%211(R5+C(9%33521/015&R6&Q@uC%211%42;1%>3;61"). Proof. apply bv_eq. reflexivity. Qed.
Lemma rl20 : ltac2:(TCodec.tc2 tcn__L5CoreKit "?';'R7y5%211(R5+D(9%33521/015&R6&Q@uD%211%42;1%>3;61"). Proof. apply bv_eq. reflexivity. Qed.
Lemma rl21 : ltac2:(TCodec.tc2 tcn__L5CoreKit "?';'R7y5%211(R5+E(9%33521/015&R6&Q@uE%211%42;1%>3;61"). Proof. apply bv_eq. reflexivity. Qed.
Lemma rl22 : ltac2:(TCodec.tc2 tcn__L5CoreKit "?';'R7y5%211(R5+F(9%33521/015&R6&Q@uF%211%42;1%>3;61"). Proof. apply bv_eq. reflexivity. Qed.
Lemma rl23 : ltac2:(TCodec.tc2 tcn__L5CoreKit "?';'R7y5%211(R5+G(9%33521/015&R6&Q@uG%211%42;1%>3;61"). Proof. apply bv_eq. reflexivity. Qed.
Lemma rl24 : ltac2:(TCodec.tc2 tcn__L5CoreKit "?';'R7y5%211(R5+H(9%33521/015&R6&Q@uH%211%42;1%>3;61"). Proof. apply bv_eq. reflexivity. Qed.
Lemma rl25 : ltac2:(TCodec.tc2 tcn__L5CoreKit "?';'R7y5%211(R5+I(9%33521/015&R6&Q@uI%211%42;1%>3;61"). Proof. apply bv_eq. reflexivity. Qed.
Lemma rl26 : ltac2:(TCodec.tc2 tcn__L5CoreKit "?';'R7y5%211(R5+J(9%33521/015&R6&Q@uJ%211%42;1%>3;61"). Proof. apply bv_eq. reflexivity. Qed.
Lemma rl27 : ltac2:(TCodec.tc2 tcn__L5CoreKit "?';'R7y5%211(R5+K(9%33521/015&R6&Q@uK%211%42;1%>3;61"). Proof. apply bv_eq. reflexivity. Qed.
End L5K.
