(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl KInv MI_Tree MI_Inv MI_Kit MI_Arith.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Spec_MI_Read () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MI_Inv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.countable."; "stdpp.gmap."; "stdpp.numbers.N."; "stdpp.numbers.Z."], [["1Some"; "1option"; "1pair"; "1prod"; "1snd"; "2and"; "2eq"; "3N"; "3Z"; "4byte_of"; "4known"; "4mslot"; "5Known"; "5NSLOTS"; "5PGSZ"; "5aptr"]; ["5area_of"; "5cell_read"; "5cellval"; "5get_shadow"; "5mstate"; "5r_cells"; "5s_shadow"; "5shadow"; "6add"; "6div"; "6land"; "6le"; "6lt"; "6modulo"; "6mul"; "6pow"]; ["6shiftr"; "0a"; "0i"; "0k"; "0o"; "0o'"; "0q"; "0r"; "0rid"; "0rid'"; "0sh"; "0st"; "7lookup"; "8N_countable"; "8Z_countable"; "9gmap"]; ["9gmap_lookup"; ":eq_dec"; ";eq_dec"; "0t"; "0v"; "0v'"; "0x"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Lemma rd8_known {R} st q v (k : Z -> M R) :
cell_read (get_shadow st (fst q)) (snd q) = Known v -> rd8 st q k = k v.
Proof. intros H. unfold rd8. rewrite H. reflexivity. Qed.
Lemma known_at : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Read "Q2'D'7'8&:r6(2r5r4%347621r3%73621'6r2%23;17r7%43>81'B&A&Cr9%221>%421>(<%11C%=3831p0:1p0=1p0A1pR<J1pRDL1pS:L1pR:M1pRBO1pRHQ11").
Proof. intros st rid o v rid' o'. intros H -> ->. exact H. Qed.
Lemma rd8_ftree {R} L st q (k : Z -> M R) Post :
(forall v, cell_read (get_shadow st (fst q)) (snd q) = Known v -> 0 <= v < 256) ->
(forall v, 0 <= v < 256 -> ftree L (k v) Post) ->
ftree L (rd8 st q k) Post.
Proof.
intros Hk H. unfold rd8. destruct (cell_read _ _) as [v|h] eqn:E.
- apply H. apply Hk. reflexivity.
- cbn [ftree]. intros v Hv. unfold peek_answer_ok.
destruct (Z.leb_spec 0 v), (Z.ltb_spec v 256); cbn [andb]; try lia. apply H. lia.
Qed.
Lemma rd16_ftree {R} L st q (k : Z -> M R) Post :
(forall q' v, cell_read (get_shadow st (fst q')) (snd q') = Known v -> 0 <= v < 256) ->
(forall v, 0 <= v < 65536 -> ftree L (k v) Post) ->
ftree L (rd16 st q k) Post.
Proof.
intros Hk H. unfold rd16. apply rd8_ftree; [apply Hk|]. intros b0 H0. apply rd8_ftree; [apply Hk|]. intros b1 H1. apply H. lia.
Qed.
Lemma known_byte : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Read "R7'D'7'8'G'6'1%113&Q<'Q?&QA&Q=%34:218&Q@%14<43:r7&Fr8%211%;6A?7541(0r4%22B1%B3@41'3%12FG%D11&QB&Q>%D4J214%A4K325&Er5%211%J6O954=1(2r3r2%34Q3Q421%C2>1%Q33>61'5&Kz%221G&L+X0%22J1%7241p091p0K1pS8QA1pS<QA1pR<QB1pRFQB1'B&A&C%12JQ5%321G(<%11H%QI3731%E2DK%C2LB%H221p041p0=1pS:R11pR:R21pRBR41pRHR61").
Proof. intros st rid o v.
intros Hc H. unfold cell_read, get_shadow in H. destruct (s_shadow st !! rid) as [sh|] eqn:E; cbn [default id] in H.
- destruct (r_cells sh !! o) as [[v' t]|] eqn:E2.
+ match type of H with (if ?c then _ else _) = _ => destruct c end; inversion H. subst. eapply Hc; eauto.
+ match type of H with (if ?c then _ else _) = _ => destruct c end; inversion H. lia.
- rewrite !lookup_empty in H. cbn in H. inversion H. lia.
Qed.
Lemma land_255 : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Read "@'8&Kzr1%3221'6&Jr2+WO%3221&M+X0%2251%83=41p0:1pS>?1").
Proof. intros x. intros. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma byte_of_0 : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Read "?'8&Kzr1%3221'6&9r2%2216&M+X0%2241%73<41p091pS>>1").
Proof. intros x. intros. unfold byte_of. rewrite Z.mul_0_r, Z.shiftr_0_r. apply land_255. lia. Qed.
Lemma byte_of_1 : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Read "B'8&Kzr1%3221'6&9r2+1%3221&M&I+X0%2261%4212%:3?61p0<1pS>A1").
Proof. intros x. intros. unfold byte_of. replace (8 * 1) with 8 by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. apply land_255. apply Z.div_pos; lia. Qed.
Lemma byte_of_2 : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Read "C'8&Kzr1%3221'6&9r2+2%3221&M&I+RPP0%2261+X0%5221%;3@71p0=1pS>B1").
Proof. intros x. intros. unfold byte_of. replace (8 * 2) with 16 by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 16) with 65536. apply land_255. apply Z.div_pos; lia. Qed.
Lemma byte_of_3 : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Read "C'8&Kzr1%3221'6&9r2+3%3221&M&I+`PPP0%2261+X0%5221%;3@71p0=1pS>B1").
Proof. intros x. intros. unfold byte_of. replace (8 * 3) with 24 by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 24) with 16777216. apply land_255. apply Z.div_pos; lia. Qed.
Lemma byte_of_range : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Read "C'8&Kzr2%3221'5&9r4r3%3221%9281&L+X0%2241%9241p0;1p0<1pR8A1pS>B1").
Proof. intros x k.
intros. unfold byte_of. rewrite land_255 by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_pos; [lia| apply Z.pow_pos_nonneg; lia]).
apply Z.mod_pos_bound. lia.
Qed.
Lemma u16_bytes : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Read "K'8'5&Kzr1%3221&L&O+2+@%3221%5271%;271'6&H&9r2%221>&N+X0+1%6251%4231%9261%;3H18p0=1pR>J1").
Proof. intros q. intros. rewrite byte_of_0, byte_of_1 by lia. rewrite (Z.mod_small (q / 256)) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]). pose proof (Z.div_mod q 256 ltac:(lia)). lia. Qed.
Lemma u32_bytes : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Read "Q4'8'5&Kzr1%3221&L&O+2+Q0%3221%5271%;271'6&H&9r2%221>&N+X0+1%6251%4231%9261+RPP0%:29A%8221%=241+`PPP0+3%?2>1%=231%B251%D3Q11Ap0F1pR@Q31").
Proof. intros r.
intros. rewrite byte_of_0, byte_of_1, byte_of_2, byte_of_3 by lia.
pose proof (Z.div_mod r 256 ltac:(lia)) as E1.
pose proof (Z.div_mod (r / 256) 256 ltac:(lia)) as E2. rewrite (Z.div_div r 256 256) in E2 by lia. change (256 * 256) with 65536 in E2.
pose proof (Z.div_mod (r / 65536) 256 ltac:(lia)) as E3. rewrite (Z.div_div r 65536 256) in E3 by lia. change (65536 * 256) with 16777216 in E3.
rewrite (Z.mod_small (r / 16777216)) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
lia.
Qed.
Lemma land31_idx : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Read "H'8'5&Kzr2%3221+O%5231%7231'6&J&Hr4&N+Q0r3%3221%6251%821<%:3C17p0?1p0=1pR@F1pR6G1").
Proof. intros i r.
intros. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. change (2 ^ 5) with 32.
replace (i + 32 * r) with (i + r * 32) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma shiftr5_res : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Read "I'8'5&Kzr2%3221+O%5231%7231'6&Q0&Hr4&N+Q0r3%3221%6251+5%9221%;3D15p0@1p0>1pR@G1pR6H1").
Proof. intros i r.
intros. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32.
replace (i + 32 * r) with (r * 32 + i) by lia. rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
Qed.
Lemma area_of_mslot : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Read "Q0'3'7'8%3221'6&M&4r2%23761&>%5221z%83:21'5&K%1248&L&=%22;1%6241&?&@&;r4r3%3221%511%G3714p091p0A1pR8L1pR4L1").
Proof. intros a k.
intros Ha Hk. unfold area_of, mslot, aadd, AREA_HDR, META_SIZE, NSLOTS, PGSZ in *. destruct a as [r o]; cbn in *. f_equal.
rewrite <- Zplus_mod_idemp_l, Ha. cbn [Z.add]. rewrite Z.mod_small by lia. lia.
Qed.
Lemma mod_pg_mod16 : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Read ">'8'6&Mr1&>%3221z%63721r2+@%8221%:3;15p051pS>=1").
Proof. intros x. intros H. unfold PGSZ in H. pose proof (Z.div_mod x 4096 ltac:(lia)). rewrite H in H0.
rewrite H0. replace (4096 * (x / 4096) + 0) with ((256 * (x / 4096)) * 16) by lia. apply Z_mod_mult. Qed.
Lemma mslot_mod8 : ltac2:(TCodec.tc2 tcn__CJ_Spec_MI_Read "G'3'7'8%3221'6&M&4r2%23761&>%5221z%83:21&;r3%2218%:3?>1+8%=221%?3A18p081pR8C1pR4C1").
Proof. intros a k.
intros Ha. unfold mslot, aadd, AREA_HDR, META_SIZE. cbn [snd].
pose proof (Z.div_mod (snd a) 4096 ltac:(lia)). unfold PGSZ in Ha. rewrite Ha in H.
rewrite H. replace (4096 * (snd a / 4096) + 0 + (24 + 40 * k)) with ((512 * (snd a / 4096) + 3 + 5 * k) * 8) by lia. apply Z_mod_mult.
Qed.
End CEIL_WRAP_1.
