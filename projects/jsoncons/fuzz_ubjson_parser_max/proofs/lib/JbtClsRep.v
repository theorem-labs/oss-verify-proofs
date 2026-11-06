(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim StoreOk As0Tables ArtMem JbtInitCache JbtPopulate1 ArtRuns JbtCls JbtFp.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtClsRep () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.As0Tables.AsanTab."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtCls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtFp."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1length"; "1list"; "1nat"; "1nil"; "1option"; "1prod"; "2and"; "2eq"; "2ex"; "3le"; "3lt"; "4nth"; "5Z"; "0M"; "0M'"; "6cell"]; ["7class_size"; "8art_carved"; "8art_cls"; "8art_cls_mfa'"; "8art_cls_new"; "8art_cls_ok"; "8art_cls_populate"; "8art_cls_take"; "8art_cptr_ok"; "8art_refill_n"; "8art_region_rep"; "8cl_au"; "8cl_cache"; "8cl_free"; "8cl_mfa"; "8cl_mu"]; ["8cl_na"; "8cl_nfr"; "9art_agree"; "9art_gap"; ":mem_grows"; ";loaded_segments"; "<In"; "=add"; "=div"; "=le"; "=lt"; "=modulo"; "=mul"; "=of_nat"; "=pow"; "0W"]; ["0au"; "0au'"; "0c"; "0cl"; "0cl'"; "0fa"; "0i"; "0j"; "0k"; "0mx"; "0mx'"; "0n"; "0new"; "0r"; "0ris"; "0spb"]; [">bv"; "0sz"; "0w"]]).
Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
Section SE.
Local Abbreviation SEC_T_art_refill_need := (ltac2:(TCodec.tc2 tcn__JbtClsRep "M'<'6&Q9+1r1%3221+N%5231%7231&Q<&@r2%211&Q=&I%114%311%8251+RPP0%A221'9u1%2217u8%4291%H231%I271p0C1pS6L1")) (only parsing).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_refill_need) 0%nat 0%nat).
Lemma art_refill_need : ltac:(sec_stmt2 constr:(SEC_T_art_refill_need) 1%nat 0%nat).
Proof.
intros Hc.
assert (H : forall x, In x (map (fun i => Z.of_nat i) (seq 1 30)) -> AsanTab.class_size x * Z.of_nat (art_refill_n x) <= 65536 /\ (1 <= art_refill_n x <= 8)%nat).
{ intros x Hx. cbn [map seq In] in Hx. repeat (destruct Hx as [<-|Hx]; [vm_compute; split; [discriminate|split; apply Nat.leb_le; reflexivity]|]). destruct Hx. }
apply H. apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
Qed.
End SE.
Lemma art_cptr_lt : ltac2:(TCodec.tc2 tcn__JbtClsRep "J'<&Q:zr3%3221&Q9+S`PPPP0%2241&Hr5r4%33218'6%82;3&Q>+2+L%3221%A281%7261p091p0>1p0B1pT6G1pS2H1pT4I1").
Proof. intros sz au w Hsz Hau (H0 & H1 & _). lia. Qed.
Lemma art_cptr_mono : ltac2:(TCodec.tc2 tcn__JbtClsRep "A'<&Q9r3r2%3221&Hr5r4%33215r6%53138p031p081pT6=1pS4>1pS2?1pT4@1").
Proof. intros sz au au' w H (H0 & H1 & H2). repeat split; [exact H0|lia|exact H2]. Qed.
Lemma art_region_rep_upd : ltac2:(TCodec.tc2 tcn__JbtClsRep "UD'<'B'R0yR0%211'4y8%511%311p051'1'5%12<<%311&Q7r:&Q<r8&Q>+2+Q0%3221%6251%9281+S`PPPP0%;221+T0r9%<221%?2>1&Q9zr1%3221&Q:r2%F21:+R0%D2C1%5231r4%;2:1r5+M%J2I1%O231%<218+4&Q=&0&Mr;%211%42QE1%611%Q7281%J21<'7&N%118r<%311%53QN31&K%114r=%311%:3R331&O%114r>%311%?3R831&Q1%114r?%311%D3R=31'9%M14%O2R@1r@%Q011%Q22RC1%6241'2&:rA%Q611%Q82RI1%42QJ1&;rB%Q;11%34RNQK1QOrC%Q>11%64S1QN1R2%Q93S241p091pS@?1&JrGrFrErD%564321>I&Q4%12EK&Q2%13MBG&Q3+H%S32Q61+Q8%43L21+R@%S72Q41+8%83K21%R61A%R82SI1%R:11%S;2R<1%=3MQ01&?&Q5u8rI%453IQ521+@%SE2Q41rH%RC11%RE2T61%RG11%;5:Q1591+R8%SL2Q11&Q0%11<%@5?Q73>1rQ0rOrNrLrJ%Q>654321?p071p0=1p0E1p0K1p0Q11p0Q61p0Q<1p0Q?1p0QB1p0QI1p0R:1p0RB1p0RH1p0RN1p0S41p0S;1p0SF1p0SL1p0SO1p0T61tSLU8T;1tS<U9T@1pS0TM1pNU21pLU31pS:U<1pS8U=1pSFU?1pSDU@1pS6UA1pSNUB1pT0UC1").
Proof.
intros spb ris c mx mx' cl cl' M M' W fa r Hr Hr' Hfa Hfa' Hnf Emfa Eau Emu Enfr Hlen Hnth RR G A G24 G80 GFA Cmx Cnf Cna.
destruct RR as (Rmx & Rnf & Rmfa & Rau & Ram & Rmu & Rmm & Rna & Rnfr & Rfa & Wr & Wfa & Wu).
fold r in Rmx, Rnf, Rmfa, Rau, Ram, Rmu, Rmm, Rna, Rnfr, Wr. fold fa in Rfa, Wfa.
unfold art_region_rep. fold r fa. rewrite Emfa, Eau, Emu, Enfr.
assert (T : forall a (n : nat) v, r + 24 <= a -> a + Z.of_nat n <= r + 64 -> cellA M a n v -> cellA M' a n v).
{ intros a n v Ha Hn C. apply (art_cell_tr W M M'); [exact A|eapply art_gap_sub; [exact G24|lia|lia]|lia|lia|exact C]. }
split; [exact Cmx|]. split; [exact Cnf|].
split; [apply T; [lia|cbn; lia|exact Rmfa]|]. split; [apply T; [lia|cbn; lia|exact Rau]|]. split; [apply T; [lia|cbn; lia|exact Ram]|].
split; [apply T; [lia|cbn; lia|exact Rmu]|]. split; [apply T; [lia|cbn; lia|exact Rmm]|].
split; [exact Cna|].
split. { apply (art_cell_tr W M M'); [exact A|exact G80|lia|cbn; lia|exact Rnfr]. }
split. { intros j Hj. rewrite (Hnth j Hj). pose proof (proj1 (Nat2Z.inj_lt _ _) Hj) as Hj'. pose proof (proj1 (Nat2Z.inj_le _ _) Hlen) as Hl'.
apply (art_cell_tr W M M'); [exact A|eapply art_gap_sub; [exact GFA|lia|cbn; lia]|lia|cbn; lia|apply Rfa; lia]. }
split; [eapply wr_grows; [exact G|exact Wr]|]. split; [eapply wr_grows; [exact G|exact Wfa]|eapply wr_grows; [exact G|exact Wu]].
Qed.
Lemma art_NoDup_map_in : forall (A B : Type) (f : A -> B) (l : list A),
List.NoDup l -> (forall x y, In x l -> In y l -> f x = f y -> x = y) -> List.NoDup (map f l).
Proof.
intros A B f l H. induction H as [|a l Hna Hnd IH]; intros Inj; cbn; [constructor|]. constructor.
- intros Hin. apply in_map_iff in Hin. destruct Hin as (y & Ey & Hy). apply Hna. rewrite (Inj a y (or_introl eq_refl) (or_intror Hy) (eq_sym Ey)). exact Hy.
- apply IH. intros x y Hx Hy. apply Inj; right; assumption.
Qed.
Lemma art_carved_in : ltac2:(TCodec.tc2 tcn__JbtClsRep "Q7'<'2&Q6r1&Ar4r3r2%43321%73961'8'6&Q9z%221;&Q:&Q=%11<%32?1%8251'7&Q8&Q7r6&Q<r5%22G1%5241+@%8221%:3NH1%D2<1qS>Q01%G2Q11p0I1pT6Q31pSJQ31pT4Q51pS2Q61").
Proof.
intros au sz new w H. unfold art_carved in H. apply in_map_iff in H. destruct H as (k & E & Hk). apply in_seq in Hk.
exists (Z.of_nat new - 1 - Z.of_nat k). split; [lia|]. symmetry. exact E.
Qed.
Lemma art_div16_mul : ltac2:(TCodec.tc2 tcn__JbtClsRep "B'<'7&Q;r2+@%3221z%63721&Q<&Q8r3%3218%3218%5219%=3>13p081pSB@1pT4A1").
Proof.
intros sz k H. assert (E : sz = 16 * (sz / 16)). { pose proof (Z.div_mod sz 16 ltac:(lia)) as D. rewrite H in D. lia. }
rewrite E at 1. replace (16 * (sz / 16) * k) with ((sz / 16 * k) * 16) by lia. rewrite Z_div_mult by lia. rewrite E at 2. lia.
Qed.
Section SE.
Local Abbreviation SEC_T_art_cls_ok_populate := (ltac2:(TCodec.tc2 tcn__JbtClsRep "Q='<'B'6&Q9+1r2%3221+N%5231%7231&Er3%2217&Q7&O%114+XPP0%4221+S`PPPP0%@221&Cr4&Q=&0&M%114%32J1%511&Dr5%2219%B241%<2;1+`PPPP0%O221r6&F%1228%L231p051p0E1p0M1p0Q11pS8Q:1pS6Q<1")) (only parsing).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_cls_ok_populate) 0%nat 0%nat).
Variable cl : ltac:(sec_ty2 constr:(SEC_T_art_cls_ok_populate) 1%nat 0%nat).
Lemma art_cls_ok_populate : ltac:(sec_stmt2 constr:(SEC_T_art_cls_ok_populate) 2%nat 0%nat).
Proof.
intros Hc OK Room1 Room2.
destruct OK as (Hlc & (Hau0 & Haumu) & Hrem0 & (km & Emu) & (ka & Eau) & Hmu3 & (kf & Emfa) & (Hmfa0 & Hmfa1) & Hnf4 & Hfor & Hnd).
destruct (art_class_size_facts c Hc) as (Hsz & Hsz16).
set (sz := AsanTab.class_size c) in *. set (nf := Z.of_nat (length (cl_free cl))) in *.
set (new := art_cls_new c cl) in *.
assert (Enew : cl_mu cl + 262144 - cl_au cl = sz * new + (cl_mu cl + 262144 - cl_au cl) mod sz) by (unfold new, art_cls_new; fold sz; apply Z.div_mod; lia).
pose proof (Z.mod_pos_bound (cl_mu cl + 262144 - cl_au cl) sz ltac:(lia)) as Hrem.
set (rem := (cl_mu cl + 262144 - cl_au cl) mod sz) in *.
assert (Hnew : 1 <= new). { destruct (Z_lt_le_dec new 1) as [Lt|Ge]; [|exact Ge]. exfalso. assert (sz * new <= 0) by nia. lia. }
assert (Hka : 0 <= ka) by nia.
unfold art_cls_ok, art_cls_populate. cbn [cl_cache cl_free cl_au cl_mu cl_mfa]. fold sz nf new.
assert (Elen : Z.of_nat (length (cl_free cl ++ art_carved (cl_au cl) sz (Z.to_nat new))) = nf + new).
{ rewrite length_app, art_carved_length, Nat2Z.inj_add, Z2Nat.id by lia. reflexivity. }
split; [exact Hlc|]. split; [nia|]. split; [nia|].
split; [exists (km + 1); lia|]. split; [exists (ka + new); nia|]. split; [exact Room1|].
split. { unfold art_cls_mfa'. destruct (4 * (nf + new) <=? cl_mfa cl); [exists kf; exact Emfa|]. exists ((4 * (nf + new) + 262143) / 262144). lia. }
split. { split; [|exact Room2]. unfold art_cls_mfa'. destruct (4 * (nf + new) <=? cl_mfa cl); [exact Hmfa0|].
assert (0 <= (4 * (nf + new) + 262143) / 262144) by (apply Z.div_pos; unfold nf; lia). lia. }
split. { rewrite Elen. unfold art_cls_mfa'. destruct (4 * (nf + new) <=? cl_mfa cl) eqn:E; [apply Z.leb_le in E; exact E|].
pose proof (Z.div_mod (4 * (nf + new) + 262143) 262144 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (4 * (nf + new) + 262143) 262144 ltac:(lia)) as R. lia. }
assert (Hcar : forall w, In w (art_carved (cl_au cl) sz (Z.to_nat new)) -> exists i, 0 <= i < new /\ 16 * w = sz * (ka + i)).
{ intros w Hw. apply art_carved_in in Hw. destruct Hw as (i & Hi & Ew). rewrite Z2Nat.id in Hi by lia. exists i. split; [exact Hi|].
rewrite Ew, Eau. replace (sz * ka + i * sz) with (sz * (ka + i)) by lia. pose proof (art_div16_mul sz (ka + i) Hsz16). lia. }
split.
{ rewrite app_assoc. apply Forall_app. split.
- eapply Forall_impl; [|exact Hfor]. intros w Hw. eapply art_cptr_mono; [|exact Hw]. nia.
- apply Forall_forall. intros w Hw. destruct (Hcar w Hw) as (i & Hi & Ew). unfold art_cptr_ok. split; [nia|]. split; [nia|]. exists (ka + i). exact Ew. }
rewrite app_assoc. apply NoDup_ListNoDup. apply NoDup_ListNoDup in Hnd. apply List.NoDup_app; [exact Hnd| |].
- unfold art_carved. apply art_NoDup_map_in; [apply seq_NoDup|]. intros x y Hx Hy E. apply in_seq in Hx. apply in_seq in Hy.
assert (Ex : ((cl_au cl + (Z.of_nat (Z.to_nat new) - 1 - Z.of_nat x) * sz) / 16) * 16 = sz * (ka + (new - 1 - Z.of_nat x))).
{ rewrite Z2Nat.id by lia. rewrite Eau. replace (sz * ka + (new - 1 - Z.of_nat x) * sz) with (sz * (ka + (new - 1 - Z.of_nat x))) by lia. apply art_div16_mul. exact Hsz16. }
assert (Ey : ((cl_au cl + (Z.of_nat (Z.to_nat new) - 1 - Z.of_nat y) * sz) / 16) * 16 = sz * (ka + (new - 1 - Z.of_nat y))).
{ rewrite Z2Nat.id by lia. rewrite Eau. replace (sz * ka + (new - 1 - Z.of_nat y) * sz) with (sz * (ka + (new - 1 - Z.of_nat y))) by lia. apply art_div16_mul. exact Hsz16. }
rewrite E in Ex. rewrite Ex in Ey. assert (ka + (new - 1 - Z.of_nat x) = ka + (new - 1 - Z.of_nat y)) by (apply (Z.mul_reg_l _ _ sz); lia). lia.
- intros w Hw Hw'. destruct (Hcar w Hw') as (i & Hi & Ew).
pose proof (proj1 (Forall_forall _ _) Hfor w Hw) as (W0 & W1 & _). nia.
Qed.
End SE.
Lemma art_cls_ok_take : ltac2:(TCodec.tc2 tcn__JbtClsRep "Q5'<'B'2&Er3r2%3221'7'1%119&L%117(3%11=%73531'9&0&Mr4%211%42D1%62A1u@%8251r7&Gr5r6%3221%J251p071p0:1p0B1p0K1pSHQ01pS8Q21pS6Q41").
Proof.
intros c cl n OK Ec Hn Hn16.
destruct OK as (Hlc & Hau & Hrem0 & Hmu & Hau' & Hmu3 & Hmfa & Hmfa' & Hnf4 & Hfor & Hnd).
rewrite Ec in Hfor, Hnd. cbn [app] in Hfor, Hnd.
unfold art_cls_ok, art_cls_take. cbn [cl_cache cl_free cl_au cl_mu cl_mfa].
set (k := (length (cl_free cl) - n)%nat).
assert (P : Permutation (cl_free cl) (skipn k (cl_free cl) ++ firstn k (cl_free cl))).
{ rewrite <- (firstn_skipn k (cl_free cl)) at 1. apply Permutation_app_comm. }
split; [rewrite length_skipn; unfold k; lia|]. split; [exact Hau|]. split; [exact Hrem0|]. split; [exact Hmu|]. split; [exact Hau'|]. split; [exact Hmu3|].
split; [exact Hmfa|]. split; [exact Hmfa'|].
split. { rewrite length_firstn. lia. }
split. { eapply Permutation_Forall; [exact P|exact Hfor]. }
apply NoDup_ListNoDup. apply NoDup_ListNoDup in Hnd. eapply Permutation_NoDup; [exact P|exact Hnd].
Qed.
