(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import HeapIfaceAJx PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA
AsanAcct AsanAcctShape AxSymExec3 AxSymExec3Sound AsanPlanSoundSums SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsAB0 L5CoreAB0.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__asan_L5StepARB0 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Init.Specif."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5DefsAB0.L5A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5KnA.L5KA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5CoreAB0.L5CA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5StepARB0.L5SAR."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.asan.L5StepARB0.L5SAR.SCFG_1.WithIface."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."], [["0A"; "0A'"; "0B"; "0BX"; "1None"; "1S"; "1Some"; "1app"; "1bool"; "1cons"; "1false"; "1fst"; "1length"; "1list"; "1nat"; "1nil"]; ["1option"; "1pair"; "1prod"; "1snd"; "1true"; "2I"; "2and"; "2eq"; "2ex"; "2not"; "2or"; "3add"; "3mul"; "4le"; "4lt"; "5sumbool"]; ["6Forall"; "6map"; "7Z"; "0D"; "0F"; "0FF"; "0FF'"; "0FX"; "0H"; "0H2"; "0HI"; "0K"; "0L"; "0LB"; "0LB'"; "0LK"]; ["0LK'"; "8Model"; "9bvmap"; "0M"; "0M'"; "0M1"; "0M1v"; "0M2"; "0M3"; "0MV2"; "0P"; "0R"; "0R'"; "0R1"; "0R2"; "0R3"]; [":H_off_segments"; ":mrestrict"; ";msteps"; "<blocks_apart"; "<credit"; "<defined"; "<regs_preserved"; "=FS_BYTES"; "=S"; "=SB"; "=ablock_range"; "=aclient"; "=aclientw"; "=aheap_pres"; "=ahid"; "=app_mem"]; ["=app_rng"; "=ar_fs"; "=ar_sptop"; "=astack_ok"; "=block_shadow"; "=cell_is"; "=ff_addr"; "=ff_bytes"; "=ff_count"; "=fframe"; "=fframes_apart"; "=in_shadow_of"; "=model_rt"; "=ri_inv"; "=shadow_zero"; "=vml"]; ["=vml_of"; "?defined"; "?limbs_at"; "?outside"; "?range"; "?u64_at"; "?u8_at"; "?writable"; ">SCFG"; "@avis"; "@cfg"; "Azeros_at"; "BFPState"; "Bgetr"; "Bmkst"; "Brdn"]; ["Bseg_rom"; "CTSet"; "Dsrealizes"; "Emem_grows"; "Fahpres"; "Famodel_ok"; "Faobj"; "Fastk"; "Fffr"; "Fffrs"; "Hdk"; "Hek"; "Gcs_all"; "Glimb_bytes"; "Iloaded_segments"; "0SCFG_P"]; ["JIn"; "Jincl"; "Jnth_error"; "Kadd"; "Kdiv"; "Kland"; "Kle"; "Klor"; "Klt"; "Kmodulo"; "Kmul"; "Kof_nat"; "Kpow"; "Ksub"; "Ktestbit"; "0V"]; ["0W"; "0W'"; "0a"; "0ar"; "0b"; "0bs"; "0cr"; "0cr'"; "0d"; "0d'"; "0dst"; "0f"; "0f0"; "0fb"; "0fb'"; "0fl"]; ["0fr"; "0fx"; "0fx1"; "0hi"; "0i"; "0k"; "0l"; "0l'"; "0l1"; "0l2"; "0lo"; "0m"; "0model"; "0model'"; "0model1"; "0model2"]; ["0n"; "0o"; "0p"; "0pc"; "0pc1"; "0q"; "0rs"; "0rs'"; "0scr"; "0scr'"; "0sp"; "0sp'"; "LNoDup"; "MBV"; "MZ_to_bv"; "Mbv"]; ["0sz"; "0w"; "0ws"; "0x"]]).
Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Module L5SAR.
Import L5A. Import L5CA.
Ltac keep_arith := lazymatch goal with |- _ => L5FastLia.prune_arith end.
Ltac clear_disj_but H := repeat match goal with H' : _ \/ _ |- _ => tryif constr_eq H' H then fail else clear H' end.
Ltac alia0 := first [ lia | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Ltac alia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia | alia0 ].
Ltac feed_concl T := lazymatch T with ?A -> ?B => feed_concl B | _ => T end.
Ltac feed P tac :=
let T := type of P in
lazymatch T with
| ?A0 -> _ =>
let C := feed_concl T in
let Q := fresh "SC" in
assert (Q : C) by (apply P; clear P; first [ tac | lazymatch goal with |- ?A => fail 1 "feed: cannot prove premise" A end ]);
move Q after P; clear P; rename Q into P
| _ => idtac
end.
Ltac greg :=
lazymatch goal with |- getr ?R ?x = ?rhs =>
match goal with H : getr R ?y = ?rhs' |- _ =>
first [ constr_eq x y | replace x with y by (apply bv_eq; vm_compute; reflexivity) ];
first [ exact H
| lazymatch rhs with Z_to_bv 64 ?z => lazymatch rhs' with Z_to_bv 64 ?z' => replace z with z' by (clear; lia); exact H end end ]
end
end.
Ltac gmem :=
lazymatch goal with
| |- L5.u64_at ?sg ?M ?a ?v => match goal with H : L5.u64_at sg M ?b ?v' |- _ => first [constr_eq a b | replace a with b by (clear; lia)]; first [exact H | replace v with v' by (clear; lia); exact H] end
| |- L5.u32_at ?sg ?M ?a ?v => match goal with H : L5.u32_at sg M ?b ?v' |- _ => first [constr_eq a b | replace a with b by (clear; lia)]; first [exact H | replace v with v' by (clear; lia); exact H] end
| |- L5.u8_at ?sg ?M ?a ?v => match goal with H : L5.u8_at sg M ?b ?v' |- _ => first [constr_eq a b | replace a with b by (clear; lia)]; first [exact H | replace v with v' by (clear; lia); exact H] end
| |- L5.defined ?M ?a ?n => match goal with H : L5.defined M ?b ?m |- _ => apply (L5.defined_sub M b m a n H); clear; lia end
| |- L5.writable ?sg ?M ?a ?n => match goal with H : L5.writable sg M ?b ?m |- _ => apply (L5.writable_sub sg M b m a n H); clear; lia end
| |- L5KA.zeros_at ?M ?a ?n => match goal with H : L5KA.zeros_at M ?b ?m |- _ => apply (L5KA.zeros_at_sub M b m a n H); clear; lia end
| |- L5.img_clear ?M _ _ => match goal with H : L5.img_clear M _ _ |- _ => exact H end
end.
Ltac arith_shape :=
lazymatch goal with
| |- (_ <= _)%Z => idtac | |- (_ < _)%Z => idtac | |- (_ <= _ <= _)%Z => idtac | |- (_ <= _ < _)%Z => idtac | |- (_ < _ <= _)%Z => idtac | |- (_ < _ < _)%Z => idtac
| |- @eq Z _ _ => idtac | |- (_ \/ _) => idtac | |- (~ _)%type => idtac | |- (_ /\ _) => idtac
| |- le _ _ => idtac | |- lt _ _ => idtac | |- @eq nat _ _ => idtac
end.
Ltac arith_goal := first [ arith_shape | red; arith_shape ].
Ltac sc0 := first [ assumption | greg | gmem | arith_goal; first [assumption | alia] ].
Ltac xfer AG C :=
first [ eapply L5C.u64_at_agree; [intros ? ?; apply AG; alia | alia | alia | exact C]
| eapply L5C.u8_at_agree; [intros ? ?; apply AG; alia | alia | alia | exact C]
| eapply L5KA.zeros_at_agree1; [intros ? ?; apply AG; alia | exact C]
| eapply L5C.defined_agree; [intros ? ?; apply AG; alia | exact C] ].
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)).
Lemma r1 : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "?'G'UOy5%211(UM+1(E%33521/015&UN&T;u1%211%42;1%>3;61"). Proof. apply bv_eq; reflexivity. Qed.
Lemma r2 : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "?'G'UOy5%211(UM+2(E%33521/015&UN&T;u2%211%42;1%>3;61"). Proof. apply bv_eq; reflexivity. Qed.
Lemma r4 : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "?'G'UOy5%211(UM+4(E%33521/015&UN&T;u4%211%42;1%>3;61"). Proof. apply bv_eq; reflexivity. Qed.
Lemma r10 : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "?'G'UOy5%211(UM+:(E%33521/015&UN&T;u:%211%42;1%>3;61"). Proof. apply bv_eq; reflexivity. Qed.
Lemma r11 : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "?'G'UOy5%211(UM+;(E%33521/015&UN&T;u;%211%42;1%>3;61"). Proof. apply bv_eq; reflexivity. Qed.
Lemma r12 : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "?'G'UOy5%211(UM+<(E%33521/015&UN&T;u<%211%42;1%>3;61"). Proof. apply bv_eq; reflexivity. Qed.
Lemma rng_dec : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "A'Q2'O'F&T6r2r3%3221&T8r1%2241%8241&I%112%<231pZ8>1pZF?1pY6@1").
Proof. intros a lo hi. destruct (Z_lt_le_dec a lo); [right; lia|]. destruct (Z_lt_le_dec a hi); [left; lia | right; lia]. Qed.
Definition cs_all : list nat := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Lemma preserved_by_index : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "N&QBy5'UOyR0%211%5241'>&T0r1&SL%33421'G&S=r3&UN&T;r2%211%42A1%7261r4%9213%;3B31p0=1pZ<B1&R6%12=:p031pSJG1pSHH1").
Proof. intros R R'.
intros KR x Hx. rewrite <- (AX2S.ridx_roundtrip x). apply KR.
unfold callee_saved_idx in Hx. unfold AX2.ridx. set (z := bv_unsigned x) in *. cbn in Hx.
repeat (destruct Hx as [Hx|Hx]; [rewrite <- Hx; cbn; tauto|]). destruct Hx.
Qed.
Lemma cs_of_preserved : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "N&QBy5'UOyR0%211%5241'>&R6r3r2%3221&T0&SL%23741'G&S=r4&UN&T;%11;%32C1%6251r5%8213%:3D31p0<1p0@1pZ<E1pSJG1pSHH1").
Proof. intros R R' k.
intros RP Hk. apply RP. unfold callee_saved_idx. cbn in Hk.
repeat (destruct Hk as [<-|Hk]; [cbn; tauto|]). destruct Hk.
Qed.
Lemma regs_preserved_trans : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "A&QBy5'UOyR0%211%5241&R6r3r2%3221r5%5214p031p041pT091pSN:1pSL;1").
Proof. intros R1 R2 R3. intros A B x Hx. rewrite (B x Hx). apply A. exact Hx. Qed.
Ltac rk :=
first [ reflexivity | greg
| match goal with K : forall x, In x _ -> getr ?Rb (reg x) = getr ?Ra (reg x) |- getr ?Rb' (Z_to_bv 5 (Z.of_nat ?k)) = _ =>
constr_eq Rb Rb'; rewrite (K k) by (apply L5K.in_b; vm_compute; reflexivity); rk end
| match goal with RP : regs_preserved ?Ra ?Rb |- getr ?Rb' (Z_to_bv 5 (Z.of_nat ?k)) = _ =>
constr_eq Rb Rb'; rewrite (cs_of_preserved Ra Rb k RP) by (apply L5K.in_b; vm_compute; reflexivity); rk end ].
Ltac sc := first [ assumption | rk | gmem | arith_goal; first [assumption | alia] ].
Lemma u64_of_zeros_at : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "Q3'UOyR0%211'@y8%511%311p051'Q2&S;r2r1+8%43321&T6z%2216&T3r3%2217&T<+2+R0%3221%:251&S5&SNr5r4%44321>p061p0?1p0C1pY6I1pS8K1").
Proof. intros M a.
intros Z8 Ha Hn. unfold L5.u64_at. change (word_to_le_bytes 8 (Z_to_bv 64 0)) with (repeat (Z_to_bv 8 0 : byte) 8).
apply APSX.rdn_overlay_all. rewrite L5.unsigned_lit by lia. cbn. lia.
intros i Hi. rewrite L5.unsigned_lit by lia. apply Z8. cbn in Hi. lia.
Qed.
Lemma reserve_flags : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "O'Q2'F&T6zr1%3221&T8+X0%2241%8241'G&T7&T5&T3&T:+4&T4r2%2213%5241+1%8221+WM%;221+2%=281%?231%@2:7%B3L21p0D1pYLN1").
Proof. intros fb.
intros H.
assert (E : forallb (fun k => Z.eqb (Z.lor (Z.land (4 * (Z.of_nat k / 4) + 1) 253) (Z.land (Z.of_nat k) 2)) (Z.lor (Z.of_nat k) 1)) (seq 0 256) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in E. specialize (E (Z.to_nat fb) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in E by lia. apply Z.eqb_eq. exact E.
Qed.
Lemma lor1_facts : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "J'Q2'F&T6zr1%3221&T8+X0%2241%8241&T7r2+1%3221%<2;1%9228%?221'G'8&T>%127A(D%53421%F271p0?1pYLI1").
Proof. intros fb.
intros H. split.
- assert (E : forallb (fun k => Z.ltb (Z.lor (Z.of_nat k) 1) 256 && Z.leb 0 (Z.lor (Z.of_nat k) 1))%bool (seq 0 256) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in E. specialize (E (Z.to_nat fb) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in E by lia. apply andb_prop in E. destruct E as [E1 E2].
apply Z.ltb_lt in E1. apply Z.leb_le in E2. lia.
- rewrite Z.lor_spec. rewrite Bool.orb_true_iff. right. reflexivity.
Qed.
Lemma rdn_overlay_list : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "QM'UOyR0%211'@y8%511%311p\851'=%114'Q2&T6zr1%3221&T3r2&T;&<r3%22?1%411%7261&T<+2+R0%3221%@251'>&Nr5%=2J1%32C1'Gr7&UN%C1D%F271%32Q51%511&T2r6%23Q51J%:3Q541p0<1pZ:A1%Q;1Q5&S?&SNr4%?2QA1%443:1D(6%12Q<G%E3831p0:1p0M1p0Q;1pY6Q@1pY<QB1pS8QE1").
Proof. intros M.
induction bs as [|b bs IH]; intros a Ha Hn Hall. reflexivity.
cbn [rdn length]. pose proof (Hall 0%nat ltac:(cbn; lia)) as H0. rewrite Z.add_0_r in H0. cbn [nth_error] in H0. rewrite H0.
cbn [length] in Hn.
replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)).
2:{ apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). change (bv_unsigned 1) with (1 mod 2 ^ 64).
rewrite <- Z.add_mod by lia. reflexivity. }
rewrite (IH (a + 1)). reflexivity. lia. lia. intros i Hi. replace (a + 1 + Z.of_nat i) with (a + Z.of_nat (Datatypes.S i)) by lia. apply (Hall (Datatypes.S i)). cbn; lia.
Qed.
Definition limb_bytes (ws : list Z) : list byte := flat_map (fun w => word_to_le_bytes 8 (Z_to_bv 64 w)) ws.
Lemma limb_bytes_length : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "C'='Q2%211'G'>&<'UOy8%211&SMr1%211%7241&Lu8%:2>5%3221%>3=51p\6@1").
Proof. intros ws. induction ws as [|w ws IH]. reflexivity. cbn [limb_bytes flat_map]. rewrite length_app, length_N_to_le_bytes. unfold limb_bytes in IH. rewrite IH. cbn [length]. lia. Qed.
Lemma rdn_of_limbs_at : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "QK'UOyR0%211'@y8%511%311p051'='Q2%211&S2&SNr3r1r2%544321&T6z%2214&T3&T:+8&T;&<r4%22A1%411%7261%92@1&T<+2+R0%3221%A251'G%L1O%Q211&S?r6&UN%12Q8@&Lu8r5%E2Q41%4231%94Q3861(6&SM%116%32?1%A3?51p0C1p0Q31p0Q71p[<Q?1p\6Q?1pS8QC1").
Proof. intros M.
induction ws as [|w ws IH]; intros q HL Hq Hn. reflexivity.
cbn [length] in Hn. replace (8 * length (w :: ws))%nat with (8 + 8 * length ws)%nat by (cbn [length]; lia).
change (limb_bytes (w :: ws)) with (word_to_le_bytes 8 (Z_to_bv 64 w) ++ limb_bytes ws).
apply SeqExec.rdn_app.
- pose proof (HL 0%nat ltac:(cbn; lia)) as H0. cbn [nth] in H0. unfold L5.u64_at in H0. rewrite Z.add_0_r in H0. exact H0.
- unfold nat_to_word.
replace (Z_to_bv 64 q + Z_to_bv 64 (Z.of_nat 8))%bv with (Z_to_bv 64 (q + 8)).
2: { apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite <- Z.add_mod by lia. reflexivity. }
apply IH. intros i Hi. replace (q + 8 + 8 * Z.of_nat i) with (q + 8 * Z.of_nat (Datatypes.S i)) by lia.
change (nth i ws 0) with (nth (Datatypes.S i) (w :: ws) 0). apply HL. cbn; lia. lia. lia.
Qed.
Lemma limbs_at_of_bytes : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "R0'UOyR0%211'@y8%511%311p\851'='Q2%211&T6zr1%3221&T3r2&T:+8&T;&<r3%22=1%411%7261%:291&T<+2+R0%3221%C251'>&N&Lu8r5%@2K1%4231%62I1'Gr7&UN%G1J%L281%32Q;1%511&T2&SMr6%211%43Q=1Q2%<3Q=61p0>1pZ:F1&S2&SNr4%34291Fp051p0M1p0Q>1pYFQD1p\6QD1pS8QH1").
Proof. intros M.
induction ws as [|w ws IH]; intros dst Hd Hn Hall i Hi. cbn in Hi; lia.
cbn [length] in Hn, Hi.
change (limb_bytes (w :: ws)) with (word_to_le_bytes 8 (Z_to_bv 64 w) ++ limb_bytes ws) in Hall.
destruct i as [|i].
- cbn [nth]. unfold L5.u64_at. rewrite Z.mul_0_r, Z.add_0_r. rewrite <- (length_N_to_le_bytes 8 (Z_to_bv 64 w)) at 1.
apply rdn_overlay_list. exact Hd. rewrite length_N_to_le_bytes. lia.
intros k Hk. rewrite length_N_to_le_bytes in Hk. rewrite (Hall k ltac:(cbn [length]; lia)). rewrite nth_error_app1. reflexivity. rewrite length_N_to_le_bytes. exact Hk.
- cbn [nth]. replace (dst + 8 * Z.of_nat (Datatypes.S i)) with (dst + 8 + 8 * Z.of_nat i) by lia. apply IH. lia. lia. 2: cbn in Hi |- *; lia.
intros k Hk. replace (dst + 8 + Z.of_nat k) with (dst + Z.of_nat (8 + k)) by lia. rewrite (Hall (8 + k)%nat ltac:(cbn [length]; lia)).
rewrite nth_error_app2. rewrite length_N_to_le_bytes. f_equal. lia. rewrite length_N_to_le_bytes. lia.
Qed.
Lemma defined_word : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "Q<'UOyR0%211'@y8%511%311p051'Q2&S1r2r1+8%43321&T6z%2216&T3r3%2217&T<+2+R0%3221%:251'H'F%=2<@&T8%12B6%4231&S5&SNr6r5%44321H%:261q\4M1%=2N1p0?1p0H1p0L1pY6Q21pS8Q41").
Proof. intros M a.
intros D Ha Hb.
set (f := fun x : Z => match M (Z_to_bv 64 x) with Some b => b | None => Z_to_bv 8 0 end).
set (bs := map (fun k => f (a + Z.of_nat k)) (seq 0 8)).
exists (bytes_le_to_Z bs).
assert (L: length bs = 8%nat) by reflexivity.
pose proof (AX2S.bytes_le_to_Z_bound bs) as B. rewrite L in B. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in B. split. exact B.
unfold L5.u64_at. rewrite (APSX.word_to_le_bytes_of_bytes_n 8 bs L ltac:(lia)). rewrite <- L at 1.
apply rdn_overlay_list. exact Ha. rewrite L; exact Hb. intros i Hi. rewrite L in Hi. unfold bs.
rewrite nth_error_map. rewrite (nth_error_nth' _ 0%nat) by (rewrite length_seq; exact Hi). rewrite seq_nth by exact Hi. cbn [option_map Nat.add]. unfold f.
destruct (M (Z_to_bv 64 (a + Z.of_nat i))) eqn:E. reflexivity. exfalso. apply (D (Z.of_nat i)). lia. exact E.
Qed.
Lemma limbs_of_defined : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "R0'UOyR0%211'@y8%511%311p051'Q2'>&S1r3r2&T:+8&T;r1%211%5241%93871&T6z%221;&T3r4%:1>%=2<1%4231&T<+2+R0%3221%<251'H'=%11K'F'G&<%12OGr5%43Q021'Q0%G2FK&T8%12M>%:231q\4Q71%63Q81Q0&S2&SNr7r6%44321Q5%B261%C2>1q\6E1%H2F1p0J1p0Q51p0Q91pZ<QD1p[<QF1pS8QH1").
Proof. intros M q.
induction k as [|k IH]; intros D Hq Hk.
- exists []. split. reflexivity. split. constructor. apply L5C.limbs_at_nil.
- destruct (IH ltac:(eapply L5.defined_sub; [exact D|lia|lia]) Hq ltac:(lia)) as (ws & Lw & Rw & LA).
destruct (defined_word M (q + 8 * Z.of_nat k) ltac:(eapply L5.defined_sub; [exact D|lia|lia]) ltac:(lia) ltac:(lia)) as (w & Rg & Uw).
exists (ws ++ [w]). split. rewrite length_app; cbn; lia. split. apply Forall_app; split; [exact Rw|constructor; [lia|constructor]].
apply L5C.limbs_at_app. exact LA. intros i Hi. cbn in Hi. destruct i; [|lia]. cbn [nth]. rewrite Lw.
replace (q + 8 * Z.of_nat k + 8 * Z.of_nat 0) with (q + 8 * Z.of_nat k) by lia. exact Uw.
Qed.
Lemma kland_byte : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "F'Q2&T6zr2%3221'F+WO%6241%3241&T5r4r3%3221%<2;1&T8+X0%2241%<241p0:1p0?1pZHD1pY6E1").
Proof. intros a m. intros Ha Hm. pose proof (L5K.land_le_r a m Ha ltac:(lia)). pose proof (Z.land_nonneg a m). lia. Qed.
Lemma klor_byte : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "E'Q2'F&T6zr2%3221&T8+X0%2241%8241&T7r4r3%3221%<2;1%9228%?221p081p091pY:C1pY6D1").
Proof. intros a b.
intros Ha Hb. split. apply Z.lor_nonneg; lia.
destruct (Z.eq_dec a 0) as [->|Na]. rewrite Z.lor_0_l. lia. destruct (Z.eq_dec b 0) as [->|Nb]. rewrite Z.lor_0_r. lia.
apply (Z.log2_lt_cancel). rewrite Z.log2_lor by lia.
apply Z.max_lub_lt; apply Z.log2_lt_pow2; try lia; change (2 ^ Z.log2 256) with 256; lia.
Qed.
Lemma signcopy_facts : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "Q1'Q2'F&T6zr2%3221&T8+X0%2241%8241&T7&T5r4+WM%3221r3+2%6221%8241%A2@1%>22=%D221'G'8&T>%127F%22>G%53421%K271p0D1p0E1pYNO1pYJQ01").
Proof. intros f0 fb'.
intros H0 H1. split.
- apply klor_byte; apply kland_byte; lia.
- rewrite Z.lor_spec, !Z.land_spec. change (Z.testbit 253 0) with true. change (Z.testbit 2 0) with false. rewrite Bool.andb_true_r, Bool.andb_false_r, Bool.orb_false_r. reflexivity.
Qed.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma aclient_mono {BS ST} LB FF sp scr sp' scr' a :
aclient_g BS ST L ar LB FF sp scr a -> (forall x, sp' - scr' <= x < sp' -> sp - scr <= x < sp) -> aclient_g BS ST L ar LB FF sp' scr' a.
Proof.
intros Hc Hs. destruct Hc as [Hc|[Hc|Hc]]. left; exact Hc. right; left. split. lia. intros X. apply (proj2 Hc). apply Hs. exact X. right; right; exact Hc.
Qed.
Lemma aclient_00 {BS ST} LB FF sp scr a : aclient_g BS ST L ar LB FF sp scr a -> aclient_g BS ST L ar LB FF 0 0 a.
Proof. intros Hc. eapply aclient_mono. exact Hc. intros x Hx. lia. Qed.
Lemma aclient_cons {BS ST} LB FF f sp scr a : aclient_g BS ST L ar LB FF sp scr a -> aclient_g BS ST L ar LB (f :: FF) sp scr a.
Proof.
intros Hc. destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]].
- left; exact Hc. - right; left; exact Hc. - right; right; left; exact Hc.
- right; right; right; left. destruct Hc as (g & Hg & X). exists g. split. right; exact Hg. exact X.
- right; right; right; right; left; exact Hc.
- right; right; right; right; right; left. destruct Hc as (g & Hg & X). exists g. split. right; exact Hg. exact X.
- right; right; right; right; right; right. exact Hc.
Qed.
Lemma aclient_consb {BS ST} LB FF b sp scr a : aclient_g BS ST L ar LB FF sp scr a -> aclient_g BS ST L ar (b :: LB) FF sp scr a.
Proof.
intros Hc. destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]].
- left. destruct Hc as (g & Hg & X). exists g. split. right; exact Hg. exact X.
- right; left; exact Hc. - right; right; left; exact Hc.
- right; right; right; left; exact Hc.
- right; right; right; right; left; exact Hc.
- right; right; right; right; right; left; exact Hc.
- right; right; right; right; right; right. destruct Hc as (g & Hg & X). exists g. split. right; exact Hg. exact X.
Qed.
Lemma aclient_app {BS ST} LB FF FX sp scr a : aclient_g BS ST L ar LB FF sp scr a -> aclient_g BS ST L ar LB (FX ++ FF) sp scr a.
Proof. intros Hc. induction FX as [|f FX IH]. exact Hc. cbn [app]. apply aclient_cons. exact IH. Qed.
Lemma aclient_appb {BS ST} LB BX FF sp scr a : aclient_g BS ST L ar LB FF sp scr a -> aclient_g BS ST L ar (BX ++ LB) FF sp scr a.
Proof. intros Hc. induction BX as [|b BX IH]. exact Hc. cbn [app]. apply aclient_consb. exact IH. Qed.
Lemma aclient_consb_inv : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "Q='='B'Q2%2211%411&RI%611&R;vQ<vTC(9r4r6%33:21r5r3r2r1%;7:954321'Jr7%>7=<19:65'F&T6&;%13GG;%321:&T8&T3&C%13LL@%3261%52@1%;271&RK%13:5C%A231%B2@1p0D1pY6Q51p[BQ61p[FQ71pY:Q71pR<Q51pRLQ81").
Proof. intros LB FF b sp scr a.
intros Hc. destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]].
- destruct Hc as (g & [<-|Hg] & X). right; left; exact X. left; left. exists g. split. exact Hg. exact X.
- left; right; left; exact Hc. - left; right; right; left; exact Hc. - left; right; right; right; left; exact Hc.
- left; right; right; right; right; left; exact Hc. - left; right; right; right; right; right; left; exact Hc.
- destruct Hc as (g & [<-|Hg] & X). right; right; exact X. left; right; right; right; right; right; right. exists g. split. exact Hg. exact X.
Qed.
Lemma aobj_cons : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "C'=&RI%211'Q2&SFr4r2r1%43321(9r5%23:61r3%93217p061p\2<1p[4=1pYH@1pR<@1").
Proof. intros FF f o sz. intros (g & Hg & X). exists g. split. right; exact Hg. exact X. Qed.
Lemma fframes_apart_incl : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "D'Q2'=&RI%211&RJr4r3r2%43321&T1%13834r6r5%93217p041p071pR>=1pR<>1p[2B1pY6C1").
Proof. intros a n FF FF'. intros H I f Hf. apply H. apply I. exact Hf. Qed.
Lemma fframes_apart_tl : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "C'Q2&RI'=%112&RJr4r3(9r2r1%33921%73651r5%93185p031pR<<1pYH?1p[2A1pY6B1").
Proof. intros a n f FF. intros H g Hg. apply H. right. exact Hg. Qed.
Lemma aclient_cases : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "R:'='B'Q2%2211%411&RI%611&R4'UOyR0%211'@y8%511%311p051&RO&RMvQ:r:r9r8r7r6r5r4%9887654321'F&T6+SoonPPPPP0&RBvTC%211%5241&T<+2+Q?%3221%:261%<261&R;vQ<r<r;r3%574>32ED1'J&T=+XPPP0%22A1%F21I&I%52ML%I21L&T8%12NQ0%M231%611%O281%52Q2:%>221p0@1p0G1p0Q51pY6QN1p[BQO1p[FR01pY0QC1pS8QE1p2R11pY>QO1pS0R11pR<R21pRLR51").
Proof. intros LB FF LK cr A M V sp scr a.
intros HH SPT Hc. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _).
destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]].
- right. destruct Hc as (b & Hb & X). pose proof (proj1 (WB b Hb)) as (_ & _ & _ & _ & Y & _). lia.
- left. split. lia. exact (proj2 Hc).
- right. rewrite (aly_img_hi L C LY) in Hc. lia.
- right. destruct Hc as (f & Hf & X). pose proof (WF f Hf) as (_ & Y & _). lia.
- right. unfold in_shadow_of, S, SB in Hc. lia.
- right. destruct Hc as (f & Hf & X). pose proof (WF f Hf) as (Y1 & Y & _). unfold in_shadow_of, S, SB in X. unfold app_mem in FSAPP. lia.
- right. destruct Hc as (b & Hb & X). pose proof (proj1 (WB b Hb)) as (Y0 & _ & _ & _ & Y & _). unfold in_shadow_of, S, SB in X. lia.
Qed.
Lemma fresh_frame_not_client : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "SO'='B'Q2%2211%411&RI%611&R4'UOyR0%211'@y8%511%311p051&RO&RMvQ:r<r;r:r9r8r7r6%9887654321'F&T6+SoonPPPPP0&RBvTC%211%5241&T<+2+Q?%3221%:261%<261+Vb\P0r5%>221&T3%12C3&T=+XPPP0%22?1%D241&R?%12JI'G&T9+8%22O1z%53QF21&T8%123Q3%72Q56%93QJ15&RJrC%23Q;Q:1&T0r1rF%33R021'Jr>r=%L221&;r2%23R8R81%Q?241&C%13R;R;4%Q3241%QC21:%<251p0>1pY:R?1%QG2=QO%Q92>R1%L2R11%QK231&R8%11B%QM21R5+1%Q>271%511%R12R91%R3251%K291&I&R;vQ<rGr@r?%574R73Q421RC%711p091p0G1p0Q;1p0Q?1p0QB1p0QE1p0QL1p0QO1p0R61p0R:1p0RH1pY6SA1p6SB1pR:SC1p[BSD1p[FSE1pY0S81pS8S:1p2SF1pY>SD1pS0SF1pR<SG1pRLSJ1").
Proof. intros LB FF LK cr A M V sp scr F B a.
intros HH SPT F1 F2 F3 F4 F5 F6 FA FB Ha Hc. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _).
unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in F3. unfold S, SB in Ha.
destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]].
- destruct Hc as (b & Hb & X). pose proof (proj1 (WB b Hb)) as (Y0 & _ & _ & _ & Y & Y2). unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Y2. specialize (FB b Hb). lia.
- lia.
- rewrite (aly_img_hi L C LY) in Hc. lia.
- destruct Hc as (f & Hf & X). pose proof (WF f Hf) as (Y1 & Y & _). specialize (FA f Hf). unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in FSAPP. lia.
- unfold in_shadow_of, S, SB in Hc. lia.
- destruct Hc as (f & Hf & X). pose proof (WF f Hf) as (Y1 & Y & Y3 & Y4 & _). specialize (FA f Hf). unfold in_shadow_of, S, SB in X.
assert (Y5 : ff_addr f mod 8 = 0 /\ ff_bytes (ff_class f) mod 8 = 0 /\ 0 < ff_bytes (ff_class f)).
{ destruct Y4 as [E|[E|[E|[E|[E|[]]]]]]; rewrite <- E in Y3 |- *;
[change (ff_bytes 0) with (8 * 8) in Y3 |- * | change (ff_bytes 1) with (16 * 8) in Y3 |- * | change (ff_bytes 2) with (32 * 8) in Y3 |- * | change (ff_bytes 3) with (64 * 8) in Y3 |- * | change (ff_bytes 4) with (128 * 8) in Y3 |- *];
(split; [|split; [apply Z_mod_mult|lia]]); apply Z.mod_divide in Y3; try lia; destruct Y3 as [k Hk]; rewrite Hk; rewrite Z.mul_assoc; apply Z_mod_mult. }
destruct Y5 as (Y5 & Y6 & Y7). unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in FSAPP. lia.
- destruct Hc as (b & Hb & X). pose proof (proj1 (WB b Hb)) as (Y0 & _ & Y1 & _ & Y & Y2). specialize (FB b Hb). unfold in_shadow_of, S, SB in X.
unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Y2. assert (Y5 : fst b mod 8 = 0) by (clear - Y1; apply Z.mod_divide in Y1; [|lia]; destruct Y1 as [k ->]; replace (k * 16) with ((2 * k) * 8) by lia; apply Z_mod_mult). lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma aclientw_not_bshadow : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "QC'='B'Q2%2211%411&RI%611&R4'UOyR0%211'@y8%511%311p051&RO&RMvQ:r:r9r8r7r6r5r4%9887654321&R<vQ<vTCr;r3r2%67543>821&I&RDr<%2216%411p061p0>1pY6Q71p[BQ81p[FQ91pY0L1pS8N1p2Q:1pY>Q81pS0Q:1pR<Q;1pRLQ>1").
Proof. intros LB FF LK cr A M V sp scr a.
intros HH Hc (b' & Hb' & X'). pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & (_ & _ & SPT & SP16) & _).
destruct (WB b' Hb') as ((Q0 & _ & Q16 & Q3 & Q4 & Q5) & _ & _ & _ & _ & QFA & _). unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Q5.
unfold in_shadow_of, S, SB in X'. unfold app_mem, FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in FSAPP.
destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]].
- destruct Hc as (b & Hb & X). pose proof (proj1 (WB b Hb)) as (Y0 & _ & _ & _ & Y & Y2). unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Y2. lia.
- lia.
- rewrite (aly_img_hi L C LY) in Hc. lia.
- destruct Hc as (f & Hf & X). pose proof (WF f Hf) as (Y1 & Y & _). unfold FS_BYTES in Y. lia.
- unfold in_shadow_of, S, SB in Hc. lia.
- destruct Hc as (f & Hf & X). pose proof (WF f Hf) as (Y1 & Y & Y3 & Y4 & _). specialize (QFA f ltac:(apply in_or_app; left; exact Hf)). unfold in_shadow_of, S, SB in X.
assert (Y5 : ff_addr f mod 8 = 0 /\ ff_bytes (ff_class f) mod 8 = 0 /\ 0 < ff_bytes (ff_class f)).
{ destruct Y4 as [E|[E|[E|[E|[E|[]]]]]]; rewrite <- E in Y3 |- *;
[change (ff_bytes 0) with (8 * 8) in Y3 |- * | change (ff_bytes 1) with (16 * 8) in Y3 |- * | change (ff_bytes 2) with (32 * 8) in Y3 |- * | change (ff_bytes 3) with (64 * 8) in Y3 |- * | change (ff_bytes 4) with (128 * 8) in Y3 |- *];
(split; [|split; [apply Z_mod_mult|lia]]); apply Z.mod_divide in Y3; try lia; destruct Y3 as [k Hk]; rewrite Hk; rewrite Z.mul_assoc; apply Z_mod_mult. }
destruct Y5 as (Y5 & Y6 & Y7). lia.
- destruct Hc as (b & _ & []).
Qed.
Lemma aclientw_of_client : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "R4'='B'Q2%2211%411&RI%611&R4'UOyR0%211'@y8%511%311p051&RO&RMvQ:r:r9r8r7r6r5r4%9887654321&R;vQ<vTCr;r3r2%67543>821&I'F&T6+RPP0%2217&T8+Vb\P0%22:1%7241%911'J+QoooPP0%72E1+`PQoooPP0%<21G%5231&R<r>r=%37IH21ONMp051p0<1p0G1p0O1pY6QH1p[BQI1p[FQJ1pY0Q=1pS8Q?1p2QK1pY>QI1pS0QK1pR<QL1pRLQO1").
Proof. intros LB FF LK cr A M V sp scr a.
intros HH Hc NI NS. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]]; unfold aclientw, aclient_g.
- left. exact Hc.
- right; left. exact Hc.
- exfalso. rewrite (aly_img_lo L C LY), (aly_img_hi L C LY) in Hc. apply NI. exact (proj1 Hc).
- right; right; right; left. exact Hc.
- right; right; right; right; left. exact Hc.
- right; right; right; right; right; left. exact Hc.
- exfalso. destruct Hc as (b & Hb & X). destruct (WB b Hb) as ((Q0 & _ & _ & Q3 & _ & (_ & _ & Q4)) & _). unfold in_shadow_of, S, SB in X.
clear - X Q0 Q3 Q4 NS. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma stack_client {BS ST} LB FF sp scr a : ahl_ceil ar <= a < 2 ^ 47 -> ~ (sp - scr <= a < sp) -> aclient_g BS ST L ar LB FF sp scr a.
Proof. intros H1 H2. right; left. split. exact H1. exact H2. Qed.
Lemma stk_shadow_client {BS ST} LB FF sp scr a : in_shadow_of (ahl_ceil ar) (ar_sptop ar - ahl_ceil ar) a -> ar_sptop ar <= 2 ^ 47 -> aclient_g BS ST L ar LB FF sp scr a.
Proof.
intros [H1 H2] HT. right; right; right; right; left. split. exact H1. eapply Z.le_trans. exact H2. unfold S.
apply Z.add_le_mono_r. apply Z.div_le_mono. reflexivity. Lia.lia.
Qed.
Lemma block_client {BS ST} LB FF sp scr q n a : In (q, n) LB -> q <= a < q + n -> aclient_g BS ST L ar LB FF sp scr a.
Proof. intros Hin Ha. left. exists (q, n). split. exact Hin. exact Ha. Qed.
Lemma obj_client {BS ST} LB FF sp scr o sz a : aobj FF o sz -> o <= a < o + sz -> aclient_g BS ST L ar LB FF sp scr a.
Proof.
intros (f & Hf & H1 & H2 & _) Ha. right; right; right; left. exists f. split. exact Hf. lia.
Qed.
Lemma fframe_client {BS ST} LB FF sp scr F k rs a : In (F, k, rs) FF -> (F <= a < F + ff_bytes k - 8 /\ ~ (F + 24 <= a < F + 32)) -> aclient_g BS ST L ar LB FF sp scr a.
Proof. intros Hf Ha. right; right; right; left. exists (F, k, rs). split. exact Hf. cbn [ff_addr ff_class fst snd]. exact Ha. Qed.
Lemma fframe_shadow_client {BS ST} LB FF sp scr F k rs a : In (F, k, rs) FF -> in_shadow_of F (ff_bytes k) a -> aclient_g BS ST L ar LB FF sp scr a.
Proof. intros Hf Ha. right; right; right; right; right; left. exists (F, k, rs). split. exact Hf. exact Ha. Qed.
Lemma client_apart : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "QM'='B'Q2%2211%411&RI%611'F&T6zr1%3221&T8r4%2241%8241&R;vQ<vTCr:r9r8r7&T3r6r2%3221%;7:987651p0=1pZ:K1r3%C2E1%I2E1&Ir;r5%=21;%E7DC3BA@1%511p071pZ:Q61%M2Q06%N2Q1M'J%E2GF%Q521E%G2F;%Q721J%5231p071p091p0;1p0G1pZHQC1pY:QD1p[2QE1pY6QF1p[BQG1p[FQH1pR<QE1pRLQH1").
Proof. intros LB FF sp scr a n b m.
intros HC HN Hn Hm. destruct (Z_lt_le_dec b (a + n)) as [X|X]; [|left; exact X]. destruct (Z_lt_le_dec a (b + m)) as [Y|Y]; [|right; exact Y].
exfalso. apply (HN (Z.max a b - b)). lia. replace (b + (Z.max a b - b)) with (a + (Z.max a b - a)) by lia. apply HC. lia.
Qed.
Lemma ff_count_app : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "E'Q2'=&RI%211'G'>&RHr3&7r2r1%33921%6251&K%8275%9285%3221%=3<51pZD?1pZB@1pZ<D1").
Proof. intros k l1 l2. unfold ff_count. rewrite list_basics.list.filter_app, length_app. reflexivity. Qed.
Lemma ff_count_cons : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "C'Q2&RI'=%112'M&RHr3(9r2r1%33921%6251(5%8274%211%;241pZ>=1pYH@1pZ<B1").
Proof. intros k f l. unfold ff_count. rewrite list_basics.list.filter_cons. destruct (decide _); cbn [length]; lia. Qed.
Lemma ff_count_incl : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "G'Q2'=&RI%211&T1r2r1%33521'ULr3%2281'M&RHr5r4%3221%4237%6221p081p0<1pZ@A1pZ>B1pZ<F1").
Proof. intros k l l'.
intros I ND. unfold ff_count. apply NoDup_incl_length.
- apply NoDup_ListNoDup. apply list_relations.list.NoDup_filter. exact ND.
- intros x Hx. apply list_elem_of_In in Hx. apply list_elem_of_In. apply list_basics.list.list_elem_of_filter in Hx. destruct Hx as [Px Hx].
apply list_basics.list.list_elem_of_filter. split. exact Px. apply list_elem_of_In. apply I. apply list_elem_of_In. exact Hx.
Qed.
Lemma nodup_of_map_app_r : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "A'=&RI%211'UL'Q2&Q1&RF&7r2r1%33921%64:751%9281%:2<5p021pZD=1pZB>1").
Proof. intros l1 l2. intros ND. rewrite map_app in ND. apply list_relations.list.NoDup_app in ND. destruct ND as (_ & _ & ND). apply (list_monad.list.NoDup_fmap_1 ff_addr). exact ND. Qed.
Lemma ffr_push : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "Q<'=&RI%211'Q2&SHr6r5r2%43321&T1%13945'UL&Q1&RF&7(9r8%23@;1%43A1=%74B@61%92A1&T6&T3r4+1%3221%521Dz%721Fr;%?3M>1r9%L321Kp051p081p0?1p0J1p0M1pYDQ31pYBQ41pYHQ71pS2Q71pS0Q81pR<Q91").
Proof. intros FF LK LK' f d d'.
unfold ffr. intros R I ND Hd Hd'. rewrite ff_count_app in R. change ((f :: FF) ++ LK') with (f :: (FF ++ LK')).
pose proof (ff_count_cons 1 f (FF ++ LK')) as C1. rewrite ff_count_app in C1.
pose proof (ff_count_incl 1 LK' LK I (nodup_of_map_app_r (f :: FF) LK' ND)) as C2. lia.
Qed.
Lemma ffr_pop : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "C'=&RI%211'Q2&SH(9r2r4%33721r3r1%73321r5%93167p031pYB<1pYH?1pS0?1pR<@1").
Proof. intros FF LK f d. unfold ffr. change ((f :: FF) ++ LK) with (f :: (FF ++ LK)). intros H. unfold ff_count in *. rewrite list_basics.list.filter_cons in H. destruct (decide _); cbn [length] in H; lia. Qed.
Lemma ffr_le : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "D'=&RI%211'Q2&SHr4r3r2%43321&T6%1234r6r5%93217p041p071pYD=1pYB>1pS0@1pR<A1").
Proof. intros FF LK d d'. unfold ffr. lia. Qed.
Lemma ffrs_push : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "Q4'=&RI%211'Q2&SIr6r5%3221&T6&T3+Q0%2251r2%5221r7%72:1(9'B%12??%221@(A%14BB@?r4%345D21r9%93621%F21<p0<1p0?1p0F1p[>K1pZ<L1pR:M1p[HN1p[FO1pR<Q11").
Proof. intros FF sp sp' F k rs. intros H Hr Hs f [<-|Hf]. cbn [ff_rs snd]. exact Hr. specialize (H f Hf). lia. Qed.
Lemma ffrs_le : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "A'=&RI%211'Q2&SIr3r2%3221&T6%1234r5%7216p031p061p[H;1p[F<1pR<>1").
Proof. intros FF sp sp'. intros H Hs f Hf. specialize (H f Hf). lia. Qed.
Lemma fl_range : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "R2'='B'Q2%2211%411&RI%611&R4'UOyR0%211'@y8%511%311p051&RO&RMvQ:r8r7r6r5r4r3r2%9887654321'F&T6&RAvTC%211%4217&T8&T3&R7%2251%42<1%;261+Vb\P0%<21@+1%82B1&T=&RB%11?+XPPP0%4221%D261&T<+2+Q?%3221%I2;1%K261%L2?1p0B1p0O1pZ0QH1pY0Q;1pS8Q=1p2QI1pY>QG1pS0QI1pR<QJ1pRLQM1").
Proof. intros LB FF LK cr A M V fl.
intros HH FLP. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & FSAPP & FSCEIL & FSIMG & _ & _ & _ & _ & TOP & _).
unfold app_mem, FS_BYTES in *. rewrite (aly_img_lo L C LY), (aly_img_hi L C LY) in FSIMG. lia.
Qed.
Lemma fl_writable : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "QH'='B'Q2%2211%411&RI%611&R4'UOyR0%211'@y8%511%311p051&RO&RMvQ:r8r7r6r5r4r3r2%9887654321'F&T6&RAvTC%211%4217&T8&T3&R7%2251%42<1%;261&S1+1%23CA1&S7&SN%241FD4%B241p081p0E1pZ0Q>1pY0Q11pS8Q31p2Q?1pY>Q=1pS0Q?1pR<Q@1pRLQC1").
Proof. intros LB FF LK cr A M V fl.
intros HH FLP. pose proof (fl_range LB FF LK cr A M V fl HH FLP) as FR.
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as WF. repeat lazymatch type of WF with _ /\ _ => apply proj2 in WF end.
assert (D : L5.defined M fl 1). { intros i Hi. replace (fl + i) with (ar_fs ar + (fl + i - ar_fs ar)) by lia. apply WF. unfold FS_BYTES in *. lia. }
split. exact D. apply (L5C.writable_of_defined RSEGS). exact D. lia. lia.
Qed.
Lemma vis_pack : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "T?'='B'Q2%2211%411&RI%611&R4'UOyR0%211'@y8%511%311p051'QA&RMvQ:r7r6r5r4r3r2&S0r1%211%;8:9876541'8p0D1&R>%12:8'F&R0&SN%221:&T6&T=&RBvTC%211+XPPP0%5221%721D&T3%12GF&T<+2+R0%3221%>251&S9%13Q0ONp031p0;1p[2QF1pY6QG1z%F21Q3+Vb\P0%H2?1p019p041p[2QN1pY6QO1&RA%11K%O21Q<&R7%I231%Q22I1p01Cp051p[2R81pY6R91&T0(A%14R<R<QHQGr=%43R=21%Q<2QLQJ%Q52QLQK%Q62QOQN%Q?221r8%Q231R1R0p031p071p091p[2RH1pY6RI1pZHRJ1p[<RK1%QI2Q4R4&T8%12R6R9%R0231&RK%QF2R>R;%23RAR@1p041pZ:S41%QC3RDRAR@p021p0I1p[2S81pY6S91pZHS:1p[<S;1%?2RDRF%R>2A1%R32RJRH%?3Q>Q<1p031pZ:SA1%R03RNRMRLp021p[2SD1pY6SE1%RB2R?R=%G3R>19p0;1pZ:SI1p018p[2SK1pY6SL1%RN281%RO2C1%S02Q41%S12QG1%S22R21%S32R;1%S42S11tRBS8S61p0S;1pZJSH1pS8SJ1p2T61pY>T41pS0T61pR<T71pRLT:1").
Proof. intros LB FF LK cr A M model.
intros HH. pose proof (HAJ.aior_lazy _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (AWF & LZ).
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & FSSH & STSH & _).
unfold app_mem in FSAPP. unfold FS_BYTES in FSAPP, FSCEIL.
cbn zeta. split.
{ apply (L5LZ.H_off_segments_ahid RSEGS A model 0x693000 segs_below). intros w Hw. pose proof (LZ w Hw) as (X & _). rewrite (aly_img_hi L C LY) in X. exact X. }
split. { intros a n Ha Hn. apply (avis_of_not_lazy A model (fun x => x < ahl_ceil ar)). intros w Hw. exact (proj1 (proj2 (LZ w Hw))). intros j Hj. lia. lia. lia. }
split. { intros a n Ha Hn. apply (avis_of_not_lazy A model (fun x => 0x693000 <= x)). intros w Hw. pose proof (proj1 (LZ w Hw)) as X. rewrite (aly_img_hi L C LY) in X. exact X. intros j Hj. lia. lia. lia. }
split. { intros a n Ha Hn. unfold app_mem, FS_BYTES in *.
apply (avis_of_not_lazy A model (fun x => ~ (ar_fs ar <= x < ar_fs ar + 11571200))). intros w Hw. exact (proj2 (proj2 (proj2 (LZ w Hw)))).
intros j Hj X. apply X. lia. lia. lia. }
split. { intros q m a n Hin Ha Hn. pose proof (proj1 (WB (q, m) Hin)) as (B0 & _ & _ & _ & B4 & B5). cbn [fst snd] in *. unfold app_mem in B5.
apply (avis_of_not_lazy A model (fun x => ~ in_block LB x)). intros w Hw. exact (proj1 (proj2 (proj2 (LZ w Hw)))).
intros j Hj X. apply X. exists (q, m). split. exact Hin. cbn [fst snd]. lia. lia. lia. }
split. { intros q m a n Hin Hs. apply (avis_of_shadow_allowed A model q m). exact (proj1 (proj2 (proj2 (proj2 (WB (q, m) Hin))))). exact Hs. }
split. { intros a n Hs. apply (avis_of_shadow_allowed A model (ar_fs ar) FS_BYTES). exact FSSH. exact Hs. }
intros a n Hs. apply (avis_of_shadow_allowed A model (ahl_ceil ar) (ar_sptop ar - ahl_ceil ar)). exact STSH. exact Hs.
Qed.
Lemma fl_vis : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "QH'='B'Q2%2211%411&RI%611&R4'UOyR0%211'@y8%511%311p051'QA&RMvQ:r8r7r6r5r4r3&S0r2%211%;8:9876541'F&T6&RAvTC%211%4218&T8&T3&R7%2251%42=1%;261&S9&R>%12FD+1%432E1p061p0C1pZ0Q>1pZJQ11pS8Q31p2Q?1pY>Q=1pS0Q?1pR<Q@1pRLQC1").
Proof. intros LB FF LK cr A M model fl. intros HH FLP. pose proof (vis_pack LB FF LK cr A M model HH) as (_ & _ & _ & VFS & _). apply VFS; lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma aobj_facts : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "T3'='B'Q2%2211%411&RI%611&R4'UOyR0%211'@y8%511%311p051'QA&RMvQ:r;r:r9r8r7r6&S0r5%211%;8:9876541&SFr4%23<51&T8z%2218'G&T9+8%22>1%43Q516'8p0O1&R>%12HF'F&T6+Vb\P0%221J&T3%12LK&T=&RBvTC%211+XPPP0%5221%;271&T<+2+Q?%3221%@2<1%J2Q9I%L3QM1N&T:&T4%12Q=M%321N%Q13R21Q?%I261%J291%K2?1%L2I1'J+QoonlP0+`PPPPPTP0%L221%Q021QH%Q12M4%6221&S1%13QNQLQK&S9r1%231QOQN&R9%Q62D1%F2R1QB%63521%Q<2QH6%QJ27R5%Q?221&R;vQ<rBrAr2%QA2R>1%675Q>43R=R<1p081pZ:S21%R52BQ3%QJ2=1%Q62RDR2%QH21C%QI219%>7=QF<;RERD1p051pZ:S:1%R1291%R22F1%R32K1%R42O1%R52Q21%R62Q:1tRBR:R81p0R=1p0RC1p0RG1p0RK1p[BSF1p[FSG1p\2SH1p[4SI1pZJS<1pS8S>1p2SJ1pY>SH1pS0SJ1pR<SK1pRLSN1").
Proof. intros LB FF LK cr A M model o sz sp scr.
intros HH (f & Hf & O1 & O2 & O8) Hsz Hsz8 H.
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & FSSH & _ & _ & _ & TOP & _).
pose proof (vis_pack LB FF LK cr A M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
pose proof (WF f Hf) as (Y1 & Y2 & Y3 & Y4 & Y5 & _).
rewrite (aly_img_lo L C LY), (aly_img_hi L C LY) in FSIMG. unfold app_mem, FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in *.
assert (HB : 0 < ff_bytes (ff_class f) <= 1024). { clear - Y4. destruct Y4 as [E|[E|[E|[E|[E|[]]]]]]; rewrite <- E; [change (ff_bytes 0) with 64 | change (ff_bytes 1) with 128 | change (ff_bytes 2) with 256 | change (ff_bytes 3) with 512 | change (ff_bytes 4) with 1024]; lia. }
apply Z.mod_divide in O8; [|lia]. destruct O8 as [q Eq].
apply Z.mod_divide in Hsz8; [|lia]. destruct Hsz8 as [m Em].
split. { subst o sz. rewrite Z_div_mult by lia. repeat split; first [apply Z_mod_mult | lia]. }
split. lia.
split. { intros i Hi. replace (o + i) with (ff_addr f + (o + i - ff_addr f)) by lia. apply Y5. lia. }
split. { apply VFS. lia. lia. }
split. { apply VFSSH. intros i Hi. unfold in_shadow_of, S. subst o sz. rewrite Z_div_mult in Hi |- * by lia. clear - Hi Y1 Y2 O1 O2 HB. lia. }
split. { intros i Hi. right; right; right; left. exists f. split. exact Hf. lia. }
intros i Hi. right; right; right; right; right; left. exists f. split. exact Hf. unfold in_shadow_of, S. subst o sz. rewrite Z_div_mult in Hi |- * by lia. clear - Hi O1 O2 HB. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma app_rng_fs : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "QC'='B'Q2%2211%411&RI%611&R4'UOyR0%211'@y8%511%311p051&RO&RMvQ:r9r8r7r6r5r4r3%9887654321&T6&RAvTC%211%4216&T3%1298&R7%3251%9231&R@%139?>p031p091p0?1pZHQ81p[6Q91pY0L1pS8N1p2Q:1pY>Q81pS0Q:1pR<Q;1pRLQ>1").
Proof. intros LB FF LK cr A M V p m.
intros HH H1 H2. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & FSAPP & FSCEIL & _).
unfold app_mem in FSAPP. split. clear - FSAPP H1; lia. split. clear - FSAPP H1 H2; lia. clear - FSCEIL H2; lia.
Qed.
Lemma app_rng_aobj : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "QF'='B'Q2%2211%411&RI%611&R4'UOyR0%211'@y8%511%311p051&RO&RMvQ:r;r:r9r8r7r6r5%9887654321&SFr4%23:41&T6%1273&T3%1285%22;:%5221&R@vTC%231>=p041p091p0<1p0@1pZHQ91p[6Q:1p\2Q;1p[4Q<1pY0O1pS8Q11p2Q=1pY>Q;1pS0Q=1pR<Q>1pRLQA1").
Proof. intros LB FF LK cr A M V o sz p m.
intros HH (f & Hf & O1 & O2 & _) H1 H2. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & WF & _).
destruct (WF f Hf) as (Y1 & Y2 & _). apply (app_rng_fs LB FF LK cr A M V p m HH). clear - Y1 O1 H1; lia. clear - Y2 O2 H2; lia.
Qed.
Lemma app_rng_block : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "QI'='B'Q2%2211%411&RI%611&R4'UOyR0%211'@y8%511%311p051&RO&RMvQ:r;r:r9r8r7r6r5%9887654321&T0(Ar4%24LL51r<%53M21&T6%12:5&T3%12;7%22>=%5221&R@vTC%231A@p041p091p0<1p0C1pZHQ<1p[6Q=1p[2Q>1p[<Q?1pY0Q21pS8Q41p2Q@1pY>Q>1pS0Q@1pR<QA1pRLQD1").
Proof. intros LB FF LK cr A M V q n p m.
intros HH Hin H1 H2. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
destruct (WB (q, n) Hin) as ((Q0 & _ & _ & _ & Q4 & (_ & Q5 & _)) & _). cbn [fst snd] in *. split. clear - Q0 H1; lia. split. clear - Q5 H1 H2; lia. clear - Q4 H2; lia.
Qed.
Lemma app_rng_img : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "G'Q2&T6+SoonPPPPP0&RBvTC%211%5241zr3%8221&T3r4%2214+Vb\P0%=221&R@r5%23=16p041p0:1p0>1pZHE1p[6F1").
Proof. intros p m. intros SPT H0 H. unfold app_rng, BIGSHADOW_LO. split. exact H0. split. left; clear - H; lia. clear - SPT H; lia. Qed.
Lemma app_rng_stack : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "H'Q2&T6+SoonPPPPP0&RBvTC%211%5241&T=+XPPP0%2241r3%:221&T3r4%2214%>21:&R@r5%23>15p041p091p0?1pZHF1p[6G1").
Proof. intros p m. intros SPT H1 H2. unfold app_rng, BIGSHADOW_HI. split. clear - SPT H1; lia. split. right; clear - SPT H1; lia. left; exact H2. Qed.
Lemma apiece : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "UJ'='B'Q2%2211%411&RI%611&R4'UOyR0%211'@y8%511%311p051'QA'S<&QBy5%221:!p0D1&SA&RMvQ:r@r?r>r=r<r;&S0r:%211%;8:9876541&SE%1286'R2&SN&S>r9&UNr8%22Q31&R1&R>%12CA%321C&S@%11;%;5D:731r7r6%<2Q=1r5%@5G4216%C3B61&SC%=2Q0N%?21Q0%3218'F&T6zr1%3221&T8&T<+2+R0%3221%5271%;271&Ir2%Q111%311'Gr3%Q62R71%Q@11rCrA%Q6221rB%Q93216%93R961p0;1p0@1pY6RH1%QB1@&R<vQ<vTCrHrG%574321Q1Q1B+RPP0%Q421D+Vb\P0%Q22F1%Q8231%M11%Q:271p0>1p0Q11pY6S91rFrErD%R?1Q>%RH8RGA@432Q51%R=24Q6&RL%125Q4'8p0S;1r4%R92G1%R:2H;%Q;3421%R<2K>%R>21R6%Q>3S=1S1%R32NR9%Q91QC%QE11%S11Q@rL%11QB%QE3SE31p051p0QL1pY6T41rJ%RJ371R7(:%QL3F21%S<1R0%N1R1%QO3SO21p041pY6T51'SB&S8vSO%211&S:%15QFQ8Q7SDS<%64S?31R3p081p0B1p0L1p0N1p0Q21p0Q91p0Q<1p0Q>1pZNT?1pS<TA1%=5T7T5T4R<R>%B4SK?1SGp031p0QI1p0R;1p0S91p0S>1p0T31p0T61pRHTC1pY2TE1pS>TM1p[:U;1pSLTJ1p[8U=1pSHTL1pZ6U01pZ4U11pZJU31pS8U51p2UA1pY>U?1pS0UA1pR<UB1pRLUE1").
Proof. intros LB FF LK cr A M model fx fx1 R pc R1 pc1 M1v W K.
intros HH [Hh MI] MS MG FZ WC KONT.
pose proof (HAJ.aior_lazy _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (AWF & LZ).
pose proof (vis_pack LB FF LK cr A M model HH) as (HOFF & _).
set (H := ahid A model) in *.
unfold cfg. eapply (L5LZ.cps_of_msteps_lazy RSEGS H A fx fx1 R _ M R1 _ M1v model K HOFF wx_nowrap (L5LZ.lazy_cover_ahid A model) AWF MI Hh MS).
intros model1 MI1 SBM1 HC1.
set (M1 := munrestrict H M M1v).
assert (M1vis : mrestrict H M1 = M1v). { apply L5LZ.mrestrict_of_munrestrict. exact HC1. }
assert (FRM1 : forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha Hn. unfold M1, munrestrict. destruct (H (Z_to_bv 64 a)) eqn:E. reflexivity. rewrite (FZ a Ha Hn). unfold mrestrict. rewrite E. reflexivity. }
assert (MGM1 : mem_grows M M1).
{ intros x Hx. unfold M1, munrestrict. destruct (H x) eqn:E. exact Hx. apply MG. unfold mrestrict. rewrite E. exact Hx. }
assert (VML : vml_of model1 = vml_of model). { unfold vml_of. rewrite (L5LZ.sbm_vmmaps _ _ SBM1), (L5LZ.sbm_lazy _ _ SBM1). reflexivity. }
apply (KONT M1 model1).
- rewrite VML. apply (HAJ.aior_frame _ _ _ _ _ HIok LB FF LK cr A M M1 _ HH).
+ intros a Ha Hp. apply FRM1. exact Ha. intros CW. destruct (WC a Ha CW) as [C1 C2]. destruct Hp as [Hp|[Hp|Hp]].
* exact (Hp (aclientw_client _ _ _ _ _ _ _ C1)). * apply C2. exact (aly_ro_img L C LY a Hp).
* exact (aclientw_not_bshadow LB FF LK cr A M _ 0 0 a HH C1 Hp).
+ exact MGM1.
- split. exact (eq_trans (L5LZ.sbm_halted _ _ SBM1) Hh). exact MI1.
- apply L5LZ.sbm_model_rt. exact SBM1.
- apply L5LZ.sbm_ahid. exact SBM1.
- exact M1vis.
- exact MGM1.
- exact FRM1.
- intros a Ha. unfold M1. apply L5LZ.munrestrict_visible. exact Ha.
Qed.
Lemma apiece_ro : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "TD'='B'Q2%2211%411&RI%611&R4'UOyR0%211'@y8%511%311p051'QA'S<&QBy5%221:&SA&RMvQ:r?r>r=r<r;r:&S0r9%211%;8:9876541&SE%1286'R2&SN&S>r8&UNr7%22Q11&R1&R>%12CA%321C&S@%11;%;5D:731r6r5%<2Q;1r4%@5G4216%C3B61&SC%=2Q0N%?21Q0%3218'F&T6zr1%3221&T8&T<+2+R0%3221%5271%;271'Gr2%Q22R11%Q411rA%Q121QEr@%Q43215%83R251p0:1pY6R@1rFrErDrCrB%QJ1I%R38R265432@1%QH24A&RLr3%2261'8p0RE1%QD2<Q;%QE2=;%J3321%QG2@>%QI21QB%M3RF1R;%Q>2CQM%R:1MrI%11O%Q23RL31p0Q41pY6S:1'SB&S8vSO%211&S:%15NKQ6RCR;%64R>31RKp081p0?1p0A1p0E1p0K1p0O1p0Q11pZNS;1pS<S=1%<5S4S2S1Q?S5%A4RI>1REp031p0Q>1p0R61p0R;1p0S01p0S31pRHS@1pS>SG1p[:T51pSLSD1p[8T71pSHSF1pZ6SJ1pZ4SK1pZJSM1pS8SO1p2T;1pY>T91pS0T;1pR<T<1pRLT?1").
Proof. intros LB FF LK cr A M model fx fx1 R pc R1 pc1 M1v K.
intros HH AM MS MG FZ KONT. apply (apiece LB FF LK cr A M model fx fx1 R pc R1 pc1 M1v (fun _ => False) K HH AM MS MG).
- intros a Ha _. apply FZ. exact Ha.
- intros a _ [].
- intros M1 model1 X1 X2 X3 X4 X5 X6 X7 _. apply (KONT M1 model1 X1 X2 X3 X4 X5 X6). intros a Ha. apply X7. exact Ha. intros [].
Qed.
Lemma mem_eq_of_agree : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "Q4'UOyR0%211'@y8%511%311p051'Q2'F&T6zr1%3221&T8&T<+2+R0%3221%5271%;271'Gr3&UNr2%22H1%411r4%113%83G31p0:1pY6G1%;3I8:p021pS:K1pS8L1").
Proof. intros M M'.
intros E. apply functional_extensionality. intros w. rewrite <- (Z_to_bv_bv_unsigned 64 w) at 1. rewrite <- (Z_to_bv_bv_unsigned 64 w) at 2.
apply E. pose proof (bv_unsigned_in_range _ w) as X. change (bv_modulus 64) with (2 ^ 64) in X. lia.
Qed.
Lemma astack_ok_of_astk : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "QD'UOyR0%211'@y8%511%311p051'Q2&SGvTCr6r4r3%544321&SCr7%2216&T6z%2218&T3r5%22<1%6218'G&T9&T=r9%221=+@%5221%73H1=&RCvQ<r;r:r8%;221%655M4G1p081p0A1p0F1p0G1p0K1p0O1p[DQ61pZ2Q71p[BQ81p[FQ91pS<Q;1pS8Q<1").
Proof. intros M M1 sp scr fr scr'.
intros (A16 & SLO & SHI & SPT & DSCR & DUP) MG Hfr Hscr Hle AL.
split. exact AL. split. lia. split. lia. split. exact SPT. split.
- intros d m Hd Hm. rewrite (aly_segs L C LY). apply (L5C.writable_of_defined RSEGS M1 (sp - fr - scr') scr'). eapply L5.defined_grows. exact MG.
eapply L5.defined_sub. exact DSCR. lia. lia. lia. lia. exact Hd. exact Hm.
- eapply L5.defined_grows. exact MG. intros j Hj. destruct (Z_lt_le_dec j fr).
+ replace (sp - fr + j) with (sp - scr + (scr - fr + j)) by lia. apply DSCR. lia.
+ replace (sp - fr + j) with (sp + (j - fr)) by lia. apply DUP. lia.
Qed.
Lemma astk_sub : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "QB'UOyR0%211'@y8%511%311p051'Q2&SGvTCr6r4r3%544321&SCr7%2216&T6z%2218&T3r5%22<1%6218'G&T9&T=r9%221=+@%5221%73H1=r;r:r8%9221%L4K41Ep061p0?1p0D1p0E1p0I1p0M1p[DQ41pZ2Q51p[BQ61p[FQ71pS<Q91pS8Q:1").
Proof. intros M M1 sp scr fr scr'.
intros (A16 & SLO & SHI & SPT & DSCR & DUP) MG Hfr Hscr Hle AL.
split. exact AL. split. lia. split. lia. split. exact SPT. split.
- eapply L5.defined_grows. exact MG. eapply L5.defined_sub. exact DSCR. lia. lia.
- eapply L5.defined_grows. exact MG. intros j Hj. destruct (Z_lt_le_dec j fr).
+ replace (sp - fr + j) with (sp - scr + (scr - fr + j)) by lia. apply DSCR. lia.
+ replace (sp - fr + j) with (sp + (j - fr)) by lia. apply DUP. lia.
Qed.
Lemma astk_grows : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "J'UOyR0%211'@y8%511%311p051'Q2&SGvTCr4r2r1%544321&SCr5%2216r3%:49381p031p071p[B>1p[F?1pS<A1pS8B1").
Proof. intros M M1 sp scr.
intros (A16 & SLO & SHI & SPT & DSCR & DUP) MG. split. exact A16. split. exact SLO. split. exact SHI. split. exact SPT.
split; eapply L5.defined_grows; eauto.
Qed.
Lemma astk_after_rt : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "R5'='B'Q2%2211%411&RI%611&R4'UOyR0%211'@y8%511%311p051&RO&RMvQ:r=r<r;r:r9r8r5%9887654321&SGvTCr4%342751&SC%12:9&R=vQ<r@r?%483921<8?>&T6&T=r7%22A1r6%421B%6231%725Fz%921H%E4DMKJp021p051p071p0?1p0E1p0H1p0M1p[DQF1p[HQG1p[BQH1p[FQI1pY0Q<1pS@Q>1pS<Q?1pS8Q@1p2QL1pY>QJ1pS0QL1pR<QM1pRLR01").
Proof. intros LB FF LK cr A M M1 M2 V sp scr sp' scr'.
intros HH (A16 & SLO & SHI & SPT & DSCR & DUP) MG [PRES SDEF] H1 H2 H0.
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TOP & _).
assert (D : forall x, (sp - scr <= x < sp \/ sp <= x < ar_stack_top ar) -> M2 (Z_to_bv 64 x) <> None).
{ intros x Hx2. destruct (rng_dec x (sp' - scr') sp') as [I|O].
- apply SDEF. exact I.
- rewrite PRES. apply MG. destruct (Z_lt_le_dec x sp).
+ replace x with (sp - scr + (x - (sp - scr))) by lia. apply DSCR. lia.
+ replace x with (sp + (x - sp)) by lia. apply DUP. lia.
+ lia. + apply stack_client. lia. exact O. }
split. exact A16. split. lia. split. lia. split. exact SPT. split.
- intros j Hj. apply D. lia.
- intros j Hj. apply D. lia.
Qed.
Lemma astk_after : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "R9'='B'Q2%2211%411&RI%611&R4'UOyR0%211'@y8%511%311p051&RO&S4%B11&RMvQ:r>r=r<r;r:r9r6%9887654321&SGvTCr5%342751&SC%12:9&SDvQ<rAr@r4%594:32=91@?&T6&T=r8%22B1r7%421C%6231%725Gz%921I%F4ENLKp021p051p071p0?1p0F1p0I1p0N1pY2Q91p[DQJ1p[HQK1p[BQL1p[FQM1pY0Q@1pS@QB1pS<QC1pS8QD1p2R01pY>QN1pS0R01pR<R11pRLR41").
Proof. intros LB FF LK cr A M M1 M2 V sp scr sp' scr' W.
intros HH (A16 & SLO & SHI & SPT & DSCR & DUP) MG (PRES & SDEF & DK) H1 H2 H0.
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TOP & _).
assert (D : forall x, (sp - scr <= x < sp \/ sp <= x < ar_stack_top ar) -> M2 (Z_to_bv 64 x) <> None).
{ intros x Hx2. destruct (rng_dec x (sp' - scr') sp') as [I|O].
- replace x with (sp' - scr' + (x - (sp' - scr'))) by lia. apply SDEF. lia.
- apply DK. lia. apply stack_client. lia. exact O. apply MG. destruct (Z_lt_le_dec x sp).
+ replace x with (sp - scr + (x - (sp - scr))) by lia. apply DSCR. lia.
+ replace x with (sp + (x - sp)) by lia. apply DUP. lia. }
split. exact A16. split. lia. split. lia. split. exact SPT. split.
- intros j Hj. apply D. lia.
- intros j Hj. apply D. lia.
Qed.
Lemma astk_writable : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "Q6'UOyR0%211'@y8%511%311p051'Q2&SGvTCr5r4r3%544321&T6&T=%1265%3215&T3%1287r6%7221z%921<&S7&SNr9%34217Ap051p081p0=1p0B1p[2I1pY6J1p[BK1p[FL1pS8N1").
Proof. intros M sp scr a n.
intros (A16 & SLO & SHI & SPT & DSCR & DUP) H1 H2 Hn. apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact DSCR. lia. lia. lia. lia.
Qed.
Lemma astk_defined : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "Q2'UOyR0%211'@y8%511%311p051'Q2&SGvTCr5r4r3%544321&T6&T=%1265%3215&T3%1287r6%7221&S1r8%231>=p041p091p0>1p[2E1pY6F1p[BG1p[FH1pS8J1").
Proof. intros M sp scr a n. intros (A16 & SLO & SHI & SPT & DSCR & DUP) H1 H2. eapply L5.defined_sub. exact DSCR. lia. lia. Qed.
Lemma retire_frame : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "SF'='B'Q2%2211%411%4223%611&RI%811&R4'UOyR0%211'@y8%511%311p051p\862&RO&RMvQ:r<(9(Ar4r3%34II21r2%54JK21r;%83J21r:r9r8r7r5%A8@?654321&RE&SN&T=&T3&RG%11B%3281+8%6221u8%:59>21D&I&R;vQ<vTCr>r6%O4QEQE1C%Q04QEQF1Or=%Q33QE21z%:7987211Q2%<11'F&T6r1%2261&T8&T<+2+R0%3221%5271%:271'G%13R8Q>D%J11'J&UN%12R3QD%QI11%G12%83R121&R<rB%QL4RBRBQDQC%QM4RBRC1QCrA%R03RB21%67Q5Q451MMQN%=281p0?1p0C1pY6RJ1&S6%14QGQNQJQ3&SC%12R:R2r@r?%R?8R>@=21Q>R=R5p041p071p0:1p0Q:1p0QH1p0R41pZ0S81p[>S91pZ<S:1pR:S;1pY0RK1pSBRM1pS@RO1p2S=1pY>S91pS0S;1pR<S>1pRLSA1").
Proof. intros LB FF LK cr A M2 M3 V F k rs fl.
intros HH FLC FLNC DIFF FL0 MG.
assert (EQFF : ff_remove F ((F, k, rs) :: FF) = FF). { cbn [ff_remove ff_addr fst snd]. rewrite Z.eqb_refl. reflexivity. }
rewrite <- EQFF.
apply (HAJ.aior_release _ _ _ _ _ HIok LB ((F, k, rs) :: FF) LK cr A M2 M3 V F k rs fl HH (or_introl eq_refl)).
- rewrite (aly_segs L C LY). exact FLC.
- exact DIFF.
- rewrite (aly_segs L C LY). exact FL0.
- exact MG.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma sm_facts : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "W<'='B'Q2%2211%411%4223%611&RI%811&R4'UOyR0%211'@y8%511%311p051'QA&RGr3%211'8p0;1&R>r8r6%3221&R1r1%2215&RMvQ:r>(9(Ar7%24Q3Q31;r5%44Q4Q521r=%73Q421r<r;r:r9&S0%11F%A8@?765431&T0z+1+2+3+4(?%11QF%G3QG31%H3QH51%I3QI71%J3QJ91%K3QK;1%=3QLJ1&T6&RAvTC%211%421F&T3%12IQ;&R7%3251%9231'G&T9%12Q0Q7%33R:1J&R?%12Q4QE%;2Q7Q2&T=&RB%11A+XPPP0%4221%F261&R5r@%231QGQ<&RE&SNrAr?%I21QB+8%?221u8%857621QG'F%Q42Q1QK&T8%12QMN%4231&I&R;vQ<rH%R84S9S9@D%R94S9S:1@rG%R<3S921%776Q>51QMQMR>%911'JrB%Q?21RB%QE21H%QA2IR2%QG214%6231&RNrErC&T4%12Q0N%53431+TP0rD%R1221%QM22Q:&T<+Q?%22R@1%R6241+Vb\P0%R8218%R927QD+R0%R;21QC+QP0%R=2QE1%Q;231%Q<261%Q=281%Q>2;1%Q?2A1%RC2AQG%R?2QHS0%RE21E%Q4231+Q0%R=2H1%R?3TF1S6&T:%O2KQL%221QM%RC3TJ1M%RC2R6D%RE3TL1S<&S1%13SOQ1R9&S7%14R8T1Q3R;+QoonlP0+`PPPPPTP0%S1221%S721Q7%S82Q64%QG221&R9%S62@1%Q@2RDR=%;4RBT;21&S;%13T=43&S5%S02Q?RB%24RGT@1RF%SC2QDRG%SD2Q0Q?%SE2Q>RI%SF2Q2S1%RD221%RE241%RF261%H4ROTHRNT6%SK2ERO%SL2Q8H%R;221&S9%13S2QOS7%23S3ED%33S4S5T=%RO221%S0241%S1271%S22;1%S32=1%S42E1%S52I1%S62L1%S72Q11%S82Q81%S92Q;1%S:2Q>1%S;2QA1%S<2QF1%S=2QJ1%S>2QO1p0RD1p0RK1p0S31p0S>1p0SD1p0SN1p0T21p0T:1p0T=1p0TB1p0TH1p0TN1p0U=1tSDV=V01tRDV8V41t6VNV;1pZ0VO1p[>W01pZ<W11pR:W21p[0VC1pS@VE1p2W31pY>VO1pS2W11pR<W41pRLW71").
Proof. intros LB FF LK' cr A M2 model2 F k rs fl.
intros B H2 MV2 HH2 Hk FS1 FS2 FAL FAPP FCEIL FDEF FLC FLP FLNC FLA FSH.
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH2) as (WB & WF & FSAPP & FSCEIL & FSIMG & FSSH & _ & _ & _ & TOP & _).
pose proof (vis_pack _ _ _ _ _ _ _ HH2) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
rewrite (aly_img_lo L C LY), (aly_img_hi L C LY) in FSIMG.
assert (HB : 64 <= B <= 1024 /\ B mod 64 = 0 /\ exists q, F = q * 64).
{ subst B. destruct Hk as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn -[Z.le Z.add Z.mul Z.modulo];
[change (ff_bytes 0) with 64 in FAL |- * | change (ff_bytes 1) with 128 in FAL |- * | change (ff_bytes 2) with 256 in FAL |- * | change (ff_bytes 3) with 512 in FAL |- * | change (ff_bytes 4) with 1024 in FAL |- *];
(split; [lia|]); (split; [reflexivity|]); apply Z.mod_divide in FAL; try lia; destruct FAL as [q Hq];
[exists q | exists (q * 2) | exists (q * 4) | exists (q * 8) | exists (q * 16)]; lia. }
destruct HB as (BR & B64 & q & EF).
unfold app_mem, FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in *.
pose proof (fl_range _ _ _ _ _ _ _ fl HH2 FLP) as FLR. pose proof (fl_writable _ _ _ _ _ _ _ fl HH2 FLP) as [FLD FLW]. pose proof (fl_vis _ _ _ _ _ _ _ fl HH2 FLP) as FLV.
assert (VF : avis H2 F B). { apply VFS. lia. lia. }
assert (VSH : avis H2 (F / 8 + SB) (B / 8)).
{ apply VFSSH. intros i Hi. unfold in_shadow_of, S. clear - Hi EF FS1 FS2 BR B64. subst F. lia. }
split. lia.
split. exact FLA.
split. { subst F. replace (q * 64) with ((q * 2) * 32) by lia. apply Z_mod_mult. } split. { clear - EF. subst F. lia. } split. exact B64.
split. { apply (proj2 (defined_vis H2 M2 F B VF)). exact FDEF. }
split. { apply (proj2 (writable_vis H2 M2 F B VF ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact FDEF. lia. lia. }
split. lia.
assert (ZSH : L5KA.zeros_at M2 (F / 8 + SB) (B / 8)). { intros i Hi. unfold shadow_zero, byte_at, S in FSH. apply FSH. exact Hi. }
split. { apply (proj2 (writable_vis H2 M2 _ _ VSH ltac:(unfold SB; lia) ltac:(unfold SB; lia))). apply (L5C.writable_of_defined RSEGS). apply L5KA.zeros_at_defined. exact ZSH. unfold SB; lia. unfold SB; lia. }
split. { apply (proj2 (zeros_at_vis H2 M2 _ _ VSH)). exact ZSH. }
split. { apply (proj2 (u64_at_vis H2 M2 (F + B - 8) fl ltac:(eapply avis_sub; [exact VF|lia|lia]) ltac:(lia) ltac:(lia))). exact FLC. }
split. lia.
split. { apply (proj2 (writable_vis H2 M2 fl 1 FLV ltac:(lia) ltac:(lia))). exact FLW. }
split. lia.
split. exact VF. split. exact VSH. exact FLV.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma sm_apart : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "UB'='B'Q2%2211%411%4223%611&RI%811&R4'UOyR0%211'@y8%511%311p051&RO&RMvQ:r?(9(Ar8r7%34HH21r6%54IJ21r>%83I21r=r<r;r:r9%A8@?654321'F&T6+SoonPPPPP0&RBvTC%211%5241&T<+2+Q?%3221%:261%<261&T0z+1+3+4(?%11QF%Q33QG31%Q43QH51%Q53QI>1%Q63QJ81%Q73QK:1%<3QLK1+Vb\P0%J21O&T3&RG%11Q2%32Q41&T=+XPPP0%22M1%Q2241&R?%81Q:%22Q<1'G&T9%<1Q?%22QB1%43R>1M&RJ%@1QE&7rErD%33RA21%63R251r1rH%Q83RG21'JrBrA%L11%N231&;r2%23S0S01%QM241&C%13S3S34%Q5241%R121;%=251p0?1pY:S71&I&R;vQ<r@%RH4S=S=B1%RI4S=S>1RKrG%RL3S=21%776R:J1R0R0RF%911%R?2R2M&T8%12ORG%RC231rKrJ%QJ2RNJ%@7?RC32>S71p051pZ:SL1%92R<RO%QO2S3S1%RK21Q<rC%R111%R32Q?1%RO21S8%Q;251&T4+8%22QD1&R9%R:221%S62<1%62:5%R=231%S921SB%QE241%S;2AQD%RA2QERN%S=21SF%QI231%S@251%SA2@1p0H1p0J1p0Q51p0Q@1p0R41p0R<1p0RB1p0RF1p0RO1p0S21p0S@1p0SN1p[2U11pY6U21p[BU31p[FU41pZ0U51p[>U61pZ<U71pR:U81pY0TI1pS@TK1p2U91pY>U51pS2U71pR<U:1pRLU=1").
Proof. intros LB FF LK' cr A M2 V F k rs fl sp scr a n.
intros HH2 SPT Hk F1 F2 F3 F4 FA FB FLNC CA Hn.
assert (HB : 0 < ff_bytes k /\ ff_bytes k mod 8 = 0 /\ F mod 8 = 0 /\ (F / 8) * 8 = F).
{ Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
destruct Hk as [<-|[<-|[<-|[<-|[<-|[]]]]]]; [change (ff_bytes 0) with 64 in F4 |- * | change (ff_bytes 1) with 128 in F4 |- * | change (ff_bytes 2) with 256 in F4 |- * | change (ff_bytes 3) with 512 in F4 |- * | change (ff_bytes 4) with 1024 in F4 |- *];
(split; [lia|]); (split; [reflexivity|]); apply Z.mod_divide in F4; try lia; destruct F4 as [q ->]; split; clear; lia. }
destruct HB as (B0 & B8 & F8 & FQ).
assert (HHF : ri_inv HI LB FF LK' cr A M2 V -> True) by (intros; exact I). clear HHF.
assert (NC : forall x, (F <= x < F + ff_bytes k \/ S F <= x <= S (F + ff_bytes k - 1)) -> ~ aclient L ar LB FF sp scr x).
{ intros x Hx. pose proof (HAJ.aior_perm _ _ _ _ _ HIok) as _.
intros Hc. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH2) as (WB & WF & FSAPP & FSCEIL & _).
unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in F3, FSAPP. unfold S, SB in Hx.
destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]].
- destruct Hc as (b & Hb & X). pose proof (proj1 (WB b Hb)) as (Y0 & _ & _ & _ & Y & Y2). unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Y2. specialize (FB b Hb). lia.
- lia.
- rewrite (aly_img_hi L C LY) in Hc. lia.
- destruct Hc as (f & Hf & X). pose proof (WF f (or_intror Hf)) as (Y1 & Y & _). specialize (FA f (in_or_app _ _ _ (or_introl Hf))). lia.
- unfold in_shadow_of, S, SB in Hc. lia.
- destruct Hc as (f & Hf & X). pose proof (WF f (or_intror Hf)) as (Y1 & Y & Y3 & Y4 & _). specialize (FA f (in_or_app _ _ _ (or_introl Hf))). unfold in_shadow_of, S, SB in X.
assert (Y5 : ff_addr f mod 8 = 0 /\ ff_bytes (ff_class f) mod 8 = 0 /\ 0 < ff_bytes (ff_class f)).
{ destruct Y4 as [E|[E|[E|[E|[E|[]]]]]]; rewrite <- E in Y3 |- *;
[change (ff_bytes 0) with (8 * 8) in Y3 |- * | change (ff_bytes 1) with (16 * 8) in Y3 |- * | change (ff_bytes 2) with (32 * 8) in Y3 |- * | change (ff_bytes 3) with (64 * 8) in Y3 |- * | change (ff_bytes 4) with (128 * 8) in Y3 |- *];
(split; [|split; [apply Z_mod_mult|lia]]); apply Z.mod_divide in Y3; try lia; destruct Y3 as [kk Hk']; rewrite Hk'; rewrite Z.mul_assoc; apply Z_mod_mult. }
destruct Y5 as (Y5 & Y6 & Y7). Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
- destruct Hc as (b & Hb & X). pose proof (proj1 (WB b Hb)) as (Y0 & _ & Y1 & _ & Y & Y2). specialize (FB b Hb). unfold in_shadow_of, S, SB in X.
unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Y2. assert (Y5 : fst b mod 8 = 0) by (clear - Y1; apply Z.mod_divide in Y1; [|lia]; destruct Y1 as [kk ->]; replace (kk * 16) with ((2 * kk) * 8) by lia; apply Z_mod_mult). lia. }
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
split. { apply (client_apart LB FF sp scr a n F (ff_bytes k) CA). intros i Hi. apply NC. left. lia. exact Hn. exact B0. }
split. { apply (client_apart LB FF sp scr a n (F / 8 + SB) (ff_bytes k / 8) CA). intros i Hi. apply NC. right. unfold S.
assert ((F + ff_bytes k - 1) / 8 = F / 8 + ff_bytes k / 8 - 1).
{ apply Z.mod_divide in B8. destruct B8 as [m Hm]. rewrite Hm. rewrite <- FQ. rewrite Z_div_mult by lia.
replace (F / 8 * 8 + m * 8 - 1) with ((F / 8 + m - 1) * 8 + 7) by lia. rewrite Z.div_add_l by lia. change (7 / 8) with 0. lia. lia. }
lia. exact Hn. apply Z.div_str_pos. lia. }
apply (client_apart LB FF sp scr a n fl 1 CA). intros i Hi X. apply FLNC. apply aclient_cons. replace (fl + i) with fl in X by lia. eapply aclient_00. exact X. exact Hn. lia.
Qed.
Lemma flagptr_now : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "S?'='B'Q2%2211%411&RI%611&R4'UOyR0%211'@y8%511%311p051&RO'QA&RMvQ:rCrBrAr@r?r>r=%9887654321r<r;r:r9r8&S0r7%211%B8A:876541&T0%Q52Q3Q4(Ar6%24Q7Q771r5%44Q8Q921rD%83721%74Q<Q<><%84Q<Q=15%;3:1G(9z+1+2+3+4(?%11QF%83QG31%93QH51%:3QI71%;3QJ91%<3QK;1%I3QLN1&RE&SN&T=&T3&RG%11Q5%32Q71+8%6221u8%:59QE21Q1'F%81Q=%:2Q?1%<217%?5>QD16Q<&S5&R1&R>%12QIQF%321QI%54D17QB%;271p0=1p0I1p0Q81p0Q<1p0QF1p0R01pZ0RJ1p[@RK1p[>RL1pZ<RM1pR:RN1pZLR@1pS:RC1p4RO1pY@RM1pS2RO1pR>S01pRNS31pY0RH1pS8RJ1p2S61pY>S41pS0S61pR<S71pRLS:1").
Proof. intros LB FF LK cr A M V LB' FF' LK' cr' A' M' model' F k rs rs' fl.
intros HH HH' IN IN' Hk FLC.
pose proof (HAJ.aior_flagptr _ _ _ _ _ HIok LB FF LK cr A M V LB' FF' LK' cr' A' M' _ F k rs rs' fl HH HH' IN IN') as X.
rewrite (aly_segs L C LY) in X. specialize (X FLC). split. exact X.
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH') as (_ & WF & FSAPP & _).
pose proof (WF _ IN') as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2.
pose proof (vis_pack _ _ _ _ _ _ _ HH') as (_ & _ & _ & VFS & _).
assert (BR : 64 <= ff_bytes k <= 1024) by (destruct Hk as [<-|[<-|[<-|[<-|[<-|[]]]]]]; vm_compute; split; discriminate).
unfold app_mem, FS_BYTES in *.
apply (proj2 (u64_at_vis (ahid A' model') M' (F + ff_bytes k - 8) fl ltac:(apply VFS; lia) ltac:(lia) ltac:(lia))). exact X.
Qed.
Definition ek (LB : list (Z * Z)) (FF : list fframe) (sp scr : Z) (W : list L5.range) (M M' : word -> option byte) : Prop :=
forall a, akept L ar LB FF sp scr W a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Definition dk (LB : list (Z * Z)) (FF : list fframe) (sp scr : Z) (M M' : word -> option byte) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp scr a -> M (Z_to_bv 64 a) <> None -> M' (Z_to_bv 64 a) <> None.
Lemma ahpres_of : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "QA'='B'Q2%2211%411&RI%611&S4%811'UOyR0%211'@y8%511%311p051&SKr7r6r5r4r3r2r1%877654321&S1&T=%1298%33619&SJr9r8%3621?><;&SDvQ<vTCr:%4932176DCBAp061p0;1p0@1pS:J1pS8K1pY2Q41p[BQ;1p[FQ<1pR<Q91pRLQ<1").
Proof. intros LB FF sp scr W M M'. intros E D K. split. exact E. split. exact D. exact K. Qed.
Lemma ek_trans : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "Q8'='B'Q2%2211%411&RI%611&S4%811'UOyR0%211'@y8%511%311p051&SKr8r7r6r5r4r3r2%877654321r9%:71987643r:%<713;:986p031p061pSB@1pS@A1pS<B1pY2K1p[BQ21p[FQ31pR<Q01pRLQ31").
Proof. intros LB FF sp scr W M1 M2 M3. intros A B a Ha. rewrite (B a Ha). apply A. exact Ha. Qed.
Lemma ek_mono : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "R1'='B'Q2%2211%411&RI%611&S4%811'UOyR0%211'@y8%511%311p051&SKr:r9r6r5r3r2r1%877654321'F&T6&T=r8r7%3221%5218&T8%12:5%9231r;%921C%;21?%62@3%>221p061p\8Q81&S3%12>D%22?Fp021pY6Q=1r=r<r4%Q2732?Q1EN1p051p0;1p0M1pS:Q71pS8Q81pY4QA1pY2QB1p[DQI1p[HQJ1p[BQK1p[FQL1pR<QI1pRLQL1").
Proof. intros LB FF sp scr sp' scr' W W' M M'. intros E Hs HW a (Ha & Hc & Ho). apply E. split. exact Ha. split. eapply aclient_mono. exact Hc. exact Hs. apply HW. exact Ho. Qed.
Lemma ek_tl : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "Q8'='B'Q2%2211%411&RI%611&S4%811'UOyR0%211'@y8%511%311p051&SK(9r7r8%33B21r6r5r4r3r2r1%;77654321r9%=71;87654p031pS:@1pS8A1pY2J1p[BQ11p[FQ21pR<O1pY:Q31pRLQ31").
Proof. intros LB b FF sp scr W M M'. intros E a (Ha & Hc & Ho). apply E. split. exact Ha. split. apply aclient_consb. exact Hc. exact Ho. Qed.
Lemma dk_tl : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "Q4'='B'Q2%2211%411&RI%611'UOyR0%211'@y8%511%311p051&SJ(9r6r7%33@21r5r4r3r2r1%:6654321r8%<61:7654p031pS:?1pS8@1p[BM1p[FN1pR<K1pY:O1pRLO1").
Proof. intros LB b FF sp scr M M'. intros D a Ha Hc HM. apply D. exact Ha. apply aclient_consb. exact Hc. exact HM. Qed.
Lemma ek_W : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "Q='='B'Q2%2211%411&RI%611&S4%811'UOyR0%211'@y8%511%311p051&SKr8r7r6r5r3r2r1%877654321&S3%1273%2285p021pY6L1r:r9r4%A732@?>1<p051p0;1pS:E1pS8F1pY4O1pY2Q01p[BQ71p[FQ81pR<Q51pRLQ81").
Proof. intros LB FF sp scr W W' M M'. intros E HW a (Ha & Hc & Ho). apply E. split. exact Ha. split. exact Hc. apply HW. exact Ho. Qed.
Lemma dk_trans : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "Q4'='B'Q2%2211%411&RI%611'UOyR0%211'@y8%511%311p051&SJr7r6r5r4r3r2%76654321r8%96187643r9%;613:986p031p061pSB?1pS@@1pS<A1p[BN1p[FO1pR<L1pRLO1").
Proof. intros LB FF sp scr M1 M2 M3. intros A B a Ha Hc D. apply B. exact Ha. exact Hc. apply A. exact Ha. exact Hc. exact D. Qed.
Lemma dk_grows : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "Q1'='B'Q2%2211%411&RI%611'UOyR0%211'@y8%511%311p051&SCr2r1%3221&SJr7r6r5r4r3%66543219p081pS:=1pS8>1p[BK1p[FL1pR<I1pRLL1").
Proof. intros LB FF sp scr M M'. intros G a _ _ D. apply G. exact D. Qed.
Lemma ek_piece : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "R='='B'Q2%2211%411&RI%611&S4%811'UOyR0%211'@y8%511%311p\851!p0@1'F&T6zr1%3221&T8&T<+2+R0%3221%5271%;271&Ir3r2%211%411'Gr5&UN%12M7%311r6%113%73L31p091p0?1pY6Q<1&R;vQ<vTCr;r:r9r8%77654321E&S3%123Hr4%A11%L11p041p071p0Q01pY6QM1&SKr7%27?>=1IM9p041p0F1pSFQC1pS:QF1pS8QG1pY2R01p[BR71p[FR81pR<R51pRLR81").
Proof. intros LB FF sp scr W M M' P. intros E X a (Ha & Hc & Ho). apply E. exact Ha. apply X. exact Ha. exact Hc. exact Ho. Qed.
Lemma ek_rt : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "QG'='B'Q2%2211%411&RI%611&S4%811'UOyR0%211'@y8%511%311p051&R=vQ<vTCr:&7r8r9%33C21r5r4r2r1%<8;:954321&T6&T=r7%22;1r6%421:%6231%725>&SKr=r<%3721EB7@?p051p071p0?1pS:M1pS8N1pY2Q71p[DQ>1p[HQ?1p[BQ@1p[FQA1pR@Q>1pR<Q?1pRLQB1").
Proof. intros LB FF FX sp scr sp' scr' W M M'.
intros [P _] H1 H2 a (Ha & Hc & _). apply P. exact Ha. apply aclient_app. eapply aclient_mono. exact Hc. intros x Hx. lia.
Qed.
Lemma aclient_narrow {BS ST} LB FF sp scr sp' scr' a :
aclient_g BS ST L ar LB FF sp scr a -> ~ (sp' - scr' <= a < sp') -> aclient_g BS ST L ar LB FF sp' scr' a.
Proof. intros Hc O. destruct Hc as [Hc|[Hc|Hc]]. left; exact Hc. right; left. split. exact (proj1 Hc). exact O. right; right; exact Hc. Qed.
Lemma dk_rt : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "QD'='B'Q2%2211%411&RI%611'UOyR0%211'@y8%511%311p051&R=vQ<vTCr9&7r7r8%33A21r4r3r2r1%<8;:954321&T6&T=r6%22;1r5%421:%6231%725>&SJr<r;%3621EB7@p051p071p0?1pS:M1pS8N1p[DQ;1p[HQ<1p[BQ=1p[FQ>1pR@Q;1pR<Q<1pRLQ?1").
Proof. intros LB FF FX sp scr sp' scr' M M'.
intros [P D] H1 H2 a Ha Hc HM. destruct (rng_dec a (sp' - scr') sp') as [I|O]. apply D. exact I.
rewrite P. exact HM. exact Ha. apply aclient_app. exact (aclient_narrow _ _ _ _ _ _ _ Hc O).
Qed.
Lemma ek_callee : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "R5'='B'Q2%2211%411&RI%611&S4%811'UOyR0%211'@y8%511%311p051&SDvQ<vTC&7r;r<%33D21r9r:%63E21r6r5r3r2r1%?9>=9654321&T6&T=r8%22<1r7%421;%6231%725?&R;r@r>%37JI21FG=&S3%12F@%22GBp021p051pY6Q@1&SK%17:9NOAIHp031p0>1p0@1p0H1pS:Q91pS8Q:1pY4QC1pY2QD1p[DQK1p[HQL1p[BQM1p[FQN1pR@QK1pR<QL1p8QO1pRLR01").
Proof. intros LB BX FF FX sp scr sp' scr' W W' M M'.
intros (P & _ & _) H1 H2 HW a (Ha & Hc & Ho). apply P. split. exact Ha. split.
apply aclient_appb. apply aclient_app. eapply aclient_mono. exact Hc. intros x Hx. lia.
apply HW. exact Hc. exact Ho.
Qed.
Lemma dk_callee : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "QK'='B'Q2%2211%411&RI%611&S4%811'UOyR0%211'@y8%511%311p051&SDvQ<vTC&7r:r;%33D21r8r9%63E21r5r4r3r2r1%?9>=9654321&T6&T=r7%22<1r6%421;%6231%725?&SJr>r<%3621GCA@p051p071p0?1pS:Q01pS8Q11pY4Q:1p[DQA1p[HQB1p[BQC1p[FQD1pR@QA1pR<QB1p8QE1pRLQF1").
Proof. intros LB BX FF FX sp scr sp' scr' W' M M'.
intros (P & D & K) H1 H2 a Ha Hc HM. destruct (rng_dec a (sp' - scr') sp') as [I|O]. replace a with (sp' - scr' + (a - (sp' - scr'))) by lia. apply D. lia.
apply K. exact Ha. 2: exact HM. apply aclient_appb. apply aclient_app. exact (aclient_narrow _ _ _ _ _ _ _ Hc O).
Qed.
Lemma apiece_retire : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "W@'='B'Q2%2211%411%4223%611&RI%811&R4'UOyR0%211'@y8%511%311p051'QA'S<&QBy5%221:!p0F1&SA&RMvQ:rD(9(Ar5r4%34OO21r3%54Q0Q121rC%83Q021rBrAr@r?&S0r>%211%C8BA876541&SE%1286&RE&SN&T=&T3r7&RGr6%211%5241+8%8221u8%<5;E21L&I&R;vQ<vTCrGr8%Q54R1R11?%Q64R1R21>rF%Q93R121z%:7987211Q9%<11&S9&R>%12Q@Q6+1%432H1'F&T6%12:M%O2N5&T<+2+R0%3221%7251%9271'R2&S>&UN%12RAQD&R1%C2IR2rE%3221&S@%11QA%95QOQL731%92RIQIr=%<5R0QM214%>3QF41&SC%N2Q8:%=21Q5%321R0r1%M2Q61&T8%123I%Q1231r2%R:11%QF11'G%J2S:RC%R@11rKrI%Q>221rJ%N3216%83S<61p0:1p0>1pY6SM1%RI1?'J%>3T0S0RG&R<rQ0%S74T3T3RNRM%S84T3T41RMrO%S;3T321%67R:R951R2R2S7%9281p0;1p0L1pY6T;1%S71Q2%RB11%?221pY6T?1&S6%14S2S=Q>R<rQ2rQ1rN%S=1Q;%SN8SM43DA2Q71%S;2BQ8&RL%125SI'8p0TA1%RC29SN%RD2:H%Q<3321%RF2=M%R521S<%Q?3TB1Q;%QL2@S@rL%11QE%S:11r;%11QDrQ6%11QF%QH3TL31p061p0QN1pY6U=1rQ4%S6371R5(:%QO3G21%<1R3%O1R4%R23U621p041pY6U<1'SB&S8vSO%211&S:r:r9%35Q<QIQ:21%84T@51T0p0:1p0D1p0Q01p0Q21p0Q61p0Q<1p0Q?1p0QA1pZNUH1pS<UJ1rH%@5RC1T<Q8RF%E4TMB1U3p041p0QM1p0R01p0R51p0RD1p0S91p0S>1p0SN1p0T91p0T?1p0TM1p0U;1p0U>1pRHV31pZ0VK1p[>VL1pZ<VM1pR:VN1pY2V91pS>VA1p[:W11pSLV>1p[8W31pSHV@1pZ6VD1pZ4VE1pZJVG1pS8VI1p2W71pY>W31pS0W51pR<W81pRLW;1").
Proof. intros LB FF LK cr A M model fx fx1 R pc R1 pc1 M1v W F k rs fl K.
intros HH [Hh MI] FLC FLNC FLV FLR MS MG FZ WC WD FL0 KONT.
pose proof (HAJ.aior_lazy _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (AWF & LZ).
pose proof (vis_pack LB _ LK cr A M model HH) as (HOFF & _).
set (H := ahid A model) in *.
unfold cfg. eapply (L5LZ.cps_of_msteps_lazy RSEGS H A fx fx1 R _ M R1 _ M1v model K HOFF wx_nowrap (L5LZ.lazy_cover_ahid A model) AWF MI Hh MS).
intros model1 MI1 SBM1 HC1.
set (M1 := munrestrict H M M1v).
assert (M1vis : mrestrict H M1 = M1v). { apply L5LZ.mrestrict_of_munrestrict. exact HC1. }
assert (FRM1 : forall a, 0 <= a < 2 ^ 64 -> ~ W a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha Hn. unfold M1, munrestrict. destruct (H (Z_to_bv 64 a)) eqn:E. reflexivity. rewrite (FZ a Ha Hn). unfold mrestrict. rewrite E. reflexivity. }
assert (MGM1 : mem_grows M M1).
{ intros x Hx. unfold M1, munrestrict. destruct (H x) eqn:E. exact Hx. apply MG. unfold mrestrict. rewrite E. exact Hx. }
assert (VML : vml_of model1 = vml_of model). { unfold vml_of. rewrite (L5LZ.sbm_vmmaps _ _ SBM1), (L5LZ.sbm_lazy _ _ SBM1). reflexivity. }
apply (KONT M1 model1).
- rewrite VML. apply (retire_frame LB FF LK cr A M M1 _ F k rs fl HH FLC FLNC).
+ intros a Ha Hne. destruct (H (Z_to_bv 64 a)) eqn:E.
* left. unfold M1, munrestrict. rewrite E. reflexivity.
* assert (EM : M1 (Z_to_bv 64 a) = M1v (Z_to_bv 64 a)). { unfold M1, munrestrict. rewrite E. reflexivity. }
destruct (WD a) as [HW|HW].
-- destruct (WC a Ha HW) as [X|X]. exfalso; exact (Hne X). right; exact X.
-- left. rewrite EM, (FZ a Ha HW). unfold mrestrict. rewrite E. reflexivity.
+ apply (proj1 (u8_at_vis H M1 fl 0 FLV ltac:(lia) ltac:(lia))). rewrite M1vis. exact FL0.
+ exact MGM1.
- split. exact (eq_trans (L5LZ.sbm_halted _ _ SBM1) Hh). exact MI1.
- apply L5LZ.sbm_model_rt. exact SBM1.
- apply L5LZ.sbm_ahid. exact SBM1.
- exact M1vis.
- exact MGM1.
- exact FRM1.
- intros a Ha. unfold M1. apply L5LZ.munrestrict_visible. exact Ha.
Qed.
Lemma astk_after_eq : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "SC'='B'Q2%2211%411&RI%611&R4'UOyR0%211'@y8%511%311p051p\862&RO&RMvQ:r=r<r;r:r9r8r5%9887654321&SGvTCr4%342751&SC%12:9'F&T6zr1%3221&T8&T<+2+R0%3221%5271%;271&T=&RB%11C+XPPP0%4221r2%A221+Q?%>2=1%@241%F241&Ir7%=2Q21r3%J221%G22Q5%M221%711'G&UN%12QJQ5%Q@11r>%113%63QI31p081p0A1p0M1pY6R91r6%O2C1%Q;21Q9%Q82Q:E%Q>221%?2R8N%QM11(4%11R7%D3R731%M11p071pY6RF1%Q;2R1R0%QG21=%QH2R2R4%QI2QHR5%R14R0HR8R7p021p041p061p091p0G1p0R21p0R51p0R:1p[DS41p[HS51p[BS61p[FS71pY0RI1pS@RK1pS<RM1pS8RN1p2S:1pY>S81pS0S:1pR<S;1pRLS>1").
Proof. intros LB FF LK cr A M M1 M2 V sp scr sp' scr'.
intros HH (A16 & SLO & SHI & SPT & DSCR & DUP) MG PRES SDEF H1 H2 H0.
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TOP & _).
assert (D : forall x, (sp - scr <= x < sp \/ sp <= x < ar_stack_top ar) -> M2 (Z_to_bv 64 x) <> None).
{ intros x Hx2. destruct (rng_dec x (sp' - scr') sp') as [I|O].
- apply SDEF. exact I.
- rewrite PRES. apply MG. destruct (Z_lt_le_dec x sp).
+ replace x with (sp - scr + (x - (sp - scr))) by lia. apply DSCR. lia.
+ replace x with (sp + (x - sp)) by lia. apply DUP. lia.
+ lia. + lia. + exact O. }
split. exact A16. split. lia. split. lia. split. exact SPT. split.
- intros j Hj. apply D. lia.
- intros j Hj. apply D. lia.
Qed.
Lemma ek_mem : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "RJ'='B'Q2%2211%411&RI%611!p061&S4%:11'UOyR0%211'@y8%511%311p\851'F&T6zr1%3221&T8&T<+2+R0%3221%5271%;271&R;vQ<vTCr<r;r8r7r2%877654321&Ir3%511%311'Gr5&UNr4%22Q41%411r6%113%83Q331p0:1p0?1p0I1pY6QF1&T=r9%221G%32G:%Q9221r:%Q;2K1r>r=%Q37Q2Q121Q0OQ<&S3%12Q0N%71L%N11p031p061pY6R71&SK%17;:Q9Q8Q6INp031p0>1p0A1p0G1pS:QN1pS8QO1pY2R81pR8R;1p[DRB1p[HRC1p[BRD1p[FRE1pR<RB1pRLRE1").
Proof. intros LB FF sp scr sp' scr' D W M M'.
intros P H1 H2 HW a (Ha & Hc & Ho). apply P. exact Ha. eapply aclient_mono. exact Hc. intros x Hx. lia. apply HW. exact Hc. exact Ho.
Qed.
Lemma dk_mem : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "S9'='B'Q2%2211%411&RI%611!p061'UOyR0%211'@y8%511%311p\851'F&T6zr1%3221&T8&T<+2+R0%3221%5271%;271&R;vQ<vTCr;r:r7r6r2%877654321&Ir3%511%311'Gr5&UNr4%22Q41%411%=12%73Q221p091p0>1p0H1pY6QC1&T=%12ED%Q621Q4%Q32Q5G%Q9221%?2QAG%?11(4%11Q@%E3Q@31%J11p071pY6R01%Q01Q?%I19%K3QF17%Q011p041pY6R61'J%Q81QF%Q511%3221pY6R;1%H2Q>Q=r9r8%K221%R0241r<%R22QC1&SJr?r>r=%4632169QGp061p091p0?1p0E1p0L1p0Q:1pS:R@1pS8RA1pR8RJ1p[DS11p[HS21p[BS31p[FS41pR<S11pRLS41").
Proof. intros LB FF sp scr sp' scr' D M M'.
intros P SD DD Ddec H1 H2 a Ha Hc HM. destruct (Ddec a) as [X|X]. apply DD. exact X.
destruct (rng_dec a (sp' - scr') sp') as [I|O]. apply SD. exact I.
rewrite P. exact HM. exact Ha. exact (aclient_narrow _ _ _ _ _ _ _ Hc O). exact X.
Qed.
Lemma fresh_block_not_client : ltac2:(TCodec.tc2 tcn__asan_L5StepARB0 "R@'='B'Q2%2211%411&RI%611&R4'UOyR0%211'@y8%511%311p051&RO&RMvQ:r<r;r:r9r8r7r6%9887654321'F&T6+SoonPPPPP0&RBvTC%211%5241&T<+2+Q?%3221%:261%<261&R:vQ<r5r4%443=21&R3r?%23F51&RJ%13IH3%F2KI&T8&T3%12NM%32M1%L251&I&R;rBrA%37CM21Q8Q7Q4%511p071p0>1p0A1p0E1p0K1p0Q91pY6R21p[2R31p[<R41p[BR51p[FR61pY0QI1pS8QK1p2R71pY>R51pS0R71pR<R81pRLR;1").
Proof. intros LB FF LK cr A M V sp scr q n a.
intros HH SPT (B0 & B1 & B2 & B3 & B4 & B5) BA FA Ha Hc.
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _).
rewrite (aly_img_lo L C LY), (aly_img_hi L C LY) in B1. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in B5.
destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]].
- destruct Hc as (b & Hb & X). specialize (BA b Hb). lia.
- lia.
- rewrite (aly_img_lo L C LY), (aly_img_hi L C LY) in Hc. lia.
- destruct Hc as (f & Hf & X). specialize (FA f Hf). lia.
- unfold in_shadow_of, S, SB in Hc. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
- destruct Hc as (f & Hf & X). pose proof (WF f Hf) as (Y1 & Y & _). unfold in_shadow_of, S, SB in X. unfold app_mem, FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in FSAPP. lia.
- destruct Hc as (b & Hb & X). pose proof (proj1 (WB b Hb)) as (Y0 & _ & _ & _ & Y & Y2). unfold in_shadow_of, S, SB in X. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Y2. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
End WithIface.
End SCFG_1.
End L5SAR.
