(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AsanPlanCore FxBase.
Import ListNotations. Import AX2. Import AX2B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__SegFastHavoc () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanCore.APC."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3.AX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3B.AX2B."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SegFastHavoc.AX2H."], [["1bool"; "1list"; "1true"; "2eq"; "3Z"; "0K"; "4havoc1pB"; "4kentry_apart_bpB"; "4kn_havoc"; "4kn_havocB"; "5ELit"; "5expr"; "5kentry"; "5sprep"; "5zlit64"; "6bctx"]; ["6ranges_apart_pB"; "7apart_c"; "7havoc1pF"; "7kn_havocF"; "7kn_havocMF"; "7mk_m1o"; "7quick"; "7same_fast"; "0bc"; "0k"; "0sp"; "0ub"; "0uk"; "0un"; "0z1"; "0z2"]]).
Module AX2H.
Definition same_fast (bc : bctx) (ub : expr) : bool :=
if shares_var ub ub then
if lin_nowrapRB bc ub then match lsub_e (snd (lin_of ub)) (snd (lin_of ub)) with [] => true | _ => false end else false
else false.
Definition apart_c (uk m1 k m2 : Z) : bool := let d := k - uk in if Z.leb m1 d then true else Z.leb d (- m2).
Definition quick (m1o : option Z) (ub : expr) (uk : Z) (K : kentry) : bool :=
match m1o with
| Some m1 =>
match K with
| KWord (SA b k) w _ => if Nat.leb w 8 then if BASF.expr_eqbF b ub then apart_c uk m1 k (zlit64 (Z.of_nat w)) else false else false
| KZero (SA b k) (ELit z2) | KBlob (SA b k) (ELit z2) _ | KFill (SA b k) (ELit z2) _ | KUnk (SA b k) (ELit z2) =>
if BASF.expr_eqbF b ub then apart_c uk m1 k (zlit64 z2) else false
| _ => false
end
| None => false
end.
Definition mk_m1o (bc : bctx) (ub : expr) (un : expr) : option Z :=
match un with ELit z1 => if same_fast bc ub then Some (zlit64 z1) else None | _ => None end.
Lemma same_apart : ltac2:(TCodec.tc2 tcn__SegFastHavoc "Q7'?'=';'4'3'0&Gr7r5%3221(2%73621&A&>r4%211r3r2%511%74;431%@3?1:&@r9r8r6(:%11B%21;%7865E42E>1%I3H1Cp0:1p0D1pR0M1pQDN1pQNO1pQJQ01pQHQ21pQFQ41pQBQ61").
Proof.
intros bc sp ub uk z1 k z2 HS HA. unfold same_fast in HS.
destruct (shares_var ub ub) eqn:SV; [|discriminate]. destruct (lin_nowrapRB bc ub) eqn:NW; [|discriminate].
destruct (lsub_e (snd (lin_of ub)) (snd (lin_of ub))) eqn:LS; [|discriminate].
unfold ranges_apart_pB. cbv zeta.
match goal with |- (if ?c then true else _) = true => destruct c; [reflexivity|] end.
match goal with |- (if ?c then true else _) = true => destruct c; [reflexivity|] end.
unfold lin_apartB. rewrite SV. unfold lin_apart0B. rewrite NW. cbv zeta. rewrite LS. cbn [andb].
unfold lin_testB. cbn [lin_range].
replace (fst (lin_of ub) + k - fst (lin_of ub) - uk) with (k - uk) by ring.
unfold apart_c in HA. cbv zeta in HA. destruct (Z.leb (zlit64 z1) (k - uk)); [reflexivity|]. rewrite HA. reflexivity.
Qed.
Lemma quick_sound : ltac2:(TCodec.tc2 tcn__SegFastHavoc "N'?'=';'4'<'3'0&F&Er6r4r2%43321r3r1%843521(2%<3;21&7r7r5%362<1;8:%A3@16p061p<D1pQLG1pQJG1pQHI1pQFK1pQBM1").
Proof.
intros bc sp ub uk un K H. unfold mk_m1o in H. destruct un as [z1| | | | | | |]; try discriminate H.
destruct (same_fast bc ub) eqn:HS; [|discriminate H]. cbn [quick] in H.
destruct K as [[b k] w v|[b k] len|[b k] len bk|lo hi|e m|e lo hi|[b k] len|a1 n1 a2 n2|[b k] len c|[b k] len]; try discriminate H; cbn [APC.kentry_apart_bpB].
- destruct (Nat.leb w 8); [|discriminate H]. destruct (BASF.expr_eqbF b ub) eqn:E; [|discriminate H].
apply BASF.expr_eqbF_true in E. subst b. cbn [andb]. apply same_apart; assumption.
- destruct len as [z2| | | | | | |]; try discriminate H. destruct (BASF.expr_eqbF b ub) eqn:E; [|discriminate H].
apply BASF.expr_eqbF_true in E. subst b. apply same_apart; assumption.
- destruct len as [z2| | | | | | |]; try discriminate H. destruct (BASF.expr_eqbF b ub) eqn:E; [|discriminate H].
apply BASF.expr_eqbF_true in E. subst b. apply same_apart; assumption.
- destruct len as [z2| | | | | | |]; try discriminate H. destruct (BASF.expr_eqbF b ub) eqn:E; [|discriminate H].
apply BASF.expr_eqbF_true in E. subst b. apply same_apart; assumption.
- destruct len as [z2| | | | | | |]; try discriminate H. destruct (BASF.expr_eqbF b ub) eqn:E; [|discriminate H].
apply BASF.expr_eqbF_true in E. subst b. apply same_apart; assumption.
Qed.
Definition havoc1pF (bc : bctx) (sp : sprep) (m1o : option Z) (ub : expr) (uk : Z) (un : expr) (K : kentry) : list kentry :=
if quick m1o ub uk K then [K] else APC.havoc1pB bc sp ub uk un K.
Lemma havoc1pF_eq : ltac2:(TCodec.tc2 tcn__SegFastHavoc "K'?'=';'4'<'3'1%113&Br6r5&Er4r2%33521r3r1%978735241&6%16:97463%?3=31p<A1pQLD1pQJD1pQHF1pQFH1pQBJ1").
Proof.
intros. unfold havoc1pF. destruct (quick (mk_m1o bc ub un) ub uk K) eqn:Q; [|reflexivity].
unfold APC.havoc1pB. rewrite (quick_sound _ sp _ _ _ _ Q). rewrite orb_true_r. reflexivity.
Qed.
Definition kn_havocF (bc : bctx) (ub : expr) (uk : Z) (un : expr) : list kentry :=
let sp := mk_sprepB bc ub uk un in
let m1o := mk_m1o bc ub un in
List.flat_map (havoc1pF bc sp m1o ub uk un) (bc_fk bc).
Lemma kn_havocF_eq : ltac2:(TCodec.tc2 tcn__SegFastHavoc "D'?';'4'3'1'<%211&Cr4r3r2r1%544321&9%146543%<3931pQL?1pQJ?1pQHA1pQBC1").
Proof.
intros. unfold kn_havocF, APC.kn_havocB. cbv zeta. f_equal.
apply functional_extensionality; intros K. apply havoc1pF_eq.
Qed.
Definition kn_havocMF (k : list kentry) := kn_havocF (mkbc k).
Lemma kn_havocMF_eq : ltac2:(TCodec.tc2 tcn__SegFastHavoc "='3'1'<%211';'4pQL23pQJ21pQH41pQD61&D&8%<3321").
Proof.
apply functional_extensionality; intros k. unfold kn_havocMF.
repeat (apply functional_extensionality; intros ?). rewrite kn_havocF_eq. rewrite APC.kn_havocB_eqf. reflexivity.
Qed.
End AX2H.
