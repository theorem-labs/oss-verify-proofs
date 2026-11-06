(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B.
Import ListNotations. Import AX2. Import AX2B.
Unset Lia Cache.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__SegFastLoad () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.Riscv.Instr."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3.AX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3B.AX2B."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SegFastLoad.AX2L."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SegFastLoad.AX2L.WithSegs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SegFastLoad.AX2L.WithSegs.Ctx."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."], [["1S"; "1bool"; "1cons"; "1false"; "1list"; "1nat"; "1nil"; "1pair"; "1prod"; "1snd"; "1true"; "2and"; "2eq"; "2not"; "3Z"; "3positive"]; ["0K"; "4Segment"; "5instr"; "6EVar"; "6PTLeaf"; "6expr"; "6facts_of"; "6itab"; "6kentry"; "6lres"; "6ptree"; "6s_know"; "6scripts"; "6sidecond"; "6stepres"; "6sym_execTX"]; ["6sym_execTX_go"; "6sym_state"; "6sym_stepX"; "7bctx"; "7know_lookupA0B"; "7know_lookupA0I"; "7mk_kix"; "7mkbc"; "7sym_stepXBI"; "7tagged"; ":stepX_g"; "9sym_execTXBI2"; "9sym_execTXBI2_go"; "9sym_stepXBI2"; "8add2"; "8bucket2"]; ["8build2"; "8cand2"; "8fits2"; "8gran2"; "8has2"; "8know_lookupA0I2"; "8mk_kix2"; "8narrow2"; "8select2"; "8vkey"; "8vtab"; "8wide2"; ";filter"; "<div"; "<le"; "<lt"]; ["0a"; "0acc"; "0b"; "0bc"; "0ck"; "0e"; "0first"; "0fuel"; "0g"; "0g'"; "0hints"; "0i"; "0kn"; "0kn0"; "0kx"; "0l"]; ["0n"; "0rb"; "0rest"; "0rk"; "0s"; "0scr"; "0segs"; "0ss"; "0stops"; "0sx"; "0t"; "0v"; "0v'"; "0w"; "0x"]]).
Module AX2L.
Definition gran2 (a : Z) : Z := Z.shiftr a 6.
Definition fits2 (s e : Z) : bool := if Z.ltb s e then Z.leb (gran2 (e - 1) - gran2 s) 1 else false.
Definition has2 (s e g : Z) : bool := if Z.eqb g (gran2 s) then true else Z.eqb g (gran2 (e - 1)).
Definition vcell (K : kentry) : option (nat * Z * Z) :=
match K with
| KWord (SA (EVar v) kk) w _ => if fits2 kk (kk + Z.of_nat w) then Some (v, kk, kk + Z.of_nat w) else None
| _ => None
end.
Definition narrow2 (v : nat) (g : Z) (K : kentry) : bool :=
match vcell K with Some (v', s, e) => if Nat.eqb v v' then has2 s e g else false | None => false end.
Definition wide2 (K : kentry) : bool :=
if kx_candf K then (match vcell K with Some _ => false | None => true end) else false.
Definition cand2 (v : nat) (g : Z) (K : kentry) : bool := (narrow2 v g K || wide2 K)%bool.
Definition vtab : Type := ptree (ptree (list (positive * kentry))).
Record kix2 : Type := KX2 { k2_w : list (positive * kentry); k2_v : vtab }.
Definition vkey (v : nat) : positive := Pos.of_succ_nat v.
Definition inner2 (t : vtab) (v : nat) : ptree (list (positive * kentry)) :=
match pt_get t (vkey v) with Some i => i | None => PTLeaf end.
Definition bucket2 (t : vtab) (v : nat) (g : Z) : list (positive * kentry) := kx_bucket (inner2 t v) g.
Definition add2 (v : nat) (g : Z) (x : positive * kentry) (t : vtab) : vtab := pt_set (vkey v) (kx_add g x (inner2 t v)) t.
Fixpoint build2 (kn : list kentry) (i : positive) : list (positive * kentry) * vtab :=
match kn with
| [] => ([], PTLeaf)
| K :: rest =>
let '(w, t) := build2 rest (Pos.succ i) in
match vcell K with
| Some (v, s, e) =>
let g1 := gran2 s in let g2 := gran2 (e - 1) in
let t1 := add2 v g1 (i, K) t in
(w, if Z.eqb g1 g2 then t1 else add2 v g2 (i, K) t1)
| None => if kx_candf K then ((i, K) :: w, t) else (w, t)
end
end.
Definition mk_kix2 (kn : list kentry) : kix2 := let r := build2 kn xH in KX2 (fst r) (snd r).
Definition select2 (kx2 : kix2) (v : nat) (rk : Z) : list kentry :=
kx_merge (bucket2 (k2_v kx2) v (gran2 rk)) (k2_w kx2).
Definition know_lookupA0I2 (bc : bctx) (kx : kix) (kx2 : kix2) (segs : list Segment) (rb : expr) (rk : Z)
(n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
match hints, n, rb with
| [], S _, EVar v => know_lookupA0B bc segs (select2 kx2 v rk) rb rk n sx [] acc
| _, _, _ => know_lookupA0I bc kx segs rb rk n sx hints acc
end.
Lemma gran2_div : ltac2:(TCodec.tc2 tcn__SegFastLoad ":'>'<&QCr1%211&QM+R0%2241%73841pT291").
Proof. intros a. unfold gran2. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.
Lemma gran2_mono : ltac2:(TCodec.tc2 tcn__SegFastLoad "='>&QNr2r1%3221&QCr3%211%316%8221p061pT6;1pT2<1").
Proof. intros a b H. rewrite !gran2_div. apply Z.div_le_mono; lia. Qed.
Lemma gran2_between : ltac2:(TCodec.tc2 tcn__SegFastLoad "L'>&QNr3r1%3221&QOr2%2215'<'1&QBr5r4%3221(:%73621&QDr6&QC%117%43391%=3<17p071p0@1p0D1pUNI1pT<J1pU:K1").
Proof.
intros s e x Hs He Hf. unfold fits2, has2 in *.
destruct (Z.ltb s e); [|discriminate]. apply Z.leb_le in Hf.
pose proof (gran2_mono s x Hs) as A. pose proof (gran2_mono x (e - 1) ltac:(lia)) as B.
destruct (Z.eqb_spec (gran2 x) (gran2 s)); [reflexivity|].
destruct (Z.eqb_spec (gran2 x) (gran2 (e - 1))); [reflexivity|]. exfalso. lia.
Qed.
Lemma vkey_inj : ltac2:(TCodec.tc2 tcn__SegFastLoad ">'5'<'?&QIr2%211r1%411%73631r3%93:16p031pT6<1pT2=1").
Proof. intros a b H. apply SuccNat2Pos.inj. exact H. Qed.
Lemma bucket2_add_same : ltac2:(TCodec.tc2 tcn__SegFastLoad "J'5'>'8'?'H%3221&QJ'<'4%114&Q?&Q>r4r3r2r1%544321%73154(2%93476%23?61%>3<41pUF@1pUNB1pTBG1pUHI1").
Proof. intros. unfold bucket2, add2. unfold inner2 at 1. rewrite pt_gss. apply kx_bucket_add_same. Qed.
Lemma bucket2_add_other_g : ltac2:(TCodec.tc2 tcn__SegFastLoad "N'5'>'8'?'H%3221&QJ&='<r4r3%33:21%511'4%119&Q?&Q>r6r2%342:91r5%63241%73452%?3921p0<1pUFC1pUNE1pTDJ1pTBK1pUHM1").
Proof. intros. unfold bucket2, add2. unfold inner2 at 1. rewrite pt_gss. apply kx_bucket_add_other. assumption. Qed.
Lemma bucket2_add_other_v : ltac2:(TCodec.tc2 tcn__SegFastLoad "Q0'5'>'8'?'H%3221&QJ&='<r6r5%33;21%511'4%119&Q?&Q>r4r3r2%44;321r7%7321<%8342=%@3:21p0=1pUFD1pUNF1pTDK1pTBL1pUJN1pUHO1").
Proof.
intros v v' g g' x t H. unfold bucket2, add2. unfold inner2 at 1. rewrite pt_gso; [reflexivity|].
intros E. apply H. apply vkey_inj. exact E.
Qed.
Lemma bucket2_leaf : ltac2:(TCodec.tc2 tcn__SegFastLoad "F'5'>'<'4'8'?'H%3221%511&Q?(D'J%114%311r2r1%73321(6%11;%A3;31pTBC1pUHE1").
Proof. intros. unfold bucket2, inner2. rewrite pt_get_leaf. apply kx_bucket_leaf. Qed.
Lemma build2_spec : ltac2:(TCodec.tc2 tcn__SegFastLoad "QC'4'H%211'?'8%1224%611&QJ'<%5232&Q@r4r3%3221(7r2r1%34;:21%:3951';&QL&QK&9%13DF7%311qUND1&Q9r5%221A%93H41%F3HB1'5'>&Q?%13GCB&QG%13HE=qUNQ01r7r6%>221%E3Q441%Q23Q481pTB;1pUH=1%J2?1p0L1pUFQ81pULQ:1pTHQ>1pTJQ@1").
Proof.
induction kn as [|K rest IH]; intros i w t H.
- cbn in H. injection H as <- <-. split; [reflexivity|]. intros v g. rewrite bucket2_leaf. reflexivity.
- cbn [build2] in H. destruct (build2 rest (Pos.succ i)) as [w' t'] eqn:Hb.
destruct (IH (Pos.succ i) w' t' Hb) as (A & B). clear IH.
cbn [tagged List.filter snd]. unfold wide2, narrow2.
destruct (vcell K) as [[[v0 s] e]|] eqn:HV.
+ match type of H with (_, ?G) = _ => set (t1 := G) in H end.
injection H as <- <-.
replace (if kx_candf K then false else false) with false by (destruct (kx_candf K); reflexivity).
split; [exact A|]. intros v g.
assert (STEP : bucket2 t1 v g = if (if Nat.eqb v v0 then has2 s e g else false) then (i, K) :: bucket2 t' v g else bucket2 t' v g).
{ subst t1. destruct (Nat.eqb_spec v v0) as [->|NV].
- unfold has2. destruct (Z.eqb_spec (gran2 s) (gran2 (e - 1))) as [EQ|NE].
+ destruct (Z.eqb_spec g (gran2 s)) as [->|NE1].
* rewrite bucket2_add_same. reflexivity.
* rewrite bucket2_add_other_g by exact NE1. destruct (Z.eqb_spec g (gran2 (e - 1))); [congruence|reflexivity].
+ destruct (Z.eqb_spec g (gran2 s)) as [->|NE1].
* rewrite bucket2_add_other_g by exact NE. rewrite bucket2_add_same. reflexivity.
* destruct (Z.eqb_spec g (gran2 (e - 1))) as [->|NE2].
-- rewrite bucket2_add_same. rewrite bucket2_add_other_g by exact NE1. reflexivity.
-- rewrite bucket2_add_other_g by exact NE2. rewrite bucket2_add_other_g by exact NE1. reflexivity.
- destruct (Z.eqb (gran2 s) (gran2 (e - 1))); rewrite ?bucket2_add_other_v by exact NV; reflexivity. }
rewrite STEP, B. reflexivity.
+ destruct (kx_candf K); injection H as <- <-.
* split; [rewrite A; reflexivity|]. intros v g. rewrite B. reflexivity.
* split; [exact A|]. intros v g. rewrite B. reflexivity.
Qed.
Lemma narrow2_not_wide2 : ltac2:(TCodec.tc2 tcn__SegFastLoad "D'5'>'H'<'1&QGr3r2r1%43321(:%83721&QK%116(3%<3;21p051pQ2?1pTBA1pUHC1").
Proof. intros v g K. unfold narrow2, wide2. destruct (vcell K) as [[[v' s] e]|]; [|discriminate]. destruct (kx_candf K); reflexivity. Qed.
Lemma select2_eq : ltac2:(TCodec.tc2 tcn__SegFastLoad "G'4'H%211'5'>'<&QH&QFr3%211r2r1%63321&QL&QA&QC%115%3271%53A1:%>3A71pU8@1pUHB1pTJD1").
Proof.
intros kn v rk. unfold select2, mk_kix2. destruct (build2 kn 1%positive) as [w t] eqn:Hb. cbn [k2_w k2_v fst snd].
destruct (build2_spec kn 1%positive w t Hb) as (A & B). rewrite B, A.
apply (kx_merge_filters (narrow2 v (gran2 rk)) wide2 kn 1%positive (narrow2_not_wide2 v (gran2 rk))).
Qed.
Lemma know_lookupA0B_skip2 : ltac2:(TCodec.tc2 tcn__SegFastLoad "QB'Q3'4'A%211'H%411'5'>'1'M%911'<&QAr5&QCr4%211r7%63521(3%93<21'I&Q4r:r9(2r8%23G1:(Cr6%211(0%11Ar3(6%11Kr2%?9>=:7H5421%@9?>E8I6532%L3B21p0D1pT4O1pUDQ21pU2Q51pU8Q51pUHQ71pU6Q91pQ2Q;1pU>Q=1pT8QA1").
Proof.
intros bc segs K rest v rk n sx acc HC. unfold cand2 in HC. apply Bool.orb_false_iff in HC as [HN HW].
unfold wide2 in HW. destruct (kx_candf K) eqn:HF; [|apply know_lookupA0B_skipf; [reflexivity|exact HF]].
unfold narrow2 in HN. destruct (vcell K) as [[[v' s] e]|] eqn:HV; [|discriminate].
destruct K as [[kb kk] w val| | | | | | | | |]; try discriminate HV. cbn [vcell] in HV.
destruct kb as [|v0| | | | | |]; try discriminate HV.
destruct (fits2 kk (kk + Z.of_nat w)) eqn:FT; [|discriminate]. injection HV as <- <- <-.
cbn [know_lookupA0B].
destruct (Nat.eqb_spec v v0) as [->|NV].
- rewrite rel_lit_same.
destruct (Z.leb kk rk && Z.leb (rk + Z.of_nat (S n)) (kk + Z.of_nat w))%bool eqn:E.
+ exfalso. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
rewrite (gran2_between kk (kk + Z.of_nat w) rk) in HN; [discriminate|lia|lia|exact FT].
+ destruct (Z.leb (rk + Z.of_nat (S n)) kk || Z.leb (kk + Z.of_nat w) rk)%bool; reflexivity.
- rewrite rel_lit_other; [reflexivity|]. cbn [expr_eqb]. apply Nat.eqb_neq. exact NV.
Qed.
Lemma know_lookupA0B_filter2 : ltac2:(TCodec.tc2 tcn__SegFastLoad "Q='Q3'4'A%211'H%411'5'>'1'M%911'<'I&Q4r8r7&QL&QAr5&QCr4%211%5241r6%83D21(C%118(0r3%211r2(6%11Hr1%E9DC:8>5421%F9ED<9?6532%I3H21pT4K1pUDN1pU2Q11pU8Q11pUHQ31pU0Q51pU>Q81pT8Q<1").
Proof.
intros bc segs l v rk n sx. induction l as [|K rest IH]; intros acc; [reflexivity|].
cbn [List.filter]. destruct (cand2 v (gran2 rk) K) eqn:HC.
- cbn [know_lookupA0B]. rewrite !IH.
destruct K as [[kb kk] w val|[kb kk] len|[kb kk] len bk|lo hi|e m|e lo hi|a wn|a1 n1 a2 n2|[kb kk] len c|[kb kk] len]; try reflexivity.
- rewrite know_lookupA0B_skip2 by exact HC. apply IH.
Qed.
Theorem know_lookupA0I2_eq : ltac2:(TCodec.tc2 tcn__SegFastLoad "Q:'Q3'4'H%211'A%411'E'>'5'1%911'M%;11'<'I&QEr9&Q6r8%211&QF%113r7r6r5r4r3r2r1%>:=:87654321&Q4%19?9=876543%C3B31pT4E1pTFH1pUDJ1pU2L1pU8N1pU4Q01pU>Q21pTJQ51pT8Q91").
Proof.
intros bc kn segs rb rk n sx hints acc. unfold know_lookupA0I2.
destruct hints as [|h hs]; [|apply know_lookupA0I_eq]. destruct n as [|n]; [apply know_lookupA0I_eq|].
destruct rb; try apply know_lookupA0I_eq.
rewrite select2_eq. apply know_lookupA0B_filter2.
Qed.
Section WithSegs.
Variable segs : list Segment.
Section Ctx.
Variable bc : bctx. Variable kx : kix.
Definition stepX_g :=
ltac:(let t := eval cbv beta delta [sym_stepXBI sym_stepBI sym_readBI know_lookupABI] in (@sym_stepXBI segs bc kx) in
lazymatch t with context [know_lookupA0I bc kx segs] => idtac | _ => fail "abstraction target does not occur" end;
let t' := eval pattern (know_lookupA0I bc kx segs) in t in
lazymatch t' with ?F _ => exact F end).
Lemma stepX_g_ref : ltac2:(TCodec.tc2 tcn__SegFastLoad "D'<'5'B'Q1'L'NpU<21pU@41pTH61pQ281&Q:&Q5vR3vR>vRF%43321%611&Q8%13465%C3:31").
Proof. reflexivity. Qed.
End Ctx.
Definition sym_stepXBI2 (bc : bctx) (kx : kix) (kx2 : kix2) := stepX_g bc (know_lookupA0I2 bc kx kx2 segs).
Lemma sym_stepXBI2_eq : ltac2:(TCodec.tc2 tcn__SegFastLoad "N'5'B'Q1'L'<'N&Q=&Q7&F&Kr2%211%411%611&Q6%114&QF%116r4r3r1%?786432;1&Q2vRF%25165>4%E3D41pU<G1pU@I1pTHK1pQ2M1").
Proof.
intros. unfold sym_stepXBI2.
replace (know_lookupA0I2 (mkbc (facts_of (s_know ss))) (mk_kix (s_know ss)) (mk_kix2 (s_know ss)) segs)
with (know_lookupA0I (mkbc (facts_of (s_know ss))) (mk_kix (s_know ss)) segs).
- rewrite stepX_g_ref. apply sym_stepXBI_eq.
- repeat (apply functional_extensionality; intros ?). rewrite know_lookupA0I2_eq, know_lookupA0I_eq. reflexivity.
Qed.
Fixpoint sym_execTXBI2_go (bc : bctx) (kx : kix) (kx2 : kix2) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z)
(ss : sym_state) (ck : sym_state) : sym_state :=
match fuel with
| O => if s_clean ss then ss else ck
| S f =>
if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (if s_clean ss then ss else ck) else
match itab_lookup t (s_pc ss) with
| None => if s_clean ss then ss else ck
| Some i =>
match sym_stepXBI2 bc kx kx2 K i ss scr_nil with
| SOk ss' [] _ => sym_execTXBI2_go bc kx kx2 t K f false stops ss' (if s_clean ss' then ss' else ck)
| _ => if s_clean ss then ss else ck
end
end
end.
Definition sym_execTXBI2 (bc : bctx) (kx : kix) (kx2 : kix2) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z)
(ss : sym_state) : sym_state :=
sym_execTXBI2_go bc kx kx2 t K fuel first stops (clr ss) (clr ss).
Lemma sym_execTXBI2_go_eq : ltac2:(TCodec.tc2 tcn__SegFastLoad "Q6&G'5'1'4'>%211'Q1'<&Q<&Q7&F&Kr2%211%411%611&Q6%114&QF%116r7r6r5r4r3r1%B:;9765432>1&Q0vRF%28198765A4%G3H41pT:I1pU@J1pUBL1pT>Q01pT@Q21pQ2Q31pUFQ51").
Proof.
intros t K fuel. induction fuel as [|f IH]; intros first stops ss ck; [reflexivity|].
cbn [sym_execTXBI2_go sym_execTX_go].
destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [reflexivity|].
destruct (itab_lookup t (s_pc ss)) as [i|]; [|reflexivity].
rewrite sym_stepXBI2_eq. destruct (sym_stepX segs K i ss scr_nil) as [ss' scs scr'|] eqn:E; [|reflexivity].
destruct scs; [|reflexivity].
rewrite <- (sym_stepX_know _ _ _ _ _ _ _ _ E). apply IH.
Qed.
Lemma sym_execTXBI2_eq : ltac2:(TCodec.tc2 tcn__SegFastLoad "Q;'4'H%211&G'5'1'>%711'Q1'<&Kr1%211r7%53<21&Q;&Q7&Fr8%211%411&Q6%114&QF%116r6r5r4r3r2%?9:86A54321&OvRF%271D87654%I3J41p0E1pU@L1pUBN1pT>Q11pT@Q31pQ2Q41pUFQ61pTLQ81").
Proof.
intros kn0 t K fuel first stops ss <-. unfold sym_execTXBI2, sym_execTX.
replace (s_know ss) with (s_know (clr ss)) by (destruct ss; reflexivity).
apply sym_execTXBI2_go_eq.
Qed.
End WithSegs.
End AX2L.
