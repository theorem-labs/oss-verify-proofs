(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec StoreOk SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__DrvKitA () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.DrvKitA.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.DrvKitA.FPX_1.LogFrame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.DrvKitA.FPX_1.Transport."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymDrive."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2.SX2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec2Sound.SX2S."; "Stdlib.Arith.PeanoNat.Nat."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0CP"; "1Some"; "1app"; "1bool"; "1length"; "1list"; "1nat"; "1option"; "1pair"; "1prod"; "1true"; "2and"; "2eq"; "2ex"; "2not"; "2or"]; ["3Z"; "0E"; "0E'"; "0K"; "0K'"; "4Segment"; "5bvmap"; "0M"; "0M'"; "0R"; "7log_in_b"; "8kkeep_b"; "8kn_keep"; "8kn_keep_g"; "8len_hi"; "8rng_keep_b"]; ["8rng_wr_b"; "6blob_agree"; "6expr_blobs_lt"; "6kentry_eqb"; "6kn_blobs_lt"; "6ksub_b"; "6ksubl_b"; "6sr_blobs_lt"; "9mem_grows"; ":blobs_ev"; ";Env"; ";edenot"; ";env"; ";expr"; ";kentry"; ";sentry"]; ["<elenZ"; "<kentry_ok"; "<know_ok"; "<mem_denot"; "<regs_ok"; "0SC"; "=eqb"; ">In"; ">existsb"; "?add"; "?le"; "?lt"; "?pow"; "0a"; "0b"; "0base"]; ["0bb"; "0bl"; "0e"; "0extra"; "0f"; "0h"; "0hi"; "0i"; "0k"; "0kn"; "0kn'"; "0l"; "0lo"; "0log"; "0n"; "0segs"]; ["0sr"; "@Z_to_bv"; "@bv"; "@bv_unsigned"; "0vals"; "0x"]]).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}.
Section Transport.
Variable segs : list Segment.
Variables (spi : nat) (so sc : Z) (bls : list (nat * Z)) (vbnd : list (nat * Z)) (hiv : list nat) (img : list (Z * Z)).
Variable wimg : list (Z * Z).
Fixpoint find_nz (i : nat) (l : list (nat * Z)) : option Z :=
match l with
| [] => None
| (j, z) :: l' => if Nat.eqb i j then Some z else find_nz i l'
end.
Definition rng_keep_b (b : expr) (k n : Z) : bool :=
(0 <=? n) &&
match b with
| EVar i =>
if Nat.eqb i spi
then (- 2 ^ 23 <=? k) && (k + n <=? 0) && ((k + n <=? so - sc) || (so <=? k))
else match find_nz i bls with
| Some nb => (0 <=? k) && (k + n <=? nb)
| None => existsb (Nat.eqb i) hiv && (0 <=? k) && (k + n <=? 2 ^ 20)
end
| ELit z => (z =? 0) && existsb (fun iv => (fst iv <=? k) && (k + n <=? snd iv)) img
| _ => false
end.
Definition rng_wr_b (b : expr) (k n : Z) : bool :=
match b with
| EVar i => if Nat.eqb i spi then (0 <=? n) && (- 2 ^ 23 <=? k) && (k + n <=? 0) else rng_keep_b b k n
| _ => rng_keep_b b k n
end.
Definition len_hi (n : expr) : option Z :=
match n with
| ELit z => if (0 <=? z) && (z <? 2 ^ 64) then Some z else None
| EVar v => find_nz v vbnd
| _ => None
end.
Definition kkeep_b (K : kentry) : bool :=
match K with
| KWord (SA b k) w _ => rng_keep_b b k (Z.of_nat w)
| KZero (SA b k) n => match len_hi n with Some h => rng_keep_b b k h | None => false end
| KBlob (SA b k) n _ => match len_hi n with Some h => rng_keep_b b k h | None => false end
| KImg l h => existsb (fun iv => (fst iv <=? l) && (h <=? snd iv)) img || (h <=? l)
| KAlign _ _ => true
| KRange _ _ _ => true
| KDisj _ _ _ _ => true
| KWr (SA b k) n => rng_wr_b b k n
|| match b with
| ELit z => (z =? 0) && (0 <=? n) && existsb (fun iv => (fst iv <=? k) && (k + n <=? snd iv)) wimg
| _ => false
end
end.
Definition kn_keep (kn : list kentry) : list kentry := List.filter kkeep_b kn.
Variables (E : env) (CP SC : Z -> Prop).
Record regions_ok : Prop := REG {
rg_sp0 : 0x7fff80000000 <= bv_unsigned (ev E spi) <= 2 ^ 47;
rg_so : - 2 ^ 23 <= so - sc /\ 0 <= sc;
rg_stack : forall z, - 2 ^ 23 <= z < 0 -> ~ (so - sc <= z < so) -> CP (bv_unsigned (ev E spi) + z);
rg_scratch : forall z, so - sc <= z < so -> CP (bv_unsigned (ev E spi) + z) \/ SC (bv_unsigned (ev E spi) + z);
rg_blocks : forall i nb, find_nz i bls = Some nb ->
bv_unsigned (ev E i) + nb <= 2 ^ 64 /\ forall z, 0 <= z < nb -> CP (bv_unsigned (ev E i) + z);
rg_vbnd : forall v b, find_nz v vbnd = Some b -> bv_unsigned (ev E v) <= b;
rg_hiv : forall i, In i hiv -> bv_unsigned (ev E spi) <= bv_unsigned (ev E i) /\ bv_unsigned (ev E i) + 2 ^ 20 <= 2 ^ 64
/\ forall z, 0 <= z < 2 ^ 20 -> CP (bv_unsigned (ev E i) + z);
rg_img : forall lo hi, In (lo, hi) img -> 0 <= lo /\ hi <= 2 ^ 64 /\ forall a, lo <= a < hi -> CP a;
rg_wimg : forall lo hi, In (lo, hi) wimg -> 0 <= lo /\ hi <= 2 ^ 64 /\
forall (Mx : word -> option byte) d (m : nat), lo <= d -> d + Z.of_nat m <= hi -> store_ok segs Mx (Z_to_bv 64 d) m = true
}.
Hypothesis RG : regions_ok.
Variables (M M' : word -> option byte).
Hypothesis PRES : forall a, 0 <= a < 2 ^ 64 -> CP a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Hypothesis SDEF : forall a, SC a -> M' (Z_to_bv 64 a) <> None.
Lemma existsb_nat_in : ltac2:(TCodec.tc2 tcn__DrvKitA "C'6'5%112'<'3&QH&QFr2%211r1%53:21(:%93821&QGr3%23?18p041pTH?1pT@B1").
Proof.
intros i l H. apply existsb_exists in H as (j & Hj & Ej). apply Nat.eqb_eq in Ej. subst j. exact Hj.
Qed.
Lemma existsb_iv : ltac2:(TCodec.tc2 tcn__DrvKitA "Q0'9'@%2211'3p021'5%114'<&QHr2r1%33921(:%63:21'=';&QG(8%14AA98r4%43B21r5%114%@3D1;%9241qT>H1%<2I1qTJJ1%>2K1p0@1pTHH1pT:K1").
Proof.
intros f l H. apply existsb_exists in H as ([lo hi] & Hin & Hf). exists lo, hi. auto.
Qed.
Lemma rng_keep_sound : ltac2:(TCodec.tc2 tcn__DrvKitA "QD'Q='@'<'3&Or3r2r1%43321(:%83721';&QJz%2218&QI&RCyR0&Q;vAr4%3221%6251%821B%<2;1%:22C&QL+2+R0%3221%B251%C2BH&QK%12JL%G231v0r6%C2B1%F2E1r5%I221%J21Q3%711p091pT@Q;1%Q22?1%Q32F1%Q42Q11p0Q61pTNQ@1pTBQA1pSNQC1").
Proof.
intros b k n H. unfold rng_keep_b in H. apply andb_prop in H as [Hn H]. apply Z.leb_le in Hn.
destruct RG as [S0 SO ST _ BL _ HV IM].
destruct b as [z|i| | | | | |]; try discriminate.
- apply andb_prop in H as [Hz H]. apply Z.eqb_eq in Hz. subst z.
apply existsb_iv in H as (lo & hi & Hin & Hf). apply andb_prop in Hf as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. cbn [fst snd] in H1, H2.
destruct (IM lo hi Hin) as (L0 & Hhi & Icp).
cbn [edenot]. change (bv_unsigned (Z_to_bv 64 0)) with 0.
split; [lia|]. split; [lia|]. split; [lia|].
intros j Hj. apply Icp. lia.
- cbn [edenot]. destruct (Nat.eqb i spi) eqn:Ei.
+ apply Nat.eqb_eq in Ei. subst i.
apply andb_prop in H as [H Hor]. apply andb_prop in H as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2.
split; [lia|]. split; [lia|]. split; [lia|].
intros j Hj. replace (bv_unsigned (ev E spi) + k + j) with (bv_unsigned (ev E spi) + (k + j)) by lia.
apply ST; [lia|]. apply orb_prop in Hor. intros [A B].
destruct Hor as [Hor|Hor]; apply Z.leb_le in Hor; lia.
+ destruct (find_nz i bls) as [nb|] eqn:Fb.
* apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
destruct (BL i nb Fb) as [Bnw Bcp]. pose proof (u64_range (ev E i)).
split; [lia|]. split; [lia|]. split; [lia|].
intros j Hj. replace (bv_unsigned (ev E i) + k + j) with (bv_unsigned (ev E i) + (k + j)) by lia.
apply Bcp. lia.
* apply andb_prop in H as [H H2]. apply andb_prop in H as [H H1].
apply existsb_nat_in in H. apply Z.leb_le in H1. apply Z.leb_le in H2.
destruct (HV i H) as (V1 & V2 & V3). pose proof (u64_range (ev E i)).
split; [lia|]. split; [lia|]. split; [lia|].
intros j Hj. replace (bv_unsigned (ev E i) + k + j) with (bv_unsigned (ev E i) + (k + j)) by lia.
apply V3. lia.
Qed.
Lemma rng_wr_sound : ltac2:(TCodec.tc2 tcn__DrvKitA "QH'Q='@'<'3&Q0r3r2r1%43321(:%83721';&QJz%2218&QI&RCyR0&Q;vAr4%3221%6251%821B%<2;1%:22C&QL+2+R0%3221%B251%C2BH&QK%12JL%G231'?v0r6%D2C1%G2F1r5%J221%K21Q4%711vQE%113%;231p0=1pT@Q?1%Q62C1%Q72J1%Q82Q51p0Q:1pTNQD1pTBQE1pSNQG1").
Proof.
intros b k n H. unfold rng_wr_b in H.
assert (KEEP : rng_keep_b b k n = true ->
0 <= n /\ 0 <= bv_unsigned (edenot E b) + k /\ bv_unsigned (edenot E b) + k + n <= 2 ^ 64
/\ forall i, 0 <= i < n -> CP (bv_unsigned (edenot E b) + k + i) \/ SC (bv_unsigned (edenot E b) + k + i)).
{ intros HK. destruct (rng_keep_sound b k n HK) as (A & B & C & D). repeat split; try assumption.
intros i Hi. left. apply D. exact Hi. }
destruct b as [z|i| | | | | |]; try (apply KEEP; exact H).
destruct (Nat.eqb i spi) eqn:Ei; [|apply KEEP; exact H].
apply Nat.eqb_eq in Ei. subst i. destruct RG as [S0 SO ST SCR _ _ _ _].
apply andb_prop in H as [H H2]. apply andb_prop in H as [Hn H1].
apply Z.leb_le in Hn. apply Z.leb_le in H1. apply Z.leb_le in H2. cbn [edenot].
split; [lia|]. split; [lia|]. split; [lia|].
intros j Hj. replace (bv_unsigned (ev E spi) + k + j) with (bv_unsigned (ev E spi) + (k + j)) by lia.
destruct (Z.lt_ge_cases (k + j) (so - sc)) as [L|G]; [left; apply ST; lia|].
destruct (Z.lt_ge_cases (k + j) so) as [L2|G2]; [apply SCR; lia | left; apply ST; lia].
Qed.
Lemma len_hi_sound : ltac2:(TCodec.tc2 tcn__DrvKitA "I'Q='@'<'7%113&Nr2%211(1r1%2291%93741';&QJz&Q@vAr3%3221%6251%722>%9221p0;1pT<F1pTNH1").
Proof.
intros n h H. unfold len_hi in H. unfold elenZ.
destruct n as [z|v| | | | | |]; try discriminate.
- destruct ((0 <=? z) && (z <? 2 ^ 64))%bool eqn:B; [|discriminate]. injection H as <-.
apply andb_prop in B as [B1 B2]. apply Z.leb_le in B1. apply Z.ltb_lt in B2.
cbn [edenot]. rewrite u_small by lia. lia.
- cbn [edenot]. pose proof (rg_vbnd RG v h H). pose proof (u64_range (ev E v)). lia.
Qed.
Lemma kentry_keep_sound : ltac2:(TCodec.tc2 tcn__DrvKitA "D'Q>&QAvR?vAvGr1%544321'<'3&Kr2%211(:%63521vHr3%?4>=21p041p0<1pQ8C1").
Proof.
intros K HK Hb.
destruct K as [[b k] w v|[b k] n|[b k] n bk|l h|e m|e l h|[b k] n|a1 n1 a2 n2]; cbn [kkeep_b] in Hb;
cbn [kentry_ok] in HK |- *; try exact HK.
-
destruct HK as (Hw8 & Hfl & Hr). split; [exact Hw8|]. split; [exact Hfl|].
destruct (rng_keep_sound b k (Z.of_nat w) Hb) as (A & B & C & D).
rewrite <- Hr. symmetry. apply rdn_agree. intros j Hj.
pose proof (flat_u E _ _ Hfl) as Hu. unfold estart in Hu. cbn [a_base a_off] in Hu. rewrite Hu.
symmetry. replace (bv_unsigned (edenot E b) + k + Z.of_nat j) with (bv_unsigned (edenot E b) + k + Z.of_nat j) by lia.
apply PRES; [lia|]. apply D. lia.
-
destruct (len_hi n) as [h|] eqn:Hh; [|discriminate].
pose proof (len_hi_sound n h Hh) as Hle.
destruct HK as (Hfl & Hz). split; [exact Hfl|]. intros i Hi.
destruct (rng_keep_sound b k h Hb) as (A & B & C & D).
unfold estart. cbn [a_base a_off]. rewrite PRES; [apply Hz; exact Hi | lia |]. apply D. lia.
-
destruct (len_hi n) as [h|] eqn:Hh; [|discriminate].
pose proof (len_hi_sound n h Hh) as Hle.
destruct HK as (Hfl & Hlen & Hz). split; [exact Hfl|]. split; [exact Hlen|]. intros i Hi.
destruct (rng_keep_sound b k h Hb) as (A & B & C & D).
unfold estart. cbn [a_base a_off]. rewrite PRES; [apply Hz; exact Hi | lia |]. apply D. lia.
-
destruct HK as (H0 & H64 & Hnone). split; [exact H0|]. split; [exact H64|].
apply orb_prop in Hb. destruct Hb as [Hb|Hb].
+ apply existsb_iv in Hb as (lo & hi & Hin & Hf). apply andb_prop in Hf as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. cbn [fst snd] in H1, H2.
destruct (rg_img RG lo hi Hin) as (L0 & Lhi & Icp).
intros i Hi. rewrite PRES; [apply Hnone; exact Hi | lia |]. apply Icp. lia.
+ apply Z.leb_le in Hb. intros i Hi. lia.
-
destruct HK as [Hfl Hst]. split; [exact Hfl|].
apply orb_prop in Hb. destruct Hb as [Hb|Hw].
2:{ destruct b as [z| | | | | | |]; try discriminate.
apply andb_prop in Hw as [Hw Hex]. apply andb_prop in Hw as [Hz Hn0]. apply Z.eqb_eq in Hz. subst z.
apply Z.leb_le in Hn0.
apply existsb_iv in Hex as (lo & hi & Hin & Hf). apply andb_prop in Hf as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. cbn [fst snd] in H1, H2.
destruct (rg_wimg RG lo hi Hin) as (L0 & Lhi & W).
intros d m Hd Hm. unfold estart. cbn [a_base a_off edenot]. change (bv_unsigned (Z_to_bv 64 0)) with 0.
apply W; lia. }
destruct (rng_wr_sound b k n Hb) as (A & B & C & D).
intros d m Hd Hm. destruct m as [|m']; [reflexivity|]. set (m := S m') in *.
assert (HU : bv_unsigned (Z_to_bv 64 (estart E (SA b k) + d)) = bv_unsigned (edenot E b) + k + d).
{ unfold estart. cbn [a_base a_off]. rewrite u_small by lia. reflexivity. }
apply store_ok_of_all; [rewrite HU; lia|].
intros x Hx. rewrite HU in Hx.
pose proof (store_ok_all segs M m (Z_to_bv 64 (estart E (SA b k) + d)) ltac:(rewrite HU; lia)
(Hst d m Hd Hm) x ltac:(rewrite HU; lia)) as W.
destruct (D (bv_unsigned x - (bv_unsigned (edenot E b) + k))) as [HC|HS]; [lia| |].
+ replace (bv_unsigned (edenot E b) + k + (bv_unsigned x - (bv_unsigned (edenot E b) + k))) with (bv_unsigned x) in HC by lia.
rewrite (wview_ext segs M M' x); [exact W|].
rewrite <- (Z_to_bv_bv_unsigned 64 x). apply PRES; [pose proof (u64_range x); lia | exact HC].
+ replace (bv_unsigned (edenot E b) + k + (bv_unsigned x - (bv_unsigned (edenot E b) + k))) with (bv_unsigned x) in HS by lia.
apply SDEF in HS. rewrite Z_to_bv_bv_unsigned in HS.
unfold wview. destruct (M' x); [discriminate | exfalso; apply HS; reflexivity].
Qed.
Theorem know_keep_sound : ltac2:(TCodec.tc2 tcn__DrvKitA "@'5'Q>%211&QBvR?vAvGr1%544321vH&Lr2%211%:49841p061pTD=1").
Proof.
intros kn HK. unfold know_ok in *. induction kn as [|K rest IH]; [constructor|].
apply Forall_cons_iff in HK as [HK1 HK2].
change (kn_keep (K :: rest)) with (if kkeep_b K then K :: kn_keep rest else kn_keep rest).
destruct (kkeep_b K) eqn:Hb.
- constructor; [|apply IH; exact HK2]. eapply kentry_keep_sound; eauto.
- apply IH. exact HK2.
Qed.
Definition is_kwr (K : kentry) : bool := match K with KWr _ _ => true | _ => false end.
Definition kn_keep_g (kn : list kentry) : list kentry := List.filter (fun K => is_kwr K || kkeep_b K) kn.
Theorem know_keep_g_sound : ltac2:(TCodec.tc2 tcn__DrvKitA "C'5'Q>%211&Q8vGvH%3221&QBvR?vAr2%443271&Mr3%211%8476:1p051p0;1pTD@1").
Proof.
intros kn Hg HK. unfold know_ok in *. induction kn as [|K rest IH]; [constructor|].
apply Forall_cons_iff in HK as [HK1 HK2].
change (kn_keep_g (K :: rest)) with (if is_kwr K || kkeep_b K then K :: kn_keep_g rest else kn_keep_g rest).
destruct (is_kwr K || kkeep_b K) eqn:Hb.
- constructor; [|apply IH; exact HK2].
destruct (is_kwr K) eqn:Hw.
+ destruct K as [| | | | | |[b k] n|]; try discriminate.
cbn [kentry_ok] in HK1 |- *. destruct HK1 as [Hfl Hst]. split; [exact Hfl|].
intros d m Hd Hm. eapply store_ok_mono; [exact Hg | apply Hst; assumption].
+ cbn [orb] in Hb. apply (kentry_keep_sound K HK1 Hb).
- apply IH. exact HK2.
Qed.
End Transport.
Section LogFrame.
Variable segs : list Segment.
Variables (spi : nat) (so sc : Z) (bls vbnd : list (nat * Z)) (hiv : list nat) (img : list (Z * Z)).
Variables (E : env) (CP SC : Z -> Prop).
Variable wimg : list (Z * Z).
Hypothesis RG : regions_ok segs spi so sc bls vbnd hiv img wimg E CP SC.
Definition sentry_in_b (se : sentry) : bool :=
match se with SE (SA b k) w _ => (Nat.leb w 8) && rng_keep_b spi so sc bls hiv img b k (Z.of_nat w) end.
Definition log_in_b (log : list sentry) : bool := forallb sentry_in_b log.
Lemma mem_denot_frame : ltac2:(TCodec.tc2 tcn__DrvKitA "Q5'RByR0%211'7y8%511%311p051'5'Q?%211'<'3&Jr2%211(:%63521&>v0&RC%12D7%311%511&QCvAr5r4r3%544321%412%D3I21p091p0@1pU<Q01pTLI1pQ@M1").
Proof.
intros M log x Hb Hx. induction log as [|[[b k] w v] rest IH]; [reflexivity|].
cbn [log_in_b forallb] in Hb. apply andb_prop in Hb as [He Hrest]. cbn [sentry_in_b] in He.
apply andb_prop in He as [Hw He]. apply Nat.leb_le in Hw.
destruct (rng_keep_sound segs spi so sc bls vbnd hiv img wimg E CP SC RG b k (Z.of_nat w) He) as (A & B & C & D).
cbn [mem_denot]. destruct w as [|w'].
{ change (word_to_le_bytes 0 (edenot E v)) with (@nil byte). cbn [wbytes]. apply IH. exact Hrest. }
set (w := S w') in *.
rewrite wbytes_out.
- apply IH. exact Hrest.
- rewrite length_N_to_le_bytes. unfold adenot, v_addi. cbn [a_base a_off]. rewrite u_small by lia. lia.
- rewrite length_N_to_le_bytes. unfold adenot, v_addi. cbn [a_base a_off]. rewrite u_small by lia.
pose proof (u64_range x).
destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned (edenot E b) + k)) as [L|G]; [left; lia|].
destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned (edenot E b) + k + Z.of_nat w)) as [L2|G2]; [|right; lia].
exfalso. apply Hx. replace (bv_unsigned x) with (bv_unsigned (edenot E b) + k + (bv_unsigned x - (bv_unsigned (edenot E b) + k))) by lia.
apply D. lia.
Qed.
Lemma mem_denot_frame_Z : ltac2:(TCodec.tc2 tcn__DrvKitA "QC'RByR0%211'7y8%511%311p051'5'Q?%211'@'<'3&Jr2%211(:%63521';&QJz%2217&QK&QL+2+R0%3221%52=1%:271&>v0r3%211%411&QCvAr6r5&RAr4%22Q81%746541%612%Q03Q621p0;1p0A1p0M1pSLQ51pTLQ71pQ@Q;1").
Proof.
intros M log a Hb Ha Hx. apply mem_denot_frame; [exact Hb|]. rewrite u_small by lia. exact Hx.
Qed.
End LogFrame.
Definition kentry_eqb (K K' : kentry) : bool :=
match K, K' with
| KWord a w v, KWord a' w' v' => saddr_eqb a a' && Nat.eqb w w' && expr_eqb v v'
| KZero a n, KZero a' n' => saddr_eqb a a' && expr_eqb n n'
| KBlob a n k, KBlob a' n' k' => saddr_eqb a a' && expr_eqb n n' && Nat.eqb k k'
| KImg l h, KImg l' h' => (l =? l') && (h =? h')
| KAlign e m, KAlign e' m' => expr_eqb e e' && (m =? m')
| KRange e l h, KRange e' l' h' => expr_eqb e e' && (l =? l') && (h =? h')
| KWr a n, KWr a' n' => saddr_eqb a a' && (n =? n')
| KDisj a n b m, KDisj a' n' b' m' => saddr_eqb a a' && (n =? n') && saddr_eqb b b' && (m =? m')
| _, _ => false
end.
Lemma kentry_eqb_eq : ltac2:(TCodec.tc2 tcn__DrvKitA ">'Q>'<'3&Q3r2r1%3221(:%73621r3%93:16p031pQ:<1pQ8=1").
Proof.
intros K K' H;
destruct K as [[b1 k1] w v|[b1 k1] n|[b1 k1] n kk|l h|e m|e l h|[b1 k1] n|[b1 k1] n1 [b2 k2] n2];
destruct K' as [[b1' k1'] w' v'|[b1' k1'] n'|[b1' k1'] n' kk'|l' h'|e' m'|e' l' h'|[b1' k1'] n'|[b1' k1'] n1' [b2' k2'] n2'];
cbn [kentry_eqb saddr_eqb a_base a_off] in H; try discriminate;
repeat (apply andb_prop in H; destruct H as [H ?]);
repeat match goal with
| X : saddr_eqb _ _ = true |- _ => apply saddr_eqb_eq in X
| X : expr_eqb _ _ = true |- _ => apply expr_eqb_eq in X; cbn [a_base a_off] in X
| X : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in X
| X : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in X; cbn [a_base a_off] in X
end; subst; congruence.
Qed.
Definition ksub_b (kn : list kentry) (K : kentry) : bool :=
existsb (kentry_eqb K) kn
|| match K with
| KImg lo hi => existsb (fun K' => match K' with KImg l h => (l <=? lo) && (hi <=? h) | _ => false end) kn
| _ => false
end.
Lemma ksub_sound : ltac2:(TCodec.tc2 tcn__DrvKitA "Q5'5'E%211'Q<'RByR0%211'7y8%511%311p051'Q>%=11&QBr5r4r3r2%544321'<'3&Q5%1265(:%53421&QAr7r6%3421><p051p0<1pQ8D1pTDD1pQ@G1pQ4Q01pU0Q21").
Proof.
intros segs E M kn K HK Hb. unfold ksub_b in Hb. apply orb_prop in Hb. destruct Hb as [Hb|Hb].
- apply existsb_exists in Hb as (K' & Hin & Heq). apply kentry_eqb_eq in Heq. subst K'.
exact (proj1 (Forall_forall _ _) HK K Hin).
- destruct K as [| | |lo hi| | | |]; try discriminate.
apply existsb_exists in Hb as (K' & Hin & Hm). destruct K' as [| | |l h| | | |]; try discriminate.
apply andb_prop in Hm as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
pose proof (proj1 (Forall_forall _ _) HK _ Hin) as HK'. cbn [kentry_ok] in HK' |- *.
destruct HK' as (A & B & C). split; [lia|]. split; [lia|]. intros i Hi. apply C. lia.
Qed.
Definition ksubl_b (kn kn' : list kentry) : bool := forallb (ksub_b kn) kn'.
Lemma ksubl_sound : ltac2:(TCodec.tc2 tcn__DrvKitA "Q4'5'E%211'Q<'RByR0%211'7y8%511%311p051'Q>%=11&QBr5r4r3r2%544321'<'3&Q6%1265(:%53421r7r6%>421=;p041p0;1pTFB1pTDC1pQ@F1pQ4O1pU0Q11").
Proof.
intros segs E M kn kn' HK Hb. unfold know_ok. apply Forall_forall. intros K Hin.
unfold ksubl_b in Hb. rewrite forallb_forall in Hb. eapply ksub_sound; [exact HK | apply Hb; exact Hin].
Qed.
Fixpoint expr_blobs_lt (bb : nat) (e : expr) : bool :=
match e with
| ELit _ | EVar _ => true
| EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => expr_blobs_lt bb x && expr_blobs_lt bb y
| EExt _ _ _ x => expr_blobs_lt bb x
| EBlob _ k _ _ => Nat.ltb k bb
end.
Definition kentry_blobs_lt (bb : nat) (K : kentry) : bool :=
match K with
| KWord a _ v => expr_blobs_lt bb (a_base a) && expr_blobs_lt bb v
| KZero a n => expr_blobs_lt bb (a_base a) && expr_blobs_lt bb n
| KBlob a n k => expr_blobs_lt bb (a_base a) && expr_blobs_lt bb n && Nat.ltb k bb
| KImg _ _ => true
| KAlign e _ => expr_blobs_lt bb e
| KRange e _ _ => expr_blobs_lt bb e
| KWr a _ => expr_blobs_lt bb (a_base a)
| KDisj a1 _ a2 _ => expr_blobs_lt bb (a_base a1) && expr_blobs_lt bb (a_base a2)
end.
Definition kn_blobs_lt (bb : nat) (kn : list kentry) : bool := forallb (kentry_blobs_lt bb) kn.
Definition sr_blobs_lt (bb : nat) (sr : list expr) : bool := forallb (expr_blobs_lt bb) sr.
Definition blob_agree (bb : nat) (E E' : env) : Prop :=
(forall n, ev E n = ev E' n) /\ (forall k, (k < bb)%nat -> eb E k = eb E' k).
Lemma edenot_bagree : ltac2:(TCodec.tc2 tcn__DrvKitA "L'6'Q<'Q=&Q1r4r3r2%43321'<'3&Q2r5%2216(:%63521'RByR0%211&Q;%128>%22@?%=3421p081p0@1pT6F1pQ6H1pQ4I1pT2K1").
Proof.
intros bb E E' e [Hv Hb]. induction e; cbn [expr_blobs_lt edenot]; intros H;
repeat match goal with
| H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
end;
try reflexivity;
try (rewrite IHe1, IHe2 by assumption; reflexivity);
try (rewrite IHe by assumption; reflexivity).
- apply Hv.
- apply Nat.ltb_lt in H. rewrite (Hb _ H). reflexivity.
Qed.
Lemma regs_ok_bagree : ltac2:(TCodec.tc2 tcn__DrvKitA "Q2'6'Q<'5'Q=%211&Fy5'RByR0%211%5241&Q1r5r4r3%43321'<'3&Q7r6%2216(:%63521&QD%135;:%236=<p021p051p0=1pQDC1pU2J1pQ6N1pQ4O1pT2Q11").
Proof.
intros bb E E' sr R Ha Hsr HR r. rewrite (HR r). apply (edenot_bagree bb E E'); [exact Ha|].
unfold sr_get. destruct (bv_eqb r 0); [reflexivity|].
unfold sr_blobs_lt in Hsr. rewrite forallb_forall in Hsr.
destruct (nth_error sr (ridx r)) as [e|] eqn:He.
- rewrite (nth_error_nth _ _ _ He). apply Hsr. eapply nth_error_In; exact He.
- rewrite nth_overflow; [reflexivity|]. apply (proj1 (nth_error_None _ _)). exact He.
Qed.
Lemma know_ok_bagree : ltac2:(TCodec.tc2 tcn__DrvKitA "Q:'5'E%211'6'Q<'RByR0%211'7y8%511%311p051'Q>%>11&Q1r5r4r3%43321'<'3&Q4r6r2%3221(:%73621&QBr8%2417=<r9%4419@?p031p071p0@1pTDF1pT0I1pQ6Q21pQ4Q31pT2Q51pU0Q71").
Proof.
intros segs bb E E' base kn Ha Hkn HK. unfold know_ok in *. unfold kn_blobs_lt in Hkn. rewrite forallb_forall in Hkn.
apply Forall_forall. intros K HinK. pose proof (proj1 (Forall_forall _ _) HK K HinK) as Hk. specialize (Hkn K HinK).
pose proof Ha as [Hv Hb].
assert (AD : forall a, expr_blobs_lt bb (a_base a) = true -> adenot E a = adenot E' a).
{ intros a H. unfold adenot. rewrite (edenot_bagree bb E E' _ Ha H). reflexivity. }
assert (ES : forall a, expr_blobs_lt bb (a_base a) = true -> estart E a = estart E' a).
{ intros a H. unfold estart. rewrite (edenot_bagree bb E E' _ Ha H). reflexivity. }
assert (FL : forall a n, expr_blobs_lt bb (a_base a) = true -> flat E a n -> flat E' a n).
{ intros a n H F. unfold flat in *. rewrite <- (ES a H). exact F. }
destruct K as [a w v|a n|a n k|lo hi|ae am|re rlo rhi|wa wn|da1 dn1 da2 dn2]; cbn [kentry_blobs_lt kentry_ok] in *;
repeat match goal with | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H end.
- destruct Hk as (A & B & C). split; [exact A|]. split; [apply FL; assumption|].
rewrite <- (AD a), <- (edenot_bagree bb E E' v Ha) by assumption. exact C.
- destruct Hk as [A B]. unfold elenZ in *. rewrite <- (edenot_bagree bb E E' n Ha) by assumption.
split; [apply FL; assumption|]. intros i Hi. rewrite <- (ES a) by assumption. apply B. exact Hi.
- destruct Hk as (A & B & C). unfold elenZ in *. rewrite <- (edenot_bagree bb E E' n Ha) by assumption.
apply Nat.ltb_lt in H0. rewrite <- (Hb _ H0).
split; [apply FL; assumption|]. split; [exact B|]. intros i Hi. rewrite <- (ES a) by assumption. apply C. exact Hi.
- exact Hk.
- rewrite <- (edenot_bagree bb E E' ae Ha) by assumption. exact Hk.
- rewrite <- (edenot_bagree bb E E' re Ha) by assumption. exact Hk.
- destruct Hk as [A B]. split; [apply FL; assumption|]. intros d m Hd Hm. rewrite <- (ES wa) by assumption. apply B; assumption.
- rewrite <- (ES da1), <- (ES da2) by assumption. exact Hk.
Qed.
Lemma blob_agree_app : ltac2:(TCodec.tc2 tcn__DrvKitA "L'6'RByR0%211p041'5y8%611%311%411&Q1&4r2%2251(Q:r3&Q9%115%4231&2r1%23=91%611%9281%>3;61pT8@1pT4A1pU:G1").
Proof.
intros vals bl extra. split; [reflexivity|]. intros k Hk. cbn [eb]. unfold blobs_ev. rewrite app_nth1 by exact Hk. reflexivity.
Qed.
End FPX_1.
