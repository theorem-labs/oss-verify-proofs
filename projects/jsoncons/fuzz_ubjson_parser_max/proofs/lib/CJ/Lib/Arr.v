(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Lib_Arr () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Arr."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Arr.WithSegs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1Some"; "1app"; "1bool"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1true"; "2and"; "2eq"; "2ex"; "2or"; "3mul"]; ["4Z"; "5ov_read_bytes"; "5store_ok"; "5write_to_mem"; "7u32arr"; "7u64arr"; "7u8arr"; "7u8ro"; "6u32s"; "6u64s"; "6upd"; "8CB"; "8cell"; "9disjoint_from"; "9ivl"; "9munch"]; ["9wmono"; ":le4"; ":le8"; ":upd_bytes"; ":wa"; ";rw_cells"; "<nth_error"; "=add"; "=le"; "=lt"; "=mul"; "=of_nat"; "=pow"; "=to_nat"; "0W"; "0a"]; ["0b"; "0bs"; "0c"; "0i"; "0m"; "0m'"; "0n"; "0post"; "0pre"; "0segs"; ">bv"; "0v"; "0w"; "0ws"; "0xs"]]).
Fixpoint u32s (ws : list word) : list byte :=
match ws with [] => [] | w :: ws' => le4 w ++ u32s ws' end.
Fixpoint u64s (ws : list word) : list byte :=
match ws with [] => [] | w :: ws' => le8 w ++ u64s ws' end.
Lemma u32s_length : ltac2:(TCodec.tc2 tcn__CJ_Lib_Arr "D'6'QJyR0%211%411'<'7&5y8%811&Hr1%211%6241&?u4%92=5%3221%=3<51pSL?1").
Proof. induction ws; cbn -[le4]; [reflexivity|]. rewrite app_length, length_le4, IHws. lia. Qed.
Lemma u64s_length : ltac2:(TCodec.tc2 tcn__CJ_Lib_Arr "D'6'QJyR0%211%411'<'7&5y8%811&Ir1%211%6241&?u8%92=5%3221%=3<51pSL?1").
Proof. induction ws; cbn -[le8]; [reflexivity|]. rewrite app_length, length_le8, IHws. lia. Qed.
Lemma u32s_app : ltac2:(TCodec.tc2 tcn__CJ_Lib_Arr "E'6'QJyR0%211%411'<y8%611%811&H&2r2r1%33:21%511%614%714%73:21%=3:41pS2?1pS0@1").
Proof. induction a; intros; cbn -[le4]; [reflexivity|]. rewrite IHa, app_assoc. reflexivity. Qed.
Lemma u64s_app : ltac2:(TCodec.tc2 tcn__CJ_Lib_Arr "E'6'QJyR0%211%411'<y8%611%811&I&2r2r1%33:21%511%614%714%73:21%=3:41pS2?1pS0@1").
Proof. induction a; intros; cbn -[le8]; [reflexivity|]. rewrite IHa, app_assoc. reflexivity. Qed.
Fixpoint upd {X} (l : list X) (i : nat) (x : X) : list X :=
match l, i with
| [], _ => []
| _ :: l', O => x :: l'
| y :: l', S i' => y :: upd l' i' x
end.
Lemma upd_length : forall {X} (l : list X) i x, length (upd l i x) = length l.
Proof. induction l; intros [|i] x; cbn; auto. Qed.
Lemma upd_app_split : forall {X} (l : list X) i x, (i < length l)%nat ->
exists pre y post, l = pre ++ y :: post /\ length pre = i /\ upd l i x = pre ++ x :: post.
Proof.
induction l as [|z l IH]; intros i x Hi; cbn in Hi; [lia|].
destruct i as [|i].
- exists [], z, l. repeat split; reflexivity.
- destruct (IH i x ltac:(lia)) as (pre & y & post & E & Hlen & Hupd).
exists (z :: pre), y, post. split; [rewrite E at 1; reflexivity|]. split; [cbn; lia|].
cbn. rewrite Hupd. reflexivity.
Qed.
Lemma nth_error_split : forall {X} (l : list X) i y, nth_error l i = Some y ->
exists pre post, l = pre ++ y :: post /\ length pre = i.
Proof.
induction l as [|z l IH]; intros [|i] y H; cbn in H; try discriminate.
- inversion H; subst. exists [], l. split; reflexivity.
- destruct (IH i y H) as (pre & post & -> & Hlen). exists (z :: pre), post. split; [reflexivity| cbn; lia].
Qed.
Lemma nth_error_lt : forall {X} (l : list X) i y, nth_error l i = Some y -> (i < length l)%nat.
Proof. intros X l i y H. apply nth_error_Some. rewrite H. discriminate. Qed.
Lemma upd_bytes_mid : ltac2:(TCodec.tc2 tcn__CJ_Lib_Arr "N'6'QJy8%211%411'<'7&5r1%2261r3%4281%73631&Q3&2r5r4%33>17%43?31%<2@4r2%83321%83C2<%93D81%C3D31p0=1pS4F1pS6G1pS2H1pS0I1").
Proof.
intros a b c bs H. unfold upd_bytes.
rewrite firstn_app, firstn_all2, Nat.sub_diag, firstn_O, app_nil_r by lia.
rewrite skipn_app, skipn_all2 by lia. cbn [app].
replace (length a + length bs - length a)%nat with (length b) by lia.
rewrite skipn_app, skipn_all2, Nat.sub_diag by lia. reflexivity.
Qed.
Section WithSegs.
Variable segs : list Segment.
Definition u8arr (m : word -> option byte) (A : Z) (bs : list byte) : Prop :=
bytes_at segs m A bs /\ wr_at segs m A (Z.of_nat (length bs)).
Definition u32arr (m : word -> option byte) (A : Z) (ws : list word) : Prop :=
bytes_at segs m A (u32s ws) /\ wr_at segs m A (4 * Z.of_nat (length ws)).
Definition u64arr (m : word -> option byte) (A : Z) (ws : list word) : Prop :=
bytes_at segs m A (u64s ws) /\ wr_at segs m A (8 * Z.of_nat (length ws)).
Definition u8ro (m : word -> option byte) (A : Z) (bs : list byte) : Prop := bytes_at segs m A bs.
Lemma u8arr_read : ltac2:(TCodec.tc2 tcn__CJ_Lib_Arr "QH'QJyR0%211'9y8%511%311p051'@'6%115&Fr6r5r4%43321'<&Q6&Q=%115%33?71(1r3%22B1%83B41&Q8z%221>&Q4&Q7r8%221C%411%A3OC1%O1H&AvQIr:u1%4432J1(4(8%11Q5%33Q6O1%G2Q21%M3;61p0=1p0D1p0H1p0Q21pS0Q@1pS2Q>1pS8Q<1pS4Q;1p2Q>1pS:Q@1").
Proof.
intros m A bs i b a [Hb _] Hn Hi ->.
pose proof (nth_error_lt _ _ _ Hn).
rewrite (bytes_at_read segs m A bs i 1 Hb) by lia.
destruct (nth_error_split _ _ _ Hn) as (pre & post & E & Hlen). rewrite E at 1.
rewrite skipn_app, skipn_all2, Hlen, Nat.sub_diag by lia. reflexivity.
Qed.
Lemma u8ro_read : ltac2:(TCodec.tc2 tcn__CJ_Lib_Arr "QH'QJyR0%211'9y8%511%311p051'@'6%115&Gr6r5r4%43321'<&Q6&Q=%115%33?71(1r3%22B1%83B41&Q8z%221>&Q4&Q7r8%221C%411%A3OC1%O1H&AvQIr:u1%4432J1(4(8%11Q5%33Q6O1%G2Q21%M3;61p0=1p0D1p0H1p0Q21pS0Q@1pS2Q>1pS8Q<1pS4Q;1p2Q>1pS:Q@1").
Proof.
intros m A bs i b a Hb Hn Hi ->.
pose proof (nth_error_lt _ _ _ Hn).
rewrite (bytes_at_read segs m A bs i 1 Hb) by lia.
destruct (nth_error_split _ _ _ Hn) as (pre & post & E & Hlen). rewrite E at 1.
rewrite skipn_app, skipn_all2, Hlen, Nat.sub_diag by lia. reflexivity.
Qed.
Lemma u8arr_store_ok : ltac2:(TCodec.tc2 tcn__CJ_Lib_Arr "QB'QJyR0%211'9y8%511%311p051'@'6%115&Fr5r4r3%43321';&Q8z%2215&Q9&Q;&5%12B:%311%52;1%:271'<&Q4&Q7r6%221B%411%63OC1'3&BvQIr8u1%4432J1(:%>3721p091p0A1p0M1pS0Q;1pS8Q61pS4Q51p2Q81pS:Q:1").
Proof. intros m A bs i a [_ Hw] Hi ->. eapply wr_at_store_ok; eauto; lia. Qed.
Lemma u8arr_write : ltac2:(TCodec.tc2 tcn__CJ_Lib_Arr "QC'QJyR0%211'9y8%511%311p051'@'6%115&Fr5r4r3%43321';&Q8z%2215&Q9&Q;&5%12B:%311%52;1%:271&Cr7&Q4&Q7r6%221C%411(4(8%11O%33Q0G1%;3:51&J&Q=%11L%34Q5N1L%Q035<1p0B1p0N1pS2Q91pS8Q71pS4Q61p2Q91pS:Q;1").
Proof.
intros m A bs i b [Hb Hw] Hi. split.
- eapply bytes_at_ext. { apply (bytes_at_write_inside segs m A bs i [b] Hb); [lia| cbn; lia]. }
destruct (upd_app_split bs (Z.to_nat i) b ltac:(lia)) as (pre & y & post & E & Hlen & Hupd).
rewrite Hupd. rewrite E at 1. unfold upd_bytes. rewrite firstn_app, firstn_all2, Hlen, Nat.sub_diag by lia. cbn.
rewrite app_nil_r. f_equal. change (y :: post) with ([y] ++ post). rewrite app_assoc, skipn_app.
rewrite skipn_all2 by (rewrite app_length, Hlen; cbn; lia). rewrite app_length, Hlen. cbn.
replace (Z.to_nat i + 1 - (Z.to_nat i + 1))%nat with 0%nat by lia. reflexivity.
- rewrite upd_length. apply wr_at_write. exact Hw.
Qed.
Lemma u32s_split : ltac2:(TCodec.tc2 tcn__CJ_Lib_Arr "QJ'6'QJyR0%211%411'7'<'9%115&Q6r3r2%33921(1r1%22<1%:3841'=';r6&2(4r4%23D19%43E=1%C3E61&5%12H@r5%G3H21y8%N11%Q011&H%11?%21H&Q1%11?%51H%C3821%D3951%Q33971%@2;7&?u4%221A%Q83Q941%M261%N2C1%O2H1qS@Q>1%Q22Q?1qSBQ@1%Q42QA1p0Q61pSJQD1pS8QC1pSLQE1").
Proof.
intros ws i w H. destruct (nth_error_split _ _ _ H) as (pre & post & -> & Hlen).
exists pre, post. rewrite u32s_app. cbn -[le4]. rewrite u32s_length. repeat split; lia.
Qed.
Lemma u32arr_read : ltac2:(TCodec.tc2 tcn__CJ_Lib_Arr "QK'QJyR0%211'9y8%511%311p051'@'6%118&Dr6r5r4%43321'<%>1?&Q6&Q=%116%33C81(1r3%22F1%93841&Q8z%221?&Q4&Q7r8&Q:+4%221F%5241%711%E3Q3G1%M1Q1%Q411&AvQIr:u4%4432O1&Q1%11Q2%I291%Q03941p0<1p0F1p0J1p0Q51pS0QC1pSJQD1pS8Q?1pSLQ>1p2QA1pS:QC1").
Proof.
intros m A ws i w a [Hb _] Hn Hi ->.
destruct (u32s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
replace (4 * i)%Z with (Z.of_nat (4 * Z.to_nat i))%Z by lia.
rewrite (bytes_at_ov_read segs m A (u32s ws) (4 * Z.to_nat i) 4 Hb).
2:{ rewrite Eu, !app_length, length_le4, Hlu. lia. }
rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
rewrite firstn_app, firstn_all2 by (rewrite length_le4; lia).
rewrite length_le4, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.
Lemma u32arr_store_ok : ltac2:(TCodec.tc2 tcn__CJ_Lib_Arr "QE'QJyR0%211'9y8%511%311p051'@'6%118&Dr5r4r3%43321';&Q8z%2215&Q9&Q;&5%12E:%311%52;1%:271'<&Q4&Q7r6&Q:+4%221D%5241%711%93Q2F1'3&BvQIr8u4%4432M1(:%A3721p091p0D1p0Q01pS0Q>1pS8Q91pSLQ81p2Q;1pS:Q=1").
Proof. intros m A ws i a [_ Hw] Hi ->. eapply wr_at_store_ok; eauto; lia. Qed.
Lemma u32arr_write : ltac2:(TCodec.tc2 tcn__CJ_Lib_Arr "QD'QJyR0%211'9y8%511%311p051'@'6%118&Dr5r4r3%43321';&Q8z%2215&Q9&Q;&5%12E:%311%52;1%:271&Cr7&Q4&Q7r6&Q:+4%221E%5241%711&Q1%11H%<3;31&J&Q=%11M%34Q9O1M%Q135=1p0C1p0O1pSHQ=1pS8Q81pSLQ71p2Q:1pS:Q<1").
Proof.
intros m A ws i v [Hb Hw] Hi.
destruct (upd_app_split ws (Z.to_nat i) v ltac:(lia)) as (pre & y & post & E & Hlen & Hupd).
split.
- eapply bytes_at_ext.
{ apply (bytes_at_write_inside segs m A (u32s ws) (4 * i) (le4 v) Hb); [lia|].
rewrite length_le4, u32s_length. lia. }
rewrite Hupd, E, !u32s_app. cbn [u32s].
replace (Z.to_nat (4 * i)) with (length (u32s pre)) by (rewrite u32s_length; lia).
apply upd_bytes_mid. rewrite !length_le4. reflexivity.
- rewrite upd_length. apply wr_at_write. exact Hw.
Qed.
Lemma u64s_split : ltac2:(TCodec.tc2 tcn__CJ_Lib_Arr "QJ'6'QJyR0%211%411'7'<'9%115&Q6r3r2%33921(1r1%22<1%:3841'=';r6&2(4r4%23D19%43E=1%C3E61&5%12H@r5%G3H21y8%N11%Q011&I%11?%21H&Q2%11?%51H%C3821%D3951%Q33971%@2;7&?u8%221A%Q83Q941%M261%N2C1%O2H1qS@Q>1%Q22Q?1qSBQ@1%Q42QA1p0Q61pSJQD1pS8QC1pSLQE1").
Proof.
intros ws i w H. destruct (nth_error_split _ _ _ H) as (pre & post & -> & Hlen).
exists pre, post. rewrite u64s_app. cbn -[le8]. rewrite u64s_length. repeat split; lia.
Qed.
Lemma u64arr_read : ltac2:(TCodec.tc2 tcn__CJ_Lib_Arr "QK'QJyR0%211'9y8%511%311p051'@'6%118&Er6r5r4%43321'<%>1?&Q6&Q=%116%33C81(1r3%22F1%93841&Q8z%221?&Q4&Q7r8&Q:+8%221F%5241%711%E3Q3G1%M1Q1%Q411&AvQIr:u8%4432O1&Q2%11Q2%I291%Q03941p0<1p0F1p0J1p0Q51pS0QC1pSJQD1pS8Q?1pSLQ>1p2QA1pS:QC1").
Proof.
intros m A ws i w a [Hb _] Hn Hi ->.
destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
rewrite (bytes_at_ov_read segs m A (u64s ws) (8 * Z.to_nat i) 8 Hb).
2:{ rewrite Eu, !app_length, length_le8, Hlu. lia. }
rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
rewrite firstn_app, firstn_all2 by (rewrite length_le8; lia).
rewrite length_le8, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.
Lemma u64arr_store_ok : ltac2:(TCodec.tc2 tcn__CJ_Lib_Arr "QE'QJyR0%211'9y8%511%311p051'@'6%118&Er5r4r3%43321';&Q8z%2215&Q9&Q;&5%12E:%311%52;1%:271'<&Q4&Q7r6&Q:+8%221D%5241%711%93Q2F1'3&BvQIr8u8%4432M1(:%A3721p091p0D1p0Q01pS0Q>1pS8Q91pSLQ81p2Q;1pS:Q=1").
Proof. intros m A ws i a [_ Hw] Hi ->. eapply wr_at_store_ok; eauto; lia. Qed.
Lemma u64arr_write : ltac2:(TCodec.tc2 tcn__CJ_Lib_Arr "QD'QJyR0%211'9y8%511%311p051'@'6%118&Er5r4r3%43321';&Q8z%2215&Q9&Q;&5%12E:%311%52;1%:271&Cr7&Q4&Q7r6&Q:+8%221E%5241%711&Q2%11H%<3;31&J&Q=%11M%34Q9O1M%Q135=1p0C1p0O1pSHQ=1pS8Q81pSLQ71p2Q:1pS:Q<1").
Proof.
intros m A ws i v [Hb Hw] Hi.
destruct (upd_app_split ws (Z.to_nat i) v ltac:(lia)) as (pre & y & post & E & Hlen & Hupd).
split.
- eapply bytes_at_ext.
{ apply (bytes_at_write_inside segs m A (u64s ws) (8 * i) (le8 v) Hb); [lia|].
rewrite length_le8, u64s_length. lia. }
rewrite Hupd, E, !u64s_app. cbn [u64s].
replace (Z.to_nat (8 * i)) with (length (u64s pre)) by (rewrite u64s_length; lia).
apply upd_bytes_mid. rewrite !length_le8. reflexivity.
- rewrite upd_length. apply wr_at_write. exact Hw.
Qed.
Lemma u8arr_frame : ltac2:(TCodec.tc2 tcn__CJ_Lib_Arr "QJ'QJyR0%211'9y8%511%311p051'@'6%115&Fr5r4r3%43321&Q8z%2214&Q7&Q;&5%12A8%311%52;1&Q<+2+R0%3221%=251'>r7r6%<2L1%>11%@241%D21H%@2Q0H%B11%D2K1%H219%;251&Cr9&Q4%11=%4331Q2r8%Q5321Ap081p0E1p0Q11p0Q51pSNQ;1pS0Q>1pS4Q=1p2Q@1pS:QB1").
Proof. intros m A bs a xs [Hb Hw] ? ? ?. split; [apply bytes_at_write_other; assumption| apply wr_at_write; assumption]. Qed.
Lemma u32arr_frame : ltac2:(TCodec.tc2 tcn__CJ_Lib_Arr "QN'QJyR0%211'9y8%511%311p051'@'6%118%216&Dr5r4r3%43321&Q8z%2214&Q7&Q;&5%12B8%311%52;1&Q<+2+R0%3221%=251'>r7&Q:+4r6%>2Q21%@11%5241%C271%G21K%C2Q4K%E11%G2N1%K21<%>251&Cr9&Q4%11>%4331Q5r8%Q8321Dp081p0H1p0Q41p0Q81pSNQ>1pS0QB1pSLQA1p2QD1pS:QF1").
Proof.
intros m A ws a xs [Hb Hw] ? ? ?. split; [|apply wr_at_write; assumption].
apply bytes_at_write_other; try assumption. rewrite u32s_length. lia.
Qed.
Lemma u64arr_frame : ltac2:(TCodec.tc2 tcn__CJ_Lib_Arr "QN'QJyR0%211'9y8%511%311p051'@'6%118%216&Er5r4r3%43321&Q8z%2214&Q7&Q;&5%12B8%311%52;1&Q<+2+R0%3221%=251'>r7&Q:+8r6%>2Q21%@11%5241%C271%G21K%C2Q4K%E11%G2N1%K21<%>251&Cr9&Q4%11>%4331Q5r8%Q8321Dp081p0H1p0Q41p0Q81pSNQ>1pS0QB1pSLQA1p2QD1pS:QF1").
Proof.
intros m A ws a xs [Hb Hw] ? ? ?. split; [|apply wr_at_write; assumption].
apply bytes_at_write_other; try assumption. rewrite u64s_length. lia.
Qed.
Lemma u8arr_bound : ltac2:(TCodec.tc2 tcn__CJ_Lib_Arr "Q4'QJyR0%211'9y8%511%311p051'@'6%115&Fr3r2r1%43321';&Q8z%2217&Q7&Q;&5%12B:%311%52=1&Q<+2+R0%3221%=251%?2<1p0A1pS4G1p2J1pS:L1").
Proof. intros m A bs [Hb _]. eapply bytes_at_bound; eauto. Qed.
Lemma u32arr_bound : ltac2:(TCodec.tc2 tcn__CJ_Lib_Arr "Q7'QJyR0%211'9y8%511%311p051'@'6%118&Dr3r2r1%43321';&Q8z%2217&Q7&Q:+4&Q;&5%12G<%311%6251%82@1&Q<+2+R0%3221%@251%B2?1p0D1pSLJ1p2M1pS:O1").
Proof. intros m A ws [Hb _]. pose proof (bytes_at_bound _ _ _ _ Hb). rewrite u32s_length in H. lia. Qed.
Lemma u64arr_bound : ltac2:(TCodec.tc2 tcn__CJ_Lib_Arr "Q7'QJyR0%211'9y8%511%311p051'@'6%118&Er3r2r1%43321';&Q8z%2217&Q7&Q:+8&Q;&5%12G<%311%6251%82@1&Q<+2+R0%3221%@251%B2?1p0D1pSLJ1p2M1pS:O1").
Proof. intros m A ws [Hb _]. pose proof (bytes_at_bound _ _ _ _ Hb). rewrite u64s_length in H. lia. Qed.
Lemma u8ro_frame : ltac2:(TCodec.tc2 tcn__CJ_Lib_Arr "QJ'QJyR0%211'9y8%511%311p051'@'6%115&Gr5r4r3%43321&Q8z%2214&Q7&Q;&5%12A8%311%52;1&Q<+2+R0%3221%=251'>r7r6%<2L1%>11%@241%D21H%@2Q0H%B11%D2K1%H219%;251&Cr9&Q4%11=%4331Q2r8%Q5321Ap081p0E1p0Q11p0Q51pSNQ;1pS0Q>1pS4Q=1p2Q@1pS:QB1").
Proof. intros m A bs a xs Hb ? ? ?. unfold u8ro. apply bytes_at_write_other; assumption. Qed.
Lemma u8arr_of_rw_cells : ltac2:(TCodec.tc2 tcn__CJ_Lib_Arr "Q2'QJyR0%211'9y8%511%311p051'@'7'6%116&Q5vQIr4r3(4'L(Kr2r1%3221(8%116%83731%=4<;:1&Fr5%231>9p041pS4C1pS>F1p2H1pS:J1").
Proof.
intros m A n bs [[Hwf Hb] Hw]. cbn in Hwf. destruct Hwf as [Hn _].
cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
cbn [cells_size csize] in Hw. rewrite Nat.add_0_r in Hw. subst n.
split; assumption.
Qed.
Lemma rw_cells_of_u8arr : ltac2:(TCodec.tc2 tcn__CJ_Lib_Arr "Q1'QJyR0%211'9y8%511%311p051'@'6%115&Fr3r2r1%43321&Q5vQIr4(4'L(K&5%12B:%321;(8%116%83731%<4;:@1p0>1pS4D1p2G1pS:I1").
Proof.
intros m A bs [Hb Hw]. split.
- split. { cbn. split; [reflexivity|exact I]. }
cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
- cbn [cells_size csize]. rewrite Nat.add_0_r. exact Hw.
Qed.
Lemma upd_firstn_skipn : forall {X} (l : list X) i x, (i < length l)%nat ->
upd l i x = firstn i l ++ x :: skipn (S i) l.
Proof.
intros X l. induction l as [|y l IH]; intros [|i] x Hi; cbn in Hi |- *; try lia; [reflexivity|].
rewrite IH by lia. reflexivity.
Qed.
Lemma nth_error_upd_same : forall {X} (l : list X) i x, (i < length l)%nat ->
nth_error (upd l i x) i = Some x.
Proof.
intros X l. induction l as [|y l IH]; intros [|i] x Hi; cbn in Hi |- *; try lia; [reflexivity|].
apply IH. lia.
Qed.
Lemma nth_error_upd_other : forall {X} (l : list X) i j x, i <> j ->
nth_error (upd l i x) j = nth_error l j.
Proof.
intros X l. induction l as [|y l IH]; intros [|i] [|j] x Hij; cbn; try reflexivity; [lia|].
apply IH. lia.
Qed.
Lemma u8arr_transport : ltac2:(TCodec.tc2 tcn__CJ_Lib_Arr "Q;'6&N%211'QJyR0%211'9y8%511%311p051'@%<14&Fr4r2r1%43321&Or6r5%33217&Q0vQI%23154&Mr8&Q;&5%12E?%311%635;1r7%D31>=p031p0;1p0?1p0D1pS4J1p2L1pS<N1pS:O1pRNQ81").
Proof.
intros W m m' A bs [Hb Hw] MU WM Hd. split.
- eapply bytes_at_transport; eauto.
- eapply wr_at_transport; eauto.
Qed.
Lemma u32arr_transport : ltac2:(TCodec.tc2 tcn__CJ_Lib_Arr "Q>'6&N%211'QJyR0%211'9y8%511%311p051'@%<17&Dr4r2r1%43321&Or6r5%33217&Q0vQI%23154&Mr8&Q:+4&Q;&5%12JA%311%6251%938>1r7%G31A@p031p0>1p0B1p0G1pSLM1p2O1pS<Q11pS:Q21pRNQ;1").
Proof.
intros W m m' A ws [Hb Hw] MU WM Hd. split.
- eapply bytes_at_transport; eauto. rewrite u32s_length, Nat2Z.inj_mul. exact Hd.
- eapply wr_at_transport; eauto.
Qed.
Lemma u64arr_transport : ltac2:(TCodec.tc2 tcn__CJ_Lib_Arr "Q>'6&N%211'QJyR0%211'9y8%511%311p051'@%<17&Er4r2r1%43321&Or6r5%33217&Q0vQI%23154&Mr8&Q:+8&Q;&5%12JA%311%6251%938>1r7%G31A@p031p0>1p0B1p0G1pSLM1p2O1pS<Q11pS:Q21pRNQ;1").
Proof.
intros W m m' A ws [Hb Hw] MU WM Hd. split.
- eapply bytes_at_transport; eauto. rewrite u64s_length, Nat2Z.inj_mul. exact Hd.
- eapply wr_at_transport; eauto.
Qed.
Lemma u8ro_transport : ltac2:(TCodec.tc2 tcn__CJ_Lib_Arr "Q7'6&N%211'QJyR0%211'9y8%511%311p051'@%<14&Gr4r2r1%43321&Or6r5%33217&Mr7&Q;&5r3%22C1%411%736?1%A3;:@p021p0;1p0@1pS4F1p2H1pS<J1pS:K1pRNQ41").
Proof. intros W m m' A bs Hb MU Hd. eapply bytes_at_transport; eauto. Qed.
End WithSegs.
