(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import PropExec MState Mem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Lib_Cells () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells.WithSegs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1Some"; "1app"; "1bool"; "1cons"; "1length"; "1list"; "1nat"; "1option"; "1true"; "2and"; "2eq"; "2ex"; "2iff"; "2or"; "3add"]; ["4le"; "5firstn"; "5skipn"; "6Z"; "7Segment"; "8ov_read_bytes"; "8write_to_mem"; ":cells_at"; "9cb_pieces"; "9cb_split"; "9cb_split_ok"; "9cbytes"; "9cell"; "9cell_at"; "9cell_upd"; "9cell_wf"]; ["9cells_at"; "9cells_bytes"; "9cells_size"; "9cells_wf"; "9csize"; ";wa"; "<add"; "<le"; "<of_nat"; "<pow"; "0a"; "0b"; "0bs"; "0c"; "0c'"; "0cs"]; ["0k"; "0m"; "0n"; "0post"; "0pre"; "0segs"; "=bv"; "0sz"]]).
Inductive cell : Type :=
| C8 (v : word)
| C4 (v : word)
| C2 (v : word)
| C1 (b : byte)
| CB (n : nat) (bs : list byte).
Definition csize (c : cell) : nat :=
match c with C8 _ => 8 | C4 _ => 4 | C2 _ => 2 | C1 _ => 1 | CB n _ => n end.
Definition cbytes (c : cell) : list byte :=
match c with C8 v => le8 v | C4 v => le4 v | C2 v => le2 v | C1 b => [b] | CB _ bs => bs end.
Fixpoint cells_size (cs : list cell) : nat :=
match cs with [] => 0 | c :: cs' => csize c + cells_size cs' end.
Fixpoint cells_bytes (cs : list cell) : list byte :=
match cs with [] => [] | c :: cs' => cbytes c ++ cells_bytes cs' end.
Definition cell_wf (c : cell) : Prop := match c with CB n bs => length bs = n | _ => True end.
Fixpoint cells_wf (cs : list cell) : Prop :=
match cs with [] => True | c :: cs' => cell_wf c /\ cells_wf cs' end.
Lemma cbytes_length : ltac2:(TCodec.tc2 tcn__CJ_Lib_Cells "C'L&Or1%211';'7&5'QFy8%211&Kr2%211%7241&Q4%114%<3;31p0>1pRLB1").
Proof.
intros [v|v|v|b|n bs] H; cbn -[le8 le4 le2].
- apply length_le8. - apply length_le4. - apply length_le2. - reflexivity. - exact H.
Qed.
Lemma cells_bytes_length : ltac2:(TCodec.tc2 tcn__CJ_Lib_Cells "E'6'L%211&Q3r1%211';'7&5'QFy8%211&Q1r2%211%7241&Q2%114%<3;31p0>1pS0B1").
Proof.
induction cs as [|c cs IH]; intros H; [reflexivity|].
cbn [cells_bytes cells_size]. destruct H as [H1 H2]. rewrite app_length, cbytes_length, IH by assumption. reflexivity.
Qed.
Fixpoint cell_at (cs : list cell) (k : nat) : option cell :=
match cs with
| [] => None
| c :: cs' => if Nat.eqb k 0 then Some c
else if Nat.ltb k (csize c) then None
else cell_at cs' (k - csize c)
end.
Fixpoint cell_upd (cs : list cell) (k : nat) (c' : cell) : list cell :=
match cs with
| [] => []
| c :: cs' => if Nat.eqb k 0 then c' :: cs'
else c :: cell_upd cs' (k - csize c) c'
end.
Lemma cells_wf_app : ltac2:(TCodec.tc2 tcn__CJ_Lib_Cells "A'6'L%211&=&Q3&2r2r1%33721%511':%715%815%3221%;251pRH=1pRF>1").
Proof. induction a as [|c a IH]; intros b; cbn; [tauto|]. rewrite IH. tauto. Qed.
Lemma cells_bytes_app : ltac2:(TCodec.tc2 tcn__CJ_Lib_Cells "D'6'L%211';'QFy8%211%711&Q1&2r2r1%33;21%511%614%714%73:21%>3:41pRH@1pRFA1").
Proof. induction a; intros; cbn; [reflexivity|]. rewrite IHa, app_assoc. reflexivity. Qed.
Lemma cells_size_app : ltac2:(TCodec.tc2 tcn__CJ_Lib_Cells "B'6'L%211';'7&Q2&2r2r1%33821%511&?%715%815%3221%<3;51pRH>1pRF?1").
Proof. induction a; intros; cbn; [reflexivity|]. rewrite IHa. lia. Qed.
Lemma cell_at_split : ltac2:(TCodec.tc2 tcn__CJ_Lib_Cells "Q='6'L%211'7';'8%115&Mr4r3%3221(1r2%22<1%:3841'<':r7&2(4r5r1%33E21%53F;1%D3F71&Q2%11>r6%H3I21&N%13=3F%<3NG:%>3OD1%M3O31%B261%C2;1qS8Q21%F2Q31qS:Q41%H2Q51p0J1pRNQ81pRLQ91pS2Q81pS0Q:1").
Proof.
induction cs as [|c0 cs IH]; intros k c c' H; [discriminate|].
cbn [cell_at cell_upd] in *. destruct (Nat.eqb_spec k 0).
- inversion H; subst. exists [], cs. repeat split; auto.
- destruct (Nat.ltb_spec0 k (csize c0)); [discriminate|].
destruct (IH _ _ c' H) as (pre & post & -> & Hsz & Hupd).
exists (c0 :: pre), post. repeat split; auto.
+ cbn. lia.
+ cbn. rewrite Hupd. reflexivity.
Qed.
Lemma skipn_app_exact : forall {X} (a b : list X), skipn (length a) (a ++ b) = b.
Proof. intros X a b. rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity. Qed.
Lemma firstn_app_exact : forall {X} (a b : list X), firstn (length a) (a ++ b) = a.
Proof. intros X a b. rewrite firstn_app, firstn_all, Nat.sub_diag. cbn. apply app_nil_r. Qed.
Section WithSegs.
Variable segs : list Segment.
Definition cells_at (m : word -> option byte) (A : Z) (cs : list cell) : Prop :=
cells_wf cs /\ bytes_at segs m A (cells_bytes cs).
Lemma cells_at_read : ltac2:(TCodec.tc2 tcn__CJ_Lib_Cells "QD'QFyR0%211'8y8%511%311p051'C'6'L%211'7&Gr5r4r3%43321';%@19&M%1265(1r2%22>1%73641%A1E%H11&EvQEr7&Q5&Q6r6&Q8%11D%4231%611&Q4%11G%<4;:31&K%11J%E2A1%J3A41p0D1p0M1pRLQ51pS2Q41pS0Q61p2Q:1pS4Q<1").
Proof.
intros m A cs k c [Hwf Hb] Hc.
destruct (cell_at_split _ _ _ c Hc) as (pre & post & Ecs & Hsz & _).
rewrite Ecs in Hwf, Hb. apply cells_wf_app in Hwf. destruct Hwf as [Hwpre [Hwc Hwpost]].
rewrite cells_bytes_app in Hb. cbn [cells_bytes] in Hb.
apply bytes_at_app in Hb. destruct Hb as [_ Hb].
rewrite cells_bytes_length in Hb by assumption. rewrite Hsz in Hb.
apply bytes_at_app in Hb. destruct Hb as [Hb _].
rewrite <- (cbytes_length c) by assumption.
rewrite <- (Z.add_0_r (A + Z.of_nat k)). change 0%Z with (Z.of_nat 0).
rewrite (bytes_at_ov_read segs _ _ _ 0 (length (cbytes c)) Hb) by lia.
cbn [skipn]. rewrite firstn_all. reflexivity.
Qed.
Lemma cells_at_write : ltac2:(TCodec.tc2 tcn__CJ_Lib_Cells "QK'QFyR0%211'8y8%511%311p051'C'6'L%211'7&Gr6r5r4%43321';%@19&M%1265(1r3%22>1%73641&Q4%114%21<%;3A21&O%11?&Fr:&Q5&Q6r9&Q8r7%211%5241%711&K%11L%<3;31&Nr8%2319Q0%Q334<1p0B1p0E1p0J1p0Q31pRNQ;1pRLQ<1pS2Q;1pS0Q=1p2QA1pS4QC1").
Proof.
intros m A cs k c c' [Hwf Hb] Hc Hsz Hwf'.
destruct (cell_at_split _ _ _ c' Hc) as (pre & post & Ecs & Hszp & Hupd).
rewrite Hupd. rewrite Ecs in Hwf, Hb. apply cells_wf_app in Hwf. destruct Hwf as [Hwpre [Hwc Hwpost]].
split. { apply cells_wf_app. cbn. tauto. }
rewrite cells_bytes_app in *. cbn [cells_bytes] in *.
pose proof (cells_bytes_length pre Hwpre) as Lpre.
pose proof (cbytes_length c Hwc) as Lc. pose proof (cbytes_length c' Hwf') as Lc'.
replace (A + Z.of_nat k)%Z with (A + Z.of_nat (length (cells_bytes pre)))%Z by (rewrite Lpre, Hszp; reflexivity).
pose proof (bytes_at_bound _ _ _ _ Hb) as HB. rewrite !app_length in HB.
replace (cells_bytes pre ++ cbytes c' ++ cells_bytes post)
with (upd_bytes (cells_bytes pre ++ cbytes c ++ cells_bytes post) (Z.to_nat (Z.of_nat (length (cells_bytes pre)))) (cbytes c')).
- apply bytes_at_write_inside; [exact Hb| lia |]. rewrite !app_length. lia.
- unfold upd_bytes. rewrite Nat2Z.id. rewrite firstn_app_exact. f_equal. f_equal.
replace (length (cells_bytes pre) + length (cbytes c'))%nat with (length (cells_bytes pre ++ cbytes c)) by (rewrite app_length; lia).
rewrite app_assoc. apply skipn_app_exact.
Qed.
Lemma cells_at_frame : ltac2:(TCodec.tc2 tcn__CJ_Lib_Cells "QM'QFyR0%211'8y8%511%311p051'C'6'L%211%317&Gr5r4r3%43321&Q7z%2214&Q6&Q8&5%12C8%311%52;1&Q9+2+R0%3221%=251'>r7&Q2r6%211%?11%A251%E21I%A2Q3I%C11%E2L1%I21:%<251&Fr9&Q5%11=%4331Q3r8%Q6321Bp081p0F1p0Q21p0Q61pRJQ<1pRFQA1pS0Q?1p2QC1pS4QE1").
Proof.
intros m A cs a bs [Hwf Hb] Ha Hl Hd. split; [assumption|].
apply bytes_at_write_other; try assumption. rewrite cells_bytes_length by assumption. exact Hd.
Qed.
Lemma cells_at_bound : ltac2:(TCodec.tc2 tcn__CJ_Lib_Cells "Q5'QFyR0%211'8y8%511%311p051'C'6'L%211&Gr3r2r1%43321':&Q7z%2217&Q6&Q8&Q2%11:%311%52=1&Q9+2+R0%3221%=251%?2<1p0A1pS0G1p2K1pS4M1").
Proof. intros m A cs [Hwf Hb]. rewrite <- cells_bytes_length by assumption. eapply bytes_at_bound; eauto. Qed.
Lemma cells_at_wf : ltac2:(TCodec.tc2 tcn__CJ_Lib_Cells "G'QFyR0%211'8y8%511%311p051'C'6'L%211&Gr3r2r1%43321&Q3%114p031pS091p2=1pS4?1").
Proof. intros m A cs [H _]; exact H. Qed.
End WithSegs.
Lemma CB3_bytes : ltac2:(TCodec.tc2 tcn__CJ_Lib_Cells "Q0'7'6'QFy8%211%411'@&?r3r2%3221&5r1%2291%8241';&2&Ar4%23?1:&B%13A3<%53B>1%@25?%43D1?%93E31%:3F71%<3F1Bp0>1pRJH1pS6N1pS2O1").
Proof.
intros k n bs H. rewrite <- (firstn_skipn k bs) at 4. f_equal.
rewrite <- (firstn_skipn n (skipn k bs)) at 2. f_equal. rewrite skipn_skipn. f_equal. lia.
Qed.
Definition cb_pieces (k n sz : nat) (bs : list byte) : list cell :=
(if Nat.eqb k 0 then [] else [CB k (firstn k bs)])
++ CB n (firstn n (skipn k bs))
:: (if Nat.eqb (k + n) sz then [] else [CB (sz - k - n) (skipn (k + n) bs)]).
Section SE.
Local Abbreviation SEC_T_cb_pieces_props := (ltac2:(TCodec.tc2 tcn__CJ_Lib_Cells "Q7'7'6'QFy8%211%411';&5r1%2251r2%53;21'@&?r5r4%3221r3%6221':&Q3&Hr6%241986%411&Q1%113%E3F1:&Q2%116%H3N1?%<241%=281p0?1p0G1pRJN1pS@Q41pS6Q51pS2Q61")) (only parsing).
Variable k : ltac:(sec_ty2 constr:(SEC_T_cb_pieces_props) 0%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_cb_pieces_props) 1%nat 0%nat).
Variable sz : ltac:(sec_ty2 constr:(SEC_T_cb_pieces_props) 2%nat 0%nat).
Variable bs : ltac:(sec_ty2 constr:(SEC_T_cb_pieces_props) 3%nat 0%nat).
Lemma cb_pieces_props : ltac:(sec_stmt2 constr:(SEC_T_cb_pieces_props) 4%nat 0%nat).
Proof.
intros Hl Hkn.
unfold cb_pieces.
destruct (Nat.eqb_spec k 0); destruct (Nat.eqb_spec (k + n) sz); subst; cbn -[firstn skipn Nat.sub];
rewrite ?firstn_length, ?skipn_length, ?app_nil_r.
- cbn [skipn]. repeat split; try lia. apply firstn_all2. lia.
- cbn [skipn Nat.add]. repeat split; try lia. apply firstn_skipn.
- repeat split; try lia. rewrite <- (firstn_skipn k bs) at 3. f_equal. apply firstn_all2. rewrite skipn_length. lia.
- repeat split; try lia. apply CB3_bytes. lia.
Qed.
End SE.
Fixpoint cb_split (cs : list cell) (k n : nat) : list cell :=
match cs with
| [] => []
| c :: cs' =>
if Nat.ltb k (csize c) then
match c with
| CB sz bs => if (Nat.eqb k 0 && Nat.eqb n sz)%bool then c :: cs' else cb_pieces k n sz bs ++ cs'
| _ => c :: cs'
end
else c :: cb_split cs' (k - csize c) n
end.
Fixpoint cb_split_ok (cs : list cell) (k n : nat) : bool :=
match cs with
| [] => true
| c :: cs' =>
if Nat.ltb k (csize c) then
match c with
| CB sz bs => Nat.leb (k + n) sz
| _ => true
end
else cb_split_ok cs' (k - csize c) n
end.
Lemma cb_split_props : ltac2:(TCodec.tc2 tcn__CJ_Lib_Cells "Q7'6'L%211'7&Q3r3%211';'3&Jr4r2%33271(9%73621':&Ir5%2318=%?11'QFy8%211%G11&Q1%117%219%D3421&Q2%11;%21=%H3L21%A251%B2>1p0D1p0M1pS6Q11pS2Q21pS0Q41").
Proof.
induction cs as [|c cs IH]; intros k n Hwf Hok; [cbn; tauto|].
cbn [cells_wf] in Hwf. destruct Hwf as [Hc Hcs].
cbn [cb_split cb_split_ok] in *.
destruct (Nat.ltb k (csize c)) eqn:LT.
- destruct c as [v|v|v|b|sz bs]; try (cbn; tauto).
cbn [cell_wf] in Hc. apply Nat.leb_le in Hok.
destruct (Nat.eqb k 0 && Nat.eqb n sz)%bool; [cbn; tauto|].
destruct (cb_pieces_props k n sz bs Hc Hok) as (A1 & A2 & A3).
rewrite cells_bytes_app, cells_size_app, A2, A3. split; [|split; [reflexivity|cbn; lia]].
apply cells_wf_app. cbn. tauto.
- cbn. destruct (IH (k - csize c)%nat n Hcs Hok) as (A1 & A2 & A3). rewrite A2, A3. tauto.
Qed.
Lemma cells_at_cb_split : ltac2:(TCodec.tc2 tcn__CJ_Lib_Cells "Q9'6'D%211'QFyR0%211'8y8%511%311p051'C'L%=11'7&Q0r6r5r4r3%544321';'3&Jr2%23761(9%63521r8r7&I%13>=<%A443@1p061p0>1pS6E1pS2F1pS0H1p2K1pS4M1pS<Q61").
Proof.
intros segs m A cs k n [Hwf Hb] Hok. destruct (cb_split_props cs k n Hwf Hok) as (A1 & A2 & A3).
split; [exact A1|]. rewrite A2. exact Hb.
Qed.
Lemma cells_size_cb_split : ltac2:(TCodec.tc2 tcn__CJ_Lib_Cells "K'6'L%211'7&Q3r3%211';'3&Jr4r2%33271(9%73621&Q2&Ir5%2318=%411%513%>3B21p081p0A1pS6E1pS2F1pS0H1").
Proof. intros. eapply cb_split_props; eauto. Qed.
