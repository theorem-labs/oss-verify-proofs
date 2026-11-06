(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim StoreOk HeapIface HeapIfaceA As0Tables ArtMem JbtPoison JbtInitCache JbtPopulate1 ArtRuns JbtCls JbtFp JbtClsRep JbtSecAllocPost JbtFxQ
ArtBridge JbtInv JbtInvFreePure JbtInvRepX
JbtRecycle1 JbtRecycle2C JbtRecycle3L JbtRecycle5A JbtRecycle5I JbtRecycle5T JbtRecycle5C JbtRecycle5D JbtInvRecycleA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtInvRecycleD () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtBridge."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtRuns."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtCls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtInvRecycleA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtInvRecycleD."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtRecycle2C."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtRecycle5A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtRecycle5T."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."], [["1Some"; "1app"; "1bool"; "1cons"; "1fst"; "1length"; "1list"; "1negb"; "1nil"; "1option"; "1pair"; "1prod"; "1true"; "2and"; "2eq"; "2ex"]; ["2iff"; "2not"; "2or"; "3le"; "4map"; "5Z"; "0G"; "6art_live"; "7AMunmap"; "7aev"; "8art_cls"; "8cl_au"; "8cl_cache"; "8cl_free"; "8cl_mfa"; "8cl_mu"]; ["9art_sec"; "9sc_map"; ":art_rel_key"; ":art_rg_ok"; ":art_sec_b"; ";art_key_in"; ";art_rel_mb"; ";art_sec_rcy"; "<art_flush_events"; "=RG"; "=art_bl_idx"; "=art_rel"; "=art_rel_steps"; "=art_rg"; "=rg_bl"; "=rg_cls"]; [">art_rels_events"; ">art_rels_pre"; "?In"; "?NoDup"; "?filter"; "?nth_error"; "@add"; "@eqb"; "@le"; "@of_nat"; "0c"; "0cls"; "0l"; "0log"; "0mb"; "0ms"]; ["0p"; "0s"; "0s0"; "0w"; "0work"]]).
Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition art_dsec : art_sec := SEC 0 0 0 0 false.
Definition art_sec_step (e : art_rel) (l : list art_sec) : list art_sec :=
match e with RES mb _ _ _ _ => art_swap_remove art_dsec (art_bl_idx mb (map art_sec_b l)) l | _ => l end.
Definition art_sec_rcy (work : list art_rel) (l : list art_sec) : list art_sec := fold_left (fun l e => art_sec_step e l) work l.
Lemma art_sec_rcy_b : ltac2:(TCodec.tc2 tcn__JbtInvRecycleD "O'6'Q;%211'E'Jp021'Q0%711'>';%1277%;11&Q>&Q<r3(Q9r2&D&Q4r1%34>:21%6251%9281%;11&Q7%12;6%94D@81%C3@41pSJE1pSHH1pT:L1").
Proof.
induction work as [|e r IH]; intros cls l; [reflexivity|]. unfold art_rel_steps, art_sec_rcy in *. cbn [fold_left].
destruct e as [c w d b1 n|mb ms m b1 n|wb]; cbn [art_rel_step art_sec_step rg_cls rg_bl]; try apply IH.
rewrite <- (art_swap_remove_map _ _ art_sec_b art_dsec). apply IH.
Qed.
Lemma art_bl_idx_sec : ltac2:(TCodec.tc2 tcn__JbtInvRecycleD "Q5'6'Q0%211'E&QBr1&D&Q1r2%348621%63751'?'='>'9%11>&QEr4&Q:r3';%12BB&Q4%A4F216%6251%93H81(0%12JF%?3=31%F1H%A3K1;%C231qT6O1%F2Q01p0H1pSNQ01pSJQ21").
Proof.
induction l as [|s r IH]; intros mb Hin; [destruct Hin|]. cbn [map art_bl_idx]. cbn [art_sec_b fst]. destruct (Z.eqb_spec (sc_map s) mb) as [E|NE].
- exists s. split; [reflexivity|exact E].
- destruct Hin as [E|Hin]; [contradiction|]. exact (IH mb Hin).
Qed.
Lemma art_swap_remove_nodup : forall (A B : Type) (f : A -> B) (d : A) i l, List.NoDup (map f l) -> List.NoDup (map f (art_swap_remove d i l)).
Proof.
intros A B f d i l ND. rewrite art_swap_remove_map. rewrite (NoDup_nth_error) in ND |- *. intros j1 j2 Hj1 E.
rewrite art_swap_remove_length in Hj1. rewrite length_map in Hj1.
assert (Hj2 : (j2 < length (map f l) - 1)%nat).
{ destruct (Nat.lt_ge_cases j2 (length (map f l) - 1)) as [H|H]; [exact H|]. exfalso.
rewrite (proj2 (nth_error_None (art_swap_remove (f d) i (map f l)) j2)) in E by (rewrite art_swap_remove_length; exact H).
apply nth_error_None in E. rewrite art_swap_remove_length, length_map in E. lia. }
rewrite !art_swap_remove_nth in E by (rewrite ?length_map in *; assumption).
assert (B1 : ((if (j1 =? i)%nat then (length (map f l) - 1)%nat else j1) < length (map f l))%nat) by (rewrite length_map in *; destruct (j1 =? i)%nat; lia).
pose proof (ND _ _ B1 E) as EJ. rewrite length_map in *.
destruct (Nat.eqb_spec j1 i) as [E1|E1]; destruct (Nat.eqb_spec j2 i) as [E2|E2]; lia.
Qed.
Lemma art_swap_remove_gone : forall (A B : Type) (f : A -> B) (d : A) i l x, List.NoDup (map f l) -> (i < length l)%nat -> In x (art_swap_remove d i l) -> f x <> f (nth i l d).
Proof.
intros A B f d i l x ND Hi Hx E. destruct (In_nth_error _ _ Hx) as (j & Hj).
assert (Hjl : (j < length l - 1)%nat) by (rewrite <- (art_swap_remove_length _ d i l); apply nth_error_Some; rewrite Hj; discriminate).
rewrite art_swap_remove_nth in Hj by exact Hjl. set (j' := if (j =? i)%nat then (length l - 1)%nat else j) in *.
assert (NEj : j' <> i) by (unfold j'; destruct (Nat.eqb_spec j i) as [E1|E1]; lia).
rewrite NoDup_nth_error in ND. apply NEj. apply ND; [rewrite length_map; unfold j'; destruct (j =? i)%nat; lia|].
rewrite !nth_error_map, Hj. rewrite (nth_error_nth' l d Hi). cbn. f_equal. exact E.
Qed.
Definition art_rel_mb (e : art_rel) : option Z := match e with RES mb _ _ _ _ => Some mb | _ => None end.
Lemma art_sec_rcy_in : ltac2:(TCodec.tc2 tcn__JbtInvRecycleD "A'6'Q;%211'Q0%411&QBr1&Q7r3r2%3221%63851%73934p021pT4;1pSJ;1pT:>1").
Proof.
induction work as [|e r IH]; intros l s H; [exact H|]. unfold art_sec_rcy in *. cbn [fold_left] in H. apply IH in H.
destruct e; cbn [art_sec_step] in H; try exact H. exact (art_swap_remove_in _ _ _ _ _ H).
Qed.
Lemma art_sec_rcy_nodup : ltac2:(TCodec.tc2 tcn__JbtInvRecycleD "E'6'Q;%211'Q0%411'QC'E&D&Q1r1%347421%6251&Q7r3r2%3221%94=:81%<2;1p071pSJ?1pT:B1").
Proof.
induction work as [|e r IH]; intros l ND; [exact ND|]. unfold art_sec_rcy in *. cbn [fold_left]. apply IH.
destruct e; cbn [art_sec_step]; try exact ND. apply art_swap_remove_nodup. exact ND.
Qed.
Lemma art_sec_rcy_notin : ltac2:(TCodec.tc2 tcn__JbtInvRecycleD "Q9'6'Q;%211'Q0%411'E'QC&D&Q1r3%347521%5261&QB&Q7r5r4%3221%53>81'9%11>(0%12@<&Q6r6%A4G521%=3641%C4GEB3%?3F<1&A'>%F17%23J1A%411p061p091p0B1p0I1pSNQ01pT4Q31pSJQ31pT:Q61").
Proof.
induction work as [|e r IH]; intros l s mb ND Hs Hmb Hl; [destruct Hmb|]. unfold art_sec_rcy in *. cbn [fold_left] in Hs. cbn [map] in Hmb.
destruct Hmb as [Ee|Hmb].
- destruct e as [c w d b1 n|mb0 ms m b1 n|wb]; cbn [art_rel_mb] in Ee; try discriminate Ee. injection Ee as ->. cbn [art_sec_step] in Hs.
apply art_sec_rcy_in in Hs. destruct (art_bl_idx_sec l mb Hl) as (s0 & Hn & Es0).
pose proof (art_swap_remove_gone _ _ sc_map art_dsec _ l s ND ltac:(apply nth_error_Some; rewrite Hn; discriminate) Hs) as NE.
rewrite (nth_error_nth _ _ art_dsec Hn) in NE. rewrite Es0 in NE. exact NE.
- set (l1 := art_sec_step e l) in *. destruct (in_dec Z.eq_dec mb (map sc_map l1)) as [X|X].
+ apply (IH l1 s mb); [|exact Hs|exact Hmb|exact X]. unfold l1. destruct e; cbn [art_sec_step]; try exact ND. apply art_swap_remove_nodup. exact ND.
+ intros E. apply X. rewrite <- E. apply in_map. exact (art_sec_rcy_in r l1 s Hs).
Qed.
Lemma art_mb_key : ltac2:(TCodec.tc2 tcn__JbtInvRecycleD "K'6'Q;%211'E&QB'9%113(0r1%2261&D&Q6r2%34<721%:3851';%12==(:z%24@@17&Q2r3%<4E621%C3741p0:1pSNF1pT:H1").
Proof.
induction work as [|e r IH]; intros mb H; [destruct H|]. cbn [map] in *. destruct H as [E|H]; [left|right; exact (IH mb H)].
destruct e; cbn [art_rel_mb art_rel_key] in *; try discriminate E. injection E as ->. reflexivity.
Qed.
Lemma art_sec_rcy_keep : ltac2:(TCodec.tc2 tcn__JbtInvRecycleD "QC'6'Q;%211'Q0%411&QBr1r2%33521&A'9'E%211(0&Q1%118%3251&D&Q6r4%34C821%@3951%=11%:2<Ar6%84H=71%E3>31%:4H@=3%G3AE1p031pSNC1'QC';%12FF&Q2%B4Q221;%5231%62J:&Q7r8r7%3221%Q53Q7B1p061p081p0?1p0H1p0Q71pT4Q=1pSJQ=1pT:Q@1").
Proof.
induction work as [|e r IH]; intros l s Hs NI ALL NDw ND; [exact Hs|]. unfold art_sec_rcy in *. cbn [fold_left]. cbn [map] in NI, ALL, NDw.
inversion NDw as [|? ? Hn NDr]; subst.
assert (ND1 : List.NoDup (map sc_map (art_sec_step e l))) by (destruct e; cbn [art_sec_step]; try exact ND; apply art_swap_remove_nodup; exact ND).
assert (Hs1 : In s (art_sec_step e l)).
{ destruct e as [c w d b1 n|mb ms m b1 n|wb]; cbn [art_sec_step]; try exact Hs. cbn [art_rel_mb] in NI, ALL.
destruct (art_bl_idx_sec l mb (ALL mb (or_introl eq_refl))) as (s0 & Hn0 & Es0).
apply art_swap_remove_keeps; [apply nth_error_Some; rewrite Hn0; discriminate|exact Hs|]. rewrite (nth_error_nth _ _ art_dsec Hn0). intros E. apply NI. left. rewrite E, Es0. reflexivity. }
apply IH; [exact Hs1|intros X; apply NI; right; exact X| |exact NDr|exact ND1].
intros mb Hmb. pose proof (ALL mb (or_intror Hmb)) as Hl. apply in_map_iff in Hl. destruct Hl as (s1 & Es1 & Hs1l).
destruct e as [c w d b1 n|mb0 ms m b1 n|wb]; cbn [art_sec_step]; try (rewrite <- Es1; apply in_map; exact Hs1l).
cbn [art_rel_mb art_rel_key] in Hn, ALL. destruct (art_bl_idx_sec l mb0 (ALL mb0 (or_introl eq_refl))) as (s0 & Hn0 & Es0).
rewrite <- Es1. apply in_map. apply art_swap_remove_keeps; [apply nth_error_Some; rewrite Hn0; discriminate|exact Hs1l|].
rewrite (nth_error_nth _ _ art_dsec Hn0). intros E. apply Hn. rewrite <- Es0, <- E, Es1. exact (art_mb_key r mb Hmb).
Qed.
Lemma art_sec_rcy_len : ltac2:(TCodec.tc2 tcn__JbtInvRecycleD "@'6'Q;%211'Q0%411'C&5&Q7r2r1%3221%5281%6293%8221pSJ:1pT:=1").
Proof.
induction work as [|e r IH]; intros l; [cbn; lia|]. unfold art_sec_rcy in *. cbn [fold_left]. specialize (IH (art_sec_step e l)).
destruct e; cbn [art_sec_step] in *; try exact IH. rewrite art_swap_remove_length in IH. lia.
Qed.
Lemma art_steps_au : ltac2:(TCodec.tc2 tcn__JbtInvRecycleD "Q0'6'Q;%211'Q='E'='>&K&Q?&Q<r3r2%3221r1%6221%811%8253%:11%<3>31&O%116%215%@3B21&N%11:%219%D3F21%F251%G2:1pSFI1pQ>K1pT:M1").
Proof.
induction work as [|e r IH]; intros G c; [repeat split|]. unfold art_rel_steps in *. cbn [fold_left]. destruct (IH (art_rel_step e G) c) as (E1 & E2 & E3). rewrite E1, E2, E3.
destruct e as [c0 w0 d0 b10 n0|mb0 ms0 m0 b10 n0|wb0]; cbn [art_rel_step rg_cls]; [|repeat split|].
- destruct (Z.eq_dec c c0) as [->|NE]; [rewrite art_cls_upd_same; exact (art_cls_dealloc_au c0 w0 (rg_cls G c0))|rewrite art_cls_upd_other by exact NE; repeat split].
- destruct (Z.eq_dec c 24) as [->|NE]; [rewrite art_cls_upd_same; exact (art_cls_dealloc_au 24 wb0 (rg_cls G 24))|rewrite art_cls_upd_other by exact NE; repeat split].
Qed.
Lemma art_steps_in : ltac2:(TCodec.tc2 tcn__JbtInvRecycleD "QI'6'Q;%211'Q='E&Q3r3%211&QAr4r5%3221'=&QH+1%2216+N%4281%6231&@&QB&1&L&Q?&Q<r7r6%3221%521B%711&M%113%;3L31%=3MH1'B%<29I%>11%712%A3Q221%C3Q3N1';%12Q5Q5(:%14Q7Q7Q1Q2&D&Q2%24Q=51E%K3641%>291%N2@1p0Q01p0Q81p0Q=1pT8QA1pSFQB1pQ>QD1pT:QF1").
Proof.
induction work as [|e r IH]; intros G c w OK PRE Hc; [cbn; tauto|]. destruct PRE as (Pe & Pr). unfold art_rel_steps in *. cbn [fold_left map].
rewrite (IH (art_rel_step e G) c w (art_rg_ok_step e G OK Pe) Pr Hc). destruct OK as (CK & _).
destruct e as [c0 w0 d0 b10 n0|mb0 ms0 m0 b10 n0|wb0]; cbn [art_rel_step rg_cls art_rel_key art_rel_pre] in *.
- destruct Pe as (Hc0 & _). destruct (Z.eq_dec c c0) as [->|NE].
+ rewrite art_cls_upd_same. rewrite (art_cls_dealloc_in c0 w0 (rg_cls G c0) w (CK c0 Hc0) ltac:(lia)).
split; [intros [[->|H]|H]; [right; left; reflexivity|left; exact H|right; right; exact H]|intros [H|[E|H]]; [left; right; exact H|left; left; injection E as ->; reflexivity|right; exact H]].
+ rewrite art_cls_upd_other by exact NE. split; [intros [H|H]; [left; exact H|right; right; exact H]|intros [H|[E|H]]; [left; exact H|injection E as E _; lia|right; exact H]].
- split; [intros [H|H]; [left; exact H|right; right; exact H]|intros [H|[E|H]]; [left; exact H|injection E as E _; lia|right; exact H]].
- destruct (Z.eq_dec c 24) as [->|NE].
+ rewrite art_cls_upd_same. rewrite (art_cls_dealloc_in 24 wb0 (rg_cls G 24) w (CK 24 ltac:(lia)) ltac:(lia)).
split; [intros [[->|H]|H]; [right; left; reflexivity|left; exact H|right; right; exact H]|intros [H|[E|H]]; [left; right; exact H|left; left; injection E as ->; reflexivity|right; exact H]].
+ rewrite art_cls_upd_other by exact NE. split; [intros [H|H]; [left; exact H|right; right; exact H]|intros [H|[E|H]]; [left; exact H|injection E as E _; lia|right; exact H]].
Qed.
Lemma art_steps_total : ltac2:(TCodec.tc2 tcn__JbtInvRecycleD "QG'6'Q;%211'Q='E&Q3r2%211&QAr3r4%3221'=&QH+1%2216+N%4281%6231&QF&QI&5&L&Q?&Q<r6r5%3221%521B%711%92J1%;11&M%115%=2N1%?11%A251%>2;K%@11%B2Q31%D11%914%E2Q61%G11%I241%H2Q<D%J11%L231%Q32<1p0O1p0Q71p0Q<1pSFQ@1pQ>QB1pT:QD1").
Proof.
induction work as [|e r IH]; intros G c OK PRE Hc; [cbn; lia|]. destruct PRE as (Pe & Pr). unfold art_rel_steps in *. cbn [fold_left length].
specialize (IH (art_rel_step e G) c (art_rg_ok_step e G OK Pe) Pr Hc). destruct OK as (CK & _).
destruct e as [c0 w0 d0 b10 n0|mb0 ms0 m0 b10 n0|wb0]; cbn [art_rel_step rg_cls art_rel_pre] in *.
- destruct Pe as (Hc0 & _). destruct (Z.eq_dec c c0) as [->|NE]; [rewrite art_cls_upd_same in IH|rewrite art_cls_upd_other in IH by exact NE; lia].
pose proof (art_cls_dealloc_total c0 w0 (rg_cls G c0) (CK c0 Hc0) ltac:(lia)). lia.
- lia.
- destruct (Z.eq_dec c 24) as [->|NE]; [rewrite art_cls_upd_same in IH|rewrite art_cls_upd_other in IH by exact NE; lia].
pose proof (art_cls_dealloc_total 24 wb0 (rg_cls G 24) (CK 24 ltac:(lia)) ltac:(lia)). lia.
Qed.
Lemma art_live_app_unmap : ltac2:(TCodec.tc2 tcn__JbtInvRecycleD "Q6'6'I%211'E'>';%1233%711&G&1r3&Q8r2r1%3221(3(H%1254(8%11B%53C31%<3D71%=3E<1%?11&QD&7&QG&4%13II?%321C%511qT2I1%H1F%93K21%N3K;1pT0Q01pSNQ11pSLQ31").
Proof.
intros log mb ms. rewrite app_assoc, art_live_snoc. cbn [art_ev_live]. f_equal.
unfold art_flush_events. destruct (art_flush_beg mb <? art_flush_end mb ms); [rewrite art_live_snoc; reflexivity|rewrite app_nil_r; reflexivity].
Qed.
Lemma art_live_rcy : ltac2:(TCodec.tc2 tcn__JbtInvRecycleD "Q8'6'Q;%211'I%411';'E%2211&@&QBr1&G&1r2&Q@r3%211%53>41%711%:3<91'=%:18%=3?<1&A'9%11C(0&4%13FFB%32G1&D&Q6%24O71A%H3841%;11%?2=1%L2A1pT2N1pSLQ21pT:Q51").
Proof.
induction work as [|e r IH]; intros log p.
- unfold art_rels_events. cbn [flat_map map In]. rewrite app_nil_r. tauto.
- change (art_rels_events (e :: r)) with (art_rel_events e ++ art_rels_events r). rewrite app_assoc, IH. cbn [map In].
destruct e as [c w d b1 n|mb ms m b1 n|wb]; cbn [art_rel_events art_rel_mb]; rewrite ?app_nil_r.
+ split; [intros (H1 & H2); split; [exact H1|intros [X|X]; [discriminate X|exact (H2 X)]]|intros (H1 & H2); split; [exact H1|intros X; apply H2; right; exact X]].
+ rewrite art_live_app_unmap, filter_In. rewrite negb_true_iff, Z.eqb_neq.
split; [intros ((H1 & H0) & H2); split; [exact H1|intros [X|X]; [injection X as X; apply H0; symmetry; exact X|exact (H2 X)]]
|intros (H1 & H2); split; [split; [exact H1|intros X; apply H2; left; rewrite X; reflexivity]|intros X; apply H2; right; exact X]].
+ split; [intros (H1 & H2); split; [exact H1|intros [X|X]; [discriminate X|exact (H2 X)]]|intros (H1 & H2); split; [exact H1|intros X; apply H2; right; exact X]].
Qed.
Definition art_key_in (work : list art_rel) (c w : Z) : bool := existsb (fun e => (fst (art_rel_key e) =? c) && (snd (art_rel_key e) =? w)) work.
Definition art_st_rcy (work : list art_rel) (st : Z -> Z -> art_cst) (c w : Z) : art_cst := if art_key_in work c w then CFree else st c w.
Lemma art_key_in_spec : ltac2:(TCodec.tc2 tcn__JbtInvRecycleD "K'6'Q;%211'E&@'>'2&Q5r3r2r1%43321(<%83721&QB';%12==(:%14??98&D&Q2%24D51=%83641%C2:1pT8E1pSFF1pT:H1").
Proof.
intros work c w. unfold art_key_in. rewrite existsb_exists. split.
- intros (e & He & E). apply andb_true_iff in E. destruct E as (E1 & E2). apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. apply in_map_iff. exists e. split; [|exact He].
destruct (art_rel_key e) as [a b]. cbn [fst snd] in *. subst. reflexivity.
- intros H. apply in_map_iff in H. destruct H as (e & E & He). exists e. split; [exact He|]. rewrite E. cbn [fst snd]. rewrite !Z.eqb_refl. reflexivity.
Qed.
