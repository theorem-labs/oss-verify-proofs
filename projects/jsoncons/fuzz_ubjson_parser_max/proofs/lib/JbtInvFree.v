(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim StoreOk HeapIface HeapIfaceA As0Tables ArtMem JbtLeaf JbtRzLog JbtPoison JbtAllocA JbtAllocG ArtRunsMem JbtInitCache JbtPopulate1 ArtRuns JbtCls JbtFp
JbtClsRep JbtClsGfa2 JbtClsRefill JbtCARSpec JbtAlloc3Pure JbtByteCell JbtCellEx JbtDepotA JbtDepot JbtAllocate3 ArtBridge JbtInv JbtInvMallocPure JbtInvMalloc JbtFsInvLaws JbtFxQ JbtFxBatch2 JbtFxBatch3 JbtFreeTop3
JbtInvFreePure.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import HeapIfaceAJx ShadowRLaws.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtInvFree () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceAJx.HAJ."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtCARSpec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtCls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtFp."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtFxBatch3."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtInvFree.Rep."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0B"; "1Some"; "1app"; "1bool"; "1cons"; "1false"; "1fst"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1prod"; "1snd"; "1true"; "2and"]; ["2eq"; "2ex"; "2not"; "2or"; "3le"; "4Z"; "0L"; "0LB"; "0LB0"; "0M"; "0M'"; "0M0"; "5apart"; "5cell"; "5wr"; "6lb_remove"]; ["7FS_BYTES"; "7S"; "7ar_fs"; "7byte_at"; "7in_shadow_of"; "8shadow_blkR"; "9art_ca_pre"; ":cl_au"; ":cl_mu"; ";art_agree"; ";art_gap"; ";art_out"; "<art_enq_fp"; "=art_batch"; "=art_batch_list"; "=art_rt_statics"]; ["=art_rt_thread"; "=bt_addr"; "=bt_items"; "=rn_HI"; "=rn_ar"; "=rn_blk"; "=rn_ctx"; "=rn_dtls"; "=rn_kbase"; "=rn_l2"; "=rn_parr"; "=rn_qs"; "=rn_ris"; "=rn_spb"; "=rn_t"; ">art_free_coarse"]; [">art_free_fpl"; ">art_free_where"; ">art_frep_W"; "?loaded_segments"; "0Sp"; "@In"; "@nth_error"; "Aadd"; "Ale"; "Alt"; "Amodulo"; "Amul"; "Aof_nat"; "Apow"; "Asub"; "0a"]; ["0b"; "0b0"; "0c0"; "0cl24"; "0cntB"; "0f"; "0i"; "0it"; "0j"; "0km"; "0l"; "0lb"; "0len"; "0lo"; "0n"; "0newb"]; ["0q16"; "0qr"; "0r"; "0rn"; "Bbv"; "Bbv_unsigned"; "0u"; "0v"; "0x"]]).
Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Ltac rok_open14 ROK :=
destruct ROK as (GEO & Esb & Kal & Kspb & Kend & Pal & Plo & Phi & Papp & Hkey & Hloff & Hloff' & Hloff'' & Htpd & Htsdd & Dl2 & Dblk
& Al2t & Al2c & Al2k & Al2s & Abt & Abc & Abk & Abs & Apt & Apc & Apk & Apl & Apb & Aft & Afc & Afk & Afl & Afb & Afp & Fhi & Fapp & Fimg & Flo
& Il2 & Iblk & Afkb & D0 & D1 & D2 & D3 & Adt & Adc & Adk & Adp & Adl & Adb & Adf & Atkb & Ackb & Al2kb & Apkb).
Section Rep.
Variable FSG : Type.
Variables (rn : art_run) (G : art_gs FSG) (LB : list (Z * Z)) (M M' : word -> option byte).
Variables (Sp u n q16 qr b1 km : Z) (kb : nat) (k : art_fk).
Let qtl := g_qt FSG G.
Let cl24 := g_cls FSG G 24.
Let newb := art_free_newb qtl.
Let wb := art_ca_cptr 24 cl24.
Let b := rn_spb rn + 24 * 2 ^ 32 + 16 * wb.
Let lastb := art_lastb qtl.
Let L := Z.of_nat (length qtl).
Let B := bt_addr lastb.
Let cntB := Z.of_nat (length (bt_items lastb)).
Let G' := art_gs_free G (rn_spb rn) k u n kb.
Definition art_free_fpl (a : Z) : Prop :=
art_free3_fp Sp (rn_t rn) u q16 qr (rn_l2 rn) (rn_blk rn) a \/ art_enq_fp newb (Sp - 2208) (rn_t rn) (rn_spb rn) (rn_ris rn) (rn_qs rn) km b L B cntB a.
Hypothesis REP : art_alloc_rep FSG rn G LB M.
Hypothesis Hin : In (u, n) LB.
Hypothesis Eu : u = 16 * q16.
Hypothesis Hn : 1 <= n < 2 ^ 28.
Hypothesis Hqr : n <= 8 * qr <= n + 7.
Hypothesis Hb1 : 0 <= b1 < 256.
Hypothesis Hty : b1 mod 4 = 1.
Hypothesis Cn : cellA M (u - 12) 4 n.
Hypothesis KIND : match k with
| FKP c w => 1 <= c <= 30 /\ art_cptr_ok (AsanTab.class_size c) (cl_au (g_cls FSG G c)) w /\ g_st FSG G c w = CAlloc u n
| FKS i => exists s, nth_error (g_sec FSG G) i = Some s /\ sc_quar s = false /\ sc_u s = u /\ sc_n s = n
end.
Hypothesis HS : rn_HI rn + 4096 <= Sp - 4096.
Hypothesis HS47 : Sp < 2 ^ 47.
Hypothesis Emu : cl_mu cl24 = 262144 * km.
Hypothesis Edep : g_depot FSG G = Datatypes.S kb.
Hypothesis OUT : art_free3_out M M' Sp (rn_t rn) u q16 qr (rn_l2 rn) (rn_blk rn) b1 n (rn_spb rn) (rn_ris rn) (rn_qs rn) km L B cntB
(art_bt_bytes lastb) (art_batches_bytes qtl) kb (g_inited FSG G) cl24.
Hypothesis LIVE : forall p, In p (art_live (g_log FSG G)) ->
0 < fst p /\ 0 < snd p /\ fst p + snd p <= rn_HI rn /\ (fst p + snd p <= 0x7fff7000 \/ 0x10007fff8000 <= fst p)
/\ (forall o, In o (art_objs rn) -> apart (fst p) (snd p) (fst o) (snd o)).
Hypothesis LIVE2 : forall p p', In p (art_live (g_log FSG G)) -> In p' (art_live (g_log FSG G)) -> fst p <> fst p' -> apart (fst p) (snd p) (fst p') (snd p').
Hypothesis LIVE3 : forall p, In p (art_live (g_log FSG G)) -> fst p mod 4096 = 0 /\ snd p mod 4096 = 0.
Hypothesis OKpre : newb = true -> art_cls_ok 24 (art_ca_pre 24 cl24).
Hypothesis Hother : forall b0, In b0 (lb_remove u LB) -> In b0 LB /\ fst b0 <> u.
#[using="OUT"] Lemma art_frep_out :
mem_grows M M'
/\ (forall x : word, ~ art_free3_fp Sp (rn_t rn) u q16 qr (rn_l2 rn) (rn_blk rn) (U x) ->
~ art_enq_fp newb (Sp - 2208) (rn_t rn) (rn_spb rn) (rn_ris rn) (rn_qs rn) km b L B cntB (U x) -> M' x = M x)
/\ DInvD (rn_l2 rn) (rn_blk rn) kb M'
/\ cellA M' (u - 16) 4 (3 + 256 * b1)
/\ cellA M' 0x1cc4c8 4 1 /\ (forall j, 0 <= j < 2 ^ 15 -> cellA M' (0x13dc48 + 8 * j) 8 0)
/\ art_pc_hdr (rn_t rn + 208) (if newb then true else g_inited FSG G) M' /\ art_cls_rep (rn_t rn + 208) (rn_spb rn) (rn_ris rn) 24 (art_enq_cls newb cl24) M'
/\ art_cls_ok 24 (art_enq_cls newb cl24)
/\ (newb = true ->
art_cptr_ok 8192 (cl_au (art_ca_pre 24 cl24)) wb
/\ (cl_cache cl24 = [] -> art_cls_needs_populate 24 cl24 = true ->
forall j, 0 <= j < 32768 -> cellA M' (2147450880 + 8192 * rn_qs rn + 24 * 2 ^ 29 + 32768 * km + j) 1 250)
/\ cellA M' b 8 0 /\ cellA M' (b + 8) 8 (n + 8192) /\ cellA M' (b + 16) 8 1 /\ cellA M' (b + 24) 8 (u - 16)
/\ cellA M' (rn_t rn + 80) 8 (L + 1) /\ cellA M' (rn_t rn + 80 + 16) 8 b /\ (L = 0 -> cellA M' (rn_t rn + 80 + 8) 8 b) /\ (L <> 0 -> cellA M' B 8 b))
/\ (newb = false -> cellA M' (B + 16) 8 (cntB + 1) /\ cellA M' (B + 8) 8 (art_bt_bytes lastb + n) /\ cellA M' (B + 24 + 8 * cntB) 8 (u - 16))
/\ cellA M' (rn_t rn + 80 + 24) 8 (art_batches_bytes qtl + n + (if newb then 8192 else 0)).
Proof. exact OUT. Qed.
Definition art_free_where : Prop :=
match k with
| FKP c w => rn_spb rn + c * 2 ^ 32 + 16 * w + 16 <= u /\ u + n <= rn_spb rn + c * 2 ^ 32 + 16 * w + AsanTab.class_size c
| FKS i => exists p, In p (art_live (g_log FSG G)) /\ fst p + 4096 <= u - 16 /\ u + n <= fst p + snd p
end.
#[using="LB M kb REP KIND"] Lemma art_frep_where : ltac2:(TCodec.tc2 tcn__JbtInvFree "1&R1").
Proof.
destruct REP as (_ & _ & _ & _ & CH & SECR & _). unfold art_free_where. destruct k as [c w|i].
- destruct KIND as (Hc & V & St). specialize (CH c Hc). cbv zeta in CH. destruct CH as (_ & _ & _ & III). specialize (III w V). rewrite St in III.
destruct III as (_ & L1 & L2 & _). split; [exact L1|exact L2].
- destruct KIND as (s & Hs & Hq & Esu & Esn). destruct SECR as (_ & _ & _ & _ & _ & _ & _ & _ & BLK & _).
destruct (BLK i s Hs) as (_ & Hlive & _ & _ & _ & _ & L1 & L2 & _). exists (sc_map s, sc_msize s). cbn [fst snd]. rewrite <- Esu, <- Esn.
split; [exact Hlive|]. split; [exact L1|exact L2].
Qed.
#[using="LB M M' Sp u n q16 qr b1 kb REP Hb1 Emu Edep OUT OKpre"] Lemma art_frep_num : ltac2:(TCodec.tc2 tcn__JbtInvFree "QJ'?&R8zvRI%3221&R;+XPP0%2214+S`PPPP0%8221'@'3vRO(>%43321&R7&QMvS3%211+H&R=+2+Q0%3221%C251%:271vR@%J221+XP0%>231%?25F%N221%Q0251p0C1&B'EvF%K321Q3%411v0%Q72?1%J22=%Q921<vRD%Q;2Q:1+oM%Q=231%Q?231%Q@261%QA291p0<1(5%Q:3Q9Q81p01?%QF241%QG2F1%QH2Q?1%QI2QE1").
Proof.
pose proof REP as (_ & _ & _ & (_ & PRIM & _) & _ & _ & QR & _). destruct (PRIM 24 ltac:(lia)) as (_ & OK & _). fold cl24 in OK.
pose proof OK as (_ & (Hau0 & Haumu) & _ & _ & _ & Hmu3 & _).
split; [lia|]. split; [lia|]. split; [|split].
- intros E. destruct art_frep_out as (_ & _ & _ & _ & _ & _ & _ & _ & OK' & NEW & _). destruct (NEW E) as ((Hw0 & Hw1 & _) & _).
rewrite E in OK'. unfold art_enq_cls, art_cls_ok in OK'. cbn [art_cls_pop cl_cache cl_free cl_au cl_mu cl_mfa] in OK'. destruct OK' as (_ & (_ & Haumu') & _ & _ & _ & Hmu3' & _).
unfold b. lia.
- intros NL. assert (NE : qtl <> []) by (intros E; apply NL; unfold L; rewrite E; reflexivity).
assert (InB : In lastb (g_qt FSG G ++ g_qg FSG G)). { apply in_or_app. left. unfold lastb, art_lastb. apply JbtFxQ.art_last_in. exact NE. }
destruct QR as ((f & l & _ & _ & _ & _ & BL) & _ & _ & _ & _ & _ & _ & _ & _ & BCH). destruct (BCH lastb InB) as (w0 & Ew0 & (V0 & V1 & _) & _).
rewrite art_class_size_24 in V1. fold cl24 in V1. unfold B. rewrite Ew0. split; [lia|]. split; [lia|]. unfold cntB. split; [lia|].
fold qtl in BL. clear - BL NE. revert f BL. induction qtl as [|x r IH]; intros f BL; [contradiction|]. cbn [art_batch_list] in BL. destruct BL as (_ & Hl & _ & _ & _ & _ & R).
unfold lastb, art_lastb in *. destruct r as [|y r']; [cbn [last]; lia|]. change (last (x :: y :: r') (BATCH 0 [])) with (last (y :: r') (BATCH 0 [])). eapply IH; [discriminate|exact R].
- intros E. destruct (art_free_newb_false qtl E) as (NE & _). unfold L. destruct qtl; [contradiction|]. cbn [length]. lia.
Qed.
#[using="LB M M' u n q16 qr b1 kb REP Hb1 Emu Edep OUT OKpre"] Lemma art_frep_zone : ltac2:(TCodec.tc2 tcn__JbtInvFree "R<'E&Q<vRO&R>vR4+RU0%3221&QNvS3%211&QM%113&QL%115&QK%117vRIvR@vFv0vRDr1%E<D@=;97654321'C'?&R8+g0%H2E1r2%4221&R9%123I%8231%82H5&R7+TP0%22K1%7291%>251%>2J;%62K5%;2=1%B231&R;+H&R=+2+Q0%3221%6251%@2Q71%J21G+I%:215%D2Q;1%I2K1%Q0251+QoooPP0+XP0%@21Q<%J231+M%A2@1%D2C1%N241%Q821Q5%G2>4%Q1271%Q62Q81%Q=241%Q?2>1%Q@2M1%QA2Q21%QB2Q91p0QD1pVBR;1").
Proof.
intros x F. destruct art_frep_num as (Hkm & Hkm' & Hbz & HBz & HnL).
apply (art_enq_fp_zone newb (Sp - 2208) (rn_t rn) (rn_spb rn) (rn_ris rn) (rn_qs rn) km b L B cntB x Hkm Hkm' eq_refl); [ | exact Hbz | | exact HnL | exact F ].
- intros NL. exact (proj2 (proj2 (HBz NL))).
- intros NL. destruct (HBz NL) as (X1 & X2 & _). split; assumption.
Qed.
#[using="n b1 kb OUT"] Lemma art_frep_lin : ltac2:(TCodec.tc2 tcn__JbtInvFree "G'S4yR0%211&B&R0&S5r1%2261%411%611'@';y8%=11%311vJr2%211vI%113%:3631p0<1pVBD1").
Proof. intros x N. destruct art_frep_out as (_ & FR & _). apply FR; intros F; apply N; [left|right]; exact F. Qed.
#[using="rn LB M b1 kb qtl cl24 wb b lastb L B cntB REP Hb1 Edep LIVE2"] Lemma art_frep_sec_p : forall s p i0, nth_error (g_sec FSG G) i0 = Some s -> In p (art_live (g_log FSG G)) -> fst p + 4096 <= sc_u s - 16 -> sc_u s + sc_n s <= fst p + snd p ->
1 <= sc_n s -> fst p = sc_map s.
Proof.
intros s p i0 Hs Hp L1 L2 Hn1. destruct REP as (_ & _ & _ & _ & _ & SECR & _). destruct SECR as (_ & _ & _ & _ & _ & _ & _ & _ & BLK & _).
destruct (BLK i0 s Hs) as (_ & Hlive & _ & _ & _ & _ & M1 & M2 & _).
destruct (Z.eq_dec (fst p) (sc_map s)) as [E|NE]; [exact E|exfalso].
pose proof (LIVE2 p (sc_map s, sc_msize s) Hp Hlive NE) as AP. cbn [fst snd] in AP. unfold apart in AP. lia.
Qed.
Section SE.
Local Abbreviation SEC_T_art_enq_fp_thread := (ltac2:(TCodec.tc2 tcn__JbtInvFree "Q<'E&Q<vRO&R>vR4+RU0%3221&QNvS3%211&QM%113&QL%115&QK%117vRIvR@vFv0vRDr1%E<D@=;97654321'?&R8r2%22A1&R9&R7+TP0%22E1%4261%9261+R@%62I1r3%<221+Rj8%:2M1%<241%A241p091p0D1pVBQ;1")) (only parsing).
Variable x : ltac:(sec_ty2 constr:(SEC_T_art_enq_fp_thread) 0%nat 0%nat).
#[using="LB M M' u n q16 qr b1 kb REP Hb1 HS Emu Edep OUT OKpre x"] Lemma art_enq_fp_thread : ltac:(sec_stmt2 constr:(SEC_T_art_enq_fp_thread) 1%nat 0%nat).
Proof.
intros F Hx.
destruct art_frep_num as (Hkm & Hkm' & Hbz & HBz & HnL).
pose proof REP as (ROK & _). rok_open14 ROK. geo_open GEO. unfold apart in G11.
unfold art_enq_fp in F. destruct newb eqn:E.
- specialize (Hbz eq_refl). unfold art_enq_new_fp, art_refill_fp in F.
destruct F as [F|[[F|[F|[F|[F|[F|[F|[F|[F|[F|F]]]]]]]]]|[F|[F|[F|F]]]]]; try lia;
first [ destruct F as (c' & Hc' & F); (clear - Edep F FSG G Hc' b c' cl24 kb rn wb x; lia) | destruct F as [NL F]; destruct (HBz NL) as (X1 & X2 & _); lia ].
- destruct (HBz (HnL eq_refl)) as (X1 & X2 & X3). destruct F as [F|[F|[F|F]]]; lia.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_enq_fp_ris := (ltac2:(TCodec.tc2 tcn__JbtInvFree "Q>'E&Q<vRO&R>vR4+RU0%3221&QNvS3%211&QM%113&QL%115&QK%117vRIvR@vFv0vRDr1%E<D@=;97654321'?&R8r2%22=1&R9&R7+TP0%22A1%4261%9261&R;+T0+H%3221%92H1r3%?221%<236%>231%C231p0;1p0F1pVBQ=1")) (only parsing).
Variable x : ltac:(sec_ty2 constr:(SEC_T_art_enq_fp_ris) 0%nat 0%nat).
#[using="LB M M' u n q16 qr b1 kb REP Hb1 HS Emu Edep OUT OKpre x"] Lemma art_enq_fp_ris : ltac:(sec_stmt2 constr:(SEC_T_art_enq_fp_ris) 1%nat 0%nat).
Proof.
intros F Hx.
destruct art_frep_num as (Hkm & Hkm' & Hbz & HBz & HnL).
pose proof REP as (ROK & _). rok_open14 ROK. geo_open GEO. unfold apart in G11.
unfold art_enq_fp in F. destruct newb eqn:E.
- specialize (Hbz eq_refl). unfold art_enq_new_fp, art_refill_fp in F.
destruct F as [F|[[F|[F|[F|[F|[F|[F|[F|[F|[F|F]]]]]]]]]|[F|[F|[F|F]]]]]; try (clear - F Hx HS G1 G2 G4 G6 G8 G11 Espb Eris Hbz Hkm Hkm'; lia);
first [ destruct F as (c' & Hc' & F); clear - F Hx Hc' G8 G11 Eris; lia | destruct F as [NL F]; destruct (HBz NL) as (X1 & X2 & _); clear - F Hx X1 X2 Eris; lia ].
- destruct (HBz (HnL eq_refl)) as (X1 & X2 & X3). destruct F as [F|[F|[F|F]]]; clear - F Hx HS G1 G6 G8 G11 X1 X2 X3 Eris; lia.
Qed.
End SE.
Definition art_free_coarse (x : Z) : Prop :=
rn_HI rn <= x \/ (rn_t rn + 80 <= x < rn_t rn + 2888) \/ (rn_spb rn + 24 * 2 ^ 32 <= x < rn_spb rn + 25 * 2 ^ 32) \/ (rn_ris rn <= x < rn_ris rn + 4096)
\/ (2147450880 + 8192 * rn_qs rn + 24 * 2 ^ 29 <= x < 2147450880 + 8192 * rn_qs rn + 25 * 2 ^ 29)
\/ dprivD (rn_l2 rn) (rn_blk rn) x \/ (0x13dc40 <= x < 0x13dc40 + 0x81030) \/ (0x1cc4c8 <= x < 0x1cc4c8 + 4)
\/ (u - 16 <= x < u - 12) \/ (u <= x < u + 8) \/ (2147450880 + 2 * q16 <= x < 2147450880 + 2 * q16 + qr).
Section SE.
Local Abbreviation SEC_T_art_frep_coarse := (ltac2:(TCodec.tc2 tcn__JbtInvFree "9'E&R0r1%211&QOr2%211p041pVB81")) (only parsing).
Variable x : ltac:(sec_ty2 constr:(SEC_T_art_frep_coarse) 0%nat 0%nat).
#[using="LB M M' n b1 kb REP Hn Hqr Hb1 HS Emu Edep OUT OKpre x"] Lemma art_frep_coarse : ltac:(sec_stmt2 constr:(SEC_T_art_frep_coarse) 1%nat 0%nat).
Proof.
intros [F|F].
- unfold art_free3_fp in F. unfold art_free_coarse. destruct F as [F|[F|[F|[F|[F|[F|[F|F]]]]]]]; try tauto; [left; lia|right; left; lia].
- pose proof (art_frep_zone x F) as Z. unfold art_free_coarse. destruct Z as [Z|[Z|[Z|[Z|Z]]]]; try tauto; [left; lia|]. right; left. exact (art_enq_fp_thread x F Z).
Qed.
End SE.
Definition art_frep_W : list (Z * Z) :=
[ (rn_HI rn, 2 ^ 64 - rn_HI rn); (rn_t rn + 80, 2808); (rn_spb rn + 24 * 2 ^ 32, 2 ^ 32); (rn_ris rn, 4096); (2147450880 + 8192 * rn_qs rn + 24 * 2 ^ 29, 2 ^ 29);
(0x20e908, 0x65e928 - 0x20e908); (rn_l2 rn, 2 ^ 20); (rn_blk rn, 2 ^ 23); (0x13dc40, 0x81030); (0x1cc4c8, 4);
(u - 16, 4); (u, 8); (2147450880 + 2 * q16, qr) ].
#[using="FSG G LB Sp n b1 km kb qtl cl24 newb wb b lastb L B cntB REP Hn Hqr Hb1 HS Emu Edep OUT OKpre"] Lemma art_frep_agree : ltac2:(TCodec.tc2 tcn__JbtInvFree "5&Q9&R2vIvJ%43321").
Proof.
intros x Hx. apply art_frep_lin. intros F. apply art_frep_coarse in F. unfold art_frep_W in Hx. cbn [art_out fst snd] in Hx.
unfold art_free_coarse, dprivD in F. pose proof (u64_range x). lia.
Qed.
#[using="FSG G LB M n q16 b1 kb k qtl cl24 wb b lastb L B cntB REP Eu Hn Hqr Hb1 KIND Edep LIVE LIVE2 LIVE3"] Lemma art_frep_u_far : ltac2:(TCodec.tc2 tcn__JbtInvFree "RF'?&R8+Vb\P0&R>vS6+@%3221%6251&R7&R;+8vS1%3221%5291&QCvS3%211%@241%:2>=%B213'C+QoonlP0%E291+`PQoooPP0%G21B%5231&L%C2F?&QN%11>+TP0%54I421&QF%11B%84L714&QI%11E&R=+2+D%3221%?4Q3>51&QE%11L+G%8271%D4Q8C31&QJ%11Q1%G4Q;F14&Q2&QD%11Q5%311&Q0%M4QAL21&QG%11Q:%Q04QDO1L+Q0&QL%11Q>%Q44QH31Q0&QM%11QA+H%M2L7%QJ221%QL241+S`PPPP0%QN221+M%Q32Q21%Q?4R3>31%R:2<1%R;2A1%R<2E1%R=2L1%R>2Q01%R?2Q61%R@2Q>1%RA2QB1%RB2QI1%RC2R01%RD2R31%RE2R>1").
Proof.
pose proof REP as (ROK & _). rok_open14 ROK. geo_open GEO. pose proof art_frep_where as WH. unfold art_free_where in WH.
destruct k as [c w|i].
- destruct KIND as (Hc & (V0 & V1 & _) & _). destruct WH as (L1 & L2).
pose proof REP as (_ & _ & _ & (_ & PRIM & _) & _). destruct (PRIM c Hc) as (_ & OK & _). destruct OK as (_ & (Hau0 & Haumu) & _ & _ & (ka & Eka) & Hmu3 & _).
pose proof (art_class_size_facts c Hc) as (Hsz & Hsz16).
assert (Hend : u + 8 * qr <= rn_spb rn + c * 2 ^ 32 + 16 * w + AsanTab.class_size c).
{ rewrite <- (Z.div_exact _ 16) in Hsz16 by lia. clear - L2 Hsz16 Espb Eu Hn Hqr. lia. }
assert (Hend16 : u + 16 <= rn_spb rn + c * 2 ^ 32 + 16 * w + AsanTab.class_size c).
{ rewrite <- (Z.div_exact _ 16) in Hsz16 by lia. clear - L2 Hsz16 Espb Eu Hn. lia. }
assert (LO : rn_spb rn + 2 ^ 32 <= u - 16) by (clear - L1 Hc V0; lia).
assert (HIu : u + 8 * qr <= rn_spb rn + c * 2 ^ 32 + 3758096384) by (clear - Hend V1 Haumu Hmu3; lia).
assert (HIu' : u + 8 * qr <= rn_spb rn + 31 * 2 ^ 32) by (clear - HIu Hc; lia).
assert (Hq0 : 1 <= qr) by (clear - Hn Hqr; lia).
split; [clear - LO G4; lia|]. split; [clear - HIu' G6 Eris; lia|]. split; [clear - HIu' G6 Eris Hq0; lia|]. split; [right; clear - LO G4; lia|].
split; [unfold apart in G11 |- *; clear - G11 LO HIu'; lia|]. split; [unfold apart in G17 |- *; clear - G17 LO HIu'; lia|].
split; [unfold apart in Al2k |- *; clear - Al2k LO HIu'; lia|]. split; [unfold apart in Abk |- *; clear - Abk LO HIu'; lia|].
split; [unfold apart in Apk |- *; clear - Apk LO HIu'; lia|]. split; [unfold apart in Afk |- *; clear - Afk LO HIu'; lia|].
split; [unfold apart in Adk |- *; clear - Adk LO HIu' Kspb; lia|].
split; [unfold apart; clear - HIu' Eris Hq0; lia|].
unfold apart. destruct (Z.eq_dec c 24) as [->|Nc]; [clear - Hend16 V1 Haumu Hmu3; lia|clear - LO L1 HIu Hc Nc V0 Hq0; lia].
- destruct WH as (p & Hp & L1 & L2). destruct (LIVE p Hp) as (P0 & P1 & P2 & P3 & PO). destruct (LIVE3 p Hp) as (A1 & A2).
destruct KIND as (s & Hs & _ & Esu & Esn).
assert (Hend : u + 8 * qr <= fst p + snd p). { rewrite <- (Z.div_exact _ 4096) in A1 by lia. rewrite <- (Z.div_exact _ 4096) in A2 by lia. clear - L2 A1 A2 Eu Hn Hqr. lia. }
assert (Hq0 : 1 <= qr) by (clear - Hn Hqr; lia).
pose proof (PO _ (or_introl eq_refl)) as At. pose proof (PO _ (or_intror (or_introl eq_refl))) as Ac. pose proof (PO _ (or_intror (or_intror (or_introl eq_refl)))) as Ak.
pose proof (PO _ (or_intror (or_intror (or_intror (or_introl eq_refl))))) as Ap.
pose proof (PO _ (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))) as Al.
pose proof (PO _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))) as Ab.
pose proof (PO _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))))) as Af.
pose proof (PO _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))))))))) as Ad.
cbn [fst snd] in At, Ac, Ak, Ap, Al, Ab, Af, Ad.
assert (Pimg : 0x693000 <= fst p). { assert (X : 0x693000 <= sc_map s) by (destruct REP as (_ & _ & _ & _ & _ & SECR & _); destruct SECR as (_ & _ & _ & _ & _ & _ & _ & _ & BLK & _); destruct (BLK i s Hs) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & X); exact X). assert (E : fst p = sc_map s) by (apply (art_frep_sec_p s p i Hs Hp); [rewrite Esu; exact L1|rewrite Esu, Esn; exact L2|rewrite Esn; clear - Hn; lia]). rewrite E. exact X. }
assert (Hend16 : u + 16 <= fst p + snd p). { rewrite <- (Z.div_exact _ 4096) in A1 by lia. rewrite <- (Z.div_exact _ 4096) in A2 by lia. clear - L2 A1 A2 Eu Hn. lia. }
split; [clear - Pimg L1; lia|]. split; [clear - Hend P2; lia|]. split; [clear - Hend16 P2; lia|]. split; [clear - P3 Hend L1; lia|].
split; [unfold apart in At |- *; clear - At L1 Hend; lia|]. split; [unfold apart in Ac |- *; clear - Ac L1 Hend; lia|].
split; [unfold apart in Al |- *; clear - Al L1 Hend; lia|]. split; [unfold apart in Ab |- *; clear - Ab L1 Hend; lia|].
split; [unfold apart in Ap |- *; clear - Ap L1 Hend; lia|]. split; [unfold apart in Af |- *; clear - Af L1 Hend; lia|].
split; [unfold apart in Ad |- *; clear - Ad L1 Hend; lia|].
split; [unfold apart in Ak |- *; clear - Ak L1 Hend Hq0 Eris Kspb Kend; lia|].
unfold apart in Ak |- *. clear - Ak L1 Hend Hq0 Kspb Kend. lia.
Qed.
#[using="FSG rn G LB M u n b1 kb k qtl cl24 wb b lastb L B cntB REP Eu Hn Hqr Hb1 KIND Edep LIVE LIVE2 LIVE3"] Lemma art_frep_ush : ltac2:(TCodec.tc2 tcn__JbtInvFree "?'?&R8+QoooPP0&R7&R;+2vS0%3221%5261%8271vS1%8231+`PQoooPP0%<221%>251").
Proof.
destruct art_frep_u_far as (U1 & U2 & _). pose proof REP as (ROK & _). rok_open14 ROK. geo_open GEO. clear - U1 U2 G2 Eu Hqr Hn. lia.
Qed.
Section SE.
Local Abbreviation SEC_T_art_fgap_img := (ltac2:(TCodec.tc2 tcn__JbtInvFree "Q0'E'C'?&R8+RPP0r2%3221&R7r1%2241+QWgR0%8221%:261+QgkS@%;219+QiaV8%=271%?231+QiaV<%@21>+RQjX8%B2<1%D231%F261%G2<1&Q:&R2r3%3321Gp051pUJN1pU0O1")) (only parsing).
Variable a : ltac:(sec_ty2 constr:(SEC_T_art_fgap_img) 0%nat 0%nat).
Variable len : ltac:(sec_ty2 constr:(SEC_T_art_fgap_img) 1%nat 0%nat).
#[using="FSG G LB M n b1 kb k qtl cl24 wb b lastb L B cntB REP Eu Hn Hqr Hb1 KIND Edep LIVE LIVE2 LIVE3 a len"] Lemma art_fgap_img : ltac:(sec_stmt2 constr:(SEC_T_art_fgap_img) 2%nat 0%nat).
Proof.
intros Ha.
destruct art_frep_u_far as (U1 & _). destruct art_frep_ush as (S1 & S2).
pose proof REP as (ROK & _). rok_open14 ROK. geo_open GEO.
unfold art_frep_W. cbn [art_gap fst snd]. unfold apart. clear - Ha U1 S1 G1 G4 Espb Eris G9 Il2 Iblk. repeat split; try exact I; lia.
Qed.
End SE.
#[using="FSG G LB M n b1 kb k qtl cl24 wb b lastb L B cntB REP Eu Hn Hqr Hb1 KIND Edep LIVE LIVE2 LIVE3"] Lemma art_fgap_tls : ltac2:(TCodec.tc2 tcn__JbtInvFree "B'E&R8+V[jY8r2%3221&R7r3%2214+Vb\P0%8221&Q:&R2r4%33217p051p0;1pUJ@1pU0A1").
Proof.
intros a len Ha Hk. destruct art_frep_u_far as (U1 & _). destruct art_frep_ush as (S1 & S2).
pose proof REP as (ROK & _). rok_open14 ROK. geo_open GEO.
unfold art_frep_W. cbn [art_gap fst snd]. unfold apart. clear - Ha Hk U1 S1 G1 G4 Espb Eris G9 Il2 Iblk. repeat split; try exact I; lia.
Qed.
Section SE.
Local Abbreviation SEC_T_art_fgap_thread := (ltac2:(TCodec.tc2 tcn__JbtInvFree "Q0'E&R8&QNvS3%211r2%5221&R7r3%2214+TP0%4271%;231'Cr4%8217+R@%:2=1%A231+Rj8%=2@1%D217%9241&Q:&R2r5%3321<p051p0@1p0G1pUJN1pU0O1")) (only parsing).
Variable a : ltac:(sec_ty2 constr:(SEC_T_art_fgap_thread) 0%nat 0%nat).
Variable len : ltac:(sec_ty2 constr:(SEC_T_art_fgap_thread) 1%nat 0%nat).
#[using="FSG G LB M n b1 kb k qtl cl24 wb b lastb L B cntB REP Eu Hn Hqr Hb1 KIND Edep LIVE LIVE2 LIVE3 a len"] Lemma art_fgap_thread : ltac:(sec_stmt2 constr:(SEC_T_art_fgap_thread) 2%nat 0%nat).
Proof.
intros Ha Hk Hlo.
destruct art_frep_u_far as (_ & _ & _ & _ & Ut & _). destruct art_frep_ush as (S1 & S2).
pose proof REP as (ROK & _). rok_open14 ROK. geo_open GEO.
unfold art_frep_W. cbn [art_gap fst snd]. unfold apart in *. clear - Ha Hk Hlo Ut S1 S2 G1 G2 G4 G6 Espb Eris G8 G9 G10 G11 Al2t Abt Hn Hqr. repeat split; try exact I; lia.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_fgap_ctx := (ltac2:(TCodec.tc2 tcn__JbtInvFree "E'E&R8&QFvS3%211r2%5221&R7r3%2214+TP0%4271%;231&Q:&R2r4%33218p051p0<1pUJC1pU0D1")) (only parsing).
Variable a : ltac:(sec_ty2 constr:(SEC_T_art_fgap_ctx) 0%nat 0%nat).
Variable len : ltac:(sec_ty2 constr:(SEC_T_art_fgap_ctx) 1%nat 0%nat).
#[using="FSG G LB M n b1 kb k qtl cl24 wb b lastb L B cntB REP Eu Hn Hqr Hb1 KIND Edep LIVE LIVE2 LIVE3 a len"] Lemma art_fgap_ctx : ltac:(sec_stmt2 constr:(SEC_T_art_fgap_ctx) 2%nat 0%nat).
Proof.
intros Ha Hk.
destruct art_frep_u_far as (_ & _ & _ & _ & _ & Uc & _). destruct art_frep_ush as (S1 & S2).
pose proof REP as (ROK & _). rok_open14 ROK. geo_open GEO.
unfold art_frep_W. cbn [art_gap fst snd]. unfold apart in *. clear - Ha Hk Uc S1 S2 G1 G2 G4 G6 Espb Eris G14 G15 G16 G17 G18 Al2c Abc Hn Hqr. repeat split; try exact I; lia.
Qed.
End SE.
#[using="FSG rn G LB Sp u n q16 qr b1 km kb k qtl cl24 newb wb b lastb L B cntB REP Eu Hn Hqr Hb1 KIND HS Emu Edep OUT LIVE LIVE2 LIVE3 OKpre"] Lemma art_frep_cell_img : ltac2:(TCodec.tc2 tcn__JbtInvFree "Q9'E'9'C'?&R8+RPP0r3%3221&R7&R<r2%211%4261+QWgR0%:221%<281+QgkS@%=21;+QiaV8%?271%A231+QiaV<%B21@+RQjX8%D2<1%F231%H261%I2<1&M&R3vIr4%45321JFvJr5%756214Mp041p0:1pV@Q61pUBQ61pU0Q81").
Proof. intros a j v Ha C. apply (art_cell_tr art_frep_W M M' a j v art_frep_agree (art_fgap_img a _ Ha)); [lia|lia|exact C]. Qed.
#[using="FSG G LB M Sp u n q16 qr b1 km kb k qtl cl24 newb wb b lastb L B cntB REP Eu Hn Hqr Hb1 KIND HS Emu Edep OUT LIVE LIVE2 LIVE3 OKpre"] Lemma art_frep_statics : ltac2:(TCodec.tc2 tcn__JbtInvFree "4&Q?vS3vJ%3221").
Proof.
pose proof REP as (ROK & ST & _). rok_open14 ROK. pose proof GEO as GEO'. geo_open GEO'.
destruct ST as (PC & LY & T & RO & RZ & DR & TG & CS).
pose proof T as (_ & _ & _ & _ & _ & TR).
unfold art_rt_statics.
split; [apply (art_prim_consts_tr _ M M' _ _ art_frep_agree); [apply art_fgap_img; lia|apply art_fgap_img; lia|apply art_fgap_img; lia|exact PC]|].
split; [apply (art_layout_tr _ M M' art_frep_agree); [apply art_fgap_img; lia|apply art_fgap_img; lia|exact LY]|].
split. { apply (art_tsd_tr _ M M' _ _ _ _ _ art_frep_agree); [apply art_fgap_img; lia|apply art_fgap_tls; lia|apply art_fgap_tls; lia|apply art_fgap_ctx; lia|exact T]. }
split. { unfold art_alloc_rodata in *. destruct RO as (a1 & a2 & a3). repeat split; apply art_frep_cell_img; first [assumption|cbn; lia]. }
split. { unfold art_rz_rodata in *. destruct RZ as (a1 & a2 & a3). repeat split; apply art_frep_cell_img; first [assumption|cbn; lia]. }
split. { destruct DR as (a1 & a2 & a3). unfold DRoD. repeat split; apply art_frep_cell_img; first [assumption|cbn; lia]. }
split. { destruct TG as (GN & T1 & T2). split; [|split].
- intros a Ha. assert (EU : U (Z_to_bv 64 a) = a) by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64); apply Z.mod_small; lia).
rewrite (art_frep_agree (Z_to_bv 64 a)); [exact (GN a Ha)|]. rewrite EU. apply (art_gap_out _ a 1); [apply art_fgap_img; lia|lia].
- apply (art_cell_tr art_frep_W M M' 0x670ab8 8%nat _ art_frep_agree (art_fgap_tls 0x670ab8 8 ltac:(lia) ltac:(lia))); [lia|cbn; lia|exact T1].
- apply (art_cell_tr art_frep_W M M' 0x670ae8 8%nat _ art_frep_agree (art_fgap_tls 0x670ae8 8 ltac:(lia) ltac:(lia))); [lia|cbn; lia|exact T2]. }
decompose [and] CS. repeat split; apply art_frep_cell_img; first [assumption|cbn; lia].
Qed.
#[using="FSG G LB M Sp u n q16 qr b1 km kb k qtl cl24 newb wb b lastb L B cntB REP Eu Hn Hqr Hb1 KIND HS Emu Edep OUT LIVE LIVE2 LIVE3 OKpre"] Lemma art_frep_thread : ltac2:(TCodec.tc2 tcn__JbtInvFree "4&Q@vS3vJ%3221").
Proof.
pose proof REP as (ROK & _ & TH & _). rok_open14 ROK. pose proof GEO as GEO'. geo_open GEO'.
destruct TH as (Wt & C1 & C2 & C3 & C4 & C5 & C6 & C7). destruct art_frep_out as (GR & _).
assert (TT : forall a (j : nat) v, rn_t rn <= a -> a + Z.of_nat j <= rn_t rn + 4096 -> (a + Z.of_nat j <= rn_t rn + 80 \/ rn_t rn + 2888 <= a) -> cellA M a j v -> cellA M' a j v).
{ intros a j v Ha Hk Hlo C. apply (art_cell_tr art_frep_W M M' a j v art_frep_agree (art_fgap_thread a _ Ha Hk Hlo)); [lia|lia|exact C]. }
unfold art_rt_thread. split; [eapply wr_grows; [exact GR|exact Wt]|].
split; [apply TT; [lia|cbn; lia|cbn; lia|exact C1]|].
split. { apply (art_cell_tr art_frep_W M M' (rn_ctx rn + 8) 4%nat 0 art_frep_agree (art_fgap_ctx (rn_ctx rn + 8) 4 ltac:(lia) ltac:(lia))); [lia|cbn; lia|exact C2]. }
split; [apply TT; [lia|cbn; lia|cbn; lia|exact C3]|]. split; [apply TT; [lia|cbn; lia|cbn; lia|exact C4]|].
split; [apply TT; [lia|cbn; lia|cbn; lia|exact C5]|]. split; [apply TT; [lia|cbn; lia|cbn; lia|exact C6]|].
apply (art_cell_tr art_frep_W M M' (rn_tp rn + rn_loff rn) 4%nat 0 art_frep_agree (art_fgap_tls (rn_tp rn + rn_loff rn) 4 ltac:(lia) ltac:(lia))); [lia|cbn; lia|exact C7].
Qed.
#[using="M Sp q16 qr b1 km qtl cl24 newb wb b lastb L B cntB OUT"] Lemma art_frep_depot : art_rt_depot FSG rn G' M'.
Proof. unfold art_rt_depot, G'. cbn [art_gs_free g_depot]. destruct art_frep_out as (_ & _ & DI & _). exact DI. Qed.
#[using="M Sp q16 qr b1 km qtl cl24 newb wb b lastb L B cntB Edep OUT"] Lemma art_frep_ia : art_rt_ia FSG G' M'.
Proof.
destruct art_frep_out as (_ & _ & _ & _ & Cia & Ctab & _). unfold art_rt_ia, G'. cbn [art_gs_free g_ia g_qt g_qg].
split; [exact Cia|]. split; [|intros E; discriminate]. intros _ j Hj. replace (0x13dc40 + 8 + 8 * j) with (0x13dc48 + 8 * j) by lia. exact (Ctab j Hj).
Qed.
Section SE.
Local Abbreviation SEC_T_art_frep_out_cache := (ltac2:(TCodec.tc2 tcn__JbtInvFree "R0'E'S4yR0%211'?&R8+1r2%3221+O%5231%7231'C&B'@r3+H%33A21%511'3vRO(5%83321%;251&R7&QNvS3%211+V@%5221&R;+R@r4%3221%:251&S5%12Q2E%Q0231&R9+4%@261%3251%Q6251+@%D2:1%Q8219%F2<?%92;1%Q<231%Q5271';y8%QC11%311vJ%11GvI%11I%Q<3531p0:1p0Q51p0QB1pVBQK1pU6QO1")) (only parsing).
Variable c0 : ltac:(sec_ty2 constr:(SEC_T_art_frep_out_cache) 0%nat 0%nat).
Variable x : ltac:(sec_ty2 constr:(SEC_T_art_frep_out_cache) 1%nat 0%nat).
#[using="LB Sp u n q16 qr b1 km kb k cl24 wb b lastb L B cntB REP Eu Hn Hqr Hb1 KIND HS Emu Edep OUT LIVE LIVE2 LIVE3 OKpre c0 x"] Lemma art_frep_out_cache : ltac:(sec_stmt2 constr:(SEC_T_art_frep_out_cache) 2%nat 0%nat).
Proof.
intros Hc0 Hne Hx.
apply art_frep_lin. destruct art_frep_num as (Hkm & Hkm' & Hbz & HBz & HnL).
destruct art_frep_u_far as (U1 & U2 & _ & _ & Ut & _). destruct art_frep_ush as (S1 & S2).
pose proof REP as (ROK & _). rok_open14 ROK. geo_open GEO.
intros [F|F].
- unfold art_free3_fp, dprivD in F. unfold apart in Ut, G11, Al2t, Abt. clear - F Hx Hc0 HS G1 G8 G9 G10 Ut S1 S2 Al2t Abt Hn Hqr. lia.
- unfold art_enq_fp in F. destruct newb eqn:E.
+ destruct Hne as [Hne|Hne]; [|discriminate]. specialize (Hbz eq_refl). unfold art_enq_new_fp, art_refill_fp in F. unfold apart in G11.
destruct F as [F|[[F|[F|[F|[F|[F|[F|[F|[F|[F|F]]]]]]]]]|[F|[F|[F|F]]]]]; try (clear - F Hx Hc0 Hne HS G1 G2 G4 G6 G8 G10 G11 Espb Eris Hbz Hkm Hkm'; lia);
first [ destruct F as (c' & Hc' & F); clear - F Hx Hc0 Hc'; lia | destruct F as [NL F]; destruct (HBz NL) as (X1 & X2 & _); clear - F Hx Hc0 X1 X2 G11 G8; lia ].
+ destruct (HBz (HnL eq_refl)) as (X1 & X2 & X3). unfold apart in G11. destruct F as [F|[F|[F|F]]]; clear - F Hx Hc0 HS G1 G8 G11 X1 X2 X3; lia.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_frep_out_region := (ltac2:(TCodec.tc2 tcn__JbtInvFree "R0'E'S4yR0%211'?&R8+1r2%3221+N%5231%7231&B'@r3+H%33@21%511'C&R7&QMvS3%211&R;r4&R=+2+Q0%3221%6251%;281+S`PPPP0%=221&S5%12Q0D%N231&R9%B279%2241%Q3241&QL%11D+T0%D21C%I231%Q821;%K224%;2=1%Q<231%O2:1';y8%QC11%311vJ%11OvI%11Q1%Q=3531p0:1p0Q;1p0QB1pVBQK1pU6QO1")) (only parsing).
Variable c0 : ltac:(sec_ty2 constr:(SEC_T_art_frep_out_region) 0%nat 0%nat).
Variable x : ltac:(sec_ty2 constr:(SEC_T_art_frep_out_region) 1%nat 0%nat).
#[using="FSG G LB Sp u n q16 qr b1 km kb k qtl cl24 newb wb b lastb L B cntB REP Eu Hn Hqr Hb1 KIND HS Emu Edep OUT LIVE LIVE2 LIVE3 OKpre c0 x"] Lemma art_frep_out_region : ltac:(sec_stmt2 constr:(SEC_T_art_frep_out_region) 2%nat 0%nat).
Proof.
intros Hc0 Hne Hx.
apply art_frep_lin. destruct art_frep_num as (Hkm & Hkm' & Hbz & HBz & HnL).
destruct art_frep_u_far as (U1 & U2 & _ & _ & Ut & _ & _ & _ & _ & _ & _ & Uris & _). destruct art_frep_ush as (S1 & S2).
pose proof art_frep_where as WH. unfold art_free_where in WH.
pose proof REP as (ROK & _). rok_open14 ROK. geo_open GEO.
assert (Ufa : ~ (u - 16 <= U x < u + 8)).
{ destruct Hx as [Hx|Hx]; [|unfold apart in Uris; clear - Hx Uris Hc0; lia]. destruct k as [c w|i].
- destruct KIND as (Hc & (V0 & V1 & _) & _). destruct WH as (L1 & L2).
pose proof REP as (_ & _ & _ & (_ & PRIM & _) & _). destruct (PRIM c Hc) as (_ & OK & _). destruct OK as (_ & (Hau0 & Haumu) & _ & _ & _ & Hmu3 & _).
pose proof (art_class_size_facts c Hc) as (Hsz & Hsz16). rewrite <- (Z.div_exact _ 16) in Hsz16 by lia.
clear - Hx Hc Hc0 V0 V1 L1 L2 Haumu Hmu3 Hsz16 Espb Eu Hn. lia.
- destruct WH as (p & Hp & L1 & L2). destruct (LIVE p Hp) as (_ & _ & _ & _ & PO). pose proof (PO _ (or_intror (or_intror (or_introl eq_refl)))) as Ak. cbn [fst snd] in Ak.
destruct (LIVE3 p Hp) as (A1 & A2). rewrite <- (Z.div_exact _ 4096) in A1 by lia. rewrite <- (Z.div_exact _ 4096) in A2 by lia. unfold apart in Ak. clear - Hx Hc0 Ak L1 L2 A1 A2 Kspb Kend Eu Hn. lia. }
intros [F|F].
- unfold art_free3_fp, dprivD in F. unfold apart in Al2k, Abk, G11. clear - F Hx Hc0 Ufa HS G1 G4 G6 G9 G11 Espb Eris S2 Al2k Abk. lia.
- pose proof F as F_. apply art_frep_zone in F. destruct (Z_lt_ge_dec (U x) (rn_ris rn)) as [Lo|Hi].
+ unfold apart in G11. clear - F Hx Hc0 Hne Lo HS G1 G4 G6 G8 G11 Espb Eris. lia.
+
destruct Hx as [Hx|Hx]; [clear - Hx Hi Hc0 Eris; lia|].
assert (Hpg : rn_ris rn <= U x < rn_ris rn + 4096) by (clear - Hx Hc0; lia).
assert (F0 : art_enq_fp newb (Sp - 2208) (rn_t rn) (rn_spb rn) (rn_ris rn) (rn_qs rn) km b L B cntB (U x)) by exact F_.
pose proof (art_enq_fp_ris (U x) F0 Hpg) as R. clear - R Hx Hc0 Hne. lia.
Qed.
End SE.
#[using="LB M Sp q16 qr b1 km qtl cl24 newb wb b lastb L B cntB REP Eu Hn Hqr Hb1 KIND HS Emu Edep OUT LIVE LIVE2 LIVE3 OKpre"] Lemma art_frep_primary : art_rt_primary FSG rn G' M'.
Proof.
pose proof REP as (ROK & _ & _ & PRIM & _). rok_open14 ROK. pose proof GEO as GEO'. geo_open GEO'.
destruct PRIM as (PH & PRIM & Wsh). destruct art_frep_out as (GR & _ & _ & _ & _ & _ & PH' & RC' & OK' & _).
unfold art_rt_primary, G'. cbn [art_gs_free g_inited g_cls]. fold qtl. fold newb. fold cl24.
split. { destruct newb; cbn [orb]; exact PH'. }
split; [|eapply wr_grows; [exact GR|exact Wsh]].
intros c0 Hc0. destruct (Z.eqb_spec c0 24) as [->|Ne].
- destruct (PRIM 24 Hc0) as (_ & _ & Hin0 & _ & Hau0). fold cl24 in Hin0, Hau0.
split; [exact RC'|]. split; [exact OK'|].
split. { destruct newb; cbn [orb]; [intros _; reflexivity|exact Hin0]. }
split. { destruct OK' as (_ & _ & _ & Hk & _). exact Hk. }
destruct newb; cbn [orb]; [intros _; reflexivity|exact Hau0].
- destruct (PRIM c0 Hc0) as (RC0 & OK0 & Hin0 & Hk0 & Hau0).
split; [|split; [exact OK0|split; [intros X; rewrite (Hin0 X); apply orb_true_r|split; [exact Hk0|intros X; rewrite (Hau0 X); apply orb_true_r]]]].
destruct OK0 as (Hl16 & _ & _ & _ & _ & _ & _ & (_ & Hmfa1) & Hnf4 & _).
destruct RC0 as [[C0 CW] (Rmx & Rnf & Rmfa & Rau & Ram & Rmu & Rmm & Rna & Rnfr & Rfa & Wr & Wfa & Wu)].
assert (TC : forall a (j : nat) v, (rn_t rn + 208 + 80 * c0 <= a /\ a + Z.of_nat j <= rn_t rn + 208 + 80 * c0 + 4 \/ rn_t rn + 208 + 80 * c0 + 16 <= a /\ a + Z.of_nat j <= rn_t rn + 208 + 80 * c0 + 80) ->
cellA M a j v -> cellA M' a j v).
{ intros a j v Ha C. apply (art_cell_agree _ M M'); [|clear - Ha G7 Hc0; lia|clear - Ha G8 G2 Hc0; lia|exact C]. intros x Hx. apply (art_frep_out_cache c0 x ltac:(lia) (or_introl Ne)). clear - Ha Hx. lia. }
assert (TR : forall a (j : nat) v, (rn_spb rn + c0 * 2 ^ 32 + 3758096384 <= a /\ a + Z.of_nat j <= rn_spb rn + c0 * 2 ^ 32 + 2 ^ 32 \/ rn_ris rn + 128 * c0 <= a /\ a + Z.of_nat j <= rn_ris rn + 128 * c0 + 128) ->
cellA M a j v -> cellA M' a j v).
{ intros a j v Ha C. apply (art_cell_agree _ M M'); [|clear - Ha G4 G6 Eris Hc0; lia|clear - Ha G6 Eris G2 Hc0; lia|exact C]. intros x Hx. apply (art_frep_out_region c0 x Hc0 Ne). clear - Ha Hx. lia. }
split; [split|].
+ apply TC; [left; cbn; lia|exact C0].
+ intros j Hj. apply TC; [right; cbn; clear - Hj Hl16; lia|exact (CW j Hj)].
+ unfold art_region_rep.
split; [apply TR; [right; cbn; lia|exact Rmx]|]. split; [apply TR; [right; cbn; lia|exact Rnf]|]. split; [apply TR; [right; cbn; lia|exact Rmfa]|].
split; [apply TR; [right; cbn; lia|exact Rau]|]. split; [apply TR; [right; cbn; lia|exact Ram]|]. split; [apply TR; [right; cbn; lia|exact Rmu]|].
split; [apply TR; [right; cbn; lia|exact Rmm]|]. split; [apply TR; [right; cbn; lia|exact Rna]|]. split; [apply TR; [right; cbn; lia|exact Rnfr]|].
split. { intros j Hj. apply TR; [left; cbn; clear - Hj Hnf4 Hmfa1; lia|exact (Rfa j Hj)]. }
split; [eapply wr_grows; [exact GR|exact Wr]|]. split; [eapply wr_grows; [exact GR|exact Wfa]|eapply wr_grows; [exact GR|exact Wu]].
Qed.
Definition art_B_written (a : Z) : Prop :=
if newb then B <= a < B + 8 else (B + 8 <= a < B + 24 \/ B + 24 + 8 * cntB <= a < B + 32 + 8 * cntB).
Section SE.
Local Abbreviation SEC_T_art_frep_eqa := (forall c0 a, 1 <= c0 <= 30 ->
(rn_spb rn + c0 * 2 ^ 32 <= a < rn_spb rn + c0 * 2 ^ 32 + cl_mu (g_cls FSG G c0)
\/ (2147450880 + 8192 * rn_qs rn + c0 * 2 ^ 29 <= a /\ 8 * (a - (2147450880 + 8192 * rn_qs rn + c0 * 2 ^ 29)) < cl_mu (g_cls FSG G c0))) ->
~ (u - 16 <= a < u - 12) -> ~ (u <= a < u + 8) -> ~ (2147450880 + 2 * q16 <= a < 2147450880 + 2 * q16 + qr) ->
(c0 = 24 -> newb = true -> ~ (b <= a < b + 32)) -> (c0 = 24 -> L <> 0 -> ~ art_B_written a) ->
M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) (only parsing).
Variable c0 : ltac:(sec_ty2 constr:(SEC_T_art_frep_eqa) 0%nat 0%nat).
Variable a : ltac:(sec_ty2 constr:(SEC_T_art_frep_eqa) 1%nat 0%nat).
#[using="LB Sp n b1 km kb REP Hb1 HS Emu Edep OUT OKpre c0 a"] Lemma art_frep_eqa : ltac:(sec_stmt2 constr:(SEC_T_art_frep_eqa) 2%nat 0%nat).
Proof.
intros Hc0 Ha N1 N2 N3 Nb NB.
unfold art_B_written in NB. destruct art_frep_num as (Hkm & Hkm' & Hbz & HBz & HnL).
pose proof REP as (ROK & _ & _ & (_ & PRIM & _) & _). rok_open14 ROK. geo_open GEO.
destruct (PRIM c0 Hc0) as (_ & OK0 & _). destruct OK0 as (_ & (Hau0 & Haumu0) & _ & _ & _ & Hmu30 & _).
assert (Hmu24 : c0 = 24 -> cl_mu (g_cls FSG G c0) = 262144 * km). { intros ->. exact Emu. }
assert (Ra : 0 <= a < 2 ^ 64) by (clear - Ha Hc0 G4 G6 G2 Eris Espb Hmu30; lia).
apply art_frep_lin. rewrite art_u_lit by exact Ra. intros [F|F].
- unfold art_free3_fp, dprivD in F. unfold apart in G11, G10, Al2k, Al2s, Abk, Abs.
clear - F Ha Hc0 N1 N2 N3 HS G1 G2 G4 G6 G8 G9 G10 G11 Espb Eris Hmu30 Al2k Al2s Abk Abs. repeat (destruct F as [F|F]); lia.
- unfold art_enq_fp in F. destruct newb eqn:E.
+ specialize (Hbz eq_refl). specialize (fun e => Nb e eq_refl). unfold art_enq_new_fp, art_refill_fp in F. unfold apart in G11, G10.
destruct F as [F|[[F|[F|[F|[F|[F|[F|[F|[F|[F|F]]]]]]]]]|[F|[F|[F|F]]]]]; try (clear - F Ha Hc0 HS G1 G2 G4 G6 G8 G10 G11 Espb Eris Hmu30 Hmu24 Hkm Hkm'; lia).
* destruct F as (c' & Hc' & F). clear - F Ha Hc0 Hc' G1 G2 G8 G10 G11 G4 G6 Espb Eris Hmu30. lia.
* destruct (Z.eq_dec c0 24) as [e|ne]; [specialize (Nb e); clear - F Nb; lia|clear - F Ha Hc0 ne Hbz G4 Espb Hmu30; lia].
* destruct F as [NL F]. destruct (HBz NL) as (X1 & X2 & _). destruct (Z.eq_dec c0 24) as [e|ne]; [specialize (NB e NL); clear - F NB; lia|clear - F Ha Hc0 ne X1 X2 G4 Espb Hmu30; lia].
+ pose proof (HnL eq_refl) as NL. destruct (HBz NL) as (X1 & X2 & X3).
assert (X4 : cntB <> 1021). { destruct (art_free_newb_false qtl E) as (_ & X). exact X. }
unfold apart in G11. destruct F as [F|[F|[F|F]]]; try (clear - F Ha Hc0 HS G1 G2 G4 G6 G8 G10 G11 Espb Eris Hmu30; lia);
(destruct (Z.eq_dec c0 24) as [e|ne]; [specialize (NB e NL); clear - F NB X3 X4; lia|clear - F Ha Hc0 ne X1 X2 X3 G4 Espb Hmu30; lia]).
Qed.
End SE.
Definition art_in_chunk (c0 w0 a : Z) : Prop :=
rn_spb rn + c0 * 2 ^ 32 + 16 * w0 <= a < rn_spb rn + c0 * 2 ^ 32 + 16 * w0 + AsanTab.class_size c0
\/ (2147450880 + 8192 * rn_qs rn + c0 * 2 ^ 29 + 2 * w0 <= a /\ 8 * (a - (2147450880 + 8192 * rn_qs rn + c0 * 2 ^ 29)) + 8 <= 16 * w0 + AsanTab.class_size c0).
Section SE.
Local Abbreviation SEC_T_art_frep_uw_where := (forall a, (u - 16 <= a < u - 12 \/ u <= a < u + 8 \/ 2147450880 + 2 * q16 <= a < 2147450880 + 2 * q16 + qr) ->
match k with
| FKP c w => art_in_chunk c w a
| FKS _ => ~ (rn_spb rn <= a < rn_spb rn + 2 ^ 37) /\ ~ (2147450880 + 8192 * rn_qs rn <= a < 2147450880 + 8192 * rn_qs rn + 2 ^ 34)
end) (only parsing).
Variable a : ltac:(sec_ty2 constr:(SEC_T_art_frep_uw_where) 0%nat 0%nat).
#[using="FSG G LB M n b1 kb qtl cl24 wb b lastb L B cntB REP Eu Hn Hqr KIND Edep LIVE LIVE3 a"] Lemma art_frep_uw_where : ltac:(sec_stmt2 constr:(SEC_T_art_frep_uw_where) 1%nat 0%nat).
Proof.
intros Ha.
pose proof art_frep_where as WH. unfold art_free_where in WH. pose proof REP as (ROK & _). rok_open14 ROK. geo_open GEO.
destruct k as [c w|i].
- destruct KIND as (Hc & (V0 & V1 & (iw & Eiw)) & _). destruct WH as (L1 & L2). pose proof (art_class_size_facts c Hc) as (Hsz & Hsz16).
rewrite <- (Z.div_exact _ 16) in Hsz16 by lia. unfold art_in_chunk.
clear - Ha L1 L2 Hsz Hsz16 Espb Eu Hn Hqr V0. lia.
- destruct WH as (p & Hp & L1 & L2). destruct (LIVE p Hp) as (P0 & P1 & P2 & P3 & PO). destruct (LIVE3 p Hp) as (A1 & A2).
pose proof (PO _ (or_intror (or_intror (or_introl eq_refl)))) as Ak. cbn [fst snd] in Ak. rewrite <- (Z.div_exact _ 4096) in A1 by lia. rewrite <- (Z.div_exact _ 4096) in A2 by lia.
assert (Hend : u + 8 * qr <= fst p + snd p) by (clear - L2 A1 A2 Eu Hn Hqr; lia).
assert (Hq0 : 1 <= qr) by (clear - Hn Hqr; lia).
unfold apart in Ak. clear - Ha L1 Hend Hq0 Ak Kspb Kend Espb Eu G1 G2 G4 G6 Eris P0 P2 P3. split; intros X; destruct Ha as [Ha|[Ha|Ha]]; destruct Ak as [Ak|Ak]; lia.
Qed.
End SE.
Definition art_uw (a : Z) : Prop := u - 16 <= a < u - 12 \/ u <= a < u + 8 \/ 2147450880 + 2 * q16 <= a < 2147450880 + 2 * q16 + qr.
Section SE.
Local Abbreviation SEC_T_art_frep_uw_other := (forall c0 w0 a, 1 <= c0 <= 30 -> art_cptr_ok (AsanTab.class_size c0) (cl_au (g_cls FSG G c0)) w0 ->
match k with FKP c w => ~ (c0 = c /\ w0 = w) | FKS _ => True end -> art_in_chunk c0 w0 a -> ~ art_uw a) (only parsing).
Variable c0 : ltac:(sec_ty2 constr:(SEC_T_art_frep_uw_other) 0%nat 0%nat).
Variable w0 : ltac:(sec_ty2 constr:(SEC_T_art_frep_uw_other) 1%nat 0%nat).
Variable a : ltac:(sec_ty2 constr:(SEC_T_art_frep_uw_other) 2%nat 0%nat).
#[using="LB M n b1 kb qtl cl24 wb b lastb L B cntB REP Eu Hn Hqr KIND Edep LIVE LIVE3 c0 w0 a"] Lemma art_frep_uw_other : ltac:(sec_stmt2 constr:(SEC_T_art_frep_uw_other) 3%nat 0%nat).
Proof.
intros Hc0 V Nk Ha Ha'.
unfold art_uw in Ha'.
pose proof REP as (ROK & _ & _ & (_ & PRIM & _) & _). rok_open14 ROK. geo_open GEO.
destruct (PRIM c0 Hc0) as (_ & OK0 & _). pose proof OK0 as (_ & (Hau0 & Haumu0) & _ & _ & Hka0 & Hmu30 & _).
pose proof (art_class_size_facts c0 Hc0) as (Hsz0 & Hsz016). pose proof V as (V0 & V1 & (i0 & Ei0)).
pose proof (art_frep_uw_where a Ha') as W. destruct k as [c w|i].
- destruct KIND as (Hc & Vw & _). unfold art_in_chunk in W, Ha.
destruct (Z.eq_dec c0 c) as [->|Nc].
+ destruct (Z.eq_dec w0 w) as [->|Nw]; [apply Nk; split; reflexivity|].
pose proof (art_cptr_apart (AsanTab.class_size c) (cl_au (g_cls FSG G c)) w0 w ltac:(clear - Hsz0; lia) V Vw Nw) as AP. destruct Vw as (W0 & W1 & _). clear - W Ha AP Hsz0 Hc0 V0 V1 W0 W1 Haumu0 Hmu30 G4 Espb. lia.
+ pose proof (art_class_size_facts c Hc) as (Hsz & _). destruct Vw as (W0 & W1 & _).
pose proof REP as (_ & _ & _ & (_ & PRIM' & _) & _). destruct (PRIM' c Hc) as (_ & OKc & _). destruct OKc as (_ & (_ & Haumuc) & _ & _ & _ & Hmu3c & _).
clear - W Ha Nc Hc Hc0 V0 V1 W0 W1 Haumu0 Hmu30 Haumuc Hmu3c Hsz Hsz0 G4 Espb. lia.
- destruct W as (W1 & W2). unfold art_in_chunk in Ha. clear - W1 W2 Ha Hc0 V0 V1 Haumu0 Hmu30 Hsz0 Espb G4. lia.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_frep_chunk_eq0 := (forall c0 w0 a, 1 <= c0 <= 30 -> art_cptr_ok (AsanTab.class_size c0) (cl_au (g_cls FSG G c0)) w0 ->
(c0 = 24 -> newb = true -> w0 <> wb) -> (c0 = 24 -> L <> 0 -> rn_spb rn + 24 * 2 ^ 32 + 16 * w0 <> B) ->
art_in_chunk c0 w0 a -> ~ art_uw a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) (only parsing).
Variable c0 : ltac:(sec_ty2 constr:(SEC_T_art_frep_chunk_eq0) 0%nat 0%nat).
Variable w0 : ltac:(sec_ty2 constr:(SEC_T_art_frep_chunk_eq0) 1%nat 0%nat).
Variable a : ltac:(sec_ty2 constr:(SEC_T_art_frep_chunk_eq0) 2%nat 0%nat).
#[using="LB Sp n b1 km kb b cntB REP Hb1 HS Emu Edep OUT OKpre c0 w0 a"] Lemma art_frep_chunk_eq0 : ltac:(sec_stmt2 constr:(SEC_T_art_frep_chunk_eq0) 3%nat 0%nat).
Proof.
intros Hc0 V Nwb NwB Ha UWa.
unfold art_uw in UWa. destruct art_frep_num as (Hkm & Hkm' & Hbz & HBz & HnL).
pose proof REP as (ROK & _ & _ & (_ & PRIM & _) & _ & _ & QR & _). rok_open14 ROK. geo_open GEO.
destruct (PRIM c0 Hc0) as (_ & OK0 & _). pose proof OK0 as (_ & (Hau0 & Haumu0) & _ & _ & Hka0 & Hmu30 & _).
pose proof (art_class_size_facts c0 Hc0) as (Hsz0 & Hsz016). pose proof V as (V0 & V1 & (i0 & Ei0)).
apply (art_frep_eqa c0 a Hc0).
- unfold art_in_chunk in Ha. clear - Ha V0 V1 Haumu0 Hsz0. lia.
- intros X. apply UWa. left. exact X.
- intros X. apply UWa. right; left. exact X.
- intros X. apply UWa. right; right. exact X.
- intros -> E X. specialize (Nwb eq_refl E). destruct art_frep_out as (_ & _ & _ & _ & _ & _ & _ & _ & OK' & NEW & _). destruct (NEW E) as (CPb & _).
rewrite art_class_size_24 in *. assert (Hau' : cl_au cl24 <= cl_au (art_ca_pre 24 cl24)).
{ destruct (art_ca_pre_au 24 cl24) as [E0|(_ & _ & E0)]; rewrite E0; [lia|]. assert (0 <= art_cls_new 24 cl24 * AsanTab.class_size 24); [|lia].
apply Z.mul_nonneg_nonneg; [|rewrite art_class_size_24; lia]. unfold art_cls_new. apply Z.div_pos; [|rewrite art_class_size_24; lia]. fold cl24 in Hau0, Haumu0. lia. }
pose proof (art_cptr_apart 8192 (cl_au (art_ca_pre 24 cl24)) w0 wb ltac:(clear; lia) (art_cptr_mono _ _ _ _ Hau' V) CPb Nwb) as AP.
unfold art_in_chunk in Ha. rewrite art_class_size_24 in Ha. unfold b in X. clear - X Ha AP Hbz E G4 Espb V0 V1 Haumu0 Hmu30. specialize (Hbz E). lia.
- intros -> NL X. specialize (NwB eq_refl NL).
assert (InB : In lastb (g_qt FSG G ++ g_qg FSG G)). { apply in_or_app. left. unfold lastb, art_lastb. apply JbtFxQ.art_last_in. intros E. apply NL. unfold L. fold qtl in E. rewrite E. reflexivity. }
destruct QR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & BCH). destruct (BCH lastb InB) as (wB & EwB & VB & _). fold B in EwB. rewrite art_class_size_24 in *.
assert (Nw : w0 <> wB) by (intros ->; apply NwB; symmetry; exact EwB).
pose proof (art_cptr_apart 8192 (cl_au (g_cls FSG G 24)) w0 wB ltac:(clear; lia) V VB Nw) as AP. unfold art_in_chunk in Ha. rewrite art_class_size_24 in Ha.
assert (XW : rn_spb rn + 24 * 2 ^ 32 + 16 * wB <= a < rn_spb rn + 24 * 2 ^ 32 + 16 * wB + 8192).
{ unfold art_B_written in X. rewrite EwB in X. destruct (HBz NL) as (_ & _ & X3). destruct newb eqn:E; [clear - X; lia|].
destruct (art_free_newb_false qtl E) as (_ & X4). fold lastb in X4. fold cntB in X4. clear - X X3 X4. lia. }
destruct VB as (VB0 & VB1 & _). clear - XW Ha AP G4 Espb V0 V1 VB0 VB1 Haumu0 Hmu30. lia.
Qed.
End SE.
#[using="LB Sp u n q16 qr b1 km kb b cntB REP Eu Hn Hqr Hb1 KIND HS Emu Edep OUT LIVE LIVE3 OKpre"] Lemma art_frep_chunk_eq : forall c0 w0 a, 1 <= c0 <= 30 -> art_cptr_ok (AsanTab.class_size c0) (cl_au (g_cls FSG G c0)) w0 ->
match k with FKP c w => ~ (c0 = c /\ w0 = w) | FKS _ => True end ->
(c0 = 24 -> newb = true -> w0 <> wb) -> (c0 = 24 -> L <> 0 -> rn_spb rn + 24 * 2 ^ 32 + 16 * w0 <> B) ->
art_in_chunk c0 w0 a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Proof.
intros c0 w0 a Hc0 V Nk Nwb NwB Ha. apply (art_frep_chunk_eq0 c0 w0 a Hc0 V Nwb NwB Ha). exact (art_frep_uw_other c0 w0 a Hc0 V Nk Ha).
Qed.
#[using="LB Sp n b1 km kb b cntB REP Hb1 HS Emu Edep OUT OKpre"] Lemma art_frep_chunk_eqw : forall c0 w0 (x : word), 1 <= c0 <= 30 -> art_cptr_ok (AsanTab.class_size c0) (cl_au (g_cls FSG G c0)) w0 ->
(c0 = 24 -> newb = true -> w0 <> wb) -> (c0 = 24 -> L <> 0 -> rn_spb rn + 24 * 2 ^ 32 + 16 * w0 <> B) ->
art_in_chunk c0 w0 (U x) -> ~ art_uw (U x) -> M' x = M x.
Proof. intros c0 w0 x Hc0 V Nwb NwB Ha UWa. rewrite <- (Z_to_bv_bv_unsigned 64 x). exact (art_frep_chunk_eq0 c0 w0 (U x) Hc0 V Nwb NwB Ha UWa). Qed.
#[using="rn LB M b1 kb b lastb L B cntB REP Edep"] Lemma art_frep_wb_free : newb = true -> g_st FSG G 24 wb = CFree.
Proof.
intros E. pose proof REP as (_ & _ & _ & (_ & PRIM & _) & CH & _). destruct (PRIM 24 ltac:(lia)) as (_ & OK & _). fold cl24 in OK.
specialize (CH 24 ltac:(lia)). cbv zeta in CH. destruct CH as (_ & II & II' & _). fold cl24 in II, II'.
pose proof (art_ca_cptr_origin 24 cl24 ltac:(lia) OK) as ORG. fold wb in ORG. destruct ORG as [Hin0|(_ & _ & Hlo)]; [exact (II wb Hin0)|].
apply II'. intros (_ & Bd & _). rewrite art_class_size_24 in Bd. lia.
Qed.
#[using="Type"] Lemma art_frep_st_pop : newb = true -> g_st FSG G' 24 wb = CBatch.
Proof. intros E. unfold G'. cbn [art_gs_free g_st]. fold qtl. fold newb. fold cl24. fold wb. rewrite E, !Z.eqb_refl. reflexivity. Qed.
#[using="LB M b1 qtl cl24 newb wb b lastb L B cntB REP KIND Edep OKpre"] Lemma art_frep_st_freed : forall c w, k = FKP c w -> g_st FSG G' c w = CQuar u n.
Proof.
intros c w Ek. unfold G'. cbn [art_gs_free g_st]. fold qtl. fold newb. fold cl24. fold wb.
assert (NA : newb && (c =? 24) && (w =? wb) = false).
{ destruct newb eqn:E; [|reflexivity]. destruct (Z.eqb_spec c 24) as [->|]; [|reflexivity]. destruct (Z.eqb_spec w wb) as [->|]; [|reflexivity]. exfalso.
pose proof (art_frep_wb_free E) as F. pose proof KIND as KD. rewrite Ek in KD. destruct KD as (_ & _ & St). rewrite F in St. discriminate. }
rewrite NA, Ek, !Z.eqb_refl. reflexivity.
Qed.
#[using="KIND OKpre"] Lemma art_frep_st_other : forall c0 w0, ~ (newb = true /\ c0 = 24 /\ w0 = wb) -> match k with FKP c w => ~ (c0 = c /\ w0 = w) | FKS _ => True end ->
g_st FSG G' c0 w0 = g_st FSG G c0 w0.
Proof.
intros c0 w0 NA Nk. unfold G'. cbn [art_gs_free g_st]. fold qtl. fold newb. fold cl24. fold wb.
assert (NA' : newb && (c0 =? 24) && (w0 =? wb) = false).
{ destruct newb eqn:E; [|reflexivity]. destruct (Z.eqb_spec c0 24) as [->|]; [|reflexivity]. destruct (Z.eqb_spec w0 wb) as [->|]; [|reflexivity]. exfalso. apply NA. repeat split; reflexivity. }
rewrite NA'. destruct k as [c w|i]; [|reflexivity]. destruct (Z.eqb_spec c0 c) as [->|]; [|reflexivity]. destruct (Z.eqb_spec w0 w) as [->|]; [|reflexivity]. exfalso. apply Nk. split; reflexivity.
Qed.
#[using="Type"] Lemma art_lb_remove_keep0 : ltac2:(TCodec.tc2 tcn__JbtInvFree "I'8'<'E%2211%411&R5r1r2%33521&B'@&6%13::5vS6%43<21%611r3&Or4%2261%?3A41p061p0>1pU4D1pQBD1").
Proof.
induction LB0 as [|x r IH]; intros b0 Hb Nu; [contradiction|]. cbn [lb_remove]. destruct Hb as [->|Hb].
- destruct (Z.eqb_spec (fst b0) u) as [E|_]; [contradiction|]. left. reflexivity.
- destruct (Z.eqb_spec (fst x) u) as [_|_]; [exact Hb|right; apply IH; assumption].
Qed.
Section SE.
Local Abbreviation SEC_T_art_frep_old_chunk := (forall c0 w0, 1 <= c0 <= 30 -> art_cptr_ok (AsanTab.class_size c0) (cl_au (g_cls FSG G c0)) w0 -> ~ (newb = true /\ c0 = 24 /\ w0 = wb) ->
let rb := rn_spb rn + c0 * 2 ^ 32 in let sz := AsanTab.class_size c0 in
match g_st FSG G' c0 w0 with
| CFree => In w0 (cl_cache (g_cls FSG G c0) ++ cl_free (g_cls FSG G c0)) /\ byte_at M' (HeapIfaceA.S (rb + 16 * w0)) 0xfa
| CAlloc u0 n0 => In (u0, n0) (lb_remove u LB) /\ rb + 16 * w0 + 16 <= u0 /\ u0 + n0 <= rb + 16 * w0 + sz /\ art_chunk_hdr M' u0 n0 2 /\ HAJ.shadow_blkR M' u0 n0
/\ byte_at M' (HeapIfaceA.S (rb + 16 * w0)) 0xfa /\ art_lch M' (rb + 16 * w0) u0
| CQuar u0 n0 => rb + 16 * w0 + 16 <= u0 /\ u0 + n0 <= rb + 16 * w0 + sz /\ art_chunk_hdr M' u0 n0 3 /\ art_in_batches (g_qt FSG G' ++ g_qg FSG G') (u0 - 16) n0
/\ byte_at M' (HeapIfaceA.S (rb + 16 * w0)) 0xfa /\ art_lch M' (rb + 16 * w0) u0
| CBatch => c0 = 24 /\ exists b0, In b0 (g_qt FSG G' ++ g_qg FSG G') /\ bt_addr b0 = rb + 16 * w0
end) (only parsing).
Variable c0 : ltac:(sec_ty2 constr:(SEC_T_art_frep_old_chunk) 0%nat 0%nat).
Variable w0 : ltac:(sec_ty2 constr:(SEC_T_art_frep_old_chunk) 1%nat 0%nat).
#[using="M Sp q16 qr b1 km b lastb L B cntB REP Eu Hn Hqr Hb1 Hty Cn KIND HS Emu Edep OUT LIVE LIVE3 OKpre c0 w0"] Lemma art_frep_old_chunk : ltac:(sec_stmt2 constr:(SEC_T_art_frep_old_chunk) 2%nat 0%nat).
Proof.
intros Hc0 V NA rb sz.
pose proof REP as (ROK & _ & _ & (_ & PRIM & _) & CH & _ & QR & _). pose proof ROK as ROK'. rok_open14 ROK'. pose proof GEO as GEO'. geo_open GEO'.
destruct art_frep_num as (Hkm & Hkm' & Hbz & HBz & HnL).
destruct art_frep_out as (GR & _ & _ & CHW & _).
pose proof (CH c0 Hc0) as CH0. cbv zeta in CH0. destruct CH0 as (_ & _ & _ & III). specialize (III w0 V). fold rb in III. fold sz in III.
destruct (PRIM c0 Hc0) as (_ & OK0 & _). pose proof OK0 as (_ & (Hau0 & Haumu0) & _ & _ & Hka0 & Hmu30 & _).
pose proof (art_class_size_facts c0 Hc0) as (Hsz0 & Hsz016). fold sz in Hsz0, Hsz016. pose proof V as (V0 & V1 & _). fold sz in V1.
assert (ES : forall y, HeapIfaceA.S (rb + 8 * y) = 2147450880 + 8192 * rn_qs rn + c0 * 2 ^ 29 + y). { intros y. unfold rb. rewrite Espb. apply art_S_lin. }
assert (Gq : g_qt FSG G' ++ g_qg FSG G' = art_qt_add qtl b (u - 16, n) ++ g_qg FSG G) by reflexivity.
assert (Nwb : c0 = 24 -> newb = true -> w0 <> wb) by (intros e1 e2 e3; apply NA; repeat split; assumption).
assert (DEC : (exists c w, k = FKP c w /\ c0 = c /\ w0 = w) \/ match k with FKP c w => ~ (c0 = c /\ w0 = w) | FKS _ => True end).
{ destruct k as [c w|i]; [|right; exact I]. destruct (Z.eq_dec c0 c) as [->|Nc]; [|right; intros (X & _); exact (Nc X)].
destruct (Z.eq_dec w0 w) as [->|Nw]; [left; exists c, w; repeat split; reflexivity|right; intros (_ & X); exact (Nw X)]. }
assert (NwB : g_st FSG G c0 w0 <> CBatch -> c0 = 24 -> L <> 0 -> rn_spb rn + 24 * 2 ^ 32 + 16 * w0 <> B).
{ intros NS -> NL E. apply NS.
assert (InB : In lastb (g_qt FSG G ++ g_qg FSG G)). { apply in_or_app. left. unfold lastb, art_lastb. apply JbtFxQ.art_last_in. intros E0. apply NL. unfold L. fold qtl in E0. rewrite E0. reflexivity. }
destruct QR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & BCH). destruct (BCH lastb InB) as (wB & EwB & _ & StB). fold B in EwB.
assert (w0 = wB) by (clear - E EwB; lia). subst w0. exact StB. }
destruct DEC as [(c & w & Ek & -> & ->)|Nk].
-
rewrite (art_frep_st_freed c w Ek). pose proof KIND as KD. rewrite Ek in KD. destruct KD as (_ & _ & St). rewrite St in III. destruct III as (_ & J2 & J3 & J4 & _ & J6 & J7).
assert (NB' : c = 24 -> L <> 0 -> rn_spb rn + 24 * 2 ^ 32 + 16 * w <> B) by (apply NwB; rewrite St; discriminate).
assert (EQ : forall a, art_in_chunk c w a -> ~ art_uw a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) by (intros a; exact (art_frep_chunk_eq0 c w a Hc0 V Nwb NB')).
assert (Hu16 : rb + 16 * w + 32 <= u \/ u - 16 = rb + 16 * w).
{ rewrite <- (Z.div_exact _ 16) in Hsz016 by lia. unfold rb. rewrite Espb. clear - J2 Eu Espb. unfold rb in J2. rewrite Espb in J2. lia. }
split; [exact J2|]. split; [exact J3|].
split. { exists b1. split; [exact Hb1|]. split; [exact Hty|]. split; [exact CHW|]. split; [|exact Hn].
apply (art_cell_agree _ M M'); [|clear - J2 G4 Hc0 V0; unfold rb in J2; lia|clear - J3 G6 Eris G2 Hc0 Hsz0 V1 Haumu0 Hmu30 Hn; unfold rb in J3; cbn; lia|exact Cn].
intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply EQ; [left; unfold rb in J2, J3; cbn in Hx; clear - Hx J2 J3 Hn; lia|unfold art_uw; cbn in Hx; clear - Hx Hqr Hn Eu J2 G4 Espb Hc0 V0; unfold rb in J2; lia]. }
split; [rewrite Gq; exact (art_in_batches_new qtl (g_qg FSG G) b (u - 16, n))|].
split. { apply (art_byte_at_eq M M'); [|exact J6]. replace (rb + 16 * w) with (rb + 8 * (2 * w)) by lia. rewrite ES. apply EQ; [right; clear - Hsz0; lia|].
unfold art_uw. clear - J2 Eu Espb G4 Hc0 V0 Hqr Hn. unfold rb in J2. rewrite Espb in J2. lia. }
intros NE. destruct (J7 NE) as (C1 & C2). destruct Hu16 as [Hu16|Hu16]; [|contradiction].
split; (apply (art_cell_agree _ M M'); [|clear - G4 Hc0 V0; unfold rb; lia|clear - Hu16 J3 G6 Eris G2 Hc0 Hsz0 V1 Haumu0 Hmu30 Hn; unfold rb in *; cbn; lia|assumption];
intros x Hx; rewrite <- (Z_to_bv_bv_unsigned 64 x); apply EQ; [left; cbn in Hx; unfold rb in *; clear - Hx Hu16 J3 Hn; lia|unfold art_uw; cbn in Hx; unfold rb in *; clear - Hx Hu16 Eu Espb G4 Hc0 V0 Hqr Hn J3 Hsz0; lia]).
-
rewrite (art_frep_st_other c0 w0 NA Nk).
assert (EQ : g_st FSG G c0 w0 <> CBatch -> forall a, art_in_chunk c0 w0 a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros NS a. exact (art_frep_chunk_eq c0 w0 a Hc0 V Nk Nwb (NwB NS)). }
assert (TB : g_st FSG G c0 w0 <> CBatch -> byte_at M (HeapIfaceA.S (rb + 16 * w0)) 250 -> byte_at M' (HeapIfaceA.S (rb + 16 * w0)) 250).
{ intros NS Bt. apply (art_byte_at_eq M M'); [|exact Bt]. replace (rb + 16 * w0) with (rb + 8 * (2 * w0)) by lia. rewrite ES. apply (EQ NS). right. clear - Hsz0. fold sz. lia. }
assert (TCELL : g_st FSG G c0 w0 <> CBatch -> forall a (j : nat) v, rb + 16 * w0 <= a -> a + Z.of_nat j <= rb + 16 * w0 + sz -> cellA M a j v -> cellA M' a j v).
{ intros NS a j v Ha Hj C. apply (art_cell_agree _ M M'); [|clear - Ha G4 Hc0 V0; unfold rb in Ha; lia|clear - Hj G6 Eris G2 Hc0 V1 Haumu0 Hmu30; unfold rb in Hj; lia|exact C].
intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply (EQ NS). left. fold rb. fold sz. clear - Hx Ha Hj. lia. }
assert (THDR : g_st FSG G c0 w0 <> CBatch -> forall u0 n0 st, rb + 16 * w0 + 16 <= u0 -> u0 + n0 <= rb + 16 * w0 + sz -> art_chunk_hdr M u0 n0 st -> art_chunk_hdr M' u0 n0 st).
{ intros NS u0 n0 st L1 L2 (bb & Hb & Hbt & C1 & C2 & Hn0). exists bb. split; [exact Hb|]. split; [exact Hbt|]. split; [|split; [|exact Hn0]].
- apply (TCELL NS); [lia|cbn; lia|exact C1]. - apply (TCELL NS); [lia|cbn; lia|exact C2]. }
assert (TSH : g_st FSG G c0 w0 <> CBatch -> forall u0 n0, 0 < n0 -> rb + 16 * w0 + 16 <= u0 -> u0 + n0 <= rb + 16 * w0 + sz -> HAJ.shadow_blkR M u0 n0 -> HAJ.shadow_blkR M' u0 n0).
{ intros NS u0 n0 Hn0 L1 L2 SB0. unfold rb in L1, L2. rewrite Espb in L1, L2. apply (shadow_blkR_tby M M' u0 n0 Hn0); [|exact SB0]. intros j Hj0 Hjc v Bv. apply (art_byte_at_eq M M'); [|exact Bv].
destruct Hjc as [Hj|(Ej & Hm)].
- assert (Hj' : 0 <= j < n0 / 8) by lia. clear Hj. rename Hj' into Hj. apply (EQ NS). right.
pose proof (art_blk_shadow_in FSG rn G 0 0 kb Edep (rn_qs rn) c0 w0 sz u0 n0 j Hsz016 Hn0 L1 L2 ltac:(left; lia) ltac:(lia)) as Bd. cbv zeta in Bd. fold sz. clear - Bd. lia.
- subst j. apply (EQ NS). right.
pose proof (art_blk_shadow_in FSG rn G 0 0 kb Edep (rn_qs rn) c0 w0 sz u0 n0 (n0 / 8) Hsz016 Hn0 L1 L2 ltac:(right; split; [reflexivity|exact Hm]) ltac:(apply Z.div_pos; lia)) as Bd.
cbv zeta in Bd. fold sz. clear - Bd. lia. }
assert (TLCH : g_st FSG G c0 w0 <> CBatch -> forall u0, rb + 16 * w0 + 16 <= u0 -> art_lch M (rb + 16 * w0) u0 -> art_lch M' (rb + 16 * w0) u0).
{ intros NS u0 L1 LC NE. destruct (LC NE) as (C1 & C2). split; (apply (TCELL NS); [lia|cbn; clear - Hsz0; fold sz; lia|assumption]). }
destruct (g_st FSG G c0 w0) as [|u0 n0|u0 n0|] eqn:St.
+ destruct III as (I1 & I2). split; [exact I1|apply TB; [discriminate|exact I2]].
+ destruct III as (J1 & J2 & J3 & J4 & J5 & J6 & J7). pose proof J4 as (_ & _ & _ & _ & _ & Hn0).
assert (Nu : u0 <> u).
{ intros ->. apply (art_frep_uw_other c0 w0 u Hc0 V Nk); [left; fold rb; fold sz; clear - J2 J3 Hn0; lia|unfold art_uw; right; left; clear; lia]. }
split; [apply art_lb_remove_keep0; [exact J1|exact Nu]|]. split; [exact J2|]. split; [exact J3|]. split; [apply THDR; [discriminate|exact J2|exact J3|exact J4]|].
split; [apply TSH; [discriminate|lia|exact J2|exact J3|exact J5]|]. split; [apply TB; [discriminate|exact J6]|apply TLCH; [discriminate|exact J2|exact J7]].
+ destruct III as (J2 & J3 & J4 & J5 & J6 & J7). split; [exact J2|]. split; [exact J3|]. split; [apply THDR; [discriminate|exact J2|exact J3|exact J4]|].
split; [rewrite Gq; apply art_in_batches_add; exact J5|]. split; [apply TB; [discriminate|exact J6]|apply TLCH; [discriminate|exact J2|exact J7]].
+ destruct III as (E24 & b0 & Hb0 & Eb0). split; [exact E24|]. rewrite Gq. apply in_app_or in Hb0. destruct Hb0 as [Hb0|Hb0].
* destruct (art_qt_add_keep qtl b (u - 16, n) b0 Hb0) as (b0' & H1 & H2 & _). exists b0'. split; [apply in_or_app; left; exact H1|rewrite H2; exact Eb0].
* exists b0. split; [apply in_or_app; right; exact Hb0|exact Eb0].
Qed.
End SE.
#[using="rn u n kb KIND"] Lemma art_frep_nk_free : forall c0 w0, g_st FSG G c0 w0 = CFree -> match k with FKP c w => ~ (c0 = c /\ w0 = w) | FKS _ => True end.
Proof. intros c0 w0 St. destruct k as [c w|i]; [|exact I]. intros (-> & ->). destruct KIND as (_ & _ & St'). rewrite St in St'. discriminate. Qed.
#[using="M Sp q16 qr b1 km qtl cl24 newb wb b lastb L B cntB REP Eu Hn Hqr Hb1 Hty Cn KIND HS Emu Edep OUT LIVE LIVE2 LIVE3 OKpre"] Lemma art_frep_chunks : art_rt_chunks FSG rn G' (lb_remove u LB) M'.
Proof.
pose proof REP as (ROK & _ & _ & (_ & PRIM & _) & CH & _). pose proof ROK as ROK'. rok_open14 ROK'. pose proof GEO as GEO'. geo_open GEO'.
destruct art_frep_num as (Hkm & Hkm' & Hbz & HBz & HnL). destruct art_frep_u_far as (_ & _ & _ & Ush & _).
destruct art_frep_out as (GR & _ & _ & _ & _ & _ & _ & _ & OK' & NEW & _).
intros c0 Hc0. pose proof (CH c0 Hc0) as CH0. cbv zeta in CH0. cbv zeta. destruct CH0 as (I0 & II & II' & III).
destruct (PRIM c0 Hc0) as (_ & OK0 & _). pose proof OK0 as (_ & (Hau0 & Haumu0) & _ & _ & Hka0 & Hmu30 & _).
pose proof (art_class_size_facts c0 Hc0) as (Hsz0 & Hsz016).
assert (ES : forall y, HeapIfaceA.S (rn_spb rn + c0 * 2 ^ 32 + 8 * y) = 2147450880 + 8192 * rn_qs rn + c0 * 2 ^ 29 + y). { intros y. rewrite Espb. apply art_S_lin. }
assert (TT : forall x, cl_au (g_cls FSG G c0) <= x < cl_mu (g_cls FSG G c0) -> x mod 8 = 0 -> byte_at M' (HeapIfaceA.S (rn_spb rn + c0 * 2 ^ 32 + x)) 250).
{ intros x Hx Hx8. assert (Ex : x = 8 * (x / 8)). { pose proof (Z.div_mod x 8 ltac:(lia)) as D. rewrite Hx8 in D. lia. }
apply (art_byte_at_eq M M'); [|exact (I0 x Hx Hx8)]. rewrite Ex, ES. set (y := x / 8) in *.
assert (UWy : ~ art_uw (2147450880 + 8192 * rn_qs rn + c0 * 2 ^ 29 + y)).
{ intros Hu. pose proof (art_frep_uw_where _ Hu) as W. destruct k as [c w|i].
- destruct KIND as (Hc & (W0 & W1 & _) & _). destruct (PRIM c Hc) as (_ & OKc & _). destruct OKc as (_ & (_ & Haumuc) & _ & _ & _ & Hmu3c & _).
pose proof (art_class_size_facts c Hc) as (Hsz & _). unfold art_in_chunk in W.
destruct (Z.eq_dec c0 c) as [->|Nc]; [clear - W Hx Ex W0 W1 G4 Espb Hc Hsz Haumuc Hmu3c; lia|clear - W Hx Ex Nc Hc Hc0 W0 W1 G4 Espb Hsz Haumuc Hmu3c Hau0 Hmu30; lia].
- destruct W as (_ & W2). apply W2. clear - Hx Ex Hc0 Hau0 Hmu30. lia. }
apply (art_frep_eqa c0 _ Hc0); [right; clear - Hx Ex Hau0; lia| | | | | ].
- intros X. apply UWy. left. exact X.
- intros X. apply UWy. right; left. exact X.
- intros X. apply UWy. right; right. exact X.
- intros _ E X. specialize (Hbz E). clear - X Hbz Hx Ex Hc0 Hmu30 Hau0 G4 G6 G2 Espb Eris. lia.
- intros _ NL X. destruct (HBz NL) as (X1 & X2 & X3). unfold art_B_written in X. clear - X X1 X2 X3 Hx Ex Hc0 Hmu30 Hau0 G4 G6 G2 Espb Eris. destruct newb; lia. }
unfold G'. cbn [art_gs_free g_cls]. fold qtl. fold newb. fold cl24. fold wb. fold G'.
destruct (Z.eqb_spec c0 24) as [E24|N24]; [destruct (Bool.bool_dec newb true) as [En|En]; [rewrite En|apply Bool.not_true_is_false in En; rewrite En]|].
-
subst c0. fold cl24 in I0, II, II', III, OK0, Hau0, Haumu0, Hka0, Hmu30, TT. unfold art_enq_cls. cbn [art_cls_pop cl_cache cl_free cl_au cl_mu]. rewrite art_class_size_24 in *.
pose proof (OKpre En) as OKp. destruct (NEW En) as (CPb & PSH & _).
assert (Hau' : cl_au cl24 <= cl_au (art_ca_pre 24 cl24)).
{ destruct (art_ca_pre_au 24 cl24) as [E0|(_ & _ & E0)]; rewrite E0; [lia|]. assert (0 <= art_cls_new 24 cl24 * AsanTab.class_size 24); [|lia].
apply Z.mul_nonneg_nonneg; [|rewrite art_class_size_24; lia]. unfold art_cls_new. apply Z.div_pos; [|rewrite art_class_size_24; lia]. lia. }
assert (NAw : forall w0, w0 <> wb -> ~ (newb = true /\ 24 = 24 /\ w0 = wb)) by (intros w0 N (_ & _ & X); exact (N X)).
assert (BYTE : forall y v, 0 <= y < 2 ^ 29 -> 0 <= v < 256 -> cellA M' (2147450880 + 8192 * rn_qs rn + 24 * 2 ^ 29 + y) 1 v -> byte_at M' (2147450880 + 8192 * rn_qs rn + 24 * 2 ^ 29 + y) v).
{ intros y v Hy Hv C. apply art_byte_of_cell1; [right; clear - Hy G4 Espb; lia|clear - Hy G4 Espb G6 Eris G2; lia|exact Hv|exact C]. }
assert (NEWB : forall x, cl_mu cl24 <= x < cl_mu (art_ca_pre 24 cl24) -> x mod 8 = 0 -> byte_at M' (HeapIfaceA.S (rn_spb rn + 24 * 2 ^ 32 + x)) 250).
{ intros x Hx Hx8. assert (Ex : x = 8 * (x / 8)). { pose proof (Z.div_mod x 8 ltac:(lia)) as D. rewrite Hx8 in D. lia. }
destruct (art_ca_pre_mu_cases 24 cl24) as [(E & _)|(E1 & E2 & E3)]; [rewrite E in Hx; lia|]. rewrite E3 in Hx. rewrite Ex, ES.
pose proof (PSH E1 E2 (x / 8 - 32768 * km) ltac:((clear - Apkb B Edep Emu Ex FSG G Hau0 Haumu0 Hb1 Hx L Plo b b1 cl24 cntB kb km lastb qtl rn wb x; lia))) as C. replace (2147450880 + 8192 * rn_qs rn + 24 * 2 ^ 29 + 32768 * km + (x / 8 - 32768 * km)) with (2147450880 + 8192 * rn_qs rn + 24 * 2 ^ 29 + x / 8) in C by lia.
apply BYTE; [clear - Hx Ex Hkm Hkm' Emu; lia|lia|exact C]. }
split. { intros x Hx Hx8. destruct (Z_lt_ge_dec x (cl_mu cl24)) as [Lo|Hi]; [apply TT; [lia|exact Hx8]|apply NEWB; [lia|exact Hx8]]. }
split. { intros w0 Hin0. destruct (art_malloc_in_free 24 cl24 Hc0 OK0 w0 OKp Hin0) as (Nw & [Hold|Hnew]); fold wb in Nw.
- rewrite (art_frep_st_other 24 w0 (NAw w0 Nw) (art_frep_nk_free 24 w0 (II w0 Hold))). exact (II w0 Hold).
- rewrite art_class_size_24 in Hnew. rewrite (art_frep_st_other 24 w0 (NAw w0 Nw) (art_frep_nk_free 24 w0 (II' w0 Hnew))). exact (II' w0 Hnew). }
split. { intros w0 NV'. assert (Nw : w0 <> wb) by (intros ->; exact (NV' CPb)). assert (NV : ~ art_cptr_ok 8192 (cl_au cl24) w0) by (intros V; apply NV'; eapply art_cptr_mono; [exact Hau'|exact V]).
rewrite (art_frep_st_other 24 w0 (NAw w0 Nw) (art_frep_nk_free 24 w0 (II' w0 NV))). exact (II' w0 NV). }
intros w0 V'. destruct (Z.eq_dec w0 wb) as [->|Nw].
{ rewrite (art_frep_st_pop En). split; [reflexivity|]. exists (BATCH b [(u - 16, n)]). split; [|reflexivity].
change (g_qt FSG G' ++ g_qg FSG G') with (art_qt_add qtl b (u - 16, n) ++ g_qg FSG G). apply in_or_app. left. unfold art_qt_add. fold newb. rewrite En. apply in_or_app. right. left. reflexivity. }
destruct (art_cptr_ok_dec 8192 (cl_au cl24) w0 ltac:(lia)) as [V|NV].
+ pose proof (art_frep_old_chunk 24 w0 Hc0 ltac:(rewrite art_class_size_24; exact V) (NAw w0 Nw)) as O. cbv zeta in O. rewrite art_class_size_24 in O.
destruct (g_st FSG G' 24 w0) as [|u0 n0|u0 n0|]; [|exact O|exact O|exact O]. destruct O as (O1 & O2). split; [|exact O2].
apply (art_malloc_free_in 24 cl24 Hc0 OK0 w0 OKp V' Nw). intros _. exact O1.
+ rewrite (art_frep_st_other 24 w0 (NAw w0 Nw) (art_frep_nk_free 24 w0 (II' w0 NV))). rewrite (II' w0 NV).
split; [apply (art_malloc_free_in 24 cl24 Hc0 OK0 w0 OKp V' Nw); intros V; contradiction|].
pose proof (art_cptr_new_lo 8192 (cl_au cl24) _ w0 ltac:(lia) Hka0 V' NV) as Hlo. pose proof V' as (V0 & V1 & _).
destruct OKp as (_ & (_ & Haumu') & _).
destruct (Z_lt_ge_dec (16 * w0) (cl_mu cl24)) as [Lo|Hi]; [apply TT; [lia|]|apply NEWB; [lia|]]; replace (16 * w0) with (2 * w0 * 8) by lia; apply Z_mod_mult.
-
subst c0. unfold art_enq_cls. fold cl24 in I0, II, II', III, TT.
assert (NA : forall w0, ~ (newb = true /\ 24 = 24 /\ w0 = wb)) by (intros w0 (X & _); rewrite En in X; discriminate).
split; [exact TT|]. split; [intros w0 Hin0; rewrite (art_frep_st_other 24 w0 (NA w0) (art_frep_nk_free 24 w0 (II w0 Hin0))); exact (II w0 Hin0)|].
split; [intros w0 NV; rewrite (art_frep_st_other 24 w0 (NA w0) (art_frep_nk_free 24 w0 (II' w0 NV))); exact (II' w0 NV)|].
intros w0 V. exact (art_frep_old_chunk 24 w0 Hc0 V (NA w0)).
-
assert (NA : forall w0, ~ (newb = true /\ c0 = 24 /\ w0 = wb)) by (intros w0 (_ & X & _); exact (N24 X)).
split; [exact TT|]. split; [intros w0 Hin0; rewrite (art_frep_st_other c0 w0 (NA w0) (art_frep_nk_free c0 w0 (II w0 Hin0))); exact (II w0 Hin0)|].
split; [intros w0 NV; rewrite (art_frep_st_other c0 w0 (NA w0) (art_frep_nk_free c0 w0 (II' w0 NV))); exact (II' w0 NV)|].
intros w0 V. exact (art_frep_old_chunk c0 w0 Hc0 V (NA w0)).
Qed.
#[using="LB M b1 qtl cl24 newb wb b lastb L B cntB REP Edep"] Lemma art_frep_au_mono : forall c0, 1 <= c0 <= 30 -> cl_au (g_cls FSG G c0) <= cl_au (g_cls FSG G' c0).
Proof.
intros c0 Hc0. unfold G'. cbn [art_gs_free g_cls]. fold qtl. fold newb. fold cl24. destruct (Z.eqb_spec c0 24) as [->|N]; [|lia]. fold cl24.
unfold art_enq_cls. destruct (Bool.bool_dec newb true) as [En|En]; [rewrite En|apply Bool.not_true_is_false in En; rewrite En; lia].
cbn [art_cls_pop cl_au]. pose proof REP as (_ & _ & _ & (_ & PRIM & _) & _). destruct (PRIM 24 ltac:(lia)) as (_ & OK & _). fold cl24 in OK.
destruct OK as (_ & (Hau0 & Haumu0) & _). destruct (art_ca_pre_au 24 cl24) as [E0|(_ & _ & E0)]; rewrite E0; [lia|].
assert (0 <= art_cls_new 24 cl24 * AsanTab.class_size 24); [|lia]. apply Z.mul_nonneg_nonneg; [|rewrite art_class_size_24; lia].
unfold art_cls_new. apply Z.div_pos; [|rewrite art_class_size_24; lia]. lia.
Qed.
#[using="M b1 qtl cl24 newb wb b lastb L B cntB REP KIND Edep OKpre Hother"] Lemma art_frep_blocks : art_rt_blocks FSG rn G' (lb_remove u LB).
Proof.
pose proof REP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & BLK & _). intros b0 Hb0. destruct (Hother b0 Hb0) as (Hb0' & Nu).
destruct (BLK b0 Hb0') as [(c0 & w0 & Hc0 & V & St)|(s & Hs & Hq & Es & En)].
- left. exists c0, w0. split; [exact Hc0|]. split; [eapply art_cptr_mono; [exact (art_frep_au_mono c0 Hc0)|exact V]|].
rewrite art_frep_st_other; [exact St| |].
+ intros (E & -> & ->). rewrite (art_frep_wb_free E) in St. discriminate.
+ destruct k as [c w|i]; [|exact I]. intros (-> & ->). destruct KIND as (_ & _ & St'). rewrite St in St'. injection St' as E1 _. exact (Nu E1).
- right. unfold G'. cbn [art_gs_free g_sec]. destruct k as [c w|i]; [exists s; repeat split; assumption|].
destruct KIND as (si & Hsi & _ & Esu & _). exists s. split; [|repeat split; assumption].
apply (art_sec_quar_in_other i _ si s Hsi Hs). rewrite Es, Esu. exact Nu.
Qed.
#[using="LIVE"] Lemma art_frep_live_far : forall p, In p (art_live (g_log FSG G)) ->
0 < fst p /\ 0 < snd p /\ fst p + snd p <= rn_HI rn /\ (fst p + snd p <= 0x7fff7000 \/ 0x10007fff8000 <= fst p)
/\ apart (fst p) (snd p) (rn_t rn) 4096 /\ apart (fst p) (snd p) (rn_kbase rn) 0x2000011000 /\ apart (fst p) (snd p) (rn_l2 rn) (2 ^ 20)
/\ apart (fst p) (snd p) (rn_blk rn) (2 ^ 23) /\ (fst p + snd p <= 0x10000 \/ 0x693000 <= fst p).
Proof.
intros p Hp. destruct (LIVE p Hp) as (P0 & P1 & P2 & P3 & PO).
pose proof (PO _ (or_introl eq_refl)) as At. pose proof (PO _ (or_intror (or_intror (or_introl eq_refl)))) as Ak.
pose proof (PO _ (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))) as Al.
pose proof (PO _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))) as Ab.
pose proof (PO _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))))) as Ai1.
pose proof (PO _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))))))) as Ai2.
pose proof (PO _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))))))) as Ai3.
pose proof (PO _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))))))))) as Ai4.
cbn [fst snd] in At, Ak, Al, Ab, Ai1, Ai2, Ai3, Ai4.
split; [exact P0|]. split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact At|]. split; [exact Ak|]. split; [exact Al|]. split; [exact Ab|].
unfold apart in Ai1, Ai2, Ai3, Ai4. clear - P1 Ai1 Ai2 Ai3 Ai4. lia.
Qed.
Section SE.
Local Abbreviation SEC_T_art_fgap_grant_sub := (forall p a len, In p (art_live (g_log FSG G)) -> fst p <= a -> a + len <= fst p + snd p ->
(a + len <= u - 16 \/ (u - 12 <= a /\ a + len <= u) \/ u + 8 <= a) -> art_gap art_frep_W a len) (only parsing).
Variable p : ltac:(sec_ty2 constr:(SEC_T_art_fgap_grant_sub) 0%nat 0%nat).
Variable a : ltac:(sec_ty2 constr:(SEC_T_art_fgap_grant_sub) 1%nat 0%nat).
Variable len : ltac:(sec_ty2 constr:(SEC_T_art_fgap_grant_sub) 2%nat 0%nat).
#[using="LB M n b1 kb k qtl cl24 wb b lastb L B cntB REP Eu Hn Hqr Hb1 KIND Edep LIVE LIVE2 LIVE3 p a len"] Lemma art_fgap_grant_sub : ltac:(sec_stmt2 constr:(SEC_T_art_fgap_grant_sub) 3%nat 0%nat).
Proof.
intros Hp Ha Hl Hu.
destruct (art_frep_live_far p Hp) as (P0 & P1 & P2 & P3 & At & Ak & Al & Ab & Ai). destruct art_frep_ush as (S1 & S2).
pose proof REP as (ROK & _). rok_open14 ROK. geo_open GEO.
unfold art_frep_W. cbn [art_gap fst snd]. unfold apart in *. clear - Ha Hl Hu P0 P1 P2 P3 At Ak Al Ab Ai S1 S2 G1 G2 G4 G6 Espb Eris Kspb Kend. repeat split; try exact I; lia.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_fgap_sh := (ltac2:(TCodec.tc2 tcn__JbtInvFree "QN'E&R8zr3%3221&R9%1243&R7r5r4%3221&QCvS3%211%=241'Cr6%:219&QH%117%C231+TPPPRTP0%?231%F217%9241'?&Q1r7%211%L21E&R>%H24?+1%3221%811%Q22K1%;271&B+QoooPP0&R;+2vS0%3221%Q4251%Q;21LvS1%Q7231%Q:2O1%G241%<11&Q:&R2%231IDp041p0B1p0O1p0Q:1p0QC1p0QF1pU0QK1pUJQL1pULQM1")) (only parsing).
Variable lo : ltac:(sec_ty2 constr:(SEC_T_art_fgap_sh) 0%nat 0%nat).
Variable len : ltac:(sec_ty2 constr:(SEC_T_art_fgap_sh) 1%nat 0%nat).
Variable a : ltac:(sec_ty2 constr:(SEC_T_art_fgap_sh) 2%nat 0%nat).
#[using="FSG G LB M n b1 kb k qtl cl24 wb b lastb L B cntB REP Eu Hn Hqr Hb1 KIND Edep LIVE LIVE2 LIVE3 lo len a"] Lemma art_fgap_sh : ltac:(sec_stmt2 constr:(SEC_T_art_fgap_sh) 3%nat 0%nat).
Proof.
intros Hlo Hlen Hhi Hk Ha Hus.
destruct art_frep_u_far as (_ & _ & _ & Ush & _).
pose proof REP as (ROK & _). rok_open14 ROK. geo_open GEO.
pose proof (art_S_ge lo 0 ltac:(lia)) as B0. pose proof (art_S_lt (lo + len - 1) (2 ^ 44) ltac:(clear - Hhi G2; lia)) as B1.
assert (B2 : a < 2147450880 + 8192 * rn_qs rn + 24 * 2 ^ 29 \/ 2147450880 + 8192 * rn_qs rn + 25 * 2 ^ 29 <= a).
{ destruct Hk as [Hk|Hk].
- left. pose proof (art_S_lt (lo + len - 1) (8192 * rn_qs rn) ltac:(clear - Hk Kspb Espb; lia)) as X. clear - X Ha. lia.
- right. pose proof (art_S_ge lo (8192 * rn_qs rn + 2 ^ 34) ltac:(clear - Hk Kspb Espb; lia)) as X. clear - X Ha. lia. }
unfold art_frep_W. cbn [art_gap fst snd]. unfold apart in G10, Al2s, Abs |- *. clear - Ha B0 B1 B2 Hus Ush G1 G4 G9 G10 Espb Eris Al2s Abs Il2 Iblk Hn Hqr. repeat split; try exact I; lia.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_fgap_parr := (ltac2:(TCodec.tc2 tcn__JbtInvFree "H'E&R8&QJvS3%211r2%5221&R7r3%2214&R=+2+G%3221%72:1%>261&Q:&R2r4%3321;p051p0?1pUJF1pU0G1")) (only parsing).
Variable a : ltac:(sec_ty2 constr:(SEC_T_art_fgap_parr) 0%nat 0%nat).
Variable len : ltac:(sec_ty2 constr:(SEC_T_art_fgap_parr) 1%nat 0%nat).
#[using="FSG G LB M n b1 kb k qtl cl24 wb b lastb L B cntB REP Eu Hn Hqr Hb1 KIND Edep LIVE LIVE2 LIVE3 a len"] Lemma art_fgap_parr : ltac:(sec_stmt2 constr:(SEC_T_art_fgap_parr) 2%nat 0%nat).
Proof.
intros Ha Hl.
destruct art_frep_u_far as (_ & _ & _ & _ & _ & _ & _ & _ & Up & _). destruct art_frep_ush as (S1 & S2).
pose proof REP as (ROK & _). rok_open14 ROK. geo_open GEO. destruct Papp as (_ & Pap & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in Pap.
unfold art_frep_W. cbn [art_gap fst snd]. unfold apart in *.
clear - Ha Hl Up S1 S2 G1 G2 G4 G6 Espb Eris Plo Phi Pap Apt Apk Apl Apb Hn Hqr. repeat split; try exact I; lia.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_frep_grant_off := (forall p, In p (art_live (g_log FSG G)) ->
match k with FKP _ _ => True | FKS i => forall s, nth_error (g_sec FSG G) i = Some s -> fst p <> sc_map s end ->
fst p + snd p <= u - 16 \/ u + 8 * qr <= fst p) (only parsing).
Variable p : ltac:(sec_ty2 constr:(SEC_T_art_frep_grant_off) 0%nat 0%nat).
#[using="rn LB M n q16 b1 kb qtl cl24 wb b lastb L B cntB REP Eu Hn Hqr Hb1 KIND Edep LIVE LIVE2 LIVE3 p"] Lemma art_frep_grant_off : ltac:(sec_stmt2 constr:(SEC_T_art_frep_grant_off) 1%nat 0%nat).
Proof.
intros Hp Hk.
destruct (art_frep_live_far p Hp) as (P0 & P1 & P2 & P3 & At & Ak & Al & Ab & Ai).
pose proof REP as (ROK & _). rok_open14 ROK. geo_open GEO. pose proof art_frep_where as WH. unfold art_free_where in WH. pose proof art_frep_sec_p as SECP.
destruct k as [c w|i].
- destruct KIND as (Hc & (V0 & V1 & _) & _). destruct WH as (L1 & L2).
pose proof REP as (_ & _ & _ & (_ & PRIM & _) & _). destruct (PRIM c Hc) as (_ & OK & _). destruct OK as (_ & (Hau0 & Haumu) & _ & _ & _ & Hmu3 & _).
pose proof (art_class_size_facts c Hc) as (Hsz & Hsz16). rewrite <- (Z.div_exact _ 16) in Hsz16 by lia.
assert (Hend : u + 8 * qr <= rn_spb rn + c * 2 ^ 32 + 16 * w + AsanTab.class_size c) by (clear - L2 Hsz16 Espb Eu Hn Hqr; lia).
assert (LO : rn_spb rn + 2 ^ 32 <= u - 16) by (clear - L1 Hc V0; lia).
assert (HIu' : u + 8 * qr <= rn_spb rn + 31 * 2 ^ 32) by (clear - Hend V1 Haumu Hmu3 Hc; lia).
unfold apart in Ak. clear - Ak LO HIu' Kspb Kend P1. lia.
- destruct WH as (pi & Hpi & L1 & L2). destruct KIND as (s & Hs & _ & Esu & Esn).
assert (E : fst pi = sc_map s) by (apply (SECP s pi i Hs Hpi); [rewrite Esu; exact L1|rewrite Esu, Esn; exact L2|rewrite Esn; clear - Hn; lia]).
specialize (Hk s Hs). destruct (LIVE3 pi Hpi) as (A1 & A2). rewrite <- (Z.div_exact _ 4096) in A1 by lia. rewrite <- (Z.div_exact _ 4096) in A2 by lia.
assert (Hend : u + 8 * qr <= fst pi + snd pi) by (clear - L2 A1 A2 Eu Hn Hqr; lia).
pose proof (LIVE2 p pi Hp Hpi ltac:(rewrite E; exact Hk)) as AP. unfold apart in AP. clear - AP L1 Hend P1. lia.
Qed.
End SE.
#[using="Eu"] Lemma art_frep_ush_off : ltac2:(TCodec.tc2 tcn__JbtInvFree "Q?'E'C&R8&R7r3r2%3221&R>vS6+@%3221%9251&R;+8vS1%3221%=281%?21=%A271'?&Q1r4%211%E21B%E23D+1%C221%711%J2G1%:261&B+QoooPP0+2vS0%F221%Q0241%Q221Q0&R9%Q323H%22Q31%E241%;11p0=1p0I1pU0Q<1pUJQ=1pULQ>1").
Proof.
intros lo len a Hoff Ha X. destruct Hoff as [Hoff|Hoff].
- pose proof (art_S_lt (lo + len - 1) (2 * q16) ltac:(clear - Hoff Eu; lia)) as Bd. clear - Bd Ha X. lia.
- pose proof (art_S_ge lo (2 * q16 + qr) ltac:(clear - Hoff Eu; lia)) as Bd. clear - Bd Ha X. lia.
Qed.
#[using="rn LB Sp n q16 qr b1 km kb k qtl cl24 newb wb b lastb L B cntB REP Eu Hn Hqr Hb1 KIND HS Emu Edep OUT LIVE LIVE2 LIVE3 OKpre"] Lemma art_frep_far_cell : forall p a (j : nat) v, In p (art_live (g_log FSG G)) -> fst p <= a -> a + Z.of_nat j <= fst p + snd p ->
(a + Z.of_nat j <= u - 16 \/ (u - 12 <= a /\ a + Z.of_nat j <= u) \/ u + 8 <= a) -> cellA M a j v -> cellA M' a j v.
Proof.
intros p a j v Hp Ha Hl Hu C. destruct (art_frep_live_far p Hp) as (P0 & P1 & P2 & _).
pose proof REP as (ROK & _). destruct ROK as (GEO & _). geo_open GEO.
apply (art_cell_tr art_frep_W M M' a j v art_frep_agree (art_fgap_grant_sub p a (Z.of_nat j) Hp Ha Hl Hu)); [clear - P0 Ha; lia|clear - Hl P2 G2; lia|exact C].
Qed.
#[using="rn LB Sp n q16 b1 km kb k qtl cl24 newb wb b lastb L B cntB REP Eu Hn Hqr Hb1 KIND HS Emu Edep OUT LIVE LIVE2 LIVE3 OKpre"] Lemma art_frep_far_hdr : forall p u0 n0 st, In p (art_live (g_log FSG G)) -> fst p + 16 <= u0 -> u0 + n0 <= fst p + snd p ->
(fst p + snd p <= u - 16 \/ u + 8 * qr <= fst p) -> art_chunk_hdr M u0 n0 st -> art_chunk_hdr M' u0 n0 st.
Proof.
intros p u0 n0 st Hp L1 L2 Off (bb & Hb & Hbt & C1 & C2 & Hn0). assert (Hq0 : 1 <= qr) by (clear - Hn Hqr; lia).
exists bb. split; [exact Hb|]. split; [exact Hbt|]. split; [|split; [|exact Hn0]].
- apply (art_frep_far_cell p (u0 - 16) 4%nat _ Hp); [clear - L1; lia|cbn; clear - L2 Hn0; lia|cbn; clear - Off L1 L2 Hn0 Hq0; lia|exact C1].
- apply (art_frep_far_cell p (u0 - 12) 4%nat _ Hp); [clear - L1; lia|cbn; clear - L2 Hn0; lia|cbn; clear - Off L1 L2 Hn0 Hq0; lia|exact C2].
Qed.
#[using="rn LB Sp n q16 b1 km kb k qtl cl24 newb wb b lastb L B cntB REP Eu Hn Hqr Hb1 KIND HS Emu Edep OUT LIVE LIVE2 LIVE3 OKpre"] Lemma art_frep_far_shadow : forall p u0 n0, In p (art_live (g_log FSG G)) -> fst p <= u0 -> u0 + n0 <= fst p + snd p -> 0 < n0 ->
(fst p + snd p <= u - 16 \/ u + 8 * qr <= fst p) -> HAJ.shadow_blkR M u0 n0 -> HAJ.shadow_blkR M' u0 n0.
Proof.
intros p u0 n0 Hp L1 L2 Hn0 Off SB0. destruct (art_frep_live_far p Hp) as (Q0 & Q1 & Q2 & _ & _ & Ak & _).
pose proof REP as (ROK & _). destruct ROK as (GEO & _). geo_open GEO.
assert (TBY : forall j, 0 <= j -> (j < n0 / 8 \/ (j = n0 / 8 /\ n0 mod 8 <> 0)) -> forall v, byte_at M (HeapIfaceA.S u0 + j) v -> byte_at M' (HeapIfaceA.S u0 + j) v).
{ intros j Hj0 Hj v Bt. apply (art_byte_at_eq M M'); [|exact Bt]. apply art_frep_agree.
pose proof (art_S_ge u0 0 ltac:(clear - Q0 L1; lia)) as B0. pose proof (art_S_blk_hi u0 n0 j Hn0 Hj) as B1.
pose proof (art_S_lt (u0 + n0 - 1) (2 ^ 44) ltac:(clear - L2 Q2 G2; lia)) as B2.
assert (RG : HeapIfaceA.S u0 <= HeapIfaceA.S u0 + j <= HeapIfaceA.S (u0 + n0 - 1)) by (clear - Hj0 B1; lia).
rewrite art_u_lit by (clear - B0 B2 RG; lia). apply (art_gap_out _ (HeapIfaceA.S u0 + j) 1); [|clear; lia].
apply (art_fgap_sh u0 n0 _ ltac:(clear - Q0 L1; lia) Hn0 ltac:(clear - L2 Q2; lia)); [unfold apart in Ak; clear - Ak L1 L2 Hn0; lia|exact RG|].
apply (art_frep_ush_off u0 n0); [clear - Off L1 L2; lia|exact RG]. }
exact (shadow_blkR_tby M M' u0 n0 Hn0 TBY SB0).
Qed.
#[using="qtl cl24 newb"] Lemma art_frep_live_eq : art_live (g_log FSG G') = art_live (g_log FSG G).
Proof.
unfold G'. cbn [art_gs_free g_log]. fold qtl. fold newb. fold cl24. unfold art_enq_events.
destruct (Bool.bool_dec newb true) as [En|En]; [rewrite En; apply art_live_ca_events|apply Bool.not_true_is_false in En; rewrite En, app_nil_r; reflexivity].
Qed.
#[using="M Sp q16 qr b1 km qtl cl24 newb wb b lastb L B cntB REP Eu Hn Hqr Hb1 Hty Cn KIND HS Emu Edep OUT LIVE LIVE2 LIVE3 OKpre"] Lemma art_frep_sec : art_rt_sec FSG rn G' (lb_remove u LB) M'.
Proof.
pose proof REP as (ROK & _ & _ & _ & _ & SEC & _). rok_open14 ROK. pose proof GEO as GEO'. geo_open GEO'.
destruct SEC as (C1 & C2 & C3 & C4 & C5 & C6 & S1 & S2 & SALL & SLIVE & SLEN). destruct art_frep_out as (GR & _ & _ & CHW & _).
assert (ELEN : length (g_sec FSG G') = length (g_sec FSG G)). { unfold G'. cbn [art_gs_free g_sec]. destruct k; [reflexivity|apply art_sec_quar_length]. }
assert (Hq0 : 1 <= qr) by (clear - Hn Hqr; lia).
unfold art_rt_sec. rewrite art_frep_live_eq, ELEN. change (g_sec_committed FSG G') with (g_sec_committed FSG G).
split; [apply art_frep_cell_img; [cbn; lia|exact C1]|]. split; [apply art_frep_cell_img; [cbn; lia|exact C2]|].
split; [apply art_frep_cell_img; [cbn; lia|exact C3]|]. split; [apply art_frep_cell_img; [cbn; lia|exact C4]|].
split; [apply art_frep_cell_img; [cbn; lia|exact C5]|]. split; [apply art_frep_cell_img; [cbn; lia|exact C6]|].
split. { intros NE. apply S1. intros E. apply NE. apply length_zero_iff_nil. rewrite ELEN, E. reflexivity. }
split; [intros E; eapply wr_grows; [exact GR|exact (S2 E)]|].
split; [|split; [|exact SLEN]].
2: { intros p Hp. destruct (SLIVE p Hp) as (s & Hs & Ep). unfold G'. cbn [art_gs_free g_sec]. destruct k as [c w|i]; [exists s; split; assumption|].
destruct (In_nth_error _ _ Hs) as (j & Hj). destruct (Nat.eq_dec j i) as [->|Nj].
- exists (SEC (sc_map s) (sc_msize s) (sc_u s) (sc_n s) true). split; [eapply nth_error_In; apply art_sec_quar_nth_same; exact Hj|exact Ep].
- exists s. split; [eapply nth_error_In; rewrite art_sec_quar_nth_other by exact Nj; exact Hj|exact Ep]. }
intros i0 s' Hi0.
assert (ORIG : exists s, nth_error (g_sec FSG G) i0 = Some s /\ sc_map s' = sc_map s /\ sc_msize s' = sc_msize s /\ sc_u s' = sc_u s /\ sc_n s' = sc_n s
/\ ((exists i, k = FKS i /\ i0 = i /\ sc_quar s' = true /\ sc_u s = u /\ sc_n s = n)
\/ (sc_quar s' = sc_quar s /\ match k with FKP _ _ => True | FKS i => i0 <> i end))).
{ unfold G' in Hi0. cbn [art_gs_free g_sec] in Hi0. destruct k as [c w|i].
- exists s'. repeat split; try reflexivity; [exact Hi0|right; split; [reflexivity|exact I]].
- destruct (Nat.eq_dec i0 i) as [->|Ni].
+ destruct KIND as (si & Hsi & Hq & Esu & Esn). rewrite (art_sec_quar_nth_same i _ si Hsi) in Hi0. injection Hi0 as <-. exists si. cbn [sc_map sc_msize sc_u sc_n sc_quar].
repeat split; try reflexivity; [exact Hsi|]. left. exists i. repeat split; try reflexivity; assumption.
+ rewrite (art_sec_quar_nth_other i _ i0 Ni) in Hi0. exists s'. repeat split; try reflexivity; [exact Hi0|right; split; [reflexivity|exact Ni]]. }
destruct ORIG as (s & Hs & Em & Ems & Eus & Ens & CASE). rewrite Em, Ems, Eus, Ens.
destruct (SALL i0 s Hs) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10).
assert (Hil : Z.of_nat i0 < Z.of_nat (length (g_sec FSG G))). { apply Nat2Z.inj_lt. apply nth_error_Some. rewrite Hs. discriminate. }
destruct (art_frep_live_far _ P2) as (L0 & L1 & L2 & _). cbn [fst snd] in L0, L1, L2.
assert (Hn0s : 1 <= sc_n s). { destruct (sc_quar s); [destruct P9 as ((bb & _ & _ & _ & _ & H) & _)|destruct P9 as (_ & (bb & _ & _ & _ & _ & H) & _)]; lia. }
assert (HDRP : forall a, sc_map s <= a -> a + 8 <= sc_map s + 32 -> a + 8 <= u - 16 \/ (u - 12 <= a /\ a + 8 <= u) \/ u + 8 <= a).
{ intros a Ha Ha'. destruct CASE as [(i & Ek & -> & _ & Esu & _)|(_ & Hk)].
- left. clear - Ha' P7 Esu. lia.
- assert (OFF : fst (sc_map s, sc_msize s) + snd (sc_map s, sc_msize s) <= u - 16 \/ u + 8 * qr <= fst (sc_map s, sc_msize s)).
{ apply (art_frep_grant_off _ P2). destruct k as [c w|i]; [exact I|]. intros si Hsi E. cbn [fst] in E. apply Hk.
destruct (SALL i si Hsi) as (_ & _ & _ & _ & _ & Q6 & _). rewrite <- E in Q6.
assert (Hil' : Z.of_nat i < Z.of_nat (length (g_sec FSG G))). { apply Nat2Z.inj_lt. apply nth_error_Some. rewrite Hsi. discriminate. }
pose proof (cell8_inj M _ _ _ P6 Q6 ltac:(clear - Hil SLEN; lia) ltac:(clear - Hil' SLEN; lia)) as EI. apply Nat2Z.inj. exact EI. }
cbn [fst snd] in OFF. clear - OFF Ha Ha' P7 P8 Hn0s Hq0. lia. }
split. { apply (art_cell_tr art_frep_W M M' _ 8%nat _ art_frep_agree (art_fgap_parr (rn_parr rn + 8 * Z.of_nat i0) 8 ltac:(clear; lia) ltac:(clear - Hil SLEN; lia))); [clear - Plo; lia|cbn; clear - Phi G2 Hil SLEN; lia|exact P1]. }
split; [exact P2|]. split; [eapply wr_grows; [exact GR|exact P3]|].
split. { apply (art_frep_far_cell (sc_map s, sc_msize s) _ 8%nat _ P2); [cbn; clear; lia|cbn; clear - P7 P8 Hn0s; lia|cbn; apply HDRP; clear; lia|exact P4]. }
split. { apply (art_frep_far_cell (sc_map s, sc_msize s) _ 8%nat _ P2); [cbn; clear; lia|cbn; clear - P7 P8 Hn0s; lia|cbn; apply HDRP; clear; lia|exact P5]. }
split. { apply (art_frep_far_cell (sc_map s, sc_msize s) _ 8%nat _ P2); [cbn; clear; lia|cbn; clear - P7 P8 Hn0s; lia|cbn; apply HDRP; clear; lia|exact P6]. }
split; [exact P7|]. split; [exact P8|]. split; [|exact P10].
destruct CASE as [(i & Ek & -> & Eq' & Esu & Esn)|(Eq' & Hk)]; rewrite Eq'.
-
rewrite Esu, Esn. rewrite Esu in P7. rewrite Esu, Esn in P8. split.
+ exists b1. split; [exact Hb1|]. split; [exact Hty|]. split; [exact CHW|]. split; [|exact Hn].
apply (art_frep_far_cell (sc_map s, sc_msize s) (u - 12) 4%nat _ P2); [cbn; clear - P7; lia|cbn; clear - P8 Hn; lia|cbn; right; left; clear; lia|exact Cn].
+ exact (art_in_batches_new qtl (g_qg FSG G) b (u - 16, n)).
- assert (OFF : sc_map s + sc_msize s <= u - 16 \/ u + 8 * qr <= sc_map s).
{ apply (art_frep_grant_off _ P2). destruct k as [c w|i]; [exact I|]. intros si Hsi E. cbn [fst] in E. apply Hk.
destruct (SALL i si Hsi) as (_ & _ & _ & _ & _ & Q6 & _). rewrite <- E in Q6.
assert (Hil' : Z.of_nat i < Z.of_nat (length (g_sec FSG G))). { apply Nat2Z.inj_lt. apply nth_error_Some. rewrite Hsi. discriminate. }
pose proof (cell8_inj M _ _ _ P6 Q6 ltac:(clear - Hil SLEN; lia) ltac:(clear - Hil' SLEN; lia)) as EI. apply Nat2Z.inj. exact EI. }
destruct (sc_quar s).
+ destruct P9 as (Q1 & Q2). split; [|exact (art_in_batches_add qtl (g_qg FSG G) b (u - 16, n) _ _ Q2)].
apply (art_frep_far_hdr (sc_map s, sc_msize s) _ _ _ P2); [cbn; clear - P7; lia|cbn; exact P8|cbn; exact OFF|exact Q1].
+ destruct P9 as (Q1 & Q2 & Q3). split; [|split].
* apply art_lb_remove_keep0; [exact Q1|]. cbn [fst]. clear - OFF P7 P8 Hn0s Hq0. lia.
* apply (art_frep_far_hdr (sc_map s, sc_msize s) _ _ _ P2); [cbn; clear - P7; lia|cbn; exact P8|cbn; exact OFF|exact Q2].
* apply (art_frep_far_shadow (sc_map s, sc_msize s) _ _ P2); [cbn; clear - P7; lia|cbn; exact P8|clear - Hn0s; lia|cbn; exact OFF|exact Q3].
Qed.
#[using="FSG rn G LB M M' Sp u n q16 qr b1 km kb k qtl cl24 lastb L B cntB Hin Eu Cn KIND OUT Hother"] Lemma art_nodup_insert : forall (A : Type) (l1 l2 : list A) x, List.NoDup (l1 ++ l2) -> ~ In x (l1 ++ l2) -> List.NoDup (l1 ++ x :: l2).
Proof.
intros A l1 l2 x. induction l1 as [|y r IH]; cbn [app]; intros ND NI.
- constructor; assumption.
- inversion ND as [|? ? Hy ND']; subst. constructor.
+ intros Hi0. apply in_app_or in Hi0. destruct Hi0 as [Hi0|[->|Hi0]]; [apply Hy; apply in_or_app; left; exact Hi0|apply NI; left; reflexivity|apply Hy; apply in_or_app; right; exact Hi0].
+ apply IH; [exact ND'|]. intros Hi0. apply NI. right. exact Hi0.
Qed.
#[using="FSG rn G LB M M' Sp u n q16 qr b1 km kb k qtl cl24 lastb L B cntB Hin Eu Cn KIND OUT Hother"] Lemma art_nodup_map_app : forall (A : Type) (f : A -> Z) (l1 l2 : list A) a1 a2, List.NoDup (map f (l1 ++ l2)) -> In a1 l1 -> In a2 l2 -> f a1 <> f a2.
Proof.
intros A f l1 l2 a1 a2. induction l1 as [|y r IH]; intros ND H1 H2; [contradiction|]. cbn [app map] in ND. inversion ND as [|? ? Hy ND']; subst.
destruct H1 as [->|H1]; [|exact (IH ND' H1 H2)]. intros E. apply Hy. rewrite E. apply in_map. apply in_or_app. right. exact H2.
Qed.
#[using="Type"] Lemma art_batch_list_last_cells : ltac2:(TCodec.tc2 tcn__JbtInvFree "R2'S4yR0%211';y8%511%311p051'8'Q=%211'E&Q>r5&2r4(4r3(:%11:%43;31%73<61r2r1%<4;321'9'<%12@@'@%J12&R6&QBr6%211%4371<(1%129=%93831&M&R3r9&R7&QAr7%211+H%5221&R;+8&R<%11Q1%4231%;261u8&6%13Q<Q<Q1%B5A@431p0D1pU@O1pUBQ21p0Q41pUFQB1pU<QC1pUHQF1pV6QF1pQHQJ1").
Proof.
intros M0 r. induction r as [|x r' IH]; intros lb f l BL j it Hj.
- cbn [app art_batch_list] in BL. destruct BL as (_ & _ & _ & _ & CI & _). exact (CI j it Hj).
- change ((x :: r') ++ [lb]) with (x :: (r' ++ [lb])) in BL. cbn [art_batch_list] in BL. destruct BL as (_ & _ & _ & _ & _ & _ & R). exact (IH lb _ _ R j it Hj).
Qed.
Section SE.
Local Abbreviation SEC_T_art_frep_sec_u_inj := (forall j1 j2 s1 s2, nth_error (g_sec FSG G) j1 = Some s1 -> nth_error (g_sec FSG G) j2 = Some s2 -> sc_u s1 = sc_u s2 -> j1 = j2) (only parsing).
Variable j1 : ltac:(sec_ty2 constr:(SEC_T_art_frep_sec_u_inj) 0%nat 0%nat).
Variable j2 : ltac:(sec_ty2 constr:(SEC_T_art_frep_sec_u_inj) 1%nat 0%nat).
Variable s1 : ltac:(sec_ty2 constr:(SEC_T_art_frep_sec_u_inj) 2%nat 0%nat).
Variable s2 : ltac:(sec_ty2 constr:(SEC_T_art_frep_sec_u_inj) 3%nat 0%nat).
#[using="rn LB M b1 kb qtl cl24 wb b lastb L B cntB REP Edep LIVE2 j1 j2 s1 s2"] Lemma art_frep_sec_u_inj : ltac:(sec_stmt2 constr:(SEC_T_art_frep_sec_u_inj) 4%nat 0%nat).
Proof.
intros H1 H2 E.
destruct REP as (_ & _ & _ & _ & _ & SECR & _). destruct SECR as (_ & _ & _ & _ & _ & _ & _ & _ & SALL & _ & SLEN).
destruct (SALL j1 s1 H1) as (_ & P2 & _ & _ & _ & P6 & P7 & P8 & P9 & _). destruct (SALL j2 s2 H2) as (_ & Q2 & _ & _ & _ & Q6 & Q7 & Q8 & Q9 & _).
assert (N1 : 1 <= sc_n s1). { destruct (sc_quar s1); [destruct P9 as ((bb & _ & _ & _ & _ & H) & _)|destruct P9 as (_ & (bb & _ & _ & _ & _ & H) & _)]; lia. }
assert (N2 : 1 <= sc_n s2). { destruct (sc_quar s2); [destruct Q9 as ((bb & _ & _ & _ & _ & H) & _)|destruct Q9 as (_ & (bb & _ & _ & _ & _ & H) & _)]; lia. }
assert (L1 : Z.of_nat j1 < Z.of_nat (length (g_sec FSG G))). { apply Nat2Z.inj_lt. apply nth_error_Some. rewrite H1. discriminate. }
assert (L2 : Z.of_nat j2 < Z.of_nat (length (g_sec FSG G))). { apply Nat2Z.inj_lt. apply nth_error_Some. rewrite H2. discriminate. }
destruct (Z.eq_dec (sc_map s1) (sc_map s2)) as [Em|Nm].
- rewrite Em in P6. pose proof (cell8_inj M _ _ _ P6 Q6 ltac:(clear - L1 SLEN; lia) ltac:(clear - L2 SLEN; lia)) as EI. apply Nat2Z.inj. exact EI.
- exfalso. pose proof (LIVE2 _ _ P2 Q2 Nm) as AP. cbn [fst snd] in AP. unfold apart in AP. clear - AP P7 P8 Q7 Q8 N1 N2 E. lia.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_frep_batch_eq := (forall b0 (x : word), In b0 (g_qt FSG G ++ g_qg FSG G) -> bt_addr b0 <= U x < bt_addr b0 + 8192 ->
(L <> 0 -> bt_addr b0 = B -> ~ art_B_written (U x)) -> M' x = M x) (only parsing).
Variable b0 : ltac:(sec_ty2 constr:(SEC_T_art_frep_batch_eq) 0%nat 0%nat).
Variable x : ltac:(sec_ty2 constr:(SEC_T_art_frep_batch_eq) 1%nat 0%nat).
#[using="rn LB Sp u n q16 qr b1 km kb k cl24 wb b REP Eu Hn Hqr Hb1 KIND HS Emu Edep OUT LIVE LIVE3 OKpre b0 x"] Lemma art_frep_batch_eq : ltac:(sec_stmt2 constr:(SEC_T_art_frep_batch_eq) 2%nat 0%nat).
Proof.
intros Hb0 Hx NW.
destruct art_frep_num as (Hkm & Hkm' & Hbz & HBz & HnL).
pose proof REP as (ROK & _ & _ & (_ & PRIM & _) & _ & _ & QR & _). rok_open14 ROK. geo_open GEO.
destruct QR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & BCH). destruct (BCH b0 Hb0) as (w0 & Ew0 & V24 & St0). pose proof V24 as V. rewrite art_class_size_24 in V.
destruct (PRIM 24 ltac:(lia)) as (_ & OK0 & _). pose proof OK0 as (_ & (Hau0 & Haumu0) & _ & _ & _ & Hmu30 & _). pose proof V as (V0 & V1 & _).
assert (INCH : art_in_chunk 24 w0 (U x)). { unfold art_in_chunk. left. rewrite art_class_size_24. rewrite Ew0 in Hx. clear - Hx. lia. }
assert (Nk : match k with FKP c w => ~ (24 = c /\ w0 = w) | FKS _ => True end).
{ pose proof KIND as KD. destruct k as [c w|i]; [|exact I]. intros (<- & <-). destruct KD as (_ & _ & St'). rewrite St0 in St'. discriminate. }
pose proof (art_frep_uw_other 24 w0 (U x) ltac:(lia) V24 Nk INCH) as NUW. unfold art_uw in NUW.
pose proof art_frep_wb_free as WBF. pose proof art_frep_out as OUT'.
rewrite <- (Z_to_bv_bv_unsigned 64 x). apply (art_frep_eqa 24 (U x) ltac:(lia)).
- left. rewrite Ew0 in Hx. clear - Hx V0 V1 Haumu0. lia.
- intros X. apply NUW. left. exact X.
- intros X. apply NUW. right; left. exact X.
- intros X. apply NUW. right; right. exact X.
- intros _ E X.
assert (Nwb : w0 <> wb). { intros ->. rewrite (WBF E) in St0. discriminate. }
destruct OUT' as (_ & _ & _ & _ & _ & _ & _ & _ & OK' & NEW & _). destruct (NEW E) as (CPb & _).
assert (Hau' : cl_au cl24 <= cl_au (art_ca_pre 24 cl24)).
{ destruct (art_ca_pre_au 24 cl24) as [E0|(_ & _ & E0)]; rewrite E0; [lia|]. assert (0 <= art_cls_new 24 cl24 * AsanTab.class_size 24); [|lia].
apply Z.mul_nonneg_nonneg; [|rewrite art_class_size_24; lia]. unfold art_cls_new. apply Z.div_pos; [|rewrite art_class_size_24; lia]. unfold cl24. lia. }
pose proof (art_cptr_apart 8192 (cl_au (art_ca_pre 24 cl24)) w0 wb ltac:(clear; lia) (art_cptr_mono _ _ _ _ Hau' V) CPb Nwb) as AP.
unfold b in X. rewrite Ew0 in Hx. clear - X Hx AP. lia.
- intros _ NL X. destruct (Z.eq_dec (bt_addr b0) B) as [EB|NB]; [exact (NW NL EB X)|].
assert (InB : In lastb (g_qt FSG G ++ g_qg FSG G)). { apply in_or_app. left. unfold lastb, art_lastb. apply JbtFxQ.art_last_in. intros E. apply NL. unfold L, qtl. rewrite E. reflexivity. }
destruct (BCH lastb InB) as (wB & EwB & VB & _). rewrite art_class_size_24 in VB.
assert (Nw : w0 <> wB) by (intros ->; apply NB; unfold B; rewrite Ew0, EwB; reflexivity).
pose proof (art_cptr_apart 8192 (cl_au (g_cls FSG G 24)) w0 wB ltac:(clear; lia) V VB Nw) as AP.
assert (XW : B <= U x < B + 8192).
{ unfold art_B_written in X. destruct (HBz NL) as (_ & _ & X3). destruct (Bool.bool_dec newb true) as [E|E]; [rewrite E in X; clear - X; lia|].
apply Bool.not_true_is_false in E. rewrite E in X. destruct (art_free_newb_false qtl E) as (_ & X4). clear - X X3 X4. unfold cntB, lastb in *. lia. }
unfold B in XW. rewrite Ew0 in Hx. rewrite EwB in XW. clear - XW Hx AP. lia.
Qed.
End SE.
#[using="LB Sp u n q16 qr b1 km kb k cl24 wb b lastb L B cntB REP Eu Hn Hqr Hb1 KIND HS Emu Edep OUT LIVE LIVE2 LIVE3 OKpre"] Lemma art_frep_thq_room : ltac2:(TCodec.tc2 tcn__JbtInvFree "Q6'@'3vRO(5%43321'S4yR0%211'?&R8&R7&QNvS3%211+R@%5221&S5r1%22<1%:241&R9+S8%<291%3251%@251';y8%F11%311vJr2%211vI%113%Q23631p0;1pVBM1p0Q11").
Proof.
intros E x Hx. destruct art_frep_num as (Hkm & Hkm' & Hbz & HBz & HnL). destruct art_frep_u_far as (_ & _ & _ & _ & Ut & _). destruct art_frep_ush as (S1 & S2).
pose proof REP as (ROK & _). rok_open14 ROK. geo_open GEO. destruct (HBz (HnL E)) as (X1 & X2 & X3).
apply art_frep_lin. intros [F|F].
- unfold art_free3_fp, dprivD in F. unfold apart in Ut, G10, G11, Al2t, Abt. clear - F Hx Ut S1 S2 HS G1 G2 G8 G9 G10 Al2t Abt Hn Hqr. lia.
- unfold art_enq_fp in F. rewrite E in F. unfold apart in G11. clear - F Hx HS G1 G8 G11 X1 X2 X3. lia.
Qed.
#[using="LB Sp u n q16 qr b1 km kb k cl24 wb b lastb B cntB REP Eu Hn Hqr Hb1 KIND HS Emu Edep OUT LIVE LIVE2 LIVE3 OKpre"] Lemma art_frep_thq_first : ltac2:(TCodec.tc2 tcn__JbtInvFree "Q='@'3vRO(>%43321&B'EvFz%93321%511'S4yR0%211'?&R8&R7&QNvS3%211+RH%5221&S5r1%22<1%:241&R9+S0%<291%3251%@251';y8%F11%311vJr2%211vI%113%Q83631p0;1pVBM1p0Q11p0Q81").
Proof.
intros E NL x Hx. destruct art_frep_num as (Hkm & Hkm' & Hbz & HBz & HnL). destruct art_frep_u_far as (_ & _ & _ & _ & Ut & _). destruct art_frep_ush as (S1 & S2).
pose proof REP as (ROK & _). rok_open14 ROK. geo_open GEO. destruct (HBz NL) as (X1 & X2 & X3). specialize (Hbz E).
apply art_frep_lin. intros [F|F].
- unfold art_free3_fp, dprivD in F. unfold apart in Ut, G10, G11, Al2t, Abt. clear - F Hx Ut S1 S2 HS G1 G2 G8 G9 G10 Al2t Abt Hn Hqr. lia.
- unfold art_enq_fp in F. rewrite E in F. unfold art_enq_new_fp, art_refill_fp in F. unfold apart in G11, G10.
destruct F as [F|[[F|[F|[F|[F|[F|[F|[F|[F|[F|F]]]]]]]]]|[F|[F|[F|F]]]]]; try (clear - F Hx HS G1 G2 G4 G6 G8 G10 G11 Espb Eris Hbz X1 X2 Hkm Hkm' NL; lia).
destruct F as (c' & Hc' & F). clear - F Hx Hc'. lia.
Qed.
#[using="LB M Sp q16 qr b1 km qtl cl24 newb wb b lastb L B cntB REP Hin Eu Hn Hqr Hb1 Cn KIND HS Emu Edep OUT LIVE LIVE2 LIVE3 OKpre Hother"] Lemma art_frep_quar : art_rt_quar_b FSG (2 ^ 29) rn G' M'.
Proof.
pose proof REP as (ROK & _ & _ & (_ & PRIM & _) & CH & SECR & QR & _). pose proof ROK as ROK'. rok_open14 ROK'. pose proof GEO as GEO'. geo_open GEO'.
destruct art_frep_num as (Hkm & Hkm' & Hbz & HBz & HnL).
destruct art_frep_out as (GR & _ & _ & CHW & _ & _ & _ & _ & OK' & NEW & OLD & CBY).
destruct QR as ((ft & lt & Ct80 & Ct88 & Ct96 & Ct104 & BLt) & (fg & lg & Cg160 & Cg168 & Cg176 & Cg184 & BLg) & Bt & Bg & Cmx & ND & NEI & ITEMS & NDI & BCH).
pose proof art_frep_batch_eq as BEQ. pose proof art_frep_thq_room as THR. pose proof art_frep_thq_first as THF. pose proof art_frep_wb_free as WBF.
pose proof art_frep_st_pop as STP. pose proof art_frep_st_freed as STF. pose proof art_frep_st_other as STO. pose proof art_frep_au_mono as AUM.
pose proof art_frep_sec_u_inj as SUI. pose proof art_frep_uw_other as UWO. pose proof art_frep_uw_where as UWW. pose proof art_frep_live_far as LFAR.
apply NoDup_ListNoDup in ND. apply NoDup_ListNoDup in NDI.
assert (ADDRB : forall b0, In b0 (g_qt FSG G ++ g_qg FSG G) -> 0 <= bt_addr b0 /\ bt_addr b0 + 8192 < 2 ^ 64).
{ intros b0 Hb0. destruct (BCH b0 Hb0) as (w0 & Ew0 & (V0 & V1 & _) & _). rewrite art_class_size_24 in V1. destruct (PRIM 24 ltac:(lia)) as (_ & OK0 & _).
destruct OK0 as (_ & (_ & Haumu0) & _ & _ & _ & Hmu30 & _). rewrite Ew0. clear - V0 V1 Haumu0 Hmu30 G4 G6 G2 Eris Espb. lia. }
assert (TCELL : forall a v, (newb = false -> rn_t rn + 80 <= a /\ a + 8 <= rn_t rn + 104) -> (newb = true -> L <> 0 /\ a = rn_t rn + 88) -> cellA M a 8 v -> cellA M' a 8 v).
{ intros a v H0 H1 C. destruct (Bool.bool_dec newb true) as [En|En].
- destruct (H1 En) as (NL & ->). apply (art_cell_agree _ M M'); [|clear - G7; lia|clear - G8 G2; cbn; lia|exact C]. intros x Hx. apply (THF En NL). cbn in Hx. clear - Hx. lia.
- apply Bool.not_true_is_false in En. destruct (H0 En) as (A0 & A1). apply (art_cell_agree _ M M'); [|clear - G7 A0; lia|clear - G8 G2 A1; cbn; lia|exact C].
intros x Hx. apply (THR En). cbn in Hx. clear - Hx A0 A1. lia. }
unfold art_rt_quar_b. change (g_qt FSG G') with (art_qt_add qtl b (u - 16, n)). change (g_qg FSG G') with (g_qg FSG G).
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]].
-
destruct (Bool.bool_dec newb true) as [En|En].
+ destruct (NEW En) as (CPb & _ & Cb0 & Cb8 & Cb16 & Cb24 & Cc & Cc16 & CL0 & CLB).
assert (EA : art_qt_add qtl b (u - 16, n) = qtl ++ [BATCH b [(u - 16, n)]]) by (unfold art_qt_add; change (art_free_newb qtl) with newb; rewrite En; reflexivity).
assert (BN : art_batch_list M' [BATCH b [(u - 16, n)]] b b).
{ cbn [art_batch_list bt_addr bt_items length fold_right snd]. split; [reflexivity|]. split; [lia|]. split; [exact Cb16|].
split; [replace (8192 + (n + 0)) with (n + 8192) by lia; exact Cb8|]. split.
{ intros j it Hj. destruct j as [|j]; [cbn in Hj; injection Hj as <-; cbn [fst]; replace (b + 24 + 8 * Z.of_nat 0) with (b + 24) by lia; exact Cb24|destruct j; discriminate]. }
split; [split; [reflexivity|exact Cb0]|reflexivity]. }
exists (if L =? 0 then b else ft), b.
split. { rewrite EA, length_app. cbn [length]. replace (Z.of_nat (length qtl + 1)) with (L + 1) by (unfold L; lia). exact Cc. }
split. { destruct (Z.eqb_spec L 0) as [EL|NL]; [replace (rn_t rn + 88) with (rn_t rn + 80 + 8) by lia; exact (CL0 EL)|]. apply TCELL; [intros E; rewrite E in En; discriminate|intros _; split; [exact NL|reflexivity]|exact Ct88]. }
split. { replace (rn_t rn + 96) with (rn_t rn + 80 + 16) by lia. exact Cc16. }
split. { rewrite art_qt_add_bytes. cbn [snd]. change (art_free_newb qtl) with newb. replace (rn_t rn + 104) with (rn_t rn + 80 + 24) by lia. exact CBY. }
rewrite EA. destruct (Z.eqb_spec L 0) as [EL|NL].
* assert (Eq0 : qtl = []) by (apply length_zero_iff_nil; unfold L in EL; clear - EL; lia). rewrite Eq0. exact BN.
* assert (NEq : qtl <> []) by (intros E0; apply NL; unfold L; rewrite E0; reflexivity).
assert (Elt : lt = B) by (unfold B, lastb; exact (art_batch_list_last M qtl ft lt NEq BLt)).
change b with (bt_addr (BATCH b [(u - 16, n)])) at 2.
apply (art_batch_list_snoc M M' qtl ft lt (BATCH b [(u - 16, n)]) NEq); [ | exact BLt | | | | exact BN ].
-- apply NoDup_ListNoDup. unfold qtl. rewrite map_app in ND. exact (NoDup_app_remove_r _ _ ND).
-- intros b0 Hb0. apply ADDRB. apply in_or_app. left. exact Hb0.
-- intros b0 x Hb0 Hx NX. apply (BEQ b0 x (in_or_app _ _ _ (or_introl Hb0)) Hx). intros _ EB X. apply NX. unfold art_B_written in X. rewrite En in X.
split; [rewrite Elt; exact EB|rewrite Elt; clear - X; lia].
-- rewrite Elt. exact (CLB NL).
+ apply Bool.not_true_is_false in En. destruct (OLD En) as (CB16 & CB8 & CBI). pose proof (HnL En) as NL. destruct (HBz NL) as (_ & _ & X3).
destruct (art_free_newb_false qtl En) as (NEq & X4).
assert (ESP : qtl = removelast qtl ++ [lastb]) by (apply art_qt_split; exact NEq).
assert (EA : art_qt_add qtl b (u - 16, n) = removelast qtl ++ [BATCH B (bt_items lastb ++ [(u - 16, n)])]) by (unfold art_qt_add; change (art_free_newb qtl) with newb; rewrite En; reflexivity).
assert (InB : In lastb (g_qt FSG G ++ g_qg FSG G)). { apply in_or_app. left. unfold lastb, art_lastb. apply JbtFxQ.art_last_in. exact NEq. }
exists ft, lt.
split. { rewrite art_qt_add_length. change (art_free_newb qtl) with newb. rewrite En, Z.add_0_r. apply TCELL; [intros _; clear; lia|intros E; rewrite E in En; discriminate|exact Ct80]. }
split; [apply TCELL; [intros _; clear; lia|intros E; rewrite E in En; discriminate|exact Ct88]|].
split; [apply TCELL; [intros _; clear; lia|intros E; rewrite E in En; discriminate|exact Ct96]|].
split. { rewrite art_qt_add_bytes. cbn [snd]. change (art_free_newb qtl) with newb. replace (rn_t rn + 104) with (rn_t rn + 80 + 24) by lia. exact CBY. }
rewrite EA.
apply (art_batch_list_upd_last M M' (removelast qtl) lastb (BATCH B (bt_items lastb ++ [(u - 16, n)])) ft lt).
* rewrite <- ESP. exact BLt.
* reflexivity.
* intros b0 Hb0. apply ADDRB. apply in_or_app. left. unfold qtl in ESP. rewrite ESP. exact Hb0.
* intros b0 x Hb0 Hx. apply (BEQ b0 x); [apply in_or_app; left; unfold qtl in ESP; rewrite ESP; apply in_or_app; left; exact Hb0|exact Hx|].
intros _ EB _. exfalso. rewrite map_app in ND. apply NoDup_app_remove_r in ND. unfold qtl in ESP. rewrite ESP in ND.
exact (art_nodup_map_app _ bt_addr (removelast (g_qt FSG G)) [lastb] b0 lastb ND Hb0 (or_introl eq_refl) EB).
* intros x Hx. apply (BEQ lastb x InB); [clear - Hx; lia|]. intros _ _ X. unfold art_B_written in X. rewrite En in X. clear - X Hx X3. unfold B in *. lia.
* cbn [bt_items]. rewrite length_app. cbn [length]. clear - X3 X4. unfold cntB, lastb in *. lia.
* cbn [bt_items bt_addr]. rewrite length_app. cbn [length]. replace (Z.of_nat (length (bt_items lastb) + 1)) with (cntB + 1) by (unfold cntB; lia). exact CB16.
* cbn [bt_addr]. pose proof (art_bt_bytes_add B (bt_items lastb) (u - 16, n)) as EBY. unfold art_bt_bytes in EBY. cbn [bt_items snd] in EBY. cbn [bt_items]. rewrite EBY.
unfold art_bt_bytes in CB8. exact CB8.
* intros j it Hj. cbn [bt_items bt_addr] in Hj |- *. destruct (Nat.lt_ge_cases j (length (bt_items lastb))) as [Hlt|Hge].
-- rewrite nth_error_app1 in Hj by exact Hlt. pose proof (art_batch_list_last_cells M (removelast qtl) lastb ft lt ltac:(rewrite <- ESP; exact BLt) j it Hj) as C0.
destruct (ADDRB lastb InB) as (A0 & A1).
apply (art_cell_agree _ M M'); [|clear - A0; unfold B; lia|clear - A1 Hlt X3; unfold B, cntB in *; cbn; lia|exact C0].
intros x Hx. apply (BEQ lastb x InB); [cbn in Hx; clear - Hx Hlt X3; unfold B, cntB in *; lia|]. intros _ _ X. unfold art_B_written in X. rewrite En in X. cbn in Hx. clear - X Hx Hlt. unfold B, cntB in *. lia.
-- rewrite nth_error_app2 in Hj by exact Hge. destruct (j - length (bt_items lastb))%nat as [|d] eqn:Ed; [|destruct d; discriminate]. cbn in Hj. injection Hj as <-. cbn [fst].
replace (Z.of_nat j) with cntB by (unfold cntB; clear - Hge Ed; lia). exact CBI.
-
exists fg, lg. split; [apply art_frep_cell_img; [cbn; lia|exact Cg160]|]. split; [apply art_frep_cell_img; [cbn; lia|exact Cg168]|].
split; [apply art_frep_cell_img; [cbn; lia|exact Cg176]|]. split; [apply art_frep_cell_img; [cbn; lia|exact Cg184]|].
apply (art_batch_list_tr M M'); [|exact BLg]. intros b0 Hb0. destruct (ADDRB b0 (in_or_app _ _ _ (or_intror Hb0))) as (A0 & A1). split; [exact A0|]. split; [exact A1|].
intros x Hx. apply (BEQ b0 x (in_or_app _ _ _ (or_intror Hb0)) Hx). intros NL EB _. exfalso.
assert (NEq : qtl <> []) by (intros E0; apply NL; unfold L; rewrite E0; reflexivity).
assert (InL : In lastb (g_qt FSG G)) by (unfold lastb, art_lastb; apply JbtFxQ.art_last_in; exact NEq).
exact (art_nodup_map_app _ bt_addr _ _ lastb b0 ND InL Hb0 (eq_sym EB)).
- rewrite art_qt_add_bytes. cbn [snd]. fold qtl in Bt. clear - Bt Hn. destruct (art_free_newb qtl); lia.
- exact Bg.
- apply art_frep_cell_img; [cbn; lia|exact Cmx].
-
apply NoDup_ListNoDup. rewrite map_app, art_qt_add_addrs. change (art_free_newb qtl) with newb. destruct (Bool.bool_dec newb true) as [En|En].
+ rewrite En. rewrite <- app_assoc. cbn [app]. rewrite map_app in ND. apply art_nodup_insert; [exact ND|]. rewrite <- map_app. intros Hi0. apply in_map_iff in Hi0. destruct Hi0 as (b0 & Eb0 & Hb0).
destruct (BCH b0 Hb0) as (w0 & Ew0 & _ & St0). assert (w0 = wb) by (unfold b in Eb0; clear - Eb0 Ew0; lia). subst w0. rewrite (WBF En) in St0. discriminate.
+ apply Bool.not_true_is_false in En. rewrite En, app_nil_r. rewrite <- map_app. exact ND.
-
intros b0 Hb0. apply in_app_or in Hb0. destruct Hb0 as [Hb0|Hb0]; [|apply NEI; apply in_or_app; right; exact Hb0].
destruct (art_qt_add_in qtl b (u - 16, n) b0 Hb0) as [(_ & ->)|[Hold|(_ & _ & ->)]]; [discriminate|apply NEI; apply in_or_app; left; exact Hold|].
cbn [bt_items]. intros E0. apply app_eq_nil in E0. destruct E0 as (_ & E0). discriminate.
-
assert (NEWIT : (exists c w, 1 <= c <= 30 /\ art_cptr_ok (AsanTab.class_size c) (cl_au (g_cls FSG G' c)) w /\ g_st FSG G' c w = CQuar (fst (u - 16, n) + 16) (snd (u - 16, n)))
\/ (exists s, In s (g_sec FSG G') /\ sc_quar s = true /\ sc_u s = fst (u - 16, n) + 16 /\ sc_n s = snd (u - 16, n))).
{ cbn [fst snd]. replace (u - 16 + 16) with u by lia. pose proof KIND as KD. destruct k as [c w|i].
- destruct KD as (Hc & V & _). left. exists c, w. split; [exact Hc|]. split; [eapply art_cptr_mono; [exact (AUM c Hc)|exact V]|exact (STF c w eq_refl)].
- destruct KD as (si & Hsi & _ & Esu & Esn). right. exists (SEC (sc_map si) (sc_msize si) (sc_u si) (sc_n si) true).
split; [unfold G'; cbn [art_gs_free g_sec]; eapply nth_error_In; apply art_sec_quar_nth_same; exact Hsi|]. cbn [sc_quar sc_u sc_n]. repeat split; [exact Esu|exact Esn]. }
assert (OLDIT : forall b0 it, In b0 (g_qt FSG G ++ g_qg FSG G) -> In it (bt_items b0) ->
(exists c w, 1 <= c <= 30 /\ art_cptr_ok (AsanTab.class_size c) (cl_au (g_cls FSG G' c)) w /\ g_st FSG G' c w = CQuar (fst it + 16) (snd it))
\/ (exists s, In s (g_sec FSG G') /\ sc_quar s = true /\ sc_u s = fst it + 16 /\ sc_n s = snd it)).
{ intros b0 it Hb0 Hit. destruct (ITEMS b0 it Hb0 Hit) as [(c0 & w0 & Hc0 & V0 & St0)|(s & Hs & Hq & Esu & Esn)].
- left. exists c0, w0. split; [exact Hc0|]. split; [eapply art_cptr_mono; [exact (AUM c0 Hc0)|exact V0]|]. rewrite STO; [exact St0| |].
+ intros (E & -> & ->). rewrite (WBF E) in St0. discriminate.
+ pose proof KIND as KD. destruct k as [c w|i]; [|exact I]. intros (-> & ->). destruct KD as (_ & _ & St'). rewrite St0 in St'. discriminate.
- right. exists s. split; [|repeat split; assumption]. unfold G'. cbn [art_gs_free g_sec]. pose proof KIND as KD. destruct k as [c w|i]; [exact Hs|].
destruct KD as (si & Hsi & Hqi & Esui & _). apply (art_sec_quar_in_other i _ si s Hsi Hs). intros EU.
destruct (In_nth_error _ _ Hs) as (j & Hj). pose proof (SUI j i s si Hj Hsi EU) as ->. rewrite Hsi in Hj. injection Hj as ->. rewrite Hq in Hqi. discriminate. }
intros b0 it Hb0 Hit. apply in_app_or in Hb0. destruct Hb0 as [Hb0|Hb0]; [|exact (OLDIT b0 it (in_or_app _ _ _ (or_intror Hb0)) Hit)].
destruct (art_qt_add_in qtl b (u - 16, n) b0 Hb0) as [(_ & ->)|[Hold|(_ & NEq & ->)]].
+ cbn [bt_items] in Hit. destruct Hit as [<-|[]]. exact NEWIT.
+ exact (OLDIT b0 it (in_or_app _ _ _ (or_introl Hold)) Hit).
+ cbn [bt_items] in Hit. apply in_app_or in Hit. destruct Hit as [Hit|[<-|[]]]; [|exact NEWIT].
apply (OLDIT lastb it); [apply in_or_app; left; unfold lastb, art_lastb; apply JbtFxQ.art_last_in; exact NEq|exact Hit].
-
apply NoDup_ListNoDup. rewrite flat_map_app, art_qt_add_flat, map_app, map_app. cbn [map fst]. rewrite <- app_assoc. cbn [app].
rewrite flat_map_app, map_app in NDI. apply art_nodup_insert; [exact NDI|]. rewrite <- map_app, <- flat_map_app. intros Hi0. apply in_map_iff in Hi0. destruct Hi0 as (it & Eit & Hit).
apply in_flat_map in Hit. destruct Hit as (b0 & Hb0 & Hit).
assert (INU : art_uw u) by (unfold art_uw; right; left; clear; lia).
destruct (ITEMS b0 it Hb0 Hit) as [(c0 & w0 & Hc0 & V0 & St0)|(s & Hs & Hq & Esu & Esn)].
+
rewrite Eit in St0. replace (u - 16 + 16) with u in St0 by lia.
pose proof (CH c0 Hc0) as CH0. cbv zeta in CH0. destruct CH0 as (_ & _ & _ & III). specialize (III w0 V0). rewrite St0 in III. destruct III as (J2 & J3 & (bb & _ & _ & _ & _ & Hn0) & _).
assert (INC : art_in_chunk c0 w0 u) by (unfold art_in_chunk; left; clear - J2 J3 Hn0; lia).
assert (Nk : match k with FKP c w => ~ (c0 = c /\ w0 = w) | FKS _ => True end).
{ pose proof KIND as KD. destruct k as [c w|i]; [|exact I]. intros (-> & ->). destruct KD as (_ & _ & St'). rewrite St0 in St'. discriminate. }
exact (UWO c0 w0 u Hc0 V0 Nk INC INU).
+
rewrite Eit in Esu. replace (u - 16 + 16) with u in Esu by lia. destruct (In_nth_error _ _ Hs) as (j & Hj).
destruct SECR as (_ & _ & _ & _ & _ & _ & _ & _ & SALL & _). destruct (SALL j s Hj) as (_ & P2 & _ & _ & _ & _ & P7 & P8 & P9 & _).
rewrite Hq in P9. destruct P9 as ((bb & _ & _ & _ & _ & Hns) & _).
pose proof (UWW u INU) as W. pose proof KIND as KD. destruct k as [c w|i].
* destruct KD as (Hc & (V0 & V1 & _) & _). unfold art_in_chunk in W. destruct (LFAR _ P2) as (_ & _ & _ & P3 & _ & Ak & _). cbn [fst snd] in Ak, P3.
destruct (PRIM c Hc) as (_ & OKc & _). destruct OKc as (_ & (_ & Haumuc) & _ & _ & _ & Hmu3c & _). pose proof (art_class_size_facts c Hc) as (Hszc & _).
unfold apart in Ak. rewrite Esu in P7, P8. clear - W Ak P3 P7 P8 Hns Hc V0 V1 Haumuc Hmu3c Hszc Kspb Kend Espb Eris G4 G1 G2 G6. lia.
* destruct KD as (si & Hsi & Hqi & Esui & _). pose proof (SUI j i s si Hj Hsi ltac:(rewrite Esu, Esui; reflexivity)) as ->. rewrite Hsi in Hj. injection Hj as ->. rewrite Hq in Hqi. discriminate.
-
assert (OLDB : forall b0, In b0 (g_qt FSG G ++ g_qg FSG G) ->
exists w0, bt_addr b0 = rn_spb rn + 24 * 2 ^ 32 + 16 * w0 /\ art_cptr_ok (AsanTab.class_size 24) (cl_au (g_cls FSG G' 24)) w0 /\ g_st FSG G' 24 w0 = CBatch).
{ intros b0 Hb0. destruct (BCH b0 Hb0) as (w0 & Ew0 & V0 & St0). exists w0. split; [exact Ew0|]. split; [eapply art_cptr_mono; [exact (AUM 24 ltac:(lia))|exact V0]|].
rewrite STO; [exact St0| |].
- intros (E & _ & ->). rewrite (WBF E) in St0. discriminate.
- pose proof KIND as KD. destruct k as [c w|i]; [|exact I]. intros (<- & <-). destruct KD as (_ & _ & St'). rewrite St0 in St'. discriminate. }
intros b0 Hb0. apply in_app_or in Hb0. destruct Hb0 as [Hb0|Hb0]; [|exact (OLDB b0 (in_or_app _ _ _ (or_intror Hb0)))].
destruct (art_qt_add_in qtl b (u - 16, n) b0 Hb0) as [(En & ->)|[Hold|(_ & NEq & ->)]].
+ change (art_free_newb qtl) with newb in En. destruct (NEW En) as (CPb & _). exists wb. split; [reflexivity|]. split; [|exact (STP En)].
rewrite art_class_size_24. unfold G'. cbn [art_gs_free g_cls]. rewrite Z.eqb_refl. change (art_free_newb (g_qt FSG G)) with newb. rewrite En. unfold art_enq_cls. cbn [art_cls_pop cl_au]. exact CPb.
+ exact (OLDB b0 (in_or_app _ _ _ (or_introl Hold))).
+ cbn [bt_addr]. apply (OLDB lastb). apply in_or_app. left. unfold lastb, art_lastb. apply JbtFxQ.art_last_in. exact NEq.
Qed.
#[using="LB M M' n b1 kb REP Hb1 HS Emu Edep OUT OKpre"] Lemma art_frep_nfpa : forall c0 a, 1 <= c0 <= 30 ->
(rn_spb rn + c0 * 2 ^ 32 <= a < rn_spb rn + c0 * 2 ^ 32 + cl_mu (g_cls FSG G c0)
\/ (2147450880 + 8192 * rn_qs rn + c0 * 2 ^ 29 <= a /\ 8 * (a - (2147450880 + 8192 * rn_qs rn + c0 * 2 ^ 29)) < cl_mu (g_cls FSG G c0))) ->
~ (u - 16 <= a < u - 12) -> ~ (u <= a < u + 8) -> ~ (2147450880 + 2 * q16 <= a < 2147450880 + 2 * q16 + qr) ->
(c0 = 24 -> newb = true -> ~ (b <= a < b + 32)) -> (c0 = 24 -> L <> 0 -> ~ art_B_written a) ->
~ art_free_fpl a.
Proof.
intros c0 a Hc0 Ha N1 N2 N3 Nb NB. unfold art_B_written in NB. destruct art_frep_num as (Hkm & Hkm' & Hbz & HBz & HnL).
pose proof REP as (ROK & _ & _ & (_ & PRIM & _) & _). rok_open14 ROK. geo_open GEO.
destruct (PRIM c0 Hc0) as (_ & OK0 & _). destruct OK0 as (_ & (Hau0 & Haumu0) & _ & _ & _ & Hmu30 & _).
assert (Hmu24 : c0 = 24 -> cl_mu (g_cls FSG G c0) = 262144 * km). { intros ->. exact Emu. }
assert (Ra : 0 <= a < 2 ^ 64) by (clear - Ha Hc0 G4 G6 G2 Eris Espb Hmu30; lia).
intros [F|F].
- unfold art_free3_fp, dprivD in F. unfold apart in G11, G10, Al2k, Al2s, Abk, Abs.
clear - F Ha Hc0 N1 N2 N3 HS G1 G2 G4 G6 G8 G9 G10 G11 Espb Eris Hmu30 Al2k Al2s Abk Abs. repeat (destruct F as [F|F]); lia.
- unfold art_enq_fp in F. destruct newb eqn:E.
+ specialize (Hbz eq_refl). specialize (fun e => Nb e eq_refl). unfold art_enq_new_fp, art_refill_fp in F. unfold apart in G11, G10.
destruct F as [F|[[F|[F|[F|[F|[F|[F|[F|[F|[F|F]]]]]]]]]|[F|[F|[F|F]]]]]; try (clear - F Ha Hc0 HS G1 G2 G4 G6 G8 G10 G11 Espb Eris Hmu30 Hmu24 Hkm Hkm'; lia).
* destruct F as (c' & Hc' & F). clear - F Ha Hc0 Hc' G1 G2 G8 G10 G11 G4 G6 Espb Eris Hmu30. lia.
* destruct (Z.eq_dec c0 24) as [e|ne]; [specialize (Nb e); clear - F Nb; lia|clear - F Ha Hc0 ne Hbz G4 Espb Hmu30; lia].
* destruct F as [NL F]. destruct (HBz NL) as (X1 & X2 & _). destruct (Z.eq_dec c0 24) as [e|ne]; [specialize (NB e NL); clear - F NB; lia|clear - F Ha Hc0 ne X1 X2 G4 Espb Hmu30; lia].
+ pose proof (HnL eq_refl) as NL. destruct (HBz NL) as (X1 & X2 & X3).
assert (X4 : cntB <> 1021). { destruct (art_free_newb_false qtl E) as (_ & X). exact X. }
unfold apart in G11. destruct F as [F|[F|[F|F]]]; try (clear - F Ha Hc0 HS G1 G2 G4 G6 G8 G10 G11 Espb Eris Hmu30; lia);
(destruct (Z.eq_dec c0 24) as [e|ne]; [specialize (NB e NL); clear - F NB X3 X4; lia|clear - F Ha Hc0 ne X1 X2 X3 G4 Espb Hmu30; lia]).
Qed.
#[using="LB M M' n b1 kb REP Hb1 HS Emu Edep OUT OKpre"] Lemma art_frep_chunk_nfp0 : forall c0 w0 a, 1 <= c0 <= 30 -> art_cptr_ok (AsanTab.class_size c0) (cl_au (g_cls FSG G c0)) w0 ->
(c0 = 24 -> newb = true -> w0 <> wb) -> (c0 = 24 -> L <> 0 -> rn_spb rn + 24 * 2 ^ 32 + 16 * w0 <> B) ->
art_in_chunk c0 w0 a -> ~ art_uw a -> ~ art_free_fpl a.
Proof.
intros c0 w0 a Hc0 V Nwb NwB Ha UWa. unfold art_uw in UWa. destruct art_frep_num as (Hkm & Hkm' & Hbz & HBz & HnL).
pose proof REP as (ROK & _ & _ & (_ & PRIM & _) & _ & _ & QR & _). rok_open14 ROK. geo_open GEO.
destruct (PRIM c0 Hc0) as (_ & OK0 & _). pose proof OK0 as (_ & (Hau0 & Haumu0) & _ & _ & Hka0 & Hmu30 & _).
pose proof (art_class_size_facts c0 Hc0) as (Hsz0 & Hsz016). pose proof V as (V0 & V1 & (i0 & Ei0)).
apply (art_frep_nfpa c0 a Hc0).
- unfold art_in_chunk in Ha. clear - Ha V0 V1 Haumu0 Hsz0. lia.
- intros X. apply UWa. left. exact X.
- intros X. apply UWa. right; left. exact X.
- intros X. apply UWa. right; right. exact X.
- intros -> E X. specialize (Nwb eq_refl E). destruct art_frep_out as (_ & _ & _ & _ & _ & _ & _ & _ & OK' & NEW & _). destruct (NEW E) as (CPb & _).
rewrite art_class_size_24 in *. assert (Hau' : cl_au cl24 <= cl_au (art_ca_pre 24 cl24)).
{ destruct (art_ca_pre_au 24 cl24) as [E0|(_ & _ & E0)]; rewrite E0; [lia|]. assert (0 <= art_cls_new 24 cl24 * AsanTab.class_size 24); [|lia].
apply Z.mul_nonneg_nonneg; [|rewrite art_class_size_24; lia]. unfold art_cls_new. apply Z.div_pos; [|rewrite art_class_size_24; lia]. fold cl24 in Hau0, Haumu0. lia. }
pose proof (art_cptr_apart 8192 (cl_au (art_ca_pre 24 cl24)) w0 wb ltac:(clear; lia) (art_cptr_mono _ _ _ _ Hau' V) CPb Nwb) as AP.
unfold art_in_chunk in Ha. rewrite art_class_size_24 in Ha. unfold b in X. clear - X Ha AP Hbz E G4 Espb V0 V1 Haumu0 Hmu30. specialize (Hbz E). lia.
- intros -> NL X. specialize (NwB eq_refl NL).
assert (InB : In lastb (g_qt FSG G ++ g_qg FSG G)). { apply in_or_app. left. unfold lastb, art_lastb. apply JbtFxQ.art_last_in. intros E. apply NL. unfold L. fold qtl in E. rewrite E. reflexivity. }
destruct QR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & BCH). destruct (BCH lastb InB) as (wB & EwB & VB & _). fold B in EwB. rewrite art_class_size_24 in *.
assert (Nw : w0 <> wB) by (intros ->; apply NwB; symmetry; exact EwB).
pose proof (art_cptr_apart 8192 (cl_au (g_cls FSG G 24)) w0 wB ltac:(clear; lia) V VB Nw) as AP. unfold art_in_chunk in Ha. rewrite art_class_size_24 in Ha.
assert (XW : rn_spb rn + 24 * 2 ^ 32 + 16 * wB <= a < rn_spb rn + 24 * 2 ^ 32 + 16 * wB + 8192).
{ unfold art_B_written in X. rewrite EwB in X. destruct (HBz NL) as (_ & _ & X3). destruct newb eqn:E; [clear - X; lia|].
destruct (art_free_newb_false qtl E) as (_ & X4). fold lastb in X4. fold cntB in X4. clear - X X3 X4. lia. }
destruct VB as (VB0 & VB1 & _). clear - XW Ha AP G4 Espb V0 V1 VB0 VB1 Haumu0 Hmu30. lia.
Qed.
#[using="LB M M' n b1 kb REP Hn Hqr Hb1 HS Emu Edep OUT OKpre"] Lemma art_frep_nfp_W : ltac2:(TCodec.tc2 tcn__JbtInvFree "I'E'?&R8zr1%3221&R9&R=+2+R0%3221%5271%;271&Q;&R2r2%3221&B&R0r3%211%411p061p0;1pU0H1").
Proof.
intros a Ha Hx F. apply art_frep_coarse in F. unfold art_frep_W in Hx. cbn [art_out fst snd] in Hx. unfold art_free_coarse, dprivD in F. lia.
Qed.
Section SE.
Local Abbreviation SEC_T_art_frep_block_cases := (forall b0, In b0 (lb_remove u LB) ->
(exists c0 w0, 1 <= c0 <= 30 /\ art_cptr_ok (AsanTab.class_size c0) (cl_au (g_cls FSG G c0)) w0 /\ g_st FSG G c0 w0 = CAlloc (fst b0) (snd b0)
/\ match k with FKP c w => ~ (c0 = c /\ w0 = w) | FKS _ => True end /\ 1 <= snd b0
/\ rn_spb rn + c0 * 2 ^ 32 + 16 * w0 + 16 <= fst b0 /\ fst b0 + snd b0 <= rn_spb rn + c0 * 2 ^ 32 + 16 * w0 + AsanTab.class_size c0)
\/ (exists p, In p (art_live (g_log FSG G)) /\ fst p + 4096 <= fst b0 /\ fst b0 + snd b0 <= fst p + snd p /\ 1 <= snd b0
/\ (fst p + snd p <= u - 16 \/ u + 8 * qr <= fst p))) (only parsing).
Variable b0 : ltac:(sec_ty2 constr:(SEC_T_art_frep_block_cases) 0%nat 0%nat).
#[using="M n q16 b1 kb qtl cl24 wb b lastb L B cntB REP Eu Hn Hqr Hb1 KIND Edep LIVE LIVE2 LIVE3 Hother b0"] Lemma art_frep_block_cases : ltac:(sec_stmt2 constr:(SEC_T_art_frep_block_cases) 1%nat 0%nat).
Proof.
intros Hb0.
destruct (Hother b0 Hb0) as (Hb & Nu). pose proof REP as (_ & _ & _ & _ & CH & SEC & _ & _ & _ & BL & _).
pose proof art_frep_grant_off as GOFF. pose proof art_frep_sec_u_inj as SUI.
destruct (BL b0 Hb) as [(c0 & w0 & Hc0 & V0 & St0)|(s & Hs & Hq & Esu & Esn)].
- left. exists c0, w0. specialize (CH c0 Hc0). cbv zeta in CH. destruct CH as (_ & _ & _ & III). specialize (III w0 V0). rewrite St0 in III.
destruct III as (_ & J2 & J3 & (bb & _ & _ & _ & _ & Hn0) & _). split; [exact Hc0|]. split; [exact V0|]. split; [exact St0|]. split; [|split; [lia|split; [exact J2|exact J3]]].
pose proof KIND as KD. destruct k as [c w|i]; [|exact I]. intros (-> & ->). destruct KD as (_ & _ & St'). rewrite St0 in St'. injection St' as E1 _. exact (Nu E1).
- right. destruct SEC as (_ & _ & _ & _ & _ & _ & _ & _ & SALL & _ & SLEN). destruct (In_nth_error _ _ Hs) as (j & Hj).
destruct (SALL j s Hj) as (_ & P2 & _ & _ & _ & P6 & P7 & P8 & P9 & _). rewrite Hq in P9. destruct P9 as (_ & (bb & _ & _ & _ & _ & Hn0) & _).
exists (sc_map s, sc_msize s). cbn [fst snd]. rewrite <- Esu, <- Esn. split; [exact P2|]. split; [clear - P7; lia|]. split; [exact P8|]. split; [clear - Hn0; lia|].
apply (GOFF (sc_map s, sc_msize s) P2). pose proof KIND as KD. destruct k as [c w|i]; [exact I|]. intros si Hsi E. cbn [fst] in E.
destruct KD as (si' & Hsi' & _ & Esui & _). rewrite Hsi in Hsi'. injection Hsi' as <-.
destruct (SALL i si Hsi) as (_ & _ & _ & _ & _ & Q6 & _). rewrite <- E in Q6.
assert (Hil : Z.of_nat j < Z.of_nat (length (g_sec FSG G))). { apply Nat2Z.inj_lt. apply nth_error_Some. rewrite Hj. discriminate. }
assert (Hil' : Z.of_nat i < Z.of_nat (length (g_sec FSG G))). { apply Nat2Z.inj_lt. apply nth_error_Some. rewrite Hsi. discriminate. }
pose proof (cell8_inj M _ _ _ P6 Q6 ltac:(clear - Hil SLEN; lia) ltac:(clear - Hil' SLEN; lia)) as EI. apply Nat2Z.inj in EI. subst j.
rewrite Hsi in Hj. injection Hj as ->. apply Nu. rewrite <- Esu. exact Esui.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_frep_nfp_block := (ltac2:(TCodec.tc2 tcn__JbtInvFree "Q3'<'E%2211&R5r2&OvS6vG%3221%63751'C'?&R8&6r3%23>>1%421<&R9&R7&=%13CC6%3261%52B1%<271&Q4%13:5E%@231&B&R0%11?%311p051p0G1pU0Q01pU4Q01")) (only parsing).
Variable b0 : ltac:(sec_ty2 constr:(SEC_T_art_frep_nfp_block) 0%nat 0%nat).
Variable a : ltac:(sec_ty2 constr:(SEC_T_art_frep_nfp_block) 1%nat 0%nat).
#[using="M M' n b1 kb k REP Eu Hn Hqr Hb1 KIND HS Emu Edep OUT LIVE LIVE2 LIVE3 OKpre Hother b0 a"] Lemma art_frep_nfp_block : ltac:(sec_stmt2 constr:(SEC_T_art_frep_nfp_block) 2%nat 0%nat).
Proof.
intros Hb0 Ha.
pose proof REP as (ROK & _ & _ & (_ & PRIM & _) & _ & _ & QR & _). rok_open14 ROK. geo_open GEO. unfold in_shadow_of in Ha.
pose proof art_frep_wb_free as WBF. pose proof art_frep_uw_other as UWO. pose proof art_frep_chunk_nfp0 as CNF. pose proof art_frep_nfp_W as NFW.
pose proof art_fgap_grant_sub as GSUB. pose proof art_fgap_sh as GSH. pose proof art_frep_ush_off as USO. pose proof art_frep_live_far as LFAR.
destruct (art_frep_block_cases b0 Hb0) as [(c0 & w0 & Hc0 & V0 & St0 & Nk & Hn0 & J2 & J3)|(p & Hp & P1 & P2 & Hn0 & OFF)].
- destruct (PRIM c0 Hc0) as (_ & OK0 & _). pose proof OK0 as (_ & (Ha0 & Ham0) & _ & _ & _ & Hmu30 & _). pose proof V0 as (V00 & V01 & _).
pose proof (art_class_size_facts c0 Hc0) as (Hsz0 & Hsz016).
assert (Es : AsanTab.class_size c0 = 16 * (AsanTab.class_size c0 / 16)). { pose proof (Z.div_mod (AsanTab.class_size c0) 16 ltac:(lia)) as D. rewrite Hsz016 in D. lia. }
assert (INC : art_in_chunk c0 w0 a).
{ unfold art_in_chunk. destruct Ha as [Ha|Ha]; [left; clear - Ha J2 J3; lia|right].
pose proof (art_S_lt (fst b0 + snd b0 - 1) (8192 * rn_qs rn + c0 * 2 ^ 29 + 2 * w0 + 2 * (AsanTab.class_size c0 / 16)) ltac:(clear - J3 Es Espb; lia)) as H2.
pose proof (art_S_ge (fst b0) (8192 * rn_qs rn + c0 * 2 ^ 29 + 2 * w0 + 2) ltac:(clear - J2 Espb; lia)) as H3. clear - Ha H2 H3 Es. split; lia. }
apply (CNF c0 w0 a Hc0 V0).
+ intros -> E ->. rewrite (WBF E) in St0. discriminate.
+ intros -> NL E. assert (InB : In lastb (g_qt FSG G ++ g_qg FSG G)). { apply in_or_app. left. unfold lastb, art_lastb. apply JbtFxQ.art_last_in. intros E0. apply NL. unfold L, qtl. rewrite E0. reflexivity. }
destruct QR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & BCH). destruct (BCH lastb InB) as (wB & EwB & _ & StB).
assert (w0 = wB) by (unfold B in E; clear - E EwB; lia). subst w0. rewrite StB in St0. discriminate.
+ exact INC.
+ exact (UWO c0 w0 a Hc0 V0 Nk INC).
- destruct (LFAR p Hp) as (L0 & L1 & L2 & _ & _ & Ak & _).
apply NFW.
+ destruct Ha as [Ha|Ha]; [clear - Ha L0 L2 P1 P2 G2; lia|]. pose proof (art_S_ge (fst b0) 0 ltac:(clear - L0 P1; lia)). pose proof (art_S_lt (fst b0 + snd b0 - 1) (2 ^ 44) ltac:(clear - L2 P2 G2; lia)). lia.
+ apply (art_gap_out _ a 1); [|clear; lia]. assert (Hq0 : 1 <= qr) by (clear - Hn Hqr; lia). destruct Ha as [Ha|Ha].
* apply (GSUB p a 1 Hp); [clear - Ha P1; lia|clear - Ha P2; lia|clear - Ha OFF P1 P2 Hq0; lia].
* apply (GSH (fst b0) (snd b0) a); [clear - L0 P1; lia|clear - Hn0; lia|clear - L2 P2; lia|unfold apart in Ak; clear - Ak P1 P2 Hn0; lia|exact Ha|].
apply (USO (fst b0) (snd b0)); [clear - OFF P1 P2; lia|exact Ha].
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_frep_nfp_stack := (ltac2:(TCodec.tc2 tcn__JbtInvFree "J'E&R8&QCvS3%211r1%5221&B'?&R>vR4+TP0%3221r2%=221&R9%1236%9231%;11&R0r3%211%?11p051p0B1pU0I1")) (only parsing).
Variable a : ltac:(sec_ty2 constr:(SEC_T_art_frep_nfp_stack) 0%nat 0%nat).
#[using="LB M M' n b1 kb k REP Eu Hn Hqr Hb1 KIND HS Emu Edep OUT LIVE LIVE2 LIVE3 OKpre a"] Lemma art_frep_nfp_stack : ltac:(sec_stmt2 constr:(SEC_T_art_frep_nfp_stack) 1%nat 0%nat).
Proof.
intros Ha Ns [F|F]; pose proof REP as (ROK & _); rok_open14 ROK; geo_open GEO.
- destruct art_frep_u_far as (_ & U2 & U3 & _). destruct art_frep_ush as (S1 & S2). unfold art_free3_fp, dprivD in F.
clear - F Ha Ns U2 U3 S1 S2 G1 G2 G8 Dl2 Dblk Hn Hqr. lia.
- pose proof (art_frep_zone a F) as Z. clear - Z Ha Ns HS G1 G2 G4 G6 G8 Espb Eris. lia.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_frep_nfp_image := (ltac2:(TCodec.tc2 tcn__JbtInvFree "Q<'E'?&R8+RPP0r1%3221&R9+Vb\P0%2241%8241&B+RQjX8r2%;221+V[jY8%9231%?231%711+QWgR0r3%B221&R7+`TQ@%2251%B251%H251%@11+QiaV8r4%K221+4%:241%J241%Q0241%H11&R0r5%211%L11p051p0>1p0H1p0Q11pU0Q;1")) (only parsing).
Variable a : ltac:(sec_ty2 constr:(SEC_T_art_frep_nfp_image) 0%nat 0%nat).
#[using="LB M M' n b1 kb k REP Eu Hn Hqr Hb1 KIND HS Emu Edep OUT LIVE LIVE2 LIVE3 OKpre a"] Lemma art_frep_nfp_image : ltac:(sec_stmt2 constr:(SEC_T_art_frep_nfp_image) 1%nat 0%nat).
Proof.
intros Ha N1 N2 N3 [F|F]; pose proof REP as (ROK & _ & _ & _ & _ & _ & _ & DEP & _); rok_open14 ROK; geo_open GEO.
- destruct art_frep_u_far as (U1 & _). destruct art_frep_ush as (S1 & S2). unfold art_free3_fp, dprivD in F.
clear - F Ha N1 N2 N3 U1 S1 HS G1 G9 Il2 Iblk. lia.
- pose proof (art_frep_zone a F) as Z. clear - Z Ha HS G1 G4 G9 Espb Eris. lia.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_fgap_fs := (ltac2:(TCodec.tc2 tcn__JbtInvFree "G'E&R8&Q2&QDvS3%211%411r2%7221&R7r3%2214&Q0%4271%=231&Q:&R2r4%33218p051p0<1pUJE1pU0F1")) (only parsing).
Variable a : ltac:(sec_ty2 constr:(SEC_T_art_fgap_fs) 0%nat 0%nat).
Variable len : ltac:(sec_ty2 constr:(SEC_T_art_fgap_fs) 1%nat 0%nat).
#[using="FSG G LB M n b1 kb k qtl cl24 wb b lastb L B cntB REP Eu Hn Hqr Hb1 KIND Edep LIVE LIVE2 LIVE3 a len"] Lemma art_fgap_fs : ltac:(sec_stmt2 constr:(SEC_T_art_fgap_fs) 2%nat 0%nat).
Proof.
intros Ha Hl.
destruct art_frep_u_far as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Uf & _). destruct art_frep_ush as (S1 & S2).
pose proof REP as (ROK & _). rok_open14 ROK. geo_open GEO. destruct Fapp as (_ & Fap & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in Fap.
unfold art_frep_W. cbn [art_gap fst snd]. unfold apart, FS_BYTES in *.
clear - Ha Hl Uf S1 S2 G1 G2 G4 G6 Espb Eris Kspb Fhi Fap Fimg Aft Afk Afl Afb Hn Hqr. repeat split; try exact I; lia.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_fgap_dtls := (ltac2:(TCodec.tc2 tcn__JbtInvFree "E'E&R8&QGvS3%211r2%5221&R7r3%2214+TP0%4271%;231&Q:&R2r4%33218p051p0<1pUJC1pU0D1")) (only parsing).
Variable a : ltac:(sec_ty2 constr:(SEC_T_art_fgap_dtls) 0%nat 0%nat).
Variable len : ltac:(sec_ty2 constr:(SEC_T_art_fgap_dtls) 1%nat 0%nat).
#[using="FSG G LB M n b1 kb k qtl cl24 wb b lastb L B cntB REP Eu Hn Hqr Hb1 KIND Edep LIVE LIVE2 LIVE3 a len"] Lemma art_fgap_dtls : ltac:(sec_stmt2 constr:(SEC_T_art_fgap_dtls) 2%nat 0%nat).
Proof.
intros Ha Hl.
destruct art_frep_u_far as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ud & _). destruct art_frep_ush as (S1 & S2).
pose proof REP as (ROK & _). rok_open14 ROK. geo_open GEO. destruct D3 as (_ & D3' & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in D3'.
unfold art_frep_W. cbn [art_gap fst snd]. unfold apart in *.
clear - Ha Hl Ud S1 S2 G1 G2 G4 G6 Espb Eris Kspb D0 D1 D2 D3' Adt Adk Adl Adb Hn Hqr. repeat split; try exact I; lia.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_fgap_far_sh := (ltac2:(TCodec.tc2 tcn__JbtInvFree "R0'E&R8zr3%3221&R9%1243&R7r5r4%3221&R=+2+Q?%3221%>251'Cr6%;21:&QHvS3%211%E241+TPPPRTP0%A231%H218%:241r7%E21;&R>vS6+@%3221%Q0251&R;+8vS1%3221%O281%Q621<%H271'?&Q1r8%211%Q<21L%Q723C+1%C221%711%QA2Q11%:261&Q:&R2%231K7p041p0@1p0O1p0Q;1p0QE1p0QH1pU0QM1pUJQN1pULQO1")) (only parsing).
Variable lo : ltac:(sec_ty2 constr:(SEC_T_art_fgap_far_sh) 0%nat 0%nat).
Variable len : ltac:(sec_ty2 constr:(SEC_T_art_fgap_far_sh) 1%nat 0%nat).
Variable a : ltac:(sec_ty2 constr:(SEC_T_art_fgap_far_sh) 2%nat 0%nat).
#[using="FSG G LB M n b1 kb k qtl cl24 wb b lastb L B cntB REP Eu Hn Hqr Hb1 KIND Edep LIVE LIVE2 LIVE3 lo len a"] Lemma art_fgap_far_sh : ltac:(sec_stmt2 constr:(SEC_T_art_fgap_far_sh) 3%nat 0%nat).
Proof.
intros Hlo Hlen Hhi Hk Off Ha.
destruct art_frep_u_far as (_ & _ & _ & Ush & _).
pose proof REP as (ROK & _). rok_open14 ROK. geo_open GEO.
pose proof (art_S_ge lo 0 ltac:(lia)) as B0. pose proof (art_S_lt (lo + len - 1) (2 ^ 44) ltac:(clear - Hhi; lia)) as B1.
pose proof (art_frep_ush_off lo len a Off Ha) as Hus.
assert (B2 : a < 2147450880 + 8192 * rn_qs rn + 24 * 2 ^ 29 \/ 2147450880 + 8192 * rn_qs rn + 25 * 2 ^ 29 <= a).
{ destruct Hk as [Hk|Hk].
- left. pose proof (art_S_lt (lo + len - 1) (8192 * rn_qs rn) ltac:(clear - Hk Kspb Espb; lia)) as X. clear - X Ha. lia.
- right. pose proof (art_S_ge lo (8192 * rn_qs rn + 2 ^ 34) ltac:(clear - Hk Kspb Espb; lia)) as X. clear - X Ha. lia. }
unfold art_frep_W. cbn [art_gap fst snd]. unfold apart in G10, Al2s, Abs |- *. clear - Ha B0 B1 B2 Hus Ush G1 G4 G9 G10 Espb Eris Al2s Abs Il2 Iblk Hn Hqr. repeat split; try exact I; lia.
Qed.
End SE.
#[using="LB M Sp u n q16 qr b1 km kb k wb b lastb L B cntB REP Eu Hn Hqr Hb1 KIND HS Emu Edep OUT LIVE LIVE3 OKpre"] Lemma art_frep_tail24 : ltac2:(TCodec.tc2 tcn__JbtInvFree "QB'@'3vRO(>%43321'E'?&R8&Q7vRC%211r1%5221&R9&Q8&Q6+H%2218%411%6281%>281&R:r2+8%3221z%J3E21&Q3vJ&Q1&R7&QMvS3%211&R;&R=+2+Q0%3221%52G1%:271r3%<221%>11+WJ%B3A21p0D1p0K1pVBQ;1p0Q=1").
Proof.
intros En x Hx Hx8.
pose proof REP as (ROK & _ & _ & (_ & PRIM & _) & CH & _). pose proof ROK as ROK'. rok_open14 ROK'. pose proof GEO as GEO'. geo_open GEO'.
destruct art_frep_num as (Hkm & Hkm' & Hbz & HBz & HnL). destruct art_frep_out as (GR & _ & _ & _ & _ & _ & _ & _ & OK' & NEW & _).
pose proof (CH 24 ltac:(lia)) as CH0. cbv zeta in CH0. destruct CH0 as (I0 & _). fold cl24 in I0.
destruct (PRIM 24 ltac:(lia)) as (_ & OK0 & _). fold cl24 in OK0. pose proof OK0 as (_ & (Hau0 & Haumu0) & _ & _ & Hka0 & Hmu30 & _).
assert (ES : forall y, HeapIfaceA.S (rn_spb rn + 24 * 2 ^ 32 + 8 * y) = 2147450880 + 8192 * rn_qs rn + 24 * 2 ^ 29 + y). { intros y. rewrite Espb. apply art_S_lin. }
assert (Ex : x = 8 * (x / 8)). { pose proof (Z.div_mod x 8 ltac:(lia)) as D. rewrite Hx8 in D. lia. }
destruct (Z_lt_ge_dec x (cl_mu cl24)) as [Lo|Hi].
- apply (art_byte_at_eq M M'); [|exact (I0 x ltac:(lia) Hx8)]. rewrite Ex, ES. set (y := x / 8) in *.
assert (UWy : ~ art_uw (2147450880 + 8192 * rn_qs rn + 24 * 2 ^ 29 + y)).
{ intros Hu. pose proof (art_frep_uw_where _ Hu) as W. destruct k as [c w|i].
- destruct KIND as (Hc & (W0 & W1 & _) & _). destruct (PRIM c Hc) as (_ & OKc & _). destruct OKc as (_ & (_ & Haumuc) & _ & _ & _ & Hmu3c & _).
pose proof (art_class_size_facts c Hc) as (Hsz & _). unfold art_in_chunk in W.
destruct (Z.eq_dec 24 c) as [<-|Nc].
{ fold cl24 in W1, Haumuc, Hmu3c. clear - W Hx Lo Ex W0 W1 G4 Espb Hsz Haumuc Hmu3c. lia. }
clear - W Hx Lo Ex Nc Hc W0 W1 G4 Espb Hsz Haumuc Hmu3c Hau0 Hmu30; lia.
- destruct W as (_ & W2). apply W2. clear - Hx Lo Ex Hau0 Hmu30. lia. }
apply (art_frep_eqa 24 _ ltac:(lia)); [right; fold cl24; clear - Hx Lo Ex Hau0; lia| | | | | ].
+ intros X. apply UWy. left. exact X.
+ intros X. apply UWy. right; left. exact X.
+ intros X. apply UWy. right; right. exact X.
+ intros _ E X. specialize (Hbz E). clear - X Hbz Hx Lo Ex Hmu30 Hau0 G4 G6 G2 Espb Eris. lia.
+ intros _ NL X. destruct (HBz NL) as (X1 & X2 & X3). unfold art_B_written in X. clear - X X1 X2 X3 Hx Lo Ex Hmu30 Hau0 G4 G6 G2 Espb Eris. destruct newb; lia.
- destruct (NEW En) as (CPb & PSH & _).
destruct (art_ca_pre_mu_cases 24 cl24) as [(E & _)|(E1 & E2 & E3)]; [rewrite E in Hx; lia|]. rewrite E3 in Hx. rewrite Ex, ES.
pose proof (PSH E1 E2 (x / 8 - 32768 * km) ltac:((clear - Apkb B Edep Emu Ex FSG G Hau0 Haumu0 Hb1 Hi Hx L Plo b b1 cl24 cntB kb km lastb qtl rn wb x; lia))) as C. replace (2147450880 + 8192 * rn_qs rn + 24 * 2 ^ 29 + 32768 * km + (x / 8 - 32768 * km)) with (2147450880 + 8192 * rn_qs rn + 24 * 2 ^ 29 + x / 8) in C by lia.
apply art_byte_of_cell1; [right; clear - Hx Hi Ex Hau0 Haumu0 G4 Espb; lia|clear - Hx Hi Ex Hau0 Haumu0 Hkm Hkm' Emu G4 Espb G6 Eris G2; lia|lia|exact C].
Qed.
#[using="LB M Sp q16 qr b1 km qtl cl24 newb wb b lastb L B cntB REP Eu Hn Hqr Hb1 KIND HS Emu Edep OUT LIVE LIVE2 LIVE3 OKpre"] Lemma art_frep_ghost : art_rt_ghost FSG rn G' M'.
Proof.
pose proof REP as (ROK & _ & _ & (_ & PRIM & _) & CH & _ & QR & _ & _ & _ & (T1 & T23 & T4 & T5)). pose proof ROK as ROK'. rok_open14 ROK'. pose proof GEO as GEO'. geo_open GEO'.
destruct QR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & BCH). destruct art_frep_num as (Hkm & Hkm' & Hbz & HBz & HnL).
destruct (PRIM 24 ltac:(lia)) as (_ & OK24 & _). fold cl24 in OK24. pose proof OK24 as (_ & (Hau24 & Haumu24) & _ & _ & _ & Hmu324 & _).
assert (ES : forall y, HeapIfaceA.S (rn_spb rn + 24 * 2 ^ 32 + 8 * y) = 2147450880 + 8192 * rn_qs rn + 24 * 2 ^ 29 + y). { intros y. rewrite Espb. apply art_S_lin. }
assert (SHB : forall w0 v, art_cptr_ok 8192 (cl_au cl24) w0 -> match k with FKP c w => ~ (24 = c /\ w0 = w) | FKS _ => True end ->
byte_at M (HeapIfaceA.S (rn_spb rn + 24 * 2 ^ 32 + 16 * w0)) v -> byte_at M' (HeapIfaceA.S (rn_spb rn + 24 * 2 ^ 32 + 16 * w0)) v).
{ intros w0 v V Nk Bt. apply (art_byte_at_eq M M'); [|exact Bt]. replace (rn_spb rn + 24 * 2 ^ 32 + 16 * w0) with (rn_spb rn + 24 * 2 ^ 32 + 8 * (2 * w0)) by lia. rewrite ES.
pose proof V as (V0 & V1 & _).
assert (INC : art_in_chunk 24 w0 (2147450880 + 8192 * rn_qs rn + 24 * 2 ^ 29 + 2 * w0)) by (unfold art_in_chunk; right; rewrite art_class_size_24; lia).
pose proof (art_frep_uw_other 24 w0 _ ltac:(lia) ltac:(rewrite art_class_size_24; exact V) Nk INC) as NUW. unfold art_uw in NUW.
apply (art_frep_eqa 24); [lia|right; fold cl24; clear - V0 V1 Haumu24; lia|intros X; apply NUW; left; exact X|intros X; apply NUW; right; left; exact X|intros X; apply NUW; right; right; exact X| |].
- intros _ E X. specialize (Hbz E). clear - X Hbz V0 V1 Haumu24 Hmu324 G4 Espb. lia.
- intros _ NL X. destruct (HBz NL) as (X1 & X2 & X3). unfold art_B_written in X. destruct newb; clear - X X1 X2 X3 V0 V1 Haumu24 Hmu324 G4 Espb; lia. }
unfold art_rt_ghost, G'. cbn [art_gs_free g_qt g_qg g_cls]. fold qtl newb cl24 wb b.
split.
{ intros b0 it Hb0 Hit. apply in_app_or in Hb0. destruct Hb0 as [Hb0|Hb0]; [|exact (T1 b0 it (in_or_app _ _ _ (or_intror Hb0)) Hit)].
assert (NEWIT : fst (u - 16, n) mod 16 = 0). { cbn [fst]. rewrite Eu. replace (16 * q16 - 16) with ((q16 - 1) * 16) by lia. apply Z_mod_mult. }
destruct (art_qt_add_in qtl b (u - 16, n) b0 Hb0) as [(_ & ->)|[Hold|(_ & NEq & ->)]]; cbn [bt_items] in Hit.
- destruct Hit as [<-|[]]. exact NEWIT.
- exact (T1 b0 it (in_or_app _ _ _ (or_introl Hold)) Hit).
- apply in_app_or in Hit. destruct Hit as [Hit|[<-|[]]]; [|exact NEWIT].
exact (T1 (art_lastb qtl) it (in_or_app _ _ _ (or_introl (JbtFxQ.art_last_in _ _ _ NEq))) Hit). }
split.
{ intros c0 Hc0. destruct (Z.eqb_spec c0 24) as [->|NE]; [|exact (T23 c0 Hc0)]. destruct (T23 24 ltac:(lia)) as (X2 & X3). fold cl24 in X2, X3.
unfold art_enq_cls. destruct newb; [exact (art_ghost_cls_pop 24 cl24 ltac:(lia) OK24 X2 X3)|split; assumption]. }
split; [|apply art_frep_cell_img; [left; cbn; lia|exact T5]].
intros b0 Hb0.
assert (OLD : forall b1, In b1 (g_qt FSG G ++ g_qg FSG G) -> byte_at M' (HeapIfaceA.S (bt_addr b1)) 0xfa).
{ intros bx Hbx. destruct (BCH bx Hbx) as (w1 & Ew1 & V1 & St1). rewrite art_class_size_24 in V1. rewrite Ew1. apply SHB; [exact V1| |rewrite <- Ew1; exact (T4 bx Hbx)].
destruct k as [c w|i]; [|exact I]. intros (Ec & Ew). subst c w. destruct KIND as (_ & _ & Stk). rewrite Stk in St1. discriminate St1. }
apply in_app_or in Hb0. destruct Hb0 as [Hb0|Hb0]; [|exact (OLD b0 (in_or_app _ _ _ (or_intror Hb0)))].
destruct (art_qt_add_in qtl b (u - 16, n) b0 Hb0) as [(En & ->)|[Hold|(_ & NEq & ->)]]; cbn [bt_addr].
-
destruct art_frep_out as (_ & _ & _ & _ & _ & _ & _ & _ & _ & NEW & _). destruct (NEW En) as (CPb & _).
pose proof (art_frep_wb_free En) as Stb.
pose proof CPb as (Wb0 & Wb1 & _). pose proof (OKpre En) as OKp. destruct OKp as (_ & (_ & Haumup) & _).
destruct (art_ca_cptr_origin 24 cl24 ltac:(lia) OK24) as [Hin0|(_ & _ & Hlo)]; fold wb in Hin0 || fold wb in Hlo.
+
destruct OK24 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FA & _). pose proof (proj1 (Forall_forall _ _) FA wb Hin0) as Vwb. rewrite art_class_size_24 in Vwb.
destruct (CH 24 ltac:(lia)) as (_ & _ & _ & III). cbv zeta in III. fold cl24 in III. specialize (III wb ltac:(rewrite art_class_size_24; exact Vwb)). rewrite Stb in III. destruct III as (_ & B0).
unfold b. apply SHB; [exact Vwb| |exact B0]. destruct k as [c w|i]; [|exact I]. intros (Ec & Ew). subst c w. destruct KIND as (_ & _ & Stk). fold wb in Stk. rewrite Stk in Stb. discriminate Stb.
+
unfold b. apply (art_frep_tail24 En (16 * wb)); [clear - Hlo Wb1 Haumup; lia|]. replace (16 * wb) with (2 * wb * 8) by lia. apply Z_mod_mult.
- exact (OLD b0 (in_or_app _ _ _ (or_introl Hold))).
- exact (OLD (art_lastb qtl) (in_or_app _ _ _ (or_introl (JbtFxQ.art_last_in _ _ _ NEq)))).
Qed.
#[using="M Sp q16 qr b1 km qtl cl24 newb wb b lastb L B cntB REP Hin Eu Hn Hqr Hb1 Hty Cn KIND HS Emu Edep OUT LIVE LIVE2 LIVE3 OKpre Hother"] Theorem art_alloc_rep_free_pre : art_alloc_rep_b FSG (2 ^ 29) rn G' (lb_remove u LB) M'.
Proof.
pose proof REP as (ROK & _).
split; [exact ROK|]. split; [exact art_frep_statics|]. split; [exact art_frep_thread|]. split; [exact art_frep_primary|]. split; [exact art_frep_chunks|].
split; [exact art_frep_sec|]. split; [exact art_frep_quar|]. split; [exact art_frep_depot|]. split; [exact art_frep_ia|]. split; [exact art_frep_blocks|exact art_frep_ghost].
Qed.
#[using="b1 REP Hin Eu Hn Hqr Hb1 Hty Cn KIND HS Emu Edep OUT LIVE LIVE2 LIVE3 OKpre Hother"] Theorem art_frep_bundle :
art_alloc_rep_b FSG (2 ^ 29) rn G' (lb_remove u LB) M'
/\ art_batches_bytes (g_qt FSG G') = art_batches_bytes qtl + n + (if newb then 8192 else 0)
/\ (forall x : word, ~ art_free_fpl (U x) -> M' x = M x)
/\ (forall b0 a, In b0 (lb_remove u LB) -> (fst b0 <= a < fst b0 + snd b0 \/ in_shadow_of (fst b0) (snd b0) a) -> ~ art_free_fpl a)
/\ (forall a, 0 <= a < 2 ^ 64 -> art_out art_frep_W a -> ~ art_free_fpl a)
/\ (forall a, rn_HI rn <= a -> ~ (Sp - 4096 <= a < Sp) -> ~ art_free_fpl a)
/\ (forall a, 0x10000 <= a < 0x693000 -> ~ (0x20e908 <= a < 0x65e928) -> ~ (0x13dc40 <= a < 0x13dc40 + 0x81030) -> ~ (0x1cc4c8 <= a < 0x1cc4c8 + 4) -> ~ art_free_fpl a)
/\ (forall a len, ar_fs (rn_ar rn) <= a -> a + len <= ar_fs (rn_ar rn) + FS_BYTES -> art_gap art_frep_W a len)
/\ (forall a len, rn_dtls rn <= a -> a + len <= rn_dtls rn + 4096 -> art_gap art_frep_W a len)
/\ (forall a len, rn_t rn <= a -> a + len <= rn_t rn + 4096 -> (a + len <= rn_t rn + 80 \/ rn_t rn + 2888 <= a) -> art_gap art_frep_W a len)
/\ (forall lo len a, 0 <= lo -> 0 < len -> lo + len <= 2 ^ 47 -> (lo + len <= rn_kbase rn \/ rn_kbase rn + 0x2000011000 <= lo) ->
(lo + len <= u - 16 \/ u + 8 * qr <= lo) -> HeapIfaceA.S lo <= a <= HeapIfaceA.S (lo + len - 1) -> art_gap art_frep_W a 1)
/\ (0x693000 <= u - 16 /\ u + 8 * qr <= rn_HI rn /\ apart (u - 16) (16 + 8 * qr) (ar_fs (rn_ar rn)) FS_BYTES).
Proof.
split; [exact art_alloc_rep_free_pre|]. split; [unfold G'; cbn [art_gs_free g_qt]; rewrite art_qt_add_bytes; reflexivity|]. split; [exact art_frep_lin|]. split; [exact art_frep_nfp_block|].
split; [exact art_frep_nfp_W|]. split; [exact art_frep_nfp_stack|]. split; [exact art_frep_nfp_image|]. split; [exact art_fgap_fs|]. split; [exact art_fgap_dtls|].
split; [exact art_fgap_thread|]. split; [exact art_fgap_far_sh|].
destruct art_frep_u_far as (U1 & U2 & _ & _ & _ & _ & _ & _ & _ & Uf & _). repeat split; assumption.
Qed.
#[using="Type"] Lemma art_batch_list_last_cells_len : ltac2:(TCodec.tc2 tcn__JbtInvFree "Q8'S4yR0%211';y8%511%311p051'8'Q=%211'E&Q>r5&2r4(4r3(:%11:%43;31%73<61r2r1%<4;321'D&7'<%12AA&QB%11?%5231uoM%8221p0:1pUFH1pU<I1pUHL1pV6L1pQHQ01").
Proof.
intros M0 r. induction r as [|x0 r' IH]; intros lb f l BL.
- cbn [app art_batch_list] in BL. destruct BL as (_ & Hl & _). exact Hl.
- change ((x0 :: r') ++ [lb]) with (x0 :: (r' ++ [lb])) in BL. cbn [art_batch_list] in BL. destruct BL as (_ & _ & _ & _ & _ & _ & R). exact (IH lb _ _ R).
Qed.
Section SE.
Local Abbreviation SEC_T_art_frep_hp24 := (ltac2:(TCodec.tc2 tcn__JbtInvFree "Q7'E'?&R8&R>vS6+@%3221r1%6221&R9+<%8271%3251%<251&B&Q<vROvR4+RU0%@221&QNvS3%211&QM%113&QL%115&QK%117vRIvR@vFv0vRDr2%D<C@=;97654321%F11p0H1pVBQ61")) (only parsing).
Variable x : ltac:(sec_ty2 constr:(SEC_T_art_frep_hp24) 0%nat 0%nat).
#[using="LB M n q16 qr b1 kb k REP Eu Hn Hqr Hb1 KIND HS Emu Edep LIVE LIVE2 LIVE3 OKpre x"] Lemma art_frep_hp24 : ltac:(sec_stmt2 constr:(SEC_T_art_frep_hp24) 1%nat 0%nat).
Proof.
intros Hx F.
destruct art_frep_u_far as (U1 & U2 & U3 & U4 & Ut & _ & _ & _ & _ & _ & _ & Uris & Ufa).
pose proof (art_frep_uw_where x (or_introl Hx)) as W. pose proof art_frep_wb_free as WBF.
pose proof REP as (ROK & _ & _ & (_ & PRIM & _) & CH & _ & QR & _). rok_open14 ROK. geo_open GEO.
destruct (PRIM 24 ltac:(lia)) as (_ & OK24 & _). pose proof OK24 as (_ & (Hau24 & Haumu24) & _ & _ & _ & Hmu324 & _).
assert (Hq0 : 1 <= qr) by (clear - Hn Hqr; lia).
assert (HBW : L <> 0 -> exists wB, B = rn_spb rn + 24 * 2 ^ 32 + 16 * wB /\ art_cptr_ok 8192 (cl_au (g_cls FSG G 24)) wB /\ g_st FSG G 24 wB = CBatch /\ 0 <= cntB <= 1021).
{ intros NL. assert (NEq : qtl <> []) by (intros E; apply NL; unfold L; rewrite E; reflexivity).
assert (InB : In lastb (g_qt FSG G ++ g_qg FSG G)). { apply in_or_app. left. unfold lastb, art_lastb. apply JbtFxQ.art_last_in. exact NEq. }
destruct QR as ((f & l & _ & _ & _ & _ & BL) & _ & _ & _ & _ & _ & _ & _ & _ & BCH). destruct (BCH lastb InB) as (wB & EwB & VB & StB). rewrite art_class_size_24 in VB.
exists wB. split; [exact EwB|]. split; [exact VB|]. split; [exact StB|]. pose proof (art_qt_split qtl NEq) as ESP. pose proof BL as BL'. fold qtl in BL'. rewrite ESP in BL'.
pose proof (art_batch_list_last_cells_len M (removelast qtl) (art_lastb qtl) f l BL') as HLEN. unfold cntB, lastb. clear - HLEN. lia. }
assert (HPB : newb = true -> art_cptr_ok 8192 (cl_au (art_ca_pre 24 cl24)) wb /\ cl_au cl24 <= cl_au (art_ca_pre 24 cl24) /\ cl_au (art_ca_pre 24 cl24) <= 3758096384).
{ intros E. pose proof (OKpre E) as OKp. pose proof OKp as (_ & (_ & Haumup) & _ & _ & _ & Hmu3p & _ & _ & _ & Hforp & _). rewrite art_class_size_24 in Hforp.
split; [apply (proj1 (Forall_forall _ _) Hforp); apply in_or_app; left; exact (art_ca_cptr_in 24 cl24 ltac:(lia) OK24)|]. split; [|clear - Haumup Hmu3p; lia].
destruct (art_ca_pre_au 24 cl24) as [E0|(_ & _ & E0)]; rewrite E0; [lia|]. assert (0 <= art_cls_new 24 cl24 * AsanTab.class_size 24); [|lia].
apply Z.mul_nonneg_nonneg; [|rewrite art_class_size_24; lia]. unfold art_cls_new. apply Z.div_pos; [|rewrite art_class_size_24; lia]. unfold cl24 in *. lia. }
assert (R24 : ~ (rn_spb rn + 24 * 2 ^ 32 <= x < rn_spb rn + 25 * 2 ^ 32)
\/ (exists w, k = FKP 24 w /\ art_cptr_ok 8192 (cl_au (g_cls FSG G 24)) w /\ g_st FSG G 24 w = CAlloc u n
/\ rn_spb rn + 24 * 2 ^ 32 + 16 * w <= x < rn_spb rn + 24 * 2 ^ 32 + 16 * w + 8192)).
{ pose proof KIND as KD. destruct k as [c w|i].
- destruct KD as (Hc & V & St). unfold art_in_chunk in W. destruct (PRIM c Hc) as (_ & OKc & _). destruct OKc as (_ & (_ & Haumuc) & _ & _ & _ & Hmu3c & _).
pose proof (art_class_size_facts c Hc) as (Hszc & _). pose proof V as (V0 & V1 & _).
destruct (Z.eq_dec c 24) as [->|Nc].
+ right. exists w. rewrite art_class_size_24 in V, V1, W. split; [reflexivity|]. split; [exact V|]. split; [exact St|]. clear - W Hx U4 Hq0 V0 V1 Haumuc Hmu3c G4 G2 G6 Eris Espb. lia.
+ left. clear - W Hx Nc Hc V0 V1 Haumuc Hmu3c Hszc U4 G4 G2 G6 Eris Espb. lia.
- left. destruct W as (W1 & _). clear - W1. lia. }
assert (Xt : x + 4 <= rn_t rn \/ rn_t rn + 4096 <= x) by (unfold apart in Ut; clear - Ut Hx Hq0; lia).
assert (Xr : x + 4 <= rn_ris rn \/ rn_ris rn + 4096 <= x) by (unfold apart in Uris; clear - Uris Hx; lia).
assert (Xfa : x + 4 <= rn_spb rn + 24 * 2 ^ 32 + 3758096384 \/ rn_spb rn + 24 * 2 ^ 32 + 3758096384 + 2 ^ 29 <= x) by (unfold apart in Ufa; clear - Ufa Hx; lia).
assert (Xsh : x < 0x7fff7000 \/ 0x10007fff8000 <= x) by (clear - U4 Hx Hq0; lia).
assert (Xhi : x < rn_HI rn) by (clear - U3 Hx; lia).
assert (SHB : 2147450880 + 8192 * rn_qs rn + 25 * 2 ^ 29 <= 0x10007fff8000 /\ 0x7fff8000 <= 2147450880 + 8192 * rn_qs rn) by (clear - G4 G6 G2 Eris Espb; lia).
unfold art_enq_fp in F. destruct (Bool.bool_dec newb true) as [En|En].
- rewrite En in F. destruct (HPB En) as (CPb & Haup & Haup3). unfold art_enq_new_fp, art_refill_fp in F.
destruct F as [F|[[F|[F|[F|[F|[F|[F|[F|[F|[F|F]]]]]]]]]|[F|[F|[F|F]]]]]; try (clear - F Hx Xt Xr Xfa Xsh Xhi SHB HS Emu Hmu324 Haumu24 Hau24; unfold cl24 in *; lia).
+ destruct F as (c' & Hc' & F). clear - F Xt Hc'. lia.
+ destruct R24 as [R24|(w & Ek & (V0 & V1 & _) & _ & Rw)]; [clear - F R24 Emu Hmu324 Haumu24 Hau24; unfold cl24 in *; lia|].
clear - F Rw V1 Haumu24 Emu. unfold cl24 in *. lia.
+ destruct R24 as [R24|(w & Ek & V & St & Rw)]; [destruct CPb as (P0 & P1 & _); unfold b in F; clear - F R24 P0 P1 Haup3; lia|].
assert (Nw : w <> wb) by (intros ->; rewrite (WBF En) in St; discriminate).
pose proof (art_cptr_apart 8192 (cl_au (art_ca_pre 24 cl24)) w wb ltac:(clear; lia) (art_cptr_mono _ _ _ _ Haup V) CPb Nw) as AP. unfold b in F. clear - F Rw AP. lia.
+ destruct F as (NL & F). destruct (HBW NL) as (wB & EB & VB & StB & _).
destruct R24 as [R24|(w & Ek & V & St & Rw)]; [destruct VB as (P0 & P1 & _); rewrite EB in F; clear - F R24 P0 P1 Haumu24 Hmu324; lia|].
assert (Nw : w <> wB) by (intros ->; rewrite StB in St; discriminate).
pose proof (art_cptr_apart 8192 (cl_au (g_cls FSG G 24)) w wB ltac:(clear; lia) V VB Nw) as AP. rewrite EB in F. clear - F Rw AP. lia.
- apply Bool.not_true_is_false in En. rewrite En in F. destruct (art_free_newb_false qtl En) as (NEq & X4).
assert (NL : L <> 0) by (intros E; apply NEq; apply length_zero_iff_nil; unfold L in E; lia). destruct (HBW NL) as (wB & EB & VB & StB & X3).
assert (FB : (Sp - 2208 - 64 <= x < Sp - 2208) \/ (rn_t rn + 104 <= x < rn_t rn + 112) \/ (B <= x < B + 8192)).
{ fold lastb in X4. fold cntB in X4. clear - F X3 X4. lia. }
destruct FB as [FB|[FB|FB]]; [clear - FB Xhi HS; lia|clear - FB Xt; lia|].
destruct R24 as [R24|(w & Ek & V & St & Rw)]; [destruct VB as (P0 & P1 & _); rewrite EB in FB; clear - FB R24 P0 P1 Haumu24 Hmu324; lia|].
assert (Nw : w <> wB) by (intros ->; rewrite StB in St; discriminate).
pose proof (art_cptr_apart 8192 (cl_au (g_cls FSG G 24)) w wB ltac:(clear; lia) V VB Nw) as AP. rewrite EB in FB. clear - FB Rw AP. lia.
Qed.
End SE.
#[using="FSG rn G b1 kb qtl cl24 wb b lastb L B cntB Hb1 Edep"] Lemma art_wr_of_bytes0 : ltac2:(TCodec.tc2 tcn__JbtInvFree "QA'S4yR0%211';y8%511%311p051'E&R8zr2%3221&R9&R7r3%2215&R=+2+R0%3221%8251'?r1%?2>1r4%=231%5231'A&Q3r8r7%B21A%4331:qV@J1%72K1p091pU>M1&N&R3r6r5%44321Ap061p0G1p0Q11pUJQ61pU0Q71pQHQ91").
Proof.
intros M0 a len Ha Hl H d j Hd Hk. apply store_ok_of_all; [rewrite art_u_lit by lia; lia|]. intros x Hx. rewrite art_u_lit in Hx by lia.
destruct (H (U x - a) ltac:(lia)) as (v & Bv). unfold byte_at in Bv. replace (a + (U x - a)) with (U x) in Bv by lia. rewrite Z_to_bv_bv_unsigned in Bv.
unfold wview. rewrite Bv. discriminate.
Qed.
#[using="rn LB M n q16 qr b1 kb k cl24 wb b cntB REP Eu Hn Hqr Hb1 KIND Edep LIVE LIVE2 LIVE3"] Lemma art_frep_u_B : ltac2:(TCodec.tc2 tcn__JbtInvFree "A&B'@'EvFz%43321%611&L&R>vS6+@%3221+Hv0+XP0%844321p0:1").
Proof.
intros NL. destruct art_frep_u_far as (U1 & U2 & U3 & U4 & _). pose proof art_frep_where as WH. unfold art_free_where in WH. pose proof art_frep_live_far as LFAR.
pose proof REP as (ROK & _ & _ & (_ & PRIM & _) & _ & _ & QR & _). rok_open14 ROK. geo_open GEO.
destruct (PRIM 24 ltac:(lia)) as (_ & OK24 & _). pose proof OK24 as (_ & (Hau24 & Haumu24) & _ & _ & _ & Hmu324 & _).
assert (NEq : qtl <> []) by (intros E; apply NL; unfold L; rewrite E; reflexivity).
assert (InB : In lastb (g_qt FSG G ++ g_qg FSG G)). { apply in_or_app. left. unfold lastb, art_lastb. apply JbtFxQ.art_last_in. exact NEq. }
destruct QR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & BCH). destruct (BCH lastb InB) as (wB & EwB & VB & StB). rewrite art_class_size_24 in VB. fold B in EwB. pose proof VB as (VB0 & VB1 & _).
unfold apart. pose proof KIND as KD. destruct k as [c w|i].
- destruct KD as (Hc & V & St). destruct WH as (L1 & L2). pose proof V as (V0 & V1 & _). pose proof (art_class_size_facts c Hc) as (Hsz & Hsz16).
destruct (PRIM c Hc) as (_ & OKc & _). destruct OKc as (_ & (_ & Haumuc) & _ & _ & _ & Hmu3c & _).
rewrite <- (Z.div_exact _ 16) in Hsz16 by lia.
assert (Hend16 : u + 16 <= rn_spb rn + c * 2 ^ 32 + 16 * w + AsanTab.class_size c) by (clear - L2 Hsz16 Espb Eu Hn; lia).
destruct (Z.eq_dec c 24) as [->|Nc].
+ assert (Nw : w <> wB) by (intros ->; rewrite StB in St; discriminate). rewrite art_class_size_24 in V, Hend16.
pose proof (art_cptr_apart 8192 (cl_au (g_cls FSG G 24)) w wB ltac:(clear; lia) V VB Nw) as AP. rewrite EwB. clear - AP L1 Hend16. lia.
+ rewrite EwB. clear - Nc Hc L1 Hend16 V0 V1 Haumuc Hmu3c VB0 VB1 Haumu24 Hmu324 Hsz. lia.
- destruct WH as (p & Hp & L1 & L2). destruct (LFAR p Hp) as (_ & _ & _ & _ & _ & Ak & _). destruct (LIVE3 p Hp) as (A1 & A2).
rewrite <- (Z.div_exact _ 4096) in A1 by lia. rewrite <- (Z.div_exact _ 4096) in A2 by lia.
assert (Hend16 : u + 16 <= fst p + snd p) by (clear - L2 A1 A2 Eu Hn; lia).
unfold apart in Ak. rewrite EwB. clear - Ak L1 Hend16 VB0 VB1 Haumu24 Hmu324 Kspb Kend. lia.
Qed.
#[using="FSG rn G LB n q16 b1 kb k qtl cl24 wb b lastb L B cntB REP Eu Hn KIND Edep LIVE3"] Lemma art_frep_wr_hdr : ltac2:(TCodec.tc2 tcn__JbtInvFree "9&N&R3vI&R>vS6+@%3221+H%847621").
Proof.
pose proof art_frep_where as WH. unfold art_free_where in WH. pose proof REP as (ROK & _ & _ & (_ & PRIM & _) & _ & SECR & _). rok_open14 ROK. geo_open GEO.
pose proof KIND as KD. destruct k as [c w|i].
- destruct KD as (Hc & V & St). destruct WH as (L1 & L2). pose proof V as (V0 & V1 & _). pose proof (art_class_size_facts c Hc) as (Hsz & Hsz16).
destruct (PRIM c Hc) as (RC & OKc & _). destruct OKc as (_ & (_ & Haumuc) & _). destruct RC as [_ RR]. pose proof RR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Wu).
rewrite <- (Z.div_exact _ 16) in Hsz16 by lia.
assert (Hend16 : u + 16 <= rn_spb rn + c * 2 ^ 32 + 16 * w + AsanTab.class_size c) by (clear - L2 Hsz16 Espb Eu Hn; lia).
eapply wr_sub; [exact Wu| |]; clear - L1 Hend16 V0 V1 Haumuc; lia.
- destruct KD as (s & Hs & Hq & Esu & Esn). destruct SECR as (_ & _ & _ & _ & _ & _ & _ & _ & SALL & _). destruct (SALL i s Hs) as (_ & P2 & P3 & _ & _ & _ & P7 & P8 & _).
destruct (LIVE3 _ P2) as (A1 & A2). cbn [fst snd] in A1, A2. rewrite <- (Z.div_exact _ 4096) in A1 by lia. rewrite <- (Z.div_exact _ 4096) in A2 by lia. rewrite Esu in P7. rewrite Esu, Esn in P8.
eapply wr_sub; [exact P3| |]; clear - P7 P8 A1 A2 Eu Hn; lia.
Qed.
#[using="FSG rn G LB b1 kb k qtl cl24 wb b lastb L B cntB REP Eu Hn Hqr Hb1 KIND Edep LIVE LIVE2 LIVE3"] Lemma art_frep_wr_sh : ltac2:(TCodec.tc2 tcn__JbtInvFree "A&Q5vIvS6vRN%43321&N&R3&R7+QoooPP0&R;+2vS0%3221%6251vS1%:49>21p0<1").
Proof.
intros SB0. destruct art_frep_ush as (S1 & S2).
assert (ES : HeapIfaceA.S u = 2147450880 + 2 * q16). { rewrite Eu. pose proof (art_S_lin 0 0 (2 * q16)) as X. replace (65536 * 0 + 0 * 2 ^ 32 + 8 * (2 * q16)) with (16 * q16) in X by lia. rewrite X. lia. }
apply art_wr_of_bytes0; [lia|lia|]. intros i Hi. rewrite <- ES.
pose proof (Z.div_mod n 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as Rm.
destruct (Z_lt_ge_dec i (n / 8)) as [Lo|Hi']; [exact (shadow_blkR_bytes M u n ltac:(lia) SB0 i ltac:(lia) (or_introl Lo))|].
assert (Ei : i = n / 8) by (clear - Hi Hi' Hqr D Rm; lia). assert (Nm : n mod 8 <> 0) by (clear - Hi Ei Hqr D Rm; lia).
exact (shadow_blkR_bytes M u n ltac:(lia) SB0 i ltac:(lia) (or_intror (conj Ei Nm))).
Qed.
End Rep.
