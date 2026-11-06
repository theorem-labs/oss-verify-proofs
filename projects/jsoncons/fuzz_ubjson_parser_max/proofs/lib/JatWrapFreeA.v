(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim StoreOk Hoare AsanAcct HeapIface HeapIfaceA As0Tables
ArtMem JatLeaf JatAllocG JatPoison JatRzLog JatAllocA JatInitCache JatPopulate1 ArtRuns ArtRunsMem JatCls JatFp JatClsRep JatClsGfa2 JatClsRefill JatCellEx JatByteCell
JatCARSpec JatAlloc3Pure JatDepotA JatDepot JatUnwind ArtBridge JatAllocate3 JatInv JatInvMallocPure JatInvMalloc JatFxQ JatFxBatch2 JatFxBatch3 JatFxImg JatFreeTop3 JatInvFreePure JatInvFree.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require JatImgCell JatPoison3.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import HeapIfaceAJx ShadowRLaws.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JatWrapFreeA () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JatInvFreePure."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1app"; "1cons"; "1length"; "1list"; "1nil"; "1option"; "1prod"; "1snd"; "2and"; "2eq"; "2ex"; "3le"; "4Z"; "0M"; "0M0"; "5cell"]; ["5wr"; "6byte_at"; "7art_batch"; "7art_batch_list"; "7art_batches_bytes"; "7bt_addr"; "7bt_items"; "8art_bt_bytes"; "9loaded_segments"; ":In"; ";add"; ";le"; ";lt"; ";mul"; ";of_nat"; ";pow"]; ["0a"; "0b"; "0bs"; "0f"; "0i"; "0it"; "0l"; "0lb"; "0n"; "0r"; "<bv"; "0v"]]).
Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Lemma art_bt_bytes_ge : ltac2:(TCodec.tc2 tcn__JatWrapFreeA "G'B'6'<%2211&Ir1&Fr2%211%53641&Kz&7%13;;6%4231p061pR<=1+XP0&G%11<%:231p051pR4F1").
Proof.
intros b H. unfold art_bt_bytes. induction (bt_items b) as [|x r IH]; cbn [fold_right]; [lia|].
pose proof (H x (or_introl eq_refl)). specialize (IH (fun it Hi => H it (or_intror Hi))). lia.
Qed.
Lemma art_batches_bytes_cons : ltac2:(TCodec.tc2 tcn__JatWrapFreeA "C'B'3%112'9'<&D(1r2r1%33921%511&J&G%116%916%4221%=3<61pRD?1pR4B1").
Proof. intros b r. unfold art_batches_bytes, art_bt_bytes. cbn [fold_right]. lia. Qed.
Lemma art_batches_bytes_ge : ltac2:(TCodec.tc2 tcn__JatWrapFreeA "Q='3'B%211'6'<%2211&Ir2r3%33821&F%113%63751&Kz&7%13<<8%4231p061p0:1pR<?1pR4D1'8&M+XP0&N&2%12JD%311%6251&D%11H%C231r1%L3Q11J&G%11Mr4%811%J231p061pR4Q81%D2:1p0F1pR6Q:1").
Proof.
induction bs as [|x r IH]; intros H; [split; [cbn; lia|intros b []]|].
destruct (IH (fun b it Hb Hi => H b it (or_intror Hb) Hi)) as (I1 & I2). pose proof (art_bt_bytes_ge x (fun it Hi => H x it (or_introl eq_refl) Hi)) as Hx.
rewrite art_batches_bytes_cons. split; [cbn [length]; lia|]. intros b [<-|Hb]; [lia|]. specialize (I2 b Hb). lia.
Qed.
Section SE.
Variables (M0 : word -> option byte).
Lemma art_batch_list_last_hdr : forall r lb f l, art_batch_list M0 (r ++ [lb]) f l ->
(length (bt_items lb) <= 1021)%nat /\ cellA M0 (bt_addr lb + 16) 8 (Z.of_nat (length (bt_items lb))) /\ cellA M0 (bt_addr lb + 8) 8 (art_bt_bytes lb).
Proof.
intros r.
induction r as [|x r' IH]; intros lb f l BL.
- cbn [app art_batch_list] in BL. destruct BL as (_ & Hl & C1 & C2 & _). split; [exact Hl|]. split; [exact C1|exact C2].
- change ((x :: r') ++ [lb]) with (x :: (r' ++ [lb])) in BL. cbn [art_batch_list] in BL. destruct BL as (_ & _ & _ & _ & _ & _ & R). exact (IH lb _ _ R).
Qed.
End SE.
Lemma art_wr_of_bytes : ltac2:(TCodec.tc2 tcn__JatWrapFreeA "QA'Q:yR0%211'5y8%511%311p051'<&Kzr2%3221&L&Jr3%2215&O+2+R0%3221%8251'8r1%?2>1r4%=231%5231':&Ar8r7%B21A%4331:qRHJ1%72K1p091pR:M1&@&Hr6r5%44321Ap061p0G1p0Q11pRBQ61pR2Q71pLQ91").
Proof.
intros M a n Ha Hn H d k Hd Hk. apply store_ok_of_all; [rewrite art_u_lit by lia; lia|]. intros x Hx. rewrite art_u_lit in Hx by lia.
destruct (H (U x - a) ltac:(lia)) as (v & Bv). unfold byte_at in Bv. replace (a + (U x - a)) with (U x) in Bv by lia. rewrite Z_to_bv_bv_unsigned in Bv.
unfold wview. rewrite Bv. discriminate.
Qed.
Section EntryFacts.
Variable FSG : Type.
Variables (rn : art_run) (G : art_gs FSG) (LB : list (Z * Z)) (M : word -> option byte).
Hypothesis REP : art_alloc_rep FSG rn G LB M.
#[using="rn M REP"] Lemma art_wfa_kind : forall u n, In (u, n) LB ->
exists k, match k with
| FKP c w => 1 <= c <= 30 /\ art_cptr_ok (AsanTab.class_size c) (cl_au (g_cls FSG G c)) w /\ g_st FSG G c w = CAlloc u n
| FKS i => exists s, nth_error (g_sec FSG G) i = Some s /\ sc_quar s = false /\ sc_u s = u /\ sc_n s = n
end.
Proof.
intros u n Hin. destruct REP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & BLK & _). destruct (BLK (u, n) Hin) as [(c & w & Hc & V & St)|(s & Hs & Hq & Eu & En)]; cbn [fst snd] in *.
- exists (FKP c w). split; [exact Hc|]. split; [exact V|exact St].
- destruct (In_nth_error _ _ Hs) as (i & Hi). exists (FKS i). exists s. repeat split; assumption.
Qed.
Section SE.
Local Abbreviation SEC_T_art_wfa_hdr := (forall u n k, match k with
| FKP c w => 1 <= c <= 30 /\ art_cptr_ok (AsanTab.class_size c) (cl_au (g_cls FSG G c)) w /\ g_st FSG G c w = CAlloc u n
| FKS i => exists s, nth_error (g_sec FSG G) i = Some s /\ sc_quar s = false /\ sc_u s = u /\ sc_n s = n
end ->
art_chunk_hdr M u n 2 /\ HAJ.shadow_blkR M u n) (only parsing).
Variable u : ltac:(sec_ty2 constr:(SEC_T_art_wfa_hdr) 0%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_wfa_hdr) 1%nat 0%nat).
Lemma art_wfa_hdr : ltac:(sec_stmt2 constr:(SEC_T_art_wfa_hdr) 2%nat 0%nat).
Proof using rn LB REP u n.
intros k KIND.
destruct REP as (_ & _ & _ & _ & CH & SECR & _). destruct k as [c w|i].
- destruct KIND as (Hc & V & St). specialize (CH c Hc). cbv zeta in CH. destruct CH as (_ & _ & _ & III). specialize (III w V). rewrite St in III.
destruct III as (_ & _ & _ & J4 & J5 & _). split; assumption.
- destruct KIND as (s & Hs & Hq & Esu & Esn). destruct SECR as (_ & _ & _ & _ & _ & _ & _ & _ & SALL & _). destruct (SALL i s Hs) as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _).
rewrite Hq in P9. rewrite Esu, Esn in P9. destruct P9 as (_ & Q2 & Q3). split; assumption.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_wfa_items := (forall b it, In b (g_qt FSG G ++ g_qg FSG G) -> In it (bt_items b) -> 1 <= snd it) (only parsing).
Variable b : ltac:(sec_ty2 constr:(SEC_T_art_wfa_items) 0%nat 0%nat).
Variable it : ltac:(sec_ty2 constr:(SEC_T_art_wfa_items) 1%nat 0%nat).
Lemma art_wfa_items : ltac:(sec_stmt2 constr:(SEC_T_art_wfa_items) 2%nat 0%nat).
Proof using rn LB M REP b it.
intros Hb Hit.
destruct REP as (_ & _ & _ & _ & CH & SECR & QR & _). destruct QR as (_ & _ & _ & _ & _ & _ & _ & ITEMS & _).
destruct (ITEMS b it Hb Hit) as [(c & w & Hc & V & St)|(s & Hs & Hq & Esu & Esn)].
- specialize (CH c Hc). cbv zeta in CH. destruct CH as (_ & _ & _ & III). specialize (III w V). rewrite St in III. destruct III as (_ & _ & (bb & _ & _ & _ & _ & Hn0) & _). lia.
- destruct SECR as (_ & _ & _ & _ & _ & _ & _ & _ & SALL & _). destruct (In_nth_error _ _ Hs) as (i & Hi). destruct (SALL i s Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _).
rewrite Hq in P9. destruct P9 as ((bb & _ & _ & _ & _ & Hn0) & _). rewrite <- Esn. lia.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_wfa_thq := (forall n, 1 <= n < 2 ^ 28 ->
let qtl := g_qt FSG G in let lastb := art_lastb qtl in let L := Z.of_nat (length qtl) in let B := bt_addr lastb in let cntB := Z.of_nat (length (bt_items lastb)) in
0 <= L < 2 ^ 63 /\ 0 <= B < 2 ^ 63 /\ 0 <= art_batches_bytes qtl /\ art_batches_bytes qtl + n + 8192 < 2 ^ 64
/\ cellA M (rn_t rn + 80) 8 L /\ cellA M (rn_t rn + 80 + 24) 8 (art_batches_bytes qtl)
/\ exists wB, (L <> 0 -> B = rn_spb rn + 24 * 2 ^ 32 + 16 * wB /\ art_cptr_ok 8192 (cl_au (g_cls FSG G 24)) wB /\ ~ In wB (cl_cache (g_cls FSG G 24) ++ cl_free (g_cls FSG G 24))
/\ cellA M (rn_t rn + 80 + 16) 8 B /\ cellA M (B + 16) 8 cntB /\ cellA M (B + 8) 8 (art_bt_bytes lastb) /\ 0 <= cntB <= 1021
/\ 0 <= art_bt_bytes lastb /\ art_bt_bytes lastb + n < 2 ^ 64)) (only parsing).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_wfa_thq) 0%nat 0%nat).
Lemma art_wfa_thq : ltac:(sec_stmt2 constr:(SEC_T_art_wfa_thq) 1%nat 0%nat).
Proof using LB REP n.
intros Hn qtl lastb L B cntB.
pose proof REP as (ROK & _ & _ & (_ & PRIM & _) & CH & _ & QR & _). destruct ROK as (GEO & _). geo_open GEO.
destruct QR as ((ft & lt & Ct80 & Ct88 & Ct96 & Ct104 & BLt) & _ & Bt & _ & _ & _ & _ & _ & _ & BCH). fold qtl in Ct80, Ct104, BLt, Bt.
assert (POS : forall b it, In b qtl -> In it (bt_items b) -> 0 <= snd it). { intros b it Hb Hit. pose proof (art_wfa_items b it (in_or_app _ _ _ (or_introl Hb)) Hit). lia. }
destruct (art_batches_bytes_ge qtl POS) as (BY1 & BY2).
assert (HL : 0 <= L < 2 ^ 63) by (unfold L; lia).
assert (HB : L <> 0 -> In lastb qtl). { intros NL. unfold lastb, art_lastb. apply JatFxQ.art_last_in. intros E. apply NL. unfold L. rewrite E. reflexivity. }
assert (HBW : L <> 0 -> exists wB, B = rn_spb rn + 24 * 2 ^ 32 + 16 * wB /\ art_cptr_ok 8192 (cl_au (g_cls FSG G 24)) wB /\ g_st FSG G 24 wB = CBatch).
{ intros NL. destruct (BCH lastb (in_or_app _ _ _ (or_introl (HB NL)))) as (wB & E & V & St). rewrite art_class_size_24 in V. exists wB. split; [exact E|]. split; assumption. }
destruct (PRIM 24 ltac:(lia)) as (_ & OK24 & _). destruct OK24 as (_ & (_ & Haumu) & _ & _ & _ & Hmu3 & _).
split; [exact HL|]. split.
{ destruct (Z.eq_dec L 0) as [EL|NL].
- assert (E0 : qtl = []) by (apply length_zero_iff_nil; unfold L in EL; lia). unfold B, lastb. rewrite E0. cbn. lia.
- destruct (HBW NL) as (wB & E & (V0 & V1 & _) & _). rewrite E. clear - V0 V1 Haumu Hmu3 G4 G6 G2 Eris. lia. }
split; [lia|]. split; [lia|]. split; [exact Ct80|]. split; [replace (rn_t rn + 80 + 24) with (rn_t rn + 104) by lia; exact Ct104|].
destruct (Z.eq_dec L 0) as [EL|NL]; [exists 0; intros X; contradiction|].
destruct (HBW NL) as (wB & E & V & St). exists wB. intros _.
assert (NEq : qtl <> []) by (intros E0; apply NL; unfold L; rewrite E0; reflexivity).
pose proof (art_qt_split qtl NEq) as ESP. fold lastb in ESP.
pose proof BLt as BLt'. rewrite ESP in BLt'. destruct (art_batch_list_last_hdr M _ lastb _ _ BLt') as (H1 & H2 & H3).
pose proof (art_batch_list_last M qtl ft lt NEq BLt) as El. fold lastb in El. fold B in El.
split; [exact E|]. split; [exact V|]. split.
{ intros Hi. specialize (CH 24 ltac:(lia)). cbv zeta in CH. destruct CH as (_ & II & _). rewrite (II wB Hi) in St. discriminate. }
split; [replace (rn_t rn + 80 + 16) with (rn_t rn + 96) by lia; rewrite <- El; exact Ct96|]. split; [exact H2|]. split; [exact H3|]. split; [unfold cntB; lia|].
pose proof (BY2 lastb (HB NL)). pose proof (art_bt_bytes_ge lastb (fun it Hi => POS lastb it (HB NL) Hi)). lia.
Qed.
End SE.
End EntryFacts.
Section Entry.
Variable FSG : Type.
Variable EVOK : list aev -> aev -> Prop.
Variable GR : list aev -> (word -> option byte) -> Z -> Z -> Prop.
Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_wf_entry := (forall (Q : list aev -> machine_state -> Prop) (log : list aev) R (Mr rom : word -> option byte) (raw0 : word) (rn : art_run) (G : art_gs FSG) (LB : list (Z * Z))
(Sp u n q16 qr b1 km top bot : Z) (kb : nat) (k : art_fk), let qtl := g_qt FSG G in
let cl24 := g_cls FSG G 24 in
let newb := art_free_newb qtl in
let lastb := art_lastb qtl in
let L := Z.of_nat (length qtl) in
let B := bt_addr lastb in
let cntB := Z.of_nat (length (bt_items lastb)) in
let bytes' := art_batches_bytes qtl + n + (if newb then 8192 else 0) in
art_alloc_rep FSG rn G LB Mr ->
match k with
| FKP c w => 1 <= c <= 30 /\ art_cptr_ok (AsanTab.class_size c) (cl_au (g_cls FSG G c)) w /\ g_st FSG G c w = CAlloc u n
| FKS i => exists s, nth_error (g_sec FSG G) i = Some s /\ sc_quar s = false /\ sc_u s = u /\ sc_n s = n
end ->
getr R 1 = raw0 -> ret_ok raw0 -> getr R 2 = Z_to_bv 64 Sp -> getr R 4 = Z_to_bv 64 (rn_tp rn) -> getr R 10 = Z_to_bv 64 u ->
u = 16 * q16 -> 1 <= n < 2 ^ 28 -> n <= 8 * qr <= n + 7 -> 0 <= b1 < 256 -> b1 mod 4 = 1 ->
cellA Mr (u - 16) 4 (2 + 256 * b1) -> cellA Mr (u - 12) 4 n -> HAJ.shadow_blkR Mr u n ->
rn_HI rn + 4096 <= Sp - 4096 -> Sp < 2 ^ 47 -> Sp mod 16 = 0 ->
top = ar_stack_top (rn_ar rn) -> bot = ar_stack_bottom (rn_ar rn) -> 0 <= bot -> bot < top -> 4096 <= top -> top < 2 ^ 63 ->
wrA Mr (Sp - 4096) 4096 -> readable8 Mr Sp top ->
g_depot FSG G = Datatypes.S kb -> cl_mu cl24 = 262144 * km ->
(newb = true -> cl_cache cl24 = [] -> art_cls_needs_populate 24 cl24 = true ->
cl_mu cl24 + 262144 <= 3758096384 /\ art_cls_mfa' cl24 (Z.of_nat (length (cl_free cl24)) + art_cls_new 24 cl24) <= 536870912) ->
(newb = true -> art_cls_ok 24 (art_ca_pre 24 cl24)) ->
art_evok_list EVOK log (art_enq_events newb (rn_spb rn) cl24) ->
(forall p, In p (art_live (g_log FSG G)) ->
0 < fst p /\ 0 < snd p /\ fst p + snd p <= rn_HI rn /\ (fst p + snd p <= 0x7fff7000 \/ 0x10007fff8000 <= fst p)
/\ (forall o, In o (art_objs rn) -> apart (fst p) (snd p) (fst o) (snd o))) ->
(forall p p', In p (art_live (g_log FSG G)) -> In p' (art_live (g_log FSG G)) -> fst p <> fst p' -> apart (fst p) (snd p) (fst p') (snd p')) ->
(forall p, In p (art_live (g_log FSG G)) -> fst p mod 4096 = 0 /\ snd p mod 4096 = 0) ->
(forall regs' (Mr' : word -> option byte),
getr regs' 2 = Z_to_bv 64 Sp -> getr regs' 1 = raw0 ->
(forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr R r) ->
bytes' <= 2 ^ 20 ->
art_free3_out Mr Mr' Sp (rn_t rn) u q16 qr (rn_l2 rn) (rn_blk rn) b1 n (rn_spb rn) (rn_ris rn) (rn_qs rn) km L B cntB (art_bt_bytes lastb) (art_batches_bytes qtl) kb (g_inited FSG G) cl24 ->
Q (log ++ art_enq_events newb (rn_spb rn) cl24) (mkst regs' raw0 Mr' rom)) ->
(forall regs' (Mr' : word -> option byte),
getr regs' 1 = (0x56084 : bv 64)%bv -> getr regs' 2 = Z_to_bv 64 (Sp - 2208) ->
getr regs' 10 = Z_to_bv 64 0x137970 -> getr regs' 11 = Z_to_bv 64 (rn_t rn + 80) -> getr regs' 12 = Z_to_bv 64 (rn_t rn + 208) -> getr regs' 13 = Z_to_bv 64 (Sp - 2128) ->
(forall r : reg, In r [3; 4; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr R r) ->
2 ^ 20 < bytes' ->
art_free3_out Mr Mr' Sp (rn_t rn) u q16 qr (rn_l2 rn) (rn_blk rn) b1 n (rn_spb rn) (rn_ris rn) (rn_qs rn) km L B cntB (art_bt_bytes lastb) (art_batches_bytes qtl) kb (g_inited FSG G) cl24 ->
art_free3_epi Mr' Sp u raw0 R -> wrA Mr' (Sp - 4096) 4096 ->
aruns ASEGS EVOK GR Q (log ++ art_enq_events newb (rn_spb rn) cl24) (mkst regs' (0x538b0 : word) Mr' rom)) ->
aruns ASEGS EVOK GR Q log (mkst R (0x78ecc : word) Mr rom)) (only parsing).
Variable Q : ltac:(sec_ty2 constr:(SEC_T_art_wf_entry) 0%nat 0%nat).
Variable log : ltac:(sec_ty2 constr:(SEC_T_art_wf_entry) 1%nat 0%nat).
Variable R : ltac:(sec_ty2 constr:(SEC_T_art_wf_entry) 2%nat 0%nat).
Variable Mr : ltac:(sec_ty2 constr:(SEC_T_art_wf_entry) 3%nat 0%nat).
Variable rom : ltac:(sec_ty2 constr:(SEC_T_art_wf_entry) 4%nat 0%nat).
Variable raw0 : ltac:(sec_ty2 constr:(SEC_T_art_wf_entry) 5%nat 0%nat).
Variable rn : ltac:(sec_ty2 constr:(SEC_T_art_wf_entry) 6%nat 0%nat).
Variable G : ltac:(sec_ty2 constr:(SEC_T_art_wf_entry) 7%nat 0%nat).
Variable LB : ltac:(sec_ty2 constr:(SEC_T_art_wf_entry) 8%nat 0%nat).
Variable Sp : ltac:(sec_ty2 constr:(SEC_T_art_wf_entry) 9%nat 0%nat).
Variable u : ltac:(sec_ty2 constr:(SEC_T_art_wf_entry) 10%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_wf_entry) 11%nat 0%nat).
Variable q16 : ltac:(sec_ty2 constr:(SEC_T_art_wf_entry) 12%nat 0%nat).
Variable qr : ltac:(sec_ty2 constr:(SEC_T_art_wf_entry) 13%nat 0%nat).
Variable b1 : ltac:(sec_ty2 constr:(SEC_T_art_wf_entry) 14%nat 0%nat).
Variable km : ltac:(sec_ty2 constr:(SEC_T_art_wf_entry) 15%nat 0%nat).
Variable top : ltac:(sec_ty2 constr:(SEC_T_art_wf_entry) 16%nat 0%nat).
Variable bot : ltac:(sec_ty2 constr:(SEC_T_art_wf_entry) 17%nat 0%nat).
Variable kb : ltac:(sec_ty2 constr:(SEC_T_art_wf_entry) 18%nat 0%nat).
Variable k : ltac:(sec_ty2 constr:(SEC_T_art_wf_entry) 19%nat 0%nat).
Lemma art_wf_entry : ltac:(sec_stmt2 constr:(SEC_T_art_wf_entry) 20%nat 0%nat).
Proof using Type Q log R Mr rom raw0 rn G LB Sp u n q16 qr b1 km top bot kb k.
intros qtl cl24 newb lastb L B cntB bytes'
REP KIND H1 Hret H2 H4 H10 Eu Hn Hqr Hb1 Hty Chw Cn SHB HHI HS47 HS16 Etop Ebot Hbot Hbt Htop4 Htop W RD0 Edep Emu Room OKpre EV LIVE LIVE2 LIVE3 K1 K2.
destruct (art_wfa_thq FSG rn G LB Mr REP n Hn) as (HL & HB & Hby & Hby' & CL & Cby & wB & LBN).
destruct (art_frep_u_far FSG rn G LB Mr u n q16 qr b1 kb k REP Eu Hn Hqr Hb1 KIND Edep LIVE LIVE2 LIVE3) as (U1 & U2 & U3 & U4 & Ut & Uc & Ul2 & Ublk & _ & _ & _ & Uris & Ufa).
pose proof (art_frep_u_B FSG rn G LB Mr u n q16 qr b1 kb k REP Eu Hn Hqr Hb1 KIND Edep LIVE LIVE2 LIVE3) as UB.
pose proof (art_frep_wr_hdr FSG rn G LB Mr u n q16 b1 kb k REP Eu Hn KIND Edep LIVE3) as Wp.
pose proof (art_frep_wr_sh FSG rn G LB Mr u n q16 qr b1 kb k REP Eu Hn Hqr Hb1 KIND Edep LIVE LIVE2 LIVE3 SHB) as Wus.
pose proof (art_frep_hp24 FSG rn G LB Mr Sp u n q16 qr b1 km kb k REP Eu Hn Hqr Hb1 KIND HHI Emu Edep LIVE LIVE2 LIVE3 OKpre) as HP24.
assert (Hq0 : 1 <= qr) by (clear - Hn Hqr; lia).
pose proof REP as (ROK & ST & TH & (PH & PRIM & Wsh) & _ & _ & _ & DEP & (IA1 & IA2 & _) & _).
rok_open14 ROK. pose proof GEO as GEO'. geo_open GEO'.
destruct ST as (PC & LY & T & _ & _ & DR & _ & C1 & _ & _ & _ & _ & _ & C7 & _ & C9 & _ & _ & _ & C13 & C14 & C15 & C16 & _).
destruct TH as (Wt & T1 & T2 & T3 & T4 & T5 & T6 & _). rewrite <- Etop in T3. rewrite <- Ebot in T4.
destruct (PRIM 24 ltac:(lia)) as (RC & OK & Hinit & _). fold cl24 in RC, OK, Hinit.
pose proof OK as (_ & (Hau0 & Haumu) & _ & _ & _ & Hmu3 & _).
unfold art_rt_depot in DEP. rewrite Edep in DEP.
assert (A24 : forall X Y, apart (u - 16) (16 + 8 * qr) X Y -> apart (u - 16) 24 X Y) by (intros X Y A; unfold apart in *; clear - A Hq0; lia).
assert (A24' : forall X Y, apart (u - 16) 32 X Y -> apart (u - 16) 24 X Y) by (intros X Y A; unfold apart in *; clear - A; lia).
apply (art_free3 EVOK GR Q log R Mr rom raw0 Sp (rn_HI rn) u q16 n qr b1 (rn_tp rn) (rn_key rn) (rn_tsd rn) (rn_ctx rn) (rn_t rn) (rn_spb rn) (rn_ris rn) (rn_qs rn) km
(rn_l2 rn) (rn_blk rn) top bot L B wB cntB (art_bt_bytes lastb) (art_batches_bytes qtl) kb (g_ia FSG G) (g_inited FSG G) cl24
H1 Hret H2 H4 H10 ltac:(clear - U1; lia) Eu Hn Hqr Hb1 Hty
ltac:(unfold JatPoison3.art_poison_lo_ok, JatPoison3.art_poison_hi_ok, SB, kHighMemBeg, kHighMemEnd; clear - U1 U2 U4 Hq0 G2; lia)
GEO HHI HS47 HS16 Hbot Hbt Htop4 Htop Htpd Htsdd Dl2 Dblk Al2t Al2c Al2k Al2s Abt Abc Abk Abs
ltac:(clear - U3; lia) (A24 _ _ Ut) (A24 _ _ Uc) (A24 _ _ Ul2) (A24 _ _ Ublk) (A24' _ _ Uris) (A24' _ _ Ufa) UB
W RD0 Wt Wp Wus (art_img_wr_iaflag Mr 0x1ca788 4 ltac:(lia) ltac:(lia) ltac:(lia)) (art_img_wr_iatab Mr 0x13bf00 0x81030 ltac:(lia) ltac:(lia) ltac:(lia))
LY T PC C1 C13 C14 T6 T5 T3 T4 IA1
ltac:(intros E j Hj; replace (0x13bf08 + 8 * j) with (0x13bf00 + 8 + 8 * j) by lia; exact (IA2 E j Hj))
Chw Cn C7 T1 T2 C15 C16 C9 PH RC OK Hinit Emu).
-
intros E1 E2 E3. destruct (Room E1 E2 E3) as (R1 & R2). split; [exact R1|]. split; [exact R2|].
split; (eapply wr_sub; [exact Wsh| |]); clear - R1 Emu Hau0 Haumu; lia.
- exact EV.
- exact HL.
- exact HB.
- exact Hby.
- exact Hby'.
- exact CL.
- exact Cby.
- exact LBN.
- exact HP24.
- exact DEP.
- exact DR.
- exact K1.
- exact K2.
Qed.
End SE.
End Entry.
