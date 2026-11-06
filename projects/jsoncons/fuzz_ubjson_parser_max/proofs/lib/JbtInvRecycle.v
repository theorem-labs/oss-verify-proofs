(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim StoreOk HeapIface HeapIfaceA As0Tables ArtMem JbtLeaf JbtRzLog JbtPoison JbtAllocA JbtAllocG ArtRunsMem JbtInitCache JbtPopulate1 ArtRuns JbtCls JbtFp
JbtClsRep JbtClsGfa2 JbtClsRefill JbtCARSpec JbtAlloc3Pure JbtByteCell JbtCellEx JbtDepotA JbtDepot JbtAllocate3 JbtSecAllocPost ArtBridge JbtInv JbtInvMallocPure JbtInvMalloc JbtFxQ JbtInvFreePure JbtInvFree JbtInvRepX JbtInvDrain
JbtRecycle2C JbtRecycle3L JbtRecycle5A JbtRecycle5I JbtRecycle5T JbtRecycle5C JbtRecycle5D JbtRecycle5E JbtRecycle5F JbtInvRecycleA JbtInvRecycleC JbtInvRecycleD JbtInvRecycleE.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import HeapIfaceAJx ShadowRLaws.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtInvRecycle () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceAJx.HAJ."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtFp."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtFxQ."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtInvFreePure."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtInvRecycle.Entry."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtInvRecycle.Entry.Work."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtInvRecycleA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtInvRecycleC."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtPoison."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtRecycle5A."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtRecycle5C."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtRecycle5D."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtRecycle5E."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtRecycle5F."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtRecycle5I."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtRecycle5T."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0B"; "1app"; "1cons"; "1fst"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1snd"; "2and"; "2eq"; "2ex"; "2not"]; ["2or"; "3le"; "4Forall"; "4firstn"; "4map"; "4skipn"; "5Z"; "0LB"; "0M"; "0M'"; "0M0"; "6apart"; "6cell"; "6wr"; "7FS_BYTES"; "7S"]; ["7app_mem"; "7ar_fs"; "7byte_at"; "7in_shadow_of"; "8shadow_blkR"; "9art_agree"; "9art_out"; ":art_qbatch"; ":qb_addr"; ";art_batch"; ";art_batch_list"; ";art_nq"; ";art_objs"; ";art_rt_statics"; ";art_rt_thread"; ";art_run_ok"]; [";bt_addr"; ";bt_items"; ";rn_HI"; ";rn_ar"; ";rn_blk"; ";rn_ctx"; ";rn_dtls"; ";rn_kbase"; ";rn_l2"; ";rn_parr"; ";rn_qs"; ";rn_ris"; ";rn_spb"; ";rn_t"; "<art_qb"; ">art_far_obj"]; ["=art_batch_ok"; "=art_el_geo"; "=art_gr"; "=art_item_ok"; "=art_wk_ok"; "?art_rel_key"; "?art_rg_ok"; "@art_fp_where"; "@art_rel_shw"; "ASB"; "BREB"; "Bart_rel"; "Bart_rel_addr"; "Bart_rel_zone"; "Brg_bl"; "Cart_rel_is_item"]; ["Dart_rb_ok"; "Dart_rb_q"; "Dart_rb_work"; "Dart_rbatch"; "Drb_items"; "Drb_wb"; "Eart_qin"; "Eart_rcy_npop"; "Fart_qin24"; "Fart_rcy_W2"; "Gart_rel_mem"; "Gart_rel_pre"; "Hart_rels_fp"; "Hart_rels_pre"; "Hart_rels_sep"; "Hart_zapart"]; ["Iloaded_segments"; "JForall2"; "JIn"; "JNoDup"; "Jflat_map"; "Jfold_right"; "Kadd"; "Kdiv"; "Kle"; "Klt"; "Kmodulo"; "Kmul"; "Kof_nat"; "Kpow"; "Ksub"; "0a"]; ["0b"; "0b0"; "0bs"; "0c"; "0e"; "0e'"; "0es"; "0f"; "0it"; "0its"; "0j"; "0k"; "0l"; "0mn"; "0n"; "0p"]; ["0rn"; "0sp"; "LZ_to_bv"; "Lbv"; "0u"; "0v"; "0w"; "0wb"; "0x"; "0xs"; "0xs'"; "0y"; "0z"; "0zlen"; "0zlo"]]).
Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Lemma art_forall2_exists : forall (A B : Type) (R : A -> B -> Prop) (l : list A), (forall a, In a l -> exists b, R a b) -> exists l', Forall2 R l l'.
Proof.
intros A B R l. induction l as [|a r IH]; intros H; [exists []; constructor|].
destruct (H a (or_introl eq_refl)) as (b & Hb). destruct (IH (fun x Hx => H x (or_intror Hx))) as (l' & Hl'). exists (b :: l'). constructor; assumption.
Qed.
Lemma art_roundup8_le : ltac2:(TCodec.tc2 tcn__JbtInvRecycle "G'F&S8zr2%3221r3&S;+8%2215%8241&S7&S6r4+7%3221%5218%:219%;2:<%A221p0:1p0@1pWHE1pWNF1").
Proof.
intros n k Hn Hk. assert ((n + 7) / 8 < k + 1); [|lia].
apply Z.div_lt_upper_bound; lia.
Qed.
Section Entry.
Variable FSG : Type.
Variables (rn : art_run) (G : art_gs FSG) (LB : list (Z * Z)) (M : word -> option byte) (bt bg : Z).
Hypothesis REPX : art_alloc_rep_x FSG bt bg rn G LB M.
Hypothesis GHOST : art_rt_ghost FSG rn G M.
Hypothesis QT0 : g_qt FSG G = [].
Hypothesis LIVE : forall p, In p (art_live (g_log FSG G)) ->
0 < fst p /\ 0 < snd p /\ fst p + snd p <= rn_HI rn /\ (fst p + snd p <= 0x7fff7000 \/ 0x10007fff8000 <= fst p)
/\ (forall o, In o (art_objs rn) -> apart (fst p) (snd p) (fst o) (snd o)).
Hypothesis LIVE2 : forall p p', In p (art_live (g_log FSG G)) -> In p' (art_live (g_log FSG G)) -> fst p <> fst p' -> apart (fst p) (snd p) (fst p') (snd p').
Hypothesis LIVE3 : forall p, In p (art_live (g_log FSG G)) -> fst p mod 4096 = 0 /\ snd p mod 4096 = 0.
#[local] Abbreviation spb := (rn_spb rn).
Definition art_gr : art_rg := RG (g_cls FSG G) (map art_sec_b (g_sec FSG G)).
Definition art_item_ok (it : Z * Z) (e : art_rel) : Prop :=
art_rel_is_item e /\ art_rel_addr spb e = fst it /\ art_rel_pre art_gr e /\ art_rel_mem spb e M
/\ match e with
| REP c w d b1 n => n = snd it /\ g_st FSG G c w = CQuar (fst it + 16) (snd it)
| RES mb ms m b1 n => n = snd it /\ exists s, In s (g_sec FSG G) /\ sc_quar s = true /\ sc_u s = fst it + 16 /\ sc_n s = snd it /\ mb = sc_map s /\ ms = sc_msize s
| REB _ => False
end.
Section SE.
Local Abbreviation SEC_T_art_item_exists := (forall b it, In b (g_qt FSG G ++ g_qg FSG G) -> In it (bt_items b) -> exists e, art_item_ok it e) (only parsing).
Variable b : ltac:(sec_ty2 constr:(SEC_T_art_item_exists) 0%nat 0%nat).
Lemma art_item_exists : ltac:(sec_stmt2 constr:(SEC_T_art_item_exists) 1%nat 0%nat).
Proof using LB bt bg REPX GHOST b.
intros it Hb Hit.
destruct it as [h n].
pose proof REPX as (ROK & _ & _ & _ & CH & SECR & QR & _). destruct ROK as (GEO & _). destruct GEO as (G1 & G2 & Espb & G4 & _).
destruct QR as (_ & _ & _ & _ & _ & _ & _ & ITEMS & _). destruct GHOST as (AL & _).
pose proof (AL b (h, n) Hb Hit) as Hal. cbn [fst] in Hal.
destruct (ITEMS b (h, n) Hb Hit) as [(c & w & Hc & OKw & Est)|(s & Hs & Hq & Eu & En)]; cbn [fst snd] in *.
- destruct (CH c Hc) as (_ & CF & _ & CW). cbv zeta in CF, CW. specialize (CW w OKw). rewrite Est in CW.
destruct CW as (Lo & Hi & (b1 & Hb1 & _ & Chw & Cn & Hn) & _ & _ & LCH).
destruct (art_class_size_facts c Hc) as (Hsz & Hsz16). pose proof OKw as (Hw0 & Hwau & _).
set (rb := spb + c * 2 ^ 32) in *. set (d := h - (rb + 16 * w)).
exists (REP c w d b1 n). split; [exact I|]. split; [cbn [art_rel_addr fst]; unfold d, rb; lia|].
split.
{ cbn [art_rel_pre art_gr rg_cls]. split; [exact Hc|]. split; [exact OKw|].
split. { intros Hin. rewrite (CF w Hin) in Est. discriminate Est. }
split; [unfold d; lia|].
assert (Ed : d = 16 * (h / 16 - 4096 * rn_qs rn - c * 2 ^ 28 - w)).
{ unfold d, rb. rewrite Espb. pose proof (Z.div_mod h 16 ltac:(lia)) as D. rewrite Hal in D. lia. }
split. { rewrite Ed. rewrite Z.mul_comm. apply Z_mod_mult. }
split. { pose proof (Z.div_mod (AsanTab.class_size c) 16 ltac:(lia)) as Ds. rewrite Hsz16 in Ds.
assert (X : (n + 7) / 8 * 8 <= 8 * (2 * (AsanTab.class_size c / 16) - 2 * (h / 16 - 4096 * rn_qs rn - c * 2 ^ 28 - w) - 2)) by (apply art_roundup8_le; [lia|unfold d in Ed; lia]).
lia. }
split; [exact Hb1|lia]. }
split.
{ cbn [art_rel_mem]. replace (spb + c * 2 ^ 32 + 16 * w + d) with (h + 16 - 16) by (unfold d, rb; lia).
split; [exact Chw|]. split; [replace (h + 16 - 16 + 4) with (h + 16 - 12) by lia; exact Cn|].
intros Hd. apply LCH. unfold d, rb in Hd. fold rb. lia. }
split; [reflexivity|exact Est].
- destruct SECR as (_ & _ & _ & _ & _ & _ & _ & _ & PER & _).
destruct (In_nth_error _ _ Hs) as (i & Hi). destruct (PER i s Hi) as (_ & _ & _ & _ & _ & _ & Lo & Hi' & Q & _).
rewrite Hq in Q. destruct Q as ((b1 & Hb1 & _ & Chw & Cn & Hn) & _). rewrite Eu in Chw, Cn, Lo, Hi'. rewrite En in Cn, Hn, Hi'.
exists (RES (sc_map s) (sc_msize s) h b1 n). split; [exact I|]. split; [reflexivity|].
split. { cbn [art_rel_pre art_gr rg_bl]. split; [apply (in_map art_sec_b) in Hs; exact Hs|]. split; [lia|]. split; [lia|]. split; [exact Hb1|lia]. }
split. { cbn [art_rel_mem]. replace h with (h + 16 - 16) at 1 by lia. split; [exact Chw|]. replace (h + 4) with (h + 16 - 12) by lia. exact Cn. }
split; [reflexivity|]. exists s. repeat split; assumption.
Qed.
End SE.
Definition art_batch_ok (b : art_batch) (x : art_rbatch) : Prop :=
bt_addr b = spb + 24 * 2 ^ 32 + 16 * rb_wb x /\ art_cptr_ok 8192 (cl_au (g_cls FSG G 24)) (rb_wb x) /\ g_st FSG G 24 (rb_wb x) = CBatch
/\ Forall2 art_item_ok (bt_items b) (rb_items x) /\ rb_size x = art_bt_bytes b.
#[using="LB bt bg REPX GHOST"] Lemma art_batch_exists : forall b, In b (g_qt FSG G ++ g_qg FSG G) -> exists x, art_batch_ok b x.
Proof.
intros b Hb. pose proof REPX as (_ & _ & _ & _ & _ & _ & QR & _). destruct QR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & BCH).
destruct (BCH b Hb) as (w & Ew & OKw & Est). rewrite art_class_size_24 in OKw.
destruct (art_forall2_exists _ _ art_item_ok (bt_items b) (fun it Hit => art_item_exists b it Hb Hit)) as (items & F2).
exists (w, items, art_bt_bytes b). unfold art_batch_ok, rb_wb, rb_items, rb_size. cbn [fst snd]. split; [exact Ew|]. split; [exact OKw|]. split; [exact Est|]. split; [exact F2|reflexivity].
Qed.
#[using="LB bt bg REPX GHOST"] Lemma art_batches_exist : forall bs, (forall b, In b bs -> In b (g_qt FSG G ++ g_qg FSG G)) -> exists xs, Forall2 art_batch_ok bs xs.
Proof. intros bs Hbs. apply art_forall2_exists. intros b Hb. exact (art_batch_exists b (Hbs b Hb)). Qed.
#[using="Type"] Lemma art_items_addr : ltac2:(TCodec.tc2 tcn__JbtInvRecycle "M'5':'F%2211%411'R;%611'S1&R3r2r1%4586321'=%=1;&D&R<&QLvT0%211%411%64?B1;&3%12DDr3%:4EF21%=3<51p0?1pW>E1pWDH1").
Proof. intros its es F. induction F as [|it e its es (_ & Ea & _) _ IH]; cbn [map]; [reflexivity|]. rewrite Ea, IH. reflexivity. Qed.
#[using="Type"] Lemma art_batch_ok_q : ltac2:(TCodec.tc2 tcn__JbtInvRecycle "D'Q9&RC&R0r2r1%3221'=&Q7&RA&QLvT0%211%4219&QNr3%211%:3941p0<1pXBA1pW2C1").
Proof.
intros b [[wb items] sz] (Ea & _ & _ & F2 & Esz). unfold art_rb_q, art_qb, rb_wb, rb_items, rb_size in *. cbn [fst snd] in *.
rewrite (art_items_addr _ _ F2), Esz, Ea. reflexivity.
Qed.
#[using="Type"] Lemma art_batches_ok_q : ltac2:(TCodec.tc2 tcn__JbtInvRecycle "K'5'Q9%211&RC%411'S1&R0r2r1%4586321'=&Q7%<11&D&RA&QLvT0%211%411%64@81<&QNr3%94E;21%=3;41p0?1pXDE1pW6H1").
Proof. intros bs xs F. induction F as [|b x bs xs Hbx _ IH]; cbn [map]; [reflexivity|]. rewrite (art_batch_ok_q b x Hbx), IH. reflexivity. Qed.
Definition art_el_geo (e : art_rel) : Prop :=
match e with
| REP c w _ _ _ => 1 <= c <= 30 /\ 0 <= w /\ 16 * w + AsanTab.class_size c <= 3758096384 /\ (exists i, 16 * w = AsanTab.class_size c * i)
| RES mb ms _ _ _ => In (mb, ms) (art_live (g_log FSG G))
| REB wb => 0 <= wb /\ 16 * wb + AsanTab.class_size 24 <= 3758096384 /\ (exists i, 16 * wb = AsanTab.class_size 24 * i)
end.
#[using="rn LB M bt bg REPX"] Lemma art_pre_geo : ltac2:(TCodec.tc2 tcn__JbtInvRecycle ":'R;&RK&R2r1%3221&R1r2%211p041pW:91").
Proof.
intros e PRE. pose proof REPX as (_ & _ & _ & (_ & PRIM & _) & _ & SECR & _).
destruct e as [c w d b1 n|mb ms m b1 n|wb]; cbn [art_rel_pre art_el_geo art_gr rg_cls rg_bl] in *.
- destruct PRE as (Hc & (Hw0 & Hwau & Hi) & _). destruct (PRIM c Hc) as (_ & OK & _). destruct OK as (_ & (_ & Haumu) & _ & _ & _ & Hmu3 & _).
split; [exact Hc|]. split; [exact Hw0|]. split; [lia|exact Hi].
- destruct PRE as (Hin & _). apply in_map_iff in Hin. destruct Hin as (s & Es & Hs). destruct (In_nth_error _ _ Hs) as (i & Hi).
destruct SECR as (_ & _ & _ & _ & _ & _ & _ & _ & PER & _). destruct (PER i s Hi) as (_ & Hlive & _). unfold art_sec_b in Es. injection Es as <- <-. exact Hlive.
- destruct PRE as ((Hw0 & Hwau & Hi) & _). destruct (PRIM 24 ltac:(lia)) as (_ & OK & _). destruct OK as (_ & (_ & Haumu) & _ & _ & _ & Hmu3 & _).
rewrite art_class_size_24. split; [exact Hw0|]. split; [lia|exact Hi].
Qed.
#[using="LB M bt bg REPX LIVE LIVE2"] Lemma art_el_zapart : ltac2:(TCodec.tc2 tcn__JbtInvRecycle "Q1'R;&R1r2%211&?'=':'F%2211&R5r4%211r3%411%93631%;11&RO&QLvT0%211r5&3&R=%124=%33AA1&;%13CC3%;48731p0=1p0J1p0K1pW<O1pW:Q01").
Proof.
intros e e' GE GE' NE. pose proof REPX as (ROK & _). destruct ROK as (GEO & _ & _ & Kspb & _). destruct GEO as (G1 & G2 & Espb & G4 & _).
assert (KS : forall p, In p (art_live (g_log FSG G)) -> apart (fst p) (snd p) (rn_kbase rn) 0x2000011000).
{ intros p Hp. destruct (LIVE p Hp) as (_ & _ & _ & _ & OB). apply (OB (rn_kbase rn, 0x2000011000)). cbn. tauto. }
assert (CHK : forall c w, 1 <= c <= 30 -> 0 <= w -> 16 * w + AsanTab.class_size c <= 3758096384 ->
rn_kbase rn <= spb + c * 2 ^ 32 + 16 * w /\ spb + c * 2 ^ 32 + 16 * w + AsanTab.class_size c <= rn_kbase rn + 0x2000011000).
{ intros c w Hc Hw Hu. destruct (art_class_size_facts c Hc) as (S1 & _). lia. }
unfold art_zapart.
destruct e as [c w d b1 n|mb ms m b1 n|wb]; destruct e' as [c' w' d' b1' n'|mb' ms' m' b1' n'|wb']; cbn [art_rel_zone art_el_geo art_rel_key fst snd] in *.
- destruct GE as (Hc & Hw & Hu & Hi). destruct GE' as (Hc' & Hw' & Hu' & Hi'). exact (art_chunk_apart spb c w c' w' Hc Hc' Hw Hu Hi Hw' Hu' Hi' NE).
- destruct GE as (Hc & Hw & Hu & Hi). pose proof (KS _ GE') as A. destruct (CHK c w Hc Hw Hu) as (X1 & X2). cbn [fst snd] in A. unfold apart in *. lia.
- destruct GE as (Hc & Hw & Hu & Hi). destruct GE' as (Hw' & Hu' & Hi'). rewrite <- art_class_size_24. exact (art_chunk_apart spb c w 24 wb' Hc ltac:(lia) Hw Hu Hi Hw' Hu' Hi' NE).
- destruct GE' as (Hc' & Hw' & Hu' & Hi'). pose proof (KS _ GE) as A. destruct (CHK c' w' Hc' Hw' Hu') as (X1 & X2). cbn [fst snd] in A. unfold apart in *. lia.
- apply (LIVE2 (mb, ms) (mb', ms') GE GE'). cbn [fst]. intros E. apply NE. rewrite E. reflexivity.
- destruct GE' as (Hw' & Hu' & Hi'). pose proof (KS _ GE) as A. destruct (CHK 24 wb' ltac:(lia) Hw' Hu') as (X1 & X2). rewrite art_class_size_24 in X2. cbn [fst snd] in A. unfold apart in *. lia.
- destruct GE as (Hw & Hu & Hi). destruct GE' as (Hc' & Hw' & Hu' & Hi'). rewrite <- art_class_size_24. exact (art_chunk_apart spb 24 wb c' w' ltac:(lia) Hc' Hw Hu Hi Hw' Hu' Hi' NE).
- destruct GE as (Hw & Hu & Hi). pose proof (KS _ GE') as A. destruct (CHK 24 wb ltac:(lia) Hw Hu) as (X1 & X2). rewrite art_class_size_24 in X2. cbn [fst snd] in A. unfold apart in *. lia.
- destruct GE as (Hw & Hu & Hi). destruct GE' as (Hw' & Hu' & Hi'). rewrite <- art_class_size_24. exact (art_chunk_apart spb 24 wb 24 wb' ltac:(lia) ltac:(lia) Hw Hu Hi Hw' Hu' Hi' NE).
Qed.
Definition art_wk_ok (e : art_rel) : Prop :=
art_rel_pre art_gr e /\ art_rel_mem spb e M
/\ match e with
| REP c w d b1 n => g_st FSG G c w = CQuar (art_rel_addr spb e + 16) n
| RES mb ms m b1 n => exists s, In s (g_sec FSG G) /\ sc_quar s = true /\ sc_u s = m + 16 /\ sc_n s = n /\ mb = sc_map s /\ ms = sc_msize s
| REB wb => g_st FSG G 24 wb = CBatch
end.
#[using="Type"] Lemma art_item_wk : ltac2:(TCodec.tc2 tcn__JbtInvRecycle "=':'F%2211'R;&R3r2r1%3221&R4%114p031pW:81pWB:1").
Proof.
intros it e (_ & Ea & PRE & MEM & GH). split; [exact PRE|]. split; [exact MEM|].
destruct e as [c w d b1 n|mb ms m b1 n|wb]; [| |destruct GH].
- destruct GH as (En & Est). rewrite Ea, En. exact Est.
- destruct GH as (En & s & Hs & Hq & Eu & Esn & Emb & Ems). cbn [art_rel_addr] in Ea. exists s. rewrite Ea, En. repeat split; assumption.
Qed.
#[using="LB bt bg REPX"] Lemma art_batch_wk : forall b x, In b (g_qg FSG G) -> art_batch_ok b x -> art_wk_ok (REB (rb_wb x)).
Proof.
intros b x Hb (Ea & OKw & Est & _). pose proof REPX as (_ & _ & _ & _ & CH & _).
split; [|split; [exact I|exact Est]]. cbn [art_rel_pre art_gr rg_cls]. split; [exact OKw|].
destruct (CH 24 ltac:(lia)) as (_ & CF & _). cbv zeta in CF. intros Hin. rewrite (CF _ Hin) in Est. discriminate Est.
Qed.
#[using="Type"] Lemma art_forall2_in_r : forall (A B : Type) (R : A -> B -> Prop) l l' y, Forall2 R l l' -> In y l' -> exists x, In x l /\ R x y.
Proof.
intros A B R l l' y F. induction F as [|a b l l' Hab _ IH]; intros Hy; [destruct Hy|].
destruct Hy as [<-|Hy]; [exists a; split; [left; reflexivity|exact Hab]|]. destruct (IH Hy) as (x & Hx & Rx). exists x. split; [right; exact Hx|exact Rx].
Qed.
Section SE.
Local Abbreviation SEC_T_art_wk_reb_item := (ltac2:(TCodec.tc2 tcn__JbtInvRecycle "M'F'R;&R4(R:r2%211%411%513&R?r3%211&?'=&R<&QLvT0%211r5%?11%6231r4%8251%:3F31%<11p0>1p0B1p0D1pW:J1pX@L1")) (only parsing).
Variable wb : ltac:(sec_ty2 constr:(SEC_T_art_wk_reb_item) 0%nat 0%nat).
Lemma art_wk_reb_item : ltac:(sec_stmt2 constr:(SEC_T_art_wk_reb_item) 1%nat 0%nat).
Proof using LB bt bg REPX LIVE wb.
intros e (PRE & _ & GH) (PRE' & _ & GH') IT EA.
pose proof (art_pre_geo _ PRE) as GE. pose proof (art_pre_geo _ PRE') as GE'.
pose proof REPX as (ROK & _). destruct ROK as (GEO & _ & _ & Kspb & _). destruct GEO as (G1 & G2 & Espb & G4 & _).
destruct e as [c w d b1 n|mb ms m b1 n|wb']; [| |destruct IT]; cbn [art_rel_addr art_el_geo art_rel_pre] in *.
- destruct GE as (Hw & Hu & (j & Hj)). destruct GE' as (Hc & Hw' & Hu' & (i & Hi)). destruct PRE' as (_ & _ & _ & Hd & _ & Hdsz & _ & Hn).
assert (Hr0 : 0 <= (n + 7) / 8 * 8) by (assert (0 <= (n + 7) / 8) by (apply Z.div_pos; lia); lia).
rewrite art_class_size_24 in *. destruct (art_class_size_facts c Hc) as (S1 & _).
assert (Ec : c = 24) by lia. subst c. rewrite art_class_size_24 in *.
assert (Ew : w = wb) by lia. subst w. rewrite GH in GH'. discriminate GH'.
- destruct GE as (Hw & Hu & _). destruct PRE' as (_ & Lo & Hi & _). destruct (LIVE _ GE') as (_ & _ & _ & _ & OB).
pose proof (OB (rn_kbase rn, 0x2000011000) ltac:(cbn; tauto)) as A. cbn [fst snd] in A. rewrite art_class_size_24 in Hu. unfold apart in A. lia.
Qed.
End SE.
#[using="Type"] Lemma art_map_flat_map : forall (A B C : Type) (f : B -> C) (g : A -> list B) l, map f (flat_map g l) = flat_map (fun x => map f (g x)) l.
Proof. intros A B C f g l. induction l as [|a r IH]; cbn [flat_map map]; [reflexivity|]. rewrite map_app, IH. reflexivity. Qed.
#[using="Type"] Lemma art_nodup_key_eq : forall (A B : Type) (f : A -> B) l x y, List.NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
intros A B f l. induction l as [|a r IH]; intros x y ND Hx Hy E; [destruct Hx|]. cbn [map] in ND. inversion ND as [|? ? Hn Nd]; subst.
destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy]; [reflexivity| | |exact (IH x y Nd Hx Hy E)].
- exfalso. apply Hn. rewrite E. apply in_map. exact Hy.
- exfalso. apply Hn. rewrite <- E. apply in_map. exact Hx.
Qed.
#[using="Type"] Lemma art_xs_items : ltac2:(TCodec.tc2 tcn__JbtInvRecycle "Q6'5'Q9%211&RC%411'S1&R0r2r1%4586321'='F%<11&S4&D'R;&R<&QLvT0%211%411&RD%11>%948<31qXBE1%<4F>1B':%12@@&3%12BB&QAr3%C4O521%C46F41%H3F91p0J1pXDQ01pW6Q31").
Proof.
intros bs xs F. induction F as [|b x bs xs' Hbx _ IH]; cbn [flat_map]; [reflexivity|]. rewrite map_app, IH. destruct Hbx as (_ & _ & _ & F2 & _). rewrite (art_items_addr _ _ F2). reflexivity.
Qed.
#[using="Type"] Lemma art_xs_addrs : ltac2:(TCodec.tc2 tcn__JbtInvRecycle "Q8'5'Q9%211&RC%411'S1&R0r2r1%4586321'='F%<11&D&S6&QLvT0%211&S;+H&S=+2+Q0%3221%6251%;281+@&RE%11D%;231%@251qXBL1%C4ME1I&Q@r3%F4Q2H21%J3H41p0L1pXDQ21pW6Q51").
Proof. intros bs xs F. induction F as [|b x bs xs' Hbx _ IH]; cbn [map]; [reflexivity|]. rewrite IH. destruct Hbx as (Ea & _). rewrite Ea. reflexivity. Qed.
#[using="Type"] Lemma art_batch_list_len : ltac2:(TCodec.tc2 tcn__JbtInvRecycle "Q4'T3yR0%211'8y8%511%311p051'5'Q9%211'F&Q:r5r4r3r2%544321&S2%13:36'A&4':%12<<&QA%11:%5231uoM%8221p0:1p0=1pW2F1pWJE1pW@F1pW6H1pQFL1").
Proof.
intros M0 bs. induction bs as [|b0 r IH]; intros f l b BL Hb; [destruct Hb|]. cbn [art_batch_list] in BL. destruct BL as (_ & Hl & _ & _ & _ & _ & R).
destruct Hb as [<-|Hb]; [exact Hl|exact (IH _ _ b R Hb)].
Qed.
#[using="Type"] Lemma art_sum_snd_bound : ltac2:(TCodec.tc2 tcn__JbtInvRecycle "Q7'5':'F%2211%411&S2r1r3%33521'<&S8z&;r2%23<<1%5241&S9%123:%9231p0;1pWBA1&S5&S6%129AqXJF1qWBF1%55HG1?C%A2@1&S;&S<&4%12LH%311%521D%H281%J281p0@1p2Q31pWJQ21").
Proof.
induction l as [|a r IH]; intros B H; cbn [fold_right length]; [lia|]. pose proof (H a (or_introl eq_refl)). specialize (IH B (fun it Hit => H it (or_intror Hit))). lia.
Qed.
#[using="Type"] Lemma art_in_firstn : forall (A : Type) k (l : list A) x, In x (firstn k l) -> In x l.
Proof. intros A k l x H. rewrite <- (firstn_skipn k l). apply in_or_app. left. exact H. Qed.
#[using="Type"] Lemma art_in_skipn : forall (A : Type) k (l : list A) x, In x (skipn k l) -> In x l.
Proof. intros A k l x H. rewrite <- (firstn_skipn k l). apply in_or_app. right. exact H. Qed.
#[using="Type"] Lemma art_nodup_app_d : forall (A B : Type) (f : A -> B) (l1 l2 : list A) a1 a2, List.NoDup (map f (l1 ++ l2)) -> In a1 l1 -> In a2 l2 -> f a1 <> f a2.
Proof.
intros A B f l1. induction l1 as [|x r IH]; intros l2 a1 a2 ND H1 H2 E; [destruct H1|]. cbn [app map] in ND. inversion ND as [|? ? Hn Nd]; subst.
destruct H1 as [<-|H1]; [|exact (IH l2 a1 a2 Nd H1 H2 E)]. apply Hn. rewrite E. apply in_map. apply in_or_app. right. exact H2.
Qed.
#[using="Type"] Lemma art_forall2_firstn : forall (A B : Type) (R : A -> B -> Prop) n l l', Forall2 R l l' -> Forall2 R (firstn n l) (firstn n l').
Proof. intros A B R n. induction n as [|n IH]; intros l l' F; [constructor|]. destruct F; cbn [firstn]; constructor; [assumption|apply IH; assumption]. Qed.
#[using="Type"] Lemma art_forall2_skipn : forall (A B : Type) (R : A -> B -> Prop) n l l', Forall2 R l l' -> Forall2 R (skipn n l) (skipn n l').
Proof. intros A B R n. induction n as [|n IH]; intros l l' F; [exact F|]. destruct F; cbn [skipn]; [constructor|apply IH; assumption]. Qed.
#[using="Type"] Lemma art_forall2_in_l : forall (A B : Type) (R : A -> B -> Prop) l l' x, Forall2 R l l' -> In x l -> exists y, In y l' /\ R x y.
Proof.
intros A B R l l' x F. induction F as [|a b l l' Hab _ IH]; intros Hx; [destruct Hx|].
destruct Hx as [<-|Hx]; [exists b; split; [left; reflexivity|exact Hab]|]. destruct (IH Hx) as (y & Hy & Ry). exists y. split; [right; exact Hy|exact Ry].
Qed.
#[using="Type"] Lemma art_rcy_npop_le : ltac2:(TCodec.tc2 tcn__JbtInvRecycle ">'F'5&Q7%211'A&RGr2r1%3221&4%1283%7231pW691pWL=1").
Proof. intros mn bs. induction bs as [|b r IH]; [cbn; lia|]. cbn [art_rcy_npop length]. destruct (mn <? art_qbytes (b :: r)); lia. Qed.
#[using="Type"] Lemma art_nq_len : ltac2:(TCodec.tc2 tcn__JbtInvRecycle "Q2'5'Q9%211&S2r1r2%33521&?'=':'F%2211%<11&QA%119(7%115%93531%;11p0=1pW2C1&S8&S;+2&S<&4%12IE%311%6251&Q;%11I%:231p0<1pW6O1").
Proof.
induction bs as [|b r IH]; intros NE; [cbn; lia|]. unfold art_nq in *. cbn [fold_right length]. specialize (IH (fun x Hx => NE x (or_intror Hx))).
pose proof (NE b (or_introl eq_refl)) as Nb. destruct (bt_items b); [contradiction|]. cbn [length]. lia.
Qed.
Section Work.
Variable xs : list art_rbatch.
Hypothesis XS : Forall2 art_batch_ok (g_qg FSG G) xs.
#[using="LB bt bg REPX XS"] Lemma art_work_ok : ltac2:(TCodec.tc2 tcn__JbtInvRecycle "<'R;&S2r1&RBvT9%211%53641&R4r2%211p041pW:;1").
Proof.
intros e He. unfold art_rb_work in He. apply in_flat_map in He. destruct He as (x & Hx & He).
destruct (art_forall2_in_r _ _ _ _ _ x XS Hx) as (b & Hb & Hbx). unfold art_rb_work1 in He. apply in_app_or in He. destruct He as [He|[<-|[]]].
- destruct Hbx as (_ & _ & _ & F2 & _). destruct (art_forall2_in_r _ _ _ _ _ e F2 He) as (it & _ & Hit). exact (art_item_wk it e Hit).
- exact (art_batch_wk b x Hb Hbx).
Qed.
#[using="Type"] Lemma art_cell8_inj : ltac2:(TCodec.tc2 tcn__JbtInvRecycle "Q0'F&L&S0vHr3u8r2%6554321r4%8576143'<&S8z%2215&S9&S=+2+R0%3221%52;1%:271'=r6r5%33H21p051p061p0B1p0E1pX>M1pX<N1pW0O1").
Proof.
intros a v w C1 C2 Hv Hw. unfold cell in *. rewrite C1 in C2.
apply (f_equal (fun o : option (list byte) => match o with Some l => bytes_le_to_Z l | None => 0 end)) in C2.
rewrite !SeqExec.bytes_le_to_Z_8 in C2. rewrite !art_u_lit in C2 by lia. exact C2.
Qed.
#[using="rn LB M bt bg REPX"] Lemma art_sec_idx_inj : forall i i' s s', nth_error (g_sec FSG G) i = Some s -> nth_error (g_sec FSG G) i' = Some s' -> sc_map s = sc_map s' -> i = i'.
Proof.
intros i i' s s' Hi Hi' E. pose proof REPX as (_ & _ & _ & _ & _ & SECR & _). destruct SECR as (_ & _ & _ & _ & _ & _ & _ & _ & PER & _ & LEN).
destruct (PER i s Hi) as (_ & _ & _ & _ & _ & Ci & _). destruct (PER i' s' Hi') as (_ & _ & _ & _ & _ & Ci' & _). rewrite <- E in Ci'.
assert (Li : (i < length (g_sec FSG G))%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
assert (Li' : (i' < length (g_sec FSG G))%nat) by (apply nth_error_Some; rewrite Hi'; discriminate).
pose proof (art_cell8_inj _ _ _ Ci Ci' ltac:(lia) ltac:(lia)) as Ei. apply Nat2Z.inj in Ei. exact Ei.
Qed.
#[using="rn LB M bt bg REPX"] Lemma art_sec_map_inj : forall s s', In s (g_sec FSG G) -> In s' (g_sec FSG G) -> sc_map s = sc_map s' -> s = s'.
Proof.
intros s s' Hs Hs' E. destruct (In_nth_error _ _ Hs) as (i & Hi). destruct (In_nth_error _ _ Hs') as (i' & Hi').
rewrite (art_sec_idx_inj i i' s s' Hi Hi' E) in Hi. rewrite Hi in Hi'. injection Hi' as <-. reflexivity.
Qed.
#[using="LB bt bg REPX"] Lemma art_wk_key_addr : ltac2:(TCodec.tc2 tcn__JbtInvRecycle "K'R;&R4r2%211'=':'F%2211&R5r4%211r3%411%93631&R<&QLvT0%211r5%5221%623;%A3?21p091p0D1p0E1pW<I1pW:J1").
Proof.
intros e e' (PRE & _ & GH) (PRE' & _ & GH') EK.
destruct e as [c w d b1 n|mb ms m b1 n|wb]; destruct e' as [c' w' d' b1' n'|mb' ms' m' b1' n'|wb']; cbn [art_rel_key art_rel_pre] in *.
- injection EK as <- <-. rewrite GH in GH'. injection GH' as E _. cbn [art_rel_addr]. lia.
- destruct PRE as (Hc & _). injection EK as E _. lia.
- injection EK as -> ->. rewrite GH in GH'. discriminate GH'.
- destruct PRE' as (Hc & _). injection EK as E _. lia.
- injection EK as <-. destruct GH as (s & Hs & _ & Eu & _ & Emb & _). destruct GH' as (s' & Hs' & _ & Eu' & _ & Emb' & _).
rewrite (art_sec_map_inj s s' Hs Hs' ltac:(congruence)) in Eu. cbn [art_rel_addr]. lia.
- injection EK as E. lia.
- injection EK as <- <-. rewrite GH in GH'. discriminate GH'.
- injection EK as E. lia.
- injection EK as <-. reflexivity.
Qed.
#[using="FSG G LB M bt bg REPX QT0 LIVE XS"] Lemma art_work_nodup_addr : ltac2:(TCodec.tc2 tcn__JbtInvRecycle ">'S3'F&D'R;&R<&QLvT0%211%411&RBvT9%211%:49;41%=2<1").
Proof.
pose proof REPX as (_ & _ & _ & _ & _ & _ & QR & _). destruct QR as (_ & _ & _ & _ & _ & ND & _ & _ & NDI & _). rewrite QT0 in ND, NDI. cbn [app] in ND, NDI.
apply NoDup_ListNoDup in ND. apply NoDup_ListNoDup in NDI.
unfold art_rb_work. rewrite art_map_flat_map.
replace (flat_map (fun x => map (art_rel_addr spb) (art_rb_work1 x)) xs)
with (flat_map (fun x => map (art_rel_addr spb) (rb_items x) ++ [spb + 24 * 2 ^ 32 + 16 * rb_wb x]) xs)
by (apply flat_map_ext; intros x; unfold art_rb_work1; rewrite map_app; reflexivity).
apply art_nodup_flat_snoc.
- rewrite (art_xs_items _ _ XS). exact NDI.
- rewrite (art_xs_addrs _ _ XS). exact ND.
- intros x x' Hx Hx' Hin. apply in_map_iff in Hin. destruct Hin as (e & Ee & He).
destruct (art_forall2_in_r _ _ _ _ _ x XS Hx) as (b & Hb & Hbx). destruct (art_forall2_in_r _ _ _ _ _ x' XS Hx') as (b' & Hb' & Hbx').
pose proof Hbx' as (_ & _ & _ & F2 & _). destruct (art_forall2_in_r _ _ _ _ _ e F2 He) as (it & _ & Hit).
apply (art_wk_reb_item (rb_wb x) e (art_batch_wk b x Hb Hbx) (art_item_wk it e Hit) (proj1 Hit)). cbn [art_rel_addr]. symmetry. exact Ee.
Qed.
#[using="FSG rn G LB M bt bg REPX QT0 LIVE XS"] Lemma art_work_nodup_key : ltac2:(TCodec.tc2 tcn__JbtInvRecycle "<'S3':'F%2211&D'R;&R5&RBvT9%211%645741%;281").
Proof.
apply (art_nodup_map_of _ _ _ (art_rel_addr spb) art_rel_key); [|exact art_work_nodup_addr].
intros e e' He He' EK. exact (art_wk_key_addr e e' (art_work_ok e He) (art_work_ok e' He') EK).
Qed.
#[using="rn LB M bt bg REPX GHOST"] Lemma art_rg_ok_gr : ltac2:(TCodec.tc2 tcn__JbtInvRecycle "3&R6&R2%211").
Proof.
destruct GHOST as (_ & GC & _). split; [intros c Hc; exact (proj2 (GC c Hc))|].
cbn [art_gr rg_bl]. intros b b' Hb Hb' E. apply in_map_iff in Hb. apply in_map_iff in Hb'. destruct Hb as (s & <- & Hs). destruct Hb' as (s' & <- & Hs').
cbn [art_sec_b fst] in E. rewrite (art_sec_map_inj s s' Hs Hs' E). reflexivity.
Qed.
Variable k : nat.
#[using="Type"] Lemma art_work_split : ltac2:(TCodec.tc2 tcn__JbtInvRecycle "B'='5'R;%211&RBvT9%211&1&C&RCvSK%33216%811&E%13549%;11%93>41%A3>;1").
Proof. unfold art_rb_work. rewrite <- flat_map_app, firstn_skipn. reflexivity. Qed.
#[using="Type"] Lemma art_work_pre_in : ltac2:(TCodec.tc2 tcn__JbtInvRecycle "@'R;&S2r1&RB&C&RCvSKvT9%43321%611%93:81r2%915%<3=21p041pW:?1").
Proof. intros e He. rewrite art_work_split. apply in_or_app. left. exact He. Qed.
#[using="FSG rn G LB M bt bg REPX QT0 LIVE XS"] Lemma art_work_pre_nodup : ltac2:(TCodec.tc2 tcn__JbtInvRecycle "@'S3':'F%2211&D'R;&R5&RB&C&RCvSKvT9%43321%611%:49;81%?2<1").
Proof. pose proof art_work_nodup_key as ND. rewrite art_work_split, map_app in ND. exact (NoDup_app_remove_r _ _ ND). Qed.
#[using="rn LB M bt bg REPX GHOST QT0 LIVE XS"] Lemma art_entry_pre : ltac2:(TCodec.tc2 tcn__JbtInvRecycle ":&RM&R2&RB&C&RCvSKvT9%43321%611%9281").
Proof.
apply art_rels_pre_intro; [exact art_rg_ok_gr| |exact art_work_pre_nodup].
intros e He. exact (proj1 (art_work_ok e (art_work_pre_in e He))).
Qed.
#[using="FSG G LB M bt bg REPX QT0 LIVE LIVE2 XS"] Lemma art_entry_sep : ltac2:(TCodec.tc2 tcn__JbtInvRecycle "<&RN&QLvT0%211&RB&C&RCvSKvT9%43321%611%;281").
Proof.
apply art_rels_sep_intro; [|exact art_work_pre_nodup]. intros e e' He He' NE.
apply art_el_zapart; [apply art_pre_geo; exact (proj1 (art_work_ok e (art_work_pre_in e He)))|apply art_pre_geo; exact (proj1 (art_work_ok e' (art_work_pre_in e' He')))|exact NE].
Qed.
#[using="FSG G LB bt bg REPX XS"] Lemma art_entry_mem : ltac2:(TCodec.tc2 tcn__JbtInvRecycle "B'B'R;&RJ&QLvT0%211r1vH%63321qW:81&RB&C&RCvSKvT9%43321%611%A3@81").
Proof. apply Forall_forall. intros e He. exact (proj1 (proj2 (art_work_ok e (art_work_pre_in e He)))). Qed.
#[using="FSG rn G LB M bt bg REPX GHOST XS"] Lemma art_entry_rb_ok : ltac2:(TCodec.tc2 tcn__JbtInvRecycle "5'B&RC&R@vT9%43321").
Proof.
pose proof REPX as (_ & _ & _ & _ & _ & _ & QR & _). destruct QR as (_ & (fg & lg & _ & _ & _ & _ & BLg) & _ & _ & _ & _ & NEI & _).
apply Forall_forall. intros x Hx. destruct (art_forall2_in_r _ _ _ _ _ x XS Hx) as (b & Hb & (_ & _ & _ & F2 & Esz)).
assert (Hb' : In b (g_qt FSG G ++ g_qg FSG G)) by (apply in_or_app; right; exact Hb).
split. { intros E. rewrite E in F2. inversion F2 as [E0|]. exact (NEI b Hb' (eq_sym E0)). }
split. { apply Forall_forall. intros e He. destruct (art_forall2_in_r _ _ _ _ _ e F2 He) as (it & _ & Hit). exact (proj1 Hit). }
rewrite Esz. unfold art_bt_bytes.
assert (RNG : forall it, In it (bt_items b) -> 0 <= snd it < 2 ^ 32).
{ intros it Hit. destruct (art_item_exists b it Hb' Hit) as (e & _ & _ & PRE & _ & GH).
destruct e as [c w d b1 n|mb ms m b1 n|wb]; [| |destruct GH]; cbn [art_rel_pre] in PRE.
- destruct GH as (<- & _). destruct PRE as (_ & _ & _ & _ & _ & _ & _ & Hn). exact Hn.
- destruct GH as (<- & _). destruct PRE as (_ & _ & _ & _ & Hn). exact Hn. }
pose proof (art_sum_snd_bound (bt_items b) (2 ^ 32) RNG) as SB0. pose proof (art_batch_list_len M _ _ _ b BLg Hb) as L. lia.
Qed.
#[using="FSG G LB M bt bg REPX QT0 LIVE LIVE2 XS"] Lemma art_entry_sepr : ltac2:(TCodec.tc2 tcn__JbtInvRecycle "N'B&Q7'R;&RO&QLvT0%211r1&Q8r2%211+XP0%946521qW:;1&RB&C&RCvSKvT9%43321%611%E3C81qW2E1&D&RA%11C&E%13;:9%54<K31%M3L71").
Proof.
apply Forall_forall. intros qb Hqb. apply in_map_iff in Hqb. destruct Hqb as (x & <- & Hx). apply Forall_forall. intros e He.
assert (Hreb : In (REB (rb_wb x)) (art_rb_work (skipn k xs))).
{ unfold art_rb_work. apply in_flat_map. exists x. split; [exact Hx|]. unfold art_rb_work1. apply in_or_app. right. left. reflexivity. }
pose proof art_work_nodup_key as ND. rewrite art_work_split in ND.
pose proof (art_nodup_app_d _ _ art_rel_key _ _ e (REB (rb_wb x)) ND He Hreb) as NE.
assert (Hreb' : In (REB (rb_wb x)) (art_rb_work xs)) by (rewrite art_work_split; apply in_or_app; right; exact Hreb).
exact (art_el_zapart e (REB (rb_wb x)) (art_pre_geo _ (proj1 (art_work_ok e (art_work_pre_in e He)))) (art_pre_geo _ (proj1 (art_work_ok _ Hreb'))) NE).
Qed.
#[using="FSG G LB M bt bg REPX QT0 LIVE LIVE2 XS"] Lemma art_entry_sepi : ltac2:(TCodec.tc2 tcn__JbtInvRecycle "O'B'R;&R?r1%211&Q7&RO&QLvT0%211r3&Q8%119+8%845421qW2:1&D&RC&RA%11:vT9%544@21%F3A71p0C1qW:G1&RB&CvSK%23;18%411%N3M61").
Proof.
apply Forall_forall. intros e He IT. apply Forall_forall. intros qb Hqb. apply in_map_iff in Hqb. destruct Hqb as (x & <- & Hx).
assert (Hreb : In (REB (rb_wb x)) (art_rb_work xs)).
{ unfold art_rb_work. apply in_flat_map. exists x. split; [exact Hx|]. unfold art_rb_work1. apply in_or_app. right. left. reflexivity. }
assert (NE : art_rel_key e <> art_rel_key (REB (rb_wb x))).
{ intros E. pose proof (art_nodup_key_eq _ _ art_rel_key _ e (REB (rb_wb x)) art_work_nodup_key (art_work_pre_in e He) Hreb E) as Ee. rewrite Ee in IT. exact IT. }
pose proof (art_el_zapart e (REB (rb_wb x)) (art_pre_geo _ (proj1 (art_work_ok e (art_work_pre_in e He)))) (art_pre_geo _ (proj1 (art_work_ok _ Hreb))) NE) as Z.
unfold art_zapart, apart in *. cbn [art_rel_zone art_rb_q qb_addr fst snd] in *. lia.
Qed.
#[using="LB M bt bg REPX"] Lemma art_rec_geo : forall b, In b (g_qg FSG G) ->
exists w, bt_addr b = spb + 24 * 2 ^ 32 + 16 * w /\ 0 <= w /\ 16 * w + 8192 <= 3758096384 /\ (exists i, 16 * w = 8192 * i)
/\ 0x693000 <= bt_addr b /\ bt_addr b + 8192 <= rn_HI rn.
Proof.
intros b Hb. pose proof REPX as (ROK & _ & _ & (_ & PRIM & _) & _ & _ & QR & _). destruct QR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & BCH).
destruct ROK as (GEO & _ & _ & Kspb & Kend & _). destruct GEO as (G1 & G2 & Espb & G4 & _).
destruct (BCH b (in_or_app _ _ b (or_intror Hb))) as (w & Ew & (Hw0 & Hwau & Hi) & _). rewrite art_class_size_24 in *.
destruct (PRIM 24 ltac:(lia)) as (_ & OK & _). destruct OK as (_ & (_ & Haumu) & _ & _ & _ & Hmu3 & _).
exists w. split; [exact Ew|]. split; [exact Hw0|]. split; [lia|]. split; [exact Hi|]. lia.
Qed.
#[using="rn LB M bt bg REPX"] Lemma art_entry_qsep_gen : forall bs, (forall b, In b bs -> In b (g_qg FSG G)) -> List.NoDup (map bt_addr bs) -> art_qsep (map art_qb bs).
Proof.
induction bs as [|b r IH]; intros Hin ND; cbn [map art_qsep]; [exact I|]. cbn [map] in ND. inversion ND as [|? ? Hn Nd]; subst.
destruct (art_rec_geo b (Hin b (or_introl eq_refl))) as (w & Ew & Hw0 & Hwu & Hi & Lo & Hi').
pose proof REPX as (ROK & _). destruct ROK as (GEO & _). destruct GEO as (G1 & G2 & _).
cbn [art_qb qb_addr fst]. split; [lia|]. split; [lia|]. split; [|apply IH; [intros b' Hb'; apply Hin; right; exact Hb'|exact Nd]].
apply Forall_forall. intros qb Hqb. apply in_map_iff in Hqb. destruct Hqb as (b' & <- & Hb'). cbn [art_qb qb_addr fst].
destruct (art_rec_geo b' (Hin b' (or_intror Hb'))) as (w' & Ew' & Hw0' & Hwu' & Hi2 & _).
assert (NE : (24, w) <> (24, w')). { intros E. injection E as E. apply Hn. rewrite Ew, E, <- Ew'. apply in_map. exact Hb'. }
pose proof (art_chunk_apart spb 24 w 24 w' ltac:(lia) ltac:(lia) Hw0 ltac:(rewrite art_class_size_24; exact Hwu) ltac:(rewrite art_class_size_24; exact Hi)
Hw0' ltac:(rewrite art_class_size_24; exact Hwu') ltac:(rewrite art_class_size_24; exact Hi2) NE) as A.
rewrite art_class_size_24 in A. rewrite Ew, Ew'. exact A.
Qed.
#[using="rn LB M bt bg REPX QT0"] Lemma art_entry_qsep : art_qsep (map art_qb (g_qg FSG G)).
Proof.
pose proof REPX as (_ & _ & _ & _ & _ & _ & QR & _). destruct QR as (_ & _ & _ & _ & _ & ND & _). rewrite QT0 in ND. cbn [app] in ND. apply NoDup_ListNoDup in ND.
apply art_entry_qsep_gen; [intros b Hb; exact Hb|exact ND].
Qed.
#[using="FSG G LB M bt bg REPX GHOST XS"] Lemma art_entry_qin : ltac2:(TCodec.tc2 tcn__JbtInvRecycle "E'<'B&Q7&RF&QBvT0%211%411&D&RC&RA&QL%117%311vT9%746=21%?3>91&RH%116%B3A14%D241").
Proof.
split; apply Forall_forall; intros qb Hqb; apply in_map_iff in Hqb; destruct Hqb as (x & <- & Hx);
destruct (art_forall2_in_r _ _ _ _ _ x XS Hx) as (b & Hb & Hbx); rewrite (art_batch_ok_q b x Hbx);
destruct (art_rec_geo b Hb) as (w & Ew & Hw0 & Hwu & Hi & Lo & Hi'); cbn [art_qb qb_addr qb_size fst snd].
- unfold art_qin. cbn [art_qb qb_addr qb_size fst snd]. split; [exact Lo|]. split; [exact Hi'|].
pose proof (proj1 (Forall_forall _ _) art_entry_rb_ok x Hx) as (_ & _ & Hsz). destruct Hbx as (_ & _ & _ & _ & Esz). rewrite <- Esz. exact Hsz.
- unfold art_qin24. cbn [art_qb qb_addr fst]. rewrite Ew. lia.
Qed.
#[using="Type"] Lemma art_work_len : ltac2:(TCodec.tc2 tcn__JbtInvRecycle "J'5'Q9%211&RC%411'S1&R0r2r1%4586321'='F&S<&4'R;&RB%119%4231%611&Q;r3%211%<3;41p0>1pXFD1pW6G1").
Proof.
intros bs xs' F. induction F as [|b x bs' xs'' Hbx _ IH]; [reflexivity|].
change (art_rb_work (x :: xs'')) with (art_rb_work1 x ++ art_rb_work xs''). unfold art_rb_work1. rewrite !length_app. cbn [length].
destruct Hbx as (_ & _ & _ & F2 & _). rewrite <- (Forall2_length F2). unfold art_nq in *. cbn [fold_right]. lia.
Qed.
#[using="rn M XS"] Lemma art_work_pre_len : 0 <= Z.of_nat (length (art_rb_work (firstn k xs))) <= art_nq (g_qg FSG G).
Proof. rewrite <- (art_work_len _ _ XS). rewrite art_work_split, length_app. lia. Qed.
Hypothesis ROOM : forall c, 1 <= c <= 30 ->
Z.of_nat (length (cl_free (g_cls FSG G c))) + Z.of_nat (length (cl_cache (g_cls FSG G c))) + art_nq (g_qg FSG G) <= 65536.
Hypothesis NEg : g_qg FSG G <> [].
Hypothesis LIVESH : forall p, In p (art_live (g_log FSG G)) -> wrA M (JbtPoison.SB + fst p / 8) (snd p / 8).
#[using="Type"] Lemma art_statics_cells : ltac2:(TCodec.tc2 tcn__JbtInvRecycle "@&Q=vT0vH%3221'<&L&S0+QV`o0u8+1%5548321+RPjH+\hkdfgWVVmUeI%857;251%:241p0<1").
Proof. unfold art_rt_statics, art_alloc_rodata. intros H. decompose [and] H. split; assumption. Qed.
#[using="Type"] Lemma art_rok_sec : ltac2:(TCodec.tc2 tcn__JbtInvRecycle "QA&Q?vT0%211'<&S8+Vb\P0&QI%116%4231&S6&S=+2+G%3221%5271&QB%11?%=231&Q0%12<6&K&QM%11E+TP0%44A;21&QE%11I%74D>14&QL%11L+Q5%E2D1%G219%=4JD41&S9&QG%11Q3%3218+RPP0%N231%Q42;1%Q6241%Q7291%Q82@1%Q92D1%Q:2J1%Q;2M1%Q<2Q71p0Q>1").
Proof. intros ROK. rok_open14 ROK. exact (conj Plo (conj Phi (conj Papp (conj Apt (conj Apc (conj Apk Kspb)))))). Qed.
Section SE.
Local Abbreviation SEC_T_art_entry_inv := (forall nt, 0 <= nt <= art_nq (g_qg FSG G) ->
art_rcy_inv (rn_HI rn) (rn_t rn) (rn_ctx rn) (rn_tp rn) (rn_key rn) (rn_tsd rn) spb (rn_ris rn) (rn_qs rn) (rn_parr rn) nt art_gr M) (only parsing).
Variable nt : ltac:(sec_ty2 constr:(SEC_T_art_entry_inv) 0%nat 0%nat).
Lemma art_entry_inv : ltac:(sec_stmt2 constr:(SEC_T_art_entry_inv) 1%nat 0%nat).
Proof using LB bt bg REPX GHOST LIVE LIVE2 LIVE3 ROOM NEg LIVESH nt.
intros Hnt.
pose proof REPX as (ROK & ST & TH & (PCH & PRIM & WSH) & CH & SECR & QR & _).
pose proof ST as (PC & LAY & TSD & _). destruct (art_statics_cells ST) as (C55 & CMAG). destruct TH as (WT & _).
destruct (art_rok_sec ROK) as (Plo & Phi & Papp & Apt & Apc & Apk & Kspb). clear ROK ST.
destruct SECR as (S0 & S8 & S56 & _ & S616 & _ & SNE & SCW & PER & _ & SLEN).
destruct GHOST as (_ & GC & _).
assert (INI : g_inited FSG G = true).
{ assert (EXb : exists b0, In b0 (g_qg FSG G)) by (clear - NEg; destruct (g_qg FSG G) as [|b0 r0]; [contradiction|exists b0; left; reflexivity]).
destruct EXb as (b0 & Hb0).
destruct QR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & BCH). destruct (BCH b0 ltac:(apply in_or_app; right; exact Hb0)) as (w' & _ & (Hw0' & Hwau & _) & _).
rewrite art_class_size_24 in Hwau. destruct (PRIM 24 ltac:(lia)) as (_ & _ & _ & _ & I2). apply I2. clear - Hw0' Hwau. lia. }
unfold art_rcy_inv. cbn [art_gr rg_cls rg_bl].
split.
{ intros c Hc. destruct (PRIM c Hc) as (RC & OK & _). destruct (GC c Hc) as (MF & CL). split; [exact RC|]. split; [exact OK|]. split; [exact CL|].
intros Hau. specialize (MF Hau). pose proof (ROOM c Hc) as RM. clear - MF RM Hnt. lia. }
split; [rewrite INI in PCH; exact PCH|]. split; [exact PC|]. split; [exact LAY|]. split; [exact TSD|]. split; [exact C55|]. split; [exact CMAG|].
split; [exact WT|]. split; [exact WSH|].
assert (LENB : Z.of_nat (length (map art_sec_b (g_sec FSG G))) = Z.of_nat (length (g_sec FSG G))) by (rewrite length_map; reflexivity).
assert (NTH : forall j b, nth_error (map art_sec_b (g_sec FSG G)) j = Some b -> exists s, nth_error (g_sec FSG G) j = Some s /\ b = art_sec_b s).
{ intros j b Hj. rewrite nth_error_map in Hj. destruct (nth_error (g_sec FSG G) j) as [s|] eqn:Es; [|discriminate Hj]. cbn in Hj. injection Hj as <-. exists s. split; reflexivity. }
assert (INB : forall b, In b (map art_sec_b (g_sec FSG G)) -> exists i s, nth_error (g_sec FSG G) i = Some s /\ b = art_sec_b s).
{ intros b Hb. apply in_map_iff in Hb. destruct Hb as (s & <- & Hs). destruct (In_nth_error _ _ Hs) as (i & Hi). exists i, s. split; [exact Hi|reflexivity]. }
assert (OBJ : forall p o, In p (art_live (g_log FSG G)) -> In o (art_objs rn) -> apart (fst p) (snd p) (fst o) (snd o)) by (intros p o Hp Ho; exact (proj2 (proj2 (proj2 (proj2 (LIVE p Hp)))) o Ho)).
split.
{
unfold art_sec_cells. rewrite LENB. split; [exact S0|]. split; [exact S8|]. split; [exact S56|]. split; [exact S616|].
split. { destruct (g_sec FSG G) as [|s0 r0] eqn:Es.
- intros d k0 Hd Hk0. cbn [length] in Hk0. assert (k0 = 0%nat) by (clear - Hd Hk0; lia). subst k0. reflexivity.
- eapply wr_sub; [exact (SCW (SNE ltac:(discriminate)))|clear; lia|clear - SLEN; lia]. }
intros j b Hj. destruct (NTH j b Hj) as (s & Hs & ->). destruct (PER j s Hs) as (P1 & P2 & P3 & P4 & P5 & P6 & _). cbn [art_sec_b fst snd].
split; [exact P1|]. split; [exact P4|]. split; [exact P5|]. split; [exact P6|]. split; [exact P3|exact (LIVESH _ P2)]. }
split.
{
unfold art_sec_geo. rewrite LENB. split; [exact Plo|]. split; [clear - Phi SLEN; lia|]. split; [clear - SLEN; lia|].
split. { unfold appmem, JbtPoison.SB, kHighMemBeg. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Papp. clear - Papp SLEN. lia. }
split. { unfold apart in *. clear - Apt SLEN. lia. } split. { unfold apart in *. clear - Apc SLEN. lia. }
split.
- intros b Hb. destruct (INB b Hb) as (i & s & Hs & ->). destruct (PER i s Hs) as (_ & P2 & _ & _ & _ & _ & Lo & Hi & Q & P0). cbn [art_sec_b fst snd].
destruct (LIVE _ P2) as (L0 & L1 & L2 & L3 & _). destruct (LIVE3 _ P2) as (A1 & A2). cbn [fst snd] in *.
assert (Hn : 1 <= sc_n s) by (destruct (sc_quar s); [destruct Q as ((b1 & _ & _ & _ & _ & Hn) & _)|destruct Q as (_ & (b1 & _ & _ & _ & _ & Hn) & _)]; clear - Hn; lia).
split; [exact A1|]. split; [exact A2|]. split; [clear - Lo Hi Hn; lia|]. split; [exact P0|]. split; [exact L2|].
split. { unfold appmem, JbtPoison.SB, kHighMemBeg. clear - L3. lia. }
pose proof (OBJ _ (rn_parr rn, 2 ^ 23) P2 ltac:(cbn; tauto)) as O1. pose proof (OBJ _ (rn_t rn, 4096) P2 ltac:(cbn; tauto)) as O2. pose proof (OBJ _ (rn_ctx rn, 4096) P2 ltac:(cbn; tauto)) as O3.
cbn [fst snd] in O1, O2, O3. unfold apart in *. clear - O1 O2 O3 SLEN. repeat split; lia.
- intros i j b b' Hi Hj NE. destruct (NTH i b Hi) as (s & Hs & ->). destruct (NTH j b' Hj) as (s' & Hs' & ->). cbn [art_sec_b fst snd].
destruct (PER i s Hs) as (_ & P2 & _). destruct (PER j s' Hs') as (_ & P2' & _).
apply (LIVE2 _ _ P2 P2'). cbn [fst]. intros E. apply NE. exact (art_sec_idx_inj i j s s' Hs Hs' E). }
split.
- intros b Hb. destruct (INB b Hb) as (i & s & Hs & ->). destruct (PER i s Hs) as (_ & P2 & _). pose proof (OBJ _ (rn_kbase rn, 0x2000011000) P2 ltac:(cbn; tauto)) as O1.
cbn [art_sec_b fst snd] in *. unfold apart in *. clear - O1 Kspb. lia.
- rewrite LENB. unfold apart in *. clear - Apk SLEN. lia.
Qed.
End SE.
#[using="rn LB M bt bg REPX"] Lemma art_sec_entry_facts : forall s, In s (g_sec FSG G) -> In (sc_map s, sc_msize s) (art_live (g_log FSG G)) /\ 4096 + 16 < sc_msize s /\ 0x693000 <= sc_map s.
Proof.
intros s Hs. destruct (In_nth_error _ _ Hs) as (i & Hi). pose proof REPX as (_ & _ & _ & _ & _ & SECR & _). destruct SECR as (_ & _ & _ & _ & _ & _ & _ & _ & PER & _).
destruct (PER i s Hi) as (_ & P2 & _ & _ & _ & _ & Lo & Hi2 & Q & P0). split; [exact P2|]. split; [|exact P0].
assert (Hn : 1 <= sc_n s) by (destruct (sc_quar s); [destruct Q as ((b1 & _ & _ & _ & _ & Hn) & _)|destruct Q as (_ & (b1 & _ & _ & _ & _ & Hn) & _)]; clear - Hn; lia).
clear - Lo Hi2 Hn. lia.
Qed.
Variables (M' : word -> option byte) (sp lg : Z).
#[local] Abbreviation work := (art_rb_work (firstn k xs)).
#[local] Abbreviation gq := (map (art_rb_q spb) xs).
#[local] Abbreviation Wtot := (art_rcy_W2 sp gq ++ art_rels_fp (rn_t rn) spb (rn_ris rn) (rn_parr rn) (sp - 192) art_gr work ++ [(sp - 192, 144)]).
Hypothesis HSP : rn_HI rn <= sp - 512.
#[using="Type"] Lemma art_rok_rcy : ltac2:(TCodec.tc2 tcn__JbtInvRecycle "S3&Q?vT0%211'<&S8+`PQoooPP0&QB%116%4231&S6+XPPP0%2241&S=+2+Q?%3221%<251'='F&QL%11C&S;+RPP0&QJ%11G%4231%93861%G2F7&QK%11L+Q5%C2B1%G2<1%@3?41+TP0%J261%Q021M&QM%11Q5%Q3251%O226%Q521Q2'@%Q723E+Vb\P0%Q9217%4231+QoonlP0%Q<281%Q=2Q<;%8221&S9&QG%11QD%321Q2%Q>22Q1%QD2Q41%QF231+TPPPRTP0%QB261%QH21QE&K%14HL94&QI%11QO%QM2E1+G%QG2QF1%QK241%R121QN&Q0%1274%;485Q2Q6%<496D?%R62R5E%R22Q<Q9%?4Q6Q:QH1%@4=:QI2%R;221%R<251%R=271%R>291%R?2;1%R@2>1%RA2C1%RB2G1%RC2J1%RD2N1%RE2Q61%RF2Q;1%RG2QA1%RH2QD1%RI2QH1%RJ2QL1%RK2R31%RL2R51%RM2R@1%RN2RI1p0S01").
Proof.
intros ROK. destruct ROK as (GEO & Esb & Kal & Kspb & Kend & Pal & Plo & Phi & Papp & Hkey & Hloff & Hloff' & Hloff'' & Htpd & Htsdd & Dl2 & Dblk
& Al2t & Al2c & Al2k & Al2s & Abt & Abc & Abk & Abs & Apt & Apc & Apk & Apl & Apb & Aft & Afc & Afk & Afl & Afb & Afp & Fhi & Fapp & Fimg & Flo
& Il2 & Iblk & Afkb & D0 & D1 & D2 & D3 & Adt & Adc & Adk & Adp & Adl & Adb & Adf & Atkb & Ackb & Al2kb & Apkb & Kb0).
destruct GEO as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & G9 & G10 & G11 & _).
exact (conj G1 (conj G2 (conj Espb (conj G4 (conj Eris (conj G6 (conj G7 (conj G8 (conj G9 (conj G10 (conj Kspb (conj Kend (conj Atkb (conj Plo (conj Phi (conj Papp (conj Apt (conj Apkb (conj Kb0 (conj G11 Apk)))))))))))))))))))).
Qed.
Definition art_far_obj (a n : Z) : Prop :=
0 <= a /\ a + n <= rn_HI rn /\ (a + n <= 0x10000 \/ 0x693000 <= a) /\ apart a n (rn_t rn) 4096 /\ apart a n spb (2 ^ 37 + 4096) /\ apart a n (rn_parr rn) (2 ^ 23)
/\ (a + n <= 0x7fff8000 \/ 0x10007fff8000 <= a) /\ In (a, n) (art_objs rn).
#[using="Type"] Lemma art_objs_in : ltac2:(TCodec.tc2 tcn__JbtInvRecycle "Q;'<&S2':'F%2211(9&QEvT0%211+TP0%547721&Q<%115%<3931&QH%118&S=+2+D%3221%?4AA51%D3A19&QD%11@+G%9281%E4GG31%J3G1?&Q1&QC%11G%311&N%L4NN21%Q13N1F&QF%11M%Q04Q2Q21L%Q53Q21J%Q7251%Q82=1%Q92D1%Q:2M1").
Proof. unfold art_objs. cbn [In]. tauto. Qed.
#[using="Type"] Lemma art_rok_far : ltac2:(TCodec.tc2 tcn__JbtInvRecycle "Q3&Q?vT0%211'<&QO&QE%115+TP0%4221&QH%119&S=+2+D%3221%;251&QD%11@+G%8271%@231&Q1&QC%11F%311&N%F221&QF%11K%I21F%K241%L2;1%M2A1%N2I1p0Q01").
Proof.
intros ROK. destruct ROK as (GEO & Esb & Kal & Kspb & Kend & Pal & Plo & Phi & Papp & Hkey & Hloff & Hloff' & Hloff'' & Htpd & Htsdd & Dl2 & Dblk
& Al2t & Al2c & Al2k & Al2s & Abt & Abc & Abk & Abs & Apt & Apc & Apk & Apl & Apb & Aft & Afc & Afk & Afl & Afb & Afp & Fhi & Fapp & Fimg & Flo
& Il2 & Iblk & Afkb & D0 & D1 & D2 & D3 & Adt & Adc & Adk & Adp & Adl & Adb & Adf & Atkb & Ackb & Al2kb & Apkb & Kb0).
destruct GEO as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & G9 & G10 & G11 & _ & G13 & G14 & G15 & G16 & G17 & G18 & _).
destruct art_objs_in as (I1 & I2 & I3 & I4 & I5).
unfold art_far_obj, app_mem, BIGSHADOW_LO, BIGSHADOW_HI, apart in *.
split; [|split; [|split; [|split]]].
- split; [clear - G13; lia|]. split; [exact G14|]. split; [exact G15|]. split; [clear - G18; lia|]. split; [exact G17|]. split; [clear - Apc; lia|]. split; [clear - G16; lia|exact I1].
- split; [clear - Il2; lia|]. split; [exact Dl2|]. split; [right; exact Il2|]. split; [exact Al2t|]. split; [exact Al2k|]. split; [clear - Apl; lia|]. split; [clear - Al2s; lia|exact I2].
- split; [clear - Iblk; lia|]. split; [exact Dblk|]. split; [right; exact Iblk|]. split; [exact Abt|]. split; [exact Abk|]. split; [clear - Apb; lia|]. split; [clear - Abs; lia|exact I3].
- split; [clear - Flo; lia|]. split; [exact Fhi|]. split; [exact Fimg|]. split; [exact Aft|]. split; [exact Afk|]. split; [exact Afp|]. split; [unfold FS_BYTES in Fapp |- *; clear - Fapp; lia|exact I4].
- split; [clear - D0; lia|]. split; [exact D1|]. split; [exact D2|]. split; [exact Adt|]. split; [clear - Adk Kspb Eris G6; lia|]. split; [exact Adp|]. split; [clear - D3; lia|exact I5].
Qed.
#[using="LB M bt bg REPX XS"] Lemma art_work_zone_where : forall e x, In e work -> fst (art_rel_zone spb e) <= x < fst (art_rel_zone spb e) + snd (art_rel_zone spb e) ->
(spb <= x < spb + 2 ^ 37) \/ (exists p, In p (art_live (g_log FSG G)) /\ fst p <= x < fst p + snd p).
Proof.
intros e x He Hx. pose proof (art_pre_geo e (proj1 (art_work_ok e (art_work_pre_in e He)))) as GE.
destruct e as [c w d b1 n|mb ms m b1 n|wb]; cbn [art_rel_zone art_el_geo fst snd] in *.
- left. destruct GE as (Hc & Hw & Hu & _). destruct (art_class_size_facts c Hc) as (S1 & _). clear - Hx Hc Hw Hu S1. lia.
- right. exists (mb, ms). split; [exact GE|exact Hx].
- left. destruct GE as (Hw & Hu & _). rewrite art_class_size_24 in Hu. clear - Hx Hw Hu. lia.
Qed.
#[using="FSG G LB M bt bg REPX XS"] Lemma art_work_shw_zone : ltac2:(TCodec.tc2 tcn__JbtInvRecycle "QB'R;'F&S2r2&RB&C&RCvSKvT9%43321%611%93;81'<&S8&3&R8&QLvT0%211r3%5221%73DD1%921C&S9&S6&;%13II6%3261%52I1%A271&R9&S7&R=r4%22@1%E3Q2Q21+8%6221%>281%J21D%?3Q7Q76%A261%;216%C2=1%E2I1%Q1261p0A1p0Q41pXBQ?1pW:QA1").
Proof.
intros e x He Hx. pose proof (proj1 (art_work_ok e (art_work_pre_in e He))) as PRE. pose proof REPX as (ROK & _).
destruct (art_rok_rcy ROK) as (_ & _ & Espb & _).
apply (art_shw_in_zone spb (rn_qs rn) e x Espb); [|exact Hx].
destruct e as [c w d b1 n|mb ms m b1 n|wb]; [|exact I|exact I]. cbn [art_rel_pre] in PRE. destruct PRE as (Hc & _ & _ & Hd & Hd16 & Hdsz & _ & Hn).
destruct (art_class_size_facts c Hc) as (_ & S16). split; [exact Hd|]. split; [exact Hd16|]. split; [exact Hdsz|]. split; [exact S16|lia].
Qed.
#[using="FSG G LB M bt bg REPX LIVE XS"] Lemma art_work_zone_hi : ltac2:(TCodec.tc2 tcn__JbtInvRecycle "Q4'R;&S2r1&RB&C&RCvSKvT9%43321%611%93:81'<&S8z&3'F&R=&QLvT0%211r2%5221%83771%;2:1&;%13::4%>2=1&S6%1263&QB%11<%C231%E261%F2:1p0H1pW:Q31").
Proof.
intros e He. pose proof (art_pre_geo e (proj1 (art_work_ok e (art_work_pre_in e He)))) as GE. pose proof REPX as (ROK & _).
destruct (art_rok_rcy ROK) as (_ & _ & _ & G4 & _ & _ & _ & _ & _ & _ & Kspb & Kend & _).
destruct e as [c w d b1 n|mb ms m b1 n|wb]; cbn [art_rel_zone art_el_geo fst snd] in *.
- destruct GE as (Hc & Hw & Hu & _). destruct (art_class_size_facts c Hc) as (S1 & _). clear - Hc Hw Hu S1 Kspb Kend G4. lia.
- destruct (LIVE _ GE) as (L0 & L1 & L2 & _). cbn [fst snd] in *. clear - L0 L1 L2. lia.
- destruct GE as (Hw & Hu & _). rewrite art_class_size_24 in Hu. clear - Hw Hu Kspb Kend G4. lia.
Qed.
#[using="FSG G LB M bt bg REPX LIVE XS"] Lemma art_work_shw_shadow : ltac2:(TCodec.tc2 tcn__JbtInvRecycle "Q7'R;'F&S2r2&RB&C&RCvSKvT9%43321%611%93;81'<&S8&3&R8&QLvT0%211r3%5221%73DD1%921C&S9&S6&;%13II6%3261%52I1%A271+QoooPP0%B21<+`PQoooPP0%:2>1%F231p061p0I1pXBQ41pW:Q61").
Proof.
intros e x He Hx. pose proof (art_work_shw_zone e x He Hx) as Z. destruct (art_work_zone_hi e He) as (Z0 & Z1 & Z2). pose proof REPX as (ROK & _).
destruct (art_rok_rcy ROK) as (_ & G2 & _). unfold JbtPoison.SB in Z.
assert (0 <= fst (art_rel_zone spb e) / 8) by (apply Z.div_pos; lia).
assert ((fst (art_rel_zone spb e) + snd (art_rel_zone spb e)) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia). lia.
Qed.
#[using="LB M bt bg REPX GHOST QT0 LIVE XS ROOM"] Lemma art_rcy_fp_where : ltac2:(TCodec.tc2 tcn__JbtInvRecycle "QB':'F%2211&S2r2&RL&QMvT0%211&QL%113&QK%115&QI%117&S>vT1+V0%3221&R2&RB&C&RCvSKvT9%43321%611%F7CA?=981%I3JH1'<&S8&3r3%23Q0Q01%421N&S9&S6&;%13Q5Q56%3261%52Q41%<271&R7&R>%11I%38Q5Q3Q1OK1C=p051p0C1pXBQ?1pX0Q?1").
Proof.
intros p x Hp Hx. pose proof REPX as (_ & _ & _ & _ & _ & SECR & _). destruct SECR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SLEN).
apply (art_rels_fp_where (rn_t rn) spb (rn_ris rn) (rn_parr rn) (sp - 192) (rg_bl art_gr) work art_gr x p art_entry_pre art_rg_ok_gr); [| |intros b Hb; exact Hb|exact Hp|exact Hx].
- intros c Hc. cbn [art_gr rg_cls]. pose proof (ROOM c Hc) as RM. pose proof art_work_pre_len as WL. clear - RM WL. lia.
- cbn [art_gr rg_bl]. rewrite length_map. clear - SLEN. lia.
Qed.
Section SE.
Local Abbreviation SEC_T_art_rcy_out_far := (forall x, ~ (sp - 512 <= x < sp) -> ~ (spb <= x < spb + 2 ^ 37 + 4096) -> ~ (rn_parr rn <= x < rn_parr rn + 2 ^ 23)
-> ~ (rn_t rn <= x < rn_t rn + 4096) -> (forall p, In p (art_live (g_log FSG G)) -> ~ (fst p <= x < fst p + snd p)) -> ~ (0x7fff8000 <= x < 0x10007fff8000)
-> ~ (0x139418 + 56 <= x < 0x1396a8) -> ~ (0x1396b0 + 152 <= x < 0x1396b0 + 192) -> art_out Wtot x) (only parsing).
Variable x : ltac:(sec_ty2 constr:(SEC_T_art_rcy_out_far) 0%nat 0%nat).
Lemma art_rcy_out_far : ltac:(sec_stmt2 constr:(SEC_T_art_rcy_out_far) 1%nat 0%nat).
Proof using LB M bt bg REPX GHOST QT0 LIVE XS ROOM x.
intros Nst Nk Np Nt Nl Nsh Nsec Nq.
pose proof REPX as (ROK & _).
destruct (art_rok_rcy ROK) as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & G9 & G10 & Kspb & Kend & Atkb & Plo & Phi & Papp & Apt & Apkb & Kb0 & G11 & Apk).
apply art_out_intro. intros p Hp Hx. apply in_app_or in Hp. destruct Hp as [Hp|Hp]; [|apply in_app_or in Hp; destruct Hp as [Hp|Hp]].
- unfold art_rcy_W2 in Hp. cbn [app In] in Hp. destruct Hp as [<-|[<-|Hp]]; cbn [fst snd] in Hx; [clear - Hx Nst; lia|clear - Hx Nq; lia|].
apply in_map_iff in Hp. destruct Hp as (qb & <- & Hqb). cbn [fst snd] in Hx. pose proof (proj1 (Forall_forall _ _) (proj2 art_entry_qin) qb Hqb) as (Q1 & Q2). clear - Hx Q1 Q2 Nk. lia.
- destruct (art_rcy_fp_where p x Hp Hx) as [H|[H|[H|[H|[(c & Hc & H)|[(e & He & [H|H])|[H|(b & Hb & H)]]]]]]].
+ clear - H Nst. lia.
+ exact (Nsec H).
+ clear - H Nt. lia.
+ clear - H Nk Eris. lia.
+ clear - H Hc Nk. lia.
+ destruct (art_work_zone_where e x He H) as [Z|(q & Hq & Z)]; [clear - Z Nk; lia|exact (Nl q Hq Z)].
+ exact (Nsh (art_work_shw_shadow e x He H)).
+ exact (Np H).
+ cbn [art_gr rg_bl] in Hb. apply in_map_iff in Hb. destruct Hb as (s0 & <- & Hs0). destruct (art_sec_entry_facts s0 Hs0) as (P2 & Big & _).
apply (Nl _ P2). cbn [art_sec_b fst snd] in *. clear - H Big. lia.
- cbn [In] in Hp. destruct Hp as [<-|[]]. cbn [fst snd] in Hx. clear - Hx Nst. lia.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_rcy_out_thread := (ltac2:(TCodec.tc2 tcn__JbtInvRecycle "R5'F'<&S8&QMvT0%211r1%5221&S9&S6+TP0%2261%4261%<261&?+V@%72;1r2%@221+RjH%;2?1%=241%E241%911&Q6&1':%12KK&RIvT1&D&RC&Q7&RA&QL%11O%311vT9%847621%;2:1&RL&QK%11Q6&QI%11Q8&S>+V0%22B1&R2&RB&CvSK%23E1?%411%>7QAC<:761(2(9+T@%24QJQJ;1(7%11Q1%63Q231%Q53Q381%Q63Q4H1r3%Q9221p0Q;1p0QF1pXBR41")) (only parsing).
Variable x : ltac:(sec_ty2 constr:(SEC_T_art_rcy_out_thread) 0%nat 0%nat).
Lemma art_rcy_out_thread : ltac:(sec_stmt2 constr:(SEC_T_art_rcy_out_thread) 1%nat 0%nat).
Proof using LB M bt bg REPX GHOST QT0 LIVE XS ROOM HSP x.
intros Ht Nw.
pose proof REPX as (ROK & _).
destruct (art_rok_rcy ROK) as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & G9 & G10 & Kspb & Kend & Atkb & Plo & Phi & Papp & Apt & Apkb & Kb0 & G11 & Apk). unfold apart in Atkb, Apt, G11.
assert (NL : forall p, In p (art_live (g_log FSG G)) -> ~ (fst p <= x < fst p + snd p)).
{ intros p Hp Hx. destruct (LIVE p Hp) as (_ & _ & _ & _ & OB). pose proof (OB (rn_t rn, 4096) ltac:(cbn; tauto)) as A. cbn [fst snd] in A. unfold apart in A. clear - A Hx Ht. lia. }
apply art_out_intro. intros p Hp Hx. apply in_app_or in Hp. destruct Hp as [Hp|Hp]; [|apply in_app_or in Hp; destruct Hp as [Hp|Hp]].
- unfold art_rcy_W2 in Hp. cbn [app In] in Hp. destruct Hp as [<-|[<-|Hp]]; cbn [fst snd] in Hx; [clear - Hx Ht G8 HSP; lia|clear - Hx Ht G9; lia|].
apply in_map_iff in Hp. destruct Hp as (qb & <- & Hqb). cbn [fst snd] in Hx. pose proof (proj1 (Forall_forall _ _) (proj2 art_entry_qin) qb Hqb) as (Q1 & Q2). clear - Hx Q1 Q2 Ht G11. lia.
- destruct (art_rcy_fp_where p x Hp Hx) as [H|[H|[H|[H|[(c & Hc & H)|[(e & He & [H|H])|[H|(b & Hb & H)]]]]]]].
+ clear - H Ht G8 HSP. lia.
+ clear - H Ht G9. lia.
+ exact (Nw H).
+ clear - H Ht G11 Eris. lia.
+ clear - H Hc Ht G11. lia.
+ destruct (art_work_zone_where e x He H) as [Z|(q & Hq & Z)]; [clear - Z Ht G11; lia|exact (NL q Hq Z)].
+ pose proof (art_work_shw_shadow e x He H) as Z. clear - Z Ht G10. lia.
+ clear - H Ht Apt. lia.
+ cbn [art_gr rg_bl] in Hb. apply in_map_iff in Hb. destruct Hb as (s0 & <- & Hs0). destruct (art_sec_entry_facts s0 Hs0) as (P2 & Big & _).
apply (NL _ P2). cbn [art_sec_b fst snd] in *. clear - H Big. lia.
- cbn [In] in Hp. destruct Hp as [<-|[]]. cbn [fst snd] in Hx. clear - Hx Ht G8 HSP. lia.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_rcy_out_shadow := (ltac2:(TCodec.tc2 tcn__JbtInvRecycle "R>'F'<&S8+QoooPP0r1%3221&S9+`PQoooPP0%2241%8241'R;&S2&RB&C&RCvSKvT9%43321%611%839?1&?&3&R8&QLvT0%211r2%5221%73LL1r4%L221&S6&;%13Q1Q16%3261%M261%Q3261%A11p0C1pW:M1&Q6&1':%12Q;Q;&RIvT1&D&Q7&RA%11H%44Q431Q2%7261&RL&QM%11N&QK%11Q0&QI%11Q2&S>+V0%22@1&R2%;79Q67521Q=(2(9+T@%24R3R361(7%11J%63K31%N3L81%O3ME1r3%Q2221p0Q41p0R31pXBR=1")) (only parsing).
Variable x : ltac:(sec_ty2 constr:(SEC_T_art_rcy_out_shadow) 0%nat 0%nat).
Lemma art_rcy_out_shadow : ltac:(sec_stmt2 constr:(SEC_T_art_rcy_out_shadow) 1%nat 0%nat).
Proof using LB M bt bg REPX GHOST QT0 LIVE XS ROOM HSP x.
intros Hs Nw.
pose proof REPX as (ROK & _).
destruct (art_rok_rcy ROK) as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & G9 & G10 & Kspb & Kend & Atkb & Plo & Phi & Papp & Apt & Apkb & Kb0 & G11 & Apk).
unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Papp.
assert (NL : forall p, In p (art_live (g_log FSG G)) -> ~ (fst p <= x < fst p + snd p)).
{ intros p Hp Hx. destruct (LIVE p Hp) as (_ & _ & _ & L3 & _). clear - L3 Hx Hs. lia. }
apply art_out_intro. intros p Hp Hx. apply in_app_or in Hp. destruct Hp as [Hp|Hp]; [|apply in_app_or in Hp; destruct Hp as [Hp|Hp]].
- unfold art_rcy_W2 in Hp. cbn [app In] in Hp. destruct Hp as [<-|[<-|Hp]]; cbn [fst snd] in Hx; [clear - Hx Hs G1 HSP; lia|clear - Hx Hs; lia|].
apply in_map_iff in Hp. destruct Hp as (qb & <- & Hqb). cbn [fst snd] in Hx. pose proof (proj1 (Forall_forall _ _) (proj2 art_entry_qin) qb Hqb) as (Q1 & Q2). clear - Hx Q1 Q2 Hs G4. lia.
- destruct (art_rcy_fp_where p x Hp Hx) as [H|[H|[H|[H|[(c & Hc & H)|[(e & He & [H|H])|[H|(b & Hb & H)]]]]]]].
+ clear - H Hs G1 HSP. lia.
+ clear - H Hs. lia.
+ clear - H Hs G10. lia.
+ clear - H Hs G4 Eris. lia.
+ clear - H Hc Hs G4. lia.
+ destruct (art_work_zone_where e x He H) as [Z|(q & Hq & Z)]; [clear - Z Hs G4; lia|exact (NL q Hq Z)].
+ exact (Nw e He H).
+ clear - H Hs Papp. lia.
+ cbn [art_gr rg_bl] in Hb. apply in_map_iff in Hb. destruct Hb as (s0 & <- & Hs0). destruct (art_sec_entry_facts s0 Hs0) as (P2 & Big & _).
apply (NL _ P2). cbn [art_sec_b fst snd] in *. clear - H Big. lia.
- cbn [In] in Hp. destruct Hp as [<-|[]]. cbn [fst snd] in Hx. clear - Hx Hs G1 HSP. lia.
Qed.
End SE.
Hypothesis INV' : art_rcy_inv (rn_HI rn) (rn_t rn) (rn_ctx rn) (rn_tp rn) (rn_key rn) (rn_tsd rn) spb (rn_ris rn) (rn_qs rn) (rn_parr rn) 0 (art_rel_steps work art_gr) M'.
Hypothesis TRQ : art_rcy_trq (rn_HI rn) (rn_t rn) spb (rn_ris rn) (rn_parr rn) sp art_gr work gq M M'.
#[using="TRQ"] Lemma art_rcy_agr : ltac2:(TCodec.tc2 tcn__JbtInvRecycle "Q?&Q5&1':'F%2211&RIvT1&D&RC&Q7&RA&QLvT0%211%411vT9%948721%<2;1&RL&QM%118&QK%11:&QI%11<&S>+V0%22E1&R2&RB&CvSK%23H1A%411%@7>E<:761(2(9+T@%24Q3Q3;1(7%11Q4%63Q531%Q93Q681%Q:3Q7J1vHvI%Q>3321").
Proof. destruct TRQ as (_ & _ & _ & A). exact A. Qed.
#[using="rn LIVE"] Lemma art_live_off_img : forall p x, In p (art_live (g_log FSG G)) -> 0x10000 <= x < 0x693000 -> ~ (fst p <= x < fst p + snd p).
Proof.
intros p x Hp Hx Hin. destruct (LIVE p Hp) as (_ & _ & _ & _ & OB).
pose proof (OB (0x10000, 0x40000) ltac:(cbn; tauto)) as A1. pose proof (OB (0x50000, 0xde000) ltac:(cbn; tauto)) as A2.
pose proof (OB (0x12e000, 0x8000) ltac:(cbn; tauto)) as A3. pose proof (OB (0x136000, 0x55d000) ltac:(cbn; tauto)) as A4.
cbn [fst snd] in A1, A2, A3, A4. unfold apart in *. clear - A1 A2 A3 A4 Hx Hin. lia.
Qed.
#[using="FSG rn G LB bt bg REPX GHOST QT0 LIVE xs XS k ROOM sp HSP TRQ"] Lemma art_rcy_cell_img : ltac2:(TCodec.tc2 tcn__JbtInvRecycle "QC'F'6&S8+RPP0r3%3221&S6r4&S<%115%4231+Vb\P0%:221'@r5%718%:221+QWUPH+QH%=221%B241+QWUe8%D218%:231r6%A1;%D221+QWUe@+TH%G221%L241+V0%J251%O219%E241&L&S0vHr7%45321?IvIr8%756214Bp041p0:1p0F1p0Q21p0Q:1pX<Q@1pWFQ@1pW0QB1").
Proof.
intros a j v Ha Hj Hs Hq C. pose proof REPX as (ROK & _).
destruct (art_rok_rcy ROK) as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & G9 & G10 & Kspb & Kend & Atkb & Plo & Phi & Papp & Apt & Apkb & Kb0 & G11 & Apk).
apply (cell_agree M M'); [|clear - Ha; lia|clear - Hj; lia|exact C]. intros x Hx. apply art_rcy_agr. apply art_rcy_out_far.
- clear - Hx Hj G1 HSP. lia.
- clear - Hx Hj G4. lia.
- clear - Hx Hj Plo. lia.
- clear - Hx Ha Hj G9. lia.
- intros p Hp. apply (art_live_off_img p (U x) Hp). clear - Hx Ha Hj. lia.
- clear - Hx Hj. lia.
- clear - Hx Hs. lia.
- clear - Hx Hq. lia.
Qed.
#[using="FSG G LB M bt bg REPX GHOST QT0 LIVE xs XS k ROOM sp HSP INV' TRQ"] Lemma art_rcy_statics : ltac2:(TCodec.tc2 tcn__JbtInvRecycle "4&Q=vT0vI%3221").
Proof.
pose proof REPX as (_ & ST & _). destruct INV' as (_ & _ & PC' & LY' & T' & _).
destruct ST as (PC & LY & T & RO & RZ & DR & TG & CS).
unfold art_rt_statics.
split; [exact PC'|]. split; [exact LY'|]. split; [exact T'|].
split. { unfold art_alloc_rodata in *. destruct RO as (a1 & a2 & a3). repeat split; (apply art_rcy_cell_img; [lia|cbn; lia|cbn; lia|cbn; lia|assumption]). }
split. { unfold art_rz_rodata in *. destruct RZ as (a1 & a2 & a3). repeat split; (apply art_rcy_cell_img; [lia|cbn; lia|cbn; lia|cbn; lia|assumption]). }
split. { destruct DR as (a1 & a2 & a3). unfold DRoD. repeat split; (apply art_rcy_cell_img; [lia|cbn; lia|cbn; lia|cbn; lia|assumption]). }
split. { destruct TG as (GN & T1 & T2). split; [|split].
- intros a Ha. rewrite <- (GN a Ha). apply art_rcy_agr. rewrite art_u_lit by lia.
pose proof REPX as (ROK & _). destruct (art_rok_rcy ROK) as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & G9 & G10 & Kspb & Kend & Atkb & Plo & Phi & Papp & Apt & Apkb & Kb0 & G11 & Apk).
apply art_rcy_out_far; [clear - Ha G1 HSP; lia|clear - Ha G4; lia|clear - Ha Plo; lia|clear - Ha G9; lia|intros p Hp; apply (art_live_off_img p a Hp); clear - Ha; lia|clear - Ha; lia|clear - Ha; lia|clear - Ha; lia].
- apply art_rcy_cell_img; [lia|cbn; lia|cbn; lia|cbn; lia|exact T1].
- apply art_rcy_cell_img; [lia|cbn; lia|cbn; lia|cbn; lia|exact T2]. }
decompose [and] CS. repeat split; (apply art_rcy_cell_img; [lia|cbn; lia|cbn; lia|cbn; lia|assumption]).
Qed.
#[using="LB M bt bg REPX GHOST QT0 LIVE XS ROOM HSP"] Lemma art_rcy_out_obj : ltac2:(TCodec.tc2 tcn__JbtInvRecycle "QO'F&QOr3r2%3221'<&S8r4%2215&S9&S6%1249%3291%8251&Q6&1':%12AA&RIvT1&D&RC&Q7&RA&QLvT0%211%411vT9%948721%<2;1&RL&QM%118&QK%11:&QI%11<&S>+V0%22E1&R2&RB&CvSK%23H1A%411%@7>E<:761(2(9+T@%24QCQC;1(7%11Q4%63Q531%Q83Q681%Q93Q7J1%Q;21QGp0Q=1p0QG1pXBQL1pWNQM1pW0QN1").
Proof.
intros a n x (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7) Hx. unfold apart in *. apply art_rcy_out_far.
- clear - Hx F1 HSP. lia.
- clear - Hx F4. lia.
- clear - Hx F5. lia.
- clear - Hx F3. lia.
- intros p Hp Hin. destruct (LIVE p Hp) as (_ & _ & _ & _ & OB). pose proof (OB (a, n) F7) as A. cbn [fst snd] in A. unfold apart in A. clear - A Hx Hin. lia.
- clear - Hx F6. lia.
- clear - Hx F2. lia.
- clear - Hx F2. lia.
Qed.
#[using="FSG G LB M bt bg REPX GHOST QT0 LIVE xs XS k ROOM sp HSP INV' TRQ"] Lemma art_rcy_thread : ltac2:(TCodec.tc2 tcn__JbtInvRecycle "4&Q>vT0vI%3221").
Proof.
pose proof REPX as (ROK & _ & TH & _). destruct INV' as (_ & _ & _ & _ & _ & _ & _ & WT' & _).
destruct (art_rok_rcy ROK) as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & G9 & G10 & Kspb & Kend & Atkb & Plo & Phi & Papp & Apt & Apkb & Kb0 & G11 & Apk).
destruct (art_rok_far ROK) as (Fctx & _). pose proof Fctx as (Fc0 & Fc1 & _).
destruct TH as (Wt & C1 & C2 & C3 & C4 & C5 & C6 & C7).
assert (TT : forall a (j : nat) v, rn_t rn <= a -> a + Z.of_nat j <= rn_t rn + 208 \/ (rn_t rn + 2904 <= a /\ a + Z.of_nat j <= rn_t rn + 4096) -> cellA M a j v -> cellA M' a j v).
{ intros a j v Ha Hk C. apply (cell_agree M M'); [|clear - Ha G7; lia|clear - Hk G8 G2; lia|exact C]. intros x Hx. apply art_rcy_agr. apply art_rcy_out_thread; clear - Hx Ha Hk; lia. }
unfold art_rt_thread. split; [exact WT'|].
split; [apply TT; [lia|left; cbn; lia|exact C1]|].
split. { apply (cell_agree M M'); [|clear - Fc0; lia|cbn; clear - Fc1 G2; lia|exact C2]. intros x Hx. apply art_rcy_agr. apply (art_rcy_out_obj _ _ _ Fctx). cbn in Hx. clear - Hx. lia. }
split; [apply TT; [lia|left; cbn; lia|exact C3]|]. split; [apply TT; [lia|left; cbn; lia|exact C4]|].
split; [apply TT; [lia|left; cbn; lia|exact C5]|]. split; [apply TT; [lia|right; cbn; lia|exact C6]|].
destruct ROK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hloff & Hloff' & Hloff'' & Htpd & _).
apply art_rcy_cell_img; [exact Hloff'|cbn; exact Hloff''|right; clear - Htpd Hloff; lia|right; clear - Htpd Hloff; lia|exact C7].
Qed.
#[using="LB M bt bg REPX GHOST QT0 LIVE xs XS k ROOM sp HSP TRQ"] Lemma art_rcy_depot : art_rt_depot FSG rn G M'.
Proof.
pose proof REPX as (ROK & _ & _ & _ & _ & _ & _ & DEP & _). unfold art_rt_depot in *.
destruct (art_rok_far ROK) as (_ & Fl2 & Fblk & _).
destruct (art_rok_rcy ROK) as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & G9 & G10 & Kspb & Kend & Atkb & Plo & Phi & Papp & Apt & Apkb & Kb0 & G11 & Apk).
apply (DInvD_frame (rn_l2 rn) (rn_blk rn) _ M M' DEP). intros x Dx. apply art_rcy_agr. destruct Dx as [D|[D|D]].
- apply art_rcy_out_far; [clear - D G1 HSP; lia|clear - D G4; lia|clear - D Plo; lia|clear - D G9; lia|intros p Hp; apply (art_live_off_img p _ Hp); clear - D; lia|clear - D; lia|clear - D; lia|clear - D; lia].
- apply (art_rcy_out_obj _ _ _ Fl2). exact D.
- apply (art_rcy_out_obj _ _ _ Fblk). exact D.
Qed.
#[using="rn LB M bt bg REPX GHOST QT0 LIVE xs XS k ROOM sp HSP TRQ"] Lemma art_rcy_ia_cells : cellA M' 0x1cc4c8 4 (if g_ia FSG G then 1 else 0) /\ (g_ia FSG G = true -> forall j, 0 <= j < 2 ^ 15 -> cellA M' (0x13dc40 + 8 + 8 * j) 8 0).
Proof.
pose proof REPX as (_ & _ & _ & _ & _ & _ & _ & _ & (IA1 & IA2 & IA3) & _).
split; [apply art_rcy_cell_img; [lia|cbn; lia|cbn; lia|cbn; lia|exact IA1]|].
intros E j Hj. apply art_rcy_cell_img; [lia|cbn; lia|cbn; lia|cbn; lia|exact (IA2 E j Hj)].
Qed.
#[using="LB M bt bg REPX XS"] Lemma art_work_zapart : forall a n, apart a n spb (2 ^ 37) -> (forall p, In p (art_live (g_log FSG G)) -> apart (fst p) (snd p) a n) -> forall e, In e work -> art_zapart spb e a n.
Proof.
intros a n Ak Al e He. pose proof (art_pre_geo e (proj1 (art_work_ok e (art_work_pre_in e He)))) as GE. unfold art_zapart, apart in *.
destruct e as [c w d b1 n0|mb ms m b1 n0|wb]; cbn [art_rel_zone art_el_geo fst snd] in *.
- destruct GE as (Hc & Hw & Hu & _). destruct (art_class_size_facts c Hc) as (S1 & _). clear - Ak Hc Hw Hu S1. lia.
- exact (Al _ GE).
- destruct GE as (Hw & Hu & _). rewrite art_class_size_24 in Hu. clear - Ak Hw Hu. lia.
Qed.
#[using="FSG G sp TRQ"] Lemma art_rcy_wr : ltac2:(TCodec.tc2 tcn__JbtInvRecycle "Q?'F&S8zr2%3221&S9&S6r3%2215&S=+2+R0%3221%8251'R;&S2r1&RB&C&RCvSKvT9%43321%611%93:81&RO&QLvT0%211r6r5%643L21p081pW:C1&M&S0vHr4%443281vI%6451;:p031p091p0N1p0Q81pWNQ=1pW0Q>1").
Proof. intros a n Ha Hn Z W. destruct TRQ as (_ & WR & _). apply WR; [exact Ha|exact Hn|right; apply Forall_forall; exact Z|exact W]. Qed.
Section SE.
Local Abbreviation SEC_T_art_rcy_zone_keep := (forall zlo zlen, 0 < zlen -> art_rcy_prot spb art_gr zlo zlen -> (forall e, In e work -> art_zapart spb e zlo zlen) ->
(forall b, In b (g_qg FSG G) -> apart zlo zlen (bt_addr b) 8) ->
forall a (j : nat) v, zlo <= a -> a + Z.of_nat j <= zlo + zlen -> cellA M a j v -> cellA M' a j v) (only parsing).
Variable zlo : ltac:(sec_ty2 constr:(SEC_T_art_rcy_zone_keep) 0%nat 0%nat).
Variable zlen : ltac:(sec_ty2 constr:(SEC_T_art_rcy_zone_keep) 1%nat 0%nat).
Lemma art_rcy_zone_keep : ltac:(sec_stmt2 constr:(SEC_T_art_rcy_zone_keep) 2%nat 0%nat).
Proof using LB bt bg REPX LIVE XS sp TRQ zlo zlen.
intros Hz Pz Zw Zl a j v Ha Hj C.
destruct TRQ as (_ & _ & PT & _). pose proof REPX as (ROK & _).
destruct (art_rok_rcy ROK) as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & G9 & G10 & Kspb & Kend & Atkb & Plo & Phi & Papp & Apt & Apkb & Kb0 & G11 & Apk).
assert (RNG : 0x693000 <= zlo /\ zlo + zlen <= rn_HI rn).
{ destruct Pz as [(c' & Hc' & P1 & P2)|(b & Hb & P1 & P2)]; [clear - Hc' P1 P2 G4 G6 Eris; lia|].
cbn [art_gr rg_bl] in Hb. apply in_map_iff in Hb. destruct Hb as (s0 & <- & Hs0). destruct (art_sec_entry_facts s0 Hs0) as (P3 & _ & P0). destruct (LIVE _ P3) as (L0 & L1 & L2 & _).
cbn [art_sec_b fst snd] in *. clear - P1 P2 L2 P0. lia. }
destruct (PT zlo zlen Hz ltac:(exact (proj2 RNG)) Pz ltac:(apply Forall_forall; exact Zw)) as (_ & CT).
- apply Forall_forall. intros qb Hqb. apply in_map_iff in Hqb. destruct Hqb as (x & <- & Hx). destruct (art_forall2_in_r _ _ _ _ _ x XS Hx) as (b & Hb & Hbx).
rewrite (art_batch_ok_q b x Hbx). cbn [art_qb qb_addr fst]. exact (Zl b Hb).
- right. clear - RNG. lia.
- apply (CT a j v Ha Hj); [clear - Ha RNG; lia|clear - Hj RNG G2; lia|exact C].
Qed.
End SE.
#[using="LB M bt bg REPX GHOST QT0 LIVE XS ROOM HSP"] Lemma art_rcy_zone_shadow : ltac2:(TCodec.tc2 tcn__JbtInvRecycle "RI'F&S8zr3%3221&S6r4%2214&S=+2+Q?%3221%;251'R;&S2r1&RB&C&RCvSKvT9%43321%611%93:81&RO&QLvT0%211r2r7r6%744321p091pW:D1'<&R9&S7+8%2281%Q2241%Q721Q2&S9r5%Q62=1%8217%Q82:1%52Q81%=271&Q6&1':%12QCQC&RIvT1&D&Q7&RA%11N%44Q831Q6%7261&RL&QM%11Q4&QK%11Q6&QI%11Q8&S>+V0%22@1&R2%;79Q<7521QA(2(9+T@%24R;R;61(7%11J%63K31%N3L81%O3ME1%Q121Q7p0Q31p0QB1p0R81p0RA1pXBRF1pXLRG1pXNRH1").
Proof.
intros zlo zlen x Hz0 Hz47 Zw Hx. unfold JbtPoison.SB in Hx.
assert (0 <= zlo / 8) by (apply Z.div_pos; lia). assert ((zlo + zlen) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
apply art_rcy_out_shadow; [lia|]. intros e He Hin. pose proof (art_work_shw_zone e x He Hin) as Zs. pose proof (Zw e He) as Ap. unfold art_zapart, apart, JbtPoison.SB in *.
destruct Ap as [Ap|Ap].
- pose proof (Z.div_le_mono _ _ 8 ltac:(lia) Ap). lia.
- pose proof (Z.div_le_mono _ _ 8 ltac:(lia) Ap). lia.
Qed.
Definition art_gs_rcy : art_gs FSG :=
GS FSG (g_log FSG G ++ art_rels_events work) (g_inited FSG G) (rg_cls (art_rel_steps work art_gr)) (art_st_rcy work (g_st FSG G))
(art_sec_rcy work (g_sec FSG G)) (g_sec_committed FSG G) [] (skipn k (g_qg FSG G)) (g_depot FSG G) (g_ia FSG G) (g_fs FSG G).
#[using="rn LB M bt bg REPX NEg"] Lemma art_entry_inited : g_inited FSG G = true.
Proof.
pose proof REPX as (_ & _ & _ & (_ & PRIM & _) & _ & _ & QR & _).
assert (EXb : exists b0, In b0 (g_qg FSG G)) by (clear - NEg; destruct (g_qg FSG G) as [|b0 r0]; [contradiction|exists b0; left; reflexivity]).
destruct EXb as (b0 & Hb0). destruct QR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & BCH). destruct (BCH b0 ltac:(apply in_or_app; right; exact Hb0)) as (w' & _ & (Hw0' & Hwau & _) & _).
rewrite art_class_size_24 in Hwau. destruct (PRIM 24 ltac:(lia)) as (_ & _ & _ & _ & I2). apply I2. clear - Hw0' Hwau. lia.
Qed.
#[using="LB bt bg REPX XS"] Lemma art_work_key_el : ltac2:(TCodec.tc2 tcn__JbtInvRecycle "Q6'F&S2':%1233(9r2r1%347721&D'R;&R5&RB&C&RCvSKvT9%43321%611%:49?81%B3@<1'>'<%E3=@5'=%>1Br4r3%G4KK21%53I41&R4%11H%:231%;2:1qW:H1%>2I1p0@1pX>Q41pW8Q51").
Proof. intros c w H. apply in_map_iff in H. destruct H as (e & E & He). exists e. split; [exact He|]. split; [exact E|exact (art_work_ok e (art_work_pre_in e He))]. Qed.
#[using="rn LB M bt bg REPX XS"] Lemma art_work_key_st : forall c w, 1 <= c -> In (c, w) (map art_rel_key work) ->
1 <= c <= 30 /\ art_cptr_ok (AsanTab.class_size c) (cl_au (g_cls FSG G c)) w /\ ((exists u n, g_st FSG G c w = CQuar u n) \/ (c = 24 /\ g_st FSG G c w = CBatch)).
Proof.
intros c w Hc H. destruct (art_work_key_el c w H) as (e & He & E & (PRE & _ & GH)).
destruct e as [c0 w0 d b1 n|mb ms m b1 n|wb]; cbn [art_rel_key art_rel_pre art_gr rg_cls] in *; injection E as <- <-.
- destruct PRE as (Hc0 & OKw & _). split; [exact Hc0|]. split; [exact OKw|]. left. eexists. eexists. exact GH.
- exfalso. lia.
- destruct PRE as (OKw & _). split; [lia|]. split; [rewrite art_class_size_24; exact OKw|]. right. split; [reflexivity|exact GH].
Qed.
#[using="rn LB M bt bg REPX XS"] Lemma art_work_mb_sec : forall mb, In (Some mb) (map art_rel_mb work) -> exists s, In s (g_sec FSG G) /\ sc_map s = mb /\ sc_quar s = true.
Proof.
intros mb H. apply in_map_iff in H. destruct H as (e & E & He). destruct (art_work_ok e (art_work_pre_in e He)) as (_ & _ & GH).
destruct e as [c0 w0 d b1 n|mb0 ms m b1 n|wb]; cbn [art_rel_mb] in E; try discriminate E. injection E as ->.
destruct GH as (s & Hs & Hq & _ & _ & Emb & _). exists s. split; [exact Hs|]. split; [symmetry; exact Emb|exact Hq].
Qed.
#[using="rn LB M bt bg REPX"] Lemma art_sec_maps_nodup : List.NoDup (map sc_map (g_sec FSG G)).
Proof.
apply NoDup_nth_error. intros i j Hi E. rewrite !nth_error_map in E. rewrite length_map in Hi.
destruct (nth_error (g_sec FSG G) i) as [s|] eqn:Ei; [|apply nth_error_None in Ei; lia]. destruct (nth_error (g_sec FSG G) j) as [s'|] eqn:Ej; [|discriminate E].
cbn in E. injection E as E. exact (art_sec_idx_inj i j s s' Ei Ej E).
Qed.
#[using="LB M bt bg REPX NEg INV'"] Lemma art_rcy_primary : art_rt_primary FSG rn art_gs_rcy M'.
Proof.
pose proof REPX as (_ & _ & _ & (_ & PRIM & _) & _). destruct INV' as (ICLS & IPH & _ & _ & _ & _ & _ & _ & IWSH & _).
unfold art_rt_primary. cbn [art_gs_rcy g_inited g_cls]. rewrite art_entry_inited.
split; [exact IPH|]. split; [|exact IWSH].
intros c Hc. destruct (ICLS c Hc) as (RC & OK & _). destruct (PRIM c Hc) as (_ & _ & _ & (km & Ekm) & _). destruct (art_steps_au work art_gr c) as (_ & Emu & _).
split; [exact RC|]. split; [exact OK|]. split; [intros _; reflexivity|]. split; [exists km; rewrite Emu; exact Ekm|intros _; reflexivity].
Qed.
#[using="M bt bg REPX QT0 LIVE XS"] Lemma art_rcy_blocks : art_rt_blocks FSG rn art_gs_rcy LB.
Proof.
pose proof REPX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & BLK & _). unfold art_rt_blocks in *. cbn [art_gs_rcy g_cls g_st g_sec].
intros b Hb. destruct (BLK b Hb) as [(c & w & Hc & OKw & Est)|(s & Hs & Hq & Eu & En)].
- left. exists c, w. split; [exact Hc|]. destruct (art_steps_au work art_gr c) as (Eau & _). rewrite Eau. split; [exact OKw|].
unfold art_st_rcy. destruct (art_key_in work c w) eqn:EK; [|exact Est]. exfalso. apply art_key_in_spec in EK.
destruct (art_work_key_st c w ltac:(lia) EK) as (_ & _ & [(u & n & X)|(_ & X)]); rewrite X in Est; discriminate Est.
- right. exists s. split; [|split; [exact Hq|split; assumption]].
apply art_sec_rcy_keep; [exact Hs| |intros mb Hmb; destruct (art_work_mb_sec mb Hmb) as (s' & Hs' & E' & _); rewrite <- E'; apply in_map; exact Hs'|exact art_work_pre_nodup|exact art_sec_maps_nodup].
intros X. destruct (art_work_mb_sec _ X) as (s' & Hs' & E' & Hq'). rewrite (art_sec_map_inj s' s Hs' Hs E') in Hq'. rewrite Hq in Hq'. discriminate Hq'.
Qed.
#[using="XS"] Lemma art_pre_batch_work : forall b, In b (firstn k (g_qg FSG G)) -> exists x, In x (firstn k xs) /\ art_batch_ok b x /\ In (REB (rb_wb x)) work.
Proof.
intros b Hb. destruct (art_forall2_in_l _ _ _ _ _ b (art_forall2_firstn _ _ _ k _ _ XS) Hb) as (x & Hx & Hbx). exists x. split; [exact Hx|]. split; [exact Hbx|].
unfold art_rb_work. apply in_flat_map. exists x. split; [exact Hx|]. unfold art_rb_work1. apply in_or_app. right. left. reflexivity.
Qed.
#[using="XS"] Lemma art_pre_item_work : forall b it, In b (firstn k (g_qg FSG G)) -> In it (bt_items b) -> exists e, In e work /\ art_item_ok it e.
Proof.
intros b it Hb Hit. destruct (art_forall2_in_l _ _ _ _ _ b (art_forall2_firstn _ _ _ k _ _ XS) Hb) as (x & Hx & (_ & _ & _ & F2 & _)).
destruct (art_forall2_in_l _ _ _ _ _ it F2 Hit) as (e & He & Hie). exists e. split; [|exact Hie].
unfold art_rb_work. apply in_flat_map. exists x. split; [exact Hx|]. unfold art_rb_work1. apply in_or_app. left. exact He.
Qed.
#[using="LB M bt bg REPX LIVE LIVE2 XS"] Lemma art_sec_keep_zapart : forall s, In s (g_sec FSG G) -> ~ In (Some (sc_map s)) (map art_rel_mb work) -> forall e, In e work -> art_zapart spb e (sc_map s) (sc_msize s).
Proof.
intros s Hs NI e He. destruct (art_sec_entry_facts s Hs) as (P2 & _). pose proof (art_pre_geo e (proj1 (art_work_ok e (art_work_pre_in e He)))) as GE.
destruct (LIVE _ P2) as (_ & _ & _ & _ & OB). pose proof (OB (rn_kbase rn, 0x2000011000) ltac:(cbn; tauto)) as A. cbn [fst snd] in A.
pose proof REPX as (ROK & _). destruct (art_rok_rcy ROK) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Kspb & _).
unfold art_zapart. destruct e as [c w d b1 n0|mb ms m b1 n0|wb]; cbn [art_rel_zone art_el_geo fst snd] in *.
- destruct GE as (Hc & Hw & Hu & _). destruct (art_class_size_facts c Hc) as (S1 & _). unfold apart in *. clear - A Hc Hw Hu S1 Kspb. lia.
- apply (LIVE2 (mb, ms) (sc_map s, sc_msize s) GE P2). cbn [fst]. intros E. apply NI. apply in_map_iff. exists (RES mb ms m b1 n0). split; [cbn [art_rel_mb]; rewrite E; reflexivity|exact He].
- destruct GE as (Hw & Hu & _). rewrite art_class_size_24 in Hu. unfold apart in *. clear - A Hw Hu Kspb. lia.
Qed.
#[using="M bt bg REPX GHOST QT0 LIVE LIVE2 LIVE3 XS ROOM sp HSP INV' TRQ"] Lemma art_rcy_sec : art_rt_sec FSG rn art_gs_rcy LB M'.
Proof.
pose proof REPX as (ROK & _ & _ & _ & _ & SECR & _). destruct INV' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & ISC & _).
destruct (art_rok_rcy ROK) as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & G9 & G10 & Kspb & Kend & Atkb & Plo & Phi & Papp & Apt & Apkb & Kb0 & G11 & Apk).
destruct SECR as (S0 & S8 & S56 & S48 & S616 & S16 & SNE & SCW & PER & SLV & SLEN).
assert (EBL : rg_bl (art_rel_steps work art_gr) = map art_sec_b (art_sec_rcy work (g_sec FSG G))) by (unfold art_gr; apply art_sec_rcy_b).
rewrite EBL in ISC. destruct ISC as (I0 & I8 & I56 & I616 & IW & IPER). rewrite length_map in I56.
assert (KEEP : forall s, In s (art_sec_rcy work (g_sec FSG G)) -> In s (g_sec FSG G) /\ ~ In (Some (sc_map s)) (map art_rel_mb work)).
{ intros s Hs'. split; [exact (art_sec_rcy_in _ _ _ Hs')|]. intros X. destruct (art_work_mb_sec _ X) as (s0 & Hs0 & E0 & _).
apply (art_sec_rcy_notin work (g_sec FSG G) s (sc_map s) art_sec_maps_nodup Hs' X); [rewrite <- E0; apply in_map; exact Hs0|reflexivity]. }
unfold art_rt_sec. cbn [art_gs_rcy g_sec g_sec_committed g_log g_qt g_qg app].
split; [exact I0|]. split; [exact I8|]. split; [exact I56|].
split; [apply art_rcy_cell_img; [lia|cbn; lia|left; cbn; lia|left; cbn; lia|exact S48]|]. split; [exact I616|].
split; [apply art_rcy_cell_img; [lia|cbn; lia|left; cbn; lia|left; cbn; lia|exact S16]|].
split. { intros NE. apply SNE. intros E. apply NE. rewrite E. pose proof (art_sec_rcy_len work []) as L. destruct (art_sec_rcy work []); [reflexivity|cbn [length] in L; lia]. }
split. { intros C. apply art_rcy_wr; [clear - Plo; lia|clear - Phi G2; lia| |exact (SCW C)].
apply art_work_zapart; [unfold apart in *; clear - Apk; lia|]. intros p Hp. destruct (LIVE p Hp) as (_ & _ & _ & _ & OB).
pose proof (OB (rn_parr rn, 2 ^ 23) ltac:(cbn; tauto)) as A. cbn [fst snd] in A. unfold apart in *. clear - A. lia. }
split.
{ intros i s Hi. pose proof (nth_error_In _ _ Hi) as Hs'. destruct (KEEP s Hs') as (Hs & NI). destruct (In_nth_error _ _ Hs) as (i0 & Hi0).
destruct (PER i0 s Hi0) as (_ & P2 & _ & _ & _ & _ & Lo & Hi2 & Q & P0).
destruct (IPER i (art_sec_b s) ltac:(rewrite nth_error_map, Hi; reflexivity)) as (J1 & J2 & J3 & J4 & J5 & _). cbn [art_sec_b fst snd] in J1, J2, J3, J4, J5.
assert (Hn : 1 <= sc_n s) by (destruct (sc_quar s); [destruct Q as ((b1 & _ & _ & _ & _ & Hn) & _)|destruct Q as (_ & (b1 & _ & _ & _ & _ & Hn) & _)]; clear - Hn; lia).
destruct (LIVE _ P2) as (L0 & L1 & L2 & L3 & _). cbn [fst snd] in L0, L1, L2, L3.
assert (ZK : forall a (j : nat) v, sc_u s - 16 <= a -> a + Z.of_nat j <= sc_u s - 16 + 8 -> cellA M a j v -> cellA M' a j v).
{ apply (art_rcy_zone_keep (sc_u s - 16) 8 ltac:(lia)).
- right. exists (art_sec_b s). split; [cbn [art_gr rg_bl]; apply in_map; exact Hs|]. cbn [art_sec_b fst snd]. clear - Lo Hi2 Hn. lia.
- intros e He. pose proof (art_sec_keep_zapart s Hs NI e He) as Z. unfold art_zapart, apart in *. clear - Z Lo Hi2 Hn. lia.
- intros b Hb. destruct (art_rec_geo b Hb) as (w & Ew & Hw0 & Hwu & _). destruct (LIVE _ P2) as (_ & _ & _ & _ & OB).
pose proof (OB (rn_kbase rn, 0x2000011000) ltac:(cbn; tauto)) as A. cbn [fst snd] in A. unfold apart in *. clear - A Ew Hw0 Hwu Kspb Lo Hi2 Hn. lia. }
assert (HDR : forall st, art_chunk_hdr M (sc_u s) (sc_n s) st -> art_chunk_hdr M' (sc_u s) (sc_n s) st).
{ intros st (b1 & Hb1 & Hty & Chw & Cn & Hn'). exists b1. split; [exact Hb1|]. split; [exact Hty|].
split; [apply ZK; [clear; lia|cbn; clear; lia|exact Chw]|]. split; [apply ZK; [clear; lia|cbn; clear; lia|exact Cn]|exact Hn']. }
split; [exact J1|]. split. { apply art_live_rcy. split; [exact P2|exact NI]. }
split; [exact J5|]. split; [exact J2|]. split; [exact J3|]. split; [exact J4|]. split; [exact Lo|]. split; [exact Hi2|]. split; [|exact P0].
destruct (sc_quar s) eqn:Eq.
- destruct Q as (Q1 & (b & Hb & Hit)). split; [exact (HDR 3 Q1)|]. exists b. split; [|exact Hit].
rewrite QT0 in Hb. cbn [app] in Hb. rewrite <- (firstn_skipn k (g_qg FSG G)) in Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [|exact Hb]. exfalso.
destruct (art_pre_item_work b _ Hb Hit) as (e & He & (_ & Ea & PRE & _ & GH)). cbn [fst snd] in *.
destruct e as [c w d b1 n0|mb ms m b1 n0|wb]; [| |destruct GH].
+ pose proof (art_pre_geo _ PRE) as (Hc & Hw & Hu & _). cbn [art_rel_addr art_rel_pre] in Ea, PRE. destruct PRE as (_ & _ & _ & Hd & _ & Hdsz & _ & Hn0). destruct (art_class_size_facts c Hc) as (S1 & _).
assert (Hr0 : 0 <= (n0 + 7) / 8 * 8) by (assert (0 <= (n0 + 7) / 8) by (apply Z.div_pos; lia); lia).
destruct (LIVE _ P2) as (_ & _ & _ & _ & OB). pose proof (OB (rn_kbase rn, 0x2000011000) ltac:(cbn; tauto)) as A. cbn [fst snd] in A. unfold apart in A.
clear - A Ea Hc Hw Hu Hd Hdsz Hr0 S1 Kspb Lo Hi2 Hn. lia.
+ destruct GH as (_ & s1 & Hs1 & _ & Eu1 & _ & Emb & _). apply NI. apply in_map_iff. exists (RES mb ms m b1 n0). split; [|exact He]. cbn [art_rel_mb]. f_equal.
destruct (Z.eq_dec (sc_map s1) (sc_map s)) as [E|NE]; [rewrite Emb; exact E|exfalso].
destruct (art_sec_entry_facts s1 Hs1) as (P21 & _). pose proof (LIVE2 _ _ P21 P2 NE) as Ap. cbn [fst snd] in Ap.
destruct (In_nth_error _ _ Hs1) as (i1 & Hi1). destruct (PER i1 s1 Hi1) as (_ & _ & _ & _ & _ & _ & Lo1 & Hi1' & Q1' & _).
assert (Hn1 : 1 <= sc_n s1) by (destruct (sc_quar s1); [destruct Q1' as ((b1' & _ & _ & _ & _ & X) & _)|destruct Q1' as (_ & (b1' & _ & _ & _ & _ & X) & _)]; clear - X; lia).
unfold apart in Ap. clear - Ap Eu1 Lo1 Hi1' Hn1 Lo Hi2 Hn. lia.
- destruct Q as (Q1 & Q2 & Q3). split; [exact Q1|]. split; [exact (HDR 2 Q2)|].
assert (TBY : forall j, 0 <= j -> (j < sc_n s / 8 \/ (j = sc_n s / 8 /\ sc_n s mod 8 <> 0)) -> forall v, byte_at M (HeapIfaceA.S (sc_u s) + j) v -> byte_at M' (HeapIfaceA.S (sc_u s) + j) v).
{ intros j Hj0 Hj v Bt. apply (art_byte_at_eq M M'); [|exact Bt]. apply art_rcy_agr.
pose proof (art_S_blk_hi (sc_u s) (sc_n s) j ltac:(lia) Hj) as B1. unfold HeapIfaceA.S, HeapIfaceA.SB in *.
assert (B0 : sc_map s / 8 <= sc_u s / 8) by (apply Z.div_le_mono; clear - Lo; lia).
assert (B2 : (sc_u s + sc_n s - 1) / 8 < (sc_map s + sc_msize s) / 8).
{ destruct (LIVE3 _ P2) as (A1 & A2). cbn [fst snd] in A1, A2. pose proof (Z.div_mod (sc_map s) 4096 ltac:(lia)) as D1. rewrite A1 in D1. pose proof (Z.div_mod (sc_msize s) 4096 ltac:(lia)) as D2. rewrite A2 in D2.
replace (sc_map s + sc_msize s) with ((512 * (sc_map s / 4096) + 512 * (sc_msize s / 4096)) * 8) by lia. rewrite Z_div_mult by lia. apply Z.div_lt_upper_bound; [lia|]. clear - Hi2 D1 D2. lia. }
rewrite art_u_lit by (clear - B0 B1 B2 Hj0 L0 L2 G2; assert (0 <= sc_map s / 8) by (apply Z.div_pos; lia); assert ((sc_map s + sc_msize s) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia); lia).
apply (art_rcy_zone_shadow (sc_map s) (sc_msize s)); [clear - L0; lia|clear - L2 G2; lia|exact (art_sec_keep_zapart s Hs NI)|]. unfold JbtPoison.SB. clear - B0 B1 B2 Hj0. lia. }
exact (shadow_blkR_tby M M' (sc_u s) (sc_n s) ltac:(lia) TBY Q3). }
split.
{ intros p Hp. apply art_live_rcy in Hp. destruct Hp as (Hp & NI). destruct (SLV p Hp) as (s & Hs & ->). exists s. split; [|reflexivity].
apply art_sec_rcy_keep; [exact Hs|exact NI|intros mb Hmb; destruct (art_work_mb_sec mb Hmb) as (s' & Hs' & E' & _); rewrite <- E'; apply in_map; exact Hs'|exact art_work_pre_nodup|exact art_sec_maps_nodup]. }
pose proof (art_sec_rcy_len work (g_sec FSG G)) as L. clear - L SLEN. lia.
Qed.
#[using="FSG G LB bt bg REPX GHOST QT0 LIVE XS ROOM sp HSP TRQ"] Lemma art_rcy_sh_range : ltac2:(TCodec.tc2 tcn__JbtInvRecycle "R5'F&S8zr3%3221&S6r4%2214&S=+2+Q?%3221%;251'R;&S2r1&RB&C&RCvSKvT9%43321%611%93:81&RO&QLvT0%211r2r7r6%744321p091pW:D1'<&R9&S7+8%2281%Q2241%Q721Q2&S9r5%Q62=1%8217%Q82:1%52Q81%=271'='8'T3y8%211%411vI&T2yR0%221?%411vH%113%=3831p0?1p0N1p0QD1p0QM1pXBR21pXLR31pXNR41").
Proof.
intros zlo zlen x Hz0 Hz47 Zw Hx. apply art_rcy_agr. unfold JbtPoison.SB in Hx.
assert (0 <= zlo / 8) by (apply Z.div_pos; lia). assert ((zlo + zlen) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
rewrite art_u_lit by lia. apply (art_rcy_zone_shadow zlo zlen x Hz0 Hz47 Zw). exact Hx.
Qed.
#[using="FSG G LB bt bg REPX GHOST QT0 LIVE XS ROOM sp HSP TRQ"] Lemma art_rcy_sh_byte : ltac2:(TCodec.tc2 tcn__JbtInvRecycle "R2'F&S8zr4%3221&S6r5%2214&S=+2+Q?%3221%;251'=&S:r6%;21:+8%4221%63C1A'R;&S2r1&RB&C&RCvSKvT9%43321%611%93:81&RO&QLvT0%211r2r9r8%744321p091pW:D1'<%Q925K&S9r7%Q8281%32O1%6251&Q2vH&O%117%4331Q5vI%41A%7321;p041p0:1p0B1p0Q81p0Q@1p0QI1pX<QN1pXHQO1pXLR01pXNR11").
Proof.
intros zlo zlen y v Hz0 Hz47 H8 Zw Hy Bt. apply (art_byte_at_eq M M'); [|exact Bt]. apply (art_rcy_sh_range zlo zlen _ Hz0 Hz47 Zw).
unfold HeapIfaceA.S, HeapIfaceA.SB, JbtPoison.SB. pose proof (Z.div_mod (zlo + zlen) 8 ltac:(lia)) as D. rewrite H8 in D.
assert (zlo / 8 <= y / 8) by (apply Z.div_le_mono; lia). assert (y / 8 < (zlo + zlen) / 8) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.
#[using="FSG G LB bt bg REPX GHOST QT0 LIVE XS ROOM sp HSP TRQ"] Lemma art_rcy_shadow_blk : ltac2:(TCodec.tc2 tcn__JbtInvRecycle "R2'F&S8zr4%3221&S6r5%2214&S=+2+Q?%3221%;251'=&S:r6%;21:+8%4221%63C1A'R;&S2r1&RB&C&RCvSKvT9%43321%611%93:81&RO&QLvT0%211r2r9r8%744321p091pW:D1%Q824J&S9%12Q9Lr7%Q8281r:%Q:21;%Q?231&Q4vH%231?>vI%4317Ap031p071p0=1p0@1p0B1p0Q81p0Q@1p0QI1pWNQN1pX:QO1pXLR01pXNR11").
Proof.
intros zlo zlen u n Hz0 Hz47 H8 Zw Hu Hn Hun SB0.
assert (TBY : forall j, 0 <= j -> (j < n / 8 \/ (j = n / 8 /\ n mod 8 <> 0)) -> forall v, byte_at M (HeapIfaceA.S u + j) v -> byte_at M' (HeapIfaceA.S u + j) v).
{ intros j Hj0 Hj v Bt. apply (art_byte_at_eq M M'); [|exact Bt]. apply (art_rcy_sh_range zlo zlen _ Hz0 Hz47 Zw).
pose proof (art_S_blk_hi u n j Hn Hj) as B1. unfold HeapIfaceA.S, HeapIfaceA.SB, JbtPoison.SB in *. pose proof (Z.div_mod (zlo + zlen) 8 ltac:(lia)) as D. rewrite H8 in D.
assert (zlo / 8 <= u / 8) by (apply Z.div_le_mono; lia). assert ((u + n - 1) / 8 < (zlo + zlen) / 8) by (apply Z.div_lt_upper_bound; lia). lia. }
exact (shadow_blkR_tby M M' u n Hn TBY SB0).
Qed.
#[using="rn LB M bt bg REPX"] Lemma art_chunk_geo : forall c w, 1 <= c <= 30 -> art_cptr_ok (AsanTab.class_size c) (cl_au (g_cls FSG G c)) w ->
0 <= w /\ 16 * w + AsanTab.class_size c <= cl_au (g_cls FSG G c) /\ cl_au (g_cls FSG G c) <= cl_mu (g_cls FSG G c) /\ cl_mu (g_cls FSG G c) <= 3758096384
/\ (exists i, 16 * w = AsanTab.class_size c * i).
Proof.
intros c w Hc (Hw0 & Hwau & Hi). pose proof REPX as (_ & _ & _ & (_ & PRIM & _) & _). destruct (PRIM c Hc) as (_ & OK & _). destruct OK as (_ & (_ & Haumu) & _ & _ & _ & Hmu3 & _).
split; [exact Hw0|]. split; [exact Hwau|]. split; [exact Haumu|]. split; [exact Hmu3|exact Hi].
Qed.
#[using="LB M bt bg REPX LIVE LIVE2 XS"] Lemma art_chunk_zapart : forall c w, 1 <= c <= 30 -> art_cptr_ok (AsanTab.class_size c) (cl_au (g_cls FSG G c)) w -> ~ In (c, w) (map art_rel_key work) ->
forall e, In e work -> art_zapart spb e (spb + c * 2 ^ 32 + 16 * w) (AsanTab.class_size c).
Proof.
intros c w Hc OKw NI e He. destruct (art_chunk_geo c w Hc OKw) as (Hw0 & Hwau & Haumu & Hmu3 & Hi).
apply (art_el_zapart e (REP c w 0 0 0) (art_pre_geo e (proj1 (art_work_ok e (art_work_pre_in e He))))).
- cbn [art_el_geo]. split; [exact Hc|]. split; [exact Hw0|]. split; [lia|exact Hi].
- cbn [art_rel_key]. intros E. apply NI. rewrite <- E. apply in_map. exact He.
Qed.
Section SE.
Local Abbreviation SEC_T_art_tail_zapart := (forall c x, 1 <= c <= 30 -> cl_au (g_cls FSG G c) <= x -> x + 8 <= cl_mu (g_cls FSG G c) -> forall e, In e work -> art_zapart spb e (spb + c * 2 ^ 32 + x) 8) (only parsing).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_tail_zapart) 0%nat 0%nat).
Variable x : ltac:(sec_ty2 constr:(SEC_T_art_tail_zapart) 1%nat 0%nat).
Lemma art_tail_zapart : ltac:(sec_stmt2 constr:(SEC_T_art_tail_zapart) 2%nat 0%nat).
Proof using LB M bt bg REPX LIVE XS c x.
intros Hc Hx Hx' e He.
pose proof REPX as (ROK & _ & _ & (_ & PRIM & _) & _). destruct (PRIM c Hc) as (_ & OK & _). destruct OK as (_ & (Hau0 & Haumu) & _ & _ & _ & Hmu3 & _).
destruct (art_work_ok e (art_work_pre_in e He)) as (PRE & _). pose proof (art_pre_geo e PRE) as GE. destruct (art_rok_rcy ROK) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Kspb & _).
unfold art_zapart, apart. destruct e as [c0 w0 d b1 n0|mb ms m b1 n0|wb]; cbn [art_rel_zone art_el_geo art_rel_pre art_gr rg_cls fst snd] in *.
- destruct GE as (Hc0 & Hw & Hu & _). destruct PRE as (_ & (_ & Hwau & _) & _). destruct (art_class_size_facts c0 Hc0) as (S1 & _).
destruct (Z.eq_dec c0 c) as [->|NE]; [clear - Hwau Hx; lia|clear - NE Hc Hc0 Hw Hu S1 Hau0 Hx Hx' Hmu3; lia].
- destruct (LIVE _ GE) as (_ & _ & _ & _ & OB). pose proof (OB (rn_kbase rn, 0x2000011000) ltac:(cbn; tauto)) as A. cbn [fst snd] in A. unfold apart in A. clear - A Hc Hau0 Hx Hx' Hmu3 Kspb. lia.
- destruct GE as (Hw & Hu & _). destruct PRE as ((_ & Hwau & _) & _). rewrite art_class_size_24 in Hu.
destruct (Z.eq_dec 24 c) as [<-|NE]; [clear - Hwau Hx; lia|clear - NE Hc Hw Hu Hau0 Hx Hx' Hmu3; lia].
Qed.
End SE.
#[using="FSG G LB M bt bg REPX XS"] Lemma art_shw_off_zone : ltac2:(TCodec.tc2 tcn__JbtInvRecycle "QF'R;'F&S2r4&RB&C&RCvSKvT9%43321%611%93;81&RO&QLvT0%211r5r3%6432?1'<&S8&3&R8r6%2291%43HH1%6219&S9&S6&;%13MM6%3261%52?1%>271&?&R9&S7+8%22?1%;241%D21Q5%=2BI%6215%?281%A2Q91%J251%<11p0>1p0N1p0Q61pXBQA1pXLQB1pXNQC1pW:QE1").
Proof.
intros e zlo zlen x He Ap Hin Hx. pose proof (art_work_shw_zone e x He Hin) as Zs. unfold art_zapart, apart, JbtPoison.SB in *.
destruct Ap as [Ap|Ap]; pose proof (Z.div_le_mono _ _ 8 ltac:(lia) Ap); lia.
Qed.
#[using="M bt bg REPX GHOST QT0 LIVE LIVE2 XS ROOM sp HSP TRQ"] Lemma art_rcy_chunks : art_rt_chunks FSG rn art_gs_rcy LB M'.
Proof.
pose proof REPX as (ROK & _ & _ & (_ & PRIM & _) & CH & _ & QR & _).
destruct (art_rok_rcy ROK) as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & G9 & G10 & Kspb & Kend & Atkb & Plo & Phi & Papp & Apt & Apkb & Kb0 & G11 & Apk).
unfold art_rt_chunks. cbn [art_gs_rcy g_cls g_st g_qt g_qg app]. intros c Hc. cbv zeta.
destruct (CH c Hc) as (C1 & C2 & C3 & C4). cbv zeta in C1, C2, C3, C4.
destruct (art_steps_au work art_gr c) as (Eau & Emu & _). cbn [art_gr rg_cls] in Eau, Emu. rewrite Eau, Emu.
destruct (PRIM c Hc) as (_ & OK & _). destruct OK as (_ & (Hau0 & Haumu) & _ & (kmu & Ekmu) & _ & Hmu3 & _).
destruct (art_class_size_facts c Hc) as (S1 & S16).
assert (RB8 : forall y, (spb + c * 2 ^ 32 + 8 * y) mod 8 = 0).
{ intros y. rewrite Espb. replace (65536 * rn_qs rn + c * 2 ^ 32 + 8 * y) with ((8192 * rn_qs rn + c * 2 ^ 29 + y) * 8) by lia. apply Z_mod_mult. }
split.
{ intros x Hx Hx8. pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. rewrite Hx8 in Dx.
apply (art_rcy_sh_byte (spb + c * 2 ^ 32 + x) 8 (spb + c * 2 ^ 32 + x) 0xfa); [clear - Hc G4 Hau0 Hx; lia|clear - Hc G6 G2 Eris Hx Hmu3; lia| | |clear; lia|exact (C1 x Hx Hx8)].
- replace (spb + c * 2 ^ 32 + x + 8) with (spb + c * 2 ^ 32 + 8 * (x / 8 + 1)) by lia. apply RB8.
- apply art_tail_zapart; [exact Hc|clear - Hx; lia|clear - Hx Dx Ekmu; lia]. }
split.
{ intros w Hin. apply (art_steps_in work art_gr c w art_rg_ok_gr art_entry_pre Hc) in Hin. unfold art_st_rcy. destruct (art_key_in work c w) eqn:EK; [reflexivity|].
destruct Hin as [Hin|Hin]; [exact (C2 w Hin)|apply art_key_in_spec in Hin; rewrite Hin in EK; discriminate EK]. }
split. { intros w NOK. unfold art_st_rcy. destruct (art_key_in work c w); [reflexivity|exact (C3 w NOK)]. }
intros w OKw. specialize (C4 w OKw). destruct (art_chunk_geo c w Hc OKw) as (Hw0 & Hwau & _ & _ & (iw & Eiw)).
set (cb := spb + c * 2 ^ 32 + 16 * w) in *.
assert (CB0 : 0 <= cb) by (unfold cb; clear - Hc G4 Hw0; lia). assert (CB47 : cb + AsanTab.class_size c <= 2 ^ 47) by (unfold cb; clear - Hc G6 G2 Eris Hwau Haumu Hmu3; lia).
assert (CB8 : (cb + AsanTab.class_size c) mod 8 = 0).
{ pose proof (Z.div_mod (AsanTab.class_size c) 16 ltac:(lia)) as Ds. rewrite S16 in Ds. unfold cb. replace (spb + c * 2 ^ 32 + 16 * w + AsanTab.class_size c) with (spb + c * 2 ^ 32 + 8 * (2 * w + 2 * (AsanTab.class_size c / 16))) by lia. apply RB8. }
unfold art_st_rcy. destruct (art_key_in work c w) eqn:EK.
-
apply art_key_in_spec in EK. split; [apply (art_steps_in work art_gr c w art_rg_ok_gr art_entry_pre Hc); right; exact EK|].
assert (BY : byte_at M (HeapIfaceA.S cb) 0xfa).
{ destruct (art_work_key_st c w ltac:(lia) EK) as (_ & _ & [(u & n & X)|(E24 & X)]); rewrite X in C4.
- destruct C4 as (_ & _ & _ & _ & B & _). exact B.
- destruct C4 as (_ & b & Hb & Eb). destruct GHOST as (_ & _ & T4 & _). rewrite <- Eb. exact (T4 b Hb). }
apply (art_byte_at_eq M M'); [|exact BY]. apply art_rcy_agr.
assert (ES : HeapIfaceA.S cb = JbtPoison.SB + cb / 8) by (unfold HeapIfaceA.S, HeapIfaceA.SB, JbtPoison.SB; lia).
assert (Q0 : 0 <= cb / 8) by (apply Z.div_pos; lia). assert (Q1 : cb / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; clear - CB47 S1; lia).
rewrite art_u_lit by (rewrite ES; unfold JbtPoison.SB; clear - Q0 Q1; lia).
apply art_rcy_out_shadow; [rewrite ES; unfold JbtPoison.SB; clear - Q0 Q1; lia|]. intros e He Hin.
destruct (prod_eq_dec (art_rel_key e) (c, w)) as [EKe|NEK].
+ destruct (art_work_ok e (art_work_pre_in e He)) as (PRE & _).
destruct e as [c0 w0 d b1 n0|mb ms m b1 n0|wb]; cbn [art_rel_key art_rel_shw art_rel_pre fst snd] in *.
* injection EKe as -> ->. destruct PRE as (_ & _ & _ & Hd & _). fold cb in Hin. rewrite ES in Hin.
assert ((cb + 16) / 8 <= (cb + d + 16) / 8) by (apply Z.div_le_mono; clear - Hd; lia).
assert (Ecb : (cb + 16) / 8 = cb / 8 + 2). { replace (cb + 16) with (cb + 2 * 8) by lia. apply Z.div_add. lia. }
clear - Hin H Ecb. lia.
* injection EKe as E _. clear - E Hc. lia.
* clear - Hin. lia.
+ apply (art_shw_off_zone e cb (AsanTab.class_size c) (HeapIfaceA.S cb) He); [|exact Hin|].
* apply (art_el_zapart e (REP c w 0 0 0) (art_pre_geo e (proj1 (art_work_ok e (art_work_pre_in e He))))); [|exact NEK].
cbn [art_el_geo]. split; [exact Hc|]. split; [exact Hw0|]. split; [clear - Hwau Haumu Hmu3; lia|exists iw; exact Eiw].
* rewrite ES. assert (cb / 8 < (cb + AsanTab.class_size c) / 8); [|unfold JbtPoison.SB; lia].
pose proof (Z.div_mod (cb + AsanTab.class_size c) 8 ltac:(lia)) as D. rewrite CB8 in D. apply Z.div_lt_upper_bound; [lia|]. clear - D S1. lia.
-
assert (NI : ~ In (c, w) (map art_rel_key work)) by (intros X; apply art_key_in_spec in X; rewrite X in EK; discriminate EK).
pose proof (art_chunk_zapart c w Hc OKw NI) as ZA. fold cb in ZA.
assert (BYT : forall v, byte_at M (HeapIfaceA.S cb) v -> byte_at M' (HeapIfaceA.S cb) v).
{ intros v B. apply (art_rcy_sh_byte cb (AsanTab.class_size c) cb v CB0 CB47 CB8 ZA); [clear - S1; lia|exact B]. }
assert (ZK : g_st FSG G c w <> CBatch -> forall a (j : nat) v, cb <= a -> a + Z.of_nat j <= cb + AsanTab.class_size c -> cellA M a j v -> cellA M' a j v).
{ intros NB. apply (art_rcy_zone_keep cb (AsanTab.class_size c) ltac:(clear - S1; lia)); [left; exists c; split; [exact Hc|unfold cb; clear - Hw0 Hwau Haumu Hmu3; lia]|exact ZA|].
intros b Hb. destruct (art_rec_geo b Hb) as (wb & Ewb & Hwb0 & Hwbu & Hiwb & _).
destruct QR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & BCH). destruct (BCH b (in_or_app _ _ b (or_intror Hb))) as (wb' & Ewb' & _ & Stb).
assert (wb' = wb) by (clear - Ewb Ewb'; lia). subst wb'.
assert (NEk : (c, w) <> (24, wb)) by (intros E; injection E as -> ->; exact (NB Stb)).
pose proof (art_chunk_apart spb c w 24 wb Hc ltac:(lia) Hw0 ltac:(clear - Hwau Haumu Hmu3; lia) ltac:(exists iw; exact Eiw) Hwb0 ltac:(rewrite art_class_size_24; exact Hwbu)
ltac:(rewrite art_class_size_24; exact Hiwb) NEk) as A. rewrite art_class_size_24 in A. fold cb in A. rewrite Ewb. unfold apart in *. clear - A. lia. }
destruct (g_st FSG G c w) as [|u n|u n|] eqn:Est.
+ destruct C4 as (Hin & B). split; [apply (art_steps_in work art_gr c w art_rg_ok_gr art_entry_pre Hc); left; exact Hin|exact (BYT _ B)].
+ destruct C4 as (InLB & Lo & Hi & (b1 & Hb1 & Hty & Chw & Cn & Hn) & SHB & B & LCH). fold cb in Lo, Hi, LCH.
split; [exact InLB|]. split; [exact Lo|]. split; [exact Hi|].
split. { exists b1. split; [exact Hb1|]. split; [exact Hty|]. split; [apply (ZK ltac:(discriminate)); [clear - Lo; lia|cbn; clear - Hi Hn; lia|exact Chw]|].
split; [apply (ZK ltac:(discriminate)); [clear - Lo; lia|cbn; clear - Hi Hn; lia|exact Cn]|exact Hn]. }
split; [apply (art_rcy_shadow_blk cb (AsanTab.class_size c) u n CB0 CB47 CB8 ZA); [clear - Lo; lia|clear - Hn; lia|exact Hi|exact SHB]|].
split; [exact (BYT _ B)|]. intros NE. destruct (LCH NE) as (L1 & L2).
split; [apply (ZK ltac:(discriminate)); [clear; lia|cbn; clear - S1; lia|exact L1]|apply (ZK ltac:(discriminate)); [clear; lia|cbn; clear - S1; lia|exact L2]].
+ destruct C4 as (Lo & Hi & (b1 & Hb1 & Hty & Chw & Cn & Hn) & (b & Hb & Hit) & B & LCH). fold cb in Lo, Hi, LCH.
split; [exact Lo|]. split; [exact Hi|].
split. { exists b1. split; [exact Hb1|]. split; [exact Hty|]. split; [apply (ZK ltac:(discriminate)); [clear - Lo; lia|cbn; clear - Hi Hn; lia|exact Chw]|].
split; [apply (ZK ltac:(discriminate)); [clear - Lo; lia|cbn; clear - Hi Hn; lia|exact Cn]|exact Hn]. }
split.
{ exists b. split; [|exact Hit]. rewrite QT0 in Hb. cbn [app] in Hb. rewrite <- (firstn_skipn k (g_qg FSG G)) in Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [|exact Hb]. exfalso.
destruct (art_pre_item_work b _ Hb Hit) as (e & He & (_ & Ea & PRE & _ & GH)). cbn [fst snd] in *. pose proof (art_pre_geo _ PRE) as GE.
destruct e as [c0 w0 d0 b10 n0|mb ms m b10 n0|wb]; [| |destruct GH]; cbn [art_rel_addr art_rel_pre art_el_geo] in *.
- destruct GE as (Hc0 & Hw00 & Hu0 & Hi0). destruct PRE as (_ & _ & _ & Hd0 & _ & Hdsz0 & _ & Hn0).
assert (Hr0 : 0 <= (n0 + 7) / 8 * 8) by (assert (0 <= (n0 + 7) / 8) by (apply Z.div_pos; lia); lia).
destruct (prod_eq_dec (c0, w0) (c, w)) as [E|NE]; [injection E as -> ->; apply NI; apply in_map_iff; exists (REP c w d0 b10 n0); split; [reflexivity|exact He]|].
pose proof (art_chunk_apart spb c0 w0 c w Hc0 Hc Hw00 Hu0 Hi0 Hw0 ltac:(clear - Hwau Haumu Hmu3; lia) ltac:(exists iw; exact Eiw) NE) as A. fold cb in A. unfold apart in A.
clear - A Ea Hd0 Hdsz0 Hr0 Lo Hi Hn. lia.
- destruct (LIVE _ GE) as (_ & _ & _ & _ & OB). pose proof (OB (rn_kbase rn, 0x2000011000) ltac:(cbn; tauto)) as A. cbn [fst snd] in A. unfold apart in A.
destruct PRE as (_ & Lo1 & Hi1 & _). unfold cb in Lo, Hi. clear - A Ea Lo1 Hi1 Lo Hi Hn Hc Hw0 Hwau Haumu Hmu3 Kspb S1. lia. }
split; [exact (BYT _ B)|]. intros NE. destruct (LCH NE) as (L1 & L2).
split; [apply (ZK ltac:(discriminate)); [clear; lia|cbn; clear - S1; lia|exact L1]|apply (ZK ltac:(discriminate)); [clear; lia|cbn; clear - S1; lia|exact L2]].
+ destruct C4 as (E24 & b & Hb & Eb). split; [exact E24|]. exists b. split; [|exact Eb].
rewrite QT0 in Hb. cbn [app] in Hb. rewrite <- (firstn_skipn k (g_qg FSG G)) in Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [|exact Hb]. exfalso.
destruct (art_pre_batch_work b Hb) as (x & _ & (Ea & _) & Hreb). apply NI. apply in_map_iff. exists (REB (rb_wb x)). split; [|exact Hreb].
cbn [art_rel_key]. subst c. unfold cb in Eb. f_equal. clear - Ea Eb. lia.
Qed.
Hypothesis C160 : cellA M' (0x1396b0 + 160) 8 (Z.of_nat (length (skipn k xs))).
Hypothesis C168 : cellA M' (0x1396b0 + 168) 8 (art_qhead (map (art_rb_q spb) (skipn k xs))).
Hypothesis C184 : cellA M' (0x1396b0 + 184) 8 (art_qbytes (map (art_rb_q spb) (skipn k xs))).
Hypothesis C176a : skipn k xs = [] -> cellA M' (0x1396b0 + 176) 8 0.
Hypothesis C176b : skipn k xs <> [] -> cellA M' (0x1396b0 + 176) 8 lg.
Hypothesis Clk : cellA M' (0x1396b0 + 152) 4 0.
Hypothesis QL' : art_qlist M' (map (art_rb_q spb) (skipn k xs)) (art_qhead (map (art_rb_q spb) (skipn k xs))) lg.
Hypothesis HREST : art_qbytes (map (art_rb_q spb) (skipn k xs)) <= 0xe666661.
#[using="XS"] Lemma art_work_item_src : forall e, In e work -> art_rel_is_item e -> exists b it, In b (firstn k (g_qg FSG G)) /\ In it (bt_items b) /\ art_item_ok it e.
Proof.
intros e He IT. unfold art_rb_work in He. apply in_flat_map in He. destruct He as (x & Hx & He).
destruct (art_forall2_in_r _ _ _ _ _ x (art_forall2_firstn _ _ _ k _ _ XS) Hx) as (b & Hb & (_ & _ & _ & F2 & _)).
unfold art_rb_work1 in He. apply in_app_or in He. destruct He as [He|[<-|[]]]; [|destruct IT].
destruct (art_forall2_in_r _ _ _ _ _ e F2 He) as (it & Hit & Hok). exists b, it. split; [exact Hb|]. split; [exact Hit|exact Hok].
Qed.
#[using="rn LB M bt bg REPX QT0"] Lemma art_pre_rest_items : forall b it b' it', In b (firstn k (g_qg FSG G)) -> In it (bt_items b) -> In b' (skipn k (g_qg FSG G)) -> In it' (bt_items b') -> fst it <> fst it'.
Proof.
intros b it b' it' Hb Hit Hb' Hit'. pose proof REPX as (_ & _ & _ & _ & _ & _ & QR & _). destruct QR as (_ & _ & _ & _ & _ & _ & _ & _ & NDI & _).
rewrite QT0 in NDI. cbn [app] in NDI. apply NoDup_ListNoDup in NDI. rewrite <- (firstn_skipn k (g_qg FSG G)) in NDI. rewrite flat_map_app in NDI.
apply (art_nodup_app_d _ _ fst _ _ it it' NDI); apply in_flat_map; [exists b|exists b']; split; assumption.
Qed.
#[using="Type"] Lemma art_rest_in : forall b, In b (skipn k (g_qg FSG G)) -> In b (g_qt FSG G ++ g_qg FSG G).
Proof. intros b Hb. apply in_or_app. right. exact (art_in_skipn _ k _ b Hb). Qed.
#[using="LB M bt bg REPX GHOST QT0 LIVE XS ROOM sp lg HSP TRQ C160 C168 C184 C176a C176b Clk QL' HREST"] Lemma art_rcy_quar : art_rt_quar FSG rn art_gs_rcy M'.
Proof.
pose proof REPX as (ROK & _ & _ & (_ & PRIM & _) & CH & SECR & QR & _).
destruct (art_rok_rcy ROK) as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & G9 & G10 & Kspb & Kend & Atkb & Plo & Phi & Papp & Apt & Apkb & Kb0 & G11 & Apk).
destruct QR as ((ft & lt & T80 & T88 & T96 & T104 & BLt) & _ & _ & _ & _ & ND & NEI & ITEMS & NDI & BCH).
pose proof (art_forall2_skipn _ _ _ k _ _ XS) as XR. pose proof (art_batches_ok_q _ _ XR) as EQR.
assert (TT : forall a (j : nat) v, rn_t rn + 80 <= a -> a + Z.of_nat j <= rn_t rn + 112 -> cellA M a j v -> cellA M' a j v).
{ intros a j v Ha Hk C. apply (cell_agree M M'); [|clear - Ha G7; lia|clear - Hk G8 G2; lia|exact C]. intros x Hx. apply art_rcy_agr. apply art_rcy_out_thread; clear - Hx Ha Hk; lia. }
unfold art_rt_quar. cbn [art_gs_rcy g_qt g_qg g_cls g_st g_sec app].
split. { rewrite QT0 in T80, T104, BLt. exists ft, lt. split; [apply TT; [lia|cbn; lia|exact T80]|]. split; [apply TT; [lia|cbn; lia|exact T88]|]. split; [apply TT; [lia|cbn; lia|exact T96]|].
split; [apply TT; [lia|cbn; lia|exact T104]|exact BLt]. }
split.
{ exists (art_qhead (map (art_rb_q spb) (skipn k xs))), (if Nat.eqb (length (skipn k xs)) 0 then 0 else lg).
split; [rewrite <- (Forall2_length XR) in C160; exact C160|]. split; [exact C168|].
split. { destruct (skipn k xs) as [|x0 r0] eqn:Es; cbn [length Nat.eqb]; [apply C176a; reflexivity|apply C176b; discriminate]. }
split; [rewrite art_batches_bytes_q, <- EQR; exact C184|].
apply art_batch_list_q. rewrite <- EQR. destruct (skipn k xs) as [|x0 r0] eqn:Es; cbn [length Nat.eqb]; [cbn [map art_qlist art_qhead]; reflexivity|exact QL']. }
split; [cbn; lia|]. split; [rewrite art_batches_bytes_q, <- EQR; clear - HREST; lia|]. split; [exact Clk|].
rewrite QT0 in ND. cbn [app] in ND. apply NoDup_ListNoDup in ND. rewrite <- (firstn_skipn k (g_qg FSG G)) in ND. pose proof ND as ND'. rewrite map_app in ND'.
split; [apply NoDup_ListNoDup; exact (NoDup_app_remove_l _ _ ND')|].
split; [intros b Hb; exact (NEI b (art_rest_in b Hb))|].
split.
{ intros b it Hb Hit. destruct (ITEMS b it (art_rest_in b Hb) Hit) as [(c & w & Hc & OKw & Est)|(s & Hs & Hq & Eu & En)].
- left. exists c, w. split; [exact Hc|]. destruct (art_steps_au work art_gr c) as (Eau & _). rewrite Eau. split; [exact OKw|].
unfold art_st_rcy. destruct (art_key_in work c w) eqn:EK; [|exact Est]. exfalso. apply art_key_in_spec in EK.
destruct (art_work_key_el c w EK) as (e & He & EKe & (_ & _ & GH)).
destruct e as [c0 w0 d b1 n0|mb ms m b1 n0|wb]; cbn [art_rel_key] in EKe; injection EKe as <- <-.
+ destruct (art_work_item_src _ He I) as (b' & it' & Hb' & Hit' & (_ & Ea' & _)). rewrite Est in GH. injection GH as E1 _.
apply (art_pre_rest_items b' it' b it Hb' Hit' Hb Hit). cbn [art_rel_addr] in Ea', E1. rewrite <- Ea'. clear - E1. lia.
+ clear - Hc. lia.
+ rewrite Est in GH. discriminate GH.
- right. exists s. split; [|split; [exact Hq|split; assumption]].
apply art_sec_rcy_keep; [exact Hs| |intros mb Hmb; destruct (art_work_mb_sec mb Hmb) as (s' & Hs' & E' & _); rewrite <- E'; apply in_map; exact Hs'|exact art_work_pre_nodup|exact art_sec_maps_nodup].
intros X. apply in_map_iff in X. destruct X as (e & Ee & He). destruct e as [c0 w0 d b1 n0|mb ms m b1 n0|wb]; cbn [art_rel_mb] in Ee; try discriminate Ee. injection Ee as Emb.
destruct (art_work_item_src _ He I) as (b' & it' & Hb' & Hit' & (_ & Ea' & _ & _ & (_ & s1 & Hs1 & _ & Eu1 & _ & Emb1 & _))). cbn [art_rel_addr] in Ea'.
assert (s1 = s) by (apply (art_sec_map_inj s1 s Hs1 Hs); rewrite <- Emb1; exact Emb). subst s1.
apply (art_pre_rest_items b' it' b it Hb' Hit' Hb Hit). clear - Eu Eu1. lia. }
rewrite flat_map_app, map_app in NDI. cbn [app] in NDI. rewrite QT0 in NDI. cbn [flat_map map app] in NDI. apply NoDup_ListNoDup in NDI.
rewrite <- (firstn_skipn k (g_qg FSG G)), flat_map_app, map_app in NDI.
split; [apply NoDup_ListNoDup; exact (NoDup_app_remove_l _ _ NDI)|].
intros b Hb. destruct (BCH b (art_rest_in b Hb)) as (w & Ew & OKw & Est). exists w. split; [exact Ew|].
destruct (art_steps_au work art_gr 24) as (Eau & _). rewrite Eau. split; [exact OKw|].
unfold art_st_rcy. destruct (art_key_in work 24 w) eqn:EK; [|exact Est]. exfalso. apply art_key_in_spec in EK.
destruct (art_work_key_el 24 w EK) as (e & He & EKe & (_ & _ & GH)).
destruct e as [c0 w0 d b1 n0|mb ms m b1 n0|wb]; cbn [art_rel_key] in EKe.
- injection EKe as -> ->. rewrite Est in GH. discriminate GH.
- injection EKe as E _. discriminate E.
- injection EKe as ->. unfold art_rb_work in He. apply in_flat_map in He. destruct He as (x & Hx & He).
destruct (art_forall2_in_r _ _ _ _ _ x (art_forall2_firstn _ _ _ k _ _ XS) Hx) as (b' & Hb' & (Ea' & _ & _ & F2 & _)).
unfold art_rb_work1 in He. apply in_app_or in He. destruct He as [He|[E|[]]].
+ destruct (art_forall2_in_r _ _ _ _ _ _ F2 He) as (it & _ & (IT & _)). exact IT.
+ injection E as E. apply (art_nodup_app_d _ _ bt_addr _ _ b' b ND Hb' Hb). rewrite Ea', Ew, E. reflexivity.
Qed.
#[using="rn LB M bt bg REPX GHOST QT0 LIVE XS ROOM NEg sp HSP TRQ"] Lemma art_rcy_ia : art_rt_ia FSG art_gs_rcy M'.
Proof.
pose proof REPX as (_ & _ & _ & _ & _ & _ & _ & _ & (IA1 & IA2 & IA3) & _). destruct art_rcy_ia_cells as (J1 & J2).
unfold art_rt_ia. cbn [art_gs_rcy g_ia g_qt g_qg]. split; [exact J1|]. split; [exact J2|]. intros E. destruct (IA3 E) as (_ & E2). exfalso. exact (NEg E2).
Qed.
#[using="LB M bt bg REPX GHOST QT0 LIVE LIVE2 XS ROOM sp HSP INV' TRQ"] Lemma art_rcy_ghost : art_rt_ghost FSG rn art_gs_rcy M'.
Proof.
destruct GHOST as (T1 & T23 & T4 & T5). destruct INV' as (ICLS & _).
unfold art_rt_ghost. cbn [art_gs_rcy g_qt g_qg g_cls app].
split; [intros b it Hb Hit; exact (T1 b it (art_rest_in b Hb) Hit)|].
split. { intros c Hc. destruct (art_steps_au work art_gr c) as (Eau & _ & Emfa). rewrite Eau, Emfa. destruct (T23 c Hc) as (X & _). destruct (ICLS c Hc) as (_ & _ & CL & _). split; [exact X|exact CL]. }
split.
{ intros b Hb. pose proof (T4 b (art_rest_in b Hb)) as B. pose proof (art_in_skipn _ k _ b Hb) as Hbq.
destruct (art_rec_geo b Hbq) as (w & Ew & Hw0 & Hwu & Hi & Lo & Hi').
pose proof REPX as (ROK & _ & _ & _ & _ & _ & QR & _). destruct QR as (_ & _ & _ & _ & _ & ND & _ & _ & _ & BCH).
destruct (BCH b (art_rest_in b Hb)) as (w' & Ew' & OKw & Est). assert (w' = w) by (clear - Ew Ew'; lia). subst w'.
destruct (art_rok_rcy ROK) as (G1 & G2 & Espb & _).
assert (NI : ~ In (24, w) (map art_rel_key work)).
{ intros EK. destruct (art_work_key_el 24 w EK) as (e & He & EKe & (_ & _ & GH)).
destruct e as [c0 w0 d b1 n0|mb ms m b1 n0|wb]; cbn [art_rel_key] in EKe.
- injection EKe as -> ->. rewrite Est in GH. discriminate GH.
- injection EKe as E _. discriminate E.
- injection EKe as ->. unfold art_rb_work in He. apply in_flat_map in He. destruct He as (x & Hx & He).
destruct (art_forall2_in_r _ _ _ _ _ x (art_forall2_firstn _ _ _ k _ _ XS) Hx) as (b' & Hb' & (Ea' & _ & _ & F2 & _)).
unfold art_rb_work1 in He. apply in_app_or in He. destruct He as [He|[E|[]]].
+ destruct (art_forall2_in_r _ _ _ _ _ _ F2 He) as (it & _ & (IT & _)). exact IT.
+ injection E as E. rewrite QT0 in ND. cbn [app] in ND. apply NoDup_ListNoDup in ND. rewrite <- (firstn_skipn k (g_qg FSG G)) in ND.
apply (art_nodup_app_d _ _ bt_addr _ _ b' b ND Hb' Hb). rewrite Ea', Ew, E. reflexivity. }
rewrite Ew in B |- *. apply (art_rcy_sh_byte (spb + 24 * 2 ^ 32 + 16 * w) 8192 _ _ ltac:(clear - Lo Ew; lia) ltac:(clear - Hi' Ew G2; lia)); [| |clear; lia|exact B].
- rewrite Espb. replace (65536 * rn_qs rn + 24 * 2 ^ 32 + 16 * w + 8192) with ((8192 * rn_qs rn + 3 * 2 ^ 32 + 2 * w + 1024) * 8) by lia. apply Z_mod_mult.
- pose proof (art_chunk_zapart 24 w ltac:(lia) OKw NI) as Z. rewrite art_class_size_24 in Z. exact Z. }
apply art_rcy_cell_img; [lia|cbn; lia|cbn; lia|cbn; lia|exact T5].
Qed.
#[using="M bt bg REPX GHOST QT0 LIVE LIVE2 LIVE3 XS ROOM NEg sp lg HSP INV' TRQ C160 C168 C184 C176a C176b Clk QL' HREST"] Theorem art_alloc_rep_recycle : art_alloc_rep FSG rn art_gs_rcy LB M' /\ art_rt_ghost FSG rn art_gs_rcy M'.
Proof.
pose proof REPX as (ROK & _). split; [|exact art_rcy_ghost].
split; [exact ROK|]. split; [exact art_rcy_statics|]. split; [exact art_rcy_thread|]. split; [exact art_rcy_primary|]. split; [exact art_rcy_chunks|].
split; [exact art_rcy_sec|]. split; [exact art_rcy_quar|]. split; [exact art_rcy_depot|]. split; [exact art_rcy_ia|]. split; [exact art_rcy_blocks|exact art_rcy_ghost].
Qed.
Section SE.
Local Abbreviation SEC_T_art_item_size := (forall b it, In b (g_qt FSG G ++ g_qg FSG G) -> In it (bt_items b) -> 1 <= snd it < 2 ^ 28) (only parsing).
Variable b : ltac:(sec_ty2 constr:(SEC_T_art_item_size) 0%nat 0%nat).
Variable it : ltac:(sec_ty2 constr:(SEC_T_art_item_size) 1%nat 0%nat).
Lemma art_item_size : ltac:(sec_stmt2 constr:(SEC_T_art_item_size) 2%nat 0%nat).
Proof using rn LB M bt bg REPX b it.
intros Hb Hit.
pose proof REPX as (_ & _ & _ & _ & CH & SECR & QR & _). destruct QR as (_ & _ & _ & _ & _ & _ & _ & ITEMS & _).
destruct (ITEMS b it Hb Hit) as [(c & w & Hc & OKw & Est)|(s & Hs & Hq & Eu & En)].
- destruct (CH c Hc) as (_ & _ & _ & CW). cbv zeta in CW. specialize (CW w OKw). rewrite Est in CW. destruct CW as (_ & _ & (b1 & _ & _ & _ & _ & Hn) & _). exact Hn.
- destruct SECR as (_ & _ & _ & _ & _ & _ & _ & _ & PER & _). destruct (In_nth_error _ _ Hs) as (i & Hi). destruct (PER i s Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & Q & _).
rewrite Hq in Q. destruct Q as ((b1 & _ & _ & _ & _ & Hn) & _). rewrite <- En. exact Hn.
Qed.
End SE.
#[using="LB M bt bg REPX XS"] Lemma art_entry_merge : art_nq (g_qg FSG G) <= 2 ^ 15 -> 2 ^ 28 < art_batches_bytes (g_qg FSG G) ->
16384 * Z.of_nat (length gq) <= art_qbytes gq /\ art_qbytes gq < 2 ^ 54 /\ 0xe666661 < art_qbytes gq.
Proof.
intros NRET BIG. pose proof REPX as (_ & _ & _ & _ & _ & _ & QR & _). destruct QR as (_ & (fg & lg0 & _ & _ & _ & _ & BLg) & _ & _ & _ & _ & NEI & _).
rewrite (art_batches_ok_q _ _ XS), <- art_batches_bytes_q. rewrite length_map.
pose proof (art_nq_len (g_qg FSG G) (fun b Hb => NEI b (in_or_app _ _ b (or_intror Hb)))) as L2.
assert (SZ : forall bs, (forall b, In b bs -> In b (g_qg FSG G)) -> art_batches_bytes bs <= Z.of_nat (length bs) * 2 ^ 39).
{ induction bs as [|b r IH]; intros Hin; [cbn; lia|]. assert (Ec : art_batches_bytes (b :: r) = art_bt_bytes b + art_batches_bytes r) by (unfold art_batches_bytes, art_bt_bytes; cbn [fold_right]; lia). rewrite Ec. cbn [length]. specialize (IH (fun x Hx => Hin x (or_intror Hx))).
pose proof (art_sum_snd_bound (bt_items b) (2 ^ 28) (fun it Hit => ltac:(pose proof (art_item_size b it (in_or_app _ _ b (or_intror (Hin b (or_introl eq_refl)))) Hit); lia))) as SB0.
pose proof (art_batch_list_len M _ _ _ b BLg (Hin b (or_introl eq_refl))) as L. unfold art_bt_bytes. lia. }
specialize (SZ (g_qg FSG G) (fun b Hb => Hb)). lia.
Qed.
#[using="FSG G LB bt bg REPX XS"] Lemma art_entry_wl : ltac2:(TCodec.tc2 tcn__JbtInvRecycle "E'B&Q7&M&S0vH&Q8r1%211+8%746521qW291&D&RC&RA&QLvT0%211%411vT9%847B21%D3C:1").
Proof.
pose proof REPX as (_ & _ & _ & (_ & PRIM & _) & _). destruct (PRIM 24 ltac:(lia)) as ((_ & RR) & OK & _).
destruct RR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Wu). destruct OK as (_ & (_ & Haumu) & _).
apply Forall_forall. intros qb Hqb. apply in_map_iff in Hqb. destruct Hqb as (x & <- & Hx). destruct (art_forall2_in_r _ _ _ _ _ x XS Hx) as (b & Hb & Hbx).
rewrite (art_batch_ok_q b x Hbx). cbn [art_qb qb_addr fst]. destruct Hbx as (Ea & (Hw0 & Hwau & _) & _). rewrite Ea.
eapply wr_sub; [exact Wu|clear - Hw0; lia|clear - Hwau Haumu; lia].
Qed.
#[using="LB bt bg REPX XS NEg"] Lemma art_entry_qlist : cellA M (0x1396b0 + 160) 8 (Z.of_nat (length gq)) /\ cellA M (0x1396b0 + 168) 8 (art_qhead gq) /\ cellA M (0x1396b0 + 184) 8 (art_qbytes gq)
/\ art_qlist M gq (art_qhead gq) (bt_addr (art_lastb (g_qg FSG G))) /\ cellA M (0x1396b0 + 152) 4 0.
Proof.
pose proof REPX as (_ & _ & _ & _ & _ & _ & QR & _). destruct QR as (_ & (fg & lg0 & C160' & C168' & _ & C184' & BLg) & _ & _ & Clk' & _).
rewrite (art_batches_ok_q _ _ XS). rewrite length_map, <- art_batches_bytes_q. apply art_batch_list_q in BLg. pose proof (art_qlist_first _ _ _ _ BLg) as Ef. subst fg.
split; [exact C160'|]. split; [exact C168'|]. split; [exact C184'|]. split; [|exact Clk'].
apply art_batch_list_q in BLg. rewrite (art_batch_list_last M _ _ _ NEg BLg) in BLg. apply art_batch_list_q. exact BLg.
Qed.
#[using="rn LB M bt bg REPX QT0 LIVE LIVE3 XS"] Lemma art_entry_evok : forall RESV BUDGET LENMAX KMAX, art_evok_list (art_EVOK RESV BUDGET LENMAX KMAX) (g_log FSG G) (art_rels_events work).
Proof.
intros RESV BUDGET LENMAX KMAX. apply art_rcy_evok; [|exact art_work_pre_nodup].
intros mb ms m b1 n Hin. pose proof (art_pre_geo _ (proj1 (art_work_ok _ (art_work_pre_in _ Hin)))) as GE. cbn [art_el_geo] in GE.
destruct (LIVE _ GE) as (L0 & L1 & _). destruct (LIVE3 _ GE) as (A1 & A2). cbn [fst snd] in *. split; [exact GE|]. split; [exact A1|]. split; [exact A2|]. lia.
Qed.
Section SE.
Local Abbreviation SEC_T_art_rcy_out_kept_chunk := (forall c w a, 1 <= c <= 30 -> art_cptr_ok (AsanTab.class_size c) (cl_au (g_cls FSG G c)) w -> ~ In (c, w) (map art_rel_key work) -> g_st FSG G c w <> CBatch ->
spb + c * 2 ^ 32 + 16 * w <= a < spb + c * 2 ^ 32 + 16 * w + AsanTab.class_size c -> art_out Wtot a) (only parsing).
Variable c : ltac:(sec_ty2 constr:(SEC_T_art_rcy_out_kept_chunk) 0%nat 0%nat).
Variable w : ltac:(sec_ty2 constr:(SEC_T_art_rcy_out_kept_chunk) 1%nat 0%nat).
Variable a : ltac:(sec_ty2 constr:(SEC_T_art_rcy_out_kept_chunk) 2%nat 0%nat).
Lemma art_rcy_out_kept_chunk : ltac:(sec_stmt2 constr:(SEC_T_art_rcy_out_kept_chunk) 3%nat 0%nat).
Proof using LB M bt bg REPX GHOST QT0 LIVE LIVE2 XS ROOM HSP c w a.
intros Hc OKw NI NB Ha.
pose proof REPX as (ROK & _ & _ & _ & _ & _ & QR & _).
destruct (art_rok_rcy ROK) as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & G9 & G10 & Kspb & Kend & Atkb & Plo & Phi & Papp & Apt & Apkb & Kb0 & G11 & Apk).
destruct (art_chunk_geo c w Hc OKw) as (Hw0 & Hwau & Haumu & Hmu3 & (iw & Eiw)). destruct (art_class_size_facts c Hc) as (S1 & _).
pose proof (art_chunk_zapart c w Hc OKw NI) as ZA. unfold apart in G11, Apk.
assert (NL : forall p, In p (art_live (g_log FSG G)) -> ~ (fst p <= a < fst p + snd p)).
{ intros p Hp Hx. destruct (LIVE p Hp) as (_ & _ & _ & _ & OB). pose proof (OB (rn_kbase rn, 0x2000011000) ltac:(cbn; tauto)) as A. cbn [fst snd] in A. unfold apart in A. clear - A Hx Ha Hc Hw0 Hwau Haumu Hmu3 Kspb. lia. }
apply art_out_intro. intros p Hp Hx. apply in_app_or in Hp. destruct Hp as [Hp|Hp]; [|apply in_app_or in Hp; destruct Hp as [Hp|Hp]].
- unfold art_rcy_W2 in Hp. cbn [app In] in Hp. destruct Hp as [<-|[<-|Hp]]; cbn [fst snd] in Hx; [clear - Hx Ha Hc Hwau Haumu Hmu3 G6 Eris HSP; lia|clear - Hx Ha Hc Hw0 G4; lia|].
apply in_map_iff in Hp. destruct Hp as (qb & <- & Hqb). cbn [fst snd] in Hx. apply in_map_iff in Hqb. destruct Hqb as (x & <- & Hxx).
destruct (art_forall2_in_r _ _ _ _ _ x XS Hxx) as (b & Hb & Hbx). rewrite (art_batch_ok_q b x Hbx) in Hx. cbn [art_qb qb_addr fst] in Hx.
destruct (art_rec_geo b Hb) as (wb & Ewb & Hwb0 & Hwbu & Hiwb & _). destruct QR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & BCH).
destruct (BCH b (in_or_app _ _ b (or_intror Hb))) as (wb' & Ewb' & _ & Stb). assert (wb' = wb) by (clear - Ewb Ewb'; lia). subst wb'.
assert (NEk : (c, w) <> (24, wb)) by (intros E; injection E as -> ->; exact (NB Stb)).
pose proof (art_chunk_apart spb c w 24 wb Hc ltac:(lia) Hw0 ltac:(clear - Hwau Haumu Hmu3; lia) ltac:(exists iw; exact Eiw) Hwb0 ltac:(rewrite art_class_size_24; exact Hwbu)
ltac:(rewrite art_class_size_24; exact Hiwb) NEk) as A. rewrite art_class_size_24 in A. unfold apart in A. clear - A Hx Ha Ewb. lia.
- destruct (art_rcy_fp_where p a Hp Hx) as [H|[H|[H|[H|[(c' & Hc' & H)|[(e & He & [H|H])|[H|(b & Hb & H)]]]]]]].
+ clear - H Ha Hc Hwau Haumu Hmu3 G6 Eris HSP. lia.
+ clear - H Ha Hc Hw0 G4. lia.
+ clear - H Ha Hc Hw0 Hwau Haumu Hmu3 G11. lia.
+ clear - H Ha Hc Hwau Haumu Hmu3 Eris. lia.
+ clear - H Ha Hc Hc' Hw0 Hwau Haumu Hmu3. lia.
+ pose proof (ZA e He) as Z. unfold art_zapart, apart in Z. clear - Z H Ha. lia.
+ pose proof (art_work_shw_shadow e a He H) as Z. clear - Z Ha Hc Hw0 G4. lia.
+ clear - H Ha Hc Hw0 Hwau Haumu Hmu3 Apk. lia.
+ cbn [art_gr rg_bl] in Hb. apply in_map_iff in Hb. destruct Hb as (s0 & <- & Hs0). destruct (art_sec_entry_facts s0 Hs0) as (P2 & Big & _).
apply (NL _ P2). cbn [art_sec_b fst snd] in *. clear - H Big. lia.
- cbn [In] in Hp. destruct Hp as [<-|[]]. cbn [fst snd] in Hx. clear - Hx Ha Hc Hwau Haumu Hmu3 G6 Eris HSP. lia.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_rcy_out_kept_block := (forall s a, In s (g_sec FSG G) -> ~ In (Some (sc_map s)) (map art_rel_mb work) -> sc_map s + 4096 <= a < sc_map s + sc_msize s -> art_out Wtot a) (only parsing).
Variable s : ltac:(sec_ty2 constr:(SEC_T_art_rcy_out_kept_block) 0%nat 0%nat).
Variable a : ltac:(sec_ty2 constr:(SEC_T_art_rcy_out_kept_block) 1%nat 0%nat).
Lemma art_rcy_out_kept_block : ltac:(sec_stmt2 constr:(SEC_T_art_rcy_out_kept_block) 2%nat 0%nat).
Proof using LB M bt bg REPX GHOST QT0 LIVE LIVE2 XS ROOM HSP s a.
intros Hs NI Ha.
pose proof REPX as (ROK & _).
destruct (art_rok_rcy ROK) as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & G9 & G10 & Kspb & Kend & Atkb & Plo & Phi & Papp & Apt & Apkb & Kb0 & G11 & Apk).
destruct (art_sec_entry_facts s Hs) as (P2 & Big & P0). destruct (LIVE _ P2) as (L0 & L1 & L2 & L3 & OB). cbn [fst snd] in L0, L1, L2, L3.
pose proof (OB (rn_kbase rn, 0x2000011000) ltac:(cbn; tauto)) as Ak. pose proof (OB (rn_parr rn, 2 ^ 23) ltac:(cbn; tauto)) as Ap. pose proof (OB (rn_t rn, 4096) ltac:(cbn; tauto)) as At.
cbn [fst snd] in Ak, Ap, At. unfold apart in Ak, Ap, At.
apply art_out_intro. intros p Hp Hx. apply in_app_or in Hp. destruct Hp as [Hp|Hp]; [|apply in_app_or in Hp; destruct Hp as [Hp|Hp]].
- unfold art_rcy_W2 in Hp. cbn [app In] in Hp. destruct Hp as [<-|[<-|Hp]]; cbn [fst snd] in Hx; [clear - Hx Ha L2 HSP; lia|clear - Hx Ha P0; lia|].
apply in_map_iff in Hp. destruct Hp as (qb & <- & Hqb). cbn [fst snd] in Hx. pose proof (proj1 (Forall_forall _ _) (proj2 art_entry_qin) qb Hqb) as (Q1 & Q2). clear - Hx Q1 Q2 Ha Ak Kspb. lia.
- destruct (art_rcy_fp_where p a Hp Hx) as [H|[H|[H|[H|[(c' & Hc' & H)|[(e & He & [H|H])|[H|(b & Hb & H)]]]]]]].
+ clear - H Ha L2 HSP. lia.
+ clear - H Ha P0. lia.
+ clear - H Ha At. lia.
+ clear - H Ha Ak Kspb Eris. lia.
+ clear - H Hc' Ha Ak Kspb. lia.
+ pose proof (art_sec_keep_zapart s Hs NI e He) as Z. unfold art_zapart, apart in Z. clear - Z H Ha. lia.
+ pose proof (art_work_shw_shadow e a He H) as Z. clear - Z Ha L3 L1. lia.
+ clear - H Ha Ap. lia.
+ cbn [art_gr rg_bl] in Hb. apply in_map_iff in Hb. destruct Hb as (s0 & <- & Hs0). destruct (art_sec_entry_facts s0 Hs0) as (P20 & Big0 & _). cbn [art_sec_b fst snd] in H.
destruct (Z.eq_dec (sc_map s0) (sc_map s)) as [E|NE]; [clear - E H Ha; lia|]. pose proof (LIVE2 _ _ P20 P2 NE) as A. cbn [fst snd] in A. unfold apart in A. clear - A H Ha Big0. lia.
- cbn [In] in Hp. destruct Hp as [<-|[]]. cbn [fst snd] in Hx. clear - Hx Ha L2 HSP. lia.
Qed.
End SE.
Section SE.
Local Abbreviation SEC_T_art_rcy_out_block := (ltac2:(TCodec.tc2 tcn__JbtInvRecycle "R6':'F%2211&S2r2vG%33421'@'<&S8&3r3%23;;1%4219&S9&S6&;%13@@6%3261%52?1%<271&Q3%13:5B%@231&Q6&1&RIvT1&D&RC&Q7&RA&QLvT0%211%411vT9%948721%<2;1&RL&QM%118&QK%11:&QI%11<&S>+V0%22E1&R2&RB&CvSK%23H1A%411%@7>E<:761(2(9+T@%24QJQJ;1(7%11QK%63QL31%Q63QM81%Q73QNJ1%Q921QFp0Q;1p0QM1pW0R31pW4R31")) (only parsing).
Variable b0 : ltac:(sec_ty2 constr:(SEC_T_art_rcy_out_block) 0%nat 0%nat).
Variable a : ltac:(sec_ty2 constr:(SEC_T_art_rcy_out_block) 1%nat 0%nat).
Lemma art_rcy_out_block : ltac:(sec_stmt2 constr:(SEC_T_art_rcy_out_block) 2%nat 0%nat).
Proof using M bt bg REPX GHOST QT0 LIVE LIVE2 LIVE3 XS ROOM HSP b0 a.
intros Hb0 Ha.
pose proof REPX as (ROK & _ & _ & (_ & PRIM & _) & CH & SECR & _ & _ & _ & BLK & _).
destruct (art_rok_rcy ROK) as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & G9 & G10 & Kspb & Kend & Atkb & Plo & Phi & Papp & Apt & Apkb & Kb0 & G11 & Apk).
unfold in_shadow_of in Ha.
destruct (BLK b0 Hb0) as [(c & w & Hc & OKw & Est)|(s & Hs & Hq & Esu & Esn)].
- destruct (CH c Hc) as (_ & _ & _ & CW). cbv zeta in CW. specialize (CW w OKw). rewrite Est in CW. destruct CW as (_ & Lo & Hi & (bb & _ & _ & _ & _ & Hn) & _).
destruct (art_chunk_geo c w Hc OKw) as (Hw0 & Hwau & Haumu & Hmu3 & _). destruct (art_class_size_facts c Hc) as (S1 & S16).
assert (NI : ~ In (c, w) (map art_rel_key work)).
{ intros EK. destruct (art_work_key_st c w ltac:(lia) EK) as (_ & _ & [(u & n & X)|(_ & X)]); rewrite X in Est; discriminate Est. }
destruct Ha as [Ha|Ha].
+ apply (art_rcy_out_kept_chunk c w a Hc OKw NI); [rewrite Est; discriminate|clear - Ha Lo Hi; lia].
+ set (cb := spb + c * 2 ^ 32 + 16 * w) in *.
apply (art_rcy_zone_shadow cb (AsanTab.class_size c)); [unfold cb; clear - Hc G4 Hw0; lia|unfold cb; clear - Hc G6 G2 Eris Hwau Haumu Hmu3; lia|exact (art_chunk_zapart c w Hc OKw NI)|].
unfold HeapIfaceA.S, HeapIfaceA.SB, JbtPoison.SB in *.
assert (CB8 : (cb + AsanTab.class_size c) mod 8 = 0).
{ pose proof (Z.div_mod (AsanTab.class_size c) 16 ltac:(lia)) as Ds. rewrite S16 in Ds. unfold cb. rewrite Espb.
replace (65536 * rn_qs rn + c * 2 ^ 32 + 16 * w + AsanTab.class_size c) with ((8192 * rn_qs rn + c * 2 ^ 29 + 2 * w + 2 * (AsanTab.class_size c / 16)) * 8) by lia. apply Z_mod_mult. }
pose proof (Z.div_mod (cb + AsanTab.class_size c) 8 ltac:(lia)) as D. rewrite CB8 in D.
assert (cb / 8 <= fst b0 / 8) by (apply Z.div_le_mono; clear - Lo; lia). assert ((fst b0 + snd b0 - 1) / 8 < (cb + AsanTab.class_size c) / 8) by (apply Z.div_lt_upper_bound; clear - Hi D; lia). lia.
- destruct (In_nth_error _ _ Hs) as (i & Hi). destruct SECR as (_ & _ & _ & _ & _ & _ & _ & _ & PER & _). destruct (PER i s Hi) as (_ & P2 & _ & _ & _ & _ & Lo & Hi2 & Q & _).
rewrite Hq in Q. destruct Q as (_ & (bb & _ & _ & _ & _ & Hn) & _). rewrite Esu in Lo. rewrite Esu, Esn in Hi2.
assert (NI : ~ In (Some (sc_map s)) (map art_rel_mb work)).
{ intros X. destruct (art_work_mb_sec _ X) as (s' & Hs' & E' & Hq'). rewrite (art_sec_map_inj s' s Hs' Hs E') in Hq'. rewrite Hq in Hq'. discriminate Hq'. }
destruct (LIVE _ P2) as (L0 & L1 & L2 & _). cbn [fst snd] in L0, L1, L2. destruct (LIVE3 _ P2) as (A1 & A2). cbn [fst snd] in A1, A2.
destruct Ha as [Ha|Ha].
+ apply (art_rcy_out_kept_block s a Hs NI). clear - Ha Lo Hi2. lia.
+ apply (art_rcy_zone_shadow (sc_map s) (sc_msize s)); [clear - L0; lia|clear - L2 G2; lia|exact (art_sec_keep_zapart s Hs NI)|].
unfold HeapIfaceA.S, HeapIfaceA.SB, JbtPoison.SB in *.
pose proof (Z.div_mod (sc_map s) 4096 ltac:(lia)) as D1. rewrite A1 in D1. pose proof (Z.div_mod (sc_msize s) 4096 ltac:(lia)) as D2. rewrite A2 in D2.
assert (E8 : (sc_map s + sc_msize s) / 8 = 512 * (sc_map s / 4096) + 512 * (sc_msize s / 4096)).
{ replace (sc_map s + sc_msize s) with ((512 * (sc_map s / 4096) + 512 * (sc_msize s / 4096)) * 8) by lia. apply Z_div_mult. lia. }
assert (sc_map s / 8 <= fst b0 / 8) by (apply Z.div_le_mono; clear - Lo; lia). assert ((fst b0 + snd b0 - 1) / 8 < (sc_map s + sc_msize s) / 8) by (rewrite E8; apply Z.div_lt_upper_bound; clear - Hi2 D1 D2; lia). lia.
Qed.
End SE.
#[using="FSG G LB M bt bg REPX LIVE3 XS"] Lemma art_work_zone_al8 : ltac2:(TCodec.tc2 tcn__JbtInvRecycle "L'R;&S2r1&RB&C&RCvSKvT9%43321%611%93:81'='F&S:&3&R=&QLvT0%211r2%5221%73991+8%:221z%>3=21p0@1pW:K1").
Proof.
intros e He. pose proof (art_pre_geo e (proj1 (art_work_ok e (art_work_pre_in e He)))) as GE. pose proof REPX as (ROK & _). destruct (art_rok_rcy ROK) as (_ & _ & Espb & _).
destruct e as [c w d b1 n0|mb ms m b1 n0|wb]; cbn [art_rel_zone art_el_geo fst] in *.
- rewrite Espb. replace (65536 * rn_qs rn + c * 2 ^ 32 + 16 * w) with ((8192 * rn_qs rn + c * 2 ^ 29 + 2 * w) * 8) by lia. apply Z_mod_mult.
- destruct (LIVE3 _ GE) as (A1 & _). cbn [fst] in A1. pose proof (Z.div_mod mb 4096 ltac:(lia)) as D. rewrite A1 in D. replace mb with ((512 * (mb / 4096)) * 8) by lia. apply Z_mod_mult.
- rewrite Espb. replace (65536 * rn_qs rn + 24 * 2 ^ 32 + 16 * wb) with ((8192 * rn_qs rn + 3 * 2 ^ 32 + 2 * wb) * 8) by lia. apply Z_mod_mult.
Qed.
#[using="M bt bg REPX GHOST QT0 LIVE LIVE2 LIVE3 XS ROOM HSP"] Theorem art_rcy_out_bundle :
(forall b0 a, In b0 LB -> (fst b0 <= a < fst b0 + snd b0 \/ in_shadow_of (fst b0) (snd b0) a) -> art_out Wtot a)
/\ (forall a, rn_HI rn <= a -> ~ (sp - 512 <= a < sp) -> art_out Wtot a)
/\ (forall a, 0x10000 <= a < 0x693000 -> ~ (0x139418 + 56 <= a < 0x1396a8) -> ~ (0x1396b0 + 152 <= a < 0x1396b0 + 192) -> art_out Wtot a)
/\ (forall a, ar_fs (rn_ar rn) <= a < ar_fs (rn_ar rn) + FS_BYTES -> art_out Wtot a)
/\ (forall a, rn_dtls rn <= a < rn_dtls rn + 4096 -> art_out Wtot a)
/\ (forall a, rn_t rn <= a < rn_t rn + 208 -> art_out Wtot a)
/\ (forall lo len a, 0 <= lo -> 0 < len -> lo + len <= 2 ^ 47 -> apart lo len spb (2 ^ 37) -> (forall p, In p (art_live (g_log FSG G)) -> apart (fst p) (snd p) lo len) ->
HeapIfaceA.S lo <= a <= HeapIfaceA.S (lo + len - 1) -> art_out Wtot a).
Proof.
pose proof REPX as (ROK & _).
destruct (art_rok_rcy ROK) as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & G9 & G10 & Kspb & Kend & Atkb & Plo & Phi & Papp & Apt & Apkb & Kb0 & G11 & Apk).
destruct (art_rok_far ROK) as (_ & _ & _ & Ffs & Fdt).
split; [exact art_rcy_out_block|].
split. { intros a Ha Ns. apply art_rcy_out_far; [exact Ns|clear - Ha G6 Eris; lia|clear - Ha Phi; lia|clear - Ha G8; lia| |clear - Ha G1; lia|clear - Ha G1; lia|clear - Ha G1; lia].
intros p Hp Hin. destruct (LIVE p Hp) as (_ & _ & L2 & _). clear - L2 Hin Ha. lia. }
split. { intros a Ha N1 N2. apply art_rcy_out_far; [clear - Ha G1 HSP; lia|clear - Ha G4; lia|clear - Ha Plo; lia|clear - Ha G9; lia|intros p Hp; exact (art_live_off_img p a Hp Ha)|clear - Ha; lia|exact N1|exact N2]. }
split; [intros a Ha; exact (art_rcy_out_obj _ _ a Ffs Ha)|]. split; [intros a Ha; exact (art_rcy_out_obj _ _ a Fdt Ha)|].
split; [intros a Ha; apply art_rcy_out_thread; clear - Ha; lia|].
intros lo len a H0 H1 H47 Ak Al Ha. unfold HeapIfaceA.S, HeapIfaceA.SB in Ha.
assert (Q0 : 0 <= lo / 8) by (apply Z.div_pos; lia). assert (Q1 : (lo + len - 1) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
apply art_rcy_out_shadow; [clear - Ha Q0 Q1; lia|]. intros e He Hin. pose proof (art_work_shw_zone e a He Hin) as Zs. pose proof (art_work_zapart lo len Ak Al e He) as Ap.
pose proof (art_work_zone_al8 e He) as A8. unfold art_zapart, apart, JbtPoison.SB in *. destruct Ap as [Ap|Ap].
- pose proof (Z.div_le_mono _ _ 8 ltac:(lia) Ap). clear - H Zs Ha. lia.
- pose proof (Z.div_mod (fst (art_rel_zone spb e)) 8 ltac:(lia)) as D. rewrite A8 in D.
assert ((lo + len - 1) / 8 < fst (art_rel_zone spb e) / 8) by (apply Z.div_lt_upper_bound; clear - Ap D; lia). clear - H Zs Ha. lia.
Qed.
End Work.
End Entry.
