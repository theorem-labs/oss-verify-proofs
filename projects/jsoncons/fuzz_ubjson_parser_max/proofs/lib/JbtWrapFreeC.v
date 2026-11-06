(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim StoreOk Hoare AsanAcct HeapIface HeapIfaceA As0Tables
ArtMem ArtRuns ArtRunsMem JbtCellEx JbtCls JbtFp JbtClsRep JbtCARSpec JbtAlloc3Pure JbtDepotA JbtDepot ArtBridge JbtInv JbtInvMallocPure JbtInvMalloc JbtFxQ JbtFxBatch2 JbtFxBatch3 JbtFreeTop3
JbtInvFreePure JbtInvFree JbtInvDrain JbtLift JbtWrapPure JbtWrapKit JbtWrapMallocH JbtWrapMallocX JbtWrapMallocC JbtIfaceLaws.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import HeapIfaceAJx ShadowRLaws.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__JbtWrapFreeC () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Specif."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtBridge."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ArtMem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtCls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtFp."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtFxBatch3."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.JbtInv."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StoreOk."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0A'"; "0B"; "1None"; "1app"; "1bool"; "1fst"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1snd"; "1true"]; ["2and"; "2eq"; "2not"; "2or"; "3add"; "4sumbool"; "5map"; "6Z"; "0FF"; "0FPT"; "0L"; "0LB"; "0LK"; "7page_base"; "7page_in_ranges"; "0M"]; ["0M1"; "8in_ev_ranges"; "9apart"; ":A_wf"; ";lb_remove"; "<FS_BYTES"; "<S"; "<aheap_pres"; "<ar_fs"; "<ff_addr"; "<ff_bytes"; "<ff_class"; "<fframe"; "<in_shadow_of"; "=art_cls"; "=art_cls_mfa'"]; ["=art_cls_needs_populate"; "=art_cls_new"; "=art_cls_ok"; "=cl_cache"; "=cl_free"; "=cl_mu"; ">art_out"; "?art_enq_events"; "?art_enq_fp"; "@art_client_ok"; "@art_eager_ok"; "@art_run"; "@art_run_ok"; "@art_zone_statics"; "@rn_HI"; "@rn_ar"]; ["@rn_kbase"; "Amem_grows"; "0Sp"; "BIn"; "BNoDup"; "Bincl"; "Cadd"; "Cle"; "Clt"; "Cmul"; "Cof_nat"; "Cpow"; "Csub"; "0W"; "0a"; "0b"]; ["0b0"; "0cl"; "0cntB"; "0f"; "0km"; "0lazy"; "0lazy'"; "0len"; "0lo"; "0n"; "0newb"; "0qr"; "0qs"; "0ris"; "0rn"; "0sp"]; ["0spb"; "DZ_to_bv"; "Dbv"; "Dbv_unsigned"; "0t"; "0u"; "0v"; "0x"; "0z"]]).
Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Lemma art_out_dec : ltac2:(TCodec.tc2 tcn__JbtWrapFreeC "?'8'='G%2211%411'E&QFr2r1%3221&B%112%7231pV@;1pTL:1").
Proof.
induction W as [|p r IH]; intros x; cbn [art_out]; [left; exact I|].
destruct (IH x) as [O|NO]; [|right; intros (_ & X); exact (NO X)].
destruct (Z_le_dec (fst p) x) as [L1|N1]; [|left; split; [lia|exact O]].
destruct (Z_lt_dec x (fst p + snd p)) as [L2|N2]; [right; intros (X & _); apply X; lia|left; split; [lia|exact O]].
Qed.
Section Pkg.
Variable FSG : Type.
Definition art_free_fpt (rn : art_run) (G : art_gs FSG) (Sp u n q16 qr km : Z) (kb : nat) (k : art_fk) (d : bool) (lg : Z) (x : Z) : Prop :=
art_free_fpl FSG rn G Sp u q16 qr km x
\/ (d = true /\ ~ art_out (art_drain_W FSG rn (art_gs_free G (rn_spb rn) k u n kb) (Sp - 2208) lg) x).
Definition art_free_pkg (rn : art_run) (G : art_gs FSG) (LB : list (Z * Z)) (Sp u n q16 qr km : Z) (kb : nat) (k : art_fk) (d : bool) (lg : Z)
(Mr0 Mr' : word -> option byte) : Prop :=
let G1 := art_gs_free G (rn_spb rn) k u n kb in
let FPT := art_free_fpt rn G Sp u n q16 qr km kb k d lg in
art_alloc_rep FSG rn (if d then art_gs_drain G1 else G1) (lb_remove u LB) Mr'
/\ mem_grows Mr0 Mr'
/\ (forall x : word, ~ FPT (U x) -> Mr' x = Mr0 x)
/\ (forall b0 a, In b0 (lb_remove u LB) -> (fst b0 <= a < fst b0 + snd b0 \/ in_shadow_of (fst b0) (snd b0) a) -> ~ FPT a)
/\ (forall a, rn_HI rn <= a < 2 ^ 64 -> ~ (Sp - 4096 <= a < Sp) -> ~ FPT a)
/\ (forall a, 0x10000 <= a < 0x693000 -> ~ art_zone_statics a -> ~ FPT a)
/\ (forall a, ar_fs (rn_ar rn) <= a < ar_fs (rn_ar rn) + FS_BYTES -> ~ FPT a)
/\ (forall a, rn_dtls rn <= a < rn_dtls rn + 4096 -> ~ FPT a)
/\ (forall a, rn_t rn + 72 <= a < rn_t rn + 80 -> ~ FPT a)
/\ (forall lo len a, 0 <= lo -> 0 < len -> lo + len <= 2 ^ 47 -> (lo + len <= rn_kbase rn \/ rn_kbase rn + 0x2000011000 <= lo) ->
(lo + len <= u - 16 \/ u + 8 * qr <= lo) -> HeapIfaceA.S lo <= a <= HeapIfaceA.S (lo + len - 1) -> ~ FPT a)
/\ (0x693000 <= u - 16 /\ u + 8 * qr <= rn_HI rn /\ apart (u - 16) (16 + 8 * qr) (ar_fs (rn_ar rn)) FS_BYTES).
Variables (rn : art_run) (G : art_gs FSG) (LB : list (Z * Z)) (M M10 : word -> option byte).
Variables (Sp u n q16 qr b1 km : Z) (kb : nat) (k : art_fk).
Let qtl := g_qt FSG G.
Let cl24 := g_cls FSG G 24.
Let newb := art_free_newb qtl.
Let lastb := art_lastb qtl.
Let Gfr := art_gs_free G (rn_spb rn) k u n kb.
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
Hypothesis Emu : cl_mu cl24 = 262144 * km.
Hypothesis Edep : g_depot FSG G = Datatypes.S kb.
Hypothesis OUT : art_free3_out M M10 Sp (rn_t rn) u q16 qr (rn_l2 rn) (rn_blk rn) b1 n (rn_spb rn) (rn_ris rn) (rn_qs rn) km (Z.of_nat (length qtl)) (bt_addr lastb)
(Z.of_nat (length (bt_items lastb))) (art_bt_bytes lastb) (art_batches_bytes qtl) kb (g_inited FSG G) cl24.
Hypothesis LIVE : forall p, In p (art_live (g_log FSG G)) ->
0 < fst p /\ 0 < snd p /\ fst p + snd p <= rn_HI rn /\ (fst p + snd p <= 0x7fff7000 \/ 0x10007fff8000 <= fst p)
/\ (forall o, In o (art_objs rn) -> apart (fst p) (snd p) (fst o) (snd o)).
Hypothesis LIVE2 : forall p p', In p (art_live (g_log FSG G)) -> In p' (art_live (g_log FSG G)) -> fst p <> fst p' -> apart (fst p) (snd p) (fst p') (snd p').
Hypothesis LIVE3 : forall p, In p (art_live (g_log FSG G)) -> fst p mod 4096 = 0 /\ snd p mod 4096 = 0.
Hypothesis OKpre : newb = true -> art_cls_ok 24 (art_ca_pre 24 cl24).
Hypothesis Hother : forall b0, In b0 (lb_remove u LB) -> In b0 LB /\ fst b0 <> u.
#[using="b1 cl24 lastb REP Hin Eu Hn Hqr Hb1 Hty Cn KIND HS Emu Edep OUT LIVE LIVE2 LIVE3 OKpre Hother"] Lemma art_wf_pkg_fpl :
art_alloc_rep_b FSG (2 ^ 29) rn Gfr (lb_remove u LB) M10
/\ art_batches_bytes (g_qt FSG Gfr) = art_batches_bytes qtl + n + (if newb then 8192 else 0)
/\ mem_grows M M10
/\ (forall x : word, ~ art_free_fpl FSG rn G Sp u q16 qr km (U x) -> M10 x = M x)
/\ (forall b0 a, In b0 (lb_remove u LB) -> (fst b0 <= a < fst b0 + snd b0 \/ in_shadow_of (fst b0) (snd b0) a) -> ~ art_free_fpl FSG rn G Sp u q16 qr km a)
/\ (forall a, rn_HI rn <= a < 2 ^ 64 -> ~ (Sp - 4096 <= a < Sp) -> ~ art_free_fpl FSG rn G Sp u q16 qr km a)
/\ (forall a, 0x10000 <= a < 0x693000 -> ~ art_zone_statics a -> ~ art_free_fpl FSG rn G Sp u q16 qr km a)
/\ (forall a, ar_fs (rn_ar rn) <= a < ar_fs (rn_ar rn) + FS_BYTES -> ~ art_free_fpl FSG rn G Sp u q16 qr km a)
/\ (forall a, rn_dtls rn <= a < rn_dtls rn + 4096 -> ~ art_free_fpl FSG rn G Sp u q16 qr km a)
/\ (forall a, rn_t rn + 72 <= a < rn_t rn + 80 -> ~ art_free_fpl FSG rn G Sp u q16 qr km a)
/\ (forall lo len a, 0 <= lo -> 0 < len -> lo + len <= 2 ^ 47 -> (lo + len <= rn_kbase rn \/ rn_kbase rn + 0x2000011000 <= lo) ->
(lo + len <= u - 16 \/ u + 8 * qr <= lo) -> HeapIfaceA.S lo <= a <= HeapIfaceA.S (lo + len - 1) -> ~ art_free_fpl FSG rn G Sp u q16 qr km a)
/\ (0x693000 <= u - 16 /\ u + 8 * qr <= rn_HI rn /\ apart (u - 16) (16 + 8 * qr) (ar_fs (rn_ar rn)) FS_BYTES).
Proof.
destruct (art_frep_bundle FSG rn G LB M M10 Sp u n q16 qr b1 km kb k REP Hin Eu Hn Hqr Hb1 Hty Cn KIND HS Emu Edep OUT LIVE LIVE2 LIVE3 OKpre Hother)
as (REPB & EBY & FRL & NFPB & NFPW & NFPS & NFPI & GFS & GDT & GTH & GSH & UF).
pose proof REP as (ROK & _). rok_open14 ROK. geo_open GEO. destruct OUT as (GRW & _).
split; [exact REPB|]. split; [exact EBY|]. split; [exact GRW|]. split; [exact FRL|]. split; [exact NFPB|].
split; [intros a Ha Ns; apply NFPS; [clear - Ha; lia|exact Ns]|].
split. { intros a Ha NZ. apply (NFPI a Ha); intros X; apply NZ; unfold art_zone_statics; clear - X; lia. }
split. { intros a Ha. apply NFPW; [unfold FS_BYTES in *; clear - Ha Flo Fhi G2; lia|]. apply (art_gap_out _ a 1); [apply GFS; clear - Ha; lia|clear; lia]. }
split. { intros a Ha. apply NFPW; [clear - Ha D0 D1 G2; lia|]. apply (art_gap_out _ a 1); [apply GDT; clear - Ha; lia|clear; lia]. }
split. { intros a Ha. apply NFPW; [clear - Ha G7 G8 G2; lia|]. apply (art_gap_out _ a 1); [apply GTH; clear - Ha; lia|clear; lia]. }
split; [|exact UF].
intros lo len a Hlo Hlen Hhi Hk Off Ha. pose proof (art_S_ge lo 0 ltac:(lia)) as B0. pose proof (art_S_lt (lo + len - 1) (2 ^ 44) ltac:(clear - Hhi; lia)) as B1.
apply NFPW; [clear - Ha B0 B1; lia|]. apply (art_gap_out _ a 1); [exact (GSH lo len a Hlo Hlen Hhi Hk Off Ha)|clear; lia].
Qed.
#[using="b1 cl24 lastb Gfr REP Hin Eu Hn Hqr Hb1 Hty Cn KIND HS Emu Edep OUT LIVE LIVE2 LIVE3 OKpre Hother"] Lemma art_wf_pkg1 : forall lg, art_batches_bytes qtl + n + (if newb then 8192 else 0) <= 2 ^ 20 -> art_free_pkg rn G LB Sp u n q16 qr km kb k false lg M M10.
Proof.
intros lg Hby. destruct art_wf_pkg_fpl as (REPB & EBY & GRW & FRL & NFPB & NFPS & NFPI & NFS & NDT & NTH & NSH & UF).
unfold art_free_pkg, art_free_fpt. cbv zeta.
assert (NF : forall a, ~ art_free_fpl FSG rn G Sp u q16 qr km a -> ~ (art_free_fpl FSG rn G Sp u q16 qr km a \/ (false = true /\ ~ art_out (art_drain_W FSG rn (art_gs_free G (rn_spb rn) k u n kb) (Sp - 2208) lg) a))).
{ intros a N [F|(E & _)]; [exact (N F)|discriminate]. }
split. { destruct REPB as (r1 & r2 & r3 & r4 & r5 & r6 & (q1 & q2 & q3 & q4) & r8 & r9 & r10). fold Gfr.
split; [exact r1|]. split; [exact r2|]. split; [exact r3|]. split; [exact r4|]. split; [exact r5|]. split; [exact r6|]. split; [|split; [exact r8|split; [exact r9|exact r10]]].
split; [exact q1|]. split; [exact q2|]. split; [rewrite EBY; exact Hby|exact q4]. }
split; [exact GRW|]. split; [intros x N; apply FRL; intros F; apply N; left; exact F|].
split; [intros b0 a Hb0 Ha; apply NF; exact (NFPB b0 a Hb0 Ha)|]. split; [intros a Ha Ns; apply NF; exact (NFPS a Ha Ns)|].
split; [intros a Ha NZ; apply NF; exact (NFPI a Ha NZ)|]. split; [intros a Ha; apply NF; exact (NFS a Ha)|]. split; [intros a Ha; apply NF; exact (NDT a Ha)|].
split; [intros a Ha; apply NF; exact (NTH a Ha)|]. split; [|exact UF]. intros lo len a H1 H2 H3 H4 H5 H6. apply NF. exact (NSH lo len a H1 H2 H3 H4 H5 H6).
Qed.
#[using="b1 qtl cl24 newb lastb REP Hin Eu Hn Hqr Hb1 Hty Cn KIND HS Emu Edep OUT LIVE LIVE2 LIVE3 OKpre Hother"] Lemma art_wf_pkg2 : forall (M' : word -> option byte) ft lt fg lg,
g_qt FSG Gfr <> [] -> art_batch_list M10 (g_qt FSG Gfr) ft lt -> cellA M10 (0x1396b0 + 168) 8 fg -> art_batch_list M10 (g_qg FSG Gfr) fg lg ->
art_batches_bytes (g_qg FSG Gfr) + art_batches_bytes (g_qt FSG Gfr) <= 2 ^ 28 ->
mem_grows M10 M' -> art_agree (art_drain_W FSG rn Gfr (Sp - 2208) lg) M10 M' ->
(cellA M' (rn_t rn + 80) 8 0 /\ cellA M' (rn_t rn + 80 + 8) 8 0 /\ cellA M' (rn_t rn + 80 + 16) 8 0 /\ cellA M' (rn_t rn + 80 + 24) 8 0
/\ cellA M' (0x1396b0 + 160) 8 (Z.of_nat (length (g_qg FSG Gfr)) + Z.of_nat (length (g_qt FSG Gfr))) /\ cellA M' (0x1396b0 + 176) 8 lt
/\ cellA M' (0x1396b0 + 184) 8 (art_batches_bytes (g_qg FSG Gfr) + art_batches_bytes (g_qt FSG Gfr)) /\ cellA M' (0x1396b0 + 152) 4 0
/\ (Z.of_nat (length (g_qg FSG Gfr)) = 0 -> cellA M' (0x1396b0 + 168) 8 ft) /\ (Z.of_nat (length (g_qg FSG Gfr)) <> 0 -> cellA M' lg 8 ft)) ->
art_free_pkg rn G LB Sp u n q16 qr km kb k true lg M M'.
Proof.
intros M' ft lt fg lg NEq BLt Gf BLg NR GRW2 AGR POST. destruct art_wf_pkg_fpl as (REPB & EBY & GRW & FRL & NFPB & NFPS & NFPI & NFS & NDT & NTH & NSH & UF).
assert (LIVE1 : forall p, In p (art_live (g_log FSG Gfr)) ->
0 < fst p /\ 0 < snd p /\ fst p + snd p <= rn_HI rn /\ (fst p + snd p <= 0x7fff7000 \/ 0x10007fff8000 <= fst p)
/\ (forall o, In o (art_objs rn) -> apart (fst p) (snd p) (fst o) (snd o))).
{ intros p Hp. apply LIVE. unfold Gfr in Hp. rewrite art_frep_live_eq in Hp. exact Hp. }
assert (HSP : rn_HI rn <= Sp - 2208 - 48) by (clear - HS; lia).
pose proof (art_alloc_rep_drain FSG rn Gfr (lb_remove u LB) M10 M' (2 ^ 29) (Sp - 2208) ft lt fg lg REPB NEq BLt Gf BLg HSP NR GRW2 AGR POST LIVE1) as REP2.
destruct (art_drn_out_bundle FSG rn Gfr (lb_remove u LB) M10 (2 ^ 29) (Sp - 2208) fg lg REPB BLg HSP LIVE1) as (OB & OSH & OST & OIM & OFS & ODT & OTH).
unfold art_free_pkg, art_free_fpt. cbv zeta. fold Gfr.
assert (NF : forall a, ~ art_free_fpl FSG rn G Sp u q16 qr km a -> art_out (art_drain_W FSG rn Gfr (Sp - 2208) lg) a ->
~ (art_free_fpl FSG rn G Sp u q16 qr km a \/ (true = true /\ ~ art_out (art_drain_W FSG rn Gfr (Sp - 2208) lg) a))).
{ intros a N O [F|(_ & X)]; [exact (N F)|exact (X O)]. }
split; [exact REP2|]. split; [eapply mem_grows_trans; [exact GRW|exact GRW2]|].
split. { intros x N. rewrite (AGR x). - apply FRL. intros F. apply N. left. exact F.
- destruct (art_out_dec (art_drain_W FSG rn Gfr (Sp - 2208) lg) (U x)) as [O|NO]; [exact O|]. exfalso. apply N. right. split; [reflexivity|exact NO]. }
split; [intros b0 a Hb0 Ha; apply NF; [exact (NFPB b0 a Hb0 Ha)|exact (OB b0 a Hb0 Ha)]|].
split; [intros a Ha Ns; apply NF; [exact (NFPS a Ha Ns)|apply OST; [clear - Ha; lia|clear - Ns; lia]]|].
split. { intros a Ha NZ. apply NF; [exact (NFPI a Ha NZ)|]. apply OIM; [exact Ha|]. intros X. apply NZ. unfold art_zone_statics. clear - X. lia. }
split; [intros a Ha; apply NF; [exact (NFS a Ha)|exact (OFS a Ha)]|]. split; [intros a Ha; apply NF; [exact (NDT a Ha)|exact (ODT a Ha)]|].
split; [intros a Ha; apply NF; [exact (NTH a Ha)|apply OTH; clear - Ha; lia]|]. split; [|exact UF].
intros lo len a H1 H2 H3 H4 H5 H6. apply NF; [exact (NSH lo len a H1 H2 H3 H4 H5 H6)|]. apply OSH.
pose proof (art_S_ge lo 0 ltac:(lia)) as B0. pose proof (art_S_lt (lo + len - 1) (2 ^ 44) ltac:(clear - H3; lia)) as B1. clear - H6 B0 B1. lia.
Qed.
End Pkg.
Lemma art_enq_events_in_fp : ltac2:(TCodec.tc2 tcn__JbtWrapFreeC "RB'5'G'Q>&QB+Hr2%3221'A&QEr3%211&R9+XPP0r8%3221%83>51r?(?%;3B21'8%11C&QCr5%211(:%11H%C3631&Q@r6%22I1%G3N1=&R7&Q?r7&R6&R:&7&QD%115%32Q61%511&QA%12Q69%9231%<2;1+`PPPP0%?221p0A1p0F1p0O1&Q1&QGr@r=%3321Q0r4%6221&QHrAr>r<r;r:r9%7<6<Q@5;4321QCOQ:p091p0A1p0QD1p0QN1pVBR41pU4R41pU6R61p6R71pQFR81pU0R91pU:R:1pUJR;1pULR<1pV2R=1pV:R>1pV0R?1pUFRA1").
Proof.
intros newb sp t spb ris qs km b L B cntB cl z OK Emu Room (ev & Hev & Hz). unfold art_enq_events in Hev. destruct newb; [|destruct Hev].
pose proof OK as (_ & _ & _ & _ & _ & _ & _ & (Hmfa0 & _) & _).
unfold art_enq_fp, art_enq_new_fp. right; left. unfold art_refill_fp. unfold art_ca_events, art_refill_events in Hev.
destruct (cl_cache cl) eqn:Ec; [|destruct Hev]. destruct (art_cls_needs_populate 24 cl) eqn:NP; [|destruct Hev]. specialize (Room eq_refl eq_refl eq_refl).
destruct Hev as [<-|Hev].
- cbn [art_ev_range fst snd] in Hz. do 5 right. left. lia.
- match type of Hev with In _ (if ?bb then _ else _) => destruct bb end; [destruct Hev|]. destruct Hev as [<-|[]].
cbn [art_ev_range fst snd] in Hz. do 6 right. left. lia.
Qed.
Section ExitMem.
Variable FSG : Type.
Context {fx : PropExec.FPState}.
Section SE.
Local Abbreviation SEC_T_art_wfc_mem := (forall rn (G : art_gs FSG) (A A' : list (Z * Z)) (M M1 : word -> option byte) (model model' : Model) (log' : list aev)
(Sp u n q16 qr km : Z) (kb : nat) (k : art_fk) (d : bool) (lg : Z), let cl := g_cls FSG G 24 in
let newb := art_free_newb (g_qt FSG G) in
let cl' := art_enq_cls newb cl in
let FPT := art_free_fpt FSG rn G Sp u n q16 qr km kb k d lg in
art_run_ok rn -> art_cls_ok 24 cl -> cl_mu cl = 262144 * km ->
(newb = true -> cl_cache cl = [] -> art_cls_needs_populate 24 cl = true -> cl_mu cl + 262144 <= 3758096384
/\ art_cls_mfa' cl (Z.of_nat (length (cl_free cl)) + art_cls_new 24 cl) <= 536870912) ->
log' = g_log FSG G ++ art_enq_events newb (rn_spb rn) cl ->
bhist A M model (g_log FSG G) log' A' M1 model' ->
mem_grows (mrestrict (bhid A model) M) (mrestrict (bhid A' model') M1) ->
(forall x : word, ~ FPT (U x) -> mrestrict (bhid A' model') M1 x = mrestrict (bhid A model) M x) ->
wrA (mrestrict (bhid A' model') M1) (rn_spb rn + 24 * 2 ^ 32) (cl_mu cl') ->
wrA (mrestrict (bhid A' model') M1) (rn_spb rn + 24 * 2 ^ 32 + 3758096384) (cl_mfa cl') ->
(forall x : word, ~ FPT (U x) -> M1 x = M x)
/\ mem_grows M M1
/\ (forall x : word, (rn_spb rn + 24 * 2 ^ 32 <= U x < rn_spb rn + 24 * 2 ^ 32 + cl_mu cl'
\/ rn_spb rn + 24 * 2 ^ 32 + 3758096384 <= U x < rn_spb rn + 24 * 2 ^ 32 + 3758096384 + cl_mfa cl') -> bhid A' model' x = false)) (only parsing).
Variable rn : ltac:(sec_ty2 constr:(SEC_T_art_wfc_mem) 0%nat 0%nat).
Variable G : ltac:(sec_ty2 constr:(SEC_T_art_wfc_mem) 1%nat 0%nat).
Variable A : ltac:(sec_ty2 constr:(SEC_T_art_wfc_mem) 2%nat 0%nat).
Variable A' : ltac:(sec_ty2 constr:(SEC_T_art_wfc_mem) 3%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_wfc_mem) 4%nat 0%nat).
Variable M1 : ltac:(sec_ty2 constr:(SEC_T_art_wfc_mem) 5%nat 0%nat).
Variable model : ltac:(sec_ty2 constr:(SEC_T_art_wfc_mem) 6%nat 0%nat).
Variable model' : ltac:(sec_ty2 constr:(SEC_T_art_wfc_mem) 7%nat 0%nat).
Variable log' : ltac:(sec_ty2 constr:(SEC_T_art_wfc_mem) 8%nat 0%nat).
Variable Sp : ltac:(sec_ty2 constr:(SEC_T_art_wfc_mem) 9%nat 0%nat).
Variable u : ltac:(sec_ty2 constr:(SEC_T_art_wfc_mem) 10%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_wfc_mem) 11%nat 0%nat).
Variable q16 : ltac:(sec_ty2 constr:(SEC_T_art_wfc_mem) 12%nat 0%nat).
Variable qr : ltac:(sec_ty2 constr:(SEC_T_art_wfc_mem) 13%nat 0%nat).
Variable km : ltac:(sec_ty2 constr:(SEC_T_art_wfc_mem) 14%nat 0%nat).
Variable kb : ltac:(sec_ty2 constr:(SEC_T_art_wfc_mem) 15%nat 0%nat).
Variable k : ltac:(sec_ty2 constr:(SEC_T_art_wfc_mem) 16%nat 0%nat).
Variable d : ltac:(sec_ty2 constr:(SEC_T_art_wfc_mem) 17%nat 0%nat).
Variable lg : ltac:(sec_ty2 constr:(SEC_T_art_wfc_mem) 18%nat 0%nat).
#[using="fx rn G A A' M M1 model model' log' Sp u n q16 qr km kb k d lg"] Lemma art_wfc_mem : ltac:(sec_stmt2 constr:(SEC_T_art_wfc_mem) 19%nat 0%nat).
Proof.
intros cl newb cl' FPT ROK OK Emu Room Elog BH GR FR Wu Wfa.
pose proof ROK as ROK'. rok_open14 ROK'. geo_open GEO.
pose proof OK as (_ & (Hau0 & Haumu) & _ & _ & _ & Hmu3 & _ & (Hmfa0 & Hmfa1) & _).
assert (OKc' : art_cls_ok 24 cl').
{ unfold cl', art_enq_cls. destruct newb eqn:En; [|exact OK]. apply art_cls_ok_pop.
- apply art_cls_ok_ca_pre; [lia|exact OK|]. intros E1 E2. exact (Room eq_refl E1 E2).
- apply art_ca_pre_cache_ne; [lia|exact OK]. }
pose proof OKc' as (_ & (Hau0' & Haumu') & _ & _ & _ & Hmu3' & _ & (Hmfa0' & Hmfa1') & _).
assert (VIS : forall x : word, (rn_spb rn + 24 * 2 ^ 32 <= U x < rn_spb rn + 24 * 2 ^ 32 + cl_mu cl'
\/ rn_spb rn + 24 * 2 ^ 32 + 3758096384 <= U x < rn_spb rn + 24 * 2 ^ 32 + 3758096384 + cl_mfa cl') -> bhid A' model' x = false).
{ intros x [Hx|Hx].
- apply (art_vis_of_wr (bhid A' model') M1 (rn_spb rn + 24 * 2 ^ 32) (cl_mu cl') ltac:(lia) ltac:(lia) ltac:(right; lia) Wu x Hx).
- apply (art_vis_of_wr (bhid A' model') M1 (rn_spb rn + 24 * 2 ^ 32 + 3758096384) (cl_mfa cl') ltac:(lia) ltac:(lia) ltac:(right; lia) Wfa x Hx). }
assert (EVL : forall sfx, log' = g_log FSG G ++ sfx -> forall z, in_ev_ranges sfx z -> FPT z).
{ intros sfx El z Hz. rewrite Elog in El. apply app_inv_head in El. subst sfx. unfold FPT, art_free_fpt. left. unfold art_free_fpl. right.
apply (art_enq_events_in_fp _ _ _ _ _ _ _ _ _ _ _ cl z OK Emu); [|exact Hz]. intros E1 E2 E3. exact (proj2 (Room E1 E2 E3)). }
split; [|split; [|exact VIS]].
- exact (art_lift_frame A A' M M1 model model' (g_log FSG G) log' BH FPT FR EVL).
- apply (art_lift_grows A A' M M1 model model' (g_log FSG G) log' BH GR). intros sfx El x Hz Hv.
rewrite Elog in El. apply app_inv_head in El. subst sfx. destruct Hz as (ev & Hev & Hz).
unfold art_enq_events in Hev. destruct newb eqn:En; [|destruct Hev].
unfold art_ca_events, art_refill_events in Hev. destruct (cl_cache cl) eqn:Ec; [|destruct Hev]. destruct (art_cls_needs_populate 24 cl) eqn:NP; [|destruct Hev].
destruct (Room eq_refl eq_refl eq_refl) as (R1 & R2).
pose proof (art_ca_pre_mu_pop 24 cl Ec NP) as Emp. pose proof (art_ca_pre_mfa_pop 24 cl Ec NP) as Emf.
assert (Emu' : cl_mu cl' = cl_mu (art_ca_pre 24 cl)) by reflexivity. assert (Emfa' : cl_mfa cl' = cl_mfa (art_ca_pre 24 cl)) by reflexivity.
assert (D : forall a j, 0 <= a -> a + j < 2 ^ 64 -> 0x693000 <= a -> wrA (mrestrict (bhid A' model') M1) a j -> a <= U x < a + j -> mrestrict (bhid A' model') M1 x <> None).
{ intros a j Ha Hj Hoff Wr Hx. pose proof (art_wr_wview ASEGS _ a j Ha Hj Wr x Hx) as V. rewrite art_wview_off in V by lia. exact V. }
destruct Hev as [<-|Hev].
+ cbn [art_ev_range fst snd] in Hz. apply (D (rn_spb rn + 24 * 2 ^ 32) (cl_mu cl') ltac:(lia) ltac:(lia) ltac:(lia) Wu). rewrite Emu', Emp. lia.
+ match type of Hev with In _ (if ?bb then _ else _) => destruct bb end; [destruct Hev|]. destruct Hev as [<-|[]]. cbn [art_ev_range fst snd] in Hz.
apply (D (rn_spb rn + 24 * 2 ^ 32 + 3758096384) (cl_mfa cl') ltac:(lia) ltac:(lia) ltac:(lia) Wfa). rewrite Emfa', Emf. lia.
Qed.
End SE.
End ExitMem.
Section LazyCredit.
Variable FSG : Type.
#[using="Type"] Lemma art_lazy_ok_step : forall rn (G G' : art_gs FSG) A lazy A' lazy',
art_lazy_ok FSG rn G A lazy -> incl A A' ->
(forall x : word, mkH lazy' A' x = true -> mkH lazy A x = true) ->
(forall wd, In wd A' -> In wd A) ->
(forall x : word, page_in_ranges (page_base x) lazy' = true -> page_in_ranges (page_base x) lazy = true) ->
(forall x : word, art_committed FSG rn G' (U x) -> art_committed FSG rn G (U x) \/ mkH lazy' A' x = false) ->
art_lazy_ok FSG rn G' A' lazy'.
Proof.
intros rn G G' A lazy A' lazy' (L1 & L2 & L3 & L4) INC B2 B4 B5 CM.
split; [|split; [|split]].
- intros x Hlz. destruct (page_allowedb A' (page_base x)) eqn:EA.
+ unfold page_allowedb in EA. apply existsb_exists in EA. destruct EA as (iv & Hiv0 & Hiv). apply andb_prop in Hiv as [I1 I2].
apply Z.leb_le in I1. apply Z.leb_le in I2. unfold page_size in I2. pose proof (art_page_base_bounds x) as PB.
destruct (L2 iv (B4 iv Hiv0)) as [Z|[Z|NL]]; [left; lia|right; left; lia|]. exfalso. pose proof (B5 x Hlz) as E0. rewrite (NL x ltac:(lia)) in E0. discriminate E0.
+ assert (Hh : mkH lazy' A' x = true) by (unfold mkH; rewrite Hlz, EA; reflexivity).
pose proof (B2 x Hh) as Hh0. unfold mkH in Hh0. apply andb_prop in Hh0 as [Hl0 _].
destruct (L1 x Hl0) as [Z|[Z|[Z NC]]]; [left; exact Z|right; left; exact Z|]. right; right. split; [exact Z|].
intros C'. destruct (CM x C') as [C0|V]; [exact (NC C0)|rewrite V in Hh; discriminate Hh].
- intros wd Hwd. destruct (L2 wd (B4 wd Hwd)) as [Z|[Z|NL]]; [left; exact Z|right; left; exact Z|right; right].
intros x Hx. destruct (page_in_ranges (page_base x) lazy') eqn:E; [|reflexivity]. pose proof (B5 x E) as E0. rewrite (NL x Hx) in E0. discriminate E0.
- intros x Hx. apply (art_page_allowedb_incl A A' _ INC). exact (L3 x Hx).
- intros x Hx. apply (art_page_allowedb_incl A A' _ INC). exact (L4 x Hx).
Qed.
#[using="Type"] Lemma art_free_committed : forall rn (G : art_gs FSG) u n kb k (d : bool) x,
let G1 := art_gs_free G (rn_spb rn) k u n kb in
let cl' := art_enq_cls (art_free_newb (g_qt FSG G)) (g_cls FSG G 24) in
art_committed FSG rn (if d then art_gs_drain G1 else G1) x ->
art_committed FSG rn G x
\/ (rn_spb rn + 24 * 2 ^ 32 <= x < rn_spb rn + 24 * 2 ^ 32 + cl_mu cl' \/ rn_spb rn + 24 * 2 ^ 32 + 3758096384 <= x < rn_spb rn + 24 * 2 ^ 32 + 3758096384 + cl_mfa cl').
Proof.
intros rn G u n kb k d x G1 cl' C.
assert (C1 : art_committed FSG rn G1 x) by (destruct d; exact C). clear C.
unfold art_committed in C1 |- *. destruct C1 as [RI|[(c0 & Hc0 & Zc)|(PC & P)]]; [left; left; exact RI| |left; right; right; split; [exact PC|exact P]].
unfold G1 in Zc. cbn [art_gs_free g_cls] in Zc. destruct (Z.eqb_spec c0 24) as [->|Ne]; [right; exact Zc|left; right; left; exists c0; split; [exact Hc0|exact Zc]].
Qed.
#[using="Type"] Lemma art_eager_ok_remove : ltac2:(TCodec.tc2 tcn__JbtWrapFreeC "Q>'8'='G%2211%411'S2yR0%211%7211%911&QJr6r5r4%43321&Q3%113'A'5&N&Mr1%211%421;(?%83721r2%711r8%:221%=3<16p061pV@I1&Q4r9%22F1%J31IHp051p0F1p0I1pV<Q61pU>Q01p4Q61pU<Q21p2Q81pQHQ91").
Proof.
intros LB A lazy A' lazy' u (AW & EG) AW' B5. split; [exact AW'|]. intros b x Hb Hx.
destruct (page_in_ranges (page_base x) lazy') eqn:E; [|reflexivity]. pose proof (B5 x E) as E0. rewrite (EG b x (art_lb_remove_in u LB b Hb) Hx) in E0. discriminate E0.
Qed.
End LazyCredit.
Lemma art_lb_remove_len : ltac2:(TCodec.tc2 tcn__JbtWrapFreeC "L'G'8'=%1233%311&R3(<r3r2%349921r1%63821'A'9&D&7&Q4r4%221:%42@1u1%7221%72C>%;3:21p0=1pQHE1pUDJ1pV<K1").
Proof.
induction LB as [|x r IH]; intros Hi; [contradiction|]. cbn [lb_remove length]. destruct (Z.eqb_spec (fst x) u) as [E|NE]; [lia|].
destruct Hi as [->|Hi]; [exfalso; apply NE; reflexivity|]. cbn [length]. specialize (IH Hi). lia.
Qed.
Lemma art_lb_remove_comm : ltac2:(TCodec.tc2 tcn__JbtWrapFreeC "F'G'8'=%1233%311&B'Ar3r2%33921%511&Q4r4%2215%3271%4287%5241%;3=31p081pQH?1pV>D1pV<E1").
Proof.
intros u v LB N. induction LB as [|x r IH]; [reflexivity|]. cbn [lb_remove].
destruct (Z.eqb_spec (fst x) u) as [Eu|Nu]; destruct (Z.eqb_spec (fst x) v) as [Ev|Nv]; cbn [lb_remove].
- exfalso. apply N. rewrite <- Eu, <- Ev. reflexivity.
- destruct (Z.eqb_spec (fst x) u) as [_|X]; [reflexivity|contradiction].
- destruct (Z.eqb_spec (fst x) v) as [_|X]; [reflexivity|contradiction].
- destruct (Z.eqb_spec (fst x) u) as [X|_]; [contradiction|]. destruct (Z.eqb_spec (fst x) v) as [X|_]; [contradiction|]. rewrite IH. reflexivity.
Qed.
Lemma art_lb_remove_nodup : ltac2:(TCodec.tc2 tcn__JbtWrapFreeC "E'G'8'=%1233%311'R4&F&6%1288r1%447:21%62;1&Q4r3r2%3221%:4=@81%<2A1p071pQH?1pV<D1").
Proof.
induction LB as [|x r IH]; intros ND; [exact ND|]. cbn [lb_remove]. cbn [map] in ND. apply NoDup_cons_iff in ND. destruct ND as (Hx & ND).
destruct (Z.eqb_spec (fst x) u) as [_|_]; [exact ND|]. cbn [map]. apply NoDup_cons_iff. split; [|exact (IH ND)].
intros Hi. apply Hx. apply in_map_iff in Hi. destruct Hi as (b & Eb & Hb). apply in_map_iff. exists b. split; [exact Eb|exact (art_lb_remove_in u r b Hb)].
Qed.
Section Credit.
Variable FSG : Type.
Section SE.
Local Abbreviation SEC_T_art_wfx_credit := (forall BUDGET rn (G : art_gs FSG) LB cr u n (kb : nat) k (d : bool), let G1 := art_gs_free G (rn_spb rn) k u n kb in
art_cls_ok 24 (g_cls FSG G 24) -> art_credit_ok FSG BUDGET rn G LB cr -> g_depot FSG G = Datatypes.S kb -> In (u, n) LB ->
art_credit_ok FSG BUDGET rn (if d then art_gs_drain G1 else G1) (lb_remove u LB) cr) (only parsing).
Variable BUDGET : ltac:(sec_ty2 constr:(SEC_T_art_wfx_credit) 0%nat 0%nat).
Variable rn : ltac:(sec_ty2 constr:(SEC_T_art_wfx_credit) 1%nat 0%nat).
Variable G : ltac:(sec_ty2 constr:(SEC_T_art_wfx_credit) 2%nat 0%nat).
Variable LB : ltac:(sec_ty2 constr:(SEC_T_art_wfx_credit) 3%nat 0%nat).
Variable cr : ltac:(sec_ty2 constr:(SEC_T_art_wfx_credit) 4%nat 0%nat).
Variable u : ltac:(sec_ty2 constr:(SEC_T_art_wfx_credit) 5%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_wfx_credit) 6%nat 0%nat).
Variable kb : ltac:(sec_ty2 constr:(SEC_T_art_wfx_credit) 7%nat 0%nat).
#[using="Type BUDGET rn G LB cr u n kb"] Lemma art_wfx_credit : ltac:(sec_stmt2 constr:(SEC_T_art_wfx_credit) 8%nat 0%nat).
Proof.
intros k d G1 OK (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8) Edep Hi.
pose proof (art_lb_remove_len u n LB Hi) as HLEN.
set (newb := art_free_newb (g_qt FSG G)). set (cl := g_cls FSG G 24) in *.
assert (Hev : 0 <= art_cost_sum (art_enq_events newb (rn_spb rn) cl) <= 2 ^ 19).
{ unfold art_enq_events. destruct newb; [exact (art_ca_cost (rn_spb rn) 24 cl ltac:(lia) OK)|cbn; lia]. }
assert (Elive : art_live (g_log FSG G ++ art_enq_events newb (rn_spb rn) cl) = art_live (g_log FSG G)).
{ unfold art_enq_events. destruct newb; [apply art_live_ca_events|rewrite app_nil_r; reflexivity]. }
assert (Enq : art_nq (art_qt_add (g_qt FSG G) (rn_spb rn + 24 * 2 ^ 32 + 16 * art_ca_cptr 24 cl) (u - 16, n)) <= art_nq (g_qt FSG G) + 2).
{ rewrite art_qt_add_nq. destruct (art_free_newb (g_qt FSG G)); lia. }
assert (ESEC : length (g_sec FSG G1) = length (g_sec FSG G)). { unfold G1. cbn [art_gs_free g_sec]. destruct k; [reflexivity|apply art_sec_quar_length]. }
assert (ENQ2 : art_nq (g_qt FSG (if d then art_gs_drain G1 else G1) ++ g_qg FSG (if d then art_gs_drain G1 else G1)) <= art_nq (g_qt FSG G ++ g_qg FSG G) + 2).
{ destruct d; cbn [art_gs_drain g_qt g_qg app]; unfold G1; cbn [art_gs_free g_qt g_qg]; fold cl; rewrite ?art_nq_app; rewrite ?art_nq_app in Enq; lia. }
assert (EQS : g_log FSG (if d then art_gs_drain G1 else G1) = g_log FSG G ++ art_enq_events newb (rn_spb rn) cl
/\ length (g_sec FSG (if d then art_gs_drain G1 else G1)) = length (g_sec FSG G)
/\ g_depot FSG (if d then art_gs_drain G1 else G1) = kb
/\ (forall c0, g_cls FSG (if d then art_gs_drain G1 else G1) c0 = if c0 =? 24 then art_enq_cls newb cl else g_cls FSG G c0)).
{ destruct d; cbn [art_gs_drain g_log g_sec g_depot g_cls]; (split; [reflexivity|]); (split; [exact ESEC|]); (split; [reflexivity|]); intros c0; reflexivity. }
destruct EQS as (Elog & Esec & Edp & Ecls).
pose proof (art_nq_nonneg (g_qt FSG G ++ g_qg FSG G)) as Hnq.
unfold art_credit_ok, art_nret in *. rewrite Elog, Esec, Edp, Elive, art_cost_sum_app. rewrite Edep in C6.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
intros c0 Hc0. destruct (C8 c0 Hc0) as (D1 & D2). rewrite Ecls. destruct (Z.eqb_spec c0 24) as [->|Ne]; [|split; lia]. fold cl in D1, D2.
unfold art_enq_cls. destruct newb; [|split; lia].
pose proof (art_pre_pop_len 24 cl ltac:(lia) OK) as HL. cbv zeta in HL. split.
- cbn [art_cls_pop cl_mu]. destruct (art_ca_pre_mu_cases 24 cl) as [(E & _)|(_ & _ & E)]; rewrite E; lia.
- destruct HL as [HL|HL]; lia.
Qed.
End SE.
End Credit.
Section ExitClient.
Variable L : asan_layout.
Hypothesis HLlo : hl_img_lo L = 0x10000.
Hypothesis HLhi : hl_img_hi L = 0x693000.
Hypothesis HLst : forall a, art_zone_statics a -> hl_rt_static L a.
Section SE.
Local Abbreviation SEC_T_art_wfc_client := (ltac2:(TCodec.tc2 tcn__JbtWrapFreeC "X4'QK'8'='G%2211%411&Q<%611'S2yR0%211';y8%511%311p051!p0>1&QLr=%211&QIr>r<r;r:r8%66584321&R5%13I54&R1r9%2271&B&S3r1%22K1%<11%511'Ar2%B11%G12%43M21p061pV@Q31&R3&Q4rC%22H1%43Q>:1'C'@&R7&6r3%23QEQE1%421A&R8&R6&>%13QJQJ6%3261%52G1%<271&Q=%13:5J%@231%Q>1=%Q411p031p0E1pTNR51pU2R51&QNrD%211%H21Q:&R;+2+R0%3221%H2Q?1%O261&R<+TP0%22QO1%Q221Q?%N2Q@R1%Q5221%QI11p01Fp091pTNRJ1+RPP0%Q:21QL+Vb\P0%Q72QN1%Q>231&QM%11QL%R411r?%11Q@%R711p041p081pTNS81&Q8&QOrF%211%411%QL21R>&Q5%QH231%QJ2RA1%R1241%@1R>%RF11p031pTNSF1z%R621R4%R222R5r5r4%R4221+Q?%QC2QB1%R=231r6%R9217&R0rL%211%RC241+TPPPRTP0%R?231%RF218%RI241r7%RC21;+@%QL2S01%RL231&R9+8rA%3221%RK2S61%S221:%S5271&Q6%11T0%S621H%S12T2?+1%R:221%611%S;2M1%S=261rG%11F%T311p041p0>1p0K1p0Q61p0Q=1p0Q?1pTNU81pU@U91pUBU:1%RJ2TKO%SJ2R?1%N2MTH%SF2TN1%S81@%SN221&Q2%SJ2Q65%R91D%R;11%44:31R6%T5261%T62;1%T62NU4&4rH%23UH1L%TA3UITL1rK%RD11%RF11&Q9%11TL%T@231&Q:&Q;%11U0%311%T?261%T@29RI%TG221%TC2RC4%TJ221%TK2:1p0A1pU8V;1rB%SO21SN%TO21UA%TK2UB3%U2221&S1%12V?U@%S;11(3%11V>%UE3V>31%UL11p081pTNVL1rJ%UB2R=1rI%V>6Q321Q6SETH&Q7vJrE%382Q665ETB1TL%UD251p0:1p0I1p0Q@1p0QB1p0R01p0SE1p0T41p0TC1p0U81p0V51p0VC1p0VG1p0VJ1p0W21pUHWD1pUDWE1pV<WF1pT6WG1pQDW:1pR2W=1pR0W>1p4WI1p2WJ1pQJWI1pQBWJ1pQHWM1pUNX31")) (only parsing).
Variable rn : ltac:(sec_ty2 constr:(SEC_T_art_wfc_client) 0%nat 0%nat).
Variable LB : ltac:(sec_ty2 constr:(SEC_T_art_wfc_client) 1%nat 0%nat).
Variable FF : ltac:(sec_ty2 constr:(SEC_T_art_wfc_client) 2%nat 0%nat).
Variable LK : ltac:(sec_ty2 constr:(SEC_T_art_wfc_client) 3%nat 0%nat).
Variable A : ltac:(sec_ty2 constr:(SEC_T_art_wfc_client) 4%nat 0%nat).
Variable A' : ltac:(sec_ty2 constr:(SEC_T_art_wfc_client) 5%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_art_wfc_client) 6%nat 0%nat).
Variable M1 : ltac:(sec_ty2 constr:(SEC_T_art_wfc_client) 7%nat 0%nat).
Variable FPT : ltac:(sec_ty2 constr:(SEC_T_art_wfc_client) 8%nat 0%nat).
Variable Sp : ltac:(sec_ty2 constr:(SEC_T_art_wfc_client) 9%nat 0%nat).
Variable u : ltac:(sec_ty2 constr:(SEC_T_art_wfc_client) 10%nat 0%nat).
Variable n : ltac:(sec_ty2 constr:(SEC_T_art_wfc_client) 11%nat 0%nat).
Variable qr : ltac:(sec_ty2 constr:(SEC_T_art_wfc_client) 12%nat 0%nat).
#[using="HLlo HLhi HLst rn LB FF LK A A' M M1 FPT Sp u n qr"] Lemma art_wfc_client : ltac:(sec_stmt2 constr:(SEC_T_art_wfc_client) 13%nat 0%nat).
Proof.
intros ROK CLI INC GRW FRF NFPB NFPS NFPI NFS NSH (U1 & U2 & Uf) Hq0 FSIN SCR.
pose proof ROK as ROK'. rok_open14 ROK'. geo_open GEO.
destruct CLI as (CB & CND & CSA1 & CSA2 & CS1 & CS2 & CS3 & CS4 & CS5 & CS6 & CSI & CSP & CS16).
assert (EQ : forall a, 0 <= a < 2 ^ 64 -> ~ FPT a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
{ intros a Ha N. apply FRF. rewrite art_u_lit by lia. exact N. }
assert (HIeq : ahl_ceil (rn_ar rn) = rn_HI rn) by reflexivity.
assert (SHA : forall a0 n0, shadow_allowed A a0 n0 -> shadow_allowed A' a0 n0).
{ intros a0 n0 SA x Hx. apply (art_page_allowedb_incl A A' _ INC). exact (SA x Hx). }
assert (SHB : forall b, In b (lb_remove u LB) -> 0 <= fst b -> fst b + snd b <= rn_HI rn -> 0 < snd b -> HAJ.shadow_blkR M (fst b) (snd b) -> HAJ.shadow_blkR M1 (fst b) (snd b)).
{ intros b Hb Hb0 Hb1 Hnb SB0.
assert (T : forall j, 0 <= j -> (j < snd b / 8 \/ (j = snd b / 8 /\ snd b mod 8 <> 0)) -> forall v, byte_at M (HeapIfaceA.S (fst b) + j) v -> byte_at M1 (HeapIfaceA.S (fst b) + j) v).
{ intros j Hj0 Hj v Bt.
pose proof (art_S_blk_hi (fst b) (snd b) j Hnb Hj) as H1. pose proof (art_S_ge (fst b) 0 ltac:(lia)) as H0. pose proof (art_S_lt (fst b + snd b - 1) (2 ^ 44) ltac:(clear - Hb1 G2; lia)) as H2.
apply (art_byte_at_eq M M1); [|exact Bt]. apply EQ; [clear - H0 H1 H2 Hj0; lia|]. apply (NFPB b _ Hb). right. unfold in_shadow_of. clear - H1 Hj0. lia. }
exact (shadow_blkR_tby M M1 (fst b) (snd b) Hnb T SB0). }
split.
-
unfold art_client_ok. split; [|split; [|split; [exact (SHA _ _ CSA1)|split; [exact (SHA _ _ CSA2)|repeat split; first [assumption|exact (SHA _ _ CSI)|lia]]]]].
+ intros b Hb. pose proof (art_lb_remove_in u LB b Hb) as Hb'. destruct (CB b Hb') as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12).
split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|]. split; [exact B5|]. split; [exact B6|].
split. { intros i Hi. apply GRW. exact (B7 i Hi). }
split; [apply SHB; [exact Hb|clear - B1; lia|rewrite HIeq in B5; exact B5|exact B4|exact B8]|]. split; [exact (SHA _ _ B9)|].
split. { intros b' Hb2. apply B10. apply NoDup_ListNoDup in CND. pose proof (art_lb_remove_gone u LB b CND Hb) as Nu.
rewrite (art_lb_remove_comm u (fst b) LB ltac:(intros E; apply Nu; symmetry; exact E)) in Hb2. exact (art_lb_remove_in u _ b' Hb2). }
split; [exact B11|exact B12].
+ apply NoDup_ListNoDup. apply art_lb_remove_nodup. apply NoDup_ListNoDup. exact CND.
-
split.
+ intros a Ha CLa. apply EQ; [exact Ha|]. unfold aclient, aclient_g in CLa.
destruct CLa as [(b & Hb & Hr)|[((C1 & C2) & C3)|[((C1 & C2) & C3)|[(f & Hf & R1 & R2)|[SH|[(f & Hf & SH)|(b & Hb & SH)]]]]]].
* apply (NFPB b a Hb). left. exact Hr.
* apply NFPS; [rewrite HIeq in C1; clear - C1 C2; lia|exact C3].
* rewrite HLlo in C1. rewrite HLhi in C2. apply NFPI; [lia|]. intros D. apply C3. apply HLst. exact D.
* destruct (FSIN f (in_or_app _ _ _ (or_introl Hf))) as (F1 & F2 & _). apply NFS. clear - R1 F1 F2. lia.
* apply (NSH (ahl_ceil (rn_ar rn)) (2 ^ 47 - ahl_ceil (rn_ar rn)) a); [rewrite HIeq; clear - G1; lia|rewrite HIeq; clear - G2; lia|clear; lia|rewrite HIeq; right; clear - Kend; lia|rewrite HIeq; right; exact U2|exact SH].
* destruct (FSIN f (in_or_app _ _ _ (or_introl Hf))) as (F1 & F2 & F3). unfold apart, FS_BYTES in *.
apply (NSH (ff_addr f) (ff_bytes (ff_class f)) a); [clear - F1 Flo; lia|exact F3|clear - F2 Fhi G2; lia|clear - F1 F2 Afkb; lia|clear - F1 F2 Uf Hq0; lia|exact SH].
* apply (NFPB b a Hb). right. exact SH.
+ intros a Ha. apply GRW. exact (SCR a Ha).
Qed.
End SE.
End ExitClient.
