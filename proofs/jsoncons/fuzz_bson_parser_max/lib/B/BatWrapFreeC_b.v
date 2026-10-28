(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatSim StoreOk Hoare AsanAcct HeapIface HeapIfaceA HeapIfaceABx As0Tables
     ArtMem ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCellEx_b BatCls_b BatFp_b BatClsRep_b BatCARSpec_b BatAlloc3Pure_b BatDepotA_b BatDepot_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtBridge. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatInv_b BatInvMallocPure_b BatInvMalloc_b BatFxQ_b BatFxBatch2_b BatFxBatch3_b BatFreeTop3_b
     BatInvFreePure_b BatInvFree_b BatInvDrain_b BatLift_b BatWrapPure_b BatWrapKit_b BatWrapMallocH_b BatWrapMallocX_b BatWrapMallocC_b BatIfaceLaws_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx ShadowRLawsB.      (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Lemma art_out_dec : forall W x, {art_out W x} + {~ art_out W x}.
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
  /\ (forall a, 0x10000 <= a < 0x696000 -> ~ art_zone_statics a -> ~ FPT a)
  /\ (forall a, ar_fs (rn_ar rn) <= a < ar_fs (rn_ar rn) + FS_BYTES -> ~ FPT a)
  /\ (forall a, rn_dtls rn <= a < rn_dtls rn + 4096 -> ~ FPT a)
  /\ (forall a, rn_t rn + 72 <= a < rn_t rn + 80 -> ~ FPT a)
  /\ (forall lo len a, 0 <= lo -> 0 < len -> lo + len <= 2 ^ 47 -> (lo + len <= rn_kbase rn \/ rn_kbase rn + 0x2000011000 <= lo) ->
        (lo + len <= u - 16 \/ u + 8 * qr <= lo) -> HeapIfaceA.S lo <= a <= HeapIfaceA.S (lo + len - 1) -> ~ FPT a)
  /\ (0x696000 <= u - 16 /\ u + 8 * qr <= rn_HI rn /\ apart (u - 16) (16 + 8 * qr) (ar_fs (rn_ar rn)) FS_BYTES).

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

(* [comment removed for export] *)
#[using="b1 cl24 lastb REP Hin Eu Hn Hqr Hb1 Hty Cn KIND HS Emu Edep OUT LIVE LIVE2 LIVE3 OKpre Hother"] Lemma art_wf_pkg_fpl :
  art_alloc_rep_b FSG (2 ^ 29) rn Gfr (lb_remove u LB) M10
  /\ art_batches_bytes (g_qt FSG Gfr) = art_batches_bytes qtl + n + (if newb then 8192 else 0)
  /\ mem_grows M M10
  /\ (forall x : word, ~ art_free_fpl FSG rn G Sp u q16 qr km (U x) -> M10 x = M x)
  /\ (forall b0 a, In b0 (lb_remove u LB) -> (fst b0 <= a < fst b0 + snd b0 \/ in_shadow_of (fst b0) (snd b0) a) -> ~ art_free_fpl FSG rn G Sp u q16 qr km a)
  /\ (forall a, rn_HI rn <= a < 2 ^ 64 -> ~ (Sp - 4096 <= a < Sp) -> ~ art_free_fpl FSG rn G Sp u q16 qr km a)
  /\ (forall a, 0x10000 <= a < 0x696000 -> ~ art_zone_statics a -> ~ art_free_fpl FSG rn G Sp u q16 qr km a)
  /\ (forall a, ar_fs (rn_ar rn) <= a < ar_fs (rn_ar rn) + FS_BYTES -> ~ art_free_fpl FSG rn G Sp u q16 qr km a)
  /\ (forall a, rn_dtls rn <= a < rn_dtls rn + 4096 -> ~ art_free_fpl FSG rn G Sp u q16 qr km a)
  /\ (forall a, rn_t rn + 72 <= a < rn_t rn + 80 -> ~ art_free_fpl FSG rn G Sp u q16 qr km a)
  /\ (forall lo len a, 0 <= lo -> 0 < len -> lo + len <= 2 ^ 47 -> (lo + len <= rn_kbase rn \/ rn_kbase rn + 0x2000011000 <= lo) ->
        (lo + len <= u - 16 \/ u + 8 * qr <= lo) -> HeapIfaceA.S lo <= a <= HeapIfaceA.S (lo + len - 1) -> ~ art_free_fpl FSG rn G Sp u q16 qr km a)
  /\ (0x696000 <= u - 16 /\ u + 8 * qr <= rn_HI rn /\ apart (u - 16) (16 + 8 * qr) (ar_fs (rn_ar rn)) FS_BYTES).
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
#[using="b1 qtl cl24 newb lastb REP Hin Eu Hn Hqr Hb1 Hty Cn KIND HS Emu Edep OUT LIVE LIVE2 LIVE3 OKpre Hother"] Lemma art_wf_pkg2 : forall (M' : word -> option byte) ft lt fg lg,
  g_qt FSG Gfr <> [] -> art_batch_list M10 (g_qt FSG Gfr) ft lt -> cellA M10 (0x13c8b0 + 168) 8 fg -> art_batch_list M10 (g_qg FSG Gfr) fg lg ->
  art_batches_bytes (g_qg FSG Gfr) + art_batches_bytes (g_qt FSG Gfr) <= 2 ^ 28 ->
  mem_grows M10 M' -> art_agree (art_drain_W FSG rn Gfr (Sp - 2208) lg) M10 M' ->
  (cellA M' (rn_t rn + 80) 8 0 /\ cellA M' (rn_t rn + 80 + 8) 8 0 /\ cellA M' (rn_t rn + 80 + 16) 8 0 /\ cellA M' (rn_t rn + 80 + 24) 8 0
   /\ cellA M' (0x13c8b0 + 160) 8 (Z.of_nat (length (g_qg FSG Gfr)) + Z.of_nat (length (g_qt FSG Gfr))) /\ cellA M' (0x13c8b0 + 176) 8 lt
   /\ cellA M' (0x13c8b0 + 184) 8 (art_batches_bytes (g_qg FSG Gfr) + art_batches_bytes (g_qt FSG Gfr)) /\ cellA M' (0x13c8b0 + 152) 4 0
   /\ (Z.of_nat (length (g_qg FSG Gfr)) = 0 -> cellA M' (0x13c8b0 + 168) 8 ft) /\ (Z.of_nat (length (g_qg FSG Gfr)) <> 0 -> cellA M' lg 8 ft)) ->
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

(* [comment removed for export] *)
Lemma art_enq_events_in_fp : forall newb sp t spb ris qs km b L B cntB cl z, art_cls_ok 24 cl -> cl_mu cl = 262144 * km ->
  (newb = true -> cl_cache cl = [] -> art_cls_needs_populate 24 cl = true -> art_cls_mfa' cl (Z.of_nat (length (cl_free cl)) + art_cls_new 24 cl) <= 536870912) ->
  in_ev_ranges (art_enq_events newb spb cl) z -> art_enq_fp newb sp t spb ris qs km b L B cntB z.
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

#[using="fx"] Lemma art_wfc_mem : forall rn (G : art_gs FSG) (A A' : list (Z * Z)) (M M1 : word -> option byte) (model model' : Model) (log' : list aev)
    (Sp u n q16 qr km : Z) (kb : nat) (k : art_fk) (d : bool) (lg : Z),
  let cl := g_cls FSG G 24 in
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
                        \/ rn_spb rn + 24 * 2 ^ 32 + 3758096384 <= U x < rn_spb rn + 24 * 2 ^ 32 + 3758096384 + cl_mfa cl') -> bhid A' model' x = false).
Proof.
  intros rn G A A' M M1 model model' log' Sp u n q16 qr km kb k d lg cl newb cl' FPT ROK OK Emu Room Elog BH GR FR Wu Wfa.
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
    assert (D : forall a j, 0 <= a -> a + j < 2 ^ 64 -> 0x696000 <= a -> wrA (mrestrict (bhid A' model') M1) a j -> a <= U x < a + j -> mrestrict (bhid A' model') M1 x <> None).
    { intros a j Ha Hj Hoff Wr Hx. pose proof (art_wr_wview ASEGS _ a j Ha Hj Wr x Hx) as V. rewrite art_wview_off in V by lia. exact V. }
    destruct Hev as [<-|Hev].
    + cbn [art_ev_range fst snd] in Hz. apply (D (rn_spb rn + 24 * 2 ^ 32) (cl_mu cl') ltac:(lia) ltac:(lia) ltac:(lia) Wu). rewrite Emu', Emp. lia.
    + match type of Hev with In _ (if ?bb then _ else _) => destruct bb end; [destruct Hev|]. destruct Hev as [<-|[]]. cbn [art_ev_range fst snd] in Hz.
      apply (D (rn_spb rn + 24 * 2 ^ 32 + 3758096384) (cl_mfa cl') ltac:(lia) ltac:(lia) ltac:(lia) Wfa). rewrite Emfa', Emf. lia.
Qed.
End ExitMem.

Section LazyCredit.
Variable FSG : Type.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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

#[using="Type"] Lemma art_eager_ok_remove : forall (LB : list (Z * Z)) A lazy A' lazy' u,
  art_eager_ok LB A lazy -> A_wf A' ->
  (forall x : word, page_in_ranges (page_base x) lazy' = true -> page_in_ranges (page_base x) lazy = true) ->
  art_eager_ok (lb_remove u LB) A' lazy'.
Proof.
  intros LB A lazy A' lazy' u (AW & EG) AW' B5. split; [exact AW'|]. intros b x Hb Hx.
  destruct (page_in_ranges (page_base x) lazy') eqn:E; [|reflexivity]. pose proof (B5 x E) as E0. rewrite (EG b x (art_lb_remove_in u LB b Hb) Hx) in E0. discriminate E0.
Qed.
End LazyCredit.

(* [comment removed for export] *)
Lemma art_lb_remove_len : forall u n (LB : list (Z * Z)), In (u, n) LB -> (length (lb_remove u LB) + 1 = length LB)%nat.
Proof.
  induction LB as [|x r IH]; intros Hi; [contradiction|]. cbn [lb_remove length]. destruct (Z.eqb_spec (fst x) u) as [E|NE]; [lia|].
  destruct Hi as [->|Hi]; [exfalso; apply NE; reflexivity|]. cbn [length]. specialize (IH Hi). lia.
Qed.
Lemma art_lb_remove_comm : forall u v (LB : list (Z * Z)), u <> v -> lb_remove v (lb_remove u LB) = lb_remove u (lb_remove v LB).
Proof.
  intros u v LB N. induction LB as [|x r IH]; [reflexivity|]. cbn [lb_remove].
  destruct (Z.eqb_spec (fst x) u) as [Eu|Nu]; destruct (Z.eqb_spec (fst x) v) as [Ev|Nv]; cbn [lb_remove].
  - exfalso. apply N. rewrite <- Eu, <- Ev. reflexivity.
  - destruct (Z.eqb_spec (fst x) u) as [_|X]; [reflexivity|contradiction].
  - destruct (Z.eqb_spec (fst x) v) as [_|X]; [reflexivity|contradiction].
  - destruct (Z.eqb_spec (fst x) u) as [X|_]; [contradiction|]. destruct (Z.eqb_spec (fst x) v) as [X|_]; [contradiction|]. rewrite IH. reflexivity.
Qed.
Lemma art_lb_remove_nodup : forall u (LB : list (Z * Z)), List.NoDup (map fst LB) -> List.NoDup (map fst (lb_remove u LB)).
Proof.
  induction LB as [|x r IH]; intros ND; [exact ND|]. cbn [lb_remove]. cbn [map] in ND. apply NoDup_cons_iff in ND. destruct ND as (Hx & ND).
  destruct (Z.eqb_spec (fst x) u) as [_|_]; [exact ND|]. cbn [map]. apply NoDup_cons_iff. split; [|exact (IH ND)].
  intros Hi. apply Hx. apply in_map_iff in Hi. destruct Hi as (b & Eb & Hb). apply in_map_iff. exists b. split; [exact Eb|exact (art_lb_remove_in u r b Hb)].
Qed.

Section Credit.
Variable FSG : Type.

#[using="Type"] Lemma art_wfx_credit : forall BUDGET rn (G : art_gs FSG) LB cr u n (kb : nat) k (d : bool),
  let G1 := art_gs_free G (rn_spb rn) k u n kb in
  art_cls_ok 24 (g_cls FSG G 24) -> art_credit_ok FSG BUDGET rn G LB cr -> g_depot FSG G = Datatypes.S kb -> In (u, n) LB ->
  art_credit_ok FSG BUDGET rn (if d then art_gs_drain G1 else G1) (lb_remove u LB) cr.
Proof.
  intros BUDGET rn G LB cr u n kb k d G1 OK (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8) Edep Hi.
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
End Credit.

Section ExitClient.
Variable L : asan_layout.
Hypothesis HLlo : hl_img_lo L = 0x10000.
Hypothesis HLhi : hl_img_hi L = 0x696000.
Hypothesis HLst : forall a, art_zone_statics a -> hl_rt_static L a.

#[using="HLlo HLhi HLst"] Lemma art_wfc_client : forall rn LB FF LK (A A' : list (Z * Z)) (M M1 : word -> option byte) (FPT : Z -> Prop) (Sp u n qr : Z),
  art_run_ok rn -> art_client_ok rn LB FF LK A M -> incl A A' -> mem_grows M M1 ->
  (forall x : word, ~ FPT (U x) -> M1 x = M x) ->
  (forall b0 a, In b0 (lb_remove u LB) -> (fst b0 <= a < fst b0 + snd b0 \/ in_shadow_of (fst b0) (snd b0) a) -> ~ FPT a) ->
  (forall a, rn_HI rn <= a < 2 ^ 64 -> ~ (Sp - 4096 <= a < Sp) -> ~ FPT a) ->
  (forall a, 0x10000 <= a < 0x696000 -> ~ art_zone_statics a -> ~ FPT a) ->
  (forall a, ar_fs (rn_ar rn) <= a < ar_fs (rn_ar rn) + FS_BYTES -> ~ FPT a) ->
  (forall lo len a, 0 <= lo -> 0 < len -> lo + len <= 2 ^ 47 -> (lo + len <= rn_kbase rn \/ rn_kbase rn + 0x2000011000 <= lo) ->
        (lo + len <= u - 16 \/ u + 8 * qr <= lo) -> HeapIfaceA.S lo <= a <= HeapIfaceA.S (lo + len - 1) -> ~ FPT a) ->
  (0x696000 <= u - 16 /\ u + 8 * qr <= rn_HI rn /\ apart (u - 16) (16 + 8 * qr) (ar_fs (rn_ar rn)) FS_BYTES) -> 1 <= qr ->
  (forall f, In f (FF ++ LK) -> ar_fs (rn_ar rn) <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= ar_fs (rn_ar rn) + FS_BYTES /\ 0 < ff_bytes (ff_class f)) ->
  (forall a, Sp - 4096 <= a < Sp -> M (Z_to_bv 64 a) <> None) ->
  art_client_ok rn (lb_remove u LB) FF LK A' M1 /\ aheap_pres L (rn_ar rn) (lb_remove u LB) FF Sp 4096 M M1.
Proof.
  intros rn LB FF LK A A' M M1 FPT Sp u n qr ROK CLI INC GRW FRF NFPB NFPS NFPI NFS NSH (U1 & U2 & Uf) Hq0 FSIN SCR.
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
  - (* [comment removed for export] *)
    unfold art_client_ok. split; [|split; [|split; [exact (SHA _ _ CSA1)|split; [exact (SHA _ _ CSA2)|repeat split; first [assumption|exact (SHA _ _ CSI)|lia]]]]].
    + intros b Hb. pose proof (art_lb_remove_in u LB b Hb) as Hb'. destruct (CB b Hb') as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12).
      split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|]. split; [exact B5|]. split; [exact B6|].
      split. { intros i Hi. apply GRW. exact (B7 i Hi). }
      split; [apply SHB; [exact Hb|clear - B1; lia|rewrite HIeq in B5; exact B5|exact B4|exact B8]|]. split; [exact (SHA _ _ B9)|].
      split. { intros b' Hb2. apply B10. apply NoDup_ListNoDup in CND. pose proof (art_lb_remove_gone u LB b CND Hb) as Nu.
               rewrite (art_lb_remove_comm u (fst b) LB ltac:(intros E; apply Nu; symmetry; exact E)) in Hb2. exact (art_lb_remove_in u _ b' Hb2). }
      split; [exact B11|exact B12].
    + apply NoDup_ListNoDup. apply art_lb_remove_nodup. apply NoDup_ListNoDup. exact CND.
  - (* [comment removed for export] *)
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
End ExitClient.
