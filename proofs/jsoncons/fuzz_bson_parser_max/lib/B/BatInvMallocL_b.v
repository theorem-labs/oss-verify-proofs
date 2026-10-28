(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatSim StoreOk AsanAcct HeapIface HeapIfaceA HeapIfaceABx As0Tables
     ArtMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatAllocG_b BatPoison_b BatRzLog_b BatAllocA_b BatInitCache_b BatPopulate1_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatFp_b BatClsRep_b BatClsGfa2_b BatCellEx_b BatByteCell_b BatCellJoin_b
     BatCARSpec_b BatAlloc3Pure_b BatDepotA_b BatDepot_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtBridge. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatAllocate3_b BatSecAllocPost_b BatSecRSpec_b BatAllocate3L_b BatMallocTop3L_b BatInv_b BatInvMallocPure_b BatInvMallocFp_b BatInvMalloc_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx ShadowRLawsB.      (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
Definition art_gs_malloc_sec {FSG : Type} (G : art_gs FSG) (parr msz r u n : Z) (kb : nat) : art_gs FSG :=
  GS FSG (g_log FSG G ++ art_sec_events msz r parr (Z.of_nat (length (g_sec FSG G))) (g_sec_committed FSG G)) (g_inited FSG G)
     (g_cls FSG G) (g_st FSG G) (g_sec FSG G ++ [SEC r msz u n false]) true (g_qt FSG G) (g_qg FSG G) kb (g_ia FSG G) (g_fs FSG G).

(* [comment removed for export] *)
Definition art_malloc_out_sec (rn : art_run) (M M' : word -> option byte) (S n rz qz qn m8 nd msz r nch : Z) (committed : bool) (kb : nat) (b1 : Z) : Prop :=
  let ab := 4096 + r in
  mem_grows M M'
  /\ art_agree (art_malloc3L_fp S (rn_t rn) (rn_parr rn) nch r msz (rn_l2 rn) (rn_blk rn) committed) M M'
  /\ (forall (x : word) b, art_shlo r <= U x < art_shhi r msz -> ~ (BatPoison_b.SB + r / 8 <= U x < BatPoison_b.SB + r / 8 + msz / 8) -> M x = Some b -> M' x = Some b)
  /\ DInvD (rn_l2 rn) (rn_blk rn) kb M'
  /\ wrA M' r msz /\ wrA M' (BatPoison_b.SB + r / 8) (msz / 8)
  /\ cellA M' r 8 r /\ cellA M' (r + 8) 8 msz /\ cellA M' (r + 16) 8 nd /\ cellA M' (r + 24) 8 nch
  /\ 0 <= b1 < 256 /\ b1 mod 4 = 1
  /\ cellA M' (ab + rz - 16) 1 2 /\ cellA M' (ab + rz - 15) 1 b1 /\ cellA M' (ab + rz - 14) 2 0 /\ cellA M' (ab + rz - 12) 4 n
  /\ (forall j, 0 <= j < qn -> cellA M' (2147450880 + ab / 8 + 2 * qz + j) 1 0) /\ (m8 <> 0 -> cellA M' (2147450880 + ab / 8 + 2 * qz + qn) 1 m8)
  /\ cellA M' 0x13c618 8 4096 /\ cellA M' (0x13c618 + 8) 8 (rn_parr rn) /\ cellA M' (0x13c618 + 16) 8 (rn_parr rn) /\ cellA M' (0x13c618 + 56) 8 (nch + 1)
  /\ cellA M' (0x13c618 + 48) 8 16384 /\ cellA M' (0x13c618 + 616) 4 0
  /\ cellA M' (rn_parr rn + 8 * nch) 8 r /\ wrA M' (rn_parr rn) 131072.

Lemma art_live_sec_events : forall log msz r parr nch cm, art_live (log ++ art_sec_events msz r parr nch cm) = (r, msz) :: art_live log.
Proof.
  intros log msz r parr nch cm. unfold art_sec_events. destruct cm.
  - rewrite art_live_snoc. reflexivity.
  - change ([AMmapNull msz r; AMmapFixed (parr + 8 * nch) 131072]) with ([AMmapNull msz r] ++ [AMmapFixed (parr + 8 * nch) 131072]).
    rewrite app_assoc, !art_live_snoc. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma art_run_ok_tail : forall rn, art_run_ok rn ->
  0x696000 <= rn_l2 rn /\ 0x696000 <= rn_blk rn /\ apart (ar_fs (rn_ar rn)) FS_BYTES (rn_kbase rn) 0x2000011000
  /\ 4096 <= rn_dtls rn /\ rn_dtls rn + 4096 <= rn_HI rn /\ (rn_dtls rn + 4096 <= 0x10000 \/ 0x696000 <= rn_dtls rn) /\ app_mem (rn_dtls rn) 4096
  /\ apart (rn_dtls rn) 4096 (rn_t rn) 4096 /\ apart (rn_dtls rn) 4096 (rn_ctx rn) 4096 /\ apart (rn_dtls rn) 4096 (rn_kbase rn) 0x2000011000
  /\ apart (rn_dtls rn) 4096 (rn_parr rn) (2 ^ 23) /\ apart (rn_dtls rn) 4096 (rn_l2 rn) (2 ^ 20) /\ apart (rn_dtls rn) 4096 (rn_blk rn) (2 ^ 23)
  /\ apart (rn_dtls rn) 4096 (ar_fs (rn_ar rn)) FS_BYTES
  /\ apart (rn_t rn) 4096 (rn_kbase rn) 0x2000011000 /\ apart (rn_ctx rn) 4096 (rn_kbase rn) 0x2000011000
  /\ apart (rn_l2 rn) (2 ^ 20) (rn_kbase rn) 0x2000011000 /\ apart (rn_parr rn) (2 ^ 23) (rn_kbase rn) 0x2000011000
  /\ 0x10007fff8000 <= rn_kbase rn.
Proof. intros rn ROK. unfold art_run_ok in ROK. do 40 (destruct ROK as [_ ROK]). exact ROK. Qed.

Section RepL.
Variable FSG : Type.
Variables (rn : art_run) (G : art_gs FSG) (LB : list (Z * Z)) (M M' : word -> option byte).
Variables (Sp n rz qz rs qr qn m8 nd q msz r : Z) (kb : nat) (b1 : Z).
Let nch := Z.of_nat (length (g_sec FSG G)).
Let cm := g_sec_committed FSG G.
Let ab := 4096 + r.
Let u := ab + rz.
Let WL := art_malloc3L_fp Sp (rn_t rn) (rn_parr rn) nch r msz (rn_l2 rn) (rn_blk rn) cm.

Hypothesis REP : art_alloc_rep FSG rn G LB M.
Hypothesis Hn : 8 <= n < 2 ^ 28.
Hypothesis Erz16 : rz = 16 * qz.
Hypothesis Hqz : 2 <= qz <= 128.
Hypothesis En : n = 8 * qn + m8.
Hypothesis Hm8 : 0 <= m8 <= 7.
Hypothesis Ers : rs = 8 * qr.
Hypothesis Hrs : n <= rs <= n + 7.
Hypothesis Hsec : 65536 < rs + rz.
Hypothesis End : nd = rs + rz + rz.
Hypothesis Hq : 4096 * (q - 1) < nd <= 4096 * q.
Hypothesis Emsz : msz = 4096 * q + 4096.
Hypothesis HS : rn_HI rn + 4096 <= Sp - 4096.
Hypothesis Edep : g_depot FSG G = Datatypes.S kb.
Hypothesis GRANT : art_sec_grant3 (rn_HI rn) (rn_t rn) (rn_ctx rn) (rn_parr rn) (rn_spb rn) (rn_l2 rn) (rn_blk rn) msz r.
Hypothesis GLIVE : forall p, In p (art_live (g_log FSG G)) -> apart r msz (fst p) (snd p).
Hypothesis OUT : art_malloc_out_sec rn M M' Sp n rz qz qn m8 nd msz r nch cm kb b1.
Hypothesis LIVE : forall p, In p (art_live (g_log FSG G)) ->
  0 < fst p /\ 0 < snd p /\ fst p + snd p <= rn_HI rn /\ (fst p + snd p <= 0x7fff7000 \/ 0x10007fff8000 <= fst p)
  /\ (forall o, In o (art_objs rn) -> apart (fst p) (snd p) (fst o) (snd o)).

#[local] Abbreviation G' := (art_gs_malloc_sec G (rn_parr rn) msz r u n kb).

(* [comment removed for export] *)
#[using="LB M qz rs qr kb u REP Erz16 Hqz Ers Hsec End Hq Emsz Edep GRANT"] Lemma art_lrep_num : 17 <= q /\ msz mod 4096 = 0 /\ 0 <= nch <= 16384 /\ ab + nd <= r + msz /\ 32 <= rz <= 2048 /\ 4096 <= r /\ r + msz <= rn_HI rn /\ 0x696000 <= r.
Proof.
  destruct GRANT as ((Hr4 & Hr & Hri & Hrm & _) & _).
  pose proof REP as (_ & _ & _ & _ & _ & SEC & _). destruct SEC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SLEN). fold nch in SLEN.
  split; [lia|]. split; [rewrite Emsz; replace (4096 * q + 4096) with ((q + 1) * 4096) by lia; apply Z_mod_mult|]. split; [unfold nch in *; lia|]. unfold ab. repeat split; lia.
Qed.

#[using="n rz qz qn m8 nd kb b1 OUT"] Lemma art_lrep_agree : art_agree WL M M'.
Proof. destruct OUT as (_ & AG & _). exact AG. Qed.

#[using="FSG rn G Sp n rz qz qn m8 nd msz r kb b1 nch cm OUT"] Lemma art_lrep_grows : mem_grows M M'.
Proof. destruct OUT as (GR & _). exact GR. Qed.

(* [comment removed for export] *)
#[using="FSG rn G LB M rz qz rs qr nd q kb nch ab u REP Erz16 Hqz Ers Hsec End Hq Emsz Edep GRANT"] Lemma art_lrep_sh : BatPoison_b.SB <= art_shlo r /\ art_shlo r <= BatPoison_b.SB + r / 8 /\ BatPoison_b.SB + r / 8 + msz / 8 <= art_shhi r msz /\ art_shhi r msz <= BatPoison_b.kHighMemBeg
                    /\ 8 * (r / 8) = r /\ 8 * (msz / 8) = msz.
Proof.
  destruct art_lrep_num as (Hq1 & Hm4 & _ & _ & _ & Hr & Hrm & _). destruct GRANT as ((Hr4 & _) & _).
  destruct REP as (ROK & _). rok_open ROK. geo_open GEO.
  destruct (art_sh_bounds r msz Hr4 Hm4 ltac:(lia) ltac:(lia) ltac:(lia)) as (S1 & S2 & S3 & S4 & _ & S6 & S7). repeat split; assumption.
Qed.

(* [comment removed for export] *)
#[local] Ltac wl_tac := unfold WL, art_malloc3L_fp; unfold apart in *; cbn [art_gap app fst snd]; unfold apart;
                        lazymatch goal with |- context [if ?c then _ else _] => destruct c | _ => idtac end; repeat split; try exact I; lia.

#[using="LB M rz qz rs qr nd q kb ab u REP Erz16 Hqz Ers Hsec End Hq Emsz HS Edep GRANT"] Lemma art_lgap_img : forall a k, 0 <= k -> (0x10000 <= a /\ a + k <= 0x13c618) \/ (0x13c8a8 <= a /\ a + k <= 0x211b08) \/ (0x661b28 <= a /\ a + k <= 0x696000) -> art_gap WL a k.
Proof.
  intros a k Hk Z. destruct art_lrep_num as (_ & _ & Hnch & _ & _ & Hr & Hrm & Hri). destruct art_lrep_sh as (S1 & _ & _ & S4 & _). unfold BatPoison_b.SB, BatPoison_b.kHighMemBeg in S1, S4.
  destruct REP as (ROK & _). pose proof (art_run_ok_tail rn ROK) as (Il2 & Iblk & _). rok_open ROK. geo_open GEO.
  set (lo := art_shlo r) in *. set (hi := art_shhi r msz) in *.
  clear - Hk Z Hnch Hri S1 HS G1 G9 Plo Il2 Iblk. wl_tac.
Qed.

#[using="LB M rz qz rs qr nd q kb ab u REP Erz16 Hqz Ers Hsec End Hq Emsz HS Edep GRANT"] Lemma art_lgap_thread : forall a k, 0 <= k -> rn_t rn <= a -> a + k <= rn_t rn + 4096 -> (a + k <= rn_t rn + 2800 \/ rn_t rn + 2912 <= a) -> art_gap WL a k.
Proof.
  intros a k Hk Ha Ha' Z. destruct art_lrep_num as (_ & _ & Hnch & _ & _ & Hr & Hrm & Hri). destruct art_lrep_sh as (S1 & _ & _ & S4 & _). unfold BatPoison_b.SB, BatPoison_b.kHighMemBeg in S1, S4.
  destruct GRANT as ((_ & _ & _ & _ & _ & Art & _) & _).
  destruct REP as (ROK & _). rok_open ROK. geo_open GEO.
  set (lo := art_shlo r) in *. set (hi := art_shhi r msz) in *.
  clear - Hk Ha Ha' Z Hnch S1 S4 HS G1 G7 G8 G9 G10 Art Apt Al2t Abt. wl_tac.
Qed.

#[using="LB M rz qz rs qr nd q kb ab u REP Erz16 Hqz Ers Hsec End Hq Emsz HS Edep GRANT"] Lemma art_lgap_ctx : forall a k, 0 <= k -> rn_ctx rn <= a -> a + k <= rn_ctx rn + 4096 -> art_gap WL a k.
Proof.
  intros a k Hk Ha Ha'. destruct art_lrep_num as (_ & _ & Hnch & _ & _ & Hr & Hrm & Hri). destruct art_lrep_sh as (S1 & _ & _ & S4 & _). unfold BatPoison_b.SB, BatPoison_b.kHighMemBeg in S1, S4.
  destruct GRANT as ((_ & _ & _ & _ & _ & _ & Arc & _) & _).
  destruct REP as (ROK & _). rok_open ROK. geo_open GEO.
  set (lo := art_shlo r) in *. set (hi := art_shhi r msz) in *.
  clear - Hk Ha Ha' Hnch S1 S4 HS G1 G13 G14 G15 G16 G18 Arc Apc Al2c Abc. wl_tac.
Qed.

#[using="LB M rz qz rs qr nd q kb ab u REP Erz16 Hqz Ers Hsec End Hq Emsz HS Edep GRANT"] Lemma art_lgap_kspace : forall a k, 0 <= k -> rn_spb rn <= a -> a + k <= rn_spb rn + 2 ^ 37 + 4096 -> art_gap WL a k.
Proof.
  intros a k Hk Ha Ha'. destruct art_lrep_num as (_ & _ & Hnch & _ & _ & Hr & Hrm & Hri). destruct art_lrep_sh as (S1 & _ & _ & S4 & _). unfold BatPoison_b.SB, BatPoison_b.kHighMemBeg in S1, S4.
  destruct GRANT as (_ & Ark & _).
  destruct REP as (ROK & _). rok_open ROK. geo_open GEO.
  set (lo := art_shlo r) in *. set (hi := art_shhi r msz) in *.
  clear - Hk Ha Ha' Hnch S1 S4 HS G1 G4 G6 Eris G11 Ark Apk Al2k Abk. wl_tac.
Qed.

#[using="LB M rz qz rs qr nd q kb ab u REP Erz16 Hqz Ers Hsec End Hq Emsz HS Edep GRANT GLIVE LIVE"] Lemma art_lgap_grant : forall p a k, 0 <= k -> In p (art_live (g_log FSG G)) -> fst p <= a -> a + k <= fst p + snd p -> art_gap WL a k.
Proof.
  intros p a k Hk Hp Ha Ha'. destruct (LIVE p Hp) as (L0 & L1 & L2 & L3 & LO). pose proof (GLIVE p Hp) as Arp'.
  pose proof (LO _ (or_introl eq_refl)) as At.
  pose proof (LO _ (or_intror (or_intror (or_intror (or_introl eq_refl))))) as Ap.
  pose proof (LO _ (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))) as Al.
  pose proof (LO _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))) as Ab.
  pose proof (LO _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))))) as Ai1.
  pose proof (LO _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))))))) as Ai2.
  pose proof (LO _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))))))) as Ai3.
  pose proof (LO _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))))))))) as Ai4.
  cbn [fst snd] in At, Ap, Al, Ab, Ai1, Ai2, Ai3, Ai4.
  destruct art_lrep_num as (_ & _ & Hnch & _ & _ & Hr & Hrm & Hri). destruct art_lrep_sh as (S1 & _ & _ & S4 & _). unfold BatPoison_b.SB, BatPoison_b.kHighMemBeg in S1, S4.
  destruct REP as (ROK & _). rok_open ROK. geo_open GEO.
  set (lo := art_shlo r) in *. set (hi := art_shhi r msz) in *.
  clear - Hk Ha Ha' L0 L1 L2 L3 Arp' At Ap Al Ab Ai1 Ai2 Ai3 Ai4 Hnch S1 S4 HS G1. wl_tac.
Qed.

(* [comment removed for export] *)
#[using="LB M rz qz rs qr nd q kb ab u REP Erz16 Hqz Ers Hsec End Hq Emsz HS Edep GRANT"] Lemma art_lgap_slot : forall i, 0 <= i < nch -> art_gap WL (rn_parr rn + 8 * i) 8.
Proof.
  intros i Hi. destruct art_lrep_num as (_ & _ & Hnch & _ & _ & Hr & Hrm & Hri). destruct art_lrep_sh as (S1 & _ & _ & S4 & _). unfold BatPoison_b.SB, BatPoison_b.kHighMemBeg in S1, S4.
  destruct GRANT as ((_ & _ & _ & _ & _ & _ & _ & Arp) & _).
  pose proof REP as (ROK & _ & _ & _ & _ & SEC & _). destruct SEC as (_ & _ & _ & _ & _ & _ & CMT & _).
  assert (Ecm : cm = true). { unfold cm. apply CMT. intros E. unfold nch in Hi. rewrite E in Hi. cbn in Hi. lia. }
  rok_open ROK. geo_open GEO. destruct Papp as (_ & Pap & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in Pap.
  set (lo := art_shlo r) in *. set (hi := art_shhi r msz) in *.
  unfold WL, art_malloc3L_fp. rewrite Ecm. clear - Hi Hnch S1 S4 HS G1 Plo Phi Pap Arp Apt Apl Apb. unfold apart in *. cbn [art_gap app fst snd]. unfold apart. repeat split; try exact I; lia.
Qed.

(* [comment removed for export] *)
#[using="FSG rn G LB Sp n rz qz rs qr qn m8 nd q kb b1 nch cm ab u REP Erz16 Hqz Ers Hsec End Hq Emsz HS Edep GRANT OUT"] Lemma art_lbyte_sh : forall a v, 0x7fff8000 <= a < 0x10007fff8000 -> ~ (BatPoison_b.SB + r / 8 <= a < BatPoison_b.SB + r / 8 + msz / 8) -> byte_at M a v -> byte_at M' a v.
Proof.
  intros a v Ha Nx B. unfold byte_at in *.
  destruct art_lrep_num as (_ & _ & Hnch & _ & _ & Hr & Hrm & Hri). destruct art_lrep_sh as (S1 & S2 & S3 & S4 & _).
  destruct OUT as (_ & AG & WIN & _).
  assert (Ua : U (Z_to_bv 64 a : word) = a) by (apply art_u_lit; lia).
  destruct (Z_le_dec (art_shlo r) a) as [L1|L1]; [destruct (Z_lt_dec a (art_shhi r msz)) as [L2|L2]|].
  - apply (WIN (Z_to_bv 64 a) (Z_to_bv 8 v)); [rewrite Ua; lia|rewrite Ua; exact Nx|exact B].
  - rewrite (AG (Z_to_bv 64 a)); [exact B|]. rewrite Ua. unfold BatPoison_b.SB, BatPoison_b.kHighMemBeg in *.
    destruct GRANT as ((_ & _ & _ & _ & APr & _) & _). unfold appmem, BatPoison_b.SB, BatPoison_b.kHighMemBeg in APr.
    destruct REP as (ROK & _). rok_open ROK. geo_open GEO. destruct Papp as (_ & Pap & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in Pap.
    set (lo := art_shlo r) in *. set (hi := art_shhi r msz) in *.
    unfold WL, art_malloc3L_fp. clear - Ha L2 Hnch APr HS G1 G10 Pap Al2s Abs. unfold apart in *. cbn [art_out fst snd]. destruct cm; repeat split; try exact I; lia.
  - rewrite (AG (Z_to_bv 64 a)); [exact B|]. rewrite Ua. unfold BatPoison_b.SB, BatPoison_b.kHighMemBeg in *.
    destruct GRANT as ((_ & _ & _ & _ & APr & _) & _). unfold appmem, BatPoison_b.SB, BatPoison_b.kHighMemBeg in APr.
    destruct REP as (ROK & _). rok_open ROK. geo_open GEO. destruct Papp as (_ & Pap & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in Pap.
    set (lo := art_shlo r) in *. set (hi := art_shhi r msz) in *.
    unfold WL, art_malloc3L_fp. clear - Ha L1 Hnch APr HS G1 G10 Pap Al2s Abs. unfold apart in *. cbn [art_out fst snd]. destruct cm; repeat split; try exact I; lia.
Qed.

(* [comment removed for export] *)
#[using="n rz qz qn m8 nd kb b1 OUT"] Lemma art_lcell : forall a (k : nat) v, art_gap WL a (Z.of_nat k) -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> cellA M a k v -> cellA M' a k v.
Proof. intros a k v Gp Ha Hk C. exact (art_cell_tr _ M M' a k v art_lrep_agree Gp Ha Hk C). Qed.

#[using="FSG rn G LB Sp n rz qz rs qr qn m8 nd q msz r kb b1 nch cm ab u WL REP Erz16 Hqz Ers Hsec End Hq Emsz HS Edep GRANT OUT"] Lemma art_lcell_img : forall a (k : nat) v, (0x10000 <= a /\ a + Z.of_nat k <= 0x13c618) \/ (0x13c8a8 <= a /\ a + Z.of_nat k <= 0x211b08) \/ (0x661b28 <= a /\ a + Z.of_nat k <= 0x696000) ->
  cellA M a k v -> cellA M' a k v.
Proof. intros a k v Z C. apply art_lcell; [apply art_lgap_img; lia|lia|lia|exact C]. Qed.

#[local] Ltac timg := apply art_lcell_img; [first [left; cbn; lia | right; left; cbn; lia | right; right; cbn; lia] | assumption].

(* [comment removed for export] *)
#[using="FSG G LB M Sp n rz qz rs qr qn m8 nd q msz r kb b1 nch cm ab u WL REP Erz16 Hqz Ers Hsec End Hq Emsz HS Edep GRANT OUT"] Lemma art_lrep_statics : art_rt_statics rn M'.
Proof.
  pose proof REP as (ROK & ST & _). rok_open ROK. pose proof GEO as GEO'. geo_open GEO'.
  destruct ST as (PC & L & T & RO & RZ & DR & TG & CS).
  unfold art_rt_statics.
  split. { unfold art_prim_consts in *. decompose [and] PC. repeat split; timg. }
  split. { unfold art_layout in *. decompose [and] L. repeat split; timg. }
  split. { destruct T as (C1 & C2 & C3 & C4 & C5 & RR). pose proof RR as (_ & _ & Hkey' & _). unfold art_tsd. split; [timg|]. split; [timg|].
           split; [apply art_lcell_img; [right; right; cbn; lia|exact C3]|]. split; [apply art_lcell_img; [right; right; cbn; lia|exact C4]|].
           split; [|exact RR]. apply art_lcell; [apply art_lgap_ctx; cbn; lia|lia|cbn; lia|exact C5]. }
  split. { unfold art_alloc_rodata in *. decompose [and] RO. repeat split; timg. }
  split. { unfold art_rz_rodata in *. decompose [and] RZ. repeat split; timg. }
  split. { unfold DRoD in *. decompose [and] DR. repeat split; timg. }
  split. { destruct TG as (GN & T1 & T2). split; [|split; timg].
           intros a Ha. assert (EU : U (Z_to_bv 64 a) = a) by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64); apply Z.mod_small; lia).
           rewrite (art_lrep_agree (Z_to_bv 64 a)); [exact (GN a Ha)|]. rewrite EU. apply (art_gap_out WL a 1 a); [apply art_lgap_img; [lia|left; lia]|lia]. }
  decompose [and] CS. repeat split; timg.
Qed.

(* [comment removed for export] *)
#[using="FSG G LB M Sp n rz qz rs qr qn m8 nd q msz r kb b1 nch cm ab u WL REP Erz16 Hqz Ers Hsec End Hq Emsz HS Edep GRANT OUT"] Lemma art_lrep_thread : art_rt_thread rn M'.
Proof.
  pose proof REP as (ROK & _ & TH & _). rok_open ROK. pose proof GEO as GEO'. geo_open GEO'.
  destruct TH as (Wt & C1 & C2 & C3 & C4 & C5 & C6 & C7).
  assert (TT : forall a (k : nat) v, rn_t rn <= a -> a + Z.of_nat k <= rn_t rn + 4096 -> (a + Z.of_nat k <= rn_t rn + 2800 \/ rn_t rn + 2912 <= a) -> cellA M a k v -> cellA M' a k v).
  { intros a k v Ha Hk Z C. apply art_lcell; [apply art_lgap_thread; lia|lia|lia|exact C]. }
  unfold art_rt_thread. split; [eapply wr_grows; [exact art_lrep_grows|exact Wt]|].
  split; [apply TT; [lia|cbn; lia|left; cbn; lia|exact C1]|]. split; [apply art_lcell; [apply art_lgap_ctx; cbn; lia|lia|cbn; lia|exact C2]|].
  split; [apply TT; [lia|cbn; lia|left; cbn; lia|exact C3]|]. split; [apply TT; [lia|cbn; lia|left; cbn; lia|exact C4]|].
  split; [apply TT; [lia|cbn; lia|left; cbn; lia|exact C5]|]. split; [apply TT; [lia|cbn; lia|right; cbn; lia|exact C6]|].
  apply art_lcell_img; [right; right; cbn; lia|exact C7].
Qed.

(* [comment removed for export] *)
#[using="M Sp qz qn m8 nd b1 nch cm OUT"] Lemma art_lrep_depot : art_rt_depot FSG rn G' M'.
Proof. unfold art_rt_depot. cbn [art_gs_malloc_sec g_depot]. destruct OUT as (_ & _ & _ & DI & _). exact DI. Qed.

#[using="LB M Sp qz rs qr qn m8 nd q b1 nch cm WL REP Erz16 Hqz Ers Hsec End Hq Emsz HS Edep GRANT OUT"] Lemma art_lrep_ia : art_rt_ia FSG G' M'.
Proof.
  pose proof REP as (_ & _ & _ & _ & _ & _ & _ & _ & IA & _). destruct IA as (C1 & C3 & C4).
  unfold art_rt_ia. cbn [art_gs_malloc_sec g_ia g_qt g_qg].
  split; [timg|]. split; [|exact C4]. intros E k Hk. apply art_lcell_img; [right; left; cbn; lia|exact (C3 E k Hk)].
Qed.

(* [comment removed for export] *)
#[using="LB M Sp qz rs qr qn m8 nd q b1 nch cm WL REP Erz16 Hqz Ers Hsec End Hq Emsz HS Edep GRANT OUT"] Lemma art_lrep_primary : art_rt_primary FSG rn G' M'.
Proof.
  pose proof REP as (ROK & _ & _ & PRIM & _). rok_open ROK. pose proof GEO as GEO'. geo_open GEO'.
  destruct PRIM as (PH & PRIM & Wsh).
  unfold art_rt_primary. cbn [art_gs_malloc_sec g_inited g_cls].
  split. { apply (art_pc_hdr_tr WL (rn_t rn + 208) (g_inited FSG G) M M' ltac:(lia) ltac:(lia) art_lrep_agree); [|exact PH].
           intros c' Hc'. apply art_lgap_thread; [lia|lia|lia|left; lia]. }
  split; [|eapply wr_grows; [exact art_lrep_grows|exact Wsh]].
  intros c0 Hc0. destruct (PRIM c0 Hc0) as (RC0 & OK0 & I0 & K0 & A0). split; [|split; [exact OK0|split; [exact I0|split; [exact K0|exact A0]]]].
  destruct OK0 as (Hl16 & _ & _ & _ & _ & _ & _ & (_ & Hmfa1) & Hnf4 & _).
  apply (art_cls_rep_tr WL (rn_t rn + 208) (rn_spb rn) (rn_ris rn) c0 (g_cls FSG G c0) M M'); first [ exact RC0 | exact art_lrep_grows | exact art_lrep_agree | exact Hl16 | lia | idtac ].
  all: first [ lia | (rewrite ?Eris; lia) | (apply art_lgap_thread; [lia|lia|lia|left; lia]) | (rewrite ?Eris; apply art_lgap_kspace; lia) ].
Qed.

(* [comment removed for export] *)
#[using="FSG rn G LB M rz qz rs qr nd q kb nch ab u REP Erz16 Hqz Ers Hsec End Hq Emsz Edep GRANT"] Lemma art_S_out_exact : forall y, 0 <= y -> (y < r \/ r + msz <= y) -> ~ (BatPoison_b.SB + r / 8 <= HeapIfaceA.S y < BatPoison_b.SB + r / 8 + msz / 8).
Proof.
  intros y Hy Z. destruct art_lrep_sh as (_ & _ & _ & _ & E1 & E2). unfold HeapIfaceA.S, HeapIfaceA.SB, BatPoison_b.SB.
  pose proof (Z.mul_div_le y 8 ltac:(lia)) as D1. pose proof (Z.mul_succ_div_gt y 8 ltac:(lia)) as D2. lia.
Qed.

#[using="FSG G rz r kb nch ab u Edep"] Lemma art_S_range : forall y, 0 <= y < 2 ^ 47 -> 0x7fff8000 <= HeapIfaceA.S y < 0x10007fff8000.
Proof.
  intros y Hy. unfold HeapIfaceA.S, HeapIfaceA.SB. pose proof (Z.mul_div_le y 8 ltac:(lia)) as D1. pose proof (Z.mul_succ_div_gt y 8 ltac:(lia)) as D2.
  assert (0 <= y / 8) by (apply Z.div_pos; lia). lia.
Qed.

(* [comment removed for export] *)
#[using="FSG rn G LB Sp n rz qz rs qr qn m8 nd q kb b1 nch cm ab u REP Erz16 Hqz Ers Hsec End Hq Emsz HS Edep GRANT OUT"] Lemma art_lbyte_far : forall y j v, 0 <= y -> 0 <= j -> 8 * (y / 8 + j) < 2 ^ 47 -> (8 * (y / 8 + j) < r \/ r + msz <= 8 * (y / 8 + j)) ->
  byte_at M (HeapIfaceA.S y + j) v -> byte_at M' (HeapIfaceA.S y + j) v.
Proof.
  intros y j v Hy Hj Hhi Z B.
  assert (Hy8 : 0 <= y / 8) by (apply Z.div_pos; lia).
  assert (E : HeapIfaceA.S y + j = HeapIfaceA.S (8 * (y / 8 + j))). { unfold HeapIfaceA.S. rewrite (Z.mul_comm 8), Z.div_mul by lia. lia. }
  rewrite E in *. apply art_lbyte_sh; [apply art_S_range; lia| |exact B]. apply art_S_out_exact; [lia|exact Z].
Qed.

(* [comment removed for export] *)
#[using="LB M rz r kb nch ab u REP Edep"] Lemma art_lchunk_in : forall c0 w0, 1 <= c0 <= 30 -> art_cptr_ok (AsanTab.class_size c0) (cl_au (g_cls FSG G c0)) w0 ->
  rn_spb rn <= rn_spb rn + c0 * 2 ^ 32 + 16 * w0 /\ rn_spb rn + c0 * 2 ^ 32 + 16 * w0 + AsanTab.class_size c0 <= rn_spb rn + 2 ^ 37.
Proof.
  intros c0 w0 Hc0 (V0 & V1 & _). pose proof REP as (_ & _ & _ & (_ & PRIM & _) & _). destruct (PRIM c0 Hc0) as (_ & OK0 & _).
  destruct OK0 as (_ & (_ & Haumu) & _ & _ & _ & Hmu3 & _). lia.
Qed.

#[using="n rz qz qn m8 nd kb b1 ab u Edep OUT"] Lemma art_lhdr : forall u0 n0 st, art_gap WL (u0 - 16) 16 -> 16 <= u0 -> u0 < 2 ^ 63 -> art_chunk_hdr M u0 n0 st -> art_chunk_hdr M' u0 n0 st.
Proof.
  intros u0 n0 st Gp H0 H1 (b & Hb & Hbt & C1 & C2 & Hn0). exists b. split; [exact Hb|]. split; [exact Hbt|]. split; [|split; [|exact Hn0]].
  - apply art_lcell; [eapply art_gap_sub; [exact Gp|lia|cbn; lia]|lia|cbn; lia|exact C1].
  - apply art_lcell; [eapply art_gap_sub; [exact Gp|lia|cbn; lia]|lia|cbn; lia|exact C2].
Qed.

#[using="FSG rn G LB Sp n rz qz rs qr qn m8 nd q kb b1 nch cm ab u REP Erz16 Hqz Ers Hsec End Hq Emsz HS Edep GRANT OUT"] Lemma art_lshadow_blk : forall u0 n0, 0 <= u0 -> 0 < n0 -> u0 + n0 < 2 ^ 47 -> (u0 + n0 <= r \/ r + msz <= u0) -> HAJ.shadow_blkR M u0 n0 -> HAJ.shadow_blkR M' u0 n0.
Proof.
  intros u0 n0 H0 Hn0 Hhi Z SB0. destruct art_lrep_sh as (_ & _ & _ & _ & E1 & E2).
  pose proof (Z.mul_div_le n0 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound n0 8 ltac:(lia)) as D3. pose proof (Z.div_mod n0 8 ltac:(lia)) as D4.
  pose proof (Z.mul_div_le u0 8 ltac:(lia)) as D5. pose proof (Z.mul_succ_div_gt u0 8 ltac:(lia)) as D6.
  apply (shadow_blkR_tby M M' u0 n0 Hn0); [|exact SB0]. intros j Hj0 Hjc v Bv. destruct Hjc as [Hj|(Ej & Hm)].
  - apply art_lbyte_far; [lia|lia|lia|lia|exact Bv].
  - subst j. apply art_lbyte_far; [lia|apply Z.div_pos; lia|lia|lia|exact Bv].
Qed.

(* [comment removed for export] *)
#[using="M Sp qz rs qr qn m8 nd q b1 nch cm WL REP Erz16 Hqz Ers Hsec End Hq Emsz HS Edep GRANT OUT"] Lemma art_lrep_chunks : art_rt_chunks FSG rn G' ((u, n) :: LB) M'.
Proof.
  pose proof REP as (ROK & _ & _ & (_ & PRIM & _) & CH & _). rok_open ROK. pose proof GEO as GEO'. geo_open GEO'.
  destruct GRANT as (_ & Ark & _). destruct art_lrep_num as (_ & _ & _ & _ & _ & Hr & Hrm & _).
  intros c0 Hc0. specialize (CH c0 Hc0). cbv zeta in CH. cbv zeta. destruct CH as (I & II & II' & III).
  cbn [art_gs_malloc_sec g_cls g_st g_qt g_qg].
  destruct (PRIM c0 Hc0) as (_ & OK0 & _). pose proof OK0 as (_ & (Hau0 & Haumu) & _ & _ & _ & Hmu3 & _).
  assert (FARK : forall y, rn_spb rn <= y < rn_spb rn + 2 ^ 37 -> y < r \/ r + msz <= y) by (intros y Hy; unfold apart in Ark; clear - Hy Ark; lia).
  assert (TB : forall x, 0 <= x < 3758096384 -> byte_at M (HeapIfaceA.S (rn_spb rn + c0 * 2 ^ 32 + x)) 250 -> byte_at M' (HeapIfaceA.S (rn_spb rn + c0 * 2 ^ 32 + x)) 250).
  { intros x Hx B. apply art_lbyte_sh; [apply art_S_range; lia| |exact B]. apply art_S_out_exact; [lia|]. apply FARK. lia. }
  split; [intros x Hx Hx8; apply TB; [lia|exact (I x Hx Hx8)]|]. split; [exact II|]. split; [exact II'|].
  intros w0 V. specialize (III w0 V). destruct (art_lchunk_in c0 w0 Hc0 V) as (K0 & K1). pose proof V as (V0 & V1 & _).
  pose proof (art_class_size_facts c0 Hc0) as (Hsz0 & _).
  assert (THDR : forall u0 n0 st, rn_spb rn + c0 * 2 ^ 32 + 16 * w0 + 16 <= u0 -> u0 + n0 <= rn_spb rn + c0 * 2 ^ 32 + 16 * w0 + AsanTab.class_size c0 -> 0 <= n0 ->
                   art_chunk_hdr M u0 n0 st -> art_chunk_hdr M' u0 n0 st).
  { intros u0 n0 st L1 L2 L3 H. apply art_lhdr; [apply art_lgap_kspace; lia|lia|lia|exact H]. }
  assert (TLCH : forall u0, art_lch M (rn_spb rn + c0 * 2 ^ 32 + 16 * w0) u0 -> art_lch M' (rn_spb rn + c0 * 2 ^ 32 + 16 * w0) u0).
  { intros u0 LC NE. destruct (LC NE) as (C1 & C2). split; (apply art_lcell; [apply art_lgap_kspace; cbn; lia|lia|cbn; lia|assumption]). }
  destruct (g_st FSG G c0 w0) as [|u0 n0|u0 n0|].
  - destruct III as (I1 & I2). split; [exact I1|apply TB; [lia|exact I2]].
  - destruct III as (J1 & J2 & J3 & J4 & J5 & J6 & J7). pose proof J4 as (_ & _ & _ & _ & _ & Hn0).
    split; [right; exact J1|]. split; [exact J2|]. split; [exact J3|]. split; [exact (THDR u0 n0 2 J2 J3 ltac:(lia) J4)|].
    split; [apply art_lshadow_blk; [lia|lia|lia|destruct (FARK u0 ltac:(lia)) as [F|F]; [left; destruct (FARK (u0 + n0 - 1) ltac:(lia)); lia|right; exact F]|exact J5]|].
    split; [apply TB; [lia|exact J6]|exact (TLCH u0 J7)].
  - destruct III as (J2 & J3 & J4 & J5 & J6 & J7). pose proof J4 as (_ & _ & _ & _ & _ & Hn0).
    split; [exact J2|]. split; [exact J3|]. split; [exact (THDR u0 n0 3 J2 J3 ltac:(lia) J4)|]. split; [exact J5|]. split; [apply TB; [lia|exact J6]|exact (TLCH u0 J7)].
  - exact III.
Qed.

Hypothesis Hroom : nch + 1 <= 16384.

(* [comment removed for export] *)
#[using="M Sp qz rs qr qn m8 nd q b1 nch cm WL REP Hn Erz16 Hqz En Hm8 Ers Hrs Hsec End Hq Emsz HS Edep GRANT GLIVE OUT LIVE Hroom"] Lemma art_lrep_sec : art_rt_sec FSG rn G' ((u, n) :: LB) M'.
Proof.
  pose proof REP as (ROK & _ & _ & _ & _ & SEC & _). rok_open ROK. pose proof GEO as GEO'. geo_open GEO'.
  destruct SEC as (C1 & C2 & C3 & C4 & C5 & C6 & S1 & S2 & SALL & SLIVE & SLEN).
  destruct art_lrep_num as (Hq1 & Hm4 & Hnch & Hblk & Hrzb & Hr & Hrm & Hri). destruct art_lrep_sh as (_ & _ & _ & _ & E1 & E2).
  destruct OUT as (GR & _ & _ & _ & WSr & WSs & Cr0 & Cr8 & Cr16 & Cr24 & Hb1 & Hty & CL1 & CL3 & CL4 & CL2 & SHZ & SHP & SS0 & SS8 & SS16 & SS56 & SS48 & SS616 & Sslot & WSp).
  fold ab in CL1, CL3, CL4, CL2, SHZ, SHP.
  unfold art_rt_sec. cbn [art_gs_malloc_sec g_sec g_sec_committed g_log g_qt g_qg]. rewrite art_live_sec_events.
  replace (1295832 + 64) with 0x13c618 by reflexivity.
  split; [exact SS0|]. split; [exact SS8|].
  split. { rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. fold nch. exact SS56. }
  split; [exact SS48|]. split; [exact SS616|]. split; [exact SS16|]. split; [intros _; reflexivity|]. split; [intros _; exact WSp|].
  split; [|split].
  - intros i s Hi. destruct (Nat.lt_ge_cases i (length (g_sec FSG G))) as [Lo|Hi'].
    + (* [comment removed for export] *)
      rewrite nth_error_app1 in Hi by exact Lo. destruct (SALL i s Hi) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10).
      destruct (LIVE _ P2) as (L0 & L1 & L2 & _). cbn [fst snd] in L0, L1, L2. pose proof (GLIVE _ P2) as AP. cbn [fst snd] in AP. unfold apart in AP.
      assert (Hn0s : 1 <= sc_n s). { destruct (sc_quar s); [destruct P9 as ((b & _ & _ & _ & _ & H) & _)|destruct P9 as (_ & (b & _ & _ & _ & _ & H) & _)]; lia. }
      split; [apply art_lcell; [apply art_lgap_slot; unfold nch; lia|lia|cbn; lia|exact P1]|].
      split; [right; exact P2|]. split; [eapply wr_grows; [exact GR|exact P3]|].
      split; [apply art_lcell; [apply (art_lgap_grant (sc_map s, sc_msize s)); [cbn; lia|exact P2|cbn; lia|cbn; lia]|lia|cbn; lia|exact P4]|].
      split; [apply art_lcell; [apply (art_lgap_grant (sc_map s, sc_msize s)); [cbn; lia|exact P2|cbn; lia|cbn; lia]|lia|cbn; lia|exact P5]|].
      split; [apply art_lcell; [apply (art_lgap_grant (sc_map s, sc_msize s)); [cbn; lia|exact P2|cbn; lia|cbn; lia]|lia|cbn; lia|exact P6]|].
      split; [exact P7|]. split; [exact P8|]. split; [|exact P10].
      destruct (sc_quar s).
      * destruct P9 as (Q1 & Q2). split; [|exact Q2]. pose proof Q1 as (_ & _ & _ & _ & _ & Hn0).
        apply art_lhdr; [apply (art_lgap_grant (sc_map s, sc_msize s)); [lia|exact P2|cbn; lia|cbn; lia]|lia|lia|exact Q1].
      * destruct P9 as (Q1 & Q2 & Q3). pose proof Q2 as (_ & _ & _ & _ & _ & Hn0). split; [right; exact Q1|]. split.
        -- apply art_lhdr; [apply (art_lgap_grant (sc_map s, sc_msize s)); [lia|exact P2|cbn; lia|cbn; lia]|lia|lia|exact Q2].
        -- apply art_lshadow_blk; [lia|lia|lia|lia|exact Q3].
    + (* [comment removed for export] *)
      assert (Ei : i = length (g_sec FSG G)).
      { assert (i < length (g_sec FSG G ++ [SEC r msz u n false]))%nat by (apply nth_error_Some; rewrite Hi; discriminate). rewrite length_app in H. cbn [length] in H. lia. }
      subst i. rewrite nth_error_app2 in Hi by lia. rewrite Nat.sub_diag in Hi. cbn [nth_error] in Hi. injection Hi as <-. cbn [sc_map sc_msize sc_u sc_n sc_quar]. fold nch.
      split; [exact Sslot|]. split; [left; reflexivity|]. split; [exact WSr|]. split; [exact Cr0|]. split; [exact Cr8|]. split; [exact Cr24|].
      split; [unfold u, ab; lia|]. split; [unfold u, ab in *; lia|]. split; [|exact Hri].
      split; [left; reflexivity|]. split.
      * exists b1. split; [exact Hb1|]. split; [exact Hty|]. split.
        { apply (art_hdr_word M' (u - 16) 2 b1); [unfold u, ab; lia|unfold u, ab; lia|lia|exact Hb1| | |].
          - replace (u - 16) with (ab + rz - 16) by (unfold u; lia). exact CL1.
          - replace (u - 16 + 1) with (ab + rz - 15) by (unfold u; lia). exact CL3.
          - replace (u - 16 + 2) with (ab + rz - 14) by (unfold u; lia). exact CL4. }
        split; [replace (u - 12) with (ab + rz - 12) by (unfold u; lia); exact CL2|lia].
      * assert (Hqn : n / 8 = qn). { symmetry. apply (Z.div_unique _ 8 qn m8); lia. }
        assert (Hmod : n mod 8 = m8). { rewrite (Z.mod_eq n 8) by lia. rewrite Hqn. lia. }
        assert (ESu : HeapIfaceA.S u = 2147450880 + ab / 8 + 2 * qz).
        { unfold HeapIfaceA.S, HeapIfaceA.SB, u. rewrite Erz16. replace (ab + 16 * qz) with (ab + (2 * qz) * 8) by lia. rewrite Z.div_add by lia. lia. }
        assert (Hab8 : 0 <= ab / 8 /\ 8 * (ab / 8) <= ab). { split; [apply Z.div_pos; unfold ab; lia|apply Z.mul_div_le; lia]. }
        assert (BYTE : forall y v, 0 <= y <= qn -> 0 <= v < 256 -> cellA M' (2147450880 + ab / 8 + 2 * qz + y) 1 v -> byte_at M' (2147450880 + ab / 8 + 2 * qz + y) v).
        { intros y v Hy Hv C. apply art_byte_of_cell1; [right; lia|unfold ab in *; lia|exact Hv|exact C]. }
        left. split.
        -- intros j Hj. rewrite ESu, Hqn in *. apply BYTE; [lia|lia|apply SHZ; lia].
        -- intros Hm. rewrite ESu, Hqn, Hmod in *. apply BYTE; [lia|lia|apply SHP; lia].
  - intros p [Ep|Hp].
    + exists (SEC r msz u n false). split; [apply in_or_app; right; left; reflexivity|]. cbn [sc_map sc_msize]. symmetry. exact Ep.
    + destruct (SLIVE p Hp) as (s & Hs & Es). exists s. split; [apply in_or_app; left; exact Hs|exact Es].
  - rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. fold nch. cbn. lia.
Qed.

(* [comment removed for export] *)
#[using="LB M Sp qz rs qr qn m8 nd q b1 nch cm WL REP Erz16 Hqz Ers Hsec End Hq Emsz HS Edep GRANT OUT"] Lemma art_lrep_quar : art_rt_quar FSG rn G' M'.
Proof.
  pose proof REP as (ROK & _ & _ & (_ & PRIM & _) & _ & _ & QU & _). rok_open ROK. pose proof GEO as GEO'. geo_open GEO'.
  destruct QU as ((ft & lt & T1 & T2 & T3 & T4 & TL) & (fg & lg & Q1 & Q2 & Q3 & Q4 & QL) & B1 & B2 & F1 & ND & NEB & ITEMS & NDI & BCH).
  destruct (PRIM 24 ltac:(lia)) as (_ & OK24 & _). pose proof OK24 as (_ & (Hau24 & Haumu24) & _ & _ & _ & Hmu324 & _).
  assert (BEQ : forall b, In b (g_qt FSG G ++ g_qg FSG G) -> 0 <= bt_addr b /\ bt_addr b + 8192 < 2 ^ 64 /\ forall x : word, bt_addr b <= U x < bt_addr b + 8192 -> M' x = M x).
  { intros b Hb. destruct (BCH b Hb) as (wb & Eb & Vb & Stb). pose proof Vb as (Vb0 & Vb1 & _). rewrite art_class_size_24 in Vb1.
    split; [rewrite Eb; clear - G4 Vb0; lia|]. split; [rewrite Eb; clear - G4 Espb G6 Eris G2 Vb1 Haumu24 Hmu324; lia|]. intros x Hx. rewrite Eb in Hx.
    apply art_lrep_agree. apply (art_gap_out _ (U x) 1); [apply art_lgap_kspace; lia|lia]. }
  assert (TT : forall a (k : nat) v, rn_t rn <= a -> a + Z.of_nat k <= rn_t rn + 208 -> cellA M a k v -> cellA M' a k v).
  { intros a k v Ha Hk C. apply art_lcell; [apply art_lgap_thread; lia|lia|lia|exact C]. }
  unfold art_rt_quar. cbn [art_gs_malloc_sec g_qt g_qg g_cls g_st g_sec].
  split. { exists ft, lt. split; [apply TT; [lia|cbn; lia|exact T1]|]. split; [apply TT; [lia|cbn; lia|exact T2]|]. split; [apply TT; [lia|cbn; lia|exact T3]|].
           split; [apply TT; [lia|cbn; lia|exact T4]|]. apply (art_batch_list_tr M M'); [|exact TL]. intros b Hb. apply BEQ. apply in_or_app. left. exact Hb. }
  split. { exists fg, lg. split; [timg|]. split; [timg|]. split; [timg|]. split; [timg|].
           apply (art_batch_list_tr M M'); [|exact QL]. intros b Hb. apply BEQ. apply in_or_app. right. exact Hb. }
  split; [exact B1|]. split; [exact B2|]. split; [timg|]. split; [exact ND|]. split; [exact NEB|].
  split. { intros b it Hb Hit. destruct (ITEMS b it Hb Hit) as [L|(s & Hs & Rr)]; [left; exact L|right]. exists s. split; [apply in_or_app; left; exact Hs|exact Rr]. }
  split; [exact NDI|exact BCH].
Qed.

(* [comment removed for export] *)
#[using="M REP"] Lemma art_lrep_blocks : art_rt_blocks FSG rn G' ((u, n) :: LB).
Proof.
  pose proof REP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & BL & _).
  intros b [Eb|Hb].
  - right. exists (SEC r msz u n false). cbn [art_gs_malloc_sec g_sec sc_quar sc_u sc_n]. subst b. cbn [fst snd].
    split; [apply in_or_app; right; left; reflexivity|]. repeat split; reflexivity.
  - destruct (BL b Hb) as [L|(s & Hs & Rr)]; [left; exact L|right]. exists s. cbn [art_gs_malloc_sec g_sec]. split; [apply in_or_app; left; exact Hs|exact Rr].
Qed.

(* [comment removed for export] *)
#[using="LB M Sp qz rs qr qn m8 nd q b1 nch cm WL REP Erz16 Hqz Ers Hsec End Hq Emsz HS Edep GRANT OUT"] Lemma art_lrep_ghost : art_rt_ghost FSG rn G' M'.
Proof.
  pose proof REP as (ROK & _ & _ & _ & _ & _ & QR & _ & _ & _ & (T1 & T23 & T4 & T5)). destruct QR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & BCH).
  destruct GRANT as (_ & Ark & _). destruct ROK as (GEO & _). geo_open GEO.
  unfold art_rt_ghost. cbn [art_gs_malloc_sec g_qt g_qg g_cls]. split; [exact T1|]. split; [exact T23|]. split.
  - intros b Hb. pose proof (T4 b Hb) as B. destruct (BCH b Hb) as (wb & Ewb & OKwb & _). destruct (art_lchunk_in 24 wb ltac:(lia) OKwb) as (K0 & K1). rewrite art_class_size_24 in K1.
    apply art_lbyte_sh; [apply art_S_range; rewrite Ewb; clear - K0 K1 G4 G6 G2 Eris; lia| |exact B].
    apply art_S_out_exact; [rewrite Ewb; clear - K0 G4; lia|]. unfold apart in Ark. rewrite Ewb. clear - Ark K0 K1. lia.
  - apply art_lcell_img; [right; left; cbn; lia|exact T5].
Qed.

(* [comment removed for export] *)
#[using="M Sp qz rs qr qn m8 nd q b1 nch cm WL REP Hn Erz16 Hqz En Hm8 Ers Hrs Hsec End Hq Emsz HS Edep GRANT GLIVE OUT LIVE Hroom"] Lemma art_lrep_new_shadow : shadow_blk M' u n.
Proof.
  pose proof REP as (ROK & _). rok_open ROK. pose proof GEO as GEO'. geo_open GEO'.
  destruct art_lrep_num as (Hq1 & Hm4 & Hnch & Hblk & Hrzb & Hr & Hrm & Hri).
  destruct OUT as (GR & _ & _ & _ & WSr & WSs & Cr0 & Cr8 & Cr16 & Cr24 & Hb1 & Hty & CL1 & CL3 & CL4 & CL2 & SHZ & SHP & SS0 & SS8 & SS16 & SS56 & SS48 & SS616 & Sslot & WSp).
  fold ab in CL1, CL3, CL4, CL2, SHZ, SHP.
  assert (Hqn : n / 8 = qn). { symmetry. apply (Z.div_unique _ 8 qn m8); lia. }
  assert (Hmod : n mod 8 = m8). { rewrite (Z.mod_eq n 8) by lia. rewrite Hqn. lia. }
  assert (ESu : HeapIfaceA.S u = 2147450880 + ab / 8 + 2 * qz).
  { unfold HeapIfaceA.S, HeapIfaceA.SB, u. rewrite Erz16. replace (ab + 16 * qz) with (ab + (2 * qz) * 8) by lia. rewrite Z.div_add by lia. lia. }
  assert (Hab8 : 0 <= ab / 8 /\ 8 * (ab / 8) <= ab). { split; [apply Z.div_pos; unfold ab; lia|apply Z.mul_div_le; lia]. }
  assert (BYTE : forall y v, 0 <= y <= qn -> 0 <= v < 256 -> cellA M' (2147450880 + ab / 8 + 2 * qz + y) 1 v -> byte_at M' (2147450880 + ab / 8 + 2 * qz + y) v).
  { intros y v Hy Hv C. apply art_byte_of_cell1; [right; lia|unfold ab in *; lia|exact Hv|exact C]. }
  split.
  - intros j Hj. rewrite ESu, Hqn in *. apply BYTE; [lia|lia|apply SHZ; lia].
  - intros Hm. rewrite ESu, Hqn, Hmod in *. apply BYTE; [lia|lia|apply SHP; lia].
Qed.

#[using="M Sp qz rs qr qn m8 nd q b1 nch cm WL REP Hn Erz16 Hqz En Hm8 Ers Hrs Hsec End Hq Emsz HS Edep GRANT GLIVE OUT LIVE Hroom"] Theorem art_alloc_rep_malloc_sec : art_alloc_rep FSG rn G' ((u, n) :: LB) M'.
Proof.
  pose proof REP as (ROK & _).
  split; [exact ROK|]. split; [exact art_lrep_statics|]. split; [exact art_lrep_thread|]. split; [exact art_lrep_primary|]. split; [exact art_lrep_chunks|].
  split; [exact art_lrep_sec|]. split; [exact art_lrep_quar|]. split; [exact art_lrep_depot|]. split; [exact art_lrep_ia|]. split; [exact art_lrep_blocks|exact art_lrep_ghost].
Qed.
End RepL.
