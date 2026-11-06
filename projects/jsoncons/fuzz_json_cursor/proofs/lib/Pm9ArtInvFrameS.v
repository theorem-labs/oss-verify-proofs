(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatSim StoreOk AsanAcct HeapIface HeapIfaceA PmHeapIfaceA PmShadowW As0Tables ArtMem Pm9ArtLeaf Pm9ArtAllocG Pm9ArtPoison Pm9ArtRzLog Pm9ArtAllocA Pm9ArtInitCache Pm9ArtPopulate1
     ArtRuns ArtRunsMem Pm9ArtCls Pm9ArtCARSpec Pm9ArtDepotA Pm9ArtDepot ArtBridge Pm9ArtInv Pm9ArtInvMallocPure Pm9ArtFsInv Pm9ArtFsInvLaws Pm9ArtIfaceLaws.

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Definition art_sx_zone (z : Z) : Prop := 0x7fff8000 <= z < 0x10007fff8000.

Section FrameLawS.
Variable FSG : Type.
Variables MAPS0 RESV0 : list (word * word).
Variables (rn : art_run) (G : art_gs FSG) (LB : list (Z * Z)) (M M' : word -> option byte).
Hypothesis REP : art_alloc_rep FSG rn G LB M.
Hypothesis GRW : mem_grows M M'.
Variables (ux nx : Z).
Hypothesis HBX : In (ux, nx) LB.
Hypothesis HUX : ux mod 8 = 0 /\ 0 < nx.
Let EX (z : Z) : Prop := in_shadow_of ux nx z.
Hypothesis SHWX : shadow_blk_w M' ux nx.
Let XB (z : Z) : Prop := in_block LB z \/ EX z.
Hypothesis AG : forall x : word, art_alloc_zone FSG rn G (U x) -> ~ XB (U x) -> M' x = M x.
Hypothesis LSAN : cellA M' (rn_tp rn + rn_loff rn) 4 0.
Hypothesis LIVEOK : live_ok MAPS0 RESV0 (rn_HI rn) (art_live (g_log FSG G)).
Hypothesis KN : art_kn_ok MAPS0 RESV0 rn.

Lemma fl_live : forall p, In p (art_live (g_log FSG G)) ->
  0 < fst p /\ 0 < snd p /\ fst p mod 4096 = 0 /\ snd p mod 4096 = 0 /\ fst p + snd p <= rn_HI rn /\ (fst p + snd p <= 0x7fff7000 \/ 0x10007fff8000 <= fst p)
  /\ (forall o, In o (art_objs rn) -> apart (fst p) (snd p) (fst o) (snd o)).
Proof.
  intros p Hp. destruct LIVEOK as (LO & _). destruct (LO p Hp) as (P0 & P1 & P2 & P3 & P4 & P5 & P6). unfold SHLO, SHHI in P5.
  repeat (split; [assumption|]). intros o Ho. destruct (KN o Ho) as (q & Hq & Q1 & Q2). specialize (P6 q Hq). unfold apart. lia.
Qed.
Lemma fl_live_apart : forall p p', In p (art_live (g_log FSG G)) -> In p' (art_live (g_log FSG G)) -> fst p <> fst p' -> apart (fst p) (snd p) (fst p') (snd p').
Proof. intros p p' Hp Hp' N. destruct LIVEOK as (_ & _ & PW). exact (PW p p' Hp Hp' N). Qed.

Lemma fl_chunk_in : forall c w, 1 <= c <= 30 -> art_cptr_ok (AsanTab.class_size c) (cl_au (g_cls FSG G c)) w ->
  0 <= 16 * w /\ 16 * w + AsanTab.class_size c <= 3758096384 /\ 32 <= AsanTab.class_size c.
Proof.
  intros c w Hc (V0 & V1 & _). pose proof REP as (_ & _ & _ & (_ & PRIM & _) & _). destruct (PRIM c Hc) as (_ & OK & _).
  destruct OK as (_ & (_ & Haumu) & _ & _ & _ & Hmu3 & _). pose proof (art_class_size_facts c Hc) as (Hsz & _). lia.
Qed.

Lemma fl_block_cases : forall b, In b LB ->
  (exists c w, 1 <= c <= 30 /\ art_cptr_ok (AsanTab.class_size c) (cl_au (g_cls FSG G c)) w /\ g_st FSG G c w = CAlloc (fst b) (snd b)
               /\ rn_spb rn + c * 2 ^ 32 + 16 * w + 16 <= fst b /\ fst b + snd b <= rn_spb rn + c * 2 ^ 32 + 16 * w + AsanTab.class_size c)
  \/ (exists i s, nth_error (g_sec FSG G) i = Some s /\ sc_quar s = false /\ sc_u s = fst b /\ sc_n s = snd b
                  /\ In (sc_map s, sc_msize s) (art_live (g_log FSG G)) /\ sc_map s + 4096 <= fst b - 16 /\ fst b + snd b <= sc_map s + sc_msize s).
Proof.
  intros b Hb. pose proof REP as (_ & _ & _ & _ & CH & SEC & _ & _ & _ & BL & _).
  destruct (BL b Hb) as [(c0 & w0 & Hc0 & V0 & St0)|(s & Hs & Hq & Eu & En0)].
  - left. exists c0, w0. specialize (CH c0 Hc0). cbv zeta in CH. destruct CH as (_ & _ & _ & III). specialize (III w0 V0). rewrite St0 in III.
    destruct III as (_ & J2 & J3 & _). repeat (split; [assumption|]). exact J3.
  - right. destruct SEC as (_ & _ & _ & _ & _ & _ & _ & _ & SALL & _). destruct (In_nth_error _ _ Hs) as (i & Hi). exists i, s.
    destruct (SALL i s Hi) as (_ & P2 & _ & _ & _ & _ & P7 & P8 & _). rewrite Eu in P7, P8. rewrite En0 in P8. repeat (split; [assumption|]). exact P8.
Qed.

Lemma fl_block_where : forall z, in_block LB z ->
  (exists c w u n, 1 <= c <= 30 /\ art_cptr_ok (AsanTab.class_size c) (cl_au (g_cls FSG G c)) w /\ g_st FSG G c w = CAlloc u n
                   /\ rn_spb rn + c * 2 ^ 32 + 16 * w + 16 <= u /\ u <= z < u + n /\ u + n <= rn_spb rn + c * 2 ^ 32 + 16 * w + AsanTab.class_size c)
  \/ (exists i s, nth_error (g_sec FSG G) i = Some s /\ sc_quar s = false /\ In (sc_map s, sc_msize s) (art_live (g_log FSG G))
                  /\ sc_map s + 4096 <= sc_u s - 16 /\ sc_u s <= z < sc_u s + sc_n s /\ sc_u s + sc_n s <= sc_map s + sc_msize s).
Proof.
  intros z (b & Hb & Hz). destruct (fl_block_cases b Hb) as [(c & w & Hc & V & St & J2 & J3)|(i & s & Hi & Hq & Eu & En0 & P2 & P7 & P8)].
  - left. exists c, w, (fst b), (snd b). repeat (split; [assumption|]). exact J3.
  - right. exists i, s. rewrite <- Eu in Hz, P7, P8. rewrite <- En0 in Hz, P8. repeat (split; [assumption|]). exact P8.
Qed.

Lemma fl_kspace_hi : 0x10007fff8000 <= rn_spb rn /\ rn_spb rn + 2 ^ 37 + 4096 <= rn_HI rn /\ rn_kbase rn < rn_spb rn <= rn_kbase rn + 65536 /\ rn_HI rn + 8388608 <= 2 ^ 47.
Proof. destruct REP as (ROK & _). rok_open ROK. geo_open GEO. rewrite Eris in G6. repeat split; lia. Qed.

Lemma fl_ex_bounds : 4096 <= ux /\ ux + nx <= rn_HI rn.
Proof.
  destruct fl_kspace_hi as (K1 & K2 & K3 & K4).
  destruct (fl_block_cases (ux, nx) HBX) as [(c & w & Hc & V & St & J2 & J3)|(i & s & Hi & Hq & Eu & En0 & P2 & P7 & P8)]; cbn [fst snd] in *.
  - destruct (fl_chunk_in c w Hc V) as (W0 & W1 & W2). clear - J2 J3 W0 W1 W2 K1 K2 Hc. lia.
  - destruct (fl_live _ P2) as (L0 & L1 & _ & _ & L4 & _). cbn [fst snd] in L0, L1, L4. clear - P7 P8 L0 L4. lia.
Qed.
Lemma fl_ex_y : forall y, 0 <= y -> EX (HeapIfaceA.S y) -> ux <= y < 8 * ((ux + nx + 7) / 8).
Proof.
  intros y Hy (E1 & E2). unfold HeapIfaceA.S in E1, E2. destruct HUX as (U8 & Un). destruct fl_ex_bounds as (B0 & _).
  pose proof (Z.div_mod ux 8 ltac:(lia)) as Du. rewrite U8, Z.add_0_r in Du.
  pose proof (Z.div_mod y 8 ltac:(lia)) as Dy. pose proof (Z.mod_pos_bound y 8 ltac:(lia)) as Ry.
  pose proof (Z.div_mod (ux + nx - 1) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (ux + nx - 1) 8 ltac:(lia)) as R1.
  pose proof (Z.div_mod (ux + nx + 7) 8 ltac:(lia)) as D7. pose proof (Z.mod_pos_bound (ux + nx + 7) 8 ltac:(lia)) as R7. lia.
Qed.
Lemma HEX : forall z, EX z -> art_sx_zone z.
Proof.
  intros z (E1 & E2). destruct fl_ex_bounds as (B0 & B1). destruct fl_kspace_hi as (_ & _ & _ & K4). destruct HUX as (_ & Un). unfold art_sx_zone, HeapIfaceA.S, HeapIfaceA.SB in *.
  pose proof (Z.div_pos ux 8 ltac:(lia) ltac:(lia)). assert ((ux + nx - 1) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.
Lemma fl_nex : forall z, z < 0x7fff8000 \/ 0x10007fff8000 <= z -> ~ EX z.
Proof. intros z Hz E. apply HEX in E. unfold art_sx_zone in E. lia. Qed.

Lemma fl_nb_far : forall lo n z, lo <= z < lo + n -> (lo + n <= 0x10000 \/ 0x6b4000 <= lo) -> (lo + n <= 0x7fff7000 \/ 0x10007fff8000 <= lo) -> apart lo n (rn_spb rn) (2 ^ 37 + 4096) -> (forall p, In p (art_live (g_log FSG G)) -> apart (fst p) (snd p) lo n) -> ~ XB z.
Proof.
  intros lo n z Hz OFF OFS Ak Ap [IB|E]; [|apply (fl_nex z); [clear - Hz OFS; lia|exact E]]. destruct (fl_block_where z IB) as [(c & w & u & n0 & Hc & V & _ & J2 & Hu & J3)|(i & s & _ & _ & P2 & P7 & Hu & P8)].
  - destruct (fl_chunk_in c w Hc V) as (K0 & K1 & K2). unfold apart in Ak. clear - Hz Ak J2 Hu J3 K0 K1 K2 Hc. lia.
  - specialize (Ap _ P2). cbn [fst snd] in Ap. unfold apart in Ap. clear - Hz Ap P7 Hu P8. lia.
Qed.

Lemma fl_grant_obj : forall p k, In p (art_live (g_log FSG G)) -> forall o, nth_error (art_objs rn) k = Some o -> apart (fst p) (snd p) (fst o) (snd o).
Proof. intros p k Hp o Ho. destruct (fl_live p Hp) as (_ & _ & _ & _ & _ & _ & LO). apply LO. exact (nth_error_In _ _ Ho). Qed.

Lemma fl_grant_img : forall p, In p (art_live (g_log FSG G)) -> fst p + snd p <= 0x10000 \/ 0x6b4000 <= fst p.
Proof.
  intros p Hp. destruct (fl_live p Hp) as (P0 & P1 & _).
  pose proof (fl_grant_obj p 7 Hp _ eq_refl) as A1. pose proof (fl_grant_obj p 8 Hp _ eq_refl) as A2.
  pose proof (fl_grant_obj p 9 Hp _ eq_refl) as A3. pose proof (fl_grant_obj p 10 Hp _ eq_refl) as A4. cbn [fst snd] in *. unfold apart in *. clear - P0 P1 A1 A2 A3 A4. lia.
Qed.

Lemma fl_nb_img0 : forall z, 0x10000 <= z < 0x6b4000 -> ~ in_block LB z.
Proof.
  intros z Hz IB. destruct fl_kspace_hi as (K1 & _).
  destruct (fl_block_where z IB) as [(c & w & u & n0 & Hc & V & _ & J2 & Hu & J3)|(i & s & _ & _ & P2 & P7 & Hu & P8)].
  - destruct (fl_chunk_in c w Hc V) as (K0 & _). clear - Hz K1 J2 Hu K0 Hc. lia.
  - destruct (fl_grant_img _ P2) as [P|P]; cbn [fst snd] in P; clear - Hz P P7 Hu P8; lia.
Qed.
Lemma fl_nb_img : forall z, 0x10000 <= z < 0x6b4000 -> ~ EX z -> ~ XB z.
Proof. intros z Hz NE [IB|E]; [exact (fl_nb_img0 z Hz IB)|exact (NE E)]. Qed.
Lemma fl_nb_thread : forall z, rn_t rn <= z < rn_t rn + 4096 -> ~ XB z.
Proof.
  intros z Hz. apply (fl_nb_far (rn_t rn) 4096 z Hz).
  - destruct REP as (ROK & _). rok_open ROK. geo_open GEO. exact G9.
  - destruct REP as (ROK & _). rok_open ROK. geo_open GEO. exact G10.
  - destruct REP as (ROK & _). rok_open ROK. geo_open GEO. exact G11.
  - intros p Hp. exact (fl_grant_obj p 0 Hp _ eq_refl).
Qed.
Lemma fl_nb_ctx : forall z, rn_ctx rn <= z < rn_ctx rn + 4096 -> ~ XB z.
Proof.
  intros z Hz. apply (fl_nb_far (rn_ctx rn) 4096 z Hz).
  - destruct REP as (ROK & _). rok_open ROK. geo_open GEO. exact G15.
  - destruct REP as (ROK & _). rok_open ROK. geo_open GEO. exact G16.
  - destruct REP as (ROK & _). rok_open ROK. geo_open GEO. exact G17.
  - intros p Hp. exact (fl_grant_obj p 1 Hp _ eq_refl).
Qed.
Lemma fl_nb_parr : forall z, rn_parr rn <= z < rn_parr rn + 2 ^ 23 -> ~ XB z.
Proof.
  intros z Hz. apply (fl_nb_far (rn_parr rn) (2 ^ 23) z Hz).
  - destruct REP as (ROK & _). rok_open ROK. right. exact Plo.
  - destruct REP as (ROK & _). rok_open ROK. destruct Papp as (_ & PA & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in PA. exact PA.
  - destruct REP as (ROK & _). rok_open ROK. exact Apk.
  - intros p Hp. exact (fl_grant_obj p 3 Hp _ eq_refl).
Qed.

Lemma fl_nb_shadow0 : forall z, 0x7fff7000 <= z < 0x10007fff8000 -> ~ in_block LB z.
Proof.
  intros z Hz IB. destruct fl_kspace_hi as (K1 & _).
  destruct (fl_block_where z IB) as [(c & w & u & n0 & Hc & V & _ & J2 & Hu & J3)|(i & s & _ & _ & P2 & P7 & Hu & P8)].
  - destruct (fl_chunk_in c w Hc V) as (K0 & _). clear - Hz K1 J2 Hu K0 Hc. lia.
  - destruct (fl_live _ P2) as (_ & _ & _ & _ & _ & P5 & _). cbn [fst snd] in P5. clear - Hz P5 P7 Hu P8. lia.
Qed.

Lemma fl_nb_shadow : forall y, 0 <= y -> 0x7fff7000 <= HeapIfaceA.S y < 0x10007fff8000 -> ~ (ux <= y < 8 * ((ux + nx + 7) / 8)) -> ~ XB (HeapIfaceA.S y).
Proof. intros y Hy Hz NY [IB|E]; [exact (fl_nb_shadow0 _ Hz IB)|exact (NY (fl_ex_y y Hy E))]. Qed.

Lemma fl_cell : forall a (n : nat) v, 0 <= a -> a + Z.of_nat n < 2 ^ 64 ->
  (forall z, a <= z < a + Z.of_nat n -> art_alloc_zone FSG rn G z /\ ~ XB z) -> cellA M a n v -> cellA M' a n v.
Proof. intros a n v Ha Hn Z C. apply (art_cell_agree ASEGS M M'); [|exact Ha|exact Hn|exact C]. intros x Hx. destruct (Z (U x) Hx) as (Z1 & Z2). exact (AG x Z1 Z2). Qed.
Lemma fl_byte : forall a v, 0 <= a < 2 ^ 64 -> art_alloc_zone FSG rn G a -> ~ XB a -> byte_at M a v -> byte_at M' a v.
Proof. intros a v Ha Z NB B. unfold byte_at in *. rewrite (AG (Z_to_bv 64 a)); [exact B|rewrite art_u_lit by lia; exact Z|rewrite art_u_lit by lia; exact NB]. Qed.

Lemma fl_cell_img : forall a (n : nat) v, 0x10000 <= a -> a + Z.of_nat n <= 0x6b4000 -> (forall z, a <= z < a + Z.of_nat n -> art_alloc_zone FSG rn G z /\ ~ art_sx_zone z) -> cellA M a n v -> cellA M' a n v.
Proof. intros a n v Ha Hn Z C. apply fl_cell; [lia|lia| |exact C]. intros z Hz. destruct (Z z Hz) as (Z1 & Z2). split; [exact Z1|apply fl_nb_img; [lia|intros E; exact (Z2 (HEX z E))]]. Qed.

#[local] Ltac zstat := intros z Hz; cbn in Hz; split; [first [ left; unfold art_zone_statics; lia | do 7 right; left; lia ] | unfold art_sx_zone; lia].
#[local] Ltac timg := apply fl_cell_img; [first [lia|cbn; lia] | first [lia|cbn; lia] | zstat | assumption].

Lemma fl_statics : art_rt_statics rn M'.
Proof.
  pose proof REP as (ROK & ST & _). rok_open ROK. pose proof GEO as GEO'. geo_open GEO'.
  destruct ST as (PC & L & T & RO & RZ & DR & TG & CS).
  unfold art_rt_statics.
  split. { unfold art_prim_consts in *. decompose [and] PC. repeat split; timg. }
  split. { unfold art_layout in *. decompose [and] L. repeat split; timg. }
  split. { destruct T as (C1 & C2 & C3 & C4 & C5 & RR). pose proof RR as (_ & _ & Hkey' & _). unfold art_tsd. split; [timg|]. split; [timg|].
           split. { apply fl_cell_img; [lia|cbn; lia| |exact C3]. intros z Hz. cbn in Hz. split; [do 8 right; left; lia|unfold art_sx_zone; lia]. }
           split. { apply fl_cell_img; [lia|cbn; lia| |exact C4]. intros z Hz. cbn in Hz. split; [do 9 right; left; lia|unfold art_sx_zone; lia]. }
           split; [|exact RR]. apply fl_cell; [lia|cbn; lia| |exact C5]. intros z Hz. cbn in Hz. split; [right; right; left; lia|apply fl_nb_ctx; lia]. }
  split. { unfold art_alloc_rodata in *. decompose [and] RO. repeat split; timg. }
  split. { unfold art_rz_rodata in *. decompose [and] RZ. repeat split; timg. }
  split. { unfold DRoD in *. decompose [and] DR. repeat split; timg. }
  split. { destruct TG as (GN & T1 & T2). split; [|split].
           - intros a Ha. rewrite (AG (Z_to_bv 64 a)); [exact (GN a Ha)|rewrite art_u_lit by lia; do 7 right; left; lia|rewrite art_u_lit by lia; apply fl_nb_img; [lia|intros E; apply HEX in E; unfold art_sx_zone in E; lia]].
           - apply fl_cell_img; [lia|cbn; lia| |exact T1]. intros z Hz. cbn in Hz. split; [do 10 right; left; lia|unfold art_sx_zone; lia].
           - apply fl_cell_img; [lia|cbn; lia| |exact T2]. intros z Hz. cbn in Hz. split; [do 11 right; lia|unfold art_sx_zone; lia]. }
  decompose [and] CS. repeat split; timg.
Qed.

Lemma fl_thread : art_rt_thread rn M'.
Proof.
  pose proof REP as (ROK & _ & TH & _). rok_open ROK. pose proof GEO as GEO'. geo_open GEO'.
  destruct TH as (Wt & C1 & C2 & C3 & C4 & C5 & C6 & C7).
  assert (TT : forall a (k : nat) v, rn_t rn <= a -> a + Z.of_nat k <= rn_t rn + 4096 -> (a + Z.of_nat k <= rn_t rn + 72 \/ rn_t rn + 80 <= a) -> cellA M a k v -> cellA M' a k v).
  { intros a k v Ha Hk Off C. apply fl_cell; [lia|lia| |exact C]. intros z Hz. split; [right; left; unfold art_zone_thread; lia|apply fl_nb_thread; lia]. }
  unfold art_rt_thread. split; [eapply wr_grows; [exact GRW|exact Wt]|].
  split; [apply TT; [lia|cbn; lia|left; cbn; lia|exact C1]|].
  split. { apply fl_cell; [lia|cbn; lia| |exact C2]. intros z Hz. cbn in Hz. split; [right; right; left; lia|apply fl_nb_ctx; lia]. }
  split; [apply TT; [lia|cbn; lia|left; cbn; lia|exact C3]|]. split; [apply TT; [lia|cbn; lia|left; cbn; lia|exact C4]|].
  split; [apply TT; [lia|cbn; lia|left; cbn; lia|exact C5]|]. split; [apply TT; [lia|cbn; lia|right; cbn; lia|exact C6]|].
  exact LSAN.
Qed.

Lemma fl_nb_kspace : forall z, rn_kbase rn <= z < rn_kbase rn + 0x2000011000 ->
  (forall c, 1 <= c <= 30 -> ~ (rn_spb rn + c * 2 ^ 32 + 16 <= z < rn_spb rn + c * 2 ^ 32 + 3758096384)) -> ~ XB z.
Proof.
  intros z Hz NC [IB|E]; [|pose proof REP as (ROKx & _); rok_open ROKx; apply (fl_nex z); [clear - Hz Khi; lia|exact E]]. destruct (fl_block_where z IB) as [(c & w & u & n0 & Hc & V & _ & J2 & Hu & J3)|(i & s & _ & _ & P2 & P7 & Hu & P8)].
  - destruct (fl_chunk_in c w Hc V) as (K0 & K1 & K2). apply (NC c Hc). clear - J2 Hu J3 K0 K1. lia.
  - pose proof (fl_grant_obj _ 2 P2 _ eq_refl) as Ak. cbn [fst snd] in Ak. unfold apart in Ak. clear - Hz Ak P7 Hu P8. lia.
Qed.

Lemma fl_primary : art_rt_primary FSG rn G M'.
Proof.
  pose proof REP as (ROK & _ & _ & (PH & PRIM & Wsh) & _). rok_open ROK. pose proof GEO as GEO'. geo_open GEO'.
  assert (TT : forall a (k : nat) v, rn_t rn + 80 <= a -> a + Z.of_nat k <= rn_t rn + 4096 -> cellA M a k v -> cellA M' a k v).
  { intros a k v Ha Hk C. apply fl_cell; [lia|lia| |exact C]. intros z Hz. split; [right; left; unfold art_zone_thread; lia|apply fl_nb_thread; lia]. }
  assert (KZ : forall z, rn_spb rn <= z < rn_spb rn + 2 ^ 37 + 4096 -> art_alloc_zone FSG rn G z).
  { intros z Hz. do 3 right. left. unfold art_zone_kspace. clear - Hz Kspb. lia. }
  split; [|split; [|eapply wr_grows; [exact GRW|exact Wsh]]].
  - intros c Hc. destruct (PH c Hc) as (P1 & P2). split; apply TT; first [lia|cbn; lia|assumption].
  - intros c Hc. destruct (PRIM c Hc) as (RC & OK & REST). split; [|split; [exact OK|exact REST]].
    destruct OK as (Hl16 & _ & _ & _ & _ & _ & _ & (_ & Hmfa1) & Hnf4 & _).
    destruct RC as ((C0 & CW) & (R0 & R16 & R24 & R32 & R40 & R48 & R56 & R72 & R80 & RF & W1 & W2 & W3)).
    assert (RI : forall a (k : nat) v, rn_ris rn + 128 * c <= a -> a + Z.of_nat k <= rn_ris rn + 128 * c + 128 -> cellA M a k v -> cellA M' a k v).
    { intros a k v Ho Hk C. apply fl_cell; [lia|lia| |exact C]. intros z Hz. split; [apply KZ; lia|].
      apply fl_nb_kspace; [clear - Hz Ho Hk Hc Eris Kspb; lia|]. intros c' Hc'. clear - Hz Ho Hk Hc Hc' Eris. lia. }
    split; [split|].
    + apply TT; [lia|cbn; lia|exact C0].
    + intros j Hj. apply TT; [lia|cbn; lia|exact (CW j Hj)].
    + repeat split; try (eapply wr_grows; [exact GRW|assumption]).
      1-9: apply RI; first [lia|cbn; lia|assumption].
      intros j Hj. apply fl_cell; [lia|cbn; lia| |exact (RF j Hj)]. intros z Hz. cbn in Hz.
      assert (Hj' : Z.of_nat j < Z.of_nat (length (cl_free (g_cls FSG G c)))) by lia.
      split; [apply KZ; clear - Hz Hj' Hnf4 Hmfa1 Hc; lia|].
      apply fl_nb_kspace; [clear - Hz Hj' Hnf4 Hmfa1 Hc Kspb; lia|]. intros c' Hc'. clear - Hz Hj' Hnf4 Hmfa1 Hc Hc'. lia.
Qed.

Lemma fl_chunk_same : forall c w c' w' z, 1 <= c <= 30 -> 1 <= c' <= 30 ->
  art_cptr_ok (AsanTab.class_size c) (cl_au (g_cls FSG G c)) w -> art_cptr_ok (AsanTab.class_size c') (cl_au (g_cls FSG G c')) w' ->
  rn_spb rn + c * 2 ^ 32 + 16 * w <= z < rn_spb rn + c * 2 ^ 32 + 16 * w + AsanTab.class_size c ->
  rn_spb rn + c' * 2 ^ 32 + 16 * w' <= z < rn_spb rn + c' * 2 ^ 32 + 16 * w' + AsanTab.class_size c' -> c = c' /\ w = w'.
Proof.
  intros c w c' w' z Hc Hc' V V' Hz Hz'. destruct (fl_chunk_in c w Hc V) as (K0 & K1 & K2). destruct (fl_chunk_in c' w' Hc' V') as (K0' & K1' & K2').
  assert (Ec : c = c') by (clear - Hz Hz' K0 K1 K0' K1' Hc Hc'; lia). subst c'. split; [reflexivity|].
  destruct (Z.eq_dec w w') as [E|N]; [exact E|exfalso]. pose proof (art_cptr_apart (AsanTab.class_size c) _ w w' ltac:(clear - K2; lia) V V' N) as AP. clear - AP Hz Hz'. lia.
Qed.

Lemma fl_nb_chunk : forall c w z, 1 <= c <= 30 -> art_cptr_ok (AsanTab.class_size c) (cl_au (g_cls FSG G c)) w ->
  rn_spb rn + c * 2 ^ 32 + 16 * w <= z < rn_spb rn + c * 2 ^ 32 + 16 * w + AsanTab.class_size c ->
  (forall u n, g_st FSG G c w = CAlloc u n -> ~ (u <= z < u + n)) -> ~ XB z.
Proof.
  intros c w z Hc V Hz NU [IB|E]; [|destruct fl_kspace_hi as (K1 & _); destruct (fl_chunk_in c w Hc V) as (K0 & _); apply (fl_nex z); [clear - Hz K1 K0 Hc; lia|exact E]]. destruct (fl_block_where z IB) as [(c' & w' & u & n0 & Hc' & V' & St & J2 & Hu & J3)|(i & s & _ & _ & P2 & P7 & Hu & P8)].
  - destruct (fl_chunk_same c w c' w' z Hc Hc' V V' Hz ltac:(clear - J2 Hu J3; lia)) as (-> & ->). exact (NU u n0 St Hu).
  - destruct (fl_chunk_in c w Hc V) as (K0 & K1 & K2). destruct fl_kspace_hi as (_ & _ & Kb & _).
    pose proof (fl_grant_obj _ 2 P2 _ eq_refl) as Ak. cbn [fst snd] in Ak. unfold apart in Ak. clear - Hz Ak P7 Hu P8 K0 K1 Kb Hc. lia.
Qed.

Lemma fl_ex_ru : ux + nx <= 8 * ((ux + nx + 7) / 8) < ux + nx + 8.
Proof. destruct HUX as (_ & Un). destruct fl_ex_bounds as (B0 & _). pose proof (Z.div_mod (ux + nx + 7) 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (ux + nx + 7) 8 ltac:(lia)) as R. lia. Qed.
Lemma fl_ex_end8 : forall e, ux + nx <= e -> e mod 8 = 0 -> 8 * ((ux + nx + 7) / 8) <= e.
Proof.
  intros e He E8. destruct HUX as (_ & Un). destruct fl_ex_bounds as (B0 & _). pose proof (Z.div_mod e 8 ltac:(lia)) as De. rewrite E8, Z.add_0_r in De.
  pose proof (Z.div_mod (ux + nx + 7) 8 ltac:(lia)) as D7. pose proof (Z.mod_pos_bound (ux + nx + 7) 8 ltac:(lia)) as R7. lia.
Qed.
Lemma fl_ex_chunk : forall c w y, 1 <= c <= 30 -> art_cptr_ok (AsanTab.class_size c) (cl_au (g_cls FSG G c)) w ->
  rn_spb rn + c * 2 ^ 32 + 16 * w <= y < rn_spb rn + c * 2 ^ 32 + 16 * w + AsanTab.class_size c -> ux <= y < 8 * ((ux + nx + 7) / 8) ->
  g_st FSG G c w = CAlloc ux nx /\ rn_spb rn + c * 2 ^ 32 + 16 * w + 16 <= ux.
Proof.
  intros c w y Hc V Hy EY. destruct fl_kspace_hi as (K1 & K2 & K3 & K4). pose proof REP as (ROK & _). rok_open ROK. geo_open GEO.
  destruct (fl_block_cases (ux, nx) HBX) as [(c0 & w0 & Hc0 & V0 & St0 & J2 & J3)|(i & s & Hi & Hq & Eu & En0 & P2 & P7 & P8)]; cbn [fst snd] in *.
  - pose proof (art_class_size_facts c0 Hc0) as (_ & Hsz16).
    assert (E8 : (rn_spb rn + c0 * 2 ^ 32 + 16 * w0 + AsanTab.class_size c0) mod 8 = 0).
    { pose proof (Z.div_mod (AsanTab.class_size c0) 16 ltac:(lia)) as D. rewrite Hsz16, Z.add_0_r in D. rewrite D, Espb.
      replace (65536 * rn_qs rn + c0 * 2 ^ 32 + 16 * w0 + 16 * (AsanTab.class_size c0 / 16)) with ((8192 * rn_qs rn + c0 * 2 ^ 29 + 2 * w0 + 2 * (AsanTab.class_size c0 / 16)) * 8) by lia. apply Z_mod_mult. }
    pose proof (fl_ex_end8 _ J3 E8) as RE.
    destruct (fl_chunk_same c w c0 w0 y Hc Hc0 V V0 Hy ltac:(clear - EY J2 RE; lia)) as (-> & ->). split; [exact St0|exact J2].
  - exfalso. destruct (fl_live _ P2) as (L0 & L1 & L2 & L3 & _). cbn [fst snd] in L0, L1, L2, L3.
    assert (E8 : (sc_map s + sc_msize s) mod 8 = 0).
    { pose proof (Z.div_mod (sc_map s) 4096 ltac:(lia)) as Dm1. rewrite L2, Z.add_0_r in Dm1. pose proof (Z.div_mod (sc_msize s) 4096 ltac:(lia)) as Dm2. rewrite L3, Z.add_0_r in Dm2. rewrite Dm1, Dm2.
      replace (4096 * (sc_map s / 4096) + 4096 * (sc_msize s / 4096)) with ((512 * (sc_map s / 4096) + 512 * (sc_msize s / 4096)) * 8) by lia. apply Z_mod_mult. }
    pose proof (fl_ex_end8 _ P8 E8) as RE. destruct (fl_chunk_in c w Hc V) as (W0 & W1 & W2).
    pose proof (fl_grant_obj _ 2 P2 _ eq_refl) as Ak. cbn [fst snd] in Ak. unfold apart in Ak. clear - Hy EY RE P7 Ak W0 W1 K3 Hc. lia.
Qed.
Lemma fl_ex_tail : forall c x, 1 <= c <= 30 -> cl_au (g_cls FSG G c) <= x < 3758096384 -> ~ (ux <= rn_spb rn + c * 2 ^ 32 + x < 8 * ((ux + nx + 7) / 8)).
Proof.
  intros c x Hc Hx EY. destruct fl_kspace_hi as (K1 & K2 & K3 & K4). pose proof REP as (ROK & _). rok_open ROK. geo_open GEO.
  pose proof REP as (_ & _ & _ & (_ & PRIM & _) & _). destruct (PRIM c Hc) as (_ & OKc & _). destruct OKc as (_ & (Hau0 & _) & _).
  destruct (fl_block_cases (ux, nx) HBX) as [(c0 & w0 & Hc0 & V0 & St0 & J2 & J3)|(i & s & Hi & Hq & Eu & En0 & P2 & P7 & P8)]; cbn [fst snd] in *.
  - pose proof (art_class_size_facts c0 Hc0) as (_ & Hsz16). pose proof V0 as (V00 & V01 & _). destruct (fl_chunk_in c0 w0 Hc0 V0) as (W0 & W1 & W2).
    assert (E8 : (rn_spb rn + c0 * 2 ^ 32 + 16 * w0 + AsanTab.class_size c0) mod 8 = 0).
    { pose proof (Z.div_mod (AsanTab.class_size c0) 16 ltac:(lia)) as D. rewrite Hsz16, Z.add_0_r in D. rewrite D, Espb.
      replace (65536 * rn_qs rn + c0 * 2 ^ 32 + 16 * w0 + 16 * (AsanTab.class_size c0 / 16)) with ((8192 * rn_qs rn + c0 * 2 ^ 29 + 2 * w0 + 2 * (AsanTab.class_size c0 / 16)) * 8) by lia. apply Z_mod_mult. }
    pose proof (fl_ex_end8 _ J3 E8) as RE.
    destruct (Z.eq_dec c c0) as [->|NE]; [clear - Hx EY RE J2 V01; lia|clear - Hx EY RE J2 W0 W1 Hc Hc0 NE Hau0; lia].
  - destruct (fl_live _ P2) as (L0 & L1 & L2 & L3 & _). cbn [fst snd] in L0, L1, L2, L3.
    assert (E8 : (sc_map s + sc_msize s) mod 8 = 0).
    { pose proof (Z.div_mod (sc_map s) 4096 ltac:(lia)) as Dm1. rewrite L2, Z.add_0_r in Dm1. pose proof (Z.div_mod (sc_msize s) 4096 ltac:(lia)) as Dm2. rewrite L3, Z.add_0_r in Dm2. rewrite Dm1, Dm2.
      replace (4096 * (sc_map s / 4096) + 4096 * (sc_msize s / 4096)) with ((512 * (sc_map s / 4096) + 512 * (sc_msize s / 4096)) * 8) by lia. apply Z_mod_mult. }
    pose proof (fl_ex_end8 _ P8 E8) as RE.
    pose proof (fl_grant_obj _ 2 P2 _ eq_refl) as Ak. cbn [fst snd] in Ak. unfold apart in Ak. clear - Hx EY RE P7 Ak K3 Hc Hau0. lia.
Qed.

Lemma fl_sh_kspace : forall y, rn_spb rn <= y < rn_spb rn + 2 ^ 37 -> ~ (ux <= y < 8 * ((ux + nx + 7) / 8)) ->
  0 <= HeapIfaceA.S y < 2 ^ 64 /\ art_alloc_zone FSG rn G (HeapIfaceA.S y) /\ ~ XB (HeapIfaceA.S y).
Proof.
  intros y Hy NY. destruct fl_kspace_hi as (K1 & K2 & K3 & K4). pose proof REP as (ROK & _). rok_open ROK. geo_open GEO.
  assert (R : 0x7fff8000 <= HeapIfaceA.S y < 0x10007fff8000).
  { unfold HeapIfaceA.S, HeapIfaceA.SB. pose proof (Z.div_pos y 8 ltac:(lia) ltac:(lia)). assert (y / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia. }
  split; [lia|]. split; [|apply fl_nb_shadow; [lia|lia|exact NY]].
  do 6 right. left. left. unfold HeapIfaceA.S. split.
  - assert (rn_kbase rn / 8 <= y / 8) by (apply Z.div_le_mono; lia). lia.
  - assert (y / 8 < (rn_kbase rn + 0x2000011000) / 8); [|lia]. apply Z.div_lt_upper_bound; [lia|].
    assert (E : 8 * ((rn_kbase rn + 0x2000011000) / 8) = rn_kbase rn + 0x2000011000).
    { pose proof (Z.div_mod (rn_kbase rn) 4096 ltac:(lia)) as D. rewrite Kal, Z.add_0_r in D. rewrite D at 1.
      replace (4096 * (rn_kbase rn / 4096) + 0x2000011000) with ((512 * (rn_kbase rn / 4096) + 0x400002200) * 8) by lia. rewrite Z.div_mul by lia. lia. }
    lia.
Qed.

Lemma fl_S_blk_hi : forall u0 n0 j, 0 < n0 -> (j < n0 / 8 \/ (j = n0 / 8 /\ n0 mod 8 <> 0)) -> HeapIfaceA.S u0 + j <= HeapIfaceA.S (u0 + n0 - 1).
Proof.
  intros u0 n0 j Hn0 Hj. unfold HeapIfaceA.S.
  pose proof (Z.div_mod u0 8 ltac:(lia)) as Du. pose proof (Z.mod_pos_bound u0 8 ltac:(lia)) as Ru.
  pose proof (Z.div_mod n0 8 ltac:(lia)) as Dn. pose proof (Z.mod_pos_bound n0 8 ltac:(lia)) as Rn.
  assert (E : u0 / 8 + j <= (u0 + n0 - 1) / 8); [|lia].
  apply Z.div_le_lower_bound; [lia|]. destruct Hj as [Hj|[Hj Hm]]; lia.
Qed.

Lemma fl_S_off : forall u0 j, HeapIfaceA.S u0 + j = HeapIfaceA.S (u0 + 8 * j).
Proof. intros u0 j. unfold HeapIfaceA.S. replace (u0 + 8 * j) with (u0 + j * 8) by lia. rewrite Z.div_add by lia. lia. Qed.

Lemma fl_shadow_blk_k : forall u n, rn_spb rn <= u -> 0 < n -> u + n <= rn_spb rn + 2 ^ 37 -> (forall y, u <= y < u + n -> ~ (ux <= y < 8 * ((ux + nx + 7) / 8))) -> shadow_blk_w M u n -> shadow_blk_w M' u n.
Proof.
  intros u n Hu Hn Hun NYB SBW0.
  assert (T : forall j v, 0 <= j -> (j < n / 8 \/ (j = n / 8 /\ n mod 8 <> 0)) -> byte_at M (HeapIfaceA.S u + j) v -> byte_at M' (HeapIfaceA.S u + j) v).
  { intros j v Hj0 Hj B. rewrite fl_S_off in *.
    pose proof (Z.div_mod n 8 ltac:(lia)) as Dn. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as Rn.
    destruct (fl_sh_kspace (u + 8 * j) ltac:(destruct Hj as [Hj|[Hj Hm]]; lia) (NYB (u + 8 * j) ltac:(destruct Hj as [Hj|[Hj Hm]]; lia))) as (R & Z & NB). exact (fl_byte _ v R Z NB B). }
  exact (shadow_blk_w_tr M M' u n T SBW0).
Qed.

Lemma fl_chunks : art_rt_chunks FSG rn G LB M'.
Proof.
  pose proof REP as (_ & _ & _ & _ & CH & _). intros c Hc. specialize (CH c Hc). cbv zeta in *.
  destruct CH as (C1 & C2 & C3 & C4). destruct fl_kspace_hi as (K1 & K2 & K3 & K4).
  pose proof REP as (_ & _ & _ & (_ & PRIM & _) & _). destruct (PRIM c Hc) as (_ & OK & _). destruct OK as (_ & (Hau0 & Haumu) & _ & _ & _ & Hmu3 & _).
  assert (SHB : forall y v, rn_spb rn + c * 2 ^ 32 <= y < rn_spb rn + c * 2 ^ 32 + 3758096384 -> ~ (ux <= y < 8 * ((ux + nx + 7) / 8)) -> byte_at M (HeapIfaceA.S y) v -> byte_at M' (HeapIfaceA.S y) v).
  { intros y v Hy NY B. destruct (fl_sh_kspace y ltac:(clear - Hy Hc; lia) NY) as (R & Z & NB). exact (fl_byte _ v R Z NB B). }
  split. { intros x Hx H8. apply SHB; [clear - Hx Hau0 Haumu Hmu3; lia|apply (fl_ex_tail c x Hc); clear - Hx Hau0 Haumu Hmu3; lia|exact (C1 x Hx H8)]. }
  split; [exact C2|]. split; [exact C3|].
  intros w Hw. specialize (C4 w Hw). destruct (fl_chunk_in c w Hc Hw) as (W0 & W1 & W2).
  assert (KZ : forall z, rn_spb rn + c * 2 ^ 32 + 16 * w <= z < rn_spb rn + c * 2 ^ 32 + 16 * w + AsanTab.class_size c -> art_alloc_zone FSG rn G z).
  { intros z Hz. do 3 right. left. unfold art_zone_kspace. clear - Hz K3 W0 W1 Hc. lia. }
  assert (HDR : forall u n st, rn_spb rn + c * 2 ^ 32 + 16 * w + 16 <= u -> u + n <= rn_spb rn + c * 2 ^ 32 + 16 * w + AsanTab.class_size c -> 0 <= n ->
            (forall u' n', g_st FSG G c w = CAlloc u' n' -> u' = u) -> art_chunk_hdr M u n st -> art_chunk_hdr M' u n st).
  { intros u n st J2 J3 Hn0 SAME (b1 & Hb1 & Hty & H1 & H2 & Hn). exists b1. split; [exact Hb1|]. split; [exact Hty|].
    assert (TH : forall a (k : nat) v, u - 16 <= a -> a + Z.of_nat k <= u -> cellA M a k v -> cellA M' a k v).
    { intros a k v Ha Hk C. apply fl_cell; [clear - Ha J2 K1 W0 Hc; lia|clear - Hk J3 K2 K4 W1 Hc Hn0; lia| |exact C]. intros z Hz.
      split; [apply KZ; clear - Hz Ha Hk J2 J3 Hn0; lia|]. apply (fl_nb_chunk c w z Hc Hw); [clear - Hz Ha Hk J2 J3 Hn0; lia|].
      intros u' n' St. rewrite (SAME u' n' St). clear - Hz Hk. lia. }
    split; [apply TH; [lia|cbn; lia|exact H1]|]. split; [apply TH; [lia|cbn; lia|exact H2]|exact Hn]. }
  assert (LCH : forall u, rn_spb rn + c * 2 ^ 32 + 16 * w + 16 <= u -> (forall u' n', g_st FSG G c w = CAlloc u' n' -> u' = u) ->
            art_lch M (rn_spb rn + c * 2 ^ 32 + 16 * w) u -> art_lch M' (rn_spb rn + c * 2 ^ 32 + 16 * w) u).
  { intros u J2 SAME LC Hne. destruct (LC Hne) as (L1 & L2).
    assert (TL : forall a (k : nat) v, rn_spb rn + c * 2 ^ 32 + 16 * w <= a -> a + Z.of_nat k <= rn_spb rn + c * 2 ^ 32 + 16 * w + 16 -> cellA M a k v -> cellA M' a k v).
    { intros a k v Ha Hk C. apply fl_cell; [clear - Ha K1 W0 Hc; lia|clear - Hk K2 K4 W1 W2 Hc; lia| |exact C]. intros z Hz.
      split; [apply KZ; clear - Hz Ha Hk W2; lia|]. apply (fl_nb_chunk c w z Hc Hw); [clear - Hz Ha Hk W2; lia|].
      intros u' n' St. rewrite (SAME u' n' St). clear - Hz Hk J2. lia. }
    split; [apply TL; [lia|cbn; lia|exact L1]|apply TL; [lia|cbn; lia|exact L2]]. }
  assert (EXC : forall y, rn_spb rn + c * 2 ^ 32 + 16 * w <= y < rn_spb rn + c * 2 ^ 32 + 16 * w + AsanTab.class_size c -> ux <= y < 8 * ((ux + nx + 7) / 8) ->
            g_st FSG G c w = CAlloc ux nx /\ rn_spb rn + c * 2 ^ 32 + 16 * w + 16 <= ux) by (intros y Hy EY; exact (fl_ex_chunk c w y Hc Hw Hy EY)).
  destruct (g_st FSG G c w) as [|u n|u n|] eqn:St.
  - destruct C4 as (I1 & B). split; [exact I1|]. apply SHB; [clear - W0 W1 W2; lia|intros EY; destruct (EXC (rn_spb rn + c * 2 ^ 32 + 16 * w) ltac:(clear - W2; lia) EY) as (StX & _); discriminate StX|exact B].
  - destruct C4 as (I1 & J2 & J3 & HD & SB & B & LC). pose proof HD as (_ & _ & _ & _ & _ & Hn).
    split; [exact I1|]. split; [exact J2|]. split; [exact J3|].
    split; [apply (HDR u n 2 J2 J3 ltac:(lia)); [intros u' n' E; injection E as -> _; reflexivity|exact HD]|].
    split. { destruct (Z.eq_dec u ux) as [EU|NU].
             - destruct HUX as (_ & Unx). destruct fl_ex_ru as (RU1 & _). destruct (EXC u ltac:(clear - J2 J3 Hn; lia) ltac:(clear - EU Unx RU1; lia)) as (StX & _). injection StX as _ ->. rewrite EU. exact SHWX.
             - apply fl_shadow_blk_k; [clear - J2 W0 Hc; lia|lia|clear - J3 W1 Hc; lia| |exact SB].
               intros y Hy EY. destruct (EXC y ltac:(clear - Hy J2 J3; lia) EY) as (StX & _). injection StX as EU _. exact (NU EU). }
    split; [apply SHB; [clear - W0 W1 W2; lia|intros EY; destruct (EXC (rn_spb rn + c * 2 ^ 32 + 16 * w) ltac:(clear - W2; lia) EY) as (StX & JX); injection StX as EU _; clear - EY JX; lia|exact B]|]. apply LCH; [exact J2|intros u' n' E; injection E as -> _; reflexivity|exact LC].
  - destruct C4 as (J2 & J3 & HD & IB & B & LC). pose proof HD as (_ & _ & _ & _ & _ & Hn).
    split; [exact J2|]. split; [exact J3|].
    split; [apply (HDR u n 3 J2 J3 ltac:(lia)); [intros u' n' E; discriminate E|exact HD]|]. split; [exact IB|].
    split; [apply SHB; [clear - W0 W1 W2; lia|intros EY; destruct (EXC (rn_spb rn + c * 2 ^ 32 + 16 * w) ltac:(clear - W2; lia) EY) as (StX & _); discriminate StX|exact B]|]. apply LCH; [exact J2|intros u' n' E; discriminate E|exact LC].
  - exact C4.
Qed.

Lemma fl_sec_index : forall i s i' s', nth_error (g_sec FSG G) i = Some s -> nth_error (g_sec FSG G) i' = Some s' -> sc_map s = sc_map s' -> i = i'.
Proof.
  intros i s i' s' Hi Hi' E. pose proof REP as (_ & _ & _ & _ & _ & SEC & _). destruct SEC as (_ & _ & _ & _ & _ & _ & _ & _ & SALL & _ & SLEN).
  destruct (SALL i s Hi) as (_ & _ & _ & _ & _ & P6 & _). destruct (SALL i' s' Hi') as (_ & _ & _ & _ & _ & P6' & _). rewrite <- E in P6'.
  assert (Li : (i < length (g_sec FSG G))%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
  assert (Li' : (i' < length (g_sec FSG G))%nat) by (apply nth_error_Some; rewrite Hi'; discriminate).
  apply Nat2Z.inj. apply (cell8_inj M (sc_map s + 24)); [exact P6|exact P6'|lia|lia].
Qed.

Lemma fl_ex_sec : forall i s y, nth_error (g_sec FSG G) i = Some s -> sc_map s <= y < sc_map s + sc_msize s -> ux <= y < 8 * ((ux + nx + 7) / 8) -> sc_u s = ux /\ sc_n s = nx.
Proof.
  intros i s y Hi Hy EY. destruct fl_kspace_hi as (K1 & K2 & K3 & K4).
  pose proof REP as (_ & _ & _ & _ & _ & SEC & _). destruct SEC as (_ & _ & _ & _ & _ & _ & _ & _ & SALL & _). destruct (SALL i s Hi) as (_ & P2s & _).
  destruct (fl_block_cases (ux, nx) HBX) as [(c0 & w0 & Hc0 & V0 & St0 & J2 & J3)|(i0 & s0 & Hi0 & Hq0 & Eu0 & En0 & P20 & P70 & P80)]; cbn [fst snd] in *.
  - exfalso. destruct (fl_chunk_in c0 w0 Hc0 V0) as (W0 & W1 & W2). pose proof (fl_ex_ru) as (_ & RU2).
    pose proof (fl_grant_obj _ 2 P2s _ eq_refl) as Ak. cbn [fst snd] in Ak. unfold apart in Ak. clear - Hy EY RU2 J2 J3 Ak W0 W1 K3 Hc0. lia.
  - destruct (fl_live _ P20) as (L0 & L1 & L2 & L3 & _). cbn [fst snd] in L0, L1, L2, L3.
    assert (E8 : (sc_map s0 + sc_msize s0) mod 8 = 0).
    { pose proof (Z.div_mod (sc_map s0) 4096 ltac:(lia)) as Dm1. rewrite L2, Z.add_0_r in Dm1. pose proof (Z.div_mod (sc_msize s0) 4096 ltac:(lia)) as Dm2. rewrite L3, Z.add_0_r in Dm2. rewrite Dm1, Dm2.
      replace (4096 * (sc_map s0 / 4096) + 4096 * (sc_msize s0 / 4096)) with ((512 * (sc_map s0 / 4096) + 512 * (sc_msize s0 / 4096)) * 8) by lia. apply Z_mod_mult. }
    pose proof (fl_ex_end8 _ P80 E8) as RE.
    destruct (Z.eq_dec (sc_map s) (sc_map s0)) as [E|N].
    + pose proof (fl_sec_index i s i0 s0 Hi Hi0 E) as ->. rewrite Hi in Hi0. injection Hi0 as <-. split; assumption.
    + exfalso. pose proof (fl_live_apart _ _ P2s P20 N) as AP. cbn [fst snd] in AP. unfold apart in AP. clear - Hy EY RE P70 AP. lia.
Qed.

Lemma fl_nb_grant : forall i s z, nth_error (g_sec FSG G) i = Some s -> sc_map s <= z < sc_map s + sc_msize s -> ~ (sc_u s <= z < sc_u s + sc_n s) -> ~ XB z.
Proof.
  intros i s z Hi Hz NU XBz. pose proof REP as (_ & _ & _ & _ & _ & SEC & _). destruct SEC as (_ & _ & _ & _ & _ & _ & _ & _ & SALL & _).
  destruct (SALL i s Hi) as (_ & P2 & _).
  destruct XBz as [IB|E]; [|destruct (fl_live _ P2) as (_ & _ & _ & _ & _ & P5 & _); cbn [fst snd] in P5; apply (fl_nex z); [clear - Hz P5; lia|exact E]]. destruct fl_kspace_hi as (K1 & K2 & K3 & K4).
  destruct (fl_block_where z IB) as [(c' & w' & u & n0 & Hc' & V' & St & J2 & Hu & J3)|(i' & s' & Hi' & _ & P2' & P7' & Hu' & P8')].
  - destruct (fl_chunk_in c' w' Hc' V') as (W0 & W1 & W2). pose proof (fl_grant_obj _ 2 P2 _ eq_refl) as Ak. cbn [fst snd] in Ak. unfold apart in Ak.
    clear - Hz Ak J2 Hu J3 W0 W1 K3 Hc'. lia.
  - destruct (Z.eq_dec (sc_map s) (sc_map s')) as [E|N].
    + pose proof (fl_sec_index i s i' s' Hi Hi' E) as ->. rewrite Hi in Hi'. injection Hi' as <-. exact (NU Hu').
    + pose proof (fl_live_apart _ _ P2 P2' N) as AP. cbn [fst snd] in AP. unfold apart in AP. clear - Hz AP P7' Hu' P8'. lia.
Qed.

Lemma fl_sec : art_rt_sec FSG rn G LB M'.
Proof.
  pose proof REP as (ROK & _ & _ & _ & _ & SEC & _). rok_open ROK. pose proof GEO as GEO'. geo_open GEO'.
  destruct SEC as (C1 & C2 & C3 & C4 & C5 & C6 & S1 & S2 & SALL & SLIVE & SLEN).
  unfold art_rt_sec. split; [timg|]. split; [timg|]. split; [timg|]. split; [timg|]. split; [timg|]. split; [timg|].
  split; [exact S1|]. split; [intros E; eapply wr_grows; [exact GRW|exact (S2 E)]|]. split; [|split; [exact SLIVE|exact SLEN]].
  intros i s Hi. destruct (SALL i s Hi) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10).
  assert (Li : Z.of_nat i < Z.of_nat (length (g_sec FSG G))) by (apply Nat2Z.inj_lt; apply nth_error_Some; rewrite Hi; discriminate).
  destruct (fl_live _ P2) as (L0 & L1 & L2 & L3 & L4 & L5 & _). cbn [fst snd] in L0, L1, L2, L3, L4, L5.
  assert (Hn0 : 1 <= sc_n s). { destruct (sc_quar s); [destruct P9 as ((b & _ & _ & _ & _ & H) & _)|destruct P9 as (_ & (b & _ & _ & _ & _ & H) & _)]; lia. }
  assert (GZ : forall z, sc_map s <= z < sc_map s + sc_msize s -> art_alloc_zone FSG rn G z).
  { intros z Hz. do 4 right. left. right. exists (sc_map s, sc_msize s). split; [exact P2|exact Hz]. }
  assert (TG : forall a (k : nat) v, sc_map s <= a -> a + Z.of_nat k <= sc_u s -> cellA M a k v -> cellA M' a k v).
  { intros a k v Ha Hk C. apply fl_cell; [clear - Ha L0; lia|clear - Hk P8 L4 G2 Hn0; lia| |exact C]. intros z Hz.
    split; [apply GZ; clear - Hz Ha Hk P8 Hn0; lia|]. apply (fl_nb_grant i s z Hi); [clear - Hz Ha Hk P8 Hn0; lia|clear - Hz Hk; lia]. }
  assert (HDR : forall st, art_chunk_hdr M (sc_u s) (sc_n s) st -> art_chunk_hdr M' (sc_u s) (sc_n s) st).
  { intros st (b1 & Hb1 & Hty & H1 & H2 & Hn). exists b1. split; [exact Hb1|]. split; [exact Hty|].
    split; [apply TG; [clear - P7; lia|cbn; lia|exact H1]|]. split; [apply TG; [clear - P7; lia|cbn; lia|exact H2]|exact Hn]. }
  split. { apply fl_cell; [clear - Plo; lia|cbn; clear - Phi G2 Li SLEN; lia| |exact P1]. intros z Hz. cbn in Hz.
           split; [do 4 right; left; left; clear - Hz Li SLEN; lia|apply fl_nb_parr; clear - Hz Li SLEN; lia]. }
  split; [exact P2|]. split; [eapply wr_grows; [exact GRW|exact P3]|].
  split; [apply TG; [lia|cbn; clear - P7; lia|exact P4]|]. split; [apply TG; [lia|cbn; clear - P7; lia|exact P5]|]. split; [apply TG; [lia|cbn; clear - P7; lia|exact P6]|].
  split; [exact P7|]. split; [exact P8|]. split; [|exact P10].
  destruct (sc_quar s).
  - destruct P9 as (Q1 & Q2). split; [exact (HDR 3 Q1)|exact Q2].
  - destruct P9 as (Q1 & Q2 & SBW0). split; [exact Q1|]. split; [exact (HDR 2 Q2)|].
    destruct (Z.eq_dec (sc_u s) ux) as [EU|NU].
    { destruct HUX as (_ & Unx). destruct fl_ex_ru as (RU1 & _). destruct (fl_ex_sec i s (sc_u s) Hi ltac:(clear - P7 P8 Hn0; lia) ltac:(clear - EU Unx RU1; lia)) as (_ & EN). rewrite EU, EN. exact SHWX. }
    assert (E8 : 8 * ((sc_map s + sc_msize s) / 8) = sc_map s + sc_msize s).
    { pose proof (Z.div_mod (sc_map s) 4096 ltac:(lia)) as Dm1. rewrite L2, Z.add_0_r in Dm1. pose proof (Z.div_mod (sc_msize s) 4096 ltac:(lia)) as Dm2. rewrite L3, Z.add_0_r in Dm2.
      rewrite Dm1 at 1. rewrite Dm2 at 1. replace (4096 * (sc_map s / 4096) + 4096 * (sc_msize s / 4096)) with ((512 * (sc_map s / 4096) + 512 * (sc_msize s / 4096)) * 8) by lia.
      rewrite Z.div_mul by lia. lia. }
    assert (T : forall j v, 0 <= j -> (j < sc_n s / 8 \/ (j = sc_n s / 8 /\ sc_n s mod 8 <> 0)) -> byte_at M (HeapIfaceA.S (sc_u s) + j) v -> byte_at M' (HeapIfaceA.S (sc_u s) + j) v).
    { intros j v Hj0 Hj B. rewrite fl_S_off in *.
      pose proof (Z.div_mod (sc_n s) 8 ltac:(lia)) as Dn. pose proof (Z.mod_pos_bound (sc_n s) 8 ltac:(lia)) as Rn.
      assert (Hy : sc_map s <= sc_u s + 8 * j < sc_map s + sc_msize s) by (destruct Hj as [Hj|[Hj Hm]]; [clear - Hj Hj0 Dn Rn P7 P8; lia|clear - Hj Hm Hj0 Dn Rn P7 P8; lia]).
      set (y := sc_u s + 8 * j) in *.
      assert (R : 0x7fff8000 <= HeapIfaceA.S y < 0x10007fff8000).
      { unfold HeapIfaceA.S, HeapIfaceA.SB. pose proof (Z.div_pos y 8 ltac:(lia) ltac:(lia)). assert (y / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; clear - Hy L4 G2; lia). lia. }
      apply fl_byte; [clear - R; lia| |apply fl_nb_shadow; [clear - Hy L0; lia|clear - R; lia|intros EY; apply NU; exact (proj1 (fl_ex_sec i s y Hi Hy EY))]|exact B].
      do 6 right. left. right. exists (sc_map s, sc_msize s). split; [exact P2|]. cbn [fst snd]. unfold HeapIfaceA.S. split.
      - assert (sc_map s / 8 <= y / 8) by (apply Z.div_le_mono; lia). lia.
      - assert (y / 8 < (sc_map s + sc_msize s) / 8); [|lia]. apply Z.div_lt_upper_bound; [lia|]. rewrite E8. lia. }
    exact (shadow_blk_w_tr M M' (sc_u s) (sc_n s) T SBW0).
Qed.

Lemma fl_class_size_24 : AsanTab.class_size 24 = 8192. Proof. reflexivity. Qed.

Lemma fl_batch_list : forall bs f l,
  (forall b, In b bs -> exists w, bt_addr b = rn_spb rn + 24 * 2 ^ 32 + 16 * w /\ art_cptr_ok (AsanTab.class_size 24) (cl_au (g_cls FSG G 24)) w /\ g_st FSG G 24 w = CBatch) ->
  art_batch_list M bs f l -> art_batch_list M' bs f l.
Proof.
  destruct fl_kspace_hi as (K1 & K2 & K3 & K4).
  induction bs as [|b r IH]; intros f l HB BL; [exact BL|]. cbn [art_batch_list] in *.
  destruct BL as (Ef & Hlen & Cc & Cs & Ci & Cn & Rest).
  destruct (HB b (or_introl eq_refl)) as (w & Ea & V & St). destruct (fl_chunk_in 24 w ltac:(lia) V) as (W0 & W1 & W2). rewrite fl_class_size_24 in *.
  assert (TB : forall a (k : nat) v, bt_addr b <= a -> a + Z.of_nat k <= bt_addr b + 8192 -> cellA M a k v -> cellA M' a k v).
  { intros a k v Ha Hk C. apply fl_cell; [clear - Ha Ea K1 W0; lia|clear - Hk Ea K2 K4 W1; lia| |exact C]. intros z Hz. split.
    - do 3 right. left. unfold art_zone_kspace. clear - Hz Ha Hk Ea K3 W0 W1. lia.
    - apply (fl_nb_chunk 24 w z ltac:(lia) V); [rewrite fl_class_size_24; clear - Hz Ha Hk Ea; lia|]. intros u n E. rewrite St in E. discriminate E. }
  split; [exact Ef|]. split; [exact Hlen|]. split; [apply TB; [lia|cbn; lia|exact Cc]|]. split; [apply TB; [lia|cbn; lia|exact Cs]|].
  split. { intros j it Hj. apply TB; [lia| |exact (Ci j it Hj)]. assert (j < length (bt_items b))%nat by (apply nth_error_Some; rewrite Hj; discriminate). cbn. lia. }
  split. { destruct r as [|b' r']; [destruct Cn as (El & C0); split; [exact El|apply TB; [lia|cbn; lia|exact C0]]|apply TB; [lia|cbn; lia|exact Cn]]. }
  apply IH; [intros b0 Hb0; apply HB; right; exact Hb0|exact Rest].
Qed.

Lemma fl_quar : art_rt_quar FSG rn G M'.
Proof.
  pose proof REP as (ROK & _ & _ & _ & _ & _ & QU & _). rok_open ROK. pose proof GEO as GEO'. geo_open GEO'.
  destruct QU as ((f1 & l1 & T1 & T2 & T3 & T4 & BL1) & (f2 & l2 & Q1 & Q2 & Q3 & Q4 & BL2) & B1 & B2 & MX & ND & NE & ITS & NDI & CB).
  assert (TT : forall a (k : nat) v, rn_t rn + 80 <= a -> a + Z.of_nat k <= rn_t rn + 4096 -> cellA M a k v -> cellA M' a k v).
  { intros a k v Ha Hk C. apply fl_cell; [lia|lia| |exact C]. intros z Hz. split; [right; left; unfold art_zone_thread; lia|apply fl_nb_thread; lia]. }
  unfold art_rt_quar.
  split. { exists f1, l1. split; [apply TT; [lia|cbn; lia|exact T1]|]. split; [apply TT; [lia|cbn; lia|exact T2]|]. split; [apply TT; [lia|cbn; lia|exact T3]|].
           split; [apply TT; [lia|cbn; lia|exact T4]|]. apply fl_batch_list; [intros b Hb; apply CB; apply in_or_app; left; exact Hb|exact BL1]. }
  split. { exists f2, l2. split; [timg|]. split; [timg|]. split; [timg|]. split; [timg|].
           apply fl_batch_list; [intros b Hb; apply CB; apply in_or_app; right; exact Hb|exact BL2]. }
  split; [exact B1|]. split; [exact B2|]. split; [timg|]. repeat (split; [assumption|]). exact CB.
Qed.

Lemma fl_depot : art_rt_depot FSG rn G M'.
Proof.
  pose proof REP as (ROK & _ & _ & _ & _ & _ & _ & DEP & _). rok_open ROK. unfold art_rt_depot in *.
  apply (DInvD_frame (rn_l2 rn) (rn_blk rn) (g_depot FSG G) M M' DEP). intros x Dx. apply AG; [do 5 right; left; exact Dx|].
  unfold dprivD in Dx. destruct Dx as [D|[D|D]].
  - apply fl_nb_img; [clear - D; lia|intros E; apply HEX in E; unfold art_sx_zone in E; clear - D E; lia].
  - apply (fl_nb_far (rn_l2 rn) (2 ^ 20) (U x) D (or_intror Il2) ltac:(unfold apart in Al2s; clear - Al2s; lia) Al2k). intros p Hp. exact (fl_grant_obj p 4 Hp _ eq_refl).
  - apply (fl_nb_far (rn_blk rn) (2 ^ 23) (U x) D (or_intror Iblk) ltac:(unfold apart in Abs; clear - Abs; lia) Abk). intros p Hp. exact (fl_grant_obj p 5 Hp _ eq_refl).
Qed.

Lemma fl_ghost : art_rt_ghost FSG rn G M'.
Proof.
  pose proof REP as (_ & _ & _ & (_ & PRIM & _) & _ & _ & QR & _ & _ & _ & (T1 & T23 & T4 & T5)). destruct QR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & BCH).
  split; [exact T1|]. split; [exact T23|]. split.
  - intros b Hb. destruct (BCH b Hb) as (w0 & Ew0 & V0 & StB). destruct (fl_chunk_in 24 w0 ltac:(lia) V0) as (K0 & K1). rewrite fl_class_size_24 in K1.
    assert (NY : ~ (ux <= bt_addr b < 8 * ((ux + nx + 7) / 8))).
    { intros EY. destruct (fl_ex_chunk 24 w0 (bt_addr b) ltac:(lia) V0 ltac:(rewrite Ew0, fl_class_size_24; clear; lia) EY) as (StX & _). rewrite StB in StX. discriminate StX. }
    destruct (fl_sh_kspace (bt_addr b) ltac:(rewrite Ew0; clear - K0 K1; lia) NY) as (R & Z & NB). exact (fl_byte _ _ R Z NB (T4 b Hb)).
  - apply fl_cell_img; [lia|cbn; lia| |exact T5]. intros z Hz. cbn in Hz. split; [left; unfold art_zone_statics; lia|unfold art_sx_zone; lia].
Qed.

Lemma fl_ia : art_rt_ia FSG G M'.
Proof.
  pose proof REP as (_ & _ & _ & _ & _ & _ & _ & _ & IA & _). destruct IA as (C1 & C3 & C4).
  split; [timg|]. split; [|exact C4]. intros E k Hk. specialize (C3 E k Hk). apply fl_cell_img; [lia|cbn; lia| |exact C3].
  intros z Hz. cbn in Hz. split; [left; unfold art_zone_statics; lia|unfold art_sx_zone; lia].
Qed.

Theorem art_alloc_rep_frame_s0 : art_alloc_rep FSG rn G LB M'.
Proof.
  pose proof REP as (ROK & _ & _ & _ & _ & _ & _ & _ & _ & BL & _).
  split; [exact ROK|]. split; [exact fl_statics|]. split; [exact fl_thread|]. split; [exact fl_primary|]. split; [exact fl_chunks|].
  split; [exact fl_sec|]. split; [exact fl_quar|]. split; [exact fl_depot|]. split; [exact fl_ia|]. split; [exact BL|exact fl_ghost].
Qed.
End FrameLawS.

Theorem art_alloc_rep_frame_s : forall FSG MAPS0 RESV0 rn (G : art_gs FSG) LB (M M' : word -> option byte) ux nx,
  art_alloc_rep FSG rn G LB M -> mem_grows M M' -> In (ux, nx) LB -> ux mod 8 = 0 -> 0 < nx ->
  (forall x : word, art_alloc_zone FSG rn G (U x) -> ~ in_block LB (U x) -> ~ in_shadow_of ux nx (U x) -> M' x = M x) ->
  shadow_blk_w M' ux nx ->
  cellA M' (rn_tp rn + rn_loff rn) 4 0 -> live_ok MAPS0 RESV0 (rn_HI rn) (art_live (g_log FSG G)) -> art_kn_ok MAPS0 RESV0 rn ->
  art_alloc_rep FSG rn G LB M'.
Proof.
  intros FSG MAPS0 RESV0 rn G LB M M' ux nx REP GRW HB U8 Un AG SHW LSAN LIVEOK KN.
  apply (art_alloc_rep_frame_s0 FSG MAPS0 RESV0 rn G LB M M' REP GRW ux nx HB (conj U8 Un) SHW); [|exact LSAN|exact LIVEOK|exact KN].
  intros x Z NX. apply AG; [exact Z| |]; intros H; apply NX; [left; exact H|right; exact H].
Qed.
