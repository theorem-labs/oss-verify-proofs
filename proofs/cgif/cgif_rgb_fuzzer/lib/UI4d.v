(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s YK0p.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YI02 YI01 YI03
UI1e UI1i UI57 YI07 YP14 YP15 YP13 YI08 YI0c YI0g UI3h UI3d
UI4v UI46 UI4g UI4c.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma U_mul3_add_r : forall E n m i b,
ew E n = Z_to_bv 64 i -> 0 <= i -> ew E m = Z_to_bv 64 b -> 0 <= b -> b + 3 * i < 2 ^ 64 ->
U E (SAlu ALU_ADD (SMd M_MUL (SOff n 0) (SLit 3)) (SOff m 0)) = b + 3 * i.
Proof.
intros E n m i b Hn Hi Hm Hb Hnw. rewrite <- (U_add_mul3' E n m i b Hn Hi Hm Hb Hnw).
rewrite !U_SAlu. cbn [zalu_raw]. rewrite Z.add_comm. reflexivity.
Qed.
Lemma U_add_sll2_r : forall E n m i b,
ew E n = Z_to_bv 64 i -> 0 <= i < 2 ^ 60 -> ew E m = Z_to_bv 64 b -> 0 <= b -> b + 4 * i < 2 ^ 64 ->
U E (SAlu ALU_ADD (SOff m 0) (SAlu ALU_SLL (SOff n 0) (SLit 2))) = b + 4 * i.
Proof.
intros E n m i b Hn Hi Hm Hb Hnw. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
rewrite (U_atom E n i Hn), (U_atom E m b Hm) by lia. change (Z.land (zcanon 2) 63) with 2.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite (zcanon_id (i * 4)) by (unfold M64; lia).
rewrite zcanon_id; unfold M64; lia.
Qed.
Lemma U_keys_j : forall E nh n8 h j3,
ew E nh = Z_to_bv 64 h -> ew E n8 = Z_to_bv 64 j3 -> 0 <= h -> 0 <= j3 < 2 ^ 32 -> h + j3 < 2 ^ 64 ->
U E (SAlu ALU_ADD (SOff nh 0) (SAlu ALU_AND (SOff n8 0) (SLit 4294967295))) = h + j3.
Proof.
intros E nh n8 h j3 Hh H8 R1 R2 R3. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_and_lit by lia. rewrite (U_atom E nh h Hh), (U_atom E n8 j3 H8) by lia.
change 4294967295 with (Z.ones 32). rewrite Z.land_ones, Z.mod_small by lia. apply zcanon_id. unfold M64; lia.
Qed.
Lemma U_add0 : forall E a x, U E a = x -> 0 <= x < 2 ^ 64 -> U E (SAlu ALU_ADD a (SLit 0)) = x.
Proof. intros E a x Ha Hx. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, Ha. change (zcanon 0) with 0. rewrite Z.add_0_r. apply zcanon_id. unfold M64; lia. Qed.
Lemma mbyte_of_val_mem1' : forall (m : word -> option byte) a v,
val_mem ubs2segs m a 1 v -> 0 <= v < 256 -> mbyte ubs2segs m a = Some (Z_to_bv 8 v).
Proof.
intros m a v H Hv. specialize (H 0%nat ltac:(lia)). cbn [Z.of_nat] in H. rewrite Z.add_0_r in H. rewrite H.
rewrite le_byte_small; [| change (2 ^ (8 * Z.of_nat 1)) with 256; exact Hv | lia].
change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
Qed.
Section d.
Variables (memc memX : word -> option byte) (f1 h1 u1 p1 x1 : Z) (K : htab) (hh : Z) (col : colour) (fq : Z).
Let T' := ht_T K.
Let cnt := ht_cnt K.
Definition rb_w (a : Z) : Prop :=
(h1 + 3 * hh <= a < h1 + 3 * hh + 3) \/ (p1 + 3 * cnt <= a < p1 + 3 * cnt + 3) \/ a = u1 + hh \/
(x1 + 4 * hh <= a < x1 + 4 * hh + 4) \/ (f1 + 4 * hh <= a < f1 + 4 * hh + 4).
Lemma cht_arrays_ins :
cht_arrays ubs2segs memc f1 h1 u1 p1 x1 K ->
zlen (ht_used K) = T' -> zlen (ht_keys K) = 3 * T' -> zlen (ht_frequ K) = T' -> zlen (ht_colidx K) = T' -> zlen (ht_pal K) = 3 * T' ->
0 <= hh < T' -> 0 <= cnt -> cnt + 1 < T' -> colour_ok col -> 0 <= fq < 2 ^ 32 -> cnt < 2 ^ 32 ->
(forall a, ~ ((h1 <= a < h1 + 3 * T') /\ (p1 <= a < p1 + 3 * T'))) -> (forall a, ~ ((h1 <= a < h1 + 3 * T') /\ (u1 <= a < u1 + T'))) ->
(forall a, ~ ((h1 <= a < h1 + 3 * T') /\ (x1 <= a < x1 + 4 * T'))) -> (forall a, ~ ((h1 <= a < h1 + 3 * T') /\ (f1 <= a < f1 + 4 * T'))) ->
(forall a, ~ ((p1 <= a < p1 + 3 * T') /\ (u1 <= a < u1 + T'))) -> (forall a, ~ ((p1 <= a < p1 + 3 * T') /\ (x1 <= a < x1 + 4 * T'))) ->
(forall a, ~ ((p1 <= a < p1 + 3 * T') /\ (f1 <= a < f1 + 4 * T'))) -> (forall a, ~ ((u1 <= a < u1 + T') /\ (x1 <= a < x1 + 4 * T'))) ->
(forall a, ~ ((u1 <= a < u1 + T') /\ (f1 <= a < f1 + 4 * T'))) -> (forall a, ~ ((x1 <= a < x1 + 4 * T') /\ (f1 <= a < f1 + 4 * T'))) ->
mbyte ubs2segs memX (h1 + 3 * hh) = Some (Z_to_bv 8 (cR col)) -> mbyte ubs2segs memX (h1 + 3 * hh + 1) = Some (Z_to_bv 8 (cG col)) ->
mbyte ubs2segs memX (h1 + 3 * hh + 2) = Some (Z_to_bv 8 (cB col)) ->
mbyte ubs2segs memX (p1 + 3 * cnt) = Some (Z_to_bv 8 (cR col)) -> mbyte ubs2segs memX (p1 + 3 * cnt + 1) = Some (Z_to_bv 8 (cG col)) ->
mbyte ubs2segs memX (p1 + 3 * cnt + 2) = Some (Z_to_bv 8 (cB col)) ->
mbyte ubs2segs memX (u1 + hh) = Some (Z_to_bv 8 1) ->
val_mem ubs2segs memX (x1 + 4 * hh) 4 cnt -> val_mem ubs2segs memX (f1 + 4 * hh) 4 fq ->
(forall a, ((h1 <= a < h1 + 3 * T') \/ (p1 <= a < p1 + 3 * T') \/ (u1 <= a < u1 + T') \/ (x1 <= a < x1 + 4 * T') \/ (f1 <= a < f1 + 4 * T')) ->
~ rb_w a -> mbyte ubs2segs memX a = mbyte ubs2segs memc a) ->
cht_arrays ubs2segs memX f1 h1 u1 p1 x1 (ht_ins K hh col fq).
Proof.
intros (Af & Ah & Au & Ap & Ax) L1 L2 L3 L4 L5 Rh Rc0 Rc1 Hcol Rfq Rcnt D1 D2 D3 D4 D5 D6 D7 D8 D9 D10 K0 K1 K2 P0 P1 P2 U1 X4 F4 KEEP.
pose proof Hcol as (Qr & Qg & Qb).
unfold cht_arrays. cbn [ht_frequ ht_keys ht_used ht_pal ht_colidx ht_ins]. unfold rb_w in KEEP.
split; [|split; [|split; [|split]]].
- apply (arr32_update memc memX f1 (ht_frequ K)); [exact Af | apply zlen_setz |].
intros j Hj. destruct (Z.eq_dec j hh) as [->|Hne].
+ right. rewrite getz_setz_same by lia. split; [exact F4 | lia].
+ left. rewrite getz_setz_other by lia. split; [reflexivity|]. intros k Hk. apply KEEP; [lia|].
intros [W|[W|[W|[W|W]]]]; [apply (D4 (f1 + 4 * j + k)) | apply (D7 (f1 + 4 * j + k)) | apply (D9 (f1 + 4 * j + k)) | apply (D10 (f1 + 4 * j + k)) | ]; lia.
- apply (arr8_update memc memX h1 (ht_keys K)); [exact Ah | apply zlen_set_col |].
intros j Hj. rewrite getz_set_col by lia.
destruct (Z.eqb_spec j (3 * hh)) as [->|N0]; [right; split; [exact K0 | lia]|].
destruct (Z.eqb_spec j (3 * hh + 1)) as [->|N1]; [right; split; [rewrite Z.add_assoc; exact K1 | lia]|].
destruct (Z.eqb_spec j (3 * hh + 2)) as [->|N2]; [right; split; [rewrite Z.add_assoc; exact K2 | lia]|].
left. split; [reflexivity|]. apply KEEP; [lia|].
intros [W|[W|[W|[W|W]]]]; [ | apply (D1 (h1 + j)) | apply (D2 (h1 + j)) | apply (D3 (h1 + j)) | apply (D4 (h1 + j))]; lia.
- apply (arr8_update memc memX u1 (ht_used K)); [exact Au | apply zlen_setz |].
intros j Hj. destruct (Z.eq_dec j hh) as [->|Hne].
+ right. rewrite getz_setz_same by lia. split; [exact U1 | lia].
+ left. rewrite getz_setz_other by lia. split; [reflexivity|]. apply KEEP; [lia|].
intros [W|[W|[W|[W|W]]]]; [apply (D2 (u1 + j)) | apply (D5 (u1 + j)) | | apply (D8 (u1 + j)) | apply (D9 (u1 + j))]; lia.
- apply (arr8_update memc memX p1 (ht_pal K)); [exact Ap | apply zlen_set_col |].
intros j Hj. rewrite getz_set_col by lia. subst cnt.
destruct (Z.eqb_spec j (3 * ht_cnt K)) as [->|N0]; [right; split; [exact P0 | lia]|].
destruct (Z.eqb_spec j (3 * ht_cnt K + 1)) as [->|N1]; [right; split; [rewrite Z.add_assoc; exact P1 | lia]|].
destruct (Z.eqb_spec j (3 * ht_cnt K + 2)) as [->|N2]; [right; split; [rewrite Z.add_assoc; exact P2 | lia]|].
left. split; [reflexivity|]. apply KEEP; [lia|].
intros [W|[W|[W|[W|W]]]]; [apply (D1 (p1 + j)) | | apply (D5 (p1 + j)) | apply (D6 (p1 + j)) | apply (D7 (p1 + j))]; lia.
- apply (arr32_update memc memX x1 (ht_colidx K)); [exact Ax | apply zlen_setz |].
intros j Hj. destruct (Z.eq_dec j hh) as [->|Hne].
+ right. rewrite getz_setz_same by lia. split; [exact X4 | subst cnt; lia].
+ left. rewrite getz_setz_other by lia. split; [reflexivity|]. intros k Hk. apply KEEP; [lia|].
intros [W|[W|[W|[W|W]]]]; [apply (D3 (x1 + 4 * j + k)) | apply (D6 (x1 + 4 * j + k)) | apply (D8 (x1 + 4 * j + k)) | | apply (D10 (x1 + 4 * j + k))]; lia.
Qed.
End d.
Definition ss_REH : sstate := mkSS PC_REH sr_atoms
[ YQ0b.mkRegion (Some 2%nat) 0 5168 0 0 [mkChunk 80 (CVal 8 (SLit 4294967295))] ;
YQ0b.mkRegion (Some 20%nat) 0 48 0 0 [mkChunk 8 (CVal 8 (SOff 32%nat 0)); mkChunk 16 (CVal 8 (SOff 33%nat 0))] ;
YQ0b.mkRegion (Some 34%nat) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff 35%nat 0))] ] None
(mkFacts [(2%nat, mkAF CEIL_MIN (2^63) 4); (22%nat, mkAF 0 (2^26) 0); (35%nat, mkAF 0 1 0); (19%nat, mkAF 0 (2^24) 0); (10%nat, mkAF 1 (2^24) 0);
(32%nat, mkAF 4096 (2^63) 0); (33%nat, mkAF 4096 (2^63) 0); (34%nat, mkAF 4096 (2^63) 0); (36%nat, mkAF 4096 (2^63) 0)]
[mkAC BC_GEU (SOff 34%nat 0) (SOff 33%nat 0); mkAC BC_GEU (SOff 36%nat 0) (SOff 32%nat 0)]
[(SAlu ALU_ADD (SOff 33%nat 0) (SOff 19%nat 0), SOff 34%nat 0); (SAlu ALU_AND (SOff 22%nat 0) (SLit 4294967295), SOff 22%nat 0);
(SAlu ALU_ADD (SOff 22%nat 0) (SOff 32%nat 0), SOff 36%nat 0)]).
Section e.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Hypothesis COLHASH : forall fx', col_hash_spec (fx:=fx') API.
Variables (L : layout) (A : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (r cfp g wfn ctx path attr gen loops W H bef beffmt cur : Z) (s : cgif_st) (N : Z).
Variables (img fmt fattr fgen delay : Z) (rest : list (Z * Z)).
Local Notation POST := (rgba_post API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest).
Local Notation SP := (sp regs0).
Local Notation BASE0 := (BASE r g N img fmt rest s bef beffmt).
Local Notation AT_REH := (at_REH API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest).
Local Notation AT_RB := (at_RB API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest).
Local Notation AT_POST := (at_POST API L A regs0 mem0 md0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr fgen delay rest).
Local Notation KEEPB := (keepb r g bef beffmt s N img fmt rest).
Local Notation RZ_MEM_KEPT := (rz_mem_kept API regs0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr delay rest).
Local Notation RZ_MEM_ZSUM := (rz_mem_zsum regs0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr delay).
Local Notation RZ_MEM_HT := (rz_mem_ht regs0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr delay).
Local Notation RZ_MEM_LIVE := (rz_mem_live regs0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr delay).
Local Notation RZ_MEM_ARRS := (rz_mem_arrs regs0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr delay).
Local Notation RINV_CALL := (rgba_inv_call API L A regs0 mem0 md0 r cfp g W H bef beffmt s N img fmt fattr fgen delay rest).
Section f.
Variables (i ha : Z) (Lc : layout) (Ac : astate) (mdc : Model) (pnew fimg : Z) (imgl : list Z) (C : cht) (T' p1 x1 h1 u1 f1 : Z) (K : htab) (j : Z).
Hypothesis KRB : forall regs1 memc, AT_RB regs1 Lc Ac memc mdc i ha pnew fimg imgl C T' p1 x1 h1 u1 f1 K j ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_RB) memc (seg_rom ubs2segs)) mdc) POST.
Hypothesis KNEXT : forall regs1 memc, j + 1 < ch_T C -> AT_REH regs1 Lc Ac memc mdc i ha pnew fimg imgl C T' p1 x1 h1 u1 f1 K (j + 1) ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_REH) memc (seg_rom ubs2segs)) mdc) POST.
Hypothesis KPOST : forall regs1 memc K', AT_POST regs1 Lc Ac memc mdc i ha pnew fimg imgl C T' p1 x1 h1 u1 f1 K' ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_POST) memc (seg_rom ubs2segs)) mdc) POST.
Theorem REH_round : forall regs1 memc, AT_REH regs1 Lc Ac memc mdc i ha pnew fimg imgl C T' p1 x1 h1 u1 f1 K j ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_REH) memc (seg_rom ubs2segs)) mdc) POST.
Proof.
intros regs1 memc HAT.
destruct HAT as (HINV & HRZF & ((G2 & G3 & G4) & G24 & G25 & G18 & G26 & G20 & G9 & G8 & G21) & (G19 & G27 & G22 & G10) & Hj & HK & LM & RZB).
pose proof LM as (RZM & S72 & CS & (Af & Ah & Au & Ap & Ax) & HTK & RZS).
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HH & HNmax & Hbf & HB0).
pose proof RZM as (_ & _ & _ & _ & _ & S80 & _).
pose proof (RZ_MEM_ARRS _ _ _ _ _ _ _ RZM) as (Bf & Bh & Bu).
pose proof (RZ_MEM_HT _ _ _ _ _ _ _ RZM) as (Hinv & HT & Hch & HTlt). pose proof (RZ_MEM_ZSUM _ _ _ _ _ _ _ RZM) as Hz.
pose proof (RZ_MEM_LIVE _ _ _ _ _ _ _ RZM) as (EhS & EuS & ETS).
pose proof HRZF as (Hfmt & Hi & Hha & ET').
pose proof (proj1 alloc_ceiling_val) as Hac. pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5168) by reflexivity. assert (HCSv : COLHASH_STK = 64) by reflexivity.
pose proof (ts_chain_ok _ Hch) as (RT1 & RT2 & RT3). unfold MAX_TABLE_SIZE in RT1, HTlt.
pose proof (resize_next (ch_T C) Hch HTlt) as (Hch' & HTT' & (RT1' & RT2' & RT3')). rewrite <- ET' in Hch', HTT', RT1', RT2', RT3'. unfold MAX_TABLE_SIZE in RT1'.
pose proof Hinv as ((L1 & L2 & L3 & L4 & L5) & (C1 & C2 & C3) & (B1 & B2 & B3) & _). rewrite HT in L1, L2, L3, C1, B1.
pose proof HK as ((M1 & M2 & M3 & M4 & M5) & (N1 & N2 & N3) & _). rewrite HTK in M1, M2, M3, M4, M5, N1.
set (T := ch_T C) in *.
unfold rz_blocks in RZB.
assert (INB : forall b, In b (KEEPB pnew fimg C ++ newb T' p1 x1 h1 u1 f1) -> In b (blocks Lc Ac)) by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact RZB | exact Hb]).
assert (RNG : forall q n, In (q, n) (blocks Lc Ac) -> 0 < n -> 4096 <= q /\ q + n <= alloc_ceiling).
{ intros q n Hq Hn. destruct (heap_blocks_range ubs2_msyms MR LAWS Lc Ac memc mdc q n HHc Hq Hn) as (Q0 & Q1 & _). lia. }
destruct (RNG (ch_c C) CHT_SIZE ltac:(apply INB; apply in_app_iff; left; unfold keepb; apply in_app_iff; right; apply in_app_iff; right; left; reflexivity) ltac:(unfold CHT_SIZE; lia)) as [Rc0 Rc1]. unfold CHT_SIZE in Rc1.
destruct (RNG (ch_u C) T ltac:(apply INB; apply in_app_iff; left; unfold keepb; apply in_app_iff; right; apply in_app_iff; right; cbn; auto 10) ltac:(lia)) as [Ru0 Ru1].
destruct (RNG (ch_f C) (4 * T) ltac:(apply INB; apply in_app_iff; left; unfold keepb; apply in_app_iff; right; apply in_app_iff; right; cbn; auto 10) ltac:(lia)) as [Rf0 Rf1].
destruct (RNG (ch_h C) (3 * T) ltac:(apply INB; apply in_app_iff; left; unfold keepb; apply in_app_iff; right; apply in_app_iff; right; cbn; auto 10) ltac:(lia)) as [Rh0 Rh1].
destruct (RNG h1 (3 * T') ltac:(apply INB; apply in_app_iff; right; cbn; auto 10) ltac:(lia)) as [Rk0 Rk1].
destruct (RNG u1 T' ltac:(apply INB; apply in_app_iff; right; cbn; auto 10) ltac:(lia)) as [Rv0 Rv1].
assert (SEPcu : ch_c C + 48 <= ch_u C \/ ch_u C + T <= ch_c C).
{ pose proof (perm_sep API Lc Ac memc mdc (ch_c C, CHT_SIZE) (ch_u C, T) (BASE0 ++ [(pnew, fmt * N); (fimg, N)]) ([(ch_f C, 4 * T); (ch_h C, 3 * T); (ch_u C, T)] ++ newb T' p1 x1 h1 u1 f1) HHc) as X.
cbn [fst snd] in X. unfold CHT_SIZE in X. apply X.
- unfold keepb in RZB. rewrite <- !app_assoc in RZB. rewrite <- !app_assoc. exact RZB.
- apply in_app_iff. right. cbn. auto 10. }
destruct (arr8_getz ubs2segs memc (ch_u C) (ht_used (ch_H C)) j Bu ltac:(lia)) as [Buj _].
change (getz (ht_used (ch_H C)) j) with (usedz (ch_H C) j) in Buj.
assert (U01 : usedz (ch_H C) j = 0 \/ usedz (ch_H C) j = 1) by (apply B1; lia).
set (uj := usedz (ch_H C) j) in *.
pose proof (obj_at_nth ubs2segs memc (ch_c C) LAY_Cht _ 1 _ _ RZS eq_refl eq_refl) as [B1s _]. pose proof (obj_at_nth ubs2segs memc (ch_c C) LAY_Cht _ 2 _ _ RZS eq_refl eq_refl) as [B2s _].
cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add] in B1s, B2s. rewrite EhS in B1s. rewrite EuS in B2s.
set (E := Ereg regs1 (map (Z_to_bv 64) [ch_h C; ch_u C; ch_u C + j; uj; ch_h C + 3 * j] ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HE32 : ew E 32 = Z_to_bv 64 (ch_h C)) by (subst E; apply (Ereg_vals regs1 _ [] 0%nat); reflexivity).
assert (HE33 : ew E 33 = Z_to_bv 64 (ch_u C)) by (subst E; apply (Ereg_vals regs1 _ [] 1%nat); reflexivity).
assert (HE34 : ew E 34 = Z_to_bv 64 (ch_u C + j)) by (subst E; apply (Ereg_vals regs1 _ [] 2%nat); reflexivity).
assert (HE35 : ew E 35 = Z_to_bv 64 uj) by (subst E; apply (Ereg_vals regs1 _ [] 3%nat); reflexivity).
assert (HE36 : ew E 36 = Z_to_bv 64 (ch_h C + 3 * j)) by (subst E; apply (Ereg_vals regs1 _ [] 4%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = SP) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (HE20 : ew E 20 = Z_to_bv 64 (ch_c C)) by (rewrite (HE 20%nat 20%bv eq_refl); exact G20).
assert (HU20 : bv_unsigned (ew E 20) = ch_c C) by (rewrite HE20; apply unsigned_lit_small; lia).
assert (HU34 : bv_unsigned (ew E 34) = ch_u C + j) by (rewrite HE34; apply unsigned_lit_small; lia).
assert (HE19 : ew E 19 = Z_to_bv 64 j) by (rewrite (HE 19%nat 19%bv eq_refl); exact G19).
assert (HE27 : ew E 27 = Z_to_bv 64 (4 * j)) by (rewrite (HE 27%nat 27%bv eq_refl); exact G27).
assert (HE22 : ew E 22 = Z_to_bv 64 (3 * j)) by (rewrite (HE 22%nat 22%bv eq_refl); exact G22).
assert (HE10 : ew E 10 = Z_to_bv 64 T) by (rewrite (HE 10%nat 10%bv eq_refl); exact G10).
assert (Hsp16 : SP mod 16 = 0).
{ unfold sp, sp0, RGBA_FRAME. replace (spZ regs0 - 5168) with (spZ regs0 + (-323) * 16) by lia. rewrite Z.mod_add; [exact Hal0 | lia]. }
assert (HS : st_ok ubs2segs E ss_REH (mkst regs1 (Z_to_bv 64 PC_REH) memc (seg_rom ubs2segs))).
{ unfold ss_REH. subst E. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]]; unfold region_ok; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
+ rewrite HU2. split; [unfold sp, sp0 in *; lia|]. split; [unfold sp, sp0 in *; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val _ _ _ _ _ _ _ 4294967295); [cbn [sv_denot]; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. apply val_mem_word_mem. exact S80.
+ rewrite HU20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
* eapply (chunk_ok_val _ _ _ _ _ _ _ (ch_h C)); [cbn [sv_denot]; rewrite Z.add_0_r, HE32, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. exact B1s.
* eapply (chunk_ok_val _ _ _ _ _ _ _ (ch_u C)); [cbn [sv_denot]; rewrite Z.add_0_r, HE33, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. exact B2s.
+ rewrite HU34. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val _ _ _ _ _ _ _ uj); [cbn [sv_denot]; rewrite Z.add_0_r, HE35, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op]. rewrite Z.add_0_r. apply val_mem_byte; [exact Buj | lia].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite HU2, HU20, HU34.
unfold sp, sp0 in *. repeat split; try exact I; clear - Rc1 Ru1 Hj Hceil HRv HFv SEPcu; lia.
- split; [| split].
 + cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HE22, HE35, HE19, HE10, HE32, HE33, HE34, HE36, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. unfold sp, sp0 in *. repeat split; lia.
 + cbn [f_conds conds_ok]. unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite !branch_geu_U.
rewrite (U_atom _ 34 (ch_u C + j) HE34), (U_atom _ 33 (ch_u C) HE33), (U_atom _ 36 (ch_h C + 3 * j) HE36), (U_atom _ 32 (ch_h C) HE32) by lia.
split; [apply negb_true_iff, Z.ltb_ge; lia | split; [apply negb_true_iff, Z.ltb_ge; lia | exact I]].
 + cbn [f_alias alias_ok]. split; [|split; [|split; [|exact I]]]; apply U_inj.
 * rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom _ 33 (ch_u C) HE33), (U_atom _ 19 j HE19), (U_atom _ 34 (ch_u C + j) HE34) by lia. apply zcanon_small. lia.
 * rewrite U_and_lit by lia. rewrite (U_atom _ 22 (3 * j) HE22) by lia. change 4294967295 with (Z.ones 32). rewrite Z.land_ones, Z.mod_small by lia. reflexivity.
 * rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom _ 22 (3 * j) HE22), (U_atom _ 32 (ch_h C) HE32), (U_atom _ 36 (ch_h C + 3 * j) HE36) by lia. rewrite zcanon_small by lia. lia. }
assert (EA0 : env_agree 32 (Ereg regs1 []) E).
{ subst E. split; [intros n Hn; rewrite !ew_Ereg_lt by exact Hn; reflexivity | reflexivity]. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 PC_REH) memc (seg_rom ubs2segs))) in HJ. clearbody E.
Ltac ro3 := apply wr_ok_cons_ro; [cbn; lia|]; apply wr_ok_cons_ro; [cbn; lia|]; apply wr_ok_cons_ro; [cbn; lia|]; apply wr_ok_nil.
jrun LAWS ubs2tbl_ok HS HJ. { ro3. }
cbn [ms_mem mkst] in HF.
assert (Em : ms_mem ms = memc) by (apply functional_extensionality; intros x; lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => exact (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF x) end).
jbranch ubs2tbl HS.
-
rewrite branch_ne_U, (U_atom E 35 uj HE35), U_lit in Hc by lia. apply negb_true_iff in Hc. apply Z.eqb_neq in Hc.
assert (Huj : uj = 0) by lia.
assert (HK' : ht_inv K (ents_below (ch_H C) (j + 1))) by (apply (rehash_step_unused (ch_H C) K j HK); [lia | exact Huj]).
jrun LAWS ubs2tbl_ok HS HJ. { ro3. }
cbn [ms_mem mkst] in HF0.
assert (Em0 : ms_mem ms0 = memc) by (rewrite <- Em; apply functional_extensionality; intros x; lazymatch type of HF0 with frame_of ?E1 ?rs ?m1 ?m2 => exact (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF0 x) end).
jbranch ubs2tbl HS.
+
rewrite branch_ltu_U, (U_atom_off E 19 j 1 HE19), (U_atom E 10 T HE10) in Hc0 by lia. apply Z.ltb_lt in Hc0.
jrun_to LAWS ubs2tbl_ok HS HJ PC_REH. { ro3. }
cbn [ms_mem mkst] in HF1.
assert (Em1 : ms_mem ms1 = memc) by (rewrite <- Em0; apply functional_extensionality; intros x; lazymatch type of HF1 with frame_of ?E1 ?rs ?m1 ?m2 => exact (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF1 x) end).
lazymatch type of HS with st_ok _ _ ?ssf ?msf =>
pose proof (regs_kept_of_st_ok ubs2segs E ssf msf regs1 [] [2; 3; 4; 24; 25; 18; 26; 20; 9; 8; 21; 10]%bv HS EA0 ltac:(vm_compute; reflexivity)) as GK end.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl), Em1. cbn [ss_pc]. change (Z_to_bv 64 80800) with (Z_to_bv 64 PC_REH).
apply (KNEXT (ms_regs ms1) memc); [lia|]. unfold at_REH.
split; [exact HINV|]. split; [exact HRZF|].
split. { unfold s_regs, rgba_regs. rewrite (GK 2%bv ltac:(cbv; auto 20)), (GK 3%bv ltac:(cbv; auto 20)), (GK 4%bv ltac:(cbv; auto 20)), (GK 24%bv ltac:(cbv; auto 20)), (GK 25%bv ltac:(cbv; auto 20)),
(GK 18%bv ltac:(cbv; auto 20)), (GK 26%bv ltac:(cbv; auto 20)), (GK 20%bv ltac:(cbv; auto 20)), (GK 9%bv ltac:(cbv; auto 20)), (GK 8%bv ltac:(cbv; auto 20)), (GK 21%bv ltac:(cbv; auto 20)).
split; [split; [exact G2 | split; [exact G3 | exact G4]]|]. repeat (split; [assumption|]). exact G21. }
split. { unfold reh_regs.
split; [eapply (getr_of_U ubs2segs); [exact HS|]; eval_sr_get; apply (U_atom_off E 19 j 1 HE19); lia|].
split; [eapply (getr_of_U ubs2segs); [exact HS|]; eval_sr_get; replace (4 * (j + 1)) with (4 * j + 4) by lia; apply (U_atom_off E 27 (4 * j) 4 HE27); lia|].
split; [eapply (getr_of_U ubs2segs); [exact HS|]; eval_sr_get; replace (3 * (j + 1)) with (3 * j + 3) by lia; apply (U_atom_off E 22 (3 * j) 3 HE22); lia|].
rewrite (GK 10%bv ltac:(cbv; auto 20)); exact G10. }
split; [lia|]. split; [exact HK'|]. split; [exact LM | exact RZB].
+
rewrite branch_ltu_U, (U_atom_off E 19 j 1 HE19), (U_atom E 10 T HE10) in Hc0 by lia. apply Z.ltb_ge in Hc0.
jrun_to LAWS ubs2tbl_ok HS HJ PC_POST. { ro3. }
cbn [ms_mem mkst] in HF1.
assert (Em1 : ms_mem ms1 = memc) by (rewrite <- Em0; apply functional_extensionality; intros x; lazymatch type of HF1 with frame_of ?E1 ?rs ?m1 ?m2 => exact (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF1 x) end).
lazymatch type of HS with st_ok _ _ ?ssf ?msf =>
pose proof (regs_kept_of_st_ok ubs2segs E ssf msf regs1 [] [2; 3; 4; 24; 25; 18; 26; 20; 9; 8; 21]%bv HS EA0 ltac:(vm_compute; reflexivity)) as GK end.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl), Em1. cbn [ss_pc]. change (Z_to_bv 64 81264) with (Z_to_bv 64 PC_POST).
apply (KPOST (ms_regs ms1) memc K). unfold at_POST.
split; [exact HINV|]. split; [exact HRZF|].
split. { unfold s_regs, rgba_regs. rewrite (GK 2%bv ltac:(cbv; auto 20)), (GK 3%bv ltac:(cbv; auto 20)), (GK 4%bv ltac:(cbv; auto 20)), (GK 24%bv ltac:(cbv; auto 20)), (GK 25%bv ltac:(cbv; auto 20)),
(GK 18%bv ltac:(cbv; auto 20)), (GK 26%bv ltac:(cbv; auto 20)), (GK 20%bv ltac:(cbv; auto 20)), (GK 9%bv ltac:(cbv; auto 20)), (GK 8%bv ltac:(cbv; auto 20)), (GK 21%bv ltac:(cbv; auto 20)).
split; [split; [exact G2 | split; [exact G3 | exact G4]]|]. repeat (split; [assumption|]). exact G21. }
split; [replace (ch_T C) with (j + 1) by (subst T; lia); exact HK'|]. split; [exact LM | exact RZB].
-
rewrite branch_ne_U, (U_atom E 35 uj HE35), U_lit in Hc by lia. apply negb_false_iff in Hc. apply Z.eqb_eq in Hc.
assert (Huz : usedz (ch_H C) j <> 0) by (subst uj; lia).
destruct (rehash_step_used (ch_H C) (ch_ent C) Hinv K j HK ltac:(rewrite HT; lia) Huz ltac:(rewrite HTK; lia)) as (hh & Hfs & Rhh & Hhz & Hcnt & HK').
rewrite HTK in Rhh.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_col_hash. { ro3. }
cbn [ms_mem mkst] in HF0.
assert (Em0 : ms_mem ms0 = memc) by (rewrite <- Em; apply functional_extensionality; intros x; lazymatch type of HF0 with frame_of ?E1 ?rs ?m1 ?m2 => exact (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF0 x) end).
jreg HS (10%bv:reg) as Ma0. rewrite HE36 in Ma0.
jreg HS (23%bv:reg) as M23. rewrite (HE 22%nat 22%bv eq_refl), G22 in M23.
jreg HS (11%bv:reg) as Ma1. rewrite (HE 24%nat 24%bv eq_refl), G24 in Ma1.
jreg HS (12%bv:reg) as Ma2. rewrite (HE 25%nat 25%bv eq_refl), G25 in Ma2.
jreg HS (13%bv:reg) as Ma3. rewrite (HE 18%nat 18%bv eq_refl), G18 in Ma3.
jreg HS (14%bv:reg) as Ma4. jreg HS (1%bv:reg) as Mra.
jreg HS (2%bv:reg) as Mq2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Mq2.
assert (Hspms : spZ (ms_regs ms0) = SP) by (unfold spZ; rewrite Mq2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
lazymatch type of HS with st_ok _ _ ?ssf ?msf =>
pose proof (regs_kept_of_st_ok ubs2segs E ssf msf regs1 [] [2; 3; 4; 24; 25; 18; 26; 20; 9; 8; 21; 19; 27; 22]%bv HS EA0 ltac:(vm_compute; reflexivity)) as GK end.
set (col := key (ch_H C) j).
assert (Hcol3 : col3 ubs2segs memc (ch_h C + 3 * j) col) by (subst col; unfold key; apply (arr8_col3 ubs2segs memc (ch_h C) (ht_keys (ch_H C)) j Bh); lia).
pose proof Hcol3 as (_ & _ & _ & Hcolok).
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl), Em0. cbn [ss_pc]. rewrite Em0 in HJ.
eapply SR_bind.
{ eapply (COLHASH fx RGBA_STK (sp0 regs0) (FPfoot r g bef beffmt s N) L A mem0 md0 Lc Ac memc mdc (ms_regs ms0)
(ch_h C + 3 * j) h1 u1 T' 3 (ht_used K) (ht_keys K) col true hh HJ);
[ rewrite Mra; apply ret_ok_even; vm_compute; reflexivity | rewrite Hspms; exact Hsp16
| rewrite Hspms; unfold sp, sp0 in *; lia | rewrite Hspms; unfold sp, sp0 in *; lia
| exact Ma0 | exact Ma1 | exact Ma2 | exact Ma3 | exact Ma4
| split; [exact Hcol3 | left; split; reflexivity] | exact Au | exact Ah | exact M1 | exact M2 | lia
| lia | lia | lia | lia | lia | lia
| intros _; subst col; rewrite <- HTK; rewrite <- probe_of_htab; exact Hfs ]. }
cbv beta. intros c' (regs2 & mem2 & -> & HJ2 & HP2 & Hr10 & Hfr2). clear HJ.
assert (KH2 : forall a, 0 <= a < 2 ^ 64 -> SP <= a -> mbyte ubs2segs mem2 a = mbyte ubs2segs memc a).
{ intros a Ha Hs. apply Hfr2; [exact Ha | rewrite Hspms; lia]. }
assert (KL2 : forall a, 0 <= a < alloc_ceiling -> mbyte ubs2segs mem2 a = mbyte ubs2segs memc a).
{ intros a Ha. apply Hfr2; [lia | rewrite Hspms; unfold sp, sp0 in *; lia]. }
assert (RP : forall rr : reg, reg_in rr CLOB = false -> getr regs2 rr = getr (ms_regs ms0) rr) by (intros rr Hrr; exact (regs_preserved_frame _ _ HP2 rr Hrr)).
rewrite Mra. change (Z_to_bv 64 80900) with (Z_to_bv 64 PC_RB).
apply (KRB regs2 mem2). unfold at_RB.
split. { pose proof RZB as RZB'. unfold keepb in RZB'. rewrite <- !app_assoc in RZB'. apply (RINV_CALL Lc Ac memc mem2 mdc Lc Ac mdc _ HINV HJ2 RZB'). intros a Ha Hs. apply KH2; [lia | lia]. }
split; [exact HRZF|].
split. { unfold s_regs, rgba_regs. rewrite !RP by (vm_compute; reflexivity).
rewrite (GK 2%bv ltac:(cbv; auto 20)), (GK 3%bv ltac:(cbv; auto 20)), (GK 4%bv ltac:(cbv; auto 20)), (GK 24%bv ltac:(cbv; auto 20)), (GK 25%bv ltac:(cbv; auto 20)),
(GK 18%bv ltac:(cbv; auto 20)), (GK 26%bv ltac:(cbv; auto 20)), (GK 20%bv ltac:(cbv; auto 20)), (GK 9%bv ltac:(cbv; auto 20)), (GK 8%bv ltac:(cbv; auto 20)), (GK 21%bv ltac:(cbv; auto 20)).
split; [split; [exact G2 | split; [exact G3 | exact G4]]|]. repeat (split; [assumption|]). exact G21. }
split; [rewrite RP by (vm_compute; reflexivity); rewrite (GK 19%bv ltac:(cbv; auto 20)); exact G19|].
split; [rewrite RP by (vm_compute; reflexivity); rewrite (GK 27%bv ltac:(cbv; auto 20)); exact G27|].
split; [rewrite RP by (vm_compute; reflexivity); rewrite (GK 22%bv ltac:(cbv; auto 20)); exact G22|].
split; [rewrite RP by (vm_compute; reflexivity); exact M23|].
split; [exists hh; split; [exact Hr10 | split; [exact Hfs | exact Hhz]]|].
split; [lia|]. split; [exact Huz|]. split; [exact HK|]. split; [exact Hcnt|].
split. { unfold loop_mem. split. { apply (RZ_MEM_KEPT Lc Ac memc mem2 mdc i ha pnew fimg imgl C _ i HHc ltac:(unfold sp, sp0 in *; lia) ltac:(unfold sp, sp0 in *; lia) Hfmt RZB RZM); [| | exact Hz].
- intros a Ha Hs _ _. apply KH2; [lia | exact Hs].
- intros b n k Hb Hk. assert (Hbn : In (b, n) (blocks Lc Ac)) by (apply INB; apply in_app_iff; left; apply (keepb_sub r g bef beffmt s N img fmt rest); exact Hb).
destruct (RNG b n Hbn ltac:(lia)) as [Rb0 Rb1]. apply KL2. lia. }
split. { unfold slot, SL_72 in S72 |- *. apply (val_mem_kept8 memc); [exact S72|]. intros k Hk. apply KH2; unfold sp, sp0 in *; lia. }
split. { destruct CS as (Q1 & Q2 & Q3). unfold cmpl_slots, slot in *.
split; [|split]; (apply (val_mem_kept8 memc); [assumption|]); intros k Hk; apply KH2; unfold sp, sp0 in *; lia. }
assert (NB : forall b n a, In (b, n) (newb T' p1 x1 h1 u1 f1) -> b <= a < b + n -> mbyte ubs2segs mem2 a = mbyte ubs2segs memc a).
{ intros b n a Hb Ha. destruct (RNG b n ltac:(apply INB; apply in_app_iff; right; exact Hb) ltac:(lia)) as [Rb0 Rb1]. apply KL2. lia. }
split. { unfold cht_arrays. split; [|split; [|split; [|split]]].
- eapply arr32_frame; [exact Af|]. intros a Ha. apply (NB f1 (4 * T')); [cbn; auto 10 | rewrite <- M3; lia].
- eapply arr8_frame; [exact Ah|]. intros a Ha. apply (NB h1 (3 * T')); [cbn; auto 10 | rewrite <- M2; lia].
- eapply arr8_frame; [exact Au|]. intros a Ha. apply (NB u1 T'); [cbn; auto 10 | rewrite <- M1; lia].
- eapply arr8_frame; [exact Ap|]. intros a Ha. apply (NB p1 (3 * T')); [cbn; auto 10 | rewrite <- M5; lia].
- eapply arr32_frame; [exact Ax|]. intros a Ha. apply (NB x1 (4 * T')); [cbn; auto 10 | rewrite <- M4; lia]. }
split; [exact HTK|].
eapply (obj_at_transport_range ubs2segs _ _ _ _ _ CHT_SIZE); [exact RZS | reflexivity |]. intros k Hk. unfold CHT_SIZE in Hk. apply KL2. lia. }
exact RZB.
Qed.
End f.
End e.
End c.
